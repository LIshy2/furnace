use once_cell::sync::Lazy;
use std::cell::Cell;
use std::fmt::{self, Write as _};
use std::fs::File;
use std::io::{LineWriter, Write};
use std::path::Path;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tracing_core::{field, span, Field, Subscriber};
use tracing_subscriber::registry::SpanRef;
use tracing_subscriber::{
    layer::{Context, Layer},
    registry::LookupSpan,
};

static START: Lazy<Instant> = Lazy::new(Instant::now);

thread_local! {
    static LAST_EVENT: Cell<Instant> = Cell::new(*START);

}

pub struct FlameLogger<W> {
    out: Arc<Mutex<W>>,
}

impl<W> FlameLogger<W> {
    pub fn new(path: impl AsRef<Path>) -> FlameLogger<LineWriter<File>> {
        let path = path.as_ref();
        let file = File::create(path).unwrap();
        let writer = LineWriter::new(file);
        FlameLogger {
            out: Arc::new(Mutex::new(writer)),
        }
    }
}

impl<S, W> Layer<S> for FlameLogger<W>
where
    S: Subscriber + for<'a> LookupSpan<'a>,
    W: Write + 'static,
{
    fn on_enter(&self, id: &span::Id, ctx: Context<'_, S>) {
        let samples = self.time_since_last_event();

        let first = ctx.span(id).expect("expected: span id exists in registry");

        let mut stack = String::new();

        stack += "all-threads";

        if let Some(second) = first.parent() {
            for parent in second.scope().from_root() {
                stack += ";";
                write(&mut stack, parent).expect("expected: write to String never fails");
            }
        }

        write!(&mut stack, " {}", samples.as_nanos())
            .expect("expected: write to String never fails");

        let _ = writeln!(*self.out.lock().unwrap(), "{}", stack);
    }

    fn on_exit(&self, id: &span::Id, ctx: Context<'_, S>) {
        let panicking = std::thread::panicking();
        macro_rules! expect {
            ($e:expr, $msg:literal) => {
                if panicking {
                    return;
                } else {
                    $e.expect($msg)
                }
            };
            ($e:expr) => {
                if panicking {
                    return;
                } else {
                    $e.unwrap()
                }
            };
        }

        let samples = self.time_since_last_event();
        let first = expect!(ctx.span(id), "expected: span id exists in registry");

        let mut stack = String::new();

        stack += "all-threads";

        for parent in first.scope().from_root() {
            stack += ";";
            expect!(
                write(&mut stack, parent),
                "expected: write to String never fails"
            );
        }

        expect!(
            write!(&mut stack, " {}", samples.as_nanos()),
            "expected: write to String never fails"
        );

        let _ = writeln!(*expect!(self.out.lock()), "{}", stack);
    }

    fn on_new_span(&self, attrs: &span::Attributes<'_>, id: &span::Id, ctx: Context<'_, S>) {
        if let Some(span) = ctx.span(id) {
            let mut fields = FieldCollector::default();
            attrs.record(&mut fields);
            span.extensions_mut().insert(fields);
        }
    }
}

impl<W> FlameLogger<W> {
    fn time_since_last_event(&self) -> Duration {
        let now = Instant::now();

        let prev = LAST_EVENT.with(|e| {
            let prev = e.get();
            e.set(now);
            prev
        });

        now - prev
    }
}

fn write<S>(dest: &mut String, span: SpanRef<'_, S>) -> fmt::Result
where
    S: Subscriber + for<'a> LookupSpan<'a>,
{
    write!(dest, "{}", span.name())?;

    if let Some(file) = span.metadata().file() {
        write!(dest, ":{}", file)?;
    }

    if let Some(line) = span.metadata().line() {
        write!(dest, ":{}", line)?;
    }
    let extensions = span.extensions();
    if let Some(fields) = extensions.get::<FieldCollector>() {
        if !fields.is_empty() {
            write!(dest, " [").unwrap();
            for (i, (name, value)) in fields.iter().enumerate() {
                if i > 0 {
                    write!(dest, ", ").unwrap();
                }
                write!(dest, "{}={}", name, value).unwrap();
            }
            write!(dest, "]").unwrap();
        } 
    }

    Ok(())
}

#[derive(Default)]
struct FieldCollector {
    fields: Vec<(String, String)>,
}

impl FieldCollector {
    fn is_empty(&self) -> bool {
        self.fields.is_empty()
    }

    fn iter(&self) -> impl Iterator<Item = &(String, String)> {
        self.fields.iter()
    }
}

impl field::Visit for FieldCollector {
    fn record_debug(&mut self, field: &Field, value: &dyn std::fmt::Debug) {
        self.fields
            .push((field.name().to_string(), format!("{:?}", value)));
    }

    fn record_i64(&mut self, field: &Field, value: i64) {
        self.fields
            .push((field.name().to_string(), value.to_string()));
    }

    fn record_u64(&mut self, field: &Field, value: u64) {
        self.fields
            .push((field.name().to_string(), value.to_string()));
    }

    fn record_bool(&mut self, field: &Field, value: bool) {
        self.fields
            .push((field.name().to_string(), value.to_string()));
    }

    fn record_str(&mut self, field: &Field, value: &str) {
        self.fields
            .push((field.name().to_string(), value.to_string()));
    }
}
