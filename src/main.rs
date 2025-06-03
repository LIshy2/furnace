use clap::Parser;
use furnace::ctt::term::Identifier;
use furnace::flame::FlameLogger;
use furnace::parser;
use furnace::parser::ast::Module;
use furnace::precise::analyze::mark_erased;
use furnace::resolver::context::Demangler;
use furnace::resolver::module::{build_module_dependencies, resolve_modules, ModuleReader};
use furnace::typechecker::check::check_declaration_set;
use furnace::typechecker::context::{ProgressNotifier, TypeContext};
use spinners::{Spinner, Spinners};
use std::collections::HashMap;
use std::fs::{self, File};
use std::io::{LineWriter, Read};
use std::path::Path;
use std::rc::Rc;
use std::sync::{Arc, Mutex};
use tracing::{info, Level};
use tracing_appender::{non_blocking, rolling};
use tracing_subscriber::fmt::format::FmtSpan;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;

struct CachedReader {
    cache: HashMap<String, Module>,
}

impl CachedReader {
    fn new() -> CachedReader {
        CachedReader {
            cache: Default::default(),
        }
    }
}

impl ModuleReader for CachedReader {
    fn read_module(&self, name: &str) -> Module {
        let module_parser = parser::grammar::ModuleParser::new();
        let mut file = fs::File::open(format!("{}.fctt", name)).unwrap();
        let mut content = String::new();
        file.read_to_string(&mut content).unwrap();
        module_parser.parse(&content).expect("parse error")
    }
}

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    name: String,
    #[arg(short, long, action)]
    silent: bool,
}

struct CliNotifier<D: Demangler> {
    silent: bool,
    demangler: D,
    spinners: Arc<Mutex<HashMap<Identifier, Spinner>>>,
}

impl<D: Demangler> CliNotifier<D> {
    fn new(silent: bool, demangler: D) -> CliNotifier<D> {
        CliNotifier {
            silent,
            demangler,
            spinners: Arc::new(Mutex::new(Default::default())),
        }
    }
}

impl<D: Demangler> ProgressNotifier for CliNotifier<D> {
    fn decl_check_started(&self, decl_name: &Identifier) {
        if !self.silent {
            let bar = Spinner::with_timer(
                Spinners::Clock,
                format!(" - Checking {}...", self.demangler.demangle(decl_name)),
            );

            let mut spinners = self.spinners.lock().unwrap();
            spinners.insert(*decl_name, bar);
        } else {
            println!("start {}", self.demangler.demangle(decl_name));
        }
    }

    fn decl_check_finished(&self, decl_name: &Identifier) {
        if !self.silent {
            let mut spinners = self.spinners.lock().unwrap();
            let spinner = spinners.get_mut(decl_name).unwrap();
            spinner.stop_and_persist(
                "✔",
                format!("Checked {}!", self.demangler.demangle(decl_name)),
            );
        } else {
            println!("finish {}", self.demangler.demangle(decl_name));
        }
    }
}

fn main() {
    let flame_layer = FlameLogger::<LineWriter<File>>::new("./flamegraph.folded");

    tracing_subscriber::registry()
        .with(flame_layer)
        .with(tracing_subscriber::fmt::Layer::default())
        .init();

    // let file_appender = rolling::never("traces", "execution.traces");

    // let (non_blocking_writer, _guard) = non_blocking(file_appender);

    // tracing_subscriber::fmt()
    //     .with_ansi(false) // Отключаем ANSI-цвета для файла
    //     .with_writer(non_blocking_writer)
    //     .with_span_events(FmtSpan::FULL)
    //     .init();

    let args = Args::parse();
    let reader = CachedReader::new();

    let path = Path::new(&args.name);

    if path.is_file() && path.extension().map(|s| s == "fctt").unwrap_or(false) {
        let deps = build_module_dependencies(&reader, path.file_stem().unwrap().to_str().unwrap())
            .unwrap();

        let (modules, names) = resolve_modules(deps).unwrap();

        // println!("man {:?}", names.demangle(&Identifier(42)));
        // println!("man {:?}", names.demangle(&Identifier(48)));

        let modules = mark_erased(&modules);

        let progress = Rc::new(CliNotifier::new(args.silent, names));

        let mut ctx = TypeContext::new(progress);

        for set in modules.iter() {
            ctx = check_declaration_set(&ctx, set).unwrap();
        }
    } else {
        panic!("Unfound file");
    }
}
