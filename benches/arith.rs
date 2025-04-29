use clap::Parser;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use furnace::ctt::term::Identifier;
use furnace::parser;
use furnace::parser::ast::Module;
use furnace::precise::analyze::mark_erased;
use furnace::resolver::module::{build_module_dependencies, resolve_modules, ModuleReader};
use furnace::typechecker::check::check_declaration_set;
use furnace::typechecker::context::{ProgressNotifier, TypeContext};
use std::collections::HashMap;
use std::fs;
use std::io::Read;
use std::path::Path;
use std::rc::Rc;
use std::time::Duration;

fn criterion_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("arith");

    group.sample_size(10);
    group.warm_up_time(Duration::from_secs(120));
    group.measurement_time(Duration::from_secs(60));

    group.bench_function("z4 strict", |b| b.iter(|| check_arith(black_box(false))));
    group.bench_function("z4 relaxed", |b| b.iter(|| check_arith(black_box(true))));

    group.finish()
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);

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
        let mut file = fs::File::open(format!("bench/{}.fctt", name)).unwrap();
        let mut content = String::new();
        file.read_to_string(&mut content).unwrap();
        module_parser.parse(&content).expect("parse error")
    }
}

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    name: String,
}

struct FakeNotifier {}

impl FakeNotifier {
    fn new() -> FakeNotifier {
        FakeNotifier {}
    }
}

impl ProgressNotifier for FakeNotifier {
    fn decl_check_started(&self, decl_name: &Identifier) {
        ()
    }

    fn decl_check_finished(&self, decl_name: &Identifier) {
        ()
    }
}

fn check_arith(compaction: bool) {
    let reader = CachedReader::new();

    let path = Path::new("bench/arith.fctt");

    if path.is_file() && path.extension().map(|s| s == "fctt").unwrap_or(false) {
        let deps = build_module_dependencies(&reader, path.file_stem().unwrap().to_str().unwrap())
            .unwrap();

        let (modules, _) = resolve_modules(deps).unwrap();

        let progress = Rc::new(FakeNotifier::new());

        let mut ctx = TypeContext::new(progress);

        if !compaction {
            ctx = ctx.uncompacted();
        }

        let modules = mark_erased(&modules);

        for set in modules.iter() {
            ctx = check_declaration_set(ctx, &set).unwrap();
        }
    } else {
        panic!("file not found");
    }
}
