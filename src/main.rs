use clap::Parser;
use furnace::parser;
use furnace::parser::ast::Module;
use furnace::precise::analyze::mark_erased;
use furnace::resolver::module::{build_module_dependencies, resolve_modules, ModuleReader};
use furnace::typechecker::check::check_declaration_set;
use furnace::typechecker::context::TypeContext;
use std::collections::HashMap;
use std::fs;
use std::io::Read;
use std::path::Path;
use std::time::SystemTime;
use furnace::ctt::term::Identifier;
use furnace::resolver::context::Demangler;

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
}

fn main() {
    let args = Args::parse();
    let reader = CachedReader::new();

    let path = Path::new(&args.name);

    if path.is_file() && path.extension().map(|s| s == "fctt").unwrap_or(false) {
        let deps = build_module_dependencies(&reader, path.file_stem().unwrap().to_str().unwrap())
            .unwrap();

        let (modules, names) = resolve_modules(deps).unwrap();

        let mut ctx = TypeContext::new();

        let modules = mark_erased(&modules);

        println!("man {:?}", names.demangle(&Identifier(36)));

        for set in modules.iter() {
            println!("{:?}", set);
            let start_time = SystemTime::now();
            ctx = check_declaration_set(ctx, &set).unwrap();
            let end_time = SystemTime::now();
            let x = end_time.duration_since(start_time).unwrap();
            println!("time: {}", x.as_secs_f64());
        }
    }
}
