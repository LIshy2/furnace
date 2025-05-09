use clap::Parser;
use furnace::ctt::term::Identifier;
use furnace::parser;
use furnace::parser::ast::Module;
use furnace::precise::analyze::mark_erased;
use furnace::resolver::context::Demangler;
use furnace::resolver::module::{build_module_dependencies, resolve_modules, ModuleReader};
use furnace::typechecker::check::check_declaration_set;
use furnace::typechecker::context::{ProgressNotifier, TypeContext};
use spinners::{Spinner, Spinners};
use std::collections::HashMap;
use std::fs;
use std::io::Read;
use std::path::Path;
use std::rc::Rc;
use std::sync::{Arc, Mutex};

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

struct CliNotifier<D: Demangler> {
    demangler: D,
    spinners: Arc<Mutex<HashMap<Identifier, Spinner>>>,
}

impl<D: Demangler> CliNotifier<D> {
    fn new(demangler: D) -> CliNotifier<D> {
        CliNotifier {
            demangler,
            spinners: Arc::new(Mutex::new(Default::default())),
        }
    }
}

impl<D: Demangler> ProgressNotifier for CliNotifier<D> {
    fn decl_check_started(&self, decl_name: &Identifier) {
        let bar = Spinner::with_timer(
            Spinners::Clock,
            format!("Checking {}...", self.demangler.demangle(decl_name)),
        );

        let mut spinners = self.spinners.lock().unwrap();
        spinners.insert(*decl_name, bar);
    }

    fn decl_check_finished(&self, decl_name: &Identifier) {
        let mut spinners = self.spinners.lock().unwrap();
        let spinner = spinners.get_mut(decl_name).unwrap();
        spinner.stop_and_persist(
            "✔",
            format!("Checked {}!", self.demangler.demangle(decl_name)),
        );
    }
}

fn main() {
    let args = Args::parse();
    let reader = CachedReader::new();

    let path = Path::new(&args.name);

    if path.is_file() && path.extension().map(|s| s == "fctt").unwrap_or(false) {
        let deps = build_module_dependencies(&reader, path.file_stem().unwrap().to_str().unwrap())
            .unwrap();

        let (modules, names) = resolve_modules(deps).unwrap();

        let progress = Rc::new(CliNotifier::new(names));

        let mut ctx = TypeContext::new(progress);

        let modules = mark_erased(&modules);

        for set in modules.iter() {
            ctx = check_declaration_set(&ctx, set).unwrap();
        }
    }
}
