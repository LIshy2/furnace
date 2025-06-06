mod tests {
    use furnace::ctt::term::Identifier;
    use furnace::parser;
    use furnace::parser::ast::Module;
    use furnace::precise::analyze::mark_erased;
    use furnace::resolver;
    use furnace::resolver::context::{Demangler, ResolveContext};
    use furnace::resolver::module::{resolve_modules, ModuleReader};
    use furnace::typechecker::check::check_declaration_set;
    use furnace::typechecker::context::{ProgressNotifier, TypeContext};
    use std::collections::HashSet;
    use std::fs;
    use std::io::Read;
    use std::rc::Rc;
    use std::sync::{Arc, Mutex};
    use std::time::SystemTime;

    struct ExampleModules;
    impl ModuleReader for ExampleModules {
        fn read_module(&self, name: &str) -> Module {
            let module_parser = parser::grammar::ModuleParser::new();
            println!("Loading... examples/{}.fctt", name);
            let mut file = fs::File::open(format!("examples/{}.fctt", name)).unwrap();
            let mut content = String::new();
            file.read_to_string(&mut content).unwrap();
            module_parser.parse(&content).expect("parse error")
        }
    }

    struct FakeNotifier {
        demangler: ResolveContext,
        already: Arc<Mutex<HashSet<Identifier>>>,
    }

    impl FakeNotifier {
        fn new(names: ResolveContext) -> FakeNotifier {
            FakeNotifier {
                demangler: names,
                already: Arc::new(Mutex::new(HashSet::new())),
            }
        }
    }

    impl ProgressNotifier for FakeNotifier {
        fn decl_check_started(&self, name: &Identifier) {
            let mut a = self.already.lock().unwrap();
            if a.contains(name) {
                println!("ALREADY CHECKED");
                panic!();
            }
            a.insert(*name);

            println!("ccc {:?}", self.demangler.demangle(name));
        }

        fn decl_check_finished(&self, _: &Identifier) {}
    }

    #[test]
    fn check_examples() {
        unsafe { backtrace_on_stack_overflow::enable() };

        let reader = ExampleModules;
        let entries = fs::read_dir("examples").unwrap();

        for entry in entries {
            let entry = entry.unwrap();
            let path = entry.path();

            println!("NEW FILE {:?}", path);

            if path.file_name().unwrap() == "univprop.fctt" || path.file_name().unwrap() == "grothendieck.fctt" {
                continue;
            }

            if path.is_file() && path.extension().map(|s| s == "fctt").unwrap_or(false) {
                let deps = resolver::module::build_module_dependencies(
                    &reader,
                    path.file_stem().unwrap().to_str().unwrap(),
                )
                .unwrap();

                let (modules, names) = resolve_modules(deps).unwrap();
                let modules = mark_erased(&modules);

                let mut ctx = TypeContext::new(Rc::new(FakeNotifier::new(names))).uncompacted();

                for set in modules.iter() {
                    let start_time = SystemTime::now();
                    ctx = check_declaration_set(&ctx, set).unwrap();
                    let end_time = SystemTime::now();
                    let x = end_time.duration_since(start_time).unwrap();
                    // println!("time: {}", x.as_secs_f64());
                }
            }
        }
    }
}
