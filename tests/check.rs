mod tests {
    use furnace::ctt::term::Identifier;
    use furnace::parser;
    use furnace::parser::ast::Module;
    use furnace::precise::analyze::mark_erased;
    use furnace::resolver;
    use furnace::resolver::context::Demangler;
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
        already: Arc<Mutex<HashSet<Identifier>>>,
    }

    impl FakeNotifier {
        fn new() -> FakeNotifier {
            FakeNotifier {
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

            println!("ccc {:?}", name);
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

            if path.is_file() && path.extension().map(|s| s == "fctt").unwrap_or(false) {
                let deps = resolver::module::build_module_dependencies(
                    &reader,
                    path.file_stem().unwrap().to_str().unwrap(),
                )
                .unwrap();

                let (modules, names) = resolve_modules(deps).unwrap();
                let modules = mark_erased(&modules);

                let mut ctx = TypeContext::new(Rc::new(FakeNotifier::new()));

                if path.to_str().unwrap() == "examples/univprop.fctt" {
                    println!("man {:?}", names.demangle(&Identifier(5261)));
                    // println!("man {:?}", names.demangle(&Identifier(2326))); // 84
                    // println!("man {:?}", names.demangle(&Identifier(4117))); // 25
                    // println!("man {:?}", names.demangle(&Identifier(4132))); // 90 
                    // println!("man {:?}", names.demangle(&Identifier(5799))); // 30
                    // println!("man {:?}", names.demangle(&Identifier(5773))); // 29
                    // println!("man {:?}", names.demangle(&Identifier(5859))); // 52
                    // println!("man {:?}", names.demangle(&Identifier(5918))); // 69
                    // println!("man {:?}", names.demangle(&Identifier(5987))); // 717
                    // println!("man {:?}", names.demangle(&Identifier(6020)));
                    // println!("man {:?}", names.demangle(&Identifier(6029)));
                    // println!("man {:?}", names.demangle(&Identifier(6038)));
                    // println!("man {:?}", names.demangle(&Identifier(6050)));
                    // panic!()
                } else {
                    continue;
                }

                for set in modules.iter() {
                    let start_time = SystemTime::now();
                    ctx = check_declaration_set(&ctx, set).unwrap();
                    let end_time = SystemTime::now();
                    let x = end_time.duration_since(start_time).unwrap();
                    println!("time: {}", x.as_secs_f64());
                }
            }
        }
    }
}
