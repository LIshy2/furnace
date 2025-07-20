mod tests {
    use furnace::ctt::Identifier;
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
    use std::time::{Duration, SystemTime};

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
                panic!("ALREADY CHECKED");
            }
            a.insert(*name);

            println!("Checking def {:?}", self.demangler.demangle(name));
        }

        fn decl_check_finished(&self, _: &Identifier) {}
    }

    #[test]
    fn check_examples() {
        unsafe { backtrace_on_stack_overflow::enable() };

        let reader = ExampleModules;
        let entries = fs::read_dir("examples").unwrap();

        let mut durations = Vec::new();

        for entry in entries {
            let entry = entry.unwrap();
            let path = entry.path();

            println!("NEW FILE {:?}", path);

            if path.file_name().unwrap() == "univprop.fctt" {
                continue;
            }

            if path.is_file() && path.extension().map(|s| s == "fctt").unwrap_or(false) {
                let begin = SystemTime::now();

                let deps = resolver::module::build_module_dependencies(
                    &reader,
                    path.file_stem().unwrap().to_str().unwrap(),
                )
                .unwrap();

                let (modules, names) = resolve_modules(deps).unwrap();
                let modules = mark_erased(&modules);

                let mut ctx = TypeContext::new(Rc::new(FakeNotifier::new(names))).uncompacted();

                for set in modules.iter() {
                    ctx = check_declaration_set(&ctx, set).unwrap();
                }

                let end = SystemTime::now();

                durations.push((end.duration_since(begin).unwrap(), path))
            }
        }
        durations.sort_by_key(|(d, _)| *d);
        for (d, name) in durations {
            println!(".. {:?} - {:?}", name, d);
        }
    }
}
