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
        // unsafe { backtrace_on_stack_overflow::enable() };

        let reader = ExampleModules;
        let entries = fs::read_dir("examples").unwrap();

        let mut failed = vec![];

        for entry in entries {
            let entry = entry.unwrap();
            let path = entry.path();

            println!("NEW FILE {:?}", path);

            if path.file_name().unwrap() != "univprop.fctt"
                || path.file_name().unwrap() == "grothendieck.fctt"
                || path.file_name().unwrap() == "torsor.fctt"
                || path.file_name().unwrap() == "csystem.fctt"
            {
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

                println!("man 444 {:?}", names.demangle(&Identifier(444)));

                // println!("man 423 {:?}", names.demangle(&Identifier(423)));
                // println!("man 426 {:?}", names.demangle(&Identifier(426)));
                // println!("man 430 {:?}", names.demangle(&Identifier(430)));
                // panic!();
                // println!("man 4097 {:?}", names.demangle(&Identifier(4097)));
                // println!("man 1258 {:?}", names.demangle(&Identifier(1258)));
                // println!("man 1259 {:?}", names.demangle(&Identifier(1259)));
                // println!("man 1260 {:?}", names.demangle(&Identifier(1260)));
                // println!("man 1261 {:?}", names.demangle(&Identifier(1261)));
                // println!("man 1262 {:?}", names.demangle(&Identifier(1262)));
                // println!("man 1263 {:?}", names.demangle(&Identifier(1263)));
                // println!("man 2401 {:?}", names.demangle(&Identifier(2401)));
                // println!("man 2304 {:?}", names.demangle(&Identifier(2304)));
                // println!("man 2114 {:?}", names.demangle(&Identifier(2114)));
                // println!("man 2115 {:?}", names.demangle(&Identifier(2115)));
                // println!("man 2116 {:?}", names.demangle(&Identifier(2116)));
                // println!("man 2117 {:?}", names.demangle(&Identifier(2116)));
                // println!("man 2118 {:?}", names.demangle(&Identifier(2116)));
                // println!("man 2119 {:?}", names.demangle(&Identifier(2116)));
                // println!("man 2120 {:?}", names.demangle(&Identifier(2116)));
                // println!("man 2121 {:?}", names.demangle(&Identifier(2116)));
                // println!("man 2122 {:?}", names.demangle(&Identifier(2116)));
                // panic!();
                let mut ctx = TypeContext::new(Rc::new(FakeNotifier::new(names))).uncompacted();

                for set in modules.iter() {
                    match check_declaration_set(&ctx, set) {
                        Ok(new_ctx) => ctx = new_ctx,
                        Err(e) => {
                            panic!("{:?}", e);
                            failed.push(path);
                            break;
                        }
                    }
                }
            }
        }
        println!("failed {:?}", failed);
        assert!(failed.len() == 0)
    }
}
