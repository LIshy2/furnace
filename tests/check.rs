mod tests {
    use furnace::resolver::context::Demangler;
    use furnace::parser;
    use furnace::parser::ast::Module;
    use furnace::resolver;
    use furnace::resolver::module::{resolve_modules, ModuleReader};
    use furnace::typechecker::check::check_declaration_set;
    use furnace::typechecker::context::TypeContext;
    use std::fs;
    use std::io::Read;
    use std::time::SystemTime;
    use furnace::ctt::term::System;

    struct ExampleModules;
    impl ModuleReader for ExampleModules {
        fn read_module(&self, name: &str) -> Module {
            let module_parser = parser::grammar::ModuleParser::new();
            print!("Loading... examples/{}.fctt\n", name);
            let mut file = fs::File::open(format!("examples/{}.fctt", name)).unwrap();
            let mut content = String::new();
            file.read_to_string(&mut content).unwrap();
            module_parser.parse(&content).expect("parse error")
        }
    }

    #[test]
    fn check_examples() {
        let reader = ExampleModules;
        let entries = fs::read_dir("examples").unwrap();

        for entry in entries {
            let entry = entry.unwrap();
            let path = entry.path();

            if path.is_file() && path.extension().map(|s| s == "fctt").unwrap_or(false) {
                let deps = resolver::module::build_module_dependencies(
                    &reader,
                    path.file_stem().unwrap().to_str().unwrap(),
                )
                    .unwrap();

                let (modules, names) = resolve_modules(deps).unwrap();
                let mut ctx = TypeContext::new();

                println!("man {}", names.demangle(&276));

                for set in modules.iter() {
                    let start_time = SystemTime::now();
                    ctx = check_declaration_set(ctx, set).unwrap();
                    let end_time = SystemTime::now();
                    let x = end_time.duration_since(start_time).unwrap();
                    println!("time: {}", x.as_secs_f64());
                }
            }
        }
    }
}
