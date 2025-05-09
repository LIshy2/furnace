mod tests {
    use furnace::parser;
    use furnace::parser::ast::Module;
    use furnace::resolver;
    use furnace::resolver::module::{resolve_modules, ModuleReader};
    use std::fs;
    use std::io::Read;

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

    #[test]
    fn resolve_examples() {
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

                resolve_modules(deps).unwrap();
            }
        }
    }
}
