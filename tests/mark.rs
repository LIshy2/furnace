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

    #[test]
    fn mark_examples() {
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
                mark_erased(&modules);
            }
        }
    }
}
