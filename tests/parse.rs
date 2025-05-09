mod tests {
    use furnace::parser;
    use std::fs;
    use std::io::Read;

    #[test]
    fn parse_examples() {
        let module_parser = parser::grammar::ModuleParser::new();
        let entries = fs::read_dir("examples").unwrap();

        for entry in entries {
            let entry = entry.unwrap();
            let path = entry.path();

            if path.is_file() && path.extension().map(|s| s == "fctt").unwrap_or(false) {
                let mut file = fs::File::open(&path).unwrap();
                let mut content = String::new();
                file.read_to_string(&mut content).unwrap();
                let file_name = path.file_name().unwrap().to_str().unwrap();
                println!("Parsing... {}", file_name);
                module_parser
                    .parse(&content)
                    .unwrap_or_else(|_| panic!("UNPARSED {}", path.display()));
            }
        }
    }
}
