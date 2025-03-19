use furnace::parser;

mod tests {
    use std::fs;
    use std::io::Read;
    use furnace::parser;
    
    #[test]
    fn parse_examples() {
        let module_parser = parser::cubicaltt::ModuleParser::new();
        let entries = fs::read_dir("examples").unwrap();

        for entry in entries {
            let entry = entry.unwrap();
            let path = entry.path();

            if path.is_file() && path.extension().map(|s| s == "fctt").unwrap_or(false) {
                let mut file = fs::File::open(&path).unwrap();
                let mut content = String::new();
                file.read_to_string(&mut content).unwrap();
                let file_name = path.file_name().unwrap().to_str().unwrap();
                print!("Parsing... {}\n", file_name);
                module_parser.parse(&content).expect(&format!("UNPARSED {}", path.display()));
            }
        }
    }
}