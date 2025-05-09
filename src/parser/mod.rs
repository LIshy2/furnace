pub mod ast;

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub grammar, "/parser/grammar.rs");

mod tests {
    use crate::parser::grammar;
    #[test]
    fn decl() {
        grammar::DeclParser::new()
            .parse("isAssociative (M : U) (op : M -> M -> M) : U = (a b c : M) -> Path M (op a (op b c)) (op (op a b) c)").unwrap();
    }

    #[test]
    fn module() {
        grammar::ModuleParser::new()
            .parse("module idtypes where { import sigma; import univalence a: U = a }")
            .unwrap();
    }
    #[test]
    fn system() {
        grammar::SystemParser::new().parse("[-> a]").unwrap();
    }
}
