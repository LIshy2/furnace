pub mod ast;

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub cubicaltt, "/parser/cubicaltt.rs");

mod tests {
    use crate::parser::cubicaltt;
    #[test]
    fn decl() {
        cubicaltt::DeclParser::new()
            .parse("isAssociative (M : U) (op : M -> M -> M) : U = (a b c : M) -> Path M (op a (op b c)) (op (op a b) c)").unwrap();
    }

    #[test]
    fn module() {
        cubicaltt::ModuleParser::new()
            .parse(
                "module idtypes where { import sigma; import univalence a = a }",
            )
            .unwrap();
    }
    #[test]
    fn system() {
        cubicaltt::SystemParser::new()
            .parse(
                "[-> a]"
            ).unwrap();
    }
    
}
