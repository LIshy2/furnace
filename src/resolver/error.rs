#[derive(Clone, Debug)]
pub enum ResolveError {
    Duplicate(String),
    UnresolvedVar(String),
    UnresolvedName(String),
    UnsupportedDeclaration,
    RecursiveImports(String, String),
}
