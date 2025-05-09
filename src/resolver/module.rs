use crate::ctt;
use crate::ctt::term::DeclarationSet;
use crate::parser::ast;
use crate::resolver::context::ResolveContext;
use crate::resolver::declaration::resolve_declarations;
use crate::resolver::error::ResolveError;
use std::collections::HashMap;

pub fn resolve_module(
    ctx: ResolveContext,
    module: ast::Module,
) -> Result<(Vec<DeclarationSet<ctt::term::Term<()>>>, ResolveContext), ResolveError> {
    let (decls, ctx) = resolve_declarations(ctx, module.decls)?;
    Ok((decls, ctx))
}

pub fn resolve_modules(
    modules: Vec<ast::Module>,
) -> Result<(Vec<DeclarationSet<ctt::term::Term<()>>>, ResolveContext), ResolveError> {
    let mut ctx = ResolveContext::new();
    Ok((
        modules
            .into_iter()
            .map(|md| {
                let (decls, new_ctx) = resolve_module(ctx.clone(), md)?;
                ctx = new_ctx;
                Ok(decls)
            })
            .collect::<Result<Vec<Vec<DeclarationSet<ctt::term::Term<()>>>>, ResolveError>>()?
            .into_iter()
            .flatten()
            .collect(),
        ctx,
    ))
}

pub trait ModuleReader {
    fn read_module(&self, name: &str) -> ast::Module;
}

enum Status {
    Was,
    Depends,
}

pub fn build_module_dependencies(
    reader: &impl ModuleReader,
    module_name: &str,
) -> Result<Vec<ast::Module>, ResolveError> {
    fn dfs(
        reader: &impl ModuleReader,
        md: String,
        was: &mut HashMap<String, Status>,
        modules: &mut Vec<ast::Module>,
    ) -> Result<(), ResolveError> {
        was.insert(md.clone(), Status::Depends);
        let module = reader.read_module(&md);
        for import in &module.imports {
            let k = import.name.as_str();
            match was.get(k) {
                None => dfs(reader, import.name.clone(), was, modules)?,
                Some(Status::Depends) => {
                    Err(ResolveError::RecursiveImports(k.to_string(), md.clone()))?
                }
                Some(Status::Was) => {}
            }
        }
        was.insert(md, Status::Was);
        modules.push(module);
        Ok(())
    }
    let mut result = vec![];
    dfs(
        reader,
        module_name.to_string(),
        &mut HashMap::new(),
        &mut result,
    )?;
    Ok(result)
}
