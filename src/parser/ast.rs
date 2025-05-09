pub type AIdent = String;

pub struct Module {
    pub name: AIdent,
    pub imports: Vec<Import>,
    pub decls: Vec<Decl>,
}

pub struct Import {
    pub name: String,
}
pub struct Tele {
    pub ids: Vec<AIdent>,
    pub tpe: Box<Term>,
}

pub struct PTele {
    pub id: Box<Term>,
    pub tpe: Box<Term>,
}

pub enum Label {
    OLabel(AIdent, Vec<Tele>),
    PLabel(AIdent, Vec<Tele>, Vec<AIdent>, System),
}

pub enum Decl {
    Def(AIdent, Vec<Tele>, Box<Term>, Box<Term>),
    Data(AIdent, Vec<Tele>, Vec<Label>),
    HData(AIdent, Vec<Tele>, Vec<Label>),
    Split(AIdent, Vec<Tele>, Box<Term>, Vec<Branch>),
    Undef(AIdent, Vec<Tele>, Box<Term>),
    Mutual(Vec<Decl>),
    Opaque(AIdent),
    Transparent(AIdent),
    TransparentAll,
}

pub enum Branch {
    OBranch(AIdent, Vec<AIdent>, Box<Term>),
    PBranch(AIdent, Vec<AIdent>, Vec<AIdent>, Box<Term>),
}

pub enum Term {
    Where(Box<Term>, Vec<Decl>),
    Let(Vec<Decl>, Box<Term>),
    Lam(Vec<PTele>, Box<Term>),
    PLam(Vec<AIdent>, Box<Term>),
    Split(Box<Term>, Vec<Branch>),
    Fun(Box<Term>, Box<Term>),
    Pi(Vec<PTele>, Box<Term>),
    Sigma(Vec<PTele>, Box<Term>),
    AppFormula(Box<Term>, Box<Formula>),
    App(Box<Term>, Box<Term>),
    PathP(Box<Term>, Box<Term>, Box<Term>),
    Comp(Box<Term>, Box<Term>, System),
    HComp(Box<Term>, Box<Term>, System),
    Trans(Box<Term>, Box<Term>),
    Fill(Box<Term>, Box<Term>, System),
    Glue(Box<Term>, System),
    GlueElem(Box<Term>, System),
    UnGlueElem(Box<Term>, System),
    Id(Box<Term>, Box<Term>, Box<Term>),
    IdPair(Box<Term>, System),
    IdJ(
        Box<Term>,
        Box<Term>,
        Box<Term>,
        Box<Term>,
        Box<Term>,
        Box<Term>,
    ),
    Fst(Box<Term>),
    Snd(Box<Term>),
    Pair(Box<Term>, Vec<Box<Term>>),
    Var(AIdent),
    PCon(AIdent, Box<Term>),
    U,
    Hole,
}

pub enum Dir {
    Zero,
    One,
}

pub struct System(pub Vec<Side>);

pub struct Face {
    pub id: AIdent,
    pub dir: Dir,
}

pub struct Side {
    pub faces: Vec<Face>,
    pub exp: Box<Term>,
}

pub enum Formula {
    Dir(Dir),
    Atom(AIdent),
    Neg(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
}
