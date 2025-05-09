use crate::ctt::term::Identifier;
use std::collections::HashMap;

pub struct Constraints {
    subs: HashMap<usize, SimpleType>,
    binds: HashMap<Identifier, SimpleType>,
    last_id: usize,
}

#[derive(Clone, Debug)]
pub enum SimpleType {
    Var(usize),
    Strict,
    Fun(Box<SimpleType>, Box<SimpleType>),
}

impl Default for Constraints {
    fn default() -> Self {
        Self::new()
    }
}

impl Constraints {
    pub fn new() -> Constraints {
        Constraints {
            subs: Default::default(),
            binds: Default::default(),
            last_id: 0,
        }
    }
    pub fn fresh(&mut self) -> SimpleType {
        self.last_id += 1;
        self.subs
            .insert(self.last_id, SimpleType::Var(self.last_id));
        SimpleType::Var(self.last_id)
    }

    pub fn get(&self, name: &Identifier) -> SimpleType {
        self.binds[name].clone()
    }

    pub fn add(&mut self, n: &Identifier, t: SimpleType) {
        self.binds.insert(*n, t);
    }

    pub fn apply(&self, t: &SimpleType) -> SimpleType {
        match t {
            SimpleType::Var(name) => {
                let s = &self.subs[name].clone();
                if let SimpleType::Var(next_name) = &s {
                    if next_name == name {
                        s.clone()
                    } else {
                        self.apply(s)
                    }
                } else {
                    self.apply(s)
                }
            }
            SimpleType::Strict => SimpleType::Strict,
            SimpleType::Fun(a, r) => {
                SimpleType::Fun(Box::new(self.apply(a)), Box::new(self.apply(r)))
            }
        }
    }

    pub fn unify(&mut self, t1: &SimpleType, t2: &SimpleType) {
        let t1 = self.apply(t1);
        let t2 = self.apply(t2);
        match (&t1, &t2) {
            (SimpleType::Var(name1), SimpleType::Var(name2)) if name1 == name2 => (),
            (SimpleType::Strict, SimpleType::Strict) => (),
            (SimpleType::Strict, SimpleType::Fun(_, _)) => (),
            (SimpleType::Fun(_, _), SimpleType::Strict) => (),
            (SimpleType::Var(name), _) => {
                self.subs.insert(*name, t2.clone());
            }

            (_, SimpleType::Var(name)) => {
                self.subs.insert(*name, t1.clone());
            }
            (SimpleType::Fun(in1, out1), SimpleType::Fun(in2, out2)) => {
                self.unify(in1.as_ref(), in2.as_ref());
                self.unify(out1.as_ref(), out2.as_ref());
            }
            _ => panic!("UAAAA {:?} {:?}", t1, t2),
        }
    }
}
