use crate::ctt::term::Identifier;
use std::collections::HashMap;

#[derive(Copy, Clone, Debug)]
pub enum Tag {
    Var(usize),
    Precise,
}

pub struct PreciseContext {
    subs: HashMap<usize, Tag>,
    binds: HashMap<Identifier, Tag>,
    last_id: usize,
}

impl Default for PreciseContext {
    fn default() -> Self {
        Self::new()
    }
}

impl PreciseContext {
    pub fn new() -> PreciseContext {
        PreciseContext {
            subs: HashMap::from([(0, Tag::Var(0))]),
            binds: Default::default(),
            last_id: 1,
        }
    }
    pub fn fresh(&mut self) -> Tag {
        self.last_id += 1;
        self.subs.insert(self.last_id, Tag::Var(self.last_id));
        Tag::Var(self.last_id)
    }

    pub fn get(&self, name: &Identifier) -> Tag {
        // println!("{:?}", name);
        self.binds
            .get(name)
            .expect(&format!("unfound {:?}", name))
            .clone()
    }

    pub fn add(&mut self, n: &Identifier, t: Tag) {
        self.binds.insert(*n, t);
    }

    pub fn apply(&self, t: &Tag) -> Tag {
        match t {
            Tag::Var(name) => {
                // println!("{:?}", name);
                let s = &self
                    .subs
                    .get(name)
                    .expect(&format!("unfound {}", name))
                    .clone();
                if let Tag::Var(next_name) = &s {
                    if next_name == name {
                        s.clone()
                    } else {
                        self.apply(s)
                    }
                } else {
                    self.apply(s)
                }
            }
            Tag::Precise => Tag::Precise,
        }
    }

    pub fn unify(&mut self, t1: &Tag, t2: &Tag) {
        let t1 = self.apply(t1);
        let t2 = self.apply(t2);
        match (&t1, &t2) {
            (Tag::Var(name1), Tag::Var(name2)) if name1 == name2 => (),
            (Tag::Precise, Tag::Precise) => (),
            (Tag::Var(name), _) => {
                self.subs.insert(*name, t2.clone());
            }

            (_, Tag::Var(name)) => {
                self.subs.insert(*name, t1.clone());
            }
        }
    }
}
