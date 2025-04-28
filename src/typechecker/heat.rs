use crate::precise::term::Term;
use std::rc::Rc;

#[derive(Debug)]
struct Path {
    begin: Rc<Term>,
    end: Rc<Term>,
}

fn term_size(t: &Rc<Term>) -> usize {
    match t.as_ref() {
        Term::U => size_of::<Term>(),
        Term::Pair(fst, snd, _) => term_size(fst) + term_size(snd),
        Term::Con(_, v, _) => size_of::<Term>() + v.iter().map(|f| term_size(f)).sum::<usize>(),
        _ => panic!("NOT HIT ELEMENT"),
    }
}

pub struct PathIndex {
    paths: Vec<Path>,
}

impl PathIndex {
    pub fn new() -> PathIndex {
        PathIndex { paths: vec![] }
    }
    pub fn add(&mut self, p1: &Rc<Term>, p2: &Rc<Term>) {
        if self.paths.iter().find(|p| &p.begin == p1).is_some()
            && self.paths.iter().find(|p| &p.begin == p2).is_some()
        {
            return;
        }
        let (begin, end) = if term_size(p1) > term_size(p2) {
            (p1, p2)
        } else {
            (p2, p1)
        };
        let mut head = end.clone();
        for p in &self.paths {
            if end == &p.end || begin == &p.end || end == &p.begin || begin == &p.begin {
                head = p.end.clone();
            }
        }
        let mut new_target = if term_size(&head) > term_size(end) {
            end
        } else {
            &head
        };
        for p in &mut self.paths {
            if head == p.end {
                p.end = new_target.clone();
            }
        }
        self.paths.push(Path {
            begin: begin.clone(),
            end: new_target.clone(),
        });
        self.paths.push(Path {
            begin: end.clone(),
            end: new_target.clone(),
        });
        // println!("{:?}", self.paths);
    }

    pub fn find_optimal_form(&self, t: &Term) -> Option<Rc<Term>> {
        for p in &self.paths {
            if p.begin.as_ref() == t {
                // println!("COMP {:?}", t);
                return Some(p.end.clone());
            }
        }
        None
    }

    pub fn compact(&self, t: &Rc<Term>) -> Rc<Term> {
        match t.as_ref() {
            Term::Con(n, cs, m) => {
                // println!("COMPACT {:?} --> {:?}", t, self.find_optimal_form(t));

                let ccs = cs.iter().map(|f| self.compact(f)).collect();
                let ut = Term::Con(n.clone(), ccs, m.clone());
                if let Some(res) = self.find_optimal_form(&ut) {
                    res
                } else {
                    Rc::new(ut)
                }
            }
            _ => t.clone(),
        }
    }
}
