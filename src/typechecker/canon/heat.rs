use crate::precise::term::Value;
use std::rc::Rc;

#[derive(Debug)]
struct Path {
    begin: Rc<Value>,
    end: Rc<Value>,
}

fn term_size(t: &Rc<Value>) -> usize {
    match t.as_ref() {
        Value::U => size_of::<Value>(),
        Value::Pair(fst, snd, _) => term_size(fst) + term_size(snd),
        Value::Con(_, v, _) => size_of::<Value>() + v.iter().map(term_size).sum::<usize>(),
        _ => panic!("NOT HIT ELEMENT"),
    }
}

pub struct PathIndex {
    paths: Vec<Path>,
}

impl Default for PathIndex {
    fn default() -> Self {
        Self::new()
    }
}

impl PathIndex {
    pub fn new() -> PathIndex {
        PathIndex { paths: vec![] }
    }
    pub fn add(&mut self, p1: &Rc<Value>, p2: &Rc<Value>) {
        if self.paths.iter().any(|p| &p.begin == p1) && self.paths.iter().any(|p| &p.begin == p2) {
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
        let new_target = if term_size(&head) > term_size(end) {
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
    }

    pub fn find_optimal_form(&self, t: &Value) -> Option<Rc<Value>> {
        for p in &self.paths {
            if p.begin.as_ref() == t {
                return Some(p.end.clone());
            }
        }
        None
    }

    pub fn compact(&self, t: &Rc<Value>) -> Rc<Value> {
        match t.as_ref() {
            Value::Con(n, cs, m) => {
                let ccs = cs.iter().map(|f| self.compact(f)).collect();
                let ut = Value::Con(*n, ccs, m.clone());
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
