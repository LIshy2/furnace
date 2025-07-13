use std::{
    collections::{hash_map::IntoIter, HashMap},
    hash::{Hash, Hasher},
    ops::Index,
    rc::Rc,
};

use crate::ctt::{formula::Dir, Identifier};

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Face {
    pub binds: HashMap<Identifier, Dir>,
}

impl Face {
    pub fn cond(name: &Identifier, dir: Dir) -> Face {
        Face {
            binds: HashMap::from([(*name, dir)]),
        }
    }

    pub fn eps() -> Face {
        Face {
            binds: HashMap::new(),
        }
    }

    pub fn domain(&self) -> Vec<Identifier> {
        self.binds.keys().copied().collect()
    }

    pub fn compatible(&self, other: &Face) -> bool {
        for (int, dir) in self.binds.iter() {
            if let Some(other_v) = other.binds.get(int) {
                if dir != other_v {
                    return false;
                }
            }
        }
        true
    }

    pub fn removed(&self, i: &Identifier) -> Face {
        let mut result = self.clone();
        result.binds.remove(i);
        result
    }

    pub fn meet(&self, other: &Face) -> Face {
        let mut result = Face::eps();
        for (i, d1) in &self.binds {
            if let Some(d2) = other.binds.get(i) {
                if d2 != d1 {
                    panic!("faces incompatible")
                }
            }
            result.binds.insert(*i, d1.clone());
        }
        for (i, d2) in &other.binds {
            if !self.binds.contains_key(i) {
                result.binds.insert(*i, d2.clone());
            }
        }

        result
    }

    pub fn minus(&self, other: &Face) -> Face {
        let mut result = self.clone();
        for k in other.binds.keys() {
            result.binds.remove(k);
        }
        result
    }

    pub fn leq(&self, other: &Face) -> bool {
        for (b, d1) in &other.binds {
            if let Some(d2) = self.binds.get(b) {
                if d1 != d2 {
                    return false;
                }
            } else {
                return false;
            }
        }
        return true;
    }
}

impl Hash for Face {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut entries = self.binds.iter().collect::<Vec<_>>();
        entries.sort_by(|a, b| a.0.cmp(b.0));

        for (k, v) in entries {
            k.hash(state);
            v.hash(state);
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct System<A> {
    binds: HashMap<Face, A>,
}

impl<A: Clone> System<A> {
    pub fn empty() -> System<A> {
        System {
            binds: HashMap::new(),
        }
    }

    pub fn domain(&self) -> Vec<Identifier> {
        self.binds.iter().flat_map(|(f, _)| f.domain()).collect()
    }

    pub fn insert(&self, alpha: Face, bind: A) -> System<A> {
        let mut result = self.clone();
        if !result.binds.iter().any(|(beta, _)| alpha.leq(beta)) {
            result.binds = result
                .binds
                .into_iter()
                .filter(|(gamma, _)| !gamma.leq(&alpha))
                .map(|(f, a)| (f.clone(), a))
                .collect();
            result.binds.insert(alpha, bind);
        }
        result
    }

    pub fn get(&self, face: &Face) -> Option<&A> {
        self.binds.get(face)
    }

    pub fn contains(&self, face: &Face) -> bool {
        self.binds.contains_key(face)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Face, &A)> {
        self.binds.iter()
    }

    pub fn values(&self) -> impl Iterator<Item = &A> {
        self.binds.values()
    }

    pub fn len(&self) -> usize {
        self.binds.len()
    }

    pub fn intersect<'a, B>(&'a self, other: &'a System<B>) -> SystemIntersect<'a, A, B> {
        SystemIntersect {
            iter: intersect(&self.binds, &other.binds).into_iter(),
        }
    }
}

impl<A: Clone> From<HashMap<Face, A>> for System<A> {
    fn from(value: HashMap<Face, A>) -> Self {
        let mut result = System::empty();
        for (alpha, v) in value {
            result = result.insert(alpha, v)
        }
        result
    }
}

impl<A> Index<&Face> for System<A> {
    type Output = A;

    fn index(&self, index: &Face) -> &Self::Output {
        &self.binds[index]
    }
}

impl<A: Clone> FromIterator<(Face, A)> for System<A> {
    fn from_iter<T: IntoIterator<Item = (Face, A)>>(iter: T) -> Self {
        System::from(HashMap::from_iter(iter))
    }
}

pub struct SystemIntersect<'a, A, B> {
    iter: IntoIter<&'a Face, (&'a A, &'a B)>,
}

impl<'a, A, B> Iterator for SystemIntersect<'a, A, B> {
    type Item = (&'a Face, (&'a A, &'a B));

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

pub fn intersect<'l, 'r, A, B, C>(
    left: &'l HashMap<A, B>,
    right: &'r HashMap<A, C>,
) -> HashMap<&'l A, (&'l B, &'r C)>
where
    A: Hash,
    A: Eq,
{
    let mut result = HashMap::new();
    for (k, v1) in left {
        if let Some(v2) = right.get(k) {
            result.insert(k, (v1, v2));
        }
    }
    result
}
