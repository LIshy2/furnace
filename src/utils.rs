use std::collections::HashMap;
use std::hash::Hash;

use rpds::HashTrieMap;

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
