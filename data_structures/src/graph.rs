use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

#[derive(Default)]
pub struct UndirectedGraph<'a, T>
where
    T: Eq + Hash,
{
    adjacency_list: HashMap<u64, Vec<u64>>,
    key_value_map: HashMap<u64, &'a Node<T>>,
}

#[derive(Default, Hash, PartialEq, Eq)]
pub struct Node<T>
where
    T: Eq + Hash,
{
    value: T,
}

impl<T> Node<T>
where
    T: Hash + Eq,
{
    pub fn new(node: T) -> Self {
        Self { value: node }
    }

    pub fn get_key(&self) -> u64 {
        let mut hasher = DefaultHasher::new();
        self.hash(&mut hasher);
        hasher.finish()
    }
}

impl<'a, T> UndirectedGraph<'a, T>
where
    T: Eq + Hash,
{
    pub fn new() -> Self {
        Self {
            adjacency_list: HashMap::new(),
            key_value_map: HashMap::new(),
        }
    }

    pub fn add_vertex(&mut self, node: &'a Node<T>) {
        let key = node.get_key();
        self.adjacency_list.entry(key).or_insert(Vec::new());
        self.key_value_map.entry(key).or_insert(node);
    }
}
