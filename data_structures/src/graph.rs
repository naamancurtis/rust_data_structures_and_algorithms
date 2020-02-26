use crate::deque;
use crate::singly_linked_list::SinglyLinkedList;
use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

#[derive(Default)]
pub struct UndirectedGraph<'a, T>
where
    T: Eq + Hash,
{
    adjacency_list: HashMap<u64, Vec<u64>>,
    key_value_map: HashMap<u64, Node<'a, T>>,
}

#[derive(Hash, PartialEq, Eq)]
pub struct Node<'a, T>
where
    T: Eq + Hash,
{
    value: &'a T,
}

impl<'a, T> Node<'a, T>
where
    T: Hash + Eq,
{
    pub fn new(node: &'a T) -> Self {
        Self { value: node }
    }

    pub fn get_key(&self) -> u64 {
        get_key(&self)
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

    pub fn add_vertex(&mut self, value: &'a T) {
        let node = Node::new(value);
        let key = node.get_key();

        self.adjacency_list.entry(key).or_insert_with(Vec::new);
        self.key_value_map.entry(key).or_insert(node);
    }

    pub fn remove_vertex(&mut self, key: &T) -> Option<&T> {
        let key = get_key(key);
        let relations = self.adjacency_list.remove(&key);

        if let Some(relations) = relations {
            relations.iter().for_each(|relation_key| {
                if let Some(relation) = self.adjacency_list.get_mut(relation_key) {
                    relation.retain(|relation_key| *relation_key != key);
                }
            })
        }

        self.key_value_map.remove(&key).map(|node| node.value)
    }

    pub fn add_edge(&mut self, value_1: &T, value_2: &T) {
        let key1 = get_key(value_1);
        let key2 = get_key(value_2);

        if let Some(connected_to) = self.adjacency_list.get_mut(&key1) {
            connected_to.push(key2);
        }
        if let Some(connected_to) = self.adjacency_list.get_mut(&key2) {
            connected_to.push(key1);
        }
    }

    pub fn remove_edge(&mut self, value_1: &T, value_2: &T) {
        let key_1 = get_key(value_1);
        let key_2 = get_key(value_2);

        if let Some(relations) = self.adjacency_list.get_mut(&key_1) {
            relations.retain(|relation_key| *relation_key != key_2);
        }

        if let Some(relations) = self.adjacency_list.get_mut(&key_2) {
            relations.retain(|relation_key| *relation_key != key_1);
        }
    }

    pub fn has(&self, value: &T) -> bool {
        self.adjacency_list.contains_key(&get_key(value))
    }

    pub fn get_relations(&self, value: &T) -> Option<Vec<&T>> {
        match self.adjacency_list.get(&get_key(value)) {
            Some(relations) => relations
                .iter()
                .map(|key| self.key_value_map.get(key).map(|node| node.value))
                .collect(),
            None => None,
        }
    }

    fn _get_relations(&self, key: u64) -> Option<&Vec<u64>> {
        self.adjacency_list.get(&key)
    }

    pub fn can_traverse_to(&self, start: &T, finish: &T) -> bool {
        if self.adjacency_list.is_empty() {
            return false;
        }

        let start_key = get_key(start);
        let target = get_key(finish);

        let mut queue = deque![start_key];
        let mut visited = HashSet::new();
        visited.insert(start_key);

        while let Some(node) = queue.pop_front() {
            if let Some(relations) = self._get_relations(node) {
                for key in relations {
                    let key = *key;
                    if key == target {
                        return true;
                    }
                    if visited.contains(&key) {
                        continue;
                    }
                    visited.insert(key);
                    queue.push_back(key);
                }
            }
        }
        false
    }

    pub fn traverse_all_nodes(&self, start: &T) -> Vec<&T> {
        let mut result = Vec::new();
        if self.adjacency_list.is_empty() {
            return result;
        }

        let start = get_key(start);
        let mut visited = HashSet::new();

        let mut stack = SinglyLinkedList::new();

        // Add the start to the necessary structures
        stack.push(start);

        while let Some(next) = stack.pop() {
            if visited.contains(&next) {
                continue;
            }

            if let Some(relations) = self.adjacency_list.get(&next) {
                relations
                    .iter()
                    .filter(|key| !visited.contains(*key))
                    .for_each(|key| stack.push(*key));
                visited.insert(next);
            }

            if let Some(node) = self.key_value_map.get(&next) {
                result.push(node.value);
            }
        }
        result
    }
}

fn get_key<T>(node: &T) -> u64
where
    T: Eq + Hash,
{
    let mut hasher = DefaultHasher::new();
    node.hash(&mut hasher);
    hasher.finish()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_vertex_add_node() {
        let mut graph = UndirectedGraph::default();

        let str_1 = String::from("Key 1");
        let str_2 = String::from("Key 2");
        let str_3 = String::from("Key 3");

        graph.add_vertex(&str_1);
        graph.add_vertex(&str_2);
        graph.add_vertex(&str_3);

        graph.add_edge(&str_1, &str_2);
        graph.add_edge(&str_1, &str_3);

        let key_1 = get_key(&str_1);
        let key_2 = get_key(&str_2);
        let key_3 = get_key(&str_3);

        assert!(graph.adjacency_list.contains_key(&key_1));
        assert!(graph.adjacency_list.contains_key(&key_2));
        assert!(graph.adjacency_list.contains_key(&key_3));

        assert!(graph.adjacency_list.get(&key_1).unwrap().contains(&key_2));
        assert!(graph.adjacency_list.get(&key_1).unwrap().contains(&key_3));
        assert!(graph.adjacency_list.get(&key_2).unwrap().contains(&key_1));
        assert!(graph.adjacency_list.get(&key_3).unwrap().contains(&key_1));
    }

    #[test]
    fn has() {
        let mut graph = UndirectedGraph::default();

        let str_1 = String::from("Key 1");
        let str_2 = String::from("Key 2");
        let str_3 = String::from("Key 3");
        let str_4 = String::from("Key 4");

        graph.add_vertex(&str_1);
        graph.add_vertex(&str_2);
        graph.add_vertex(&str_3);

        assert!(graph.has(&str_1));
        assert!(graph.has(&str_2));
        assert!(graph.has(&str_3));
        assert!(!graph.has(&str_4));
    }

    #[test]
    fn get_relations() {
        let mut graph = UndirectedGraph::default();

        let str_1 = String::from("Key 1");
        let str_2 = String::from("Key 2");
        let str_3 = String::from("Key 3");

        graph.add_vertex(&str_1);
        graph.add_vertex(&str_2);
        graph.add_vertex(&str_3);

        graph.add_edge(&str_1, &str_2);
        graph.add_edge(&str_1, &str_3);

        let result = graph.get_relations(&str_1).unwrap();
        assert_eq!(result.len(), 2);
        assert!(result.contains(&&str_2));
        assert!(result.contains(&&str_3));

        let result = graph.get_relations(&str_2).unwrap();
        assert_eq!(result.len(), 1);
        assert!(result.contains(&&str_1));
    }

    #[test]
    fn remove_edge_and_vertex() {
        let mut graph = UndirectedGraph::default();

        let str_1 = String::from("Key 1");
        let str_2 = String::from("Key 2");
        let str_3 = String::from("Key 3");
        let str_4 = String::from("Key 4");

        graph.add_vertex(&str_1);
        graph.add_vertex(&str_2);
        graph.add_vertex(&str_3);
        graph.add_vertex(&str_4);

        graph.add_edge(&str_1, &str_2);
        graph.add_edge(&str_1, &str_3);
        graph.add_edge(&str_1, &str_4);

        assert!(graph.has(&str_1));
        assert!(graph.has(&str_2));
        assert!(graph.has(&str_3));
        assert!(graph.has(&str_4));

        assert_eq!(graph.get_relations(&str_1).unwrap().len(), 3);
        graph.remove_edge(&str_1, &str_3);
        assert_eq!(graph.get_relations(&str_1).unwrap().len(), 2);
        assert_eq!(graph.get_relations(&str_3).unwrap().len(), 0);

        let result = graph.remove_vertex(&str_1).unwrap();
        assert_eq!(&str_1, result);

        assert!(!graph.has(&str_1));
        assert_eq!(graph.get_relations(&str_2).unwrap().len(), 0);
        assert_eq!(graph.get_relations(&str_3).unwrap().len(), 0);
        assert_eq!(graph.get_relations(&str_4).unwrap().len(), 0);
    }

    #[test]
    fn can_traverse_to() {
        let mut graph = UndirectedGraph::default();

        let str_1 = String::from("Key 1");
        let str_2 = String::from("Key 2");
        let str_3 = String::from("Key 3");
        let str_4 = String::from("Key 4");

        graph.add_vertex(&str_1);
        graph.add_vertex(&str_2);
        graph.add_vertex(&str_3);
        graph.add_vertex(&str_4);

        graph.add_edge(&str_1, &str_2);
        graph.add_edge(&str_1, &str_3);
        graph.add_edge(&str_2, &str_4);

        assert!(graph.has(&str_1));
        assert!(graph.has(&str_2));
        assert!(graph.has(&str_3));
        assert!(graph.has(&str_4));

        assert!(graph.can_traverse_to(&str_1, &str_4));
        graph.remove_vertex(&str_2);
        assert!(!graph.can_traverse_to(&str_1, &str_4));
    }

    #[test]
    fn traverse_all_nodes() {
        let mut graph = UndirectedGraph::default();

        let str_1 = String::from("Key 1");
        let str_2 = String::from("Key 2");
        let str_3 = String::from("Key 3");
        let str_4 = String::from("Key 4");

        graph.add_vertex(&str_1);
        graph.add_vertex(&str_2);
        graph.add_vertex(&str_3);
        graph.add_vertex(&str_4);

        graph.add_edge(&str_1, &str_2);
        graph.add_edge(&str_1, &str_3);
        graph.add_edge(&str_2, &str_4);

        let result = graph.traverse_all_nodes(&str_1);
        let expected = vec![&str_1, &str_3, &str_2, &str_4];
        assert_eq!(result, expected);
    }
}
