use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
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

    pub fn remove_vertex(&mut self, key: &'a T) -> Option<&T> {
        let key = get_key(key);
        let relations = self.adjacency_list.remove(&key);

        relations.map(|relations| {
            relations.iter().for_each(|relation_key| {
                self.adjacency_list.get_mut(relation_key).map(|relation| {
                    relation.retain(|relation_key| *relation_key != key);
                });
            })
        });

        self.key_value_map.remove(&key).map(|node| node.value)
    }

    pub fn add_edge(&mut self, value_1: &'a T, value_2: &'a T) {
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

        self.adjacency_list
            .get_mut(&key_1)
            .map(|relations| relations.retain(|relation_key| *relation_key != key_2));

        self.adjacency_list
            .get_mut(&key_2)
            .map(|relations| relations.retain(|relation_key| *relation_key != key_1));
    }

    pub fn has(&self, value: &'a T) -> bool {
        self.adjacency_list.contains_key(&get_key(value))
    }

    pub fn get_relations(&self, value: &'a T) -> Option<Vec<&T>> {
        match self.adjacency_list.get(&get_key(value)) {
            Some(relations) => relations
                .iter()
                .map(|key| self.key_value_map.get(key).map(|node| node.value))
                .collect(),
            None => None,
        }
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
}
