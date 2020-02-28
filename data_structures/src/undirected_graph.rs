//! # Undirected Graph
//!
//! A structure that builds up an Adjacency List, based off the vertex and edges that are added to
//! it. Once the graph has been constructed it's possible to both traverse all nodes and find
//!  out if it's possible to traverse from one specific node to another (Maze solving).

use crate::deque;
use crate::singly_linked_list::SinglyLinkedList;
use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

/// # Undirected Graph
///
/// A wrapper around an underlying adjacency list. The type of the graph `UndirectedGraph<T>` is
/// constructable so long as `T` implements `Hash & Eq`. The graph does not consume any
/// values in it's creation, instead just holding a reference to them, as such any
/// data put into the graph must last at least as long as the graph itself.
///
/// # Examples
///
/// ```rust
/// use::data_structures::undirected_graph::UndirectedGraph;
///
/// let mut graph = UndirectedGraph::new();
///
/// let data_1 = 10;
/// let data_2 = 50;
/// let data_3 = 100;
/// let data_4 = 250;
/// let data_5 = 500;
///
/// // Add the vertexes
/// graph.add_vertex(&data_1);
/// graph.add_vertex(&data_2);
/// graph.add_vertex(&data_3);
/// graph.add_vertex(&data_4);
/// graph.add_vertex(&data_5);
///
/// // Add the edges
/// graph.add_edge(&data_1, &data_2);
/// graph.add_edge(&data_1, &data_3);
/// graph.add_edge(&data_2, &data_4);
/// graph.add_edge(&data_3, &data_5);
///
/// // Our graph can traverse from data 1 to data 5
/// // Path: Data 1 -> Data 3 -> Data 5
/// // So this should return true
/// // Is performed through a Breadth First Search
/// assert!(graph.can_traverse_to(&data_1, &data_5));
///
/// let expected = vec![&10, &100, &500, &50, &250];
///
/// // We can also traverse all nodes from the given start node
/// // This is implemented as a Post-Order Depth First Search
/// // So the path would be:
/// // Path: Data 1 -> Data 3 -> Data 5 -> Data 2 -> Data 4
/// assert_eq!(graph.traverse_all_nodes(&data_1), expected);
/// ```
///
/// More detailed example using non-primitive data structures
/// ```rust
/// use data_structures::undirected_graph::UndirectedGraph;
/// #[derive(Hash, PartialEq, Eq, Debug)]
/// struct City {
///     name: String,
///     population: u32,
///     airport: String,
///     country: String
/// }
///
/// let new_york = City {
///     name: "New York".to_string(),
///     population: 8_623_000,
///     airport: "JFK".to_string(),
///     country: "USA".to_string(),
/// };
///
/// let london = City {
///     name: "London".to_string(),
///     population: 8_900_000,
///     airport: "Heathrow".to_string(),
///     country: "UK".to_string(),
/// };
///
/// let hong_kong = City {
///     name: "Hong Kong".to_string(),
///     population: 7_392_000,
///     airport: "Hong Kong International".to_string(),
///     country: "China".to_string(),
/// };
///
/// let sydney = City {
///     name: "Sydney".to_string(),
///     population: 5_230_000,
///     airport: "Sydney".to_string(),
///     country: "Australia".to_string(),
/// };
///
/// let johannesburg = City {
///     name: "Johannesburg".to_string(),
///     population: 5_635_000,
///     airport: "O.R. Tambo International".to_string(),
///     country: "South Africa".to_string(),
/// };
///
/// let mut graph = UndirectedGraph::new();
/// graph.add_vertex(&new_york);
/// graph.add_vertex(&london);
/// graph.add_vertex(&hong_kong);
/// graph.add_vertex(&sydney);
/// graph.add_vertex(&johannesburg);
///
/// graph.add_edge(&new_york, &london);
/// graph.add_edge(&new_york, &hong_kong);
/// graph.add_edge(&london, &hong_kong);
/// graph.add_edge(&london, &johannesburg);
/// graph.add_edge(&hong_kong, &sydney);
/// graph.add_edge(&johannesburg, &sydney);
///
/// assert_eq!(graph.size(), 5);
///
/// assert_eq!(graph.get_relations(&sydney), Some(vec![&hong_kong, &johannesburg]));
/// assert!(graph.can_traverse_to(&new_york, &johannesburg));
///
/// graph.remove_edge(&london, &johannesburg);
/// assert_eq!(graph.get_relations(&london), Some(vec![&new_york, &hong_kong]));
///
/// assert_eq!(graph.remove_vertex(&hong_kong), Some(&hong_kong));
/// assert!(!graph.has(&hong_kong));
/// assert_eq!(graph.size(), 4);
///
/// // Now we've removed Hong Kong, along with the edge from Johannesburg to London
/// assert!(!graph.can_traverse_to(&new_york, &sydney));
/// assert!(graph.can_traverse_to(&johannesburg, &sydney));
/// ```
#[derive(Default)]
pub struct UndirectedGraph<'a, T>
where
    T: Eq + Hash,
{
    adjacency_list: HashMap<u64, Vec<u64>>,
    key_value_map: HashMap<u64, Node<'a, T>>,
}

#[derive(Hash, PartialEq, Eq)]
struct Node<'a, T>
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
    /// Constructs a new, empty `UndirectedGraph<T>`
    /// where `T: Eq + Hash`
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::undirected_graph::UndirectedGraph;
    ///
    /// let mut graph: UndirectedGraph<i32> = UndirectedGraph::new();
    /// assert_eq!(graph.size(), 0)
    /// ```
    pub fn new() -> Self {
        Self {
            adjacency_list: HashMap::new(),
            key_value_map: HashMap::new(),
        }
    }

    /// Returns the number of vertexes in the graph
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::undirected_graph::UndirectedGraph;
    ///
    /// let mut graph: UndirectedGraph<i32> = UndirectedGraph::new();
    /// assert_eq!(graph.size(), 0);
    ///
    /// graph.add_vertex(&50);
    /// assert_eq!(graph.size(), 1);
    /// ```
    pub fn size(&self) -> usize {
        self.adjacency_list.len()
    }

    /// Returns true if the graph is empty, false if it contains 1 or more vertexes
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::undirected_graph::UndirectedGraph;
    ///
    /// let mut graph: UndirectedGraph<i32> = UndirectedGraph::new();
    /// assert!(graph.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.adjacency_list.is_empty()
    }

    /// Adds a new vertex to the graph
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::undirected_graph::UndirectedGraph;
    ///
    /// let mut graph = UndirectedGraph::new();
    ///
    /// graph.add_vertex(&50);
    /// graph.add_vertex(&25);
    /// assert_eq!(graph.size(), 2);
    /// ```
    pub fn add_vertex(&mut self, value: &'a T) {
        let node = Node::new(value);
        let key = node.get_key();

        self.adjacency_list.entry(key).or_insert_with(Vec::new);
        self.key_value_map.entry(key).or_insert(node);
    }

    /// Removes a new vertex from the graph, returning an `Option<T>` if
    /// the vertex is found, `None` if it isn't.
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::undirected_graph::UndirectedGraph;
    ///
    /// let mut graph = UndirectedGraph::new();
    ///
    /// let data_1 = 50;
    /// let data_2 = 25;
    ///
    /// graph.add_vertex(&data_1);
    /// graph.add_vertex(&data_2);
    /// assert_eq!(graph.size(), 2);
    ///
    /// assert_eq!(graph.remove_vertex(&data_1), Some(&50));
    /// assert_eq!(graph.size(), 1)
    /// ```
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

    /// Adds a new edge between the two vertexes
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::undirected_graph::UndirectedGraph;
    ///
    /// let mut graph = UndirectedGraph::new();
    ///
    /// let data_1 = 50;
    /// let data_2 = 25;
    ///
    /// graph.add_vertex(&data_1);
    /// graph.add_vertex(&data_2);
    /// assert_eq!(graph.size(), 2);
    ///
    /// graph.add_edge(&data_1, &data_2);
    ///
    /// assert_eq!(graph.get_relations(&data_1), Some(vec![&data_2]));
    /// ```
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

    /// Adds removes an edge between two vertexes
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::undirected_graph::UndirectedGraph;
    ///
    /// let mut graph = UndirectedGraph::new();
    ///
    /// let data_1 = 50;
    /// let data_2 = 25;
    ///
    /// graph.add_vertex(&data_1);
    /// graph.add_vertex(&data_2);
    /// assert_eq!(graph.size(), 2);
    ///
    /// graph.add_edge(&data_1, &data_2);
    ///
    /// assert_eq!(graph.get_relations(&data_1), Some(vec![&data_2]));
    ///
    /// graph.remove_edge(&data_1, &data_2);
    /// assert_eq!(graph.get_relations(&data_1), Some(vec![]));
    /// ```
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

    /// Returns true if a value is in the adjacency list, false if it isn't
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::undirected_graph::UndirectedGraph;
    ///
    /// let mut graph = UndirectedGraph::new();
    ///
    /// let data_1 = 50;
    /// let data_2 = 25;
    /// let data_3 = 500;
    ///
    /// graph.add_vertex(&data_1);
    /// graph.add_vertex(&data_2);
    ///
    /// assert!(graph.has(&data_1));
    /// assert!(graph.has(&data_2));
    /// assert!(!graph.has(&data_3));
    /// ```
    pub fn has(&self, value: &T) -> bool {
        self.adjacency_list.contains_key(&get_key(value))
    }

    /// Returns all the relationships that the given value has. If no
    /// key is found `None` is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use data_structures::undirected_graph::UndirectedGraph;
    ///
    /// let mut graph = UndirectedGraph::new();
    ///
    /// let data_1 = 50;
    /// let data_2 = 25;
    /// let data_3 = 10;
    ///
    /// graph.add_vertex(&data_1);
    /// graph.add_vertex(&data_2);
    /// graph.add_vertex(&data_3);
    /// assert_eq!(graph.size(), 3);
    ///
    /// graph.add_edge(&data_1, &data_2);
    /// graph.add_edge(&data_1, &data_3);
    ///
    /// assert_eq!(graph.get_relations(&data_1), Some(vec![&data_2, &data_3]));
    /// ```
    pub fn get_relations(&self, value: &T) -> Option<Vec<&T>> {
        match self.adjacency_list.get(&get_key(value)) {
            Some(relations) => relations
                .iter()
                .map(|key| self.key_value_map.get(key).map(|node| node.value))
                .collect(),
            None => None,
        }
    }

    /// Private API to get the relations of a node by it's key as
    /// opposed to it's value
    fn _get_relations(&self, key: u64) -> Option<&Vec<u64>> {
        self.adjacency_list.get(&key)
    }

    /// Conducts a Breadth First Search to determine whether or not
    /// it is possible to traverse from the start node to the finish node in the
    /// given graph.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use data_structures::undirected_graph::UndirectedGraph;
    ///
    /// let mut graph = UndirectedGraph::new();
    ///
    /// let data_1 = 50;
    /// let data_2 = 25;
    /// let data_3 = 10;
    /// let data_4 = 100;
    ///
    /// graph.add_vertex(&data_1);
    /// graph.add_vertex(&data_2);
    /// graph.add_vertex(&data_3);
    /// graph.add_vertex(&data_4);
    /// assert_eq!(graph.size(), 4);
    ///
    /// graph.add_edge(&data_1, &data_2);
    /// graph.add_edge(&data_2, &data_3);
    /// graph.add_edge(&data_3, &data_4);
    ///
    /// assert!(graph.can_traverse_to(&data_1, &data_4));
    /// graph.remove_vertex(&data_3);
    /// assert!(!graph.can_traverse_to(&data_1, &data_4));
    /// ```
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

    /// Conducts a Post Order Depth First Search to traverse all nodes in the graph,
    /// returning a Vec<&T> in the order the nodes are visited. If the graph has no
    /// no nodes are in the graph an empty `Vec` is returned
    ///
    /// # Examples
    ///
    /// ```rust
    /// use data_structures::undirected_graph::UndirectedGraph;
    ///
    /// let mut graph = UndirectedGraph::new();
    ///
    /// let data_1 = 50;
    /// let data_2 = 25;
    /// let data_3 = 10;
    /// let data_4 = 100;
    ///
    /// graph.add_vertex(&data_1);
    /// graph.add_vertex(&data_2);
    /// graph.add_vertex(&data_3);
    /// graph.add_vertex(&data_4);
    /// assert_eq!(graph.size(), 4);
    ///
    /// graph.add_edge(&data_1, &data_2);
    /// graph.add_edge(&data_2, &data_3);
    /// graph.add_edge(&data_3, &data_4);
    ///
    /// assert_eq!(graph.traverse_all_nodes(&data_1), vec![&50, &25, &10, &100]);
    /// ```
    pub fn traverse_all_nodes(&self, start: &T) -> Vec<&T> {
        let mut result = Vec::new();
        if self.adjacency_list.is_empty() {
            return result;
        }

        let start = get_key(start);
        let mut visited = HashSet::new();

        let mut stack = SinglyLinkedList::new();

        // Depth first search pre-order
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
