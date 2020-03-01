//! # Graph
//!
//! A weighted and directed graph that builds up an Adjacency List, based off the vertex and edges that are added to
//! it. Once the graph has been constructed various methods are offered to traverse the graph, including:
//! - Retrieving the relationships for a given node
//! - Traversing the entire structure from a starting node
//! - Establishing whether it is possible to get from one node to another
//! - Dijkstra's Shortest Path Algorithm
//!
//! ## Notes on Lifetimes
//! The graph does not consume any values, therefore the values that are being used to construct
//! the graph (lets call it `'a` for this example) must live at least as long as the graph itself
//! (`'b`), so `'a > 'b`.
//!
//! # Examples
//!
//! As a sample use case below, we'll look at finding the cheapest path between two cities, using
//! the price of airline tickets as the weighting for each edge.
//!
//! ```rust
//! use data_structures::graph::Graph;
//!
//! #[derive(Hash, PartialEq, Eq, Debug)]
//! struct City {
//!     name: String,
//!     population: u32,
//!     airport: String,
//!     country: String
//! }
//!
//! // Set up our data for each Vertex of the graph
//! let new_york = City {
//!     name: "New York".to_string(),
//!     population: 8_623_000,
//!     airport: "JFK".to_string(),
//!     country: "USA".to_string(),
//! };
//!
//! let san_francisco = City {
//!     name: "San Francisco".to_string(),
//!     population: 884_363,
//!     airport: "San Francisco International".to_string(),
//!     country: "USA".to_string(),
//! };
//!
//! let london = City {
//!     name: "London".to_string(),
//!     population: 8_900_000,
//!     airport: "Heathrow".to_string(),
//!     country: "UK".to_string(),
//! };
//!
//! let hong_kong = City {
//!     name: "Hong Kong".to_string(),
//!     population: 7_392_000,
//!     airport: "Hong Kong International".to_string(),
//!     country: "China".to_string(),
//! };
//!
//! let singapore = City {
//!     name: "Singapore".to_string(),
//!     population: 5_612_000,
//!     airport: "Singapore Changi".to_string(),
//!     country: "Singapore".to_string(),
//! };
//!
//! let sydney = City {
//!     name: "Sydney".to_string(),
//!     population: 5_230_000,
//!     airport: "Sydney".to_string(),
//!     country: "Australia".to_string(),
//! };
//!
//! let johannesburg = City {
//!     name: "Johannesburg".to_string(),
//!     population: 5_635_000,
//!     airport: "O.R. Tambo International".to_string(),
//!     country: "South Africa".to_string(),
//! };
//!
//! let mut graph = Graph::new();
//!
//! // Add the vertexes to the graph
//! graph.add_vertex(&new_york);
//! graph.add_vertex(&san_francisco);
//! graph.add_vertex(&singapore);
//! graph.add_vertex(&london);
//! graph.add_vertex(&hong_kong);
//! graph.add_vertex(&sydney);
//! graph.add_vertex(&johannesburg);
//!
//! // Adding the price of flights between each airport
//! graph.add_undirected_edge(&new_york, &london, 225);
//! graph.add_undirected_edge(&new_york, &san_francisco, 154);
//! graph.add_directed_edge(&new_york, &johannesburg, 431);
//!
//! graph.add_undirected_edge(&london, &hong_kong, 391);
//! graph.add_undirected_edge(&london, &johannesburg, 823);
//! graph.add_undirected_edge(&london, &san_francisco, 391);
//! graph.add_undirected_edge(&london, &singapore, 447);
//!
//! graph.add_directed_edge(&hong_kong, &new_york, 624);
//! graph.add_undirected_edge(&hong_kong, &sydney, 494);
//! graph.add_directed_edge(&hong_kong, &san_francisco, 565);
//! graph.add_undirected_edge(&hong_kong, &singapore, 123);
//!
//! graph.add_directed_edge(&johannesburg, &sydney, 820);
//! graph.add_undirected_edge(&sydney, &san_francisco, 447);
//!
//! assert_eq!(graph.size(), 7);
//!
//! // We can find out what vertices are connected to a given vertex
//! assert_eq!(
//!     graph.get_relations(&hong_kong),
//!     Some(vec![&london, &new_york, &sydney, &san_francisco, &singapore])
//! );
//!
//! // We can also see if it's possible to traverse between two vertices
//! // This uses a breadth first search to traverse the graph
//! assert!(graph.can_traverse_to(&new_york, &johannesburg));
//!
//! // However, given the 1 way connection we've added, although Hong Kong is connected to New York,
//! // New York isn't connected to Hong Kong
//! assert_eq!(
//!     graph.get_relations(&new_york),
//!     Some(vec![&london, &san_francisco, &johannesburg])
//! );
//!
//! // We can also find the shortest path given the weighting we've added to the graph
//! // (in this example, the price of the airline tickets)
//! //
//! // With this specific implementation, as you're able to add custom weightings to the graph,
//! // you need to specify the "Zero value" for the weighting while calling Dijkstra's,
//! // in this case it would be $0.
//! //
//! // The result contains the vertices in the shortest path, and the total weight of the path
//! // ie. the airports we would fly through, and the total cost of the trip
//! assert_eq!(
//!     graph.dijkstras_shortest_path(&new_york, &hong_kong, 0),
//!     Some((vec![&new_york, &london, &hong_kong], 616))
//! );
//!
//! assert_eq!(
//!     graph.dijkstras_shortest_path(&sydney, &johannesburg, 0),
//!     Some((vec![&sydney, &san_francisco, &new_york, &johannesburg], 1032))
//! );
//!
//! // We can remove an entire vertex, which automatically removes all relationships
//! assert_eq!(graph.remove_vertex(&london), Some(&london));
//! assert!(!graph.has(&london));
//! assert_eq!(graph.size(), 6);
//!
//! // We can also remove individual edges (relationships) within the graph
//! graph.remove_edge(&san_francisco, &sydney);
//! graph.remove_edge(&hong_kong, &sydney);
//!
//! // Now we've removed London completely and the routes:
//! // - San Francisco <-> Sydney
//! // - Hong Kong <-> Sydney
//! // We are able to fly from `Johannesburg -> Sydney`, but not from `Sydney -> Johannesburg`
//!
//! // We can either check if the graph is traversable
//! assert!(!graph.can_traverse_to(&sydney, &johannesburg));
//! assert!(graph.can_traverse_to(&johannesburg, &sydney));
//!
//! // Or we can attempt to find the shortest path, as there isn't one, `None` is returned
//! assert_eq!(
//!     graph.dijkstras_shortest_path(&sydney, &johannesburg, 0),
//!     None
//! );
//! ```

use crate::deque;
use crate::singly_linked_list::SinglyLinkedList;
use std::cmp::Ordering;
use std::collections::hash_map::DefaultHasher;
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::ops::Add;

/// Helper method for retrieving the hash of a reference to a value
fn get_key<T>(node: &T) -> u64
where
    T: PartialEq + Hash,
{
    let mut hasher = DefaultHasher::new();
    node.hash(&mut hasher);
    hasher.finish()
}

/// # Graph
///
/// A wrapper around an underlying adjacency list. The type of the graph `Graph<T, W>` is
/// constructable so long as `T` _(The underlying type of each vertex)_ implements `Hash & Eq` and
/// `W` the weighting for each Edge implements `PartialOrd + PartialEq`.
/// The graph does not consume any values in it's creation, instead just holding a
/// reference to them, as such any data put into the graph must have a lifetime that lasts
/// at least as long as the graph itself.
///
/// ## Edges
///
/// Each edge between vertexes in the graph must have both a direction and a weight. An enum
/// [`EdgeDirection`] is provided which can either be `Single`, for a directed edge, or `Bi`
/// for a bi-directional edge. The weighting on the graph can be anything, provided it
/// implements both `PartialOrd + PartialEq`.
///
/// ## Weighting
///
/// The **Weighting: `W`** of used for each edge in the graph must implement `Ord + PartialEq + Clone + Add<Output = W>`
/// this is so that it can be used within the [`binary heap`] acting as a Priority Queue within some of the algorithms. See
/// the offical rust docs for an example of how these traits need to be implemented. There are
/// also additional examples below and on the [`summary page`].
///
/// # Examples
///
/// ```rust
/// use::data_structures::graph::Graph;
///
/// let mut graph = Graph::new();
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
/// graph.add_undirected_edge(&data_1, &data_2, 5);
/// graph.add_undirected_edge(&data_1, &data_3, 10);
/// graph.add_undirected_edge(&data_2, &data_4, 15);
/// graph.add_undirected_edge(&data_3, &data_5, 20);
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
/// use data_structures::graph::Graph;
/// // todo
/// ```
///
/// [`summary page`]: ./index.html
/// [`binary heap`]: https://doc.rust-lang.org/std/collections/binary_heap/index.html
#[derive(Default)]
pub struct Graph<'a, T, W>
where
    T: Eq + Hash,
    W: Ord + PartialEq + Clone + Add<Output = W>,
{
    adjacency_list: HashMap<u64, Vec<Edge<'a, T, W>>>,
    key_value_map: HashMap<u64, Vertex<'a, T>>,
}

/// Public API
impl<'a, T, W> Graph<'a, T, W>
where
    T: Eq + Hash,
    W: Ord + PartialEq + Clone + Add<Output = W>,
{
    /// Constructs a new, empty `Graph<T>`
    /// where `T: Eq + Hash`
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::graph::Graph;
    ///
    /// let mut graph: Graph<i32, u32> = Graph::new();
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
    /// use data_structures::graph::Graph;
    ///
    /// let mut graph: Graph<i32, u32> = Graph::new();
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
    /// use data_structures::graph::Graph;
    ///
    /// let mut graph: Graph<i32, u32> = Graph::new();
    /// assert!(graph.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.adjacency_list.is_empty()
    }

    /// Adds a new vertex to the graph
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::graph::Graph;
    ///
    /// let mut graph: Graph<i32, i32> = Graph::new();
    ///
    /// graph.add_vertex(&50);
    /// graph.add_vertex(&25);
    /// assert_eq!(graph.size(), 2);
    /// ```
    pub fn add_vertex(&mut self, value: &'a T) {
        let node = Vertex::new(value);
        let key = node.get_key();

        self.adjacency_list.entry(key).or_insert_with(Vec::new);
        self.key_value_map.entry(key).or_insert(node);
    }

    /// Removes a new vertex from the graph, returning an `Option<T>` if
    /// the vertex is found, `None` if it isn't.
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::graph::Graph;
    ///
    /// let mut graph: Graph<i32, i32> = Graph::new();
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
            relations
                .iter()
                .filter(|edge| edge.direction() == EdgeDirection::Undirected)
                .map(|relation_key| get_key(relation_key))
                .for_each(|relation_key| {
                    if let Some(relation) = self.adjacency_list.get_mut(&relation_key) {
                        relation.retain(|relation_key| get_key(relation_key) != key);
                    }
                })
        }

        self.key_value_map.remove(&key).map(|node| node.value)
    }

    /// Adds a new directed edge between the two vertexes
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::graph::Graph;
    ///
    /// let mut graph = Graph::new();
    ///
    /// let data_1 = 50;
    /// let data_2 = 25;
    ///
    /// graph.add_vertex(&data_1);
    /// graph.add_vertex(&data_2);
    /// assert_eq!(graph.size(), 2);
    ///
    /// graph.add_directed_edge(&data_1, &data_2, 10);
    ///
    /// assert_eq!(graph.get_relations(&data_1), Some(vec![&data_2]));
    /// assert_eq!(graph.get_relations(&data_2), None);
    /// ```
    pub fn add_directed_edge(&mut self, from_vertex: &'a T, to_vertex: &'a T, weight: W) {
        self.add_edge(from_vertex, to_vertex, weight, EdgeDirection::Directed)
    }

    /// Adds a new undirected edge between the two vertexes
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::graph::Graph;
    ///
    /// let mut graph = Graph::new();
    ///
    /// let data_1 = 50;
    /// let data_2 = 25;
    ///
    /// graph.add_vertex(&data_1);
    /// graph.add_vertex(&data_2);
    /// assert_eq!(graph.size(), 2);
    ///
    /// graph.add_undirected_edge(&data_1, &data_2, 10);
    ///
    /// assert_eq!(graph.get_relations(&data_1), Some(vec![&data_2]));
    /// assert_eq!(graph.get_relations(&data_2), Some(vec![&data_1]));
    /// ```
    pub fn add_undirected_edge(&mut self, vertex_1: &'a T, vertex_2: &'a T, weight: W) {
        self.add_edge(vertex_1, vertex_2, weight, EdgeDirection::Undirected)
    }

    /// Adds removes an edge between two vertexes
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::graph::Graph;
    ///
    /// let mut graph = Graph::new();
    ///
    /// let data_1 = 50;
    /// let data_2 = 25;
    ///
    /// graph.add_vertex(&data_1);
    /// graph.add_vertex(&data_2);
    /// assert_eq!(graph.size(), 2);
    ///
    /// graph.add_undirected_edge(&data_1, &data_2, 10);
    ///
    /// assert_eq!(graph.get_relations(&data_1), Some(vec![&data_2]));
    ///
    /// graph.remove_edge(&data_1, &data_2);
    /// assert_eq!(graph.get_relations(&data_1), None);
    /// ```
    pub fn remove_edge(&mut self, value_1: &T, value_2: &T) {
        let key = get_key(value_1);
        let target_key = get_key(value_2);
        let mut is_directional = true;

        if let Some(relations) = self.adjacency_list.get_mut(&key) {
            relations.retain(|relation_key| {
                let cmp = get_key(relation_key) != target_key;
                if !cmp {
                    if let EdgeDirection::Undirected = relation_key.direction() {
                        is_directional = false;
                    }
                }
                cmp
            });
        }
        if is_directional {
            return;
        }

        if let Some(relations) = self.adjacency_list.get_mut(&target_key) {
            relations.retain(|relation_key| get_key(relation_key) != key);
        }
    }

    /// Returns true if a value is in the adjacency list, false if it isn't
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::graph::Graph;
    ///
    /// let mut graph: Graph<i32, i32> = Graph::new();
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
    /// relationships are found `None` is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use data_structures::graph::Graph;
    ///
    /// let mut graph = Graph::new();
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
    /// graph.add_undirected_edge(&data_1, &data_2, 10);
    /// graph.add_undirected_edge(&data_1, &data_3, 15);
    ///
    /// assert_eq!(graph.get_relations(&data_1), Some(vec![&data_2, &data_3]));
    /// ```
    pub fn get_relations(&self, value: &T) -> Option<Vec<&T>> {
        match self.adjacency_list.get(&get_key(value)) {
            Some(relations) => match relations.is_empty() {
                true => None,
                false => relations
                    .iter()
                    .map(|key| self.key_value_map.get(&get_key(key)).map(|node| node.value))
                    .collect(),
            },
            None => None,
        }
    }

    /// Returns information about the edge (it's direction and weighting) between
    /// two vertexes, if no edge is found `None` is returned
    ///
    /// # Examples
    ///
    /// ```rust
    /// use data_structures::graph::{Graph, EdgeDirection};
    ///
    /// let mut graph = Graph::new();
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
    /// graph.add_undirected_edge(&data_1, &data_2, 10);
    /// graph.add_undirected_edge(&data_1, &data_3, 15);
    ///
    /// assert_eq!(graph.get_edge(&data_1, &data_2), Some((EdgeDirection::Undirected, &10)));
    /// ```
    pub fn get_edge(&self, from: &T, to: &T) -> Option<(EdgeDirection, &W)> {
        let from_key = get_key(from);
        let to_key = get_key(to);

        if let Some(relations) = self.adjacency_list.get(&from_key) {
            return match relations
                .iter()
                .filter(|edge| get_key(edge) == to_key)
                .peekable()
                .peek()
            {
                Some(sibling) => Some((sibling.direction(), sibling.weight())),
                None => None,
            };
        }
        None
    }

    /// Conducts a Breadth First Search to determine whether or not
    /// it is possible to traverse from the start node to the finish node in the
    /// given graph.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use data_structures::graph::Graph;
    ///
    /// let mut graph = Graph::new();
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
    /// graph.add_undirected_edge(&data_1, &data_2, 10);
    /// graph.add_undirected_edge(&data_2, &data_3, 15);
    /// graph.add_undirected_edge(&data_3, &data_4, 20);
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
                    let key = get_key(key);
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
    /// use data_structures::graph::Graph;
    ///
    /// let mut graph = Graph::new();
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
    /// graph.add_undirected_edge(&data_1, &data_2, 10);
    /// graph.add_undirected_edge(&data_2, &data_3, 15);
    /// graph.add_undirected_edge(&data_3, &data_4, 20);
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
                    .filter(|key| !visited.contains(&get_key(key)))
                    .for_each(|key| stack.push(get_key(key)));
                visited.insert(next);
            }

            if let Some(node) = self.key_value_map.get(&next) {
                result.push(node.value);
            }
        }
        result
    }

    /// Computes the shortest path between two vertices using Dijstra's Shortest Path
    /// algorithm. If a shortest path is found, it is returned as an `Option<(Vec<&T>, W)>`.
    /// Where `Vec<&T>` is a vector of nodes, in the order of start to finish, and `W` is
    /// the total weighting for the path.
    ///
    /// If no path is possible then `None` is returned
    ///
    /// # Notes
    /// As the API offered with this algorithm is fairly flexible there are a few nuances
    /// to calling it correctly.
    ///
    /// ## Method Parameters
    ///
    /// The `Min Weighting` parameter in the function needs to be provided to mimic what the **Zero value*
    /// of whatever weighting you're using within the graph is. In the case of just using some form
    /// of number `0` can be passed. However if a custom data structure is used, then that needs
    /// to be passed with the cloest approximation as to what the 0 value is.
    ///
    /// # Examples
    /// See [`graph`] and [`summary page`] for some more detailed examples of how this method can be used
    ///
    /// ```rust
    /// use data_structures::graph::{EdgeDirection, Graph};
    ///
    /// let mut graph = Graph::new();
    ///
    /// let a = String::from("A");
    /// let b = String::from("B");
    /// let c = String::from("C");
    /// let d = String::from("D");
    /// let e = String::from("E");
    /// let f = String::from("F");
    ///
    /// graph.add_vertex(&a);
    /// graph.add_vertex(&b);
    /// graph.add_vertex(&c);
    /// graph.add_vertex(&d);
    /// graph.add_vertex(&e);
    /// graph.add_vertex(&f);
    ///
    /// graph.add_undirected_edge(&a, &b, 4);
    /// graph.add_undirected_edge(&a, &c, 2);
    /// graph.add_undirected_edge(&b, &e, 3);
    /// graph.add_undirected_edge(&c, &d, 2);
    /// graph.add_undirected_edge(&c, &f, 4);
    /// graph.add_undirected_edge(&d, &e, 3);
    /// graph.add_undirected_edge(&d, &f, 1);
    /// graph.add_undirected_edge(&e, &f, 1);
    ///
    /// assert_eq!(
    ///     graph.dijkstras_shortest_path(&a, &e, 0),
    ///     Some((vec![&a, &c, &d, &f, &e], 6))
    /// );
    /// ```
    ///
    /// [`graph`]: ./struct.Graph.html#examples
    /// [`summary page`]: ./index.html
    pub fn dijkstras_shortest_path(
        &self,
        start: &'a T,
        finish: &'a T,
        min_weighting: W,
    ) -> Option<(Vec<&T>, W)> {
        if start == finish {
            return Some((vec![start], min_weighting));
        }

        let finish_key = get_key(finish);

        let mut queue = BinaryHeap::new();
        let mut distances = HashMap::new();
        let mut previous = HashMap::new();
        let mut visited = HashSet::new();

        self.adjacency_list.keys().into_iter().for_each(|key| {
            distances.insert(*key, None);
            previous.insert(*key, None);
        });

        let start_key = get_key(start);
        if let Some(start_value) = distances.get_mut(&start_key) {
            *start_value = Some(min_weighting.clone());
        };

        let start_edge = Edge::new(
            Direction::Directed(Vertex::new(start)),
            min_weighting.clone(),
        );
        queue.push(&start_edge);
        visited.insert(start_key);

        let mut current_key;
        let mut result = Vec::new();
        let mut total = min_weighting;
        while let Some(next) = queue.pop() {
            current_key = next.target_key();
            visited.insert(current_key);

            if current_key == finish_key {
                result.push(current_key);
                if let Some(total_distance) = distances.get(&current_key) {
                    total = total_distance
                        .as_ref()
                        .expect("This value should have been set at least once")
                        .clone();
                }
                while let Some(previous_node) = previous
                    .get(&current_key)
                    .expect("Key should have already been added to previous")
                {
                    result.push(*previous_node);
                    current_key = *previous_node;
                }
                break;
            }

            if let Some(siblings) = self.adjacency_list.get(&current_key) {
                for next_vertex in siblings.iter() {
                    let sibling_key = get_key(next_vertex);
                    if visited.contains(&sibling_key) {
                        continue;
                    }
                    queue.push(&next_vertex);

                    if let Some(distance) = distances.get(&current_key) {
                        let mut candidate = match distance {
                            Some(distance) => {
                                W::from(distance.clone() + next_vertex.weight().clone())
                            }
                            None => next_vertex.weight().clone(),
                        };

                        let distance_weight = distances
                            .get_mut(&sibling_key)
                            .expect("This unwrap should be safe as we've added it in to the keys");

                        match distance_weight {
                            Some(weight) => {
                                if &mut candidate < weight {
                                    *weight = candidate;
                                    if let Some(sibling) = previous.get_mut(&sibling_key) {
                                        *sibling = Some(current_key);
                                    }
                                }
                            }
                            None => {
                                distances.insert(sibling_key, Some(candidate));
                                if let Some(sibling) = previous.get_mut(&sibling_key) {
                                    *sibling = Some(current_key);
                                }
                            }
                        };
                    }
                }
            }
        }

        match result.is_empty() {
            true => None,
            false => Some((
                result
                    .into_iter()
                    .rev()
                    .map(|key| self.key_value_map.get(&key).unwrap().value)
                    .collect(),
                total,
            )),
        }
    }
}

/// Private API
impl<'a, T, W> Graph<'a, T, W>
where
    T: Eq + Hash,
    W: Ord + PartialEq + Clone + Add<Output = W>,
{
    /// Retrieve the relations of a node by it's key as
    /// opposed to it's value
    fn _get_relations(&self, key: u64) -> Option<&Vec<Edge<T, W>>> {
        self.adjacency_list.get(&key)
    }

    fn add_edge(&mut self, from_node: &'a T, to_node: &'a T, weight: W, direction: EdgeDirection) {
        let _direction = direction.convert(to_node);
        let edge = Edge::new(_direction, weight.clone());
        let key = get_key(from_node);

        if let Some(connected_to) = self.adjacency_list.get_mut(&key) {
            connected_to.push(edge);
        }
        // If it's a directed edge, we don't need to add it to the list of the finishing
        // vertexes relationships - as we can't traverse from our finishing vertex back to the
        // starting vertex
        if direction == EdgeDirection::Directed {
            return;
        }

        // If it's undirected, then add the relationship into the finishing vertexes
        // relationships too
        let _direction = direction.convert(from_node);
        let edge = Edge::new(_direction, weight);
        let key = get_key(to_node);

        if let Some(connected_to) = self.adjacency_list.get_mut(&key) {
            connected_to.push(edge);
        }
    }
}

/// An enum declaring the type of edge that is
/// being added to the graph.
///
/// Either it is:
/// - `Directed` for a directed edge
/// - `Undirected` for a undirected edge
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum EdgeDirection {
    Directed,
    Undirected,
}

#[derive(Hash, PartialEq, Eq)]
struct Vertex<'a, T>
where
    T: Eq + Hash,
{
    value: &'a T,
}

/// A private data structure that holds the relationships between vertexes.
///
/// The `direction member` holds the type of edge that it is, along with
/// the node that this edge connects to. As edges are created and inserted into the
/// in a graph in a controlled manner the way to read the data flow would be:
///
/// `Graph.adjacency_list[from_vertex] : [Edge.direction(to_vertex)]`
///
/// All of the edges that a vertex is connected to is stored in it's corresponding
/// entry in it's adjacency list.
/// In the event that the type of Edge is `Single`, then it is only added in the
/// start vertexes list of relationships. If the type of edge is `Bi`, then it is
/// added in both vertexes relationships
#[derive(Eq, PartialEq)]
struct Edge<'a, T, W>
where
    W: Ord + PartialEq + Clone + Add<Output = W>,
    T: Eq + Hash,
{
    direction: Direction<'a, T>,
    weight: W,
}

/// Private enum which wraps the value within the direction, removing the need for
/// an additional data field within the Edge
#[derive(Eq, PartialEq)]
enum Direction<'a, T>
where
    T: Eq + Hash,
{
    Directed(Vertex<'a, T>),
    Undirected(Vertex<'a, T>),
}

impl<'a, T, W> Edge<'a, T, W>
where
    W: Ord + PartialEq + Clone + Add<Output = W>,
    T: Eq + Hash,
{
    fn new(direction: Direction<'a, T>, weight: W) -> Self {
        Self { direction, weight }
    }

    fn direction(&self) -> EdgeDirection {
        match &self.direction {
            Direction::Directed(_) => EdgeDirection::Directed,
            Direction::Undirected(_) => EdgeDirection::Undirected,
        }
    }

    fn target_key(&self) -> u64 {
        match &self.direction {
            Direction::Directed(node) => get_key(node),
            Direction::Undirected(node) => get_key(node),
        }
    }

    fn weight(&self) -> &W {
        &self.weight
    }
}

impl<'a, T, W> Ord for Edge<'a, T, W>
where
    T: Eq + Hash,
    W: Ord + PartialEq + Clone + Add<Output = W>,
{
    fn cmp(&self, other: &Self) -> Ordering {
        other.weight().cmp(self.weight())
    }
}

impl<'a, T, W> PartialOrd for Edge<'a, T, W>
where
    T: Eq + Hash,
    W: Ord + PartialEq + Clone + Add<Output = W>,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'a, T, W> Hash for Edge<'a, T, W>
where
    T: Eq + Hash,
    W: Ord + PartialEq + Clone + Add<Output = W>,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        match &self.direction {
            Direction::Directed(node) => node.hash(state),
            Direction::Undirected(node) => node.hash(state),
        }
    }
}

impl EdgeDirection {
    fn convert<'a, T>(&self, node: &'a T) -> Direction<'a, T>
    where
        T: Eq + Hash,
    {
        match &self {
            EdgeDirection::Directed => Direction::Directed(Vertex::new(node)),
            EdgeDirection::Undirected => Direction::Undirected(Vertex::new(node)),
        }
    }
}

impl<'a, T> Vertex<'a, T>
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn has() {
        let mut graph: Graph<String, u32> = Graph::default();

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
        let mut graph = Graph::default();

        let str_1 = String::from("Key 1");
        let str_2 = String::from("Key 2");
        let str_3 = String::from("Key 3");

        graph.add_vertex(&str_1);
        graph.add_vertex(&str_2);
        graph.add_vertex(&str_3);

        graph.add_undirected_edge(&str_1, &str_2, 10);
        graph.add_undirected_edge(&str_1, &str_3, 10);

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
        let mut graph = Graph::default();

        let str_1 = String::from("Key 1");
        let str_2 = String::from("Key 2");
        let str_3 = String::from("Key 3");
        let str_4 = String::from("Key 4");
        let false_str = String::from("Incorrect");

        graph.add_vertex(&str_1);
        graph.add_vertex(&str_2);
        graph.add_vertex(&str_3);
        graph.add_vertex(&str_4);

        graph.add_undirected_edge(&str_1, &str_2, 10);
        graph.add_undirected_edge(&str_1, &str_3, 10);
        graph.add_undirected_edge(&str_1, &str_4, 10);

        assert!(graph.has(&str_1));
        assert!(graph.has(&str_2));
        assert!(graph.has(&str_3));
        assert!(graph.has(&str_4));
        assert!(!graph.has(&false_str));

        assert_eq!(graph.size(), 4);
        assert_eq!(graph.get_relations(&str_1).unwrap().len(), 3);

        graph.remove_edge(&str_1, &str_3);
        assert_eq!(graph.get_relations(&str_1).unwrap().len(), 2);
        assert_eq!(graph.get_relations(&str_3), None);

        let result = graph.remove_vertex(&str_1).unwrap();
        assert_eq!(&str_1, result);

        assert!(!graph.has(&str_1));
        assert_eq!(graph.get_relations(&str_2), None);
        assert_eq!(graph.get_relations(&str_3), None);
        assert_eq!(graph.get_relations(&str_4), None);
    }

    #[test]
    fn can_traverse_to() {
        let mut graph = Graph::default();

        let str_1 = String::from("Key 1");
        let str_2 = String::from("Key 2");
        let str_3 = String::from("Key 3");
        let str_4 = String::from("Key 4");

        graph.add_vertex(&str_1);
        graph.add_vertex(&str_2);
        graph.add_vertex(&str_3);
        graph.add_vertex(&str_4);

        graph.add_undirected_edge(&str_1, &str_2, 10);
        graph.add_undirected_edge(&str_1, &str_3, 10);
        graph.add_undirected_edge(&str_2, &str_4, 10);

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
        let mut graph = Graph::default();

        let str_1 = String::from("Key 1");
        let str_2 = String::from("Key 2");
        let str_3 = String::from("Key 3");
        let str_4 = String::from("Key 4");

        graph.add_vertex(&str_1);
        graph.add_vertex(&str_2);
        graph.add_vertex(&str_3);
        graph.add_vertex(&str_4);

        graph.add_undirected_edge(&str_1, &str_2, 10);
        graph.add_undirected_edge(&str_1, &str_3, 10);
        graph.add_undirected_edge(&str_2, &str_4, 10);

        let result = graph.traverse_all_nodes(&str_1);
        let expected = vec![&str_1, &str_3, &str_2, &str_4];
        assert_eq!(result, expected);
    }
}
