//! # Binary Tree
//!
//! A simple heap allocated node based binary tree, the purpose of this library is to demonstrate
//! tree traversal schemes, as such only the traversal methods are optimised.
//!
//! Insertion is randomised via coin toss to introduce unpredictability into how the tree is created.
//!
//! # Examples
//!
//! Instantiating a new Binary Tree
//! ```rust
//! use data_structures::binary_tree::BinaryTree;
//!
//! let mut bt: BinaryTree<i32> = BinaryTree::new();
//! assert!(bt.is_empty());
//! assert_eq!(bt.len(), 0);
//!
//! // Alternatively, default has been derived
//! let mut bt: BinaryTree<i32> = BinaryTree::default();
//! assert!(bt.is_empty());
//! assert_eq!(bt.len(), 0);
//! ```

use crate::deque::Deque;

/// # Binary Search Tree
///
/// This binary tree uses a random insertion algorithm (based on a coin toss) to create a tree, upon which
/// different methods of traversal are offered. To offer a simplified public API and appropriately demonstrate
/// the traversal schemes, the type of the tree `T` (`BinaryTree<T>`) requires `T` to
/// implement `PartialOrd`, `PartialEq` and `Copy`.
///
/// # Examples
///
/// ```rust
/// use data_structures::binary_tree::BinaryTree;
///
/// let mut bt = BinaryTree::new();
/// assert!(bt.is_empty());
/// assert_eq!(bt.len(), 0);
///
/// bt.insert(20);
/// bt.insert(50);
/// bt.insert(25);
///
/// assert!(!bt.is_empty());
/// assert_eq!(bt.len(), 3);
/// ```
///
/// ## Macro
/// The [`binary_tree!`] macro can be used to make initialization more convenient, the
/// first value within the square `[]` being the first value inserted.
///
/// ```rust
/// use data_structures::binary_tree;
///
/// let bt = binary_tree![10, 5, 20];
///
/// assert!(!bt.is_empty());
/// assert_eq!(bt.len(), 3)
/// ```
/// [`binary_tree!`]: ../macro.binary_tree.html
#[derive(Default)]
pub struct BinaryTree<T>
where
    T: PartialOrd + PartialEq + Copy,
{
    root: Edge<T>,
    length: usize,
}

#[derive(Default)]
struct Node<T> {
    data: T,
    right: Edge<T>,
    left: Edge<T>,
}

type Edge<T> = Option<Box<Node<T>>>;

enum TraversalGoal<'a, T> {
    Target(&'a T),
    Max,
    Min,
    VisitAll,
}

impl<T> Node<T> {
    fn new(data: T) -> Edge<T> {
        Some(Box::new(Self {
            data,
            right: None,
            left: None,
        }))
    }
}

impl<T> BinaryTree<T>
where
    T: PartialOrd + PartialEq + Copy,
{
    /// Constructs a new, empty `BinaryTree<T>`
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::binary_tree::BinaryTree;
    ///
    /// let bt: BinaryTree<i32> = BinaryTree::new();
    /// assert_eq!(bt.len(), 0);
    /// assert!(bt.is_empty());
    /// ```
    pub fn new() -> Self {
        Self {
            root: None,
            length: 0,
        }
    }

    /// Returns the number of elements in the binary search tree, also referred to as it's _length_
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::binary_tree;
    ///
    /// let bt = binary_tree![1, 2, 3];
    ///
    /// assert_eq!(bt.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.length
    }

    /// Returns true if the binary search tree is empty, false if it contains 1 or more elements
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::binary_tree;
    /// use data_structures::binary_tree::BinaryTree;
    ///
    /// let bt = binary_tree![1, 2, 3];
    /// assert!(!bt.is_empty());
    ///
    /// let bt: BinaryTree<i32> = BinaryTree::new();
    /// assert!(bt.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    /// Inserts a value into the binary search tree, as the purpose of this Binary Tree
    /// is to demonstrate traversal schemes, randomness is introduced in order to create
    /// unpredictable trees.
    ///
    /// Therefore insertion complexity is **not** optimal.
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::binary_tree;
    ///
    /// let mut bt = binary_tree![500, 10, 1000];
    /// assert_eq!(bt.len(), 3);
    ///
    /// bt.insert(50);
    /// bt.insert(750);
    ///
    /// assert_eq!(bt.len(), 5);
    /// ```
    pub fn insert(&mut self, data: T) {
        self.length += 1;
        if self.root.is_none() {
            self.root = Node::new(data);
            return;
        }

        insert_rec(
            self.root.as_mut().expect("Already checked this is some"),
            data,
        );
    }

    // Private API for Breath First Search Traversal of the Tree
    fn breadth_first_search(&self, target: TraversalGoal<T>) -> (bool, Vec<T>) {
        let mut data = Vec::new();
        let mut result = false;
        if self.root.is_none() {
            return (result, data);
        }

        let mut queue = Deque::new();
        queue.push_back(self.root.as_ref());

        while let Some(node) = queue.pop_front() {
            if let Some(node) = node {
                match target {
                    TraversalGoal::Target(target) => {
                        if &node.data == target {
                            result = true;
                            return (result, data);
                        }
                    }
                    TraversalGoal::VisitAll => {
                        data.push(node.data);
                    }
                    TraversalGoal::Max => {
                        if data.is_empty() {
                            data.push(node.data);
                        } else if data[0] < node.data {
                            data.pop();
                            data.push(node.data);
                        }
                    }
                    TraversalGoal::Min => {
                        if data.is_empty() {
                            data.push(node.data);
                        } else if data[0] > node.data {
                            data.pop();
                            data.push(node.data);
                        }
                    }
                }

                if node.left.is_some() {
                    queue.push_back(node.left.as_ref());
                }
                if node.right.is_some() {
                    queue.push_back(node.right.as_ref());
                }
            }
        }
        (result, data)
    }

    /// Searches for the minimum value in the tree using a breadth first search algorithm
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::binary_tree;
    ///
    /// let mut bt = binary_tree![500, 10, 1000, 50, 600];
    /// assert_eq!(bt.len(), 5);
    ///
    /// assert_eq!(bt.bfs_min_value(), Some(10));
    /// ```
    pub fn bfs_min_value(&self) -> Option<T> {
        let (_, mut data) = self.breadth_first_search(TraversalGoal::Min);
        data.pop()
    }

    /// Searches for the maximum value in the tree using a breadth first search algorithm
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::binary_tree;
    ///
    /// let mut bt = binary_tree![500, 10, 1000, 50, 600];
    /// assert_eq!(bt.len(), 5);
    ///
    /// assert_eq!(bt.bfs_max_value(), Some(1000));
    /// ```
    pub fn bfs_max_value(&self) -> Option<T> {
        let (_, mut data) = self.breadth_first_search(TraversalGoal::Max);
        data.pop()
    }

    /// Returns all the values in a tree in a vec using the breadth first search algorithm
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::binary_tree;
    ///
    /// let mut bt = binary_tree![500, 10, 1000, 50, 600];
    /// assert_eq!(bt.len(), 5);
    ///
    /// let result = bt.bfs_all();
    ///
    /// let expected = [500, 10, 1000, 50, 600];
    ///
    /// let matched = result.iter().zip(expected.iter()).filter(|&(a, b)| a == b).count();
    /// assert_eq!(matched, 5);
    /// ```
    pub fn bfs_all(&self) -> Vec<T> {
        let (_, data) = self.breadth_first_search(TraversalGoal::VisitAll);
        data
    }

    /// Returns all the values in a tree in a vec using the breadth first search algorithm
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::binary_tree;
    ///
    /// let mut bt = binary_tree![500, 10, 1000, 50, 600];
    /// assert_eq!(bt.len(), 5);
    ///
    /// assert!(bt.bfs_contains(50));
    /// assert!(!bt.bfs_contains(2));
    /// ```
    pub fn bfs_contains(&self, target: T) -> bool {
        let (success, _) = self.breadth_first_search(TraversalGoal::Target(&target));
        success
    }
}

// Mimics a coin toss to decide where to insert the node
fn insert_rec<T>(node: &mut Node<T>, data: T) {
    // Heads
    if rand::random() {
        if node.left.is_none() {
            node.left = Node::new(data);
            return;
        }
        insert_rec(
            node.left
                .as_mut()
                .expect("We've already checked that it is some"),
            data,
        );
    } else {
        // Tails
        if node.right.is_none() {
            node.right = Node::new(data);
            return;
        }
        insert_rec(
            node.right
                .as_mut()
                .expect("We've already checked that it is some"),
            data,
        );
    }
}

/// Provides a shorthand macro for creating a Binary Tree with multiple elements in it.
///
/// This macro inserts the values into the tree in the order provided, left to right, so for the
/// arguments `[10, 3, 4, 5, 6]`, 10 is inserted as the root node, then 3, then 4 etc.
///
/// # Examples
///
/// ```rust
/// #[macro_use]
/// use data_structures::binary_tree;
/// use data_structures::binary_tree::BinaryTree;
///
/// // Macro notation:
/// let mut bt = binary_tree![3, 2, 4, 1, 5];
///
/// assert_eq!(bt.len(), 5);
///
/// // Longhand notation:
/// let mut bt = BinaryTree::default();
/// bt.insert(4);
/// bt.insert(2);
/// bt.insert(5);
/// bt.insert(1);
///
/// assert_eq!(bt.len(), 4);
/// ```
#[macro_export]
macro_rules! binary_tree {
    ($($x:expr),*) => {
        {
            let mut bt = $crate::binary_tree::BinaryTree::default();
            $(
                bt.insert($x);
            )*
            bt
        }
    };
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn correctly_inserts_elements() {
        let mut bst = BinaryTree::default();
        bst.insert(10);
        bst.insert(5);
        bst.insert(3);
        bst.insert(12);
        bst.insert(7);

        assert_eq!(bst.len(), 5);
    }
}
