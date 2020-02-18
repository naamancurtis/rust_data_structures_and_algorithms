//! # Binary Search Tree
//!
//! A simple heap allocated node based binary search tree which contains the following properties:
//! 1. The left subtree of a node only contains nodes with values below it (according to the provided
//! comparator function)
//! 2. The right subtree of a node only contains nodes with values above it (according to the provided
//! comparator function)
//! 3. The left and right subtrees are also binary search trees
//!
//! # Examples
//!
//! You can instantiate a new Binary Search Tree in 2 ways.
//! 1. By using `BinarySearchTree::new(Fn)`, you can pass a custom comparator function for the tree
//!
//! ```rust
//! use data_structures::binary_search_tree::BinarySearchTree;
//!
//! let mut bst = BinarySearchTree::new(&|a: &i32, b: &i32| a.cmp(b));
//! bst.insert(20);
//!
//! assert!(bst.contains(20));
//! assert!(!bst.contains(10));
//! ```
//! 2. Alternatively, if the type of the Binary Search Tree implements Ord, you can
//! use `BinarySearchTree::default()`, to use the default implementation of comparison
//!
//! ```rust
//! use data_structures::binary_search_tree::BinarySearchTree;
//!
//! let mut bst = BinarySearchTree::default();
//! bst.insert(20);
//!
//! assert!(bst.contains(20));
//! assert!(!bst.contains(10));
//! ```

use std::cmp::Ordering;

/// # Binary Search Tree
///
/// This binary search tree maintains a sorted binary tree through insertion according to a
/// comparator function _(either one passed when it's created or the default `Ord` implementation)_
///
/// Insertion and Searching should occur on **Average** in **O**( log(_n_) ) time provided the tree
/// is roughly distributed evenly around the root node. Worst case is **O**(n) if all nodes are present
/// on only 1 branch.
///
/// # Examples
///
/// ```rust
/// use data_structures::binary_search_tree::BinarySearchTree;
///
/// // Passing a custom comparator function
/// let mut bst = BinarySearchTree::new(&|a: &i32, b: &i32| a.cmp(b));
/// bst.insert(20);
/// bst.insert(10);
///
/// assert_eq!(bst.len(), 2);
///
/// bst.insert(5);
/// bst.insert(50);
///
/// assert_eq!(bst.len(), 4);
///
/// assert!(bst.contains(20));
/// assert!(!bst.contains(170));
/// assert!(bst.contains(50));
/// assert!(bst.contains(5));
///
/// // Using the default Ord Implementation
///
/// let mut bst = BinarySearchTree::default();
/// assert!(bst.is_empty());
/// bst.insert(20);
///
/// assert!(!bst.is_empty());
/// assert!(bst.contains(20));
/// assert!(!bst.contains(10));
/// ```
///
/// ## Macro
/// The [`bst!`] macro can be used to make initialization more convenient when `T` implements `Ord`, the
/// first value within the square `[]` being the first value inserted.
///
/// ```rust
/// use data_structures::bst;
///
/// let bst = bst![10, 5, 20];
///
/// assert!(!bst.is_empty());
/// assert!(bst.contains(10));
/// assert!(bst.contains(5));
/// assert!(bst.contains(20));
/// assert!(!bst.contains(300));
/// ```
/// [`bst!`]: ../macro.bst.html
pub struct BinarySearchTree<'a, T> {
    root: Edge<T>,
    cmp: Box<&'a dyn Fn(&T, &T) -> Ordering>,
    length: usize,
}

#[derive(Default)]
struct Node<T> {
    data: T,
    right: Edge<T>,
    left: Edge<T>,
}

type Edge<T> = Option<Box<Node<T>>>;

impl<T> Node<T> {
    fn new(data: T) -> Edge<T> {
        Some(Box::new(Self {
            data,
            right: None,
            left: None,
        }))
    }
}

impl<'a, T> BinarySearchTree<'a, T> {
    /// Constructs a new, empty `BinarySearchTree<T>` where `T` implements `Ord`
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::binary_search_tree::BinarySearchTree;
    ///
    /// let mut bst: BinarySearchTree<i32> = BinarySearchTree::default();
    /// assert_eq!(bst.len(), 0);
    /// assert!(bst.is_empty());
    /// ```
    pub fn default() -> Self
    where
        T: Ord,
    {
        Self {
            root: None,
            cmp: Box::new(&|a, b| a.cmp(b)),
            length: 0,
        }
    }

    /// Constructs a new, empty `BinarySearchTree<T>` with a custom comparator function
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::binary_search_tree::BinarySearchTree;
    ///
    /// let comparator_fn = |a: &i32, b: &i32| a.cmp(b);
    /// let mut bst: BinarySearchTree<i32> = BinarySearchTree::new(&comparator_fn);
    /// assert_eq!(bst.len(), 0);
    /// assert!(bst.is_empty());
    /// ```
    pub fn new<F: 'a>(cmp: &'a F) -> Self
    where
        F: Fn(&T, &T) -> Ordering,
    {
        Self {
            root: None,
            cmp: Box::new(cmp),
            length: 0,
        }
    }

    /// Returns the number of elements in the binary search tree, also referred to as it's _length_
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::bst;
    ///
    /// let bst = bst![1, 2, 3];
    ///
    /// assert_eq!(bst.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.length
    }

    /// Returns true if the binary search tree is empty, false if it contains 1 or more elements
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::bst;
    /// use data_structures::binary_search_tree::BinarySearchTree;
    ///
    /// let bst = bst![1, 2, 3];
    /// assert!(!bst.is_empty());
    ///
    /// let bst: BinarySearchTree<i32> = bst![];
    /// assert!(bst.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    /// Inserts a value into the binary search tree while maintaining insertion order according to
    /// the provided comparator function.
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::bst;
    ///
    /// let mut bst = bst![500, 10, 1000];
    /// assert_eq!(bst.len(), 3);
    ///
    /// bst.insert(50);
    /// bst.insert(750);
    ///
    /// assert!(bst.contains(50));
    /// assert!(bst.contains(750));
    /// assert_eq!(bst.len(), 5);
    /// ```
    pub fn insert(&mut self, data: T) {
        self.length += 1;
        if self.root.is_none() {
            self.root = Node::new(data);
            return;
        }

        let mut node_to_compare_to = self.root.as_mut();

        // Traverse the tree to find the appropriate place to insert it
        while let Some(node) = node_to_compare_to {
            match (self.cmp)(&data, &node.data) {
                Ordering::Greater => {
                    match &node.right {
                        Some(_) => {
                            node_to_compare_to = node.right.as_mut();
                        }
                        None => {
                            node.as_mut().right = Node::new(data);
                            break;
                        }
                    };
                }
                Ordering::Less | Ordering::Equal => {
                    match &node.left {
                        Some(_) => {
                            node_to_compare_to = node.left.as_mut();
                        }
                        None => {
                            node.as_mut().left = Node::new(data);
                            break;
                        }
                    };
                }
            }
        }
    }

    /// Searches a binary search tree to find whether or not a node is present within it
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::bst;
    ///
    /// let mut bst = bst![500, 10, 1000, 50, 600];
    /// assert_eq!(bst.len(), 5);
    ///
    /// assert!(bst.contains(50));
    /// assert!(bst.contains(600));
    /// assert!(bst.contains(500));
    ///
    /// assert!(!bst.contains(1));
    /// assert!(!bst.contains(501));
    /// assert!(!bst.contains(1010));
    /// ```
    pub fn contains(&self, target: T) -> bool {
        if self.root.is_none() {
            return false;
        }

        let mut node_to_compare_to = self.root.as_ref();

        // Traverse the tree
        while let Some(node) = node_to_compare_to {
            match (self.cmp)(&target, &node.data) {
                Ordering::Equal => return true,
                Ordering::Greater => {
                    match &node.right {
                        Some(_) => {
                            node_to_compare_to = node.right.as_ref();
                        }
                        None => return false,
                    };
                }
                Ordering::Less => {
                    match &node.left {
                        Some(_) => {
                            node_to_compare_to = node.left.as_ref();
                        }
                        None => return false,
                    };
                }
            }
        }
        false
    }
}

/// Provides a shorthand macro for creating a Binary Search Tree with multiple elements in it.
///
/// For this macro, the type (`T`) of the search tree (`BinarySearchTree<T>`)
/// must implement `Ord` or the macro will fail.
///
/// This macro inserts the values into the *BST* in the order provided, left to right, so for the
/// arguments `[10, 3, 4, 5, 6]`, 10 is inserted as the root node, then 3, then 4 etc.
///
/// # Examples
///
/// ```rust
/// #[macro_use]
/// use data_structures::bst;
/// use data_structures::binary_search_tree::BinarySearchTree;
///
/// // Macro notation:
/// let mut bst = bst![3, 2, 4, 1, 5];
///
/// assert!(bst.contains(1));
/// assert!(bst.contains(2));
/// assert!(bst.contains(3));
/// assert!(bst.contains(4));
/// assert!(bst.contains(5));
/// assert!(!bst.contains(6));
///
/// // Longhand notation:
/// let mut bst = BinarySearchTree::default();
/// bst.insert(4);
/// bst.insert(2);
/// bst.insert(5);
/// bst.insert(1);
/// bst.insert(3);
///
/// assert!(bst.contains(1));
/// assert!(bst.contains(2));
/// assert!(bst.contains(3));
/// assert!(bst.contains(4));
/// assert!(bst.contains(5));
/// assert!(!bst.contains(6));
/// ```
#[macro_export]
macro_rules! bst {
    ($($x:expr),*) => {
        {
            let mut bst = $crate::binary_search_tree::BinarySearchTree::default();
            $(
                bst.insert($x);
            )*
            bst
        }
    };
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use std::borrow::Borrow;

    #[test]
    fn correctly_inserts_elements() {
        let mut bst = BinarySearchTree::default();
        bst.insert(10);
        bst.insert(5);
        bst.insert(3);
        bst.insert(12);
        bst.insert(7);

        assert_eq!(bst.len(), 5);
        assert_eq!(bst.root.as_ref().unwrap().data.borrow(), &10);
        assert_eq!(
            bst.root
                .as_ref()
                .unwrap()
                .right
                .as_ref()
                .unwrap()
                .as_ref()
                .data
                .borrow(),
            &12
        );
        assert_eq!(
            bst.root
                .as_ref()
                .unwrap()
                .left
                .as_ref()
                .unwrap()
                .as_ref()
                .data
                .borrow(),
            &5
        );
        assert_eq!(
            bst.root
                .as_ref()
                .unwrap()
                .left
                .as_ref()
                .unwrap()
                .left
                .as_ref()
                .unwrap()
                .as_ref()
                .data
                .borrow(),
            &3
        );
        assert_eq!(
            bst.root
                .as_ref()
                .unwrap()
                .left
                .as_ref()
                .unwrap()
                .right
                .as_ref()
                .unwrap()
                .as_ref()
                .data
                .borrow(),
            &7
        );
    }

    #[test]
    fn correctly_contains() {
        let mut bst = BinarySearchTree::default();
        bst.insert(5);
        bst.insert(1);
        bst.insert(9);
        bst.insert(2);
        bst.insert(8);
        bst.insert(3);
        bst.insert(7);
        bst.insert(4);
        bst.insert(6);

        assert!(bst.contains(1));
        assert!(bst.contains(2));
        assert!(bst.contains(3));
        assert!(bst.contains(4));
        assert!(bst.contains(5));
        assert!(bst.contains(6));
        assert!(bst.contains(7));
        assert!(bst.contains(8));
        assert!(bst.contains(9));
        assert!(!bst.contains(10));
        assert!(!bst.contains(-10));
        assert!(!bst.contains(11));
        assert!(!bst.contains(100000));
    }
}
