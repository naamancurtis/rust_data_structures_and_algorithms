//! # Max Binary Heap
//!
//! A simple heap allocated node based max binary heap which contains the following properties:
//! 1. Each parent has at most two nodes
//! 2. All child nodes must be smaller than their parent node
//! 3. A binary heap is as compact as possible, with left children being filled first
//!
//! Given the properties of a Binary Heap, it's simple to model in a Vec<T>, therefore for
//! simplicity this approach coupled with the optimisations made to Rust's Vec, this
//! route has been taken.
//!
//! # Examples
//!
//! You can instantiate a binary heap using `new` or `default`
//!
//! ```rust
//! use data_structures::binary_heap::BinaryHeap;
//!
//! let heap: BinaryHeap<i32> = BinaryHeap::new();
//! assert_eq!(heap.len(), 0);
//!
//! let heap: BinaryHeap<i32> = BinaryHeap::default();
//! assert!(heap.is_empty())
//! ```

#[derive(Default)]
pub struct BinaryHeap<T>
where
    T: PartialEq + PartialOrd + Copy,
{
    heap: Vec<T>,
}

impl<T> BinaryHeap<T>
where
    T: PartialEq + PartialOrd + Copy,
{
    /// Constructs a new, empty `BinaryHeap<T>` where `T` implements `PartialOrd + PartialEq + Copy`
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::binary_heap::BinaryHeap;
    ///
    /// let mut heap: BinaryHeap<i32> = BinaryHeap::new();
    ///
    /// assert_eq!(heap.len(), 0);
    /// assert!(heap.is_empty());
    /// ```
    pub fn new() -> Self {
        Self { heap: Vec::new() }
    }

    /// Returns the number of elements in the binary heap, also referred to as it's _length_
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::binary_heap::BinaryHeap;
    ///
    /// let mut heap = BinaryHeap::new();
    ///
    /// assert_eq!(heap.len(), 0);
    ///
    /// heap.insert(10);
    /// assert_eq!(heap.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.heap.len()
    }

    /// Returns true if the binary heap is empty, false if it contains 1 or more elements
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::binary_heap::BinaryHeap;
    ///
    /// let mut heap = BinaryHeap::new();
    ///
    /// assert!(heap.is_empty());
    ///
    /// heap.insert(10);
    /// assert!(!heap.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    /// Returns the depth of the binary heap
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::binary_heap::BinaryHeap;
    ///
    /// let mut heap = BinaryHeap::new();
    ///
    /// assert_eq!(heap.depth(), 0);
    ///
    /// heap.insert(10);
    /// assert_eq!(heap.depth(), 1);
    ///
    /// heap.insert(20);
    /// assert_eq!(heap.depth(), 2);
    ///
    /// heap.insert(5);
    /// heap.insert(100);
    /// assert_eq!(heap.depth(), 3);
    /// ```
    pub fn depth(&self) -> usize {
        if self.is_empty() {
            return 0;
        }
        ((self.len() + 1) as f64).log2().ceil() as usize
    }

    /// Returns an optional tuple containing the index of the child node and the value of the child
    /// node at the specified parent index
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::binary_heap::BinaryHeap;
    ///
    /// let mut heap = BinaryHeap::new();
    ///
    /// heap.insert(10);
    /// heap.insert(9);
    /// heap.insert(8);
    /// heap.insert(7);
    /// heap.insert(6);
    ///
    /// assert_eq!(heap.depth(), 3);
    ///
    /// assert_eq!(heap.get_children(0), (Some((1, &9)), Some((2, &8))));
    /// assert_eq!(heap.get_children(1), (Some((3, &7)), Some((4, &6))));
    /// assert_eq!(heap.get_children(2), (None, None));
    /// assert_eq!(heap.get_children(6), (None, None));
    /// ```
    pub fn get_children(&self, index: usize) -> (Option<(usize, &T)>, Option<(usize, &T)>) {
        let temp_index = 2 * index;
        let left = match self.heap.get(temp_index + 1) {
            Some(val) => Some((temp_index + 1, val)),
            None => None,
        };
        let right = match self.heap.get(temp_index + 2) {
            Some(val) => Some((temp_index + 2, val)),
            None => None,
        };
        (left, right)
    }

    /// Returns the children nodes of the parent node at the index provided
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::binary_heap::BinaryHeap;
    ///
    /// let mut heap = BinaryHeap::new();
    ///
    /// heap.insert(10);
    /// heap.insert(9);
    /// heap.insert(8);
    /// heap.insert(7);
    /// heap.insert(6);
    ///
    /// assert_eq!(heap.depth(), 3);
    ///
    /// assert_eq!(heap.get_parent(1), Some((0, &10)));
    /// assert_eq!(heap.get_parent(3), Some((1, &9)));
    ///
    /// assert_eq!(heap.get_parent(0), None);
    /// assert_eq!(heap.get_parent(6), None);
    /// ```
    pub fn get_parent(&self, index: usize) -> Option<(usize, &T)> {
        if index >= self.len() || index == 0 {
            return None;
        }
        let parent_index = (index - 1) / 2;

        match self.heap.get(parent_index) {
            Some(val) => Some((parent_index, val)),
            None => None,
        }
    }

    /// Inserts the provided value, bubbling it up the heap as required to maintain the appropriate
    /// sorting on the heap
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::binary_heap::BinaryHeap;
    ///
    /// let mut heap = BinaryHeap::new();
    ///
    /// heap.insert(10);
    /// heap.insert(9);
    /// heap.insert(8);
    /// heap.insert(7);
    /// heap.insert(6);
    /// heap.insert(15);
    ///
    /// assert_eq!(heap.depth(), 3);
    ///
    /// assert_eq!(heap.get_parent(1), Some((0, &15)));
    /// assert_eq!(heap.get_children(0), (Some((1, &9)), Some((2, &10))));
    /// assert_eq!(heap.get_children(2), (Some((5, &8)), None));
    /// ```
    pub fn insert(&mut self, data: T) {
        self.heap.push(data);

        let mut inserted_index = self.len() - 1;

        while let Some((parent_index, parent_val)) = self.get_parent(inserted_index) {
            if &data > parent_val {
                self.heap.swap(inserted_index, parent_index);
                inserted_index = parent_index;
            } else {
                break;
            }
        }
    }
}
