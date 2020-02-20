//! # Unstable Binary Heap
//!
//! A simple heap allocated node based binary heap which contains the following properties:
//! 1. Each parent has at most two nodes
//! 2. A binary heap is as compact as possible, with left children being filled first
//! 3. The type of the binary heap (min/max) will affect how nodes are inserted into it
//!
//! Given the properties of a Binary Heap, it's simple to model in a Vec<T>, therefore for
//! simplicity this approach coupled with the optimisations made to Rust's Vec, this
//! route has been taken.
//!
//! Note: This binary heap is **unstable**, insertion order is not maintained
//!
//! # Examples
//!
//! You can instantiate a binary heap in 2 ways
//! 1. If the type of the heap, `BinaryHeap<T>` satisfies the trait that `T: Ord`, and
//! the default ordering implementation can be used, then a heap can be instantiated with [`new`]
//! 2. If custom ordering logic is required, _for example, in the case of a priority queue_ then
//! a custom comparator function can be provided to the heap using the [`with_custom_comparator_fn`]
//! method
//!
//! The first argument to both methods of instantiating is the heap type, whether you want it to be
//! a minimum or maximum heap
//!
//! ```rust
//! use data_structures::binary_heap::{BinaryHeap, BinaryHeapType};
//!
//! let heap: BinaryHeap<i32> = BinaryHeap::new(BinaryHeapType::Min);
//! assert_eq!(heap.len(), 0);
//!
//! struct SampleStruct {
//!     data: i32,
//!     priority: u32
//! }
//!
//! let cmp = |a: &SampleStruct, b: &SampleStruct| a.priority.cmp(&b.priority);
//!
//! let heap: BinaryHeap<SampleStruct> = BinaryHeap::with_custom_comparator_fn(BinaryHeapType::Max, &cmp);
//! assert!(heap.is_empty())
//! ```

use std::cmp::Ordering;

// Can't implement Deref for BinaryHeap, as we don't want to offer the full Vec API, as sorting
// or iterating over the heap using Vec logic would break the structure

pub struct BinaryHeap<'a, T> {
    heap: Vec<T>,
    cmp: Box<&'a dyn Fn(&T, &T) -> Ordering>,
    heap_type: BinaryHeapType,
    comparator: Ordering,
}

#[derive(Copy, Clone)]
pub enum BinaryHeapType {
    Max,
    Min,
}

impl<'a, T> BinaryHeap<'a, T> {
    /// Constructs a new, empty `BinaryHeap<T>`, in the example below it is a Max Binary Heap
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::binary_heap::{BinaryHeap, BinaryHeapType};
    ///
    /// let mut heap: BinaryHeap<i32> = BinaryHeap::new(BinaryHeapType::Max);
    ///
    /// assert_eq!(heap.len(), 0);
    /// assert!(heap.is_empty());
    /// ```
    pub fn new(heap_type: BinaryHeapType) -> Self
    where
        T: Ord,
    {
        Self {
            heap: Vec::new(),
            cmp: Box::new(&|a, b| a.cmp(b)),
            heap_type,
            comparator: match heap_type {
                BinaryHeapType::Max => Ordering::Greater,
                BinaryHeapType::Min => Ordering::Less,
            },
        }
    }

    /// Constructs a new, empty `BinaryHeap<T>`, with a custom comparator function,
    /// this can be used to create a priority queue or other bespoke sorting logic
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::binary_heap::{BinaryHeap, BinaryHeapType};
    ///
    /// let cmp = |a: &i32, b: &i32| a.cmp(b);
    /// let mut heap: BinaryHeap<i32> = BinaryHeap::with_custom_comparator_fn(BinaryHeapType::Min, &cmp);
    ///
    /// assert_eq!(heap.len(), 0);
    /// assert!(heap.is_empty());
    /// ```
    pub fn with_custom_comparator_fn<F: 'a>(heap_type: BinaryHeapType, cmp: &'a F) -> Self
    where
        F: Fn(&T, &T) -> Ordering,
    {
        Self {
            heap: Vec::new(),
            cmp: Box::new(cmp),
            heap_type,
            comparator: match heap_type {
                BinaryHeapType::Max => Ordering::Greater,
                BinaryHeapType::Min => Ordering::Less,
            },
        }
    }

    /// Returns the number of elements in the binary heap, also referred to as it's _length_
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::binary_heap::{BinaryHeap, BinaryHeapType};
    ///
    /// let mut heap = BinaryHeap::new(BinaryHeapType::Max);
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
    /// use data_structures::binary_heap::{BinaryHeap, BinaryHeapType};
    ///
    /// let mut heap = BinaryHeap::new(BinaryHeapType::Max);
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
    /// use data_structures::binary_heap::{BinaryHeap, BinaryHeapType};
    ///
    /// let mut heap = BinaryHeap::new(BinaryHeapType::Max);
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

    /// Returns a reference to the root node of the Heap
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::binary_heap::{BinaryHeap, BinaryHeapType};
    ///
    /// let mut heap = BinaryHeap::new(BinaryHeapType::Max);
    ///
    /// heap.insert(10);
    /// heap.insert(9);
    /// heap.insert(8);
    ///
    /// assert_eq!(heap.get_root(), Some(&10))
    /// ```
    pub fn get_root(&self) -> Option<&T> {
        self.heap.get(0)
    }

    /// Returns an optional tuple containing the index of the child node and the value of the child
    /// node at the specified parent index
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::binary_heap::{BinaryHeap, BinaryHeapType};
    ///
    /// let mut heap = BinaryHeap::new(BinaryHeapType::Max);
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
    /// use data_structures::binary_heap::{BinaryHeap, BinaryHeapType};
    ///
    /// let mut heap = BinaryHeap::new(BinaryHeapType::Max);
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
    /// use data_structures::binary_heap::{BinaryHeap, BinaryHeapType};
    ///
    /// let mut heap = BinaryHeap::new(BinaryHeapType::Max);
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
            if (self.cmp)(&self.heap[inserted_index], parent_val) == self.comparator {
                self.heap.swap(inserted_index, parent_index);
                inserted_index = parent_index;
            } else {
                break;
            }
        }
    }

    /// Returns a reference to the node at the provided index
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::binary_heap::{BinaryHeap, BinaryHeapType};
    ///
    /// let mut heap = BinaryHeap::new(BinaryHeapType::Max);
    ///
    /// heap.insert(10);
    /// heap.insert(9);
    /// heap.insert(8);
    /// heap.insert(7);
    /// heap.insert(6);
    ///
    /// assert_eq!(heap.depth(), 3);
    ///
    /// assert_eq!(heap.get(1), Some(&9));
    /// assert_eq!(heap.get(3), Some(&7));
    /// assert_eq!(heap.get(6), None);
    /// ```
    pub fn get(&mut self, index: usize) -> Option<&T> {
        self.heap.get(index)
    }

    /// Returns a mutable reference to the node at the provided index
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::binary_heap::{BinaryHeap, BinaryHeapType};
    ///
    /// let mut heap = BinaryHeap::new(BinaryHeapType::Max);
    ///
    /// heap.insert(10);
    /// heap.insert(9);
    /// heap.insert(8);
    /// heap.insert(7);
    /// heap.insert(6);
    ///
    /// assert_eq!(heap.depth(), 3);
    ///
    /// assert_eq!(heap.get_mut(1), Some(&mut 9));
    /// assert_eq!(heap.get_mut(3), Some(&mut 7));
    /// assert_eq!(heap.get_mut(6), None);
    ///
    /// *heap.get_mut(1).unwrap() = 50;
    /// assert_eq!(heap.get(1), Some(&50));
    /// ```
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.heap.get_mut(index)
    }
}
