//! # Unstable Binary Heap
//!
//! A simple heap allocated node based binary heap which contains the following properties:
//! 1. Each parent has at most two nodes
//! 2. A binary heap is as compact as possible, with left children being filled first
//! 3. The type of the binary heap (min/max) will affect how nodes are inserted into it
//!
//! This implementation uses an underlying `Vec<T>` to store the `BinaryHeap<T>` so limitations & performance
//! are based off Rust's `Vec`.
//!
//! Note: This binary heap is **unstable**, insertion order is not maintained
//!
//! # Examples
//!
//! You can instantiate a binary heap in 2 ways
//! 1. If the type of the heap, `BinaryHeap<T>` satisfies the trait that `T: Ord` and
//! the `Ord` implementation is suitable for your use case, then a heap can be instantiated with [`new`]
//! 2. If custom ordering logic is required, _for example, in the case of a **Priority Queue**_ then
//! a custom comparator function can be provided to the heap when instantiating it
//! using the [`with_custom_comparator_fn`] method
//!
//! The first argument to both methods of instantiating is the heap type, ie. whether you want it to be
//! a minimum or maximum heap
//!
//! ```rust
//! use data_structures::binary_heap::{BinaryHeap, BinaryHeapType};
//!
//! // Instantiating using new
//! let heap: BinaryHeap<i32> = BinaryHeap::new(BinaryHeapType::Min);
//! assert_eq!(heap.len(), 0);
//!
//!
//! // Providing a custom comparator function
//! struct SampleStruct {
//!     data: i32,
//!     priority: u32
//! }
//!
//! let cmp = |a: &SampleStruct, b: &SampleStruct| a.priority.cmp(&b.priority);
//!
//! let heap: BinaryHeap<SampleStruct> =
//!     BinaryHeap::with_custom_comparator_fn(BinaryHeapType::Max, &cmp);
//! assert!(heap.is_empty())
//! ```
//!
//! ## Use as a Priority Queue
//!
//! The API of the Binary Heap is extended to allow you to create a fully functional priority queue
//! from it. In order to do so you need to provide a custom comparator function which specifies how
//! the data in the heap should be sorted, as well as if it should be sorted by min or max (depending
//! on what your comparator function returns)
//!
//! ```rust
//! use data_structures::binary_heap::{BinaryHeap, BinaryHeapType};
//! struct PriorityStruct {
//!     data: String,
//!     priority: u32
//! }
//!
//! // The custom function must return an Ordering
//! let cmp = |a: &PriorityStruct, b: &PriorityStruct| a.priority.cmp(&b.priority);
//!
//! // For our example use case, the lower the value of the priority, the more important it is
//! let mut heap = BinaryHeap::with_custom_comparator_fn(BinaryHeapType::Min, &cmp);
//!
//! let data_1 = PriorityStruct {
//!     data: String::from("Task 1"),
//!     priority: 10,
//! };
//!
//! let data_2 = PriorityStruct {
//!     data: String::from("Task 2"),
//!     priority: 5,
//! };
//!
//! let data_3 = PriorityStruct {
//!     data: String::from("Task 3"),
//!     priority: 1,
//! };
//!
//! heap.insert(data_1);
//! heap.insert(data_2);
//! heap.insert(data_3);
//!
//! assert_eq!(heap.get_root().unwrap().priority, 1);
//! assert_eq!(heap.get_root().unwrap().data, String::from("Task 3"));
//! ```
//!
//! [`new`]: ./struct.BinaryHeap.html#method.new
//! [`with_custom_comparator_fn`]: ./struct.BinaryHeap.html#method.with_custom_comparator_fn

use std::cmp::Ordering;

// Can't implement Deref for BinaryHeap, as we don't want to offer the full Vec API, as sorting
// or iterating over the heap using Vec logic would break the structure

/// # Binary Heap
///
/// A simple heap allocated node based binary heap which contains the following properties:
/// 1. Each parent has at most two nodes
/// 2. A binary heap is as compact as possible, with left children being filled first
/// 3. The type of the binary heap (min/max) will affect how nodes are inserted into it
/// # Examples
/// ```rust
/// use data_structures::binary_heap::{BinaryHeap, BinaryHeapType};
///
/// let mut heap = BinaryHeap::new(BinaryHeapType::Min);
/// assert!(heap.is_empty());
///
/// heap.insert(10);
/// heap.insert(9);
/// heap.insert(8);
/// heap.insert(7);
/// heap.insert(6);
///
/// // As it is a Minimum Binary Heap, the root should be the lowest value
/// assert_eq!(heap.get_root(), Some(&6));
/// assert_eq!(heap.get_children(0), (Some((1, &7)), Some((2, &9))));
///
/// // Check the depth and the length
/// assert_eq!(heap.depth(), 3);
/// assert_eq!(heap.len(), 5);
///
/// // Extract the root
/// assert_eq!(heap.extract_root(), Some(6));
/// assert_eq!(heap.get_root(), Some(&7));
///
/// assert_eq!(heap.depth(), 3);
/// assert_eq!(heap.len(), 4);
///
/// assert_eq!(heap.extract_root(), Some(7));
/// assert_eq!(heap.get_root(), Some(&8));
///
/// assert_eq!(heap.depth(), 2);
/// assert_eq!(heap.len(), 3);
/// ```
///
/// ## Use as a Priority Queue
///
/// The API of the Binary Heap is extended to allow you to create a fully functional priority queue
/// from it. In order to do so you need to provide a custom comparator function which specifies how
/// the data in the heap should be sorted, as well as if it should be sorted by min or max (depending
/// on what your comparator function returns)
///
/// ```rust
/// use data_structures::binary_heap::{BinaryHeap, BinaryHeapType};
/// struct PriorityStruct {
///     data: String,
///     priority: u32
/// }
///
/// // The custom function must return an Ordering
/// let cmp = |a: &PriorityStruct, b: &PriorityStruct| a.priority.cmp(&b.priority);
///
/// // For our example use case, the lower the value of the priority, the more important it is
/// let mut heap = BinaryHeap::with_custom_comparator_fn(BinaryHeapType::Min, &cmp);
///
/// let data_1 = PriorityStruct {
///     data: String::from("Task 1"),
///     priority: 10,
/// };
///
/// let data_2 = PriorityStruct {
///     data: String::from("Task 2"),
///     priority: 5,
/// };
///
/// let data_3 = PriorityStruct {
///     data: String::from("Task 3"),
///     priority: 1,
/// };
///
/// heap.insert(data_1);
/// heap.insert(data_2);
/// heap.insert(data_3);
///
/// assert_eq!(heap.get_root().unwrap().priority, 1);
/// assert_eq!(heap.get_root().unwrap().data, String::from("Task 3"));
/// ```
pub struct BinaryHeap<'a, T> {
    heap: Vec<T>,
    cmp: Box<&'a dyn Fn(&T, &T) -> Ordering>,
    heap_type: BinaryHeapType,
    comparator: Ordering,
}

/// Specifies whether the Heap Type should be a Maximum Binary Heap, or Minimum Binary Heap
#[derive(Copy, Clone, PartialEq, Eq)]
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

    /// Returns an optional tuple containing the index of the child node and a reference to
    /// the value of the child node at the specified parent index
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
    #[allow(clippy::type_complexity)]
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
    pub fn get(&self, index: usize) -> Option<&T> {
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

    /// Changes the heap type to the provided value. If the same heap type is provided, then the
    /// function just returns. If the alternate heap type is provided then a new Binary Heap is
    /// created and the data is inserted into it from scratch.
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
    ///
    /// heap.set_heap_type(BinaryHeapType::Min);
    /// assert_eq!(heap.depth(), 3);
    /// assert_eq!(heap.get_root(), Some(&6));
    /// assert_eq!(heap.get_children(0), (Some((1, &8)), Some((2, &7))));
    /// ```
    pub fn set_heap_type(&mut self, heap_type: BinaryHeapType) {
        if heap_type == self.heap_type {
            return;
        }

        let data = std::mem::replace(&mut self.heap, Vec::new());
        let cmp = std::mem::replace(&mut self.cmp, Box::new(&|_, _| Ordering::Greater));

        *self = Self {
            heap: Vec::new(),
            cmp,
            heap_type,
            comparator: match heap_type {
                BinaryHeapType::Max => Ordering::Greater,
                BinaryHeapType::Min => Ordering::Less,
            },
        };
        data.into_iter().rev().for_each(|node| self.insert(node));
    }

    /// Extracts the root value from the heap and returns it
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
    /// assert_eq!(heap.extract_root(), Some(10));
    /// assert_eq!(heap.get_root(), Some(&9));
    /// ```
    pub fn extract_root(&mut self) -> Option<T> {
        if self.len() == 1 {
            return self.heap.pop();
        }
        let heap_length = self.len();
        self.heap.swap(0, heap_length - 1);
        let root = self.heap.pop();

        // Bubble the (probably) incorrect back down the tree
        let mut index = 0;

        // The logic within this loop is somewhat messy, however due to the borrow checker and
        // requirement to get a non-mutable reference to child nodes (has to be non-mutable as
        // there are potentially 2 children, which would break the only 1 immutable reference rule)
        // and then requiring a mutable reference to the heap in order to perform swaps. This
        // verbose way of performing the comparison allows the desired logic to occur without
        // having to use unsafe
        loop {
            let mut did_swap = false;
            let children = self.get_children(index);

            match children {
                (Some(left), Some(right)) => {
                    let mut value_to_swap = right.1;

                    let index_to_swap = if (self.cmp)(left.1, right.1) == self.comparator
                        || (self.cmp)(left.1, right.1) == Ordering::Equal
                    {
                        value_to_swap = left.1;
                        left.0
                    } else {
                        right.0
                    };

                    if (self.cmp)(
                        value_to_swap,
                        self.get(index)
                            .expect("This should always be within the bound of the vec"),
                    ) == self.comparator
                    {
                        self.heap.swap(index, index_to_swap);
                        index = index_to_swap;
                        did_swap = true;
                    }
                }
                (Some(left), None) => {
                    let index_to_swap = left.0;
                    if (self.cmp)(
                        left.1,
                        self.get(index)
                            .expect("This should always be within the bound of the vec"),
                    ) == self.comparator
                    {
                        self.heap.swap(index, index_to_swap);
                        index = index_to_swap;
                        did_swap = true;
                    }
                }
                // It would be incorrect for this case to actually occur given our insert logic
                (None, Some(right)) => {
                    let index_to_swap = right.0;
                    if (self.cmp)(
                        right.1,
                        self.get(index)
                            .expect("This should always be within the bound of the vec"),
                    ) == self.comparator
                    {
                        self.heap.swap(index, index_to_swap);
                        index = index_to_swap;
                        did_swap = true;
                    }
                }
                (None, None) => {}
            }

            if !did_swap {
                break;
            }
        }

        root
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn min_insert() {
        let mut heap = BinaryHeap::new(BinaryHeapType::Min);

        heap.insert(10);
        heap.insert(9);
        heap.insert(8);

        assert_eq!(heap.get_root(), Some(&8));
        assert_eq!(heap.get_children(0), (Some((1, &10)), Some((2, &9))));
        assert_eq!(heap.depth(), 2);

        heap.insert(7);
        heap.insert(6);
        heap.insert(15);

        assert_eq!(heap.depth(), 3);

        assert_eq!(heap.get_root(), Some(&6));

        assert_eq!(heap.get_parent(1), Some((0, &6)));
        assert_eq!(heap.get_children(0), (Some((1, &7)), Some((2, &9))));
        assert_eq!(heap.get_children(2), (Some((5, &15)), None));
    }

    #[test]
    fn min_extract_root() {
        let mut heap = BinaryHeap::new(BinaryHeapType::Min);

        heap.insert(10);
        heap.insert(9);
        heap.insert(8);
        heap.insert(7);
        heap.insert(6);

        assert_eq!(heap.depth(), 3);

        assert_eq!(heap.extract_root(), Some(6));
        assert_eq!(heap.get_root(), Some(&7));
    }
}
