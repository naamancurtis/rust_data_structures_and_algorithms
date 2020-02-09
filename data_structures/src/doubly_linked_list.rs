//! # Doubly Linked List
//!
//! A growable doubly linked list with heap allocated contents. **Note:** this is just a re-write of the
//! LinkedList found in [Contain RS](https://github.com/contain-rs/linked-list/blob/master/src/lib.rs) and
//! was useful for me just to look through and understand 1 step at a time. If you plan to use an actual
//! Doubly Linked List, I'd advise using the one found in `std::collections` or the one linked above
//!
//! It has `O(1)` access, insertion and removal from the *head* or *tail* elements.
//!
//! # Examples
//! You can explicitly create a new list with [`new`]
//! ```rust
//! use data_structures::doubly_linked_list::DoublyLinkedList;
//!
//! let mut list: DoublyLinkedList<i32> = DoublyLinkedList::new();
//! ```
//!
//! or alternatively use the provided [`DoublyLinkedList!`] macro
//! ```rust
//! #[macro_use]
//! use data_structures::doubly_linked_list;
//!
//! let mut list = doubly_linked_list![1, 2, 3]; // Head = 3
//! ```
//!
//! Once the list is instantiated you can then [`push_front`], [`push_back`] [`pop_front`] and [`pop_back`]
//! methods, all of which resolve in constant time (**O**(1))
//!
//! ```rust
//! #[macro_use]
//! use data_structures::doubly_linked_list;
//!
//! let mut list = doubly_linked_list![1, 2, 3]; // Head = 3
//!
//! list.push_front(20); // Push a new value onto the head of the list
//!
//! assert_eq!(list.len(), 4);
//!
//! assert_eq!(list.pop_front(), Some(20)); // Popping a value returns `Option<T>`
//! ```
//!
//! [`new`]: ./struct.DoublyLinkedList.html#method.new
//! [`push_front`]: ./struct.DoublyLinkedList.html#method.push_front
//! [`push_back`]: ./struct.DoublyLinkedList.html#method.push_back
//! [`pop_front`]: ./struct.DoublyLinkedList.html#method.pop_front
//! [`pop_back`]: ./struct.DoublyLinkedList.html#method.pop_back
//! [`DoublyLinkedList!`]: ../macro.DoublyLinkedList.html

use std::default::Default;
use std::fmt::{Debug, Error, Formatter};
use std::marker::PhantomData;
use std::{mem, ptr};

/// # A safe abstraction around unsafe implementation of a Doubly Linked List
///
/// This list maintains a pointers to the element at the *head* and *tail* of the list. In turn each element
/// maintains a pointer to the element immediately before and after it. Each node in the list **owns** the _next_ node,
/// in the list, the reverse pointers are non-owning.
///
/// # Examples
///
/// ```rust
/// use data_structures::doubly_linked_list::DoublyLinkedList;
///
/// let mut list = DoublyLinkedList::new();
/// list.push_front(10);
/// list.push_front(20);
/// list.push_front(30); // <- This is our head
///
/// println!("{:?}", list); // Debug has been implemented for DoublyLinkedList
/// // Prints: H: | 30 | 20 | 10 | :T
///
/// assert_eq!(list.len(), 3);
///
/// let element = list.pop_front(); // We pop the head off the list
/// assert_eq!(element, Some(30));
/// assert_eq!(list.pop_front(), Some(20));
/// assert_eq!(list.pop_front(), Some(10));
/// assert_eq!(list.pop_front(), None); // Once we exhaust the list, None is returned
/// ```
///
/// ## Macro
/// The [`DoublyLinkedList!`] macro can be used to make initialization more convenient, the
/// first value within the square `[]` being the tail, and the final being the head.
///
/// ```rust
/// #[macro_use]
/// use data_structures::doubly_linked_list;
///
/// let mut list = doubly_linked_list![1, 2, 3]; // Head = 3
///
/// assert_eq!(list.pop_front(), Some(3));
/// ```
///
/// ## Use as a Stack
///
/// Methods are offered to enable O(1) insertion and removal from the head of the list
/// ```rust
/// #[macro_use]
/// use data_structures::doubly_linked_list;
///
/// let mut list = doubly_linked_list![2, 3, 4];
///
/// list.push_front(5); // Push to the head
/// list.push_back(1); // Push to the tail
///
/// while let Some(head) = list.pop_front() { // Extracting elements from the head of the list
///     // Prints: 5, 4, 3, 2, 1
///     println!("{}", head);
/// }
///
/// list.push_front(10);
/// assert_eq!(list.pop_back(), Some(10)) // Popping an element from the tail of the list
/// ```
///
/// ## Use as a Queue
///
/// The Methods are offered also make it ideal for use as a queue and enable O(1) insertion and removal from the head and tail of the list
/// ```rust
/// #[macro_use]
/// use data_structures::doubly_linked_list;
///
/// let mut list = doubly_linked_list![2, 3, 4];
///
/// list.push_back(1); // Push to the head
/// list.push_back(0); // Push to the tail
///
/// while let Some(head) = list.pop_front() { // Extracting elements from the tail of the list
///     // Prints: 4, 3, 2, 1, 0
///     println!("{}", head);
/// }
///
/// ```
///
/// ## Iterating over a Doubly Linked List
///
/// However, iteration in both directions is supported, however if required an alternate data structure
/// might be more effective for the use case
///
/// ```rust
/// #[macro_use]
/// use data_structures::doubly_linked_list;
///
/// let list = doubly_linked_list![1, 2, 3];
///
/// let mut iter = list.into_iter();
///
///
/// assert_eq!(iter.next(), Some(3));
/// assert_eq!(iter.next_back(), Some(1));
///
/// assert_eq!(iter.next(), Some(2)); // Empty the iterator
///
/// assert_eq!(iter.next(), None);
/// assert_eq!(iter.next_back(), None);
/// ```
///
#[derive(Default)]
pub struct DoublyLinkedList<T> {
    head: Link<T>,
    tail: RawLink<T>,
    length: usize,
}

struct Node<T> {
    data: T,
    next: Link<T>,
    prev: RawLink<T>,
}

type Link<T> = Option<Box<Node<T>>>;
struct RawLink<T> {
    ptr: *const Node<T>,
}

impl<T> DoublyLinkedList<T> {
    /// Constructs a new, empty `DoublyLinkedList<T>`
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::doubly_linked_list::DoublyLinkedList;
    ///
    /// let mut list: DoublyLinkedList<i32> = DoublyLinkedList::new();
    /// assert_eq!(list.len(), 0);
    /// ```
    pub fn new() -> Self {
        Self {
            head: None,
            tail: RawLink::default(),
            length: 0,
        }
    }

    /// Returns the number of elements in the list, also referred to as it's _length_
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::doubly_linked_list;
    ///
    /// let mut list = doubly_linked_list![1, 2, 3];
    ///
    /// assert_eq!(list.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.length
    }

    /// Returns true if the list is empty, false if it contains 1 or more elements
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::doubly_linked_list;
    /// use data_structures::doubly_linked_list::DoublyLinkedList;
    ///
    /// let mut list = doubly_linked_list![1, 2, 3];
    /// assert_eq!(list.is_empty(), false);
    ///
    /// let mut list: DoublyLinkedList<i32> = doubly_linked_list![];
    /// assert_eq!(list.is_empty(), true);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    /// Clears the list
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::doubly_linked_list;
    ///
    /// let mut list = doubly_linked_list![1, 2, 3];
    /// assert_eq!(list.is_empty(), false);
    ///
    /// list.clear();
    /// assert_eq!(list.is_empty(), true);
    /// ```
    pub fn clear(&mut self) {
        *self = Self::new();
    }

    /// Pushes the provided element to the head of the list
    ///
    /// # Panics
    /// Panics if the number of elements in the list overflows a `usize`
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::doubly_linked_list::DoublyLinkedList;
    ///
    /// let mut list = DoublyLinkedList::new();
    /// list.push_front(1);
    /// list.push_front(5);
    /// list.push_front(10);
    ///
    /// assert_eq!(list.len(), 3);
    /// ```
    pub fn push_front(&mut self, data: T) {
        self.length += 1;

        let mut new_node = Box::new(Node::new(data));
        match self.head.take() {
            Some(head) => new_node.link(head),
            None => self.tail = RawLink::from(&mut *new_node),
        }
        self.head = Some(new_node);
    }

    /// Pops the element off the head of the list and returns it, returning `None` if the list
    /// is empty
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::doubly_linked_list;
    ///
    /// let mut list = doubly_linked_list![1, 5, 10];
    ///
    /// assert_eq!(list.pop_front(), Some(10));
    /// assert_eq!(list.pop_front(), Some(5));
    /// assert_eq!(list.pop_front(), Some(1));
    /// assert_eq!(list.pop_front(), None);
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        self.head.take().map(|mut old_head| {
            self.length -= 1;
            match old_head.take_next() {
                Some(node) => self.head = Some(node),
                None => self.tail = RawLink::default(),
            }
            old_head.data
        })
    }

    /// Pushes the provided element to the tail of the list
    ///
    /// # Panics
    /// Panics if the number of elements in the list overflows a `usize`
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::doubly_linked_list::DoublyLinkedList;
    ///
    /// let mut list = DoublyLinkedList::new();
    /// list.push_back(1);
    /// list.push_back(5);
    /// list.push_back(10);
    ///
    /// assert_eq!(list.len(), 3);
    /// assert_eq!(list.pop_front(),Some(1));
    /// ```
    pub fn push_back(&mut self, data: T) {
        self.length += 1;

        let mut new_node = Box::new(Node::new(data));
        let mut old_tail = mem::replace(&mut self.tail, RawLink::from(&mut *new_node));
        match old_tail.as_mut() {
            Some(tail) => tail.link(new_node),
            None => self.head = Some(new_node),
        }
    }

    /// Pops the element off the tail of the list and returns it, returning `None` if the list
    /// is empty.
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::doubly_linked_list;
    ///
    /// let mut list = doubly_linked_list![1, 5, 10];
    ///
    /// assert_eq!(list.pop_back(), Some(1));
    /// assert_eq!(list.pop_back(), Some(5));
    /// assert_eq!(list.pop_back(), Some(10));
    /// assert_eq!(list.pop_back(), None);
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        self.tail.take().as_mut().and_then(|tail| {
            self.length -= 1;
            match tail.prev.take().as_mut() {
                Some(prev_node) => {
                    self.tail = RawLink::from(prev_node);
                    prev_node.next.take().map(|node| node.data)
                }
                None => self.head.take().map(|node| node.data),
            }
        })
    }

    /// Returns a reference to the next element in the list
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::doubly_linked_list;
    ///
    /// let mut list = doubly_linked_list![1, 5, 10];
    ///
    /// // Because the element is wrapped in an `Rc<RefCell<T>>>` we need to `.unwrap()` the
    /// // option and de-reference the `Ref` to receive the value
    /// assert_eq!(*(list.peek_front().unwrap()), 10);
    ///
    /// // *list.peek_front().unwrap() = 50; - This value can't be assigned to (it will error) as it doesn't implement
    /// // the DerefMut trait (see .peek_front_mut() if a mutable reference is needed)
    ///
    /// assert_eq!(&* list.peek_front().unwrap(), &10); // .peek() doesn't consume the element
    /// ```
    pub fn peek_front(&self) -> Option<&T> {
        self.head.as_ref().map(|node| &node.data)
    }

    /// Returns a mutable reference to the next element in the list
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::doubly_linked_list;
    ///
    /// let mut list = doubly_linked_list![1, 5, 10];
    ///
    /// assert_eq!(&mut *(list.peek_front_mut().unwrap()), &mut 10);
    /// assert_eq!(list.len(), 3);
    ///
    /// *list.peek_front_mut().unwrap() = 50;
    /// assert_eq!(list.len(), 3);
    ///
    /// assert_eq!(list.pop_front(), Some(50));
    /// ```
    pub fn peek_front_mut(&mut self) -> Option<&mut T> {
        self.head.as_mut().map(|node| &mut node.data)
    }

    /// Returns a reference to the last element in the list
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::doubly_linked_list;
    ///
    /// let mut list = doubly_linked_list![1, 5, 10];
    ///
    /// // Because the element is wrapped in an `Rc<RefCell<T>>>` we need to `.unwrap()` the
    /// // option and de-reference the `Ref` to receive the value
    /// assert_eq!(*(list.peek_back().unwrap()), 1);
    ///
    /// // *list.peek_back().unwrap() = 50; - This value can't be assigned to (it will error) as it doesn't implement
    /// // DerefMut (see .peek_back_mut() if a mutable reference is needed)
    ///
    /// assert_eq!(&* list.peek_back().unwrap(), &1); // .peek() doesn't consume the element
    /// ```
    pub fn peek_back(&self) -> Option<&T> {
        self.tail.as_ref().map(|node| &node.data)
    }

    /// Returns a mutable reference to the last element in the list
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::doubly_linked_list;
    ///
    /// let mut list = doubly_linked_list![1, 5, 10];
    ///
    /// assert_eq!(&mut *(list.peek_back_mut().unwrap()), &mut 1);
    /// assert_eq!(list.len(), 3);
    ///
    /// *list.peek_back_mut().unwrap() = 25;
    /// assert_eq!(list.len(), 3);
    ///
    /// assert_eq!(list.pop_back(), Some(25));
    /// ```
    pub fn peek_back_mut(&mut self) -> Option<&mut T> {
        self.tail.as_mut().map(|node| &mut node.data)
    }

    pub fn iter(&self) -> Iter<T> {
        Iter {
            head_next: &self.head,
            tail_next: &self.tail,
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<T> {
        let raw_head = match self.head.as_mut() {
            Some(head) => RawLink::from(&mut **head),
            None => RawLink::default(),
        };

        IterMut {
            head_next: raw_head,
            tail_next: self.tail.clone(),
            phantom: PhantomData,
        }
    }

    /// Consumes the list, returning a Vec<T> filled with the elements in the order of head -> tail
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::doubly_linked_list;
    ///
    /// let mut list = doubly_linked_list![1, 5, 10, 25, 50];
    ///
    /// assert_eq!(list.len(), 5);
    ///
    /// assert_eq!(list.into_vec(), vec![50, 25, 10, 5, 1])
    /// ```
    pub fn into_vec(self) -> Vec<T> {
        self.into_iter().collect()
    }
}

// ============ Iterator Wrappers ============

/// An iterator that moves out of a DoublyLinkedList, consuming it in the process
///
/// # Examples
///
/// ```rust
/// #[macro_use]
/// use data_structures::doubly_linked_list;
///
/// let mut list = doubly_linked_list![1, 5, 10, 25, 50];
///
/// let mut iter = list.into_iter(); // list has been `moved` and can no longer be used
///
/// assert_eq!(iter.next(), Some(50));
/// assert_eq!(iter.next_back(), Some(1)); // We can also iterate in reverse
///
/// // list.peek() // Won't compile, as the list has been consumed
/// ```
pub struct IntoIter<T>(DoublyLinkedList<T>);

impl<T> IntoIterator for DoublyLinkedList<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self)
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop_front()
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.pop_back()
    }
}

/// An iterator that provides immutable references over a Doubly Linked List, it does not consume it in the process
///
/// # Examples
///
/// ```rust
/// #[macro_use]
/// use data_structures::doubly_linked_list;
///
/// let mut list = doubly_linked_list![1, 5, 10, 25, 50];
///
/// let mut iter = list.iter();
///
/// assert_eq!(iter.next(), Some(&50));
/// assert_eq!(iter.next(), Some(&25));
/// assert_eq!(iter.next_back(), Some(&1)); // we can also iterate in reverse
///
/// // Checking that the original list is the way we would expect it to be:
/// assert_eq!(list.pop_front(), Some(50)); // the first element hasn't been consumed
/// assert_eq!(list.pop_front(), Some(25)); // nor has the second element
/// assert_eq!(list.pop_back(), Some(1)); // and the tail element is still 1
/// ```
pub struct Iter<'a, T> {
    head_next: &'a Link<T>,
    tail_next: &'a RawLink<T>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.head_next.as_ref().map(|node| {
            self.head_next = &node.next;
            &node.data
        })
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.tail_next.as_ref().map(|node| {
            self.tail_next = &node.prev;
            &node.data
        })
    }
}

/// An iterator that provides mutable references over a Doubly Linked List, it does not consume it in the process
///
/// # Examples
///
/// ```rust
/// #[macro_use]
/// use data_structures::doubly_linked_list;
///
/// let mut list = doubly_linked_list![1, 5, 10, 25, 50];
///
/// let mut iter = list.iter_mut();
///
/// assert_eq!(iter.next(), Some(&mut 50));
///
/// iter.next().map(|val| *val *= 10); // lets mutate the second value
///
/// assert_eq!(iter.next_back(), Some(&mut 1)); // we can also iterate in reverse
///
/// // Checking that the original list is the way we would expect it to be:
/// assert_eq!(list.pop_front(), Some(50)); // the first element hasn't been consumed
/// assert_eq!(list.pop_front(), Some(250)); // the second element is mutated as we would expect
/// assert_eq!(list.pop_back(), Some(1)); // the tail element is still 1
/// ```
pub struct IterMut<'a, T> {
    head_next: RawLink<T>,
    tail_next: RawLink<T>,
    phantom: PhantomData<&'a mut T>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        self.head_next.take().as_mut().map(|node| {
            self.head_next = match node.next {
                Some(ref mut head) => RawLink::from(&mut **head),
                None => RawLink::default(),
            };

            unsafe { &mut *((&mut node.data) as *mut _) }
        })
    }
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.tail_next.take().as_mut().map(|node| {
            self.tail_next = node.prev.clone();

            unsafe { &mut *((&mut node.data) as *mut _) }
        })
    }
}

// ============ /Iterator Wrappers ============

impl<T> Drop for DoublyLinkedList<T> {
    fn drop(&mut self) {
        while self.pop_front().is_some() {}
    }
}

/// Provides a shorthand macro for creating a double-ended list with multiple elements in it.
///
/// The first value contained within the `[]` being the tail and the last being the head.
///
/// # Examples
///
/// ```rust
/// #[macro_use]
/// use data_structures::doubly_linked_list;
/// use data_structures::doubly_linked_list::DoublyLinkedList;
///
/// // Tail: 1
/// // Head: 5
///
/// // Macro notation:
/// let mut list = doubly_linked_list![1, 2, 3, 4, 5];
///
/// assert_eq!(list.pop_front(), Some(5));
///
/// // Longhand notation:
/// let mut list = DoublyLinkedList::new();
/// list.push_front(1);
/// list.push_front(2);
/// list.push_front(3);
/// list.push_front(4);
/// list.push_front(5);
///
/// assert_eq!(list.pop_front(), Some(5));
/// ```
#[macro_export]
macro_rules! doubly_linked_list {
    ($($x:expr),*) => {
        {
            let mut temp_list = $crate::doubly_linked_list::DoublyLinkedList::new();
            $(
                temp_list.push_front($x);
            )*
            temp_list
        }
    };
}

impl<T> Node<T> {
    /// Returns an initialised version of Node
    fn new(data: T) -> Self {
        Self {
            data,
            next: None,
            prev: RawLink::default(),
        }
    }

    fn link(&mut self, mut next: Box<Self>) {
        next.prev = RawLink::from(self);
        self.next = Some(next);
    }

    fn take_next(&mut self) -> Option<Box<Self>> {
        let mut next = self.next.take();
        if let Some(node) = next.as_mut() {
            node.prev = RawLink::default();
        }
        next
    }
}

impl<T> Default for RawLink<T> {
    fn default() -> Self {
        Self {
            ptr: ptr::null_mut(),
        }
    }
}

impl<T> RawLink<T> {
    #[inline]
    fn from(ptr: *mut Node<T>) -> Self {
        Self { ptr }
    }

    #[inline]
    fn as_ref(&self) -> Option<&Node<T>> {
        if self.ptr.is_null() {
            return None;
        }

        unsafe { Some(&*self.ptr) }
    }

    #[inline]
    fn as_mut(&mut self) -> Option<&mut Node<T>> {
        if self.ptr.is_null() {
            return None;
        }

        unsafe { Some(&mut *(self.ptr as *mut Node<T>)) }
    }

    #[inline]
    fn take(&mut self) -> Self {
        mem::replace(self, RawLink::default())
    }

    #[inline]
    fn clone(&mut self) -> Self {
        RawLink { ptr: self.ptr }
    }
}

impl<T: Debug> Debug for DoublyLinkedList<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        let mut node = self.head.as_ref();
        write!(f, "H: ")?;
        while let Some(n) = node {
            write!(f, "| {:?}", n.data)?;
            node = n.next.as_ref();
            if node.is_some() {
                write!(f, " ")?;
            }
        }
        write!(f, " | :T")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn push_pop() {
        let mut list = DoublyLinkedList::new();
        list.push_front(1);
        list.push_front(2);
        list.push_front(3);

        assert_eq!(list.len(), 3);

        assert_eq!(list.pop_front(), Some(3));
        assert_eq!(list.pop_front(), Some(2));

        assert_eq!(list.len(), 1);

        list.push_front(4);
        list.push_front(5);

        assert_eq!(list.len(), 3);

        assert_eq!(list.pop_front(), Some(5));
        assert_eq!(list.pop_front(), Some(4));

        assert_eq!(list.len(), 1);

        assert_eq!(list.pop_front(), Some(1));
        assert_eq!(list.pop_front(), None);

        assert_eq!(list.len(), 0);
    }

    #[test]
    fn push_pop_back() {
        let mut list = DoublyLinkedList::new();

        // Check empty list behaves right
        assert_eq!(list.pop_back(), None);

        // Check pushing data
        list.push_back(1);
        list.push_back(2);
        list.push_back(3);

        // Check popping data
        assert_eq!(list.pop_back(), Some(3));
        assert_eq!(list.pop_back(), Some(2));

        // Check popping hasn't corrupted pushing
        list.push_back(4);
        list.push_back(5);

        // Check popping still works
        assert_eq!(list.pop_back(), Some(5));
        assert_eq!(list.pop_back(), Some(4));

        // Check exhaustion
        assert_eq!(list.pop_back(), Some(1));
        assert_eq!(list.pop_back(), None);
    }

    #[test]
    fn into_iter() {
        let list = doubly_linked_list![1, 2, 3];

        let mut iter = list.into_iter();

        assert_eq!(iter.next(), Some(3));
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next(), Some(1));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn iter() {
        let list = doubly_linked_list![1, 2, 3];

        let mut iter = list.iter();

        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn iter_mut() {
        let mut list = doubly_linked_list![1, 2, 3];

        let mut iter = list.iter_mut();

        *iter.next().unwrap() = 10;
        assert_eq!(iter.next(), Some(&mut 2));
        assert_eq!(iter.next(), Some(&mut 1));
        assert_eq!(iter.next(), None);
        assert_eq!(list.pop_front(), Some(10));
    }

    #[test]
    fn peek() {
        let mut list = doubly_linked_list![1, 2, 3];

        assert_eq!(list.peek_front(), Some(&3));
        assert_eq!(list.peek_front(), Some(&3));

        assert_eq!(list.peek_back(), Some(&1));
        assert_eq!(list.peek_back(), Some(&1));

        list.push_front(4);
        list.push_front(5);

        assert_eq!(list.peek_front(), Some(&5));
        assert_eq!(list.peek_front(), Some(&5));

        assert_eq!(list.peek_back(), Some(&1));
        assert_eq!(list.peek_back(), Some(&1));

        list.push_back(6);
        list.push_back(7);

        assert_eq!(list.peek_front(), Some(&5));
        assert_eq!(list.peek_front(), Some(&5));

        assert_eq!(list.peek_back(), Some(&7));
        assert_eq!(list.peek_back(), Some(&7));
    }

    #[test]
    fn peek_mut() {
        let mut list = doubly_linked_list![1, 2, 3];

        assert_eq!(list.peek_front_mut(), Some(&mut 3));
        assert_eq!(list.peek_front_mut(), Some(&mut 3));

        assert_eq!(list.peek_back_mut(), Some(&mut 1));
        assert_eq!(list.peek_back_mut(), Some(&mut 1));

        list.push_front(4);
        list.push_front(5);

        assert_eq!(list.peek_front_mut(), Some(&mut 5));
        *list.peek_front_mut().unwrap() = 10;

        assert_eq!(list.peek_front_mut(), Some(&mut 10));

        assert_eq!(list.peek_back_mut(), Some(&mut 1));
        *list.peek_back_mut().unwrap() = 15;

        assert_eq!(list.peek_back_mut(), Some(&mut 15));

        list.push_back(6);
        list.push_back(7);

        assert_eq!(list.peek_front_mut(), Some(&mut 10));
        assert_eq!(list.peek_front_mut(), Some(&mut 10));

        assert_eq!(list.peek_back_mut(), Some(&mut 7));
        assert_eq!(list.peek_back_mut(), Some(&mut 7));
    }

    #[test]
    fn into_vec() {
        let mut list = DoublyLinkedList::new();
        list.push_front(1);
        list.push_front(2);
        list.push_front(3);
        list.push_front(4);
        list.push_front(5);

        assert_eq!(list.len(), 5);

        assert_eq!(list.into_vec(), vec![5, 4, 3, 2, 1])
    }
}
