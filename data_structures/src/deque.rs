//! # Doubly Linked Queue
//!
//! A growable doubly linked queue with heap allocated contents.
//!
//! It has `O(1)` access, insertion and removal from the *head* or *tail* elements.
//!
//! # Examples
//! You can explicitly create a new queue with [`new`]
//! ```rust
//! use data_structures::deque::Deque;
//!
//! let mut queue: Deque<i32> = Deque::new();
//! ```
//!
//! or alternatively use the provided [`deque!`] macro
//! ```rust
//! #[macro_use]
//! use data_structures::deque;
//!
//! let mut queue = deque![1, 2, 3]; // Head = 3
//! ```
//!
//! Once the queue is instantiated you can then [`push_back`] and [`pop_front`] values - _(
//! methods are also provided for the inverse operations [`push_front`] and [`pop_back`])_
//!
//! ```rust
//! #[macro_use]
//! use data_structures::deque;
//!
//! let mut queue = deque![1, 2, 3]; // Head = 3
//!
//! queue.push_back(20); // Push a new value onto the head of the queue
//!
//! assert_eq!(queue.len(), 4);
//!
//! assert_eq!(queue.pop_front(), Some(3)); // Popping a value returns `Option<T>`
//! ```
//!
//! [`new`]: ./struct.Deque.html#method.new
//! [`push_front`]: ./struct.Deque.html#method.push_front
//! [`push_back`]: ./struct.Deque.html#method.push_back
//! [`pop_front`]: ./struct.Deque.html#method.pop_front
//! [`pop_back`]: ./struct.Deque.html#method.pop_back
//! [`deque!`]: ../macro.deque.html

use std::cell::{Ref, RefCell, RefMut};
use std::default::Default;
use std::fmt::{Debug, Error, Formatter};
use std::ops::{Deref, DerefMut};
use std::rc::Rc;

/// # A safe implementation of a Double-Ended Queue
///
/// This queue maintains a pointers to the element at the *head* and *tail* of the queue. In turn each element
/// maintains a pointer to the element immediately before and after it.
///
/// Any traversal required within the queue is highly inefficient and if required another data structure should
/// most likely be considered. However traversal is offered through conversion to an iterator or vector,
/// both of which would consume the queue.
///
/// # Examples
///
/// ```rust
/// use data_structures::deque::Deque;
///
/// let mut queue = Deque::new();
/// queue.push_back(10);
/// queue.push_back(20);
/// queue.push_back(30); // <- This is our head
///
/// println!("{:?}", queue); // Debug has been implemented for Deque
/// // Prints: H: | 10 | 20 | 30 | :T
///
/// assert_eq!(queue.len(), 3);
///
/// let element = queue.pop_front(); // We pop the head off the queue
/// assert_eq!(element, Some(10));
/// assert_eq!(queue.pop_front(), Some(20));
/// assert_eq!(queue.pop_front(), Some(30));
/// assert_eq!(queue.pop_front(), None); // Once we exhaust the queue, None is returned
/// ```
///
/// ## Macro
/// The [`deque!`] macro can be used to make initialization more convenient, the
/// first value within the square `[]` being the tail, and the final being the head.
///
/// ```rust
/// #[macro_use]
/// use data_structures::deque;
///
/// let mut queue = deque![1, 2, 3]; // Head = 3
///
/// assert_eq!(queue.pop_front(), Some(3));
/// ```
///
/// ## Use as a Queue
///
/// Methods are offered to enable O(1) insertion and removal from the head and tail of the queue
/// ```rust
/// #[macro_use]
/// use data_structures::deque;
///
/// let mut queue = deque![2, 3, 4];
///
/// queue.push_front(5); // Push to the head
/// queue.push_back(1); // Push to the tail
///
/// while let Some(head) = queue.pop_front() { // Extracting elements from the head of the queue
///     // Prints: 5, 4, 3, 2, 1
///     println!("{}", head);
/// }
///
/// queue.push_front(10);
/// assert_eq!(queue.pop_back(), Some(10)) // Popping an element from the tail of the queue
/// ```
///
/// ## Iterating over a Deque
///
/// Given the ambiguous ownership model required by a Deque, implementing iteration over it in
/// **Safe** Rust code is inefficient and complex. As such the only methods of iterating over a
/// Deque provided in this crate consume the queue in order to create the iterator.
///
/// However, iteration in both directions is supported.
///
/// ```rust
/// #[macro_use]
/// use data_structures::deque;
///
/// let queue = deque![1, 2, 3];
///
/// let mut iter = queue.into_iter();
///
/// // queue.len() - Unable to compile this, the queue has been consumed.
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
pub struct Deque<T> {
    head: Link<T>,
    tail: Link<T>,
    length: usize,
}

struct Node<T> {
    data: T,
    next: Link<T>,
    prev: Link<T>,
}

type Link<T> = Option<Rc<RefCell<Node<T>>>>;

impl<T> Deque<T> {
    /// Constructs a new, empty `Deque<T>`
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::deque::Deque;
    ///
    /// let mut queue: Deque<i32> = Deque::new();
    /// assert_eq!(queue.len(), 0);
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self {
            head: None,
            tail: None,
            length: 0,
        }
    }

    /// Returns the number of elements in the queue, also referred to as it's _length_
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::deque;
    ///
    /// let mut queue = deque![1, 2, 3];
    ///
    /// assert_eq!(queue.len(), 3);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.length
    }

    /// Returns true if the queue is empty, false if it contains 1 or more elements
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::deque;
    /// use data_structures::deque::Deque;
    ///
    /// let mut queue = deque![1, 2, 3];
    /// assert_eq!(queue.is_empty(), false);
    ///
    /// let mut queue: Deque<i32> = deque![];
    /// assert_eq!(queue.is_empty(), true);
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    /// Clears the queue
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::deque;
    ///
    /// let mut queue = deque![1, 2, 3];
    /// assert_eq!(queue.is_empty(), false);
    ///
    /// queue.clear();
    /// assert_eq!(queue.is_empty(), true);
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        *self = Self::new();
    }

    /// Pushes the provided element to the head of the queue
    ///
    /// # Panics
    /// Panics if the number of elements in the queue overflows a `usize`
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::deque::Deque;
    ///
    /// let mut queue = Deque::new();
    /// queue.push_front(1);
    /// queue.push_front(5);
    /// queue.push_front(10);
    ///
    /// assert_eq!(queue.len(), 3);
    /// ```
    #[inline]
    pub fn push_front(&mut self, data: T) {
        let new_node = Node::new(data);
        match self.head.take() {
            Some(old_head) => {
                old_head.borrow_mut().prev = Some(Rc::clone(&new_node));
                new_node.borrow_mut().next = Some(old_head);
                self.head = Some(new_node);
            }
            None => {
                self.tail = Some(Rc::clone(&new_node));
                self.head = Some(new_node);
            }
        }
        self.length += 1;
    }

    /// Pops the element off the head of the queue and returns it, returning `None` if the queue
    /// is empty
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::deque;
    ///
    /// let mut queue = deque![1, 5, 10];
    ///
    /// assert_eq!(queue.pop_front(), Some(10));
    /// assert_eq!(queue.pop_front(), Some(5));
    /// assert_eq!(queue.pop_front(), Some(1));
    /// assert_eq!(queue.pop_front(), None);
    /// ```
    #[inline]
    pub fn pop_front(&mut self) -> Option<T> {
        self.head.take().map(|old_node| {
            match old_node.borrow_mut().next.take() {
                Some(new_head) => {
                    new_head.borrow_mut().prev.take();
                    self.head = Some(new_head);
                }
                None => {
                    self.tail.take();
                }
            }

            if self.length >= 1 {
                self.length -= 1;
            } else {
                self.tail = None;
            }

            Rc::try_unwrap(old_node).ok().unwrap().into_inner().data
        })
    }

    /// Pushes the provided element to the tail of the queue
    ///
    /// # Panics
    /// Panics if the number of elements in the queue overflows a `usize`
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::deque::Deque;
    ///
    /// let mut queue = Deque::new();
    /// queue.push_back(1);
    /// queue.push_back(5);
    /// queue.push_back(10);
    ///
    /// assert_eq!(queue.len(), 3);
    /// assert_eq!(queue.pop_front(),Some(1));
    /// ```
    #[inline]
    pub fn push_back(&mut self, data: T) {
        let new_node = Node::new(data);
        match self.tail.take() {
            Some(old_tail) => {
                new_node.borrow_mut().prev = Some(Rc::clone(&old_tail));
                old_tail.borrow_mut().next = Some(Rc::clone(&new_node));
                self.tail = Some(new_node);
            }
            None => {
                self.tail = Some(Rc::clone(&new_node));
                self.head = Some(new_node);
            }
        }
        self.length += 1;
    }

    /// Pops the element off the tail of the queue and returns it, returning `None` if the queue
    /// is empty.
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::deque;
    ///
    /// let mut queue = deque![1, 5, 10];
    ///
    /// assert_eq!(queue.pop_back(), Some(1));
    /// assert_eq!(queue.pop_back(), Some(5));
    /// assert_eq!(queue.pop_back(), Some(10));
    /// assert_eq!(queue.pop_back(), None);
    /// ```
    #[inline]
    pub fn pop_back(&mut self) -> Option<T> {
        self.tail.take().map(|old_tail| {
            match old_tail.borrow_mut().prev.take() {
                Some(new_tail) => {
                    RefCell::borrow_mut(&new_tail).next.take();
                    self.tail = Some(new_tail);
                }
                None => {
                    self.head.take();
                }
            };

            if self.length >= 1 {
                self.length -= 1;
            } else {
                self.length = 0;
            }

            Rc::try_unwrap(old_tail).ok().unwrap().into_inner().data
        })
    }

    /// Iterates over the queue, reversing the links between all elements. The head becomes
    /// the tail and the tail becomes the head.
    ///
    /// # Notes
    /// This method actually mutates each node so that `next` becomes `previous` and
    /// `previous` becomes `next` as opposed to just reversing the direction of traversal.
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::deque;
    ///
    /// let mut queue = deque![1, 5, 10]; // 10 is currently the head
    ///
    /// queue.rev();
    /// println!("{:?}", queue);
    /// // Prints: H: | 1 | 5 | 10 | :T
    ///
    /// assert_eq!(queue.pop_front(), Some(1)); // After reversing, 1 is the head
    /// assert_eq!(queue.pop_back(), Some(10)); // 10 is the tail
    /// assert_eq!(queue.pop_front(), Some(5));
    /// assert_eq!(queue.pop_front(), None);
    /// ```
    #[inline]
    pub fn rev(&mut self) {
        let head = self.head.take();
        let tail = self.tail.take();

        let mut node_to_swap = None;
        match &head {
            Some(node) => {
                node_to_swap = Some(Rc::clone(node));
            }
            None => {}
        }

        while let Some(node) = node_to_swap.clone() {
            {
                let mut borrowed_node = RefCell::borrow_mut(&node);
                let next_node = borrowed_node.prev.take();

                borrowed_node.prev = borrowed_node.next.take();
                borrowed_node.next = next_node;
            }
            node_to_swap = node.borrow().prev.clone();
        }

        self.head = tail;
        self.tail = head;
    }

    /// Returns a reference to the next element in the queue
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::deque;
    ///
    /// let mut queue = deque![1, 5, 10];
    ///
    /// // Because the element is wrapped in an `Rc<RefCell<T>>>` we need to `.unwrap()` the
    /// // option and de-reference the `Ref` to receive the value
    /// assert_eq!(*(queue.peek_front().unwrap()), 10);
    ///
    /// // *queue.peek_front().unwrap() = 50; - This value can't be assigned to (it will error) as it doesn't implement
    /// // the DerefMut trait (see .peek_front_mut() if a mutable reference is needed)
    ///
    /// assert_eq!(&* queue.peek_front().unwrap(), &10); // .peek() doesn't consume the element
    /// ```
    #[inline]
    pub fn peek_front(&self) -> Option<impl Deref<Target = T> + '_> {
        self.head
            .as_ref()
            .map(|node| Ref::map(RefCell::borrow(node), |node| &node.data))
    }

    /// Returns a mutable reference to the next element in the queue
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::deque;
    ///
    /// let mut queue = deque![1, 5, 10];
    ///
    /// assert_eq!(&mut *(queue.peek_front_mut().unwrap()), &mut 10);
    /// assert_eq!(queue.len(), 3);
    ///
    /// *queue.peek_front_mut().unwrap() = 50;
    /// assert_eq!(queue.len(), 3);
    ///
    /// assert_eq!(queue.pop_front(), Some(50));
    /// ```
    #[inline]
    pub fn peek_front_mut(&mut self) -> Option<impl DerefMut<Target = T> + '_> {
        self.head
            .as_ref()
            .map(|node| RefMut::map(RefCell::borrow_mut(node), |node| &mut node.data))
    }

    /// Returns a reference to the last element in the queue
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::deque;
    ///
    /// let mut queue = deque![1, 5, 10];
    ///
    /// // Because the element is wrapped in an `Rc<RefCell<T>>>` we need to `.unwrap()` the
    /// // option and de-reference the `Ref` to receive the value
    /// assert_eq!(*(queue.peek_back().unwrap()), 1);
    ///
    /// // *queue.peek_back().unwrap() = 50; - This value can't be assigned to (it will error) as it doesn't implement
    /// // DerefMut (see .peek_back_mut() if a mutable reference is needed)
    ///
    /// assert_eq!(&* queue.peek_back().unwrap(), &1); // .peek() doesn't consume the element
    /// ```
    #[inline]
    pub fn peek_back(&self) -> Option<impl Deref<Target = T> + '_> {
        self.tail
            .as_ref()
            .map(|node| Ref::map(RefCell::borrow(node), |node| &node.data))
    }

    /// Returns a mutable reference to the last element in the queue
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::deque;
    ///
    /// let mut queue = deque![1, 5, 10];
    ///
    /// assert_eq!(&mut *(queue.peek_back_mut().unwrap()), &mut 1);
    /// assert_eq!(queue.len(), 3);
    ///
    /// *queue.peek_back_mut().unwrap() = 25;
    /// assert_eq!(queue.len(), 3);
    ///
    /// assert_eq!(queue.pop_back(), Some(25));
    /// ```
    #[inline]
    pub fn peek_back_mut(&mut self) -> Option<impl DerefMut<Target = T> + '_> {
        self.tail
            .as_ref()
            .map(|node| RefMut::map(RefCell::borrow_mut(node), |node| &mut node.data))
    }

    /// Consumes the queue, returning a Vec<T> filled with the elements in the order of head -> tail
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::deque;
    ///
    /// let mut queue = deque![1, 5, 10, 25, 50];
    ///
    /// assert_eq!(queue.len(), 5);
    ///
    /// assert_eq!(queue.into_vec(), vec![50, 25, 10, 5, 1])
    /// ```
    #[inline]
    pub fn into_vec(self) -> Vec<T> {
        self.into_iter().collect()
    }
}

impl<T> Drop for Deque<T> {
    fn drop(&mut self) {
        while self.pop_front().is_some() {}
    }
}

/// Provides a shorthand macro for creating a double-ended queue with multiple elements in it.
///
/// The first value contained within the `[]` being the tail and the last being the head.
///
/// # Examples
///
/// ```rust
/// #[macro_use]
/// use data_structures::deque;
/// use data_structures::deque::Deque;
///
/// // Tail: 1
/// // Head: 5
///
/// // Macro notation:
/// let mut queue = deque![1, 2, 3, 4, 5];
///
/// assert_eq!(queue.pop_front(), Some(5));
///
/// // Longhand notation:
/// let mut queue = Deque::new();
/// queue.push_front(1);
/// queue.push_front(2);
/// queue.push_front(3);
/// queue.push_front(4);
/// queue.push_front(5);
///
/// assert_eq!(queue.pop_front(), Some(5));
/// ```
#[macro_export]
macro_rules! deque {
    ($($x:expr),*) => {
        {
            let mut temp_queue = $crate::deque::Deque::new();
            $(
                temp_queue.push_front($x);
            )*
            temp_queue
        }
    };
}

impl<T> Node<T> {
    /// Returns an initialised version of Node wrapped in `Rc<RefCell<..>`
    pub fn new(data: T) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self {
            data,
            next: None,
            prev: None,
        }))
    }
}

// ============ Iterator Wrappers ============

/// An iterator that moves out of a Deque, consuming it in the process
///
/// # Examples
///
/// ```rust
/// #[macro_use]
/// use data_structures::deque;
///
/// let mut queue = deque![1, 5, 10, 25, 50];
///
/// let mut iter = queue.into_iter(); // queue has been `moved` and can no longer be used
///
/// assert_eq!(iter.next(), Some(50));
/// ```
pub struct IntoIter<T>(Deque<T>);

impl<T> IntoIterator for Deque<T> {
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

// ============ /Iterator Wrappers ============

impl<T: Debug> Debug for Deque<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        let mut node = self.head.clone();
        write!(f, "H: ")?;
        while let Some(n) = node {
            write!(f, "| {:?}", n.borrow().data)?;
            node = n.borrow().next.clone();
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
        let mut queue = Deque::new();
        queue.push_front(1);
        queue.push_front(2);
        queue.push_front(3);

        assert_eq!(queue.len(), 3);

        assert_eq!(queue.pop_front(), Some(3));
        assert_eq!(queue.pop_front(), Some(2));

        assert_eq!(queue.len(), 1);

        queue.push_front(4);
        queue.push_front(5);

        assert_eq!(queue.len(), 3);

        assert_eq!(queue.pop_front(), Some(5));
        assert_eq!(queue.pop_front(), Some(4));

        assert_eq!(queue.len(), 1);

        assert_eq!(queue.pop_front(), Some(1));
        assert_eq!(queue.pop_front(), None);

        assert_eq!(queue.len(), 0);
    }

    #[test]
    fn push_pop_back() {
        let mut queue = Deque::new();

        // Check empty queue behaves right
        assert_eq!(queue.pop_back(), None);

        // Check pushing data
        queue.push_back(1);
        queue.push_back(2);
        queue.push_back(3);

        // Check popping data
        assert_eq!(queue.pop_back(), Some(3));
        assert_eq!(queue.pop_back(), Some(2));

        // Check popping hasn't corrupted pushing
        queue.push_back(4);
        queue.push_back(5);

        // Check popping still works
        assert_eq!(queue.pop_back(), Some(5));
        assert_eq!(queue.pop_back(), Some(4));

        // Check exhaustion
        assert_eq!(queue.pop_back(), Some(1));
        assert_eq!(queue.pop_back(), None);
    }

    #[test]
    fn into_iter() {
        let queue = deque![1, 2, 3];

        let mut iter = queue.into_iter();

        assert_eq!(iter.next(), Some(3));
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next(), Some(1));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn peek() {
        let mut queue = Deque::new();
        queue.push_front(1);
        queue.push_front(2);
        queue.push_front(3);

        assert_eq!(&*queue.peek_front().unwrap(), &3);
        assert_eq!(&*queue.peek_front().unwrap(), &3);

        assert_eq!(&*queue.peek_back().unwrap(), &1);
        assert_eq!(&*queue.peek_back().unwrap(), &1);

        queue.push_front(4);
        queue.push_front(5);

        assert_eq!(&*queue.peek_front().unwrap(), &5);
        assert_eq!(&*queue.peek_front().unwrap(), &5);

        assert_eq!(&*queue.peek_back().unwrap(), &1);
        assert_eq!(&*queue.peek_back().unwrap(), &1);

        queue.push_back(6);
        queue.push_back(7);

        assert_eq!(&*queue.peek_front().unwrap(), &5);
        assert_eq!(&*queue.peek_front().unwrap(), &5);

        assert_eq!(&*queue.peek_back().unwrap(), &7);
        assert_eq!(&*queue.peek_back().unwrap(), &7);
    }

    #[test]
    fn peek_mut() {
        let mut queue = Deque::new();
        queue.push_front(1);
        queue.push_front(2);
        queue.push_front(3);

        assert_eq!(&*queue.peek_front_mut().unwrap(), &mut 3);
        assert_eq!(&*queue.peek_front_mut().unwrap(), &mut 3);

        assert_eq!(&*queue.peek_back_mut().unwrap(), &mut 1);
        assert_eq!(&*queue.peek_back_mut().unwrap(), &mut 1);

        queue.push_front(4);
        queue.push_front(5);

        assert_eq!(&*queue.peek_front_mut().unwrap(), &mut 5);

        *queue.peek_front_mut().unwrap() = 50;
        assert_eq!(&*queue.peek_front_mut().unwrap(), &mut 50);

        assert_eq!(&*queue.peek_back_mut().unwrap(), &mut 1);
        assert_eq!(&*queue.peek_back_mut().unwrap(), &mut 1);

        queue.push_back(6);
        queue.push_back(7);

        assert_eq!(&*queue.peek_front_mut().unwrap(), &mut 50);
        assert_eq!(&*queue.peek_front_mut().unwrap(), &mut 50);

        assert_eq!(&*queue.peek_back_mut().unwrap(), &mut 7);

        *queue.peek_back_mut().unwrap() = 100;
        assert_eq!(&*queue.peek_back_mut().unwrap(), &mut 100);
    }

    #[test]
    fn rev() {
        let mut queue = deque![1, 2, 3, 4, 5, 6];
        assert_eq!(queue.len(), 6);

        queue.rev();
        assert_eq!(queue.len(), 6);

        assert_eq!(queue.pop_front(), Some(1));
        assert_eq!(queue.pop_back(), Some(6));
        assert_eq!(queue.len(), 4);

        queue.push_front(7);
        queue.push_front(8);
        assert_eq!(queue.len(), 6);

        queue.rev();
        assert_eq!(queue.len(), 6);

        assert_eq!(queue.pop_back(), Some(8));
        assert_eq!(queue.pop_front(), Some(5));
    }

    #[test]
    fn into_vec() {
        let mut queue = Deque::new();
        queue.push_front(1);
        queue.push_front(2);
        queue.push_front(3);
        queue.push_front(4);
        queue.push_front(5);

        assert_eq!(queue.len(), 5);

        assert_eq!(queue.into_vec(), vec![5, 4, 3, 2, 1])
    }
}
