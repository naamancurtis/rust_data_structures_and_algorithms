//! # Doubly Linked List
//!
//! A growable doubly linked list with heap allocated contents.
//!
//! It has `O(1)` access, pushing and popping from the **head** or **tail* elements. Interacting with any
//! value in the list other than the head will require `O(k)` time to iterate through the list
//! where `k` is the desired index of the element _(`O(n)` worst case)_.
//!
//! # Examples
//! You can explicitly create a new list with [`new`]
//! ```rust
//! use data_structures::singly_linked_list::SinglyLinkedList;
//!
//! let mut list: SinglyLinkedList<i32> = SinglyLinkedList::new();
//! ```
//!
//! or alternatively use the provided [`singly_linked_list!`] macro
//! ```rust
//! #[macro_use]
//! use data_structures::singly_linked_list;
//!
//! let mut list = singly_linked_list![1, 2, 3]; // Head = 3
//! ```
//!
//! Once the list is instantiated you can then [`push`] and [`pop`] values in much the same way
//! as a `Vec<T>`
//!
//! ```rust
//! #[macro_use]
//! use data_structures::singly_linked_list;
//!
//! let mut list = singly_linked_list![1, 2, 3]; // Head = 3
//!
//! list.push(20); // Push a new value onto the head of the list
//! assert_eq!(list.len(), 4);
//!
//! assert_eq!(list.pop(), Some(20)); // pop returns `Option<T>`
//! // As we just pushed 20 onto the head of the list, it's also the value we pop off
//! ```
//!
//! [`new`]: ./struct.SinglyLinkedList.html#method.new
//! [`push`]: ./struct.SinglyLinkedList.html#method.push
//! [`pop`]: ./struct.SinglyLinkedList.html#method.pop
//! [`singly_linked_list!`]: ../macro.singly_linked_list.html

use std::cell::RefCell;
use std::fmt::{Debug, Error, Formatter};
use std::rc::{Rc, Weak};

/// # Safe implementation of a Singly Linked List with single ownership
///
/// This list maintains a pointer to the element at the *head* of the list, where each element
/// maintains a subsequent pointer to the next element in the list. Interactions should ideally be
/// kept at the head level where this list can operate in O(1) time.
///
/// Any traversal required within the list is highly inefficient given the nature of it
/// _(although it is offered, primarily through the use of rust iterators)_.
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
/// println!("{:?}", list); // Debug has been implemented for DoublyLinkedList<T>
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
/// The [`doubly_linked_list!`] macro can be used to make initialization more convenient, the
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
///
/// ## Use as a Stack
///
/// The properties of the list make it ideal for use as a stack
/// ```rust
/// #[macro_use]
/// use data_structures::doubly_linked_list;
///
/// let mut stack = doubly_linked_list![1, 2, 3, 4, 5];
/// while let Some(head) = stack.pop_front() {
///     // Prints: 5, 4, 3, 2, 1
///     println!("{}", head);
/// }
/// ```
pub struct DoublyLinkedList<T> {
    head: Link<T>,
    tail: Link<T>,
    length: usize,
}

struct Node<T> {
    data: T,
    next: Link<T>,
    prev: Option<Weak<RefCell<Node<T>>>>,
}

type Link<T> = Option<Rc<RefCell<Node<T>>>>;

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
            tail: None,
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
        let new_node = Node::new(data);
        match self.head.take() {
            Some(old_head) => {
                old_head.borrow_mut().prev = Some(Rc::downgrade(&Rc::clone(&new_node)));
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

    /// Pops the element off the head of the list and returns it, returning `None` if the list
    /// is empty.
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
    /// list.push_back(1);
    /// list.push_back(5);
    /// list.push_back(10);
    ///
    /// assert_eq!(list.len(), 3);
    /// assert_eq!(list.pop_front(),Some(1));
    /// ```
    pub fn push_back(&mut self, data: T) {
        let new_node = Node::new(data);
        match self.tail.take() {
            Some(old_tail) => {
                new_node.borrow_mut().prev = Some(Rc::downgrade(&Rc::clone(&old_tail)));
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

    /// Pops the element off the head of the list and returns it, returning `None` if the list
    /// is empty.
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::doubly_linked_list;
    ///
    /// let mut list = doubly_linked_list![1, 5, 10, 25];
    ///
    /// println!("{:?}", list);
    ///
    /// assert_eq!(list.pop_back(), Some(1));
    /// println!("First {:?}", list);
    /// assert_eq!(list.pop_back(), Some(5));
    /// println!("Second {:?}", list);
    /// assert_eq!(list.pop_back(), Some(10));
    /// println!("Third {:?}", list);
    /// assert_eq!(list.pop_back(), Some(25));
    /// println!("Empty {:?}", list);
    /// assert_eq!(list.pop_back(), None);
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        self.tail.take().map(|old_tail| {
            match old_tail.borrow_mut().prev.take() {
                Some(new_tail) => {
                    let upgraded_tail = match new_tail.upgrade() {
                        Some(tail) => {
                            RefCell::borrow_mut(&tail).next.take();
                            Some(tail)
                        }
                        None => None,
                    };

                    self.tail = upgraded_tail;
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

    //    /// Iterates over the list, reversing the links between all elements. The head becomes
    //    /// the tail and the tail becomes the head.
    //    ///
    //    /// # Examples
    //    /// ```rust
    //    /// #[macro_use]
    //    /// use data_structures::singly_linked_list;
    //    ///
    //    /// let mut list = singly_linked_list![1, 5, 10]; // 10 is currently the head
    //    ///
    //    /// list.rev();
    //    ///
    //    /// assert_eq!(list.pop(), Some(1)); // After reversing, 1 is the head
    //    /// assert_eq!(list.pop(), Some(5));
    //    /// assert_eq!(list.pop(), Some(10));
    //    /// assert_eq!(list.pop(), None);
    //    /// ```
    //    pub fn rev(&mut self) {
    //        let mut previous_ptr = None;
    //        let mut current_ptr = self.head.take();
    //        let mut following_ptr;
    //
    //        while current_ptr.is_some() {
    //            following_ptr = current_ptr.as_mut().map(|node| node.next.take()).flatten();
    //            current_ptr.as_mut().map(|node| node.next = previous_ptr);
    //            previous_ptr = current_ptr;
    //            current_ptr = following_ptr;
    //        }
    //        self.head = previous_ptr;
    //    }
    //
    //    /// Returns a reference to the next element in the list
    //    ///
    //    /// # Examples
    //    /// ```rust
    //    /// #[macro_use]
    //    /// use data_structures::singly_linked_list;
    //    ///
    //    /// let mut list = singly_linked_list![1, 5, 10];
    //    /// assert_eq!(list.peek(), Some(&10));
    //    /// assert_eq!(list.peek(), Some(&10)); // .peek() doesn't consume the element
    //    /// ```
    //    pub fn peek(&self) -> Option<&T> {
    //        self.head.as_ref().take().map(|node| &node.data)
    //    }
    //
    //    /// Returns a mutable reference to the next element in the list
    //    ///
    //    /// # Examples
    //    /// ```rust
    //    /// #[macro_use]
    //    /// use data_structures::singly_linked_list;
    //    ///
    //    /// let mut list = singly_linked_list![1, 5, 10];
    //    /// assert_eq!(list.peek_mut(), Some(&mut 10));
    //    /// assert_eq!(list.len(), 3);
    //    ///
    //    /// list.peek_mut().map(|val| *val = 50);
    //    /// assert_eq!(list.len(), 3);
    //    ///
    //    /// assert_eq!(list.pop(), Some(50));
    //    /// ```
    //    pub fn peek_mut(&mut self) -> Option<&mut T> {
    //        self.head.as_mut().take().map(|node| &mut node.data)
    //    }
    //
    //    /// Returns an iterator over the list, consuming the list in the process
    //    ///
    //    /// # Examples
    //    ///
    //    /// ```rust
    //    /// #[macro_use]
    //    /// use data_structures::singly_linked_list;
    //    ///
    //    /// let mut list = singly_linked_list![1, 5, 10];
    //    /// let mut iter = list.into_iter();
    //    ///
    //    /// assert_eq!(iter.next(), Some(10));
    //    /// assert_eq!(iter.next(), Some(5));
    //    /// assert_eq!(iter.next(), Some(1));
    //    /// assert_eq!(iter.next(), None);
    //    /// ```
    //    pub fn into_iter(self) -> IntoIter<T> {
    //        IntoIter(self)
    //    }
    //
    //    /// Returns an iterator over the list, providing a reference to each element
    //    ///
    //    /// # Examples
    //    ///
    //    /// ```rust
    //    /// #[macro_use]
    //    /// use data_structures::singly_linked_list;
    //    ///
    //    /// let mut list = singly_linked_list![1, 5, 10];
    //    /// let mut iter = list.iter();
    //    ///
    //    /// assert_eq!(iter.next(), Some(&10));
    //    /// assert_eq!(iter.next(), Some(&5));
    //    /// assert_eq!(iter.next(), Some(&1));
    //    /// assert_eq!(iter.next(), None);
    //    ///
    //    /// assert_eq!(list.len(), 3); // Note: the list hasn't been consumed
    //    /// assert_eq!(list.pop(), Some(10));
    //    /// ```
    //    pub fn iter(&self) -> Iter<T> {
    //        Iter {
    //            next: self.head.as_ref().map(|node| &**node),
    //        }
    //    }
    //
    //    /// Returns an iterator over the list, providing a mutable reference to each element
    //    ///
    //    /// # Examples
    //    ///
    //    /// Mutating a single value
    //    /// ```rust
    //    /// #[macro_use]
    //    /// use data_structures::singly_linked_list;
    //    ///
    //    /// let mut list = singly_linked_list![1, 5, 10];
    //    /// let mut iter = list.iter_mut();
    //    ///
    //    /// assert_eq!(iter.next(), Some(&mut 10));
    //    /// iter.next().map(|val| *val = 50); // Mutate 5 to be 50;
    //    ///
    //    /// assert_eq!(iter.next(), Some(&mut 1));
    //    /// assert_eq!(iter.next(), None);
    //    ///
    //    /// assert_eq!(list.len(), 3); // Note: the list hasn't been consumed
    //    /// assert_eq!(list.pop(), Some(10));
    //    /// assert_eq!(list.pop(), Some(50));
    //    /// assert_eq!(list.pop(), Some(1));
    //    /// ```
    //    ///
    //    /// Mutating each value in the list
    //    /// ```rust
    //    /// #[macro_use]
    //    /// use data_structures::singly_linked_list;
    //    ///
    //    /// let mut list = singly_linked_list![1, 5, 10];
    //    /// let mut iter = list.iter_mut();
    //    ///
    //    /// iter.for_each(|val| *val *= 10);
    //    ///
    //    /// assert_eq!(list.len(), 3);
    //    /// assert_eq!(list.pop(), Some(100));
    //    /// assert_eq!(list.pop(), Some(50));
    //    /// assert_eq!(list.pop(), Some(10));
    //    /// ```
    //    pub fn iter_mut(&mut self) -> IterMut<T> {
    //        IterMut {
    //            next: self.head.as_mut().map(|node| &mut **node),
    //        }
    //    }
    //
    //    /// Starting with the head at index `0`, iterates through the list returning a reference to
    //    /// the element at the provided index or `None` if that index doesn't exist
    //    ///
    //    /// # Examples
    //    /// ```rust
    //    /// #[macro_use]
    //    /// use data_structures::singly_linked_list;
    //    ///
    //    /// let mut list = singly_linked_list![1, 5, 10, 25, 50];
    //    ///
    //    /// assert_eq!(list.nth(3), Some(&5));
    //    ///
    //    /// assert_eq!(list.pop(), Some(50));
    //    /// assert_eq!(list.pop(), Some(25));
    //    ///
    //    /// assert_eq!(list.nth(3), None);
    //    /// assert_eq!(list.nth(2), Some(&1));
    //    /// ```
    //    pub fn nth(&self, index: usize) -> Option<&T> {
    //        if !(index < self.length) {
    //            return None;
    //        }
    //        self.iter().nth(index)
    //    }
    //
    //    /// Starting with the head at index `0`, iterates through the list returning a mutable reference to
    //    /// the element at the provided index or `None` if that index doesn't exist
    //    ///
    //    /// # Examples
    //    /// ```rust
    //    /// #[macro_use]
    //    /// use data_structures::singly_linked_list;
    //    ///
    //    /// let mut list = singly_linked_list![1, 5, 10, 25, 50];
    //    ///
    //    /// assert_eq!(list.nth_mut(3), Some(&mut 5));
    //    ///
    //    /// assert_eq!(list.pop(), Some(50));
    //    /// assert_eq!(list.pop(), Some(25));
    //    ///
    //    /// assert_eq!(list.nth_mut(3), None);
    //    /// assert_eq!(list.nth_mut(2), Some(&mut 1));
    //    /// ```
    //    pub fn nth_mut(&mut self, index: usize) -> Option<&mut T> {
    //        if !(index < self.length) {
    //            return None;
    //        }
    //        self.iter_mut().nth(index)
    //    }
    //
    //    /// Inserts the data provided and the specified index within the list. If the index
    //    /// exceeds the length of the list, it will add the new element at the end of the list.
    //    ///
    //    /// In the event that `0` is passed as the index, the `.push()` method is called to add the
    //    /// element instead
    //    ///
    //    /// # Examples
    //    ///
    //    /// ```rust
    //    /// #[macro_use]
    //    /// use data_structures::singly_linked_list;
    //    ///
    //    /// let mut list = singly_linked_list![1, 5, 10];
    //    ///
    //    /// assert_eq!(list.len(), 3);
    //    ///
    //    /// list.insert(50, 1);
    //    /// assert_eq!(list.len(), 4);
    //    ///
    //    /// assert_eq!(list.pop(), Some(10));
    //    /// assert_eq!(list.pop(), Some(50));
    //    /// assert_eq!(list.pop(), Some(5));
    //    /// assert_eq!(list.pop(), Some(1));
    //    /// assert_eq!(list.pop(), None);
    //    /// ```
    //    pub fn insert(&mut self, data: T, index: usize) {
    //        if index == 0 {
    //            self.push(data);
    //            return;
    //        }
    //
    //        let mut old_list_tail = self
    //            .head
    //            .as_mut()
    //            .expect("as the length is greater than 0, the head should always contain Some(node)");
    //
    //        let mut counter = index.min(self.length);
    //
    //        loop {
    //            counter -= 1;
    //
    //            // If the counter is down to 0, then we want to take the next value
    //            if counter == 0 {
    //                let mut new_node = Node::new(data);
    //                new_node.next = old_list_tail.next.take();
    //                old_list_tail.next = Some(new_node);
    //                break;
    //            }
    //
    //            // Otherwise we want to iterate to the next element in the list
    //            old_list_tail = match old_list_tail.next.as_mut() {
    //                Some(node) => node,
    //                // If the list is none, then we've reached the end of the list, so we'll
    //                // add the new element at the end of the list
    //                None => break,
    //            };
    //        }
    //
    //        self.length += 1;
    //    }
    //
    //    /// Mutates the list it is called on, splitting it into 2 at index provided
    //    /// _(with the index being head for the newly created second list)_, returning
    //    /// the newly created second list.
    //    ///
    //    /// **Note:** If an index of `0` is passed as an argument, an empty list is returned,
    //    /// with the existing list remaining unmutated.
    //    ///
    //    /// # Examples
    //    ///
    //    /// ```rust
    //    /// #[macro_use]
    //    /// use data_structures::singly_linked_list;
    //    ///
    //    /// let mut list = singly_linked_list![1, 5, 10];
    //    /// let mut split_list = list.split(1);
    //    ///
    //    /// assert_eq!(list.len(), 1);
    //    /// assert_eq!(split_list.len(), 2);
    //    ///
    //    /// assert_eq!(list.pop(), Some(10));
    //    /// assert_eq!(list.pop(), None);
    //    ///
    //    /// assert_eq!(split_list.pop(), Some(5));
    //    /// assert_eq!(split_list.pop(), Some(1));
    //    /// assert_eq!(split_list.pop(), None);
    //    ///```
    //    pub fn split(&mut self, index: usize) -> DoublyLinkedList<T> {
    //        let mut new_list = DoublyLinkedList::new();
    //        if index > self.length || index == 0 {
    //            return new_list;
    //        }
    //
    //        let mut old_list_tail = self
    //            .head
    //            .as_mut()
    //            .expect("as the length is greater than 0, the head should always contain Some(node)");
    //
    //        let mut counter = index;
    //
    //        loop {
    //            counter -= 1;
    //
    //            // If the counter is down to 0, then we want to take the next value
    //            if counter == 0 {
    //                new_list.head = old_list_tail.next.take();
    //                break;
    //            }
    //
    //            // Otherwise we want to iterate to the next element in the list
    //            old_list_tail = match old_list_tail.next.as_mut() {
    //                Some(node) => node,
    //                _ => break,
    //            };
    //        }
    //
    //        // Todo - Not sure this is the most reliable way to do this, but
    //        // it's more efficient than iterating over both new lists and counting elements
    //        new_list.length = self.length - index;
    //        self.length = self.length - new_list.length;
    //
    //        new_list
    //    }
    //
    //    /// Consumes the list, returning a Vec<T> filled with the elements in the order of head -> tail
    //    ///
    //    /// # Examples
    //    /// ```rust
    //    /// #[macro_use]
    //    /// use data_structures::singly_linked_list;
    //    ///
    //    /// let mut list = singly_linked_list![1, 5, 10, 25, 50];
    //    ///
    //    /// assert_eq!(list.len(), 5);
    //    ///
    //    /// assert_eq!(list.into_vec(), vec![50, 25, 10, 5, 1])
    //    /// ```
    //    pub fn into_vec(self) -> Vec<T> {
    //        self.into_iter().collect()
    //    }
}

impl<T> Drop for DoublyLinkedList<T> {
    fn drop(&mut self) {
        while self.pop_front().is_some() {}
    }
}

/// Provides a shorthand macro for creating a Singly Linked List with multiple elements in it.
///
/// The start of the list being the tail and the final element being the head.
///
/// # Examples
///
/// ```rust
/// #[macro_use]
/// use data_structures::singly_linked_list;
/// use data_structures::singly_linked_list::SinglyLinkedList;
///
/// // Tail: 1
/// // Head: 5
///
/// // Macro notation:
/// let mut list = singly_linked_list![1, 2, 3, 4, 5];
///
/// assert_eq!(list.pop(), Some(5));
///
/// // Longhand notation:
/// let mut list = SinglyLinkedList::new();
/// list.push(1);
/// list.push(2);
/// list.push(3);
/// list.push(4);
/// list.push(5);
///
/// assert_eq!(list.pop(), Some(5));
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
    /// Returns an initialised version of Node wrapped in Rc<RefCell<..
    pub fn new(data: T) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self {
            data,
            next: None,
            prev: None,
        }))
    }
}

//// ============ Iterator Wrappers ============
//
///// An iterator that moves out of a SinglyLinkedList, consuming it in the process
/////
///// # Examples
/////
///// ```rust
///// #[macro_use]
///// use data_structures::singly_linked_list;
/////
///// let mut list = singly_linked_list![1, 5, 10, 25, 50];
/////
///// let mut iter = list.into_iter(); // list has been `moved` and can no longer be used
/////
///// assert_eq!(iter.next(), Some(50));
///// ```
//pub struct IntoIter<T>(DoublyLinkedList<T>);
//
///// An iterator that provides immutable references over a SinglyLinkedList, it does not consume it in the process
/////
///// # Examples
/////
///// ```rust
///// #[macro_use]
///// use data_structures::singly_linked_list;
/////
///// let mut list = singly_linked_list![1, 5, 10, 25, 50];
/////
///// let mut iter = list.iter();
/////
///// assert_eq!(iter.next(), Some(&50));
///// assert_eq!(list.len(), 5); // list hasn't been consumed
///// ```
//pub struct Iter<'a, T> {
//    next: Option<&'a Node<T>>,
//}
//
///// An iterator that provides mutable references over a SinglyLinkedList, it does not consume it in the process
/////
///// # Examples
/////
///// ```rust
///// #[macro_use]
///// use data_structures::singly_linked_list;
/////
///// let mut list = singly_linked_list![1, 5, 10, 25, 50];
/////
///// let mut iter = list.iter_mut();
/////
///// assert_eq!(iter.next(), Some(&mut 50));
/////
///// iter.next().map(|val| *val *= 10); // lets mutate the second value
/////
///// assert_eq!(list.pop(), Some(50)); // the element hasn't been consumed
///// assert_eq!(list.pop(), Some(250)); // here is our mutated value
///// ```
//pub struct IterMut<'a, T> {
//    next: Option<&'a mut Node<T>>,
//}
//
//impl<T> Iterator for IntoIter<T> {
//    type Item = T;
//
//    fn next(&mut self) -> Option<Self::Item> {
//        self.0.pop()
//    }
//}
//
//impl<'a, T> Iterator for Iter<'a, T> {
//    type Item = &'a T;
//
//    fn next(&mut self) -> Option<Self::Item> {
//        self.next.map(|node| {
//            self.next = node.next.as_ref().map(|new_node| &**new_node);
//            &node.data
//        })
//    }
//}
//
//impl<'a, T> Iterator for IterMut<'a, T> {
//    type Item = &'a mut T;
//
//    fn next(&mut self) -> Option<Self::Item> {
//        self.next.take().map(|node| {
//            self.next = node.next.as_mut().map(|new_node| &mut **new_node);
//            &mut node.data
//        })
//    }
//}

// ============ /Iterator Wrappers ============

impl<T: Debug> Debug for DoublyLinkedList<T> {
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
    //
    //    #[test]
    //    fn iter() {
    //        let mut list = DoublyLinkedList::new();
    //        list.push(1);
    //        list.push(2);
    //        list.push(3);
    //
    //        let mut iter = list.iter();
    //
    //        assert_eq!(iter.next(), Some(&3));
    //        assert_eq!(iter.next(), Some(&2));
    //        assert_eq!(iter.next(), Some(&1));
    //        assert_eq!(iter.next(), None);
    //    }
    //
    //    #[test]
    //    fn into_iter() {
    //        let mut list = DoublyLinkedList::new();
    //        list.push(1);
    //        list.push(2);
    //        list.push(3);
    //
    //        let mut iter = list.into_iter();
    //
    //        assert_eq!(iter.next(), Some(3));
    //        assert_eq!(iter.next(), Some(2));
    //        assert_eq!(iter.next(), Some(1));
    //        assert_eq!(iter.next(), None);
    //    }
    //
    //    #[test]
    //    fn iter_mut() {
    //        let mut list = DoublyLinkedList::new();
    //        list.push(1);
    //        list.push(2);
    //        list.push(3);
    //
    //        let mut iter = list.iter_mut();
    //
    //        assert_eq!(iter.next(), Some(&mut 3));
    //        assert_eq!(iter.next(), Some(&mut 2));
    //        assert_eq!(iter.next(), Some(&mut 1));
    //        assert_eq!(iter.next(), None);
    //    }
    //
    //    #[test]
    //    fn peek() {
    //        let mut list = DoublyLinkedList::new();
    //        list.push(1);
    //        list.push(2);
    //        list.push(3);
    //
    //        assert_eq!(list.peek(), Some(&3));
    //        assert_eq!(list.peek(), Some(&3));
    //
    //        list.push(4);
    //        list.push(5);
    //
    //        assert_eq!(list.peek(), Some(&5));
    //    }
    //
    //    #[test]
    //    fn peek_mut() {
    //        let mut list = DoublyLinkedList::new();
    //        list.push(1);
    //        list.push(2);
    //        list.push(3);
    //
    //        assert_eq!(list.peek_mut(), Some(&mut 3));
    //        assert_eq!(list.peek_mut(), Some(&mut 3));
    //
    //        list.push(4);
    //        list.push(5);
    //
    //        assert_eq!(list.peek_mut(), Some(&mut 5));
    //
    //        list.peek_mut().map(|val| *val = 42);
    //
    //        assert_eq!(list.pop(), Some(42));
    //    }
    //
    //    #[test]
    //    fn rev() {
    //        let mut list = DoublyLinkedList::new();
    //        list.push(1);
    //        list.push(2);
    //        list.push(3);
    //
    //        list.rev();
    //        assert_eq!(list.len(), 3);
    //
    //        assert_eq!(list.pop(), Some(1));
    //        assert_eq!(list.pop(), Some(2));
    //        assert_eq!(list.len(), 1);
    //
    //        list.push(4);
    //        list.push(5);
    //        assert_eq!(list.len(), 3);
    //
    //        list.rev();
    //        assert_eq!(list.len(), 3);
    //
    //        assert_eq!(list.pop(), Some(3));
    //        assert_eq!(list.pop(), Some(4));
    //        assert_eq!(list.pop(), Some(5));
    //        assert_eq!(list.pop(), None);
    //    }
    //
    //    #[test]
    //    fn nth() {
    //        let mut list = DoublyLinkedList::new();
    //        list.push(1);
    //        list.push(2);
    //        list.push(3);
    //        list.push(4);
    //        list.push(5);
    //
    //        assert_eq!(list.nth(3), Some(&2));
    //
    //        assert_eq!(list.pop(), Some(5));
    //        assert_eq!(list.pop(), Some(4));
    //
    //        assert_eq!(list.nth(3), None);
    //        assert_eq!(list.nth(2), Some(&1));
    //    }
    //
    //    #[test]
    //    fn nth_mut() {
    //        let mut list = DoublyLinkedList::new();
    //        list.push(1);
    //        list.push(2);
    //        list.push(3);
    //        list.push(4);
    //        list.push(5);
    //
    //        assert_eq!(list.nth_mut(3), Some(&mut 2));
    //
    //        list.nth_mut(3).map(|val| *val = 42);
    //
    //        assert_eq!(list.pop(), Some(5));
    //        assert_eq!(list.pop(), Some(4));
    //
    //        assert_eq!(list.nth(3), None);
    //        assert_eq!(list.nth_mut(2), Some(&mut 1));
    //        assert_eq!(list.nth_mut(1), Some(&mut 42));
    //    }
    //
    //    #[test]
    //    fn into_vec() {
    //        let mut list = DoublyLinkedList::new();
    //        list.push(1);
    //        list.push(2);
    //        list.push(3);
    //        list.push(4);
    //        list.push(5);
    //
    //        assert_eq!(list.len(), 5);
    //
    //        assert_eq!(list.into_vec(), vec![5, 4, 3, 2, 1])
    //    }
    //
    //    #[test]
    //    fn split() {
    //        let mut list = singly_linked_list![1, 2, 3, 7, 8, 9];
    //        let mut split_list = list.split(3);
    //
    //        assert_eq!(list.len(), 3);
    //        assert_eq!(split_list.len(), 3);
    //
    //        assert_eq!(list.pop(), Some(9));
    //        assert_eq!(list.pop(), Some(8));
    //        assert_eq!(list.pop(), Some(7));
    //        assert_eq!(list.pop(), None);
    //
    //        assert_eq!(split_list.pop(), Some(3));
    //        assert_eq!(split_list.pop(), Some(2));
    //        assert_eq!(split_list.pop(), Some(1));
    //        assert_eq!(split_list.pop(), None);
    //    }
    //
    //    #[test]
    //    fn split_len_2() {
    //        let mut list = singly_linked_list![1, 2];
    //        let mut split_list = list.split(1);
    //
    //        assert_eq!(list.len(), 1);
    //        assert_eq!(split_list.len(), 1);
    //
    //        assert_eq!(list.pop(), Some(2));
    //        assert_eq!(list.pop(), None);
    //
    //        assert_eq!(split_list.pop(), Some(1));
    //        assert_eq!(split_list.pop(), None);
    //    }
    //
    //    #[test]
    //    fn insert() {
    //        let mut list = singly_linked_list![5, 10];
    //
    //        list.insert(50, 1);
    //        assert_eq!(list.len(), 3);
    //
    //        list.insert(100, 10);
    //        assert_eq!(list.len(), 4);
    //
    //        list.insert(250, 0);
    //        assert_eq!(list.len(), 5);
    //
    //        assert_eq!(list.pop(), Some(250));
    //        assert_eq!(list.pop(), Some(10));
    //        assert_eq!(list.pop(), Some(50));
    //        assert_eq!(list.pop(), Some(5));
    //        assert_eq!(list.pop(), Some(100));
    //        assert_eq!(list.pop(), None);
    //    }
}
