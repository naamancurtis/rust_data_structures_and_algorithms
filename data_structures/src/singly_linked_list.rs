pub struct SinglyLinkedList<T> {
    head: Link<T>,
    length: usize,
}

type Link<T> = Option<Box<Node<T>>>;

struct Node<T> {
    data: T,
    next: Link<T>,
}

impl<T> SinglyLinkedList<T> {
    /// Constructs a new, empty `SinglyLinkedList<T>`
    ///
    /// # Examples
    /// ```rust
    /// use data_structures::singly_linked_list::SinglyLinkedList;
    ///
    /// let mut list: SinglyLinkedList<i32> = SinglyLinkedList::new();
    /// assert_eq!(list.len(), 0);
    /// ```
    ///
    /// Alternatively this can be created shorthand using the `singly_linked_list![]` macro
    /// ```rust
    /// #[macro_use]
    /// use data_structures::singly_linked_list;
    ///
    /// let mut list = singly_linked_list![1, 2, 3];
    /// ```
    pub fn new() -> Self {
        Self {
            head: None,
            length: 0,
        }
    }

    /// Returns the number of elements in the list, also referred to as it's _length_
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::singly_linked_list;
    ///
    /// let mut list = singly_linked_list![1, 2, 3];
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
    /// use data_structures::singly_linked_list::SinglyLinkedList;
    ///
    /// let mut list = SinglyLinkedList::new();
    /// list.push(1);
    /// list.push(5);
    /// list.push(10);
    /// ```
    pub fn push(&mut self, data: T) {
        let mut new_node = Node::new(data);
        match self.head.take() {
            Some(old_head) => {
                new_node.next = Some(old_head);
                self.head = Some(new_node);
            }
            None => self.head = Some(new_node),
        }
        self.length += 1;
    }

    /// Pops the element off the head of the list and returns it, returning `None` if the list
    /// is empty.
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::singly_linked_list;
    ///
    /// let mut list = singly_linked_list![1, 5, 10];
    ///
    /// assert_eq!(list.pop(), Some(10));
    /// assert_eq!(list.pop(), Some(5));
    /// assert_eq!(list.pop(), Some(1));
    /// assert_eq!(list.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        self.head.take().map(|old_node| {
            self.head = old_node.next;
            if self.length >= 1 {
                self.length -= 1;
            }
            old_node.data
        })
    }

    /// Iterates over the list, reversing the links between all elements. The head becomes
    /// the tail and the tail becomes the head.
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::singly_linked_list;
    ///
    /// let mut list = singly_linked_list![1, 5, 10]; // 10 is currently the head
    ///
    /// list.rev();
    ///
    /// assert_eq!(list.pop(), Some(1)); // After reversing, 1 is the head
    /// assert_eq!(list.pop(), Some(5));
    /// assert_eq!(list.pop(), Some(10));
    /// assert_eq!(list.pop(), None);
    /// ```
    pub fn rev(&mut self) {
        let mut previous_ptr = None;
        let mut current_ptr = self.head.take();
        let mut following_ptr;

        while current_ptr.is_some() {
            following_ptr = current_ptr.as_mut().map(|node| node.next.take()).flatten();
            current_ptr.as_mut().map(|node| node.next = previous_ptr);
            previous_ptr = current_ptr;
            current_ptr = following_ptr;
        }
        self.head = previous_ptr;
    }

    /// Returns a reference to the next element in the list
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::singly_linked_list;
    ///
    /// let mut list = singly_linked_list![1, 5, 10];
    /// assert_eq!(list.peek(), Some(&10));
    /// assert_eq!(list.peek(), Some(&10)); // .peek() doesn't consume the element
    /// ```
    pub fn peek(&self) -> Option<&T> {
        self.head.as_ref().take().map(|node| &node.data)
    }

    /// Returns a mutable reference to the next element in the list
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::singly_linked_list;
    ///
    /// let mut list = singly_linked_list![1, 5, 10];
    /// assert_eq!(list.peek_mut(), Some(&mut 10));
    /// assert_eq!(list.len(), 3);
    ///
    /// list.peek_mut().map(|val| *val = 50);
    /// assert_eq!(list.len(), 3);
    ///
    /// assert_eq!(list.pop(), Some(50));
    /// ```
    pub fn peek_mut(&mut self) -> Option<&mut T> {
        self.head.as_mut().take().map(|node| &mut node.data)
    }

    /// Returns an iterator over the list, consuming the list in the process
    ///
    /// # Examples
    ///
    /// ```rust
    /// #[macro_use]
    /// use data_structures::singly_linked_list;
    ///
    /// let mut list = singly_linked_list![1, 5, 10];
    /// let mut iter = list.into_iter();
    ///
    /// assert_eq!(iter.next(), Some(10));
    /// assert_eq!(iter.next(), Some(5));
    /// assert_eq!(iter.next(), Some(1));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn into_iter(self) -> IntoIter<T> {
        IntoIter(self)
    }

    /// Returns an iterator over the list, providing a reference to each element
    ///
    /// # Examples
    ///
    /// ```rust
    /// #[macro_use]
    /// use data_structures::singly_linked_list;
    ///
    /// let mut list = singly_linked_list![1, 5, 10];
    /// let mut iter = list.iter();
    ///
    /// assert_eq!(iter.next(), Some(&10));
    /// assert_eq!(iter.next(), Some(&5));
    /// assert_eq!(iter.next(), Some(&1));
    /// assert_eq!(iter.next(), None);
    ///
    /// assert_eq!(list.len(), 3); // Note: the list hasn't been consumed
    /// assert_eq!(list.pop(), Some(10));
    /// ```
    pub fn iter(&self) -> Iter<T> {
        Iter {
            next: self.head.as_ref().map(|node| &**node),
        }
    }

    /// Returns an iterator over the list, providing a mutable reference to each element
    ///
    /// # Examples
    ///
    /// Mutating a single value
    /// ```rust
    /// #[macro_use]
    /// use data_structures::singly_linked_list;
    ///
    /// let mut list = singly_linked_list![1, 5, 10];
    /// let mut iter = list.iter_mut();
    ///
    /// assert_eq!(iter.next(), Some(&mut 10));
    /// iter.next().map(|val| *val = 50); // Mutate 5 to be 50;
    ///
    /// assert_eq!(iter.next(), Some(&mut 1));
    /// assert_eq!(iter.next(), None);
    ///
    /// assert_eq!(list.len(), 3); // Note: the list hasn't been consumed
    /// assert_eq!(list.pop(), Some(10));
    /// assert_eq!(list.pop(), Some(50));
    /// assert_eq!(list.pop(), Some(1));
    /// ```
    ///
    /// Mutating each value in the list
    /// ```rust
    /// #[macro_use]
    /// use data_structures::singly_linked_list;
    ///
    /// let mut list = singly_linked_list![1, 5, 10];
    /// let mut iter = list.iter_mut();
    ///
    /// iter.for_each(|val| *val *= 10);
    ///
    /// assert_eq!(list.len(), 3);
    /// assert_eq!(list.pop(), Some(100));
    /// assert_eq!(list.pop(), Some(50));
    /// assert_eq!(list.pop(), Some(10));
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut {
            next: self.head.as_mut().map(|node| &mut **node),
        }
    }

    /// Starting with the head at index `0`, iterates through the list returning a reference to
    /// the element at the provided index or `None` if that index doesn't exist
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::singly_linked_list;
    ///
    /// let mut list = singly_linked_list![1, 5, 10, 25, 50];
    ///
    /// assert_eq!(list.nth(3), Some(&5));
    ///
    /// assert_eq!(list.pop(), Some(50));
    /// assert_eq!(list.pop(), Some(25));
    ///
    /// assert_eq!(list.nth(3), None);
    /// assert_eq!(list.nth(2), Some(&1));
    /// ```
    pub fn nth(&self, index: usize) -> Option<&T> {
        if !(index < self.length) {
            return None;
        }
        self.iter().nth(index)
    }

    /// Starting with the head at index `0`, iterates through the list returning a mutable reference to
    /// the element at the provided index or `None` if that index doesn't exist
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::singly_linked_list;
    ///
    /// let mut list = singly_linked_list![1, 5, 10, 25, 50];
    ///
    /// assert_eq!(list.nth(3), Some(&5));
    ///
    /// assert_eq!(list.pop(), Some(50));
    /// assert_eq!(list.pop(), Some(25));
    ///
    /// assert_eq!(list.nth(3), None);
    /// assert_eq!(list.nth(2), Some(&1));
    /// ```
    pub fn nth_mut(&mut self, index: usize) -> Option<&mut T> {
        if !(index < self.length) {
            return None;
        }
        self.iter_mut().nth(index)
    }

    /// Consumes the list, returning a Vec<T> filled with the elements in the order of head -> tail
    ///
    /// # Examples
    /// ```rust
    /// #[macro_use]
    /// use data_structures::singly_linked_list;
    ///
    /// let mut list = singly_linked_list![1, 5, 10, 25, 50];
    ///
    /// assert_eq!(list.len(), 5);
    ///
    /// assert_eq!(list.into_vec(), vec![50, 25, 10, 5, 1])
    /// ```
    pub fn into_vec(self) -> Vec<T> {
        self.into_iter().collect()
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
macro_rules! singly_linked_list {
    ($($x:expr),*) => {
        {
            let mut temp_list = $crate::singly_linked_list::SinglyLinkedList::new();
            $(
                temp_list.push($x);
            )*
            temp_list
        }
    };
}

impl<T> Node<T> {
    /// Returns a Boxed instantiation of Node<T>
    pub fn new(data: T) -> Box<Self> {
        Box::new(Self { data, next: None })
    }
}

// ============ Iterator Wrappers ============

pub struct IntoIter<T>(SinglyLinkedList<T>);

pub struct Iter<'a, T> {
    next: Option<&'a Node<T>>,
}

pub struct IterMut<'a, T> {
    next: Option<&'a mut Node<T>>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop()
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.next.map(|node| {
            self.next = node.next.as_ref().map(|new_node| &**new_node);
            &node.data
        })
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        self.next.take().map(|node| {
            self.next = node.next.as_mut().map(|new_node| &mut **new_node);
            &mut node.data
        })
    }
}

// ============ /Iterator Wrappers ============

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn push_pop() {
        let mut list = SinglyLinkedList::new();
        list.push(1);
        list.push(2);
        list.push(3);

        assert_eq!(list.len(), 3);

        assert_eq!(list.pop(), Some(3));
        assert_eq!(list.pop(), Some(2));

        assert_eq!(list.len(), 1);

        list.push(4);
        list.push(5);

        assert_eq!(list.len(), 3);

        assert_eq!(list.pop(), Some(5));
        assert_eq!(list.pop(), Some(4));

        assert_eq!(list.len(), 1);

        assert_eq!(list.pop(), Some(1));
        assert_eq!(list.pop(), None);

        assert_eq!(list.len(), 0);
    }

    #[test]
    fn iter() {
        let mut list = SinglyLinkedList::new();
        list.push(1);
        list.push(2);
        list.push(3);

        let mut iter = list.iter();

        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn into_iter() {
        let mut list = SinglyLinkedList::new();
        list.push(1);
        list.push(2);
        list.push(3);

        let mut iter = list.into_iter();

        assert_eq!(iter.next(), Some(3));
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next(), Some(1));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn iter_mut() {
        let mut list = SinglyLinkedList::new();
        list.push(1);
        list.push(2);
        list.push(3);

        let mut iter = list.iter_mut();

        assert_eq!(iter.next(), Some(&mut 3));
        assert_eq!(iter.next(), Some(&mut 2));
        assert_eq!(iter.next(), Some(&mut 1));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn peek() {
        let mut list = SinglyLinkedList::new();
        list.push(1);
        list.push(2);
        list.push(3);

        assert_eq!(list.peek(), Some(&3));
        assert_eq!(list.peek(), Some(&3));

        list.push(4);
        list.push(5);

        assert_eq!(list.peek(), Some(&5));
    }

    #[test]
    fn peek_mut() {
        let mut list = SinglyLinkedList::new();
        list.push(1);
        list.push(2);
        list.push(3);

        assert_eq!(list.peek_mut(), Some(&mut 3));
        assert_eq!(list.peek_mut(), Some(&mut 3));

        list.push(4);
        list.push(5);

        assert_eq!(list.peek_mut(), Some(&mut 5));

        list.peek_mut().map(|val| *val = 42);

        assert_eq!(list.pop(), Some(42));
    }

    #[test]
    fn rev() {
        let mut list = SinglyLinkedList::new();
        list.push(1);
        list.push(2);
        list.push(3);

        list.rev();
        assert_eq!(list.len(), 3);

        assert_eq!(list.pop(), Some(1));
        assert_eq!(list.pop(), Some(2));
        assert_eq!(list.len(), 1);

        list.push(4);
        list.push(5);
        assert_eq!(list.len(), 3);

        list.rev();
        assert_eq!(list.len(), 3);

        assert_eq!(list.pop(), Some(3));
        assert_eq!(list.pop(), Some(4));
        assert_eq!(list.pop(), Some(5));
        assert_eq!(list.pop(), None);
    }

    #[test]
    fn nth() {
        let mut list = SinglyLinkedList::new();
        list.push(1);
        list.push(2);
        list.push(3);
        list.push(4);
        list.push(5);

        assert_eq!(list.nth(3), Some(&2));

        assert_eq!(list.pop(), Some(5));
        assert_eq!(list.pop(), Some(4));

        assert_eq!(list.nth(3), None);
        assert_eq!(list.nth(2), Some(&1));
    }

    #[test]
    fn nth_mut() {
        let mut list = SinglyLinkedList::new();
        list.push(1);
        list.push(2);
        list.push(3);
        list.push(4);
        list.push(5);

        assert_eq!(list.nth_mut(3), Some(&mut 2));

        list.nth_mut(3).map(|val| *val = 42);

        assert_eq!(list.pop(), Some(5));
        assert_eq!(list.pop(), Some(4));

        assert_eq!(list.nth(3), None);
        assert_eq!(list.nth_mut(2), Some(&mut 1));
        assert_eq!(list.nth_mut(1), Some(&mut 42));
    }

    #[test]
    fn into_vec() {
        let mut list = SinglyLinkedList::new();
        list.push(1);
        list.push(2);
        list.push(3);
        list.push(4);
        list.push(5);

        assert_eq!(list.len(), 5);

        assert_eq!(list.into_vec(), vec![5, 4, 3, 2, 1])
    }
}
