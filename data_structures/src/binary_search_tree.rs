use std::cmp::Ordering;

pub struct BinarySearchTree<'a, T> {
    root: Edge<T>,
    cmp: Box<&'a dyn Fn(&T, &T) -> Ordering>,
    length: usize,
}

#[derive(Default, Debug)]
pub struct Node<T> {
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

    pub fn as_ref(&self) -> Option<&T> {
        Some(&self.data)
    }
}

impl<'a, T> BinarySearchTree<'a, T> {
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

    pub fn len(&self) -> usize {
        self.length
    }

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
}
