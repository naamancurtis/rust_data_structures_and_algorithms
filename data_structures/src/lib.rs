//! # Data Structures
//!
//! This library contains practice implementations of various data structures
//!
//! ## Lists
//! - Singly Linked List
//! - Deque
//! - Doubly Linked List - _(Safe abstraction around unsafe code)_
//!
//! ## Graphs
//! - Undirected Graph
//!
//! ### Trees
//! - Binary Tree - _Used to demonstrate traversal schemes_
//! - Binary Search Tree
//!
//! #### Heaps
//! - Binary Heap - _Also exposes API for Priority Queue_
//!
//! # Hash Tables
//! - Hash Table - _Only implemented to learn the theory, not usable_
pub mod binary_heap;
pub mod binary_search_tree;
pub mod binary_tree;
pub mod deque;
pub mod doubly_linked_list;
// Not usable, so not publicly exported
mod hash_table;
pub mod singly_linked_list;
pub mod undirected_graph;
