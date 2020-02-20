# Rust Data Structures and Algorithms

A Cargo Workspace storing practice implementations of various data structures and algorithms in Rust. 

## [Data Structures](https://github.com/naamancurtis/rust_data_structures_and_algorithms/tree/master/data_structures/src)
#### Lists
 - Singly Linked List
 - Deque
 - Doubly Linked List

#### Trees
 - Binary Tree
 - Binary Search Tree

##### Heaps
 - Binary Heap - _Contains_ **Priority Queue** _API_

## [Problem Solving Patterns](https://github.com/naamancurtis/rust_data_structures_and_algorithms/tree/master/problem_solving_patterns/src)
- Frequency Counter
- Multiple Pointers
- Recursion
- Sliding Window

## [Searching Algorithms](https://github.com/naamancurtis/rust_data_structures_and_algorithms/tree/master/searching/src)
- Linear Search
- Binary Search

## [Sorting Algorithms](https://github.com/naamancurtis/rust_data_structures_and_algorithms/tree/master/sorting/src)
- Bubble Sort
- Insertion Sort
- Selection Sort
- Radix Sort
- Merge Sort
- Quick Sort

### Docs
Cargo can be used to build the docs, to do so navigate to the project root and run:
 ```shell script
# to build the docs:
cargo doc 

# if you want them to open in the browser after building
cargo doc --open
```

### Tests
Tests can be run throughout the entire workspace by running `cargo test` at the root project level. Alternatively tests
can be run on each library by navigating to the library root and running the same command.

### Resources used
- [JS Algorithms & Data Structures Masterclass - _Colt Steele_](https://www.udemy.com/course/js-algorithms-and-data-structures-masterclass/)
- [Learning Rust with entirely too many Linked Lists](https://cglab.ca/~abeinges/blah/too-many-lists/book/README.html)
- [Contain-RS](https://github.com/contain-rs)