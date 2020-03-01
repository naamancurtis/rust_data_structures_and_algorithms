# Rust Data Structures and Algorithms

A Cargo Workspace storing practice implementations of various data structures and algorithms in Rust. 

## [Data Structures](https://github.com/naamancurtis/rust_data_structures_and_algorithms/tree/master/data_structures/src)
#### Lists
 - [Singly Linked List](https://github.com/naamancurtis/rust_data_structures_and_algorithms/blob/master/data_structures/src/singly_linked_list.rs)
 - [Deque](https://github.com/naamancurtis/rust_data_structures_and_algorithms/blob/master/data_structures/src/deque.rs)
 - [Doubly Linked List](https://github.com/naamancurtis/rust_data_structures_and_algorithms/blob/master/data_structures/src/doubly_linked_list.rs)
 
#### Graphs
 - [Undirected Graph](https://github.com/naamancurtis/rust_data_structures_and_algorithms/blob/master/data_structures/src/undirected_graph.rs)
    - Breadth First Search
    - Depth First Search
 - [Graph](https://github.com/naamancurtis/rust_data_structures_and_algorithms/blob/master/data_structures/src/graph.rs) - _Optionally can be directed & weighted_
    - Breadth First Search
    - Depth First Search
    - Dijkstra's Shortest Path

##### Trees
 - [Binary Tree](https://github.com/naamancurtis/rust_data_structures_and_algorithms/blob/master/data_structures/src/binary_tree.rs)
   - Depth First Search - _Pre, In and Post Order_
   - Breadth First Search
 - [Binary Search Tree](https://github.com/naamancurtis/rust_data_structures_and_algorithms/blob/master/data_structures/src/binary_search_tree.rs)

###### Heaps
 - [Binary Heap](https://github.com/naamancurtis/rust_data_structures_and_algorithms/blob/master/data_structures/src/binary_heap.rs)
   - API allows the creation of a Min Heap, Max Heap or Priority Queue

## [Problem Solving Patterns](https://github.com/naamancurtis/rust_data_structures_and_algorithms/tree/master/problem_solving_patterns/src)
 - [Frequency Counter](https://github.com/naamancurtis/rust_data_structures_and_algorithms/blob/master/problem_solving_patterns/src/frequency_counter_pattern.rs)
 - [Multiple Pointers](https://github.com/naamancurtis/rust_data_structures_and_algorithms/blob/master/problem_solving_patterns/src/multiple_pointers_pattern.rs)
 - [Recursion](https://github.com/naamancurtis/rust_data_structures_and_algorithms/blob/master/problem_solving_patterns/src/recursion.rs)
 - [Sliding Window](https://github.com/naamancurtis/rust_data_structures_and_algorithms/blob/master/problem_solving_patterns/src/sliding_window.rs)

## [Searching Algorithms](https://github.com/naamancurtis/rust_data_structures_and_algorithms/tree/master/searching/src)
 - [Linear Search](https://github.com/naamancurtis/rust_data_structures_and_algorithms/blob/master/searching/src/linear_search.rs)
 - [Binary Search](https://github.com/naamancurtis/rust_data_structures_and_algorithms/blob/master/searching/src/binary_search.rs)

## [Sorting Algorithms](https://github.com/naamancurtis/rust_data_structures_and_algorithms/tree/master/sorting/src)
 - [Bubble Sort](https://github.com/naamancurtis/rust_data_structures_and_algorithms/blob/master/sorting/src/bubble_sort.rs)
 - [Insertion Sort](https://github.com/naamancurtis/rust_data_structures_and_algorithms/blob/master/sorting/src/insertion_sort.rs)
 - [Selection Sort](https://github.com/naamancurtis/rust_data_structures_and_algorithms/blob/master/sorting/src/selection_sort.rs)
 - [Radix Sort](https://github.com/naamancurtis/rust_data_structures_and_algorithms/blob/master/sorting/src/radix_sort.rs)
 - [Merge Sort](https://github.com/naamancurtis/rust_data_structures_and_algorithms/blob/master/sorting/src/merge_sort.rs)
 - [Quick Sort](https://github.com/naamancurtis/rust_data_structures_and_algorithms/blob/master/sorting/src/quick_sort.rs)

## [Sample Problems](https://github.com/naamancurtis/rust_data_structures_and_algorithms/tree/master/sample_problems/src)
- [Find availability in two calendars](https://github.com/naamancurtis/rust_data_structures_and_algorithms/blob/master/sample_problems/src/find_availability_in_two_calendars.rs)

## Workspace Documentation
Most libraries are documented inline with `rustdoc`, to build the docs use [Cargo](https://doc.rust-lang.org/cargo/index.html). 
TL;DR: Navigate to the project root and run:

 ```shell script
# to build the docs:
cargo doc 
# By default they'll be found somewhere like `./target/doc/{crate_name}/index.html`

# if you want them to open in the browser after building
cargo doc --open
```

## Tests
Tests can be run throughout the entire workspace by running `cargo test` at the root project level. Alternatively tests
can be run on each library by navigating to the library root and running the same command.

### Resources used
- [JS Algorithms & Data Structures Masterclass - _Colt Steele_](https://www.udemy.com/course/js-algorithms-and-data-structures-masterclass/)
- [Learning Rust with entirely too many Linked Lists](https://cglab.ca/~abeinges/blah/too-many-lists/book/README.html)
- [Contain-RS](https://github.com/contain-rs)