use std::fmt::Debug;

/// ## Recursive Merge Sort
/// Given an unsorted collection, return a sorted collection through the use of the
/// merge sort algorithm.
///
/// The collection is first split down into sub-arrays of length 0 or 1, which takes
/// advantage of the fact that anything of length 0 or 1 is inherenetly sorted.
/// The sub-arrays are then merged back together to reform the sorted array
///
/// Time Complexity: O(nlog(n))
/// Space Complexity: O(n)
///
/// ```
/// use sorting::quicksort::quicksort;
///
/// fn simple_recursive_sort() {
///     let mut arr = vec![37, 45, 29, 8];
///     quicksort(&mut arr);
///     assert_eq!(arr, [8, 29, 37, 45]);
/// }
/// ```
pub fn quicksort<T>(collection: &mut [T])
where
    T: Ord + PartialEq + Copy + Debug,
{
    let length = collection.len();
    if length == 0 {
        return;
    }
    array_quicksort(collection, 0, length - 1);
}

pub fn array_quicksort<T>(mut collection: &mut [T], start: usize, end: usize)
where
    T: Ord + PartialEq + Copy + Debug,
{
    if start <= end {
        let pivot = partition(collection, start, end);
        if pivot > 0 {
            array_quicksort(&mut collection, start, pivot - 1);
        }
        array_quicksort(&mut collection, pivot + 1, end);
    }
}

/// ## Partition
///
/// Pivots the collection around the final element of the array
/// ```
/// use std::cmp::Ordering;
/// use sorting::quicksort::partition;
///
/// fn it_works() {
///    let mut arr = vec![37, 45, 29, 8, 16, 29, 30];
///    let ptr = partition(&mut arr, 0, 7);
///    for (index, el) in arr.iter().enumerate() {
///        match index.cmp(&4) {
///            Ordering::Greater => assert!(el.gt(&30)),
///            Ordering::Equal => assert!(el.eq(&30)),
///            Ordering::Less => assert!(el.lt(&30)),
///        }
///    }
///     assert_eq!(ptr, 4);
/// }
/// ```
pub fn partition<T>(collection: &mut [T], start: usize, end: usize) -> usize
where
    T: Ord + PartialEq + Copy + Debug,
{
    println!("Arr: {:?}, low: {}, high: {}", collection, start, end);
    let pivot = collection[end];
    let mut pointer = start;
    let mut i = start;

    loop {
        if collection[i] < pivot {
            collection.swap(i, pointer);
            pointer += 1;
        }
        i += 1;

        if i > end {
            break;
        }
    }

    collection.swap(pointer, end);
    pointer
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_semi_sorted() {
        let mut arr = vec![1, 23, 2, 32, 29, 33];
        quicksort(&mut arr);
        assert_eq!(arr, [1, 2, 23, 29, 32, 33]);
    }

    #[test]
    fn test_backwards() {
        let mut arr = vec![50, 25, 10, 5, 1];
        quicksort(&mut arr);
        assert_eq!(arr, [1, 5, 10, 25, 50]);
    }

    #[test]
    fn test_sorted() {
        let mut arr = vec![1, 5, 10, 25, 50];
        quicksort(&mut arr);
        assert_eq!(arr, [1, 5, 10, 25, 50]);
    }

    #[test]
    fn test_empty() {
        let mut arr: Vec<u32> = vec![];
        quicksort(&mut arr);
        assert_eq!(arr, []);
    }

    #[test]
    fn test_len_two() {
        let mut arr = vec![5, 1];
        quicksort(&mut arr);
        assert_eq!(arr, [1, 5]);
    }

    #[test]
    fn test_partially_sorted() {
        let mut arr = vec![50, 75, 1, 1, 3, 4, 5, 6, 50];
        quicksort(&mut arr);
        assert_eq!(arr, [1, 1, 3, 4, 5, 6, 50, 50, 75]);
    }
}
