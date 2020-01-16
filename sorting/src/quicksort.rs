//! # Quicksort
//!
//! QuickSort is a Divide and Conquer algorithm. It picks an element as a pivot and partitions a given array around the picked pivot.
//! It recursively applies the same partitioning logic to the arrays around the pivot until arrays are length 0 || 1, at which
//! point the array is sorted.
//!
//! Time Complexity: O(nlog(n))
//! Space Complexity: O(1) - Sort is in-place
//!
//! This implementation is based off https://github.com/kyrias/ironsort/

use std::cmp;
use std::cmp::Ordering;

/// Shorthand helper function which carries out in-place sorting of a slice of <T> where T: Ord.
///
/// # Examples
/// ```rust
/// use sorting::quicksort::quicksort;
///
/// fn simple_sort() {
///     let mut arr = vec![37, 45, 29, 8];
///     quicksort(&mut arr);
///     assert_eq!(arr, [8, 29, 37, 45]);
/// }
/// ```
pub fn quicksort<T>(arr: &mut [T])
where
    T: Ord,
{
    partition(arr, &|x, y| x.cmp(y))
}

/// Function carries out in-place sorting of a slice of <T> using a provided comparator function
///
/// # Examples
/// ```rust
/// use sorting::quicksort::quicksort_by;
///
/// fn simple_sort() {
///     let mut arr = vec![37, 45, 29, 8 ,10];
///     quicksort_by(&mut arr, &|x, y| x.cmp(y));
///     assert_eq!(arr, [8, 10, 29, 37, 45]);
/// }
/// ```
pub fn quicksort_by<T, F>(arr: &mut [T], cmp: &F)
where
    F: Fn(&T, &T) -> Ordering,
{
    partition(arr, cmp);
}

/// Partitions an array around a pivot point, which is assigned as the first
/// element in the array
fn partition<T, F>(arr: &mut [T], cmp: &F)
where
    F: Fn(&T, &T) -> Ordering,
{
    let len = arr.len();
    if len <= 1 {
        return;
    }

    // Set the pivot to the first element in the collection
    let pivot = 0;

    let mut left_ptr = 1;
    let mut right_ptr = arr.len() - 1;

    // Iterate over the collection from both sides
    loop {
        // For as long as the element is less than the pivot, move the pointer in
        while left_ptr < len && cmp(&arr[left_ptr], &arr[pivot]) != Ordering::Greater {
            left_ptr += 1;
        }

        // For as long as the elements are greater than the pivot, move the pointer in
        while right_ptr > 0 && cmp(&arr[right_ptr], &arr[pivot]) != Ordering::Less {
            right_ptr -= 1;
        }

        // We don't want the pointers passing each other
        if left_ptr >= right_ptr {
            break;
        }

        // To hit this point in code, the left pointer must have found something greater than
        // the pivot, and the right pointer must have found something less than the pivot.
        // Therefore we can swap these two values and then move the pointers 1 element inwards
        // ready for the next loop
        arr.swap(left_ptr, right_ptr);
        left_ptr += 1;
        right_ptr -= 1;
    }

    // Once we've broken out of the loop, the right_ptr points to a value lower than the pivot
    // Our pivot value was held in the [0] index of the collection, therefore we can swap the
    // two to complete this iteration of the sort
    arr.swap(pivot, right_ptr);

    // Recursively call this fn with the values from the start of the array up to
    // (but not including) the pivot
    partition(&mut arr[0..cmp::min(left_ptr - 1, right_ptr)], cmp);
    // Recursively call this fn with the values from 1 index above the pivot till the
    // end of the collection
    partition(&mut arr[cmp::max(left_ptr, right_ptr + 1)..], cmp);
}

#[cfg(test)]
extern crate rand;

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{self, Rng};

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

    #[test]
    fn test_long_zeroes() {
        let mut vec = vec![0u8; 10000];
        quicksort(&mut vec);
        for i in 0..vec.len() - 1 {
            assert!(vec[i] <= vec[i + 1])
        }
    }

    #[test]
    fn test_random() {
        let mut rng = rand::thread_rng();
        let mut vec = (0..10000)
            .map(|x| x * rng.gen_range(-10, 10))
            .collect::<Vec<i32>>();
        quicksort(&mut vec);
        for i in 0..vec.len() - 1 {
            assert!(vec[i] <= vec[i + 1])
        }
    }
}

#[test]
fn test_partition() {
    let mut arr = [37, 45, 29, 8, 16, 29, 30];
    partition(&mut arr, &|x, y| x.cmp(y));
    for (index, el) in arr.iter().enumerate() {
        match index.cmp(&5) {
            Ordering::Greater => assert!(el.gt(&37)),
            Ordering::Equal => assert!(el.eq(&37)),
            Ordering::Less => assert!(el.lt(&37)),
        }
    }
}
