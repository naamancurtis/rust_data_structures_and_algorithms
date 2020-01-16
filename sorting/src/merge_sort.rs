//! # Merge Sort
//!
//! Merge Sort is a Divide and Conquer algorithm. It divides input array in two halves, calls
//! itself for the two halves and then merges the two sorted halves back together.
//!
//! - Time Complexity: **O**(n _log_(n))
//! - Space Complexity: **O**(n)

/// Recursive implementation of Merge Sort
///
///  # Examples
/// ```
/// use sorting::merge_sort::recursive_merge_sort;
///
/// fn simple_recursive_sort() {
///     let mut arr = vec![37, 45, 29, 8];
///     recursive_merge_sort(&mut arr);
///     assert_eq!(arr, [8, 29, 37, 45]);
/// }
/// ```
pub fn recursive_merge_sort<T>(collection: &mut [T])
where
    T: Ord + Copy,
{
    if collection.len() > 1 {
        let (lhs, rhs) = collection.split_at_mut(collection.len() / 2);
        recursive_merge_sort(lhs);
        recursive_merge_sort(rhs);
        merge(collection, collection.len())
    }
}

/// Iterative implementation of Merge Sort
///
/// # Examples
/// ```
/// use sorting::merge_sort::iterative_merge_sort;
///
/// fn simple_iterative_sort() {
///     let mut arr = vec![37, 45, 29, 8];
///     iterative_merge_sort(&mut arr);
///     assert_eq!(arr, [8, 29, 37, 45]);
/// }
/// ```
pub fn iterative_merge_sort<T>(collection: &mut [T])
where
    T: Ord + Copy,
{
    let length = collection.len();
    if length <= 1 {
        return;
    }

    let mut current_sub_array_multiplier = 1;
    let mut current_sub_array_size = 2;

    loop {
        collection
            .chunks_mut(current_sub_array_size)
            .for_each(|sub_arr| merge(sub_arr, current_sub_array_size));

        if current_sub_array_size > length {
            break;
        }

        current_sub_array_multiplier += 1;
        current_sub_array_size = 2f64.powi(current_sub_array_multiplier) as usize;
    }
}

fn merge<T>(collection: &mut [T], sub_array_length: usize)
where
    T: Ord + Copy,
{
    if sub_array_length < 2 {
        return;
    }

    let mut temp_vec = Vec::with_capacity(collection.len());
    {
        let mid = sub_array_length / 2;
        let mut lhs = collection.iter().take(mid).peekable();
        let mut rhs = collection.iter().skip(mid).peekable();

        while let (Some(&lhs_el), Some(&rhs_el)) = (lhs.peek(), rhs.peek()) {
            if *lhs_el <= *rhs_el {
                temp_vec.push(*lhs.next().unwrap())
            } else {
                temp_vec.push(*rhs.next().unwrap())
            }
        }

        for el in lhs {
            temp_vec.push(*el);
        }

        for el in rhs {
            temp_vec.push(*el);
        }
    }

    assert_eq!(temp_vec.len(), collection.len());
    temp_vec
        .iter()
        .enumerate()
        .for_each(|(i, el)| collection[i] = *el);
}

#[cfg(test)]
extern crate rand;

#[cfg(test)]
mod recursive_tests {
    use super::*;
    use rand::{self, Rng};

    #[test]
    fn test_semi_sorted() {
        let mut arr = vec![1, 23, 2, 32, 29, 33];
        recursive_merge_sort(&mut arr);
        assert_eq!(arr, [1, 2, 23, 29, 32, 33]);
    }

    #[test]
    fn test_backwards() {
        let mut arr = vec![50, 25, 10, 5, 1];
        recursive_merge_sort(&mut arr);
        assert_eq!(arr, [1, 5, 10, 25, 50]);
    }

    #[test]
    fn test_sorted() {
        let mut arr = vec![1, 5, 10, 25, 50];
        recursive_merge_sort(&mut arr);
        assert_eq!(arr, [1, 5, 10, 25, 50]);
    }

    #[test]
    fn test_empty() {
        let mut arr: Vec<u32> = vec![];
        recursive_merge_sort(&mut arr);
        assert_eq!(arr, []);
    }

    #[test]
    fn test_len_two() {
        let mut arr = vec![5, 1];
        recursive_merge_sort(&mut arr);
        assert_eq!(arr, [1, 5]);
    }

    #[test]
    fn test_partially_sorted() {
        let mut arr = vec![50, 75, 1, 1, 3, 4, 5, 6, 50];
        recursive_merge_sort(&mut arr);
        assert_eq!(arr, [1, 1, 3, 4, 5, 6, 50, 50, 75]);
    }

    #[test]
    fn test_long_zeroes() {
        let mut vec = vec![0u8; 10000];
        recursive_merge_sort(&mut vec);
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
        recursive_merge_sort(&mut vec);
        for i in 0..vec.len() - 1 {
            assert!(vec[i] <= vec[i + 1])
        }
    }
}

#[cfg(test)]
mod iterative_tests {
    use super::*;
    use rand::{self, Rng};

    #[test]
    fn test_semi_sorted() {
        let mut arr = vec![1, 23, 2, 32, 29, 33];
        iterative_merge_sort(&mut arr);
        assert_eq!(arr, [1, 2, 23, 29, 32, 33]);
    }

    #[test]
    fn test_backwards() {
        let mut arr = vec![50, 25, 10, 5, 1];
        iterative_merge_sort(&mut arr);
        assert_eq!(arr, [1, 5, 10, 25, 50]);
    }

    #[test]
    fn test_sorted() {
        let mut arr = vec![1, 5, 10, 25, 50];
        iterative_merge_sort(&mut arr);
        assert_eq!(arr, [1, 5, 10, 25, 50]);
    }

    #[test]
    fn test_empty() {
        let mut arr: Vec<u32> = vec![];
        iterative_merge_sort(&mut arr);
        assert_eq!(arr, []);
    }

    #[test]
    fn test_len_two() {
        let mut arr = vec![5, 1];
        iterative_merge_sort(&mut arr);
        assert_eq!(arr, [1, 5]);
    }

    #[test]
    fn test_partially_sorted() {
        let mut arr = vec![50, 75, 1, 1, 3, 4, 5, 6, 50];
        iterative_merge_sort(&mut arr);
        assert_eq!(arr, [1, 1, 3, 4, 5, 6, 50, 50, 75]);
    }

    #[test]
    fn test_long_zeroes() {
        let mut vec = vec![0u8; 10000];
        iterative_merge_sort(&mut vec);
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
        iterative_merge_sort(&mut vec);
        for i in 0..vec.len() - 1 {
            assert!(vec[i] <= vec[i + 1])
        }
    }
}
