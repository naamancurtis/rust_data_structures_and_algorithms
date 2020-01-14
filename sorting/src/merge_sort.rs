/// ## Merge Sort
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
///
/// ```
/// use sorting::merge_sort::recursive_merge_sort;
///
/// fn test_simple_sort() {
///     let mut arr = vec![37, 45, 29, 8];
///     recursive_merge_sort(&mut arr);
///     assert_eq!(arr, [8, 29, 37, 45]);
/// }
/// ```
pub fn recursive_merge_sort<T>(collection: &mut [T])
where
    T: Ord + PartialEq + Copy,
{
    if collection.len() > 1 {
        let (lhs, rhs) = collection.split_at_mut(collection.len() / 2);
        recursive_merge_sort(lhs);
        recursive_merge_sort(rhs);
        merge(collection)
    }
}

pub fn merge<T>(collection: &mut [T])
where
    T: Ord + PartialEq + Copy,
{
    let length = collection.len();
    if length < 2 {
        return;
    }

    let mut temp_vec = Vec::with_capacity(length);
    {
        let mid = length / 2;
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

    temp_vec
        .iter()
        .enumerate()
        .for_each(|(i, el)| collection[i] = *el)
}

#[cfg(test)]
mod tests {
    use super::*;

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
}
