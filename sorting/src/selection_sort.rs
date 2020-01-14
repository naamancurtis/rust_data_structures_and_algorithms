/// ## Selection Sort
/// Given an unsorted collection, return a sorted collection through the use of the
/// selection sort algorithm.
///
/// As the collection is parsed, the smallest value is found in each iteration
/// and placed at the start of the collection. This kind of sort is generally
/// highly inefficient, but has the niche use case where you want to minimise
/// writes
///
/// Time Complexity: O(n^2)
/// Space Complexity: O(1)
///
///
/// ```
/// use sorting::selection_sort::selection_sort;
///
/// fn test_simple_sort() {
///     let mut arr = vec![37, 45, 29, 8];
///     let result = selection_sort(&mut arr);
///     assert_eq!(result, [8, 29, 37, 45]);
/// }
/// ```
pub fn selection_sort<T>(collection: &mut [T]) -> &[T]
where
    T: Ord + PartialEq + Copy,
{
    if collection.is_empty() {
        return collection;
    }
    let mut pointer = 0;

    while pointer < collection.len() {
        match collection
            .iter()
            .enumerate()
            .skip(pointer)
            .min_by(|(_, x), (_, y)| x.cmp(y))
        {
            Some((i, _)) if pointer != i => collection.swap(pointer, i),
            _ => {}
        }
        pointer += 1;
    }

    collection
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_semi_sorted() {
        let mut arr = vec![1, 23, 2, 32, 29, 33];
        let result = selection_sort(&mut arr);
        assert_eq!(result, [1, 2, 23, 29, 32, 33]);
    }

    #[test]
    fn test_backwards() {
        let mut arr = vec![50, 25, 10, 5, 1];
        let result = selection_sort(&mut arr);
        assert_eq!(result, [1, 5, 10, 25, 50]);
    }

    #[test]
    fn test_sorted() {
        let mut arr = vec![1, 5, 10, 25, 50];
        let result = selection_sort(&mut arr);
        assert_eq!(result, [1, 5, 10, 25, 50]);
    }

    #[test]
    fn test_empty() {
        let mut arr = vec![];
        let result: &[u32] = selection_sort(&mut arr);
        assert_eq!(result, []);
    }

    #[test]
    fn test_len_two() {
        let mut arr = vec![5, 1];
        let result = selection_sort(&mut arr);
        assert_eq!(result, [1, 5]);
    }

    #[test]
    fn test_partially_sorted() {
        let mut arr = vec![50, 75, 1, 1, 3, 4, 5, 6, 50];
        let result = selection_sort(&mut arr);
        assert_eq!(result, [1, 1, 3, 4, 5, 6, 50, 50, 75]);
    }
}
