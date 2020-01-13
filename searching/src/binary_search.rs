use std::cmp::Ordering;

/// ## Binary Search Challenge
/// Given a sorted collection and a value, parse the collection and return the index where that
/// value resides.
///
/// ```
/// use searching::binary_search::binary_search;
///
/// fn test_lower() {
///     let result = binary_search(&vec![1, 2, 3, 4, 5], 2);
///     assert_eq!(result, Some(1));
/// }
/// ```
pub fn binary_search<T>(collection: &[T], target_value: T) -> Option<usize>
where
    T: PartialEq + PartialOrd,
{
    if collection.is_empty() {
        return None;
    }

    let mut start = 0;
    let mut end = collection.len() - 1;
    let middle_fn = |start, end| -> usize { start + ((end - start) / 2) };

    loop {
        let middle = middle_fn(start, end);

        match collection[middle].partial_cmp(&target_value) {
            Some(Ordering::Less) => start = middle,
            Some(Ordering::Greater) => end = middle,
            Some(Ordering::Equal) => return Some(middle),
            _ => panic!("This should not be reachable"),
        }

        if start == middle && start + 1 == end {
            if collection[end] == target_value {
                return Some(end);
            } else {
                return None;
            };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_first_odd() {
        let result = binary_search(&vec![1, 2, 3, 4, 5], 1);
        assert_eq!(result, Some(0));
    }

    #[test]
    fn test_first_even() {
        let result = binary_search(&vec![1, 2, 3, 4, 5, 6], 1);
        assert_eq!(result, Some(0));
    }

    #[test]
    fn test_middle_odd() {
        let result = binary_search(&vec![1, 2, 3, 4, 5], 3);
        assert_eq!(result, Some(2));
    }

    #[test]
    fn test_middle_even() {
        let result = binary_search(&vec![1, 2, 3, 4, 5, 6], 3);
        assert_eq!(result, Some(2));
    }

    #[test]
    fn test_upper() {
        let result = binary_search(&vec![1, 2, 3, 4, 5], 4);
        assert_eq!(result, Some(3));
    }

    #[test]
    fn test_last_odd() {
        let result = binary_search(&vec![1, 2, 3, 4, 5], 5);
        assert_eq!(result, Some(4));
    }

    #[test]
    fn test_last_even() {
        let result = binary_search(&vec![1, 2, 3, 4, 5, 6], 6);
        assert_eq!(result, Some(5));
    }

    #[test]
    fn test_longer_array_start() {
        let result = binary_search(
            &vec![
                5, 6, 10, 13, 14, 18, 30, 34, 35, 37, 40, 44, 64, 79, 84, 86, 95, 96, 98, 99,
            ],
            10,
        );
        assert_eq!(result, Some(2));
    }

    #[test]
    fn test_longer_array_end() {
        let result = binary_search(
            &vec![
                5, 6, 10, 13, 14, 18, 30, 34, 35, 37, 40, 44, 64, 79, 84, 86, 95, 96, 98, 99,
            ],
            95,
        );
        assert_eq!(result, Some(16));
    }

    #[test]
    fn test_longer_array_out_of_bounds() {
        let result = binary_search(
            &vec![
                5, 6, 10, 13, 14, 18, 30, 34, 35, 37, 40, 44, 64, 79, 84, 86, 95, 96, 98, 99,
            ],
            100,
        );
        assert_eq!(result, None);
    }

    #[test]
    fn test_longer_array() {
        let result = binary_search(&vec![], 10);
        assert_eq!(result, None);
    }
}
