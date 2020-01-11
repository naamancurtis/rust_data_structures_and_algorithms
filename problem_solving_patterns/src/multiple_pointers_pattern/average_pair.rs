extern crate num;
use num::{Integer, Num, ToPrimitive};
use std::cmp::Ordering;
use std::iter::Sum;

/// ## Average Pair Challenge
/// Given a sorted collection of integers, find out if there are any pair of numbers within the
/// collection that equal a specified average value
///
/// ```
/// use problem_solving_patterns::multiple_pointers_pattern::average_pair::average_pair;
///
/// fn test_valid_average() {
///     let result = average_pair(&vec![1,2,3,4,5,6], 4.5);
///     assert_eq!(result, true);
/// }
/// ```
pub fn average_pair<I, N>(collection: &[I], target_average: N) -> bool
where
    I: Integer + ToPrimitive + PartialOrd + Sum<I> + Copy,
    N: Num + ToPrimitive + PartialOrd,
{
    if collection.len() < 2 {
        return false;
    }

    let mut pointer_1 = 0;
    let mut pointer_2 = collection.len() - 1;

    let average_fn = |ptr_1: usize, ptr_2: usize| -> f64 {
        (ToPrimitive::to_f64(&(collection[ptr_1] + collection[ptr_2])).unwrap() / 2f64)
    };

    let target_average = ToPrimitive::to_f64(&target_average).unwrap();
    let mut average = average_fn(pointer_1, pointer_2);

    while (average - target_average).abs() > 0.005 {
        if pointer_2 - pointer_1 == 1 {
            return false;
        }

        match average.partial_cmp(&target_average) {
            Some(Ordering::Less) => pointer_1 += 1,
            Some(Ordering::Greater) => pointer_2 -= 1,
            // We're handling the equals case within epsilon for the while loop
            _ => continue,
        }
        average = average_fn(pointer_1, pointer_2);
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_valid_arguments_2() {
        let result = average_pair(&vec![1, 2, 3], 2.5);
        assert_eq!(result, true);
    }

    #[test]
    fn test_longer_array() {
        let result = average_pair(&vec![1, 3, 6, 7, 9, 10, 22, 25], 9.5);
        assert_eq!(result, true);
    }

    #[test]
    fn test_invalid_arguments() {
        let result = average_pair(&vec![-10, -3, 0, 1, 2, 3], 4.1);
        assert_eq!(result, false);
    }

    #[test]
    fn test_empty_array() {
        let arr: Vec<u8> = vec![];
        let result = average_pair(&arr, 10);
        assert_eq!(result, false);
    }
}
