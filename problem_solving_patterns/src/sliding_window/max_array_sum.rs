/// ## Max Array Sum Challenge
/// Given an array of integers and a number of items to use, work out the maximum sum of that many
/// consecutive items within that array.
///
/// ```
/// use problem_solving_patterns::sliding_window::max_array_sum::max_array_sum;
///
/// fn test_valid_average() {
///     let result = max_array_sum(&vec![1, 2, 3, 4, 100, 200, 300], 2);
///     assert_eq!(result, 500);
/// }
/// ```
pub fn max_array_sum(collection: &[i32], number_of_elements_to_use: usize) -> i32 {
    if collection.is_empty()
        || number_of_elements_to_use <= 0
        || number_of_elements_to_use > collection.len()
    {
        return 0;
    }

    let mut pointer = 0;

    let mut temp_sum: i32 = collection.iter().take(number_of_elements_to_use).sum();
    let mut max_sum = temp_sum.clone();

    for i in 0..collection.len() - number_of_elements_to_use {
        temp_sum = temp_sum + collection[number_of_elements_to_use + i] - collection[pointer];
        pointer += 1;

        if temp_sum > max_sum {
            max_sum = temp_sum;
        }
    }

    max_sum
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn max_sum_at_start() {
        let result = max_array_sum(&vec![5, 5, 1, 2], 3);
        assert_eq!(result, 11);
    }

    #[test]
    fn max_sum_in_middle() {
        let result = max_array_sum(&vec![5, 5, 1, 22, 1, 12, 10], 2);
        assert_eq!(result, 23);
    }

    #[test]
    fn max_sum_at_end() {
        let result = max_array_sum(&vec![5, 5, 1, 1, 12, 10], 4);
        assert_eq!(result, 24);
    }

    #[test]
    fn num_to_use_is_zero() {
        let result = max_array_sum(&vec![5, 5, 1, 1, 12, 10], 0);
        assert_eq!(result, 0);
    }

    #[test]
    fn num_to_use_is_greater_than_array_length() {
        let result = max_array_sum(&vec![5, 5, 1, 1, 12, 10], 20);
        assert_eq!(result, 0);
    }
}
