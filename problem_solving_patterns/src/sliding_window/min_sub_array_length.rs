/// ## Min Sub Array Length Challenge
/// Given an array of positive integers and an integer, return the minimal contiguous
/// sub array that the sum of which is greater than or equal to the integer passed, if
/// there isn't one, return 0 instead.
///
/// ```
/// use problem_solving_patterns::sliding_window::min_sub_array_length::min_sub_array;
///
/// fn test_valid_average() {
///     let result = min_sub_array(&vec![2, 3, 1, 2, 4, 3], 7);
///     assert_eq!(result, 2);
/// }
/// ```
pub fn min_sub_array(collection: &[i32], target_value: i32) -> i32 {
    if collection.is_empty() || target_value <= 0 {
        return 0;
    } else if collection[0] >= target_value {
        return 1;
    }

    let mut min_number_of_elements_required = std::i32::MAX;
    let mut pointer_1 = 0;
    let mut pointer_2 = 1;
    let mut temp_sum = collection[0];

    loop {
        if pointer_2 < collection.len() {
            temp_sum += collection[pointer_2];
        }

        if temp_sum >= target_value {
            // Move pointer 1 up as far as possible where it still exceeds the target value
            while (temp_sum - collection[pointer_1]) >= target_value && pointer_1 < pointer_2 {
                temp_sum -= collection[pointer_1];
                pointer_1 += 1;
            }

            min_number_of_elements_required =
                min_number_of_elements_required.min((pointer_2 - pointer_1 + 1) as i32);
        }

        // If pointer 2 is at the end of the array and we can't move pointer 1 up any further, break
        if pointer_2 == collection.len() - 1 && (temp_sum - collection[pointer_1]) < target_value {
            break;
        }

        pointer_2 = (collection.len() - 1).min(pointer_2 + 1);
    }

    // Assumption: If min_number_of_elements_required is still the constant, we've found no values, so return 0
    if min_number_of_elements_required == std::i32::MAX {
        min_number_of_elements_required = 0;
    }

    min_number_of_elements_required
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_valid_array() {
        let result = min_sub_array(&vec![2, 1, 6, 5, 4], 9);
        assert_eq!(result, 2);
    }

    #[test]
    fn test_single_element() {
        let result = min_sub_array(&vec![3, 1, 7, 11, 2, 9, 8, 21, 62, 33, 19], 52);
        assert_eq!(result, 1);
    }

    #[test]
    fn test_middle_sub_array() {
        let result = min_sub_array(&vec![1, 4, 16, 22, 5, 7, 8, 9, 10], 39);
        assert_eq!(result, 3);
    }

    #[test]
    fn test_long_sub_array() {
        let result = min_sub_array(&vec![1, 4, 16, 22, 5, 7, 8, 9, 10], 55);
        assert_eq!(result, 5);
    }

    #[test]
    fn test_valid_sub_array_2() {
        let result = min_sub_array(&vec![4, 3, 3, 8, 1, 2, 3], 11);
        assert_eq!(result, 2);
    }

    #[test]
    fn test_no_match() {
        let result = min_sub_array(&vec![1, 4, 16, 22, 5, 7, 8, 9, 10], 95);
        assert_eq!(result, 0);
    }

    #[test]
    fn test_multiple_answers_valid_last() {
        let result = min_sub_array(&vec![1, 4, 5, 6, 4, 10, 9, 5, 7, 8, 9, 10, 11], 20);
        assert_eq!(result, 2);
    }

    #[test]
    fn test_multiple_answers_valid_first() {
        let result = min_sub_array(&vec![19, 2, 1, 4, 5, 6, 4, 7, 12, 5, 7, 8, 9, 10], 20);
        assert_eq!(result, 2);
    }

    #[test]
    fn empty_array() {
        let input: Vec<i32> = Vec::new();
        let result = min_sub_array(&input, 95);
        assert_eq!(result, 0);
    }
}
