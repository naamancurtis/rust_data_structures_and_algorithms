/*
    Create a function that accepts a sorted collection and returns a count of the number of unique
    values in that array.
*/

pub fn count_unique<T>(vec: Vec<T>) -> u32
where
    T: PartialEq,
{
    let mut pointer_1: usize = 0;
    let mut counter = 1;

    vec.iter().enumerate().for_each(|(index, value)| {
        if value != &vec[pointer_1] {
            counter += 1;
            pointer_1 = index;
        }
    });

    counter
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_a_i32_vec() {
        let result = count_unique(vec![1, 2, 3, 4]);
        assert_eq!(result, 4);
    }

    #[test]
    fn parses_a_i32_vec_with_duplicate_values() {
        let result = count_unique(vec![1, 1, 1, 1, 2, 3, 4]);
        assert_eq!(result, 4);
    }

    #[test]
    fn parses_a_i32_vec_with_multiple_duplicate_values() {
        let result = count_unique(vec![1, 1, 1, 1, 2, 2, 3, 3, 4, 10, 11]);
        assert_eq!(result, 6);
    }

    #[test]
    fn parses_a_i32_vec_with_negative_values() {
        let result = count_unique(vec![-10, -5, 1, 1, 2, 2, 3, 3, 4, 10, 11]);
        assert_eq!(result, 8);
    }

    #[test]
    fn parses_a_str_vec() {
        let result = count_unique(vec!["test", "test", "help"]);
        assert_eq!(result, 2);
    }

    #[test]
    fn parses_a_string_vec() {
        let result = count_unique(vec![
            String::from("test"),
            String::from("test"),
            String::from("help"),
        ]);
        assert_eq!(result, 2);
    }
}
