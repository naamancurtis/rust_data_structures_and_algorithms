extern crate unicode_segmentation;
use unicode_segmentation::UnicodeSegmentation;

/// ## Is Subsequence Challenge
/// Given two strings, establish whether or not the first string is a subsequence of the second
///
/// ```
/// use problem_solving_patterns::multiple_pointers_pattern::is_subsequence::is_subsequence;
///
/// fn test_valid_substring() {
///     let result = is_subsequence(String::from("test"), String::from("A test string"));
///     assert_eq!(result, true);
/// }
/// ```
///
/// The solution below stays true to the design pattern specified, however given the specific way
/// that the Rust language treats strings, there are likely easier ways of fulfilling this requirement.
/// For example:
/// ```text
/// if full_string.contains(sub_string.as_str()) {
//        return true;
//  }
//  false
/// ```
///
pub fn is_subsequence(mut sub_string: String, mut full_string: String) -> bool {
    if sub_string.is_empty() || full_string.is_empty() || sub_string.len() > full_string.len() {
        return false;
    }

    sub_string.make_ascii_lowercase();
    full_string.make_ascii_lowercase();

    let sub_string =
        UnicodeSegmentation::graphemes(sub_string.as_str(), true).collect::<Vec<&str>>();
    let sub_string_length = sub_string.len();
    let full_string =
        UnicodeSegmentation::graphemes(full_string.as_str(), true).collect::<Vec<&str>>();

    let mut pointer_1 = 0;

    while pointer_1 <= full_string.len() - sub_string_length {
        if full_string[pointer_1] == sub_string[0]
            && full_string[pointer_1 + sub_string_length - 1] == sub_string[sub_string_length - 1]
        {
            for i in 1..sub_string_length {
                if full_string[pointer_1 + i] != sub_string[i] {
                    break;
                }
            }
            return true;
        }
        pointer_1 += 1;
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_valid_substring_start() {
        let result = is_subsequence(String::from("test"), String::from("test a string"));
        assert_eq!(result, true);
    }

    #[test]
    fn test_valid_substring_end() {
        let result = is_subsequence(String::from("test"), String::from("A test"));
        assert_eq!(result, true);
    }

    #[test]
    fn test_one_word() {
        let result = is_subsequence(String::from("test"), String::from("thisisateststring"));
        assert_eq!(result, true);
    }

    #[test]
    fn test_case_insensitive() {
        let result = is_subsequence(String::from("test"), String::from("this is a TeSt string"));
        assert_eq!(result, true);
    }

    #[test]
    fn test_invalid_substring() {
        let result = is_subsequence(
            String::from("test"),
            String::from("There is nothing in this string"),
        );
        assert_eq!(result, false);
    }

    #[test]
    fn test_invalid_substring_start() {
        let result = is_subsequence(String::from("test"), String::from("tes this string"));
        assert_eq!(result, false);
    }

    #[test]
    fn test_invalid_substring_end() {
        let result = is_subsequence(String::from("test"), String::from("this tes"));
        assert_eq!(result, false);
    }

    #[test]
    fn test_empty_string() {
        let result = is_subsequence(String::from("Test"), String::from(""));
        assert_eq!(result, false);
    }

    #[test]
    fn test_empty_sub_string() {
        let result = is_subsequence(String::from(""), String::from("Test"));
        assert_eq!(result, false);
    }

    #[test]
    fn test_empty_strings() {
        let result = is_subsequence(String::from(""), String::from(""));
        assert_eq!(result, false);
    }

    #[test]
    fn test_sub_string_larger() {
        let result = is_subsequence(String::from("Testing"), String::from("test"));
        assert_eq!(result, false);
    }
}
