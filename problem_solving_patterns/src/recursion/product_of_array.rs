use std::ops::Mul;

/// ## Recursion: Product of Array Challenge
/// Write out a function that recursively calculates the product of an array
///
/// ```
/// use problem_solving_patterns::recursion::product_of_array::recursive_array_product;
///
/// fn test_simple_array() {
///     let result = recursive_array_product(&vec![1,2,3,4]);
///     assert_eq!(result, 24);
/// }
/// ```
///
/// This has been implemented recusively inline with the challenge, however in reality
/// something like this is much more effectively done with something like:
///
/// ```text
/// let product = collection.iter().fold(1i32, |a, &b| a * b);
/// // or
/// let product = collection.iter().product::<i32>();
/// ```
///
pub fn recursive_array_product<T>(collection: &[T]) -> T
where
    T: Copy + Mul<T, Output = T> + From<i32>,
{
    if collection.is_empty() {
        return 1.into();
    }
    collection[0] * recursive_array_product(&collection[1..])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_1() {
        let result = recursive_array_product(&vec![1, 2, 3]);
        assert_eq!(result, 6);
    }

    #[test]
    fn test_2() {
        let result = recursive_array_product(&vec![1, 2, 3, 10]);
        assert_eq!(result, 60);
    }
}
