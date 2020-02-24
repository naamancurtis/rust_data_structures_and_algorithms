//! # Find availability from two calendars
//!
//! Question from this [YouTube video](https://www.youtube.com/watch?v=3Q_oYDQ2whs) - Clément Mihailescu
//!
//! ## Parameters:
//! - **Two calendars** - where a calendar is `[(String, String), ...]` where the tuple is `(start_time, end_time)`
//!     - The time is in military time and each entry represents a timeslot where they are NOT free
//!     (ie. they already have a meeting)
//! - **Meeting duration** - `int`
//! - **2 Calendar Bounds** - of which no meetings can occur outside of given `(String, String)`
//!
//! ## Return
//! - `[(String, String), ...]` - An array of all free blocks where a meeting could be scheduled.
//!     - *Note:* Each block should be a total period of cumulative free time. **NOT** blocks the size of the length of the meeting
//!
//! ## Assumptions
//! - You can assume the calendars are always sorted
//! - You can assume that no meetings in the calendars are outside of the bounds provided
//!
//! ## Solution Complexity
//!
//! ### Time
//! - Creating ref array - **O**(s) - *where s is the total number of slots that a meeting could fit in between the bounds*
//! - Looping over the calendars to fill the HashSet - **O**(c1 + c2)
//! - Looping over the ref array to find the available slots - **O**(s)
//! - Mapping strings to ints in unreduced array - **O**(u) - *where u is the length of the un-reduced array*
//! - Loop over unreduced array once to fill the reduced array - **O**(u)
//!
//! **Total:** **O**(2s + c1 + c2 + 2u) which simplifies to **O**(n)
//!
//! ### Space
//! - Ref Array - **O**(s) - *where s is the total number of slots that a meeting could fit in between the bounds*
//! - HashSet - **O**(u') - *where u' is all of the unavailable time slots*
//! - Unreduced availability array - **O**(u) - *where u is all of the available time slots*
//! - Reduced availability - **O**(u) - *worst case would be that you can't reduce any elements, and it's the same length*
//!
//! **Total:** **O**(2s + u) - *as `u + u' = s`*

use std::borrow::BorrowMut;
use std::collections::HashSet;

type Calendar = Vec<Block>;
type Block = (String, String);

pub fn find_availability(
    calendar_1: Calendar,
    calendar_2: Calendar,
    bound_1: Block,
    bound_2: Block,
    duration: i32,
) -> Calendar {
    let start = string_to_int(bound_1.0).max(string_to_int(bound_2.0));
    let end = string_to_int(bound_1.1).min(string_to_int(bound_2.1));

    let num_of_blocks = (end - start) / duration;
    let mut ref_arr = Vec::new();
    for n in 0..num_of_blocks {
        ref_arr.push(start + (n * duration))
    }

    let mut availability_map = HashSet::new();

    parse_calendar(calendar_1, availability_map.borrow_mut(), &ref_arr);
    parse_calendar(calendar_2, availability_map.borrow_mut(), &ref_arr);

    let mut unreduced_availability = Vec::new();

    ref_arr.into_iter().for_each(|time_slot| {
        if !availability_map.contains(&time_slot) {
            unreduced_availability.push(time_slot);
        }
    });

    let unreduced_availability = unreduced_availability
        .into_iter()
        .map(|start| (start, start + 30))
        .collect::<Vec<(i32, i32)>>();

    let mut reduced_availability = Vec::with_capacity(unreduced_availability.len());
    let mut ptr_left = 0;
    let mut ptr_right = 1;

    if unreduced_availability.is_empty() {
        return Vec::new();
    }

    loop {
        if ptr_right == unreduced_availability.len() && ptr_right - ptr_left == 1 {
            reduced_availability.push(tuple_int_to_string(unreduced_availability[ptr_left]));
            break;
        }

        if unreduced_availability[ptr_left].1 == unreduced_availability[ptr_right].0 {
            // Need to move ptr right up 1 to check the following thing
            ptr_right += 1;
        } else if ptr_right - ptr_left == 1 && ptr_right < unreduced_availability.len() {
            reduced_availability.push(tuple_int_to_string(unreduced_availability[ptr_left]));
            ptr_left += 1;
            ptr_right += 1;
        } else {
            reduced_availability.push((
                int_to_string(unreduced_availability[ptr_left].0),
                int_to_string(unreduced_availability[ptr_right - 1].1),
            ));
            ptr_left = ptr_right;
            ptr_right += 1;
        }

        if ptr_right > unreduced_availability.len() {
            break;
        }
    }

    reduced_availability
}

fn string_to_int(s: String) -> i32 {
    let split_str: Vec<_> = s.split(':').collect();
    (split_str[0].parse::<i32>().unwrap() * 60) + split_str[1].parse::<i32>().unwrap()
}

fn int_to_string(i: i32) -> String {
    format!("{:02}:{:02}", i / 60, (i % 60))
}

fn tuple_int_to_string(b: (i32, i32)) -> Block {
    (int_to_string(b.0), int_to_string(b.1))
}

fn parse_calendar(calendar: Calendar, set: &mut HashSet<i32>, ref_arr: &[i32]) {
    let mut ptr = 0;

    calendar
        .into_iter()
        .map(|(start, end)| (string_to_int(start), string_to_int(end)))
        .for_each(|(start_time, end_time)| {
            loop {
                let ptr_val = ref_arr[ptr];
                // This block is before the first bound
                if ptr_val >= end_time {
                    break;
                }

                // Ptr is between the values
                if start_time <= ptr_val && ptr_val <= end_time {
                    set.insert(ptr_val);
                    ptr += 1;
                }

                // Pointer value is below the start time, so we need to move it up
                if ptr_val < start_time {
                    ptr += 1;
                }

                if ptr >= ref_arr.len() {
                    break;
                }
            }
        });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = find_availability(
            vec![
                (String::from("9:00"), String::from("10:00")),
                (String::from("12:00"), String::from("12:30")),
                (String::from("14:00"), String::from("15:30")),
            ],
            vec![
                (String::from("9:30"), String::from("10:30")),
                (String::from("11:30"), String::from("13:30")),
                (String::from("14:00"), String::from("16:30")),
            ],
            (String::from("9:00"), String::from("18:30")),
            (String::from("8:45"), String::from("17:00")),
            30,
        );

        let expected = vec![
            (String::from("10:30"), String::from("11:30")),
            (String::from("13:30"), String::from("14:00")),
            (String::from("16:30"), String::from("17:00")),
        ];

        assert_eq!(result, expected);
    }

    #[test]
    fn no_matches() {
        let result = find_availability(
            vec![
                (String::from("9:00"), String::from("10:00")),
                (String::from("12:00"), String::from("12:30")),
                (String::from("14:00"), String::from("15:30")),
            ],
            vec![(String::from("9:30"), String::from("18:30"))],
            (String::from("9:00"), String::from("18:30")),
            (String::from("8:45"), String::from("17:00")),
            30,
        );

        assert!(result.is_empty());
    }
}
