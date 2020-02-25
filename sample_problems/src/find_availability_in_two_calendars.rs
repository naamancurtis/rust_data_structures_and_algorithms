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
//! - Looping over timeslots array to fill the results array - **O**(s)
//!     - Although this is a nested `loop{for...{}}` structure, exactly `s` loops will be run
//!
//! **Total:** **O**(2s + c1 + c2) which simplifies to **O**(n) - Linear Time
//!
//! ### Space
//! - Ref Array - **O**(s) - *where s is the total number of slots that a meeting could fit in between the bounds*
//! - HashSet - **O**(u') - *where u' is all of the unavailable time slots*
//! - Results - **O**(n) - *where n is the total number of results*
//!
//! **Total:** **O**(n + s + u') - Linear Time

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
    let mut timeslots = Vec::new();
    for n in 0..num_of_blocks {
        timeslots.push(start + (n * duration))
    }

    let mut unavailable_timeslots = HashSet::new();

    parse_calendar(calendar_1, unavailable_timeslots.borrow_mut(), &timeslots);
    parse_calendar(calendar_2, unavailable_timeslots.borrow_mut(), &timeslots);

    let mut availability = Vec::new();

    let mut left_ptr = 0;
    let mut right_ptr;

    loop {
        if unavailable_timeslots.contains(&timeslots[left_ptr]) {
            left_ptr += 1;
            // Edge case where there's no valid times
            if left_ptr >= timeslots.len() {
                break;
            }
            continue;
        }

        if left_ptr == timeslots.len() - 1 {
            let start_time = timeslots[left_ptr];
            availability.push(tuple_int_to_string((start_time, start_time + duration)));
            break;
        }

        right_ptr = left_ptr + 1;

        for slot in timeslots.iter().skip(right_ptr) {
            if !unavailable_timeslots.contains(slot) {
                right_ptr += 1;
            } else {
                break;
            }
        }

        availability.push((
            int_to_string(timeslots[left_ptr]),
            int_to_string(timeslots[right_ptr]),
        ));

        left_ptr = right_ptr;
    }

    availability
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
