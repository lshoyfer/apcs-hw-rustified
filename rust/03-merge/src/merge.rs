// Given two sorted arrays a and b, merge them into one sorted array.
use std::cmp::Ordering::*;

pub fn merge(arr1: &[u32], arr2: &[u32]) -> Vec<u32> {
    let (mut p1, mut p2) = (0usize, 0usize);
    let mut build = vec![];

    while p1 < arr1.len() && p2 < arr2.len() {
        match arr1[p1].cmp(&arr2[p2]) {
            Greater => {
                build.push(arr2[p2]);
                p2 += 1;
            }
            Less => {
                build.push(arr1[p1]);
                p1 += 1;
            }
            Equal => {
                build.push(arr1[p1]);
                p1 += 1;
            }
        }     
    }

    if p1 < arr1.len() {
        build.extend_from_slice(&arr1[p1..]);
    } else if p2 < arr2.len() {
        build.extend_from_slice(&arr2[p2..]);
    }

    build
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equal_sizes_1() {
        let a1 = [3, 4, 5];
        let b1 = [1, 2, 7];

        assert_eq!(vec![1, 2, 3, 4, 5, 7], merge(&a1, &b1));
    }

    #[test]
    fn a_length_less_than_b_length_2() {
        let a2 = [1, 5];
        let b2 = [2, 4, 6];

        assert_eq!(vec![1, 2, 4, 5, 6], merge(&a2, &b2));
    }

    #[test]
    fn a_length_greater_than_b_length_3() {
        let a3 = [1, 5, 9];
        let b3 = [2, 7];

        assert_eq!(vec![1, 2, 5, 7, 9], merge(&a3, &b3));
    }

    #[test]
    fn merge_sort_1() {

    }

    #[test]
    fn merge_sort_2() {

    }
}