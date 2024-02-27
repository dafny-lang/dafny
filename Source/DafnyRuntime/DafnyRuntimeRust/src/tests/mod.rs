// Test module
#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn test_sequence() {
        let values = vec![1, 2, 3];
        let seq = Sequence::<i32>::from_array_owned(values.clone());
        assert_eq!(seq.cardinality_usize(), 3);
        assert_eq!(seq.to_array(), values.into());
    
        // Create a concat array, wrap it into a lazy one, get the i-th element,
        // and verify that this operation flattened the array
        let left = Sequence::<i32>::from_array_owned(vec![1, 2, 3]);
        let right = Sequence::<i32>::from_array_owned(vec![4, 5, 6]);
        let concat = Sequence::<i32>::new_concat_sequence(&left, &right);

        assert_eq!(concat.cardinality_usize(), 6);
        match &concat {
            Sequence::ConcatSequence { boxed, length, left, right} => {
                assert_eq!(*length, 6);
                assert_eq!(unsafe {&*left.get()}.cardinality_usize(), 3);
                // Test that boxed is None
                assert!(boxed.as_ref().clone().borrow().as_ref().is_none());
            },
            _ => panic!("This should never happen")        
        }
        let value = concat.select(0);
        assert_eq!(value, 1);
        match &concat {
            crate::Sequence::ConcatSequence { boxed, length, left, right} => {
                assert_eq!(*boxed.as_ref().clone().borrow().as_ref().unwrap().as_ref(), vec![1, 2, 3, 4, 5, 6]);
            },
            _ => panic!("This should never happen")        
        }
    }


    #[test]
    fn test_dafny_int() {
        assert_eq!(int!(0).to_usize(), Some(0));
        assert_eq!(int!(42).to_usize(), Some(42));
    }

    #[test]
    fn test_dafny_sequence_print() {
        let hello = seq![
            DafnyChar('H'), DafnyChar('e'), DafnyChar('l'), DafnyChar('l'), DafnyChar('o')];
        assert_eq!(DafnyPrintWrapper(&hello).to_string(), "Hello");
        let hello = seq![
            DafnyCharUTF16(0x0048), DafnyCharUTF16(0x0065), DafnyCharUTF16(0x006c), DafnyCharUTF16(0x006c), DafnyCharUTF16(0x006f)
        ];
        assert_eq!(DafnyPrintWrapper(&hello).to_string(), "Hello");
        assert_eq!(DafnyPrintWrapper(&string_of("Hello")).to_string(), "Hello");
        let hello = seq![1, 2, 3];
        assert_eq!(DafnyPrintWrapper(&hello).to_string(), "[1, 2, 3]");
    }
    #[test]
    fn test_dafny_sequence() {
        let s = seq![55, 56, 57];
        assert_eq!(seq![55, 56] != s, true);
        assert_eq!(s.cardinality_usize(), 3);
        assert_eq!(s.cardinality(), int!(3));
        assert_eq!(s.get(&int!(1)), 56);
        assert_eq!(s.slice(&int!(1), &int!(2)), seq![56]);
        assert_eq!(s.take(&int!(2)), seq![55, 56]);
        assert_eq!(s.drop(&int!(1)), seq![56, 57]);
        assert_eq!(s.update_index(&int!(1), &8), seq![55, 8, 57]);
        assert_eq!(s.concat(&seq![58, 59]), seq!(55, 56, 57, 58, 59));
    }

    #[test]
    fn test_dafny_set() {
        let s = set!{55, 56, 57, 56, 58};
        let t = set!{59, 58, 57};
        assert_eq!(s.cardinality_usize(), 4);
        assert_eq!(s.cardinality(), int!(4));
        assert_eq!(s.contains(&55), true);
        assert_eq!(s.contains(&54), false);
        assert_eq!(s.merge(&set!{}), s);
        assert_eq!(set!{}.merge(&s), s);
        assert_eq!(s.merge(&t), set!{59, 58, 57, 56, 55});
        assert_eq!(s.intersect(&t), set!{57, 58});
        assert_eq!(s.subtract(&set!{}), s);
        assert_eq!(set!{}.subtract(&s), set!{});
        let smt = s.subtract(&t);
        assert_eq!(smt, set!{55, 56});
        assert_eq!(t.subtract(&s), set!{59});
        assert_eq!(s.disjoint(&set!{}), true);
        assert_eq!(set!{}.disjoint(&s), true);
        assert_eq!(s.disjoint(&t), false);
        assert_eq!(t.disjoint(&s), false);
        assert_eq!(smt.disjoint(&t), true);
        assert_eq!(t.disjoint(&smt), true);
        assert_eq!(s.elements(), s);
        assert_eq!(s.as_dafny_multiset(), Multiset::from_array(&vec!(55, 56, 57, 58)));        
    }

    #[test]
    fn test_dafny_multiset() {
        let s = multiset!{55, 56, 57, 56, 58};
        let t = multiset!{59, 58, 57, 56};
        assert_eq!(s.cardinality_usize(), 5);
        assert_eq!(s.cardinality(), int!(5));
        assert_eq!(s.contains(&55), true);
        assert_eq!(s.contains(&54), false);
        assert_eq!(s.get(&54), int!(0));
        assert_eq!(s.get(&55), int!(1));
        assert_eq!(s.get(&56), int!(2));
        assert_eq!(s.get(&57), int!(1));
        assert_eq!(s.merge(&multiset!{}), s);
        assert_eq!(multiset!{}.merge(&s), s);
        let merged = multiset!{59, 58, 58, 57, 57, 56, 56, 56, 55};
        assert_eq!(s.merge(&t), merged);
        assert_eq!(merged.cardinality_usize(), 9);
        assert_eq!(s.intersect(&t), multiset!{57, 58, 56});
        assert_eq!(s.subtract(&multiset!{}), s);
        assert_eq!(multiset!{}.subtract(&s), multiset!{});
        let smt = s.subtract(&t);
        assert_eq!(smt, multiset!{55, 56});
        let tms = t.subtract(&s);
        assert_eq!(tms, multiset!{59});
        assert_eq!(s.disjoint(&multiset!{}), true);
        assert_eq!(multiset!{}.disjoint(&s), true);
        assert_eq!(s.disjoint(&t), false);
        assert_eq!(t.disjoint(&s), false);
        assert_eq!(smt.disjoint(&t), false);
        assert_eq!(t.disjoint(&smt), false);
        assert_eq!(tms.disjoint(&s), true);
        assert_eq!(s.disjoint(&tms), true);
        assert_eq!(s.as_dafny_multiset(), s);
    }

    #[test]
    fn test_dafny_map() {
        let m_empty: Map<i32, i32> = map![];
        let m_3 = map![1 => 2, 3 => 6, 5 => 10];
        let k_3 = set!{1, 3, 5};
        let v_3 = set!{2, 6, 10};
        assert_eq!(m_empty.cardinality_usize(), 0);
        assert_eq!(m_empty.cardinality(), int!(0));
        assert_eq!(m_3.cardinality_usize(), 3);
        assert_eq!(m_3.cardinality(), int!(3));
        assert_eq!(m_3.contains(&1), true);
        assert_eq!(m_3.contains(&0), false);
        assert_eq!(m_3.keys(), k_3);
        assert_eq!(m_3.values(), v_3);
        assert_eq!(m_3.get(&1), 2);
        assert_eq!(m_3.get_or_none(&1), Some(2));
        assert_eq!(m_3.get_or_none(&0), None);
        let mut m_4 = m_3.update_index(&0, &2);
        assert_eq!(m_3.contains(&0), false);
        assert_eq!(m_4.contains(&0), true);
        m_4 = m_4.update_index_owned(0, 7);
        assert_eq!(m_4.contains(&0), true);
        
        assert_eq!(m_4.get(&0), 7);
        assert_eq!(m_4.cardinality_usize(), 4);
        assert_eq!(m_4.merge(&map![]), m_4);
        assert_eq!(map![].merge(&m_4), m_4);
        let m_5 = m_4.merge(&map![3 => 9, 6 => 12]);
        assert_eq!(m_5.cardinality_usize(), 5);
        println!("m_4 is {:?}", m_4);
        assert_eq!(m_4.get(&3), 6);
        assert_eq!(m_5.get(&3), 9);
        assert_eq!(m_5.subtract(&set!{}), m_5);
        let m_4b = m_5.subtract(&set!{3});
        assert_eq!(m_4b.cardinality_usize(), 4);
        assert_eq!(m_4b.contains(&3), false)
    }
}
// Struct containing two reference-counted fields
