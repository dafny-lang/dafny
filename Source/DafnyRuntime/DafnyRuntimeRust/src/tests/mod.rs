#![allow(nonstandard_style)]

// Test module
#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn test_int() {
        let x = int!(37);
        assert_eq!(x.to_u8().unwrap(), truncate!(x.clone(), u8));
        assert_eq!(x.to_u16().unwrap(), truncate!(x.clone(), u16));
        assert_eq!(x.to_u32().unwrap(), truncate!(x.clone(), u32));
        assert_eq!(x.to_u64().unwrap(), truncate!(x.clone(), u64));
        assert_eq!(x.to_u128().unwrap(), truncate!(x.clone(), u128));
        assert_eq!(x.to_i8().unwrap(), truncate!(x.clone(), i8));
        assert_eq!(x.to_i16().unwrap(), truncate!(x.clone(), i16));
        assert_eq!(x.to_i32().unwrap(), truncate!(x.clone(), i32));
        assert_eq!(x.to_i64().unwrap(), truncate!(x.clone(), i64));
        assert_eq!(x.to_i128().unwrap(), truncate!(x.clone(), i128));
    }

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
            Sequence::ConcatSequence {
                boxed,
                length,
                left,
                ..
            } => {
                assert_eq!(*length, 6);
                assert_eq!(unsafe { &*left.get() }.cardinality_usize(), 3);
                // Test that boxed is None
                assert!(boxed.as_ref().clone().borrow().as_ref().is_none());
            }
            _ => panic!("This should never happen"),
        }
        let value = concat.get_usize(0);
        assert_eq!(value, 1);
        match &concat {
            crate::Sequence::ConcatSequence { boxed, .. } => {
                assert_eq!(
                    *boxed.as_ref().clone().borrow().as_ref().unwrap().as_ref(),
                    vec![1, 2, 3, 4, 5, 6]
                );
            }
            _ => panic!("This should never happen"),
        }
    }

    #[test]
    fn test_dafny_int() {
        assert_eq!(int!(0).to_usize(), Some(0));
        assert_eq!(int!(42).to_usize(), Some(42));
    }

    #[test]
    fn test_dafny_sequence_print() {
        let hello: DafnyString = seq![
            DafnyChar('H'),
            DafnyChar('e'),
            DafnyChar('l'),
            DafnyChar('l'),
            DafnyChar('o')
        ];
        assert_eq!(DafnyPrintWrapper(&hello).to_string(), "Hello");
        let hello: DafnyStringUTF16 = seq![
            DafnyCharUTF16(0x0048),
            DafnyCharUTF16(0x0065),
            DafnyCharUTF16(0x006c),
            DafnyCharUTF16(0x006c),
            DafnyCharUTF16(0x006f)
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
        let s = set! {55, 56, 57, 56, 58};
        let t = set! {59, 58, 57};
        assert_eq!(s.cardinality_usize(), 4);
        assert_eq!(s.cardinality(), int!(4));
        assert_eq!(s.contains(&55), true);
        assert_eq!(s.contains(&54), false);
        assert_eq!(s.merge(&set! {}), s);
        assert_eq!(set! {}.merge(&s), s);
        assert_eq!(s.merge(&t), set! {59, 58, 57, 56, 55});
        assert_eq!(s.intersect(&t), set! {57, 58});
        assert_eq!(s.subtract(&set! {}), s);
        assert_eq!(set! {}.subtract(&s), set! {});
        let smt = s.subtract(&t);
        assert_eq!(smt, set! {55, 56});
        assert_eq!(t.subtract(&s), set! {59});
        assert_eq!(s.disjoint(&set! {}), true);
        assert_eq!(set! {}.disjoint(&s), true);
        assert_eq!(s.disjoint(&t), false);
        assert_eq!(t.disjoint(&s), false);
        assert_eq!(smt.disjoint(&t), true);
        assert_eq!(t.disjoint(&smt), true);
        assert_eq!(s.elements(), s);
        assert_eq!(
            s.as_dafny_multiset(),
            Multiset::from_array(&vec!(55, 56, 57, 58))
        );
    }

    #[test]
    fn test_dafny_multisubset() {
        let s = multiset! {55, 56, 57, 58, 59};
        let t = multiset! {55, 56, 57, 58};
        assert!(t < s);
        assert!(t <= s);
        assert!(s > t);
        assert!(s >= t);
        assert!(s != t);
        assert!(t != s);

        assert!(!(t > s));
        assert!(!(t >= s));
        assert!(!(s < t));
        assert!(!(s <= t));
        assert!(!(s == t));
        assert!(!(t == s));

        let s = multiset! {55, 56, 57, 58, 58};
        let t = multiset! {55, 56, 57, 58};
        assert!(t < s);
        assert!(t <= s);
        assert!(s > t);
        assert!(s >= t);
        assert!(s != t);
        assert!(t != s);

        assert!(!(t > s));
        assert!(!(t >= s));
        assert!(!(s < t));
        assert!(!(s <= t));
        assert!(!(s == t));
        assert!(!(t == s));

        let s = multiset! {55, 56, 57, 58, 59};
        let t = multiset! {55, 56, 57, 58, 59};
        assert!(t <= s);
        assert!(s <= t);
        assert!(s >= t);
        assert!(t >= s);
        assert!(s == t);
        assert!(t == s);

        assert!(!(t < s));
        assert!(!(t > s));
        assert!(!(s > t));
        assert!(!(s < t));
        assert!(!(s != t));
        assert!(!(t != s));

        let s = multiset! {55, 56, 57, 58, 59};
        let t = multiset! {55, 56, 57, 58, 58};
        assert!(s != t);
        assert!(t != s);

        assert!(!(t < s));
        assert!(!(t <= s));
        assert!(!(t > s));
        assert!(!(t >= s));
        assert!(!(s < t));
        assert!(!(s <= t));
        assert!(!(s > t));
        assert!(!(s >= t));
        assert!(!(s == t));
        assert!(!(t == s));
    }

    #[test]
    fn test_dafny_multiset() {
        let s = multiset! {55, 56, 57, 56, 58};
        let t = multiset! {59, 58, 57, 56};
        assert_eq!(s.cardinality_usize(), 5);
        assert_eq!(s.cardinality(), int!(5));
        assert_eq!(s.contains(&55), true);
        assert_eq!(s.contains(&54), false);
        assert_eq!(s.get(&54), int!(0));
        assert_eq!(s.get(&55), int!(1));
        assert_eq!(s.get(&56), int!(2));
        assert_eq!(s.get(&57), int!(1));
        assert_eq!(s.merge(&multiset! {}), s);
        assert_eq!(multiset! {}.merge(&s), s);
        let merged = multiset! {59, 58, 58, 57, 57, 56, 56, 56, 55};
        assert_eq!(s.merge(&t), merged);
        assert_eq!(merged.cardinality_usize(), 9);
        assert_eq!(s.intersect(&t), multiset! {57, 58, 56});
        assert_eq!(s.subtract(&multiset! {}), s);
        assert_eq!(multiset! {}.subtract(&s), multiset! {});
        let smt = s.subtract(&t);
        assert_eq!(smt, multiset! {55, 56});
        let tms = t.subtract(&s);
        assert_eq!(tms, multiset! {59});
        assert_eq!(s.disjoint(&multiset! {}), true);
        assert_eq!(multiset! {}.disjoint(&s), true);
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
        let k_3 = set! {1, 3, 5};
        let v_3 = set! {2, 6, 10};
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
        assert_eq!(m_5.subtract(&set! {}), m_5);
        let m_4b = m_5.subtract(&set! {3});
        assert_eq!(m_4b.cardinality_usize(), 4);
        assert_eq!(m_4b.contains(&3), false)
    }

    #[test]
    fn test_dafny_array() {
        let a = array![1, 2, 3];
        assert_eq!(crate::array::length_usize(a), 3);
        assert_eq!(crate::array::length(a), int!(3));
        assert_eq!(array::get_usize(a, 0), 1);
        assert_eq!(array::get_usize(a, 1), 2);
        assert_eq!(array::get_usize(a, 2), 3);
        array::update_usize(a, 0, 4);
        array::update_usize(a, 1, 5);
        array::update_usize(a, 2, 6);
        assert_eq!(array::get_usize(a, 0), 4);
        assert_eq!(array::get_usize(a, 1), 5);
        assert_eq!(array::get_usize(a, 2), 6);
        deallocate(a);
    }

    #[test]
    fn test_dafny_array_init() {
        // test from_vec, and initialize
        let mut v = Vec::new();
        v.push(1);
        v.push(2);
        v.push(3);
        let a = array::from_vec(v);
        assert_eq!(array::length_usize(a), 3);
        assert_eq!(array::get_usize(a, 0), 1);
        let v2 = array::initialize_usize(3, Rc::new(|i| i + 1));
        assert_eq!(array::length_usize(v2), 3);
        assert_eq!(array::get_usize(v2, 0), 1);
        assert_eq!(array::get_usize(v2, 1), 2);
        assert_eq!(array::get_usize(v2, 2), 3);
        array::update_usize(v2, 1, 10);
        assert_eq!(array::get_usize(v2, 1), 10);


        let v3 = array::initialize(&int!(3), Rc::new(|i| i.clone() + int!(1)));
        assert_eq!(array::length_usize(v3), 3);
        assert_eq!(array::get_usize(v3, 0), int!(1));
        assert_eq!(array::get_usize(v3, 1), int!(2));
        assert_eq!(array::get_usize(v3, 2), int!(3));
        array::update(v3, &int!(1), int!(10));
        assert_eq!(array::get_usize(v3, 1), int!(10));

        deallocate(a);
        deallocate(v2);
        deallocate(v3);
    }

    #[test]
    fn test_array2() {
        let p = Array2::<DafnyInt>::placebos(&int!(3), &int!(4));
        for i in 0..3 {
            for j in 0..4 {
                modify!(p).data[i][j] = MaybeUninit::new(int!(i + j));
            }
        }
        let p = Array2::construct(p);
        assert_eq!(read!(p).length0_usize(), 3);
        assert_eq!(read!(p).length1_usize(), 4);
        let v = read!(p).to_vec();
        assert_eq!(v.len(), 3);
        assert_eq!(v, vec![
            vec![int!(0), int!(1), int!(2), int!(3)],
              vec![int!(1), int!(2), int!(3), int!(4)],
              vec![int!(2), int!(3), int!(4), int!(5)]]);

        deallocate(p);
        // Allocate an array whose first dimension is zero
        let p = Array2::<DafnyInt>::placebos(&int!(0), &int!(4));
        let p = Array2::construct(p);
        assert_eq!(read!(p).length0_usize(), 0);
        assert_eq!(read!(p).length1_usize(), 4);
        deallocate(p);
    }

    #[test]
    fn test_array3() {
        let a = Array3::<DafnyInt>::placebos(&int!(3), &int!(2), &int!(4));
        for i in 0..3 {
            for j in 0..2 {
                for k in 0..4 {
                    modify!(a).data[i][j][k] = MaybeUninit::new(DafnyInt::from(i * j + k));
                }
            }
        }
        let a = Array3::construct(a);
        assert_eq!(read!(a).length0(), int!(3));
        assert_eq!(read!(a).length1(), int!(2));
        assert_eq!(read!(a).length2(), int!(4));
        let v = read!(a).to_vec();
        assert_eq!(v.len(), 3);
        for i in 0..3 {
            for j in 0..2 {
                for k in 0..4 {
                    assert_eq!(read!(a).data[i][j][k], DafnyInt::from(i * j + k));
                    assert_eq!(v[i][j][k], DafnyInt::from(i * j + k));
                }
            }
        }
        deallocate(a);
        // Even if the first two dimensions are zero, the third dimension should not be zero
        let a = Array3::<DafnyInt>::placebos(&int!(0), &int!(0), &int!(4));
        let a = Array3::construct(a);
        assert_eq!(read!(a).length0(), int!(0));
        assert_eq!(read!(a).length1(), int!(0));
        assert_eq!(read!(a).length2(), int!(4));
        deallocate(a);
    }

    struct ClassWrapper<T> {
        /*var*/ t: Field<T>,
        /*var*/ x: Field<crate::DafnyInt>,
        /*const*/ next: Ptr<ClassWrapper<T>>,
        /*const*/ constant: crate::DafnyInt,
    }
    impl<T: Clone> ClassWrapper<T> {
        fn constant_plus_x(&self) -> crate::DafnyInt {
            self.constant.clone() + read_field!(self.x)
        }
        fn increment_x(&mut self) {
            modify_field!(self.x, read_field!(self.x) + int!(1));
        }
    }

    impl<T: Clone + Display> ClassWrapper<T> {
        fn constructor(t: T) -> Ptr<ClassWrapper<T>> {
            let this = crate::allocate::<ClassWrapper<T>>();
            update_field_mut_nodrop!(this, t, t);
            update_field_nodrop!(this, next, this);
            // If x is assigned twice, we need to keep track of whether it's assigned
            // like in methods.
            let mut x_assigned = false;
            update_field_mut_uninit!(this, x, x_assigned, int!(2));
            update_field_mut_uninit!(this, x, x_assigned, int!(1));
            // If we can prove that x is assigned, we can even write this
            modify_field!(read!(this).x,int!(0));
            update_field_nodrop!(this, constant, int!(42));
            update_field_mut_if_uninit!(this, x, x_assigned, int!(0));
            assert_eq!(x_assigned, true);
            let mut next_assigned = true;
            update_field_if_uninit!(this, next, next_assigned, this);
            assert_eq!(next_assigned, true);
            this
        }

        fn constructor_object(t: T) -> Object<ClassWrapper<T>> {
            let mut this = crate::allocate_object::<ClassWrapper<T>>();
            update_field_mut_nodrop_object!(this, t, t);
            update_field_nodrop_object!(this, next, Ptr::from_raw_nonnull(this.as_mut()));
            // If x is assigned twice, we need to keep track of whether it's assigned
            // like in methods.
            let mut x_assigned = false;
            update_field_mut_uninit_object!(this, x, x_assigned, int!(2));
            update_field_mut_uninit_object!(this, x, x_assigned, int!(1));
            // If we can prove that x is assigned, we can even write this
            modify_field!(rd!(this).x,int!(0));
            update_field_nodrop_object!(this, constant, int!(42));
            update_field_mut_if_uninit_object!(this, x, x_assigned, int!(0));
            assert_eq!(x_assigned, true);
            let mut next_assigned = true;
            update_field_if_uninit_object!(this, next, next_assigned, Ptr::from_raw_nonnull(this.as_mut()));
            assert_eq!(next_assigned, true);
            this
        }
    }

    impl <T: DafnyType> Upcast<dyn Any> for ClassWrapper<T> {
        UpcastFn!(dyn Any);
    }
    impl <T: DafnyType> UpcastObject<dyn Any> for ClassWrapper<T> {
        UpcastObjectFn!(dyn Any);
    }

    #[test]
    #[allow(unused_unsafe)]
    fn test_class_wrapper() {
        let c: Ptr<ClassWrapper<i32>> = ClassWrapper::constructor(53);
        assert_eq!(read!(c).constant, int!(42));
        assert_eq!(read_field!(read!(c).t), 53);
        assert_eq!(read_field!(read!(c).x), int!(0));
        assert_eq!(read_field!(read!(read!(c).next).t), 53);
        assert_eq!(read!(c).constant_plus_x(), int!(42));
        modify!(c).increment_x();
        assert_eq!(read!(c).constant_plus_x(), int!(43));
        modify_field!(read!(c).x,int!(40));
        assert_eq!(read!(c).constant_plus_x(), int!(82));
        modify_field!(read!(c).t,54);
        assert_eq!(read_field!(read!(c).t), 54);
        let x_copy = read_field!(read!(c).x);
        assert_eq!(Rc::strong_count(&x_copy.data), 2);
        deallocate(c);
        assert_eq!(Rc::strong_count(&x_copy.data), 1);
    }


    #[test]
    #[allow(unused_unsafe)]
    fn test_class_wrapper_object() {
        let c: Object<ClassWrapper<i32>> = ClassWrapper::constructor_object(53);
        assert_eq!(rd!(c).constant, int!(42));
        assert_eq!(read_field!(rd!(c).t), 53);
        assert_eq!(read_field!(rd!(c).x), int!(0));
        assert_eq!(read_field!(rd!(rd!(c).next).t), 53);
        assert_eq!(rd!(c).constant_plus_x(), int!(42));
        md!(c).increment_x();
        assert_eq!(rd!(c).constant_plus_x(), int!(43));
        if true {
          modify_field!(rd!(c).x,int!(40))
        }
        assert_eq!(rd!(c).constant_plus_x(), int!(82));
        modify_field!(rd!(c).t,54);
        assert_eq!(read_field!(rd!(c).t), 54);
    }

    // Requires test1 || test2
    // We will not do that as it enables the compiler to assume that t contains a valid Rc<i32> when it does not.
    // Prefer MaybePlacebo
    fn assign_lazy_in_method(test1: bool, test2: bool) -> Rc<i32> {
        let mut t = MaybePlacebo::<Rc<i32>>::new();
        if test1 {
            t = MaybePlacebo::from(Rc::new(5 as i32));
        }
        if test2 {
            t = MaybePlacebo::from(Rc::new(
                7 as i32 + if test1 { *MaybePlacebo::read(&t) } else { 0 },
            ));
        }
        println!("{}", MaybePlacebo::read(&t));
        MaybePlacebo::read(&t)
    }

    #[test]
    fn assign_lazy_in_method_test() {
        let mut t = assign_lazy_in_method(true, false);
        assert_eq!(*t, 5);
        t = assign_lazy_in_method(false, true);
        assert_eq!(*t, 7);
        t = assign_lazy_in_method(true, true);
        assert_eq!(*t, 12);
    }

    fn override_placebo<T: Clone>(o: T, do_override: bool) {
        let mut _x: MaybePlacebo<T> = MaybePlacebo::<T>::new();
        if do_override {
            _x = MaybePlacebo::from(o.clone());
        }
    }

    #[test]
    fn test_placebo() {
        override_placebo::<Rc<BigInt>>(Rc::new(BigInt::from(1)), false);
        override_placebo::<Rc<BigInt>>(Rc::new(BigInt::from(1)), true);
        override_placebo::<DafnyInt>(int!(1), false);
        override_placebo::<DafnyInt>(int!(1), true);
        let _x: MaybePlacebo<Ptr<ClassWrapper<DafnyInt>>> =
            MaybePlacebo::<Ptr<ClassWrapper<DafnyInt>>>::new();
        //let mut f: Rc<dyn Fn(Class) -> Class> = <Rc<dyn Fn(Class) -> Class> as Placebo>::new();
    }

    #[test]
    fn test_maybe_placebos_from() {
        let x = (1, 2, 3, 4);
        let (a, b, c, d) = maybe_placebos_from!(x, 0, 1, 2, 3);
        assert_eq!(a.read(), 1);
        assert_eq!(b.read(), 2);
        assert_eq!(c.read(), 3);
        assert_eq!(d.read(), 4);
    }

    #[test]
    fn test_coercion_immutable() {
        let o = ClassWrapper::<i32>::constructor(1);
        let a: Ptr<dyn Any> = Upcast::<dyn Any>::upcast(read!(o));
        assert_eq!(cast!(a, ClassWrapper<i32>), o);
        let seq_o = seq![o];
        let seq_a = Sequence::<Ptr<ClassWrapper<i32>>>::coerce(upcast::<ClassWrapper<i32>, dyn Any>())(seq_o);
        assert_eq!(cast!(seq_a.get_usize(0), ClassWrapper<i32>), o);
        let set_o = set! {o};
        let set_a = Set::<Ptr<ClassWrapper<i32>>>::coerce(upcast::<ClassWrapper<i32>, dyn Any>())(set_o);
        assert_eq!(cast!(set_a.peek(), ClassWrapper<i32>), o);
        let multiset_o = multiset! {o, o};
        let multiset_a = Multiset::<Ptr<ClassWrapper<i32>>>::coerce(upcast::<ClassWrapper<i32>, dyn Any>())(multiset_o);
        assert_eq!(cast!(multiset_a.peek(), ClassWrapper<i32>), o);
        let map_o = map![1 => o, 2 => o];
        let map_a = Map::<i32, Ptr<ClassWrapper<i32>>>::coerce(upcast::<ClassWrapper<i32>, dyn Any>())(map_o);
        assert_eq!(cast!(map_a.get(&1), ClassWrapper<i32>), o);
        deallocate(o);
    }

    #[test]
    fn test_defaults() {
        let set_i32 = <Set<i32> as Default>::default();
        let seq_i32 = <Sequence<i32> as Default>::default();
        let map_i32 = <Map<i32, i32> as Default>::default();
        let multiset_i32 = <Multiset<i32> as Default>::default();
        assert_eq!(set_i32.cardinality_usize(), 0);
        assert_eq!(seq_i32.cardinality_usize(), 0);
        assert_eq!(map_i32.cardinality_usize(), 0);
        assert_eq!(multiset_i32.cardinality_usize(), 0);
    }

    #[test]
    fn test_nontrivial_defaults() {
        let set_i32 = <Set<i32> as NontrivialDefault>::nontrivial_default();
        let seq_i32 = <Sequence<i32> as NontrivialDefault>::nontrivial_default();
        let map_i32 = <Map<i32, i32> as NontrivialDefault>::nontrivial_default();
        let multiset_i32 = <Multiset<i32> as NontrivialDefault>::nontrivial_default();
        assert_eq!(set_i32.cardinality_usize(), 0);
        assert_eq!(seq_i32.cardinality_usize(), 0);
        assert_eq!(map_i32.cardinality_usize(), 0);
        assert_eq!(multiset_i32.cardinality_usize(), 0);
        let ptr_i32 = <Ptr<i32> as NontrivialDefault>::nontrivial_default();
        assert_eq!(ptr_i32, Ptr::<i32>::null());
    }

    #[test]
    fn test_function_wrappers() {
        let f: Rc<dyn Fn(i32) -> i32> = Rc::new(|i: i32| i + 1);
        let g = f.clone();
        let _h = seq![g];
    }

    #[test]
    fn test_forall_exists() {
        assert!(integer_range(int!(0), int!(10))
            .all(Rc::new(|i: DafnyInt| i.clone() < int!(10)).as_ref()));
        assert!(!integer_range(int!(0), int!(11))
            .all(Rc::new(|i: DafnyInt| i.clone() < int!(10)).as_ref()));
        assert!(!integer_range(int!(0), int!(10))
            .any(Rc::new(|i: DafnyInt| i.clone() >= int!(10)).as_ref()));
        assert!(integer_range(int!(0), int!(11))
            .any(Rc::new(|i: DafnyInt| i.clone() >= int!(10)).as_ref()));

        assert!(integer_range(int!(0), int!(10)).all(
            Rc::new(|i: DafnyInt| !(i.clone() % int!(4) == int!(0))
                || i.clone() < int!(10) && i.clone() % int!(2) == int!(0))
            .as_ref()
        ));
        assert!(integer_range(int!(0), int!(11)).all(
            Rc::new(|i: DafnyInt| !(i.clone() % int!(4) == int!(0))
                || i.clone() < int!(10) && i.clone() % int!(2) == int!(0))
            .as_ref()
        ));
        assert!(!integer_range(int!(0), int!(10)).any(
            Rc::new(|i: DafnyInt| i.clone() % int!(4) == int!(0)
                && i.clone() >= int!(10)
                && i.clone() % int!(2) == int!(0))
            .as_ref()
        ));
        assert!(!integer_range(int!(0), int!(11)).any(
            Rc::new(|i: DafnyInt| i.clone() % int!(4) == int!(0)
                && i.clone() >= int!(10)
                && i.clone() % int!(2) == int!(0))
            .as_ref()
        ));

        assert!(exact_range(10).all(Rc::new(|i: i32| i == 10).as_ref()));
        assert!(exact_range(10).any(Rc::new(|i: i32| i == 10).as_ref()));
        assert!(!exact_range(10).all(Rc::new(|i: i32| i != 10).as_ref()));
        assert!(!exact_range(10).any(Rc::new(|i: i32| i != 10).as_ref()));

        assert!(seq![1, 3, 5, 7]
            .iter()
            .all(Rc::new(|i: u32| i % 2 == 1).as_ref()));
        assert!(!seq![1, 3, 5, 7]
            .iter()
            .any(Rc::new(|i: u32| i % 2 == 0).as_ref()));
        assert!(!seq![1, 3, 5, 7, 8]
            .iter()
            .all(Rc::new(|i: u32| i % 2 == 1).as_ref()));
        assert!(seq![1, 3, 5, 7, 8]
            .iter()
            .any(Rc::new(|i: u32| i % 2 == 0).as_ref()));

        assert!(set! {1, 3, 5, 7}
            .iter()
            .cloned()
            .all(Rc::new(|i: u32| i % 2 == 1).as_ref()));
        assert!(!set! {1, 3, 5, 7}
            .iter()
            .cloned()
            .any(Rc::new(|i: u32| i % 2 == 0).as_ref()));
        assert!(!set! {1, 3, 5, 7, 8}
            .iter()
            .cloned()
            .all(Rc::new(|i: u32| i % 2 == 1).as_ref()));
        assert!(set! {1, 3, 5, 7, 8}
            .iter()
            .cloned()
            .any(Rc::new(|i: u32| i % 2 == 0).as_ref()));

        for i in set! {1, 3, 5, 7}.iter() {
            println!("{}", i);
        }

        assert!(multiset! {1, 1, 5, 7}
            .iter()
            .all(Rc::new(|i: u32| i % 2 == 1).as_ref()));
        assert!(!multiset! {1, 1, 5, 7}
            .iter()
            .any(Rc::new(|i: u32| i % 2 == 0).as_ref()));
        assert!(!multiset! {1, 1, 5, 7, 8}
            .iter()
            .all(Rc::new(|i: u32| i % 2 == 1).as_ref()));
        assert!(multiset! {1, 1, 5, 7, 8}
            .iter()
            .any(Rc::new(|i: u32| i % 2 == 0).as_ref()));
        let count = Rc::new(RefCell::new(0));
        let count_inner = count.clone();
        multiset!{1, 1, 5, 7, 8}
            .iter().for_each(move |_i: u32| {
                let c: i32 = *count_inner.as_ref().borrow();
                *count_inner.borrow_mut() = c + 1;
             });
        assert_eq!(*count.as_ref().borrow(), 5);

        let m = map![1 => 4, 3 => 6, 5 => 8];
        let m2 = m.clone();
        let m3 = m.clone();
        assert!(m
            .clone()
            .iter()
            .all(Rc::new(move |i: u32| i + 3 == m2.get(&i)).as_ref()));
        assert!(!m
            .iter()
            .any(Rc::new(move |i: u32| i + 2 == m3.get(&i)).as_ref()));
        let m = map![1 => 4, 3 => 7, 5 => 7];
        let m2 = m.clone();
        let m3 = m.clone();
        assert!(!m
            .clone()
            .iter()
            .all(Rc::new(move |i: u32| i + 3 == m2.get(&i)).as_ref()));
        assert!(m
            .iter()
            .any(Rc::new(move |i: u32| i + 2 == m3.get(&i)).as_ref()));
    }

    #[test]
    fn test_for_loops() {
        let mut sum: i32 = 0;
        for i in integer_range(1, 11) {
            sum += i;
        }
        assert_eq!(sum, 55);

        let mut sum: i32 = 0;
        for i in integer_range_down(11, 1) {
            sum += i;
        }
        assert_eq!(sum, 55);

        let mut sum: i32 = 0;
        for i in integer_range_unbounded(1) {
            sum += i;
            if i == 10 {
                break;
            }
        }
        assert_eq!(sum, 55);

        let mut sum: i32 = 0;
        for i in integer_range_down_unbounded(11) {
            sum += i;
            if i == 1 {
                break;
            }
        }
        assert_eq!(sum, 55);
    }

    trait SuperTrait: Upcast<dyn Any> + UpcastObject<dyn Any> {
    }

    trait NodeRcMutTrait: SuperTrait + Upcast<dyn SuperTrait> + UpcastObject<dyn SuperTrait>{
    }

    pub struct NodeRcMut {
        val: DafnyInt,
        next: Object<NodeRcMut>,
    }
    impl NodeRcMut {
        fn _ctor(this: Object<NodeRcMut>, val: DafnyInt) {
            let mut val_assign = false;
            let mut next_assign = false;
            update_field_uninit_object!(this.clone(), val, val_assign, val);
            update_field_if_uninit_object!(this.clone(), next, next_assign, Object(None));
        }
    }
    impl SuperTrait for NodeRcMut {}
    impl UpcastObject<dyn Any> for NodeRcMut {
        UpcastObjectFn!(dyn Any);
    }
    impl Upcast<dyn Any> for NodeRcMut {
        UpcastFn!(dyn Any);
    }
    impl UpcastObject<dyn NodeRcMutTrait> for NodeRcMut {
        UpcastObjectFn!(dyn NodeRcMutTrait);
    }
    impl Upcast<dyn NodeRcMutTrait> for NodeRcMut {
        UpcastFn!(dyn NodeRcMutTrait);
    }
    impl UpcastObject<dyn SuperTrait> for NodeRcMut {
        UpcastObjectFn!(dyn SuperTrait);
    }
    impl Upcast<dyn SuperTrait> for NodeRcMut {
        UpcastFn!(dyn SuperTrait);
    }
    impl NodeRcMutTrait for NodeRcMut {}

    #[test]
    fn test_object() {
        let mut x: Object<NodeRcMut> = allocate_object::<NodeRcMut>();
        NodeRcMut::_ctor(x.clone(), int!(42));
        assert_eq!(refcount!(x), 1);
        assert_eq!(x.as_ref().val, int!(42));
        x.as_mut().next = x.clone();
        assert_eq!(refcount!(x), 2);
        assert_eq!(x.as_ref().next.as_ref().val, int!(42));
        md!(rd!(x).next).next = Object(None);
        assert_eq!(refcount!(x), 1);
        let y: Object<dyn Any> = upcast_object::<_, _>()(x.clone());
        assert_eq!(refcount!(x), 2);
        let z: Object<dyn NodeRcMutTrait> = upcast_object::<_, _>()(x.clone());
        assert_eq!(refcount!(x), 3);
        let a2: Object<NodeRcMut> = cast_object!(y.clone(), NodeRcMut);
        assert_eq!(refcount!(x), 4);
        assert_eq!(rd!(a2).val, int!(42));
        let a3: Object<NodeRcMut> = cast_object!(z.clone(), NodeRcMut);
        assert_eq!(refcount!(x), 5);
        assert_eq!(rd!(a3).val, int!(42));

        // Other way to create objects
        let direct: Object<NodeRcMut> = Object::<NodeRcMut>::new(NodeRcMut {val: int!(1), next: Object::<NodeRcMut>::null()});
        assert_eq!(rd!(direct).val, int!(1));
        let tail: Object<NodeRcMut> = Object::<NodeRcMut>::null();
        assert_eq!(tail, rd!(direct).next);
        assert!(tail.is_null());
        assert!(!direct.is_null());
        
        let a: Object<[i32]> = rcmut::array_object_from_rc(Rc::new([42, 43, 44]));
        assert_eq!(rd!(a).len(), 3);
        assert_eq!(rd!(a)[0], 42);
        assert_eq!(rd!(a)[1], 43);
        assert_eq!(rd!(a)[2], 44);
        let b: Object<[i32]> = a.clone();
        md!(b)[0] = 45;
        assert_eq!(rd!(a)[0], 45);

        let previous_count = refcount!(x);
        {
            let z = Object::<NodeRcMut>::from_ref(x.as_ref());
            assert_eq!(refcount!(z), previous_count + 1);
            assert_eq!(refcount!(x), previous_count + 1);
        }
        assert_eq!(refcount!(x), previous_count);

        let objects: Set<Object<dyn ::std::any::Any>> = crate::set!{y.clone(), cast_any_object!(x.clone())};
        assert_eq!(objects.cardinality_usize(), 1);
        test_dafny_type(a.clone());
    }

    pub struct NodeRawMut {
        val: DafnyInt,
        next: Ptr<NodeRawMut>,
    }
    impl NodeRawMut {
        fn _ctor(this: Ptr<NodeRawMut>, val: DafnyInt) {
            let mut val_assign = false;
            update_field_uninit!(this, val, val_assign, val);
        }
    }
    impl NodeRcMutTrait for NodeRawMut {}
    UpcastDefObject!(NodeRawMut, dyn NodeRcMutTrait, dyn SuperTrait, dyn Any);
    UpcastDef!(NodeRawMut, dyn NodeRcMutTrait, dyn SuperTrait, dyn Any);

    impl SuperTrait for NodeRawMut {}

    #[test]
    fn test_rawmut() {
        let x: Ptr<NodeRawMut> = allocate::<NodeRawMut>();
        NodeRawMut::_ctor(x.clone(), int!(42));
        assert_eq!(read!(x.clone()).val, int!(42));
        modify!(x.clone()).next = x.clone();
        assert_eq!(read!(read!(x.clone()).next.clone()).val, int!(42));
        modify!(read!(x.clone()).next.clone()).next = Ptr::null();
        let y: Ptr<dyn Any> = upcast::<_, _>()(x);
        assert!(y.is_instance_of::<NodeRawMut>());
        assert!(!y.is_instance_of::<NodeRcMut>());
        let z: Ptr<dyn NodeRcMutTrait> = upcast::<_, _>()(x);
        let _a2: Ptr<NodeRawMut> = cast!(y, NodeRawMut);
        let _a3: Ptr<NodeRawMut> = cast!(z, NodeRawMut);
        deallocate(x);

        let a = array::from_native(Box::new([42, 43, 44]));
        assert_eq!(read!(a.clone()).len(), 3);
        assert_eq!(read!(a.clone())[0], 42);
        assert_eq!(read!(a.clone())[1], 43);
        assert_eq!(read!(a.clone())[2], 44);
        let b = a.clone();
        modify!(b.clone())[0] = 45;
        assert_eq!(read!(a.clone())[0], 45);

        deallocate(a);
    }

    // Conversion of any usize-compatible value into usize
    #[test]
    fn test_usize() {
        let a: u128 = 1;
        let b: i8 = 1;
        let u: usize = 1;
        assert_eq!(DafnyUsize::into_usize(int!(a)), u);
        assert_eq!(DafnyUsize::into_usize(a), u);
        assert_eq!(DafnyUsize::into_usize(b), u);
        assert_eq!(DafnyUsize::into_usize(int!(b)), u);
    }

    // Tests that we can compose Dafny types, like a sequence of maps
    fn _test<X: DafnyTypeEq, Y: DafnyType>(_input: Sequence<Map<X, Y>>) {
    }
    // Tests that the input type is a DafnyType
    fn test_dafny_type<X: DafnyType>(_input: X) {
    }

    #[derive(Clone)]
    pub struct InternalOpaqueError {
        pub message: String,
    }

    crate::UpcastDefObject!(InternalOpaqueError, dyn Any);

    #[test]
    fn test_native_string_upcast() {
        let s = InternalOpaqueError { message: "Hello, World!".to_string() };
        let o: Object<InternalOpaqueError> = Object::new(s);
        let n: Object<dyn ::std::any::Any> = upcast_object::<InternalOpaqueError, dyn ::std::any::Any>()(o);
        let x = cast_object!(n, InternalOpaqueError);
        let s2 = crate::dafny_runtime_conversions::object::dafny_class_to_struct(x);
        assert_eq!(s2.message, "Hello, World!");
    }

    #[test]
    fn test_native_string_upcast_raw() {
        let message = "Hello, World!".to_string();
        let object = Object::new(message.clone());
        let object_any: Object<dyn Any> = UpcastObject::<dyn Any>::upcast(object.as_ref());
        let resulting_message = format!("{:?}", object_any);
        assert_eq!(resulting_message, message);
    }

    // Every general trait must declare how to clone a Box<dyn .> of itself
    trait GeneralTraitSuper<T> {
        fn _clone(&self) -> Box<dyn GeneralTraitSuper<T>>;
        fn _is_GeneralTrait(&self) -> bool;
        fn _as_GeneralTrait(&self) -> Box<dyn GeneralTrait>;
        fn _is_Datatype(&self) -> bool;
        fn _as_Datatype(&self) -> ADatatype;
    }
    impl <T> Clone for Box<dyn GeneralTraitSuper<T>> {
        fn clone(&self) -> Self {
            GeneralTraitSuper::_clone(self.as_ref())
        }
    }
    impl <T> DafnyPrint for Box<dyn GeneralTraitSuper<T>> {
        fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
            write!(f, "GeneralTraitSuper")
        }
    }
    // Traits extending other traits also implement a direct way to upcast their Box<dyn .> of themselves
    trait GeneralTrait: GeneralTraitSuper<i32> + UpcastBox<dyn GeneralTraitSuper<i32>> {
        fn _clone(&self) -> Box<dyn GeneralTrait>;
    }
    impl UpcastBox<dyn GeneralTraitSuper<i32>> for Box<dyn GeneralTrait> {
        fn upcast(&self) -> ::std::boxed::Box<dyn crate::tests::tests::GeneralTraitSuper<i32>> {
            crate::tests::tests::GeneralTraitSuper::<i32>::_clone(self.as_ref())
        }
    }
    impl Clone for Box<dyn GeneralTrait> {
        fn clone(&self) -> Self {
            GeneralTrait::_clone(self.as_ref())
        }
    }
    impl DafnyPrint for Box<dyn GeneralTrait> {
        fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
            write!(f, "GeneralTrait")
        }
    }

    #[derive(Clone, PartialEq, Debug)]
    struct ADatatype{i: i32}
    impl GeneralTrait for ADatatype {
        fn _clone(&self) -> Box<dyn GeneralTrait> {
            Box::new(self.clone()) as Box<dyn GeneralTrait>
        }
    }
    impl GeneralTraitSuper<i32> for ADatatype {
        fn _clone(&self) -> Box<dyn GeneralTraitSuper<i32>> {
            Box::new(self.clone())
        }
        
        fn _is_GeneralTrait(&self) -> bool {
            true
        }
        
        fn _as_GeneralTrait(&self) -> Box<dyn GeneralTrait> {
            GeneralTrait::_clone(self)
        }
        
        fn _is_Datatype(&self) -> bool {
            true
        }
        
        fn _as_Datatype(&self) -> ADatatype {
            self.clone()
        }
    }
    impl UpcastBox<dyn GeneralTrait> for ADatatype {
        fn upcast(&self) -> ::std::boxed::Box<dyn GeneralTrait> {
            GeneralTrait::_clone(self)
        }
    }
    impl UpcastBox<dyn GeneralTraitSuper<i32>> for ADatatype {
        fn upcast(&self) -> ::std::boxed::Box<dyn GeneralTraitSuper<i32>> {
            GeneralTraitSuper::<i32>::_clone(self)
        }
    }
    #[test]
    fn test_general_traits() {
        let x = ADatatype{i: 3};
        let gt = upcast_box::<ADatatype, dyn GeneralTrait>()(x.clone());
        let gts = upcast_box::<ADatatype, dyn GeneralTraitSuper<i32>>()(x.clone());
        let gtgts = upcast_box_box::<dyn GeneralTrait, dyn GeneralTraitSuper<i32>>()(gt.clone());
        assert!(gt._is_Datatype());
        assert!(gts._is_Datatype());
        assert!(gtgts._is_Datatype());
        assert!(gts._is_GeneralTrait());
        assert!(gtgts._is_GeneralTrait());
        assert_eq!(gt._as_Datatype(), x);
        assert_eq!(gts._as_Datatype(), x);
        assert_eq!(gtgts._as_Datatype(), x);
        let gtsgt = gts._as_GeneralTrait();
        let gtgtsgt = gtgts._as_GeneralTrait();
        assert!(gtsgt._is_Datatype());
        assert!(gtgtsgt._is_Datatype());
        assert_eq!(gtsgt._as_Datatype(), x);
        assert_eq!(gtsgt._as_Datatype(), x);
    }
    /*impl GeneralTrait for Rc<ADatatype> {
        fn _clone(&self) -> Box<dyn GeneralTrait> {
            Box::new(self.as_ref().clone())
        }
    }*/


}
