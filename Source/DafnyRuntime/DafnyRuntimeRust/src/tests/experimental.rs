
// Test module
#[cfg(test)]
mod experimental {
    use std::{any::Any, borrow::Borrow, cell::RefCell, fmt::Formatter, mem::{transmute, MaybeUninit}, rc::{Rc, Weak}};
    use as_any::Downcast;
    use num::{BigInt, One, Zero};
    use once_cell::unsync::Lazy;

    use crate::{allocate, deallocate, is_instance_of, AsAny, DafnyPrint, LazyFieldWrapper, Sequence};

    // A datatype encoded in Rust
    // T can either be an allocated type *const X or a reference type Rc<X>
    // Either way, T must extend Clone and DafnyPrint
    // T must be equatable
    #[derive(PartialEq)]
    enum Tree<T: Clone>
      where T: DafnyPrint
    {
        Leaf,
        Node{left: Rc<Tree<T>>, value: T, right: Rc<Tree<T>>}
    }
    impl <T: Clone> Tree<T>
      where T: DafnyPrint
    {
        fn _isLeaf(&self) -> bool {
            match self {
                Tree::Leaf => true,
                Tree::Node{..} => false
            }
        }
        fn _isNode(&self) -> bool {
            match self {
                Tree::Leaf => false,
                Tree::Node{..} => true
            }
        }
        fn value(&self) -> T {
            match self {
                Tree::Leaf => panic!("Leaf has not value"),
                Tree::Node{value, ..} => value.clone()
            }
        }
        fn left(&self) -> Rc<Tree<T>> {
            match self {
                Tree::Leaf => panic!("Leaf has not left"),
                Tree::Node{left, ..} => Rc::clone(left)
            }
        }
        fn right(&self) -> Rc<Tree<T>> {
            match self {
                Tree::Leaf => panic!("Leaf has not right"),
                Tree::Node{right, ..} => Rc::clone(right)
            }
        }
    }

    trait HasFirst: AsAny
    {
        // Encoding of "var first"
        fn _get_first(&self) -> Rc<String>;
        fn _set_first(&self, new_first: &Rc<String>);
        fn replace_first(&self, new_first: &Rc<String>) -> Rc<String> {
            let old_first = self._get_first();
            self._set_first(new_first);
            old_first
        }
    }
    struct NoStruct {}

    struct MyStructDatatype { // For a class
        first: Rc<String>,
        last: Rc<String>,
    }
    impl DafnyPrint for MyStructDatatype {
        fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
            write!(f, "MyStruct({}, {})",
              self.first,
              self.last)
        }
    }

    //#[derive(PartialEq)]
    struct _MyStructUninit {
        first: MaybeUninit<Rc<String>>,
        last: MaybeUninit<Rc<String>>,
    }
    struct MyStruct { // For a class
        first: Rc<String>,
        last: Rc<String>,
    }
    impl DafnyPrint for MyStruct {
        fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
            write!(f, "MyStruct({}, {})",
              unsafe{std::ptr::read(self.first.as_ptr())},
              unsafe{std::ptr::read(self.last.as_ptr())})
        }
    }
    
    impl MyStruct {
        fn constructor(first: &Rc<String>, last: &Rc<String>) -> *const MyStruct {
            let this =
              allocate(Box::new(_MyStructUninit {
                first: MaybeUninit::uninit(),
                last: MaybeUninit::uninit()}));
            // Two ways to write uninitialized values
            unsafe {(*(this  as *mut _MyStructUninit)).first.as_mut_ptr().write(Rc::clone(first))};
            unsafe {(*(this as *mut _MyStructUninit)).last = transmute(Rc::clone(last))};
            // new;
            this as *const MyStruct
        }
    }
    impl AsAny for MyStruct {
        fn as_any(&self) -> &dyn Any {
            self
        }
    }
    impl HasFirst for MyStruct {
        // Use unsafe and pointer casting if necessary
        fn _get_first(&self) -> Rc<String> {
            self.first.clone()
        }
        fn _set_first(&self, new_first: &Rc<String>) {
            unsafe {(*(self as *const MyStruct as *mut MyStruct)).first
              = transmute(Rc::clone(new_first))};
        }
    }
    impl MyStruct {
        fn _set_first_mut(&mut self, new_first: &Rc<String>) {
            unsafe {(*(self as *mut MyStruct)).first
              = transmute(Rc::clone(new_first))};
        }
        fn _set_first_static(this: *const MyStruct, new_first: &Rc<String>) {
            unsafe {transmute::<*const MyStruct, &mut MyStruct>(this)}
              ._set_first_mut(new_first)
        }
    }
    #[test]
    fn test_has_first() {
        let doe = Rc::new("Doe".to_string());
        let mut theobject: *const dyn HasFirst = MyStruct::constructor(
            &Rc::new("John".to_string()),
            &doe);
        let original_first = unsafe { (*theobject)._get_first() };
        assert_eq!(original_first, Rc::new("John".to_string()), "Initial value should be 'John'");
    
        let new_first = Rc::new("Jane".to_string());
        unsafe { (*theobject)._set_first(&new_first) };

        // Test if the pointer theobject points to a struct HasFirst, and then if it's a pointer to a Tree
        // In the first case, do nothing, in the second case, panic
        let is_no_struct = unsafe { &*theobject }.as_any().downcast_ref::<NoStruct>().is_some();
        assert!(!is_no_struct, "The value should not be a NoStruct");
        assert!(!is_instance_of::<dyn HasFirst, NoStruct>(theobject)); // Why is this working??!
        //assert!(!DafnyUpdowncast::<NoStruct>::is_instance_of(&theobject)); // TODO: Clone instead
        
        let is_has_first = unsafe { &*theobject }.as_any().downcast_ref::<MyStruct>().is_some();
        assert!(is_has_first, "The value should be a HasFirst");
        assert!(is_instance_of::<dyn HasFirst, MyStruct>(theobject));
        //assert!(DafnyUpdowncast::<MyStruct>::is_instance_of(&theobject));

        let replaced_value = unsafe { (*theobject).replace_first(&Rc::new("Jack".to_string())) };
        assert_eq!(replaced_value, Rc::new("Jane".to_string()), "Replaced value should be 'Jane'");
        let old_count = Rc::strong_count(&doe);
        //unsafe { drop(Box::from_raw(theobject as *mut dyn HasFirst)) };
        deallocate(theobject);
        assert_eq!(Rc::strong_count(&doe), old_count - 1, "Doe should be deallocated");
    }

    // Function to test allocation and aliasing
    #[test]
    fn test_full_reuse() {
        test_reuse(true);
        test_reuse(false);
    }

    // Function to test allocation and aliasing
    fn test_reuse(reuse: bool) {
        // Create a struct for "John" "Doe" and wrap it with the function allocate()
        let theobject: *const MyStruct = MyStruct::constructor(
            &Rc::new("John".to_string()),
            &Rc::new("Doe".to_string()));

        // Assign the result to a *const on a raw pointer named "theobject"
        let mut possiblealias: *const MyStruct = theobject;

        // If 'reuse' is true, assign the same pointer to another named "possiblealias"
        // Otherwise, use the method allocate() on a new structure
        if !reuse {
            possiblealias = MyStruct::constructor(
                &Rc::new("John".to_string()),
                &Rc::new("Doe".to_string()));
        }

        // Modify the field "first" to "Jane" in theobject (unsafe code is fine)
        unsafe {(*(theobject as *mut MyStruct)).first = transmute(Rc::new("Jane".to_string()))};
        // Using std::ptr::write:
        //unsafe {std::ptr::write(&mut (*theobject).first, "Jane".to_string())};}h

        // If !reuse and theobject.first == possiblealias.first, panic (unreachable code)
        if !reuse && unsafe{std::ptr::read(&(*theobject).first.as_ptr())}
                  == unsafe{std::ptr::read(&(*possiblealias).first.as_ptr())} {
            panic!("Unreachable code reached!");
        }

        // Deallocate possiblealias
        deallocate(possiblealias);

        // If !reuse, deallocate theobject
        if !reuse {
            deallocate(theobject);
        }
    }

    #[test]
    fn test_tree() {
        let tree: Tree<Rc<MyStructDatatype>> = Tree::Node{
            left: Rc::new(Tree::Leaf),
            value: Rc::new(MyStructDatatype{
                first: Rc::new("Jane".to_string()),
                last: Rc::new("Doe".to_string())}),
            right: Rc::new(Tree::Leaf)
        };
        assert!(tree._isNode());
        assert!(!tree._isLeaf());
        let value = unsafe{std::ptr::read(&(*tree.value()).first)};
        assert_eq!((*value).as_ref(), "Jane".to_string());

        assert!(tree.left().as_ref()._isLeaf());
        assert!(tree.right().as_ref()._isLeaf());

        // Now we test with a *const MyStruct
        let tree: Tree<*const MyStruct> = Tree::Node{
            left: Rc::new(Tree::Leaf),
            value: allocate(Box::new(MyStruct{
                first: unsafe{transmute(Rc::new("Jane".to_string()))},
                last: unsafe{transmute(Rc::new("Doe".to_string()))}
            })),
            right: Rc::new(Tree::Leaf)};
        
        assert!(tree._isNode());
        assert!(!tree._isLeaf());
        // Use the unsafe read in the previous test
        let value = unsafe{std::ptr::read(&(*tree.value()).first)};
        assert_eq!((*value).as_ref(), "Jane".to_string());
    }

    // Now let's encode a codatatype from Dafny
    // A codatatype is like a datatype but it can expand infinitely
    // For example, an infinite stream of numbers
    //codatatype NumberStream = NumberStream(value: int, tail: NumberStream)
    //{
    //    static function from(i: int): NumberStream {
    //        NumberStream(i, from(i + 1))
    //    }
    //    function get(i: nat): int {
    //        if i == 0 then value else tail.get(i-1)
    //    }
    // }
    struct NumberStream {
        value: Rc<BigInt>,
        // tail is a lazily initialized Rc<NumberStream>
        tail: LazyFieldWrapper<Rc<NumberStream>>
    }
    impl NumberStream {
        fn from(i: &Rc<BigInt>) -> Rc<NumberStream> {
            let i_copy = i.clone(); // Create a cloned BigInt
            Rc::new(NumberStream {
                value: i.clone(),
                tail: LazyFieldWrapper(Lazy::new(::std::boxed::Box::new({
                    move || NumberStream::from(&Rc::new(i_copy.as_ref() + BigInt::one()))})))
                
                /*Lazy::new(
                    Box::new(move || NumberStream::from(&(i_copy + BigInt::one())))
                as Box<dyn FnOnce() -> Rc<NumberStream>>)*/
            })
        }
        fn value(&self) -> Rc<BigInt> {
            Rc::clone(&self.value)
        }
        fn tail(&self) -> Rc<NumberStream> {
            Rc::clone(Lazy::force(&self.tail.0))
        }

        fn get(&self, i: &Rc<BigInt>) -> Rc<BigInt> {
            if i.as_ref() == &BigInt::zero() {
                self.value.clone()
            } else {
                self.tail().get(&Rc::new(i.as_ref() - BigInt::one()))
            }
        }
    }

    #[test]
    fn test_numberstream() {
        let stream = NumberStream::from(&Rc::new(BigInt::zero()));
        assert_eq!(*stream.get(&Rc::new(BigInt::zero())), BigInt::zero());
        assert_eq!(*stream.get(&Rc::new(BigInt::one())), BigInt::one());
    }

    struct Wrapper {
        w: Rc<WithConstInitializer>
    }

    trait _WithConstInitializer_consts<T> {
        fn _itself(&self) -> Rc<Wrapper>;
        fn _z(&self) -> i16;
    }

    struct WithConstInitializer {
        x: i16,
        z: RefCell<Option<i16>>,
        itself: RefCell<Option<Weak<Wrapper>>>
    }

    impl WithConstInitializer {
        fn _new(x: i16) -> Rc<WithConstInitializer> {
            let result = Rc::new(WithConstInitializer {
                x: x,
                z: RefCell::new(None),
                itself: RefCell::new(None),
            });
            result.z.replace(Some(if x <= 0 { x } else { x - 1}));
            result
        }
    }
    impl _WithConstInitializer_consts<WithConstInitializer> for Rc<WithConstInitializer> {
        fn _itself(&self) -> Rc<Wrapper> {
            // If itself points to nothing, we compute it
            if self.itself.borrow().as_ref().is_none() ||
              self.itself.borrow().as_ref().unwrap().upgrade().is_none()
            {
              let result = Rc::new(Wrapper{w: Rc::clone(self)});
              self.itself.replace(Some(Rc::downgrade(&result)));
              result
            } else {
              Rc::clone(&self.itself.borrow().as_ref().unwrap().upgrade().unwrap())
            }          
        }
        fn _z(&self) -> i16 {
            self.z.borrow().as_ref().unwrap().clone()
        }
    }

    #[test]
    fn test_const_this_in_datatype() {
        let w: Rc<WithConstInitializer> = WithConstInitializer::_new(2);

        assert_eq!(w.x, 2);
        assert_eq!(w._z(), 1);
        assert_eq!(w._itself().w.x, 2);
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

        let lazy = Sequence::<i32>::new_lazy_sequence(&concat);
        assert_eq!(lazy.cardinality_usize(), 6);
        match lazy.borrow() {
            Sequence::LazySequence { boxed, .. } =>
            match (&*boxed.borrow()).borrow() {
                Sequence::ConcatSequence { length, .. } =>
                {
                    assert_eq!(*length, 6);
                },
                _ => panic!("This should never happen")
            },
            _ => panic!("This should never happen")        
        }
        let value = lazy.select(0);
        assert_eq!(value, 1);
        match lazy.borrow() {
            Sequence::LazySequence { boxed, .. } =>
            match (&*boxed.borrow()).borrow() {
                Sequence::ArraySequence { values, .. } =>
                  assert_eq!(values, &Rc::new(vec![1, 2, 3, 4, 5, 6])),
                _ => panic!("This should never happen")
            },
            _ => panic!("This should never happen")        
        }
    }

    #[test]
    fn test_native_array_pointer() {
        let values: *const Vec<i32> = Box::into_raw(Box::new(vec![1, 2, 3]));
        // allocate another vec of size 100
        let values2: *const Vec<i32> = allocate(Box::new(vec![0; 100]));

        // Verify that the length of values is 3
        assert_eq!(unsafe{(*values).len()}, 3);
        // If we change the first element to 4, we should read it as being 4 again
        unsafe{*(*(values as *mut Vec<i32>)).get_unchecked_mut(0) = 4};
        assert_eq!(unsafe{*(*values).get_unchecked(0)}, 4);

        deallocate(values);
    }

    fn Test2(x: bool, y: &mut bool, z: &mut bool) {
        *y = !x;
        *z = !x || *y;
    }
    fn Test3() { 
      let mut y = true; let mut z = true;
      Test2(true, &mut y, &mut z);
      let mut i; let mut j;
      i = y;
      j = z;
    }

    trait Func1<T1, O1> {
        fn apply(&self, x: &T1) -> O1;
    }

    struct Closure1 {  y: Rc<BigInt>}
    impl Func1<Rc<BigInt>, bool> for Closure1 {
        fn apply(&self, x: &Rc<BigInt>) -> bool {
            x.eq(&self.y)
        }
    }
    #[test]
    fn test_apply1() {
      let y = Rc::new(BigInt::one());
      let f: Rc<dyn Func1<Rc<BigInt>, bool>> = Rc::new(Closure1{ y });
      assert_eq!(f.apply(&Rc::new(BigInt::zero())), false);
    }

    #[test]
    fn test_apply1Native() {
        let y: Rc<BigInt> = Rc::new(BigInt::one());
        let y_copy = Rc::clone(&y); // Create a cloned BigInt
        let f: Rc<dyn Fn(&Rc<BigInt>) -> bool> = Rc::new(
            move |x: &Rc<BigInt>|y_copy.eq(x));
        assert_eq!(f.as_ref()(&Rc::new(BigInt::zero())), false);
    }

    // Covariance and contravariance for traits
    trait Input {
        fn get_value(&self) -> Rc<BigInt>;
        fn with_initial(&self) -> Option<*const dyn InputWithInitial>;
        /*fn as_input(&self) -> Rc<dyn Input>;
        fn as_input_allocated(&self) -> Rc<*const dyn Input>;*/
    }
    trait InputWithInitial: Input {
        fn initial_value(&self) -> Rc<BigInt>;    
    }
    struct JustInput {
        value: Rc<BigInt>
    }
    // Allocated version
    impl Input for *const JustInput {
        fn get_value(&self) -> Rc<BigInt> {
            unsafe { Rc::clone(&(**self).value) }
        }
        fn with_initial(&self) -> Option<*const dyn InputWithInitial> {
            None
        }
    }
    // Datatype version
    impl Input for Rc<JustInput> {
        fn get_value(&self) -> Rc<BigInt> {
            Rc::clone(&self.value)
        }
        fn with_initial(&self) -> Option<*const dyn InputWithInitial> {
            None
        }
    }
    impl Input for JustInput {
        fn get_value(&self) -> Rc<BigInt> {
            Rc::clone(&self.value)
        }
        fn with_initial(&self) -> Option<*const dyn InputWithInitial> {
            None
        }
    }

    struct JustInputWithInitial {
        value: Rc<BigInt>,
        initial: Rc<BigInt>
    }
    impl InputWithInitial for Rc<JustInputWithInitial> {
        fn initial_value(&self) -> Rc<BigInt> {
            Rc::clone(&self.initial)
        }
    }
    impl InputWithInitial for *const JustInputWithInitial {
        fn initial_value(&self) -> Rc<BigInt> {
            unsafe { Rc::clone(&(**self).initial) }
        }
    }
    impl InputWithInitial for JustInputWithInitial {
        fn initial_value(&self) -> Rc<BigInt> {
            Rc::clone(&self.initial)
        }
    }
    impl Input for Rc<JustInputWithInitial> {
        fn get_value(&self) -> Rc<BigInt> {
            Rc::clone(&self.value)
        }
        fn with_initial(&self) -> Option<*const dyn InputWithInitial> {
            Some(self as *const dyn InputWithInitial)
        }
    }
    impl Input for *const JustInputWithInitial {
        fn get_value(&self) -> Rc<BigInt> {
            unsafe { Rc::clone(&(**self).value) }
        }
        fn with_initial(&self) -> Option<*const dyn InputWithInitial> {
            Some(self)
        }
    }
    impl Input for JustInputWithInitial {
        fn get_value(&self) -> Rc<BigInt> {
            Rc::clone(&self.value)
        }
        fn with_initial(&self) -> Option<*const dyn InputWithInitial> {
            Some(self as *const dyn InputWithInitial)
        }
    }
    
    #[test]
    fn test_allocated_native() {
        let a: Rc<dyn Fn(*const dyn Input) -> *const dyn InputWithInitial> =
          Rc::new(|x: *const dyn Input| {
            // Just return a new value 
            allocate(Box::new(JustInputWithInitial {
                value: (unsafe{&*x}).get_value(),
                initial: (unsafe{&*x}).get_value()
            }))
          });
        let b: Rc<dyn Fn(*const dyn InputWithInitial) -> *const dyn Input> =
          unsafe { transmute(Rc::clone(&a))};
        // Let's try to pass a regular Input and a regular InputWithInitial to a
        // Let's try to pass a regular InputWithInitial to b
        let just_input = allocate(Box::new(JustInput { value: Rc::new(BigInt::zero())}));
        let just_input_with_initial = allocate(Box::new(JustInputWithInitial {
            value: Rc::new(BigInt::zero()),
            initial: Rc::new(BigInt::one())
        }));
        let input: *const dyn Input = just_input;
        let input_with_initial: *const dyn InputWithInitial = just_input_with_initial;
        // The following will be fixed by Rust on February 8, 2024
        // https://github.com/rust-lang/rust/pull/118133
        //let input_with_initial_as_input: *const dyn Input = input_with_initial;
        let result1: *const dyn Input = (*b)(input_with_initial);
        //let result2: *const dyn InputWithInitial = (*a)(input_with_initial_as_input);
        let result3: *const dyn InputWithInitial = (*a)(input);
        assert_eq!(unsafe { &*result1 }.get_value(), (unsafe{&*input}).get_value());
        //assert_eq!(unsafe { &*result2 }.get_value(), (unsafe{&*input}).get_value());
        assert_eq!(unsafe { &*result3 }.get_value(), (unsafe{&*input}).get_value());
    }

    struct Closure2 { }
    impl Func1<*const dyn Input, *const dyn InputWithInitial> for Closure2 {
        fn apply(&self, x: &*const dyn Input) -> *const dyn InputWithInitial {
            allocate(Box::new(JustInputWithInitial {
                value: unsafe { (**x).get_value() },
                initial: unsafe { (**x).get_value() }
            }))
        }
    }

    #[test]
    fn test_allocated_interpreted() {
        let a: Rc<dyn Func1<*const dyn Input, *const dyn InputWithInitial>> =
          Rc::new(Closure2{});
        let b: Rc<dyn Func1<*const dyn InputWithInitial, *const dyn Input>> =
          unsafe { transmute(Rc::clone(&a))};
        // Let's try to pass a regular Input and a regular InputWithInitial to a
        // Let's try to pass a regular InputWithInitial to b
        let just_input = allocate(Box::new(JustInput { value: Rc::new(BigInt::zero())}));
        let just_input_with_initial = allocate(Box::new(JustInputWithInitial {
            value: Rc::new(BigInt::zero()),
            initial: Rc::new(BigInt::one())
        }));
        let input: *const dyn Input = just_input;
        let input_with_initial: *const dyn InputWithInitial = just_input_with_initial;
        // The following will be fixed by Rust on February 8, 2024
        // https://github.com/rust-lang/rust/pull/118133
        //let input_with_initial_as_input: *const dyn Input = input_with_initial;
        let result1: *const dyn Input = (*b).apply(&input_with_initial);
        //let result2: *const dyn InputWithInitial = (*a)(input_with_initial_as_input);
        let result3: *const dyn InputWithInitial = (*a).apply(&input);
        assert_eq!(unsafe { &*result1 }.get_value(), (unsafe{&*input}).get_value());
        //assert_eq!(unsafe { &*result2 }.get_value(), (unsafe{&*input}).get_value());
        assert_eq!(unsafe { &*result3 }.get_value(), (unsafe{&*input}).get_value());
    }

    #[test]
    fn test_datatype_native() {
        let a: Rc<dyn Fn(&Rc<dyn Input>) -> Rc<dyn InputWithInitial>> =
          Rc::new(|x: &Rc<dyn Input>| {
            // Just return a new value 
            Rc::new(JustInputWithInitial {
                value: x.get_value(),
                initial: x.get_value()
            })
          });
        let b: Rc<dyn Fn(&Rc<dyn InputWithInitial>) -> Rc<dyn Input>> =
          unsafe { transmute(Rc::clone(&a))};
        let just_input = Rc::new(JustInput { value: Rc::new(BigInt::zero())});
        let just_input_with_initial = Rc::new(JustInputWithInitial {
            value: Rc::new(BigInt::zero()),
            initial: Rc::new(BigInt::one())
        });
        let input: Rc<dyn Input> = just_input;
        let input_with_initial: Rc<dyn InputWithInitial> = just_input_with_initial;
        // The following will be fixed by Rust on February 8, 2024
        // https://github.com/rust-lang/rust/pull/118133
        //let input_with_initial_as_input: Rc<dyn Input> = input_with_initial;
        let result1: Rc<dyn Input> = (*b)(&input_with_initial);
        //let result2: Rc<dyn InputWithInitial> = (*a)(input_with_initial_as_input);
        let result3: Rc<dyn InputWithInitial> = (*a)(&input);
        assert_eq!(result1.get_value(), input.get_value());
        //assert_eq!(result2.get_value(), input.get_value());
        assert_eq!(result3.get_value(), input.get_value());
    }

    fn test_partial_initialization_aux(b: bool) {
        let mut c: Option<Rc<MyStructDatatype>> = None;
        if b {
            c = Some(Rc::new(MyStructDatatype {
                first: Rc::new("John".to_string()),
                last: Rc::new("Doe".to_string()) }));
        }
        if b {
            assert_eq!(c.as_ref().unwrap().first.as_str(), "John");
            assert_eq!(c.as_ref().unwrap().last.as_str(), "Doe");
        }
        
    }

    #[test]
    fn test_partial_initialization() {
        test_partial_initialization_aux(true);
        test_partial_initialization_aux(false);
    }

    type Even = Rc<BigInt>;
    mod _Even {
        use std::rc::Rc;
        use num::{Integer, BigInt};
        use super::Even;

        pub fn halve(this: &Even) -> Rc<BigInt> {
            Rc::new(this.div_floor(
              &crate::BigInt::parse_bytes(b"2", 10).unwrap()
            ))
        }
    }

    fn TestEven(even: &Even) {
        let half= _Even::halve(even);
        assert_eq!(half.as_ref() * crate::BigInt::parse_bytes(b"2", 10).unwrap(),
        even.as_ref().clone());
    }

    #[test]
    fn test_even() {
        let even = Even::new(crate::BigInt::parse_bytes(b"8", 10).unwrap());
        TestEven(&even);
    }

    #[test]
    fn test_newtypes() {
        let five_bigint = Rc::new(crate::BigInt::parse_bytes(b"5", 10).unwrap());
        // Convert five_bigint to u16
        let five_u16: u16 = num::ToPrimitive::to_u16(five_bigint.as_ref()).unwrap();
    }

    trait object {
        fn as_object(self: Box<Self>) -> *mut dyn object;
        //fn is_<T>(self: Box<Self>) -> bool;
    }
    trait Trait: object {
        fn as_trait(self: Box<Self>) -> *mut dyn Trait;
        //fn from_object(this: *mut dyn object) -> *mut dyn Trait;
    }

    struct Class {}

    impl CastableTo<*mut dyn object> for *mut Class
    {
        fn cast_to(&self) -> *mut dyn object {
            unsafe{Box::<Class>::from_raw(*self)}.as_object()
        }
    }

    impl CastableTo<*mut Class> for *mut dyn object
    {
        fn cast_to(&self) -> *mut Class {
            self.downcast_ref::<Class>().unwrap() as *const Class as *mut Class
        }
    }

    impl Trait for Class {
        fn as_trait(self: Box<Self>) -> *mut dyn Trait {
            Box::into_raw(self)
        }
    }

    impl object for Class {
        fn as_object(self: Box<Self>) -> *mut dyn object {
           Box::into_raw(self)
        }
    }

    enum DafnyOption<T: Clone> {
        Some{value: T},
        None
    }

    trait CastableTo<Y> {
        fn cast_to(self: &Self) -> Y;
    }

    impl <T: Clone, U: Clone> CastableTo<Rc<DafnyOption<U>>> for Rc<DafnyOption<T>>
      where T: CastableTo<U>
    {
        fn cast_to(self: &Rc<DafnyOption<T>>) -> Rc<DafnyOption<U>> {
            match self.as_ref() {
                DafnyOption::Some{value} =>
                  Rc::new(DafnyOption::Some{value: value.cast_to()}),
                  DafnyOption::None =>
                  Rc::new(DafnyOption::None)
            }
        }
    }

    #[test]
    fn test_covariance() {
        // trait X {}
        // class A extends X {}
        // method Test() {
        //   var a := new A;
        //   var x: Option<X> := Some(a);
        // }

        let mut c: *mut Class = Box::into_raw(Box::new(Class{}));
        let mut c_t: *mut dyn Trait = c;
        let mut c_t_o: *mut dyn object = unsafe{Box::<dyn Trait>::from_raw(c_t)}.as_object();
        let mut c_o: *mut dyn object = c;
        //let mut c_o_t: *mut dyn Trait = c_o;
        let mut c_o_c: *mut Class = c_o.downcast_mut::<Class>().unwrap();
        let mut c_t_c: *mut Class = c_t.downcast_mut::<Class>().unwrap();

        // Now let's put a c into an Option<*mut class> and upcast it to an Option<*mut dyn object>
        // and let's do the reverse transformation
        let mut opt_c = Rc::new(DafnyOption::<*mut Class>::Some{value: c});
        let mut opt_c_o = opt_c.cast_to();
        let mut opt_c_o_c: Rc<DafnyOption<*mut Class>> = opt_c_o.cast_to();
    }
}
// Struct containing two reference-counted fields
