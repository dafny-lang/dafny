
// Test module
#[cfg(test)]
mod tests {
    use std::{rc::Rc, fmt::Formatter, borrow::Borrow, any::Any};
    use as_any::{AsAny, Downcast};
    use num::{BigInt, One, Zero};
    use once_cell::unsync::Lazy;

    use crate::{DafnyPrint, deallocate, allocate, Sequence, is_instance_of, LazyFieldWrapper};

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

    #[derive(PartialEq)]
    struct MyStruct {
        first: Rc<String>,
        last: Rc<String>,
    }
    impl DafnyPrint for MyStruct {
        fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
            write!(f, "MyStruct({}, {})", self.first, self.last)
        }
    }
    impl MyStruct {
        fn constructor(first: &Rc<String>, last: &Rc<String>) -> *const MyStruct {
            let this =
              allocate(Box::new(MyStruct {
                first: Rc::new("".to_string()),
                last: Rc::new("".to_string())}));
            unsafe {(*(this as *mut MyStruct)).first = Rc::clone(first)};
            unsafe {(*(this as *mut MyStruct)).last = Rc::clone(last)};
            this
        }
    }
    impl HasFirst for MyStruct {
        // Use unsafe and pointer casting if necessary
        fn _get_first(&self) -> Rc<String> {
            self.first.clone()
        }
        fn _set_first(&self, new_first: &Rc<String>) {
            let this = self as *const MyStruct;
            unsafe {(*(this as *mut MyStruct)).first = Rc::clone(new_first)};
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
        assert!(!is_instance_of::<dyn HasFirst, NoStruct>(theobject));
        
        let is_has_first = unsafe { &*theobject }.as_any().downcast_ref::<MyStruct>().is_some();
        assert!(is_has_first, "The value should be a HasFirst");
        assert!(!is_instance_of::<dyn HasFirst, MyStruct>(theobject));

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
        unsafe {(*(theobject as *mut MyStruct)).first = Rc::new("Jane".to_string())};
        // Using std::ptr::write:
        //unsafe {std::ptr::write(&mut (*theobject).first, "Jane".to_string())};}h

        // If !reuse and theobject.first == possiblealias.first, panic (unreachable code)
        if !reuse && unsafe{std::ptr::read(&(*theobject).first)}
                  == unsafe{std::ptr::read(&(*possiblealias).first)} {
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
        let tree: Tree<Rc<MyStruct>> = Tree::Node{
            left: Rc::new(Tree::Leaf),
            value: Rc::new(MyStruct{
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
                first: Rc::new("Jane".to_string()),
                last: Rc::new("Doe".to_string())})),
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

    #[test]
    fn test_sequence() {
        let values = Rc::new(vec![1, 2, 3]);
        let seq = Sequence::<i32>::new_array_sequence(&values);
        assert_eq!(seq.node_count(), 1);
        assert_eq!(seq.cardinality(), 3);
        assert_eq!(seq.to_array(), values);
    
        // Create a concat array, wrap it into a lazy one, get the i-th element,
        // and verify that this operation flattened the array
        let left = Sequence::<i32>::new_array_sequence(&Rc::new(vec![1, 2, 3]));
        let right = Sequence::<i32>::new_array_sequence(&Rc::new(vec![4, 5, 6]));
        let concat = Sequence::<i32>::new_concat_sequence(&left, &right);

        let lazy = Sequence::<i32>::new_lazy_sequence(&concat);
        assert_eq!(lazy.node_count(), 4);
        assert_eq!(lazy.cardinality(), 6);
        match lazy.borrow() {
            Sequence::LazySequence { boxed, .. } =>
            match (&*boxed.borrow()).borrow() {
                Sequence::ConcatSequence { is_string, node_count, length, .. } =>
                {
                    assert_eq!(*is_string, false);
                    assert_eq!(*node_count, 3);
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
}
// Struct containing two reference-counted fields
