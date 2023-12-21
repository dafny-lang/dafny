
// Test module
#[cfg(test)]
mod tests {
    use std::{rc::Rc, fmt::Formatter};

    use num::{BigInt, One, Zero};
    use once_cell::sync::Lazy;

    use crate::{DafnyClone, DafnyPrint, deallocate, allocate};

    use super::*;

    // A datatype encoded in Rust
    // T can either be an allocated type *const X or a reference type Rc<X>
    // Either way, T must extend DafnyClone and DafnyPrint
    // T must be equatable
    #[derive(PartialEq)]
    enum Tree<T: DafnyClone>
      where T: DafnyPrint
    {
        Leaf,
        Node{left: Rc<Tree<T>>, value: T, right: Rc<Tree<T>>}
    }
    impl <T: DafnyClone> Tree<T>
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
                Tree::Node{value, ..} => value.clone_value()
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

    #[derive(PartialEq)]
    struct MyStruct {
        first: Rc<String>,
        last: Rc<String>,
    }
    impl DafnyPrint for MyStruct {
        fn fmt_print(&self, f: &mut Formatter<'_>, in_seq: bool) -> std::fmt::Result {
            write!(f, "MyStruct({}, {})", self.first, self.last)
        }
    }
    impl MyStruct {
        fn constructor(first: Rc<String>, last: Rc<String>) -> *const MyStruct {
            let this =
              allocate(Box::new(MyStruct {
                first: Rc::new("".to_string()),
                last: Rc::new("".to_string())}));
            unsafe {(*(this as *mut MyStruct)).first = first};
            unsafe {(*(this as *mut MyStruct)).last = last};
            this
        }
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
            Rc::new("John".to_string()),
            Rc::new("Doe".to_string()));

        // Assign the result to a *const on a raw pointer named "theobject"
        let mut possiblealias: *const MyStruct = theobject;

        // If 'reuse' is true, assign the same pointer to another named "possiblealias"
        // Otherwise, use the method allocate() on a new structure
        if !reuse {
            possiblealias = MyStruct::constructor(
                Rc::new("John".to_string()),
                Rc::new("Doe".to_string()));
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
    /*codatatype NumberStream = NumberStream(value: int, tail: NumberStream)
    {
        static function from(i: int): NumberStream {
            NumberStream(i, from(i + 1))
        }
        function get(i: nat): int {
            if i == 0 then value else tail.get(i-1)
        }
    } */
    type LazyNumberStream = Lazy<Rc<NumberStream>, Box<dyn FnOnce() -> Rc<NumberStream>>>;

    struct NumberStream {
        value: Rc<BigInt>,
        // tail is a lazily initialized Rc<NumberStream>
        tail: LazyNumberStream
    }
    impl NumberStream {
        fn from(i: &BigInt) -> Rc<NumberStream> {
            let i_copy = i.clone(); // Create a cloned BigInt
            let closure: Box<dyn FnOnce() -> Rc<NumberStream>> =
                Box::new(move || NumberStream::from(&((&i_copy).clone() + BigInt::one())));
            let thunk = Lazy::new(closure);
            Rc::new(NumberStream {
                value: Rc::new(i.clone()),
                tail: thunk
            })
        }
        fn value(&self) -> Rc<BigInt> {
            Rc::clone(&self.value)
        }
        fn tail(&self) -> Rc<NumberStream> {
            Rc::clone(Lazy::force(&self.tail))
        }

        fn get(&self, i: &BigInt) -> Rc<BigInt> {
            if i == &BigInt::zero() {
                Rc::clone(&self.value)
            } else {
                self.tail().get(&(i.clone() - BigInt::one()))
            }
        }
    }

    #[test]
    fn test_numberstream() {
        let stream = NumberStream::from(&BigInt::zero());
        assert_eq!(*stream.get(&BigInt::zero()), BigInt::zero());
        assert_eq!(*stream.get(&BigInt::one()), BigInt::one());
    }
    
}
// Struct containing two reference-counted fields
