use dafny_runtime::{DynAny, Upcast, UpcastObject};

struct SmokeStruct {
    pub i: i32,
}
pub struct OtherSmokeStruct(pub i32);

impl UpcastObject<DynAny> for SmokeStruct {
    dafny_runtime::UpcastObjectFn!(DynAny);
}
impl Upcast<DynAny> for SmokeStruct {
    dafny_runtime::UpcastFn!(DynAny);
}

#[test]
fn smoke_test() {
    let mut x = ::dafny_runtime::dafny_runtime_conversions::object::boxed_struct_to_dafny_class(
        Box::new(SmokeStruct { i: 3 }),
    );
    assert_eq!(::dafny_runtime::refcount!(x), 1);
    let y = ::dafny_runtime::cast_any_object!(x);
    assert_eq!(::dafny_runtime::refcount!(x), 2);
    assert!(::dafny_runtime::is_object!(y, SmokeStruct));
    assert!(!::dafny_runtime::is_object!(y, OtherSmokeStruct));
    assert_eq!(::dafny_runtime::rd!(x).i, 3);
    x = ::dafny_runtime::cast_object!(y, SmokeStruct);
    assert_eq!(::dafny_runtime::rd!(x).i, 3);
    let mut x = ::dafny_runtime::dafny_runtime_conversions::ptr::boxed_struct_to_dafny_class(
        Box::new(SmokeStruct { i: 3 }),
    );
    let y = ::dafny_runtime::cast_any!(x);
    assert!(::dafny_runtime::is!(y, SmokeStruct));
    assert!(!::dafny_runtime::is!(y, OtherSmokeStruct));
    assert_eq!(::dafny_runtime::read!(x).i, 3);
    x = ::dafny_runtime::cast!(y, SmokeStruct);
    assert_eq!(::dafny_runtime::read!(x).i, 3);
    let z = ::dafny_runtime::truncate!(::dafny_runtime::int!(3), usize);
    let a = ::dafny_runtime::array!(1, 2, 3);
    assert_eq!(z, 3);
    assert_eq!(::dafny_runtime::read!(a)[2], 3);
}
