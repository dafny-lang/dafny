pub mod tokiouser;
use std::thread;
pub use tokiouser::_module::*;
fn main() {
    let list = _default::OfSize(
        &::dafny_runtime::int!(3),
        &::dafny_runtime::DafnyChar('a'),
    );
    let list_copy = list.clone();
    // We spawn a thread to compute the tail and return it.
    let tail_spawn = thread::spawn(move || {
        list.tail().clone()
    });
    let obj = UnderlyingObject::_allocate_object();
    UnderlyingObject::_ctor(&obj);
    let obj = ::dafny_runtime::UpcastObject::<dyn UpperTrait>::upcast(::dafny_runtime::rd!(obj));
    let obj_copy = obj.clone();
    let obj_spawn = thread::spawn(move || {
        ::dafny_runtime::rd!(obj).ReturnWhatWasGiven(&::dafny_runtime::int!(3))
    });
    let tail_normal = list_copy.tail().clone();
    let tail_spawned = tail_spawn.join().unwrap();
    let three_normal = ::dafny_runtime::rd!(obj_copy).ReturnWhatWasGiven(&::dafny_runtime::int!(3));
    let three_spawned = obj_spawn.join().unwrap();
    assert_eq!(tail_normal, tail_spawned);
    assert_eq!(three_normal, three_spawned);
    _default::Test();
    println!("The two lists, which are the tail of the same list but treated in different threads, are the same!");
}
