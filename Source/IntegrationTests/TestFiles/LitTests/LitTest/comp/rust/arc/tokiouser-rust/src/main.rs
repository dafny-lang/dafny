pub mod tokiouser;
use std::thread;
fn main() {
    let list = tokiouser::_module::_default::OfSize(
        &::dafny_runtime::int!(3),
        &::dafny_runtime::DafnyChar('a'),
    );
    let list_copy = list.clone();
    // We spawn a thread to compute the tail and return it.
    let tail_spawn = thread::spawn(move || {
        list.tail().clone()
    });
    let tail_normal = list_copy.tail().clone();
    let tail_spawned = tail_spawn.join().unwrap();
    assert_eq!(tail_normal, tail_spawned);
    println!("The two lists, which are the tail of the same list but treated in different threads, are the same!");
}
