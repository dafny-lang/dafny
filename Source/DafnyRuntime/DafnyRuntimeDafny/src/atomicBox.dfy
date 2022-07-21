
module AtomicBoxes {
  class {:extern} AtomicBox<T> {

    ghost const inv: T -> bool

    static method Make(ghost inv: T -> bool, t: T) returns (ret: AtomicBox<T>)
      requires inv(t)
      ensures ret.inv == inv

    method Get() returns (t: T)
      ensures inv(t)

    method Put(t: T)
      requires inv(t)
  }
}