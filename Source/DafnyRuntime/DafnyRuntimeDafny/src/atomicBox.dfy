
module AtomicBoxes {
  class {:extern} AtomicBox<T> {

    ghost const inv: T -> bool

    static method {:extern} Make(ghost inv: T -> bool, t: T) returns (ret: AtomicBox<T>)
      requires inv(t)
      ensures ret.inv == inv

    method {:extern} Get() returns (t: T)
      ensures inv(t)

    method {:extern} Put(t: T)
      requires inv(t)
  }
}