module UserD {
  import Outer.Inner
  method M() { var x := Inner.G(); }
}
