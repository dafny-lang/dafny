module M {
  class T { }
  class U { }
}

module N {
  class T { } // error: duplicate class name
}

module U imports N {  // fine, despite the fact that a class is called U--module names are in their own name space
}

module V imports T {  // error: T is not a module
}

module A imports B, M {
  class Y { }
}

module B imports N, M {
  class X { }
}

module G imports A, M, A, H, B {  // error: cycle in import graph
}

module H imports A, N, I {
}

module I imports J {
}

module J imports G, M {
}
