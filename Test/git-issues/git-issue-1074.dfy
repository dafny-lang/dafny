// RUN: %dafny /compileVerbose:1 /compile:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  // This test uses an opaque type as the type of "children" below. This once caused
  // a crash in the compiler.

  // To distinguish the crashing test output from the correct test output, we need to
  // get to a point where the compiler prints some output. If the compilation succeeds,
  // there will be some output. But to make the opaque type compile, it needs to be
  // marked with an :extern that redirects it to some existing type. Rather than relying
  // on some type in the C#-or-other-target runtime library, this test declares a class
  // MyCollection, which is then named in the :extern attribute. (This relies on that
  // "MyCollection" is not name mangled in the process.)
  type {:extern "MyCollection"} Container<A>
  class MyCollection<X> {
  }

  datatype Node = Leaf | Node(children: Container<Node>)

  method Test(node: Node)
    requires node.Node?
  {
    var Node(ch) := node; // this line once crashed the compiler
  }
}

module B {
  datatype InnerT<X> = Inner(x: X)
  datatype Node<X, Y> = Leaf | Node(children: Y)

  method Test(node: Node<int, InnerT<real>>)
    requires node.Node?
  {
    var Node(Inner(z)) := node; // this once compiled into malformed code, because the compiler used "int" instead of "InnerT<real>" as the type of Inner(z)
  }
}

module C {
  datatype InnerT<X> = Inner(x: X)
  datatype Node<X> = Leaf | Node(children: InnerT<X>)

  method Test(node: Node<int>)
    requires node.Node?
  {
    var Node(Inner(z)) := node; // this once compiled into malformed code, because the compiler used "X" instead of "InnerT<int>" as the type of Inner(z)
  }
}
