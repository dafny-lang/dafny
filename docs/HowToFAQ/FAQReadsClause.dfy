// dafny Example.dfy
class A {
  var x: string
}

type AA = a: A | a.x == "" witness * reads a

