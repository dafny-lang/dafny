// dafny Example.dfy
class A {
  var x: string
}

type AA = z: A | z.x == "" witness * reads z

