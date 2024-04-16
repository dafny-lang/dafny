module {:compile false} Std.JavaInterop {

  import opened BoundedInts

  // TODO: There's no Dafny type that directly maps to a Java char
  // like the bounded ints map to types like int and long.
  // This extern hack is very likely to fall apart quickly.
  type {:extern "char"} JavaChar

  class {:extern} String {

    ghost const elements: seq<JavaChar>

    function JavaChar At(i: index)

  }
}