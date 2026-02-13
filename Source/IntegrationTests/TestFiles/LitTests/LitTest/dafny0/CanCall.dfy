// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


module ModifiesCallee {
  ghost function Wrap(S: set<object>): set<object> {
    S
  }

  method DoWrapped(S: set<object>)
    modifies Wrap(S)
  {
    DoOne(S);
  }

  method DoOne(S: set<object>)
    modifies S
  {
  }
}

module ModifiesCaller {
  ghost function Wrap(S: set<object>): set<object> {
    S
  }

  method DoWrapped(S: set<object>)
    modifies Wrap(S)
  {
  }

  method DoOne(S: set<object>)
    modifies S
  {
    DoWrapped(S);
  }
}

module ArraySeqInit {
  function F(a: int): int {
    45
  }

  method TestArrayF() {
    var m := new int[3](F);
    assert m[0] == 45;
  }

  method TestArrayLambda() {
    var m := new int[3](_ => 45);
    assert m[0] == 45;
  }

  method TestSeqF() {
    var m := seq(3, F);
    assert m[0] == 45;
  }

  method TestSeqLambda() {
    var m := seq(3, _ => 45);
    assert m[0] == 45;
  }

}

module QuantifierBeforeOtherConjunct {
  datatype List<T> = Nil | Cons(head: T, tail: List)

  function Length(list: List): nat {
    match list
    case Nil => 0
    case Cons(_, tl) => 1 + Length(tl)
  }

  function Occurrences(x: int, list: List<int>): nat
  {
    match list
    case Nil => 0
    case Cons(y, tl) => (if x == y then 1 else 0) + Occurrences(x, tl)
  }

  function Partition(x: int, l: List<int>): (result: (List<int>, List<int>))
    ensures
      && (forall y :: Occurrences(y, result.0) == if y <= x then Occurrences(y, l) else 0)
      && Length(l) == Length(result.0) + Length(result.1)

  lemma CallPartition(x: int, l: List<int>) returns (aaa: List<int>, bbb: List<int>)
    requires l.Cons? && l.head <= x
    ensures
      && (forall y :: Occurrences(y, aaa) == if y <= x then Occurrences(y, l) else 0)
      && Length(l) == Length(aaa) + Length(bbb)
  {
    var (lo, hi) := Partition(x, l.tail);
    aaa := Cons(l.head, lo);
    bbb := hi;
  }
}

module StaticConstFields {
  function DoNotCall(): int
    requires false
  {
    DoNotCall() + 1
  }

  const X := (Test(); DoNotCall())

  lemma Test()
    ensures false
  {
    // If we someone got a DoNotCall#canCall for free, then we'd be able to prove anything,
    // including the precondition in the following line (which would mean that everything
    // verifies in this module).
    var x := DoNotCall(); // error: precondition violation
  }

  lemma UseX()
    ensures false
  {
    var x := X;
  }
}

module InstanceConstFields {
  class MyClass {
    constructor ()
      ensures false
    { // error: postcondition violation
    }
    
    function DoNotCall(): int
      requires false
    {
      DoNotCall() + 1
    }

    const X := (Test(); DoNotCall())

    lemma Test()
      ensures false
    {
      // See comment in StaticConstFields.Test() above.
      var x := DoNotCall(); // error: precondition violation
    }

    lemma UseX()
      ensures false
    {
      var x := X;
    }
  }
}

module ThemesOnStandardLibraryJSON {
  const TWO_TO_THE_8:   int := 0x100
  const TWO_TO_THE_32:  int := 0x1_00000000
  newtype uint8 = x: int   | 0 <= x < TWO_TO_THE_8
  newtype uint32 = x: int  | 0 <= x < TWO_TO_THE_32
  type byte = uint8
  type bytes = seq<byte>

  type View = v: View_ | v.Valid? witness View([], 0, 0)
  datatype View_ = View(s: bytes, beg: uint32, end: uint32) {
    ghost const Valid?: bool :=
      0 <= beg as int <= end as int <= |s| < TWO_TO_THE_32

    predicate Char?(c: char)
      requires Valid?
      requires c as int < 256
    {
      Byte?(c as byte)
    }

     function Bytes(): bytes requires Valid? {
      s[beg..end]
    }

    predicate Byte?(c: byte)
      requires Valid?
    {
      Bytes() == [c]
    }

    static function OfBytes(bs: bytes) : (v: View)
      requires |bs| < TWO_TO_THE_32
      ensures v.Bytes() == bs
    {
      View(bs, 0 as uint32, |bs| as uint32)
    }

    static const StaticDoubleQuote := View.OfBytes(['\"' as byte])
    const InstanceDoubleQuote := View.OfBytes(['\"' as byte])
    static function FunctionDoubleQuote(): View_ {
      View.OfBytes(['\"' as byte])
    }
  }

  type jquoteStatic = v: View | v.Char?('\"') witness View_.StaticDoubleQuote
  type jquoteInstance = v: View | v.Char?('\"') witness View([], 0, 0).InstanceDoubleQuote
  type jquoteFunction = v: View | v.Char?('\"') witness View_.FunctionDoubleQuote()

  datatype jstringStatic = JStringStatic(lq: jquoteStatic)
  datatype jstringInstance = JStringInstance(lq: jquoteInstance)
  datatype jstringFunction = JStringFunction(lq: jquoteFunction)
  datatype jstringDefaultValue = JStringDefaultValue(lq: jquoteStatic := View_.StaticDoubleQuote)

  method TestStatic() {
    var j := JStringStatic(View_.StaticDoubleQuote);
  }

  method TestInstance() {
    var v := View([], 0, 0);
    var j := JStringInstance(v.InstanceDoubleQuote);
  }

  method TestFunction() {
    var j := JStringFunction(View_.FunctionDoubleQuote());
  }

  method TestDefaultValue() {
    var j := JStringDefaultValue();
  }
}
