// RUN: %testDafnyForEachResolver "%s"


class MyList<T>
{
}

method AAA<U>(aax: MyList?<U>) returns (aay: MyList?<U>)
  ensures BBB(aax, aay)

ghost predicate BBB<V>(bbx: MyList?<V>, bby: MyList?<V>)
{
  // the translation of this "null", when inlined into the postcondition of AAA above, once
  // generated malformed Boogie (because of a missing substitution of the type for "null")
  CCC(bbx, null)
}

ghost predicate CCC<W>(ccx: MyList?<W>, ccy: MyList?<W>)
