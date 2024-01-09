
// Interface with the System namespace
module {:extern "System"} {:compile false} {:options "-functionSyntax:4"} System {
  class {:extern "Text.StringBuilder"} {:compile false} CsStringBuilder {
    ghost var built: CsString
    constructor {:extern} ()
    method {:extern "Append"} Append(s: CsString)
      modifies this
      ensures built == String.Concat(old(built), s)
    // This hack is necessary because ToString is replaced by ToString_
    // in the C# compiler, even if it's declared extern...
    method {:extern @"ToString().ToString"} ToString() returns (r: CsString)
      ensures r == built
  }
  type {:extern "String"} CsString(!new,==) {
    ghost predicate {:extern} Contains(needle: CsString)
    lemma {:axiom} ContainsTransitive(other: CsString, needle: CsString)
      requires Contains(other) && other.Contains(needle)
      ensures Contains(needle)
  }
  lemma ContainsTransitive()
    ensures forall s1: CsString, s2: CsString, s3: CsString
              | s1.Contains(s2) && s2.Contains(s3) :: s1.Contains(s3)
  {
    forall s1: CsString, s2: CsString, s3: CsString
      | s1.Contains(s2) && s2.Contains(s3)
    {
      s1.ContainsTransitive(s2, s3);
    }
  }
  class {:extern "String"} {:compile false} String {
    static function Concat(s1: CsString, s2: CsString): (r: CsString)
      ensures r.Contains(s1)
      ensures r.Contains(s2)
  }
}
