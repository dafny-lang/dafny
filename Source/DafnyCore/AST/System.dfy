
// Interface with the System namespace
@Options("-functionSyntax:4")
@Compile(false)
module {:extern "System"} System {
  @Compile(false)
  class {:extern "Text.StringBuilder"} CsStringBuilder {
    ghost var built: CsString
    constructor {:extern} ()
    @Axiom
    method {:extern "Append"} Append(s: CsString)
      modifies this
      ensures built == String.Concat(old(built), s)
    // This hack is necessary because ToString is replaced by ToString_
    // in the C# compiler, even if it's declared extern...
    @Axiom
    method {:extern @"ToString().ToString"} ToString() returns (r: CsString)
      ensures r == built
  }
  type {:extern "String"} CsString(!new,==) {
    ghost predicate {:extern} Contains(needle: CsString)
    @Axiom
    lemma ContainsTransitive(other: CsString, needle: CsString)
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
  @Compile(false)
  class {:extern "String"} String {
    @Axiom
    static function {:extern} Concat(s1: CsString, s2: CsString): (r: CsString)
      ensures r.Contains(s1)
      ensures r.Contains(s2)
  }
}
