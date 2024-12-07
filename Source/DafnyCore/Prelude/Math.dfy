module {:extract_boogie} Math {
  export
    provides Min, Clip
    provides Min0, Min1, MinEither
    provides ClipId, ClipZero

  // boogie:
  // function Math#min(a: int, b: int): int;
  function {:extract_boogie_name "Math#min"} Min(a: int, b: int): int {
    if a <= b then a else b
  }

  // boogie:
  // axiom (forall a: int, b: int :: { Math#min(a, b) } a <= b <==> Math#min(a, b) == a);
  lemma {:extract_pattern Min(a, b)} Min0(a: int, b: int)
    ensures a <= b <==> Min(a, b) == a
  {
  }

  // boogie:
  // axiom (forall a: int, b: int :: { Math#min(a, b) } b <= a <==> Math#min(a, b) == b);
  lemma {:extract_pattern Min(a, b)} Min1(a: int, b: int)
    ensures b <= a <==> Min(a, b) == b
  {
  }

  // boogie:
  // axiom (forall a: int, b: int :: { Math#min(a, b) } Math#min(a, b) == a || Math#min(a, b) == b);
  lemma {:extract_pattern Min(a, b)} MinEither(a: int, b: int)
    ensures Min(a, b) == a || Min(a, b) == b
  {
  }

  // boogie:
  // function Math#clip(a: int): int;
  function {:extract_boogie_name "Math#clip"} Clip(a: int): int {
    if 0 <= a then a else 0
  }

  // boogie:
  // axiom (forall a: int :: { Math#clip(a) } 0 <= a ==> Math#clip(a) == a);
  lemma {:extract_pattern Clip(a)} ClipId(a: int)
    requires 0 <= a
    ensures Clip(a) == a
  {
  }

  // boogie:
  // axiom (forall a: int :: { Math#clip(a) } a < 0  ==> Math#clip(a) == 0);
  lemma {:extract_pattern Clip(a)} ClipZero(a: int)
    requires a < 0
    ensures Clip(a) == 0
  {
  }
}
