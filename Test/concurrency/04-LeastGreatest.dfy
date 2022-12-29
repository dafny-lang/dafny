// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Simple least predicate

// Note: `least predicate P(x: int) { true && P(x) }` would be equivalent to `false`.

least predicate P(x: int) {
  x == 123 || P(x)
}

lemma BuildP(x: int) requires x == 123 ensures P(x) {}

// Simple greatest predicate

greatest predicate Q(x: int) {
  true && Q(x)
}

greatest lemma BuildQ(x: int)
  ensures Q(x)
{
}

lemma AdvBuildQ(x: int)
  ensures Q(x)
{
  forall k: ORDINAL { AdvBuildQAux(k, x); }
}

lemma AdvBuildQAux(k: ORDINAL, x: int) ensures Q#[k](x) {}

// Another simple greatest predicate

greatest predicate R(x: bool) {
  x ==> R(x)
}

greatest lemma BuildR(x: bool) ensures R(true) {}

// Mutually recursive

trait Object {}

greatest predicate A(x: Object) {
  B(x)
}

greatest predicate B(x: Object) {
  A(x)
}

lemma BuildA(x: Object) ensures A(x) {
  forall k: ORDINAL { BuildAAux(k, x); }
}

lemma BuildAAux(k: ORDINAL, x: Object) ensures A#[k](x) {
  forall j: ORDINAL | j < k { BuildBAux(j, x); }
}

lemma BuildBAux(k: ORDINAL, x: Object) ensures B#[k](x) {
  forall j: ORDINAL | j < k { BuildAAux(j, x); }
}

// Mutually recursive, using two different traits

trait TraitA {
  var b: TraitB
}

trait TraitB {
  var a: TraitA
}

greatest predicate invA(self: TraitA) reads * {
  invB(self.b)
}

greatest predicate invB(self: TraitB) reads * {
  invA(self.a)
}

lemma EstablishInvA(self: TraitA)
  ensures invA(self)
{
  forall k: ORDINAL { EstablishInvAuxA(k, self); }
}

lemma EstablishInvAuxA(k: ORDINAL, self: TraitA)
  ensures invA#[k](self)
{
  forall j: ORDINAL | j < k { EstablishInvAuxB(j, self.b); }
}

lemma EstablishInvB(self: TraitB)
  ensures invB(self)
{
  forall k: ORDINAL { EstablishInvAuxB(k, self); }
}

lemma EstablishInvAuxB(k: ORDINAL, self: TraitB)
  ensures invB#[k](self)
{
  forall j: ORDINAL | j < k { EstablishInvAuxA(j, self.a); }
}

greatest lemma AlternativeEstablishInvA(self: TraitA) ensures invA(self) && invB(self.b) {}

greatest lemma AlternativeEstablishInvB(self: TraitB) ensures invB(self) && invA(self.a) {}
