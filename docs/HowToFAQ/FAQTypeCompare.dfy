abstract module Mixin1 { type T = int }
abstract module Mixin2 { type T = int }
abstract module Mixins1and2 {
    import M1 : Mixin1
    import M2 : Mixin2
    lemma typeConstraint() ensures M1.T == M2.T
}
