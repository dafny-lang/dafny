// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/// # Random variable. extracted from any number of bits
  datatype ImapSimulator_<!A, B> = ImapSimulator(
    input: iset<A>,
    apply: A --> B)
  {
    ghost predicate Valid() {
      forall i <- input :: apply.requires(i)
    }
  }

  type ImapSimulator<!A, B> =
    X: ImapSimulator_<A, B> |
    X.Valid() witness ImapSimulator(iset{}, (x: A) requires false => match() {})
//                  error probably comes from here                   ^^^^^^^^^^