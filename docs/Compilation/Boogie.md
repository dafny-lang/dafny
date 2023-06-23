<p></p> <!-- avoids duplicate title -->

# Dafny compilation to Boogie

## `{:opaque} attribute`

During verification in Boogie, all functions are given an extra first parameter, which is the _fuel_ (represented in Boogie by unary numbers, e.g. `$LS($LS($LZ)`) is a fuel of two).
To unroll a function, axioms ensure that a recursive call is provided with the current fuel minus 1, so that we don't unroll undefinitely.

**Normal behavior:** When verifying a method or a function, Dafny will look at every `assert`. If it finds one, every function call inside it will use a fuel argument of at least 2 (`$LS($LS($LZ))`), meaning the verifier will be able to unroll the function's body twice for this assertion. When this assertion is proven, Dafny provides an `assume` about the result, but in this case the functions are provided a fuel of only 1 (`$LS($LZ)`), meaning it unrolls the body only once.

**Opaque behavior:** When Dafny sees an `{:opaque}` attribute on a function `foo`, Dafny declares to Boogie two unknown constants `StartFuel_f` and `StartFuelAssert_f`. It uses `StartFuelAssert_f` in lieu of the default fuel (`$LS($LS($LZ))`) in the context of `assert` statements or expressions, and `StartFuel_f` in lieu of the default fuel (`$LS($LZ)`) in the context of the `assume` that immediately follows the `assert`. These two constants don't have any axioms so, by default, the verifier is unable to unroll the functions and they behave like uninterpreted functions.

**Reveal lemma:** Every statement (or part of expression) `reveal foo(), bar();` is translated to calls to lemmas `reveal_foo(); reveal_bar();`.
Such lemmas are defined in Dafny and with special attribute provide the postcondition that 1) `StartFuel_f` is `$LS(MoreFuel_f)` (where `MoreFuel_f` is an declared constant without axiom), and `StartFuelAssert_f` is `$LS($LS(MoreFuel_f))`. This makes the call to a function the same as if it was not opaque.

```dafny
  lemma {:axiom} {:opaque_reveal} {:auto_generated} {:fuel foo,1,2} reveal_foo()
```

The `{:fuel foo,1,2}` annotation in Dafny corresponds to the Boogie equivalent of:
```
ensures StartFuel_f = $LS(MoreFuel_f)
ensures StartFuelAssert_f = $LS($LS(MoreFuel_f))
```
