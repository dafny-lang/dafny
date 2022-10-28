---
title: "Error: this symbol not expected in Dafny"
---

This error message is not clear and may come from a variety of sources. Here is one:
```dafny
{% include_relative ERROR_PostconditionLemma.dfy %}
```
which produces 
```text
{% include_relative ERROR_PostconditionLemma.txt %}
```

The error message points to the token `true` as the unexpected symbol.
`true` is definitely a legitimate symbol in Dafny.

The problem is that the `;` in the `ensures` clause is seen as the (optional) semicolon that can end
the clause. Thus the `true` is interpreted as the (illegal) start to a new clause (or a `{` to start the body).

The correct way to include a lemma with the postcondition is to use parentheses:
`ensures (L(); true)
