
### Error: Duplicate declaration modifier: abstract

```dafny
abstract abstract module M {}
```

No Dafny modifier, such as [`abstract`, `static, `ghost`](../DafnyRef/DafnyRef/#sec-declaration-modifiers may be repeated. Such repetition would be superfluous even if allowed.

### Error: a _decl_ cannot be declared 'abstract'
 
```dafny
module M {
  abstract const c := 4
}
```

Only some kinds of declarations can be declared abstract. In the example,
a const declaration cannot be abstract.

### Error: a _decl_ cannot be declared 'ghost'

```dafny
ghost module M {}
```

Only some kinds of declarations can be declared `ghost`, most often functions,
fields, and local declarations. In the example, a `module` may not be `ghost`.

