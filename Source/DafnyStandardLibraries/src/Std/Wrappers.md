
## The `Wrappers` module

The Wrappers module holds some
simple datatypes to support common patterns, such as optional values or the result of operations that can fail.
These are particularly useful with Dafny's update-with-failure `:-` operator.

Any user datatype can serve this purpose, as long as it has an `IsFailure?` predicate 
(in which case it is known as a [_failure-compatible_](https://dafny.org/latest/DafnyRef/DafnyRef#sec-failure-compatible-types) type --- an FC-type). 

In this library module Dafny defines three such types:
- `Option<R>` - which is either `Some` with a value of type `T` or a `None` with no information
- `Outcome<E>` - which is either `Pass` with no information or `Fail` with an error value of type `E` (often a `string`) 
- `Result<R,E>` - which is either `Success` with a value of type `R` or `Failure` with error value of type `E`

### Option

Consider this routine that looks for a value in a sequence, beginning at position `k`, returning its index:
<!-- %check-verify %save tmp-find.dfy -->
```dafny
import opened Std.Wrappers
function Find<T(==)>(s: seq<T>, k: int, value: T): (r: Option<int>)
  requires 0 <= k <= |s|
  ensures  r.Some? ==> 0 <= r.Extract() < |s| && s[r.Extract()] == value
  ensures  r.None? ==> forall i | k <= i < |s| :: s[i] != value
  decreases |s| - k
{
  if k >= |s| then None else if s[k] == value then Some(k) else Find(s, k+1, value)
}
```

It could be used in a method like this

<!-- %check-resolve %use tmp-find.dfy -->
```dafny
method m(s: seq<int>) returns (r: Option<int>) {
  var value: int;
  // do various calculations
  var index: int :- Find(s, 0, value);
  // more calculations
  return Some(value);
}
```

You could just capture the result of `Find` using `:=` in a `Option<int>` variable and inspect it. But if the `None` condition is 
generally a rare error, it is easy to forget to always check that each operation was successful. Instead, the `:-` changes the 
control flow so that if a `None` value is returned from `Find`, the method immediately aborts, with the output value (which has
the `Option<int>` type) getting that returned `None` value. So this operates something like exceptions.
See the [reference manual](https://dafny.org/latest/DafnyRef/DafnyRef#sec-update-with-failure-statement)
for more on the similarities and differences with exceptions.

### Outcome

`Outcome` is a variation on these types in which we mostly just care whether the operations succeeded or failed.
It has no place to carry a value, just information about the error. 

This datatype is most useful in conjunction with functions that check conditions at runtime, such as `Need`. 
This function takes a boolean condition and a value `e` of an error type `E` and returns an
`Outcome<E>` value: `Pass` if the condition is true, `Fail(e)` if it is false. 
It provides a simple runtime check that does not abort the program (like the `expect` statement does);
rather it propagates the Dafny equivalent of an exception.

<!-- %no-check -->
```dafny
:- Need(IsEverythingOK(), "failure in method M");
```

This datatype is also useful when used with methods with multiple return values.
Then the first return value can be an `Outcome` to indicate success or failure, with the other outputs returning 
appropriate values in the success situation.

For example, if we have this method
<!-- %check-resolve %save tmp-matches.dfy -->
```dafny
import opened Std.Wrappers
method FindAllMatches<T(==)>(s: seq<T>, value: T) returns (status: Outcome<string>, matches: seq<int>)
```
we can call it as
<!-- %check-resolve %use tmp-matches.dfy -->
```dafny
method m(s: seq<int>, value: int) returns (r: Outcome<string>) {
  var matches :- FindAllMatches(s, value);
}
```

Notice that there is no left-hand-side for the first out-parameter. It does not carry a value: if the value is a `Fail`, the control
flow will abruptly return; if is is a `Pass`, the first out-parameter is then discarded and the second is assigned to the remaining LHS.
An `Outcome` serves as an automatically-checked error mechanism.

### Result

A `Result` carries both a success value and failure information, with two separate, specifiable types. Its use is then very similar to `Option`.

### Combining different failure-compatible types in expressions

The example given for `Option` above is legal Dafny code because the output of the caller method `m` has the same type
(`Option<int>`) as the output of the callee function `Find`. But what if it does not? You may be writing code that generally uses, say, `Result`,
but happens to be using code supplied by someone else that returns an `Outcome`.

When values of these types are used in expressions, the library types offer means to convert among them: each type has instance functions that
convert to values of the other types. For example, we can rewrite the example above this way:

<!-- %check-verify %save tmp-find.dfy -->
```dafny
import opened Std.Wrappers

function Find<T(==)>(s: seq<T>, k: int, value: T): (r: Option<int>)
  requires 0 <= k <= |s|
  ensures  r.Some? ==> k <= r.Extract() < |s|
  ensures  r.Some? ==> s[r.Extract()] == value
  ensures  r.None? ==> forall i | k <= i < |s| :: s[i] != value
  decreases |s| - k
{
  if k >= |s| then None else if s[k] == value then Some(k) else Find(s, k+1, value)
}

method m(s: seq<int>) returns (r: Result<int,string>) {
  var value: int := *;
  // do various calculations
  var index: int :- Find(s, 0, value).ToResult("not found");
  // more calculations
  return Success(index);
}
```

Here we used the `ToResult` function of `Option` to convert the result value to a `Result`. There are similar `ToOutcome` and `ToOption` functions in each type.

But what if we need to convert to some custom FC-type?
Each datatype comes with a `Map` function, which can be given as an argument a function that converts from
one FC-type to another. For example, we could rewrite the above as

<!-- %no-check -->
```dafny
  var index: int :- Find(s, 0, value).
     Map((o: Option<int>) => match o case Some(v) => Success(v) 
                                     case None => Failure("not found") );
```

An alternative is to write
<!-- %no-check -->
```dafny
  var convert := match o case Some(v) => Success(v)
                                     case None => Failure("not found") );
  var index: int :- convert(Find(s, 0, value));
```

### Combining different failure-compatible types in methods

The conversion functions used in the last section work syntactically because we had boxed values that were returned by expressions (function calls), to which the conversion functions could
be applied. When a FC-value is returned by a method there is no place to call such a conversion function: the return value of the method must be captured by either `:=` or `:-`.
So some new syntax will be needed --- what this will be is under design and discussion.

The workaround, however, is straightforward: just capture the results using `:=` and make the conversion directly. Here the is example above restated using a method.

<!-- %check-verify -->
```dafny
import opened Std.Wrappers

method Find<T(==)>(s: seq<T>, k: int, value: T) returns (r: Option<int>, v: T)
  requires 0 <= k <= |s|
  ensures  r.Some? ==> k <= r.Extract() < |s|
  ensures  r.Some? ==> s[r.Extract()] == value
  ensures  r.None? ==> forall i | k <= i < |s| :: s[i] != value
  decreases |s| - k
{
  if k >= |s| {
    return None, value;
  } else if s[k] == value {
    return Some(k), value;
  } else {
    r, v := Find(s, k+1, value);
    return r, v;
  }
}

method m(s: seq<int>) returns (r: Result<int,string>) {
  var value: int := *;
  // do various calculations
  var maybeIndex, v := Find(s, 0, value);
  var index :- maybeIndex.ToResult("not found"); // or f(maybeIndex)
  // more calculations
  return Success(index);
}
```

Besides the extra writing, the caution for this workaround is the the programmer must remember to catch and convert the error result.
However, if one just uses `:-` in this case, it will either be OK (because the types match) or it will give a type error (because they don't match).
So it does not silently do something unexpected.

