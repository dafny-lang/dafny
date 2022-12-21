<p></p> <!-- avoids duplicate title -->

# Sequences

Sequences are a built-in Dafny type representing an ordered
list. They can be used to represent many ordered collections, including lists,
queues, stacks, etc. Sequences are an immutable value type: they cannot be
modified once they are created. In this sense, they are similar to strings in
languages like Java and Python, except they can be sequences of arbitrary
types, rather than only characters. Sequence types are written:

```dafny <!-- %no-check -->
seq<int>
```

for a sequence of integers, for example.
For example, this function takes a sequence as a parameter:

```dafny <!-- %check-verify -->
predicate sorted(s: seq<int>)
{
  forall i,j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}
```

The length of a sequence is written `|s|`, as in the above quantifier. Specific elements of a
sequence are accessed using the same square bracket syntax as arrays. Note also
that the function does not require a reads clause to access the sequence. That
is because sequences are not stored on the heap; they are values, so functions
don't need to declare when they are accessing them. The most powerful property
of sequences is the fact that annotations and functions can create and
manipulate them. For example, another way of expressing sorted-ness is
recursive: if the first element is smaller than the rest, and the rest is
sorted, then the whole array is sorted:

```dafny <!-- %check-verify -->
predicate sorted2(s: seq<int>)
{
  0 < |s| ==> (forall i :: 0 < i < |s| ==> s[0] <= s[i]) &&
               sorted2(s[1..])
}
```


The notation `s[1..]`
is *slicing* the sequence. It means starting at the first element, take
elements until you reach the end. This does not modify s, as sequences are
immutable. Rather, it creates a new sequence which has all the same elements in
the same order, except for the first one. This is similar to addition of
integers in that the original values are not changed, just new ones created.
The slice notation is:

```dafny <!-- %no-check -->
  s[i..j]
```

where `0 <= i <= j <= |s|`. Dafny will enforce these index bounds. The resulting sequence
will have exactly `j-i` elements, and will start with the element `s[i]` and
continue sequentially through the sequence, if the result is non-empty. This
means that the element at index `j` is excluded from the slice, which mirrors the
same half-open interval used for regular indexing.

Sequences can also be constructed from their elements, using *display notation*:

```dafny <!-- %check-verify -->
method m() {
  var s := [1, 2, 3];
}
```

Here we have a integer sequence variable in some imperative
code containing the elements 1, 2, and 3. Type inference has been used here to
determine that the sequence is one of integers. This notation allows us to
construct empty sequences and singleton sequences:

```dafny <!-- %no-check -->
  [] // the empty sequence, which can be a sequence of any type
  [true] // a singleton sequence of type seq<bool>
```

Slice notation and display notation can be used to check
properties of sequences:

```dafny <!-- %check-verify -->
method m()
{
  var s := [1, 2, 3, 4, 5];
  assert s[|s|-1] == 5; //access the last element
  assert s[|s|-1..|s|] == [5]; //slice just the last element, as a singleton
  assert s[1..] == [2, 3, 4, 5]; // everything but the first
  assert s[..|s|-1] == [1, 2, 3, 4]; // everything but the last
  assert s == s[0..] == s[..|s|] == s[0..|s|]; // the whole sequence
}
```

By far the most common operations on sequences are getting
the first and last elements, and getting everything but the first or last
element, as these are often used in recursive functions, such as `sorted2`
above. In addition to being deconstructed by being accessed or sliced, sequences
can also be concatenated, using the plus (`+`) symbol:

```dafny <!-- %check-verify -->
method m()
{
  var s := [1, 2, 3, 4, 5];
  assert [1,2,3] == [1] + [2,3];
  assert s == s + [];
  assert forall i :: 0 <= i <= |s| ==> s == s[..i] + s[i..];
}
```

The last assertion gives a relationship between
concatenation and slicing. Because the slicing operation is exclusive on one
side and inclusive on the other, the element appears in the concatenation
exactly once, as it should. Note that the concatenation operation is
associative:

```dafny <!-- %check-verify -->
method m()
{
  assert forall a: seq<int>, b: seq<int>, c: seq<int> ::
         (a + b) + c == a + (b + c);
}
```

but that the Z3 theorem prover will not realize this unless
it is prompted with an assertion stating that fact (see Lemmas/Induction for
more information on why this is necessary).

Sequences also support the `in` and `!in` operators, which test
for containment within a sequence:

```dafny <!-- %check-verify -->
method m()
{
  var s := [1, 2, 3, 4, 5];
  assert 5 in s;
  assert 0 !in s;
}
```

This also allows us an alternate means of quantifying over
the elements of a sequence, when we don't care about the index. For example, we
can require that a sequence only contains elements which are indices into the
sequence:

```dafny <!-- %check-verify -->
method m()
{
  var s := [2,3,1,0];
  assert forall i :: i in s ==> 0 <= i < |s|;
}
```

This is a property of each individual element of the
sequence. If we wanted to relate multiple elements to each other, we would need
to quantify over the indices, as in the first example.

Sometimes we would like to emulate the updatable nature of
arrays using sequences. While we can't change the original sequence, we can
create a new sequence with the same elements everywhere except for the updated
element:

```dafny <!-- %check-verify -->
method m()
{
  var s := [1,2,3,4];
  assert s[2 := 6] == [1,2,6,4];
}
```

Of course, the index `i` has to be an index into the array. This syntax is just
a shortcut for an operation that can be done with regular slicing and access operations.
Can you fill in the code below that does this?

```dafny <!-- %check-verify -->
function update(s: seq<int>, i: int, v: int): seq<int>
  requires 0 <= i < |s|
  ensures update(s, i, v) == s[i := v]
{
  s[..i] + [v] + s[i+1..]
  // This works by concatenating everything that doesn't
  // change with the singleton of the new value.
}
```

You can also form a sequence from the elements of an array. This is done
using the same "slice" notation as above:

```dafny <!-- %check-verify -->
method m()
{
  var a := new int[][42, 43, 44]; // 3 element array of ints
  a[0], a[1], a[2] := 0, 3, -1;
  var s := a[..];
  assert s == [0, 3, -1];
}
```

To extract just part of the array, the bounds can be given just like in a regular
slicing operation:

```dafny <!-- %check-verify -->
method m()
{
  var a := new int[][42, 43, 44]; // 3 element array of ints
  a[0], a[1], a[2] := 0, 3, -1;
  assert a[1..] == [3, -1];
  assert a[..1] == [0];
  assert a[1..2] == [3];
}
```

Because sequences support `in` and `!in`, this operation gives us
an easy way to express the "element not in array" property, turning:

```dafny <!-- %no-check -->
forall k :: 0 <= k < a.Length ==> elem != a[k]
```

into:

```dafny <!-- %no-check -->
elem !in a[..]
```

Further, bounds are easily included:
```dafny <!-- %no-check -->
forall k :: 0 <= k < i ==> elem != a[k]
```

is the same as

```dafny <!-- %no-check -->
elem !in a[..i]
```
