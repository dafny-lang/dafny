<p></p> <!-- avoids duplicate title -->

# Collection Types

Value types are types which represent some information that does not depend on
the state of the heap. These values have a mathematical flair: they cannot be modified
once they are created. Examples include sequences and sets. You don't *change* a
set the way you might change an index into an array. Rather, to insert an element into
as set, you would construct the *union* of the original set and the singleton set
containing the new element. The old set is still around, of course. This lack of a dependence
on the heap makes value types especially useful in specification.

This is not to say that you can't update things with value types in them. Variables that contain
a value type can be updated to have a new value of that type. It is just that any other variables or
fields with the same set will keep their old value. Value types can contain references to
the heap, as in the ubiquitous `set<object>`. In this case, the information in the value type
is *which objects are in the set*, which does not depend on the values of any fields stored in
those objects, for example. Further, all of Dafny's value types can be stored in fields on the heap,
and used in real code in addition to specifications. Dafny's built in value types are sets, sequences, multisets, and maps.

For a complete guide to various collection types and their operations,
see the document on the [Dafny type system](http://leino.science/papers/krml243.html).
Note, if you want to use these types in an executing program and you
care about performance, use Dafny's `-optimize` option when compiling.


## Sets

Sets of various types form one of the core tools of verification for Dafny.
Sets represent an orderless collection of elements, without repetition. Like
sequences, sets are immutable value types. This allows them to be used easily
in annotations, without involving the heap, as a set cannot be modified once
it has been created. A set has the type:

<!-- %no-check -->
```dafny
  set<int>
```

for a set of integers, for example. In general, sets can be of almost any type, including objects. Concrete sets can be specified by using display notation:

<!-- %check-verify -->
```dafny
method m()
{
  var s1: set<int> := {}; // the empty set
  var s2 := {1, 2, 3}; // set contains exactly 1, 2, and 3
  assert s2 == {1,1,2,3,3,3,3}; // same as before
  var s3, s4 := {1,2}, {1,4};
}
```

The set formed by the display is the expected set, containing just
the elements specified. Above we also see that equality is defined
for sets. Two sets are equal if they have exactly the same elements.
New sets can be created from existing ones using the common set operations:

<!-- %check-verify -->
```dafny
method m ()
{
  var s1: set<int> := {};
  var s2 := {1, 2, 3};
  var s3, s4 := {1,2}, {1,4};
  assert s2 + s4 == {1,2,3,4}; // set union
  assert s2 * s3 == {1,2} && s2 * s4 == {1}; // set intersection
  assert s2 - s3 == {3}; // set difference
}
```

Note that because sets can only contain at most one of each element,
the union does not count repeated elements more than once. These
operators will result in a finite set if both operands are finite,
so they cannot generate an infinite set. Unlike the arithmetic
operators, the set operators are always defined. In addition to set
forming operators, there are comparison operators with their usual
meanings:

<!-- %check-verify -->
```dafny
method m()
{
  assert {1} <= {1, 2} && {1, 2} <= {1, 2}; // subset
  assert {} < {1, 2} && !({1} < {1}); // strict, or proper, subset
  assert !({1, 2} <= {1, 4}) && !({1, 4} <= {1}); // not subsets
  assert {1, 2} == {1, 2} && {1, 3} != {1, 2}; // equality and non-equality
}
```

Sets, like sequences, support the `in` and `!in` operators, to
test element membership. For example:

<!-- %check-verify-warn Sets.W1.expect -->
```dafny
method m()
{
  assert 5 in {1,3,4,5};
  assert 1 in {1,3,4,5};
  assert 2 !in {1,3,4,5};
  assert forall x: int :: x !in {};
}
```

Sets are used in several annotations, including reads and modifies
clauses. In this case, they can be sets of a specific object type
(like `Nodes` in a linked list), or they can be sets of the
generic reference type `object`. Despite its name, this can point to
any object or array. This is useful to bundle up all of the locations
that a function or method might read or write when they can be different types.


When used in a decreases clause, sets are ordered by subset. This is unlike
sequences, which are ordered by length only. In order for sets to be used in
decreases clauses, the successive values must be "related" in some sense, which
usually implies that they are recursively calculated, or similar.
This requirement comes from the fact that there is no way to get the cardinality
(size) of a set in Dafny. The size is guaranteed to be some finite natural, but it is inaccessible.
You can test if the set is empty by comparing it to the empty set (`s == {}` is true if and
only if `s` has no elements.)



A useful way to create sets is using a set comprehension. This defines a new set by including `f(x)`
in the set for all `x` of type `T` that satisfy `p(x)`:

<!-- %no-check -->
```dafny
  set x: T | p(x) :: f(x)
```

This defines a set in a manner reminiscent of a universal quantifier (`forall`). As with quantifiers,
the type can usually be inferred. In contrast to quantifiers, the bar syntax (`|`) is required to
separate the predicate (`p`) from the bound variable (`x`). The type of the elements of the resulting set is
the type of the return value of `f(x)`. The values in the constructed set are the return values of `f(x)`:
`x` itself acts only as a bridge between the predicate `p` and the function `f`. It
usually has the same type as the resulting set, but it does not need to. As an example:

<!-- %check-verify-warn Sets.W2.expect -->
```dafny
method m()
{
  assert (set x | x in {0,1,2} :: x + 0) == {0,1,2};
}
```

If the function is the identity, then the expression can be written with a particularly nice form:

<!-- %check-verify-warn Sets.W3.expect -->
```dafny
method m()
{
  assert (set x | x in {0,1,2,3,4,5} && x < 3) == {0,1,2};
}
```

General, non-identity functions in set comprehensions confuse Dafny easily. For example,
the following is true, but Dafny cannot prove it:

<!-- %check-verify  Sets.1.expect -->
```dafny
method m()
{
  // assert {0*1, 1*1, 2*1} == {0,1,2};  // include this assertion as a lemma to prove the next line
  assert (set x | x in {0,1,2} :: x * 1) == {0,1,2};
}
```

This mechanism has the potential to create an infinite set, which is not allowed in Dafny.
To prevent this, Dafny employs heuristics in an attempt to prove that that the resulting
set will be finite. When creating sets of integers, this can be done by bounding the integers
in at least one clause of the predicate (something like `0 <= x < n`). Requiring a bound
variable to be in an existing set also works, as in `x in {0,1,2}` from above. This works
only when the inclusion part is conjuncted (`&&`'ed) with the rest of the predicate, as it
needs to limit the possible values to consider.

## Sequences

Sequences are a built-in Dafny type representing an ordered
list. They can be used to represent many ordered collections, including lists,
queues, stacks, etc. Sequences are an immutable value type: they cannot be
modified once they are created. In this sense, they are similar to strings in
languages like Java and Python, except they can be sequences of arbitrary
types, rather than only characters. Sequence types are written:

<!-- %no-check -->
```dafny
  seq<int>
```

for a sequence of integers, for example. 
For example, this function takes a sequence as a parameter:

<!-- %check-verify -->
```dafny
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

<!-- %check-verify -->
```dafny
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

<!-- %no-check -->
```dafny
  s[i..j]
```

where `0 <= i <= j <= |s|`. Dafny will enforce these index bounds. The resulting sequence
will have exactly `j-i` elements, and will start with the element `s[i]` and
continue sequentially through the sequence, if the result is non-empty. This
means that the element at index `j` is excluded from the slice, which mirrors the
same half-open interval used for regular indexing.

Sequences can also be constructed from their elements, using *display notation*:

<!-- %check-verify -->
```dafny
method m() {
  var s := [1, 2, 3];
}
```

Here we have a integer sequence variable in some imperative
code containing the elements 1, 2, and 3. Type inference has been used here to
determine that the sequence is one of integers. This notation allows us to
construct empty sequences and singleton sequences:

<!-- %no-check -->
```dafny
  [] // the empty sequence, which can be a sequence of any type
  [true] // a singleton sequence of type seq<bool>
```

Slice notation and display notation can be used to check
properties of sequences:

<!-- %check-verify -->
```dafny
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

<!-- %check-verify -->
```dafny
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
side and inclusive on the other, the `i`th element appears in the concatenation
exactly once, as it should. Note that the concatenation operation is
associative:

<!-- %check-verify -->
```dafny
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

<!-- %check-verify -->
```dafny
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

<!-- %check-verify -->
```dafny
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

<!-- %check-verify -->
```dafny
method m()
{
  var s := [1,2,3,4];
  assert s[2 := 6] == [1,2,6,4];
}
```

Of course, the index `i` has to be an index into the array. This syntax is just
a shortcut for an operation that can be done with regular slicing and access operations.
Can you fill in the code below that does this?

<!-- %check-verify -->
```dafny
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

<!-- %check-verify -->
```dafny
method m()
{
  var a := new int[][42,43,44]; // 3 element array of ints
  a[0], a[1], a[2] := 0, 3, -1;
  var s := a[..];
  assert s == [0, 3, -1];
}
```

To extract just part of the array, the bounds can be given just like in a regular
slicing operation:

<!-- %check-verify -->
```dafny
method m()
{
  var a := new int[][42,43,44]; // 3 element array of ints
  a[0], a[1], a[2] := 0, 3, -1;
  assert a[1..] == [3, -1];
  assert a[..1] == [0];
  assert a[1..2] == [3];
}
```

Because sequences support `in` and `!in`, this operation gives us
an easy way to express the "element not in array" property, turning:

<!-- %no-check -->
```dafny
forall k :: 0 <= k < a.Length ==> elem != a[k]
```

into:

<!-- %no-check -->
```dafny
elem !in a[..]
```

Further, bounds are easily included:

<!-- %no-check -->
```dafny
forall k :: 0 <= k < i ==> elem != a[k]
```

is the same as

<!-- %no-check -->
```dafny
elem !in a[..i]
```

## Multisets

Multisets are like sets in almost every way, except that they keep track of how
many copies of each element they have. This makes them particularly useful for storing
the set of elements in an array, for example, where the number of copies of each element is the same.
The multiset type is almost the same as sets:

<!-- %no-check -->
```dafny
  multiset<int>
```

Similarly, to give a multiset literal, you write curly braces, except preceeded by the `multiset` keyword:

<!-- %no-check -->
```dafny
  multiset{3,5,7,3}
```

Be careful! `multiset({3,3})` is not a multiset literal with two 3's. The braces have to be
adjacent to the keyword for it to work as you would expect.

Like sets, multisets are unordered. However, because they keep track of how many of each
element they have, the above literal actually has two 3's in it.

Many of the operations defined on sets are also available for multisets. You can use `in` to
test whether some element is in a multiset (in means that it has at least one member of the given value). Multiset sum
(`+`) means take elements from both, and add them up. So if one multiset has two 3's and another has one, then their multiset
sum would have a total of three 3's. The multiset difference (`-`) works similarly, in that the multiplicity of the elements
(i.e. how many of each element are in the multiset) matters. So the following:

<!-- %check-verify -->
```dafny
method test()
{
  assert (multiset{1,1,1} - multiset{1,1}) == multiset{1};
}
```

holds, because we start with three 1's, then take away two to be left with one.

Multiset disjoint (`!!`) works as expected: it is true if and only if the two multisets have no members in common.
Also, two multisets are equal if they have exactly the same count of each element.


Finally, multisets can be created from both sequences and sets by using multiset with parentheses:

<!-- %check-verify -->
```dafny
method test()
{
  assert multiset([1,1]) == multiset{1,1};
  assert multiset({1,1}) == multiset{1};
}
```

Both of these assertions are correct because the multiset of a sequence considers each element seperately,
whereas a set only has at most one of each element. Dafny lets you write `{1,1}`, but this is the same
as `{1}`, because duplicates are ignored. Thus when making a multiset from a set, each element in the
multiset will have multiplicity exactly one. Making multisets from sequences is particularly useful, as when
combined with the slice of an array, allows you to talk about the set of elements in an array (as in `multiset(a[..])`),
which is very helpful in verifying sorting algorithms and some data structures.


## Maps

Maps in Dafny represent *associative arrays*. Unlike the other types so far, they take two types:
the *key* type, and the *value* type.
Values can be retrieved, or looked up, based on the key. A map type is written:

<!-- %no-check -->
```dafny
  map<U, V>
```

where `U` is the key type and `V` is the value type. For example, we can have a map from integers
to integers as `map<int, int>`. A literal of this type might be `map[4 := 5, 5 := 6]`. This map
associates 4 with 5 and 5 with 6. You can access the value for a given key with `m[key]`, if `m` is a
map and `key` is a key. So we could write:

<!-- %check-verify -->
```dafny
method test() {
  var m := map[4 := 5, 5 := 6];
  assert m[4] == 5;
}
```

This is because 4, taken as a key into `m`, produces 5. We also know that `m[5] == 6`, as this is
the other mapping.

Each map has a *domain*, which are all of the keys for which that map has values. It is not well formed
to ask a map for keys outside its domain. So `m[7]` doesn't make any sense, because `m` does not define
any value for 7. To test whether a key is in the domain of a map, you can use the `in` operator. For example,
`4 in m` and `5 in m`, but `7 !in m`. With quantifiers, you can say that the domain is some set, as
in `forall i :: i in m <==> 0 <= i < 100` (which is true when `m`'s domain is exactly the numbers 0-99).
In addition, two maps are disjoint (`!!`) if their domains taken as sets are disjoint.


If `m` is a map, then `m[i := j]` is a new map which is the result of adding `i` to the domain of `m` and
then associating the key `i` with the value `j`. If `i` already had a value, then it is overridden in
the new map. This also means that when using map literals, it is permissible to repeat a key, but then the first value will be
overridden. So `map[3 := 5, 3 := 4] == map[3 := 4]`. Note that two maps are equal if they have the same domain, and they
map equal keys to equal values. Also, the domain of a map must always be finite.

Like sets, maps have a map comprehension. The syntax is almost the same as for sets:

<!-- %no-check -->
```dafny
map i: T | p(i) :: f(i)
```

The difference is that `i` is the key, and it is mapped to `f(i)`. `p(i)` is used to determine what the domain
of the new map is. So:

<!-- %check-verify -->
```dafny
method test() {
  var m := map i | 0 <= i < 10 :: 2*i;
}
```

is a map which takes the numbers 0-9 to their doubles. This is also how you can remove a key from a map. For example, this expression
removes the key 3 from an `int` to `int` map `m`:

<!-- %check-verify -->
```dafny
method test() {
  var m := map[3 := 5, 4 := 6, 1 := 4];
  var l := map i | i in m && i != 3 :: m[i];
  assert l == map[4:= 6, 1 := 4];
}
```
