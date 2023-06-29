| Feature | C# | JavaScript | Go | Java | Python | C++ | Dafny Library (.doo) |
|-|-|-|-|-|-|-|-|
| [Unbounded integers](#sec-numeric-types) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [Real numbers](#sec-numeric-types) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [Ordinals](#sec-ordinals) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [Function values](#sec-arrow-subset-types) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [Iterators](#sec-iterator-types) |  X  |  X  |  X  |  |  X  |  |  X  |
| [Collections with trait element types](#sec-collection-types) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [External module names with only underscores](#sec-extern-decls) |  X  |  X  |  |  X  |  X  |  X  |  X  |
| [Co-inductive datatypes](#sec-coinductive-datatypes) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [Multisets](#sec-multisets) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [Runtime type descriptors](#) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [Multi-dimensional arrays](#sec-multi-dimensional-arrays) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [Map comprehensions](#sec-map-comprehension-expression) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [Traits](#sec-trait-types) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [Let-such-that expressions](#sec-let-expression) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [Non-native numeric newtypes](#sec-newtypes) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [Method synthesis](#sec-synthesize-attr) |  X  |  |  |  |  |  |  X  |
| [External classes](#sec-extern-decls) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [Instantiating the `object` type](#sec-object-type) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [`forall` statements that cannot be sequentialized](#sec-forall-statement)[^compiler-feature-forall-note] |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [Taking an array's length](#sec-array-type) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [`m.Items` when `m` is a map](#sec-maps) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [The /runAllTests option](#sec-test-attribute) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [Integer range constraints in quantifiers (e.g. `a <= x <= b`)](#sec-quantifier-domains) |  X  |  X  |  X  |  X  |  X  |  X  |  X  |
| [Exact value constraints in quantifiers (`x == C`)](#sec-quantifier-domains) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [Sequence displays of characters](#sec-sequence-displays)[^compiler-sequence-display-of-characters-note] |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [Type test expressions (`x is T`)](#sec-as-is-expression) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [Type test expressions on subset types](#sec-as-is-expression) |  |  |  |  |  |  |  X  |
| [Quantifiers](#sec-quantifier-expression) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [Bitvector RotateLeft/RotateRight functions](#sec-bit-vector-types) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [`for` loops](#sec-for-statement) |  X  |  X  |  X  |  X  |  X  |  X  |  X  |
| [`continue` statements](#sec-break-continue-statement) |  X  |  X  |  X  |  X  |  X  |  X  |  X  |
| [Assign-such-that statements with potentially infinite bounds](#sec-update-and-call-statement)[^compiler-infinite-assign-such-that-note] |  X  |  X  |  X  |  X  |  X  |  X  |  X  |
| [Sequence update expressions](#sec-other-sequence-expressions) |  X  |  X  |  X  |  X  |  X  |  X  |  X  |
| [Sequence constructions with non-lambda initializers](#sec-sequence-displays)[^compiler-sequence-display-nolambda-note] |  X  |  X  |  X  |  X  |  X  |  X  |  X  |
| [Externally-implemented constructors](#sec-extern-decls) |  X  |  |  |  X  |  X  |  X  |  X  |
| [Auto-initialization of tuple variables](#sec-tuple-types) |  X  |  X  |  X  |  X  |  X  |  X  |  X  |
| [Subtype constraints in quantifiers](#sec-quantifier-expression) |  X  |  X  |  X  |  X  |  X  |  X  |  X  |
| [Tuples with more than 20 arguments](#sec-tuple-types) |  |  X  |  X  |  |  X  |  X  |  X  |
| [Unicode chars](##sec-characters) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [Converting values to strings](##sec-print-statement) |  X  |  X  |  X  |  X  |  X  |  |  X  |
| [Legacy CLI without commands](###sec-dafny-commands) |  X  |  X  |  X  |  X  |  X  |  X  |  |

[^compiler-feature-forall-note]: 'Sequentializing' a `forall` statement refers to compiling it directly to a series of nested loops
    with the statement's body directly inside. The alternative, default compilation strategy
    is to calculate the quantified variable bindings separately as a collection of tuples,
    and then execute the statement's body for each tuple.
    Not all `forall` statements can be sequentialized; See [the implementation](https://github.com/dafny-lang/dafny/blob/master/Source/Dafny/Compilers/SinglePassCompiler.cs#L3493-L3528)
    for details.

[^compiler-sequence-display-of-characters-note]: This refers to an expression such as `['H', 'e', 'l', 'l', 'o']`, as opposed to a string literal such as `"Hello"`.

[^compiler-infinite-assign-such-that-note]: This refers to assign-such-that statements with multiple variables,
    and where at least one variable has potentially infinite bounds.
    For example, the implementation of the statement `var x: nat, y: nat :| 0 < x && 0 < y && x*x == y*y*y + 1;`
    needs to avoid the naive approach of iterating all possible values of `x` and `y` in a nested loop.

[^compiler-sequence-display-nolambda-note]: Sequence construction expressions often use a direct lambda expression, as in `seq(10, x => x * x)`,
    but they can also be used with arbitrary function values, as in `seq(10, squareFn)`.


