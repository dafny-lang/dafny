using System;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class FeatureDescriptionAttribute : Attribute {
  public readonly string Description;
  public readonly string ReferenceManualSection;
  public readonly string FootnoteIdentifier;
  public readonly string Footnote;


  public FeatureDescriptionAttribute(string description, string refmanSec, string footnoteIdentifier = null, string footnote = null) {
    Contract.Requires((footnoteIdentifier == null) == (footnote == null));
    Description = description;
    ReferenceManualSection = refmanSec;
    FootnoteIdentifier = footnoteIdentifier;
    Footnote = footnote;
  }

  public static FeatureDescriptionAttribute GetDescription(Feature feature) {
    var memberInfo = typeof(Feature).GetMember(feature.ToString()).First();
    return (FeatureDescriptionAttribute)GetCustomAttribute(memberInfo, typeof(FeatureDescriptionAttribute));
  }

  public static Feature ForDescription(string description) {
    var memberInfo = typeof(Feature).GetMembers().FirstOrDefault(memberInfo => {
      var attribute = (FeatureDescriptionAttribute)GetCustomAttribute(memberInfo, typeof(FeatureDescriptionAttribute));
      return attribute != null && attribute.Description == description;
    });
    if (memberInfo == null) {
      throw new Exception($"Unrecognized feature description: '{description}'");
    }

    return (Feature)Enum.Parse(typeof(Feature), memberInfo.Name);
  }
}

public enum Feature {
  [FeatureDescription("Unbounded integers", "sec-numeric-types")]
  UnboundedIntegers,

  [FeatureDescription("Real numbers", "sec-numeric-types")]
  RealNumbers,

  [FeatureDescription("Ordinals", "sec-ordinals")]
  Ordinals,

  [FeatureDescription("Function values", "sec-arrow-subset-types")]
  FunctionValues,

  [FeatureDescription("Iterators", "sec-iterator-types")]
  Iterators,

  [FeatureDescription("Collections with trait element types", "sec-collection-types")]
  CollectionsOfTraits,

  [FeatureDescription("External module names with only underscores", "sec-extern-decls")]
  AllUnderscoreExternalModuleNames,

  [FeatureDescription("Co-inductive datatypes", "sec-coinductive-datatypes")]
  Codatatypes,

  [FeatureDescription("Multisets", "sec-multisets")]
  Multisets,

  [FeatureDescription("Runtime type descriptors", null)]
  RuntimeTypeDescriptors,

  [FeatureDescription("Multi-dimensional arrays", "sec-multi-dimensional-arrays")]
  MultiDimensionalArrays,

  [FeatureDescription("Map comprehensions", "sec-map-comprehension-expression")]
  MapComprehensions,

  [FeatureDescription("Traits", "sec-trait-types")]
  Traits,

  [FeatureDescription("Let-such-that expressions", "sec-let-expression")]
  LetSuchThatExpressions,

  [FeatureDescription("Non-native numeric newtypes", "sec-newtypes")]
  NonNativeNewtypes,

  [FeatureDescription("Method synthesis", "sec-synthesize-attr")]
  MethodSynthesis,

  [FeatureDescription("External classes", "sec-extern-decls")]
  ExternalClasses,

  [FeatureDescription("Instantiating the `object` type", "sec-object-type")]
  NewObject,

  [FeatureDescription("`forall` statements that cannot be sequentialized", "sec-forall-statement",
    "compiler-feature-forall-note", @"'Sequentializing' a `forall` statement refers to compiling it directly to a series of nested loops
    with the statement's body directly inside. The alternative, default compilation strategy
    is to calculate the quantified variable bindings separately as a collection of tuples,
    and then execute the statement's body for each tuple.
    Not all `forall` statements can be sequentialized.")]
  NonSequentializableForallStatements,

  [FeatureDescription("Taking an array's length", "sec-array-type")]
  ArrayLength,

  [FeatureDescription("`m.Items` when `m` is a map", "sec-maps")]
  MapItems,

  [FeatureDescription("The /runAllTests option", "sec-test-attribute")]
  RunAllTests,

  [FeatureDescription("Integer range constraints in quantifiers (e.g. `a <= x <= b`)", "sec-quantifier-domains")]
  IntBoundedPool,

  [FeatureDescription("Exact value constraints in quantifiers (`x == C`)", "sec-quantifier-domains")]
  ExactBoundedPool,

  [FeatureDescription("Sequence displays of characters", "sec-sequence-displays",
    "compiler-sequence-display-of-characters-note", "This refers to an expression such as `['H', 'e', 'l', 'l', 'o']`, as opposed to a string literal such as `\"Hello\"`.")]
  SequenceDisplaysOfCharacters,

  [FeatureDescription("Type test expressions (`x is T`)", "sec-as-is-expression")]
  TypeTests,

  [FeatureDescription("Type test expressions on subset types", "sec-as-is-expression")]
  SubsetTypeTests,

  [FeatureDescription("Quantifiers", "sec-quantifier-expression")]
  Quantifiers,

  [FeatureDescription("Bitvector RotateLeft/RotateRight functions", "sec-bit-vector-types")]
  BitvectorRotateFunctions,

  [FeatureDescription("`for` loops", "sec-for-statement")]
  ForLoops,

  [FeatureDescription("`continue` statements", "sec-break-continue-statement")]
  ContinueStatements,

  [FeatureDescription("Assign-such-that statements with potentially infinite bounds", "sec-update-and-call-statement",
    "compiler-infinite-assign-such-that-note", @"This refers to assign-such-that statements with multiple variables,
    and where at least one variable has potentially infinite bounds.
    For example, the implementation of the statement `var x: nat, y: nat :| 0 < x && 0 < y && x*x == y*y*y + 1;`
    needs to avoid the naive approach of iterating all possible values of `x` and `y` in a nested loop.")]
  AssignSuchThatWithNonFiniteBounds,

  [FeatureDescription("Sequence update expressions", "sec-other-sequence-expressions")]
  SequenceUpdateExpressions,

  [FeatureDescription("Sequence constructions with non-lambda initializers", "sec-sequence-displays",
    "compiler-sequence-display-nolambda-note", @"Sequence construction expressions often use a direct lambda expression, as in `seq(10, x => x * x)`,
    but they can also be used with arbitrary function values, as in `seq(10, squareFn)`.")]
  SequenceConstructionsWithNonLambdaInitializers,

  [FeatureDescription("Externally-implemented constructors", "sec-extern-decls")]
  ExternalConstructors,

  [FeatureDescription("Auto-initialization of tuple variables", "sec-tuple-types")]
  TupleInitialization,

  [FeatureDescription("Subtype constraints in quantifiers", "sec-quantifier-expression")]
  SubtypeConstraintsInQuantifiers,

  [FeatureDescription("Tuples with more than 20 arguments", "#sec-compilation-built-ins")]
  TuplesWiderThan20,

  [FeatureDescription("Arrays with more than 16 dimensions", "#sec-compilation-built-ins")]
  ArraysWithMoreThan16Dims,

  [FeatureDescription("Arrow types with more than 16 arguments", "#sec-compilation-built-ins")]
  ArrowsWithMoreThan16Arguments,

  [FeatureDescription("Unicode chars", "#sec-characters")]
  UnicodeChars,

  [FeatureDescription("Converting values to strings", "sec-print-statement")]
  ConvertingValuesToStrings,

  // Only used internally for the DooBackend to skip legacy CLI tests
  [FeatureDescription("Legacy CLI without commands", "sec-dafny-commands")]
  LegacyCLI,

  [FeatureDescription("Separate compilation", "sec-compilation")]
  SeparateCompilation,

  [FeatureDescription("All built-in types in runtime library", "sec-compilation-built-ins")]
  BuiltinsInRuntime,

  [FeatureDescription("Execution coverage report", "sec-dafny-test")]
  RuntimeCoverageReport
}

public class UnsupportedFeatureException : Exception {

  public const string MessagePrefix =
    "Feature not supported for this compilation target: ";

  public readonly IOrigin Token;
  public readonly Feature Feature;

  public UnsupportedFeatureException(IOrigin token, Feature feature)
    : this(token, feature, MessagePrefix + FeatureDescriptionAttribute.GetDescription(feature).Description) {

  }

  public UnsupportedFeatureException(IOrigin token, Feature feature, string message) : base(message) {
    Token = token;
    Feature = feature;
  }
}



public class RecoverableUnsupportedFeatureException : UnsupportedFeatureException {

  public static readonly string MessageSuffix = ". To continue despite this issue, you can compile with the option --" +
                                       CommonOptionBag.EmitUncompilableCode.Name;
  public RecoverableUnsupportedFeatureException(IOrigin token, Feature feature)
    : base(token, feature, MessagePrefix + FeatureDescriptionAttribute.GetDescription(feature).Description + MessageSuffix) {
  }
}

public class UnsupportedInvalidOperationException : Exception {

  public readonly IOrigin Token;

  public UnsupportedInvalidOperationException(IOrigin token, string why) : base("Unsupported Invalid Operation: " + why) {
    Token = token;
  }
}