using System.Threading.Tasks;
using JetBrains.Annotations;
using Xunit;
using Xunit.Abstractions;

namespace DafnyPipeline.Test;

[Collection("Singleton Test Collection - FormatterForDatatypeDeclaration")]
public class FormatterForDatatypeDeclarationTest : FormatterBaseTest {
  [Fact]
  public async Task FormatterWorksForFinalSpaceAfterDatatype() {
    await FormatterWorksFor(@"
datatype Maybe<T> = None | Some(get: T)
");
  }

  [Fact]
  public async Task FormatWorksForDataTypes() {
    await FormatterWorksFor(@"
include ""test1""
include
  ""test2""

datatype Color =   Red
                   // Comment1
               |   /** Comment2 */
                   Green
               |   Blue

datatype Color2
  =   Red
      // Comment not docstring
  |   Green   |
      // Comment not docstring
      Blue
// Not blue docstring

// Comment here
datatype T =
    C1()
  | /** C2's comment */
    C2(a: int,
       b: int
       // comment on b
    )
    // C2's comment
  | C3(
      a: int,
      b: int
    , c: int)

datatype D =
  | D1(x: LongType1<
         P1,
         P2>
    )
  | D2( a: int,
        b: LongTypeX< map< int,
                           int>>
      , c: int
    )
  | D3(x: LongType< int,
                    int
       >)

");
  }

  [Fact]
  public async Task FormatterWorksForUniversalPatternShiftDatatypeParens() {
    await FormatterWorksFor(@"
newtype b17 = x | 0 <= x < (10 as bv8 << -1) as int
newtype b18 = x | 0 <= x < (10 as bv8 >> -1) as int

method UniversalPattern() {
  var f, _ := Capture(15);
  x := 1 << 2;
  x := 1 >> 3;
}

datatype T = Test
{
}
");
  }

  [Fact]
  public async Task FormatterWorksForIteratorsAfterDatatypes() {
    await FormatterWorksFor(@"
datatype MG5 =  MG5(ghost x: int, y: int := FG(x), ghost z: int := FC(x), w: int := FC(x)) // error: call to FC passes in a ghost expression
iterator        MG6(      x: int, y: int := FG(x), ghost z: int := FC(x), w: int := FC(x))
iterator        MG7(ghost x: int, y: int := FG(x), ghost z: int := FC(x), w: int := FC(x)) // error: call to FC passes in a ghost expression

iterator Iter0(x: int := y, y: int := 0)
  requires true
  yield requires true
{ }
");
  }


  [Fact]
  public async Task FormatterWorksForDatatypeWithVerticalBarAfterwardsOrOneLine() {
    await FormatterWorksFor(@"
datatype Single =
  SingleWithArguments(a: int)

datatype Lindgren =
  Pippi(Node) |
  Longstocking(seq<object>, Lindgren) |
  HerrNilsson

datatype Logical =
  Iff // And, Or, and Imp are in LazyOp
datatype Eq =
  EqCommon | NeqCommon
");
  }

  [Fact]
  public async Task FormatterWorksForDoublecomment() {
    await FormatterWorksFor(@"
datatype Test =
  | Zero
    /* Zero */
  | One
    // One
  | MOne /* -1 */
    // Minus one
  | Both /* 2 */
/* Two */
");
  }
  [Fact]
  public async Task FormatterWorksForSingleDatatypeConstructor() {
    await FormatterWorksFor(@"
datatype C = C(
  arg1: int,
  arg2: int
)
", reduceBlockiness: true);
    await FormatterWorksFor(@"
datatype C = C(
               arg1: int,
               arg2: int
             )
", reduceBlockiness: false);
  }

  public FormatterForDatatypeDeclarationTest([NotNull] ITestOutputHelper output) : base(output) {
  }
}
