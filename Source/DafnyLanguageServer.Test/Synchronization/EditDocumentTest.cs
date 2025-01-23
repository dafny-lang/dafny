using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization;

[Collection("Sequential Collection")]
public class EditDocumentTest : ClientBasedLanguageServerTest {

  [Fact]
  public async Task SlowlyTypeFile() {
    var source = @"
module Bla {
  method Foo() { assume (0 decreases to 0);  }
}

module NoTypeArgs0 {


  datatype List<+T> = Nil | Cons(T, List)
  datatype Tree<+A,+B> = Leaf(A, B) | Node(Tree, Tree<B,A>)

  method DoAPrefix0<A, B, C>(xs: List) returns (ys: List<A>)
  {
    ys := xs;
  }

  method DoAPrefix1<A, B, C>(xs: List) returns (ys: List<B>)
  {
    ys := xs;  // error: List<B> cannot be assign to a List<A>
  }

  method DoAPrefix2<A, B, C>(xs: List) returns (ys: List<B>)
  {
    ys := xs;  // error: List<B> cannot be assign to a List<A>
  }

  ghost function FTree0(t: Tree): Tree
  {
    match t
    case Leaf(_,_) => t
    case Node(x, y) => x
  }

  ghost function FTree1(t: Tree): Tree
  {
    match t
    case Leaf(_,_) => t
    case Node(x, y) => y  // error: y does not have the right type
  }

  ghost function FTree2<A,B,C>(t: Tree): Tree<A,B>
  {
    t
  }
}

module NoTypeArgs1 {
  datatype Tree<A,B> = Leaf(A, B) | Node(Tree, Tree<B,A>)

  ghost function FTree3<T>(t: Tree): Tree<T,T>  // error: type of 't' does not have enough type parameters
  {
    t
  }
}

// ----------- let-such-that expressions ------------------------

module MiscMisc {
  method LetSuchThat(ghost z: int, n: nat)
  {
    var x: int;
    x := var y :| y < 0; y;  // fine for the resolver (but would give a verification error for not being deterministic)

    x := var w :| w == 2*w; w;  // fine (even for the verifier, this one)
    x := var w := 2*w; w;  // error: the 'w' in the RHS of the assignment is not in scope
    ghost var xg := var w :| w == 2*w; w;
  }
}

// ------------ quantified variables whose types are not inferred ----------

module NonInferredType {
  ghost predicate P<T>(x: T)

  method InferredType(x: int)
  {
    var t;
    assume forall z :: P(z) && z == t;
    assume t == x;  // this statement determines the type of t and z
  }

  method NonInferredType(x: int)
  {
    var t;  // error: the type of t is not determined
    assume forall z :: P(z) && z == t;  // error: the type of z is not determined
  }
}

// ------------ Here are some tests that lemma contexts don't allocate objects -------------

module GhostAllocationTests {
  class G { }
  iterator GIter() { }
  class H { constructor () }
  lemma GhostNew0()
    ensures exists o: G :: fresh(o)
  {
    var p := new G;  // error: lemma context is not allowed to allocate state
    p := new G;  // error: ditto
  }

  method GhostNew1(n: nat, ghost g: int) returns (t: G, z: int)
  {
    if n < 0 {
      z, t := 5, new G;  // fine
    }
    if n < g {
      var tt := new H();  // error: 'new' not allowed in ghost contexts
    }
  }

  method GhostNew2(ghost b: bool)
  {
    if (b) {
      var y := new GIter();  // error: 'new' not allowed in ghost contexts (and a non-ghost method is not allowed to be called here either)
    }
  }
}
module MoreGhostAllocationTests {
  class G { }
  method GhostNew3(n: nat) {
    var g := new G;
    calc {
      5;
      { var y := new G; }  // error: 'new' not allowed in lemma contexts
      2 + 3;
    }
  }
  ghost method GhostNew4(g: G)
    modifies g
  {
  }
}

module NewForallAssign {
  class G { }
  method NewForallTest(n: nat) {
    var a := new G[n];
    forall i | 0 <= i < n {
      a[i] := new G;  // error: 'new' is currently not supported in forall statements
  } }
}
module NewForallProof {
  class G { }
  method NewForallTest(n: nat) { var a := new G[n];
    forall i | 0 <= i < n ensures true { // this makes the whole 'forall' statement into a ghost statement
      a[i] := new G;  // error: proof-forall cannot update state (and 'new' not allowed in ghost contexts, but that's checked at a later stage)
  } }
}

// ------------------------- underspecified types ------------------------------

module UnderspecifiedTypes {
  method M(S: set<int>) {
    var n, p, T0 :| 12 <= n && n in T0 && 10 <= p && p in T0 && T0 <= S && p % 2 != n % 2;
    var T1 :| 12 in T1 && T1 <= S;
    var T2 :| T2 <= S && 12 in T2;

    var T3'0: set<int> :| 120 in T3'0;
    var T3'1: multiset<int> :| 120 in T3'1;
    var T3'2: map<int,bool> :| 120 in T3'2;
    var T3'3: seq<int> :| 120 in T3'3;
    var T3'4: bool :| 120 in T3'4;  // error: second argument to 'in' cannot be bool
    var T4 :| T4 <= S;
  }
}

module UnderspecifiedTypes' {
  method M() {
    var T3 :| 120 in T3;  // error: underspecified type
  }
}

// ------------------------- lemmas ------------------------------

module MiscLemma {
  class L { }

  // a lemma is allowed to have out-parameters, but not a modifies clause
  lemma MyLemma(x: int, l: L) returns (y: int)
    requires 0 <= x
    modifies l
    ensures 0 <= y
  {
    y := x;
  }
}
";
    await SlowlyTypeInSource(source, 200);
  }

  private async Task<TextDocumentItem> SlowlyTypeInSource(string source, int steps) {
    await SetUp(dafnyOptions => {
      dafnyOptions.Set(ProjectManager.UpdateThrottling, ProjectManager.DefaultThrottleTime);
    });
    var document = CreateAndOpenTestDocument("");

    var sourceParts = Regex.Split(source, @"(?<=[\}])");
    var stepSize = (int)Math.Ceiling(source.Length / (double)steps);

    var index = 0;
    var buffer = new TextBuffer("");
    foreach (var midPart in sourceParts) {
      for (var midIndex = 0; midIndex < midPart.Length; midIndex += stepSize) {
        var length = Math.Min(midPart.Length, midIndex + stepSize) - midIndex;
        var part = midPart.Substring(midIndex, length);
        var cursorIndex = index + part.Length;

        var position = buffer.FromIndex(index);
        buffer = buffer.ApplyTextChange(new TextDocumentContentChangeEvent() {
          Range = new Range(position, position),
          Text = part
        });
        ApplyChange(ref document, new Range(position, position), part);

        await WaitUntilResolutionFinished(document);
        var position2 = buffer.FromIndex(midIndex + length);
        var completionItems = await RequestCompletionAsync(document, position2);
        var hover = await RequestHover(document, position2);
        index = cursorIndex;
      }
    }

    return document;
  }

  private Task<Hover> RequestHover(TextDocumentItem documentItem, Position position) {
    return client.RequestHover(
      new HoverParams {
        TextDocument = documentItem.Uri,
        Position = position
      },
      CancellationToken
    );
  }

  private async Task<List<CompletionItem>> RequestCompletionAsync(TextDocumentItem documentItem, Position position) {
    // TODO at this time we do not set the context since it appears that's also the case when used within VSCode.
    var completionList = await client.RequestCompletion(
      new CompletionParams {
        TextDocument = documentItem.Uri,
        Position = position
      },
      CancellationToken
    ).AsTask();
    return completionList.OrderBy(completion => completion.Label).ToList();
  }

  public EditDocumentTest(ITestOutputHelper output, LogLevel dafnyLogLevel = LogLevel.Information) : base(output, dafnyLogLevel) {
  }
}