// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


// --------------- let-such-that ghost regressions ------------------------------

module LetSuchThatGhost {
  ghost predicate True<T>(t: T) { true }

  function F<T>(s: set<T>): int
    requires s != {}
  {
    // once, the RHS for p was (bogusly) considered ghost, which made p ghost,
    // which made this body illegal
    var p :=
      var e :| e in s;
      true;
    if p then 6 else 8
  }

  function G<T>(s: set<T>): int
    requires s != {}
  {
    // again, e and p are both non-ghost
    var p :=
      var e :| e in s;
      e == e;
    if p then 6 else 8
  }

  function H<T>(s: set<T>): int
    requires s != {}
  {
    // here, e is ghost, but p is still not
    var p :=
      var e :| e in s && True(e);
      true;
    if p then 6 else 8
  }

  function I<T>(s: set<T>): int
    requires s != {}
  {
    // here, e is ghost, and therefore so is p
    var p :=
      var e :| e in s && True(e);
      e == e;
    if p then 6 else 8  // error: p is ghost
  }
}

// --------------- hint restrictions in non-while loops ------------------------------

module HintRestrictionsOtherLoops {
  class C {
    ghost function F(): int
    {
      calc {
        6;
        { var x := 8;
          while
            modifies this  // error: cannot use a modifies clause on a loop inside a hint
          {
            case x != 0 => x := x - 1;
          }
        }
        6;
        { for i := 0 to 8
            modifies this  // error: cannot use a modifies clause on a loop inside a hint
          {
          }
        }
        6;
      }
      5
    }
  }
}

// --------------- regressions: types of arguments to fresh, unchanged, modifies, reads ------------------------------

module FrameTypes {
  // ----- fresh takes an expression as its argument

  method FreshArgumentType0(
    o: object,
    s: set<object>, ss: iset<object>,
    q: seq<object>,
    ms: multiset<object>,
    mp: map<object, int>, mp2: map<int, object>,
    im: imap<object, object>)
  {
    ghost var b;
    b := fresh(o);
    b := fresh(s);
    b := fresh(ss);
    b := fresh(q);
    b := fresh(ms); // error: wrong argument type for fresh
    b := fresh(mp); // error: wrong argument type for fresh
    b := fresh(mp2); // error: wrong argument type for fresh
    b := fresh(im); // error: wrong argument type for fresh
  }

  method FreshArgumentType1(x: int, s: set<bool>, ss: iset<bv8>, q: seq<int>) {
    ghost var b;
    b := fresh(x); // error: wrong argument type for fresh
    b := fresh(s); // error: wrong argument type for fresh
    b := fresh(ss); // error: wrong argument type for fresh
    b := fresh(q); // error: wrong argument type for fresh
  }

  method FreshArgumentType2(f: int -> int, g: int -> object, h: int -> set<object>, i: int -> iset<object>, j: int -> seq<object>, k: set<object> -> int) {
    ghost var b;
    b := fresh(f); // error: wrong argument type for fresh
    b := fresh(g); // error: wrong argument type for fresh
    b := fresh(h); // error: wrong argument type for fresh
    b := fresh(j); // error: wrong argument type for fresh
    b := fresh(k); // error: wrong argument type for fresh
  }

  // ----- unchanged, modifies, and reads take frame expressions as their arguments

  method UnchangedArgumentType0(
    o: object,
    s: set<object>, ss: iset<object>,
    q: seq<object>,
    ms: multiset<object>,
    mp: map<object, int>, mp2: map<int, object>,
    im: imap<object, object>)
  {
    ghost var b;
    b := unchanged(o);
    b := unchanged(s);
    b := unchanged(ss);
    b := unchanged(q);
    b := unchanged(ms);
    b := unchanged(mp); // error: wrong argument type for unchanged
    b := unchanged(mp2); // error: wrong argument type for unchanged
    b := unchanged(im); // error: wrong argument type for unchanged
  }

  method UnchangedArgumentType1(x: int, s: set<bool>, ss: iset<bv8>, q: seq<int>) {
    ghost var b;
    b := unchanged(x); // error: wrong argument type for unchanged
    b := unchanged(s); // error: wrong argument type for unchanged
    b := unchanged(ss); // error: wrong argument type for unchanged
    b := unchanged(q); // error: wrong argument type for unchanged
  }

  method UnchangedArgumentType2(
    f: int -> int,
    g: int -> object, h: int -> set<object>, i: int -> iset<object>, j: int -> seq<object>, k: set<object> -> int,
    l: bool -> multiset<object>, m: bool -> map<object, object>)
  {
    ghost var b;
    b := unchanged(f); // error: wrong argument type for unchanged
    b := unchanged(g); // error: wrong argument type for unchanged
    b := unchanged(h); // error: wrong argument type for unchanged
    b := unchanged(i); // error: wrong argument type for unchanged
    b := unchanged(j); // error: wrong argument type for unchanged
    b := unchanged(k); // error: wrong argument type for unchanged
    b := unchanged(l); // error: wrong argument type for unchanged
    b := unchanged(m); // error: wrong argument type for unchanged
  }

  method ModifiesArgumentType0(
    o: object,
    s: set<object>, ss: iset<object>,
    q: seq<object>,
    ms: multiset<object>,
    mp: map<object, int>, mp2: map<int, object>,
    im: imap<object, object>)
    modifies o
    modifies s
    modifies ss
    modifies q
    modifies ms
    modifies mp // error: wrong argument type for modifies
    modifies mp2 // error: wrong argument type for modifies
    modifies im // error: wrong argument type for modifies
  {
  }

  method ModifiesArgumentType1(x: int, s: set<bool>, ss: iset<bv8>, q: seq<int>)
    modifies x // error: wrong argument type for modifies
    modifies s // error: wrong argument type for modifies
    modifies ss // error: wrong argument type for modifies
    modifies q // error: wrong argument type for modifies
  {
  }

  method ModifiesArgumentType2(
    f: int -> int,
    g: int -> object, h: int -> set<object>, i: int -> iset<object>, j: int -> seq<object>, k: set<object> -> int,
    l: bool -> multiset<object>, m: bool -> map<object, object>)
    modifies f // error: wrong argument type for modifies
    modifies g // error: wrong argument type for modifies
    modifies h // error: wrong argument type for modifies
    modifies i // error: wrong argument type for modifies
    modifies j // error: wrong argument type for modifies
    modifies k // error: wrong argument type for modifies
    modifies l // error: wrong argument type for modifies
    modifies m // error: wrong argument type for modifies
  {
  }

  ghost predicate ReadsArgumentType0(
    o: object,
    s: set<object>, ss: iset<object>,
    q: seq<object>,
    ms: multiset<object>,
    mp: map<object, int>, mp2: map<int, object>,
    im: imap<object, object>)
    reads o
    reads s
    reads ss
    reads q
    reads ms
    reads mp // error: wrong argument type for reads
    reads mp2 // error: wrong argument type for reads
    reads im // error: wrong argument type for reads
  {
    true
  }

  ghost predicate ReadsArgumentType1(x: int, s: set<bool>, ss: iset<bv8>, q: seq<int>)
    reads x // error: wrong argument type for reads
    reads s // error: wrong argument type for reads
    reads ss // error: wrong argument type for reads
    reads q // error: wrong argument type for reads
  {
    true
  }

  ghost predicate ReadsArgumentType2(
    f: int -> int,
    g: int -> object, h: int -> set<object>, i: int -> iset<object>, j: int -> seq<object>, k: set<object> -> int,
    l: bool -> multiset<object>, m: bool -> map<object, object>)
    reads f // error: wrong argument type for reads
    reads g // error: a function must be to a collection of references
    reads h
    reads i
    reads j
    reads k // error: wrong argument type for reads
    reads l
    reads m // error: wrong argument type for reads
  {
    true
  }
}

module Continue0 {
  method BadTargetsLevels(a: int, b: int, c: int) {
    for i := 0 to 100 {
      for j := 0 to 100 {
        for k := 0 to 100 {
          if
          case k == a =>
            continue;
          case k == b =>
            break continue;
          case k == c =>
            break break continue;
          case k == a + b + c =>
            break break break continue; // error: too many levels
        }
      }
    }
  }

  method BadTargetsLabels(a: int, b: int, c: int) {
    label A:
    for i := 0 to 100 {
      label B0: label B1:
      for j := 0 to 100 {
        label C:
        for k := 0 to 100 {
          if
          case k == a =>
            continue C;
          case k == b =>
            continue B0;
          case k == b =>
            continue B1;
          case k == c =>
            continue A;
        }
      }
    }
  }

  method NonLoopLabels(a: int, b: int, c: int) {
    // the following labels are attached to BlockStmt's, not loops
    label X: {
      for i := 0 to 100 {
        label Y0: label Y1: {
          for j := 0 to 100 {
            label Z: {
              for k := 0 to 100 {
                if
                case k == a =>
                  continue X; // error: X is not a loop label
                case k == b =>
                  continue Y0; // error: Y0 is not a loop label
                case k == b =>
                  continue Y1; // error: Y1 is not a loop label
                case k == c =>
                  continue Z; // error: Z is not a loop label
              }
            }
          }
        }
      }
    }
  }

  method SimpleBadJumps0() {
    break; // error: cannot "break" from here
  }

  method SimpleBadJumps1() {
    continue; // error: cannot "continue" from here
  }

  method SimpleBadJumps2() {
    label X: {
      if
      case true => break; // error: cannot "break" from here
      case true => continue; // error: cannot "continue" from here
      case true => break X;
      case true => continue X; // error: X is not a loop label
    }
  }

  method GhostContinueAssertBy(ghost t: int, ghost u: nat)
  {
    label L:
    for i := 0 to 100 {
      assert true by {
        for j := 0 to 100 {
          if j == t {
            break;
          } else if j == u {
            continue;
          }
        }
        if
        case true => break; // error: cannot jump outside the assert-by
        case true => continue; // error: cannot jump outside the assert-by
        case true => break L; // error: cannot jump outside the assert-by
        case true => continue L; // error: cannot jump outside the assert-by
      }
    }
  }
}

module Continue1 {
  method GhostContinueLevels(ghost t: int, ghost u: nat)
  {
    var m := 0;
    for i := 0 to 100 {
      if i == t {
        // The following "continue" would pass the increment to m
        continue; // error: continue from ghost context must target a ghost loop
      }
      m := m + 1;
    }

    for i := 0 to 100 {
      m := m + 1;
      // The following "break" would potentially pass both increments to m
      if i == t {
        break; // error: break from ghost context must target a ghost loop
      }
      m := m + 1;
    }

    for i := 0 to 100 {
      if i == t {
        // Even though there's no statement in the loop body after this ghost if, the continue violates the rule
        continue; // error: continue from ghost context must target a ghost loop
      }
    }

    for i := 0 to 100 {
      for j := 0 to u {
        if i == t {
          continue; // fine
        }
      }
    }

    for i := 0 to 100 {
      for j := 0 to u {
        if i == t {
          break continue; // error: continue from ghost context must target a ghost loop
        }
      }
    }

    for i := 0 to 100 + u {
      for j := 0 to u {
        if i == t {
          break continue; // fine
        }
      }
    }
  }

  method GhostContinueLabels(ghost t: int, ghost u: nat)
  {
    label Outer:
    for i := 0 to 100 {
      label Inner:
      for j := 0 to u {
        if j == t {
          continue Inner; // fine
        } else if j == 20 + t {
          continue Outer; // error: continue from ghost context must target a ghost loop
        }
      }
    }
  }
}

module LabelRegressions {
  // The cases of if-case, while-case, and match statements are List<Statement>'s, which are essentially
  // a BlockStmt but without the curly braces. Each Statement in such a List can have labels, so
  // it's important to ResolveStatementWithLabels, not ResolveStatement. Alas, that was once not the
  // case (pun intended).
  // There's also something analogous going on in the Verifier, where lists of statements should call
  // TrStmtList, not just call TrStmt on every Statement in the List. (See method LabelRegressions()
  // in Test/comp/ForLoops-Compilation.dfy.)
  method IfCaseRegression() {
    if
    case true =>
      label Loop:
      for k := 0 to 10 {
        continue Loop;
        break Loop;
      }
  }

  method WhileCaseRegression() {
    while
    case true =>
      label Loop:
      for k := 0 to 10 {
        continue Loop;
        break Loop;
      }
  }

  method Match() {
    match (0, 0)
    case (_, _) =>
      label Loop:
      for k := 0 to 10 {
        break Loop;
        continue Loop;
      }
  }
}
