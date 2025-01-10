// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in .NET should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
#pragma warning disable CS0164 // This label has not been referenced
#pragma warning disable CS0162 // Unreachable code detected
#pragma warning disable CS1717 // Assignment made to same variable

namespace DefsCoverage {

  public partial class __default {
    public static void Expect(bool x)
    {
      if (!(x)) {
        throw new Dafny.HaltException("Backends/Rust/Dafny-compiler-rust-definitions-coverage.dfy(17,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
    }
    public static void Tests()
    {
      DefsCoverage.__default.Expect(object.Equals((Defs.AssignmentStatus.create_SurelyAssigned()).Join(Defs.AssignmentStatus.create_SurelyAssigned()), Defs.AssignmentStatus.create_SurelyAssigned()));
      DefsCoverage.__default.Expect(object.Equals((Defs.AssignmentStatus.create_NotAssigned()).Join(Defs.AssignmentStatus.create_NotAssigned()), Defs.AssignmentStatus.create_NotAssigned()));
      DefsCoverage.__default.Expect(object.Equals((Defs.AssignmentStatus.create_NotAssigned()).Join(Defs.AssignmentStatus.create_SurelyAssigned()), Defs.AssignmentStatus.create_Unknown()));
      DefsCoverage.__default.Expect(object.Equals((Defs.AssignmentStatus.create_SurelyAssigned()).Join(Defs.AssignmentStatus.create_NotAssigned()), Defs.AssignmentStatus.create_Unknown()));
      DefsCoverage.__default.Expect((object.Equals((Defs.AssignmentStatus.create_Unknown()).Join(Defs.AssignmentStatus.create_NotAssigned()), (Defs.AssignmentStatus.create_NotAssigned()).Join(Defs.AssignmentStatus.create_Unknown()))) && (object.Equals((Defs.AssignmentStatus.create_NotAssigned()).Join(Defs.AssignmentStatus.create_Unknown()), Defs.AssignmentStatus.create_Unknown())));
      DefsCoverage.__default.Expect((object.Equals((Defs.AssignmentStatus.create_Unknown()).Join(Defs.AssignmentStatus.create_SurelyAssigned()), (Defs.AssignmentStatus.create_SurelyAssigned()).Join(Defs.AssignmentStatus.create_Unknown()))) && (object.Equals((Defs.AssignmentStatus.create_SurelyAssigned()).Join(Defs.AssignmentStatus.create_Unknown()), Defs.AssignmentStatus.create_Unknown())));
      DefsCoverage.__default.Expect(object.Equals((Defs.AssignmentStatus.create_Unknown()).Join(Defs.AssignmentStatus.create_Unknown()), Defs.AssignmentStatus.create_Unknown()));
      DefsCoverage.__default.Expect((((object.Equals((Defs.AssignmentStatus.create_SurelyAssigned()).Then(Defs.AssignmentStatus.create_Unknown()), (Defs.AssignmentStatus.create_SurelyAssigned()).Then(Defs.AssignmentStatus.create_NotAssigned()))) && (object.Equals((Defs.AssignmentStatus.create_SurelyAssigned()).Then(Defs.AssignmentStatus.create_NotAssigned()), (Defs.AssignmentStatus.create_SurelyAssigned()).Then(Defs.AssignmentStatus.create_SurelyAssigned())))) && (object.Equals((Defs.AssignmentStatus.create_SurelyAssigned()).Then(Defs.AssignmentStatus.create_SurelyAssigned()), (Defs.AssignmentStatus.create_NotAssigned()).Then(Defs.AssignmentStatus.create_SurelyAssigned())))) && (object.Equals((Defs.AssignmentStatus.create_NotAssigned()).Then(Defs.AssignmentStatus.create_SurelyAssigned()), Defs.AssignmentStatus.create_SurelyAssigned())));
      DefsCoverage.__default.Expect((((object.Equals((Defs.AssignmentStatus.create_Unknown()).Then(Defs.AssignmentStatus.create_NotAssigned()), (Defs.AssignmentStatus.create_Unknown()).Then(Defs.AssignmentStatus.create_SurelyAssigned()))) && (object.Equals((Defs.AssignmentStatus.create_Unknown()).Then(Defs.AssignmentStatus.create_SurelyAssigned()), (Defs.AssignmentStatus.create_Unknown()).Then(Defs.AssignmentStatus.create_Unknown())))) && (object.Equals((Defs.AssignmentStatus.create_Unknown()).Then(Defs.AssignmentStatus.create_Unknown()), (Defs.AssignmentStatus.create_NotAssigned()).Then(Defs.AssignmentStatus.create_Unknown())))) && (object.Equals((Defs.AssignmentStatus.create_NotAssigned()).Then(Defs.AssignmentStatus.create_Unknown()), Defs.AssignmentStatus.create_Unknown())));
      DefsCoverage.__default.Expect(object.Equals((Defs.AssignmentStatus.create_NotAssigned()).Then(Defs.AssignmentStatus.create_NotAssigned()), Defs.AssignmentStatus.create_NotAssigned()));
      Dafny.ISequence<Dafny.Rune> _0_x;
      _0_x = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x");
      Dafny.ISequence<Dafny.Rune> _1_y;
      _1_y = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("y");
      DAST._IExpression _2_z;
      _2_z = DAST.Expression.create_Ident(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("z"));
      Dafny.ISequence<DAST._IStatement> _3_assigns__x;
      _3_assigns__x = Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_Assign(DAST.AssignLhs.create_Ident(_0_x), DAST.Expression.create_Ident(_1_y)));
      Dafny.ISequence<DAST._IStatement> _4_assigns__y;
      _4_assigns__y = Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_Assign(DAST.AssignLhs.create_Ident(_1_y), DAST.Expression.create_Ident(_0_x)));
      DAST._IExpression _5_cond;
      _5_cond = DAST.Expression.create_Ident(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cond"));
      Dafny.ISequence<DAST._IStatement> _6_unknown__x;
      _6_unknown__x = Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_If(_5_cond, _3_assigns__x, _4_assigns__y));
      Dafny.ISequence<DAST._IStatement> _7_surely__double__x;
      _7_surely__double__x = Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_If(_5_cond, _3_assigns__x, _3_assigns__x));
      Dafny.ISequence<DAST._IStatement> _8_call__to__x;
      _8_call__to__x = Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_Call(_2_z, DAST.CallName.create_SetBuilderAdd(), Dafny.Sequence<DAST._IType>.FromElements(), Dafny.Sequence<DAST._IExpression>.FromElements(), Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_0_x))));
      Dafny.ISequence<DAST._IStatement> _9_declare__x__again;
      _9_declare__x__again = Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_0_x, DAST.Type.create_Tuple(Dafny.Sequence<DAST._IType>.FromElements()), Std.Wrappers.Option<DAST._IExpression>.create_None()));
      DefsCoverage.__default.Expect(object.Equals(Defs.__default.DetectAssignmentStatus(_4_assigns__y, _0_x), Defs.AssignmentStatus.create_NotAssigned()));
      DefsCoverage.__default.Expect(object.Equals(Defs.__default.DetectAssignmentStatus(_3_assigns__x, _0_x), Defs.AssignmentStatus.create_SurelyAssigned()));
      DefsCoverage.__default.Expect(object.Equals(Defs.__default.DetectAssignmentStatus(_3_assigns__x, _1_y), Defs.AssignmentStatus.create_NotAssigned()));
      DefsCoverage.__default.Expect(object.Equals(Defs.__default.DetectAssignmentStatus(Dafny.Sequence<DAST._IStatement>.Concat(_3_assigns__x, _4_assigns__y), _1_y), Defs.AssignmentStatus.create_SurelyAssigned()));
      DefsCoverage.__default.Expect(object.Equals(Defs.__default.DetectAssignmentStatus(_6_unknown__x, _0_x), Defs.AssignmentStatus.create_Unknown()));
      DefsCoverage.__default.Expect(object.Equals(Defs.__default.DetectAssignmentStatus(_7_surely__double__x, _0_x), Defs.AssignmentStatus.create_SurelyAssigned()));
      DefsCoverage.__default.Expect(object.Equals(Defs.__default.DetectAssignmentStatus(_7_surely__double__x, _1_y), Defs.AssignmentStatus.create_NotAssigned()));
      DefsCoverage.__default.Expect(object.Equals(Defs.__default.DetectAssignmentStatus(_8_call__to__x, _0_x), Defs.AssignmentStatus.create_SurelyAssigned()));
      DefsCoverage.__default.Expect(object.Equals(Defs.__default.DetectAssignmentStatus(_8_call__to__x, _1_y), Defs.AssignmentStatus.create_NotAssigned()));
      DefsCoverage.__default.Expect(object.Equals(Defs.__default.DetectAssignmentStatus(Dafny.Sequence<DAST._IStatement>.Concat(_8_call__to__x, _4_assigns__y), _1_y), Defs.AssignmentStatus.create_SurelyAssigned()));
      DefsCoverage.__default.Expect(object.Equals(Defs.__default.DetectAssignmentStatus(Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_Labeled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("l"), _4_assigns__y)), _3_assigns__x), _1_y), Defs.AssignmentStatus.create_SurelyAssigned()));
      DefsCoverage.__default.Expect(object.Equals(Defs.__default.DetectAssignmentStatus(Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_Labeled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("l"), _3_assigns__x)), _4_assigns__y), _0_x), Defs.AssignmentStatus.create_SurelyAssigned()));
      DefsCoverage.__default.Expect(object.Equals(Defs.__default.DetectAssignmentStatus(Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_Labeled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("l"), _3_assigns__x)), _4_assigns__y), _0_x), Defs.AssignmentStatus.create_SurelyAssigned()));
      DefsCoverage.__default.Expect(object.Equals(Defs.__default.DetectAssignmentStatus(Dafny.Sequence<DAST._IStatement>.Concat(_9_declare__x__again, _3_assigns__x), _0_x), Defs.AssignmentStatus.create_NotAssigned()));
      DefsCoverage.__default.Expect(object.Equals(Defs.__default.DetectAssignmentStatus(Dafny.Sequence<DAST._IStatement>.Concat(_9_declare__x__again, _4_assigns__y), _1_y), Defs.AssignmentStatus.create_SurelyAssigned()));
      DefsCoverage.__default.Expect(object.Equals(Defs.__default.DetectAssignmentStatus(Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_Return(_2_z)), _3_assigns__x), _0_x), Defs.AssignmentStatus.create_NotAssigned()));
      DefsCoverage.__default.Expect(object.Equals(Defs.__default.DetectAssignmentStatus(Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_EarlyReturn()), _3_assigns__x), _0_x), Defs.AssignmentStatus.create_NotAssigned()));
      DefsCoverage.__default.Expect(object.Equals(Defs.__default.DetectAssignmentStatus(Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_JumpTailCallStart()), _3_assigns__x), _0_x), Defs.AssignmentStatus.create_NotAssigned()));
      DefsCoverage.__default.Expect(object.Equals(Defs.__default.DetectAssignmentStatus(Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_Print(_2_z)), _3_assigns__x), _0_x), Defs.AssignmentStatus.create_SurelyAssigned()));
      DefsCoverage.__default.Expect(object.Equals(Defs.__default.DetectAssignmentStatus(Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_Print(_2_z)), _3_assigns__x), _0_x), Defs.AssignmentStatus.create_SurelyAssigned()));
      DefsCoverage.__default.Expect(object.Equals(Defs.__default.DetectAssignmentStatus(Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_While(_2_z, Dafny.Sequence<DAST._IStatement>.FromElements())), _3_assigns__x), _0_x), Defs.AssignmentStatus.create_Unknown()));
      DefsCoverage.__default.Expect(object.Equals(Defs.__default.DetectAssignmentStatus(Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_If(_5_cond, _3_assigns__x, Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_If(_5_cond, _3_assigns__x, _4_assigns__y)))), _0_x), Defs.AssignmentStatus.create_Unknown()));
      DefsCoverage.__default.Expect(object.Equals(Defs.__default.DetectAssignmentStatus(Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_If(_5_cond, Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_If(_5_cond, Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_Return(_2_z)), Dafny.Sequence<DAST._IStatement>.FromElements())), _3_assigns__x), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_If(_5_cond, Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_If(_5_cond, Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_Return(_2_z)), Dafny.Sequence<DAST._IStatement>.FromElements())), _3_assigns__x), _4_assigns__y)))), _0_x), Defs.AssignmentStatus.create_Unknown()));
    }
    public static Dafny.ISequence<Dafny.Rune> IND { get {
      return RAST.__default.IND;
    } }
  }
} // end of namespace DefsCoverage