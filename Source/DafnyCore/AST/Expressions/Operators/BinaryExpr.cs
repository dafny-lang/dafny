using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class BinaryExpr : Expression, ICloneable<BinaryExpr>, ICanFormat {
  public enum Opcode {
    Iff,
    Imp,
    Exp, // turned into Imp during resolution
    And,
    Or,
    Eq,
    Neq,
    Lt,
    Le,
    Ge,
    Gt,
    Disjoint,
    In,
    NotIn,
    LeftShift,
    RightShift,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor
  }
  public readonly Opcode Op;
  public enum ResolvedOpcode {
    YetUndetermined,  // the value before resolution has determined the value; .ResolvedOp should never be read in this state

    // logical operators
    Iff,
    Imp,
    And,
    Or,
    // non-collection types
    EqCommon,
    NeqCommon,
    // integers, reals, bitvectors
    Lt,
    LessThanLimit,  // a synonym for Lt for ORDINAL, used only during translation
    Le,
    Ge,
    Gt,
    Add, // also used for char
    Sub, // also used for char
    Mul,
    Div,
    Mod,
    // bitvectors
    LeftShift,
    RightShift,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    // char
    LtChar,
    LeChar,
    GeChar,
    GtChar,
    // sets
    SetEq,
    SetNeq,
    ProperSubset,
    Subset,
    Superset,
    ProperSuperset,
    Disjoint,
    InSet,
    NotInSet,
    Union,
    Intersection,
    SetDifference,
    // multi-sets
    MultiSetEq,
    MultiSetNeq,
    MultiSubset,
    MultiSuperset,
    ProperMultiSubset,
    ProperMultiSuperset,
    MultiSetDisjoint,
    InMultiSet,
    NotInMultiSet,
    MultiSetUnion,
    MultiSetIntersection,
    MultiSetDifference,
    // Sequences
    SeqEq,
    SeqNeq,
    ProperPrefix,
    Prefix,
    Concat,
    InSeq,
    NotInSeq,
    // Maps
    MapEq,
    MapNeq,
    InMap,
    NotInMap,
    MapMerge,
    MapSubtraction,
    // datatypes
    RankLt,
    RankGt
  }
  private ResolvedOpcode _theResolvedOp = ResolvedOpcode.YetUndetermined;
  public ResolvedOpcode ResolvedOp {
    get {
      Debug.Assert(_theResolvedOp != ResolvedOpcode.YetUndetermined);  // shouldn't read it until it has been properly initialized
      return _theResolvedOp;
    }
    set {
      Contract.Assume(_theResolvedOp == ResolvedOpcode.YetUndetermined || _theResolvedOp == value);  // there's never a reason for resolution to change its mind, is there?
      _theResolvedOp = value;
    }
  }
  public ResolvedOpcode ResolvedOp_PossiblyStillUndetermined {  // offer a way to return _theResolveOp -- for experts only!
    get { return _theResolvedOp; }
  }
  public static bool IsEqualityOp(ResolvedOpcode op) {
    switch (op) {
      case ResolvedOpcode.EqCommon:
      case ResolvedOpcode.SetEq:
      case ResolvedOpcode.SeqEq:
      case ResolvedOpcode.MultiSetEq:
      case ResolvedOpcode.MapEq:
        return true;
      default:
        return false;
    }
  }

  public static Opcode ResolvedOp2SyntacticOp(ResolvedOpcode rop) {
    switch (rop) {
      case ResolvedOpcode.Iff: return Opcode.Iff;
      case ResolvedOpcode.Imp: return Opcode.Imp;
      case ResolvedOpcode.And: return Opcode.And;
      case ResolvedOpcode.Or: return Opcode.Or;

      case ResolvedOpcode.EqCommon:
      case ResolvedOpcode.SetEq:
      case ResolvedOpcode.MultiSetEq:
      case ResolvedOpcode.SeqEq:
      case ResolvedOpcode.MapEq:
        return Opcode.Eq;

      case ResolvedOpcode.NeqCommon:
      case ResolvedOpcode.SetNeq:
      case ResolvedOpcode.MultiSetNeq:
      case ResolvedOpcode.SeqNeq:
      case ResolvedOpcode.MapNeq:
        return Opcode.Neq;

      case ResolvedOpcode.Lt:
      case ResolvedOpcode.LtChar:
      case ResolvedOpcode.ProperSubset:
      case ResolvedOpcode.ProperMultiSuperset:
      case ResolvedOpcode.ProperPrefix:
      case ResolvedOpcode.RankLt:
        return Opcode.Lt;

      case ResolvedOpcode.Le:
      case ResolvedOpcode.LeChar:
      case ResolvedOpcode.Subset:
      case ResolvedOpcode.MultiSubset:
      case ResolvedOpcode.Prefix:
        return Opcode.Le;

      case ResolvedOpcode.Ge:
      case ResolvedOpcode.GeChar:
      case ResolvedOpcode.Superset:
      case ResolvedOpcode.MultiSuperset:
        return Opcode.Ge;

      case ResolvedOpcode.Gt:
      case ResolvedOpcode.GtChar:
      case ResolvedOpcode.ProperSuperset:
      case ResolvedOpcode.ProperMultiSubset:
      case ResolvedOpcode.RankGt:
        return Opcode.Gt;

      case ResolvedOpcode.LeftShift:
        return Opcode.LeftShift;

      case ResolvedOpcode.RightShift:
        return Opcode.RightShift;

      case ResolvedOpcode.Add:
      case ResolvedOpcode.Union:
      case ResolvedOpcode.MultiSetUnion:
      case ResolvedOpcode.MapMerge:
      case ResolvedOpcode.Concat:
        return Opcode.Add;

      case ResolvedOpcode.Sub:
      case ResolvedOpcode.SetDifference:
      case ResolvedOpcode.MultiSetDifference:
      case ResolvedOpcode.MapSubtraction:
        return Opcode.Sub;

      case ResolvedOpcode.Mul:
      case ResolvedOpcode.Intersection:
      case ResolvedOpcode.MultiSetIntersection:
        return Opcode.Mul;

      case ResolvedOpcode.Div: return Opcode.Div;
      case ResolvedOpcode.Mod: return Opcode.Mod;

      case ResolvedOpcode.BitwiseAnd: return Opcode.BitwiseAnd;
      case ResolvedOpcode.BitwiseOr: return Opcode.BitwiseOr;
      case ResolvedOpcode.BitwiseXor: return Opcode.BitwiseXor;

      case ResolvedOpcode.Disjoint:
      case ResolvedOpcode.MultiSetDisjoint:
        return Opcode.Disjoint;

      case ResolvedOpcode.InSet:
      case ResolvedOpcode.InMultiSet:
      case ResolvedOpcode.InSeq:
      case ResolvedOpcode.InMap:
        return Opcode.In;

      case ResolvedOpcode.NotInSet:
      case ResolvedOpcode.NotInMultiSet:
      case ResolvedOpcode.NotInSeq:
      case ResolvedOpcode.NotInMap:
        return Opcode.NotIn;

      case ResolvedOpcode.LessThanLimit:  // not expected here (but if it were, the same case as Lt could perhaps be used)
      default:
        Contract.Assert(false);  // unexpected ResolvedOpcode
        return Opcode.Add;  // please compiler
    }
  }

  public static string OpcodeString(Opcode op) {
    Contract.Ensures(Contract.Result<string>() != null);

    switch (op) {
      case Opcode.Iff:
        return "<==>";
      case Opcode.Imp:
        return "==>";
      case Opcode.Exp:
        return "<==";
      case Opcode.And:
        return "&&";
      case Opcode.Or:
        return "||";
      case Opcode.Eq:
        return "==";
      case Opcode.Lt:
        return "<";
      case Opcode.Gt:
        return ">";
      case Opcode.Le:
        return "<=";
      case Opcode.Ge:
        return ">=";
      case Opcode.Neq:
        return "!=";
      case Opcode.Disjoint:
        return "!!";
      case Opcode.In:
        return "in";
      case Opcode.NotIn:
        return "!in";
      case Opcode.LeftShift:
        return "<<";
      case Opcode.RightShift:
        return ">>";
      case Opcode.Add:
        return "+";
      case Opcode.Sub:
        return "-";
      case Opcode.Mul:
        return "*";
      case Opcode.Div:
        return "/";
      case Opcode.Mod:
        return "%";
      case Opcode.BitwiseAnd:
        return "&";
      case Opcode.BitwiseOr:
        return "|";
      case Opcode.BitwiseXor:
        return "^";
      default:
        Contract.Assert(false);
        throw new cce.UnreachableException();  // unexpected operator
    }
  }
  public Expression E0;
  public Expression E1;
  public enum AccumulationOperand { None, Left, Right }
  public AccumulationOperand AccumulatesForTailRecursion = AccumulationOperand.None; // set by Resolver
  [FilledInDuringResolution] public bool InCompiledContext;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(E0 != null);
    Contract.Invariant(E1 != null);
  }

  public BinaryExpr Clone(Cloner cloner) {
    return new BinaryExpr(cloner, this);
  }

  public BinaryExpr(Cloner cloner, BinaryExpr original) : base(cloner, original) {
    this.Op = original.Op;
    this.E0 = cloner.CloneExpr(original.E0);
    this.E1 = cloner.CloneExpr(original.E1);

    if (cloner.CloneResolvedFields) {
      ResolvedOp = original.ResolvedOp;
    }
  }

  public BinaryExpr(IOrigin tok, Opcode op, Expression e0, Expression e1)
    :
    base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(e0 != null);
    Contract.Requires(e1 != null);
    this.Op = op;
    this.E0 = e0;
    this.E1 = e1;
  }

  /// <summary>
  /// Returns a resolved binary expression
  /// </summary>
  public BinaryExpr(IOrigin tok, BinaryExpr.ResolvedOpcode rop, Expression e0, Expression e1)
    : this(tok, BinaryExpr.ResolvedOp2SyntacticOp(rop), e0, e1) {
    ResolvedOp = rop;
    switch (rop) {
      case ResolvedOpcode.EqCommon:
      case ResolvedOpcode.NeqCommon:
      case ResolvedOpcode.Lt:
      case ResolvedOpcode.LessThanLimit:
      case ResolvedOpcode.Le:
      case ResolvedOpcode.Ge:
      case ResolvedOpcode.Gt:
      case ResolvedOpcode.LtChar:
      case ResolvedOpcode.LeChar:
      case ResolvedOpcode.GeChar:
      case ResolvedOpcode.GtChar:
      case ResolvedOpcode.SetEq:
      case ResolvedOpcode.SetNeq:
      case ResolvedOpcode.ProperSubset:
      case ResolvedOpcode.Subset:
      case ResolvedOpcode.Superset:
      case ResolvedOpcode.ProperSuperset:
      case ResolvedOpcode.Disjoint:
      case ResolvedOpcode.InSet:
      case ResolvedOpcode.NotInSet:
      case ResolvedOpcode.MultiSetEq:
      case ResolvedOpcode.MultiSetNeq:
      case ResolvedOpcode.MultiSubset:
      case ResolvedOpcode.MultiSuperset:
      case ResolvedOpcode.ProperMultiSubset:
      case ResolvedOpcode.ProperMultiSuperset:
      case ResolvedOpcode.MultiSetDisjoint:
      case ResolvedOpcode.InMultiSet:
      case ResolvedOpcode.NotInMultiSet:
      case ResolvedOpcode.SeqEq:
      case ResolvedOpcode.SeqNeq:
      case ResolvedOpcode.ProperPrefix:
      case ResolvedOpcode.Prefix:
      case ResolvedOpcode.InSeq:
      case ResolvedOpcode.NotInSeq:
      case ResolvedOpcode.MapEq:
      case ResolvedOpcode.MapNeq:
      case ResolvedOpcode.InMap:
      case ResolvedOpcode.NotInMap:
      case ResolvedOpcode.RankLt:
      case ResolvedOpcode.RankGt:
        Type = Type.Bool;
        break;
      default:
        Type = e0.Type;
        break;
    }
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return E0;
      yield return E1;
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    var indent = indentBefore;
    if (Op is Opcode.And or Opcode.Or) {
      var ownedTokens = OwnedTokens.ToList();
      // Alignment required.
      if (ownedTokens.Count == 2) {
        var firstToken = ownedTokens[0];
        var secondToken = ownedTokens[1];
        indent = formatter.GetNewTokenVisualIndent(firstToken, formatter.GetIndentInlineOrAbove(firstToken));
        var c = 0;
        while (c < firstToken.TrailingTrivia.Length && firstToken.TrailingTrivia[c] == ' ') {
          c++;
        }

        var conjunctExtraIndent = c + formatter.SpaceTab;
        formatter.binOpIndent = indent;
        formatter.binOpArgIndent = indent + conjunctExtraIndent;
        formatter.SetIndentations(firstToken, formatter.binOpIndent, formatter.binOpIndent, formatter.binOpArgIndent);
        formatter.SetIndentations(secondToken, formatter.binOpIndent, formatter.binOpIndent, formatter.binOpArgIndent);
      } else if (ownedTokens.Count > 0) {
        if (ownedTokens[0].val == "requires") { // Requirement conjunctions inside lambdas are separated by the keyword "requires"
          if (this.StartToken.Prev.val == "requires") {
            formatter.binOpIndent = formatter.GetIndentInlineOrAbove(this.StartToken.Prev);
          }
        }
        if (formatter.binOpIndent > 0) {
          formatter.SetIndentations(ownedTokens[0], formatter.binOpIndent, formatter.binOpIndent, formatter.binOpArgIndent);
        } else {
          var startToken = this.StartToken;
          //"," in a comprehension is an "&&", except that it should not try to keep a visual indentation between components.
          var newIndent =
            ownedTokens[0].val == "," ?
              formatter.GetIndentInlineOrAbove(startToken)
              : formatter.GetNewTokenVisualIndent(startToken, formatter.GetIndentInlineOrAbove(startToken));
          formatter.SetIndentations(ownedTokens[0], newIndent, newIndent, newIndent);
        }
      }

      if (formatter.binOpIndent > 0 && (this.E0 is not BinaryExpr { Op: var op } || op != this.Op)) {
        formatter.binOpIndent = -1;
        formatter.binOpArgIndent = -1;
      }

      return true; // Default indentation
    } else if (Op is Opcode.Imp or Opcode.Exp) {
      foreach (var token in this.OwnedTokens) {
        switch (token.val) {
          case "==>": {
              formatter.SetOpeningIndentedRegion(token, indent);
              break;
            }
          case "<==": {
              formatter.SetIndentations(token, indent, indent, indent);
              break;
            }
        }
      }
      formatter.Visit(this.E0, indent);
      formatter.Visit(this.E1, this.Op is BinaryExpr.Opcode.Exp ? indent : indent + formatter.SpaceTab);
      formatter.SetIndentations(this.EndToken, below: indent);
      return false;
    } else if (Op is Opcode.Eq or Opcode.Le or Opcode.Lt or Opcode.Ge or Opcode.Gt or Opcode.Iff or Opcode.Neq) {
      var itemIndent = formatter.GetNewTokenVisualIndent(
        E0.StartToken, indent);
      var item2Indent = itemIndent;
      var startToken = this.E0.StartToken;
      if (startToken.Prev.line == startToken.line) {
        // like assert E0
        //          == E1
        // Careful: The binaryExpr.op's first column should be greater than the
        // token's first column before E0.StartToken. 
        foreach (var token in this.OwnedTokens) {
          switch (token.val) {
            case "==":
            case "<=":
            case "<":
            case ">=":
            case ">":
            case "<==>":
            case "!=": {
                var followedByNewline = TokenNewIndentCollector.IsFollowedByNewline(token);
                var selfIndent = followedByNewline ? itemIndent : Math.Max(itemIndent - token.val.Length - 1, 0);
                if (selfIndent <= formatter.GetNewTokenVisualIndent(startToken.Prev, itemIndent)) {
                  // There could be a visual ambiguity if this token is aligned with the enclosing token.
                  selfIndent = itemIndent;
                }
                formatter.SetIndentations(token, itemIndent, selfIndent);
                item2Indent = followedByNewline ? itemIndent : formatter.GetNewTokenVisualIndent(this.E1.StartToken, itemIndent);
                formatter.SetIndentations(token, below: item2Indent);
                break;
              }
          }
        }
      }
      formatter.Visit(E0, itemIndent);
      formatter.Visit(E1, item2Indent);
      formatter.SetIndentations(EndToken, below: indent);
      return false;
    } else if (Op is Opcode.In or Opcode.NotIn) {
      var itemIndent = formatter.GetNewTokenVisualIndent(
        E0.StartToken, indent);
      var item2Indent = itemIndent + formatter.SpaceTab;
      formatter.Visit(E0, itemIndent);
      foreach (var token in this.OwnedTokens) {
        switch (token.val) {
          case "<": {
              if (token.Prev.line != token.line) {
                itemIndent = formatter.GetNewTokenVisualIndent(token, indent);
              }

              break;
            }
          case "in":
          case "-": {
              if (TokenNewIndentCollector.IsFollowedByNewline(token)) {
                formatter.SetOpeningIndentedRegion(token, itemIndent);
              } else {
                formatter.SetAlign(itemIndent, token, out item2Indent, out _);
              }
              break;
            }
        }
      }
      formatter.Visit(E1, item2Indent);
      return false;
    } else {
      foreach (var token in OwnedTokens) {
        formatter.SetIndentations(token, indent, indent, indent);
      }
      formatter.Visit(E0, indent);
      formatter.Visit(E1, indent);
      formatter.SetIndentations(EndToken, below: indent);
      return false;
    }
  }
}