//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny.Compilers; 

internal class InternalCompilersPluginConfiguration : Plugins.PluginConfiguration {
  public static readonly InternalCompilersPluginConfiguration Singleton = new();

  public override Plugins.Compiler[] GetCompilers() {
    return new Plugins.Compiler[] {
      new CsharpCompiler(),
      new JavaScriptCompiler(),
      new GoCompiler(),
      new JavaCompiler(),
      new PythonCompiler(),
      new CppCompiler()
    };
  }
}

public abstract class GenericSinglePassCompiler<TExpression, TStatements, TStatement, TType> // TODO remove generic from the name
  where TStatements : IList<TStatement> {
  protected internal readonly FreshIdGenerator idGenerator = new();
  protected TopLevelDeclWithMembers thisContext;  // non-null when type members are being translated
  protected Method enclosingMethod;  // non-null when a method body is being translated
  protected Function enclosingFunction;  // non-null when a function body is being translated

  internal abstract TType TypeName(Type type, IToken tok, MemberDecl/*?*/ member = null);

  protected internal abstract TExpression TrExpr(Expression expr, bool inLetExprBody, TStatements wStmts);
  protected abstract TExpression This();

  protected abstract TExpression LiteralExpr(LiteralExpr e);
  protected delegate TExpression FCE_Arg_Translator(Expression e, bool inLetExpr, TStatements wStmts);

  protected abstract TExpression ArraySelect(List<Expression> indices, Type elementType, bool inLetExprBody, TExpression array, TStatements wStmts);

  protected abstract TExpression IndexCollectionSelect(Expression source, Expression index, bool inLetExprBody,
    TStatements wStmts);

  /// <summary>
  /// If "fromArray" is false, then "source" is a sequence.
  /// If "fromArray" is true, then "source" is an array.
  /// </summary>
  protected abstract TExpression SeqSelectRange(Expression source, Expression lo /*?*/, Expression hi /*?*/,
    bool fromArray, bool inLetExprBody, TStatements wStmts);

  protected abstract TExpression TrParenExpr(Expression expr, bool inLetExprBody, TStatements wStmts);

  private protected string ProtectedFreshId(string prefix) => IdProtect(idGenerator.FreshId(prefix));
  private protected string ProtectedFreshNumericId(string prefix) => IdProtect(idGenerator.FreshNumericId(prefix));
  protected virtual string IdProtect(string name) {
    Contract.Requires(name != null);
    return name;
  }

  protected abstract TStatement VariableDeclaration(string name, Type type, IToken token, TExpression initialValue);

  protected abstract TStatement AsStatement(TExpression expression);

  protected virtual TExpression Downcast(Type from, Type to, IToken tok, TExpression value) {
    Contract.Requires(from != null);
    Contract.Requires(to != null);
    Contract.Requires(tok != null);
    Contract.Requires(value != null);
    Contract.Requires(!IsTargetSupertype(to, from));
    return value;
  }

  protected virtual TExpression CoercionIfNecessary(Type/*?*/ from, Type/*?*/ to, IToken tok, TExpression value) {
    return value;
  }

  protected TExpression DowncastIfNecessary(Type /*?*/ from, Type /*?*/ to, IToken tok, TExpression value) {
    Contract.Requires(tok != null);
    Contract.Requires(value != null);
    if (from != null && to != null) {
      from = DatatypeWrapperEraser.SimplifyType(from);
      to = DatatypeWrapperEraser.SimplifyType(to);
      if (!IsTargetSupertype(to, from)) {
        // By the way, it is tempting to think that IsTargetSupertype(from, to)) would hold here, but that's not true.
        // For one, in a language with NeedsCastFromTypeParameter, "to" and "from" may contain uninstantiated formal type parameters.
        // Also, it is possible (subject to a check enforced by the verifier) to assign Datatype<X> to Datatype<Y>,
        // where Datatype is co-variant in its argument type and X and Y are two incomparable types with a common supertype.

        return Downcast(from, to, tok, value);
      }
    }
    return value;
  }

  /// <summary>
  /// Determine if "to" is a supertype of "from" in the target language, if "!typeEqualityOnly".
  /// Determine if "to" is equal to "from" in the target language, if "typeEqualityOnly".
  /// This to similar to Type.IsSupertype and Type.Equals, respectively, but ignores subset types (that
  /// is, always uses the base type of any subset type).
  /// </summary>
  public bool IsTargetSupertype(Type to, Type from, bool typeEqualityOnly = false) {
    Contract.Requires(from != null);
    Contract.Requires(to != null);
    to = to.NormalizeExpand();
    from = from.NormalizeExpand();
    if (Type.SameHead(to, from)) {
      Contract.Assert(to.TypeArgs.Count == from.TypeArgs.Count);
      var formalTypeParameters = (to as UserDefinedType)?.ResolvedClass?.TypeArgs;
      Contract.Assert(formalTypeParameters == null || formalTypeParameters.Count == to.TypeArgs.Count);
      Contract.Assert(formalTypeParameters != null || to.TypeArgs.Count == 0 || to is CollectionType);
      for (var i = 0; i < to.TypeArgs.Count; i++) {
        bool okay;
        if (typeEqualityOnly || TargetSubtypingRequiresEqualTypeArguments(to)) {
          okay = IsTargetSupertype(to.TypeArgs[i], from.TypeArgs[i], true);
        } else if (formalTypeParameters == null || formalTypeParameters[i].Variance == TypeParameter.TPVariance.Co) {
          okay = IsTargetSupertype(to.TypeArgs[i], from.TypeArgs[i]);
        } else if (formalTypeParameters[i].Variance == TypeParameter.TPVariance.Contra) {
          okay = IsTargetSupertype(from.TypeArgs[i], to.TypeArgs[i]);
        } else {
          okay = IsTargetSupertype(to.TypeArgs[i], from.TypeArgs[i], true);
        }
        if (!okay) {
          return false;
        }
      }
      return true;
    } else if (typeEqualityOnly) {
      return false;
    } else if (to.IsObjectQ) {
      return true;
    } else {
      return from.ParentTypes().Any(fromParentType => IsTargetSupertype(to, fromParentType));
    }
  }


  protected virtual bool TargetSubtypingRequiresEqualTypeArguments(Type type) => false;

  protected virtual TExpression Assignment(ILvalue wLhs, Type lhsType /*?*/, Type rhsType /*?*/,
    TExpression value, IToken tok) {
    return wLhs.Write(CoercionIfNecessary(rhsType, lhsType, tok,
      DowncastIfNecessary(rhsType, lhsType, tok, value)));
  }

  protected abstract string EmitAssignmentLhs(Expression e, TStatements wStmts); // TODO implement using others?

  protected abstract TStatements CreateStatementList();

  /// <summary>
  /// The "additionalCustomParameter" is used when the member is an instance function that requires customer-receiver support.
  /// This parameter is then to be added between any run-time type descriptors and the "normal" arguments. The caller will
  /// arrange for "additionalCustomParameter" to be properly bound.
  /// </summary>
  protected abstract ILvalue MemberSelect(TExpression obj, Type objType, MemberDecl member, List<TypeArgumentInstantiation> typeArgs, Dictionary<TypeParameter, Type> typeMap,
    Type expectedType, string/*?*/ additionalCustomParameter = null, bool internalAccess = false);

  protected abstract TExpression Variable(string name);

  protected abstract ILvalue ArraySelectAsLvalue(string array, List<TExpression> indices, Type elementType);

  protected virtual TExpression ArrayIndexToNativeInt(TExpression arrayIndex, Type fromType) {
    Contract.Requires(arrayIndex != null);
    Contract.Requires(fromType != null);
    return arrayIndex;
  }

  protected virtual TStatements MultiAssignment(List<Expression> lhsExprs, List<ILvalue> lhss, List<Type> lhsTypes, IReadOnlyList<TExpression> values,
    List<Type> rhsTypes) {
    Contract.Assert(lhss.Count == lhsTypes.Count);
    Contract.Assert(lhsTypes.Count == rhsTypes.Count);

    var statements = CreateStatementList();

    var rhsVars = new List<string>();
    for (var index = 0; index < rhsTypes.Count; index++) {
      var rhsType = rhsTypes[index];
      var value = values[index];
      string target = ProtectedFreshId("_rhs");
      rhsVars.Add(target);
      statements.Add(VariableDeclaration(target, rhsType, Token.NoToken, value));
    }

    List<ILvalue> lhssn;
    if (lhss.Count > 1) {
      lhssn = new List<ILvalue>();
      for (int i = 0; i < lhss.Count; ++i) {
        Expression lexpr = lhsExprs[i].Resolved;
        ILvalue lhs = lhss[i];
        if (lexpr is IdentifierExpr) {
          lhssn.Add(lhs);
        } else if (lexpr is MemberSelectExpr) {
          var resolved = (MemberSelectExpr)lexpr;
          string target = EmitAssignmentLhs(resolved.Obj, statements);
          var typeArgs = TypeArgumentInstantiation.ListFromMember(resolved.Member, null, resolved.TypeApplication_JustMember);
          ILvalue newLhs = MemberSelect(Variable(target), resolved.Obj.Type, resolved.Member, typeArgs, resolved.TypeArgumentSubstitutionsWithParents(), resolved.Type, internalAccess: enclosingMethod is Constructor);
          lhssn.Add(newLhs);
        } else if (lexpr is SeqSelectExpr) {
          var seqExpr = (SeqSelectExpr)lexpr;
          string targetArray = EmitAssignmentLhs(seqExpr.Seq, statements);
          var targetIndex = Variable(EmitAssignmentLhs(seqExpr.E0, statements));
          if (seqExpr.Seq.Type.IsArrayType || seqExpr.Seq.Type.AsSeqType != null) {
            targetIndex = ArrayIndexToNativeInt(targetIndex, seqExpr.E0.Type);
          }
          ILvalue newLhs = ArraySelectAsLvalue(targetArray,
            new List<TExpression>() { targetIndex }, lhsTypes[i]);
          lhssn.Add(newLhs);
        } else if (lexpr is MultiSelectExpr) {
          var seqExpr = (MultiSelectExpr)lexpr;
          Expression array = seqExpr.Array;
          List<Expression> indices = seqExpr.Indices;
          string targetArray = EmitAssignmentLhs(array, statements);
          var targetIndices = new List<TExpression>();
          foreach (var index in indices) {
            string targetIndex = EmitAssignmentLhs(index, statements);
            targetIndices.Add(Variable(targetIndex));
          }
          ILvalue newLhs = ArraySelectAsLvalue(targetArray, targetIndices, lhsTypes[i]);
          lhssn.Add(newLhs);
        } else {
          Contract.Assert(false); // Unknown kind of expression
        }
      }
    } else {
      lhssn = lhss;
    }

    Contract.Assert(rhsVars.Count == lhsTypes.Count);
    for (int i = 0; i < rhsVars.Count; i++) {
      statements.Add(AsStatement(Assignment(lhssn[i], lhsTypes[i], rhsTypes[i], Variable(rhsVars[i]), Token.NoToken)));
    }

    return statements;
  }

  protected interface ILvalue {
    TExpression Read();

    /// Write an assignment expression (or equivalent) for the lvalue,
    /// returning a TargetWriter for the RHS.  IMPORTANT: Whoever calls
    /// EmitWrite is responsible for making the types match up (as by
    /// EmitCoercionIfNecessary), for example by going through the overload
    /// of EmitAssignment that takes an ILvalue.
    TExpression Write(TExpression value);
  }

  protected TExpression TrSeqSelectExpr(bool inLetExprBody, TStatements wStmts, SeqSelectExpr e) {
    Contract.Assert(e.Seq.Type != null);
    if (e.Seq.Type.IsArrayType) {
      if (!e.SelectOne) {
        return SeqSelectRange(e.Seq, e.E0, e.E1, true, inLetExprBody, wStmts);
      }

      Contract.Assert(e.E0 != null && e.E1 == null);
      var array = TrParenExpr(e.Seq, inLetExprBody, wStmts);
      return ArraySelect(new List<Expression> { e.E0 }, e.Type, inLetExprBody, array, wStmts);
    }

    if (e.SelectOne) {
      Contract.Assert(e.E0 != null && e.E1 == null);
      return IndexCollectionSelect(e.Seq, e.E0, inLetExprBody, wStmts);
    }

    return SeqSelectRange(e.Seq, e.E0, e.E1, false, inLetExprBody, wStmts);
  }

}