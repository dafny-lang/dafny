//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using JetBrains.Annotations;

namespace Microsoft.Dafny {
  public abstract class ResolverPass {
    protected readonly Resolver resolver;

    protected ResolverPass(Resolver resolver) {
      Contract.Requires(resolver != null);
      this.resolver = resolver;
    }

    protected int ErrorCount => resolver.Reporter.Count(ErrorLevel.Error);

    protected void ReportError(Declaration d, string msg, params object[] args) {
      Contract.Requires(d != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      ReportError(d.tok, msg, args);
    }

    protected void ReportError(Statement stmt, string msg, params object[] args) {
      Contract.Requires(stmt != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      ReportError(stmt.Tok, msg, args);
    }

    protected void ReportError(Expression expr, string msg, params object[] args) {
      Contract.Requires(expr != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      ReportError(expr.tok, msg, args);
    }

    public void ReportError(IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      resolver.Reporter.Error(MessageSource.Resolver, tok, "PRE-TYPE: " + msg, args);
    }

    public void ReportWarning(IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      resolver.Reporter.Warning(MessageSource.Resolver, ErrorRegistry.NoneId, tok, msg, args);
    }

    protected void ReportInfo(IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      resolver.Reporter.Info(MessageSource.Resolver, tok, msg, args);
    }
  }

  public partial class PreTypeResolver : ResolverPass {
    public enum Type2PreTypeOption { GoodForInference, GoodForPrinting, GoodForBoth }

    public PreType Type2PreType(Type type, string description = null, Type2PreTypeOption option = Type2PreTypeOption.GoodForBoth) {
      Contract.Requires(type != null);

      type = type.Normalize();
      var expandedType = type.NormalizeExpand();
      if (expandedType is TypeProxy) {
        return CreatePreTypeProxy(description ?? $"from type proxy {type}");
      }

      DPreType printablePreType = null;
      if (option != Type2PreTypeOption.GoodForInference) {
        var printableDecl = Type2PreTypeDecl(type);
        var printableArguments = type.TypeArgs.ConvertAll(ty => Type2PreType(ty, null, Type2PreTypeOption.GoodForPrinting));
        printablePreType = new DPreType(printableDecl, printableArguments, null);
        if (option == Type2PreTypeOption.GoodForPrinting) {
          return printablePreType;
        }
      }

      type = expandedType;
      var decl = Type2PreTypeDecl(type);
      var arguments = type.TypeArgs.ConvertAll(ty => Type2PreType(ty, null, Type2PreTypeOption.GoodForInference));
      return new DPreType(decl, arguments, printablePreType);
    }

    TopLevelDecl Type2PreTypeDecl(Type type) {
      Contract.Requires(type != null);
      Contract.Requires(type is NonProxyType and not SelfType);
      TopLevelDecl decl;
      if (type is BoolType) {
        decl = BuiltInTypeDecl("bool");
      } else if (type is CharType) {
        decl = BuiltInTypeDecl("char");
      } else if (type is IntType) {
        decl = BuiltInTypeDecl("int");
      } else if (type is RealType) {
        decl = BuiltInTypeDecl("real");
      } else if (type is BigOrdinalType) {
        decl = BuiltInTypeDecl("ORDINAL");
      } else if (type is BitvectorType bitvectorType) {
        decl = BuiltInTypeDecl("bv" + bitvectorType.Width);
      } else if (type is CollectionType) {
        var name =
          type is SetType st ? (st.Finite ? "set" : "iset") :
          type is MultiSetType ? "multiset" :
          type is MapType mt ? (mt.Finite ? "map" : "imap") :
          "seq";
        decl = BuiltInTypeDecl(name);
      } else if (type is ArrowType at) {
        decl = BuiltInArrowTypeDecl(at.Arity);
      } else if (type is UserDefinedType udt) {
        decl = udt.ResolvedClass;
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
      return decl;
    }

    public PreTypeResolver(Resolver resolver)
      : base(resolver) {
      Contract.Requires(resolver != null);
    }

    /// <summary>
    /// For every declaration in "declarations", resolve names and determine pre-types.
    /// </summary>
    public void ResolveDeclarations(List<TopLevelDecl> declarations, string moduleName) {
      // under construction... (the CLI option --type-system-refresh has informed the user that this mode is not yet ready)
    }

  }
}
