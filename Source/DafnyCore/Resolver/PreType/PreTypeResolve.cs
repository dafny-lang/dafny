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
    private readonly Dictionary<string, TopLevelDecl> preTypeBuiltins = new();

    TopLevelDecl BuiltInTypeDecl(string name) {
      Contract.Requires(name != null);
      if (preTypeBuiltins.TryGetValue(name, out var decl)) {
        return decl;
      }
      if (IsArrayName(name, out var dims)) {
        // make sure the array class has been created
        var at = resolver.builtIns.ArrayType(Token.NoToken, dims,
          new List<Type> { new InferredTypeProxy() }, true);
        decl = resolver.builtIns.arrayTypeDecls[dims];
      } else if (IsBitvectorName(name, out var width)) {
        var bvDecl = new ValuetypeDecl(name, resolver.builtIns.SystemModule, t => t.IsBitVectorType,
          typeArgs => new BitvectorType(resolver.Options, width));
        preTypeBuiltins.Add(name, bvDecl);
        AddRotateMember(bvDecl, "RotateLeft", width);
        AddRotateMember(bvDecl, "RotateRight", width);
        return bvDecl;
      } else {
        foreach (var valueTypeDecl in resolver.valuetypeDecls) {
          if (valueTypeDecl.Name == name) {
            // bool, int, real, ORDINAL, map, imap
            decl = valueTypeDecl;
            break;
          }
        }
        if (decl == null) {
          if (name == "set" || name == "seq" || name == "multiset") {
            var variances = new List<TypeParameter.TPVarianceSyntax>() { TypeParameter.TPVarianceSyntax.Covariant_Strict };
            decl = new ValuetypeDecl(name, resolver.builtIns.SystemModule, variances, _ => false, null);
          } else if (name == "iset") {
            var variances = new List<TypeParameter.TPVarianceSyntax>() { TypeParameter.TPVarianceSyntax.Covariant_Permissive };
            decl = new ValuetypeDecl(name, resolver.builtIns.SystemModule, variances, _ => false, null);
          } else {
            decl = new ValuetypeDecl(name, resolver.builtIns.SystemModule, _ => false, null);
          }
        }
      }
      preTypeBuiltins.Add(name, decl);
      return decl;
    }

    public void AddRotateMember(ValuetypeDecl bitvectorTypeDecl, string name, int width) {
      var argumentType = resolver.builtIns.Nat();
      var formals = new List<Formal> {
        new Formal(Token.NoToken, "w", argumentType, true, false, null, false) {
          PreType = Type2PreType(argumentType)
        }
      };
      var resultType = new BitvectorType(resolver.Options, width);
      var rotateMember = new SpecialFunction(RangeToken.NoToken, name, resolver.builtIns.SystemModule, false, false,
        new List<TypeParameter>(), formals, resultType,
        new List<AttributedExpression>(), new List<FrameExpression>(), new List<AttributedExpression>(),
        new Specification<Expression>(new List<Expression>(), null), null, null, null) {
        EnclosingClass = bitvectorTypeDecl,
        ResultPreType = Type2PreType(resultType)
      };
      rotateMember.AddVisibilityScope(resolver.builtIns.SystemModule.VisibilityScope, false);
      bitvectorTypeDecl.Members.Add(name, rotateMember);
    }

    TopLevelDecl BuiltInArrowTypeDecl(int arity) {
      Contract.Requires(0 <= arity);
      var name = ArrowType.ArrowTypeName(arity);
      if (!preTypeBuiltins.TryGetValue(name, out var decl)) {
        // the arrow type declaration should already have been created by the parser
        decl = resolver.builtIns.ArrowTypeDecls[arity];
        preTypeBuiltins.Add(name, decl);
      }
      return decl;
    }

    DPreType BuiltInArrowType(List<PreType> inPreTypes, PreType resultPreType) {
      return new DPreType(BuiltInArrowTypeDecl(inPreTypes.Count), Util.Snoc(inPreTypes, resultPreType));
    }

    DPreType BuiltInArrayType(int dims, PreType elementPreType) {
      Contract.Requires(1 <= dims);
      var arrayName = dims == 1 ? "array" : $"array{dims}";
      return new DPreType(BuiltInTypeDecl(arrayName), new List<PreType>() { elementPreType });
    }

    private int typeProxyCount = 0; // used to give each PreTypeProxy a unique ID

    private readonly List<(PreTypeProxy, string)> allPreTypeProxies = new();

    public PreType CreatePreTypeProxy(string description = null) {
      var proxy = new PreTypeProxy(typeProxyCount++);
      allPreTypeProxies.Add((proxy, description));
      return proxy;
    }

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

    public static bool HasTraitSupertypes(DPreType dp) {
      /*
       * When traits can be used as supertypes for non-reference types (and "object" is an implicit parent trait of every
       * class), then this method can be implemented by
       *         return dp.Decl is TopLevelDeclWithMembers md && md.ParentTraits.Count != 0;
       * For now, every reference type except "object" has trait supertypes.
       */
      if (dp.Decl is TopLevelDeclWithMembers md && md.ParentTraits.Count != 0) {
        // this type has explicitly declared parent traits
        return true;
      }
      if (dp.Decl is TraitDecl trait && trait.IsObjectTrait) {
        // the built-in type "object" has no parent traits
        return false;
      }
      // any non-object reference type has "object" as an implicit parent trait
      return DPreType.IsReferenceTypeDecl(dp.Decl);
    }

    public static bool IsBitvectorName(string name, out int width) {
      Contract.Requires(name != null);
      if (name.StartsWith("bv")) {
        var bits = name.Substring(2);
        width = 0; // set to 0, in case the first disjunct of the next line evaluates to true
        return bits == "0" || (bits.Length != 0 && bits[0] != '0' && int.TryParse(bits, out width));
      }
      width = 0; // unused by caller
      return false;
    }

    public static bool IsBitvectorName(string name) {
      return IsBitvectorName(name, out _);
    }

    public static bool IsArrayName(string name, out int dimensions) {
      Contract.Requires(name != null);
      if (name.StartsWith("array")) {
        var dims = name.Substring(5);
        if (dims.Length == 0) {
          dimensions = 1;
          return true;
        } else if (dims[0] != '0' && dims != "1" && int.TryParse(dims, out dimensions)) {
          return true;
        }
      }
      dimensions = 0; // unused by caller
      return false;
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
