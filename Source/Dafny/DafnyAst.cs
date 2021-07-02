#define TI_DEBUG_PRINT
//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.Text;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Numerics;
using System.Linq;
using Microsoft.Boogie;
using System.Diagnostics;

namespace Microsoft.Dafny {
  public class Program {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(FullName != null);
      Contract.Invariant(DefaultModule != null);
    }

    public readonly string FullName;
    public Dictionary<ModuleDefinition,ModuleSignature> ModuleSigs; // filled in during resolution.
                                                     // Resolution essentially flattens the module hierarchy, for
                                                     // purposes of translation and compilation.
    public List<ModuleDefinition> CompileModules; // filled in during resolution.
                                                  // Contains the definitions to be used for compilation.

    public Method MainMethod; // Method to be used as main if compiled
    public readonly ModuleDecl DefaultModule;
    public readonly ModuleDefinition DefaultModuleDef;
    public readonly BuiltIns BuiltIns;
    public readonly ErrorReporter reporter;

    public Program(string name, [Captured] ModuleDecl module, [Captured] BuiltIns builtIns, ErrorReporter reporter) {
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(module is LiteralModuleDecl);
      Contract.Requires(reporter != null);
      FullName = name;
      DefaultModule = module;
      DefaultModuleDef = (DefaultModuleDecl)((LiteralModuleDecl)module).ModuleDef;
      BuiltIns = builtIns;
      this.reporter = reporter;
      ModuleSigs = new Dictionary<ModuleDefinition,ModuleSignature>();
      CompileModules = new List<ModuleDefinition>();
    }

    //Set appropriate visibilty before presenting module
    public IEnumerable<ModuleDefinition> Modules() {

      foreach (var msig in ModuleSigs) {
        Type.PushScope(msig.Value.VisibilityScope);
        yield return msig.Key;
        Type.PopScope(msig.Value.VisibilityScope);
      }

    }

    public IEnumerable<ModuleDefinition> RawModules() {
      return ModuleSigs.Keys;
    }

    public string Name
    {
      get
      {
        try
        {
          return System.IO.Path.GetFileName(FullName);
        }
        catch (ArgumentException)
        {
          return FullName;
        }
      }
    }
  }

  public class Include : IComparable
  {
    public readonly IToken tok;
    public readonly string includerFilename;
    public readonly string includedFilename;
    public readonly string canonicalPath;
    public bool ErrorReported;

    public Include(IToken tok, string includer, string theFilename) {
      this.tok = tok;
      this.includerFilename = includer;
      this.includedFilename = theFilename;
      this.canonicalPath = DafnyFile.Canonicalize(theFilename);
      this.ErrorReported = false;
    }

    public int CompareTo(object obj) {
      var i = obj as Include;
      if (i != null) {
        return this.canonicalPath.CompareTo(i.canonicalPath);
      } else {
        throw new NotImplementedException();
      }
    }
  }

  public class BuiltIns
  {
    public readonly ModuleDefinition SystemModule = new ModuleDefinition(Token.NoToken, "_System", new List<IToken>(), false, false, null, null, null, true, true, true);
    readonly Dictionary<int, ClassDecl> arrayTypeDecls = new Dictionary<int, ClassDecl>();
    public readonly Dictionary<int, ArrowTypeDecl> ArrowTypeDecls = new Dictionary<int, ArrowTypeDecl>();
    public readonly Dictionary<int, SubsetTypeDecl> PartialArrowTypeDecls = new Dictionary<int, SubsetTypeDecl>();  // same keys as arrowTypeDecl
    public readonly Dictionary<int, SubsetTypeDecl> TotalArrowTypeDecls = new Dictionary<int, SubsetTypeDecl>();  // same keys as arrowTypeDecl
    readonly Dictionary<object, TupleTypeDecl> tupleTypeDecls = new Dictionary<object, TupleTypeDecl>();
    public readonly ISet<int> Bitwidths = new HashSet<int>();
    public SpecialField ORDINAL_Offset;  // filled in by the resolver, used by the translator

    public readonly SubsetTypeDecl NatDecl;
    public UserDefinedType Nat() { return new UserDefinedType(Token.NoToken, "nat", NatDecl, new List<Type>()); }
    public readonly TraitDecl ObjectDecl;
    public UserDefinedType ObjectQ() {
      Contract.Assume(ObjectDecl != null);
      return new UserDefinedType(Token.NoToken, "object?", null) { ResolvedClass = ObjectDecl };
    }

    public BuiltIns() {
      SystemModule.Height = -1;  // the system module doesn't get a height assigned later, so we set it here to something below everything else
      // create type synonym 'string'
      var str = new TypeSynonymDecl(Token.NoToken, "string",
        new TypeParameter.TypeParameterCharacteristics(TypeParameter.EqualitySupportValue.InferredRequired, Type.AutoInitInfo.CompilableValue, false),
        new List<TypeParameter>(), SystemModule, new SeqType(new CharType()), null);
      SystemModule.TopLevelDecls.Add(str);
      // create subset type 'nat'
      var bvNat = new BoundVar(Token.NoToken, "x", Type.Int);
      var natConstraint = Expression.CreateAtMost(Expression.CreateIntLiteral(Token.NoToken, 0), Expression.CreateIdentExpr(bvNat));
      var ax = AxiomAttribute();
      NatDecl = new SubsetTypeDecl(Token.NoToken, "nat",
        new TypeParameter.TypeParameterCharacteristics(TypeParameter.EqualitySupportValue.InferredRequired, Type.AutoInitInfo.CompilableValue, false),
        new List<TypeParameter>(), SystemModule, bvNat, natConstraint, SubsetTypeDecl.WKind.CompiledZero, null, ax);
      SystemModule.TopLevelDecls.Add(NatDecl);
      // create trait 'object'
      ObjectDecl = new TraitDecl(Token.NoToken, "object", SystemModule, new List<TypeParameter>(), new List<MemberDecl>(), DontCompile(), false, null);
      SystemModule.TopLevelDecls.Add(ObjectDecl);
      // add one-dimensional arrays, since they may arise during type checking
      // Arrays of other dimensions may be added during parsing as the parser detects the need for these
      UserDefinedType tmp = ArrayType(1, Type.Int, true);
      // Arrow types of other dimensions may be added during parsing as the parser detects the need for these.  For the 0-arity
      // arrow type, the resolver adds a Valid() predicate for iterators, whose corresponding arrow type is conveniently created here.
      CreateArrowTypeDecl(0);
      // Note, in addition to these types, the _System module contains tuple types.  These tuple types are added to SystemModule
      // by the parser as the parser detects the need for these.
    }

    private Attributes DontCompile() {
      var flse = Expression.CreateBoolLiteral(Token.NoToken, false);
      return new Attributes("compile", new List<Expression>() { flse }, null);
    }

    public static Attributes AxiomAttribute() {
      return new Attributes("axiom", new List<Expression>(), null);
    }

    public UserDefinedType ArrayType(int dims, Type arg, bool allowCreationOfNewClass) {
      Contract.Requires(1 <= dims);
      Contract.Requires(arg != null);
      return ArrayType(Token.NoToken, dims, new List<Type>() { arg }, allowCreationOfNewClass);
    }
    public UserDefinedType ArrayType(IToken tok, int dims, List<Type> optTypeArgs, bool allowCreationOfNewClass, bool useClassNameType = false) {
      Contract.Requires(tok != null);
      Contract.Requires(1 <= dims);
      Contract.Requires(optTypeArgs == null || optTypeArgs.Count > 0);  // ideally, it is 1, but more will generate an error later, and null means it will be filled in automatically
      Contract.Ensures(Contract.Result<UserDefinedType>() != null);

      var arrayName = ArrayClassName(dims);
      if (useClassNameType) {
        arrayName = arrayName + "?";
      }
      if (allowCreationOfNewClass && !arrayTypeDecls.ContainsKey(dims)) {
        ArrayClassDecl arrayClass = new ArrayClassDecl(dims, SystemModule, DontCompile());
        for (int d = 0; d < dims; d++) {
          string name = dims == 1 ? "Length" : "Length" + d;
          Field len = new SpecialField(Token.NoToken, name, SpecialField.ID.ArrayLength, dims == 1 ? null : (object)d, false, false, false, Type.Int, null);
          len.EnclosingClass = arrayClass;  // resolve here
          arrayClass.Members.Add(len);
        }
        arrayTypeDecls.Add(dims, arrayClass);
        SystemModule.TopLevelDecls.Add(arrayClass);
        CreateArrowTypeDecl(dims);  // also create an arrow type with this arity, since it may be used in an initializing expression for the array
      }
      UserDefinedType udt = new UserDefinedType(tok, arrayName, optTypeArgs);
      return udt;
    }

    public static string ArrayClassName(int dims) {
      Contract.Requires(1 <= dims);
      if (dims == 1) {
        return "array";
      } else {
        return "array" + dims;
      }
    }

    /// <summary>
    /// Idempotently add an arrow type with arity 'arity' to the system module, and along
    /// with this arrow type, the two built-in subset types based on the arrow type.
    /// </summary>
    public void CreateArrowTypeDecl(int arity) {
      Contract.Requires(0 <= arity);
      if (!ArrowTypeDecls.ContainsKey(arity)) {
        IToken tok = Token.NoToken;
        var tps = Util.Map(Enumerable.Range(0, arity + 1), x => x < arity ?
          new TypeParameter(tok, "T" + x, TypeParameter.TPVarianceSyntax.Contravariance) :
          new TypeParameter(tok, "R", TypeParameter.TPVarianceSyntax.Covariant_Strict));
        var tys = tps.ConvertAll(tp => (Type)(new UserDefinedType(tp)));
        var args = Util.Map(Enumerable.Range(0, arity), i => new Formal(tok, "x" + i, tys[i], true, false, null));
        var argExprs = args.ConvertAll(a =>
              (Expression)new IdentifierExpr(tok, a.Name) { Var = a, Type = a.Type });
        var readsIS = new FunctionCallExpr(tok, "reads", new ImplicitThisExpr(tok), tok, argExprs) {
          Type = new SetType(true, ObjectQ()),
        };
        var readsFrame = new List<FrameExpression> { new FrameExpression(tok, readsIS, null) };
        var req = new Function(tok, "requires", false, true,
          new List<TypeParameter>(), args, null, Type.Bool,
          new List<AttributedExpression>(), readsFrame, new List<AttributedExpression>(),
          new Specification<Expression>(new List<Expression>(), null),
          null, null, null);
        var reads = new Function(tok, "reads", false, true,
          new List<TypeParameter>(), args, null, new SetType(true, ObjectQ()),
          new List<AttributedExpression>(), readsFrame, new List<AttributedExpression>(),
          new Specification<Expression>(new List<Expression>(), null),
          null, null, null);
        readsIS.Function = reads;  // just so we can really claim the member declarations are resolved
        readsIS.TypeApplication_AtEnclosingClass = tys;  // ditto
        readsIS.TypeApplication_JustFunction = new List<Type>();  // ditto
        var arrowDecl = new ArrowTypeDecl(tps, req, reads, SystemModule, DontCompile());
        ArrowTypeDecls.Add(arity, arrowDecl);
        SystemModule.TopLevelDecls.Add(arrowDecl);

        // declaration of read-effect-free arrow-type, aka heap-independent arrow-type, aka partial-function arrow-type
        tps = Util.Map(Enumerable.Range(0, arity + 1), x => x < arity ?
          new TypeParameter(tok, "T" + x, TypeParameter.TPVarianceSyntax.Contravariance) :
          new TypeParameter(tok, "R", TypeParameter.TPVarianceSyntax.Covariant_Strict));
        tys = tps.ConvertAll(tp => (Type)(new UserDefinedType(tp)));
        var id = new BoundVar(tok, "f", new ArrowType(tok, arrowDecl, tys));
        var partialArrow = new SubsetTypeDecl(tok, ArrowType.PartialArrowTypeName(arity),
          new TypeParameter.TypeParameterCharacteristics(false), tps, SystemModule,
          id, ArrowSubtypeConstraint(tok, id, reads, tps, false), SubsetTypeDecl.WKind.Special, null, DontCompile());
        PartialArrowTypeDecls.Add(arity, partialArrow);
        SystemModule.TopLevelDecls.Add(partialArrow);

        // declaration of total arrow-type

        tps = Util.Map(Enumerable.Range(0, arity + 1), x => x < arity ?
          new TypeParameter(tok, "T" + x, TypeParameter.TPVarianceSyntax.Contravariance) :
          new TypeParameter(tok, "R", TypeParameter.TPVarianceSyntax.Covariant_Strict));
        tys = tps.ConvertAll(tp => (Type)(new UserDefinedType(tp)));
        id = new BoundVar(tok, "f", new UserDefinedType(tok, partialArrow.Name, partialArrow, tys));
        var totalArrow = new SubsetTypeDecl(tok, ArrowType.TotalArrowTypeName(arity),
          new TypeParameter.TypeParameterCharacteristics(false), tps, SystemModule,
          id, ArrowSubtypeConstraint(tok, id, req, tps, true), SubsetTypeDecl.WKind.Special, null, DontCompile());
        TotalArrowTypeDecls.Add(arity, totalArrow);
        SystemModule.TopLevelDecls.Add(totalArrow);
      }
    }

    /// <summary>
    /// Returns an expression that is the constraint of:
    /// the built-in partial-arrow type (if "!total", in which case "member" is expected to denote the "reads" member), or
    /// the built-in total-arrow type (if "total", in which case "member" is expected to denote the "requires" member).
    /// The given "id" is expected to be already resolved.
    /// </summary>
    private Expression ArrowSubtypeConstraint(IToken tok, BoundVar id, Function member, List<TypeParameter> tps, bool total) {
      Contract.Requires(tok != null);
      Contract.Requires(id != null);
      Contract.Requires(member != null);
      Contract.Requires(tps != null && 1 <= tps.Count);
      var f = new IdentifierExpr(tok, id);
      // forall x0,x1,x2 :: f.reads(x0,x1,x2) == {}
      // OR
      // forall x0,x1,x2 :: f.requires(x0,x1,x2)
      var bvs = new List<BoundVar>();
      var args = new List<Expression>();
      var bounds = new List<ComprehensionExpr.BoundedPool>();
      for (int i = 0; i < tps.Count - 1; i++) {
        var bv = new BoundVar(tok, "x" + i, new UserDefinedType(tps[i]));
        bvs.Add(bv);
        args.Add(new IdentifierExpr(tok, bv));
        bounds.Add(new ComprehensionExpr.SpecialAllocIndependenceAllocatedBoundedPool());
      }
      var fn = new MemberSelectExpr(tok, f, member.Name) {
        Member = member,
        TypeApplication_AtEnclosingClass = f.Type.TypeArgs,
        TypeApplication_JustMember = new List<Type>(),
        Type = GetTypeOfFunction(member, tps.ConvertAll(tp => (Type)new UserDefinedType(tp)), new List<Type>())
      };
      Expression body = new ApplyExpr(tok, fn, args);
      body.Type = member.ResultType;  // resolve here
      if (!total) {
        Expression emptySet = new SetDisplayExpr(tok, true, new List<Expression>());
        emptySet.Type = member.ResultType;  // resolve here
        body = Expression.CreateEq(body, emptySet, member.ResultType);
      }
      if (tps.Count > 1) {
        body = new ForallExpr(tok, bvs, null, body, null) { Type = Type.Bool, Bounds = bounds };
      }
      return body;
    }

    Type GetTypeOfFunction(Function f, List<Type> typeArgumentsClass, List<Type> typeArgumentsMember) {
      Contract.Requires(f != null);
      Contract.Requires(f.EnclosingClass != null);
      Contract.Requires(typeArgumentsClass != null);
      Contract.Requires(typeArgumentsMember != null);
      Contract.Requires(typeArgumentsClass.Count == f.EnclosingClass.TypeArgs.Count);
      Contract.Requires(typeArgumentsMember.Count == f.TypeArgs.Count);

      var atd = ArrowTypeDecls[f.Formals.Count];

      var formals = Util.Concat(f.EnclosingClass.TypeArgs, f.TypeArgs);
      var actuals = Util.Concat(typeArgumentsClass, typeArgumentsMember);
      var typeMap = Resolver.TypeSubstitutionMap(formals, actuals);
      return new ArrowType(f.tok, atd, f.Formals.ConvertAll(arg => Resolver.SubstType(arg.Type, typeMap)), Resolver.SubstType(f.ResultType, typeMap));
    }

    private object MakeTupleKey(List<bool> isGhost, int dims) {
      if (dims == 0) {
        return 0;
      } else {
        var g = isGhost[dims - 1];
        return Tuple.Create(g, MakeTupleKey(isGhost, dims - 1));
      }
    }

    public TupleTypeDecl TupleType(IToken tok, int dims, bool allowCreationOfNewType, List<bool> argumentGhostness = null) {
      Contract.Requires(tok != null);
      Contract.Requires(0 <= dims);
      Contract.Ensures(Contract.Result<TupleTypeDecl>() != null);

      TupleTypeDecl tt;
      argumentGhostness = argumentGhostness ?? new bool[dims].Select(_ => false).ToList();
      object key = MakeTupleKey(argumentGhostness, dims);
      if (!tupleTypeDecls.TryGetValue(key, out tt)) {
        Contract.Assume(allowCreationOfNewType);  // the parser should ensure that all needed tuple types exist by the time of resolution
        // tuple#2 is already defined in DafnyRuntime.cs
        var attributes = dims == 2 && !argumentGhostness.Contains(true) ? DontCompile() : null;
        tt = new TupleTypeDecl(argumentGhostness, SystemModule, attributes);
        tupleTypeDecls.Add(key, tt);
        SystemModule.TopLevelDecls.Add(tt);
      }
      return tt;
    }

    public static char IsGhostToChar(bool isGhost) {
      return isGhost ? 'G' : 'O';
    }

    public static bool IsGhostFromChar(char c) {
      Contract.Requires(c == 'G' || c == 'O');
      return c == 'G';
    }

    public static string ArgumentGhostnessToString(List<bool> argumentGhostness) {
      return argumentGhostness.Count + (!argumentGhostness.Contains(true)
        ? "" : String.Concat(argumentGhostness.Select(IsGhostToChar)));
    }

    public static IEnumerable<bool> ArgumentGhostnessFromString(string s, int count) {
      List<bool> argumentGhostness = new bool[count].ToList();
      if (System.Char.IsDigit(s[s.Length - 1])) {
        return argumentGhostness.Select(_ => false);
      } else {
        return argumentGhostness.Select((_, i) => IsGhostFromChar(s[s.Length - count + i]));
      }
    }

    public static string TupleTypeName(List<bool> argumentGhostness) {
      return "_tuple#" + ArgumentGhostnessToString(argumentGhostness);
    }
    
    public static bool IsTupleTypeName(string s) {
      Contract.Requires(s != null);
      return s.StartsWith("_tuple#");
    }
    public const string TupleTypeCtorNamePrefix = "_#Make";  // the printer wants this name prefix to be uniquely recognizable
  }

  /// <summary>
  /// A class implementing this interface is one that can carry attributes.
  /// </summary>
  public interface IAttributeBearingDeclaration
  {
  }

  public class Attributes {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Name != null);
      Contract.Invariant(cce.NonNullElements(Args));
    }

    public string Name;
    /*Frozen*/
    public readonly List<Expression> Args;
    public readonly Attributes Prev;

    public Attributes(string name, [Captured] List<Expression> args, Attributes prev) {
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(args));
      Name = name;
      Args = args;
      Prev = prev;
    }

    public static IEnumerable<Expression> SubExpressions(Attributes attrs) {
      return attrs.AsEnumerable().SelectMany(aa => aa.Args);
    }

    public static bool Contains(Attributes attrs, string nm) {
      Contract.Requires(nm != null);
      return attrs.AsEnumerable().Any(aa => aa.Name == nm);
    }

    /// <summary>
    /// Returns true if "nm" is a specified attribute.  If it is, then:
    /// - if the attribute is {:nm true}, then value==true
    /// - if the attribute is {:nm false}, then value==false
    /// - if the attribute is anything else, then value returns as whatever it was passed in as.
    /// </summary>
    [Pure]
    public static bool ContainsBool(Attributes attrs, string nm, ref bool value) {
      Contract.Requires(nm != null);
      foreach (var attr in attrs.AsEnumerable()) {
        if (attr.Name == nm) {
          if (attr.Args.Count == 1) {
            var arg = attr.Args[0] as LiteralExpr;
            if (arg != null && arg.Value is bool) {
              value = (bool)arg.Value;
            }
          }
          return true;
        }
      }
      return false;
    }

    /// <summary>
    /// Checks whether a Boolean attribute has been set on the declaration itself,
    /// the enclosing class, or any enclosing module.  Settings closer to the declaration
    /// override those further away.
    /// </summary>
    public static bool ContainsBoolAtAnyLevel(MemberDecl decl, string attribName) {
      bool setting = true;
      if (Attributes.ContainsBool(decl.Attributes, attribName, ref setting)) {
        return setting;
      }

      if (Attributes.ContainsBool(decl.EnclosingClass.Attributes, attribName, ref setting)) {
        return setting;
      }

      // Check the entire stack of modules
      var mod = decl.EnclosingClass.EnclosingModuleDefinition;
      while (mod != null) {
        if (Attributes.ContainsBool(mod.Attributes, attribName, ref setting)) {
          return setting;
        }
        mod = mod.EnclosingModule;
      }

      return false;
    }

    /// <summary>
    /// Returns list of expressions if "nm" is a specified attribute:
    /// - if the attribute is {:nm e1,...,en}, then returns (e1,...,en)
    /// Otherwise, returns null.
    /// </summary>
    public static List<Expression> FindExpressions(Attributes attrs, string nm) {
      Contract.Requires(nm != null);
      foreach (var attr in attrs.AsEnumerable()) {
        if (attr.Name == nm) {
          return attr.Args;
        }
      }
      return null;
    }

    /// <summary>
    /// Same as FindExpressions, but returns all matches
    /// </summary>
    public static List<List<Expression>> FindAllExpressions(Attributes attrs, string nm) {
      Contract.Requires(nm != null);
      List<List<Expression>> ret = null;
      for (; attrs != null; attrs = attrs.Prev) {
        if (attrs.Name == nm) {
          ret = ret ?? new List<List<Expression>>();   // Avoid allocating the list in the common case where we don't find nm
          ret.Add(attrs.Args);
        }
      }
      return ret;
    }

    /// <summary>
    /// Returns true if "nm" is a specified attribute whose arguments match the "allowed" parameter.
    /// - if "nm" is not found in attrs, return false and leave value unmodified.  Otherwise,
    /// - if "allowed" contains Empty and the Args contains zero elements, return true and leave value unmodified.  Otherwise,
    /// - if "allowed" contains Bool and Args contains one bool literal, return true and set value to the bool literal.  Otherwise,
    /// - if "allowed" contains Int and Args contains one BigInteger literal, return true and set value to the BigInteger literal.  Otherwise,
    /// - if "allowed" contains String and Args contains one string literal, return true and set value to the string literal.  Otherwise,
    /// - if "allowed" contains Expression and Args contains one element, return true and set value to the one element (of type Expression).  Otherwise,
    /// - return false, leave value unmodified, and call reporter with an error string.
    /// </summary>
    public enum MatchingValueOption { Empty, Bool, Int, String, Expression }
    public static bool ContainsMatchingValue(Attributes attrs, string nm, ref object value, IEnumerable<MatchingValueOption> allowed, Action<string> reporter) {
      Contract.Requires(nm != null);
      Contract.Requires(allowed != null);
      Contract.Requires(reporter != null);
      List<Expression> args = FindExpressions(attrs, nm);
      if (args == null) {
        return false;
      } else if (args.Count == 0) {
        if (allowed.Contains(MatchingValueOption.Empty)) {
          return true;
        } else {
          reporter("Attribute " + nm + " requires one argument");
          return false;
        }
      } else if (args.Count == 1) {
        Expression arg = args[0];
        StringLiteralExpr stringLiteral = arg as StringLiteralExpr;
        LiteralExpr literal = arg as LiteralExpr;
        if (literal != null && literal.Value is bool && allowed.Contains(MatchingValueOption.Bool)) {
          value = literal.Value;
          return true;
        } else if (literal != null && literal.Value is BigInteger && allowed.Contains(MatchingValueOption.Int)) {
          value = literal.Value;
          return true;
        } else if (stringLiteral != null && stringLiteral.Value is string && allowed.Contains(MatchingValueOption.String)) {
          value = stringLiteral.Value;
          return true;
        } else if (allowed.Contains(MatchingValueOption.Expression)) {
          value = arg;
          return true;
        } else {
          reporter("Attribute " + nm + " expects an argument in one of the following categories: " + String.Join(", ", allowed));
          return false;
        }
      } else {
        reporter("Attribute " + nm + " cannot have more than one argument");
        return false;
      }
    }
  }

  public static class AttributesExtensions {
    /// <summary>
    /// By making this an extension method, it can also be invoked for a null receiver.
    /// </summary>
    public static IEnumerable<Attributes> AsEnumerable(this Attributes attr) {
      while (attr != null) {
        yield return attr;
        attr = attr.Prev;
      }
    }
  }

  public class UserSuppliedAttributes : Attributes
  {
    public readonly IToken tok;  // may be null, if the attribute was constructed internally
    public readonly IToken OpenBrace;
    public readonly IToken CloseBrace;
    public bool Recognized;  // set to true to indicate an attribute that is processed by some part of Dafny; this allows it to be colored in the IDE
    public UserSuppliedAttributes(IToken tok, IToken openBrace, IToken closeBrace, List<Expression> args, Attributes prev)
      : base(tok.val, args, prev) {
      Contract.Requires(tok != null);
      Contract.Requires(openBrace != null);
      Contract.Requires(closeBrace != null);
      Contract.Requires(args != null);
      this.tok = tok;
      OpenBrace = openBrace;
      CloseBrace = closeBrace;
    }
  }

  public class VisibilityScope {
    private static uint maxScopeID = 0;

    private SortedSet<uint> scopeTokens = new SortedSet<uint>();

    // Only for debugging
    private SortedSet<string> scopeIds = new SortedSet<string>();

    private bool overlaps(SortedSet<uint> set1, SortedSet<uint> set2) {
      if (set1.Count < set2.Count) {
        return set2.Overlaps(set1);
      } else {
        return set1.Overlaps(set2);
      }
    }

    private Dictionary<VisibilityScope, Tuple<int, bool>> cached = new Dictionary<VisibilityScope, Tuple<int, bool>>();

    //By convention, the "null" scope sees all
    public bool VisibleInScope(VisibilityScope other) {
      if (other != null) {
        Tuple<int, bool> result;
        if (cached.TryGetValue(other, out result)) {
          if (result.Item1 == other.scopeTokens.Count) {
            return result.Item2;
          } else {
            if (result.Item2) {
              return true;
            }
          }
        }
        var isoverlap = overlaps(other.scopeTokens, this.scopeTokens);
        cached[other] = new Tuple<int, bool>(other.scopeTokens.Count, isoverlap);
        return isoverlap;

      }
      return true;
    }

    [Pure]
    public bool IsEmpty() {
      return scopeTokens.Count == 0;
    }

    //However augmenting with a null scope does nothing
    public void Augment(VisibilityScope other) {
      if (other != null) {
        scopeTokens.UnionWith(other.scopeTokens);
        scopeIds.UnionWith(other.scopeIds);
        cached.Clear();
      }
    }

    public VisibilityScope(string name) {
      scopeTokens.Add(maxScopeID);
      scopeIds.Add(name);
      if (maxScopeID == uint.MaxValue) {
        Contract.Assert(false);
      }
      maxScopeID++;
    }

    public VisibilityScope() {
    }

  }

  // ------------------------------------------------------------------------------------------------------

  public abstract class Type {
    public static readonly BoolType Bool = new BoolType();
    public static readonly CharType Char = new CharType();
    public static readonly IntType Int = new IntType();
    public static readonly RealType Real = new RealType();
    public static Type Nat() { return new UserDefinedType(Token.NoToken, "nat", null); }  // note, this returns an unresolved type
    public static Type String() { return new UserDefinedType(Token.NoToken, "string", null); }  // note, this returns an unresolved type
    public static readonly BigOrdinalType BigOrdinal = new BigOrdinalType();

    [ThreadStatic]
    private static List<VisibilityScope> scopes = new List<VisibilityScope>();

    [ThreadStatic]
    private static bool scopesEnabled = false;

    public static void PushScope(VisibilityScope scope) {
      scopes.Add(scope);
    }

    public static void ResetScopes() {
      scopes = new List<VisibilityScope>();
      scopesEnabled = false;
    }

    public static void PopScope() {
      Contract.Assert(scopes.Count > 0);
      scopes.RemoveAt(scopes.Count - 1);
    }

    public static void PopScope(VisibilityScope expected) {
      Contract.Assert(scopes.Count > 0);
      Contract.Assert(scopes[scopes.Count - 1] == expected);
      PopScope();
    }

    public static VisibilityScope GetScope() {
      if (scopes.Count > 0 && scopesEnabled) {
        return scopes[scopes.Count - 1];
      }
      return null;
    }

    public static void EnableScopes() {
      Contract.Assert(!scopesEnabled);
      scopesEnabled = true;
    }

    public static void DisableScopes() {
      Contract.Assert(scopesEnabled);
      scopesEnabled = false;
    }

    public static string TypeArgsToString(ModuleDefinition/*?*/ context, List<Type> typeArgs, bool parseAble = false) {
      Contract.Requires(typeArgs == null ||
        (typeArgs.All(ty => ty != null && ty.TypeName(context, parseAble) != null) &&
         (typeArgs.All(ty => ty.TypeName(context, parseAble).StartsWith("_")) ||
          typeArgs.All(ty => !ty.TypeName(context, parseAble).StartsWith("_")))));

      if (typeArgs != null && typeArgs.Count > 0 &&
          (!parseAble || !typeArgs[0].TypeName(context, parseAble).StartsWith("_"))) {
        return string.Format("<{0}>",Util.Comma(typeArgs, ty => ty.TypeName(context, parseAble)));
      }
      return "";
    }

    public static string TypeArgsToString(List<Type> typeArgs, bool parseAble = false) {
      return TypeArgsToString(null, typeArgs, parseAble);
    }

    public string TypeArgsToString(ModuleDefinition/*?*/ context, bool parseAble = false) {
      return Type.TypeArgsToString(context, this.TypeArgs, parseAble);
    }

    // Type arguments to the type
    public List<Type> TypeArgs = new List<Type>();

    /// <summary>
    /// Add to "tps" the free type parameters in "this".
    /// Requires the type to be resolved.
    /// </summary>
    public void AddFreeTypeParameters(ISet<TypeParameter> tps) {
      Contract.Requires(tps != null);
      var ty = this.NormalizeExpandKeepConstraints();
      var tp = ty.AsTypeParameter;
      if (tp != null) {
        tps.Add(tp);
      }
      foreach (var ta in ty.TypeArgs) {
        ta.AddFreeTypeParameters(tps);
      }
    }

    [Pure]
    public abstract string TypeName(ModuleDefinition/*?*/ context, bool parseAble = false);
    [Pure]
    public override string ToString() {
      return TypeName(null, false);
    }

    /// <summary>
    /// Return the most constrained version of "this", getting to the bottom of proxies.
    /// </summary>
    public Type Normalize() {
      Contract.Ensures(Contract.Result<Type>() != null);
      Type type = this;
      while (true) {
        var pt = type as TypeProxy;
        if (pt != null && pt.T != null) {
          type = pt.T;
        } else {
          return type;
        }
      }
    }

    /// <summary>
    /// Return the type that "this" stands for, getting to the bottom of proxies and following type synonyms.
    /// </summary>
    [Pure]
    public Type NormalizeExpand(bool keepConstraints = false) {
      Contract.Ensures(Contract.Result<Type>() != null);
      Contract.Ensures(!(Contract.Result<Type>() is TypeProxy) || ((TypeProxy)Contract.Result<Type>()).T == null);  // return a proxy only if .T == null
      Type type = this;
      while (true) {

        var pt = type as TypeProxy;
        if (pt != null && pt.T != null) {
          type = pt.T;
          continue;
        }

        var scope = Type.GetScope();
        var rtd = type.AsRevealableType;
        if (rtd != null) {
          var udt = (UserDefinedType)type;

          if (!rtd.AsTopLevelDecl.IsVisibleInScope(scope)) {
            // This can only mean "rtd" is a class/trait that is only provided, not revealed. For a provided class/trait,
            // it is the non-null type declaration that is visible, not the class/trait declaration itself.
            if (rtd is ClassDecl cl) {
              Contract.Assert(cl.NonNullTypeDecl != null);
              Contract.Assert(cl.NonNullTypeDecl.IsVisibleInScope(scope));
            } else {
              Contract.Assert(rtd is OpaqueTypeDecl);
            }
          }

          if (rtd.IsRevealedInScope(scope)) {
            if (rtd is TypeSynonymDecl && (!(rtd is SubsetTypeDecl) || !keepConstraints)) {
              type = ((TypeSynonymDecl)rtd).RhsWithArgumentIgnoringScope(udt.TypeArgs);
              continue;
            } else {
              return type;
            }
          } else { // type is hidden, no more normalization is possible
            return rtd.SelfSynonym(type.TypeArgs);
          }
        }

        //A hidden type may become visible in another scope
        var isyn = type.AsInternalTypeSynonym;
        if (isyn != null) {
          var udt = (UserDefinedType)type;

          if (!isyn.IsVisibleInScope(scope)) {
            // This can only mean "isyn" refers to a class/trait that is only provided, not revealed. For a provided class/trait,
            // it is the non-null type declaration that is visible, not the class/trait declaration itself.
            var rhs = isyn.RhsWithArgumentIgnoringScope(udt.TypeArgs);
            Contract.Assert(rhs is UserDefinedType);
            var cl = ((UserDefinedType)rhs).ResolvedClass as ClassDecl;
            Contract.Assert(cl != null && cl.NonNullTypeDecl != null);
            Contract.Assert(cl.NonNullTypeDecl.IsVisibleInScope(scope));
          }

          if (isyn.IsRevealedInScope(scope)) {
            type = isyn.RhsWithArgument(udt.TypeArgs);
            continue;
          } else {
            return type;
          }
        }

        return type;
      }
    }

    /// <summary>
    /// Return the type that "this" stands for, getting to the bottom of proxies and following type synonyms, but does
    /// not follow subset types.
    /// </summary>
    [Pure]
    public Type NormalizeExpandKeepConstraints() {
      return NormalizeExpand(true);
    }

    /// <summary>
    /// Return "the type that "this" stands for, getting to the bottom of proxies and following type synonyms.
    /// </summary>
    public Type UseInternalSynonym() {
      Contract.Ensures(Contract.Result<Type>() != null);
      Contract.Ensures(!(Contract.Result<Type>() is TypeProxy) || ((TypeProxy)Contract.Result<Type>()).T == null);  // return a proxy only if .T == null

      Type type = Normalize();
      var scope = Type.GetScope();
      var rtd = type.AsRevealableType;
      if (rtd != null) {
        var udt = (UserDefinedType)type;
        if (!rtd.AsTopLevelDecl.IsVisibleInScope(scope)) {
          // This can only mean "rtd" is a class/trait that is only provided, not revealed. For a provided class/trait,
          // it is the non-null type declaration that is visible, not the class/trait declaration itself.
          var cl = rtd as ClassDecl;
          Contract.Assert(cl != null && cl.NonNullTypeDecl != null);
          Contract.Assert(cl.NonNullTypeDecl.IsVisibleInScope(scope));
        }
        if (!rtd.IsRevealedInScope(scope)) {
          return rtd.SelfSynonym(type.TypeArgs, udt.NamePath);
        }
      }

      return type;
    }

    /// <summary>
    /// Returns whether or not "this" and "that" denote the same type, modulo proxies and type synonyms and subset types.
    /// </summary>
    [Pure]
    public abstract bool Equals(Type that, bool keepConstraints = false);

    public bool IsBoolType { get { return NormalizeExpand() is BoolType; } }
    public bool IsCharType { get { return NormalizeExpand() is CharType; } }
    public bool IsIntegerType { get { return NormalizeExpand() is IntType; } }
    public bool IsRealType { get { return NormalizeExpand() is RealType; } }
    public bool IsBigOrdinalType { get { return NormalizeExpand() is BigOrdinalType; } }
    public bool IsBitVectorType { get { return AsBitVectorType != null; } }
    public BitvectorType AsBitVectorType { get { return NormalizeExpand() as BitvectorType; } }
    public bool IsNumericBased() {
      var t = NormalizeExpand();
      return t.IsIntegerType || t.IsRealType || t.AsNewtype != null;
    }
    public enum NumericPersuasion { Int, Real }
    [Pure]
    public bool IsNumericBased(NumericPersuasion p) {
      Type t = this;
      while (true) {
        t = t.NormalizeExpand();
        if (t.IsIntegerType) {
          return p == NumericPersuasion.Int;
        } else if (t.IsRealType) {
          return p == NumericPersuasion.Real;
        }
        var d = t.AsNewtype;
        if (d == null) {
          return false;
        }
        t = d.BaseType;
      }
    }

    /// <summary>
    /// This property returns true if the type is known to be nonempty.
    /// This property should be used only after successful resolution. It is assumed that all type proxies have
    /// been resolved and that all recursion through types comes to an end.
    /// Note, HasCompilableValue ==> IsNonEmpty.
    /// </summary>
    public bool IsNonempty => GetAutoInit() != AutoInitInfo.MaybeEmpty;

    /// <summary>
    /// This property returns true if the type has a known compilable value.
    /// This property should be used only after successful resolution. It is assumed that all type proxies have
    /// been resolved and that all recursion through types comes to an end.
    /// Note, HasCompilableValue ==> IsNonEmpty.
    /// </summary>
    public bool HasCompilableValue => GetAutoInit() == AutoInitInfo.CompilableValue;

    public bool KnownToHaveToAValue(bool ghostContext) {
      return ghostContext ? IsNonempty : HasCompilableValue;
    }

    public enum AutoInitInfo { MaybeEmpty, Nonempty, CompilableValue }

    /// <summary>
    /// This property returns
    ///     - CompilableValue, if the type has a known compilable value
    ///     - Nonempty,        if the type is known to contain some value
    ///     - MaybeEmpty,      otherwise
    /// This property should be used only after successful resolution. It is assumed that all type proxies have
    /// been resolved and that all recursion through types comes to an end.
    /// </summary>
    public AutoInitInfo GetAutoInit(List<UserDefinedType>/*?*/ coDatatypesBeingVisited = null) {
      var t = NormalizeExpandKeepConstraints();
      Contract.Assume(t is NonProxyType); // precondition

      AutoInitInfo CharacteristicToAutoInitInfo(TypeParameter.TypeParameterCharacteristics c) {
        if (c.HasCompiledValue) {
          return AutoInitInfo.CompilableValue;
        } else if (c.IsNonempty) {
          return AutoInitInfo.Nonempty;
        } else {
          return AutoInitInfo.MaybeEmpty;
        }
      }

      if (t is BoolType || t is CharType || t is IntType || t is BigOrdinalType || t is RealType || t is BitvectorType) {
        return AutoInitInfo.CompilableValue;
      } else if (t is CollectionType) {
        return AutoInitInfo.CompilableValue;
      }

      var udt = (UserDefinedType)t;
      var cl = udt.ResolvedClass;
      Contract.Assert(cl != null);
      if (cl is OpaqueTypeDecl) {
        var otd = (OpaqueTypeDecl)cl;
        return CharacteristicToAutoInitInfo(otd.Characteristics);
      } else if (cl is TypeParameter) {
        var tp = (TypeParameter)cl;
        return CharacteristicToAutoInitInfo(tp.Characteristics);
      } else if (cl is InternalTypeSynonymDecl) {
        var isyn = (InternalTypeSynonymDecl)cl;
        return CharacteristicToAutoInitInfo(isyn.Characteristics);
      } else if (cl is NewtypeDecl) {
        var td = (NewtypeDecl)cl;
        switch (td.WitnessKind) {
          case SubsetTypeDecl.WKind.CompiledZero:
          case SubsetTypeDecl.WKind.Compiled:
            return AutoInitInfo.CompilableValue;
          case SubsetTypeDecl.WKind.Ghost:
            return AutoInitInfo.Nonempty;
          case SubsetTypeDecl.WKind.OptOut:
            return AutoInitInfo.MaybeEmpty;
          case SubsetTypeDecl.WKind.Special:
          default:
            Contract.Assert(false); // unexpected case
            throw new cce.UnreachableException();
        }
      } else if (cl is SubsetTypeDecl) {
        var td = (SubsetTypeDecl)cl;
        switch (td.WitnessKind) {
          case SubsetTypeDecl.WKind.CompiledZero:
          case SubsetTypeDecl.WKind.Compiled:
            return AutoInitInfo.CompilableValue;
          case SubsetTypeDecl.WKind.Ghost:
            return AutoInitInfo.Nonempty;
          case SubsetTypeDecl.WKind.OptOut:
            return AutoInitInfo.MaybeEmpty;
          case SubsetTypeDecl.WKind.Special:
            // WKind.Special is only used with -->, ->, and non-null types:
            Contract.Assert(ArrowType.IsPartialArrowTypeName(td.Name) || ArrowType.IsTotalArrowTypeName(td.Name) || td is NonNullTypeDecl);
            if (ArrowType.IsPartialArrowTypeName(td.Name)) {
              // partial arrow
              return AutoInitInfo.CompilableValue;
            } else if (ArrowType.IsTotalArrowTypeName(td.Name)) {
              // total arrow
              return udt.TypeArgs.Last().GetAutoInit(coDatatypesBeingVisited);
            } else if (((NonNullTypeDecl)td).Class is ArrayClassDecl) {
              // non-null array type; we know how to initialize them
              return AutoInitInfo.CompilableValue;
            } else {
              // non-null (non-array) type
              return AutoInitInfo.MaybeEmpty;
            }
          default:
            Contract.Assert(false); // unexpected case
            throw new cce.UnreachableException();
        }
      } else if (cl is ClassDecl) {
        return AutoInitInfo.CompilableValue; // null is a value of this type
      } else if (cl is DatatypeDecl) {
        var dt = (DatatypeDecl)cl;
        var subst = Resolver.TypeSubstitutionMap(dt.TypeArgs, udt.TypeArgs);
        var r = AutoInitInfo.CompilableValue;  // assume it's compilable, until we find out otherwise
        if (cl is CoDatatypeDecl) {
          if (coDatatypesBeingVisited != null) {
            if (coDatatypesBeingVisited.Exists(coType => udt.Equals(coType))) {
              // This can be compiled into a lazy constructor call
              return AutoInitInfo.CompilableValue;
            } else if (coDatatypesBeingVisited.Exists(coType => dt == coType.ResolvedClass)) {
              // This requires more recursion and bookkeeping than we care to try out
              return AutoInitInfo.MaybeEmpty;
            }
            coDatatypesBeingVisited = new List<UserDefinedType>(coDatatypesBeingVisited);
          } else {
            coDatatypesBeingVisited = new List<UserDefinedType>();
          }
          coDatatypesBeingVisited.Add(udt);
        }
        foreach (var formal in dt.GetGroundingCtor().Formals) {
          var autoInit = Resolver.SubstType(formal.Type, subst).GetAutoInit(coDatatypesBeingVisited);
          if (autoInit == AutoInitInfo.MaybeEmpty) {
            return AutoInitInfo.MaybeEmpty;
          } else if (formal.IsGhost) {
            // cool
          } else if (autoInit == AutoInitInfo.CompilableValue) {
            // cool
          } else {
            r = AutoInitInfo.Nonempty;
          }
        }
        return r;
      } else {
        Contract.Assert(false); // unexpected type
        throw new cce.UnreachableException();
      }
    }

    public bool HasFinitePossibleValues {
      get {
        if (IsBoolType || IsCharType || IsRefType) {
          return true;
        }
        var st = AsSetType;
        if (st != null && st.Arg.HasFinitePossibleValues) {
          return true;
        }
        var mt = AsMapType;
        if (mt != null && mt.Domain.HasFinitePossibleValues) {
          return true;
        }
        var dt = AsDatatype;
        if (dt != null && dt.HasFinitePossibleValues) {
          return true;
        }
        return false;
      }
    }

    public bool IsAllocFree {
      get {
        if (IsRefType) {
          return false;
        } else if (IsTypeParameter) {
          return AsTypeParameter.Characteristics.ContainsNoReferenceTypes;
        } else if (IsOpaqueType) {
          return AsOpaqueType.Characteristics.ContainsNoReferenceTypes;
        } else {
          return TypeArgs.All(ta => ta.IsAllocFree);
        }
      }
    }

    public CollectionType AsCollectionType { get { return NormalizeExpand() as CollectionType; } }
    public SetType AsSetType { get { return NormalizeExpand() as SetType; } }
    public MultiSetType AsMultiSetType { get { return NormalizeExpand() as MultiSetType; } }
    public SeqType AsSeqType { get { return NormalizeExpand() as SeqType; } }
    public MapType AsMapType { get { return NormalizeExpand() as MapType; } }

    public bool IsRefType {
      get {
        var udt = NormalizeExpand() as UserDefinedType;
        return udt != null && udt.ResolvedClass is ClassDecl && !(udt.ResolvedClass is ArrowTypeDecl);
      }
    }

    public bool IsTopLevelTypeWithMembers {
      get {
        return AsTopLevelTypeWithMembers != null;
      }
    }
    public TopLevelDeclWithMembers/*?*/ AsTopLevelTypeWithMembers {
      get {
        var udt = NormalizeExpand() as UserDefinedType;
        return udt?.ResolvedClass as TopLevelDeclWithMembers;
      }
    }
    public TopLevelDeclWithMembers/*?*/ AsTopLevelTypeWithMembersBypassInternalSynonym {
      get {
        var udt = NormalizeExpand() as UserDefinedType;
        if (udt != null && udt.ResolvedClass is InternalTypeSynonymDecl isyn) {
          udt = isyn.RhsWithArgumentIgnoringScope(udt.TypeArgs) as UserDefinedType;
          if (udt?.ResolvedClass is NonNullTypeDecl nntd) {
            return nntd.Class;
          }
        }
        return udt?.ResolvedClass as TopLevelDeclWithMembers;
      }
    }
    /// <summary>
    /// Returns "true" if the type represents the type "object?".
    /// </summary>
    public bool IsObjectQ {
      get {
        var udt = NormalizeExpandKeepConstraints() as UserDefinedType;
        return udt != null && udt.ResolvedClass is ClassDecl && ((ClassDecl)udt.ResolvedClass).IsObjectTrait;
      }
    }
    /// <summary>
    /// Returns "true" if the type represents the type "object".
    /// </summary>
    public bool IsObject {
      get {
        var nn = AsNonNullRefType;
        if (nn != null) {
          var nonNullRefDecl = (NonNullTypeDecl)nn.ResolvedClass;
          return nonNullRefDecl.Class.IsObjectTrait;
        }
        return false;
      }
    }
    /// <summary>
    /// Returns "true" if the type is a non-null type or any subset type thereof.
    /// </summary>
    public bool IsNonNullRefType {
      get {
        return AsNonNullRefType != null;
      }
    }
    /// <summary>
    /// If the type is a non-null type or any subset type thereof, return the UserDefinedType whose
    /// .ResolvedClass value is a NonNullTypeDecl.
    /// Otherwise, return "null".
    /// </summary>
    public UserDefinedType AsNonNullRefType {
      get {
        var t = this;
        while (true) {
          var udt = t.NormalizeExpandKeepConstraints() as UserDefinedType;
          if (udt == null) {
            return null;
          }
          if (udt.ResolvedClass is NonNullTypeDecl) {
            return udt;
          }
          var sst = udt.ResolvedClass as SubsetTypeDecl;
          if (sst != null) {
            t = sst.RhsWithArgument(udt.TypeArgs);  // continue the search up the chain of subset types
          } else {
            return null;
          }
        }
      }
    }
    /// <summary>
    /// Returns the type "parent<X>", where "X" is a list of type parameters that makes "parent<X>" a supertype of "this".
    /// Requires "this" to be some type "C<Y>" and "parent" to be among the reflexive, transitive parent traits of "C".
    /// </summary>
    public UserDefinedType AsParentType(TopLevelDecl parent) {
      Contract.Requires(parent != null);

      var udt = (UserDefinedType)NormalizeExpand();
      if (udt.ResolvedClass is InternalTypeSynonymDecl isyn) {
        udt = isyn.RhsWithArgumentIgnoringScope(udt.TypeArgs) as UserDefinedType;
      }
      TopLevelDeclWithMembers cl;
      if (udt.ResolvedClass is NonNullTypeDecl nntd) {
        cl = (TopLevelDeclWithMembers)nntd.ViewAsClass;
      } else {
        cl = (TopLevelDeclWithMembers)udt.ResolvedClass;
      }
      if (cl == parent) {
        return udt;
      }
      var typeMapParents = cl.ParentFormalTypeParametersToActuals;
      var typeMapUdt = Resolver.TypeSubstitutionMap(cl.TypeArgs, udt.TypeArgs);
      var typeArgs = parent.TypeArgs.ConvertAll(tp => Resolver.SubstType(typeMapParents[tp], typeMapUdt));
      return new UserDefinedType(udt.tok, parent.Name, parent, typeArgs);
    }
    public bool IsTraitType {
      get {
        return AsTraitType != null;
      }
    }
    public TraitDecl/*?*/ AsTraitType {
      get {
        var udt = NormalizeExpand() as UserDefinedType;
        return udt?.ResolvedClass as TraitDecl;
      }
    }
    public bool IsArrayType {
      get {
        return AsArrayType != null;
      }
    }
    public ArrayClassDecl/*?*/ AsArrayType {
      get {
        var t = NormalizeExpand();
        var udt = UserDefinedType.DenotesClass(t);
        return udt?.ResolvedClass as ArrayClassDecl;
      }
    }
    /// <summary>
    /// Returns "true" if the type is one of the 3 built-in arrow types.
    /// </summary>
    public bool IsBuiltinArrowType {
      get {
        var t = Normalize();  // but don't expand synonyms or strip off constraints
        if (t is ArrowType) {
          return true;
        }
        var udt = t as UserDefinedType;
        return udt != null && (ArrowType.IsPartialArrowTypeName(udt.Name) || ArrowType.IsTotalArrowTypeName(udt.Name));
      }
    }
    /// <summary>
    /// Returns "true" if the type is a partial arrow or any subset type thereof.
    /// </summary>
    public bool IsArrowTypeWithoutReadEffects {
      get {
        var t = this;
        while (true) {
          var udt = t.NormalizeExpandKeepConstraints() as UserDefinedType;
          if (udt == null) {
            return false;
          } else if (ArrowType.IsPartialArrowTypeName(udt.Name)) {
            return true;
          }
          var sst = udt.ResolvedClass as SubsetTypeDecl;
          if (sst != null) {
            t = sst.RhsWithArgument(udt.TypeArgs);  // continue the search up the chain of subset types
          } else {
            return false;
          }
        }
      }
    }
    /// <summary>
    /// Returns "true" if the type is a total arrow or any subset type thereof.
    /// </summary>
    public bool IsArrowTypeWithoutPreconditions {
      get {
        var t = this;
        while (true) {
          var udt = t.NormalizeExpandKeepConstraints() as UserDefinedType;
          if (udt == null) {
            return false;
          } else if (ArrowType.IsTotalArrowTypeName(udt.Name)) {
            return true;
          }
          var sst = udt.ResolvedClass as SubsetTypeDecl;
          if (sst != null) {
            t = sst.RhsWithArgument(udt.TypeArgs);  // continue the search up the chain of subset types
          } else {
            return false;
          }
        }
      }
    }
    public bool IsArrowType {
      get { return AsArrowType != null; }
    }
    public ArrowType AsArrowType {
      get {
        var t = NormalizeExpand();
        return t as ArrowType;
      }
    }

    public bool IsMapType {
      get {
        var t = NormalizeExpand() as MapType;
        return t != null && t.Finite;
      }
    }
    public bool IsIMapType {
      get {
        var t = NormalizeExpand() as MapType;
        return t != null && !t.Finite;
      }
    }
    public bool IsISetType {
      get {
        var t = NormalizeExpand() as SetType;
        return t != null && !t.Finite;
      }
    }
    public NewtypeDecl AsNewtype {
      get {
        var udt = NormalizeExpand() as UserDefinedType;
        return udt == null ? null : udt.ResolvedClass as NewtypeDecl;
      }
    }
    public TypeSynonymDecl AsTypeSynonym {
      get {
        var udt = this as UserDefinedType;  // note, it is important to use 'this' here, not 'this.NormalizeExpand()'
        if (udt == null) {
          return null;
        } else {
          return udt.ResolvedClass as TypeSynonymDecl;
        }
      }
    }
    public InternalTypeSynonymDecl AsInternalTypeSynonym {
      get {
        var udt = this as UserDefinedType;  // note, it is important to use 'this' here, not 'this.NormalizeExpand()'
        if (udt == null) {
          return null;
        } else {
          return udt.ResolvedClass as InternalTypeSynonymDecl;
        }
      }
    }
    public RedirectingTypeDecl AsRedirectingType {
      get {
        var udt = this as UserDefinedType;  // Note, it is important to use 'this' here, not 'this.NormalizeExpand()'.  This property getter is intended to be used during resolution, or with care thereafter.
        if (udt == null) {
          return null;
        } else {
          return (RedirectingTypeDecl)(udt.ResolvedClass as TypeSynonymDecl) ?? udt.ResolvedClass as NewtypeDecl;
        }
      }
    }
    public RevealableTypeDecl AsRevealableType {
      get {
        var udt = this as UserDefinedType;
        if (udt == null) {
          return null;
        } else {
          return (udt.ResolvedClass as RevealableTypeDecl);
        }
      }
    }
    public bool IsRevealableType {
      get { return AsRevealableType != null; }
    }
    public bool IsDatatype {
      get {
        return AsDatatype != null;
      }
    }
    public DatatypeDecl AsDatatype {
      get {
        var udt = NormalizeExpand() as UserDefinedType;
        if (udt == null) {
          return null;
        } else {
          return udt.ResolvedClass as DatatypeDecl;
        }
      }
    }
    public bool IsIndDatatype {
      get {
        return AsIndDatatype != null;
      }
    }
    public IndDatatypeDecl AsIndDatatype {
      get {
        var udt = NormalizeExpand() as UserDefinedType;
        if (udt == null) {
          return null;
        } else {
          return udt.ResolvedClass as IndDatatypeDecl;
        }
      }
    }
    public bool IsCoDatatype {
      get {
        return AsCoDatatype != null;
      }
    }
    public CoDatatypeDecl AsCoDatatype {
      get {
        var udt = NormalizeExpand() as UserDefinedType;
        if (udt == null) {
          return null;
        } else {
          return udt.ResolvedClass as CoDatatypeDecl;
        }
      }
    }
    public bool InvolvesCoDatatype {
      get {
        return IsCoDatatype;  // TODO: should really check structure of the type recursively
      }
    }
    public bool IsTypeParameter {
      get {
        return AsTypeParameter != null;
      }
    }
    public bool IsInternalTypeSynonym {
      get { return AsInternalTypeSynonym != null; }
    }
    public TypeParameter AsTypeParameter {
      get {
        var ct = NormalizeExpandKeepConstraints() as UserDefinedType;
        return ct?.ResolvedClass as TypeParameter;
      }
    }
    public bool IsOpaqueType {
      get { return AsOpaqueType != null; }
    }
    public OpaqueTypeDecl AsOpaqueType {
      get {
        var udt = this.Normalize() as UserDefinedType;  // note, it is important to use 'this.Normalize()' here, not 'this.NormalizeExpand()'
        return udt?.ResolvedClass as OpaqueTypeDecl;
      }
    }
    public virtual bool SupportsEquality {
      get {
        return true;
      }
    }
    public virtual bool MayInvolveReferences {
      get {
        return false;
      }
    }

    /// <summary>
    /// Returns true if it is known how to meaningfully compare the type's inhabitants.
    /// </summary>
    public bool IsOrdered {
      get {
        var ct = NormalizeExpand();
        return !ct.IsTypeParameter && !ct.IsOpaqueType && !ct.IsInternalTypeSynonym && !ct.IsCoDatatype && !ct.IsArrowType && !ct.IsIMapType && !ct.IsISetType;
      }
    }

    /// <summary>
    /// Returns "true" if:  Given a value of type "this", can we determine at run time if the
    /// value is a member of type "target"?
    /// </summary>
    public bool IsTestableToBe(Type target) {
      Contract.Requires(target != null);

      // First up, we know how to check for null, so let's expand "target" and "source"
      // past any type synonyms and also past any (built-in) non-null constraint.
      var source = this.NormalizeExpandKeepConstraints();
      if (source is UserDefinedType && ((UserDefinedType)source).ResolvedClass is NonNullTypeDecl) {
        source = source.NormalizeExpand(); // also lop off non-null constraint
      }
      target = target.NormalizeExpandKeepConstraints();
      if (target is UserDefinedType && ((UserDefinedType)target).ResolvedClass is NonNullTypeDecl) {
        target = target.NormalizeExpand(); // also lop off non-null constraint
      }

      if (source.IsSubtypeOf(target, false, true)) {
        // Every value of "source" (except possibly "null") is also a member of type "target",
        // so no run-time test is needed (except possibly a null check).
        return true;
#if SOON  // include in a coming PR that sorts this one in the compilers
      } else if (target is UserDefinedType udt && (udt.ResolvedClass is SubsetTypeDecl || udt.ResolvedClass is NewtypeDecl)) {
        // The type of the bound variable has a constraint. Such a constraint is a ghost expression, so it cannot
        // (in general) by checked at run time. (A possible enhancement here would be to look at the type constraint
        // to if it is compilable after all.)
        var constraints = target.GetTypeConstraints();
        return false;
#endif
      } else if (target.TypeArgs.Count == 0) {
        // No type parameters. So, we just need to check the run-time class/interface type.
        return true;
      } else {
        // We give up.
        return false;
      }
    }

    /// <summary>
    /// Returns "true" iff "sub" is a subtype of "super".
    /// Expects that neither "super" nor "sub" is an unresolved proxy.
    /// </summary>
    public static bool IsSupertype(Type super, Type sub) {
      Contract.Requires(super != null);
      Contract.Requires(sub != null);
      return sub.IsSubtypeOf(super, false, false);
    }

    /// <summary>
    /// Expects that "type" has already been normalized.
    /// </summary>
    public static List<TypeParameter.TPVariance> GetPolarities(Type type) {
      Contract.Requires(type != null);
      if (type is BasicType || type is ArtificialType) {
        // there are no type parameters
        return new List<TypeParameter.TPVariance>();
      } else if (type is MapType) {
        return new List<TypeParameter.TPVariance> { TypeParameter.TPVariance.Co, TypeParameter.TPVariance.Co };
      } else if (type is CollectionType) {
        return new List<TypeParameter.TPVariance> { TypeParameter.TPVariance.Co };
      } else {
        var udf = (UserDefinedType)type;
        if (udf.TypeArgs.Count == 0) {
          return new List<TypeParameter.TPVariance>();
        }
        // look up the declaration of the formal type parameters
        var cl = udf.ResolvedClass;
        return cl.TypeArgs.ConvertAll(tp => tp.Variance);
      }
    }

    public static bool FromSameHead_Subtype(Type t, Type u, BuiltIns builtIns, out Type a, out Type b) {
      Contract.Requires(t != null);
      Contract.Requires(u != null);
      Contract.Requires(builtIns != null);
      if (FromSameHead(t, u, out a, out b)) {
        return true;
      }
      t = t.NormalizeExpand();
      u = u.NormalizeExpand();
      if (t.IsRefType && u.IsRefType) {
        if (t.IsObjectQ) {
          a = b = t;
          return true;
        } else if (u.IsObjectQ) {
          a = b = u;
          return true;
        }
        var tt = ((UserDefinedType)t).ResolvedClass as ClassDecl;
        var uu = ((UserDefinedType)u).ResolvedClass as ClassDecl;
        if (uu.HeadDerivesFrom(tt)) {
          a = b = t;
          return true;
        } else if (tt.HeadDerivesFrom(uu)) {
          a = b = u;
          return true;
        }
      }
      return false;
    }

    public static bool FromSameHead(Type t, Type u, out Type a, out Type b) {
      a = t;
      b = u;
      var towerA = GetTowerOfSubsetTypes(a);
      var towerB = GetTowerOfSubsetTypes(b);
      for (var n = Math.Min(towerA.Count, towerB.Count); 0 <= --n;) {
        a = towerA[n];
        b = towerB[n];
        if (SameHead(a, b)) {
          return true;
        }
      }
      return false;
    }

    /// <summary>
    /// Returns true if t and u have the same head type.
    /// It is assumed that t and u have been normalized and expanded by the caller, according
    /// to its purposes.
    /// The value of "allowNonNull" matters only if both "t" and "u" denote reference types.
    /// If "t" is a non-null reference type "T" or a possibly-null type "T?"
    /// and "u" is a non-null reference type "U" or a possibly-null type "U?", then
    /// SameHead returns:
    ///            !allowNonNull     allowNonNull
    ///   T?  U?        true           true
    ///   T?  U         false          true
    ///   T   U?        false          false
    ///   T   U         true           true
    /// </summary>
    public static bool SameHead(Type t, Type u) {
      Contract.Requires(t != null);
      Contract.Requires(u != null);
      if (t is TypeProxy) {
        return t == u;
      } else if (t.TypeArgs.Count == 0) {
        return Equal_Improved(t, u);
      } else if (t is SetType) {
        return u is SetType && t.IsISetType == u.IsISetType;
      } else if (t is SeqType) {
        return u is SeqType;
      } else if (t is MultiSetType) {
        return u is MultiSetType;
      } else if (t is MapType) {
        return u is MapType && t.IsIMapType == u.IsIMapType;
      } else {
        var udtT = (UserDefinedType)t;
        var udtU = u as UserDefinedType;
        return udtU != null && udtT.ResolvedClass == udtU.ResolvedClass;
      }
    }

    /// <summary>
    /// Returns "true" iff the head symbols of "sub" can be a subtype of the head symbol of "super".
    /// Expects that neither "super" nor "sub" is an unresolved proxy type (but their type arguments are
    /// allowed to be, since this method does not inspect the type arguments).
    /// </summary>
    public static bool IsHeadSupertypeOf(Type super, Type sub) {
      Contract.Requires(super != null);
      Contract.Requires(sub != null);
      super = super.NormalizeExpandKeepConstraints();  // expand type synonyms
      var origSub = sub;
      sub = sub.NormalizeExpand();  // expand type synonyms AND constraints
      if (super is TypeProxy) {
        return super == sub;
      } else if (super is BoolType) {
        return sub is BoolType;
      } else if (super is CharType) {
        return sub is CharType;
      } else if (super is IntType) {
        return sub is IntType;
      } else if (super is RealType) {
        return sub is RealType;
      } else if (super is BitvectorType) {
        var bitvectorSuper = (BitvectorType)super;
        var bitvectorSub = sub as BitvectorType;
        return bitvectorSub != null && bitvectorSuper.Width == bitvectorSub.Width;
      } else if (super is IntVarietiesSupertype) {
        while (sub.AsNewtype != null) {
          sub = sub.AsNewtype.BaseType.NormalizeExpand();
        }
        return sub.IsIntegerType || sub is BitvectorType || sub is BigOrdinalType;
      } else if (super is RealVarietiesSupertype) {
        while (sub.AsNewtype != null) {
          sub = sub.AsNewtype.BaseType.NormalizeExpand();
        }
        return sub is RealType;
      } else if (super is BigOrdinalType) {
        return sub is BigOrdinalType;
      } else if (super is SetType) {
        return sub is SetType && (super.IsISetType || !sub.IsISetType);
      } else if (super is SeqType) {
        return sub is SeqType;
      } else if (super is MultiSetType) {
        return sub is MultiSetType;
      } else if (super is MapType) {
        return sub is MapType && (super.IsIMapType || !sub.IsIMapType);
      } else if (super is ArrowType) {
        var asuper = (ArrowType)super;
        var asub = sub as ArrowType;
        return asub != null && asuper.Arity == asub.Arity;
      } else if (super.IsObjectQ) {
        var clSub = sub as UserDefinedType;
        return sub.IsObjectQ || (clSub != null && clSub.ResolvedClass is ClassDecl);
      } else if (super is UserDefinedType) {
        var udtSuper = (UserDefinedType)super;
        Contract.Assert(udtSuper.ResolvedClass != null);
        if (udtSuper.ResolvedClass is TypeParameter) {
          return udtSuper.ResolvedClass == sub.AsTypeParameter;
        } else {
          sub = origSub;  // get back to the starting point
          while (true) {
            sub = sub.NormalizeExpandKeepConstraints();  // skip past proxies and type synonyms
            var udtSub = sub as UserDefinedType;
            if (udtSub == null) {
              return false;
            } else if (udtSuper.ResolvedClass == udtSub.ResolvedClass) {
              return true;
            } else if (udtSub.ResolvedClass is SubsetTypeDecl) {
              sub = ((SubsetTypeDecl)udtSub.ResolvedClass).RhsWithArgument(udtSub.TypeArgs);
              if (udtSub.ResolvedClass is NonNullTypeDecl && udtSuper.ResolvedClass is NonNullTypeDecl) {
                // move "super" up the base-type chain, as was done with "sub", because non-nullness is essentially a co-variant type constructor
                var possiblyNullSuper = ((SubsetTypeDecl)udtSuper.ResolvedClass).RhsWithArgument(udtSuper.TypeArgs);
                udtSuper = (UserDefinedType)possiblyNullSuper;  // applying .RhsWithArgument to a NonNullTypeDecl should always yield a UserDefinedType
                if (udtSuper.IsObjectQ) {
                  return true;
                }
              }
            } else if (udtSub.ResolvedClass is ClassDecl) {
              var cl = (ClassDecl)udtSub.ResolvedClass;
              return cl.HeadDerivesFrom(udtSuper.ResolvedClass);
            } else {
              return false;
            }
          }
        }
      } else {
        Contract.Assert(false);  // unexpected kind of type
        return true;  // to please the compiler
      }
    }

    /// <summary>
    /// Returns "true" iff "a" and "b" denote the same type, expanding type synonyms (but treating types with
    /// constraints as being separate types).
    /// Expects that neither "a" nor "b" is or contains an unresolved proxy type.
    /// </summary>
    public static bool Equal_Improved(Type a, Type b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      a = a.NormalizeExpandKeepConstraints();  // expand type synonyms
      b = b.NormalizeExpandKeepConstraints();  // expand type synonyms
      if (a is BoolType) {
        return b is BoolType;
      } else if (a is CharType) {
        return b is CharType;
      } else if (a is IntType) {
        return b is IntType;
      } else if (a is RealType) {
        return b is RealType;
      } else if (a is BitvectorType) {
        var bitvectorSuper = (BitvectorType)a;
        var bitvectorSub = b as BitvectorType;
        return bitvectorSub != null && bitvectorSuper.Width == bitvectorSub.Width;
      } else if (a is BigOrdinalType) {
        return b is BigOrdinalType;
      } else if (a is SetType) {
        return b is SetType && Equal_Improved(a.TypeArgs[0], b.TypeArgs[0]) && (a.IsISetType == b.IsISetType);
      } else if (a is SeqType) {
        return b is SeqType && Equal_Improved(a.TypeArgs[0], b.TypeArgs[0]);
      } else if (a is MultiSetType) {
        return b is MultiSetType && Equal_Improved(a.TypeArgs[0], b.TypeArgs[0]);
      } else if (a is MapType) {
        return b is MapType && Equal_Improved(a.TypeArgs[0], b.TypeArgs[0]) && Equal_Improved(a.TypeArgs[1], b.TypeArgs[1]) && (a.IsIMapType == b.IsIMapType);
      } else if (a is ArrowType) {
        var asuper = (ArrowType)a;
        var asub = b as ArrowType;
        return asub != null && asuper.Arity == asub.Arity;
      } else if (a is UserDefinedType) {
        var udtA = (UserDefinedType)a;
        Contract.Assert(udtA.ResolvedClass != null);
        if (udtA.ResolvedClass is TypeParameter) {
          Contract.Assert(udtA.TypeArgs.Count == 0);
          return udtA.ResolvedClass == b.AsTypeParameter;
        } else {
          var udtB = b as UserDefinedType;
          if (udtB == null) {
            return false;
          } else if (udtA.ResolvedClass != udtB.ResolvedClass) {
            return false;
          } else {
            Contract.Assert(udtA.TypeArgs.Count == udtB.TypeArgs.Count);
            for (int i = 0; i < udtA.TypeArgs.Count; i++) {
              if (!Equal_Improved(udtA.TypeArgs[i], udtB.TypeArgs[i])) {
                return false;
              }
            }
            return true;
          }
        }
      } else if (a is Resolver_IdentifierExpr.ResolverType_Module) {
        return b is Resolver_IdentifierExpr.ResolverType_Module;
      } else if (a is Resolver_IdentifierExpr.ResolverType_Type) {
        return b is Resolver_IdentifierExpr.ResolverType_Type;
      } else {
        // this is an unexpected type; however, it may be that we get here during the resolution of an erroneous
        // program, so we'll just return false
        return false;
      }
    }

    public static Type HeadWithProxyArgs(Type t) {
      Contract.Requires(t != null);
      Contract.Requires(!(t is TypeProxy));
      if (t.TypeArgs.Count == 0) {
        return t;
      } else if (t is SetType) {
        var s = (SetType)t;
        return new SetType(s.Finite, new InferredTypeProxy());
      } else if (t is MultiSetType) {
        return new MultiSetType(new InferredTypeProxy());
      } else if (t is SeqType) {
        return new SeqType(new InferredTypeProxy());
      } else if (t is MapType) {
        var s = (MapType)t;
        return new MapType(s.Finite, new InferredTypeProxy(), new InferredTypeProxy());
      } else if (t is ArrowType) {
        var s = (ArrowType)t;
        var args = s.TypeArgs.ConvertAll(_ => (Type)new InferredTypeProxy());
        return new ArrowType(s.tok, (ArrowTypeDecl)s.ResolvedClass, args);
      } else {
        var s = (UserDefinedType)t;
        var args = s.TypeArgs.ConvertAll(_ => (Type)new InferredTypeProxy());
        return new UserDefinedType(s.tok, s.Name, s.ResolvedClass, args);
      }
    }

    /// <summary>
    /// Returns a stack of base types leading to "type".  More precisely, of the tower returned,
    ///     tower[0] == type.NormalizeExpand()
    ///     tower.Last == type.NormalizeExpandKeepConstraints()
    /// In between, for consecutive indices i and i+1:
    ///     tower[i] is the base type (that is, .Rhs) of the subset type tower[i+1]
    /// The tower thus has the property that:
    ///     tower[0] is not a UserDefinedType with .ResolvedClass being a SubsetTypeDecl,
    ///     but all other tower[i] (for i > 0) are.
    /// </summary>
    public static List<Type> GetTowerOfSubsetTypes(Type type) {
      Contract.Requires(type != null);
      type = type.NormalizeExpandKeepConstraints();
      List<Type> tower;
      var udt = type as UserDefinedType;
      if (udt != null && udt.ResolvedClass is SubsetTypeDecl) {
        var sst = (SubsetTypeDecl)udt.ResolvedClass;
        var parent = sst.RhsWithArgument(udt.TypeArgs);
        tower = GetTowerOfSubsetTypes(parent);
      } else {
        tower = new List<Type>();
      }
      tower.Add(type);
      return tower;
    }

    /// <summary>
    /// For each i, computes some combination of a[i] and b[i], according to direction[i].
    /// For a negative direction (Contra), computes Join(a[i], b[i]), provided this join exists.
    /// For a zero direction (Inv), uses a[i], provided a[i] and b[i] are equal.
    /// For a positive direction (Co), computes Meet(a[i], b[i]), provided this meet exists.
    /// Returns null if any operation fails.
    /// </summary>
    public static List<Type> ComputeExtrema(List<TypeParameter.TPVariance> directions, List<Type> a, List<Type> b, BuiltIns builtIns) {
      Contract.Requires(directions != null);
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Requires(directions.Count == a.Count);
      Contract.Requires(directions.Count == b.Count);
      Contract.Requires(builtIns != null);
      var n = directions.Count;
      var r = new List<Type>(n);
      for (int i = 0; i < n; i++) {
        if (a[i].Normalize() is TypeProxy) {
          r.Add(b[i]);
        } else if (b[i].Normalize() is TypeProxy) {
          r.Add(a[i]);
        } else if (directions[i] == TypeParameter.TPVariance.Non) {
          if (a[i].Equals(b[i])) {
            r.Add(a[i]);
          } else {
            return null;
          }
        } else {
          var t = directions[i] == TypeParameter.TPVariance.Contra ? Join(a[i], b[i], builtIns) : Meet(a[i], b[i], builtIns);
          if (t == null) {
            return null;
          }
          r.Add(t);
        }
      }
      return r;
    }

    /// <summary>
    /// Does a best-effort to compute the join of "a" and "b", returning "null" if not successful.
    ///
    /// Since some type parameters may still be proxies, it could be that the returned type is not
    /// really a join, so the caller should set up additional constraints that the result is
    /// assignable to both a and b.
    /// </summary>
    public static Type Join(Type a, Type b, BuiltIns builtIns) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Requires(builtIns != null);
      var j = JoinX(a, b, builtIns);
      if (DafnyOptions.O.TypeInferenceDebug) {
        Console.WriteLine("DEBUG: Meet( {0}, {1} ) = {2}", a, b, j);
      }
      return j;
    }
    public static Type JoinX(Type a, Type b, BuiltIns builtIns) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Requires(builtIns != null);

      // As a special-case optimization, check for equality here, which will better preserve un-expanded type synonyms
      if (a.Equals(b, true)) {
        return a;
      }

      // Before we do anything else, make a note of whether or not both "a" and "b" are non-null types.
      var abNonNullTypes = a.IsNonNullRefType && b.IsNonNullRefType;

      var towerA = GetTowerOfSubsetTypes(a);
      var towerB = GetTowerOfSubsetTypes(b);
      for (var n = Math.Min(towerA.Count, towerB.Count); 1 <= --n; ) {
        a = towerA[n];
        b = towerB[n];
        var udtA = (UserDefinedType)a;
        var udtB = (UserDefinedType)b;
        if (udtA.ResolvedClass == udtB.ResolvedClass) {
          // We have two subset types with equal heads
          if (a.Equals(b)) {  // optimization for a special case, which applies for example when there are no arguments or when the types happen to be the same
            return a;
          }
          Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
          var directions = udtA.ResolvedClass.TypeArgs.ConvertAll(tp => TypeParameter.Negate(tp.Variance));
          var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
          if (typeArgs == null) {
            return null;
          }
          return new UserDefinedType(udtA.tok, udtA.Name, udtA.ResolvedClass, typeArgs);
        }
      }
      // We exhausted all possibilities of subset types being equal, so use the base-most types.
      a = towerA[0];
      b = towerB[0];

      if (a is IntVarietiesSupertype) {
        return b is IntVarietiesSupertype || b.IsNumericBased(NumericPersuasion.Int) || b.IsBigOrdinalType || b.IsBitVectorType ? b : null;
      } else if (b is IntVarietiesSupertype) {
        return a.IsNumericBased(NumericPersuasion.Int) || a.IsBigOrdinalType || a.IsBitVectorType ? a : null;
      } else if (a.IsBoolType || a.IsCharType || a.IsBitVectorType || a.IsBigOrdinalType || a.IsTypeParameter || a.IsInternalTypeSynonym || a is TypeProxy) {
        return a.Equals(b) ? a : null;
      } else if (a is RealVarietiesSupertype) {
        return b is RealVarietiesSupertype || b.IsNumericBased(NumericPersuasion.Real) ? b : null;
      } else if (b is RealVarietiesSupertype) {
        return a.IsNumericBased(NumericPersuasion.Real) ? a : null;
      } else if (a.IsNumericBased()) {
        // Note, for join, we choose not to step down to IntVarietiesSupertype or RealVarietiesSupertype
        return a.Equals(b) ? a : null;
      } else if (a.IsBitVectorType) {
        return a.Equals(b) ? a : null;
      } else if (a is SetType) {
        var aa = (SetType)a;
        var bb = b as SetType;
        if (bb == null || aa.Finite != bb.Finite) {
          return null;
        }
        // sets are co-variant in their argument type
        var typeArg = Join(a.TypeArgs[0], b.TypeArgs[0], builtIns);
        return typeArg == null ? null : new SetType(aa.Finite, typeArg);
      } else if (a is MultiSetType) {
        var aa = (MultiSetType)a;
        var bb = b as MultiSetType;
        if (bb == null) {
          return null;
        }
        // multisets are co-variant in their argument type
        var typeArg = Join(a.TypeArgs[0], b.TypeArgs[0], builtIns);
        return typeArg == null ? null : new MultiSetType(typeArg);
      } else if (a is SeqType) {
        var aa = (SeqType)a;
        var bb = b as SeqType;
        if (bb == null) {
          return null;
        }
        // sequences are co-variant in their argument type
        var typeArg = Join(a.TypeArgs[0], b.TypeArgs[0], builtIns);
        return typeArg == null ? null : new SeqType(typeArg);
      } else if (a is MapType) {
        var aa = (MapType)a;
        var bb = b as MapType;
        if (bb == null || aa.Finite != bb.Finite) {
          return null;
        }
        // maps are co-variant in both argument types
        var typeArgDomain = Join(a.TypeArgs[0], b.TypeArgs[0], builtIns);
        var typeArgRange = Join(a.TypeArgs[1], b.TypeArgs[1], builtIns);
        return typeArgDomain == null || typeArgRange == null ? null : new MapType(aa.Finite, typeArgDomain, typeArgRange);
      } else if (a.IsDatatype) {
        var aa = a.AsDatatype;
        if (aa != b.AsDatatype) {
          return null;
        }
        if (a.Equals(b)) {  // optimization for a special case, which applies for example when there are no arguments or when the types happen to be the same
          return a;
        }
        Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
        var directions = aa.TypeArgs.ConvertAll(tp => TypeParameter.Negate(tp.Variance));
        var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
        if (typeArgs == null) {
          return null;
        }
        var udt = (UserDefinedType)a;
        return new UserDefinedType(udt.tok, udt.Name, aa, typeArgs);
      } else if (a.AsArrowType != null) {
        var aa = a.AsArrowType;
        var bb = b.AsArrowType;
        if (bb == null || aa.Arity != bb.Arity) {
          return null;
        }
        int arity = aa.Arity;
        Contract.Assert(a.TypeArgs.Count == arity + 1);
        Contract.Assert(b.TypeArgs.Count == arity + 1);
        Contract.Assert(((ArrowType)a).ResolvedClass == ((ArrowType)b).ResolvedClass);
        var directions = new List<TypeParameter.TPVariance>();
        for (int i = 0; i < arity; i++) {
          directions.Add(TypeParameter.Negate(TypeParameter.TPVariance.Contra));  // arrow types are contra-variant in the argument types, so compute joins of these
        }
        directions.Add(TypeParameter.Negate(TypeParameter.TPVariance.Co));  // arrow types are co-variant in the result type, so compute the meet of these
        var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
        if (typeArgs == null) {
          return null;
        }
        var arr = (ArrowType)aa;
        return new ArrowType(arr.tok, (ArrowTypeDecl)arr.ResolvedClass, typeArgs);
      } else if (b.IsObjectQ) {
        var udtB = (UserDefinedType)b;
        return !a.IsRefType ? null : abNonNullTypes ? UserDefinedType.CreateNonNullType(udtB) : udtB;
      } else if (a.IsObjectQ) {
        var udtA = (UserDefinedType)a;
        return !b.IsRefType ? null : abNonNullTypes ? UserDefinedType.CreateNonNullType(udtA) : udtA;
      } else {
        // "a" is a class, trait, or opaque type
        var aa = ((UserDefinedType)a).ResolvedClass;
        Contract.Assert(aa != null);
        if (!(b is UserDefinedType)) {
          return null;
        }
        var bb = ((UserDefinedType)b).ResolvedClass;
        if (a.Equals(b)) {  // optimization for a special case, which applies for example when there are no arguments or when the types happen to be the same
          return a;
        } else if (aa == bb) {
          Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
          var directions = aa.TypeArgs.ConvertAll(tp => TypeParameter.Negate(tp.Variance));
          var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
          if (typeArgs == null) {
            return null;
          }
          var udt = (UserDefinedType)a;
          var xx = new UserDefinedType(udt.tok, udt.Name, aa, typeArgs);
          return abNonNullTypes ? UserDefinedType.CreateNonNullType(xx) : xx;
        } else if (aa is ClassDecl && bb is ClassDecl) {
          var A = (ClassDecl)aa;
          var B = (ClassDecl)bb;
          if (A.HeadDerivesFrom(B)) {
            var udtB = (UserDefinedType)b;
            return abNonNullTypes ? UserDefinedType.CreateNonNullType(udtB) : udtB;
          } else if (B.HeadDerivesFrom(A)) {
            var udtA = (UserDefinedType)a;
            return abNonNullTypes ? UserDefinedType.CreateNonNullType(udtA) : udtA;
          }
          // A and B are classes or traits. They always have object as a common supertype, but they may also both be extending some other
          // trait.  If such a trait is unique, pick it. (Unfortunately, this makes the join operation not associative.)
          var commonTraits = TopLevelDeclWithMembers.CommonTraits(A, B);
          if (commonTraits.Count == 1) {
            var typeMap = Resolver.TypeSubstitutionMap(A.TypeArgs, a.TypeArgs);
            var r = (UserDefinedType)Resolver.SubstType(commonTraits[0], typeMap);
            return abNonNullTypes ? UserDefinedType.CreateNonNullType(r) : r;
          } else {
            // the unfortunate part is when commonTraits.Count > 1 here :(
            return abNonNullTypes ? UserDefinedType.CreateNonNullType(builtIns.ObjectQ()) : builtIns.ObjectQ();
          }
        } else {
          return null;
        }
      }
    }

    /// <summary>
    /// Does a best-effort to compute the meet of "a" and "b", returning "null" if not successful.
    ///
    /// Since some type parameters may still be proxies, it could be that the returned type is not
    /// really a meet, so the caller should set up additional constraints that the result is
    /// assignable to both a and b.
    /// </summary>
    public static Type Meet(Type a, Type b, BuiltIns builtIns) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Requires(builtIns != null);
      a = a.NormalizeExpandKeepConstraints();
      b = b.NormalizeExpandKeepConstraints();

      var joinNeedsNonNullConstraint = false;
      Type j;
      if (a is UserDefinedType && ((UserDefinedType)a).ResolvedClass is NonNullTypeDecl) {
        joinNeedsNonNullConstraint = true;
        var nnt = (NonNullTypeDecl)((UserDefinedType)a).ResolvedClass;
        j = MeetX(nnt.RhsWithArgument(a.TypeArgs), b, builtIns);
      } else if (b is UserDefinedType && ((UserDefinedType)b).ResolvedClass is NonNullTypeDecl) {
        joinNeedsNonNullConstraint = true;
        var nnt = (NonNullTypeDecl)((UserDefinedType)b).ResolvedClass;
        j = MeetX(a, nnt.RhsWithArgument(b.TypeArgs), builtIns);
      } else {
        j = MeetX(a, b, builtIns);
      }
      if (j != null && joinNeedsNonNullConstraint && !j.IsNonNullRefType) {
        // try to make j into a non-null type; if that's not possible, then there is no meet
        var udt = j as UserDefinedType;
        if (udt != null && udt.ResolvedClass is ClassDecl) {
          // add the non-null constraint back in
          j = UserDefinedType.CreateNonNullType(udt);
        } else {
          // the original a and b have no meet
          j = null;
        }
      }
      if (DafnyOptions.O.TypeInferenceDebug) {
        Console.WriteLine("DEBUG: Meet( {0}, {1} ) = {2}", a, b, j);
      }
      return j;
    }
    public static Type MeetX(Type a, Type b, BuiltIns builtIns) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Requires(builtIns != null);

      var towerA = GetTowerOfSubsetTypes(a);
      var towerB = GetTowerOfSubsetTypes(b);
      if (towerB.Count < towerA.Count) {
      // make A be the shorter tower
        var tmp0 = a; a = b; b = tmp0;
        var tmp1 = towerA; towerA = towerB; towerB = tmp1;
      }
      var n = towerA.Count;
      Contract.Assert(1 <= n);  // guaranteed by GetTowerOfSubsetTypes
      if (towerA.Count < towerB.Count) {
        // B is strictly taller. The meet exists only if towerA[n-1] is a supertype of towerB[n-1], and
        // then the meet is "b".
        return Type.IsSupertype(towerA[n - 1], towerB[n - 1]) ? b : null;
      }
      Contract.Assert(towerA.Count == towerB.Count);
      a = towerA[n - 1];
      b = towerB[n - 1];
      if (2 <= n) {
        var udtA = (UserDefinedType)a;
        var udtB = (UserDefinedType)b;
        if (udtA.ResolvedClass == udtB.ResolvedClass) {
          // We have two subset types with equal heads
          if (a.Equals(b)) {  // optimization for a special case, which applies for example when there are no arguments or when the types happen to be the same
            return a;
          }
          Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
          var directions = udtA.ResolvedClass.TypeArgs.ConvertAll(tp => tp.Variance);
          var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
          if (typeArgs == null) {
            return null;
          }
          return new UserDefinedType(udtA.tok, udtA.Name, udtA.ResolvedClass, typeArgs);
        } else {
          // The two subset types do not have the same head, so there is no meet
          return null;
        }
      }
      Contract.Assert(towerA.Count == 1 && towerB.Count == 1);

      if (a is IntVarietiesSupertype) {
        return b is IntVarietiesSupertype || b.IsNumericBased(NumericPersuasion.Int) || b.IsBigOrdinalType || b.IsBitVectorType ? b : null;
      } else if (b is IntVarietiesSupertype) {
        return a.IsNumericBased(NumericPersuasion.Int) || a.IsBigOrdinalType || a.IsBitVectorType ? a : null;
      } else if (a.IsBoolType || a.IsCharType || a.IsBigOrdinalType || a.IsTypeParameter || a.IsInternalTypeSynonym || a is TypeProxy) {
        return a.Equals(b) ? a : null;
      } else if (a is RealVarietiesSupertype) {
        return b is RealVarietiesSupertype || b.IsNumericBased(NumericPersuasion.Real) ? b : null;
      } else if (b is RealVarietiesSupertype) {
        return a.IsNumericBased(NumericPersuasion.Real) ? a : null;
      } else if (a.IsNumericBased()) {
        return a.Equals(b) ? a : null;
      } else if (a.IsBitVectorType) {
        return a.Equals(b) ? a : null;
      } else if (a is SetType) {
        var aa = (SetType)a;
        var bb = b as SetType;
        if (bb == null || aa.Finite != bb.Finite) {
          return null;
        }
        // sets are co-variant in their argument type
        var typeArg = Meet(a.TypeArgs[0], b.TypeArgs[0], builtIns);
        return typeArg == null ? null : new SetType(aa.Finite, typeArg);
      } else if (a is MultiSetType) {
        var aa = (MultiSetType)a;
        var bb = b as MultiSetType;
        if (bb == null) {
          return null;
        }
        // multisets are co-variant in their argument type
        var typeArg = Meet(a.TypeArgs[0], b.TypeArgs[0], builtIns);
        return typeArg == null ? null : new MultiSetType(typeArg);
      } else if (a is SeqType) {
        var aa = (SeqType)a;
        var bb = b as SeqType;
        if (bb == null) {
          return null;
        }
        // sequences are co-variant in their argument type
        var typeArg = Meet(a.TypeArgs[0], b.TypeArgs[0], builtIns);
        return typeArg == null ? null : new SeqType(typeArg);
      } else if (a is MapType) {
        var aa = (MapType)a;
        var bb = b as MapType;
        if (bb == null || aa.Finite != bb.Finite) {
          return null;
        }
        // maps are co-variant in both argument types
        var typeArgDomain = Meet(a.TypeArgs[0], b.TypeArgs[0], builtIns);
        var typeArgRange = Meet(a.TypeArgs[1], b.TypeArgs[1], builtIns);
        return typeArgDomain == null || typeArgRange == null ? null : new MapType(aa.Finite, typeArgDomain, typeArgRange);
      } else if (a.IsDatatype) {
        var aa = a.AsDatatype;
        if (aa != b.AsDatatype) {
          return null;
        }
        if (a.Equals(b)) {  // optimization for a special case, which applies for example when there are no arguments or when the types happen to be the same
          return a;
        }
        Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
        var directions = aa.TypeArgs.ConvertAll(tp => tp.Variance);
        var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
        if (typeArgs == null) {
          return null;
        }
        var udt = (UserDefinedType)a;
        return new UserDefinedType(udt.tok, udt.Name, aa, typeArgs);
      } else if (a.AsArrowType != null) {
        var aa = a.AsArrowType;
        var bb = b.AsArrowType;
        if (bb == null || aa.Arity != bb.Arity) {
          return null;
        }
        int arity = aa.Arity;
        Contract.Assert(a.TypeArgs.Count == arity + 1);
        Contract.Assert(b.TypeArgs.Count == arity + 1);
        Contract.Assert(((ArrowType)a).ResolvedClass == ((ArrowType)b).ResolvedClass);
        var directions = new List<TypeParameter.TPVariance>();
        for (int i = 0; i < arity; i++) {
          directions.Add(TypeParameter.TPVariance.Contra);  // arrow types are contra-variant in the argument types, so compute joins of these
        }
        directions.Add(TypeParameter.TPVariance.Co);  // arrow types are co-variant in the result type, so compute the meet of these
        var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
        if (typeArgs == null) {
          return null;
        }
        var arr = (ArrowType)aa;
        return new ArrowType(arr.tok, (ArrowTypeDecl)arr.ResolvedClass, typeArgs);
      } else if (b.IsObjectQ) {
        return a.IsRefType ? a : null;
      } else if (a.IsObjectQ) {
        return b.IsRefType ? b : null;
      } else {
        // "a" is a class, trait, or opaque type
        var aa = ((UserDefinedType)a).ResolvedClass;
        Contract.Assert(aa != null);
        if (!(b is UserDefinedType)) {
          return null;
        }
        var bb = ((UserDefinedType)b).ResolvedClass;
        if (a.Equals(b)) {  // optimization for a special case, which applies for example when there are no arguments or when the types happen to be the same
          return a;
        } else if (aa == bb) {
          Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
          var directions = aa.TypeArgs.ConvertAll(tp => tp.Variance);
          var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
          if (typeArgs == null) {
            return null;
          }
          var udt = (UserDefinedType)a;
          return new UserDefinedType(udt.tok, udt.Name, aa, typeArgs);
        } else if (aa is ClassDecl && bb is ClassDecl) {
          if (a.IsSubtypeOf(b, false, false)) {
            return a;
          } else if (b.IsSubtypeOf(a, false, false)) {
            return b;
          } else {
            return null;
          }
        } else {
          return null;
        }
      }
    }

    public void ForeachTypeComponent(Action<Type> action) {
      action(this);
      TypeArgs.ForEach(x => x.ForeachTypeComponent(action));
    }

    public bool ContainsProxy(TypeProxy proxy) {
      Contract.Requires(proxy != null && proxy.T == null);
      if (this == proxy) {
        return true;
      } else {
        return TypeArgs.Exists(t => t.ContainsProxy(proxy));
      }
    }

    public virtual List<Type> ParentTypes() {
      return new List<Type>();
    }

    /// <summary>
    /// Return whether or not "this" is a subtype of "super".
    /// If "ignoreTypeArguments" is "true", then proceed as if the type arguments were equal.
    /// If "ignoreNullity" is "true", then the difference between a non-null reference type C
    /// and the corresponding nullable reference type C? is ignored.
    /// </summary>
    public virtual bool IsSubtypeOf(Type super, bool ignoreTypeArguments, bool ignoreNullity) {
      Contract.Requires(super != null);

      super = super.NormalizeExpandKeepConstraints();
      var sub = NormalizeExpandKeepConstraints();
      bool equivalentHeads = SameHead(sub, super);
      if (!equivalentHeads && ignoreNullity) {
        if (super is UserDefinedType a && sub is UserDefinedType b) {
          var clA = (a.ResolvedClass as NonNullTypeDecl)?.Class ?? a.ResolvedClass;
          var clB = (b.ResolvedClass as NonNullTypeDecl)?.Class ?? b.ResolvedClass;
          equivalentHeads = clA == clB;
        }
      }
      if (equivalentHeads) {
        return ignoreTypeArguments || CompatibleTypeArgs(super, sub);
      }

      return ParentTypes().Any(parentType => parentType.IsSubtypeOf(super, ignoreTypeArguments, ignoreNullity));
    }

    public static bool CompatibleTypeArgs(Type super, Type sub) {
      var polarities = GetPolarities(super);
      Contract.Assert(polarities.Count == super.TypeArgs.Count && polarities.Count == sub.TypeArgs.Count);
      var allGood = true;
      for (int i = 0; allGood && i < polarities.Count; i++) {
        switch (polarities[i]) {
          case TypeParameter.TPVariance.Co:
            allGood = IsSupertype(super.TypeArgs[i], sub.TypeArgs[i]);
            break;
          case TypeParameter.TPVariance.Contra:
            allGood = IsSupertype(sub.TypeArgs[i], super.TypeArgs[i]);
            break;
          case TypeParameter.TPVariance.Non:
          default:  // "default" shouldn't ever happen
            allGood = Equal_Improved(super.TypeArgs[i], sub.TypeArgs[i]);
            break;
        }
      }
      return allGood;
    }
  }

  /// <summary>
  /// An ArtificialType is only used during type checking. It should never be assigned as the type of any expression.
  /// </summary>
  public abstract class ArtificialType : Type
  {
  }
  /// <summary>
  /// The type "IntVarietiesSupertype" is used to denote a decimal-less number type, namely an int-based type
  /// or a bitvector type.
  /// </summary>
  public class IntVarietiesSupertype : ArtificialType
  {
    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      return "int";
    }
    public override bool Equals(Type that, bool keepConstraints = false) {
      return keepConstraints ? this.GetType() == that.GetType() : that is IntVarietiesSupertype;
    }
  }
  public class RealVarietiesSupertype : ArtificialType
  {
    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      return "real";
    }
    public override bool Equals(Type that, bool keepConstraints = false) {
      return keepConstraints ? this.GetType() == that.GetType() : that is RealVarietiesSupertype;
    }
  }

  /// <summary>
  /// A NonProxy type is a fully constrained type.  It may contain members.
  /// </summary>
  public abstract class NonProxyType : Type
  {
  }

  public abstract class BasicType : NonProxyType
  {
  }

  public class BoolType : BasicType {
    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      return "bool";
    }
    public override bool Equals(Type that, bool keepConstraints = false) {
      return that.IsBoolType;
    }
  }

  public class CharType : BasicType
  {
    public const char DefaultValue = 'D';
    public const string DefaultValueAsString = "'D'";
    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      return "char";
    }
    public override bool Equals(Type that, bool keepConstraints = false) {
      return that.IsCharType;
    }
  }

  public class IntType : BasicType
  {
    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      return "int";
    }
    public override bool Equals(Type that, bool keepConstraints = false) {
      return that.NormalizeExpand(keepConstraints) is IntType;
    }
    public override bool IsSubtypeOf(Type super, bool ignoreTypeArguments, bool ignoreNullity) {
      if (super is IntVarietiesSupertype) {
        return true;
      }
      return base.IsSubtypeOf(super, ignoreTypeArguments, ignoreNullity);
    }
  }

  public class RealType : BasicType {
    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      return "real";
    }
    public override bool Equals(Type that, bool keepConstraints = false) {
      return that.NormalizeExpand(keepConstraints) is RealType;
    }
    public override bool IsSubtypeOf(Type super, bool ignoreTypeArguments, bool ignoreNullity) {
      if (super is RealVarietiesSupertype) {
        return true;
      }
      return base.IsSubtypeOf(super, ignoreTypeArguments, ignoreNullity);
    }
  }

  public class BigOrdinalType : BasicType
  {
    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      return "ORDINAL";
    }
    public override bool Equals(Type that, bool keepConstraints = false) {
      return that.NormalizeExpand(keepConstraints) is BigOrdinalType;
    }
    public override bool IsSubtypeOf(Type super, bool ignoreTypeArguments, bool ignoreNullity) {
      if (super is IntVarietiesSupertype) {
        return true;
      }
      return base.IsSubtypeOf(super, ignoreTypeArguments, ignoreNullity);
    }
  }

  public class BitvectorType : BasicType
  {
    public readonly int Width;
    public readonly NativeType NativeType;
    public BitvectorType(int width)
      : base() {
      Contract.Requires(0 <= width);
      Width = width;
      foreach (var nativeType in Resolver.NativeTypes) {
        if ((nativeType.CompilationTargets & DafnyOptions.O.CompileTarget) != 0 && width <= nativeType.Bitwidth) {
          NativeType = nativeType;
          break;
        }
      }
    }

    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      return "bv" + Width;
    }
    public override bool Equals(Type that, bool keepConstraints = false) {
      var bv = that.NormalizeExpand(keepConstraints) as BitvectorType;
      return bv != null && bv.Width == Width;
    }
    public override bool IsSubtypeOf(Type super, bool ignoreTypeArguments, bool ignoreNullity) {
      if (super is IntVarietiesSupertype) {
        return true;
      }
      return base.IsSubtypeOf(super, ignoreTypeArguments, ignoreNullity);
    }
  }

  public class SelfType : NonProxyType
  {
    public TypeParameter TypeArg;
    public Type ResolvedType;
    public SelfType() : base() {
      TypeArg = new TypeParameter(Token.NoToken, "selfType", TypeParameter.TPVarianceSyntax.NonVariant_Strict);
    }

    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      return "selftype";
    }
    public override bool Equals(Type that, bool keepConstraints = false) {
      return that.NormalizeExpand(keepConstraints) is SelfType;
    }
  }

  public class ArrowType : UserDefinedType
  {
    public List<Type> Args {
      get { return TypeArgs.GetRange(0, Arity); }
    }

    public Type Result {
      get { return TypeArgs[Arity]; }
    }

    public int Arity {
      get { return TypeArgs.Count - 1; }
    }

    /// <summary>
    /// Constructs a(n unresolved) arrow type.
    /// </summary>
    public ArrowType(IToken tok, List<Type> args, Type result)
      :  base(tok, ArrowTypeName(args.Count), Util.Snoc(args, result)) {
      Contract.Requires(tok != null);
      Contract.Requires(args != null);
      Contract.Requires(result != null);
    }
    /// <summary>
    /// Constructs and returns a resolved arrow type.
    /// </summary>
    public ArrowType(IToken tok, ArrowTypeDecl atd, List<Type> typeArgsAndResult)
      : base(tok, ArrowTypeName(atd.Arity), atd, typeArgsAndResult) {
      Contract.Requires(tok != null);
      Contract.Requires(atd != null);
      Contract.Requires(typeArgsAndResult != null);
      Contract.Requires(typeArgsAndResult.Count == atd.Arity + 1);
    }
    /// <summary>
    /// Constructs and returns a resolved arrow type.
    /// </summary>
    public ArrowType(IToken tok, ArrowTypeDecl atd, List<Type> typeArgs, Type result)
      : this(tok, atd, Util.Snoc(typeArgs, result)) {
      Contract.Requires(tok != null);
      Contract.Requires(atd != null);
      Contract.Requires(typeArgs!= null);
      Contract.Requires(typeArgs.Count == atd.Arity);
      Contract.Requires(result != null);
    }

    public const string Arrow_FullCompileName = "Func";  // this is the same for all arities

    public static string ArrowTypeName(int arity) {
      return "_#Func" + arity;
    }

    [Pure]
    public static bool IsArrowTypeName(string s) {
      return s.StartsWith("_#Func");
    }

    public static string PartialArrowTypeName(int arity) {
      return "_#PartialFunc" + arity;
    }

    [Pure]
    public static bool IsPartialArrowTypeName(string s) {
      return s.StartsWith("_#PartialFunc");
    }

    public static string TotalArrowTypeName(int arity) {
      return "_#TotalFunc" + arity;
    }

    [Pure]
    public static bool IsTotalArrowTypeName(string s) {
      return s.StartsWith("_#TotalFunc");
    }

    public const string ANY_ARROW = "~>";
    public const string PARTIAL_ARROW = "-->";
    public const string TOTAL_ARROW = "->";

    public override string TypeName(ModuleDefinition context, bool parseAble) {
      return PrettyArrowTypeName(ANY_ARROW, Args, Result, context, parseAble);
    }

    /// <summary>
    /// Pretty prints an arrow type.  If "result" is null, then all arguments, including the result type are expected in "typeArgs".
    /// If "result" is non-null, then only the in-arguments are in "typeArgs".
    /// </summary>
    public static string PrettyArrowTypeName(string arrow, List<Type> typeArgs, Type result, ModuleDefinition context, bool parseAble) {
      Contract.Requires(arrow != null);
      Contract.Requires(typeArgs != null);
      Contract.Requires(result != null || 1 <= typeArgs.Count);

      int arity = result == null ? typeArgs.Count - 1 : typeArgs.Count;
      var domainNeedsParens = false;
      if (arity != 1) {
        // 0 or 2-or-more arguments:  need parentheses
        domainNeedsParens = true;
      } else if (typeArgs[0].IsBuiltinArrowType) {
        // arrows are right associative, so we need parentheses around the domain type
        domainNeedsParens = true;
      } else {
        // if the domain type consists of a single tuple type, then an extra set of parentheses is needed
        // Note, we do NOT call .AsDatatype or .AsIndDatatype here, because those calls will do a NormalizeExpand().  Instead, we do the check manually.
        var udt = typeArgs[0].Normalize() as UserDefinedType;  // note, we do Normalize(), not NormalizeExpand(), since the TypeName will use any synonym
        if (udt != null && udt.ResolvedClass is TupleTypeDecl) {
          domainNeedsParens = true;
        }
      }
      string s = "";
      if (domainNeedsParens) { s += "("; }
      s += Util.Comma(typeArgs.Take(arity), arg => arg.TypeName(context, parseAble));
      if (domainNeedsParens) { s += ")"; }
      s += " " + arrow + " ";
      s += (result ?? typeArgs.Last()).TypeName(context, parseAble);
      return s;
    }

    public override bool SupportsEquality {
      get {
        return false;
      }
    }
  }

  public abstract class CollectionType : NonProxyType
  {
    public abstract string CollectionTypeName { get; }
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      Contract.Ensures(Contract.Result<string>() != null);
      var targs = HasTypeArg() ? this.TypeArgsToString(context, parseAble) : "";
      return CollectionTypeName + targs;
    }
    public Type Arg {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);  // this is true only after "arg" has really been set (i.e., it follows from the precondition)
        Contract.Assume(arg != null);  // This is really a precondition.  Don't call Arg until "arg" has been set.
        return arg;
      }
    }  // denotes the Domain type for a Map
    private Type arg;
    // The following methods, HasTypeArg and SetTypeArg/SetTypeArgs, are to be called during resolution to make sure that "arg" becomes set.
    public bool HasTypeArg() {
      return arg != null;
    }
    public void SetTypeArg(Type arg) {
      Contract.Requires(arg != null);
      Contract.Requires(1 <= this.TypeArgs.Count);  // this is actually an invariant of all collection types
      Contract.Assume(this.arg == null);  // Can only set it once.  This is really a precondition.
      this.arg = arg;
      this.TypeArgs[0] = arg;
    }
    public virtual void SetTypeArgs(Type arg, Type other) {
      Contract.Requires(arg != null);
      Contract.Requires(other != null);
      Contract.Requires(this.TypeArgs.Count == 2);
      Contract.Assume(this.arg == null);  // Can only set it once.  This is really a precondition.
      this.arg = arg;
      this.TypeArgs[0] = arg;
      this.TypeArgs[1] = other;
    }
    [ContractInvariantMethod]
    void ObjectInvariant() {
      // Contract.Invariant(Contract.ForAll(TypeArgs, tp => tp != null));
      // After resolution, the following is invariant:  Contract.Invariant(Arg != null);
      // However, it may not be true until then.
    }
    /// <summary>
    /// This constructor is a collection types with 1 type argument
    /// </summary>
    protected CollectionType(Type arg) {
      this.arg = arg;
      this.TypeArgs = new List<Type> { arg };
    }
    /// <summary>
    /// This constructor is a collection types with 2 type arguments
    /// </summary>
    protected CollectionType(Type arg, Type other) {
      this.arg = arg;
      this.TypeArgs = new List<Type> { arg, other };
    }

    public override bool MayInvolveReferences {
      get {
        return Arg.MayInvolveReferences;
      }
    }
  }

  public class SetType : CollectionType {
    private bool finite;

    public bool Finite {
      get { return finite; }
      set { finite = value; }
    }

    public SetType(bool finite, Type arg) : base(arg) {
      this.finite = finite;
    }
    public override string CollectionTypeName { get { return finite ? "set" : "iset"; } }
    [Pure]
    public override bool Equals(Type that, bool keepConstraints = false) {
      var t = that.NormalizeExpand(keepConstraints) as SetType;
      return t != null && Finite == t.Finite && Arg.Equals(t.Arg, keepConstraints);
    }
    public override bool SupportsEquality {
      get {
        // Sets always support equality, because there is a check that the set element type always does.
        return true;
      }
    }
  }

  public class MultiSetType : CollectionType
  {
    public MultiSetType(Type arg) : base(arg) {
    }
    public override string CollectionTypeName { get { return "multiset"; } }
    public override bool Equals(Type that, bool keepConstraints = false) {
      var t = that.NormalizeExpand(keepConstraints) as MultiSetType;
      return t != null && Arg.Equals(t.Arg, keepConstraints);
    }
    public override bool SupportsEquality {
      get {
        // Multisets always support equality, because there is a check that the set element type always does.
        return true;
      }
    }
  }

  public class SeqType : CollectionType {
    public SeqType(Type arg) : base(arg) {
    }
    public override string CollectionTypeName { get { return "seq"; } }
    public override bool Equals(Type that, bool keepConstraints = false) {
      var t = that.NormalizeExpand(keepConstraints) as SeqType;
      return t != null && Arg.Equals(t.Arg, keepConstraints);
    }
    public override bool SupportsEquality {
      get {
        // The sequence type supports equality if its element type does
        return Arg.SupportsEquality;
      }
    }
  }
  public class MapType : CollectionType
  {
    public bool Finite {
      get { return finite; }
      set { finite = value; }
    }
    private bool finite;
    public Type Range {
      get { return range; }
    }
    private Type range;
    public override void SetTypeArgs(Type domain, Type range) {
      base.SetTypeArgs(domain, range);
      Contract.Assume(this.range == null);  // Can only set once.  This is really a precondition.
      this.range = range;
    }
    public MapType(bool finite, Type domain, Type range) : base(domain, range) {
      Contract.Requires((domain == null && range == null) || (domain != null && range != null));
      this.finite = finite;
      this.range = range;
    }
    public Type Domain {
      get { return Arg; }
    }
    public override string CollectionTypeName { get { return finite ? "map" : "imap"; } }
    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      Contract.Ensures(Contract.Result<string>() != null);
      var targs = HasTypeArg() ? this.TypeArgsToString(context, parseAble) : "";
      return CollectionTypeName + targs;
    }
    public override bool Equals(Type that, bool keepConstraints = false) {
      var t = that.NormalizeExpand(keepConstraints) as MapType;
      return t != null && Finite == t.Finite && Arg.Equals(t.Arg, keepConstraints) && Range.Equals(t.Range, keepConstraints);
    }
    public override bool SupportsEquality {
      get {
        // A map type supports equality if both its Keys type and Values type does.  It is checked
        // that the Keys type always supports equality, so we only need to check the Values type here.
        return range.SupportsEquality;
      }
    }
    public override bool MayInvolveReferences {
      get {
        return Domain.MayInvolveReferences || Range.MayInvolveReferences;
      }
    }
  }

  public class UserDefinedType : NonProxyType
  {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(tok != null);
      Contract.Invariant(Name != null);
      Contract.Invariant(cce.NonNullElements(TypeArgs));
      Contract.Invariant(NamePath is NameSegment || NamePath is ExprDotName);
      Contract.Invariant(!ArrowType.IsArrowTypeName(Name) || this is ArrowType);
    }

    public readonly Expression NamePath;  // either NameSegment or ExprDotName (with the inner expression satisfying this same constraint)
    public readonly IToken tok;  // token of the Name
    public readonly string Name;
    [Rep]

    public string FullName {
      get {
        if (ResolvedClass != null && !ResolvedClass.EnclosingModuleDefinition.IsDefaultModule) {
          return ResolvedClass.EnclosingModuleDefinition.Name + "." + Name;
        } else {
          return Name;
        }
      }
    }

    string compileName;
    public string CompileName {
      get {
        if (compileName == null) {
          compileName = ResolvedClass.CompileName;
        }
        return compileName;
      }
    }
    public string FullCompanionCompileName {
      get {
        Contract.Requires(ResolvedClass is TraitDecl || (ResolvedClass is NonNullTypeDecl nntd && nntd.Class is TraitDecl));
        var m = ResolvedClass.EnclosingModuleDefinition;
        var s = m.IsDefaultModule ? "" : m.CompileName + ".";
        return s + "_Companion_" + ResolvedClass.CompileName;
      }
    }

    public TopLevelDecl ResolvedClass;  // filled in by resolution, if Name denotes a class/datatype/iterator and TypeArgs match the type parameters of that class/datatype/iterator

    public UserDefinedType(IToken tok, string name, List<Type> optTypeArgs)
      : this(tok, new NameSegment(tok, name, optTypeArgs))
    {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(optTypeArgs == null || optTypeArgs.Count > 0);  // this is what it means to be syntactically optional
    }

    public UserDefinedType(IToken tok, Expression namePath) {
      Contract.Requires(tok != null);
      Contract.Requires(namePath is NameSegment || namePath is ExprDotName);
      this.tok = tok;
      if (namePath is NameSegment) {
        var n = (NameSegment)namePath;
        this.Name = n.Name;
        this.TypeArgs = n.OptTypeArguments;
      } else {
        var n = (ExprDotName)namePath;
        this.Name = n.SuffixName;
        this.TypeArgs = n.OptTypeArguments;
      }
      if (this.TypeArgs == null) {
        this.TypeArgs = new List<Type>();  // TODO: is this really the thing to do?
      }
      this.NamePath = namePath;
    }

    /// <summary>
    /// Constructs a Type (in particular, a UserDefinedType) from a TopLevelDecl denoting a type declaration.  If
    /// the given declaration takes type parameters, these are filled as references to the formal type parameters
    /// themselves.  (Usually, this method is called when the type parameters in the result don't matter, other
    /// than that they need to be filled in, so as to make a properly resolved UserDefinedType.)
    /// If "typeArgs" is non-null, then its type parameters are used in constructing the returned type.
    /// If "typeArgs" is null, then the formal type parameters of "cd" are used.
    /// </summary>
    public static UserDefinedType FromTopLevelDecl(IToken tok, TopLevelDecl cd, List<TypeParameter> typeArgs = null) {
      Contract.Requires(tok != null);
      Contract.Requires(cd != null);
      Contract.Assert((cd is ArrowTypeDecl) == ArrowType.IsArrowTypeName(cd.Name));
      var args = (typeArgs ?? cd.TypeArgs).ConvertAll(tp => (Type)new UserDefinedType(tp));
      if (cd is ArrowTypeDecl) {
        return new ArrowType(tok, (ArrowTypeDecl)cd, args);
      } else if (cd is ClassDecl && !(cd is DefaultClassDecl)) {
        return new UserDefinedType(tok, cd.Name + "?", cd, args);
      } else {
        return new UserDefinedType(tok, cd.Name, cd, args);
      }
    }

    public static UserDefinedType FromTopLevelDeclWithAllBooleanTypeParameters(TopLevelDecl cd) {
      Contract.Requires(cd != null);
      Contract.Requires(!(cd is ArrowTypeDecl));

      var typeArgs = cd.TypeArgs.ConvertAll(tp => (Type)Type.Bool);
      return new UserDefinedType(cd.tok, cd.Name, cd, typeArgs);
    }

    /// <summary>
    /// If "member" is non-null, then:
    ///   Return the upcast of "receiverType" that has base type "member.EnclosingClass".
    ///   Assumes that "receiverType" normalizes to a UserDefinedFunction with a .ResolveClass that is a subtype
    ///   of "member.EnclosingClass".
    /// Otherwise:
    ///   Return "receiverType" (expanded).
    /// </summary>
    public static Type UpcastToMemberEnclosingType(Type receiverType, MemberDecl/*?*/ member) {
      Contract.Requires(receiverType != null);
      if (member != null && member.EnclosingClass != null && !(member.EnclosingClass is ValuetypeDecl)) {
        return receiverType.AsParentType(member.EnclosingClass);
      }
      return receiverType.NormalizeExpandKeepConstraints();
    }

    /// <summary>
    /// This constructor constructs a resolved class/datatype/iterator/subset-type/newtype type
    /// </summary>
    public UserDefinedType(IToken tok, string name, TopLevelDecl cd, [Captured] List<Type> typeArgs, Expression/*?*/ namePath = null) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cd != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cd.TypeArgs.Count == typeArgs.Count);
      Contract.Requires(namePath == null || namePath is NameSegment || namePath is ExprDotName);
      // The following is almost a precondition. In a few places, the source program names a class, not a type,
      // and in then name==cd.Name for a ClassDecl.
      //Contract.Requires(!(cd is ClassDecl) || cd is DefaultClassDecl || cd is ArrowTypeDecl || name == cd.Name + "?");
      Contract.Requires(!(cd is ArrowTypeDecl) || name == cd.Name);
      Contract.Requires(!(cd is DefaultClassDecl) || name == cd.Name);
      this.tok = tok;
      this.Name = name;
      this.ResolvedClass = cd;
      this.TypeArgs = typeArgs;
      if (namePath == null) {
        var ns = new NameSegment(tok, name, typeArgs.Count == 0 ? null : typeArgs);
        var r = new Resolver_IdentifierExpr(tok, cd, typeArgs);
        ns.ResolvedExpression = r;
        ns.Type = r.Type;
        this.NamePath = ns;
      } else {
        this.NamePath = namePath;
      }
    }

    public static UserDefinedType CreateNonNullType(UserDefinedType udtNullableType) {
      Contract.Requires(udtNullableType != null);
      Contract.Requires(udtNullableType.ResolvedClass is ClassDecl);
      var cl = (ClassDecl)udtNullableType.ResolvedClass;
      return new UserDefinedType(udtNullableType.tok, cl.NonNullTypeDecl.Name, cl.NonNullTypeDecl, udtNullableType.TypeArgs);
    }

    public static UserDefinedType CreateNullableType(UserDefinedType udtNonNullType) {
      Contract.Requires(udtNonNullType != null);
      Contract.Requires(udtNonNullType.ResolvedClass is NonNullTypeDecl);
      var nntd = (NonNullTypeDecl)udtNonNullType.ResolvedClass;
      return new UserDefinedType(udtNonNullType.tok, nntd.Class.Name + "?", nntd.Class, udtNonNullType.TypeArgs);
    }

    /// <summary>
    /// This constructor constructs a resolved type parameter
    /// </summary>
    public UserDefinedType(TypeParameter tp)
      : this(tp.tok, tp) {
      Contract.Requires(tp != null);
    }

    /// <summary>
    /// This constructor constructs a resolved type parameter (but shouldn't be called if "tp" denotes
    /// the .TheType of an opaque type -- use the (OpaqueType_AsParameter, OpaqueTypeDecl, List(Type))
    /// constructor for that).
    /// </summary>
    public UserDefinedType(IToken tok, TypeParameter tp) {
      Contract.Requires(tok != null);
      Contract.Requires(tp != null);
      this.tok = tok;
      this.Name = tp.Name;
      this.TypeArgs = new List<Type>();
      this.ResolvedClass = tp;
      var ns = new NameSegment(tok, tp.Name, null);
      var r = new Resolver_IdentifierExpr(tok, tp);
      ns.ResolvedExpression = r;
      ns.Type = r.Type;
      this.NamePath = ns;
    }

    public override bool Equals(Type that, bool keepConstraints = false) {
      var i = NormalizeExpand(keepConstraints);
      if (i is UserDefinedType) {
        var ii = (UserDefinedType)i;
        var t = that.NormalizeExpand(keepConstraints) as UserDefinedType;
        if (t == null || ii.ResolvedClass != t.ResolvedClass || ii.TypeArgs.Count != t.TypeArgs.Count) {
          return false;
        } else {
          for (int j = 0; j < ii.TypeArgs.Count; j++) {
            if (!ii.TypeArgs[j].Equals(t.TypeArgs[j], keepConstraints)) {
              return false;
            }
          }
          return true;
        }
      } else {
        // TODO?: return i.Equals(that.NormalizeExpand());
        return i.Equals(that, keepConstraints);
      }
    }

    /// <summary>
    /// If type denotes a resolved class type, then return that class type.
    /// Otherwise, return null.
    /// </summary>
    public static UserDefinedType DenotesClass(Type type) {
      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<UserDefinedType>() == null || Contract.Result<UserDefinedType>().ResolvedClass is ClassDecl);
      type = type.NormalizeExpand();
      UserDefinedType ct = type as UserDefinedType;
      if (ct != null && ct.ResolvedClass is ClassDecl) {
        return ct;
      } else {
        return null;
      }
    }

    public static Type ArrayElementType(Type type) {
      Contract.Requires(type != null);
      Contract.Requires(type.IsArrayType);
      Contract.Ensures(Contract.Result<Type>() != null);

      UserDefinedType udt = DenotesClass(type);
      Contract.Assert(udt != null);
      Contract.Assert(udt.TypeArgs.Count == 1);  // holds true of all array types
      return udt.TypeArgs[0];
    }

    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      Contract.Ensures(Contract.Result<string>() != null);
      if (BuiltIns.IsTupleTypeName(Name)) {
        // Unfortunately, ResolveClass may be null, so Name is all we have.  Reverse-engineer the string name.
        IEnumerable<bool> argumentGhostness = BuiltIns.ArgumentGhostnessFromString(Name, TypeArgs.Count);
        return "(" + Util.Comma(System.Linq.Enumerable.Zip(TypeArgs, argumentGhostness),
          (ty_u) => Resolver.IsGhostPrefix(ty_u.Item2) + ty_u.Item1.TypeName(context, parseAble)) + ")";
      } else if (ArrowType.IsPartialArrowTypeName(Name)) {
        return ArrowType.PrettyArrowTypeName(ArrowType.PARTIAL_ARROW, TypeArgs, null, context, parseAble);
      } else if (ArrowType.IsTotalArrowTypeName(Name)) {
        return ArrowType.PrettyArrowTypeName(ArrowType.TOTAL_ARROW, TypeArgs, null, context, parseAble);
      } else {
#if TEST_TYPE_SYNONYM_TRANSPARENCY
        if (Name == "type#synonym#transparency#test" && ResolvedClass is TypeSynonymDecl) {
          return ((TypeSynonymDecl)ResolvedClass).Rhs.TypeName(context);
        }
#endif
        var s = Printer.ExprToString(NamePath);
        if (ResolvedClass != null) {
          var optionalTypeArgs = NamePath is NameSegment ? ((NameSegment)NamePath).OptTypeArguments : ((ExprDotName)NamePath).OptTypeArguments;
          if (optionalTypeArgs == null && TypeArgs != null && TypeArgs.Count != 0) {
            s += this.TypeArgsToString(context, parseAble);
          }
        }
        return s;
      }
    }

    public override bool SupportsEquality {
      get {
        if (ResolvedClass is ClassDecl || ResolvedClass is NewtypeDecl) {
          return ResolvedClass.IsRevealedInScope(Type.GetScope());
        } else if (ResolvedClass is CoDatatypeDecl) {
          return false;
        } else if (ResolvedClass is IndDatatypeDecl) {
          var dt = (IndDatatypeDecl)ResolvedClass;
          Contract.Assume(dt.EqualitySupport != IndDatatypeDecl.ES.NotYetComputed);
          if (!dt.IsRevealedInScope(Type.GetScope())) {
            return false;
          }
          if (dt.EqualitySupport == IndDatatypeDecl.ES.Never) {
            return false;
          }
          Contract.Assert(dt.TypeArgs.Count == TypeArgs.Count);
          var i = 0;
          foreach (var tp in dt.TypeArgs) {
            if (tp.NecessaryForEqualitySupportOfSurroundingInductiveDatatype && !TypeArgs[i].SupportsEquality) {
              return false;
            }
            i++;
          }
          return true;
        } else if (ResolvedClass is TypeSynonymDeclBase) {
          var t = (TypeSynonymDeclBase)ResolvedClass;
          if (t.SupportsEquality) {
            return true;
          } else if (t.IsRevealedInScope(Type.GetScope())) {
            return t.RhsWithArgument(TypeArgs).SupportsEquality;
          } else {
            return false;
          }
        } else if (ResolvedClass is TypeParameter) {
          return ((TypeParameter)ResolvedClass).SupportsEquality;
        } else if (ResolvedClass is OpaqueTypeDecl) {
          return ((OpaqueTypeDecl)ResolvedClass).SupportsEquality;
        }
        Contract.Assume(false);  // the SupportsEquality getter requires the Type to have been successfully resolved
        return true;
      }
    }

    public override bool MayInvolveReferences {
      get {
        if (ResolvedClass is ClassDecl) {
          return true;
        } else if (ResolvedClass is NewtypeDecl) {
          return false;
        } else if (ResolvedClass is DatatypeDecl) {
          var dt = (DatatypeDecl)ResolvedClass;
          if (!dt.IsRevealedInScope(Type.GetScope())) {
            return true;
          }
          Contract.Assert(dt.TypeArgs.Count == TypeArgs.Count);
          return TypeArgs.TrueForAll(ta => ta.MayInvolveReferences);
        } else if (ResolvedClass is TypeSynonymDeclBase) {
          var t = (TypeSynonymDeclBase)ResolvedClass;
          // (Note, if type parameters/opaque types could have a may-involve-references characteristic, then it would be consulted here)
          if (t.IsRevealedInScope(Type.GetScope())) {
            return t.RhsWithArgument(TypeArgs).MayInvolveReferences;
          } else {
            return true;
          }
        } else if (ResolvedClass is TypeParameter || ResolvedClass is OpaqueTypeDecl) {
          // (Note, if type parameters/opaque types could have a may-involve-references characteristic, then it would be consulted here)
          return true;
        }
        Contract.Assume(false);  // the MayInvolveReferences getter requires the Type to have been successfully resolved
        return true;
      }
    }

    public override List<Type> ParentTypes() {
      return ResolvedClass != null ? ResolvedClass.ParentTypes(TypeArgs) : base.ParentTypes();
    }

    public override bool IsSubtypeOf(Type super, bool ignoreTypeArguments, bool ignoreNullity) {
      super = super.NormalizeExpandKeepConstraints();

      // Specifically handle object as the implicit supertype of classes and traits.
      // "object?" is handled by Builtins rather than the Type hierarchy, so unfortunately
      // it can't be returned in ParentTypes().
      if (super.IsObjectQ) {
        return IsRefType;
      } else if (super.IsObject) {
        return ignoreNullity ? IsRefType : IsNonNullRefType;
      }

      return base.IsSubtypeOf(super, ignoreTypeArguments, ignoreNullity);
    }
  }

  public abstract class TypeProxy : Type {
    public Type T;  // filled in during resolution
    public readonly List<Resolver.TypeConstraint> SupertypeConstraints = new List<Resolver.TypeConstraint>();
    public readonly List<Resolver.TypeConstraint> SubtypeConstraints = new List<Resolver.TypeConstraint>();
    public IEnumerable<Type> Supertypes {
      get {
        foreach (var c in SupertypeConstraints) {
          if (c.KeepConstraints) {
            yield return c.Super.NormalizeExpandKeepConstraints();
          } else {
            yield return c.Super.NormalizeExpand();
          }
        }
      }
    }
    public IEnumerable<Type> SupertypesKeepConstraints {
      get {
        foreach (var c in SupertypeConstraints) {
          yield return c.Super.NormalizeExpandKeepConstraints();
        }
      }
    }
    public void AddSupertype(Resolver.TypeConstraint c) {
      Contract.Requires(c != null);
      Contract.Requires(c.Sub == this);
      SupertypeConstraints.Add(c);
    }
    public IEnumerable<Type> Subtypes {
      get {
        foreach (var c in SubtypeConstraints) {
          if (c.KeepConstraints) {
            yield return c.Sub.NormalizeExpandKeepConstraints();
          } else {
            yield return c.Sub.NormalizeExpand();
          }
        }
      }
    }

    public IEnumerable<Type> SubtypesKeepConstraints {
      get {
        foreach (var c in SubtypeConstraints) {
          yield return c.Sub.NormalizeExpandKeepConstraints();
        }
      }
    }

    public IEnumerable<Type> SubtypesKeepConstraints_WithAssignable(List<Resolver.XConstraint> allXConstraints) {
      Contract.Requires(allXConstraints != null);
      foreach (var c in SubtypeConstraints) {
        yield return c.Sub.NormalizeExpandKeepConstraints();
      }
      foreach (var xc in allXConstraints) {
        if (xc.ConstraintName == "Assignable") {
          if (xc.Types[0].Normalize() == this) {
            yield return xc.Types[1].NormalizeExpandKeepConstraints();
          }
        }
      }
    }

    public void AddSubtype(Resolver.TypeConstraint c) {
      Contract.Requires(c != null);
      Contract.Requires(c.Super == this);
      SubtypeConstraints.Add(c);
    }

    public enum Family { Unknown, Bool, Char, IntLike, RealLike, Ordinal, BitVector, ValueType, Ref, Opaque }
    public Family family = Family.Unknown;
    public static Family GetFamily(Type t) {
      Contract.Ensures(Contract.Result<Family>() != Family.Unknown || t is TypeProxy || t is Resolver_IdentifierExpr.ResolverType);  // return Unknown ==> t is TypeProxy || t is ResolverType
      if (t.IsBoolType) {
        return Family.Bool;
      } else if (t.IsCharType) {
        return Family.Char;
      } else if (t.IsNumericBased(NumericPersuasion.Int) || t is IntVarietiesSupertype) {
        return Family.IntLike;
      } else if (t.IsNumericBased(NumericPersuasion.Real) || t is RealVarietiesSupertype) {
        return Family.RealLike;
      } else if (t.IsBigOrdinalType) {
        return Family.Ordinal;
      } else if (t.IsBitVectorType) {
        return Family.BitVector;
      } else if (t.AsCollectionType != null || t.AsArrowType != null || t.IsDatatype) {
        return Family.ValueType;
      } else if (t.IsRefType) {
        return Family.Ref;
      } else if (t.IsTypeParameter || t.IsOpaqueType || t.IsInternalTypeSynonym) {
        return Family.Opaque;
      } else if (t is TypeProxy) {
        return ((TypeProxy)t).family;
      } else {
        return Family.Unknown;
      }
    }

    internal TypeProxy() {
    }

#if TI_DEBUG_PRINT
    static int _id = 0;
    int id = _id++;
#endif
    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      Contract.Ensures(Contract.Result<string>() != null);
#if TI_DEBUG_PRINT
      if (DafnyOptions.O.TypeInferenceDebug) {
        return T == null ? "?" + id : T.TypeName(context);
      }
#endif
      return T == null ? "?" : T.TypeName(context, parseAble);
    }
    public override bool SupportsEquality {
      get {
        if (T != null) {
          return T.SupportsEquality;
        } else {
          return base.SupportsEquality;
        }
      }
    }
    public override bool MayInvolveReferences {
      get {
        if (T != null) {
          return T.MayInvolveReferences;
        } else {
          return true;
        }
      }
    }
    public override bool Equals(Type that, bool keepConstraints = false) {
      var i = NormalizeExpand(keepConstraints);
      if (i is TypeProxy) {
        var u = that.NormalizeExpand(keepConstraints) as TypeProxy;
        return u != null && object.ReferenceEquals(i, u);
      } else {
        return i.Equals(that,keepConstraints);
      }
    }

    [Pure]
    internal static bool IsSupertypeOfLiteral(Type t) {
      Contract.Requires(t != null);
      return t is ArtificialType;
    }
    internal Type InClusterOfArtificial(List<Resolver.XConstraint> allXConstraints) {
      Contract.Requires(allXConstraints != null);
      return InClusterOfArtificial_aux(new HashSet<TypeProxy>(), allXConstraints);
    }
    private Type InClusterOfArtificial_aux(ISet<TypeProxy> visitedProxies, List<Resolver.XConstraint> allXConstraints) {
      Contract.Requires(visitedProxies != null);
      Contract.Requires(allXConstraints != null);
      if (visitedProxies.Contains(this)) {
        return null;
      }
      visitedProxies.Add(this);
      foreach (var c in SupertypeConstraints) {
        var sup = c.Super.Normalize();
        if (sup is IntVarietiesSupertype) {
          return Type.Int;
        } else if (sup is RealVarietiesSupertype) {
          return Type.Real;
        } else if (sup is TypeProxy) {
          var a = ((TypeProxy)sup).InClusterOfArtificial_aux(visitedProxies, allXConstraints);
          if (a != null) {
            return a;
          }
        }
      }
      foreach (var su in SubtypesKeepConstraints_WithAssignable(allXConstraints)) {
        var pr = su as TypeProxy;
        if (pr != null) {
          var a = pr.InClusterOfArtificial_aux(visitedProxies, allXConstraints);
          if (a != null) {
            return a;
          }
        }
      }
      return null;
    }
  }

  /// <summary>
  /// This proxy stands for any type.
  /// </summary>
  public class InferredTypeProxy : TypeProxy {
    public bool KeepConstraints;
    public InferredTypeProxy() : base() {
      KeepConstraints = false; // whether the typeProxy should be inferred to base type or as subset type
    }
  }

  /// <summary>
  /// This proxy stands for any type, but it originates from an instantiated type parameter.
  /// </summary>
  public class ParamTypeProxy : TypeProxy {
    public TypeParameter orig;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(orig != null);
    }

    public ParamTypeProxy(TypeParameter orig) {
      Contract.Requires(orig != null);
      this.orig = orig;
    }
  }

  // ------------------------------------------------------------------------------------------------------

  /// <summary>
  /// This interface is used by the Dafny IDE.
  /// </summary>
  public interface INamedRegion
  {
    IToken BodyStartTok { get; }
    IToken BodyEndTok { get; }
    string Name { get; }
  }

  public abstract class Declaration : INamedRegion, IAttributeBearingDeclaration
  {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(tok != null);
      Contract.Invariant(Name != null);
    }

    public static string IdProtect(string name) {
      switch (DafnyOptions.O.CompileTarget) {
        case DafnyOptions.CompilationTarget.Csharp:
          return CsharpCompiler.PublicIdProtect(name);
        case DafnyOptions.CompilationTarget.JavaScript:
          return JavaScriptCompiler.PublicIdProtect(name);
        case DafnyOptions.CompilationTarget.Go:
          return GoCompiler.PublicIdProtect(name);
        case DafnyOptions.CompilationTarget.Java:
          return JavaCompiler.PublicIdProtect(name);
        case DafnyOptions.CompilationTarget.Cpp:
          return CppCompiler.PublicIdProtect(name);
        default:
          Contract.Assert(false);  // unexpected compile target
          return name;
      }
    }

    public IToken tok;
    public IToken BodyStartTok = Token.NoToken;
    public IToken BodyEndTok = Token.NoToken;
    public readonly string Name;
    public bool IsRefining;
    IToken INamedRegion.BodyStartTok { get { return BodyStartTok; } }
    IToken INamedRegion.BodyEndTok { get { return BodyEndTok; } }
    string INamedRegion.Name { get { return Name; } }
    protected string compileName;

    private VisibilityScope opaqueScope = new VisibilityScope();
    private VisibilityScope revealScope = new VisibilityScope();

    private bool scopeIsInherited = false;

    public virtual bool CanBeExported() {
      return true;
    }

    public virtual bool CanBeRevealed() {
      return false;
    }

    public bool ScopeIsInherited { get { return scopeIsInherited; } }

    public void AddVisibilityScope(VisibilityScope scope, bool IsOpaque) {
      if (IsOpaque) {
        opaqueScope.Augment(scope);
      } else {
        revealScope.Augment(scope);
      }
    }

    public void InheritVisibility(Declaration d, bool onlyRevealed = true) {
      Contract.Assert(opaqueScope.IsEmpty());
      Contract.Assert(revealScope.IsEmpty());
      scopeIsInherited = false;

      revealScope = d.revealScope;

      if (!onlyRevealed) {
        opaqueScope = d.opaqueScope;
      }
      scopeIsInherited = true;

    }

    public bool IsRevealedInScope(VisibilityScope scope) {
      return revealScope.VisibleInScope(scope);
    }

    public bool IsVisibleInScope(VisibilityScope scope) {
      return IsRevealedInScope(scope) || opaqueScope.VisibleInScope(scope);
    }

    public virtual string CompileName {
      get {
        if (compileName == null) {
          string qual;
          IsExtern(out qual, out compileName);
          if (compileName == null) {
            // this is the usual name
            compileName = NonglobalVariable.CompilerizeName(Name);
          }
        }
        return compileName;
      }
    }
    public bool IsExtern(out string/*?*/ qualification, out string/*?*/ name) {
      // ensures result==false ==> qualification == null && name == null
      Contract.Ensures(Contract.Result<bool>() || (Contract.ValueAtReturn(out qualification) == null && Contract.ValueAtReturn(out name) == null));
      // ensures result==true ==> qualification != null ==> name != null
      Contract.Ensures(!Contract.Result<bool>() || Contract.ValueAtReturn(out qualification) == null || Contract.ValueAtReturn(out name) != null);

      qualification = null;
      name = null;
      if (!DafnyOptions.O.DisallowExterns) {
        var externArgs = Attributes.FindExpressions(this.Attributes, "extern");
        if (externArgs != null) {
          if (externArgs.Count == 0) {
            return true;
          } else if (externArgs.Count == 1 && externArgs[0] is StringLiteralExpr) {
            name = externArgs[0].AsStringLiteral();
            return true;
          } else if (externArgs.Count == 2 && externArgs[0] is StringLiteralExpr && externArgs[1] is StringLiteralExpr) {
            qualification = externArgs[0].AsStringLiteral();
            name = externArgs[1].AsStringLiteral();
            return true;
          }
        }
      }
      return false;
    }
    public Attributes Attributes;  // readonly, except during class merging in the refinement transformations and when changed by Compiler.MarkCapitalizationConflict

    public Declaration(IToken tok, string name, Attributes attributes, bool isRefining) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      this.tok = tok;
      this.Name = name;
      this.Attributes = attributes;
      this.IsRefining = isRefining;
    }

    [Pure]
    public override string ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      return Name;
    }

    internal FreshIdGenerator IdGenerator = new FreshIdGenerator();
  }

  public class TypeParameter : TopLevelDecl {
    public interface ParentType {
      string FullName { get; }
    }

    public override string WhatKind => "type parameter";

    ParentType parent;
    public ParentType Parent {
      get {
        return parent;
      }
      set {
        Contract.Requires(Parent == null);  // set it only once
        Contract.Requires(value != null);
        parent = value;
      }
    }

    public override string CompileName {
      get {
        if (compileName == null) {
          var name = Name;
          if (parent is MemberDecl && !name.StartsWith("_")) {
            // prepend "_" to type parameters of functions and methods, to ensure they don't clash with type parameters of the enclosing type
            name = "_" + name;
          }
          compileName = NonglobalVariable.CompilerizeName(name);
        }
        return compileName;
      }
    }

    /// <summary>
    /// NonVariant_Strict     (default) - non-variant, no uses left of an arrow
    /// NonVariant_Permissive    !      - non-variant
    /// Covariant_Strict         +      - co-variant, no uses left of an arrow
    /// Covariant_Permissive     *      - co-variant
    /// Contravariant            -      - contra-variant
    /// </summary>
    public enum TPVarianceSyntax { NonVariant_Strict, NonVariant_Permissive, Covariant_Strict, Covariant_Permissive, Contravariance }
    public enum TPVariance { Co, Non, Contra }
    public static TPVariance Negate(TPVariance v) {
      switch (v) {
        case TPVariance.Co:
          return TPVariance.Contra;
        case TPVariance.Contra:
          return TPVariance.Co;
        default:
          return v;
      }
    }
    public static int Direction(TPVariance v) {
      switch (v) {
        case TPVariance.Co:
          return 1;
        case TPVariance.Contra:
          return -1;
        default:
          return 0;
      }
    }
    public TPVarianceSyntax VarianceSyntax;
    public TPVariance Variance {
      get {
        switch (VarianceSyntax) {
          case TPVarianceSyntax.Covariant_Strict:
          case TPVarianceSyntax.Covariant_Permissive:
            return TPVariance.Co;
          case TPVarianceSyntax.NonVariant_Strict:
          case TPVarianceSyntax.NonVariant_Permissive:
            return TPVariance.Non;
          case TPVarianceSyntax.Contravariance:
            return TPVariance.Contra;
          default:
            Contract.Assert(false);  // unexpected VarianceSyntax
            throw new cce.UnreachableException();
        }
      }
    }
    public bool StrictVariance {
      get {
        switch (VarianceSyntax) {
          case TPVarianceSyntax.Covariant_Strict:
          case TPVarianceSyntax.NonVariant_Strict:
            return true;
          case TPVarianceSyntax.Covariant_Permissive:
          case TPVarianceSyntax.NonVariant_Permissive:
          case TPVarianceSyntax.Contravariance:
            return false;
          default:
            Contract.Assert(false);  // unexpected VarianceSyntax
            throw new cce.UnreachableException();
        }
      }
    }

    public enum EqualitySupportValue { Required, InferredRequired, Unspecified }
    public struct TypeParameterCharacteristics
    {
      public EqualitySupportValue EqualitySupport;  // the resolver may change this value from Unspecified to InferredRequired (for some signatures that may immediately imply that equality support is required)
      public Type.AutoInitInfo AutoInit;
      public bool HasCompiledValue => AutoInit == Type.AutoInitInfo.CompilableValue;
      public bool IsNonempty => AutoInit != Type.AutoInitInfo.MaybeEmpty;
      public bool ContainsNoReferenceTypes;
      public TypeParameterCharacteristics(bool dummy) {
        EqualitySupport = EqualitySupportValue.Unspecified;
        AutoInit = Type.AutoInitInfo.MaybeEmpty;
        ContainsNoReferenceTypes = false;
      }
      public TypeParameterCharacteristics(EqualitySupportValue eqSupport, Type.AutoInitInfo autoInit, bool containsNoReferenceTypes) {
        EqualitySupport = eqSupport;
        AutoInit = autoInit;
        ContainsNoReferenceTypes = containsNoReferenceTypes;
      }
    }
    public TypeParameterCharacteristics Characteristics;
    public bool SupportsEquality {
      get { return Characteristics.EqualitySupport != EqualitySupportValue.Unspecified; }
    }

    public bool NecessaryForEqualitySupportOfSurroundingInductiveDatatype = false;  // computed during resolution; relevant only when Parent denotes an IndDatatypeDecl

    public bool IsToplevelScope { // true if this type parameter is on a toplevel (ie. class C<T>), and false if it is on a member (ie. method m<T>(...))
      get { return parent is TopLevelDecl; }
    }
    public int PositionalIndex; // which type parameter this is (ie. in C<S, T, U>, S is 0, T is 1 and U is 2).

    public TypeParameter(IToken tok, string name, TPVarianceSyntax varianceS, TypeParameterCharacteristics characteristics)
      : base(tok, name, null, new List<TypeParameter>(), null, false) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Characteristics = characteristics;
      VarianceSyntax = varianceS;
    }

    public TypeParameter(IToken tok, string name, TPVarianceSyntax varianceS)
      : this(tok, name, varianceS, new TypeParameterCharacteristics(false)) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
    }

    public TypeParameter(IToken tok, string name, int positionalIndex, ParentType parent)
       : this(tok, name, TPVarianceSyntax.NonVariant_Strict)
    {
      PositionalIndex = positionalIndex;
      Parent = parent;
    }

    public override string FullName {
      get {
        // when debugging, print it all:
        return /* Parent.FullName + "." + */ Name;
      }
    }

    public static TypeParameterCharacteristics GetExplicitCharacteristics(TopLevelDecl d) {
      Contract.Requires(d != null);
      TypeParameterCharacteristics characteristics = new TypeParameterCharacteristics(false);
      if (d is OpaqueTypeDecl) {
        var dd = (OpaqueTypeDecl)d;
        characteristics = dd.Characteristics;
      } else if (d is TypeSynonymDecl) {
        var dd = (TypeSynonymDecl)d;
        characteristics = dd.Characteristics;
      }
      if (characteristics.EqualitySupport == EqualitySupportValue.InferredRequired) {
        return new TypeParameterCharacteristics(EqualitySupportValue.Unspecified, characteristics.AutoInit, characteristics.ContainsNoReferenceTypes);
      } else {
        return characteristics;
      }
    }
  }

  // Represents a submodule declaration at module level scope
  abstract public class ModuleDecl : TopLevelDecl
  {
    public override string WhatKind { get { return "module"; } }
    public ModuleSignature Signature; // filled in by resolution, in topological order.
    public virtual ModuleSignature AccessibleSignature(bool ignoreExports) {
      Contract.Requires(Signature != null);
      return Signature;
    }
    public virtual ModuleSignature AccessibleSignature() {
      Contract.Requires(Signature != null);
      return Signature;
    }
    public int Height;

    public readonly bool Opened;

    public ModuleDecl(IToken tok, string name, ModuleDefinition parent, bool opened, bool isRefining)
      : base(tok, name, parent, new List<TypeParameter>(), null, isRefining) {
        Height = -1;
      Signature = null;
      Opened = opened;
    }
    public abstract object Dereference();

    public int? ResolvedHash { get; set; }
  }
  // Represents module X { ... }
  public class LiteralModuleDecl : ModuleDecl
  {
    public readonly ModuleDefinition ModuleDef;
    public ModuleSignature DefaultExport;  // the default export set of the module. fill in by the resolver.

    private ModuleSignature emptySignature;
    public override ModuleSignature AccessibleSignature(bool ignoreExports) {
      if (ignoreExports) {
        return Signature;
      }
      return this.AccessibleSignature();
    }
    public override ModuleSignature AccessibleSignature() {
      if (DefaultExport == null) {
        if (emptySignature == null) {
          emptySignature = new ModuleSignature();
        }
        return emptySignature;
      }
      return DefaultExport;
    }

    public LiteralModuleDecl(ModuleDefinition module, ModuleDefinition parent)
      : base(module.tok, module.Name, parent, false, false) {
      ModuleDef = module;
    }
    public override object Dereference() { return ModuleDef; }
  }
  // Represents "module name = path;", where name is an identifier and path is a possibly qualified name.
  public class AliasModuleDecl : ModuleDecl
  {
    public readonly ModuleQualifiedId TargetQId; // generated by the parser, this is looked up
    public readonly List<IToken> Exports; // list of exports sets
    public bool ShadowsLiteralModule;  // initialized early during Resolution (and used not long after that); true for "import opened A = A" where "A" is a literal module in the same scope

    public AliasModuleDecl(ModuleQualifiedId path, IToken name, ModuleDefinition parent, bool opened, List<IToken> exports)
      : base(name, name.val, parent, opened, false) {
       Contract.Requires(path != null && path.Path.Count > 0);
       Contract.Requires(exports != null);
       Contract.Requires(exports.Count == 0 || path.Path.Count == 1);
       TargetQId = path;
       Exports = exports;
    }
    public override object Dereference() { return Signature.ModuleDef; }
  }

  // Represents "module name as path [ = compilePath];", where name is a identifier and path is a possibly qualified name.
  // Used to be called ModuleFacadeDecl -- renamed to be like LiteralModuleDecl, AliasModuleDecl
  public class AbstractModuleDecl : ModuleDecl
  {
    public readonly ModuleQualifiedId QId;
    public readonly List<IToken> Exports; // list of exports sets
    public ModuleDecl CompileRoot;
    public ModuleSignature OriginalSignature;

    public AbstractModuleDecl(ModuleQualifiedId qid, IToken name, ModuleDefinition parent, bool opened, List<IToken> exports)
      : base(name, name.val, parent, opened, false) {
      Contract.Requires(qid != null && qid.Path.Count > 0);
      Contract.Requires(exports != null);

      QId = qid;
      Exports = exports;
    }
    public override object Dereference() { return this; }
  }

  // Represents the exports of a module.
  public class ModuleExportDecl : ModuleDecl
  {
    public readonly bool IsDefault;
    public List<ExportSignature> Exports; // list of TopLevelDecl that are included in the export
    public List<IToken> Extends; // list of exports that are extended
    public readonly List<ModuleExportDecl> ExtendDecls = new List<ModuleExportDecl>(); // fill in by the resolver
    public readonly HashSet<Tuple<Declaration, bool>> ExportDecls = new HashSet<Tuple<Declaration, bool>>(); // fill in by the resolver
    public bool RevealAll; // only kept for initial rewriting, then discarded
    public bool ProvideAll;

    public readonly VisibilityScope ThisScope;
    public ModuleExportDecl(IToken tok, ModuleDefinition parent,
      List<ExportSignature> exports, List<IToken> extends, bool provideAll, bool revealAll, bool isDefault, bool isRefining)
      : base(tok, (isDefault || tok.val == "export") ? parent.Name : tok.val, parent, false, isRefining) {
      Contract.Requires(exports != null);
      IsDefault = isDefault;
      Exports = exports;
      Extends = extends;
      ProvideAll = provideAll;
      RevealAll = revealAll;
      ThisScope = new VisibilityScope(this.FullCompileName);
    }

    public ModuleExportDecl(IToken tok, string name, ModuleDefinition parent,
      List<ExportSignature> exports, List<IToken> extends, bool provideAll, bool revealAll, bool isDefault, bool isRefining)
      : base(tok, name, parent, false, isRefining) {
      Contract.Requires(exports != null);
      IsDefault = isDefault;
      Exports = exports;
      Extends = extends;
      ProvideAll = provideAll;
      RevealAll = revealAll;
      ThisScope = new VisibilityScope(this.FullCompileName);
    }

    public void SetupDefaultSignature() {
      Contract.Requires(this.Signature == null);
      var sig = new ModuleSignature();
      sig.ModuleDef = this.EnclosingModuleDefinition;
      sig.IsAbstract = this.EnclosingModuleDefinition.IsAbstract;
      sig.VisibilityScope = new VisibilityScope();
      sig.VisibilityScope.Augment(ThisScope);
      this.Signature = sig;
    }

    public override object Dereference() { return this; }
    public override bool CanBeExported() {
      return false;
    }

  }

  public class ExportSignature
  {
    public readonly IToken Tok;
    public readonly IToken ClassIdTok;
    public readonly bool Opaque;
    public readonly string ClassId;
    public readonly string Id;

    public Declaration Decl;  // filled in by the resolver

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Tok != null);
      Contract.Invariant(Id != null);
      Contract.Invariant((ClassId != null) == (ClassIdTok != null));
    }

    public ExportSignature(IToken prefixTok, string prefix, IToken idTok, string id, bool opaque) {
      Contract.Requires(prefixTok != null);
      Contract.Requires(prefix != null);
      Contract.Requires(idTok != null);
      Contract.Requires(id != null);
      Tok = idTok;
      ClassIdTok = prefixTok;
      ClassId = prefix;
      Id = id;
      Opaque = opaque;
    }

    public ExportSignature(IToken idTok, string id, bool opaque) {
      Contract.Requires(idTok != null);
      Contract.Requires(id != null);
      Tok = idTok;
      Id = id;
      Opaque = opaque;
    }

    public override string ToString() {
      if (ClassId != null) {
        return ClassId + "." + Id;
      }
      return Id;
    }
  }

  public class ModuleSignature {
    public  VisibilityScope VisibilityScope = null;
    public readonly Dictionary<string, TopLevelDecl> TopLevels = new Dictionary<string, TopLevelDecl>();
    public readonly Dictionary<string, ModuleExportDecl> ExportSets = new Dictionary<string, ModuleExportDecl>();
    public readonly Dictionary<string, Tuple<DatatypeCtor, bool>> Ctors = new Dictionary<string, Tuple<DatatypeCtor, bool>>();
    public readonly Dictionary<string, MemberDecl> StaticMembers = new Dictionary<string, MemberDecl>();
    public ModuleDefinition ModuleDef = null; // Note: this is null if this signature does not correspond to a specific definition (i.e.
                                              // it is abstract). Otherwise, it points to that definition.
    public ModuleSignature CompileSignature = null; // This is the version of the signature that should be used at compile time.
    public ModuleSignature Refines = null;
    public bool IsAbstract = false;
    public ModuleSignature() {}
    public int? ResolvedHash { get; set; }

    // Qualified accesses follow module imports
    public bool FindImport(string name, out ModuleDecl decl) {
      TopLevelDecl top;
      if (TopLevels.TryGetValue(name, out top) && top is ModuleDecl) {
          decl = (ModuleDecl)top;
        return true;
      } else {
        decl = null;
        return false;
      }
    }
  }

  public class ModuleQualifiedId {
    public readonly List<IToken> Path; // Path != null && Path.Count > 0

    public ModuleQualifiedId(List<IToken> path) {
      Contract.Assert(path != null && path.Count > 0);
      this.Path = path; // note that the list is aliased -- not to be modified after construction
    }

    // Creates a clone, including a copy of the list;
    // if the argument is true, resolution information is included
    public ModuleQualifiedId Clone(bool includeResInfo) {
      List<IToken> newlist = new List<IToken>(Path);
      ModuleQualifiedId cl = new ModuleQualifiedId(newlist);
      if (includeResInfo) {
        cl.Root = this.Root;
        cl.Decl = this.Decl;
        cl.Def = this.Def;
        cl.Sig = this.Sig;
        Contract.Assert(this.Def == this.Sig.ModuleDef);
      }
      return cl;
    }

    public string rootName() {
      return Path[0].val;
    }

    public IToken rootToken() {
      return Path[0];
    }

    override public string ToString() {
      string s = Path[0].val;
      for (int i = 1; i < Path.Count; ++i) {
        s = s + "." + Path[i].val;
      }

      return s;
    }

    public void SetRoot(ModuleDecl m) {
      this.Root = m;
    }

    public void Set(ModuleDecl m) {
      if (m == null) {
        this.Decl = null;
        this.Def = null;
        this.Sig = null;
      } else {
        this.Decl = m;
        this.Def = ((LiteralModuleDecl)m).ModuleDef;
        this.Sig = m.Signature;
      }
    }

    // The following are filled in during resolution
    // Note that the root (first path segment) is resolved initially,
    // as it is needed to determine dependency relationships.
    // Then later the rest of the path is resolved, at which point all of the
    // ids in the path have been fully resolved
    // Note also that the resolution of the root depends on the syntactice location
    // of the qualified id; the resolution of subsequent ids depends on the
    // default export set of the previous id.
    public ModuleDecl Root; // the module corresponding to Path[0].val
    public ModuleDecl Decl; // the module corresponding to the full path
    public ModuleDefinition Def; // the module definition corresponding to the full path
    public ModuleSignature Sig; // the module signature corresponding to the full path
  }

  public class ModuleDefinition : INamedRegion, IAttributeBearingDeclaration
  {
    public readonly IToken tok;
    public IToken BodyStartTok = Token.NoToken;
    public IToken BodyEndTok = Token.NoToken;
    public readonly string DafnyName; // The (not-qualified) name as seen in Dafny source code
    public readonly string Name; // (Last segment of the) module name
    public string FullDafnyName {
      get {
        if (EnclosingModule == null) return "";
        string n = EnclosingModule.FullDafnyName;
        return (n.Length == 0 ? n : (n + ".")) + DafnyName;
      }
    }
    public string FullName {
      get {
        if (EnclosingModule == null || EnclosingModule.IsDefaultModule) {
          return Name;
        } else {
          return EnclosingModule.FullName + "." + Name;
        }
      }
    }
    public readonly List<IToken> PrefixIds; // The qualified module name, except the last segment when a
                                            // nested module declaration is outside its enclosing module
    IToken INamedRegion.BodyStartTok { get { return BodyStartTok; } }
    IToken INamedRegion.BodyEndTok { get { return BodyEndTok; } }
    string INamedRegion.Name { get { return Name; } }
    public ModuleDefinition EnclosingModule;  // readonly, except can be changed by resolver for prefix-named modules when the real parent is discovered
    public readonly Attributes Attributes;
    public ModuleQualifiedId RefinementQId; // full qualified ID of the refinement parent, null if no refinement base
    public bool SuccessfullyResolved;  // set to true upon successful resolution; modules that import an unsuccessfully resolved module are not themselves resolved

    public List<Include> Includes;

    public readonly List<TopLevelDecl> TopLevelDecls = new List<TopLevelDecl>();  // filled in by the parser; readonly after that, except for the addition of prefix-named modules, which happens in the resolver
    public readonly List<Tuple<List<IToken>, LiteralModuleDecl>> PrefixNamedModules = new List<Tuple<List<IToken>, LiteralModuleDecl>>();  // filled in by the parser; emptied by the resolver
    public readonly Graph<ICallable> CallGraph = new Graph<ICallable>();  // filled in during resolution
    public int Height;  // height in the topological sorting of modules; filled in during resolution
    public readonly bool IsAbstract;
    public readonly bool IsFacade; // True iff this module represents a module facade (that is, an abstract interface)
    private readonly bool IsBuiltinName; // true if this is something like _System that shouldn't have it's name mangled.
    public readonly bool IsToBeVerified;
    public readonly bool IsToBeCompiled;

    public int? ResolvedHash { get; set; }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(TopLevelDecls));
      Contract.Invariant(CallGraph != null);
    }

    public ModuleDefinition(IToken tok, string name, List<IToken> prefixIds, bool isAbstract, bool isFacade,
      ModuleQualifiedId refinementQId, ModuleDefinition parent, Attributes attributes, bool isBuiltinName,
      bool isToBeVerified, bool isToBeCompiled)
    {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      this.tok = tok;
      this.DafnyName = tok.val;
      this.Name = name;
      this.PrefixIds = prefixIds;
      this.Attributes = attributes;
      this.EnclosingModule = parent;
      this.RefinementQId = refinementQId;
      this.IsAbstract = isAbstract;
      this.IsFacade = isFacade;
      this.Includes = new List<Include>();
      this.IsBuiltinName = isBuiltinName;
      this.IsToBeVerified = isToBeVerified;
      this.IsToBeCompiled = isToBeCompiled;
    }

    VisibilityScope visibilityScope;

    public VisibilityScope VisibilityScope {
      get {
        if (visibilityScope == null) {
          visibilityScope = new VisibilityScope(this.CompileName);
        }
        return visibilityScope;
      }
    }

    public virtual bool IsDefaultModule {
      get {
        return false;
      }
    }
    string compileName;
    public string CompileName {
      get {
        if (compileName == null) {
          var externArgs = DafnyOptions.O.DisallowExterns ? null : Attributes.FindExpressions(this.Attributes, "extern");
          if (externArgs != null && 1 <= externArgs.Count && externArgs[0] is StringLiteralExpr) {
            compileName = (string)((StringLiteralExpr)externArgs[0]).Value;
          } else if (IsBuiltinName || externArgs != null) {
            compileName = Name;
          } else {
            if (EnclosingModule != null && EnclosingModule.Name != "_module") {
              // Include all names in the module tree path, to disambiguate when compiling
              // a flat list of modules.
              // Use an "underscore-escaped" character as a module name separator, since
              // underscores are already used as escape characters in CompilerizeName()
              compileName = EnclosingModule.CompileName + "_m" + NonglobalVariable.CompilerizeName(Name);
            } else {
              compileName = NonglobalVariable.CompilerizeName(Name);
            }
          }
        }
        return compileName;
      }
    }

    public string RefinementCompileName {
      get {
        return this.CompileName;
      }
    }

    /// <summary>
    /// Determines if "a" and "b" are in the same strongly connected component of the call graph, that is,
    /// if "a" and "b" are mutually recursive.
    /// Assumes that CallGraph has already been filled in for the modules containing "a" and "b".
    /// </summary>
    public static bool InSameSCC(ICallable a, ICallable b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      if (a is SpecialFunction || b is SpecialFunction) { return false; }
      var module = a.EnclosingModule;
      return module == b.EnclosingModule && module.CallGraph.GetSCCRepresentative(a) == module.CallGraph.GetSCCRepresentative(b);
    }

    /// <summary>
    /// Return the representative elements of the SCCs that contain any member declaration in a
    /// class in "declarations".
    /// Note, the representative element may in some cases be a Method, not necessarily a Function.
    /// </summary>
    public static IEnumerable<ICallable> AllFunctionSCCs(List<TopLevelDecl> declarations) {
      var set = new HashSet<ICallable>();
      foreach (var d in declarations) {
        var cl = d as TopLevelDeclWithMembers;
        if (cl != null) {
          var module = cl.EnclosingModuleDefinition;
          foreach (var member in cl.Members) {
            var fn = member as Function;
            if (fn != null) {
              var repr = module.CallGraph.GetSCCRepresentative(fn);
              set.Add(repr);
            }
          }
        }
      }
      return set;
    }

    public static IEnumerable<Function> AllFunctions(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        var cl = d as TopLevelDeclWithMembers;
        if (cl != null) {
          foreach (var member in cl.Members) {
            var fn = member as Function;
            if (fn != null) {
              yield return fn;
            }
          }
        }
      }
    }

    public static IEnumerable<Field> AllFields(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        var cl = d as TopLevelDeclWithMembers;
        if (cl != null) {
          foreach (var member in cl.Members) {
            var fn = member as Field;
            if (fn != null) {
              yield return fn;
            }
          }
        }
      }
    }

    public static IEnumerable<ClassDecl> AllClasses(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        if (d is ClassDecl cl) {
          yield return cl;
        }
      }
    }

    public static IEnumerable<TopLevelDeclWithMembers> AllTypesWithMembers(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        if (d is TopLevelDeclWithMembers cl) {
          yield return cl;
        }
      }
    }

    /// <summary>
    /// Yields all functions and methods that are members of some type in the given list of
    /// declarations.
    /// Note, an iterator declaration is a type, in this sense.
    /// Note, if the given list are the top-level declarations of a module, the yield will include
    /// greatest lemmas but not their associated prefix lemmas (which are tucked into the greatest lemma's
    /// .PrefixLemma field).
    /// </summary>
    public static IEnumerable<ICallable> AllCallables(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        var cl = d as TopLevelDeclWithMembers;
        if (cl != null) {
          foreach (var member in cl.Members) {
            var clbl = member as ICallable;
            if (clbl != null && !(member is ConstantField)) {
              yield return clbl;
            }
          }
        }
      }
    }

    /// <summary>
    /// Yields all functions and methods that are members of some non-iterator type in the given
    /// list of declarations, as well as any IteratorDecl's in that list.
    /// </summary>
    public static IEnumerable<ICallable> AllItersAndCallables(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        if (d is IteratorDecl) {
          var iter = (IteratorDecl)d;
          yield return iter;
        } else if (d is TopLevelDeclWithMembers) {
          var cl = (TopLevelDeclWithMembers)d;
          foreach (var member in cl.Members) {
            var clbl = member as ICallable;
            if (clbl != null) {
              yield return clbl;
            }
          }
        }
      }
    }

    public static IEnumerable<IteratorDecl> AllIteratorDecls(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        var iter = d as IteratorDecl;
        if (iter != null) {
          yield return iter;
        }
      }
    }

    /// <summary>
    /// Emits the declarations in "declarations", but for each such declaration that is a class with
    /// a corresponding non-null type, also emits that non-null type *after* the class declaration.
    /// </summary>
    public static IEnumerable<TopLevelDecl> AllDeclarationsAndNonNullTypeDecls(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        yield return d;
        var cl = d as ClassDecl;
        if (cl != null && cl.NonNullTypeDecl != null) {
          yield return cl.NonNullTypeDecl;
        }
      }
    }

    public static IEnumerable<ExtremeLemma> AllExtremeLemmas(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        var cl = d as TopLevelDeclWithMembers;
        if (cl != null) {
          foreach (var member in cl.Members) {
            var m = member as ExtremeLemma;
            if (m != null) {
              yield return m;
            }
          }
        }
      }
    }

    public bool IsEssentiallyEmptyModuleBody() {
      foreach (var d in TopLevelDecls) {
        if (d is ModuleDecl) {
          // modules don't count
          continue;
        } else if (d is ClassDecl) {
          var cl = (ClassDecl)d;
          if (cl.Members.Count == 0) {
            // the class is empty, so it doesn't count
            continue;
          }
        }
        return false;
      }
      return true;
    }
  }

  public class DefaultModuleDecl : ModuleDefinition {
    public DefaultModuleDecl()
      : base(Token.NoToken, "_module", new List<IToken>(), false, false, null, null, null, true, true, true) {
    }
    public override bool IsDefaultModule {
      get {
        return true;
      }
    }
  }

  public abstract class TopLevelDecl : Declaration, TypeParameter.ParentType {
    public abstract string WhatKind { get; }
    public readonly ModuleDefinition EnclosingModuleDefinition;
    public readonly List<TypeParameter> TypeArgs;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(TypeArgs));
    }

    public TopLevelDecl(IToken tok, string name, ModuleDefinition enclosingModule, List<TypeParameter> typeArgs, Attributes attributes, bool isRefining)
      : base(tok, name, attributes, isRefining) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      EnclosingModuleDefinition = enclosingModule;
      TypeArgs = typeArgs;
    }

    public string FullDafnyName {
      get {
        if (Name == "_module") return "";
        if (Name == "_default") return EnclosingModuleDefinition.FullDafnyName;
        string n = EnclosingModuleDefinition.FullDafnyName;
        return (n.Length == 0 ? n : (n + ".")) + Name;
      }
    }
    public virtual string FullName {
      get {
        return EnclosingModuleDefinition.FullName + "." + Name;
      }
    }
    public string FullSanitizedName {
      get {
        return EnclosingModuleDefinition.CompileName + "." + CompileName;
      }
    }

    public string FullSanitizedRefinementName {
      get {
        return EnclosingModuleDefinition.RefinementCompileName + "." + CompileName;
      }
    }

    public string FullNameInContext(ModuleDefinition context) {
      if (EnclosingModuleDefinition == context) {
        return Name;
      } else {
        return EnclosingModuleDefinition.Name + "." + Name;
      }
    }
    public string FullCompileName {
      get {
        var externArgs = Attributes.FindExpressions(this.Attributes, "extern");
        if (!DafnyOptions.O.DisallowExterns && externArgs != null) {
          if (externArgs.Count == 2 && externArgs[0] is StringLiteralExpr && externArgs[1] is StringLiteralExpr) {
            return externArgs[0].AsStringLiteral() + "." + externArgs[1].AsStringLiteral();
          }
        }
        if (EnclosingModuleDefinition.IsDefaultModule && DafnyOptions.O.CompileTarget == DafnyOptions.CompilationTarget.Csharp) {
          return Declaration.IdProtect(CompileName);
        } else {
          return Declaration.IdProtect(EnclosingModuleDefinition.CompileName) + "." + Declaration.IdProtect(CompileName);
        }
      }
    }

    public TopLevelDecl ViewAsClass {
      get {
        if (this is NonNullTypeDecl) {
          return ((NonNullTypeDecl)this).Class;
        } else {
          return this;
        }
      }
    }

    /// <summary>
    /// Return the list of parent types of "this", where the type parameters
    /// of "this" have been instantiated by "typeArgs". For example, for a subset
    /// type, the return value is the RHS type, appropriately instantiated. As
    /// two other examples, given
    ///     class C<X> extends J<X, int>
    /// C.ParentTypes(real) = J<real, int>    // non-null types C and J
    /// C?.ParentTypes(real) = J?<real, int>  // possibly-null type C? and J?
    /// </summary>
    public virtual List<Type> ParentTypes(List<Type> typeArgs) {
      Contract.Requires(typeArgs != null);
      Contract.Requires(this.TypeArgs.Count == typeArgs.Count);
      return new List<Type>();
    }
  }

  public abstract class TopLevelDeclWithMembers : TopLevelDecl {
    public readonly List<MemberDecl> Members;

    // The following fields keep track of parent traits
    public readonly List<MemberDecl> InheritedMembers = new List<MemberDecl>();  // these are instance members declared in parent traits
    public readonly List<Type> ParentTraits;  // these are the types that are parsed after the keyword 'extends'; note, for a successfully resolved program, these are UserDefinedType's where .ResolvedClas is NonNullTypeDecl
    public readonly Dictionary<TypeParameter, Type> ParentFormalTypeParametersToActuals = new Dictionary<TypeParameter, Type>();  // maps parent traits' type parameters to actuals

    /// <summary>
    /// TraitParentHeads contains the head of each distinct trait parent. It is initialized during resolution.
    /// </summary>
    public readonly List<TraitDecl> ParentTraitHeads = new List<TraitDecl>();

    public InheritanceInformationClass ParentTypeInformation;  // filled in during resolution
    public class InheritanceInformationClass
    {
      private readonly Dictionary<TraitDecl, List<(Type, List<TraitDecl> /*via this parent path*/)>> info = new Dictionary<TraitDecl, List<(Type, List<TraitDecl>)>>();

      /// <summary>
      /// Returns a subset of the trait's ParentTraits, but not repeating any head type.
      /// Assumes the declaration has been successfully resolved.
      /// </summary>
      public List<Type> UniqueParentTraits() {
        return info.ToList().ConvertAll(entry => entry.Value[0].Item1);
      }

      public void Record(TraitDecl traitHead, UserDefinedType parentType) {
        Contract.Requires(traitHead != null);
        Contract.Requires(parentType != null);
        Contract.Requires(parentType.ResolvedClass is NonNullTypeDecl nntd && nntd.ViewAsClass == traitHead);

        if (!info.TryGetValue(traitHead, out var list)) {
          list = new List<(Type, List<TraitDecl>)>();
          info.Add(traitHead, list);
        }
        list.Add((parentType, new List<TraitDecl>()));
      }

      public void Extend(TraitDecl parent, InheritanceInformationClass parentInfo, Dictionary<TypeParameter, Type> typeMap) {
        Contract.Requires(parent != null);
        Contract.Requires(parentInfo != null);
        Contract.Requires(typeMap != null);

        foreach (var entry in parentInfo.info) {
          var traitHead = entry.Key;
          if (!info.TryGetValue(traitHead, out var list)) {
            list = new List<(Type, List<TraitDecl>)>();
            info.Add(traitHead, list);
          }
          foreach (var pair in entry.Value) {
            var ty = Resolver.SubstType(pair.Item1, typeMap);
            // prepend the path with "parent"
            var parentPath = new List<TraitDecl>() {parent};
            parentPath.AddRange(pair.Item2);
            list.Add((ty, parentPath));
          }
        }
      }

      public IEnumerable<List<(Type, List<TraitDecl>)>> GetTypeInstantiationGroups() {
        foreach (var pair in info.Values) {
          yield return pair;
        }
      }
    }

    public TopLevelDeclWithMembers(IToken tok, string name, ModuleDefinition module, List<TypeParameter> typeArgs, List<MemberDecl> members, Attributes attributes, bool isRefining, List<Type>/*?*/ traits = null)
      : base(tok, name, module, typeArgs, attributes, isRefining) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(members));
      Members = members;
      ParentTraits = traits ?? new List<Type>();
    }

    public static List<UserDefinedType> CommonTraits(TopLevelDeclWithMembers a, TopLevelDeclWithMembers b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      var aa = a.TraitAncestors();
      var bb = b.TraitAncestors();
      aa.IntersectWith(bb);
      var types = new List<UserDefinedType>();
      foreach (var t in aa) {
        var typeArgs = t.TypeArgs.ConvertAll(tp => a.ParentFormalTypeParametersToActuals[tp]);
        var u = new UserDefinedType(t.tok, t.Name + "?", t, typeArgs);
        types.Add(u);
      }
      return types;
    }

    /// <summary>
    /// Returns the set of transitive parent traits (not including "this" itself).
    /// This method assumes the .ParentTraits fields have been checked for various cycle restrictions.
    /// </summary>
    public ISet<TraitDecl> TraitAncestors() {
      var s = new HashSet<TraitDecl>();
      AddTraitAncestors(s);
      return s;
    }
    /// <summary>
    /// Adds to "s" the transitive parent traits (not including "this" itself).
    /// This method assumes the .ParentTraits fields have been checked for various cycle restrictions.
    /// </summary>
    private void AddTraitAncestors(ISet<TraitDecl> s) {
      Contract.Requires(s != null);
      foreach (var parent in ParentTraits) {
        var udt = (UserDefinedType)parent;  // in a successfully resolved program, we expect all .ParentTraits to be a UserDefinedType
        var nntd = (NonNullTypeDecl)udt.ResolvedClass;  // we expect the trait type to be the non-null version of the trait type
        var tr = (TraitDecl)nntd.Class;
        s.Add(tr);
        tr.AddTraitAncestors(s);
      }
    }
  }

  public class TraitDecl : ClassDecl {
    public override string WhatKind { get { return "trait"; } }
    public bool IsParent { set; get; }
    public TraitDecl(IToken tok, string name, ModuleDefinition module,
      List<TypeParameter> typeArgs, [Captured] List<MemberDecl> members, Attributes attributes, bool isRefining, List<Type>/*?*/ traits)
      : base(tok, name, module, typeArgs, members, attributes, isRefining, traits) { }
  }

  public class ClassDecl : TopLevelDeclWithMembers, RevealableTypeDecl {
    public override string WhatKind { get { return "class"; } }
    public override bool CanBeRevealed() { return true; }
    public bool HasConstructor;  // filled in (early) during resolution; true iff there exists a member that is a Constructor
    public readonly NonNullTypeDecl NonNullTypeDecl;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Members));
      Contract.Invariant(ParentTraits != null);
    }

    public ClassDecl(IToken tok, string name, ModuleDefinition module,
      List<TypeParameter> typeArgs, [Captured] List<MemberDecl> members, Attributes attributes, bool isRefining, List<Type>/*?*/ traits)
      : base(tok, name, module, typeArgs, members, attributes, isRefining, traits) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(members));
      Contract.Assume(!(this is ArrowTypeDecl));  // this is also a precondition, really, but "this" cannot be mentioned in Requires of a constructor; ArrowTypeDecl should use the next constructor
      if (!IsDefaultClass) {
        NonNullTypeDecl = new NonNullTypeDecl(this);
      }
      this.NewSelfSynonym();
    }
    /// <summary>
    /// The following constructor is supposed to be called by the ArrowTypeDecl subtype, in order to avoid
    /// the call to this.NewSelfSynonym() (because NewSelfSynonym() depends on the .Arity field having been
    /// set, which it hasn't during the base call of the ArrowTypeDecl constructor). Instead, the ArrowTypeDecl
    /// constructor will do that call.
    /// </summary>
    protected ClassDecl(IToken tok, string name, ModuleDefinition module,
      List<TypeParameter> typeArgs, [Captured] List<MemberDecl> members, Attributes attributes, bool isRefining)
      : base(tok, name, module, typeArgs, members, attributes, isRefining, null) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(members));
      Contract.Assume(this is ArrowTypeDecl);  // this is also a precondition, really, but "this" cannot be mentioned in Requires of a constructor
    }
    public virtual bool IsDefaultClass {
      get {
        return false;
      }
    }

    public bool IsObjectTrait {
      get => Name == "object";
    }

    internal bool HeadDerivesFrom(TopLevelDecl b) {
      Contract.Requires(b != null);
      return this == b || this.ParentTraitHeads.Exists(tr => tr.HeadDerivesFrom(b));
    }

    public List<Type> NonNullTraitsWithArgument(List<Type> typeArgs) {
      Contract.Requires(typeArgs != null);
      Contract.Requires(typeArgs.Count == TypeArgs.Count);

      // Instantiate with the actual type arguments
      if (typeArgs.Count == 0) {
        // this optimization seems worthwhile
        return ParentTraits;
      } else {
        var subst = Resolver.TypeSubstitutionMap(TypeArgs, typeArgs);
        return ParentTraits.ConvertAll(traitType => Resolver.SubstType(traitType, subst));
      }
    }

    public List<Type> PossiblyNullTraitsWithArgument(List<Type> typeArgs) {
      Contract.Requires(typeArgs != null);
      Contract.Requires(typeArgs.Count == TypeArgs.Count);
      // Instantiate with the actual type arguments
      var subst = Resolver.TypeSubstitutionMap(TypeArgs, typeArgs);
      return ParentTraits.ConvertAll(traitType => (Type)UserDefinedType.CreateNullableType((UserDefinedType)Resolver.SubstType(traitType, subst)));
    }

    public override List<Type> ParentTypes(List<Type> typeArgs) {
      return PossiblyNullTraitsWithArgument(typeArgs);
    }

    TopLevelDecl RevealableTypeDecl.AsTopLevelDecl { get => this; }
  }

  public class DefaultClassDecl : ClassDecl {
    public DefaultClassDecl(ModuleDefinition module, [Captured] List<MemberDecl> members)
      : base(Token.NoToken, "_default", module, new List<TypeParameter>(), members, null, false, null) {
      Contract.Requires(module != null);
      Contract.Requires(cce.NonNullElements(members));
    }
    public override bool IsDefaultClass {
      get {
        return true;
      }
    }
  }

  public class ArrayClassDecl : ClassDecl {
    public override string WhatKind { get { return "array type"; } }
    public readonly int Dims;
    public ArrayClassDecl(int dims, ModuleDefinition module, Attributes attrs)
    : base(Token.NoToken, BuiltIns.ArrayClassName(dims), module,
      new List<TypeParameter>(new TypeParameter[]{ new TypeParameter(Token.NoToken, "arg", TypeParameter.TPVarianceSyntax.NonVariant_Strict) }),
      new List<MemberDecl>(), attrs, false, null)
    {
      Contract.Requires(1 <= dims);
      Contract.Requires(module != null);

      Dims = dims;
      // Resolve type parameter
      Contract.Assert(TypeArgs.Count == 1);
      var tp = TypeArgs[0];
      tp.Parent = this;
      tp.PositionalIndex = 0;
    }
  }

  public class ArrowTypeDecl : ClassDecl
  {
    public override string WhatKind { get { return "function type"; } }
    public readonly int Arity;
    public readonly Function Requires;
    public readonly Function Reads;

    public ArrowTypeDecl(List<TypeParameter> tps, Function req, Function reads, ModuleDefinition module, Attributes attributes)
      : base(Token.NoToken, ArrowType.ArrowTypeName(tps.Count - 1), module, tps,
             new List<MemberDecl> { req, reads }, attributes, false) {
      Contract.Requires(tps != null && 1 <= tps.Count);
      Contract.Requires(req != null);
      Contract.Requires(reads != null);
      Contract.Requires(module != null);
      Arity = tps.Count - 1;
      Requires = req;
      Reads = reads;
      Requires.EnclosingClass = this;
      Reads.EnclosingClass = this;
      this.NewSelfSynonym();
    }
  }

  public abstract class DatatypeDecl : TopLevelDeclWithMembers, RevealableTypeDecl, ICallable
  {
    public override bool CanBeRevealed() { return true; }
    public readonly List<DatatypeCtor> Ctors;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Ctors));
      Contract.Invariant(1 <= Ctors.Count);
    }

    public DatatypeDecl(IToken tok, string name, ModuleDefinition module, List<TypeParameter> typeArgs,
      [Captured] List<DatatypeCtor> ctors, List<MemberDecl> members, Attributes attributes, bool isRefining)
      : base(tok, name, module, typeArgs, members, attributes, isRefining) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(ctors));
      Contract.Requires(cce.NonNullElements(members));
      Contract.Requires(1 <= ctors.Count);
      Ctors = ctors;
      this.NewSelfSynonym();
    }
    public bool HasFinitePossibleValues {
      get {
        return (TypeArgs.Count == 0 && Ctors.TrueForAll(ctr => ctr.Formals.Count == 0));
      }
    }

    public bool IsRecordType {
      get { return this is IndDatatypeDecl && Ctors.Count == 1; }
    }

    TopLevelDecl RevealableTypeDecl.AsTopLevelDecl { get { return this; } }

    bool ICodeContext.IsGhost { get { return true; } }
    List<TypeParameter> ICodeContext.TypeArgs { get { return TypeArgs; } }
    List<Formal> ICodeContext.Ins { get { return new List<Formal>(); } }
    ModuleDefinition ICodeContext.EnclosingModule { get { return EnclosingModuleDefinition; } }
    bool ICodeContext.MustReverify { get { return false; } }
    bool ICodeContext.AllowsNontermination { get { return false; } }
    IToken ICallable.Tok { get { return tok; } }
    string ICallable.NameRelativeToModule { get { return Name; } }
    Specification<Expression> ICallable.Decreases {
      get {
        // The resolver checks that a NewtypeDecl sits in its own SSC in the call graph.  Therefore,
        // the question of what its Decreases clause is should never arise.
        throw new cce.UnreachableException();
      }
    }
    bool ICallable.InferredDecreases {
      get { throw new cce.UnreachableException(); }  // see comment above about ICallable.Decreases
      set { throw new cce.UnreachableException(); }  // see comment above about ICallable.Decreases
    }

    public abstract DatatypeCtor GetGroundingCtor();
  }

  public class IndDatatypeDecl : DatatypeDecl, RevealableTypeDecl
  {
    public override string WhatKind { get { return "datatype"; } }
    public DatatypeCtor GroundingCtor;  // set during resolution

    public override DatatypeCtor GetGroundingCtor() {
      return GroundingCtor;
    }

    public bool[] TypeParametersUsedInConstructionByGroundingCtor;  // set during resolution; has same length as the number of type arguments

    public enum ES { NotYetComputed, Never, ConsultTypeArguments }
    public ES EqualitySupport = ES.NotYetComputed;

    public IndDatatypeDecl(IToken tok, string name, ModuleDefinition module, List<TypeParameter> typeArgs,
      [Captured] List<DatatypeCtor> ctors, List<MemberDecl> members, Attributes attributes, bool isRefining)
      : base(tok, name, module, typeArgs, ctors, members, attributes, isRefining) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(ctors));
      Contract.Requires(cce.NonNullElements(members));
      Contract.Requires(1 <= ctors.Count);
    }
  }

  public class TupleTypeDecl : IndDatatypeDecl
  {
    public readonly List<bool> ArgumentGhostness;

    public int Dims
    {
      get { return ArgumentGhostness.Count; }
    }
    
    public int NonGhostDims
    {
      get { return ArgumentGhostness.Count(x => !x); }
    }

    /// <summary>
    /// Construct a resolved built-in tuple type with "dim" arguments.  "systemModule" is expected to be the _System module.
    /// </summary>
    public TupleTypeDecl(List<bool> argumentGhostness, ModuleDefinition systemModule, Attributes attributes)
      : this(systemModule, CreateCovariantTypeParameters(argumentGhostness.Count), argumentGhostness, attributes) {
      Contract.Requires(0 <= Dims);
      Contract.Requires(systemModule != null);

      // Resolve the type parameters here
      Contract.Assert(TypeArgs.Count == Dims);
      for (var i = 0; i < Dims; i++) {
        var tp = TypeArgs[i];
        tp.Parent = this;
        tp.PositionalIndex = i;
      }
    }

    private TupleTypeDecl(ModuleDefinition systemModule, List<TypeParameter> typeArgs, List<bool> argumentGhostness, Attributes attributes)
      : base(Token.NoToken, BuiltIns.TupleTypeName(argumentGhostness), systemModule, typeArgs, CreateConstructors(typeArgs, argumentGhostness), new List<MemberDecl>(), attributes, false) {
      Contract.Requires(systemModule != null);
      Contract.Requires(typeArgs != null);
      ArgumentGhostness = argumentGhostness;
      foreach (var ctor in Ctors) {
        ctor.EnclosingDatatype = this;  // resolve here
        GroundingCtor = ctor;
        TypeParametersUsedInConstructionByGroundingCtor = new bool[typeArgs.Count];
        for (int i = 0; i < typeArgs.Count; i++)
        {
          TypeParametersUsedInConstructionByGroundingCtor[i] = !argumentGhostness[i];
        }
      }
      this.EqualitySupport = ES.ConsultTypeArguments;
    }
    private static List<TypeParameter> CreateCovariantTypeParameters(int dims) {
      Contract.Requires(0 <= dims);
      var ts = new List<TypeParameter>();
      for (int i = 0; i < dims; i++) {
        var tp = new TypeParameter(Token.NoToken, "T" + i, TypeParameter.TPVarianceSyntax.Covariant_Strict);
        tp.NecessaryForEqualitySupportOfSurroundingInductiveDatatype = true;
        ts.Add(tp);
      }
      return ts;
    }
    private static List<DatatypeCtor> CreateConstructors(List<TypeParameter> typeArgs, List<bool> argumentGhostness) {
      Contract.Requires(typeArgs != null);
      var formals = new List<Formal>();
      for (int i = 0; i < typeArgs.Count; i++) {
        var tp = typeArgs[i];
        var f = new Formal(Token.NoToken, i.ToString(), new UserDefinedType(Token.NoToken, tp), true, argumentGhostness[i], null);
        formals.Add(f);
      }
      string ctorName = BuiltIns.TupleTypeCtorNamePrefix + typeArgs.Count;
      var ctor = new DatatypeCtor(Token.NoToken, ctorName, formals, null);
      return new List<DatatypeCtor>() { ctor };
    }

    public override string CompileName {
      get
      {
        return "Tuple" + BuiltIns.ArgumentGhostnessToString(ArgumentGhostness);
      }
    }
  }

  public class CoDatatypeDecl : DatatypeDecl
  {
    public override string WhatKind { get { return "codatatype"; } }
    public CoDatatypeDecl SscRepr;  // filled in during resolution

    public CoDatatypeDecl(IToken tok, string name, ModuleDefinition module, List<TypeParameter> typeArgs,
      [Captured] List<DatatypeCtor> ctors, List<MemberDecl> members, Attributes attributes, bool isRefining)
      : base(tok, name, module, typeArgs, ctors, members, attributes, isRefining) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(ctors));
      Contract.Requires(cce.NonNullElements(members));
      Contract.Requires(1 <= ctors.Count);
    }

    public override DatatypeCtor GetGroundingCtor() {
      return Ctors[0];
    }
  }

  /// <summary>
  /// The "ValuetypeDecl" class models the built-in value types (like bool, int, set, and seq.
  /// Its primary function is to hold the formal type parameters and built-in members of these types.
  /// </summary>
  public class ValuetypeDecl : TopLevelDecl
  {
    public override string WhatKind { get { return Name; } }
    public readonly Dictionary<string, MemberDecl> Members = new Dictionary<string, MemberDecl>();
    readonly Func<Type, bool> typeTester;
    readonly Func<List<Type>, Type>/*?*/ typeCreator;

    public ValuetypeDecl(string name, ModuleDefinition module, int typeParameterCount, Func<Type, bool> typeTester, Func<List<Type>, Type>/*?*/ typeCreator)
      : base(Token.NoToken, name, module, new List<TypeParameter>(), null, false) {
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(0 <= typeParameterCount);
      Contract.Requires(typeTester != null);
      // fill in the type parameters
      for (int i = 0; i < typeParameterCount; i++) {
        TypeArgs.Add(new TypeParameter(Token.NoToken, ((char)('T' + i)).ToString(), i, this));
      }
      this.typeTester = typeTester;
      this.typeCreator = typeCreator;
    }

    public bool IsThisType(Type t) {
      Contract.Assert(t != null);
      return typeTester(t);
    }

    public Type CreateType(List<Type> typeArgs) {
      Contract.Requires(typeArgs != null);
      Contract.Requires(typeArgs.Count == TypeArgs.Count);
      Contract.Assume(typeCreator != null);  // can only call CreateType for a ValuetypeDecl with a type creator (this is up to the caller to ensure)
      return typeCreator(typeArgs);
    }
  }

  public class DatatypeCtor : Declaration, TypeParameter.ParentType
  {
    public readonly List<Formal> Formals;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Formals));
      Contract.Invariant(Destructors != null);
      Contract.Invariant(
        Destructors.Count == 0 || // this is until resolution
        Destructors.Count == Formals.Count);  // after resolution
    }

    // TODO: One could imagine having a precondition on datatype constructors
    public DatatypeDecl EnclosingDatatype;  // filled in during resolution
    public SpecialField QueryField;  // filled in during resolution
    public List<DatatypeDestructor> Destructors = new List<DatatypeDestructor>();  // contents filled in during resolution; includes both implicit (not mentionable in source) and explicit destructors

    public DatatypeCtor(IToken tok, string name, [Captured] List<Formal> formals, Attributes attributes)
      : base(tok, name, attributes, false) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(formals));
      this.Formals = formals;
    }

    public string FullName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        Contract.Assume(EnclosingDatatype != null);

        return "#" + EnclosingDatatype.FullName + "." + Name;
      }
    }
  }

  /// <summary>
  /// An ICodeContext is an ICallable or a NoContext.
  /// </summary>
  public interface ICodeContext
  {
    bool IsGhost { get; }
    List<TypeParameter> TypeArgs { get; }
    List<Formal> Ins { get; }
    ModuleDefinition EnclosingModule { get; }  // to be called only after signature-resolution is complete
    bool MustReverify { get; }
    string FullSanitizedName { get; }
    bool AllowsNontermination { get; }
  }

  public class CodeContextWrapper : ICodeContext {
    private readonly ICodeContext inner;
    private readonly bool isGhostContext;
    public CodeContextWrapper(ICodeContext inner, bool isGhostContext) {
      this.inner = inner;
      this.isGhostContext = isGhostContext;
    }

    public bool IsGhost => isGhostContext;
    public List<TypeParameter> TypeArgs => inner.TypeArgs;
    public List<Formal> Ins => inner.Ins;
    public ModuleDefinition EnclosingModule => inner.EnclosingModule;
    public bool MustReverify => inner.MustReverify;
    public string FullSanitizedName => inner.FullSanitizedName;
    public bool AllowsNontermination => inner.AllowsNontermination;

    public static ICodeContext Unwrap(ICodeContext codeContext) {
      while (codeContext is CodeContextWrapper ccw) {
        codeContext = ccw.inner;
      }
      return codeContext;
    }
  }

  /// <summary>
  /// An ICallable is a Function, Method, IteratorDecl, or (less fitting for the name ICallable) RedirectingTypeDecl or DatatypeDecl.
  /// </summary>
  public interface ICallable : ICodeContext
  {
    IToken Tok { get; }
    string WhatKind { get; }
    string NameRelativeToModule { get; }
    Specification<Expression> Decreases { get; }
    /// <summary>
    /// The InferredDecreases property says whether or not a process was attempted to provide a default decreases
    /// clause.  If such a process was attempted, even if the resulting decreases clause turned out to be empty,
    /// the property will get the value "true".  This is so that a useful error message can be provided.
    /// </summary>
    bool InferredDecreases { get; set; }
  }

  public class DontUseICallable : ICallable
  {
    public string WhatKind { get { throw new cce.UnreachableException(); } }
    public bool IsGhost { get { throw new cce.UnreachableException(); } }
    public List<TypeParameter> TypeArgs { get { throw new cce.UnreachableException(); } }
    public List<Formal> Ins { get { throw new cce.UnreachableException(); } }
    public ModuleDefinition EnclosingModule { get { throw new cce.UnreachableException(); } }
    public bool MustReverify { get { throw new cce.UnreachableException(); } }
    public string FullSanitizedName { get { throw new cce.UnreachableException(); } }
    public bool AllowsNontermination { get { throw new cce.UnreachableException(); } }
    public IToken Tok { get { throw new cce.UnreachableException(); } }
    public string NameRelativeToModule { get { throw new cce.UnreachableException(); } }
    public Specification<Expression> Decreases { get { throw new cce.UnreachableException(); } }
    public bool InferredDecreases {
      get { throw new cce.UnreachableException(); }
      set { throw new cce.UnreachableException(); }
    }
  }
  /// <summary>
  /// An IMethodCodeContext is a Method or IteratorDecl.
  /// </summary>
  public interface IMethodCodeContext : ICallable
  {
    List<Formal> Outs { get; }
    Specification<FrameExpression> Modifies { get; }
  }

  /// <summary>
  /// Applies when we are not inside an ICallable.  In particular, a NoContext is used to resolve the attributes of declarations with no other context.
  /// </summary>
  public class NoContext : ICodeContext
  {
    public readonly ModuleDefinition Module;
    public NoContext(ModuleDefinition module)
    {
      this.Module = module;
    }
    bool ICodeContext.IsGhost { get { return true; } }
    List<TypeParameter> ICodeContext.TypeArgs { get { return new List<TypeParameter>(); } }
    List<Formal> ICodeContext.Ins { get { return new List<Formal>(); } }
    Specification<Expression> Decreases { get { return new Specification<Expression>(null, null); } }
    ModuleDefinition ICodeContext.EnclosingModule { get { return Module; } }
    bool ICodeContext.MustReverify { get { Contract.Assume(false, "should not be called on NoContext"); throw new cce.UnreachableException(); } }
    public string FullSanitizedName { get { Contract.Assume(false, "should not be called on NoContext"); throw new cce.UnreachableException(); } }
    public bool AllowsNontermination { get { Contract.Assume(false, "should not be called on NoContext"); throw new cce.UnreachableException(); } }
  }

  public class IteratorDecl : ClassDecl, IMethodCodeContext
  {
    public override string WhatKind { get { return "iterator"; } }
    public readonly List<Formal> Ins;
    public readonly List<Formal> Outs;
    public readonly Specification<FrameExpression> Reads;
    public readonly Specification<FrameExpression> Modifies;
    public readonly Specification<Expression> Decreases;
    public readonly List<AttributedExpression> Requires;
    public readonly List<AttributedExpression> Ensures;
    public readonly List<AttributedExpression> YieldRequires;
    public readonly List<AttributedExpression> YieldEnsures;
    public readonly BlockStmt Body;
    public bool SignatureIsOmitted { get { return SignatureEllipsis != null; } }
    public readonly IToken SignatureEllipsis;
    public readonly List<Field> OutsFields;
    public readonly List<Field> OutsHistoryFields;  // these are the 'xs' variables
    public readonly List<Field> DecreasesFields;  // filled in during resolution
    public SpecialField Member_Modifies;  // filled in during resolution
    public SpecialField Member_Reads;  // filled in during resolution
    public SpecialField Member_New;  // filled in during resolution
    public Constructor Member_Init;  // created during registration phase of resolution; its specification is filled in during resolution
    public Predicate Member_Valid;  // created during registration phase of resolution; its specification is filled in during resolution
    public Method Member_MoveNext;  // created during registration phase of resolution; its specification is filled in during resolution
    public readonly LocalVariable YieldCountVariable;

    public IteratorDecl(IToken tok, string name, ModuleDefinition module, List<TypeParameter> typeArgs,
                        List<Formal> ins, List<Formal> outs,
                        Specification<FrameExpression> reads, Specification<FrameExpression> mod, Specification<Expression> decreases,
                        List<AttributedExpression> requires,
                        List<AttributedExpression> ensures,
                        List<AttributedExpression> yieldRequires,
                        List<AttributedExpression> yieldEnsures,
                        BlockStmt body, Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, module, typeArgs, new List<MemberDecl>(), attributes, signatureEllipsis != null, null)
    {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(typeArgs != null);
      Contract.Requires(ins != null);
      Contract.Requires(outs != null);
      Contract.Requires(reads != null);
      Contract.Requires(mod != null);
      Contract.Requires(decreases != null);
      Contract.Requires(requires != null);
      Contract.Requires(ensures != null);
      Contract.Requires(yieldRequires != null);
      Contract.Requires(yieldEnsures != null);
      Ins = ins;
      Outs = outs;
      Reads = reads;
      Modifies = mod;
      Decreases = decreases;
      Requires = requires;
      Ensures = ensures;
      YieldRequires = yieldRequires;
      YieldEnsures = yieldEnsures;
      Body = body;
      SignatureEllipsis = signatureEllipsis;

      OutsFields = new List<Field>();
      OutsHistoryFields = new List<Field>();
      DecreasesFields = new List<Field>();

      YieldCountVariable = new LocalVariable(tok, tok, "_yieldCount", new EverIncreasingType(), true);
      YieldCountVariable.type = YieldCountVariable.OptionalType;  // resolve YieldCountVariable here
    }

    /// <summary>
    /// Returns the non-null expressions of this declaration proper (that is, do not include the expressions of substatements).
    /// Does not include the generated class members.
    /// </summary>
    public virtual IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in Attributes.SubExpressions(Attributes)) {
          yield return e;
        }
        foreach (var e in Attributes.SubExpressions(Reads.Attributes)) {
          yield return e;
        }
        foreach (var e in Reads.Expressions) {
          yield return e.E;
        }
        foreach (var e in Attributes.SubExpressions(Modifies.Attributes)) {
          yield return e;
        }
        foreach (var e in Modifies.Expressions) {
          yield return e.E;
        }
        foreach (var e in Attributes.SubExpressions(Decreases.Attributes)) {
          yield return e;
        }
        foreach (var e in Decreases.Expressions) {
          yield return e;
        }
        foreach (var e in Requires) {
          yield return e.E;
        }
        foreach (var e in Ensures) {
          yield return e.E;
        }
        foreach (var e in YieldRequires) {
          yield return e.E;
        }
        foreach (var e in YieldEnsures) {
          yield return e.E;
        }
      }
    }

    /// <summary>
    /// This Dafny type exists only for the purpose of giving the yield-count variable a type, so
    /// that the type can be recognized during translation of Dafny into Boogie.  It represents
    /// an integer component in a "decreases" clause whose order is (\lambda x,y :: x GREATER y),
    /// not the usual (\lambda x,y :: x LESS y AND 0 ATMOST y).
    /// </summary>
    public class EverIncreasingType : BasicType
    {
      [Pure]
      public override string TypeName(ModuleDefinition context, bool parseAble) {
        Contract.Assert(parseAble == false);

        return "_increasingInt";
      }
      public override bool Equals(Type that, bool keepConstraints = false) {
        return that.NormalizeExpand(keepConstraints) is EverIncreasingType;
      }
    }

    bool ICodeContext.IsGhost { get { return false; } }
    List<TypeParameter> ICodeContext.TypeArgs { get { return this.TypeArgs; } }
    List<Formal> ICodeContext.Ins { get { return this.Ins; } }
    List<Formal> IMethodCodeContext.Outs { get { return this.Outs; } }
    Specification<FrameExpression> IMethodCodeContext.Modifies { get { return this.Modifies; } }
    IToken ICallable.Tok { get { return this.tok; } }
    string ICallable.NameRelativeToModule { get { return this.Name; } }
    Specification<Expression> ICallable.Decreases { get { return this.Decreases; } }
    bool _inferredDecr;
    bool ICallable.InferredDecreases {
      set { _inferredDecr = value; }
      get { return _inferredDecr; }
    }

    ModuleDefinition ICodeContext.EnclosingModule { get { return this.EnclosingModuleDefinition; } }
    bool ICodeContext.MustReverify { get { return false; } }
    public bool AllowsNontermination {
      get {
        return Contract.Exists(Decreases.Expressions, e => e is WildcardExpr);
      }
    }
  }

  public abstract class MemberDecl : Declaration {
    public abstract string WhatKind { get; }
    public readonly bool HasStaticKeyword;
    public virtual bool IsStatic {
      get {
        return HasStaticKeyword || (EnclosingClass is ClassDecl && ((ClassDecl)EnclosingClass).IsDefaultClass);
      }
    }
    protected readonly bool isGhost;
    public bool IsGhost { get { return isGhost; } }

    /// <summary>
    /// The term "instance independent" can be confusing. It means that the constant does not get its value in
    /// a constructor. (But the RHS of the const's declaration may mention "this".)
    /// </summary>
    public bool IsInstanceIndependentConstant => this is ConstantField cf && cf.Rhs != null;

    public TopLevelDecl EnclosingClass;  // filled in during resolution
    public MemberDecl RefinementBase;  // filled in during the pre-resolution refinement transformation; null if the member is new here
    public MemberDecl OverriddenMember;  // filled in during resolution; non-null if the member overrides a member in a parent trait
    public virtual bool IsOverrideThatAddsBody => OverriddenMember != null;

    /// <summary>
    /// Returns "true" if "this" is a (possibly transitive) override of "possiblyOverriddenMember".
    /// </summary>
    public bool Overrides(MemberDecl possiblyOverriddenMember) {
      Contract.Requires(possiblyOverriddenMember != null);
      for (var th = this; th != null; th = th.OverriddenMember) {
        if (th == possiblyOverriddenMember) {
          return true;
        }
      }
      return false;
    }

    public MemberDecl(IToken tok, string name, bool hasStaticKeyword, bool isGhost, Attributes attributes, bool isRefining)
      : base(tok, name, attributes, isRefining) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      HasStaticKeyword = hasStaticKeyword;
      this.isGhost = isGhost;
    }
    /// <summary>
    /// Returns className+"."+memberName.  Available only after resolution.
    /// </summary>
    public virtual string FullDafnyName {
      get {
        Contract.Requires(EnclosingClass != null);
        Contract.Ensures(Contract.Result<string>() != null);
        string n = EnclosingClass.FullDafnyName;
        return (n.Length == 0 ? n : (n + ".")) + Name;
      }
    }
    public virtual string FullName {
      get {
        Contract.Requires(EnclosingClass != null);
        Contract.Ensures(Contract.Result<string>() != null);

        return EnclosingClass.FullName + "." + Name;
      }
    }
    public virtual string FullSanitizedName {
      get {
        Contract.Requires(EnclosingClass != null);
        Contract.Ensures(Contract.Result<string>() != null);

        if (Name == "requires") {
          return Translator.Requires(((ArrowTypeDecl)EnclosingClass).Arity);
        } else if (Name == "reads") {
          return Translator.Reads(((ArrowTypeDecl)EnclosingClass).Arity);
        } else {
          return EnclosingClass.FullSanitizedName + "." + CompileName;
        }
      }
    }
    public virtual string FullSanitizedRefinementName {
      get {
        Contract.Requires(EnclosingClass != null);
        Contract.Ensures(Contract.Result<string>() != null);

        if (Name == "requires") {
          return Translator.Requires(((ArrowTypeDecl)EnclosingClass).Arity);
        } else if (Name == "reads") {
          return Translator.Reads(((ArrowTypeDecl)EnclosingClass).Arity);
        } else {
          return EnclosingClass.FullSanitizedRefinementName + "." + CompileName;
        }
      }
    }
    public virtual string FullNameInContext(ModuleDefinition context) {
      Contract.Requires(EnclosingClass != null);
      Contract.Ensures(Contract.Result<string>() != null);

      return EnclosingClass.FullNameInContext(context) + "." + Name;
    }
    public override string CompileName {
      get {
        var nm = base.CompileName;
        if (this.Name == EnclosingClass.Name) {
          nm = "_" + nm;
        }
        return nm;
      }
    }
    public virtual string FullCompileName {
      get {
        Contract.Requires(EnclosingClass != null);
        Contract.Ensures(Contract.Result<string>() != null);

        return EnclosingClass.FullCompileName + "." + Declaration.IdProtect(CompileName);
      }
    }
    public virtual IEnumerable<Expression> SubExpressions {
      get {
        yield break;
      }
    }
  }

  public class Field : MemberDecl {
    public override string WhatKind { get { return "field"; } }
    public readonly bool IsMutable;  // says whether or not the field can ever change values
    public readonly bool IsUserMutable;  // says whether or not code is allowed to assign to the field (IsUserMutable implies IsMutable)
    public readonly Type Type;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Type != null);
      Contract.Invariant(!IsUserMutable || IsMutable);  // IsUserMutable ==> IsMutable
    }

    public Field(IToken tok, string name, bool isGhost, Type type, Attributes attributes)
      : this(tok, name, false, isGhost, true, true, type, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
    }

    public Field(IToken tok, string name, bool hasStaticKeyword, bool isGhost, bool isMutable, bool isUserMutable, Type type, Attributes attributes)
      : base(tok, name, hasStaticKeyword, isGhost, attributes, false) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      Contract.Requires(!isUserMutable || isMutable);
      IsMutable = isMutable;
      IsUserMutable = isUserMutable;
      Type = type;
    }
  }

  public class SpecialFunction : Function, ICodeContext, ICallable
  {
    readonly ModuleDefinition Module;
    public SpecialFunction(IToken tok, string name, ModuleDefinition module, bool hasStaticKeyword, bool isGhost,
      List<TypeParameter> typeArgs, List<Formal> formals, Type resultType,
      List<AttributedExpression> req, List<FrameExpression> reads, List<AttributedExpression> ens, Specification<Expression> decreases,
      Expression body, Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, hasStaticKeyword, isGhost, typeArgs, formals, null, resultType, req, reads, ens, decreases, body, attributes, signatureEllipsis)
    {
      Module = module;
    }
    ModuleDefinition ICodeContext.EnclosingModule { get { return this.Module; } }
    string ICallable.NameRelativeToModule { get { return Name; } }
  }

  public class SpecialField : Field
  {
    public enum ID {
      UseIdParam,  // IdParam is a string
      ArrayLength,  // IdParam is null for .Length; IdParam is an int "x" for GetLength(x)
      ArrayLengthInt,  // same as ArrayLength, but produces int instead of BigInteger
      Floor,
      IsLimit,
      IsSucc,
      Offset,
      IsNat,
      Keys,
      Values,
      Items,
      Reads,
      Modifies,
      New,
    }
    public readonly ID SpecialId;
    public readonly object IdParam;
    public SpecialField(IToken tok, string name, ID specialId, object idParam, bool isGhost, bool isMutable, bool isUserMutable, Type type, Attributes attributes)
      : this(tok, name, specialId, idParam, false, isGhost, isMutable, isUserMutable, type, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(!isUserMutable || isMutable);
      Contract.Requires(type != null);
    }

    public SpecialField(IToken tok, string name, ID specialId, object idParam, bool hasStaticKeyword, bool isGhost, bool isMutable, bool isUserMutable, Type type, Attributes attributes)
      : base(tok, name, hasStaticKeyword, isGhost, isMutable, isUserMutable, type, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(!isUserMutable || isMutable);
      Contract.Requires(type != null);

      SpecialId = specialId;
      IdParam = idParam;
    }

    public override string FullName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return EnclosingClass != null ? EnclosingClass.FullName + "." + Name : Name;
      }
    }

    public override string FullSanitizedName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return EnclosingClass != null ? EnclosingClass.FullSanitizedName + "." + CompileName : CompileName;
      }
    }

    public override string FullSanitizedRefinementName {
      get{
        Contract.Ensures(Contract.Result<string>() != null);
        return EnclosingClass != null ? EnclosingClass.FullSanitizedRefinementName + "." + CompileName : CompileName;
      }
    }

    public override string FullNameInContext(ModuleDefinition context) {
      Contract.Ensures(Contract.Result<string>() != null);
      return EnclosingClass != null ? EnclosingClass.FullNameInContext(context) + "." + Name : Name;
    }

    public override string CompileName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return EnclosingClass != null ? base.CompileName : Name;
      }
    }

    public override string FullCompileName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        var cn = Declaration.IdProtect(CompileName);
        return EnclosingClass != null ? EnclosingClass.FullCompileName + "." + cn : cn;
      }
    }
  }

  public class DatatypeDestructor : SpecialField
  {
    public readonly List<DatatypeCtor> EnclosingCtors = new List<DatatypeCtor>();  // is always a nonempty list
    public readonly List<Formal> CorrespondingFormals = new List<Formal>();  // is always a nonempty list
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(EnclosingCtors != null);
      Contract.Invariant(CorrespondingFormals != null);
      Contract.Invariant(EnclosingCtors.Count > 0);
      Contract.Invariant(EnclosingCtors.Count == CorrespondingFormals.Count);
    }

    public DatatypeDestructor(IToken tok, DatatypeCtor enclosingCtor, Formal correspondingFormal, string name, string compiledName, bool isGhost, Type type, Attributes attributes)
      : base(tok, name, SpecialField.ID.UseIdParam, compiledName, isGhost, false, false, type, attributes)
    {
      Contract.Requires(tok != null);
      Contract.Requires(enclosingCtor != null);
      Contract.Requires(correspondingFormal != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      EnclosingCtors.Add(enclosingCtor);  // more enclosing constructors may be added later during resolution
      CorrespondingFormals.Add(correspondingFormal);  // more corresponding formals may be added later during resolution
    }

    /// <summary>
    /// To be called only by the resolver. Called to share this datatype destructor between multiple constructors
    /// of the same datatype.
    /// </summary>
    internal void AddAnotherEnclosingCtor(DatatypeCtor ctor, Formal formal) {
      Contract.Requires(ctor != null);
      Contract.Requires(formal != null);
      EnclosingCtors.Add(ctor);  // more enclosing constructors may be added later during resolution
      CorrespondingFormals.Add(formal);  // more corresponding formals may be added later during resolution
    }

    internal string EnclosingCtorNames(string grammaticalConjunction) {
      Contract.Requires(grammaticalConjunction != null);
      return PrintableCtorNameList(EnclosingCtors, grammaticalConjunction);
    }

    static internal string PrintableCtorNameList(List<DatatypeCtor> ctors, string grammaticalConjunction) {
      Contract.Requires(ctors != null);
      Contract.Requires(grammaticalConjunction != null);
      var n = ctors.Count;
      if (n == 1) {
        return string.Format("'{0}'", ctors[0].Name);
      } else if (n == 2) {
        return string.Format("'{0}' {1} '{2}'", ctors[0].Name, grammaticalConjunction, ctors[1].Name);
      } else {
        var s = "";
        for (int i = 0; i < n - 1; i++) {
          s += string.Format("'{0}', ", ctors[i].Name);
        }
        return s + string.Format("{0} '{1}'", grammaticalConjunction, ctors[n - 1].Name);
      }
    }
  }

  public class ConstantField : SpecialField, ICallable
  {
    public override string WhatKind { get { return "const field"; } }
    public readonly Expression Rhs;
    public ConstantField(IToken tok, string name, Expression/*?*/ rhs, bool hasStaticKeyword, bool isGhost, Type type, Attributes attributes)
      : base(tok, name, SpecialField.ID.UseIdParam, NonglobalVariable.CompilerizeName(name), hasStaticKeyword, isGhost, false, false, type, attributes)
    {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      this.Rhs = rhs;
    }

    public override bool CanBeRevealed() {
      return true;
    }

    //
    public new bool IsGhost { get { return this.isGhost; } }
    public List<TypeParameter> TypeArgs { get { return new List<TypeParameter>(); } }
    public List<Formal> Ins { get { return new List<Formal>(); } }
    public ModuleDefinition EnclosingModule { get { return this.EnclosingClass.EnclosingModuleDefinition; } }
    public bool MustReverify { get { return false; } }
    public bool AllowsNontermination { get { throw new cce.UnreachableException(); } }
    public IToken Tok { get { return tok; } }
    public string NameRelativeToModule {
      get {
        if (EnclosingClass is DefaultClassDecl) {
          return Name;
        } else {
          return EnclosingClass.Name + "." + Name;
        }
      }
    }
    public Specification<Expression> Decreases { get { throw new cce.UnreachableException(); } }
    public bool InferredDecreases
    {
      get { throw new cce.UnreachableException(); }
      set { throw new cce.UnreachableException(); }
    }
  }

  public class OpaqueTypeDecl : TopLevelDeclWithMembers, TypeParameter.ParentType, RevealableTypeDecl
  {
    public override string WhatKind { get { return "opaque type"; } }
    public override bool CanBeRevealed() { return true; }
    public readonly TypeParameter.TypeParameterCharacteristics Characteristics;
    public bool SupportsEquality {
      get { return Characteristics.EqualitySupport != TypeParameter.EqualitySupportValue.Unspecified; }
    }

    public OpaqueTypeDecl(IToken tok, string name, ModuleDefinition module, TypeParameter.TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs, List<MemberDecl> members, Attributes attributes, bool isRefining)
      : base(tok, name, module, typeArgs, members, attributes, isRefining) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(typeArgs != null);
      Characteristics = characteristics;
      this.NewSelfSynonym();
    }

    public TopLevelDecl AsTopLevelDecl {
      get { return this; }
    }
  }

  public interface RedirectingTypeDecl : ICallable
  {
    string Name { get; }

    IToken tok { get; }
    Attributes Attributes { get; }
    ModuleDefinition Module { get; }
    BoundVar/*?*/ Var { get; }
    Expression/*?*/ Constraint { get; }
    SubsetTypeDecl.WKind WitnessKind { get; }
    Expression/*?*/ Witness { get; }  // non-null iff WitnessKind is Compiled or Ghost
    FreshIdGenerator IdGenerator { get; }
  }

  public class NativeType
  {
    public readonly string Name;
    public readonly BigInteger LowerBound;
    public readonly BigInteger UpperBound;
    public readonly int Bitwidth;  // for unasigned types, this shows the number of bits in the type; else is 0
    public enum Selection { Byte, SByte, UShort, Short, UInt, Int, Number, ULong, Long }
    public readonly Selection Sel;
    public readonly DafnyOptions.CompilationTarget CompilationTargets;
    public NativeType(string Name, BigInteger LowerBound, BigInteger UpperBound, int bitwidth, Selection sel, DafnyOptions.CompilationTarget compilationTargets) {
      Contract.Requires(Name != null);
      Contract.Requires(0 <= bitwidth && (bitwidth == 0 || LowerBound == 0));
      this.Name = Name;
      this.LowerBound = LowerBound;
      this.UpperBound = UpperBound;
      this.Bitwidth = bitwidth;
      this.Sel = sel;
      this.CompilationTargets = compilationTargets;
    }
  }

  public static class RevealableTypeDeclHelper {
    private static Dictionary<TopLevelDecl, InternalTypeSynonymDecl> tsdMap = new Dictionary<TopLevelDecl, InternalTypeSynonymDecl>();

    public static void NewSelfSynonym(this RevealableTypeDecl rtd) {
      var d = rtd.AsTopLevelDecl;
      Contract.Assert(!tsdMap.ContainsKey(d));
      var thisType = UserDefinedType.FromTopLevelDecl(d.tok, d);
      var tsd = new InternalTypeSynonymDecl(d.tok, d.Name, TypeParameter.GetExplicitCharacteristics(d), d.TypeArgs, d.EnclosingModuleDefinition, thisType, d.Attributes);
      tsd.InheritVisibility(d, false);
      tsdMap.Add(d, tsd);
    }

    public static UserDefinedType SelfSynonym(this RevealableTypeDecl rtd, List<Type> args, Expression/*?*/ namePath = null) {
      Contract.Requires(args != null);
      Contract.Requires(namePath == null || namePath is NameSegment || namePath is ExprDotName);
      var d = rtd.AsTopLevelDecl;
      Contract.Assert(tsdMap.ContainsKey(d));
      var typeSynonym = tsdMap[d];
      Contract.Assert(typeSynonym.TypeArgs.Count == args.Count);
      return new UserDefinedType(typeSynonym.tok, typeSynonym.Name, typeSynonym, args, namePath);
    }

    public static InternalTypeSynonymDecl SelfSynonymDecl(this RevealableTypeDecl rtd) {
      var d = rtd.AsTopLevelDecl;
      Contract.Assert(tsdMap.ContainsKey(d));
      return tsdMap[d];
    }

    public static TopLevelDecl AccessibleDecl(this RevealableTypeDecl rtd, VisibilityScope scope) {
      var d = rtd.AsTopLevelDecl;
      if (d.IsRevealedInScope(scope)) {
        return d;
      } else {
        return rtd.SelfSynonymDecl();
      }
    }

    //Internal implementations are called before extensions, so this is safe
    public static bool IsRevealedInScope(this RevealableTypeDecl rtd, VisibilityScope scope) {
      var d = rtd.AsTopLevelDecl;
      return d.IsRevealedInScope(scope);
    }
  }

  public interface RevealableTypeDecl {
    TopLevelDecl AsTopLevelDecl {get; }
  }

  public class NewtypeDecl : TopLevelDeclWithMembers, RevealableTypeDecl, RedirectingTypeDecl
  {
    public override string WhatKind { get { return "newtype"; } }
    public override bool CanBeRevealed() { return true; }
    public readonly Type BaseType;
    public readonly BoundVar Var;  // can be null (if non-null, then object.ReferenceEquals(Var.Type, BaseType))
    public readonly Expression Constraint;  // is null iff Var is
    public readonly SubsetTypeDecl.WKind WitnessKind = SubsetTypeDecl.WKind.CompiledZero;
    public readonly Expression/*?*/ Witness;  // non-null iff WitnessKind is Compiled or Ghost
    public NativeType NativeType; // non-null for fixed-size representations (otherwise, use BigIntegers for integers)
    public NewtypeDecl(IToken tok, string name, ModuleDefinition module, Type baseType, List<MemberDecl> members, Attributes attributes, bool isRefining)
      : base(tok, name, module, new List<TypeParameter>(), members, attributes, isRefining) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(baseType != null);
      Contract.Requires(members != null);
      BaseType = baseType;
    }
    public NewtypeDecl(IToken tok, string name, ModuleDefinition module, BoundVar bv, Expression constraint, SubsetTypeDecl.WKind witnessKind, Expression witness, List<MemberDecl> members, Attributes attributes, bool isRefining)
      : base(tok, name, module, new List<TypeParameter>(), members, attributes, isRefining) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(bv != null && bv.Type != null);
      Contract.Requires((witnessKind == SubsetTypeDecl.WKind.Compiled || witnessKind == SubsetTypeDecl.WKind.Ghost) == (witness != null));
      Contract.Requires(members != null);
      BaseType = bv.Type;
      Var = bv;
      Constraint = constraint;
      Witness = witness;
      WitnessKind = witnessKind;
      this.NewSelfSynonym();
    }

    TopLevelDecl RevealableTypeDecl.AsTopLevelDecl { get { return this; } }
    public TypeParameter.EqualitySupportValue EqualitySupport {
      get {
        if (this.BaseType.SupportsEquality) {
          return TypeParameter.EqualitySupportValue.Required;
        } else {
          return TypeParameter.EqualitySupportValue.Unspecified;
        }
      }
    }

    string RedirectingTypeDecl.Name { get { return Name; } }
    IToken RedirectingTypeDecl.tok { get { return tok; } }
    Attributes RedirectingTypeDecl.Attributes { get { return Attributes; } }
    ModuleDefinition RedirectingTypeDecl.Module { get { return EnclosingModuleDefinition; } }
    BoundVar RedirectingTypeDecl.Var { get { return Var; } }
    Expression RedirectingTypeDecl.Constraint { get { return Constraint; } }
    SubsetTypeDecl.WKind RedirectingTypeDecl.WitnessKind { get { return WitnessKind; } }
    Expression RedirectingTypeDecl.Witness { get { return Witness; } }
    FreshIdGenerator RedirectingTypeDecl.IdGenerator { get { return IdGenerator; } }

    bool ICodeContext.IsGhost {
      get { throw new NotSupportedException(); }  // if .IsGhost is needed, the object should always be wrapped in an CodeContextWrapper
    }
    List<TypeParameter> ICodeContext.TypeArgs { get { return new List<TypeParameter>(); } }
    List<Formal> ICodeContext.Ins { get { return new List<Formal>(); } }
    ModuleDefinition ICodeContext.EnclosingModule { get { return EnclosingModuleDefinition; } }
    bool ICodeContext.MustReverify { get { return false; } }
    bool ICodeContext.AllowsNontermination { get { return false; } }
    IToken ICallable.Tok { get { return tok; } }
    string ICallable.NameRelativeToModule { get { return Name; } }
    Specification<Expression> ICallable.Decreases {
      get {
        // The resolver checks that a NewtypeDecl sits in its own SSC in the call graph.  Therefore,
        // the question of what its Decreases clause is should never arise.
        throw new cce.UnreachableException();
      }
    }
    bool ICallable.InferredDecreases {
      get { throw new cce.UnreachableException(); }  // see comment above about ICallable.Decreases
      set { throw new cce.UnreachableException(); }  // see comment above about ICallable.Decreases
    }
  }

  public abstract class TypeSynonymDeclBase : TopLevelDecl, RedirectingTypeDecl
  {
    public override string WhatKind { get { return "type synonym"; } }
    public TypeParameter.TypeParameterCharacteristics Characteristics;  // the resolver may change the .EqualitySupport component of this value from Unspecified to InferredRequired (for some signatures that may immediately imply that equality support is required)
    public bool SupportsEquality {
      get { return Characteristics.EqualitySupport != TypeParameter.EqualitySupportValue.Unspecified; }
    }
    public readonly Type Rhs;
    public TypeSynonymDeclBase(IToken tok, string name, TypeParameter.TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs, ModuleDefinition module, Type rhs, Attributes attributes)
      : base(tok, name, module, typeArgs, attributes, false) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(typeArgs != null);
      Contract.Requires(module != null);
      Contract.Requires(rhs != null);
      Characteristics = characteristics;
      Rhs = rhs;
    }
    /// <summary>
    /// Return .Rhs instantiated with "typeArgs", but only look at the part of .Rhs that is in scope.
    /// </summary>
    public Type RhsWithArgument(List<Type> typeArgs) {
      Contract.Requires(typeArgs != null);
      Contract.Requires(typeArgs.Count == TypeArgs.Count);
      var scope = Type.GetScope();
      var rtd = Rhs.AsRevealableType;
      if (rtd != null) {
        Contract.Assume(rtd.AsTopLevelDecl.IsVisibleInScope(scope));
        if (!rtd.IsRevealedInScope(scope)) {
          // type is actually hidden in this scope
          return rtd.SelfSynonym(typeArgs);
        }
      }
      return RhsWithArgumentIgnoringScope(typeArgs);
    }
    /// <summary>
    /// Returns the declared .Rhs but with formal type arguments replaced by the given actuals.
    /// </summary>
    public Type RhsWithArgumentIgnoringScope(List<Type> typeArgs) {
      Contract.Requires(typeArgs != null);
      Contract.Requires(typeArgs.Count == TypeArgs.Count);
      // Instantiate with the actual type arguments
      if (typeArgs.Count == 0) {
        // this optimization seems worthwhile
        return Rhs;
      } else {
        var subst = Resolver.TypeSubstitutionMap(TypeArgs, typeArgs);
        return Resolver.SubstType(Rhs, subst);
      }
    }

    string RedirectingTypeDecl.Name { get { return Name; } }
    IToken RedirectingTypeDecl.tok { get { return tok; } }
    Attributes RedirectingTypeDecl.Attributes { get { return Attributes; } }
    ModuleDefinition RedirectingTypeDecl.Module { get { return EnclosingModuleDefinition; } }
    BoundVar RedirectingTypeDecl.Var { get { return null; } }
    Expression RedirectingTypeDecl.Constraint { get { return null; } }
    SubsetTypeDecl.WKind RedirectingTypeDecl.WitnessKind { get { return SubsetTypeDecl.WKind.CompiledZero; } }
    Expression RedirectingTypeDecl.Witness { get { return null; } }
    FreshIdGenerator RedirectingTypeDecl.IdGenerator { get { return IdGenerator; } }

    bool ICodeContext.IsGhost {
      get { throw new NotSupportedException(); }  // if .IsGhost is needed, the object should always be wrapped in an CodeContextWrapper
    }
    List<TypeParameter> ICodeContext.TypeArgs { get { return TypeArgs; } }
    List<Formal> ICodeContext.Ins { get { return new List<Formal>(); } }
    ModuleDefinition ICodeContext.EnclosingModule { get { return EnclosingModuleDefinition; } }
    bool ICodeContext.MustReverify {get { return false; } }
    bool ICodeContext.AllowsNontermination { get { return false; } }
    IToken ICallable.Tok { get { return tok; } }
    string ICallable.NameRelativeToModule { get { return Name; } }
    Specification<Expression> ICallable.Decreases {
      get {
        // The resolver checks that a NewtypeDecl sits in its own SSC in the call graph.  Therefore,
        // the question of what its Decreases clause is should never arise.
        throw new cce.UnreachableException();
      }
    }
    bool ICallable.InferredDecreases {
      get { throw new cce.UnreachableException(); }  // see comment above about ICallable.Decreases
      set { throw new cce.UnreachableException(); }  // see comment above about ICallable.Decreases
    }
    public override bool CanBeRevealed() {
      return true;
    }
  }

  public class TypeSynonymDecl : TypeSynonymDeclBase, RedirectingTypeDecl, RevealableTypeDecl {
    public TypeSynonymDecl(IToken tok, string name, TypeParameter.TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs, ModuleDefinition module, Type rhs, Attributes attributes)
      : base(tok, name, characteristics, typeArgs, module, rhs, attributes) {
        this.NewSelfSynonym();
    }
    TopLevelDecl RevealableTypeDecl.AsTopLevelDecl { get { return this; } }
  }

  public class InternalTypeSynonymDecl : TypeSynonymDeclBase, RedirectingTypeDecl {
    public InternalTypeSynonymDecl(IToken tok, string name, TypeParameter.TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs, ModuleDefinition module, Type rhs, Attributes attributes)
      : base(tok, name, characteristics, typeArgs, module, rhs, attributes) {
    }
  }


  public class SubsetTypeDecl : TypeSynonymDecl, RedirectingTypeDecl
  {
    public override string WhatKind { get { return "subset type"; } }
    public readonly BoundVar Var;
    public readonly Expression Constraint;
    public enum WKind { CompiledZero, Compiled, Ghost, OptOut, Special }
    public readonly SubsetTypeDecl.WKind WitnessKind;
    public readonly Expression/*?*/ Witness;  // non-null iff WitnessKind is Compiled or Ghost
    public SubsetTypeDecl(IToken tok, string name, TypeParameter.TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs, ModuleDefinition module,
      BoundVar id, Expression constraint, WKind witnessKind, Expression witness,
      Attributes attributes)
      : base(tok, name, characteristics, typeArgs, module, id.Type, attributes) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(typeArgs != null);
      Contract.Requires(module != null);
      Contract.Requires(id != null && id.Type != null);
      Contract.Requires(constraint != null);
      Contract.Requires((witnessKind == WKind.Compiled || witnessKind == WKind.Ghost) == (witness != null));
      Var = id;
      Constraint = constraint;
      Witness = witness;
      WitnessKind = witnessKind;
    }
    BoundVar RedirectingTypeDecl.Var { get { return Var; } }
    Expression RedirectingTypeDecl.Constraint { get { return Constraint; } }
    WKind RedirectingTypeDecl.WitnessKind { get { return WitnessKind; } }
    Expression RedirectingTypeDecl.Witness { get { return Witness; } }

    public override List<Type> ParentTypes(List<Type> typeArgs) {
      return new List<Type>{ RhsWithArgument(typeArgs) };
    }
  }

  public class NonNullTypeDecl : SubsetTypeDecl
  {
    public override string WhatKind { get { return "non-null type"; } }
    public readonly ClassDecl Class;
    /// <summary>
    /// The public constructor is NonNullTypeDecl(ClassDecl cl). The rest is pretty crazy: There are stages of "this"-constructor calls
    /// in order to build values that depend on previously computed parameters.
    /// </summary>
    public NonNullTypeDecl(ClassDecl cl)
      : this(cl, cl.TypeArgs.ConvertAll(tp => new TypeParameter(tp.tok, tp.Name, tp.VarianceSyntax, tp.Characteristics)))
    {
      Contract.Requires(cl != null);
    }

    private NonNullTypeDecl(ClassDecl cl, List<TypeParameter> tps)
      : this(cl, tps,
      new BoundVar(cl.tok, "c", new UserDefinedType(cl.tok, cl.Name + "?", tps.Count == 0 ? null : tps.ConvertAll(tp => (Type)new UserDefinedType(tp)))))
    {
      Contract.Requires(cl != null);
      Contract.Requires(tps != null);
    }

    private NonNullTypeDecl(ClassDecl cl, List<TypeParameter> tps, BoundVar id)
      : base(cl.tok, cl.Name, new TypeParameter.TypeParameterCharacteristics(), tps, cl.EnclosingModuleDefinition, id,
      new BinaryExpr(cl.tok, BinaryExpr.Opcode.Neq, new IdentifierExpr(cl.tok, id), new LiteralExpr(cl.tok)),
      SubsetTypeDecl.WKind.Special, null, BuiltIns.AxiomAttribute())
    {
      Contract.Requires(cl != null);
      Contract.Requires(tps != null);
      Contract.Requires(id != null);
      Class = cl;
    }

    public override List<Type> ParentTypes(List<Type> typeArgs) {
      List<Type> result = new List<Type>(base.ParentTypes(typeArgs));

      foreach (var rhsParentType in Class.ParentTypes(typeArgs)) {
        var rhsParentUdt = (UserDefinedType)rhsParentType; // all parent types of .Class are expected to be possibly-null class types
        Contract.Assert(rhsParentUdt.ResolvedClass is ClassDecl);
        result.Add(UserDefinedType.CreateNonNullType(rhsParentUdt));
      }

      return result;
    }
  }

  [ContractClass(typeof(IVariableContracts))]
  public interface IVariable {
    string Name {
      get;
    }
    string DisplayName {  // what the user thinks he wrote
      get;
    }
    string UniqueName {
      get;
    }
    bool HasBeenAssignedUniqueName {  // unique names are not assigned until the Translator; if you don't already know if that stage has run, this boolean method will tell you
      get;
    }
    string AssignUniqueName(FreshIdGenerator generator);
    string CompileName {
      get;
    }
    Type Type {
      get;
    }
    Type OptionalType {
      get;
    }
    bool IsMutable {
      get;
    }
    bool IsGhost {
      get;
    }
    void MakeGhost();
    IToken Tok {
      get;
    }
  }
  [ContractClassFor(typeof(IVariable))]
  public abstract class IVariableContracts : IVariable {
    public string Name {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public string DisplayName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public string UniqueName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public bool HasBeenAssignedUniqueName {
      get {
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public string CompileName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public Type Type {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public Type OptionalType {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public bool IsMutable {
      get {
        throw new NotImplementedException();
      }
    }
    public bool IsGhost {
      get {
        throw new NotImplementedException();
      }
    }
    public void MakeGhost() {
      throw new NotImplementedException();
    }
    public IToken Tok {
      get {
        Contract.Ensures(Contract.Result<IToken>() != null);
        throw new NotImplementedException();
      }
    }
    public string AssignUniqueName(FreshIdGenerator generator)
    {
      Contract.Ensures(Contract.Result<string>() != null);
      throw new NotImplementedException();
    }
  }

  public abstract class NonglobalVariable : IVariable {
    public readonly IToken tok;
    readonly string name;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(tok != null);
      Contract.Invariant(name != null);
      Contract.Invariant(type != null);
    }

    public string Name {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return name;
      }
    }
    public string DisplayName {
      get { return LocalVariable.DisplayNameHelper(this); }
    }
    private string uniqueName;
    public string UniqueName {
      get {
        return uniqueName;
      }
    }
    public bool HasBeenAssignedUniqueName {
      get {
        return uniqueName != null;
      }
    }
    public string AssignUniqueName(FreshIdGenerator generator)
    {
      if (uniqueName == null)
      {
        uniqueName = generator.FreshId(Name + "#");
        compileName = string.Format("_{0}_{1}", Compiler.FreshId(), CompilerizeName(name));
      }
      return UniqueName;
    }
    static char[] specialChars = new char[] { '\'', '_', '?', '\\', '#' };
    public static string CompilerizeName(string nm) {
      if ('0' <= nm[0] && nm[0] <= '9') {
        // the identifier is one that consists of just digits
        return "_" + nm;
      }
      string name = null;
      int i = 0;
      while (true) {
        int j = nm.IndexOfAny(specialChars, i);
        if (j == -1) {
          if (i == 0) {
            return nm;  // this is the common case
          } else {
            return name + nm.Substring(i);
          }
        } else {
          string nxt = nm.Substring(i, j - i);
          name = name == null ? nxt : name + nxt;
          switch (nm[j]) {
            case '\'': name += "_k"; break;
            case '_': name += "__"; break;
            case '?': name += "_q"; break;
            case '\\': name += "_b"; break;
            case '#': name += "_h"; break;
            default:
              Contract.Assume(false);  // unexpected character
              break;
          }
          i = j + 1;
          if (i == nm.Length) {
            return name;
          }
        }
      }
    }
    protected string compileName;
    public virtual string CompileName {
      get {
        if (compileName == null)
        {
          compileName = string.Format("_{0}_{1}", Compiler.FreshId(), CompilerizeName(name));
        }
        return compileName;
      }
    }
    Type type;
    public Type SyntacticType { get { return type; } }  // returns the non-normalized type
    public Type Type {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);
        return type.Normalize();
      }
    }
    Type IVariable.OptionalType {
      get { return Type; }  // same as Type for NonglobalVariable
    }
    public abstract bool IsMutable {
      get;
    }
    bool isGhost;  // readonly after resolution
    public bool IsGhost {
      get {
        return isGhost;
      }
      set {
        isGhost = value;
      }
    }
    public void MakeGhost() {
      IsGhost = true;
    }
    public IToken Tok {
      get {
        return tok;
      }
    }

    public NonglobalVariable(IToken tok, string name, Type type, bool isGhost) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      this.tok = tok;
      this.name = name;
      this.type = type;
      this.isGhost = isGhost;
    }
  }

  public class Formal : NonglobalVariable {
    public readonly bool InParam;  // true to in-parameter, false for out-parameter
    public override bool IsMutable {
      get {
        return !InParam;
      }
    }
    public readonly bool IsOld;
    public readonly Expression DefaultValue;
    public readonly bool IsNameOnly;

    public Formal(IToken tok, string name, Type type, bool inParam, bool isGhost, Expression defaultValue, bool isOld = false, bool isNameOnly = false)
      : base(tok, name, type, isGhost) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      Contract.Requires(inParam || defaultValue == null);
      Contract.Requires(!isNameOnly || (inParam && !name.StartsWith("#")));
      InParam = inParam;
      IsOld = isOld;
      DefaultValue = defaultValue;
      IsNameOnly = isNameOnly;
    }

    public bool HasName {
      get {
        return !Name.StartsWith("#");
      }
    }
    public override string CompileName {
      get {
        if (compileName == null) {
          compileName = CompilerizeName(Name);
        }
        return compileName;
      }
    }
  }

  /// <summary>
  /// An ImplicitFormal is a parameter that is declared implicitly, in particular the "_k" depth parameter
  /// of each extreme lemma (for use in the extreme-method body only, not the specification).
  /// </summary>
  public class ImplicitFormal : Formal {
    public ImplicitFormal(IToken tok, string name, Type type, bool inParam, bool isGhost)
      : base(tok, name, type, inParam, isGhost, null) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
    }
  }

  /// <summary>
  /// ThisSurrogate represents the implicit parameter "this". It is used to allow more uniform handling of
  /// parameters. A pointer value of a ThisSurrogate object is not important, only the fact that it is
  /// a ThisSurrogate is. ThisSurrogate objects are only used in specially marked places in the Dafny
  /// implementation.
  /// </summary>
  public class ThisSurrogate : ImplicitFormal {
    public ThisSurrogate(IToken tok, Type type)
      : base(tok, "this", type, true, false) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
    }
  }

  [DebuggerDisplay("Bound<{name}>")]
  public class BoundVar : NonglobalVariable {
    public override bool IsMutable {
      get {
        return false;
      }
    }

    public BoundVar(IToken tok, string name, Type type)
      : base(tok, name, type, false) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
    }
  }

  public class ActualBinding {
    public readonly IToken /*?*/ FormalParameterName;
    public readonly Expression Actual;
    public readonly bool IsGhost;

    public ActualBinding(IToken /*?*/ formalParameterName, Expression actual, bool isGhost = false) {
      Contract.Requires(actual != null);
      FormalParameterName = formalParameterName;
      Actual = actual;
      IsGhost = isGhost;
    }
  }

  public class ActualBindings {
    public readonly List<ActualBinding> ArgumentBindings;

    public ActualBindings(List<ActualBinding> argumentBindings) {
      Contract.Requires(argumentBindings != null);
      ArgumentBindings = argumentBindings;
    }

    public ActualBindings(List<Expression> actuals) {
      Contract.Requires(actuals != null);
      ArgumentBindings = actuals.ConvertAll(actual => new ActualBinding(null, actual));
    }

    private List<Expression> arguments; // set by ResolveActualParameters during resolution

    public bool WasResolved => arguments != null;

    public List<Expression> Arguments {
      get {
        Contract.Requires(WasResolved);
        return arguments;
      }
    }

    public void AcceptArgumentExpressionsAsExactParameterList(List<Expression> args = null) {
      Contract.Requires(!WasResolved); // this operation should be done at most once
      Contract.Assume(ArgumentBindings.TrueForAll(arg => arg.Actual.WasResolved()));
      arguments = args ?? ArgumentBindings.ConvertAll(binding => binding.Actual);
    }
  }

  public class Function : MemberDecl, TypeParameter.ParentType, ICallable {
    public override string WhatKind { get { return "function"; } }
    public override bool CanBeRevealed() { return true; }
    public bool IsRecursive;  // filled in during resolution
    public TailStatus TailRecursion = TailStatus.NotTailRecursive;  // filled in during resolution; NotTailRecursive = no tail recursion; TriviallyTailRecursive is never used here
    public bool IsTailRecursive => TailRecursion != TailStatus.NotTailRecursive;
    public bool IsAccumulatorTailRecursive => IsTailRecursive && TailRecursion != Function.TailStatus.TailRecursive;
    public bool IsFueled;  // filled in during resolution if anyone tries to adjust this function's fuel
    public readonly List<TypeParameter> TypeArgs;
    public readonly List<Formal> Formals;
    public readonly Formal Result;
    public readonly Type ResultType;
    public readonly List<AttributedExpression> Req;
    public readonly List<FrameExpression> Reads;
    public readonly List<AttributedExpression> Ens;
    public readonly Specification<Expression> Decreases;
    public Expression Body;  // an extended expression; Body is readonly after construction, except for any kind of rewrite that may take place around the time of resolution
    public bool SignatureIsOmitted { get { return SignatureEllipsis != null; } }  // is "false" for all Function objects that survive into resolution
    public readonly IToken SignatureEllipsis;
    public bool IsBuiltin;
    public Function OverriddenFunction;
    public Function Original => OverriddenFunction == null ? this : OverriddenFunction.Original;
    public override bool IsOverrideThatAddsBody => base.IsOverrideThatAddsBody && Body != null;

    public bool containsQuantifier;
    public bool ContainsQuantifier {
      set { containsQuantifier = value; }
      get { return containsQuantifier;  }
    }

    public enum TailStatus
    {
      TriviallyTailRecursive, // contains no recursive calls (in non-ghost expressions)
      TailRecursive, // all recursive calls (in non-ghost expressions) are tail calls
      NotTailRecursive, // contains some non-ghost recursive call outside of a tail-call position
      // E + F or F + E, where E has no tail call and F is a tail call
      Accumulate_Add,
      AccumulateRight_Sub,
      Accumulate_Mul,
      Accumulate_SetUnion,
      AccumulateRight_SetDifference,
      Accumulate_MultiSetUnion,
      AccumulateRight_MultiSetDifference,
      AccumulateLeft_Concat,
      AccumulateRight_Concat,
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var formal in Formals.Where(f => f.DefaultValue != null)) {
          yield return formal.DefaultValue;
        }
        foreach (var e in Req) {
          yield return e.E;
        }
        foreach (var e in Reads) {
          yield return e.E;
        }
        foreach (var e in Ens) {
          yield return e.E;
        }
        foreach (var e in Decreases.Expressions) {
          yield return e;
        }
        if (Body != null) {
          yield return Body;
        }
      }
    }

    public Type GetMemberType(ArrowTypeDecl atd) {
      Contract.Requires(atd != null);
      Contract.Requires(atd.Arity == Formals.Count);

      // Note, the following returned type can contain type parameters from the function and its enclosing class
      return new ArrowType(tok, atd, Formals.ConvertAll(f => f.Type), ResultType);
    }

    public bool AllowsNontermination {
      get {
        return Contract.Exists(Decreases.Expressions, e => e is WildcardExpr);
      }
    }

    /// <summary>
    /// The "AllCalls" field is used for non-ExtremePredicate, non-PrefixPredicate functions only (so its value should not be relied upon for ExtremePredicate and PrefixPredicate functions).
    /// It records all function calls made by the Function, including calls made in the body as well as in the specification.
    /// The field is filled in during resolution (and used toward the end of resolution, to attach a helpful "decreases" prefix to functions in clusters
    /// with co-recursive calls.
    /// </summary>
    public readonly List<FunctionCallExpr> AllCalls = new List<FunctionCallExpr>();
    public enum CoCallClusterInvolvement {
      None,  // the SCC containing the function does not involve any co-recursive calls
      IsMutuallyRecursiveTarget,  // the SCC contains co-recursive calls, and this function is the target of some non-self recursive call
      CoRecursiveTargetAllTheWay,  // the SCC contains co-recursive calls, and this function is the target only of self-recursive calls and co-recursive calls
    }
    public CoCallClusterInvolvement CoClusterTarget = CoCallClusterInvolvement.None;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(TypeArgs));
      Contract.Invariant(cce.NonNullElements(Formals));
      Contract.Invariant(ResultType != null);
      Contract.Invariant(cce.NonNullElements(Req));
      Contract.Invariant(cce.NonNullElements(Reads));
      Contract.Invariant(cce.NonNullElements(Ens));
      Contract.Invariant(Decreases != null);
    }

    /// <summary>
    /// Note, functions are "ghost" by default; a non-ghost function is called a "function method".
    /// </summary>
    public Function(IToken tok, string name, bool hasStaticKeyword, bool isGhost,
      List<TypeParameter> typeArgs, List<Formal> formals, Formal result, Type resultType,
      List<AttributedExpression> req, List<FrameExpression> reads, List<AttributedExpression> ens, Specification<Expression> decreases,
      Expression body, Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, hasStaticKeyword, isGhost, attributes, signatureEllipsis != null) {

      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(formals));
      Contract.Requires(resultType != null);
      Contract.Requires(cce.NonNullElements(req));
      Contract.Requires(cce.NonNullElements(reads));
      Contract.Requires(cce.NonNullElements(ens));
      Contract.Requires(decreases != null);
      this.IsFueled = false;  // Defaults to false.  Only set to true if someone mentions this function in a fuel annotation
      this.TypeArgs = typeArgs;
      this.Formals = formals;
      this.Result = result;
      this.ResultType = result != null ? result.Type : resultType;
      this.Req = req;
      this.Reads = reads;
      this.Ens = ens;
      this.Decreases = decreases;
      this.Body = body;
      this.SignatureEllipsis = signatureEllipsis;

      if (attributes != null) {
        List<Expression> args = Attributes.FindExpressions(attributes, "fuel");
        if (args != null) {
          if (args.Count == 1) {
            LiteralExpr literal = args[0] as LiteralExpr;
            if (literal != null && literal.Value is BigInteger) {
              this.IsFueled = true;
            }
          } else if (args.Count == 2) {
            LiteralExpr literalLow = args[0] as LiteralExpr;
            LiteralExpr literalHigh = args[1] as LiteralExpr;

            if (literalLow != null && literalLow.Value is BigInteger && literalHigh != null && literalHigh.Value is BigInteger) {
              this.IsFueled = true;
            }
          }
        }
      }
    }

    bool ICodeContext.IsGhost { get { return this.IsGhost; } }
    List<TypeParameter> ICodeContext.TypeArgs { get { return this.TypeArgs; } }
    List<Formal> ICodeContext.Ins { get { return this.Formals; } }
    IToken ICallable.Tok { get { return this.tok; } }
    string ICallable.NameRelativeToModule {
      get {
        if (EnclosingClass is DefaultClassDecl) {
          return Name;
        } else {
          return EnclosingClass.Name + "." + Name;
        }
      }
    }
    Specification<Expression> ICallable.Decreases { get { return this.Decreases; } }
    bool _inferredDecr;
    bool ICallable.InferredDecreases {
      set { _inferredDecr = value; }
      get { return _inferredDecr; }
    }
    ModuleDefinition ICodeContext.EnclosingModule { get { return this.EnclosingClass.EnclosingModuleDefinition; } }
    bool ICodeContext.MustReverify { get { return false; } }

    [Pure]
    public bool IsFuelAware() { return IsRecursive || IsFueled || (OverriddenFunction != null && OverriddenFunction.IsFuelAware()); }
    public virtual bool ReadsHeap { get { return Reads.Count != 0; } }
  }

  public class Predicate : Function
  {
    public override string WhatKind { get { return "predicate"; } }
    public enum BodyOriginKind
    {
      OriginalOrInherited,  // this predicate definition is new (and the predicate may or may not have a body), or the predicate's body (whether or not it exists) is being inherited unmodified (from the previous refinement--it may be that the inherited body was itself an extension, for example)
      DelayedDefinition,  // this predicate declaration provides, for the first time, a body--the declaration refines a previously declared predicate, but the previous one had no body
      Extension  // this predicate extends the definition of a predicate with a body in a module being refined
    }
    public readonly BodyOriginKind BodyOrigin;
    public Predicate(IToken tok, string name, bool hasStaticKeyword, bool isGhost,
      List<TypeParameter> typeArgs, List<Formal> formals,
      List<AttributedExpression> req, List<FrameExpression> reads, List<AttributedExpression> ens, Specification<Expression> decreases,
      Expression body, BodyOriginKind bodyOrigin, Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, hasStaticKeyword, isGhost, typeArgs, formals, null, Type.Bool, req, reads, ens, decreases, body, attributes, signatureEllipsis) {
      Contract.Requires(bodyOrigin == Predicate.BodyOriginKind.OriginalOrInherited || body != null);
      BodyOrigin = bodyOrigin;
    }
  }

  /// <summary>
  /// An PrefixPredicate is the inductive unrolling P# implicitly declared for every extreme predicate P.
  /// </summary>
  public class PrefixPredicate : Function
  {
    public override string WhatKind { get { return "prefix predicate"; } }
    public readonly Formal K;
    public readonly ExtremePredicate ExtremePred;
    public PrefixPredicate(IToken tok, string name, bool hasStaticKeyword,
      List<TypeParameter> typeArgs, Formal k, List<Formal> formals,
      List<AttributedExpression> req, List<FrameExpression> reads, List<AttributedExpression> ens, Specification<Expression> decreases,
      Expression body, Attributes attributes, ExtremePredicate extremePred)
      : base(tok, name, hasStaticKeyword, true, typeArgs, formals, null, Type.Bool, req, reads, ens, decreases, body, attributes, null) {
      Contract.Requires(k != null);
      Contract.Requires(extremePred != null);
      Contract.Requires(formals != null && 1 <= formals.Count && formals[0] == k);
      K = k;
      ExtremePred = extremePred;
    }
  }

  public abstract class ExtremePredicate : Function
  {
    public enum KType { Unspecified, Nat, ORDINAL }
    public readonly KType TypeOfK;
    public bool KNat {
      get {
        return TypeOfK == KType.Nat;
      }
    }
    public readonly List<FunctionCallExpr> Uses = new List<FunctionCallExpr>();  // filled in during resolution, used by verifier
    public PrefixPredicate PrefixPredicate;  // filled in during resolution (name registration)

    public ExtremePredicate(IToken tok, string name, bool hasStaticKeyword, KType typeOfK,
      List<TypeParameter> typeArgs, List<Formal> formals,
      List<AttributedExpression> req, List<FrameExpression> reads, List<AttributedExpression> ens,
      Expression body, Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, hasStaticKeyword, true, typeArgs, formals, null, Type.Bool,
             req, reads, ens, new Specification<Expression>(new List<Expression>(), null), body, attributes, signatureEllipsis) {
      TypeOfK = typeOfK;
    }

    /// <summary>
    /// For the given call P(s), return P#[depth](s).  The resulting expression shares some of the subexpressions
    /// with 'fexp' (that is, what is returned is not necessarily a clone).
    /// </summary>
    public FunctionCallExpr CreatePrefixPredicateCall(FunctionCallExpr fexp, Expression depth) {
      Contract.Requires(fexp != null);
      Contract.Requires(fexp.Function == this);
      Contract.Requires(depth != null);
      Contract.Ensures(Contract.Result<FunctionCallExpr>() != null);

      var args = new List<Expression>() { depth };
      args.AddRange(fexp.Args);
      var prefixPredCall = new FunctionCallExpr(fexp.tok, this.PrefixPredicate.Name, fexp.Receiver, fexp.OpenParen, args);
      prefixPredCall.Function = this.PrefixPredicate;  // resolve here
      prefixPredCall.TypeApplication_AtEnclosingClass = fexp.TypeApplication_AtEnclosingClass;  // resolve here
      prefixPredCall.TypeApplication_JustFunction = fexp.TypeApplication_JustFunction;  // resolve here
      prefixPredCall.Type = fexp.Type;  // resolve here
      prefixPredCall.CoCall = fexp.CoCall;  // resolve here
      return prefixPredCall;
    }
  }

  public class LeastPredicate : ExtremePredicate
  {
    public override string WhatKind { get { return "least predicate"; } }
    public LeastPredicate(IToken tok, string name, bool hasStaticKeyword, KType typeOfK,
      List<TypeParameter> typeArgs, List<Formal> formals,
      List<AttributedExpression> req, List<FrameExpression> reads, List<AttributedExpression> ens,
      Expression body, Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, hasStaticKeyword, typeOfK, typeArgs, formals,
             req, reads, ens, body, attributes, signatureEllipsis) {
    }
  }

  public class GreatestPredicate : ExtremePredicate
  {
    public override string WhatKind { get { return "greatest predicate"; } }
    public GreatestPredicate(IToken tok, string name, bool hasStaticKeyword, KType typeOfK,
      List<TypeParameter> typeArgs, List<Formal> formals,
      List<AttributedExpression> req, List<FrameExpression> reads, List<AttributedExpression> ens,
      Expression body, Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, hasStaticKeyword, typeOfK, typeArgs, formals,
             req, reads, ens, body, attributes, signatureEllipsis) {
    }
  }

  public class TwoStateFunction : Function
  {
    public override string WhatKind { get { return "twostate function"; } }
    public TwoStateFunction(IToken tok, string name, bool hasStaticKeyword,
                     List<TypeParameter> typeArgs, List<Formal> formals, Formal result, Type resultType,
                     List<AttributedExpression> req, List<FrameExpression> reads, List<AttributedExpression> ens, Specification<Expression> decreases,
                     Expression body, Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, hasStaticKeyword, true, typeArgs, formals, result, resultType, req, reads, ens, decreases, body, attributes, signatureEllipsis) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(typeArgs != null);
      Contract.Requires(formals != null);
      Contract.Requires(resultType != null);
      Contract.Requires(req != null);
      Contract.Requires(reads != null);
      Contract.Requires(ens != null);
      Contract.Requires(decreases != null);
    }
    public override bool ReadsHeap { get { return true; } }
  }

  public class TwoStatePredicate : TwoStateFunction
  {
    public override string WhatKind { get { return "twostate predicate"; } }
    public TwoStatePredicate(IToken tok, string name, bool hasStaticKeyword,
                     List<TypeParameter> typeArgs, List<Formal> formals,
                     List<AttributedExpression> req, List<FrameExpression> reads, List<AttributedExpression> ens, Specification<Expression> decreases,
                     Expression body, Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, hasStaticKeyword, typeArgs, formals, null, Type.Bool, req, reads, ens, decreases, body, attributes, signatureEllipsis) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(typeArgs != null);
      Contract.Requires(formals != null);
      Contract.Requires(req != null);
      Contract.Requires(reads != null);
      Contract.Requires(ens != null);
      Contract.Requires(decreases != null);
    }
  }

  public class Method : MemberDecl, TypeParameter.ParentType, IMethodCodeContext
  {
    public override string WhatKind { get { return "method"; } }
    public bool SignatureIsOmitted { get { return SignatureEllipsis != null; } }
    public readonly IToken SignatureEllipsis;
    public bool MustReverify;
    public bool IsEntryPoint = false;
    public readonly List<TypeParameter> TypeArgs;
    public readonly List<Formal> Ins;
    public readonly List<Formal> Outs;
    public readonly List<AttributedExpression> Req;
    public readonly Specification<FrameExpression> Mod;
    public readonly List<AttributedExpression> Ens;
    public readonly Specification<Expression> Decreases;
    private BlockStmt methodBody;  // Body is readonly after construction, except for any kind of rewrite that may take place around the time of resolution (note that "methodBody" is a "DividedBlockStmt" for any "Method" that is a "Constructor")
    public bool IsRecursive;  // filled in during resolution
    public bool IsTailRecursive;  // filled in during resolution
    public readonly ISet<IVariable> AssignedAssumptionVariables = new HashSet<IVariable>();
    public Method OverriddenMethod;
    public Method Original => OverriddenMethod == null ? this : OverriddenMethod.Original;
    public override bool IsOverrideThatAddsBody => base.IsOverrideThatAddsBody && Body != null;
    private static BlockStmt emptyBody = new BlockStmt(Token.NoToken, Token.NoToken, new List<Statement>());

    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var formal in Ins.Where(f => f.DefaultValue != null)) {
          yield return formal.DefaultValue;
        }
        foreach (var e in Req) {
          yield return e.E;
        }
        foreach (var e in Mod.Expressions) {
          yield return e.E;
        }
        foreach (var e in Ens) {
          yield return e.E;
        }
        foreach (var e in Decreases.Expressions) {
          yield return e;
        }
      }
    }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(TypeArgs));
      Contract.Invariant(cce.NonNullElements(Ins));
      Contract.Invariant(cce.NonNullElements(Outs));
      Contract.Invariant(cce.NonNullElements(Req));
      Contract.Invariant(Mod != null);
      Contract.Invariant(cce.NonNullElements(Ens));
      Contract.Invariant(Decreases != null);
    }

    public Method(IToken tok, string name,
                  bool hasStaticKeyword, bool isGhost,
                  [Captured] List<TypeParameter> typeArgs,
                  [Captured] List<Formal> ins, [Captured] List<Formal> outs,
                  [Captured] List<AttributedExpression> req, [Captured] Specification<FrameExpression> mod,
                  [Captured] List<AttributedExpression> ens,
                  [Captured] Specification<Expression> decreases,
                  [Captured] BlockStmt body,
                  Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, hasStaticKeyword, isGhost, attributes, signatureEllipsis != null) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(ins));
      Contract.Requires(cce.NonNullElements(outs));
      Contract.Requires(cce.NonNullElements(req));
      Contract.Requires(mod != null);
      Contract.Requires(cce.NonNullElements(ens));
      Contract.Requires(decreases != null);
      this.TypeArgs = typeArgs;
      this.Ins = ins;
      this.Outs = outs;
      this.Req = req;
      this.Mod = mod;
      this.Ens = ens;
      this.Decreases = decreases;
      this.methodBody = body;
      this.SignatureEllipsis = signatureEllipsis;
      MustReverify = false;
    }

    bool ICodeContext.IsGhost { get { return this.IsGhost; } }
    List<TypeParameter> ICodeContext.TypeArgs { get { return this.TypeArgs; } }
    List<Formal> ICodeContext.Ins { get { return this.Ins; } }
    List<Formal> IMethodCodeContext.Outs { get { return this.Outs; } }
    Specification<FrameExpression> IMethodCodeContext.Modifies { get { return Mod; } }
    IToken ICallable.Tok { get { return this.tok; } }
    string ICallable.NameRelativeToModule {
      get {
        if (EnclosingClass is DefaultClassDecl) {
          return Name;
        } else {
          return EnclosingClass.Name + "." + Name;
        }
      }
    }
    Specification<Expression> ICallable.Decreases { get { return this.Decreases; } }
    bool _inferredDecr;
    bool ICallable.InferredDecreases {
      set { _inferredDecr = value; }
      get { return _inferredDecr; }
    }

    ModuleDefinition ICodeContext.EnclosingModule {
      get {
        Contract.Assert(this.EnclosingClass != null);  // this getter is supposed to be called only after signature-resolution is complete
        return this.EnclosingClass.EnclosingModuleDefinition;
      }
    }
    bool ICodeContext.MustReverify { get { return this.MustReverify; } }
    public bool AllowsNontermination {
      get {
        return Contract.Exists(Decreases.Expressions, e => e is WildcardExpr);
      }
    }

    public override string CompileName {
      get {
        var nm = base.CompileName;
        if (nm == Dafny.Compiler.DefaultNameMain && IsStatic && !IsEntryPoint) {
          // for a static method that is named "Main" but is not a legal "Main" method,
          // change its name.
          nm = EnclosingClass.Name + "_" + nm;
        }
        return nm;
      }
    }

    public BlockStmt Body {
      get {
        // Lemma from included files do not need to be resolved and translated
        // so we return emptyBody. This is to speed up resolvor and translator.
        if (methodBody != null && (this is Lemma || this is TwoStateLemma) && this.tok is IncludeToken && !DafnyOptions.O.VerifyAllModules) {
          return Method.emptyBody;
        } else {
          return methodBody;
        }
      }
      set {
        methodBody = value;
      }
    }

    public BlockStmt BodyForRefinement {
      // For refinement, we still need to merge in the body
      // a lemma that is in the refinement base that is defined
      // in a include file.
      get {
        return methodBody;
      }
    }
  }

  public class Lemma : Method
  {
    public override string WhatKind { get { return "lemma"; } }
    public Lemma(IToken tok, string name,
                 bool hasStaticKeyword,
                 [Captured] List<TypeParameter> typeArgs,
                 [Captured] List<Formal> ins, [Captured] List<Formal> outs,
                 [Captured] List<AttributedExpression> req, [Captured] Specification<FrameExpression> mod,
                 [Captured] List<AttributedExpression> ens,
                 [Captured] Specification<Expression> decreases,
                 [Captured] BlockStmt body,
                 Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, hasStaticKeyword, true, typeArgs, ins, outs, req, mod, ens, decreases, body, attributes, signatureEllipsis) {
    }
  }

  public class TwoStateLemma : Method
  {
    public override string WhatKind { get { return "twostate lemma"; } }
    public TwoStateLemma(IToken tok, string name,
                 bool hasStaticKeyword,
                 [Captured] List<TypeParameter> typeArgs,
                 [Captured] List<Formal> ins, [Captured] List<Formal> outs,
                 [Captured] List<AttributedExpression> req,
                 [Captured] Specification<FrameExpression> mod,
                 [Captured] List<AttributedExpression> ens,
                 [Captured] Specification<Expression> decreases,
                 [Captured] BlockStmt body,
                 Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, hasStaticKeyword, true, typeArgs, ins, outs, req, mod, ens, decreases, body, attributes, signatureEllipsis) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(typeArgs != null);
      Contract.Requires(ins != null);
      Contract.Requires(outs != null);
      Contract.Requires(req != null);
      Contract.Requires(mod != null);
      Contract.Requires(ens != null);
      Contract.Requires(decreases != null);
    }
  }

  public class Constructor : Method
  {
    public override string WhatKind { get { return "constructor"; } }
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Body == null || Body is DividedBlockStmt);
    }
    public List<Statement> BodyInit {  // first part of Body's statements
      get {
        if (Body == null) {
          return null;
        } else {
          return ((DividedBlockStmt)Body).BodyInit;
        }
      }
    }
    public List<Statement> BodyProper {  // second part of Body's statements
      get {
        if (Body == null) {
          return null;
        } else {
          return ((DividedBlockStmt)Body).BodyProper;
        }
      }
    }
    public Constructor(IToken tok, string name,
                  List<TypeParameter> typeArgs,
                  List<Formal> ins,
                  List<AttributedExpression> req, [Captured] Specification<FrameExpression> mod,
                  List<AttributedExpression> ens,
                  Specification<Expression> decreases,
                  DividedBlockStmt body,
                  Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, false, false, typeArgs, ins, new List<Formal>(), req, mod, ens, decreases, body, attributes, signatureEllipsis) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(ins));
      Contract.Requires(cce.NonNullElements(req));
      Contract.Requires(mod != null);
      Contract.Requires(cce.NonNullElements(ens));
      Contract.Requires(decreases != null);
    }

    public bool HasName {
      get {
        return Name != "_ctor";
      }
    }
  }

  /// <summary>
  /// A PrefixLemma is the inductive unrolling M# implicitly declared for every extreme lemma M.
  /// </summary>
  public class PrefixLemma : Method
  {
    public override string WhatKind { get { return "prefix lemma"; } }
    public readonly Formal K;
    public readonly ExtremeLemma ExtremeLemma;
    public PrefixLemma(IToken tok, string name, bool hasStaticKeyword,
                       List<TypeParameter> typeArgs, Formal k, List<Formal> ins, List<Formal> outs,
                       List<AttributedExpression> req, Specification<FrameExpression> mod, List<AttributedExpression> ens, Specification<Expression> decreases,
                       BlockStmt body, Attributes attributes, ExtremeLemma extremeLemma)
      : base(tok, name, hasStaticKeyword, true, typeArgs, ins, outs, req, mod, ens, decreases, body, attributes, null) {
      Contract.Requires(k != null);
      Contract.Requires(ins != null && 1 <= ins.Count && ins[0] == k);
      Contract.Requires(extremeLemma != null);
      K = k;
      ExtremeLemma = extremeLemma;
    }
  }

  public abstract class ExtremeLemma : Method
  {
    public readonly ExtremePredicate.KType TypeOfK;
    public bool KNat {
      get {
        return TypeOfK == ExtremePredicate.KType.Nat;
      }
    }
    public PrefixLemma PrefixLemma;  // filled in during resolution (name registration)

    public ExtremeLemma(IToken tok, string name,
                         bool hasStaticKeyword, ExtremePredicate.KType typeOfK,
                         List<TypeParameter> typeArgs,
                         List<Formal> ins, [Captured] List<Formal> outs,
                         List<AttributedExpression> req, [Captured] Specification<FrameExpression> mod,
                         List<AttributedExpression> ens,
                         Specification<Expression> decreases,
                         BlockStmt body,
                         Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, hasStaticKeyword, true, typeArgs, ins, outs, req, mod, ens, decreases, body, attributes, signatureEllipsis) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(ins));
      Contract.Requires(cce.NonNullElements(outs));
      Contract.Requires(cce.NonNullElements(req));
      Contract.Requires(mod != null);
      Contract.Requires(cce.NonNullElements(ens));
      Contract.Requires(decreases != null);
      TypeOfK = typeOfK;
    }
  }

  public class LeastLemma : ExtremeLemma
  {
    public override string WhatKind { get { return "least lemma"; } }

    public LeastLemma(IToken tok, string name,
                          bool hasStaticKeyword, ExtremePredicate.KType typeOfK,
                          List<TypeParameter> typeArgs,
                          List<Formal> ins, [Captured] List<Formal> outs,
                          List<AttributedExpression> req, [Captured] Specification<FrameExpression> mod,
                          List<AttributedExpression> ens,
                          Specification<Expression> decreases,
                          BlockStmt body,
                          Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, hasStaticKeyword, typeOfK, typeArgs, ins, outs, req, mod, ens, decreases, body, attributes, signatureEllipsis) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(ins));
      Contract.Requires(cce.NonNullElements(outs));
      Contract.Requires(cce.NonNullElements(req));
      Contract.Requires(mod != null);
      Contract.Requires(cce.NonNullElements(ens));
      Contract.Requires(decreases != null);
    }
  }

  public class GreatestLemma : ExtremeLemma
  {
    public override string WhatKind { get { return "greatest lemma"; } }

    public GreatestLemma(IToken tok, string name,
                   bool hasStaticKeyword, ExtremePredicate.KType typeOfK,
                   List<TypeParameter> typeArgs,
                   List<Formal> ins, [Captured] List<Formal> outs,
                   List<AttributedExpression> req, [Captured] Specification<FrameExpression> mod,
                   List<AttributedExpression> ens,
                   Specification<Expression> decreases,
                   BlockStmt body,
                   Attributes attributes, IToken signatureEllipsis)
      : base(tok, name, hasStaticKeyword, typeOfK, typeArgs, ins, outs, req, mod, ens, decreases, body, attributes, signatureEllipsis) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(ins));
      Contract.Requires(cce.NonNullElements(outs));
      Contract.Requires(cce.NonNullElements(req));
      Contract.Requires(mod != null);
      Contract.Requires(cce.NonNullElements(ens));
      Contract.Requires(decreases != null);
    }
  }

  // ------------------------------------------------------------------------------------------------------

  public abstract class Statement : IAttributeBearingDeclaration
  {
    public readonly IToken Tok;
    public readonly IToken EndTok;  // typically a terminating semi-colon or end-curly-brace
    public LList<Label> Labels;  // mutable during resolution

    private Attributes attributes;
    public Attributes Attributes {
      get {
        return attributes;
      }
      set {
        attributes = value;
      }
    }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Tok != null);
      Contract.Invariant(EndTok != null);
    }

    public bool IsGhost;  // filled in by resolution

    public Statement(IToken tok, IToken endTok, Attributes attrs) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      this.Tok = tok;
      this.EndTok = endTok;
      this.attributes = attrs;
    }

    public Statement(IToken tok, IToken endTok)
      : this(tok, endTok, null) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
    }

    /// <summary>
    /// Returns the non-null substatements of the Statements.
    /// </summary>
    public virtual IEnumerable<Statement> SubStatements {
      get { yield break; }
    }

    /// <summary>
    /// Returns the non-null expressions of this statement proper (that is, do not include the expressions of substatements).
    /// </summary>
    public virtual IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in Attributes.SubExpressions(Attributes)) {
          yield return e;
        }
      }
    }
  }

  public class LList<T>
  {
    public readonly T Data;
    public readonly LList<T> Next;
    const LList<T> Empty = null;

    public LList(T d, LList<T> next) {
      Data = d;
      Next = next;
    }

    public static LList<T> Append(LList<T> a, LList<T> b) {
      if (a == null) return b;
      return new LList<T>(a.Data, Append(a.Next, b));
      // pretend this is ML
    }
    public static int Count(LList<T> n) {
      int count = 0;
      while (n != null) {
        count++;
        n = n.Next;
      }
      return count;
    }
  }

  public class Label
  {
    public readonly IToken Tok;
    public readonly string Name;
    string uniqueId = null;
    public string AssignUniqueId(FreshIdGenerator idGen)
    {
      if (uniqueId == null)
      {
        uniqueId = idGen.FreshNumericId("label");
      }
      return uniqueId;
    }
    public Label(IToken tok, string/*?*/ label) {
      Contract.Requires(tok != null);
      Tok = tok;
      Name = label;
    }
  }

  public class AssertLabel : Label
  {
    public Boogie.Expr E;  // filled in during translation
    public AssertLabel(IToken tok, string label)
      : base(tok, label) {
      Contract.Requires(tok != null);
      Contract.Requires(label != null);
    }
  }

  public abstract class PredicateStmt : Statement
  {
    public readonly Expression Expr;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Expr != null);
    }

    public PredicateStmt(IToken tok, IToken endTok, Expression expr, Attributes attrs)
      : base(tok, endTok, attrs) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(expr != null);
      this.Expr = expr;
    }

    public PredicateStmt(IToken tok, IToken endTok, Expression expr)
      : this(tok, endTok, expr, null) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(expr != null);
      this.Expr = expr;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        yield return Expr;
      }
    }
  }

  public class AssertStmt : PredicateStmt {
    public readonly BlockStmt Proof;
    public readonly AssertLabel Label;
    public AssertStmt(IToken tok, IToken endTok, Expression expr, BlockStmt/*?*/ proof, AssertLabel/*?*/ label, Attributes attrs)
      : base(tok, endTok, expr, attrs) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(expr != null);
      Proof = proof;
      Label = label;
    }
    public override IEnumerable<Statement> SubStatements {
      get {
        if (Proof != null) {
          yield return Proof;
        }
      }
    }
    public void AddCustomizedErrorMessage(IToken tok, string s) {
      var args = new List<Expression>() { new StringLiteralExpr(tok, s, true) };
      IToken openBrace = tok;
      IToken closeBrace = new Token(tok.line, tok.col + 7 + s.Length + 1); // where 7 = length(":error ")
      this.Attributes = new UserSuppliedAttributes(tok, openBrace, closeBrace, args, this.Attributes);
    }
  }

  public class ExpectStmt : PredicateStmt
  {
    public Expression Message;
    public ExpectStmt(IToken tok, IToken endTok, Expression expr, Expression message, Attributes attrs)
      : base(tok, endTok, expr, attrs) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(expr != null);
      this.Message = message;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        if (Message != null) {
          yield return Message;
        }
      }
    }
  }

  public class AssumeStmt : PredicateStmt {
    public AssumeStmt(IToken tok, IToken endTok, Expression expr, Attributes attrs)
      : base(tok, endTok, expr, attrs) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(expr != null);
    }
  }

  public class PrintStmt : Statement {
    public readonly List<Expression> Args;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Args));
    }

    public PrintStmt(IToken tok, IToken endTok, List<Expression> args)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(cce.NonNullElements(args));

      Args = args;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        foreach (var arg in Args) {
          yield return arg;
        }
      }
    }
  }

  public class RevealStmt : Statement
  {
    public readonly List<Expression> Exprs;
    public readonly List<AssertLabel> LabeledAsserts = new List<AssertLabel>();  // contents filled in during resolution to indicate that "Expr" denotes a labeled assertion
    public readonly List<Statement> ResolvedStatements = new List<Statement>(); // contents filled in during resolution

    public override IEnumerable<Statement> SubStatements {
      get { return ResolvedStatements; }
    }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Exprs != null);
      Contract.Invariant(LabeledAsserts.Count <= Exprs.Count);
    }

    public RevealStmt(IToken tok, IToken endTok, List<Expression> exprs)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(exprs != null);
      this.Exprs = exprs;
    }

    public static string SingleName(Expression e) {
      Contract.Requires(e != null);
      if (e is NameSegment || e is LiteralExpr) {
        return e.tok.val;
      } else {
        return null;
      }
    }
  }

  public class BreakStmt : Statement {
    public readonly string TargetLabel;
    public readonly int BreakCount;
    public Statement TargetStmt;  // filled in during resolution
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(TargetLabel != null || 1 <= BreakCount);
    }

    public BreakStmt(IToken tok, IToken endTok, string targetLabel)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(targetLabel != null);
      this.TargetLabel = targetLabel;
    }
    public BreakStmt(IToken tok, IToken endTok, int breakCount)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(1 <= breakCount);
      this.BreakCount = breakCount;
    }
  }

  public abstract class ProduceStmt : Statement
  {
    public List<AssignmentRhs> rhss;
    public UpdateStmt hiddenUpdate;
    public ProduceStmt(IToken tok, IToken endTok, List<AssignmentRhs> rhss)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      this.rhss = rhss;
      hiddenUpdate = null;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        if (rhss != null) {
          foreach (var rhs in rhss) {
            foreach (var ee in rhs.SubExpressions) {
              yield return ee;
            }
          }
        }
      }
    }
    public override IEnumerable<Statement> SubStatements {
      get {
        if (rhss != null) {
          foreach (var rhs in rhss) {
            foreach (var s in rhs.SubStatements) {
              yield return s;
            }
          }
        }
      }
    }
  }

  public class ReturnStmt : ProduceStmt
  {
    public bool ReverifyPost;  // set during pre-resolution refinement transformation
    public ReturnStmt(IToken tok, IToken endTok, List<AssignmentRhs> rhss)
      : base(tok, endTok, rhss) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
    }
  }

  public class YieldStmt : ProduceStmt
  {
    public YieldStmt(IToken tok, IToken endTok, List<AssignmentRhs> rhss)
      : base(tok, endTok, rhss) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
    }
  }

  public abstract class AssignmentRhs
  {
    public readonly IToken Tok;

    private Attributes attributes;
    public Attributes Attributes
    {
      get
      {
        return attributes;
      }
      set
      {
        attributes = value;
      }
    }

    public bool HasAttributes()
    {
      return Attributes != null;
    }

    internal AssignmentRhs(IToken tok, Attributes attrs = null) {
      Tok = tok;
      Attributes = attrs;
    }
    public abstract bool CanAffectPreviouslyKnownExpressions { get; }
    /// <summary>
    /// Returns the non-null subexpressions of the AssignmentRhs.
    /// </summary>
    public virtual IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in Attributes.SubExpressions(Attributes)) {
          yield return e;
        }
      }
    }
    /// <summary>
    /// Returns the non-null sub-statements of the AssignmentRhs.
    /// </summary>
    public virtual IEnumerable<Statement> SubStatements{
      get { yield break; }
    }
  }

  public class ExprRhs : AssignmentRhs
  {
    public readonly Expression Expr;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Expr != null);
    }

    public ExprRhs(Expression expr, Attributes attrs = null)  // TODO: these 'attrs' apparently aren't handled correctly in the Cloner, and perhaps not in various visitors either (for example, CheckIsCompilable should not go into attributes)
      : base(expr.tok, attrs)
    {
      Contract.Requires(expr != null);
      Expr = expr;
    }
    public override bool CanAffectPreviouslyKnownExpressions { get { return false; } }
    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Expr;
      }
    }
  }

  /// <summary>
  /// A TypeRhs represents one of five things, each having to do with allocating something in the heap:
  ///  * new T[EE]
  ///    This allocates an array of objects of type T (where EE is a list of expression)
  ///  * new T[EE] (elementInit)
  ///    This is like the previous, but uses "elementInit" to initialize the elements of the new array.
  ///  * new T[E] [EE]
  ///    This is like the first one, but uses the elements displayed in the list EE as the initial
  ///    elements of the array.  Only a 1-dimensional array may be used in this case.  The size denoted
  ///    by E must equal the length of EE.
  ///  * new C
  ///    This allocates an object of type C
  ///  * new C.Init(EE)
  ///    This allocates an object of type C and then invokes the method/constructor Init on it
  /// There are three ways to construct a TypeRhs syntactically:
  ///  * TypeRhs(T, EE, initExpr)
  ///      -- represents "new T[EE]" (with "elementInit" being "null") and "new T[EE] (elementInit)"
  ///  * TypeRhs(T, E, EE)
  ///      -- represents "new T[E] [EE]"
  ///  * TypeRhs(C)
  ///      -- represents new C
  ///  * TypeRhs(Path, EE)
  ///    Here, Path may either be of the form C.Init
  ///      -- represents new C.Init(EE)
  ///    or all of Path denotes a type
  ///      -- represents new C._ctor(EE), where _ctor is the anonymous constructor for class C
  /// </summary>
  public class TypeRhs : AssignmentRhs
  {
    /// <summary>
    /// If ArrayDimensions != null, then the TypeRhs represents "new EType[ArrayDimensions]",
    ///     ElementInit is non-null to represent "new EType[ArrayDimensions] (elementInit)",
    ///     InitDisplay is non-null to represent "new EType[ArrayDimensions] [InitDisplay]",
    ///     and Arguments, Path, and InitCall are all null.
    /// If ArrayDimentions == null && Arguments == null, then the TypeRhs represents "new EType"
    ///     and ElementInit, Path, and InitCall are all null.
    /// If Arguments != null, then the TypeRhs represents "new Path(Arguments)"
    ///     and EType and InitCall is filled in by resolution, and ArrayDimensions == null and ElementInit == null.
    /// If OptionalNameComponent == null and Arguments != null, then the TypeRHS has not been resolved yet;
    ///   resolution will either produce an error or will chop off the last part of "EType" and move it to
    ///   OptionalNameComponent, after which the case above applies.
    /// </summary>
    public Type EType;  // in the case of Arguments != null, EType is filled in during resolution
    public readonly List<Expression> ArrayDimensions;
    public readonly Expression ElementInit;
    public readonly List<Expression> InitDisplay;
    public readonly ActualBindings/*?*/ Bindings;
    public List<Expression> Arguments {
      get {
        Contract.Requires(Bindings != null);
        return Bindings.Arguments;
      }
    }

    public Type Path;
    public CallStmt InitCall;  // may be null (and is definitely null for arrays), may be filled in during resolution
    public Type Type;  // filled in during resolution
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(EType != null || Bindings != null);
      Contract.Invariant(ElementInit == null || InitDisplay == null);
      Contract.Invariant(InitDisplay == null || ArrayDimensions.Count == 1);
      Contract.Invariant(ArrayDimensions == null || (Bindings == null && Path == null && InitCall == null && 1 <= ArrayDimensions.Count));
      Contract.Invariant(Bindings == null || (Path != null && ArrayDimensions == null && ElementInit == null && InitDisplay == null));
      Contract.Invariant(!(ArrayDimensions == null && Bindings == null) || (Path == null && InitCall == null && ElementInit == null && InitDisplay == null));
    }

    public TypeRhs(IToken tok, Type type, List<Expression> arrayDimensions, Expression elementInit)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      Contract.Requires(arrayDimensions != null && 1 <= arrayDimensions.Count);
      EType = type;
      ArrayDimensions = arrayDimensions;
      ElementInit = elementInit;
    }
    public TypeRhs(IToken tok, Type type, Expression dim, List<Expression> initDisplay)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      Contract.Requires(dim != null);
      Contract.Requires(initDisplay != null);
      EType = type;
      ArrayDimensions = new List<Expression> { dim };
      InitDisplay = initDisplay;
    }
    public TypeRhs(IToken tok, Type type)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      EType = type;
    }
    public TypeRhs(IToken tok, Type path, List<ActualBinding> arguments)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(path != null);
      Contract.Requires(arguments != null);
      Path = path;
      Bindings = new ActualBindings(arguments);
    }
    public override bool CanAffectPreviouslyKnownExpressions {
      get {
        if (InitCall != null) {
          foreach (var mod in InitCall.Method.Mod.Expressions) {
            if (!(mod.E is ThisExpr)) {
              return true;
            }
          }
        }
        return false;
      }
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        if (ArrayDimensions != null) {
          foreach (var e in ArrayDimensions) {
            yield return e;
          }
          if (ElementInit != null) {
            yield return ElementInit;
          }
          if (InitDisplay != null) {
            foreach (var e in InitDisplay) {
              yield return e;
            }
          }
        }
      }
    }
    public override IEnumerable<Statement> SubStatements {
      get {
        if (InitCall != null) {
          yield return InitCall;
        }
      }
    }
  }

  public class HavocRhs : AssignmentRhs {
    public HavocRhs(IToken tok)
      : base(tok)
    {
    }
    public override bool CanAffectPreviouslyKnownExpressions { get { return false; } }
  }

  public class VarDeclStmt : Statement
  {
    public readonly List<LocalVariable> Locals;
    public readonly ConcreteUpdateStatement Update;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Locals));
      Contract.Invariant(Locals.Count != 0);
    }

    public VarDeclStmt(IToken tok, IToken endTok, List<LocalVariable> locals, ConcreteUpdateStatement update)
      : base(tok, endTok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(locals != null);
      Contract.Requires(locals.Count != 0);

      Locals = locals;
      Update = update;
    }

    public override IEnumerable<Statement> SubStatements {
      get { if (Update != null) { yield return Update; } }
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        foreach (var v in Locals) {
          foreach (var e in Attributes.SubExpressions(v.Attributes)) {
            yield return e;
          }
        }
      }
    }
  }

  public class VarDeclPattern : Statement
  {
    public readonly CasePattern<LocalVariable> LHS;
    public readonly Expression RHS;
    public bool HasGhostModifier;

    public VarDeclPattern(IToken tok, IToken endTok, CasePattern<LocalVariable> lhs, Expression rhs, bool hasGhostModifier = true)
      : base(tok, endTok) {
      LHS = lhs;
      RHS = rhs;
      HasGhostModifier = hasGhostModifier;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in Attributes.SubExpressions(Attributes)) {
          yield return e;
        }
        yield return RHS;
      }
    }

    public IEnumerable<LocalVariable> LocalVars {
      get {
        foreach (var bv in LHS.Vars) {
          yield return bv;
        }
      }
    }
  }

  /// <summary>
  /// Common superclass of UpdateStmt, AssignSuchThatStmt and AssignOrReturnStmt
  /// </summary>
  public abstract class ConcreteUpdateStatement : Statement
  {
    public readonly List<Expression> Lhss;
    public ConcreteUpdateStatement(IToken tok, IToken endTok, List<Expression> lhss, Attributes attrs = null)
      : base(tok, endTok, attrs) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(cce.NonNullElements(lhss));
      Lhss = lhss;
    }
  }

  public class AssignSuchThatStmt : ConcreteUpdateStatement
  {
    public readonly Expression Expr;
    public readonly IToken AssumeToken;

    public List<ComprehensionExpr.BoundedPool> Bounds;  // initialized and filled in by resolver; null for a ghost statement
    // invariant Bounds == null || Bounds.Count == BoundVars.Count;
    public List<IVariable> MissingBounds;  // filled in during resolution; remains "null" if bounds can be found
    // invariant Bounds == null || MissingBounds == null;
    public class WiggleWaggleBound : ComprehensionExpr.BoundedPool
    {
      public override PoolVirtues Virtues => PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
      public override int Preference() => 1;
    }

    /// <summary>
    /// "assumeToken" is allowed to be "null", in which case the verifier will check that a RHS value exists.
    /// If "assumeToken" is non-null, then it should denote the "assume" keyword used in the statement.
    /// </summary>
    public AssignSuchThatStmt(IToken tok, IToken endTok, List<Expression> lhss, Expression expr, IToken assumeToken, Attributes attrs)
      : base(tok, endTok, lhss, attrs) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(cce.NonNullElements(lhss));
      Contract.Requires(lhss.Count != 0);
      Contract.Requires(expr != null);
      Expr = expr;
      if (assumeToken != null) {
        AssumeToken = assumeToken;
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        yield return Expr;
        foreach (var lhs in Lhss) {
          yield return lhs;
        }
      }
    }
  }

  public class UpdateStmt : ConcreteUpdateStatement
  {
    public readonly List<AssignmentRhs> Rhss;
    public readonly bool CanMutateKnownState;
    public Expression OriginalInitialLhs = null;

    public readonly List<Statement> ResolvedStatements = new List<Statement>();  // contents filled in during resolution
    public override IEnumerable<Statement> SubStatements {
      get { return ResolvedStatements; }
    }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Lhss));
      Contract.Invariant(cce.NonNullElements(Rhss));
    }
    public UpdateStmt(IToken tok, IToken endTok, List<Expression> lhss, List<AssignmentRhs> rhss)
      : base(tok, endTok, lhss)
    {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(cce.NonNullElements(lhss));
      Contract.Requires(cce.NonNullElements(rhss));
      Contract.Requires(lhss.Count != 0 || rhss.Count == 1);
      Rhss = rhss;
      CanMutateKnownState = false;
    }
    public UpdateStmt(IToken tok, IToken endTok, List<Expression> lhss, List<AssignmentRhs> rhss, bool mutate)
      : base(tok, endTok, lhss)
    {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(cce.NonNullElements(lhss));
      Contract.Requires(cce.NonNullElements(rhss));
      Contract.Requires(lhss.Count != 0 || rhss.Count == 1);
      Rhss = rhss;
      CanMutateKnownState = mutate;
    }
  }

  public class AssignOrReturnStmt : ConcreteUpdateStatement
  {
    public readonly Expression Rhs; // this is the unresolved RHS, and thus can also be a method call
    public readonly List<AssignmentRhs> Rhss;
    public readonly IToken KeywordToken;
    public readonly List<Statement> ResolvedStatements = new List<Statement>();  // contents filled in during resolution
    public override IEnumerable<Statement> SubStatements {
      get { return ResolvedStatements; }
    }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Lhss != null);
      Contract.Invariant(
          Lhss.Count == 0 ||                   // ":- MethodOrExpresion;" which returns void success or an error
          Lhss.Count == 1 && Lhss[0] != null   // "y :- MethodOrExpression;"
      );
      Contract.Invariant(Rhs != null);
    }

    public AssignOrReturnStmt(IToken tok, IToken endTok, List<Expression> lhss, Expression rhs, IToken keywordToken, List<AssignmentRhs> rhss = null)
      : base(tok, endTok, lhss)
    {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(lhss != null);
      Contract.Requires(lhss.Count <= 1);
      Contract.Requires(rhs != null);
      Rhs = rhs;
      Rhss = rhss;
      KeywordToken = keywordToken;
    }
  }

  public class AssignStmt : Statement {
    public readonly Expression Lhs;
    public readonly AssignmentRhs Rhs;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Lhs != null);
      Contract.Invariant(Rhs != null);
    }

    public AssignStmt(IToken tok, IToken endTok, Expression lhs, AssignmentRhs rhs)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(lhs != null);
      Contract.Requires(rhs != null);
      this.Lhs = lhs;
      this.Rhs = rhs;
    }

    public override IEnumerable<Statement> SubStatements {
      get {
        foreach (var s in Rhs.SubStatements) {
          yield return s;
        }
      }
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        yield return Lhs;
        foreach (var ee in Rhs.SubExpressions) {
          yield return ee;
        }
      }
    }

    /// <summary>
    /// This method assumes "lhs" has been successfully resolved.
    /// </summary>
    public static bool LhsIsToGhost(Expression lhs) {
      Contract.Requires(lhs != null);
      return LhsIsToGhost_Which(lhs) == NonGhostKind.IsGhost;
    }
    public static bool LhsIsToGhostOrAutoGhost(Expression lhs) {
      Contract.Requires(lhs != null);
      return LhsIsToGhost_Which(lhs) == NonGhostKind.IsGhost || lhs.Resolved is AutoGhostIdentifierExpr;
    }
    public enum NonGhostKind { IsGhost, Variable, Field, ArrayElement }
    public static string NonGhostKind_To_String(NonGhostKind gk) {
      Contract.Requires(gk != NonGhostKind.IsGhost);
      switch (gk) {
        case NonGhostKind.Variable: return "non-ghost variable";
        case NonGhostKind.Field: return "non-ghost field";
        case NonGhostKind.ArrayElement: return "array element";
        default:
          Contract.Assume(false);  // unexpected NonGhostKind
          throw new cce.UnreachableException();  // please compiler
      }
    }
    /// <summary>
    /// This method assumes "lhs" has been successfully resolved.
    /// </summary>
    public static NonGhostKind LhsIsToGhost_Which(Expression lhs) {
      Contract.Requires(lhs != null);
      lhs = lhs.Resolved;
      if (lhs is AutoGhostIdentifierExpr) {
        // TODO: Should we return something different for this case?
        var x = (IdentifierExpr)lhs;
        if (!x.Var.IsGhost) {
          return NonGhostKind.Variable;
        }
      } else if (lhs is IdentifierExpr) {
        var x = (IdentifierExpr)lhs;
        if (!x.Var.IsGhost) {
          return NonGhostKind.Variable;
        }
      } else if (lhs is MemberSelectExpr) {
        var x = (MemberSelectExpr)lhs;
        if (!x.Member.IsGhost) {
          return NonGhostKind.Field;
        }
      } else {
        // LHS denotes an array element, which is always non-ghost
        return NonGhostKind.ArrayElement;
      }
      return NonGhostKind.IsGhost;
    }
  }

  public class LocalVariable : IVariable, IAttributeBearingDeclaration {
    public readonly IToken Tok;
    public readonly IToken EndTok;  // typically a terminating semi-colon or end-curly-brace
    readonly string name;
    public Attributes Attributes;
    public bool IsGhost;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(name != null);
      Contract.Invariant(OptionalType != null);
    }

    public LocalVariable(IToken tok, IToken endTok, string name, Type type, bool isGhost) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);  // can be a proxy, though

      this.Tok = tok;
      this.EndTok = endTok;
      this.name = name;
      this.OptionalType = type;
      if (type is InferredTypeProxy) {
        ((InferredTypeProxy)type).KeepConstraints = true;
      }
      this.IsGhost = isGhost;
    }

    public string Name {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return name;
      }
    }
    public static bool HasWildcardName(IVariable v) {
      Contract.Requires(v != null);
      return v.Name.StartsWith("_v");
    }
    public static string DisplayNameHelper(IVariable v) {
      Contract.Requires(v != null);
      return HasWildcardName(v) ? "_" : v.Name;
    }
    public string DisplayName {
      get { return DisplayNameHelper(this); }
    }
    private string uniqueName;
    public string UniqueName {
      get {
        return uniqueName;
      }
    }
    public bool HasBeenAssignedUniqueName {
      get {
        return uniqueName != null;
      }
    }
    public string AssignUniqueName(FreshIdGenerator generator)
    {
      if (uniqueName == null)
      {
        uniqueName = generator.FreshId(Name + "#");
        compileName = string.Format("_{0}_{1}", Compiler.FreshId(), NonglobalVariable.CompilerizeName(name));
      }
      return UniqueName;
    }
    string compileName;
    public string CompileName {
      get {
        if (compileName == null)
        {
          compileName = string.Format("_{0}_{1}", Compiler.FreshId(), NonglobalVariable.CompilerizeName(name));
        }
        return compileName;
      }
    }
    public readonly Type OptionalType;  // this is the type mentioned in the declaration, if any
    Type IVariable.OptionalType { get { return this.OptionalType; } }
    internal Type type;  // this is the declared or inferred type of the variable; it is non-null after resolution (even if resolution fails)
    public Type Type {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);

        Contract.Assume(type != null);  /* we assume object has been resolved */
        return type.Normalize();
      }
    }
    public bool IsMutable {
      get {
        return true;
      }
    }
    bool IVariable.IsGhost {
      get {
        return this.IsGhost;
      }
    }
    /// <summary>
    /// This method retrospectively makes the LocalVariable a ghost.  It is to be used only during resolution.
    /// </summary>
    public void MakeGhost() {
      this.IsGhost = true;
    }
    IToken IVariable.Tok {
      get {
        return Tok;
      }
    }
  }

  /// <summary>
  /// A CallStmt is always resolved.  It is typically produced as a resolved counterpart of the syntactic AST note ApplySuffix.
  /// </summary>
  public class CallStmt : Statement {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(MethodSelect.Member is Method);
      Contract.Invariant(cce.NonNullElements(Lhs));
      Contract.Invariant(cce.NonNullElements(Args));
    }

    public readonly List<Expression> Lhs;
    public readonly MemberSelectExpr MethodSelect;
    public readonly ActualBindings Bindings;
    public List<Expression> Args => Bindings.Arguments;
    public Expression OriginalInitialLhs = null;

    public Expression Receiver { get { return MethodSelect.Obj; } }
    public Method Method { get { return (Method)MethodSelect.Member; } }

    public CallStmt(IToken tok, IToken endTok, List<Expression> lhs, MemberSelectExpr memSel, List<ActualBinding> args)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(cce.NonNullElements(lhs));
      Contract.Requires(memSel != null);
      Contract.Requires(memSel.Member is Method);
      Contract.Requires(cce.NonNullElements(args));

      this.Lhs = lhs;
      this.MethodSelect = memSel;
      this.Bindings = new ActualBindings(args);
    }

    /// <summary>
    /// This constructor is intended to be used when constructing a resolved CallStmt. The "args" are expected
    /// to be already resolved, and are all given positionally.
    /// </summary>
    public CallStmt(IToken tok, IToken endTok, List<Expression> lhs, MemberSelectExpr memSel, List<Expression> args)
      : this(tok, endTok, lhs, memSel, args.ConvertAll(e => new ActualBinding(null, e))) {
      Bindings.AcceptArgumentExpressionsAsExactParameterList();
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        foreach (var ee in Lhs) {
          yield return ee;
        }
        yield return MethodSelect;
        foreach (var ee in Args) {
          yield return ee;
        }
      }
    }
  }

  public class BlockStmt : Statement {
    public readonly List<Statement> Body;
    public BlockStmt(IToken tok, IToken endTok, [Captured] List<Statement> body)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(cce.NonNullElements(body));
      this.Body = body;
    }

    public override IEnumerable<Statement> SubStatements {
      get { return Body; }
    }

    public virtual void AppendStmt(Statement s) {
      Contract.Requires(s != null);
      Body.Add(s);
    }
  }

  public class DividedBlockStmt : BlockStmt
  {
    public readonly List<Statement> BodyInit;  // first part of Body's statements
    public readonly IToken SeparatorTok;  // token that separates the two parts, if any
    public readonly List<Statement> BodyProper;  // second part of Body's statements
    public DividedBlockStmt(IToken tok, IToken endTok, List<Statement> bodyInit, IToken/*?*/ separatorTok, List<Statement> bodyProper)
      : base(tok, endTok, Util.Concat(bodyInit, bodyProper)) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(cce.NonNullElements(bodyInit));
      Contract.Requires(cce.NonNullElements(bodyProper));
      this.BodyInit = bodyInit;
      this.SeparatorTok = separatorTok;
      this.BodyProper = bodyProper;
    }
    public override void AppendStmt(Statement s) {
      BodyProper.Add(s);
      base.AppendStmt(s);
    }
  }

  public class IfStmt : Statement {
    public readonly bool IsBindingGuard;
    public readonly Expression Guard;
    public readonly BlockStmt Thn;
    public readonly Statement Els;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(!IsBindingGuard || (Guard is ExistsExpr && ((ExistsExpr)Guard).Range == null));
      Contract.Invariant(Thn != null);
      Contract.Invariant(Els == null || Els is BlockStmt || Els is IfStmt || Els is SkeletonStatement);
    }
    public IfStmt(IToken tok, IToken endTok, bool isBindingGuard, Expression guard, BlockStmt thn, Statement els)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(!isBindingGuard || (guard is ExistsExpr && ((ExistsExpr)guard).Range == null));
      Contract.Requires(thn != null);
      Contract.Requires(els == null || els is BlockStmt || els is IfStmt || els is SkeletonStatement);
      this.IsBindingGuard = isBindingGuard;
      this.Guard = guard;
      this.Thn = thn;
      this.Els = els;
    }
    public IfStmt(IToken tok, IToken endTok, bool isBindingGuard, Expression guard, BlockStmt thn, Statement els, Attributes attrs)
      : base(tok, endTok, attrs) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(!isBindingGuard || (guard is ExistsExpr && ((ExistsExpr)guard).Range == null));
      Contract.Requires(thn != null);
      Contract.Requires(els == null || els is BlockStmt || els is IfStmt || els is SkeletonStatement);
      this.IsBindingGuard = isBindingGuard;
      this.Guard = guard;
      this.Thn = thn;
      this.Els = els;
    }
    public override IEnumerable<Statement> SubStatements {
      get {
        yield return Thn;
        if (Els != null) {
          yield return Els;
        }
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        if (Guard != null) {
          yield return Guard;
        }
      }
    }
  }

  public class GuardedAlternative
  {
    public readonly IToken Tok;
    public readonly bool IsBindingGuard;
    public readonly Expression Guard;
    public readonly List<Statement> Body;
    public Attributes Attributes;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Tok != null);
      Contract.Invariant(Guard != null);
      Contract.Invariant(!IsBindingGuard || (Guard is ExistsExpr && ((ExistsExpr)Guard).Range == null));
      Contract.Invariant(Body != null);
    }
    public GuardedAlternative(IToken tok, bool isBindingGuard, Expression guard, List<Statement> body)
    {
      Contract.Requires(tok != null);
      Contract.Requires(guard != null);
      Contract.Requires(!isBindingGuard || (guard is ExistsExpr && ((ExistsExpr)guard).Range == null));
      Contract.Requires(body != null);
      this.Tok = tok;
      this.IsBindingGuard = isBindingGuard;
      this.Guard = guard;
      this.Body = body;
      this.Attributes = null;
    }
    public GuardedAlternative(IToken tok, bool isBindingGuard, Expression guard, List<Statement> body, Attributes attrs)
    {
      Contract.Requires(tok != null);
      Contract.Requires(guard != null);
      Contract.Requires(!isBindingGuard || (guard is ExistsExpr && ((ExistsExpr)guard).Range == null));
      Contract.Requires(body != null);
      this.Tok = tok;
      this.IsBindingGuard = isBindingGuard;
      this.Guard = guard;
      this.Body = body;
      this.Attributes = attrs;
    }
  }

  public class AlternativeStmt : Statement
  {
    public readonly bool UsesOptionalBraces;
    public readonly List<GuardedAlternative> Alternatives;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Alternatives != null);
    }
    public AlternativeStmt(IToken tok, IToken endTok, List<GuardedAlternative> alternatives, bool usesOptionalBraces)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(alternatives != null);
      this.Alternatives = alternatives;
      this.UsesOptionalBraces = usesOptionalBraces;
    }
    public AlternativeStmt(IToken tok, IToken endTok, List<GuardedAlternative> alternatives, bool usesOptionalBraces, Attributes attrs)
      : base(tok, endTok, attrs) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(alternatives != null);
      this.Alternatives = alternatives;
      this.UsesOptionalBraces = usesOptionalBraces;
    }
    public override IEnumerable<Statement> SubStatements {
      get {
        foreach (var alt in Alternatives) {
          foreach (var s in alt.Body) {
            yield return s;
          }
        }
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        foreach (var alt in Alternatives) {
          yield return alt.Guard;
        }
      }
    }
  }

  public abstract class LoopStmt : Statement
  {
    public readonly List<AttributedExpression> Invariants;
    public readonly Specification<Expression> Decreases;
    public bool InferredDecreases;  // filled in by resolution; says that no explicit "decreases" clause was given and an attempt was made to find one automatically (which may or may not have produced anything)
    public readonly Specification<FrameExpression> Mod;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Invariants));
      Contract.Invariant(Decreases != null);
      Contract.Invariant(Mod != null);
    }
    public LoopStmt(IToken tok, IToken endTok, List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod)
    : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(cce.NonNullElements(invariants));
      Contract.Requires(decreases != null);
      Contract.Requires(mod != null);

      this.Invariants = invariants;
      this.Decreases = decreases;
      this.Mod = mod;
    }
    public LoopStmt(IToken tok, IToken endTok, List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod, Attributes attrs)
       : base(tok, endTok, attrs) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(cce.NonNullElements(invariants));
      Contract.Requires(decreases != null);
      Contract.Requires(mod != null);

      this.Invariants = invariants;
      this.Decreases = decreases;
      this.Mod = mod;
    }
    public IEnumerable<Expression> LoopSpecificationExpressions {
      get {
        foreach (var mfe in Invariants) {
          foreach (var e in Attributes.SubExpressions(mfe.Attributes)) { yield return e; }
          yield return mfe.E;
        }
        foreach (var e in Attributes.SubExpressions(Decreases.Attributes)) { yield return e; }
        if (Decreases.Expressions != null) {
          foreach (var e in Decreases.Expressions) {
            yield return e;
          }
        }
        foreach (var e in Attributes.SubExpressions(Mod.Attributes)) { yield return e; }
        if (Mod.Expressions != null) {
          foreach (var fe in Mod.Expressions) {
            yield return fe.E;
          }
        }
      }
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) {
          yield return e;
        }
        foreach (var e in LoopSpecificationExpressions) {
          yield return e;
        }
      }
    }
  }

  public abstract class OneBodyLoopStmt : LoopStmt {
    public readonly BlockStmt/*?*/ Body;
    public WhileStmt.LoopBodySurrogate/*?*/ BodySurrogate;  // set by Resolver; remains null unless Body==null

    public OneBodyLoopStmt(IToken tok, IToken endTok,
      List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
      BlockStmt /*?*/ body, Attributes/*?*/ attrs)
      : base(tok, endTok, invariants, decreases, mod, attrs) {
      Body = body;
    }

    public override IEnumerable<Statement> SubStatements {
      get {
        if (Body != null) {
          yield return Body;
        }
      }
    }
  }

  public class WhileStmt : OneBodyLoopStmt
  {
    public readonly Expression/*?*/ Guard;

    public class LoopBodySurrogate
    {
      public readonly List<IVariable> LocalLoopTargets;
      public readonly bool UsesHeap;

      public LoopBodySurrogate(List<IVariable> localLoopTargets, bool usesHeap) {
        LocalLoopTargets = localLoopTargets;
        UsesHeap = usesHeap;
      }
    }

    public WhileStmt(IToken tok, IToken endTok, Expression guard,
                     List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
                     BlockStmt body)
      : base(tok, endTok, invariants, decreases, mod, body, null) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      this.Guard = guard;
    }

    public WhileStmt(IToken tok, IToken endTok, Expression guard,
                 List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
                 BlockStmt body, Attributes attrs)
      : base(tok, endTok, invariants, decreases, mod, body, attrs) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      this.Guard = guard;
    }

    public override IEnumerable<Statement> SubStatements {
      get {
        if (Body != null) {
          yield return Body;
        }
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        if (Guard != null) {
          yield return Guard;
        }
      }
    }
  }

  /// <summary>
  /// This class is really just a WhileStmt, except that it serves the purpose of remembering if the object was created as the result of a refinement
  /// merge.
  /// </summary>
  public class RefinedWhileStmt : WhileStmt
  {
    public RefinedWhileStmt(IToken tok, IToken endTok, Expression guard,
                            List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
                            BlockStmt body)
      : base(tok, endTok, guard, invariants, decreases, mod, body) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(body != null);
    }
  }

  public class ForLoopStmt : OneBodyLoopStmt {
    public readonly BoundVar LoopIndex;
    public readonly Expression Start;
    public readonly Expression/*?*/ End;
    public readonly bool GoingUp;

    public ForLoopStmt(IToken tok, IToken endTok, BoundVar loopIndexVariable, Expression start, Expression/*?*/ end, bool goingUp,
      List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
      BlockStmt /*?*/ body, Attributes attrs)
      : base(tok, endTok, invariants, decreases, mod, body, attrs)
    {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(loopIndexVariable != null);
      Contract.Requires(start != null);
      Contract.Requires(invariants != null);
      Contract.Requires(decreases != null);
      Contract.Requires(mod != null);
      LoopIndex = loopIndexVariable;
      Start = start;
      End = end;
      GoingUp = goingUp;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        yield return Start;
        if (End != null) {
          yield return End;
        }
      }
    }
  }

  public class AlternativeLoopStmt : LoopStmt
  {
    public readonly bool UsesOptionalBraces;
    public readonly List<GuardedAlternative> Alternatives;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Alternatives != null);
    }
    public AlternativeLoopStmt(IToken tok, IToken endTok,
                               List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
                               List<GuardedAlternative> alternatives, bool usesOptionalBraces)
      : base(tok, endTok, invariants, decreases, mod) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(alternatives != null);
      this.Alternatives = alternatives;
      this.UsesOptionalBraces = usesOptionalBraces;
    }
    public AlternativeLoopStmt(IToken tok, IToken endTok,
                   List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
                   List<GuardedAlternative> alternatives, bool usesOptionalBraces, Attributes attrs)
      : base(tok, endTok, invariants, decreases, mod, attrs) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(alternatives != null);
      this.Alternatives = alternatives;
      this.UsesOptionalBraces = usesOptionalBraces;
    }
    public override IEnumerable<Statement> SubStatements {
      get {
        foreach (var alt in Alternatives) {
          foreach (var s in alt.Body) {
            yield return s;
          }
        }
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        foreach (var alt in Alternatives) {
          yield return alt.Guard;
        }
      }
    }
  }

  public class ForallStmt : Statement
  {
    public readonly List<BoundVar> BoundVars;  // note, can be the empty list, in which case Range denotes "true"
    public Expression Range;  // mostly readonly, except that it may in some cases be updated during resolution to conjoin the precondition of the call in the body
    public readonly List<AttributedExpression> Ens;
    public readonly Statement Body;
    public List<Expression> ForallExpressions;   // fill in by rewriter.
    public bool CanConvert = true; //  can convert to ForallExpressions

    public List<ComprehensionExpr.BoundedPool> Bounds;  // initialized and filled in by resolver
    // invariant: if successfully resolved, Bounds.Count == BoundVars.Count;

    /// <summary>
    /// Assign means there are no ensures clauses and the body consists of one update statement,
    ///   either to an object field or to an array.
    /// Call means there are no ensures clauses and the body consists of a single call to a (presumably
    ///   ghost, but non-ghost is also allowed) method with no out-parameters and an empty modifies
    ///   clause.
    /// Proof means there is at least one ensures clause, and the body consists of any (presumably ghost,
    ///   but non-ghost is also allowed) code without side effects on variables (including fields and array
    ///   elements) declared outside the body itself.
    /// Notes:
    /// * More kinds may be allowed in the future.
    /// * One could also allow Call to call non-ghost methods without side effects.  However, that
    ///   would seem pointless in the program, so they are disallowed (to avoid any confusion that
    ///   such use of the forall statement might actually have a point).
    /// * One could allow Proof even without ensures clauses that "export" what was learned.
    ///   However, that might give the false impression that the body is nevertheless exported.
    /// </summary>
    public enum BodyKind { Assign, Call, Proof }
    public BodyKind Kind;  // filled in during resolution

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(BoundVars != null);
      Contract.Invariant(Range != null);
      Contract.Invariant(BoundVars.Count != 0 || LiteralExpr.IsTrue(Range));
      Contract.Invariant(Ens != null);
    }

    public ForallStmt(IToken tok, IToken endTok, List<BoundVar> boundVars, Attributes attrs, Expression range, List<AttributedExpression> ens, Statement body)
      : base(tok, endTok, attrs) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(cce.NonNullElements(boundVars));
      Contract.Requires(range != null);
      Contract.Requires(boundVars.Count != 0 || LiteralExpr.IsTrue(range));
      Contract.Requires(cce.NonNullElements(ens));
      this.BoundVars = boundVars;
      this.Range = range;
      this.Ens = ens;
      this.Body = body;
    }

    public Statement S0 {
      get {
        // dig into Body to find a single statement
        Statement s = this.Body;
        while (true) {
          var block = s as BlockStmt;
          if (block != null && block.Body.Count == 1) {
            s = block.Body[0];
            // dig further into s
          } else if (s is UpdateStmt) {
            var update = (UpdateStmt)s;
            if (update.ResolvedStatements.Count == 1) {
              s = update.ResolvedStatements[0];
              // dig further into s
            } else {
              return s;
            }
          } else {
            return s;
          }
        }
      }
    }

    public override IEnumerable<Statement> SubStatements {
      get {
        if (Body != null) {
          yield return Body;
        }
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        yield return Range;
        foreach (var ee in Ens) {
          foreach (var e in Attributes.SubExpressions(ee.Attributes)) { yield return e; }
          yield return ee.E;
        }
      }
    }

    public List<BoundVar> UncompilableBoundVars() {
      Contract.Ensures(Contract.Result<List<BoundVar>>() != null);
      var v = ComprehensionExpr.BoundedPool.PoolVirtues.Finite | ComprehensionExpr.BoundedPool.PoolVirtues.Enumerable;
      return ComprehensionExpr.BoundedPool.MissingBounds(BoundVars, Bounds, v);
    }
  }

  public class ModifyStmt : Statement
  {
    public readonly Specification<FrameExpression> Mod;
    public readonly BlockStmt Body;

    public ModifyStmt(IToken tok, IToken endTok, List<FrameExpression> mod, Attributes attrs, BlockStmt body)
      : base(tok, endTok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(mod != null);
      Mod = new Specification<FrameExpression>(mod, attrs);
      Body = body;
    }

    public override IEnumerable<Statement> SubStatements {
      get {
        if (Body != null) {
          yield return Body;
        }
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        foreach (var e in Attributes.SubExpressions(Mod.Attributes)) { yield return e; }
        foreach (var fe in Mod.Expressions) {
          yield return fe.E;
        }
      }
    }
  }

  public class CalcStmt : Statement
  {
    public abstract class CalcOp {
      /// <summary>
      /// Resulting operator "x op z" if "x this y" and "y other z".
      /// Returns null if this and other are incompatible.
      /// </summary>
      [Pure]
      public abstract CalcOp ResultOp(CalcOp other);

      /// <summary>
      /// Returns an expression "line0 this line1".
      /// </summary>
      [Pure]
      public abstract Expression StepExpr(Expression line0, Expression line1);
    }

    public class BinaryCalcOp : CalcOp {
      public readonly BinaryExpr.Opcode Op;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(ValidOp(Op));
      }

      /// <summary>
      /// Is op a valid calculation operator?
      /// </summary>
      [Pure]
      public static bool ValidOp(BinaryExpr.Opcode op) {
        return
             op == BinaryExpr.Opcode.Eq || op == BinaryExpr.Opcode.Neq
          || op == BinaryExpr.Opcode.Lt || op == BinaryExpr.Opcode.Le
          || op == BinaryExpr.Opcode.Gt || op == BinaryExpr.Opcode.Ge
          || LogicOp(op);
      }

      /// <summary>
      /// Is op a valid operator only for Boolean lines?
      /// </summary>
      [Pure]
      public static bool LogicOp(BinaryExpr.Opcode op) {
        return op == BinaryExpr.Opcode.Iff || op == BinaryExpr.Opcode.Imp || op == BinaryExpr.Opcode.Exp;
      }

      public BinaryCalcOp(BinaryExpr.Opcode op) {
        Contract.Requires(ValidOp(op));
        Op = op;
      }

      /// <summary>
      /// Does this subsume other (this . other == other . this == this)?
      /// </summary>
      private bool Subsumes(BinaryCalcOp other) {
        Contract.Requires(other != null);
        var op1 = Op;
        var op2 = other.Op;
        if (op1 == BinaryExpr.Opcode.Neq || op2 == BinaryExpr.Opcode.Neq)
          return op2 == BinaryExpr.Opcode.Eq;
        if (op1 == op2)
          return true;
        if (LogicOp(op1) || LogicOp(op2))
          return op2 == BinaryExpr.Opcode.Eq ||
            (op1 == BinaryExpr.Opcode.Imp && op2 == BinaryExpr.Opcode.Iff) ||
            (op1 == BinaryExpr.Opcode.Exp && op2 == BinaryExpr.Opcode.Iff) ||
            (op1 == BinaryExpr.Opcode.Eq && op2 == BinaryExpr.Opcode.Iff);
        return op2 == BinaryExpr.Opcode.Eq ||
          (op1 == BinaryExpr.Opcode.Lt && op2 == BinaryExpr.Opcode.Le) ||
          (op1 == BinaryExpr.Opcode.Gt && op2 == BinaryExpr.Opcode.Ge);
      }

      public override CalcOp ResultOp(CalcOp other) {
        if (other is BinaryCalcOp) {
          var o = (BinaryCalcOp) other;
          if (this.Subsumes(o)) {
            return this;
          } else if (o.Subsumes(this)) {
            return other;
          }
          return null;
        } else if (other is TernaryCalcOp) {
          return other.ResultOp(this);
        } else {
          Contract.Assert(false);
          throw new cce.UnreachableException();
        }
      }

      public override Expression StepExpr(Expression line0, Expression line1)
      {
        if (Op == BinaryExpr.Opcode.Exp) {
          // The order of operands is reversed so that it can be turned into implication during resolution
          return new BinaryExpr(line0.tok, Op, line1, line0);
        } else {
          return new BinaryExpr(line0.tok, Op, line0, line1);
        }
      }

      public override string ToString()
      {
        return BinaryExpr.OpcodeString(Op);
      }

    }

    public class TernaryCalcOp : CalcOp {
      public readonly Expression Index; // the only allowed ternary operator is ==#, so we only store the index

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(Index != null);
      }

      public TernaryCalcOp(Expression idx) {
        Contract.Requires(idx != null);
        Index = idx;
      }

      public override CalcOp ResultOp(CalcOp other) {
        if (other is BinaryCalcOp) {
          if (((BinaryCalcOp) other).Op == BinaryExpr.Opcode.Eq) {
            return this;
          }
          return null;
        } else if (other is TernaryCalcOp) {
          var a = Index;
          var b = ((TernaryCalcOp) other).Index;
          var minIndex = new ITEExpr(a.tok, false, new BinaryExpr(a.tok, BinaryExpr.Opcode.Le, a, b), a, b);
          return new TernaryCalcOp(minIndex); // ToDo: if we could compare expressions for syntactic equalty, we could use this here to optimize
        } else {
          Contract.Assert(false);
          throw new cce.UnreachableException();
        }
      }

      public override Expression StepExpr(Expression line0, Expression line1)
      {
        return new TernaryExpr(line0.tok, TernaryExpr.Opcode.PrefixEqOp, Index, line0, line1);
      }

      public override string ToString()
      {
        return "==#";
      }

    }

    public readonly List<Expression> Lines;    // Last line is dummy, in order to form a proper step with the dangling hint
    public readonly List<BlockStmt> Hints;     // Hints[i] comes after line i; block statement is used as a container for multiple sub-hints
    public readonly CalcOp UserSuppliedOp;     // may be null, if omitted by the user
    public CalcOp Op;                          // main operator of the calculation (either UserSuppliedOp or (after resolution) an inferred CalcOp)
    public readonly List<CalcOp/*?*/> StepOps; // StepOps[i] comes after line i
    public readonly List<Expression> Steps;    // expressions li op l<i + 1>, filled in during resolution (last step is dummy)
    public Expression Result;                  // expression l0 ResultOp ln, filled in during resolution

    public static readonly CalcOp DefaultOp = new BinaryCalcOp(BinaryExpr.Opcode.Eq);

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Lines != null);
      Contract.Invariant(cce.NonNullElements(Lines));
      Contract.Invariant(Hints != null);
      Contract.Invariant(cce.NonNullElements(Hints));
      Contract.Invariant(StepOps != null);
      Contract.Invariant(Steps != null);
      Contract.Invariant(cce.NonNullElements(Steps));
      Contract.Invariant(Hints.Count == Math.Max(Lines.Count - 1, 0));
      Contract.Invariant(StepOps.Count == Hints.Count);
    }

    public CalcStmt(IToken tok, IToken endTok, CalcOp userSuppliedOp, List<Expression> lines, List<BlockStmt> hints, List<CalcOp/*?*/> stepOps, Attributes attrs)
      : base(tok, endTok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(lines != null);
      Contract.Requires(hints != null);
      Contract.Requires(stepOps != null);
      Contract.Requires(cce.NonNullElements(lines));
      Contract.Requires(cce.NonNullElements(hints));
      Contract.Requires(hints.Count == Math.Max(lines.Count - 1, 0));
      Contract.Requires(stepOps.Count == hints.Count);
      this.UserSuppliedOp = userSuppliedOp;
      this.Lines = lines;
      this.Hints = hints;
      this.StepOps = stepOps;
      this.Steps = new List<Expression>();
      this.Result = null;
      this.Attributes = attrs;
    }

    public override IEnumerable<Statement> SubStatements
    {
      get {
        foreach (var h in Hints) {
          yield return h;
        }
      }
    }
    public override IEnumerable<Expression> SubExpressions
    {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        foreach (var e in Attributes.SubExpressions(Attributes)) { yield return e; }

        for (int i = 0; i < Lines.Count - 1; i++) {  // note, we skip the duplicated line at the end
          yield return Lines[i];
        }
        foreach (var calcop in AllCalcOps) {
          var o3 = calcop as TernaryCalcOp;
          if (o3 != null) {
            yield return o3.Index;
          }
        }
      }
    }

    IEnumerable<CalcOp> AllCalcOps {
      get {
        if (UserSuppliedOp != null) {
          yield return UserSuppliedOp;
        }
        foreach (var stepop in StepOps) {
          if (stepop != null) {
            yield return stepop;
          }
        }
      }
    }

    /// <summary>
    /// Left-hand side of a step expression.
    /// Note that Lhs(op.StepExpr(line0, line1)) != line0 when op is <==.
    /// </summary>
    public static Expression Lhs(Expression step)
    {
      Contract.Requires(step is BinaryExpr || step is TernaryExpr);
      if (step is BinaryExpr) {
        return ((BinaryExpr) step).E0;
      } else {
        return ((TernaryExpr) step).E1;
      }
    }

    /// <summary>
    /// Right-hand side of a step expression.
    /// Note that Rhs(op.StepExpr(line0, line1)) != line1 when op is REVERSE-IMPLICATION.
    /// </summary>
    public static Expression Rhs(Expression step)
    {
      Contract.Requires(step is BinaryExpr || step is TernaryExpr);
      if (step is BinaryExpr) {
        return ((BinaryExpr) step).E1;
      } else {
        return ((TernaryExpr) step).E2;
      }
    }
  }

  public class MatchStmt : Statement
  {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Source != null);
      Contract.Invariant(cce.NonNullElements(Cases));
      Contract.Invariant(cce.NonNullElements(MissingCases));
    }

    private Expression source;
    private List<MatchCaseStmt> cases;
    public readonly MatchingContext Context;
    public readonly List<DatatypeCtor> MissingCases = new List<DatatypeCtor>();  // filled in during resolution
    public readonly bool UsesOptionalBraces;
    public MatchStmt OrigUnresolved;  // the resolver makes this clone of the MatchStmt before it starts desugaring it
    public MatchStmt(IToken tok, IToken endTok, Expression source, [Captured] List<MatchCaseStmt> cases, bool usesOptionalBraces, MatchingContext context = null)
      : base(tok, endTok) {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(source != null);
      Contract.Requires(cce.NonNullElements(cases));
      this.source = source;
      this.cases = cases;
      this.UsesOptionalBraces = usesOptionalBraces;
      this.Context = context is null? new HoleCtx() : context;
    }
    public MatchStmt(IToken tok, IToken endTok, Expression source, [Captured] List<MatchCaseStmt> cases, bool usesOptionalBraces, Attributes attrs, MatchingContext context = null)
      : base(tok, endTok, attrs)
    {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      Contract.Requires(source != null);
      Contract.Requires(cce.NonNullElements(cases));
      this.source = source;
      this.cases = cases;
      this.UsesOptionalBraces = usesOptionalBraces;
      this.Context = context is null ? new HoleCtx() : context;
    }

    public Expression Source {
      get { return source; }
    }

    public List<MatchCaseStmt> Cases {
      get { return cases; }
    }

    // should only be used in desugar in resolve to change the cases of the matchexpr
    public void UpdateSource(Expression source) {
      this.source = source;
    }

    public void UpdateCases(List<MatchCaseStmt> cases) {
      this.cases = cases;
    }

    public override IEnumerable<Statement> SubStatements {
      get {
        foreach (var kase in cases) {
          foreach (var s in kase.Body) {
            yield return s;
          }
        }
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        yield return Source;
      }
    }
  }

  public class MatchCaseStmt : MatchCase
  {
    private List<Statement> body;
    public Attributes Attributes;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Body));
    }

    public MatchCaseStmt(IToken tok, DatatypeCtor ctor, [Captured] List<BoundVar> arguments, [Captured] List<Statement> body, Attributes attrs = null)
      : base(tok, ctor, arguments)
    {
      Contract.Requires(tok != null);
      Contract.Requires(ctor != null);
      Contract.Requires(cce.NonNullElements(arguments));
      Contract.Requires(cce.NonNullElements(body));
      this.body = body;
      this.Attributes = attrs;
    }

    public List<Statement> Body {
      get { return body; }
    }

    // should only be called by resolve to reset the body of the MatchCaseExpr
    public void UpdateBody(List<Statement> body) {
      this.body = body;
    }
  }

  /// <summary>
  /// The class represents several possible scenarios:
  /// * ...;
  ///   S == null
  /// * assert ...
  ///   ConditionOmitted == true
  /// * assume ...
  ///   ConditionOmitted == true
  /// * if ... { Stmt }
  ///   if ... { Stmt } else ElseStmt
  ///   ConditionOmitted == true
  /// * while ... invariant J;
  ///   ConditionOmitted == true && BodyOmitted == true
  /// * while ... invariant J; { Stmt }
  ///   ConditionOmitted == true && BodyOmitted == false
  /// * modify ...;
  ///   ConditionOmitted == true && BodyOmitted == false
  /// * modify ... { Stmt }
  ///   ConditionOmitted == true && BodyOmitted == false
  /// </summary>
  public class SkeletonStatement : Statement
  {
    public readonly Statement S;
    public bool ConditionOmitted { get { return ConditionEllipsis != null; } }
    public readonly IToken ConditionEllipsis;
    public bool BodyOmitted { get { return BodyEllipsis != null; } }
    public readonly IToken BodyEllipsis;
    public SkeletonStatement(IToken tok, IToken endTok)
      : base(tok, endTok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(endTok != null);
      S = null;
    }
    public SkeletonStatement(Statement s, IToken conditionEllipsis, IToken bodyEllipsis)
      : base(s.Tok, s.EndTok)
    {
      Contract.Requires(s != null);
      S = s;
      ConditionEllipsis = conditionEllipsis;
      BodyEllipsis = bodyEllipsis;
    }
    public override IEnumerable<Statement> SubStatements {
      get {
        // The SkeletonStatement is really a modification of its inner statement S.  Therefore,
        // we don't consider S to be a substatement.  Instead, the substatements of S are the
        // substatements of the SkeletonStatement.  In the case the SkeletonStatement modifies
        // S by omitting its body (which is true only for loops), there are no substatements.
        if (!BodyOmitted) {
          foreach (var s in S.SubStatements) {
            yield return s;
          }
        }
      }
    }
  }

  // ------------------------------------------------------------------------------------------------------

  public abstract class TokenWrapper : IToken
  {
    protected readonly IToken WrappedToken;
    protected TokenWrapper(IToken wrappedToken) {
      Contract.Requires(wrappedToken != null);
      WrappedToken = wrappedToken;
    }

    public int col {
      get { return WrappedToken.col; }
      set { throw new NotSupportedException(); }
    }
    public virtual string filename {
      get { return WrappedToken.filename; }
      set { throw new NotSupportedException(); }
    }
    public bool IsValid {
      get { return WrappedToken.IsValid; }
    }
    public int kind {
      get { return WrappedToken.kind; }
      set { throw new NotSupportedException(); }
    }
    public int line {
      get { return WrappedToken.line; }
      set { throw new NotSupportedException(); }
    }
    public int pos {
      get { return WrappedToken.pos; }
      set { throw new NotSupportedException(); }
    }
    public virtual string val {
      get { return WrappedToken.val; }
      set { throw new NotSupportedException(); }
    }
  }

  public class NestedToken : TokenWrapper
  {
    public NestedToken(IToken outer, IToken inner)
      : base(outer)
    {
      Contract.Requires(outer != null);
      Contract.Requires(inner != null);
      Inner = inner;
    }
    public IToken Outer { get { return WrappedToken; } }
    public readonly IToken Inner;
  }

  /// <summary>
  /// An IncludeToken is a wrapper that indicates that the function/method was
  /// declared in a file that was included. Any proof obligations from such an
  /// included file are to be ignored.
  /// </summary>
  public class IncludeToken : TokenWrapper
  {
    public Include Include;
    public IncludeToken(Include include, IToken wrappedToken)
      : base(wrappedToken) {
      Contract.Requires(wrappedToken != null);
      this.Include = include;
    }

    public override string val {
      get { return WrappedToken.val; }
      set { WrappedToken.val = value; }
    }
  }

  // ------------------------------------------------------------------------------------------------------
  [DebuggerDisplay("{Printer.ExprToString(this)}")]
  public abstract class Expression
  {
    public readonly IToken tok;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(tok != null);
    }

    [Pure]
    public bool WasResolved()
    {
      return Type != null;
    }

    public Expression Resolved {
      get {
        Contract.Requires(WasResolved());  // should be called only on resolved expressions; this approximates that precondition
        Expression r = this;
        while (true) {
          Contract.Assert(r.WasResolved());  // this.WasResolved() implies anything it reaches is also resolved
          var rr = r as ConcreteSyntaxExpression;
          if (rr == null) {
            return r;
          }
          r = rr.ResolvedExpression;
          if (r == null) {
            // for a NegationExpression, we're willing to return its non-ResolveExpression form (since it is filled in
            // during a resolution phase after type checking and we may be called here during type checking)
            return rr is NegationExpression ? rr : null;
          }
        }
      }
    }

    protected Type type;
    public Type Type {  // filled in during resolution
      get {
        Contract.Ensures(type != null || Contract.Result<Type>() == null);  // useful in conjunction with postcondition of constructor
        return type == null ? null : type.Normalize();
      }
      set {
        Contract.Requires(!WasResolved());  // set it only once
        Contract.Requires(value != null);

        //modifies type;
        type = value.Normalize();
      }
    }
    /// <summary>
    /// This method can be used when .Type has been found to be erroneous and its current value
    /// would be unexpected by the rest of the resolver. This method then sets .Type to a neutral
    /// value.
    /// </summary>
    public void ResetTypeAssignment() {
      Contract.Requires(WasResolved());
      type = new InferredTypeProxy();
    }
#if TEST_TYPE_SYNONYM_TRANSPARENCY
    public void DebugTest_ChangeType(Type ty) {
      Contract.Requires(WasResolved());  // we're here to set it again
      Contract.Requires(ty != null);
      type = ty;
    }
#endif

    public Expression(IToken tok) {
      Contract.Requires(tok != null);
      Contract.Ensures(type == null);  // we would have liked to have written Type==null, but that's not admissible or provable

      this.tok = tok;
    }

    /// <summary>
    /// Returns the non-null subexpressions of the Expression.  To be called after the expression has been resolved; this
    /// means, for example, that any concrete syntax that resolves to some other expression will return the subexpressions
    /// of the resolved expression.
    /// </summary>
    public virtual IEnumerable<Expression> SubExpressions {
      get { yield break; }
    }

    /// <summary>
    /// Returns the list of types that appear in this expression proper (that is, not including types that
    /// may appear in subexpressions). Types occurring in sub-statements of the expression are not included.
    /// To be called after the expression has been resolved.
    /// </summary>
    public virtual IEnumerable<Type> ComponentTypes {
      get { yield break; }
    }

    public virtual bool IsImplicit {
      get { return false; }
    }

    public static IEnumerable<Expression> Conjuncts(Expression expr) {
      Contract.Requires(expr != null);
      Contract.Requires(expr.Type.IsBoolType);
      Contract.Ensures(cce.NonNullElements(Contract.Result<IEnumerable<Expression>>()));

      expr = StripParens(expr);
      if (expr is UnaryOpExpr unary && unary.Op == UnaryOpExpr.Opcode.Not) {
        foreach (Expression e in Disjuncts(unary.E)) {
          yield return Expression.CreateNot(e.tok, e);
        }
        yield break;

      } else if (expr is BinaryExpr bin) {
        if (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.And) {
          foreach (Expression e in Conjuncts(bin.E0)) {
            yield return e;
          }
          foreach (Expression e in Conjuncts(bin.E1)) {
            yield return e;
          }
          yield break;
        }
      }

      yield return expr;
    }

    public static IEnumerable<Expression> Disjuncts(Expression expr) {
      Contract.Requires(expr != null);
      Contract.Requires(expr.Type.IsBoolType);
      Contract.Ensures(cce.NonNullElements(Contract.Result<IEnumerable<Expression>>()));

      expr = StripParens(expr);
      if (expr is UnaryOpExpr unary && unary.Op == UnaryOpExpr.Opcode.Not) {
        foreach (Expression e in Conjuncts(unary.E)) {
          yield return Expression.CreateNot(e.tok, e);
        }
        yield break;

      } else if (expr is BinaryExpr bin) {
        if (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Or) {
          foreach (Expression e in Conjuncts(bin.E0)) {
            yield return e;
          }
          foreach (Expression e in Conjuncts(bin.E1)) {
            yield return e;
          }
          yield break;
        } else if (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Imp) {
          foreach (Expression e in Conjuncts(bin.E0)) {
            yield return Expression.CreateNot(e.tok, e);
          }
          foreach (Expression e in Conjuncts(bin.E1)) {
            yield return e;
          }
          yield break;
        }
      }

      yield return expr;
    }

    /// <summary>
    /// Create a resolved expression of the form "e0 + e1"
    /// </summary>
    public static Expression CreateAdd(Expression e0, Expression e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(
        (e0.Type.IsNumericBased(Type.NumericPersuasion.Int) && e1.Type.IsNumericBased(Type.NumericPersuasion.Int)) ||
        (e0.Type.IsNumericBased(Type.NumericPersuasion.Real) && e1.Type.IsNumericBased(Type.NumericPersuasion.Real)));
      Contract.Ensures(Contract.Result<Expression>() != null);
      var s = new BinaryExpr(e0.tok, BinaryExpr.Opcode.Add, e0, e1);
      s.ResolvedOp = BinaryExpr.ResolvedOpcode.Add;  // resolve here
      s.Type = e0.Type.NormalizeExpand();  // resolve here
      return s;
    }

    /// <summary>
    /// Create a resolved expression of the form "e0 * e1"
    /// </summary>
    public static Expression CreateMul(Expression e0, Expression e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(
        (e0.Type.IsNumericBased(Type.NumericPersuasion.Int) && e1.Type.IsNumericBased(Type.NumericPersuasion.Int)) ||
        (e0.Type.IsNumericBased(Type.NumericPersuasion.Real) && e1.Type.IsNumericBased(Type.NumericPersuasion.Real)));
      Contract.Ensures(Contract.Result<Expression>() != null);
      var s = new BinaryExpr(e0.tok, BinaryExpr.Opcode.Mul, e0, e1);
      s.ResolvedOp = BinaryExpr.ResolvedOpcode.Mul;  // resolve here
      s.Type = e0.Type.NormalizeExpand();  // resolve here
      return s;
    }

    /// <summary>
    /// Create a resolved expression of the form "CVT(e0) - CVT(e1)", where "CVT" is either "int" (if
    /// e0.Type is an integer-based numeric type) or "real" (if e0.Type is a real-based numeric type).
    /// </summary>
    public static Expression CreateSubtract_TypeConvert(Expression e0, Expression e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(
        (e0.Type.IsNumericBased(Type.NumericPersuasion.Int) && e1.Type.IsNumericBased(Type.NumericPersuasion.Int)) ||
        (e0.Type.IsNumericBased(Type.NumericPersuasion.Real) && e1.Type.IsNumericBased(Type.NumericPersuasion.Real)) ||
        (e0.Type.IsBitVectorType && e1.Type.IsBitVectorType) ||
        (e0.Type.IsCharType && e1.Type.IsCharType));
      Contract.Ensures(Contract.Result<Expression>() != null);

      Type toType;
      if (e0.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
        toType = Type.Int;
      } else if (e0.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
        toType = Type.Real;
      } else {
        Contract.Assert(e0.Type.IsBitVectorType || e0.Type.IsCharType);
        toType = Type.Int; // convert char and bitvectors to int
      }
      e0 = CastIfNeeded(e0, toType);
      e1 = CastIfNeeded(e1, toType);
      return CreateSubtract(e0, e1);
    }

    private static Expression CastIfNeeded(Expression expr, Type toType) {
      if (!expr.Type.Equals(toType)) {
        var cast = new ConversionExpr(expr.tok, expr, toType);
        cast.Type = toType;
        return cast;
      } else {
        return expr;
      }
    }

    /// <summary>
    /// Create a resolved expression of the form "e0 - e1"
    /// </summary>
    public static Expression CreateSubtract(Expression e0, Expression e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e0.Type != null);
      Contract.Requires(e1 != null);
      Contract.Requires(e1.Type != null);
      Contract.Requires(
        (e0.Type.IsNumericBased(Type.NumericPersuasion.Int) && e1.Type.IsNumericBased(Type.NumericPersuasion.Int)) ||
        (e0.Type.IsNumericBased(Type.NumericPersuasion.Real) && e1.Type.IsNumericBased(Type.NumericPersuasion.Real)) ||
        (e0.Type.IsBigOrdinalType && e1.Type.IsBigOrdinalType));
      Contract.Ensures(Contract.Result<Expression>() != null);
      var s = new BinaryExpr(e0.tok, BinaryExpr.Opcode.Sub, e0, e1);
      s.ResolvedOp = BinaryExpr.ResolvedOpcode.Sub;  // resolve here
      s.Type = e0.Type.NormalizeExpand();  // resolve here (and it's important to remove any constraints)
      return s;
    }

    /// <summary>
    /// Create a resolved expression of the form "e0 - e1".
    /// Optimization: If either "e0" or "e1" is the literal denoting the empty set, then just return "e0".
    /// </summary>
    public static Expression CreateSetDifference(Expression e0, Expression e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e0.Type != null);
      Contract.Requires(e1 != null);
      Contract.Requires(e1.Type != null);
      Contract.Requires(e0.Type.AsSetType != null && e1.Type.AsSetType != null);
      Contract.Ensures(Contract.Result<Expression>() != null);
      if (LiteralExpr.IsEmptySet(e0) || LiteralExpr.IsEmptySet(e1)) {
        return e0;
      }
      var s = new BinaryExpr(e0.tok, BinaryExpr.Opcode.Sub, e0, e1) {
        ResolvedOp = BinaryExpr.ResolvedOpcode.SetDifference,
        Type = e0.Type.NormalizeExpand() // important to remove any constraints
      };
      return s;
    }

    /// <summary>
    /// Create a resolved expression of the form "e0 - e1".
    /// Optimization: If either "e0" or "e1" is the literal denoting the empty multiset, then just return "e0".
    /// </summary>
    public static Expression CreateMultisetDifference(Expression e0, Expression e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e0.Type != null);
      Contract.Requires(e1 != null);
      Contract.Requires(e1.Type != null);
      Contract.Requires(e0.Type.AsMultiSetType != null && e1.Type.AsMultiSetType != null);
      Contract.Ensures(Contract.Result<Expression>() != null);
      if (LiteralExpr.IsEmptyMultiset(e0) || LiteralExpr.IsEmptyMultiset(e1)) {
        return e0;
      }
      var s = new BinaryExpr(e0.tok, BinaryExpr.Opcode.Sub, e0, e1) {
        ResolvedOp = BinaryExpr.ResolvedOpcode.MultiSetDifference,
        Type = e0.Type.NormalizeExpand() // important to remove any constraints
      };
      return s;
    }

    /// <summary>
    /// Create a resolved expression of the form "|e|"
    /// </summary>
    public static Expression CreateCardinality(Expression e, BuiltIns builtIns) {
      Contract.Requires(e != null);
      Contract.Requires(e.Type != null);
      Contract.Requires(e.Type.AsSetType != null || e.Type.AsMultiSetType != null || e.Type.AsSeqType != null);
      Contract.Ensures(Contract.Result<Expression>() != null);
      var s = new UnaryOpExpr(e.tok, UnaryOpExpr.Opcode.Cardinality, e) {
        Type = builtIns.Nat()
      };
      return s;
    }

    /// <summary>
    /// Create a resolved expression of the form "e + n"
    /// </summary>
    public static Expression CreateIncrement(Expression e, int n) {
      Contract.Requires(e != null);
      Contract.Requires(e.Type != null);
      Contract.Requires(e.Type.IsNumericBased(Type.NumericPersuasion.Int));
      Contract.Requires(0 <= n);
      Contract.Ensures(Contract.Result<Expression>() != null);
      if (n == 0) {
        return e;
      }
      var nn = CreateIntLiteral(e.tok, n);
      return CreateAdd(e, nn);
    }

    /// <summary>
    /// Create a resolved expression of the form "e - n"
    /// </summary>
    public static Expression CreateDecrement(Expression e, int n) {
      Contract.Requires(e != null);
      Contract.Requires(e.Type.IsNumericBased(Type.NumericPersuasion.Int));
      Contract.Requires(0 <= n);
      Contract.Ensures(Contract.Result<Expression>() != null);
      if (n == 0) {
        return e;
      }
      var nn = CreateIntLiteral(e.tok, n);
      return CreateSubtract(e, nn);
    }

    /// <summary>
    /// Create a resolved expression of the form "n"
    /// </summary>
    public static Expression CreateIntLiteral(IToken tok, int n) {
      Contract.Requires(tok != null);
      Contract.Requires(n != int.MinValue);
      if (0 <= n) {
        var nn = new LiteralExpr(tok, n);
        nn.Type = Type.Int;
        return nn;
      } else {
        return CreateDecrement(CreateIntLiteral(tok, 0), -n);
      }
    }

    /// <summary>
    /// Create a resolved expression of the form "x"
    /// </summary>
    public static Expression CreateRealLiteral(IToken tok, BaseTypes.BigDec x) {
      Contract.Requires(tok != null);
      var nn = new LiteralExpr(tok, x);
      nn.Type = Type.Real;
      return nn;
    }

    /// <summary>
    /// Create a resolved expression of the form "n", for either type "int" or type "ORDINAL".
    /// </summary>
    public static Expression CreateNatLiteral(IToken tok, int n, Type ty) {
      Contract.Requires(tok != null);
      Contract.Requires(0 <= n);
      Contract.Requires(ty.IsNumericBased(Type.NumericPersuasion.Int) || ty is BigOrdinalType);
      var nn = new LiteralExpr(tok, n);
      nn.Type = ty;
      return nn;
    }

    /// <summary>
    /// Create a resolved expression for a bool b
    /// </summary>
    public static LiteralExpr CreateBoolLiteral(IToken tok, bool b) {
      Contract.Requires(tok != null);
      var lit = new LiteralExpr(tok, b);
      lit.Type = Type.Bool;  // resolve here
      return lit;
    }

    /// <summary>
    /// Returns "expr", but with all outer layers of parentheses removed.
    /// This method can be called before resolution.
    /// </summary>
    public static Expression StripParens(Expression expr) {
      while (true) {
        var e = expr as ParensExpression;
        if (e == null) {
          return expr;
        }
        expr = e.E;
      }
    }

    public static ThisExpr AsThis(Expression expr) {
      Contract.Requires(expr != null);
      return StripParens(expr) as ThisExpr;
    }

    /// <summary>
    /// If "expr" denotes a boolean literal "b", then return "true" and set "value" to "b".
    /// Otherwise, return "false" (and the value of "value" should not be used by the caller).
    /// This method can be called before resolution.
    /// </summary>
    public static bool IsBoolLiteral(Expression expr, out bool value) {
      Contract.Requires(expr != null);
      var e = StripParens(expr) as LiteralExpr;
      if (e != null && e.Value is bool) {
        value = (bool)e.Value;
        return true;
      } else {
        value = false;  // to please compiler
        return false;
      }
    }

    /// <summary>
    /// Returns "true" if "expr" denotes the empty set (for "iset", "set", or "multiset").
    /// This method can be called before resolution.
    /// </summary>
    public static bool IsEmptySetOrMultiset(Expression expr) {
      Contract.Requires(expr != null);
      expr = StripParens(expr);
      return (expr is SetDisplayExpr && ((SetDisplayExpr)expr).Elements.Count == 0) ||
        (expr is MultiSetDisplayExpr && ((MultiSetDisplayExpr)expr).Elements.Count == 0);
    }

    public static Expression CreateNot(IToken tok, Expression e) {
      Contract.Requires(tok != null);
      Contract.Requires(e != null && e.Type != null && e.Type.IsBoolType);

      e = StripParens(e);
      if (e is UnaryOpExpr unary && unary.Op == UnaryOpExpr.Opcode.Not) {
        return unary.E;
      }

      if (e is BinaryExpr bin) {
        var negatedOp = BinaryExpr.ResolvedOpcode.Add; // let "Add" stand for "no negated operator"
        switch (bin.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.EqCommon:
            negatedOp = BinaryExpr.ResolvedOpcode.NeqCommon;
            break;
          case BinaryExpr.ResolvedOpcode.SetEq:
            negatedOp = BinaryExpr.ResolvedOpcode.SetNeq;
            break;
          case BinaryExpr.ResolvedOpcode.MultiSetEq:
            negatedOp = BinaryExpr.ResolvedOpcode.MultiSetNeq;
            break;
          case BinaryExpr.ResolvedOpcode.SeqEq:
            negatedOp = BinaryExpr.ResolvedOpcode.SeqNeq;
            break;
          case BinaryExpr.ResolvedOpcode.MapEq:
            negatedOp = BinaryExpr.ResolvedOpcode.MapNeq;
            break;
          case BinaryExpr.ResolvedOpcode.NeqCommon:
            negatedOp = BinaryExpr.ResolvedOpcode.EqCommon;
            break;
          case BinaryExpr.ResolvedOpcode.SetNeq:
            negatedOp = BinaryExpr.ResolvedOpcode.SetEq;
            break;
          case BinaryExpr.ResolvedOpcode.MultiSetNeq:
            negatedOp = BinaryExpr.ResolvedOpcode.MultiSetEq;
            break;
          case BinaryExpr.ResolvedOpcode.SeqNeq:
            negatedOp = BinaryExpr.ResolvedOpcode.SeqEq;
            break;
          case BinaryExpr.ResolvedOpcode.MapNeq:
            negatedOp = BinaryExpr.ResolvedOpcode.MapEq;
            break;
          default:
            break;
        }
        if (negatedOp != BinaryExpr.ResolvedOpcode.Add) {
          return new BinaryExpr(bin.tok, BinaryExpr.ResolvedOp2SyntacticOp(negatedOp), bin.E0, bin.E1) {
            ResolvedOp = negatedOp,
            Type = bin.Type
          };
        }
      }

      return new UnaryOpExpr(tok, UnaryOpExpr.Opcode.Not, e) {
        Type = Type.Bool
      };
    }

    /// <summary>
    /// Create a resolved expression of the form "e0 LESS e1"
    /// Works for integers, reals, bitvectors, chars, and ORDINALs.
    /// </summary>
    public static Expression CreateLess(Expression e0, Expression e1) {
      Contract.Requires(e0 != null && e0.Type != null);
      Contract.Requires(e1 != null && e1.Type != null);
      Contract.Requires(
        (e0.Type.IsNumericBased(Type.NumericPersuasion.Int) && e1.Type.IsNumericBased(Type.NumericPersuasion.Int)) ||
        (e0.Type.IsNumericBased(Type.NumericPersuasion.Real) && e1.Type.IsNumericBased(Type.NumericPersuasion.Real)) ||
        (e0.Type.IsBitVectorType && e1.Type.IsBitVectorType) ||
        (e0.Type.IsCharType && e1.Type.IsCharType) ||
        (e0.Type.IsBigOrdinalType && e1.Type.IsBigOrdinalType));
      Contract.Ensures(Contract.Result<Expression>() != null);
      return new BinaryExpr(e0.tok, BinaryExpr.Opcode.Lt, e0, e1) {
        ResolvedOp = e0.Type.IsCharType ? BinaryExpr.ResolvedOpcode.LtChar : BinaryExpr.ResolvedOpcode.Lt,
        Type = Type.Bool
      };
    }

    /// <summary>
    /// Create a resolved expression of the form "e0 ATMOST e1".
    /// Works for integers, reals, bitvectors, chars, and ORDINALs.
    /// </summary>
    public static Expression CreateAtMost(Expression e0, Expression e1) {
      Contract.Requires(e0 != null && e0.Type != null);
      Contract.Requires(e1 != null && e1.Type != null);
      Contract.Requires(
        (e0.Type.IsNumericBased(Type.NumericPersuasion.Int) && e1.Type.IsNumericBased(Type.NumericPersuasion.Int)) ||
        (e0.Type.IsNumericBased(Type.NumericPersuasion.Real) && e1.Type.IsNumericBased(Type.NumericPersuasion.Real)) ||
        (e0.Type.IsBitVectorType && e1.Type.IsBitVectorType) ||
        (e0.Type.IsCharType && e1.Type.IsCharType) ||
        (e0.Type.IsBigOrdinalType && e1.Type.IsBigOrdinalType));
      Contract.Ensures(Contract.Result<Expression>() != null);
      return new BinaryExpr(e0.tok, BinaryExpr.Opcode.Le, e0, e1) {
        ResolvedOp = e0.Type.IsCharType ? BinaryExpr.ResolvedOpcode.LeChar : BinaryExpr.ResolvedOpcode.Le,
        Type = Type.Bool
      };
    }

    public static Expression CreateEq(Expression e0, Expression e1, Type ty) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(ty != null);
      var eq = new BinaryExpr(e0.tok, BinaryExpr.Opcode.Eq, e0, e1);
      if (ty is SetType) {
        eq.ResolvedOp = BinaryExpr.ResolvedOpcode.SetEq;
      } else if (ty is SeqType) {
        eq.ResolvedOp = BinaryExpr.ResolvedOpcode.SeqEq;
      } else if (ty is MultiSetType) {
        eq.ResolvedOp = BinaryExpr.ResolvedOpcode.MultiSetEq;
      } else if (ty is MapType) {
        eq.ResolvedOp = BinaryExpr.ResolvedOpcode.MapEq;
      } else {
        eq.ResolvedOp = BinaryExpr.ResolvedOpcode.EqCommon;
      }
      eq.type = Type.Bool;
      return eq;
    }

    /// <summary>
    /// Create a resolved expression of the form "e0 && e1"
    /// </summary>
    public static Expression CreateAnd(Expression a, Expression b, bool allowSimplification = true) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Requires(a.Type.IsBoolType && b.Type.IsBoolType);
      Contract.Ensures(Contract.Result<Expression>() != null);
      if (allowSimplification && LiteralExpr.IsTrue(a)) {
        return b;
      } else if (allowSimplification && LiteralExpr.IsTrue(b)) {
        return a;
      } else {
        var and = new BinaryExpr(a.tok, BinaryExpr.Opcode.And, a, b);
        and.ResolvedOp = BinaryExpr.ResolvedOpcode.And;  // resolve here
        and.Type = Type.Bool;  // resolve here
        return and;
      }
    }

    /// <summary>
    /// Create a resolved expression of the form "e0 ==> e1"
    /// </summary>
    public static Expression CreateImplies(Expression a, Expression b, bool allowSimplification = true) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Requires(a.Type.IsBoolType && b.Type.IsBoolType);
      Contract.Ensures(Contract.Result<Expression>() != null);
      if (allowSimplification && (LiteralExpr.IsTrue(a) || LiteralExpr.IsTrue(b))) {
        return b;
      } else {
        var imp = new BinaryExpr(a.tok, BinaryExpr.Opcode.Imp, a, b);
        imp.ResolvedOp = BinaryExpr.ResolvedOpcode.Imp;  // resolve here
        imp.Type = Type.Bool;  // resolve here
        return imp;
      }
    }

    /// <summary>
    /// Create a resolved expression of the form "e0 || e1"
    /// </summary>
    public static Expression CreateOr(Expression a, Expression b, bool allowSimplification = true) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Requires(a.Type.IsBoolType && b.Type.IsBoolType);
      Contract.Ensures(Contract.Result<Expression>() != null);
      if (allowSimplification && LiteralExpr.IsTrue(a)) {
        return a;
      } else if (allowSimplification && LiteralExpr.IsTrue(b)) {
        return b;
      } else {
        var or = new BinaryExpr(a.tok, BinaryExpr.Opcode.Or, a, b);
        or.ResolvedOp = BinaryExpr.ResolvedOpcode.Or;  // resolve here
        or.Type = Type.Bool;  // resolve here
        return or;
      }
    }

    /// <summary>
    /// Create a resolved expression of the form "if test then e0 else e1"
    /// </summary>
    public static Expression CreateITE(Expression test, Expression e0, Expression e1) {
      Contract.Requires(test != null);
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(test.Type.IsBoolType && e0.Type.Equals(e1.Type));
      Contract.Ensures(Contract.Result<Expression>() != null);
      var ite = new ITEExpr(test.tok, false, test, e0, e1);
      ite.Type = e0.type;  // resolve here
      return ite;
    }

    /// <summary>
    /// Create a resolved case expression for a match expression
    /// </summary>
    public static MatchCaseExpr CreateMatchCase(MatchCaseExpr old_case, Expression new_body) {
      Contract.Requires(old_case != null);
      Contract.Requires(new_body != null);
      Contract.Ensures(Contract.Result<MatchCaseExpr>() != null);

      ResolvedCloner cloner = new ResolvedCloner();
      var newVars = old_case.Arguments.ConvertAll(cloner.CloneBoundVar);
      new_body = VarSubstituter(old_case.Arguments.ConvertAll<NonglobalVariable>(x=>(NonglobalVariable)x), newVars, new_body);

      var new_case = new MatchCaseExpr(old_case.tok, old_case.Ctor, newVars, new_body, old_case.Attributes);

      new_case.Ctor = old_case.Ctor; // resolve here
      return new_case;
    }

    /// <summary>
    /// Create a match expression with a resolved type
    /// </summary>
    public static Expression CreateMatch(IToken tok, Expression src, List<MatchCaseExpr> cases, Type type) {
      MatchExpr e = new MatchExpr(tok, src, cases, false);
      e.Type = type;  // resolve here

      return e;
    }

    /// <summary>
    /// Create a let expression with a resolved type and fresh variables
    /// </summary>
    public static Expression CreateLet(IToken tok, List<CasePattern<BoundVar>> LHSs, List<Expression> RHSs, Expression body, bool exact) {
      Contract.Requires(tok  != null);
      Contract.Requires(LHSs != null && RHSs != null);
      Contract.Requires(LHSs.Count == RHSs.Count);
      Contract.Requires(body != null);

      ResolvedCloner cloner = new ResolvedCloner();
      var newLHSs = LHSs.ConvertAll(cloner.CloneCasePattern);

      var oldVars = new List<BoundVar>();
      LHSs.Iter(p => oldVars.AddRange(p.Vars));
      var newVars = new List<BoundVar>();
      newLHSs.Iter(p => newVars.AddRange(p.Vars));
      body = VarSubstituter(oldVars.ConvertAll<NonglobalVariable>(x => (NonglobalVariable)x), newVars, body);

      var let = new LetExpr(tok, newLHSs, RHSs, body, exact);
      let.Type = body.Type;  // resolve here
      return let;
    }

    /// <summary>
    /// Create a quantifier expression with a resolved type and fresh variables
    /// Optionally replace the old body with the supplied argument
    /// </summary>
    public static Expression CreateQuantifier(QuantifierExpr expr, bool forall,  Expression body = null) {
      //(IToken tok, List<BoundVar> vars, Expression range, Expression body, Attributes attribs, Qu) {
      Contract.Requires(expr != null);

      ResolvedCloner cloner = new ResolvedCloner();
      var newVars = expr.BoundVars.ConvertAll(cloner.CloneBoundVar);

      if (body == null) {
        body = expr.Term;
      }

      body = VarSubstituter(expr.BoundVars.ConvertAll<NonglobalVariable>(x=>(NonglobalVariable)x), newVars, body);

      QuantifierExpr q;
      if (forall) {
        q = new ForallExpr(expr.tok, new List<TypeParameter>(), newVars, expr.Range, body, expr.Attributes);
      } else {
        q = new ExistsExpr(expr.tok, new List<TypeParameter>(), newVars, expr.Range, body, expr.Attributes);
      }
      q.Type = Type.Bool;

      return q;
    }

    /// <summary>
    /// Create a resolved IdentifierExpr (whose token is that of the variable)
    /// </summary>
    public static Expression CreateIdentExpr(IVariable v) {
      Contract.Requires(v != null);
      var e = new IdentifierExpr(v.Tok, v.Name);
      e.Var = v;  // resolve here
      e.type = v.Type;  // resolve here
      return e;
    }

    public static Expression VarSubstituter(List<NonglobalVariable> oldVars, List<BoundVar> newVars, Expression e, Dictionary<TypeParameter, Type> typeMap=null) {
      Contract.Requires(oldVars != null && newVars != null);
      Contract.Requires(oldVars.Count == newVars.Count);

      Dictionary<IVariable, Expression/*!*/> substMap = new Dictionary<IVariable, Expression>();
      if (typeMap == null) {
        typeMap = new Dictionary<TypeParameter, Type>();
      }

      for (int i = 0; i < oldVars.Count; i++) {
        var id = new IdentifierExpr(newVars[i].tok, newVars[i].Name);
        id.Var = newVars[i];    // Resolve here manually
        id.Type = newVars[i].Type;  // Resolve here manually
        substMap.Add(oldVars[i], id);
      }

      Substituter sub = new Substituter(null, substMap, typeMap);
      return sub.Substitute(e);
    }

    /// <summary>
    /// Returns the string literal underlying an actual string literal (not as a sequence display of characters)
    /// </summary>
    /// <returns></returns>
    public string AsStringLiteral() {
      var le = this as StringLiteralExpr;
      return le == null ? null : le.Value as string;
    }
  }

  /// <summary>
  /// Instances of this class are introduced during resolution to indicate that a static method or function has
  /// been invoked without specifying a receiver (that is, by just giving the name of the enclosing class).
  /// </summary>
  public class StaticReceiverExpr : LiteralExpr
  {
    public readonly Type UnresolvedType;
    private bool Implicit;
    public Expression OriginalResolved;

    public StaticReceiverExpr(IToken tok, Type t, bool isImplicit)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(t != null);
      UnresolvedType = t;
      Implicit = isImplicit;
      OriginalResolved = null;
    }

    /// <summary>
    /// Constructs a resolved LiteralExpr representing the fictitious static-receiver literal whose type is
    /// "cl" parameterized by the type arguments of "cl" itself.
    /// </summary>
    public StaticReceiverExpr(IToken tok, TopLevelDeclWithMembers cl, bool isImplicit)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(cl != null);
      var typeArgs = cl.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp));
      Type = new UserDefinedType(tok, cl is ClassDecl klass && klass.IsDefaultClass ? cl.Name : cl.Name + "?", cl, typeArgs);
      UnresolvedType = Type;
      Implicit = isImplicit;
    }

    /// <summary>
    /// Constructs a resolved LiteralExpr representing the fictitious literal whose type is
    /// "cl" parameterized according to the type arguments to "t".  It is assumed that "t" denotes
    /// a class or trait that (possibly reflexively or transitively) extends "cl".
    /// Examples:
    /// * If "t" denotes "C(G)" and "cl" denotes "C", then the type of the StaticReceiverExpr
    ///   will be "C(G)".
    /// * Suppose "C" is a class that extends a trait "T"; then, if "t" denotes "C" and "cl" denotes
    ///   "T", then the type of the StaticReceiverExpr will be "T".
    /// * Suppose "C(X)" is a class that extends "T(f(X))", and that "T(Y)" is
    ///   a trait that in turn extends trait "W(g(Y))".  If "t" denotes type "C(G)" and "cl" denotes "W",
    ///   then type of the StaticReceiverExpr will be "T(g(f(G)))".
    /// </summary>
    public StaticReceiverExpr(IToken tok, UserDefinedType t, TopLevelDeclWithMembers cl, bool isImplicit, Expression lhs = null)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(t.ResolvedClass != null);
      Contract.Requires(cl != null);
      var top = t.AsTopLevelTypeWithMembersBypassInternalSynonym;
      if (top != cl) {
        Contract.Assert(top != null);
        var clArgsInTermsOfTFormals = cl.TypeArgs.ConvertAll(tp => top.ParentFormalTypeParametersToActuals[tp]);
        var subst = Resolver.TypeSubstitutionMap(top.TypeArgs, t.TypeArgs);
        var typeArgs = clArgsInTermsOfTFormals.ConvertAll(ty => Resolver.SubstType(ty, subst));
        Type = new UserDefinedType(tok, cl.Name, cl, typeArgs);
      } else if (t.Name != cl.Name) {  // t may be using the name "C?", and we'd prefer it read "C"
        Type = new UserDefinedType(tok, cl.Name, cl, t.TypeArgs);
      } else {
        Type = t;
      }
      UnresolvedType = Type;
      Implicit = isImplicit;
      OriginalResolved = lhs;
    }

    public override bool IsImplicit {
      get { return Implicit; }
    }
  }

  public class LiteralExpr : Expression {
    /// <summary>
    /// One of the following:
    ///   * 'null' for the 'null' literal (a special case of which is the subclass StaticReceiverExpr)
    ///   * a bool for a bool literal
    ///   * a BigInteger for int literal
    ///   * a BaseTypes.BigDec for a (rational) real literal
    ///   * a string for a char literal
    ///     This case always uses the subclass CharLiteralExpr.
    ///     Note, a string is stored to keep any escape sequence, since this simplifies printing of the character
    ///     literal, both when pretty printed as a Dafny expression and when being compiled into C# code.  The
    ///     parser checks the validity of any escape sequence and the verifier deals with turning such into a
    ///     single character value.
    ///   * a string for a string literal
    ///     This case always uses the subclass StringLiteralExpr.
    ///     Note, the string is stored with all escapes as characters.  For example, the input string "hello\n" is
    ///     stored in a LiteralExpr has being 7 characters long, whereas the Dafny (and C#) length of this string is 6.
    ///     This simplifies printing of the string, both when pretty printed as a Dafny expression and when being
    ///     compiled into C# code.  The parser checks the validity of the escape sequences and the verifier deals
    ///     with turning them into single characters.
    /// </summary>
    public readonly object Value;

    [Pure]
    public static bool IsTrue(Expression e) {
      Contract.Requires(e != null);
      if (e is LiteralExpr) {
        LiteralExpr le = (LiteralExpr)e;
        return le.Value is bool && (bool)le.Value;
      } else {
        return false;
      }
    }

    public static bool IsEmptySet(Expression e) {
      Contract.Requires(e != null);
      return StripParens(e) is SetDisplayExpr display && display.Elements.Count == 0;
    }

    public static bool IsEmptyMultiset(Expression e) {
      Contract.Requires(e != null);
      return StripParens(e) is MultiSetDisplayExpr display && display.Elements.Count == 0;
    }

    public static bool IsEmptySequence(Expression e) {
      Contract.Requires(e != null);
      return StripParens(e) is SeqDisplayExpr display && display.Elements.Count == 0;
    }

    public LiteralExpr(IToken tok)
      : base(tok) {  // represents the Dafny literal "null"
      Contract.Requires(tok != null);
      this.Value = null;
    }

    public LiteralExpr(IToken tok, BigInteger n)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(0 <= n.Sign);
      this.Value = n;
    }

    public LiteralExpr(IToken tok, BaseTypes.BigDec n)
      : base(tok) {
      Contract.Requires(0 <= n.Mantissa.Sign);
      Contract.Requires(tok != null);
      this.Value = n;
    }

    public LiteralExpr(IToken tok, int n)
      :base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(0 <= n);
      this.Value = new BigInteger(n);
    }

    public LiteralExpr(IToken tok, bool b)
      : base(tok) {
      Contract.Requires(tok != null);
      this.Value = b;
    }

    /// <summary>
    /// This constructor is to be used only with the StringLiteralExpr and CharLiteralExpr subclasses, for
    /// two reasons:  both of these literals store a string in .Value, and string literals also carry an
    /// additional field.
    /// </summary>
    protected LiteralExpr(IToken tok, string s)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(s != null);
      this.Value = s;
    }
  }

  public class CharLiteralExpr : LiteralExpr
  {
    public CharLiteralExpr(IToken tok, string s)
      : base(tok, s) {
      Contract.Requires(s != null);
    }
  }

  public class StringLiteralExpr : LiteralExpr
  {
    public readonly bool IsVerbatim;
    public StringLiteralExpr(IToken tok, string s, bool isVerbatim)
      : base(tok, s) {
      Contract.Requires(s != null);
      IsVerbatim = isVerbatim;
    }
  }

  public class DatatypeValue : Expression {
    public readonly string DatatypeName;
    public readonly string MemberName;
    public readonly ActualBindings Bindings;
    public List<Expression> Arguments => Bindings.Arguments;
    public DatatypeCtor Ctor;  // filled in by resolution
    public List<Type> InferredTypeArgs = new List<Type>();  // filled in by resolution
    public bool IsCoCall;  // filled in by resolution
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(DatatypeName != null);
      Contract.Invariant(MemberName != null);
      Contract.Invariant(cce.NonNullElements(Arguments));
      Contract.Invariant(cce.NonNullElements(InferredTypeArgs));
      Contract.Invariant(Ctor == null || InferredTypeArgs.Count == Ctor.EnclosingDatatype.TypeArgs.Count);
    }

    public DatatypeValue(IToken tok, string datatypeName, string memberName, [Captured] List<ActualBinding> arguments)
      : base(tok) {
      Contract.Requires(cce.NonNullElements(arguments));
      Contract.Requires(tok != null);
      Contract.Requires(datatypeName != null);
      Contract.Requires(memberName != null);
      this.DatatypeName = datatypeName;
      this.MemberName = memberName;
      this.Bindings = new ActualBindings(arguments);
    }

    /// <summary>
    /// This constructor is intended to be used when constructing a resolved DatatypeValue. The "args" are expected
    /// to be already resolved, and are all given positionally.
    /// </summary>
    public DatatypeValue(IToken tok, string datatypeName, string memberName, List<Expression> arguments)
      : this(tok, datatypeName, memberName, arguments.ConvertAll(e => new ActualBinding(null, e))) {
      Bindings.AcceptArgumentExpressionsAsExactParameterList();
    }

    public override IEnumerable<Expression> SubExpressions {
      get { return Arguments; }
    }
  }

  public class ThisExpr : Expression {
    public ThisExpr(IToken tok)
      : base(tok) {
      Contract.Requires(tok != null);
    }

    /// <summary>
    /// This constructor creates a ThisExpr and sets its Type field to denote the receiver type
    /// of member "m". This constructor is intended to be used by post-resolution code that needs
    /// to obtain a Dafny "this" expression.
    /// </summary>
    public ThisExpr(MemberDecl m)
      : base(m.tok) {
      Contract.Requires(m != null);
      Contract.Requires(m.tok != null);
      Contract.Requires(m.EnclosingClass != null);
      Contract.Requires(!m.IsStatic);
      Type = Resolver.GetReceiverType(m.tok, m);
    }

    /// <summary>
    /// This constructor creates a ThisExpr and sets its Type field to denote the receiver type
    /// of member "m". This constructor is intended to be used by post-resolution code that needs
    /// to obtain a Dafny "this" expression.
    /// </summary>
    public ThisExpr(TopLevelDeclWithMembers cl)
      : base(cl.tok) {
      Contract.Requires(cl != null);
      Contract.Requires(cl.tok != null);
      Type = Resolver.GetThisType(cl.tok, cl);
    }
  }
  public class ExpressionPair {
    public Expression A, B;
    public ExpressionPair(Expression a, Expression b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      A = a;
      B = b;
    }
  }

  public class ImplicitThisExpr : ThisExpr {
    public ImplicitThisExpr(IToken tok)
      : base(tok) {
      Contract.Requires(tok != null);
    }

    public override bool IsImplicit {
      get { return true; }
    }
  }

  /// <summary>
  /// An ImplicitThisExpr_ConstructorCall is used in the .InitCall of a TypeRhs,
  /// which has a need for a "throw-away receiver".  Using a different type
  /// gives a way to distinguish this receiver from other receivers, which
  /// plays a role in checking the restrictions on divided block statements.
  /// </summary>
  public class ImplicitThisExpr_ConstructorCall : ImplicitThisExpr
  {
    public ImplicitThisExpr_ConstructorCall(IToken tok)
      : base(tok) {
      Contract.Requires(tok != null);
    }
  }

  public class IdentifierExpr : Expression
  {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Name != null);
    }

    public readonly string Name;
    public IVariable Var;  // filled in by resolution

    public IdentifierExpr(IToken tok, string name)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Name = name;
    }
    /// <summary>
    /// Constructs a resolved IdentifierExpr.
    /// </summary>
    public IdentifierExpr(IToken tok, IVariable v)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(v != null);
      Name = v.Name;
      Var = v;
      Type = v.Type;
    }
  }

  /// <summary>
  /// If an "AutoGhostIdentifierExpr" is used as the out-parameter of a ghost method or
  /// a method with a ghost parameter, resolution will change the .Var's .IsGhost to true
  /// automatically.  This class is intended to be used only as a communicate between the
  /// parser and parts of the resolver.
  /// </summary>
  public class AutoGhostIdentifierExpr : IdentifierExpr
  {
    public AutoGhostIdentifierExpr(IToken tok, string name)
      : base(tok, name) { }
  }

  /// <summary>
  /// This class is used only inside the resolver itself. It gets hung in the AST in uncompleted name segments.
  /// </summary>
  class Resolver_IdentifierExpr : Expression
  {
    public readonly TopLevelDecl Decl;
    public readonly List<Type> TypeArgs;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Decl != null);
      Contract.Invariant(TypeArgs != null);
      Contract.Invariant(TypeArgs.Count == Decl.TypeArgs.Count);
      Contract.Invariant(Type is ResolverType_Module || Type is ResolverType_Type);
    }

    public abstract class ResolverType : Type
    {
    }
    public class ResolverType_Module : ResolverType
    {
      [Pure]
      public override string TypeName(ModuleDefinition context, bool parseAble) {
        Contract.Assert(parseAble == false);
        return "#module";
      }
      public override bool Equals(Type that, bool keepConstraints = false) {
        return that.NormalizeExpand(keepConstraints) is ResolverType_Module;
      }
    }
    public class ResolverType_Type : ResolverType {
      [Pure]
      public override string TypeName(ModuleDefinition context, bool parseAble) {
        Contract.Assert(parseAble == false);
        return "#type";
      }
      public override bool Equals(Type that, bool keepConstraints = false) {
        return that.NormalizeExpand(keepConstraints) is ResolverType_Type;
      }
    }

    public Resolver_IdentifierExpr(IToken tok, TopLevelDecl decl, List<Type> typeArgs)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(decl != null);
      Contract.Requires(typeArgs != null && typeArgs.Count == decl.TypeArgs.Count);
      Decl = decl;
      TypeArgs = typeArgs;
      Type = decl is ModuleDecl ? (Type)new ResolverType_Module() : new ResolverType_Type();
    }
    public Resolver_IdentifierExpr(IToken tok, TypeParameter tp)
      : this(tok, tp, new List<Type>()) {
      Contract.Requires(tok != null);
      Contract.Requires(tp != null);
    }
  }

  public abstract class DisplayExpression : Expression {
    public readonly List<Expression> Elements;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Elements));
    }

    public DisplayExpression(IToken tok, List<Expression> elements)
      : base(tok) {
      Contract.Requires(cce.NonNullElements(elements));
      Elements = elements;
    }

    public override IEnumerable<Expression> SubExpressions {
      get { return Elements; }
    }
  }

  public class SetDisplayExpr : DisplayExpression {
    public bool Finite;
    public SetDisplayExpr(IToken tok, bool finite, List<Expression> elements)
      : base(tok, elements) {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(elements));
      Finite = finite;
    }
  }

  public class MultiSetDisplayExpr : DisplayExpression {
    public MultiSetDisplayExpr(IToken tok, List<Expression> elements) : base(tok, elements) {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(elements));
    }
  }

  public class MapDisplayExpr : Expression {
    public bool Finite;
    public List<ExpressionPair> Elements;
    public MapDisplayExpr(IToken tok, bool finite, List<ExpressionPair> elements)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(elements));
      Finite = finite;
      Elements = elements;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var ep in Elements) {
          yield return ep.A;
          yield return ep.B;
        }
      }
    }
  }
  public class SeqDisplayExpr : DisplayExpression {
    public SeqDisplayExpr(IToken tok, List<Expression> elements)
      : base(tok, elements) {
      Contract.Requires(cce.NonNullElements(elements));
      Contract.Requires(tok != null);
    }
  }

  public class MemberSelectExpr : Expression {
    public readonly Expression Obj;
    public readonly string MemberName;
    public MemberDecl Member;    // filled in by resolution, will be a Field or Function
    public Label /*?*/ AtLabel;  // determined by resolution; non-null for a two-state selection

    /// <summary>
    /// TypeApplication_AtEnclosingClass is the list of type arguments used to instantiate the type that
    /// declares Member (which is some supertype of the receiver type).
    /// </summary>
    public List<Type> TypeApplication_AtEnclosingClass;  // filled in during resolution

    /// <summary>
    ///  TypeApplication_JustMember is the list of type arguments used to instantiate the type parameters
    /// of Member.
    /// </summary>
    public List<Type> TypeApplication_JustMember;  // filled in during resolution

    /// <summary>
    /// Returns a mapping from formal type parameters to actual type arguments. For example, given
    ///     trait T<A> {
    ///       function F<X>(): bv8 { ... }
    ///     }
    ///     class C<B, D> extends T<map<B, D>> { }
    /// and MemberSelectExpr o.F<int> where o has type C<real, bool>, the type map returned is
    ///     A -> map<real, bool>
    ///     X -> int
    /// To also include B and D in the mapping, use TypeArgumentSubstitutionsWithParents instead.
    /// </summary>
    public Dictionary<TypeParameter, Type> TypeArgumentSubstitutionsAtMemberDeclaration() {
      Contract.Requires(WasResolved());
      Contract.Ensures(Contract.Result<Dictionary<TypeParameter, Type>>() != null);

      var subst = new Dictionary<TypeParameter, Type>();

      // Add the mappings from the member's own type parameters
      if (Member is ICallable icallable) {
        Contract.Assert(TypeApplication_JustMember.Count == icallable.TypeArgs.Count);
        for (var i = 0; i < icallable.TypeArgs.Count; i++) {
          subst.Add(icallable.TypeArgs[i], TypeApplication_JustMember[i]);
        }
      } else {
        Contract.Assert(TypeApplication_JustMember.Count == 0);
      }

      // Add the mappings from the enclosing class.
      TopLevelDecl cl = Member.EnclosingClass;
      // Expand the type down to its non-null type, if any
      if (cl != null) {
        Contract.Assert(cl.TypeArgs.Count == TypeApplication_AtEnclosingClass.Count);
        for (var i = 0; i < cl.TypeArgs.Count; i++) {
          subst.Add(cl.TypeArgs[i], TypeApplication_AtEnclosingClass[i]);
        }
      }

      return subst;
    }

    /// <summary>
    /// Returns a mapping from formal type parameters to actual type arguments. For example, given
    ///     trait T<A> {
    ///       function F<X>(): bv8 { ... }
    ///     }
    ///     class C<B, D> extends T<map<B, D>> { }
    /// and MemberSelectExpr o.F<int> where o has type C<real, bool>, the type map returned is
    ///     A -> map<real, bool>
    ///     B -> real
    ///     D -> bool
    ///     X -> int
    /// NOTE: This method should be called only when all types have been fully and successfully
    /// resolved. During type inference, when there may still be some unresolved proxies, use
    /// TypeArgumentSubstitutionsAtMemberDeclaration instead.
    /// </summary>
    public Dictionary<TypeParameter, Type> TypeArgumentSubstitutionsWithParents() {
      Contract.Requires(WasResolved());
      Contract.Ensures(Contract.Result<Dictionary<TypeParameter, Type>>() != null);

      return TypeArgumentSubstitutionsWithParentsAux(Obj.Type, Member, TypeApplication_JustMember);
    }

    public static Dictionary<TypeParameter, Type> TypeArgumentSubstitutionsWithParentsAux(Type receiverType, MemberDecl member, List<Type> typeApplicationMember) {
      Contract.Requires(receiverType != null);
      Contract.Requires(member != null);
      Contract.Requires(typeApplicationMember != null);
      Contract.Ensures(Contract.Result<Dictionary<TypeParameter, Type>>() != null);

      var subst = new Dictionary<TypeParameter, Type>();

      // Add the mappings from the member's own type parameters
      if (member is ICallable) {
        // Make sure to include the member's type parameters all the way up the inheritance chain
        for (var ancestor = member; ancestor != null; ancestor = ancestor.OverriddenMember) {
          var icallable = (ICallable)ancestor;
          Contract.Assert(typeApplicationMember.Count == icallable.TypeArgs.Count);
          for (var i = 0; i < icallable.TypeArgs.Count; i++) {
            subst.Add(icallable.TypeArgs[i], typeApplicationMember[i]);
          }
        }
      } else {
        Contract.Assert(typeApplicationMember.Count == 0);
      }

      // Add the mappings from the receiver's type "cl"
      var udt = receiverType.NormalizeExpand() as UserDefinedType;
      if (udt != null) {
        if (udt.ResolvedClass is InternalTypeSynonymDecl isyn) {
          udt = isyn.RhsWithArgumentIgnoringScope(udt.TypeArgs) as UserDefinedType;
        }
        if (udt.ResolvedClass is NonNullTypeDecl nntd) {
          udt = nntd.RhsWithArgumentIgnoringScope(udt.TypeArgs) as UserDefinedType;
        }
      }
      var cl = udt?.ResolvedClass;

      if (cl != null) {
        Contract.Assert(cl.TypeArgs.Count == udt.TypeArgs.Count);
        for (var i = 0; i < cl.TypeArgs.Count; i++) {
          subst.Add(cl.TypeArgs[i], udt.TypeArgs[i]);
        }

        // Add in the mappings from parent types' formal type parameters to types
        if (cl is TopLevelDeclWithMembers cls) {
          foreach (var entry in cls.ParentFormalTypeParametersToActuals) {
            var v = Resolver.SubstType(entry.Value, subst);
            subst.Add(entry.Key, v);
          }
        }
      }

      return subst;
    }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Obj != null);
      Contract.Invariant(MemberName != null);
      Contract.Invariant((Member != null) == (TypeApplication_AtEnclosingClass != null));  // TypeApplication_* are set whenever Member is set
      Contract.Invariant((Member != null) == (TypeApplication_JustMember != null));  // TypeApplication_* are set whenever Member is set
    }

    public MemberSelectExpr(IToken tok, Expression obj, string memberName)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(obj != null);
      Contract.Requires(memberName != null);
      this.Obj = obj;
      this.MemberName = memberName;
    }

    /// <summary>
    /// Returns a resolved MemberSelectExpr for a field.
    /// </summary>
    public MemberSelectExpr(IToken tok, Expression obj, Field field)
      : this(tok, obj, field.Name)
    {
      Contract.Requires(tok != null);
      Contract.Requires(obj != null);
      Contract.Requires(field != null);
      Contract.Requires(obj.Type != null);  // "obj" is required to be resolved

      this.Member = field;  // resolve here

      var receiverType = obj.Type.NormalizeExpand();
      this.TypeApplication_AtEnclosingClass = receiverType.TypeArgs;
      this.TypeApplication_JustMember = new List<Type>();

      var typeMap = new Dictionary<TypeParameter, Type>();
      if (receiverType is UserDefinedType udt) {
        var cl = udt.ResolvedClass as TopLevelDeclWithMembers;
        Contract.Assert(cl != null);
        Contract.Assert(cl.TypeArgs.Count == TypeApplication_AtEnclosingClass.Count);
        for (var i = 0; i < cl.TypeArgs.Count; i++) {
          typeMap.Add(cl.TypeArgs[i], TypeApplication_AtEnclosingClass[i]);
        }
        foreach (var entry in cl.ParentFormalTypeParametersToActuals) {
          var v = Resolver.SubstType(entry.Value, typeMap);
          typeMap.Add(entry.Key, v);
        }
      } else if (field.EnclosingClass == null) {
        // leave typeMap as the empty substitution
      } else {
        Contract.Assert(field.EnclosingClass.TypeArgs.Count == TypeApplication_AtEnclosingClass.Count);
        for (var i = 0; i < field.EnclosingClass.TypeArgs.Count; i++) {
          typeMap.Add(field.EnclosingClass.TypeArgs[i], TypeApplication_AtEnclosingClass[i]);
        }
      }
      this.Type = Resolver.SubstType(field.Type, typeMap);  // resolve here
    }

    public void MemberSelectCase(Action<Field> fieldK, Action<Function> functionK) {
      MemberSelectCase<bool>(
        f => {
          fieldK(f);
          return true;
        },
        f => {
          functionK(f);
          return true;
        });
    }

    public A MemberSelectCase<A>(Func<Field,A> fieldK, Func<Function,A> functionK) {
      var field = Member as Field;
      var function = Member as Function;
      if (field != null) {
        return fieldK(field);
      } else {
        Contract.Assert(function != null);
        return functionK(function);
      }
    }

    public override IEnumerable<Expression> SubExpressions {
      get { yield return Obj; }
    }

    public override IEnumerable<Type> ComponentTypes => Util.Concat(TypeApplication_AtEnclosingClass, TypeApplication_JustMember);
  }

  public class SeqSelectExpr : Expression {
    public readonly bool SelectOne;  // false means select a range
    public readonly Expression Seq;
    public readonly Expression E0;
    public readonly Expression E1;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Seq != null);
      Contract.Invariant(!SelectOne || E1 == null);
    }

    public SeqSelectExpr(IToken tok, bool selectOne, Expression seq, Expression e0, Expression e1)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(seq != null);
      Contract.Requires(!selectOne || e1 == null);

      SelectOne = selectOne;
      Seq = seq;
      E0 = e0;
      E1 = e1;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Seq;
        if (E0 != null) yield return E0;
        if (E1 != null) yield return E1;
      }
    }
  }

  public class MultiSelectExpr : Expression {
    public readonly Expression Array;
    public readonly List<Expression> Indices;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Array != null);
      Contract.Invariant(cce.NonNullElements(Indices));
      Contract.Invariant(1 <= Indices.Count);
    }

    public MultiSelectExpr(IToken tok, Expression array, List<Expression> indices)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(array != null);
      Contract.Requires(cce.NonNullElements(indices) && 1 <= indices.Count);

      Array = array;
      Indices = indices;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Array;
        foreach (var e in Indices) {
          yield return e;
        }
      }
    }
  }

  /// <summary>
  /// Represents an expression of the form A[B := C], where, syntactically, A, B, and C are expressions.
  /// Successfully resolved, the expression stands for one of the following:
  /// * if A is a sequence, then B is an integer-based index into the sequence and C's type is the sequence element type
  /// * if A is a map(T,U), then B is a key of type T and C is a value of type U
  /// * if A is a multiset, then B's type is the multiset element type and C is an integer-based numeric
  /// * if A is a datatype, then B is the name of a destructor of A's type and C's type is the type of that destructor -- in
  ///   this case, the resolver will set the ResolvedUpdateExpr to an expression that constructs an appropriate datatype value
  /// </summary>
  public class SeqUpdateExpr : Expression {
    public readonly Expression Seq;
    public readonly Expression Index;
    public readonly Expression Value;
    public Expression ResolvedUpdateExpr;       // filled in during resolution, if the SeqUpdateExpr corresponds to a datatype update
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Seq != null);
      Contract.Invariant(Index != null);
      Contract.Invariant(Value != null);
    }

    public SeqUpdateExpr(IToken tok, Expression seq, Expression index, Expression val)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(seq != null);
      Contract.Requires(index != null);
      Contract.Requires(val != null);
      Seq = seq;
      Index = index;
      Value = val;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        if (ResolvedUpdateExpr == null)
        {
          yield return Seq;
          yield return Index;
          yield return Value;
        }
        else
        {
          foreach (var e in ResolvedUpdateExpr.SubExpressions)
          {
            yield return e;
          }
        }
      }
    }
  }

  public class ApplyExpr : Expression {
    // The idea is that this apply expression does not need a type argument substitution,
    // since lambda functions and anonymous functions are never polymorphic.
    // Make a FunctionCallExpr otherwise, to call a resolvable anonymous function.
    public readonly Expression Function;
    public readonly List<Expression> Args;

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Function;
        foreach (var e in Args) {
          yield return e;
        }
      }
    }

    public ApplyExpr(IToken tok, Expression fn, List<Expression> args)
      : base(tok)
    {
      Function = fn;
      Args = args;
    }
  }

  public class FunctionCallExpr : Expression {
    public readonly string Name;
    public readonly Expression Receiver;
    public readonly IToken OpenParen;  // can be null if Args.Count == 0
    public readonly Label/*?*/ AtLabel;
    public readonly ActualBindings Bindings;
    public List<Expression> Args => Bindings.Arguments;
    public List<Type> TypeApplication_AtEnclosingClass;  // filled in during resolution
    public List<Type> TypeApplication_JustFunction;  // filled in during resolution

    /// <summary>
    /// Return a mapping from each type parameter of the function and its enclosing class to actual type arguments.
    /// This method should only be called on fully and successfully resolved FunctionCallExpr's.
    /// </summary>
    public Dictionary<TypeParameter, Type> GetTypeArgumentSubstitutions() {
      var typeMap = new Dictionary<TypeParameter, Type>();
      Util.AddToDict(typeMap, Function.EnclosingClass.TypeArgs, TypeApplication_AtEnclosingClass);
      Util.AddToDict(typeMap, Function.TypeArgs, TypeApplication_JustFunction);
      return typeMap;
    }

    /// <summary>
    /// Returns a mapping from formal type parameters to actual type arguments. For example, given
    ///     trait T<A> {
    ///       function F<X>(): bv8 { ... }
    ///     }
    ///     class C<B, D> extends T<map<B, D>> { }
    /// and FunctionCallExpr o.F<int>(args) where o has type C<real, bool>, the type map returned is
    ///     A -> map<real, bool>
    ///     B -> real
    ///     D -> bool
    ///     X -> int
    /// NOTE: This method should be called only when all types have been fully and successfully
    /// resolved.
    /// </summary>
    public Dictionary<TypeParameter, Type> TypeArgumentSubstitutionsWithParents() {
      Contract.Requires(WasResolved());
      Contract.Ensures(Contract.Result<Dictionary<TypeParameter, Type>>() != null);

      return MemberSelectExpr.TypeArgumentSubstitutionsWithParentsAux(Receiver.Type, Function, TypeApplication_JustFunction);
    }

    public enum CoCallResolution {
      No,
      Yes,
      NoBecauseFunctionHasSideEffects,
      NoBecauseFunctionHasPostcondition,
      NoBecauseRecursiveCallsAreNotAllowedInThisContext,
      NoBecauseIsNotGuarded,
      NoBecauseRecursiveCallsInDestructiveContext
    }
    public CoCallResolution CoCall = CoCallResolution.No;  // indicates whether or not the call is a co-recursive call; filled in by resolution
    public string CoCallHint = null;  // possible additional hint that can be used in verifier error message, filled in by resolver

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Name != null);
      Contract.Invariant(Receiver != null);
      Contract.Invariant(cce.NonNullElements(Args));
      Contract.Invariant(
        Function == null || TypeApplication_AtEnclosingClass == null ||
        Function.EnclosingClass.TypeArgs.Count == TypeApplication_AtEnclosingClass.Count);
      Contract.Invariant(
        Function == null || TypeApplication_JustFunction == null ||
        Function.TypeArgs.Count == TypeApplication_JustFunction.Count);
    }

    public Function Function;  // filled in by resolution

    public FunctionCallExpr(IToken tok, string fn, Expression receiver, IToken openParen, [Captured] List<ActualBinding> args, Label/*?*/ atLabel = null)
      : this(tok, fn, receiver, openParen, new ActualBindings(args), atLabel) {
      Contract.Requires(tok != null);
      Contract.Requires(fn != null);
      Contract.Requires(receiver != null);
      Contract.Requires(cce.NonNullElements(args));
      Contract.Requires(openParen != null || args.Count == 0);
      Contract.Ensures(type == null);
    }

    public FunctionCallExpr(IToken tok, string fn, Expression receiver, IToken openParen, [Captured] ActualBindings bindings, Label/*?*/ atLabel = null)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(fn != null);
      Contract.Requires(receiver != null);
      Contract.Requires(bindings != null);
      Contract.Requires(openParen != null);
      Contract.Ensures(type == null);

      this.Name = fn;
      this.Receiver = receiver;
      this.OpenParen = openParen;
      this.AtLabel = atLabel;
      this.Bindings = bindings;
    }

    /// <summary>
    /// This constructor is intended to be used when constructing a resolved FunctionCallExpr. The "args" are expected
    /// to be already resolved, and are all given positionally.
    /// </summary>
    public FunctionCallExpr(IToken tok, string fn, Expression receiver, IToken openParen, [Captured] List<Expression> args,
      Label /*?*/ atLabel = null)
      : this(tok, fn, receiver, openParen, args.ConvertAll(e => new ActualBinding(null, e)), atLabel) {
      Bindings.AcceptArgumentExpressionsAsExactParameterList();
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Receiver;
        foreach (var e in Args) {
          yield return e;
        }
      }
    }

    public override IEnumerable<Type> ComponentTypes => Util.Concat(TypeApplication_AtEnclosingClass, TypeApplication_JustFunction);
  }

  public class SeqConstructionExpr : Expression
  {
    public Type/*?*/ ExplicitElementType;
    public Expression N;
    public Expression Initializer;
    public SeqConstructionExpr(IToken tok, Type/*?*/ elementType, Expression length, Expression initializer)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(length != null);
      Contract.Requires(initializer != null);
      ExplicitElementType = elementType;
      N = length;
      Initializer = initializer;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return N;
        yield return Initializer;
      }
    }

    public override IEnumerable<Type> ComponentTypes {
      get {
        if (ExplicitElementType != null) {
          yield return ExplicitElementType;
        }
      }
    }
  }

  public class MultiSetFormingExpr : Expression
  {
    [Peer]
    public readonly Expression E;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
    }

    [Captured]
    public MultiSetFormingExpr(IToken tok, Expression expr)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      cce.Owner.AssignSame(this, expr);
      E = expr;
    }

    public override IEnumerable<Expression> SubExpressions {
      get { yield return E; }
    }
  }

  public class OldExpr : Expression
  {
    [Peer]
    public readonly Expression E;
    public readonly string/*?*/ At;
    public Label AtLabel;  // filled in during resolution; after that, At==null iff AtLabel==null
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
    }

    [Captured]
    public OldExpr(IToken tok, Expression expr, string at = null)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      cce.Owner.AssignSame(this, expr);
      E = expr;
      At = at;
    }

    public override IEnumerable<Expression> SubExpressions {
      get { yield return E; }
    }
  }

  public class UnchangedExpr : Expression
  {
    public readonly List<FrameExpression> Frame;
    public readonly string/*?*/ At;
    public Label AtLabel;  // filled in during resolution; after that, At==null iff AtLabel==null
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Frame != null);
    }

    public UnchangedExpr(IToken tok, List<FrameExpression> frame, string/*?*/ at)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(frame != null);
      this.Frame = frame;
      this.At = at;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var fe in Frame) {
          yield return fe.E;
        }
      }
    }
  }

  public abstract class UnaryExpr : Expression
  {
    public readonly Expression E;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
    }

    public UnaryExpr(IToken tok, Expression e)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(e != null);
      this.E = e;
    }

    public override IEnumerable<Expression> SubExpressions {
      get { yield return E; }
    }
  }

  public class UnaryOpExpr : UnaryExpr
  {
    public enum Opcode {
      Not,  // boolean negation or bitwise negation
      Cardinality,
      Fresh,
      Allocated,
      Lit,  // there is no syntax for this operator, but it is sometimes introduced during translation
    }
    public readonly Opcode Op;

    public UnaryOpExpr(IToken tok, Opcode op, Expression e)
      : base(tok, e) {
      Contract.Requires(tok != null);
      Contract.Requires(e != null);
      this.Op = op;
    }
  }

  public abstract class TypeUnaryExpr : UnaryExpr
  {
    public readonly Type ToType;
    public TypeUnaryExpr(IToken tok, Expression expr, Type toType)
      : base(tok, expr) {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      Contract.Requires(toType != null);
      ToType = toType;
    }

    public override IEnumerable<Type> ComponentTypes {
      get {
        yield return ToType;
      }
    }
  }

  public class ConversionExpr : TypeUnaryExpr
  {
    public ConversionExpr(IToken tok, Expression expr, Type toType)
      : base(tok, expr, toType) {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      Contract.Requires(toType != null);
    }
  }

  public class TypeTestExpr : TypeUnaryExpr
  {
    public TypeTestExpr(IToken tok, Expression expr, Type toType)
      : base(tok, expr, toType) {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      Contract.Requires(toType != null);
    }
  }

  public class BinaryExpr : Expression
  {
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
      Add,
      Sub,
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
      set {
        Contract.Assume(_theResolvedOp == ResolvedOpcode.YetUndetermined || _theResolvedOp == value);  // there's never a reason for resolution to change its mind, is there?
        _theResolvedOp = value;
      }
      get {
        Contract.Assume(_theResolvedOp != ResolvedOpcode.YetUndetermined);  // shouldn't read it until it has been properly initialized
        return _theResolvedOp;
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
    public readonly Expression E0;
    public readonly Expression E1;
    public enum AccumulationOperand { None, Left, Right }
    public AccumulationOperand AccumulatesForTailRecursion = AccumulationOperand.None; // set by Resolver
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E0 != null);
      Contract.Invariant(E1 != null);
    }

    public BinaryExpr(IToken tok, Opcode op, Expression e0, Expression e1)
      : base(tok) {
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
    public BinaryExpr(Boogie.IToken tok, BinaryExpr.ResolvedOpcode rop, Expression e0, Expression e1)
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
  }

  public class TernaryExpr : Expression
  {
    public readonly Opcode Op;
    public readonly Expression E0;
    public readonly Expression E1;
    public readonly Expression E2;
    public enum Opcode { /*SOON: IfOp,*/ PrefixEqOp, PrefixNeqOp }
    public static readonly bool PrefixEqUsesNat = false;  // "k" is either a "nat" or an "ORDINAL"
    public TernaryExpr(IToken tok, Opcode op, Expression e0, Expression e1, Expression e2)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(e2 != null);
      Op = op;
      E0 = e0;
      E1 = e1;
      E2 = e2;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return E0;
        yield return E1;
        yield return E2;
      }
    }
  }

  public class LetExpr : Expression, IAttributeBearingDeclaration
  {
    public readonly List<CasePattern<BoundVar>> LHSs;
    public readonly List<Expression> RHSs;
    public readonly Expression Body;
    public readonly bool Exact;  // Exact==true means a regular let expression; Exact==false means an assign-such-that expression
    public readonly Attributes Attributes;
    public List<ComprehensionExpr.BoundedPool> Constraint_Bounds;  // initialized and filled in by resolver; null for Exact=true and for when expression is in a ghost context
    // invariant Constraint_Bounds == null || Constraint_Bounds.Count == BoundVars.Count;
    private Expression translationDesugaring;  // filled in during translation, lazily; to be accessed only via Translation.LetDesugaring; always null when Exact==true
    private Translator lastTranslatorUsed; // avoid clashing desugaring between translators

    public void setTranslationDesugaring(Translator trans, Expression expr) {
      lastTranslatorUsed = trans;
      translationDesugaring = expr;
    }

    public Expression getTranslationDesugaring(Translator trans) {
      if (lastTranslatorUsed == trans) {
        return translationDesugaring;
      } else {
        return null;
      }
    }

    public LetExpr(IToken tok, List<CasePattern<BoundVar>> lhss, List<Expression> rhss, Expression body, bool exact, Attributes attrs = null)
      : base(tok) {
      LHSs = lhss;
      RHSs = rhss;
      Body = body;
      Exact = exact;
      Attributes = attrs;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in Attributes.SubExpressions(Attributes)) {
          yield return e;
        }
        foreach (var rhs in RHSs) {
          yield return rhs;
        }
        yield return Body;
      }
    }

    public override IEnumerable<Type> ComponentTypes => BoundVars.Select(bv => bv.Type);

    public IEnumerable<BoundVar> BoundVars {
      get {
        foreach (var lhs in LHSs) {
          foreach (var bv in lhs.Vars) {
            yield return bv;
          }
        }
      }
    }
  }

  public class LetOrFailExpr : ConcreteSyntaxExpression
  {
    public readonly CasePattern<BoundVar>/*?*/ Lhs; // null means void-error handling: ":- E; F", non-null means "var pat :- E; F"
    public readonly Expression Rhs;
    public readonly Expression Body;

    public LetOrFailExpr(IToken tok, CasePattern<BoundVar>/*?*/ lhs, Expression rhs, Expression body): base(tok) {
      Lhs = lhs;
      Rhs = rhs;
      Body = body;
    }
  }

  /// <summary>
  /// A ComprehensionExpr has the form:
  ///   BINDER x Attributes | Range(x) :: Term(x)
  /// When BINDER is "forall" or "exists", the range may be "null" (which stands for the logical value "true").
  /// For other BINDERs (currently, "set"), the range is non-null.
  /// where "Attributes" is optional, and "| Range(x)" is optional and defaults to "true".
  /// Currently, BINDER is one of the logical quantifiers "exists" or "forall".
  /// </summary>
  public abstract class ComprehensionExpr : Expression, IAttributeBearingDeclaration
  {
    public readonly List<BoundVar> BoundVars;
    public readonly Expression Range;
    private Expression term;
    public Expression Term { get { return term; } }

    public void UpdateTerm(Expression newTerm) {
      term = newTerm;
    }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(BoundVars != null);
      Contract.Invariant(Term != null);
    }

    public Attributes Attributes;

    public abstract class BoundedPool {
      [Flags]
      public enum PoolVirtues { None = 0, Finite = 1, Enumerable = 2, IndependentOfAlloc = 4, IndependentOfAlloc_or_ExplicitAlloc = 8 }
      public abstract PoolVirtues Virtues { get; }
      /// <summary>
      /// A higher preference is better.
      /// A preference below 2 is a last-resort bounded pool. Bounds discovery will not consider
      /// such a pool to be final until there are no other choices.
      ///
      /// For easy reference, here is the BoundedPool hierarchy and their preference levels:
      ///
      /// 0: AllocFreeBoundedPool
      /// 0: ExplicitAllocatedBoundedPool
      /// 0: SpecialAllocIndependenceAllocatedBoundedPool
      ///
      /// 1: WiggleWaggleBound
      ///
      /// 2: SuperSetBoundedPool
      /// 2: DatatypeInclusionBoundedPool
      ///
      /// 3: SubSetBoundedPool
      ///
      /// 4: IntBoundedPool with one bound
      /// 5: IntBoundedPool with both bounds
      /// 5: CharBoundedPool
      ///
      /// 8: DatatypeBoundedPool
      ///
      /// 10: CollectionBoundedPool
      ///     - SetBoundedPool
      ///     - MapBoundedPool
      ///     - SeqBoundedPool
      ///
      /// 14: BoolBoundedPool
      ///
      /// 15: ExactBoundedPool
      /// </summary>
      public abstract int Preference(); // higher is better

      public static BoundedPool GetBest(List<BoundedPool> bounds, PoolVirtues requiredVirtues) {
        Contract.Requires(bounds != null);
        bounds = CombineIntegerBounds(bounds);
        BoundedPool best = null;
        foreach (var bound in bounds) {
          if ((bound.Virtues & requiredVirtues) == requiredVirtues) {
            if (best == null || bound.Preference() > best.Preference()) {
              best = bound;
            }
          }
        }
        return best;
      }
      public static List<VT> MissingBounds<VT>(List<VT> vars, List<BoundedPool> bounds, PoolVirtues requiredVirtues = PoolVirtues.None) where VT : IVariable {
        Contract.Requires(vars != null);
        Contract.Requires(bounds != null);
        Contract.Requires(vars.Count == bounds.Count);
        Contract.Ensures(Contract.Result<List<VT>>() != null);
        var missing = new List<VT>();
        for (var i = 0; i < vars.Count; i++) {
          if (bounds[i] == null || (bounds[i].Virtues & requiredVirtues) != requiredVirtues) {
            missing.Add(vars[i]);
          }
        }
        return missing;
      }
      public static List<bool> HasBounds(List<BoundedPool> bounds, PoolVirtues requiredVirtues = PoolVirtues.None) {
        Contract.Requires(bounds != null);
        Contract.Ensures(Contract.Result<List<bool>>() != null);
        Contract.Ensures(Contract.Result<List<bool>>().Count == bounds.Count);
        return bounds.ConvertAll(bound => bound != null && (bound.Virtues & requiredVirtues) == requiredVirtues);
      }
      static List<BoundedPool> CombineIntegerBounds(List<BoundedPool> bounds) {
        var lowerBounds = new List<IntBoundedPool>();
        var upperBounds = new List<IntBoundedPool>();
        var others = new List<BoundedPool>();
        foreach (var b in bounds) {
          var ib = b as IntBoundedPool;
          if (ib != null && ib.UpperBound == null) {
            lowerBounds.Add(ib);
          } else if (ib != null && ib.LowerBound == null) {
            upperBounds.Add(ib);
          } else {
            others.Add(b);
          }
        }
        // pair up the bounds
        var n = Math.Min(lowerBounds.Count, upperBounds.Count);
        for (var i = 0; i < n; i++) {
          others.Add(new IntBoundedPool(lowerBounds[i].LowerBound, upperBounds[i].UpperBound));
        }
        for (var i = n; i < lowerBounds.Count; i++) {
          others.Add(lowerBounds[i]);
        }
        for (var i = n; i < upperBounds.Count; i++) {
          others.Add(upperBounds[i]);
        }
        return others;
      }
    }
    public class ExactBoundedPool : BoundedPool
    {
      public readonly Expression E;
      public ExactBoundedPool(Expression e) {
        Contract.Requires(e != null);
        E = e;
      }
      public override PoolVirtues Virtues => PoolVirtues.Finite | PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
      public override int Preference() => 15;  // the best of all bounds
    }
    public class BoolBoundedPool : BoundedPool
    {
      public override PoolVirtues Virtues => PoolVirtues.Finite | PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
      public override int Preference() => 14;
    }
    public class CharBoundedPool : BoundedPool
    {
      public override PoolVirtues Virtues => PoolVirtues.Finite | PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
      public override int Preference() => 5;
    }
    public class AllocFreeBoundedPool : BoundedPool
    {
      public Type Type;
      public AllocFreeBoundedPool(Type t) {
        Type = t;
      }
      public override PoolVirtues Virtues {
        get {
          if (Type.IsRefType) {
            return PoolVirtues.Finite | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
          } else {
            return PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
          }
        }
      }
      public override int Preference() => 0;
    }
    public class ExplicitAllocatedBoundedPool : BoundedPool
    {
      public ExplicitAllocatedBoundedPool() {
      }
      public override PoolVirtues Virtues => PoolVirtues.Finite | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
      public override int Preference() => 0;
    }
    public class SpecialAllocIndependenceAllocatedBoundedPool : BoundedPool
    {
      public SpecialAllocIndependenceAllocatedBoundedPool() {
      }
      public override PoolVirtues Virtues => PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
      public override int Preference() => 0;
    }
    public class IntBoundedPool : BoundedPool
    {
      public readonly Expression LowerBound;
      public readonly Expression UpperBound;
      public IntBoundedPool(Expression lowerBound, Expression upperBound) {
        Contract.Requires(lowerBound != null || upperBound != null);
        LowerBound = lowerBound;
        UpperBound = upperBound;
      }
      public override PoolVirtues Virtues {
        get {
          if (LowerBound != null && UpperBound != null) {
            return PoolVirtues.Finite | PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
          } else {
            return PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
          }
        }
      }
      public override int Preference() => LowerBound != null && UpperBound != null ? 5 : 4;
    }
    public abstract class CollectionBoundedPool : BoundedPool
    {
      public readonly Type BoundVariableType;
      public readonly Type CollectionElementType;
      public readonly bool IsFiniteCollection;

      public CollectionBoundedPool(Type bvType, Type collectionElementType, bool isFiniteCollection) {
        Contract.Requires(bvType != null);
        Contract.Requires(collectionElementType != null);

        BoundVariableType = bvType;
        CollectionElementType = collectionElementType;
        IsFiniteCollection = isFiniteCollection;
      }

      public override PoolVirtues Virtues {
        get {
          var v = PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
          if (IsFiniteCollection) {
            v |= PoolVirtues.Finite;
            if (CollectionElementType.IsTestableToBe(BoundVariableType)) {
              v |= PoolVirtues.Enumerable;
            }
          }
          return v;
        }
      }
      public override int Preference() => 10;
    }
    public class SetBoundedPool : CollectionBoundedPool
    {
      public readonly Expression Set;

      public SetBoundedPool(Expression set, Type bvType, Type collectionElementType, bool isFiniteCollection)
        : base(bvType, collectionElementType, isFiniteCollection) {
        Contract.Requires(set != null);
        Contract.Requires(bvType != null);
        Contract.Requires(collectionElementType != null);
        Set = set;
      }
    }
    public class SubSetBoundedPool : BoundedPool
    {
      public readonly Expression UpperBound;
      public readonly bool IsFiniteCollection;
      public SubSetBoundedPool(Expression set, bool isFiniteCollection) {
        UpperBound = set;
        IsFiniteCollection = isFiniteCollection;
      }
      public override PoolVirtues Virtues {
        get {
          if (IsFiniteCollection) {
            return PoolVirtues.Finite | PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
          } else {
            // it's still enumerable, because at run time, all sets are finite after all
            return PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
          }
        }
      }
      public override int Preference() => 3;
    }
    public class SuperSetBoundedPool : BoundedPool
    {
      public readonly Expression LowerBound;
      public SuperSetBoundedPool(Expression set) { LowerBound = set; }
      public override int Preference() => 2;
      public override PoolVirtues Virtues {
        get {
          if (LowerBound.Type.IsAllocFree) {
            return PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
          } else {
            return PoolVirtues.None;
          }
        }
      }
    }
    public class MultiSetBoundedPool : CollectionBoundedPool
    {
      public readonly Expression MultiSet;

      public MultiSetBoundedPool(Expression multiset, Type bvType, Type collectionElementType)
        : base(bvType, collectionElementType, true) {
        Contract.Requires(multiset != null);
        Contract.Requires(bvType != null);
        Contract.Requires(collectionElementType != null);
        MultiSet = multiset;
      }
    }
    public class MapBoundedPool : CollectionBoundedPool
    {
      public readonly Expression Map;

      public MapBoundedPool(Expression map, Type bvType, Type collectionElementType, bool isFiniteCollection)
        : base(bvType, collectionElementType, isFiniteCollection) {
        Contract.Requires(map != null);
        Contract.Requires(bvType != null);
        Contract.Requires(collectionElementType != null);
        Map = map;
      }
    }
    public class SeqBoundedPool : CollectionBoundedPool
    {
      public readonly Expression Seq;

      public SeqBoundedPool(Expression seq, Type bvType, Type collectionElementType)
        : base(bvType, collectionElementType, true) {
        Contract.Requires(seq != null);
        Contract.Requires(bvType != null);
        Contract.Requires(collectionElementType != null);
        Seq = seq;
      }
    }
    public class DatatypeBoundedPool : BoundedPool
    {
      public readonly DatatypeDecl Decl;

      public DatatypeBoundedPool(DatatypeDecl d) {
        Contract.Requires(d != null);
        Decl = d;
      }
      public override PoolVirtues Virtues => PoolVirtues.Finite | PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
      public override int Preference() => 8;
    }
    public class DatatypeInclusionBoundedPool : BoundedPool
    {
      public readonly bool IsIndDatatype;
      public DatatypeInclusionBoundedPool(bool isIndDatatype) : base() { IsIndDatatype = isIndDatatype; }
      public override PoolVirtues Virtues => (IsIndDatatype ? PoolVirtues.Finite : PoolVirtues.None) | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
      public override int Preference() => 2;
    }

    public List<BoundedPool> Bounds;  // initialized and filled in by resolver
    // invariant Bounds == null || Bounds.Count == BoundVars.Count;

    public List<BoundVar> UncompilableBoundVars() {
      Contract.Ensures(Contract.Result<List<BoundVar>>() != null);
      var v = BoundedPool.PoolVirtues.Finite | BoundedPool.PoolVirtues.Enumerable;
      return ComprehensionExpr.BoundedPool.MissingBounds(BoundVars, Bounds, v);
    }

    public ComprehensionExpr(IToken tok, List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(term != null);

      this.BoundVars = bvars;
      this.Range = range;
      this.UpdateTerm(term);
      this.Attributes = attrs;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in Attributes.SubExpressions(Attributes)) {
          yield return e;
        }
        if (Range != null) { yield return Range; }
        yield return Term;
      }
    }

    public override IEnumerable<Type> ComponentTypes => BoundVars.Select(bv => bv.Type);
  }

  public abstract class QuantifierExpr : ComprehensionExpr, TypeParameter.ParentType {
    private readonly int UniqueId;
    public List<TypeParameter> TypeArgs;
    private static int currentQuantId = -1;

    protected virtual BinaryExpr.ResolvedOpcode SplitResolvedOp { get { return BinaryExpr.ResolvedOpcode.Or; } }

    private Expression SplitQuantifierToExpression() {
      Contract.Requires(SplitQuantifier != null && SplitQuantifier.Any());
      Expression accumulator = SplitQuantifier[0];
      for (int tid = 1; tid < SplitQuantifier.Count; tid++) {
        accumulator = new BinaryExpr(Term.tok, SplitResolvedOp, accumulator, SplitQuantifier[tid]);
      }
      return accumulator;
    }

    private List<Expression> _SplitQuantifier;
    public List<Expression> SplitQuantifier {
      get {
        return _SplitQuantifier;
      }
      set {
        Contract.Assert(!value.Contains(this)); // don't let it put into its own split quantifiers.
        _SplitQuantifier = value;
        SplitQuantifierExpression = SplitQuantifierToExpression();
      }
    }

    internal Expression SplitQuantifierExpression { get; private set; }

    static int FreshQuantId() {
      return System.Threading.Interlocked.Increment(ref currentQuantId);
    }

    public string FullName {
      get {
        return "q$" + UniqueId;
      }
    }

    public String Refresh(string prefix, FreshIdGenerator idGen) {
      return idGen.FreshId(prefix);
    }

    public TypeParameter Refresh(TypeParameter p, FreshIdGenerator idGen) {
      var cp = new TypeParameter(p.tok, idGen.FreshId(p.Name + "#"), p.VarianceSyntax, p.Characteristics);
      cp.Parent = this;
      return cp;
    }
    [ContractInvariantMethod]
    void ObjectInvariant() {
      var _scratch = true;
      Contract.Invariant(Attributes.ContainsBool(Attributes, "typeQuantifier", ref _scratch) || TypeArgs.Count == 0);
    }
    public QuantifierExpr(IToken tok, List<TypeParameter> tvars, List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
      : base(tok, bvars, range, term, attrs) {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(term != null);
      this.TypeArgs = tvars;
      this.UniqueId = FreshQuantId();
    }

    public virtual Expression LogicalBody(bool bypassSplitQuantifier = false) {
      // Don't call this on a quantifier with a Split clause: it's not a real quantifier. The only exception is the Compiler.
      Contract.Requires(bypassSplitQuantifier || SplitQuantifier == null);
      throw new cce.UnreachableException(); // This body is just here for the "Requires" clause
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        if (SplitQuantifier == null) {
          foreach (var e in base.SubExpressions) {
            yield return e;
          }
        } else {
          foreach (var e in Attributes.SubExpressions(Attributes)) {
            yield return e;
          }
          foreach (var e in SplitQuantifier) {
            yield return e;
          }
        }
      }
    }
  }

  public class ForallExpr : QuantifierExpr {
    protected override BinaryExpr.ResolvedOpcode SplitResolvedOp { get { return BinaryExpr.ResolvedOpcode.And; } }

    public ForallExpr(IToken tok, List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
      : this(tok, new List<TypeParameter>(), bvars, range, term, attrs) {
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(tok != null);
      Contract.Requires(term != null);
    }
    public ForallExpr(IToken tok, List<TypeParameter> tvars, List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
      : base(tok, tvars, bvars, range, term, attrs) {
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(tok != null);
      Contract.Requires(term != null);
    }
    public override Expression LogicalBody(bool bypassSplitQuantifier = false) {
      if (Range == null) {
        return Term;
      }
      var body = new BinaryExpr(Term.tok, BinaryExpr.Opcode.Imp, Range, Term);
      body.ResolvedOp = BinaryExpr.ResolvedOpcode.Imp;
      body.Type = Term.Type;
      return body;
    }
  }

  public class ExistsExpr : QuantifierExpr {
    protected override BinaryExpr.ResolvedOpcode SplitResolvedOp { get { return BinaryExpr.ResolvedOpcode.Or; } }

    public ExistsExpr(IToken tok, List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
      : this(tok, new List<TypeParameter>(), bvars, range, term, attrs) {
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(tok != null);
      Contract.Requires(term != null);
    }
    public ExistsExpr(IToken tok, List<TypeParameter> tvars, List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
      : base(tok, tvars, bvars, range, term, attrs) {
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(tok != null);
      Contract.Requires(term != null);
    }
    public override Expression LogicalBody(bool bypassSplitQuantifier = false) {
      if (Range == null) {
        return Term;
      }
      var body = new BinaryExpr(Term.tok, BinaryExpr.Opcode.And, Range, Term);
      body.ResolvedOp = BinaryExpr.ResolvedOpcode.And;
      body.Type = Term.Type;
      return body;
    }
  }

  public class SetComprehension : ComprehensionExpr
  {
    public readonly bool Finite;
    public readonly bool TermIsImplicit;  // records the given syntactic form
    public bool TermIsSimple {
      get {
        var term = Term as IdentifierExpr;
        var r = term != null && BoundVars.Count == 1 && BoundVars[0].Name == term.Name;
        Contract.Assert(!TermIsImplicit || r);  // TermIsImplicit ==> r
        Contract.Assert(!r || term.Var == null || term.Var == BoundVars[0]);  // if the term is simple and it has been resolved, then it should have resolved to BoundVars[0]
        return r;
      }
    }

    public SetComprehension(IToken tok, bool finite, List<BoundVar> bvars, Expression range, Expression/*?*/ term, Attributes attrs)
      : base(tok, bvars, range, term ?? new IdentifierExpr(tok, bvars[0].Name), attrs) {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(1 <= bvars.Count);
      Contract.Requires(range != null);
      Contract.Requires(term != null || bvars.Count == 1);

      TermIsImplicit = term == null;
      Finite = finite;
    }
  }
  public class MapComprehension : ComprehensionExpr
  {
    public readonly bool Finite;
    public readonly Expression TermLeft;

    public List<Boogie.Function> ProjectionFunctions;  // filled in during translation (and only for general map comprehensions where "TermLeft != null")

    public MapComprehension(IToken tok, bool finite, List<BoundVar> bvars, Expression range, Expression/*?*/ termLeft, Expression termRight, Attributes attrs)
      : base(tok, bvars, range, termRight, attrs) {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(1 <= bvars.Count);
      Contract.Requires(range != null);
      Contract.Requires(termRight != null);
      Contract.Requires(termLeft != null || bvars.Count == 1);

      Finite = finite;
      TermLeft = termLeft;
    }

    /// <summary>
    /// IsGeneralMapComprehension returns true for general map comprehensions.
    /// In other words, it returns false if either no TermLeft was given or if
    /// the given TermLeft is the sole bound variable.
    /// This property getter requires that the expression has been successfully
    /// resolved.
    /// </summary>
    public bool IsGeneralMapComprehension {
      get {
        Contract.Requires(WasResolved());
        if (TermLeft == null) {
          return false;
        } else if (BoundVars.Count != 1) {
          return true;
        }
        var lhs = StripParens(TermLeft).Resolved;
        if (lhs is IdentifierExpr ide && ide.Var == BoundVars[0]) {
          // TermLeft is the sole bound variable, so this is the same as
          // if TermLeft wasn't given at all
          return false;
        }
        return true;
      }
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in Attributes.SubExpressions(Attributes)) {
          yield return e;
        }
        if (Range != null) { yield return Range; }
        if (TermLeft != null) { yield return TermLeft; }
        yield return Term;
      }
    }
  }

  public class LambdaExpr : ComprehensionExpr
  {
    public readonly List<FrameExpression> Reads;

    public LambdaExpr(IToken tok, List<BoundVar> bvars, Expression requires, List<FrameExpression> reads, Expression body)
      : base(tok, bvars, requires, body, null)
    {
      Contract.Requires(reads != null);
      Reads = reads;
    }

    // Synonym
    public Expression Body {
      get {
        return Term;
      }
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Term;
        if (Range != null) {
          yield return Range;
        }
        foreach (var read in Reads) {
          yield return read.E;
        }
      }
    }

  }

  public class WildcardExpr : Expression
  {  // a WildcardExpr can occur only in reads clauses and a loop's decreases clauses (with different meanings)
    public WildcardExpr(IToken tok)
      : base(tok) {
      Contract.Requires(tok != null);
    }
  }

  /// <summary>
  /// A StmtExpr has the form S;E where S is a statement (from a restricted set) and E is an expression.
  /// The expression S;E evaluates to whatever E evaluates to, but its well-formedness comes down to
  /// executing S (which itself must be well-formed) and then checking the well-formedness of E.
  /// </summary>
  public class StmtExpr : Expression
  {
    public readonly Statement S;
    public readonly Expression E;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(S != null);
      Contract.Invariant(E != null);
    }

    public StmtExpr(IToken tok, Statement stmt, Expression expr)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(stmt != null);
      Contract.Requires(expr != null);
      S = stmt;
      E = expr;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        // Note:  A StmtExpr is unusual in that it contains a statement.  For now, callers
        // of SubExpressions need to be aware of this and handle it specially.
        yield return E;
      }
    }

    /// <summary>
    /// Returns a conclusion that S gives rise to, that is, something that is known after
    /// S is executed.
    /// This method should be called only after successful resolution of the expression.
    /// </summary>
    public Expression GetSConclusion() {
      // this is one place where we actually investigate what kind of statement .S is
      if (S is PredicateStmt) {
        var s = (PredicateStmt)S;
        return s.Expr;
      } else if (S is CalcStmt) {
        var s = (CalcStmt)S;
        return s.Result;
      } else if (S is RevealStmt) {
        return new LiteralExpr(tok, true);  // one could use the definition axiom or the referenced labeled assertions, but "true" is conservative and much simpler :)
      } else if (S is UpdateStmt) {
        return new LiteralExpr(tok, true);  // one could use the postcondition of the method, suitably instantiated, but "true" is conservative and much simpler :)
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement
      }
    }
  }

  public class ITEExpr : Expression
  {
    public readonly bool IsBindingGuard;
    public readonly Expression Test;
    public readonly Expression Thn;
    public readonly Expression Els;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Test != null);
      Contract.Invariant(Thn != null);
      Contract.Invariant(Els != null);
    }

    public ITEExpr(IToken tok, bool isBindingGuard, Expression test, Expression thn, Expression els)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(test != null);
      Contract.Requires(thn != null);
      Contract.Requires(els != null);
      this.IsBindingGuard = isBindingGuard;
      this.Test = test;
      this.Thn = thn;
      this.Els = els;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Test;
        yield return Thn;
        yield return Els;
      }
    }
  }

  public class MatchExpr : Expression {  // a MatchExpr is an "extended expression" and is only allowed in certain places
    private Expression source;
    private List<MatchCaseExpr> cases;
    public readonly MatchingContext Context;
    public readonly List<DatatypeCtor> MissingCases = new List<DatatypeCtor>();  // filled in during resolution
    public readonly bool UsesOptionalBraces;
    public MatchExpr OrigUnresolved;  // the resolver makes this clone of the MatchExpr before it starts desugaring it

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Source != null);
      Contract.Invariant(cce.NonNullElements(Cases));
      Contract.Invariant(cce.NonNullElements(MissingCases));
    }

    public MatchExpr(IToken tok, Expression source, [Captured] List<MatchCaseExpr> cases, bool usesOptionalBraces, MatchingContext context = null)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(source != null);
      Contract.Requires(cce.NonNullElements(cases));
      this.source = source;
      this.cases = cases;
      this.UsesOptionalBraces = usesOptionalBraces;
      this.Context = context is null? new HoleCtx() : context;
    }

    public Expression Source {
      get { return source; }
    }

    public List<MatchCaseExpr> Cases {
      get { return cases; }
    }

    // should only be used in desugar in resolve to change the source and cases of the matchexpr
    public void UpdateSource(Expression source) {
      this.source = source;
    }

    public void UpdateCases(List<MatchCaseExpr> cases) {
      this.cases = cases;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Source;
        foreach (var mc in cases) {
          yield return mc.Body;
        }
      }
    }

    public override IEnumerable<Type> ComponentTypes {
      get {
        foreach (var mc in cases) {
          foreach (var bv in mc.Arguments) {
            yield return bv.Type;
          }
        }
      }
    }
  }

  /// <summary>
  /// A CasePattern is either a BoundVar or a datatype constructor with optional arguments.
  /// Lexically, the CasePattern starts with an identifier.  If it continues with an open paren (as
  /// indicated by Arguments being non-null), then the CasePattern is a datatype constructor.  If
  /// it continues with a colon (which is indicated by Var.Type not being a proxy type), then it is
  /// a BoundVar.  But if it ends with just the identifier, then resolution is required to figure out
  /// which it is; in this case, Var is non-null, because this is the only place where Var.IsGhost
  /// is recorded by the parser.
  /// </summary>
  public class CasePattern<VT> where VT : IVariable
  {
    public readonly IToken tok;
    public readonly string Id;
    // After successful resolution, exactly one of the following two fields is non-null.
    public DatatypeCtor Ctor;  // finalized by resolution (null if the pattern is a bound variable)
    public VT Var;  // finalized by resolution (null if the pattern is a constructor)  Invariant:  Var != null ==> Arguments == null
    public List<CasePattern<VT>> Arguments;

    public Expression Expr;  // an r-value version of the CasePattern; filled in by resolution

    public void MakeAConstructor() {
      this.Arguments = new List<CasePattern<VT>>();
    }

    public CasePattern(IToken tok, string id, [Captured] List<CasePattern<VT>> arguments) {
      Contract.Requires(tok != null);
      Contract.Requires(id != null);
      this.tok = tok;
      Id = id;
      Arguments = arguments;
    }

    public CasePattern(IToken tok, VT bv) {
      Contract.Requires(tok != null);
      Contract.Requires(bv != null);
      this.tok = tok;
      Id = bv.Name;
      Var = bv;
    }

    /// <summary>
    /// Sets the Expr field.  Assumes the CasePattern and its arguments to have been successfully resolved, except for assigning
    /// to Expr.
    /// </summary>
    public void AssembleExpr(List<Type> dtvTypeArgs) {
      Contract.Requires(Var != null || dtvTypeArgs != null);
      if (Var != null) {
        Contract.Assert(this.Id == this.Var.Name);
        this.Expr = new IdentifierExpr(this.tok, this.Var);
      } else {
        var dtValue = new DatatypeValue(this.tok, this.Ctor.EnclosingDatatype.Name, this.Id,
          this.Arguments == null ? new List<Expression>() : this.Arguments.ConvertAll(arg => arg.Expr));
        dtValue.Ctor = this.Ctor;  // resolve here
        dtValue.InferredTypeArgs.AddRange(dtvTypeArgs);  // resolve here
        dtValue.Type = new UserDefinedType(this.tok, this.Ctor.EnclosingDatatype.Name, this.Ctor.EnclosingDatatype, dtvTypeArgs);
        this.Expr = dtValue;
      }
    }

    public IEnumerable<VT> Vars {
      get {
        if (Var != null) {
          yield return Var;
        } else {
          if (Arguments != null) {
            foreach (var arg in Arguments) {
              foreach (var bv in arg.Vars) {
                yield return bv;
              }
            }
          }
        }
      }
    }
  }

  public abstract class MatchCase
  {
    public readonly IToken tok;
    public DatatypeCtor Ctor;  // filled in by resolution
    public List<BoundVar> Arguments; // created by the resolver.
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(tok != null);
      Contract.Invariant(Ctor != null);
      Contract.Invariant(cce.NonNullElements(Arguments));
    }

    public MatchCase(IToken tok, DatatypeCtor ctor, [Captured] List<BoundVar> arguments) {
      Contract.Requires(tok != null);
      Contract.Requires(ctor != null);
      Contract.Requires(cce.NonNullElements(arguments));
      this.tok = tok;
      this.Ctor = ctor;
      this.Arguments = arguments;
    }
  }

  public class MatchCaseExpr : MatchCase
  {
    private Expression body;
    public Attributes Attributes;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(body != null);
    }

    public MatchCaseExpr(IToken tok, DatatypeCtor ctor, [Captured] List<BoundVar> arguments, Expression body, Attributes attrs = null)
      : base(tok, ctor, arguments) {
      Contract.Requires(tok != null);
      Contract.Requires(ctor != null);
      Contract.Requires(cce.NonNullElements(arguments));
      Contract.Requires(body != null);
      this.body = body;
      this.Attributes = attrs;
    }

    public Expression Body {
      get { return body; }
    }

    // should only be called by resolve to reset the body of the MatchCaseExpr
    public void UpdateBody(Expression body) {
      this.body = body;
    }
  }
  /*
  MatchingContext represents the context
  in which a pattern-match takes place during pattern-matching compilation

  MatchingContext is either:
  1 - a HoleCtx
      standing for one of the current selectors in pattern-matching compilation
  2 - A ForallCtx
      standing for a pattern-match over any expression
  3 - an IdCtx of a string and a list of MatchingContext
      standing for a pattern-match over a constructor
  4 - a LitCtx
      standing for a pattern-match over a constant
  */
  public abstract class MatchingContext
  {
    public virtual MatchingContext AbstractAllHoles() {
      return this;
    }

    public MatchingContext AbstractHole() {
      return this.FillHole(new ForallCtx());
    }

    public virtual MatchingContext FillHole(MatchingContext curr) {
      return this;
    }
  }

  public class LitCtx : MatchingContext
  {
    public readonly LiteralExpr Lit;

    public LitCtx(LiteralExpr lit) {
      Contract.Requires(lit != null);
      this.Lit = lit;
    }

    public override string ToString() {
      return Printer.ExprToString(Lit);
    }
  }

  public class HoleCtx : MatchingContext
  {
    public HoleCtx() {}

    public override string ToString() {
      return "*";
    }

    public override MatchingContext AbstractAllHoles() {
      return new ForallCtx();
    }

    public override MatchingContext FillHole(MatchingContext curr) {
      return curr;
    }
  }

  public class ForallCtx : MatchingContext
  {
    public ForallCtx() {}

    public override string ToString() {
      return "_";
    }
  }

  public class IdCtx : MatchingContext
  {
    public readonly String Id;
    public readonly List<MatchingContext> Arguments;

    public IdCtx(String id, List<MatchingContext> arguments) {
      Contract.Requires(id != null);
      Contract.Requires(arguments != null); // Arguments can be empty, but shouldn't be null
      this.Id = id;
      this.Arguments = arguments;
    }

    public IdCtx(KeyValuePair<string, DatatypeCtor> ctor) {
      List<MatchingContext> arguments = Enumerable.Repeat((MatchingContext)new HoleCtx(), ctor.Value.Formals.Count).ToList();
      this.Id = ctor.Key;
      this.Arguments = arguments;
    }

    public override string ToString() {
      if (Arguments.Count == 0) {
        return Id;
      } else {
        List<string> cps = Arguments.ConvertAll<string>(x => x.ToString());
        return string.Format("{0}({1})",Id, String.Join(",", cps));
      }
    }

    public override MatchingContext AbstractAllHoles() {
      return new IdCtx(this.Id, this.Arguments.ConvertAll<MatchingContext>(x => x.AbstractAllHoles()));
    }

    // Find the first (leftmost) occurrence of HoleCtx and replace it with curr
    // Returns false if no HoleCtx is found
    private bool ReplaceLeftmost(MatchingContext curr, out MatchingContext newcontext) {
      var newArguments = new List<MatchingContext>();
      bool foundHole = false;
      int currArgIndex = 0;

      while (!foundHole && currArgIndex < this.Arguments.Count) {
        var arg = this.Arguments.ElementAt(currArgIndex);
        switch (arg) {
          case HoleCtx _:
            foundHole = true;
            newArguments.Add(curr);
            break;
          case IdCtx argId:
            MatchingContext newarg;
            foundHole = argId.ReplaceLeftmost(curr, out newarg);
            newArguments.Add(newarg);
            break;
          default:
            newArguments.Add(arg);
            break;
        }
        currArgIndex++;
      }

      if (foundHole) {
        while (currArgIndex < this.Arguments.Count) {
          newArguments.Add(this.Arguments.ElementAt(currArgIndex));
          currArgIndex++;
        }
      }

      newcontext = new IdCtx(this.Id, newArguments);
      return foundHole;
    }

    public override MatchingContext FillHole(MatchingContext curr) {
      MatchingContext newcontext;
      ReplaceLeftmost(curr, out newcontext);
      return newcontext;
    }
  }

  /*
  ExtendedPattern is either:
  1 - A LitPattern of a LiteralExpr, representing a constant pattern
  2 - An IdPattern of a string and a list of ExtendedPattern, representing either
      a bound variable or a constructor applied to n arguments or a symbolic constant
  */
  public abstract class ExtendedPattern
  {
    public readonly IToken Tok;
    public bool IsGhost;

    public ExtendedPattern(IToken tok, bool isGhost = false) {
      Contract.Requires(tok != null);
      this.Tok = tok;
      this.IsGhost = isGhost;
    }
  }
  public class LitPattern : ExtendedPattern
  {
    public readonly Expression OrigLit;  // the expression as parsed; typically a LiteralExpr, but could be a NegationExpression

    /// <summary>
    /// The patterns of match constructs are rewritten very early during resolution, before any type information
    /// is available. This is unfortunate. It means we can't reliably rewrite negated expressions. In Dafny, "-" followed
    /// by digits is a negative literal for integers and reals, but as unary minus for bitvectors and ORDINAL (and
    /// unary minus is not allowed for ORDINAL, so that should always give an error).
    ///
    /// Since we don't have the necessary type information at this time, we optimistically negate all numeric literals here.
    /// After type checking, we look to see if we negated something we should not have.
    ///
    /// One could imagine allowing negative bitvector literals in case patterns and treating and them as synonyms for their
    /// positive counterparts. However, since the rewriting does not know about these synonyms, it would end up splitting
    /// cases that should have been combined, which leads to incorrect code.
    ///
    /// It would be good to check for these inadvertently allowed unary expressions only in the expanded patterns. However,
    /// the rewriting of patterns turns them into "if" statements and what not, so it's not easy to identify when a literal
    /// comes from this rewrite. Luckily, when other NegationExpressions are resolved, they turn into unary minus for bitvectors
    /// and into errors for ORDINALs. Therefore, any negative bitvector or ORDINAL literal discovered later can only have
    /// come from this rewriting. So, that's where errors are generated.
    ///
    /// One more detail, after the syntactic "-0" has been negated, the result is not negative. Therefore, what the previous
    /// paragraph explained as checking for negative bitvectors and ORDINALs doesn't work for "-0". So, instead of checking
    /// for the number being negative, the later pass will check if the token associated with the literal is "-0", a condition
    /// the assignment below ensures.
    /// </summary>
    public LiteralExpr OptimisticallyDesugaredLit {
      get {
        if (OrigLit is NegationExpression neg) {
          var lit = (LiteralExpr)neg.E;
          if (lit.Value is BaseTypes.BigDec d) {
            return new LiteralExpr(neg.tok, -d);
          } else {
            var n = (BigInteger)lit.Value;
            var tok = new Token(neg.tok.line, neg.tok.col) {
              filename = neg.tok.filename,
              val = "-0"
            };
            return new LiteralExpr(tok, -n);
          }
        } else {
          return (LiteralExpr)OrigLit;
        }
      }
    }

    public LitPattern(IToken tok, Expression lit, bool isGhost = false) : base(tok, isGhost) {
      Contract.Requires(lit is LiteralExpr || lit is NegationExpression);
      this.OrigLit = lit;
    }

    public override string ToString() {
      return Printer.ExprToString(OrigLit);
    }
  }

  public class IdPattern : ExtendedPattern
  {
    public readonly String Id;
    public readonly Type Type; // This is the syntactic type, ExtendedPatterns dissapear during resolution.
    public List<ExtendedPattern> Arguments; // null if just an identifier; possibly empty argument list if a constructor call
    public LiteralExpr ResolvedLit; // null if just an identifier

    public void MakeAConstructor() {
      this.Arguments = new List<ExtendedPattern>();
    }

    public IdPattern(IToken tok, String id, List<ExtendedPattern> arguments, bool isGhost = false) : base(tok, isGhost) {
      Contract.Requires(id != null);
      Contract.Requires(arguments != null); // Arguments can be empty, but shouldn't be null
      this.Id = id;
      this.Type = new InferredTypeProxy();
      this.Arguments = arguments;
    }

    public IdPattern(IToken tok, String id, Type type, List<ExtendedPattern> arguments, bool isGhost = false) : base(tok, isGhost) {
      Contract.Requires(id != null);
      Contract.Requires(arguments != null); // Arguments can be empty, but shouldn't be null
      this.Id = id;
      this.Type = type == null? new InferredTypeProxy(): type ;
      this.Arguments = arguments;
      this.IsGhost = isGhost;
    }

    public override string ToString() {
      if (Arguments == null || Arguments.Count == 0) {
        return Id;
      } else {
        List<string> cps = Arguments.ConvertAll<string>(x => x.ToString());
        return string.Format("{0}({1})", Id, String.Join(",", cps));
      }
    }
  }

  public abstract class NestedMatchCase
  {
    public readonly IToken Tok;
    public readonly ExtendedPattern Pat;

    public NestedMatchCase(IToken tok, ExtendedPattern pat) {
      Contract.Requires(tok != null);
      Contract.Requires(pat != null);
      this.Tok = tok;
      this.Pat = pat;
    }
  }

  public class NestedMatchCaseExpr : NestedMatchCase
  {
    public readonly Expression Body;
    public Attributes Attributes;

    public NestedMatchCaseExpr(IToken tok, ExtendedPattern pat, Expression body, Attributes attrs): base(tok, pat) {
      Contract.Requires(body != null);
      this.Body = body;
      this.Attributes = attrs;
    }
  }

  public class NestedMatchCaseStmt : NestedMatchCase
  {
    public readonly List<Statement> Body;
    public Attributes Attributes;
    public NestedMatchCaseStmt(IToken tok, ExtendedPattern pat, List<Statement> body) : base(tok, pat) {
      Contract.Requires(body != null);
      this.Body = body;
      this.Attributes = null;
    }
    public NestedMatchCaseStmt(IToken tok, ExtendedPattern pat, List<Statement> body, Attributes attrs) : base(tok, pat) {
      Contract.Requires(body != null);
      this.Body = body;
      this.Attributes = attrs;
    }

  }

  public class NestedMatchStmt : ConcreteSyntaxStatement
  {
    public readonly Expression Source;
    public readonly List<NestedMatchCaseStmt> Cases;
    public readonly bool UsesOptionalBraces;

    private void InitializeAttributes()
    {
      // Default case for match is false
      bool splitMatch = Attributes.Contains(this.Attributes, "split");
      Attributes.ContainsBool(this.Attributes, "split", ref splitMatch);
      foreach (var c in this.Cases) {
        if (!Attributes.Contains(c.Attributes, "split")) {
          List<Expression> args = new List<Expression>();
          args.Add(new LiteralExpr(c.Tok, splitMatch));
          Attributes attrs = new Attributes("split", args, c.Attributes);
          c.Attributes = attrs;
        }
      }
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        if (this.ResolvedStatement == null) {
          yield return Source;
        }
      }
    }
    public NestedMatchStmt(IToken tok, IToken endTok, Expression source, [Captured] List<NestedMatchCaseStmt> cases, bool usesOptionalBraces, Attributes attrs = null)
      : base(tok, endTok, attrs) {
      Contract.Requires(source != null);
      Contract.Requires(cce.NonNullElements(cases));
      this.Source = source;
      this.Cases = cases;
      this.UsesOptionalBraces = usesOptionalBraces;
      InitializeAttributes();
    }
  }

  public class NestedMatchExpr : ConcreteSyntaxExpression
  {
    public readonly Expression Source;
    public readonly List<NestedMatchCaseExpr> Cases;
    public readonly bool UsesOptionalBraces;
    public Attributes Attributes;

    public NestedMatchExpr(IToken tok, Expression source, [Captured] List<NestedMatchCaseExpr> cases, bool usesOptionalBraces, Attributes attrs = null): base(tok) {
      Contract.Requires(source != null);
      Contract.Requires(cce.NonNullElements(cases));
      this.Source = source;
      this.Cases = cases;
      this.UsesOptionalBraces = usesOptionalBraces;
      this.Attributes = attrs;
    }
  }

  public class BoxingCastExpr : Expression {  // a BoxingCastExpr is used only as a temporary placeholding during translation
    public readonly Expression E;
    public readonly Type FromType;
    public readonly Type ToType;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
      Contract.Invariant(FromType != null);
      Contract.Invariant(ToType != null);
    }

    public BoxingCastExpr(Expression e, Type fromType, Type toType)
      : base(e.tok) {
      Contract.Requires(e != null);
      Contract.Requires(fromType != null);
      Contract.Requires(toType != null);

      E = e;
      FromType = fromType;
      ToType = toType;
    }

    public override IEnumerable<Expression> SubExpressions {
      get { yield return E; }
    }
  }

  public class UnboxingCastExpr : Expression {  // an UnboxingCastExpr is used only as a temporary placeholding during translation
    public readonly Expression E;
    public readonly Type FromType;
    public readonly Type ToType;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
      Contract.Invariant(FromType != null);
      Contract.Invariant(ToType != null);
    }

    public UnboxingCastExpr(Expression e, Type fromType, Type toType)
      : base(e.tok) {
      Contract.Requires(e != null);
      Contract.Requires(fromType != null);
      Contract.Requires(toType != null);

      E = e;
      FromType = fromType;
      ToType = toType;
    }

    public override IEnumerable<Expression> SubExpressions {
      get { yield return E; }
    }
  }

  public class AttributedExpression {
    public readonly Expression E;
    public readonly AssertLabel/*?*/ Label;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
    }

    private Attributes attributes;
    public Attributes Attributes {
      get {
        return attributes;
      }
      set {
        attributes = value;
      }
    }

    public bool HasAttributes() {
      return Attributes != null;
    }

    public AttributedExpression(Expression e)
      : this(e, null)
    {
      Contract.Requires(e != null);
    }

    public AttributedExpression(Expression e, Attributes attrs) {
      Contract.Requires(e != null);
      E = e;
      Attributes = attrs;
    }

    public AttributedExpression(Expression e, AssertLabel/*?*/ label, Attributes attrs) {
      Contract.Requires(e != null);
      E = e;
      Label = label;
      Attributes = attrs;
    }

    public void AddCustomizedErrorMessage(IToken tok, string s) {
      var args = new List<Expression>() { new StringLiteralExpr(tok, s, true) };
      IToken openBrace = tok;
      IToken closeBrace = new Token(tok.line, tok.col + 7 + s.Length + 1); // where 7 = length(":error ")
      this.Attributes = new UserSuppliedAttributes(tok, openBrace, closeBrace, args, this.Attributes);
    }
  }

  public class FrameExpression {
    public readonly IToken tok;
    public readonly Expression E;  // may be a WildcardExpr
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
      Contract.Invariant(!(E is WildcardExpr) || FieldName == null && Field == null);
    }

    public readonly string FieldName;
    public Field Field;  // filled in during resolution (but is null if FieldName is)

    /// <summary>
    /// If a "fieldName" is given, then "tok" denotes its source location.  Otherwise, "tok"
    /// denotes the source location of "e".
    /// </summary>
    public FrameExpression(IToken tok, Expression e, string fieldName) {
      Contract.Requires(tok != null);
      Contract.Requires(e != null);
      Contract.Requires(!(e is WildcardExpr) || fieldName == null);
      this.tok = tok;
      E = e;
      FieldName = fieldName;
    }
  }

  /// <summary>
  /// This class represents a piece of concrete syntax in the parse tree.  During resolution,
  /// it gets "replaced" by the expression in "ResolvedExpression".
  /// </summary>
  public abstract class ConcreteSyntaxExpression : Expression
  {
    public Expression ResolvedExpression;  // filled in during resolution; after resolution, manipulation of "this" should proceed as with manipulating "this.ResolvedExpression"
    public ConcreteSyntaxExpression(IToken tok)
      : base(tok) {
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        if (ResolvedExpression != null) {
          yield return ResolvedExpression;
        }
      }
    }

    public override IEnumerable<Type> ComponentTypes => ResolvedExpression.ComponentTypes;
  }

  /// <summary>
  /// This class represents a piece of concrete syntax in the parse tree.  During resolution,
  /// it gets "replaced" by the statement in "ResolvedStatement".
  /// Adapted from ConcreteSyntaxStatement
  /// </summary>
  public abstract class ConcreteSyntaxStatement : Statement
  {
    public Statement ResolvedStatement;  // filled in during resolution; after resolution, manipulation of "this" should proceed as with manipulating "this.ResolvedExpression"
    public ConcreteSyntaxStatement(IToken tok, IToken endtok)
      : base(tok, endtok) {
    }
    public ConcreteSyntaxStatement(IToken tok, IToken endtok, Attributes attrs)
      : base(tok, endtok, attrs) {
    }
    public override IEnumerable<Statement> SubStatements {
      get {
          yield return ResolvedStatement;
      }
    }
  }
  public class ParensExpression : ConcreteSyntaxExpression
  {
    public readonly Expression E;
    public ParensExpression(IToken tok, Expression e)
      : base(tok) {
      E = e;
    }
  }

  public class TypeExpr : ParensExpression
  {
    public readonly Type T;
    public TypeExpr(IToken tok, Expression e, Type t)
      : base(tok, e)
    {
      Contract.Requires(t != null);
      T = t;
    }

    public static Expression MaybeTypeExpr(Expression e, Type t) {
      if (t == null) {
        return e;
      } else {
        return new TypeExpr(e.tok, e, t);
      }
    }
  }

  public class DatatypeUpdateExpr : ConcreteSyntaxExpression
  {
    public readonly Expression Root;
    public readonly List<Tuple<IToken, string, Expression>> Updates;
    public List<DatatypeCtor> LegalSourceConstructors;  // filled in by resolution
    public DatatypeUpdateExpr(IToken tok, Expression root, List<Tuple<IToken, string, Expression>> updates)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(root != null);
      Contract.Requires(updates != null);
      Contract.Requires(updates.Count != 0);
      Root = root;
      Updates = updates;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        if (ResolvedExpression == null) {
          yield return Root;
          foreach (var update in Updates) {
            yield return update.Item3;
          }
        } else {
          foreach (var e in base.SubExpressions) {
            yield return e;
          }
        }
      }
    }
  }

  /// <summary>
  /// An AutoGeneratedExpression is simply a wrapper around an expression.  This expression tells the generation of hover text (in the Dafny IDE)
  /// that the expression was no supplied directly in the program text and should therefore be ignored.  In other places, an AutoGeneratedExpression
  /// is just a parenthesized expression, which means that it works just the like expression .E that it contains.
  /// (Ironically, AutoGeneratedExpression, which is like the antithesis of concrete syntax, inherits from ConcreteSyntaxExpression, which perhaps
  /// should rather have been called SemanticsNeutralExpressionWrapper.)
  /// </summary>
  public class AutoGeneratedExpression : ParensExpression
  {
    public AutoGeneratedExpression(IToken tok, Expression e)
      : base(tok, e) {
      Contract.Requires(tok != null);
      Contract.Requires(e != null);
    }

    /// <summary>
    /// This maker method takes a resolved expression "e" and wraps a resolved AutoGeneratedExpression
    /// around it.
    /// </summary>
    public static AutoGeneratedExpression Create(Expression e) {
      Contract.Requires(e != null);
      var a = new AutoGeneratedExpression(e.tok, e);
      a.type = e.Type;
      a.ResolvedExpression = e;
      return a;
    }
  }

  /// <summary>
  /// When an actual parameter is omitted for a formal with a default value, the positional resolved
  /// version of the actual parameter will have a DefaultValueExpression value. This has three
  /// advantages:
  /// * It allows the entire module to be resolved before any substitutions take place.
  /// * It gives a good place to check for default-value expressions that would give rise to an
  ///   infinite expansion.
  /// * It preserves the pre-substitution form, which gives compilers a chance to avoid re-evaluation
  ///   of actual parameters used in other default-valued expressions.
  ///
  /// Note. Since DefaultValueExpression is a wrapper around another expression and can in several
  /// places be expanded according to its ResolvedExpression, it is convenient to make DefaultValueExpression
  /// inherit from ConcreteSyntaxExpression. However, there are some places in the code where
  /// one then needs to pay attention to DefaultValueExpression's. Such places would be more
  /// conspicuous if DefaultValueExpression were not an Expression at all. At the time of this
  /// writing, a change to a separate type has shown to be more hassle than the need for special
  /// attention to DefaultValueExpression's in some places.
  /// </summary>
  public class DefaultValueExpression : ConcreteSyntaxExpression {
    public readonly Formal Formal;
    public readonly Expression Receiver;
    public readonly Dictionary<IVariable, Expression> SubstMap;
    public readonly Dictionary<TypeParameter, Type> TypeMap;

    public DefaultValueExpression(IToken tok, Formal formal,
      Expression/*?*/ receiver, Dictionary<IVariable, Expression> substMap, Dictionary<TypeParameter, Type> typeMap)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(formal != null);
      Contract.Requires(formal.DefaultValue != null);
      Contract.Requires(substMap != null);
      Contract.Requires(typeMap != null);
      Formal = formal;
      Receiver = receiver;
      SubstMap = substMap;
      TypeMap = typeMap;
      Type = Resolver.SubstType(formal.Type, typeMap);
    }
  }

  /// <summary>
  /// A NegationExpression e represents the value -e and is syntactic shorthand
  /// for 0-e (for integers) or 0.0-e (for reals).
  /// </summary>
  public class NegationExpression : ConcreteSyntaxExpression
  {
    public readonly Expression E;
    public NegationExpression(IToken tok, Expression e)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(e != null);
      E = e;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        if (ResolvedExpression == null) {
          // the expression hasn't yet been turned into a resolved expression, so use .E as the subexpression
          yield return E;
        } else {
          foreach (var ee in base.SubExpressions) {
            yield return ee;
          }
        }
      }
    }
  }

  public class ChainingExpression : ConcreteSyntaxExpression
  {
    public readonly List<Expression> Operands;
    public readonly List<BinaryExpr.Opcode> Operators;
    public readonly List<IToken> OperatorLocs;
    public readonly List<Expression/*?*/> PrefixLimits;
    public readonly Expression E;
    public ChainingExpression(IToken tok, List<Expression> operands, List<BinaryExpr.Opcode> operators, List<IToken> operatorLocs, List<Expression/*?*/> prefixLimits)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(operands != null);
      Contract.Requires(operators != null);
      Contract.Requires(operatorLocs != null);
      Contract.Requires(prefixLimits != null);
      Contract.Requires(1 <= operators.Count);
      Contract.Requires(operands.Count == operators.Count + 1);
      Contract.Requires(operatorLocs.Count == operators.Count);
      Contract.Requires(prefixLimits.Count == operators.Count);
      // Additional preconditions apply, see Contract.Assume's below

      Operands = operands;
      Operators = operators;
      OperatorLocs = operatorLocs;
      PrefixLimits = prefixLimits;
      Expression desugaring;
      // Compute the desugaring
      if (operators[0] == BinaryExpr.Opcode.Disjoint) {
        Expression acc = operands[0];  // invariant:  "acc" is the union of all operands[j] where j <= i
        desugaring = new BinaryExpr(operatorLocs[0], operators[0], operands[0], operands[1]);
        for (int i = 0; i < operators.Count; i++) {
          Contract.Assume(operators[i] == BinaryExpr.Opcode.Disjoint);
          var opTok = operatorLocs[i];
          var e = new BinaryExpr(opTok, BinaryExpr.Opcode.Disjoint, acc, operands[i + 1]);
          desugaring = new BinaryExpr(opTok, BinaryExpr.Opcode.And, desugaring, e);
          acc = new BinaryExpr(opTok, BinaryExpr.Opcode.Add, acc, operands[i + 1]);
        }
      } else {
        desugaring = null;
        for (int i = 0; i < operators.Count; i++) {
          var opTok = operatorLocs[i];
          var op = operators[i];
          Contract.Assume(op != BinaryExpr.Opcode.Disjoint);
          var k = prefixLimits[i];
          Contract.Assume(k == null || op == BinaryExpr.Opcode.Eq || op == BinaryExpr.Opcode.Neq);
          var e0 = operands[i];
          var e1 = operands[i + 1];
          Expression e;
          if (k == null) {
            e = new BinaryExpr(opTok, op, e0, e1);
          } else {
            e = new TernaryExpr(opTok, op == BinaryExpr.Opcode.Eq ? TernaryExpr.Opcode.PrefixEqOp : TernaryExpr.Opcode.PrefixNeqOp, k, e0, e1);
          }
          desugaring = desugaring == null ? e : new BinaryExpr(opTok, BinaryExpr.Opcode.And, desugaring, e);
        }
      }
      E = desugaring;
    }
  }

  /// <summary>
  /// The parsing and resolution/type checking of expressions of the forms
  ///   0. ident &lt; Types &gt;
  ///   1. Expr . ident &lt; Types &gt;
  ///   2. Expr ( Exprs )
  ///   3. Expr [ Exprs ]
  ///   4. Expr [ Expr .. Expr ]
  /// is done as follows.  These forms are parsed into the following AST classes:
  ///   0. NameSegment
  ///   1. ExprDotName
  ///   2. ApplySuffix
  ///   3. SeqSelectExpr or MultiSelectExpr
  ///   4. SeqSelectExpr
  ///
  /// The first three of these inherit from ConcreteSyntaxExpression.  The resolver will resolve
  /// these into:
  ///   0. IdentifierExpr or MemberSelectExpr (with .Lhs set to ImplicitThisExpr or StaticReceiverExpr)
  ///   1. IdentifierExpr or MemberSelectExpr
  ///   2. FuncionCallExpr or ApplyExpr
  ///
  /// The IdentifierExpr's that forms 0 and 1 can turn into sometimes denote the name of a module or
  /// type.  The .Type field of the corresponding resolved expressions are then the special Type subclasses
  /// ResolutionType_Module and ResolutionType_Type, respectively.  These will not be seen by the
  /// verifier or compiler, since, in a well-formed program, the verifier and compiler will use the
  /// .ResolvedExpr field of whatever form-1 expression contains these.
  ///
  /// Notes:
  ///   * IdentifierExpr and FunctionCallExpr are resolved-only expressions (that is, they don't contain
  ///     all the syntactic components that were used to parse them).
  ///   * Rather than the current SeqSelectExpr/MultiSelectExpr split of forms 3 and 4, it would
  ///     seem more natural to refactor these into 3: IndexSuffixExpr and 4: RangeSuffixExpr.
  /// </summary>
  abstract public class SuffixExpr : ConcreteSyntaxExpression {
    public readonly Expression Lhs;
    public SuffixExpr(IToken tok, Expression lhs)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(lhs != null);
      Lhs = lhs;
    }
  }

  public class NameSegment : ConcreteSyntaxExpression
  {
    public readonly string Name;
    public readonly List<Type> OptTypeArguments;
    public NameSegment(IToken tok, string name, List<Type> optTypeArguments)
      : base(tok) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(optTypeArguments == null || optTypeArguments.Count > 0);
      Name = name;
      OptTypeArguments = optTypeArguments;
    }
  }

  /// <summary>
  /// An ExprDotName desugars into either an IdentifierExpr (if the Lhs is a static name) or a MemberSelectExpr (if the Lhs is a computed expression).
  /// </summary>
  public class ExprDotName : SuffixExpr
  {
    public readonly string SuffixName;
    public readonly List<Type> OptTypeArguments;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(SuffixName != null);
    }

    public ExprDotName(IToken tok, Expression obj, string suffixName, List<Type> optTypeArguments)
      : base(tok, obj) {
      Contract.Requires(tok != null);
      Contract.Requires(obj != null);
      Contract.Requires(suffixName != null);
      this.SuffixName = suffixName;
      OptTypeArguments = optTypeArguments;
    }
  }

  /// <summary>
  /// An ApplySuffix desugars into either an ApplyExpr or a FunctionCallExpr
  /// </summary>
  public class ApplySuffix : SuffixExpr {
    public readonly IToken/*?*/ AtTok;
    public readonly ActualBindings Bindings;
    public List<Expression> Args => Bindings.Arguments;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Args != null);
    }

    public ApplySuffix(IToken tok, IToken/*?*/ atLabel, Expression lhs, List<ActualBinding> args)
      : base(tok, lhs) {
      Contract.Requires(tok != null);
      Contract.Requires(lhs != null);
      Contract.Requires(cce.NonNullElements(args));
      AtTok = atLabel;
      Bindings = new ActualBindings(args);
    }
  }

  public class Specification<T> where T : class
  {
    public readonly List<T> Expressions;

    [ContractInvariantMethod]
    private void ObjectInvariant()
    {
      Contract.Invariant(Expressions == null || cce.NonNullElements<T>(Expressions));
    }

    public Specification(List<T> exprs, Attributes attrs)
    {
      Contract.Requires(exprs == null || cce.NonNullElements<T>(exprs));
      Expressions = exprs;
      Attributes = attrs;
    }

    private Attributes attributes;
    public Attributes Attributes
    {
      get
      {
        return attributes;
      }
      set
      {
        attributes = value;
      }
    }

    public bool HasAttributes()
    {
      return Attributes != null;
    }
  }

  public class BottomUpVisitor
  {
    public void Visit(IEnumerable<Expression> exprs) {
      exprs.Iter(Visit);
    }
    public void Visit(IEnumerable<Statement> stmts) {
      stmts.Iter(Visit);
    }
    public void Visit(AttributedExpression expr) {
      Visit(expr.E);
    }
    public void Visit(FrameExpression expr) {
      Visit(expr.E);
    }
    public void Visit(IEnumerable<AttributedExpression> exprs) {
      exprs.Iter(Visit);
    }
    public void Visit(IEnumerable<FrameExpression> exprs) {
      exprs.Iter(Visit);
    }
    public void Visit(ICallable decl) {
      if (decl is Function f) {
        Visit(f);
      } else if (decl is Method m) {
        Visit(m);
      } else if (decl is TypeSynonymDecl tsd) {
        Visit(tsd);
      } else if (decl is NewtypeDecl ntd) {
        Visit(ntd);
      }
      //TODO More?
    }

    public void Visit(SubsetTypeDecl ntd) {
      if (ntd.Constraint != null) Visit(ntd.Constraint);
      if (ntd.Witness != null) Visit(ntd.Witness);
    }
    public void Visit(NewtypeDecl ntd) {
      if (ntd.Constraint != null) Visit(ntd.Constraint);
      if (ntd.Witness != null) Visit(ntd.Witness);
    }
    public void Visit(Method method) {
      Visit(method.Req);
      Visit(method.Mod.Expressions);
      Visit(method.Ens);
      Visit(method.Decreases.Expressions);
      if (method.Body != null) { Visit(method.Body); }
      //TODO More?
    }
    public void Visit(Function function) {
      Visit(function.Req);
      Visit(function.Reads);
      Visit(function.Ens);
      Visit(function.Decreases.Expressions);
      if (function.Body != null) { Visit(function.Body); }
      //TODO More?
    }
    public void Visit(Expression expr) {
      Contract.Requires(expr != null);
      // recursively visit all subexpressions and all substatements
      expr.SubExpressions.Iter(Visit);
      if (expr is StmtExpr) {
        // a StmtExpr also has a sub-statement
        var e = (StmtExpr)expr;
        Visit(e.S);
      }
      VisitOneExpr(expr);
    }
    public void Visit(Statement stmt) {
      Contract.Requires(stmt != null);
      // recursively visit all subexpressions and all substatements
      stmt.SubExpressions.Iter(Visit);
      stmt.SubStatements.Iter(Visit);
      VisitOneStmt(stmt);
    }
    protected virtual void VisitOneExpr(Expression expr) {
      Contract.Requires(expr != null);
      // by default, do nothing
    }
    protected virtual void VisitOneStmt(Statement stmt) {
      Contract.Requires(stmt != null);
      // by default, do nothing
    }
  }
  public class TopDownVisitor<State>
  {
    public void Visit(Expression expr, State st) {
      Contract.Requires(expr != null);
      if (VisitOneExpr(expr, ref st)) {
        // recursively visit all subexpressions and all substatements
        expr.SubExpressions.Iter(e => Visit(e, st));
        if (expr is StmtExpr) {
          // a StmtExpr also has a sub-statement
          var e = (StmtExpr)expr;
          Visit(e.S, st);
        }
      }
    }
    public void Visit(Statement stmt, State st) {
      Contract.Requires(stmt != null);
      if (VisitOneStmt(stmt, ref st)) {
        // recursively visit all subexpressions and all substatements
        stmt.SubExpressions.Iter(e => Visit(e, st));
        stmt.SubStatements.Iter(s => Visit(s, st));
      }
    }
    public void Visit(IEnumerable<Expression> exprs, State st) {
      exprs.Iter(e => Visit(e, st));
    }
    public void Visit(IEnumerable<Statement> stmts, State st) {
      stmts.Iter(e => Visit(e, st));
    }
    public void Visit(AttributedExpression expr, State st) {
      Visit(expr.E, st);
    }
    public void Visit(FrameExpression expr, State st) {
      Visit(expr.E, st);
    }
    public void Visit(IEnumerable<AttributedExpression> exprs, State st) {
      exprs.Iter(e => Visit(e, st));
    }
    public void Visit(IEnumerable<FrameExpression> exprs, State st) {
      exprs.Iter(e => Visit(e, st));
    }
    public void Visit(ICallable decl, State st) {
      if (decl is Function) {
        Visit((Function)decl, st);
      } else if (decl is Method) {
        Visit((Method)decl, st);
      }
      //TODO More?
    }
    public void Visit(Method method, State st) {
      Visit(method.Ens, st);
      Visit(method.Req, st);
      Visit(method.Mod.Expressions, st);
      Visit(method.Decreases.Expressions, st);
      if (method.Body != null) { Visit(method.Body, st); }
      //TODO More?
    }
    public void Visit(Function function, State st) {
      Visit(function.Ens, st);
      Visit(function.Req, st);
      Visit(function.Reads, st);
      Visit(function.Decreases.Expressions, st);
      if (function.Body != null) { Visit(function.Body, st); }
      //TODO More?
    }
    /// <summary>
    /// Visit one expression proper.  This method is invoked before it is invoked on the
    /// sub-parts (sub-expressions and sub-statements).  A return value of "true" says to
    /// continue invoking the method on sub-parts, whereas "false" says not to do so.
    /// The on-return value of "st" is the value that is passed to sub-parts.
    /// </summary>
    protected virtual bool VisitOneExpr(Expression expr, ref State st) {
      Contract.Requires(expr != null);
      return true;  // by default, visit the sub-parts with the same "st"
    }
    /// <summary>
    /// Visit one statement proper.  For the rest of the description of what this method
    /// does, see VisitOneExpr.
    /// </summary>
    protected virtual bool VisitOneStmt(Statement stmt, ref State st) {
      Contract.Requires(stmt != null);
      return true;  // by default, visit the sub-parts with the same "st"
    }
  }
}
