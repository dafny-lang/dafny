//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.Collections;
using System.Text;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics.Contracts;
using System.Numerics;
using System.Linq;
using System.Diagnostics;
using System.Threading;
using Microsoft.Boogie;
using Microsoft.Dafny.Auditor;
using Action = System.Action;

namespace Microsoft.Dafny {
  [System.AttributeUsage(System.AttributeTargets.Field | System.AttributeTargets.Property)]
  public class FilledInDuringTranslationAttribute : System.Attribute { }
  [System.AttributeUsage(System.AttributeTargets.Field | System.AttributeTargets.Property)]
  public class FilledInDuringResolutionAttribute : System.Attribute { }

  public abstract class INode {

    public IToken tok = Token.NoToken;
    [DebuggerBrowsable(DebuggerBrowsableState.Never)]
    public IToken Tok {
      get => tok;
      set => tok = value;
    }

    /// <summary>
    /// These children should be such that they contain information produced by resolution such as inferred types
    /// and resolved references. However, they should not be so transformed that source location from the initial
    /// program is lost. As an example, the pattern matching compilation may deduplicate nodes from the original AST,
    /// losing source location information, so those transformed nodes should not be returned by this property.
    /// </summary>
    public abstract IEnumerable<INode> Children { get; }

    public IEnumerable<INode> Descendants() {
      return Children.Concat(Children.SelectMany(n => n.Descendants()));
    }

    public virtual IEnumerable<AssumptionDescription> Assumptions() {
      return Enumerable.Empty<AssumptionDescription>();
    }

    public ISet<INode> Visit(Func<INode, bool> beforeChildren = null, Action<INode> afterChildren = null) {
      beforeChildren ??= node => true;
      afterChildren ??= node => { };

      var visited = new HashSet<INode>();
      var toVisit = new LinkedList<INode>();
      toVisit.AddFirst(this);
      while (toVisit.Any()) {
        var current = toVisit.First();
        toVisit.RemoveFirst();
        if (!visited.Add(current)) {
          continue;
        }

        if (!beforeChildren(current)) {
          continue;
        }

        var nodeAfterChildren = toVisit.First;
        foreach (var child in current.Children) {
          if (child == null) {
            throw new InvalidOperationException($"Object of type {current.GetType()} has null child");
          }

          if (nodeAfterChildren == null) {
            toVisit.AddLast(child);
          } else {
            toVisit.AddBefore(nodeAfterChildren, child);
          }
        }

        afterChildren(current);
      }

      return visited;
    }

    protected RangeToken rangeToken = null;

    // Contains tokens that did not make it in the AST but are part of the expression,
    // Enables ranges to be correct.
    // TODO: Re-add format tokens where needed until we put all the formatting to replace the tok of every expression
    internal IToken[] FormatTokens = null;

    public virtual RangeToken RangeToken {
      get {
        if (rangeToken == null) {
          if (tok is RangeToken tokAsRange) {
            rangeToken = tokAsRange;
          } else {
            var startTok = tok;
            var endTok = tok;

            void UpdateStartEndToken(IToken token1) {
              if (token1.Filename != tok.Filename) {
                return;
              }

              if (token1.pos < startTok.pos) {
                startTok = token1;
              }

              if (token1.pos + token1.val.Length > endTok.pos + endTok.val.Length) {
                endTok = token1;
              }
            }

            void UpdateStartEndTokRecursive(INode node) {
              if (node is null) {
                return;
              }

              if (node.tok.Filename != tok.Filename || node is Expression { IsImplicit: true } ||
                  node is DefaultValueExpression) {
                // Ignore any auto-generated expressions.
              } else if (node != this && node.RangeToken != null) {
                UpdateStartEndToken(node.StartToken);
                UpdateStartEndToken(node.EndToken);
              } else {
                UpdateStartEndToken(node.tok);
                node.Children.Iter(UpdateStartEndTokRecursive);
              }
            }

            UpdateStartEndTokRecursive(this);

            if (FormatTokens != null) {
              foreach (var token in FormatTokens) {
                UpdateStartEndToken(token);
              }
            }

            rangeToken = new RangeToken(startTok, endTok);
          }
        }

        if (rangeToken.Filename == null) {
          rangeToken.Filename = tok.Filename;
        }

        return rangeToken;
      }
      set => rangeToken = value;
    }

    public IToken StartToken => RangeToken?.StartToken;

    public IToken EndToken => RangeToken?.EndToken;

    protected IReadOnlyList<IToken> OwnedTokensCache;

    /// <summary>
    /// A token is owned by a node if it was used to parse this node,
    /// but is not owned by any of this Node's children
    /// </summary>
    public IEnumerable<IToken> OwnedTokens {
      get {
        if (OwnedTokensCache != null) {
          return OwnedTokensCache;
        }

        var startToEndTokenNotOwned =
          Children.Where(child => child.StartToken != null && child.EndToken != null)
            .ToDictionary(child => child.StartToken!, child => child.EndToken!);

        var result = new List<IToken>();
        if (StartToken == null) {
          Contract.Assume(EndToken == null);
        } else {
          Contract.Assume(EndToken != null);
          var tmpToken = StartToken;
          while (tmpToken != null && tmpToken != EndToken.Next) {
            if (startToEndTokenNotOwned.TryGetValue(tmpToken, out var endNotOwnedToken)) {
              tmpToken = endNotOwnedToken;
            } else if (tmpToken.filename != null) {
              result.Add(tmpToken);
            }

            tmpToken = tmpToken.Next;
          }
        }


        OwnedTokensCache = result;

        return OwnedTokensCache;
      }
    }
  }

  public interface IDeclarationOrUsage {
    IToken NameToken { get; }
  }

  public interface IHasUsages : IDeclarationOrUsage {
    public IEnumerable<IDeclarationOrUsage> GetResolvedDeclarations();
  }
  public class Program : INode {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(FullName != null);
      Contract.Invariant(DefaultModule != null);
    }

    public readonly string FullName;
    [FilledInDuringResolution] public Dictionary<ModuleDefinition, ModuleSignature> ModuleSigs;
    // Resolution essentially flattens the module hierarchy, for
    // purposes of translation and compilation.
    [FilledInDuringResolution] public List<ModuleDefinition> CompileModules;
    // Contains the definitions to be used for compilation.

    public Method MainMethod; // Method to be used as main if compiled
    public readonly ModuleDecl DefaultModule;
    public readonly ModuleDefinition DefaultModuleDef;
    public readonly BuiltIns BuiltIns;
    public ErrorReporter Reporter { get; set; }

    public Program(string name, [Captured] ModuleDecl module, [Captured] BuiltIns builtIns, ErrorReporter reporter) {
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(module is LiteralModuleDecl);
      Contract.Requires(reporter != null);
      FullName = name;
      DefaultModule = module;
      DefaultModuleDef = (DefaultModuleDecl)((LiteralModuleDecl)module).ModuleDef;
      BuiltIns = builtIns;
      this.Reporter = reporter;
      ModuleSigs = new Dictionary<ModuleDefinition, ModuleSignature>();
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

    public string Name {
      get {
        try {
          return System.IO.Path.GetFileName(FullName);
        } catch (ArgumentException) {
          return FullName;
        }
      }
    }

    public IToken GetFirstTopLevelToken() {
      return DefaultModuleDef.GetFirstTopLevelToken();
    }

    public override IEnumerable<INode> Children => new[] { DefaultModule };

    public IEnumerable<INode> ConcreteChildren => Children;
  }

  public class Include : INode, IComparable {
    public string IncluderFilename { get; }
    public string IncludedFilename { get; }
    public string CanonicalPath { get; }
    public bool CompileIncludedCode { get; }
    public bool ErrorReported;

    public Include(IToken tok, string includer, string theFilename, bool compileIncludedCode) {
      this.tok = tok;
      this.IncluderFilename = includer;
      this.IncludedFilename = theFilename;
      this.CanonicalPath = DafnyFile.Canonicalize(theFilename);
      this.ErrorReported = false;
      CompileIncludedCode = compileIncludedCode;
    }

    public int CompareTo(object obj) {
      var i = obj as Include;
      if (i != null) {
        return this.CanonicalPath.CompareTo(i.CanonicalPath);
      } else {
        throw new NotImplementedException();
      }
    }

    public override IEnumerable<INode> Children => Enumerable.Empty<INode>();
  }

  /// <summary>
  /// An expression introducting bound variables
  /// </summary>
  public interface IBoundVarsBearingExpression : IRegion {
    public IEnumerable<BoundVar> AllBoundVars {
      get;
    }
  }

  /// <summary>
  /// A class implementing this interface is one that can carry attributes.
  /// </summary>
  public interface IAttributeBearingDeclaration {
    Attributes Attributes { get; }
  }

  public class Attributes : INode {
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
    /// Returns first occurrence of an attribute named <c>nm</c>, or <c>null</c> if there is no such
    /// attribute.
    /// </summary>
    [Pure]
    public static Attributes/*?*/ Find(Attributes attrs, string nm) {
      Contract.Requires(nm != null);
      return attrs.AsEnumerable().FirstOrDefault(attr => attr.Name == nm);
    }

    /// <summary>
    /// Returns true if "nm" is a specified attribute.  If it is, then:
    /// - if the attribute is {:nm true}, then value==true
    /// - if the attribute is {:nm false}, then value==false
    /// - if the attribute is anything else, then value returns as whatever it was passed in as.
    /// This method does NOT use type information of the attribute arguments, so it can safely
    /// be called very early during resolution before types are available and names have been resolved.
    /// </summary>
    [Pure]
    public static bool ContainsBool(Attributes attrs, string nm, ref bool value) {
      Contract.Requires(nm != null);
      var attr = attrs.AsEnumerable().FirstOrDefault(attr => attr.Name == nm);
      if (attr == null) {
        return false;
      }

      if (attr.Args.Count == 1 && attr.Args[0] is LiteralExpr { Value: bool v }) {
        value = v;
      }
      return true;
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

    public override IEnumerable<INode> Children => Args.Concat<INode>(
      Prev == null
        ? Enumerable.Empty<INode>()
        : new List<INode> { Prev });
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

  public class UserSuppliedAttributes : Attributes {
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

  /// <summary>
  /// This interface is used by the Dafny IDE.
  /// </summary>
  public interface IRegion {
    IToken BodyStartTok { get; }
    IToken BodyEndTok { get; }
  }

  public interface INamedRegion : IRegion {
    string Name { get; }
  }

  [ContractClass(typeof(IVariableContracts))]
  public interface IVariable : IDeclarationOrUsage {
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
    static FreshIdGenerator CompileNameIdGenerator = new FreshIdGenerator();
    string AssignUniqueName(FreshIdGenerator generator);
    string SanitizedName {
      get;
    }
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
  public abstract class IVariableContracts : INode, IVariable {
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
    public string SanitizedName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
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
    public string AssignUniqueName(FreshIdGenerator generator) {
      Contract.Ensures(Contract.Result<string>() != null);
      throw new NotImplementedException();
    }

    public abstract IToken NameToken { get; }
  }

  public abstract class NonglobalVariable : INode, IVariable {
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
    public string DisplayName =>
      LocalVariable.DisplayNameHelper(this);

    private string uniqueName;
    public string UniqueName => uniqueName;
    public bool HasBeenAssignedUniqueName => uniqueName != null;
    public string AssignUniqueName(FreshIdGenerator generator) {
      return uniqueName ??= generator.FreshId(Name + "#");
    }

    static char[] specialChars = { '\'', '_', '?', '\\', '#' };
    /// <summary>
    /// Mangle name <c>nm</c> by replacing and escaping characters most likely to cause issues when compiling and
    /// when translating to Boogie.  This transformation is injective.
    /// </summary>
    /// <returns>A string uniquely determined from <c>nm</c>, containing none of the characters in
    /// <c>specialChars</c>.</returns>
    public static string SanitizeName(string nm) {
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

    private string sanitizedName;
    public virtual string SanitizedName =>
      sanitizedName ??= $"_{IVariable.CompileNameIdGenerator.FreshNumericId()}_{SanitizeName(Name)}";

    protected string compileName;
    public virtual string CompileName =>
      compileName ??= SanitizedName;

    Type type;
    public bool IsTypeExplicit = false;
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

    public NonglobalVariable(IToken tok, string name, Type type, bool isGhost) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      this.tok = tok;
      this.name = name;
      this.type = type;
      this.isGhost = isGhost;
    }

    public IToken NameToken => tok;
    public override IEnumerable<INode> Children => IsTypeExplicit ? Type.Nodes : Enumerable.Empty<INode>();
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
    public readonly bool IsOlder;
    public readonly string NameForCompilation;

    public Formal(IToken tok, string name, Type type, bool inParam, bool isGhost, Expression defaultValue,
      bool isOld = false, bool isNameOnly = false, bool isOlder = false, string nameForCompilation = null)
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
      IsOlder = isOlder;
      NameForCompilation = nameForCompilation ?? name;
    }

    public bool HasName {
      get {
        return !Name.StartsWith("#");
      }
    }

    private string sanitizedName;
    public override string SanitizedName =>
      sanitizedName ??= SanitizeName(Name); // No unique-ification
    public override string CompileName =>
      compileName ??= SanitizeName(NameForCompilation);
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
    public override bool IsMutable => false;

    public BoundVar(IToken tok, string name, Type type)
      : base(tok, name, type, false) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
    }
  }

  /// <summary>
  /// A QuantifiedVar is a bound variable used in a quantifier such as "forall x :: ...",
  /// a comprehension such as "set x | 0 <= x < 10", etc.
  /// In addition to its type, which may be inferred, it can have an optional domain collection expression
  /// (x <- C) and an optional range boolean expressions (x | E).
  /// </summary>
  [DebuggerDisplay("Quantified<{name}>")]
  public class QuantifiedVar : BoundVar {
    public readonly Expression Domain;
    public readonly Expression Range;

    public QuantifiedVar(IToken tok, string name, Type type, Expression domain, Expression range)
      : base(tok, name, type) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      Domain = domain;
      Range = range;
    }

    /// <summary>
    /// Map a list of quantified variables to an eqivalent list of bound variables plus a single range expression.
    /// The transformation looks like this in general:
    ///
    /// x1 <- C1 | E1, ..., xN <- CN | EN
    ///
    /// becomes:
    ///
    /// x1, ... xN | x1 in C1 && E1 && ... && xN in CN && EN
    ///
    /// Note the result will be null rather than "true" if there are no such domains or ranges.
    /// Some quantification contexts (such as comprehensions) will replace this with "true".
    /// </summary>
    public static void ExtractSingleRange(List<QuantifiedVar> qvars, out List<BoundVar> bvars, out Expression range) {
      bvars = new List<BoundVar>();
      range = null;

      foreach (var qvar in qvars) {
        BoundVar bvar = new BoundVar(qvar.tok, qvar.Name, qvar.SyntacticType);
        bvars.Add(bvar);

        if (qvar.Domain != null) {
          // Attach a token wrapper so we can produce a better error message if the domain is not a collection
          var domainWithToken = QuantifiedVariableDomainCloner.Instance.CloneExpr(qvar.Domain);
          var inDomainExpr = new BinaryExpr(domainWithToken.tok, BinaryExpr.Opcode.In, new IdentifierExpr(bvar.tok, bvar), domainWithToken);
          range = range == null ? inDomainExpr : new BinaryExpr(domainWithToken.tok, BinaryExpr.Opcode.And, range, inDomainExpr);
        }

        if (qvar.Range != null) {
          // Attach a token wrapper so we can produce a better error message if the range is not a boolean expression
          var rangeWithToken = QuantifiedVariableRangeCloner.Instance.CloneExpr(qvar.Range);
          range = range == null ? qvar.Range : new BinaryExpr(rangeWithToken.tok, BinaryExpr.Opcode.And, range, rangeWithToken);
        }
      }
    }
  }

  public class ActualBinding : INode {
    public readonly IToken /*?*/ FormalParameterName;
    public readonly Expression Actual;
    public readonly bool IsGhost;

    public override IEnumerable<INode> Children => new List<INode> { Actual }.Where(x => x != null);
    // Names are owned by the method call

    public ActualBinding(IToken /*?*/ formalParameterName, Expression actual, bool isGhost = false) {
      Contract.Requires(actual != null);
      FormalParameterName = formalParameterName;
      Actual = actual;
      IsGhost = isGhost;
    }
  }

  public class ActualBindings : INode {
    public readonly List<ActualBinding> ArgumentBindings;

    public ActualBindings(List<ActualBinding> argumentBindings) {
      Contract.Requires(argumentBindings != null);
      ArgumentBindings = argumentBindings;
    }

    public ActualBindings(Cloner cloner, ActualBindings original) {
      ArgumentBindings = original.ArgumentBindings.Select(actualBinding => new ActualBinding(
        actualBinding.FormalParameterName == null ? null : cloner.Tok(actualBinding.FormalParameterName),
        cloner.CloneExpr(actualBinding.Actual))).ToList();
      if (cloner.CloneResolvedFields) {
        arguments = original.Arguments?.Select(cloner.CloneExpr).ToList();
      }
    }

    public ActualBindings(List<Expression> actuals) {
      Contract.Requires(actuals != null);
      ArgumentBindings = actuals.ConvertAll(actual => new ActualBinding(null, actual));
    }

    [FilledInDuringResolution]
    private List<Expression> arguments; // set by ResolveActualParameters during resolution

    public bool WasResolved => arguments != null;

    public List<Expression> Arguments => arguments;

    public void AcceptArgumentExpressionsAsExactParameterList(List<Expression> args = null) {
      Contract.Requires(!WasResolved); // this operation should be done at most once
      Contract.Assume(ArgumentBindings.TrueForAll(arg => arg.Actual.WasResolved()));
      arguments = args ?? ArgumentBindings.ConvertAll(binding => binding.Actual);
    }

    public override IEnumerable<INode> Children => arguments == null ? ArgumentBindings : arguments;
  }

  class QuantifiedVariableDomainCloner : Cloner {
    public static readonly QuantifiedVariableDomainCloner Instance = new();
    private QuantifiedVariableDomainCloner() { }
    public override Expression CloneExpr(Expression expr) {
      var result = base.CloneExpr(expr);
      if (result is BinaryExpr binaryExpr) {
        binaryExpr.SecondArgumentIsDomainOfQuantifiedVariable = true;
      }
      return result;
    }
  }

  class QuantifiedVariableRangeCloner : Cloner {
    public static readonly QuantifiedVariableRangeCloner Instance = new();
    private QuantifiedVariableRangeCloner() { }
    public override Expression CloneExpr(Expression expr) {
      var result = base.CloneExpr(expr);
      if (result is BinaryExpr binaryExpr) {
        binaryExpr.SecondArgumentIsQuantifiedVariableRange = true;
      }
      return result;
    }
  }

  public class Specification<T> : INode, IAttributeBearingDeclaration
    where T : INode {
    public readonly List<T> Expressions;

    [ContractInvariantMethod]
    private void ObjectInvariant() {
      Contract.Invariant(Expressions == null || cce.NonNullElements<T>(Expressions));
    }

    public Specification(List<T> exprs, Attributes attrs) {
      Contract.Requires(exprs == null || cce.NonNullElements<T>(exprs));
      Expressions = exprs;
      Attributes = attrs;
    }

    public Attributes Attributes { get; set; }

    public bool HasAttributes() {
      return Attributes != null;
    }

    public override IEnumerable<INode> Children => Expressions;
  }

  public class BottomUpVisitor {
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
      if (ntd.Constraint != null) {
        Visit(ntd.Constraint);
      }

      if (ntd.Witness != null) {
        Visit(ntd.Witness);
      }
    }
    public void Visit(NewtypeDecl ntd) {
      if (ntd.Constraint != null) {
        Visit(ntd.Constraint);
      }

      if (ntd.Witness != null) {
        Visit(ntd.Witness);
      }
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
        // a StmtExpr also has a substatement
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
  public class TopDownVisitor<State> {
    public void Visit(Expression expr, State st) {
      Contract.Requires(expr != null);
      if (VisitOneExpr(expr, ref st)) {
        // recursively visit all subexpressions and all substatements
        expr.SubExpressions.Iter(e => Visit(e, st));
        if (expr is StmtExpr) {
          // a StmtExpr also has a substatement
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
    public virtual void Visit(Method method, State st) {
      Visit(method.Ens, st);
      Visit(method.Req, st);
      Visit(method.Mod.Expressions, st);
      Visit(method.Decreases.Expressions, st);
      if (method.Body != null) { Visit(method.Body, st); }
      //TODO More?
    }
    public virtual void Visit(Function function, State st) {
      Visit(function.Ens, st);
      Visit(function.Req, st);
      Visit(function.Reads, st);
      Visit(function.Decreases.Expressions, st);
      if (function.Body != null) { Visit(function.Body, st); }
      //TODO More?
    }
    /// <summary>
    /// Visit one expression proper.  This method is invoked before it is invoked on the
    /// sub-parts (subexpressions and substatements).  A return value of "true" says to
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
