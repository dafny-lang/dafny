#nullable enable
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Numerics;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

static class AttributeBearingDeclaration {
  public static bool IsExtern(this IAttributeBearingDeclaration me, DafnyOptions options) =>
    options.AllowExterns && Attributes.Contains(me.Attributes, "extern");

  public static bool IsExplicitAxiom(this IAttributeBearingDeclaration me) =>
    Attributes.Contains(me.Attributes, "axiom");
}

public record BuiltInAtAttributeArgSyntax(
  String ArgName,
  Type? ArgType, // If null, it means it's not resolved
  bool HasDefaultValue,
  Expression? DefaultValue) {
  public Formal ToFormal() {
    Contract.Assert(ArgType != null);
    return new Formal(Token.NoToken, ArgName, ArgType, true, false,
      HasDefaultValue
        ? DefaultValue ?? (ArgType.IsStringType
          ? new StringLiteralExpr(Token.NoToken, "", false)
          : new StringLiteralExpr(Token.NoToken, "TODO", false))
        : null);
  }
}

public record BuiltInAtAttributeSyntax(
  string Name,
  List<BuiltInAtAttributeArgSyntax> Args) {
  public BuiltInAtAttributeSyntax WithArg(String argName, Type? argType, bool hasDefaultValue, Expression? defaultValue) {
    var c = new List<BuiltInAtAttributeArgSyntax>(Args) {
      new(argName, argType, hasDefaultValue, defaultValue) };
    return this with { Args = c };
  }
}

public class Attributes : TokenNode {
  static BuiltInAtAttributeSyntax B(string name) {
    return new BuiltInAtAttributeSyntax(
      name, new List<BuiltInAtAttributeArgSyntax>());
  }

  private static (Attributes?, (string, IToken)?) A(string name, params Expression[] args) {
    return (new Attributes(name, args.ToList(), null), null);
  }
  private static (Attributes?, (string, IToken)?) Error(string message, IToken tok) {
    return (null, (message, tok));
  }
  
  public static (Attributes? attrs, (string, IToken)? error) ExpandAtAttribute(ModuleResolver resolver, ResolutionContext resolutionContext, Dictionary<TypeParameter, Type> typeMap, Expression atAttribute) {
    var toMatch = atAttribute;
    if (atAttribute is IdentifierExpr) {
      toMatch = new ApplySuffix(atAttribute.tok, null, atAttribute, new List<ActualBinding>(), atAttribute.EndToken);
    }

    if (toMatch is not ApplySuffix { Lhs: IdentifierExpr { Name: var name }, Bindings: var bindings }) {
      return Error("@-Attribute not recognized: " + atAttribute.ToString(), atAttribute.RangeToken);
    }

    var resolution = ResolveLikeDatatypeConstructor(resolver, resolutionContext, typeMap, bindings, toMatch.tok);
    if (!TryGetBuiltinAtAttribute(name, out var b) || b == null) {
      resolver.ResolveExpression(atAttribute, resolutionContext);
      return (null, null);
    }

    if (name != "Induction" && name != "Trigger") {
      var formals = b.Args.Select(
        arg => arg.ToFormal()
      ).ToArray();
      resolution(name, formals);
    } else {
      foreach (var argumentBinding in bindings.ArgumentBindings) {
        resolver.ResolveExpression(argumentBinding.Actual, resolutionContext);
      }
    }

    switch (name) {
      case "Abstemious": {
        return A("abstemious");
      }
      case "Assumption": {
        return A("assumption");
      }
      case "AssumeConcurrent": {
        return A("assume_concurrent");
      }
      case "AutoContracts": {
        return A("autocontracts");
      }
      case "AutoRequires": {
        return A("autoReq");
      }
      case "AutoRevealDependenciesAll": {
        return A1("autoRevealDependencies", bindings);
      }
      case "AutoRevealDependencies": {
        return A1("autoRevealDependencies", bindings);
      }
      case "Axiom": {
        return A("axiom");
      }
      case "Compile": {
        return A1("compile", bindings);
      }
      case "Concurrent": {
        return A("concurrent");
      }
      case "Contradiction": {
        return A("contradiction");
      }
      case "DisableNonlinearArithmetic": {
        return A1("disable-nonlinear-arithmetic", bindings);
      }
      case "Error": {
        if (Get(bindings, 0, out var failureMessage) && failureMessage != null) {
          if (Get(bindings, 1, out var successMessage) && successMessage != null) {
            return A("error", failureMessage, successMessage);
          }

          return A("error", failureMessage);
        }

        return Error("@error requires at least one argument", atAttribute.Tok);
      }
      case "Extern": {
        if (Get(bindings, 0, out var externName) && externName != null) {
          if (Get(bindings, 1, out var moduleName) && moduleName != null) {
            return A("extern", moduleName, externName);
          }

          return A("extern", externName);
        }

        return A("extern");
      }
      case "Focus": {
        return A("focus");
      }
      case "Fuel": {
        if (Get(bindings, 0, out var externName) && externName != null) {
          if (Get(bindings, 1, out var moduleName) && moduleName != null) {
            return A("extern", moduleName, externName);
          }

          return A("extern", externName);
        }

        return A("extern");
      }
      case "Id": {
        return A1("id", bindings);
      }
      case "Induction": {
        return A1("induction", bindings);
      }
      case "IsolateAssertions": {
        return A("isolate_assertions");
      }
      case "NativeType": {
        if (Get(bindings, 0, out var native) && native != null) {
          if (native is LiteralExpr { Value: false }) {
            return A("nativeType", native);
          }

          if (Get(bindings, 1, out var nameExpr) && nameExpr != null) {
            return A("nativeType", nameExpr);
          }
        }

        return A("nativeType");
      }
      case "Options": {
        return A1("options", bindings);
      }
      case "Print": {
        return A("print");
      }
      case "Priority": {
        return A1("priority", bindings);
      }
      case "ResourceLimit": {
        return A1("resource_limit", bindings);
      }
      case "SelectiveChecking": {
        return A("selective_checking");
      }
      case "SplitHere": {
        return A("split_here");
      }
      case "StartCheckingHere": {
        return A("start_checking_here");
      }
      case "Subsumption": {
        return A1("subsumption", bindings);
      }
      case "Synthesize": {
        return A("synthesize");
      }
      case "TimeLimit": {
        return A1("timeLimit", bindings);
      }
      case "TimeLimitMultiplier": {
        return A1("timeLimitMultiplier", bindings);
      }
      case "TailRecursion": {
        return A("tailrecursion");
      }
      case "Test": {
        return A("test");
      }
      case "Transparent": {
        return A("transparent");
      }
      case "Trigger": {
        return A("trigger", bindings.ArgumentBindings.Select(binding => binding.Actual).ToArray());
      }
      case "VcsMaxCost": {
        return A1("vcs_max_cost", bindings);
      }
      case "VcsMaxKeepGoingSplits": {
        return A1("vcs_max_keep_going_splits", bindings);
      }
      case "VcsMaxSplits": {
        return A1("vcs_max_splits", bindings);
      }
      case "Verify": {
        return A1("verify", bindings);
      }
      case "VerifyOnly": {
        return A("only");
      }
      case "VerifyOnlyAfter": {
        return A("only", new StringLiteralExpr(atAttribute.tok, "after", false));
      }
      case "VerifyOnlyBefore": {
        return A("only", new StringLiteralExpr(atAttribute.tok, "before", false));
      }
      default: {
        return Error($"Built-in @-Attribute {name} not convertible yet", atAttribute.Tok);
      }
    }
  }

  private static (Attributes? attrs, (string, IToken)? error)
    A1(string name, ActualBindings bindings)
  {
    if (Get(bindings, 0, out var expr) && expr != null) {
      return A(name, expr);
    }

    return A(name);
  }

  private static bool Get(ActualBindings bindings, int i, out Expression? expr) {
    if (bindings.Arguments.Count < i + 1 || bindings.Arguments[i] is StringLiteralExpr { Value : "" }) {
      expr = null;
      return true;
    }

    expr = bindings.Arguments[i];
    return false;
  }

  private static Action<string, Formal[]> ResolveLikeDatatypeConstructor(
    ModuleResolver resolver, ResolutionContext resolutionContext,
    Dictionary<TypeParameter, Type> typeMap, ActualBindings bindings, IToken tok) {
    return (name, formals) => {
      var datatypeCtor = new DatatypeCtor(RangeToken.NoToken, new Name(RangeToken.NoToken, name), false,
        formals.ToList(), null);
      resolver.ResolveActualParameters(bindings, formals.ToList(), tok,
        datatypeCtor, resolutionContext, typeMap, null);
    };
  }

  public static bool TryGetBuiltinAtAttribute(string name, out BuiltInAtAttributeSyntax? builtinAtAttribute) {
    return BuiltInAtAttributeDictionary.TryGetValue(name, out builtinAtAttribute);
  }

  public static List<BuiltInAtAttributeSyntax> BuiltinAtAttributes = new() {
    B("Abstemious"),
    B("Assumption"),
    B("AssumeConcurrent"),
    B("AutoContracts"),
    B("AutoRequires"),
    B("AutoRevealDependenciesAll").WithArg("0", Type.Bool, true, new LiteralExpr(Token.NoToken, true)),
    B("AutoRevealDependencies").WithArg("level", Type.Int, false, null),
    B("Axiom"),
    B("Compile").WithArg("0", Type.Bool, false, new LiteralExpr(Token.NoToken, true)),
    B("Concurrent"),
    B("Contradiction"),
    B("DisableNonlinearArithmetic"),
    B("Error")
      .WithArg("message", Type.ResolvedString(), false, null)
      .WithArg("successMessage", Type.ResolvedString(), true, null),
    B("Extern")
      .WithArg("name", Type.ResolvedString(), true, null)
      .WithArg("moduleName", Type.ResolvedString(), true, null),
    B("Focus"),
    B("Fuel")
      .WithArg("low", Type.Int, true, new LiteralExpr(Token.NoToken, 1))
      .WithArg("high", Type.Int, true, new LiteralExpr(Token.NoToken, 2))
      .WithArg("functionName", Type.ResolvedString(), true, null),
    B("Id").WithArg("0", Type.ResolvedString(), false, null),
    B("Induction"), // Resolution is different
    B("IsolateAssertions"),
    B("NativeType")
      .WithArg("native", Type.Bool, true, new LiteralExpr(Token.NoToken, true))
      .WithArg("name", Type.ResolvedString(), true, null),
    B("Options").WithArg("0", Type.ResolvedString(), false, null),
    B("Print"),
    B("Priority").WithArg("0", Type.Int, false, null),
    B("ResourceLimit").WithArg("0", Type.Int, false, null),
    B("SelectiveChecking"),
    B("SplitHere"),
    B("StartCheckingHere"),
    B("SubSumption").WithArg("0", Type.Int, false, null),
    B("Synthesize"),
    B("TimeLimit").WithArg("0", Type.Int, false, null),
    B("TimeLimitMultiplier").WithArg("0", Type.Int, false, null),
    B("TailRecursion"),
    B("Test"),
    B("Transparent"),
    B("Trigger"), // Resolution is different
    B("VcsMaxCost").WithArg("0", Type.Int, false, null),
    B("VcsMaxKeepGoingSplits").WithArg("0", Type.Int, false, null),
    B("VcsMaxSplits").WithArg("0", Type.Int, false, null),
    B("Verify"),
    B("VerifyOnly"),
    B("VerifyOnlyAfter"),
    B("VerifyOnlyBefore"),
  };

  public static Dictionary<string, BuiltInAtAttributeSyntax> BuiltInAtAttributeDictionary =
    BuiltinAtAttributes.ToDictionary(b => {
      if (b.Name.Contains("_") || b.Name.Contains("-") || Char.IsLower(b.Name[0])) {
        throw new Exception("Builtin @-attributes are PascalCase for consistency");
      }
      return b.Name;
    }, b => b);

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Name != null);
    Contract.Invariant(cce.NonNullElements(Args));
  }

  public static string AxiomAttributeName = "axiom";
  public static string ConcurrentAttributeName = "concurrent";
  public static string AssumeConcurrentAttributeName = "assume_concurrent";
  public static string ExternAttributeName = "extern";
  public static string VerifyAttributeName = "verify";
  public static string AutoGeneratedAttributeName = "auto_generated";

  public string Name;
  /*Frozen*/
  public readonly List<Expression> Args;

  public readonly Attributes? Prev;
  public Attributes(string name, [Captured] List<Expression> args, Attributes? prev) {
    Contract.Requires(name != null);
    Contract.Requires(cce.NonNullElements(args));
    Name = name!;
    Args = args;
    Prev = prev;
  }

  public virtual Attributes? CloneAfter(Attributes? prev) {
    return new Attributes(Name, Args, prev);
  }

  public override string ToString() {
    string result = Prev?.ToString() + "{:" + Name;
    if (Args == null || !Args.Any()) {
      return result + "}";
    } else {
      var exprs = String.Join(", ", Args.Select(e => e.ToString()));
      return result + " " + exprs + "}";
    }
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
  [System.Diagnostics.Contracts.Pure]
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
  [System.Diagnostics.Contracts.Pure]
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
  public static bool ContainsBoolAtAnyLevel(MemberDecl decl, string attribName, bool defaultVal = false) {
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

    return defaultVal;
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
  public static List<List<Expression>> FindAllExpressions(Attributes? attrs, string nm) {
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

  public override IEnumerable<INode> Children => Args.Concat<Node>(
    Prev == null
      ? Enumerable.Empty<Node>()
      : new List<Node?> { Prev });

  public override IEnumerable<INode> PreResolveChildren => Children;

  // # After ensuring we started to parse something, we assign its attributes
  // Consumes all attributes of tmpStack and prepend them into attributesStack
  // It assumes attributesStack was parsed after tmpStack,
  // as if attributesStack was used all along
  // Sets tmpStack to null to mark the attributes as consumed.
  public static void MergeInto(ref Attributes? tmpStack, ref Attributes? attributesStack) {
    MergeIntoReadonly(tmpStack, ref attributesStack);
    tmpStack = null;
  }
  
  private static void MergeIntoReadonly(Attributes? tmpStack, ref Attributes? attributesStack) {
    if (tmpStack == null) {
      return;
    }
    if (attributesStack == null) {
      attributesStack = tmpStack;
      return;
    }
    MergeIntoReadonly(tmpStack.Prev, ref attributesStack);
    attributesStack = tmpStack.CloneAfter(attributesStack);
  }
}

public static class AttributesExtensions {
  /// <summary>
  /// By making this an extension method, it can also be invoked for a null receiver.
  /// </summary>
  public static IEnumerable<Attributes?> AsEnumerable(this Attributes? attr) {
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
  public UserSuppliedAttributes(IToken tok, IToken openBrace, IToken closeBrace, List<Expression> args, Attributes? prev)
    : base(tok.val, args, prev) {
    Contract.Requires(tok != null);
    Contract.Requires(openBrace != null);
    Contract.Requires(closeBrace != null);
    Contract.Requires(args != null);
    this.tok = tok;
    OpenBrace = openBrace!;
    CloseBrace = closeBrace!;
  }
  
  public override Attributes? CloneAfter(Attributes? prev) {
    return new UserSuppliedAttributes(tok, OpenBrace, CloseBrace, Args, prev);
  }
}


public class UserSuppliedAtAttribute : Attributes {
  public static readonly string UserAttribute = "@";
  public readonly IToken AtSign;
  public bool Recognized;  // set to true to indicate an attribute that is processed by some part of Dafny; this allows it to be colored in the IDE
  public UserSuppliedAtAttribute(IToken tok, Expression arg, Attributes? prev)
    : base(UserAttribute, new List<Expression>(){arg}, prev) {
    Contract.Requires(tok != null);
    this.tok = tok;
    this.AtSign = tok;
  }

  public Expression Arg => Args[0];
  
  public override Attributes? CloneAfter(Attributes? prev) {
    return new UserSuppliedAtAttribute(AtSign, Args[0], prev);
  }
}

/// <summary>
/// A class implementing this interface is one that can carry attributes.
/// </summary>
public interface IAttributeBearingDeclaration {
  Attributes Attributes { get; }
}

public static class AttributeBearingDeclarationExtensions {
  public static bool HasUserAttribute(this IAttributeBearingDeclaration decl, string name, out Attributes attribute) {
    if (Attributes.Find(decl.Attributes, name) is UserSuppliedAttributes attr) {
      attribute = attr;
      return true;
    }

    attribute = null;
    return false;
  }
}