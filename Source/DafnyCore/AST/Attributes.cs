#nullable enable
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Numerics;

namespace Microsoft.Dafny;

static class AttributeBearingDeclaration {

  public static bool IsExtern(this IAttributeBearingDeclaration me, DafnyOptions options) =>
    options.AllowExterns && Attributes.Contains(me.Attributes, "extern");

  public static bool IsExplicitAxiom(this IAttributeBearingDeclaration me) =>
    Attributes.Contains(me.Attributes, "axiom");
}

// Syntax of a formal of a built-in @-attribute
// To create one, prefer using the chaining BuiltInAtAttributeSyntax.WithArg()
public record BuiltInAtAttributeArgSyntax(
  string ArgName,
  Type ArgType, // If null, it means it's not resolved (@Induction and @Trigger)
  Expression? DefaultValue) {
  public Formal ToFormal() {
    Contract.Assert(ArgType != null);
    return new Formal(Token.NoToken, ArgName, ArgType, true, false,
      DefaultValue);
  }
}

// Syntax for a built-in @-attribute.
// To create such an attribute, use the Attributes.B() helper
public record BuiltInAtAttributeSyntax(
  string Name,
  List<BuiltInAtAttributeArgSyntax> Args,
  Func<IAttributeBearingDeclaration, bool> CanBeApplied) {
  public BuiltInAtAttributeSyntax WithArg(String argName, Type argType, Expression? defaultValue = null) {
    var c = new List<BuiltInAtAttributeArgSyntax>(Args) {
      new(argName, argType, defaultValue) };
    return this with { Args = c };
  }

  public BuiltInAtAttributeSyntax Filter(Func<IAttributeBearingDeclaration, bool> canBeApplied) {
    return this with { CanBeApplied = canBeApplied };
  }
}

public class Attributes : NodeWithComputedRange, ICanFormat {
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

  [ParseConstructor]
  public Attributes(IOrigin origin, string name, List<Expression> args, Attributes? prev) : base(origin) {
    Name = name;
    Args = args;
    Prev = prev;
  }

  public Attributes(string name, [Captured] List<Expression> args, Attributes? prev) : base(Token.NoToken) {
    Contract.Requires(cce.NonNullElements(args));
    Contract.Requires(name != UserSuppliedAtAttribute.AtName || this is UserSuppliedAtAttribute);
    Name = name;
    Args = args;
    Prev = prev;
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

  public static IEnumerable<Expression> SubExpressions(Attributes? attrs) {
    return attrs.AsEnumerable().SelectMany(aa => aa.Args);
  }

  public static bool Contains(Attributes? attrs, string nm) {
    Contract.Requires(nm != null);
    return attrs.AsEnumerable().Any(aa => aa.Name == nm);
  }

  /// <summary>
  /// Returns first occurrence of an attribute named <c>nm</c>, or <c>null</c> if there is no such
  /// attribute.
  /// </summary>
  [Pure]
  public static Attributes? Find(Attributes? attrs, string nm) {
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
  public static bool ContainsBool(Attributes? attrs, string nm, ref bool value) {
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
  public static List<Expression>? FindExpressions(Attributes attrs, string nm) {
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
  public static List<List<Expression>>? FindAllExpressions(Attributes? attrs, string nm) {
    List<List<Expression>>? ret = null;
    for (; attrs != null; attrs = attrs.Prev) {
      if (attrs.Name == nm) {
        ret = ret ?? [];   // Avoid allocating the list in the common case where we don't find nm
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
  public static bool ContainsMatchingValue(Attributes attrs, string nm, ref object value,
    ISet<MatchingValueOption> allowed, Action<string> reporter) {
    var args = FindExpressions(attrs, nm);
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
      var arg = args[0];
      var literal = arg as LiteralExpr;
      if (literal is { Value: bool } && allowed.Contains(MatchingValueOption.Bool)) {
        value = literal.Value;
        return true;
      } else if (literal != null && literal.Value is BigInteger && allowed.Contains(MatchingValueOption.Int)) {
        value = literal.Value;
        return true;
      } else if (arg is StringLiteralExpr stringLiteral && stringLiteral.Value is string && allowed.Contains(MatchingValueOption.String)) {
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
      : new List<Node> { Prev });

  public override IEnumerable<INode> PreResolveChildren => Children;
  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    foreach (var token in OwnedTokens) {
      switch (token.val) {
        case "}": {
            formatter.SetClosingIndentedRegion(token, indentBefore);
            break;
          }
        case "@": {
            formatter.SetIndentations(token, indentBefore, indentBefore, indentBefore);
            break;
          }
        case ",": {
            formatter.SetDelimiterInsideIndentedRegions(token, indentBefore);
            break;
          }
        case "{" or "{:": {
            formatter.SetOpeningIndentedRegion(token, indentBefore);
            break;
          }
      }
    }
    foreach (var arg in Args) {
      formatter.SetExpressionIndentation(arg);
    }
    formatter.SetClosingIndentedRegion(EndToken, indentBefore);
    return false; // Don't do inner attributes, they should be performed independently
  }

  // Typically, {:} are indented when @-attributes are not
  public static void SetIndents(Attributes attrs, int indentBefore, TokenNewIndentCollector formatter) {
    foreach (var attribute in attrs.AsEnumerable()) {
      if (attribute.StartToken.val == UserSuppliedAtAttribute.AtName) {
        attribute.SetIndent(indentBefore, formatter);
      } else {
        attribute.SetIndent(indentBefore + formatter.SpaceTab, formatter);
      }
    }
  }
  public static string TupleItem0Name => "0";
  // Helper to create a built-in @-attribute
  static BuiltInAtAttributeSyntax BuiltIn(string name) {
    return new BuiltInAtAttributeSyntax(
      name, [], _ => true);
  }

  // Helper to create an old-style attribute
  private static Attributes A(string name, params Expression[] args) {
    return new Attributes(name, args.Select(arg =>
      arg is DefaultValueExpression defaultExpr ? defaultExpr.Resolved : arg).ToList(), null);
  }

  // Helper to create an old-style attribute with only one argument
  private static Attributes A1(string name, ActualBindings bindings) {
    if (Get(bindings, 0, out var expr) && expr != null) {
      return A(name, expr);
    }

    return A(name);
  }

  // Given a user-supplied @-attribute, expand it if recognized as builtin to an old-style attribute
  // or mark it as not built-in for later resolution
  public static Attributes? ExpandAtAttribute(Program program, UserSuppliedAtAttribute atAttribute, IAttributeBearingDeclaration attributeHost) {
    var name = atAttribute.UserSuppliedName;
    var bindings = atAttribute.UserSuppliedPreResolveBindings;

    if (name == null) {
      program.Reporter.Error(MessageSource.Resolver, atAttribute.Origin, "Attribute not recognized: " + atAttribute.ToString());
      return null;
    }

    if (!TryGetBuiltinAtAttribute(name, out var builtinSyntax) || builtinSyntax == null) {
      atAttribute.Builtin = false; // Will be resolved after
      return null;
    }

    if (!builtinSyntax.CanBeApplied(attributeHost)) {
      program.Reporter.Error(MessageSource.Resolver, atAttribute.Origin, UserSuppliedAtAttribute.AtName + atAttribute.UserSuppliedName + " attribute cannot be applied to " + attributeHost.WhatKind);
    }

    var resolver = new ModuleResolver(new ProgramResolver(program), program.Options) {
      reporter = program.Reporter
    };
    resolver.moduleInfo = resolver.ProgramResolver.SystemModuleManager.systemNameInfo;
    var formals = builtinSyntax.Args.Select(arg => arg.ToFormal()).ToArray();
    ResolveLikeDatatypeConstructor(program, formals, name, atAttribute, bindings, resolver);

    atAttribute.Builtin = true;
    atAttribute.Arg.Type = Type.Int; // Dummy type to avoid crashes
    var intDecl = resolver.SystemModuleManager.valuetypeDecls.First(valueTypeDecl => valueTypeDecl.Name == PreType.TypeNameInt);

    atAttribute.Arg.PreType = new DPreType(intDecl, [], null);

    switch (name) {
      case "AssumeCrossModuleTermination": {
          return A("AssumeCrossModuleTermination");
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
          return A(AxiomAttributeName);
        }
      case "Compile": {
          return A1("compile", bindings);
        }
      case "Concurrent": {
          return A(ConcurrentAttributeName);
        }
      case "DisableNonlinearArithmetic": {
          return A1("disableNonlinearArithmetic", bindings);
        }
      case "Fuel": {
          if (Get(bindings, 0, out var lowFuel) && lowFuel != null) {
            if (Get(bindings, 1, out var highFuel) && highFuel != null) {
              if (Get(bindings, 2, out var functionName) && IsStringNotEmpty(functionName)) {
                return A("fuel", functionName!, lowFuel, highFuel);
              }

              return A("fuel", lowFuel, highFuel);
            }

            return A("fuel", lowFuel);
          }

          return A("fuel");
        }
      case "IsolateAssertions": {
          return A("isolate_assertions");
        }
      case "NativeUInt8": {
          return A("nativeType", DefaultString("byte"));
        }
      case "NativeInt8": {
          return A("nativeType", DefaultString("sbyte"));
        }
      case "NativeUInt16": {
          return A("nativeType", DefaultString("ushort"));
        }
      case "NativeInt16": {
          return A("nativeType", DefaultString("short"));
        }
      case "NativeUInt32": {
          return A("nativeType", DefaultString("uint"));
        }
      case "NativeInt32": {
          return A("nativeType", DefaultString("int"));
        }
      case "NativeInt53": {
          return A("nativeType", DefaultString("number"));
        }
      case "NativeUInt64": {
          return A("nativeType", DefaultString("ulong"));
        }
      case "NativeInt64": {
          return A("nativeType", DefaultString("long"));
        }
      case "NativeUInt128": {
          return A("nativeType", DefaultString("udoublelong"));
        }
      case "NativeInt128": {
          return A("nativeType", DefaultString("doublelong"));
        }
      case "NativeInt": {
          return A("nativeType", DefaultBool(true));
        }
      case "NativeNone": {
          return A("nativeType", DefaultBool(false));
        }
      case "NativeIntOrReal": {
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
      case "TestEntry": {
          return A("TestEntry");
        }
      case "TestInline": {
          return A1("testInline", bindings);
        }
      case "Transparent": {
          return A("transparent");
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
          return A1(VerifyAttributeName, bindings);
        }
      case "VerifyOnly": {
          return A("only");
        }
      default: {
          throw new Exception("@-Attribute added to Attributes.BuiltinAtAttributes needs to be handled here");
        }
    }
  }

  // List of built-in @-attributes with their definitions.
  // This list could be obtained from parsing and resolving a .Dfy file
  // but for now it's good enough.
  public static readonly List<BuiltInAtAttributeSyntax> BuiltinAtAttributes = [
    BuiltIn("AssumeCrossModuleTermination")
      .Filter(attributeHost => attributeHost is ClassDecl or TraitDecl),

    BuiltIn("AutoContracts")
      .Filter(attributeHost => attributeHost is ClassDecl),

    BuiltIn("AutoRequires")
      .Filter(attributeHost => attributeHost is Function),

    BuiltIn("AutoRevealDependenciesAll").WithArg(TupleItem0Name, Type.Bool, DefaultBool(true))
      .Filter(attributeHost => attributeHost is MethodOrFunction),

    BuiltIn("AutoRevealDependencies").WithArg("level", Type.Int)
      .Filter(attributeHost => attributeHost is MethodOrFunction),

    BuiltIn("Axiom")
      .Filter(attributeHost => attributeHost is MethodOrFunction),

    BuiltIn("Compile")
      .WithArg(TupleItem0Name, Type.Bool, DefaultBool(true))
      .Filter(attributeHost =>
        attributeHost is TopLevelDecl and not TypeParameter or MemberDecl or ModuleDefinition),

    BuiltIn("Concurrent")
      .Filter(attributeHost =>
        attributeHost is MethodOrFunction),

    BuiltIn("DisableNonlinearArithmetic")
      .WithArg("disable", Type.Bool, DefaultBool(true))
      .Filter(attributeHost =>
        attributeHost is ModuleDefinition),

    BuiltIn("Fuel")
      .WithArg("low", Type.Int, DefaultInt(1))
      .WithArg("high", Type.Int, DefaultInt(2))
      .WithArg("functionName", Type.ResolvedString(), DefaultString(""))
      .Filter(attributeHost => attributeHost is MethodOrFunction or AssertStmt),

    BuiltIn("IsolateAssertions")
      .Filter(attributeHost => attributeHost is ICanVerify),

    BuiltIn("NativeUInt8")
      .Filter(attributeHost => attributeHost is NewtypeDecl),

    BuiltIn("NativeInt8")
      .Filter(attributeHost => attributeHost is NewtypeDecl),

    BuiltIn("NativeUInt16")
      .Filter(attributeHost => attributeHost is NewtypeDecl),

    BuiltIn("NativeInt16")
      .Filter(attributeHost => attributeHost is NewtypeDecl),

    BuiltIn("NativeUInt32")
      .Filter(attributeHost => attributeHost is NewtypeDecl),

    BuiltIn("NativeInt32")
      .Filter(attributeHost => attributeHost is NewtypeDecl),

    BuiltIn("NativeInt53")
      .Filter(attributeHost => attributeHost is NewtypeDecl),

    BuiltIn("NativeUInt64")
      .Filter(attributeHost => attributeHost is NewtypeDecl),

    BuiltIn("NativeInt64")
      .Filter(attributeHost => attributeHost is NewtypeDecl),

    BuiltIn("NativeUInt128")
      .Filter(attributeHost => attributeHost is NewtypeDecl),

    BuiltIn("NativeInt128")
      .Filter(attributeHost => attributeHost is NewtypeDecl),

    BuiltIn("NativeInt")
      .Filter(attributeHost => attributeHost is NewtypeDecl),

    BuiltIn("NativeNone")
      .Filter(attributeHost => attributeHost is NewtypeDecl),

    BuiltIn("NativeIntOrReal")
      .Filter(attributeHost => attributeHost is NewtypeDecl),

    BuiltIn("Options")
      .WithArg(TupleItem0Name, Type.ResolvedString())
      .Filter(attributeHost => attributeHost is ModuleDecl or ModuleDefinition),

    BuiltIn("Print")
      .Filter(attributeHost => attributeHost is Method),

    BuiltIn("Priority").WithArg(TupleItem0Name, Type.Int)
      .Filter(attributeHost => attributeHost is ICanVerify),

    BuiltIn("ResourceLimit").WithArg(TupleItem0Name, Type.ResolvedString())
      .Filter(attributeHost => attributeHost is ICanVerify),

    BuiltIn("Synthesize")
      .Filter(attributeHost => attributeHost is Method),

    BuiltIn("TimeLimit").WithArg(TupleItem0Name, Type.Int)
      .Filter(attributeHost => attributeHost is ICanVerify),

    BuiltIn("TimeLimitMultiplier").WithArg(TupleItem0Name, Type.Int)
      .Filter(attributeHost => attributeHost is ICanVerify),

    BuiltIn("TailRecursion")
      .Filter(attributeHost => attributeHost is MethodOrFunction),

    BuiltIn("Test")
      .Filter(attributeHost => attributeHost is MethodOrFunction),

    BuiltIn("TestEntry")
      .Filter(attributeHost => attributeHost is MethodOrFunction),

    BuiltIn("TestInline").WithArg("level", Type.Int, DefaultInt(1))
      .Filter(attributeHost => attributeHost is MethodOrFunction),

    BuiltIn("Transparent")
      .Filter(attributeHost => attributeHost is Function),

    BuiltIn("VcsMaxCost").WithArg(TupleItem0Name, Type.Int)
      .Filter(attributeHost => attributeHost is ICanVerify),

    BuiltIn("VcsMaxKeepGoingSplits").WithArg(TupleItem0Name, Type.Int)
      .Filter(attributeHost => attributeHost is ICanVerify),

    BuiltIn("VcsMaxSplits").WithArg(TupleItem0Name, Type.Int)
      .Filter(attributeHost => attributeHost is ICanVerify),

    BuiltIn("Verify")
      .Filter(attributeHost => attributeHost is ICanVerify),

    BuiltIn("VerifyOnly")
      .Filter(attributeHost => attributeHost is ICanVerify)

  ];

  ////// Helpers to create default values for the @-attribute definitions above //////

  public static LiteralExpr DefaultString(string value) {
    return Expression.CreateStringLiteral(Token.NoToken, value);
  }

  public static LiteralExpr DefaultBool(bool value) {
    return Expression.CreateBoolLiteral(Token.NoToken, value);
  }

  public static LiteralExpr DefaultInt(int value) {
    return Expression.CreateIntLiteralNonnegative(Token.NoToken, value);
  }

  private static bool IsStringNotEmpty(Expression? value) {
    return value is StringLiteralExpr { Value: string and not "" };
  }

  // Given resolved bindings, gets the i-th argument according to the
  // declaration formals order
  private static bool Get(ActualBindings bindings, int i, out Expression? expr) {
    if (bindings.Arguments.Count < i + 1) {
      expr = null;
      return false;
    }

    expr = bindings.Arguments[i];
    return true;
  }

  // Resolves bindings given a list of datatype constructor-like formals,
  // obtained from built-in @-attribute definitions
  private static void ResolveLikeDatatypeConstructor(Program program, Formal[] formals, string attrName,
    UserSuppliedAtAttribute attrs, ActualBindings bindings, ModuleResolver resolver) {
    var resolutionContext = new ResolutionContext(new NoContext(program.DefaultModuleDef), false); ;
    var typeMap = new Dictionary<TypeParameter, Type>();
    resolver.ResolveActualParameters(bindings, formals.ToList(), attrs.Origin,
      attrs, resolutionContext, typeMap, null);
    resolver.FillInDefaultValueExpressions();
    resolver.SolveAllTypeConstraints();
    // Verify that provided arguments are given literally
    foreach (var binding in bindings.ArgumentBindings) {
      if (binding.Actual is not LiteralExpr) {
        program.Reporter.Error(MessageSource.Resolver, binding.Actual.Origin, $"Argument to attribute {attrName} must be a literal");
      }
    }
  }

  // Recovers a built-in @-Attribute if it exists
  public static bool TryGetBuiltinAtAttribute(string name, out BuiltInAtAttributeSyntax? builtinAtAttribute) {
    return BuiltInAtAttributeDictionary.TryGetValue(name, out builtinAtAttribute);
  }

  // Builtin @-attributes dictionary based on the sequence of definitions of @-attributes
  public static Dictionary<string, BuiltInAtAttributeSyntax> BuiltInAtAttributeDictionary =
    BuiltinAtAttributes.ToDictionary(b => {
      if (b.Name.Contains("_") || b.Name.Contains("-") || Char.IsLower(b.Name[0])) {
        throw new Exception("Builtin @-attributes are PascalCase for consistency");
      }
      return b.Name;
    }, b => b);

  // Overridable method to clone the attribute as if the new attribute was placed after "prev" in the source code
  public virtual Attributes CloneAfter(Attributes? prev) {
    return new Attributes(Name, Args, prev);
  }

  //////// Helpers for parsing attributes //////////////////

  // Returns the memory location's attributes content and set the memory location to null (no attributes)
  public static Attributes? Consume(ref Attributes? tmpStack) {
    var result = tmpStack;
    tmpStack = null;
    return result;
  }

  // Empties the first attribute memory location while prepending its attributes to the second attribute memory location, in the same order
  public static void MergeInto(ref Attributes? tmpStack, ref Attributes? attributesStack) {
    MergeIntoReadonly(tmpStack, ref attributesStack);
    tmpStack = null;
  }

  // Prepends the attributes tmpStack before the attributes contained in the memory location attributesStack 
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
  public static IEnumerable<Attributes> AsEnumerable(this Attributes? attr) {
    while (attr != null) {
      yield return attr;
      attr = attr.Prev;
    }
  }
}

// {:..} Attributes parsed are built using this class
public class UserSuppliedAttributes : Attributes {
  public readonly IOrigin OpenBrace;
  public readonly IOrigin CloseBrace;
  public bool Recognized;  // set to true to indicate an attribute that is processed by some part of Dafny; this allows it to be colored in the IDE
  public UserSuppliedAttributes(IOrigin origin, IOrigin openBrace, IOrigin closeBrace, List<Expression> args, Attributes? prev)
    : base(origin.val, args, prev) {
    SetOrigin(origin);
    OpenBrace = openBrace;
    CloseBrace = closeBrace;
  }
}

// @-Attributes parsed are built using this class
public class UserSuppliedAtAttribute : Attributes {
  public static readonly string AtName = "@";
  public readonly IOrigin AtSign;
  public bool Builtin;  // set to true to indicate it was recognized as a builtin attribute
  // Otherwise it's a user-defined one and Arg needs to be fully resolved
  public UserSuppliedAtAttribute(IOrigin origin, Expression arg, Attributes? prev)
    : base(AtName, [arg], prev) {
    SetOrigin(origin);
    this.AtSign = origin;
  }

  public Expression Arg => Args[0];

  public override Attributes CloneAfter(Attributes? prev) {
    return new UserSuppliedAtAttribute(AtSign, Args[0], prev);
  }

  // Name of this @-Attribute, which is the part right after the @
  public string? UserSuppliedName => GetName(this);

  // Pre-resolved bindings of this @-Attribute
  public ActualBindings UserSuppliedPreResolveBindings =>
    GetPreResolveBindings(this);

  // Pre-resolved arguments of this @-Attributes. The order is the one provided by the user,
  // not by any binding. Used for 
  public IEnumerable<Expression> UserSuppliedPreResolveArguments =>
    GetPreResolveArguments(this);

  // Gets the name of an @-attribute. Attributes might be applied.
  public static string? GetName(Attributes a) {
    if (a is UserSuppliedAtAttribute { Arg: ApplySuffix { Lhs: NameSegment { Name: var name } } }) {
      return name;
    }
    if (a is UserSuppliedAtAttribute { Arg: NameSegment { Name: var singleName } }) {
      return singleName;
    }

    return null;
  }

  // Gets the pre-resolved bindings of an @-Attribute.
  // Returns an empty bindings if it's anything else
  public static ActualBindings GetPreResolveBindings(Attributes a) {
    if (a is UserSuppliedAtAttribute { Arg: ApplySuffix { Bindings: var bindings } }) {
      return bindings;
    }
    return new ActualBindings(new List<ActualBinding>());
  }

  // Gets the list of pre-resolved arguments of an @-Attribute, and an empty list otherwise
  public static IEnumerable<Expression> GetPreResolveArguments(Attributes a) {
    if (a is UserSuppliedAtAttribute { UserSuppliedPreResolveBindings: var bindings }) {
      return bindings.ArgumentBindings.Select(arg => arg.Actual);
    }

    return new List<Expression>();
  }

  // Gets the list of pre-resolved arguments of an @-Attribute, and the list of arguments
  // for any other kind of attributes. Used for example to extract module options for parsing.
  public static IEnumerable<Expression> GetUserSuppliedArguments(Attributes a) {
    return a is UserSuppliedAtAttribute { UserSuppliedPreResolveArguments: var arguments } ? arguments : a.Args;
  }

  public override string ToString() => Prev + (Prev == null ? "" : " ") + "@" + Arg;
}

/// <summary>
/// A class implementing this interface is one that can carry attributes.
/// </summary>
public interface IAttributeBearingDeclaration {
  Attributes? Attributes { get; internal set; }
  string WhatKind { get; }
}

public static class AttributeBearingDeclarationExtensions {
  public static bool HasUserAttribute(this IAttributeBearingDeclaration decl, string name, out Attributes? attribute) {
    if (Attributes.Find(decl.Attributes, name) is UserSuppliedAttributes attr) {
      attribute = attr;
      return true;
    }

    attribute = null;
    return false;
  }
}