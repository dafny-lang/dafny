// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable

using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny;
using Type = Microsoft.Dafny.Type;

namespace DafnyTestGeneration;

// This AST pass is run before test generation to detect any potential issues and report them to the user
public class FirstPass {
  private List<DafnyDiagnostic> diagnostics;
  private IEnumerable<DafnyDiagnostic> Errors => diagnostics.Where(diagnostic => diagnostic.Level == ErrorLevel.Error);
  private IEnumerable<DafnyDiagnostic> Warnings => diagnostics.Where(diagnostic => diagnostic.Level == ErrorLevel.Warning);
  private readonly DafnyOptions options;
  public bool NonZeroExitCode { get; private set; }

  // Errors always lead to preemptive termination of test generation and cannot be bypassed
  public const string NoTestEntryError = "NoTestEntryError";
  public const string NoExternalModuleError = "NoExternalModuleError";
  public const string MalformedAttributeError = "MalformedAttributeError";
  public const string UnsupportedInputTypeError = "UnsupportedInputTypeError";

  // Warnings lead to preemptive terminate of test generation unless --ignore-warnings flag is used
  public const string InlinedMethodNotReachableWarning = "InlinedMethodNotReachableWarning";
  public const string NotFullySupportedInputTypeWarning = "NotFullySupportedInputTypeWarning";
  public const string NoWitnessWarning = "NoWitnessWarning";
  public const string SmallTimeLimitWarning = "SmallTumeLimitWarning";

  // List of all types that have been checked for being supported. Used to prevent infinite recursion
  private HashSet<Type> typesConsidered = [];

  public FirstPass(DafnyOptions options) {
    this.options = options;
  }

  /// <summary>
  /// Check that test generation will be able to process the program.
  /// Return false, if test generation should preemptively terminated,
  /// i.e. if there are any errors or if there are warnings and the --ignore-warnings flag is not used
  /// </summary>
  public async Task<bool> IsOk(string source, Uri uri) {
    var errorReporter = new ConsoleErrorReporter(options);
    var program = await Utils.Parse(errorReporter, source, true, uri);
    diagnostics = [];
    if (errorReporter.FailCompilation) {
      NonZeroExitCode = true;
      return false;
    }
    typesConsidered = [];
    CheckIsWrappedInAModule(program);
    CheckHasTestEntry(program);
    CheckInlinedDeclarationsAreReachable(program);
    CheckInlineAttributes(program);
    CheckInputTypesAreSupported(program);
    CheckVerificationTimeLimit(program);
    PrintWarningsAndErrors(errorReporter, program);
    NonZeroExitCode = Errors.Count() != 0;
    return !Errors.Any() && (!Warnings.Any() || !options.FailOnWarnings);
  }

  /// <summary>
  /// Print all gathered warnings and errors
  /// </summary>
  private void PrintWarningsAndErrors(ErrorReporter errorReporter, Program program) {
    if (Errors.Count() != 0) {
      errorReporter.Error(MessageSource.TestGeneration, "", program.StartToken,
        $"Test generation returned {Errors.Count()} errors. Fix them to proceed:");
      foreach (var error in Errors) {
        var errorId = error.ErrorId == "none" ? "Error" : error.ErrorId;
        errorReporter.MessageCore(error with {
          Source = MessageSource.TestGeneration,
          Level = ErrorLevel.Error,
          ErrorId = errorId,
          RelatedInformation = []
        });
      }
    }
    if (Warnings.Count() != 0 && !options.TestGenOptions.IgnoreWarnings) {
      errorReporter.Warning(MessageSource.TestGeneration, "", program.StartToken,
        $"Test generation returned {Warnings.Count()} warnings:");
      foreach (var warning in Warnings) {
        errorReporter.MessageCore(warning with {
          Source = MessageSource.TestGeneration,
          Level = ErrorLevel.Warning,
          RelatedInformation = []
        });
      }
    }
  }

  /// <summary>
  /// Emit a warning proposing to raise test generation time limit if
  /// any of the functions/methods in the program is annotated with a custom {:timeLimit} value higher than the default
  /// </summary>
  private bool CheckVerificationTimeLimit(Program program) {
    uint maxTimeLimit = (options.TimeLimit == 0 ? TestGenerationOptions.DefaultTimeLimit : options.TimeLimit);
    Declaration callableWithMaxTimeLimit = null;
    foreach (var declaration in Utils.AllMemberDeclarationsWithAttribute(program.DefaultModule, "timeLimit")) {
      if (declaration.HasUserAttribute("timeLimit", out var attribute) &&
          uint.TryParse(attribute.Args.First().ToString(), out uint timeLimit) &&
          timeLimit > maxTimeLimit) {
        maxTimeLimit = timeLimit;
        callableWithMaxTimeLimit = declaration;
      }
    }
    if (callableWithMaxTimeLimit != null) {
      diagnostics.Add(new DafnyDiagnostic(MessageSource.TestGeneration, SmallTimeLimitWarning, callableWithMaxTimeLimit.Origin.ReportingRange,
        $"Method/function {callableWithMaxTimeLimit} is annotated with {{:timeLimit {maxTimeLimit}}} but test " +
        $"generation is called with --{BoogieOptionBag.VerificationTimeLimit.Name}:{options.TimeLimit}." +
        $"\nConsider increasing the time limit for test generation",
        ErrorLevel.Warning, new List<DafnyRelatedInformation>()));
      return false;
    }
    return true;
  }

  /// <summary>
  /// Check that function/methods annotated with {:testInline} use this attribute correctly
  /// </summary>
  private void CheckInlineAttributes(Program program) {
    foreach (var toInline in Utils
               .AllMemberDeclarationsWithAttribute(program.DefaultModule, TestGenerationOptions.TestInlineAttribute)) {
      toInline.HasUserAttribute(TestGenerationOptions.TestInlineAttribute, out var attribute);
      if (attribute.Args.Count == 0 ||
          (attribute.Args.Count == 1 && uint.TryParse(attribute.Args.First().ToString(), out uint result) && result > 0)) {
        continue;
      }
      diagnostics.Add(new DafnyDiagnostic(MessageSource.TestGeneration, MalformedAttributeError, toInline.Origin.ReportingRange,
        $"{{:{TestGenerationOptions.TestInlineAttribute}}} attribute on the {toInline.FullDafnyName} method/function " +
        $"can only take one argument, which must be a positive integer specifying the recursion unrolling limit " +
        $"(absence of such an argument or 1 means no unrolling)",
        ErrorLevel.Error, new List<DafnyRelatedInformation>()));
      return;
    }
  }

  /// <summary>
  /// For each {:testInline}-annotated method or function, make sure it is reachable through the call graph
  /// from any of the {:testEntry}-annotated methods or function. Return false if this is not the case.
  /// </summary>
  private bool CheckInlinedDeclarationsAreReachable(Program program) {
    // First build a set of all functions/methods reachable from the {:testEntry} annotated declarations:
    var reachable = Utils
      .AllMemberDeclarationsWithAttribute(program.DefaultModule, TestGenerationOptions.TestEntryAttribute)
      .OfType<ICallable>().ToHashSet();
    var toVisit = reachable.ToList();
    var callGraphBuilderCLoner = new CallGraphBuilderCloner();
    while (toVisit.Count != 0) {
      var next = toVisit[0];
      toVisit.Remove(next);
      callGraphBuilderCLoner.VisitCallable(next);
      foreach (var callee in callGraphBuilderCLoner.Edges.GetValueOrDefault(next, [])) {
        if (!reachable.Contains(callee) &&
            callee is MemberDecl memberDecl &&
            memberDecl.HasUserAttribute(TestGenerationOptions.TestInlineAttribute, out var _)) {
          reachable.Add(callee);
          toVisit.Add(callee);
        }
      }
    }
    var result = true;
    foreach (var toInline in Utils
               .AllMemberDeclarationsWithAttribute(program.DefaultModule, TestGenerationOptions.TestInlineAttribute)
               .OfType<ICallable>()) {
      if (reachable.Contains(toInline)) {
        continue;
      }
      string message;
      if (toInline is Method method) {
        message = $"Method {method.Name} will not be inlined because it is not reachable from any of the {{:{TestGenerationOptions.TestEntryAttribute}}}-annotated methods or functions";
      } else if (toInline is Function function) {
        message = $"Function {function.Name} will not be inlined because it is not reachable from any of the {{:{TestGenerationOptions.TestEntryAttribute}}}-annotated methods or functions";
      } else {
        message = $"Found a {{:{TestGenerationOptions.TestInlineAttribute}}}-annotated declaration that is neither a method nor a function";
      }
      diagnostics.Add(new DafnyDiagnostic(MessageSource.TestGeneration, InlinedMethodNotReachableWarning,
        toInline.Origin.ReportingRange, message,
        ErrorLevel.Warning, new List<DafnyRelatedInformation>()));
      result = false;
    }
    return result;
  }

  /// <summary>
  /// Return true iff the program has no elements that are not wrapped in a module
  /// (so all elements can be imported provided the export sets allow it)
  /// </summary>
  private bool CheckIsWrappedInAModule(Program program) {
    if (program.DefaultModuleDef.Children.OfType<ClassLikeDecl>().Any() || program.DefaultModuleDef.Children.OfType<DefaultClassDecl>().Any(decl => decl.Children.Any())) {
      diagnostics.Add(new DafnyDiagnostic(MessageSource.TestGeneration, NoExternalModuleError, program.Origin.ReportingRange,
        "Program is not wrapped in a module. Put your code inside \"module M {}\" or equivalent",
        ErrorLevel.Error, new List<DafnyRelatedInformation>()));
      return false;
    }
    return true;
  }

  /// <summary>
  /// For each input parameter of every {:testEntry}-annotated function/method, make sure that
  /// the type of the parameter is fully supported by test generation. Return false, if this is not the case.
  /// </summary>
  private bool CheckInputTypesAreSupported(Program program) {
    var result = true;
    foreach (MemberDecl declaration in Utils.AllMemberDeclarationsWithAttribute(program.DefaultModule, TestGenerationOptions.TestEntryAttribute)) {
      if (declaration.EnclosingClass is TraitDecl or ArrayClassDecl or IteratorDecl) {
        diagnostics.Add(new DafnyDiagnostic(MessageSource.TestGeneration, UnsupportedInputTypeError, declaration.Origin.ReportingRange,
          $"Test Generation does not support trait, array, or iterator types as receivers of " +
          $"{{:{TestGenerationOptions.TestEntryAttribute}}}-annotated methods.\n" +
          $"Consider writing a wrapper method that creates a receiver and passes on the arguments to it",
          ErrorLevel.Warning, new List<DafnyRelatedInformation>()));
        result = false;
      } else if (declaration.EnclosingClass is ClassDecl) {
        diagnostics.Add(new DafnyDiagnostic(MessageSource.TestGeneration, NotFullySupportedInputTypeWarning, declaration.Origin.ReportingRange,
          $"Test Generation does not fully support class types as receivers of " +
          $"{{:{TestGenerationOptions.TestEntryAttribute}}}-annotated methods.\n" +
          $"Consider writing a wrapper method that creates a receiver and passes on the arguments to it",
          ErrorLevel.Warning, new List<DafnyRelatedInformation>()));
        result = false;
      }
      if (declaration is Method method) {
        foreach (var formal in method.Ins) {
          if (!TypeIsSupported(formal.Type, method.Name)) {
            result = false; // No short-circuiting here to emit all possible errors/warnings
          }
        }
      } else if (declaration is Function function) {
        foreach (var formal in function.Ins) {
          if (!TypeIsSupported(formal.Type, function.Name)) {
            result = false; // No short-circuiting here to emit all possible errors/warnings
          }
        }
      }
    }
    return result;
  }

  /// <summary>
  /// Recursively traverse a given type and emit warning/errors if this type cannot be fully reconstructed
  /// from the counterexample by test generation, i.e. no parameters of the {:testEntry}-annotated method/function
  /// should have such a type. Return true, if the type is fully supported. 
  /// </summary>
  private bool TypeIsSupported(Type type, string testEntry) {
    if (typesConsidered.Contains(type)) {
      return true;
    }
    typesConsidered.Add(type);
    var isSupported = false;
    while (type is InferredTypeProxy inferred) {
      type = inferred.T;
    }
    if (type is UserDefinedType userDefinedType) {
      var genericMessage =
        $"Consider modelling values of type {userDefinedType} with a datatype and passing them as input to " +
        $"{{:{TestGenerationOptions.TestEntryAttribute}}} annotated method/function {testEntry}";
      if (userDefinedType.IsAbstractType || userDefinedType.IsArrayType || userDefinedType.IsTraitType) {
        diagnostics.Add(new DafnyDiagnostic(MessageSource.TestGeneration, UnsupportedInputTypeError, type.Origin.ReportingRange,
          $"Test Generation does not support abstract types, array types, and trait types as inputs.\n{genericMessage}",
          ErrorLevel.Error, new List<DafnyRelatedInformation>()));
      } else if (userDefinedType.IsRefType) {
        if (userDefinedType.ResolvedClass is ClassDecl classDecl) {
          foreach (var field in classDecl.Members.Union(classDecl.InheritedMembers).OfType<Field>()) {
            TypeIsSupported(field.Type, testEntry);
          }
        }
        diagnostics.Add(new DafnyDiagnostic(MessageSource.TestGeneration, NotFullySupportedInputTypeWarning, type.Origin.ReportingRange,
          $"Test Generation does not fully support class types as inputs.\n{genericMessage}",
          ErrorLevel.Warning, new List<DafnyRelatedInformation>()));
      } else if (userDefinedType.IsArrowType) {
        diagnostics.Add(new DafnyDiagnostic(MessageSource.TestGeneration, NotFullySupportedInputTypeWarning, type.Origin.ReportingRange,
          $"Test Generation does not fully support function types as inputs.\n{genericMessage}",
          ErrorLevel.Warning, new List<DafnyRelatedInformation>()));
      } else if (userDefinedType.AsNewtype != null) {
        if (userDefinedType.AsNewtype.Witness == null) {
          diagnostics.Add(new DafnyDiagnostic(MessageSource.TestGeneration, NoWitnessWarning, type.Origin.ReportingRange,
            $"Cannot find witness for type {userDefinedType}. Please consider adding a witness to the declaration",
            ErrorLevel.Warning, new List<DafnyRelatedInformation>()));
        }
        isSupported = TypeIsSupported(userDefinedType.AsNewtype.BaseType, testEntry);
      } else if (userDefinedType.AsSubsetType != null) {
        if (userDefinedType.AsSubsetType.Witness == null) {
          diagnostics.Add(new DafnyDiagnostic(MessageSource.TestGeneration, NoWitnessWarning, type.Origin.ReportingRange,
            $"Cannot find witness for type {userDefinedType}. Please consider adding a witness to the declaration",
            ErrorLevel.Warning, new List<DafnyRelatedInformation>()));
        }
        isSupported = TypeIsSupported(userDefinedType.AsSubsetType.Rhs, testEntry);
      } else if (userDefinedType.AsTypeSynonym != null) {
        isSupported = TypeIsSupported(userDefinedType.AsTypeSynonym.Rhs, testEntry);
      } else if (userDefinedType.IsDatatype) {
        if (userDefinedType.IsCoDatatype) {
          diagnostics.Add(new DafnyDiagnostic(MessageSource.TestGeneration, NotFullySupportedInputTypeWarning, type.Origin.ReportingRange,
            $"Test Generation has not been properly tested with co-inductive datatypes.\n{genericMessage}",
            ErrorLevel.Warning, new List<DafnyRelatedInformation>()));
        } else {
          isSupported = true;
        }
        if (userDefinedType.ResolvedClass is DatatypeDecl datatypeDecl) {
          foreach (var constructor in datatypeDecl.Ctors) {
            foreach (var formal in constructor.Children.OfType<Formal>()) {
              isSupported = TypeIsSupported(formal.Type, testEntry) && isSupported;
            }
          }
        }
      } else {
        isSupported = true;
      }
    }

    foreach (var arg in type.TypeArgs) {
      if (!TypeIsSupported(arg, testEntry)) {
        isSupported = false; // No short-circuiting here to emit all possible errors/warnings
      }
    }
    return isSupported;
  }

  /// <summary>
  /// Return true if the program has at least one method/function annotated with {:testEntry}
  /// </summary>
  private bool CheckHasTestEntry(Program program) {
    if (!Utils.ProgramHasAttribute(program, TestGenerationOptions.TestEntryAttribute)) {
      diagnostics.Add(new DafnyDiagnostic(MessageSource.TestGeneration, NoTestEntryError, program.Origin.ReportingRange,
        $"Cannot find a method or function annotated with {{:{TestGenerationOptions.TestEntryAttribute}}}",
        ErrorLevel.Error, new List<DafnyRelatedInformation>()));
      return false;
    }
    return true;
  }

  /// <summary>
  /// Builds a call graph for the entire program by adding edges to it on each call to VisitCallable
  /// </summary>
  private class CallGraphBuilderCloner : Cloner {
    internal readonly Dictionary<ICallable, HashSet<ICallable>> Edges;
    private ICallable currentlyVisited; // method/function from which the call is made

    internal CallGraphBuilderCloner() : base(false, true) {
      Edges = new();
      currentlyVisited = null;
    }

    public void VisitCallable(ICallable callable) {
      currentlyVisited = callable;
      if (callable is Method method) {
        base.CloneBlockStmt(method.Body);
      } else if (callable is Function function) {
        if (function.ByMethodBody != null) {
          base.CloneBlockStmt(function.ByMethodBody);
        } else if (function.Body != null) {
          base.CloneExpr(function.Body);
        }
      }
      currentlyVisited = null;
    }

    public override Expression CloneExpr(Expression expr) {
      if (expr is FunctionCallExpr functionCallExpr) {
        if (!Edges.ContainsKey(currentlyVisited)) {
          Edges[currentlyVisited] = [];
        }
        Edges[currentlyVisited].Add(functionCallExpr.Function);
      }
      return base.CloneExpr(expr);
    }

    public override Statement CloneStmt(Statement stmt, bool isReference) {
      if (stmt is CallStmt callStmt) {
        if (!Edges.ContainsKey(currentlyVisited)) {
          Edges[currentlyVisited] = [];
        }
        Edges[currentlyVisited].Add(callStmt.Method);
      }
      return base.CloneStmt(stmt, isReference);
    }
  }
}