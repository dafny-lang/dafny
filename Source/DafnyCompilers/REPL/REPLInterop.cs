#nullable enable

using System.Diagnostics;
using Microsoft.Dafny;

namespace REPLInterop;

public class Utils {
  public static void Initialize() {
    Console.OutputEncoding = System.Text.Encoding.UTF8;
    DafnyOptions.Install(DafnyOptions.Create());
  }

  public static string? ReadLine() {
    return Console.In.ReadLine();
  }
}

class REPLErrorReporter : BatchErrorReporter {
  public void Clear() {
    foreach (var (_, messages) in AllMessages) {
      messages.Clear();
    }
  }

  // DISCUSS: Better heuristic for reaching EOF?
  public bool ReachedEOF(int endPos) =>
    AllMessages[ErrorLevel.Error].Any(msg =>
      msg.source == MessageSource.Parser &&
      msg.token.kind == Parser._EOF);

  public string Format(ErrorLevel level) {
    return String.Join(Environment.NewLine,
      AllMessages[level].Select(msg => ErrorToString(level, msg.token, msg.message)));
  }
}

public interface ParseResult {}
public record IncompleteParse : ParseResult;
public record ParseError(string Message) : ParseResult;
public record SuccessfulParse(REPLState ReplState, Program UnresolvedProgram, List<UserInput> NewInputs) : ParseResult {
  public ResolutionResult Resolve() {
    return ReplState.TryResolve(UnresolvedProgram) as ResolutionResult ?? new TypecheckedProgram(NewInputs);
  }
}

public interface ResolutionResult {}
public record ResolutionError(string Message) : ResolutionResult;
public record TypecheckedProgram(List<UserInput> NewInputs) : ResolutionResult;

public interface UserInput {
  string FullName { get; }
  string ShortName { get; }
}

internal record ExprInput(ConstantField Decl) : UserInput {
  public string FullName => Decl.FullName;
  public string ShortName => Decl.Name;
  public Expression Body => Decl.Rhs;
}

record Utf8Source(string Text) {
  public readonly int UTF8Length = System.Text.Encoding.UTF8.GetByteCount(Text);
}

internal class REPLInputParser {
  private static int exprCounter = 0;

  private readonly Parser parser;
  
  private readonly Utf8Source source;
  private readonly REPLState replState;

  private readonly Program unresolvedProgram;
  private readonly List<Expression> topLevelExprs;

  internal REPLInputParser(REPLState replState, Utf8Source source) {
    this.source = source;
    this.replState = replState;
    topLevelExprs = new List<Expression>();
    unresolvedProgram = replState.CloneUnresolvedProgram();
    var errors = new Errors(replState.Reporter);
    parser = Parser.SetupParser(source.Text, fullFilename: REPLState.Fname, filename: REPLState.Fname,
      include: null, unresolvedProgram.DefaultModule, unresolvedProgram.BuiltIns, errors,
      verifyThisFile: true, compileThisFile: true,
      isREPLParser: true, topLevelExprs);
  }

  private static IEnumerable<A> SkipPrefix<A>(List<A> list, List<A> prefix) {
    Debug.Assert(prefix.Count <= list.Count);
    Debug.Assert(Enumerable.Range(0, prefix.Count).All(i => ReferenceEquals(prefix[i], list[i])));
    return list.Skip(prefix.Count);
  }

  private static List<MemberDecl>? GetDefaultClassMembers(Program prog) {
    return prog.DefaultModuleDef.TopLevelDecls.OfType<DefaultClassDecl>().FirstOrDefault()?.Members;
  }

  private List<UserInput> CollectNewParseResults(Program previous) {
    var newInputs = new List<UserInput>();

    var defaultMembersBefore = GetDefaultClassMembers(previous)!;
    var defaultMembersAfter = GetDefaultClassMembers(unresolvedProgram)!;

    foreach (var expr in topLevelExprs) {
      var field = new ConstantField(expr.tok, $"_{exprCounter++}", expr, true, false,
        new InferredTypeProxy(), null);
      defaultMembersAfter.Add(field);
      newInputs.Add(new ExprInput(field));
    }

    return newInputs;
  }

  internal ParseResult TryParse() {
    replState.Reporter.Clear();
    parser.Parse();
    if (replState.Reporter.Count(ErrorLevel.Error) == 0) {
      var newInputs = CollectNewParseResults(replState.UnresolvedProgram);
      return new SuccessfulParse(replState, unresolvedProgram, newInputs);
    }
    if (replState.Reporter.ReachedEOF(source.UTF8Length)) {
      return new IncompleteParse();
    }
    return new ParseError(replState.Reporter.Format(ErrorLevel.Error));
  }
}

public class REPLState {
  internal REPLErrorReporter Reporter { get; private init; }

  internal static readonly string Fname = "<input>";

  // FIXME(performance): Dafny doesn't support incremental resolution, so we redo the full resolution every time
  internal Program UnresolvedProgram;

  public REPLState() {
    Reporter = new REPLErrorReporter();
    var defaultModule = new DefaultModuleDecl();
    var defaultModuleDecl = new LiteralModuleDecl(defaultModule, null);
    //defaultModule.TopLevelDecls.Add(new DefaultClassDecl(defaultModule, new List<MemberDecl>()));
    UnresolvedProgram = new Program(Fname, defaultModuleDecl, new BuiltIns(), Reporter);
  }

  private static Program Clone(Program prog) {
    var cloner = new Cloner();
    var defaultModule = cloner.CloneModuleDefinition(prog.DefaultModuleDef, prog.DefaultModuleDef.Name);
    var defaultModuleDecl = new LiteralModuleDecl(defaultModule, null);
    // FIXME clone builtins to preserve arrow type decls
    return new Program(prog.FullName, defaultModuleDecl, new BuiltIns(), prog.reporter);
  }

  public Program CloneUnresolvedProgram() {
    return Clone(UnresolvedProgram);
  } 
  
  public ParseResult TryParse(string input) {
    return new REPLInputParser(this, new Utf8Source(input.Trim())).TryParse();
  }

  public ResolutionError? TryResolve(Program prog) {
    Reporter.Clear();
    var unresolvedWithDecls = Clone(prog);
    new Resolver(prog).ResolveProgram(prog);
    if (Reporter.Count(ErrorLevel.Error) == 0) {
      UnresolvedProgram = unresolvedWithDecls;
      return null;
    }
    return new ResolutionError(Reporter.Format(ErrorLevel.Error));
  }
}
