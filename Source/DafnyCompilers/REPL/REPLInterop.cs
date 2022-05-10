#nullable enable

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
public interface ParsedDeclaration : ParseResult { // FIXME supports more than one in a definition
  string FullName { get; }
  string ShortName { get; }
  Expression Body { get; }
  ResolutionResult Resolve();
}

public interface ResolutionResult {}
public record ResolutionError(string Message) : ResolutionResult;
public record TypecheckedProgram : ResolutionResult;

record Utf8Source(string Text) {
  public readonly int UTF8Length = System.Text.Encoding.UTF8.GetByteCount(Text);
}

internal abstract class ParserWrapper {
  protected readonly Parser parser;
  
  private readonly Utf8Source source;
  public readonly REPLState replState;
  
  public readonly Program UnresolvedProgram;

  internal ParserWrapper(REPLState replState, Utf8Source source) {
    this.source = source;
    this.replState = replState;
    UnresolvedProgram = replState.CloneUnresolvedProgram();
    var errors = new Errors(replState.Reporter);
    parser = Parser.SetupParser(source.Text, fullFilename: REPLState.Fname, filename: REPLState.Fname,
      include: null, UnresolvedProgram.DefaultModule, UnresolvedProgram.BuiltIns, errors);
    parser.PreParse();
  }

  protected bool ReachedEOF =>
    replState.Reporter.ReachedEOF(source.UTF8Length);

  internal abstract ParseResult TryParse();
}

internal class ExprParseResult : ParsedDeclaration {
  private static int counter = 0;

  private readonly MemberDecl memberDecl;
  private readonly ParserWrapper parser;

  public string FullName => memberDecl.FullName;
  public string ShortName => memberDecl.Name;
  public Expression Body { get; init; }
  
  public ExprParseResult(ParserWrapper parser, Expression expr) {
    this.parser = parser;
    memberDecl = new ConstantField(expr.tok, $"_{counter++}", expr, true, false, new InferredTypeProxy(), null);
    var members = GetDefaultClassMembers(parser.UnresolvedProgram)!;
    members.RemoveAll(m => m.Name == ShortName);
    members.Add(memberDecl);
    this.Body = expr;
  }

  private static List<MemberDecl>? GetDefaultClassMembers(Program prog) {
    return prog.DefaultModuleDef.TopLevelDecls.OfType<DefaultClassDecl>().FirstOrDefault()?.Members;
  }

  public ResolutionResult Resolve() {
    return parser.replState.TryResolve(parser.UnresolvedProgram);
  }
}

internal class ExprParser : ParserWrapper {
  internal ExprParser(REPLState replState, Utf8Source source) : base(replState, source) {}

  internal override ParseResult TryParse() {
    replState.Reporter.Clear();
    var expr = parser.ParseExpression();
    if (replState.Reporter.Count(ErrorLevel.Error) == 0) {
      return new ExprParseResult(this, expr);
    }
    if (ReachedEOF) {
      return new IncompleteParse();
    }
    return new ParseError(replState.Reporter.Format(ErrorLevel.Error));
  }
}

public class REPLState {
  internal readonly REPLErrorReporter Reporter;

  internal static readonly string Fname = "<input>";

  // FIXME(performance): Dafny doesn't support incremental resolution, so we redo the full parsing + resolution every time
  private Program unresolvedProgram;
  internal Program? ResolvedProgram { get; private set; }

  public REPLState() {
    Reporter = new REPLErrorReporter();
    var defaultModule = new DefaultModuleDecl();
    var defaultModuleDecl = new LiteralModuleDecl(defaultModule, null);
    defaultModule.TopLevelDecls.Add(new DefaultClassDecl(defaultModule, new List<MemberDecl>()));
    unresolvedProgram = new Program(Fname, defaultModuleDecl, new BuiltIns(), Reporter);
  }

  private Program Clone(Program prog) {
    var cloner = new Cloner();
    var defaultModule = cloner.CloneModuleDefinition(prog.DefaultModuleDef, prog.DefaultModuleDef.Name);
    var defaultModuleDecl = new LiteralModuleDecl(defaultModule, null);
    // FIXME clone builtins to preserve arrow type decls
    return new Program(prog.FullName, defaultModuleDecl, new BuiltIns(), prog.reporter);
  }

  public Program CloneUnresolvedProgram() {
    return Clone(unresolvedProgram);
  } 
  
  public ParseResult TryParse(string input) {
    // FIXME: Really needs new rule in DafnyAtg; otherwise we don't know which error messages to return
    return new ExprParser(this, new Utf8Source(input.Trim())).TryParse();
  }

  public ResolutionResult TryResolve(Program prog) {
    Reporter.Clear();
    var unresolvedWithDecls = Clone(prog);
    new Resolver(prog).ResolveProgram(prog);
    if (Reporter.Count(ErrorLevel.Error) == 0) {
      unresolvedProgram = unresolvedWithDecls;
      ResolvedProgram = prog;
      return new TypecheckedProgram();
    }
    return new ResolutionError(Reporter.Format(ErrorLevel.Error));
  }
}
