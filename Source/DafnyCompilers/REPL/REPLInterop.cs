#nullable enable

using System.Diagnostics;
using Microsoft.Dafny;

namespace REPLInterop;

public class Utils {
  public static void Initialize() {
    // FIXME make C-c exit current prompt
    Console.OutputEncoding = System.Text.Encoding.UTF8;
    DafnyOptions.Install(DafnyOptions.Create());
  }

  public static string? ReadLine() {
    return Console.In.ReadLine();
  }
}

class DafnyError : Exception {
  internal readonly MessageSource source;
  internal readonly ErrorLevel level;
  internal readonly Microsoft.Boogie.IToken tok;
  internal readonly string msg;

  public DafnyError(MessageSource source, ErrorLevel level, Microsoft.Boogie.IToken tok, string msg) {
    this.source = source;
    this.level = level;
    this.tok = tok;
    this.msg = msg;
  }

  public bool ReachedEOF(string input) {
    if (source == MessageSource.Parser && tok.kind == Parser._EOF) {
      var lines = input.Split("\n");
      var col = System.Text.Encoding.UTF8.GetByteCount(lines[^1]);
      return tok.line == lines.Length && tok.col == col + 1;
    }
    return false;
  }
}

class REPLErrorReporter : BatchErrorReporter {
  public void Clear() {
    foreach (var (_, messages) in AllMessages) {
      messages.Clear();
    }
  }

  public string Format(ErrorLevel level) {
    return String.Join(Environment.NewLine,
      AllMessages[level].Select(msg => ErrorToString(level, msg.token, msg.message)));
  }

  public override bool Message(MessageSource source, ErrorLevel level, Microsoft.Boogie.IToken tok, string msg) {
    var b = base.Message(source, level, tok, msg);
    if (level == ErrorLevel.Error && source == MessageSource.Parser) {
      // Fail fast in the parser to disable error recovery
      throw new DafnyError(source, level, tok, msg);
    }
    return b;
  }
}

public interface ParseResult {}
public record FailedParse(bool Incomplete, string Message) : ParseResult;
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

internal class REPLInputParser {
  private static int exprCounter = 0;

  private readonly Parser parser;
  
  private readonly string source;
  private readonly REPLState replState;

  private readonly Program unresolvedProgram;
  private readonly List<Expression> topLevelExprs;

  internal REPLInputParser(REPLState replState, string source) {
    this.source = source;
    this.replState = replState;
    topLevelExprs = new List<Expression>();
    unresolvedProgram = replState.CloneUnresolvedProgram();
    var errors = new Errors(replState.Reporter);
    parser = Parser.SetupParser(source, fullFilename: REPLState.Fname, filename: REPLState.Fname,
      include: null, unresolvedProgram.DefaultModule, unresolvedProgram.BuiltIns, errors,
      verifyThisFile: true, compileThisFile: true,
      isREPLParser: true, topLevelExprs);
  }

  private static IEnumerable<A> SkipPrefix<A>(List<A>? prefix, List<A> list) {
    if (prefix == null) {
      return list;
    }
    Debug.Assert(prefix.Count <= list.Count);
    return list.Skip(prefix.Count);
  }

  private static void Deduplicate(List<MemberDecl> items) {
    HashSet<string> names = new();
    for (var pos = items.Count - 1; pos >= 0; pos--) {
      var name = items[pos].Name;
      if (names.Contains(name)) {
        items.RemoveAt(pos);
      } else {
        names.Add(name);
      }
    }
  }

  private static List<MemberDecl>? GetDefaultClassMembers(Program prog) {
    return prog.DefaultModuleDef.TopLevelDecls.OfType<DefaultClassDecl>().FirstOrDefault()?.Members;
  }

  private List<UserInput> CollectNewParseResults(Program previous) {
    var newInputs = new List<UserInput>();

    var defaultMembersBefore = GetDefaultClassMembers(previous);
    var defaultMembersAfter = GetDefaultClassMembers(unresolvedProgram)!;

    foreach (var newMember in SkipPrefix(defaultMembersBefore, defaultMembersAfter)) {
      if (newMember is ConstantField field) {
        newInputs.Add(new ExprInput(field));
      }
    }

    Deduplicate(defaultMembersAfter);

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

    try {
      parser.Parse();
    } catch (DafnyError err) {
      var incomplete = err.ReachedEOF(source);
      return new FailedParse(incomplete, replState.Reporter.Format(ErrorLevel.Error));
    }

    var newInputs = CollectNewParseResults(replState.UnresolvedProgram);
    return new SuccessfulParse(replState, unresolvedProgram, newInputs);
  }
}

public class REPLState {
  internal REPLErrorReporter Reporter { get; }

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
    return new REPLInputParser(this, input.TrimEnd()).TryParse();
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
