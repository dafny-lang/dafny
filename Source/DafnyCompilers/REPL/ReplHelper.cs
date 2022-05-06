using System.Diagnostics.Contracts;
using Microsoft.Dafny;

namespace REPL;

public class ReplHelper {
  private static readonly string fname = "<input>";

  private readonly DefaultClassDecl defaultClass;
  private readonly LiteralModuleDecl defaultModuleDecl;
  private readonly BuiltIns builtIns;
  private readonly string source;

  public Expression Expression { get; set; }

  public static void Setup() {
    Console.OutputEncoding = System.Text.Encoding.UTF8;
    DafnyOptions.Install(DafnyOptions.Create());
  }

  public static string Input() {
    return Console.In.ReadLine();
  }

  public ReplHelper(string source) {
    this.source = source;
    var defaultModule = new DefaultModuleDecl();
    defaultModuleDecl = new LiteralModuleDecl(defaultModule, null);
    defaultClass = new DefaultClassDecl(defaultModule, new List<MemberDecl>());
    defaultModule.TopLevelDecls.Add(defaultClass);
    builtIns = new BuiltIns();
  }

  public bool Parse() {
    Contract.Assert(Expression == null);
    var reporter = new ConsoleErrorReporter();
    var errors = new Errors(reporter);
    Expression = Parser.ParseExpression(source, fname, fname, null, defaultModuleDecl, builtIns, errors);
    return reporter.Count(ErrorLevel.Error) == 0;
  }

  private static MemberDecl MakeConstantField(Expression expr) {
    var type = new InferredTypeProxy();
    return new ConstantField(expr.tok, "internal_tmp_variable", expr, true, false, type, null);
  }

  public bool Resolve() {
    Contract.Assert(Expression is {Type: null});
    var reporter = new ConsoleErrorReporter();
    var dafnyProgram = new Program(fname, defaultModuleDecl, builtIns, reporter);
    defaultClass.Members.Add(MakeConstantField(Expression)); // FIXME do this better?
    var resolver = new Resolver(dafnyProgram);
    resolver.ResolveProgram(dafnyProgram);
    return reporter.Count(ErrorLevel.Error) == 0;
  }
}
