include "../Interp.dfy"
include "../CompilerCommon.dfy"
include "../Printer.dfy"
include "../Library.dfy"
include "../CSharpInterop.dfy"
include "../CSharpDafnyASTModel.dfy"
include "../CSharpDafnyInterop.dfy"
include "../../AutoExtern/CSharpModel.dfy"

import DafnyCompilerCommon.AST
import DafnyCompilerCommon.Translator
import opened Lib.Datatypes
import opened CSharpDafnyInterop
import C = CSharpDafnyASTModel

module {:extern "REPLInterop"} {:compile false} REPLInterop {
  import System
  import C = CSharpDafnyASTModel

  class {:compile false} {:extern} Utils {
    constructor {:extern} () requires false

    static method {:extern} Initialize()

    static method {:extern} ReadLine()
      returns (e: System.String?)

    static method {:extern} RunWithCustomStack<A, B>(f: A -> B, a0: A, size: System.int32)
      returns (b: B)
      ensures b == f(a0)
  }

  trait {:compile false} {:extern} ParseResult {
    lemma Sealed()
      ensures || this is FailedParse
              || this is SuccessfulParse
  }
  class {:compile false} {:extern} FailedParse extends ParseResult {
    lemma Sealed() {}
    constructor {:extern} () requires false
    var {:extern} Incomplete: bool;
    var {:extern} Message: System.String;
  }
  class {:compile false} {:extern} SuccessfulParse extends ParseResult {
    method {:extern} Resolve() returns (r: ResolutionResult)
    lemma Sealed() {}
  }

  trait {:compile false} {:extern} ResolutionResult {
    lemma Sealed()
      ensures || this is ResolutionError
              || this is TypecheckedProgram
  }
  class {:compile false} {:extern} ResolutionError extends ResolutionResult {
    lemma Sealed() {}
    constructor {:extern} () requires false
    var {:extern} Message: System.String;
  }
  class {:compile false} {:extern} TypecheckedProgram extends ResolutionResult {
    lemma Sealed() {}
    constructor {:extern} () requires false
    var {:extern} NewInputs: System.Collections.Generic.List<UserInput>;
  }

  trait {:compile false} {:extern} UserInput {
    lemma Sealed()
      ensures || this is MemberDeclInput
    var {:extern} FullName: System.String;
    var {:extern} ShortName: System.String;
  }
  class {:compile false} {:extern} MemberDeclInput extends UserInput {
    lemma Sealed() {}
    constructor {:extern} () requires false
    var {:extern} IsTopLevelExpr: bool;
    var {:extern} Decl: C.MemberDecl;
  }

  class {:compile false} {:extern} REPLState {
    constructor {:extern} ()
    method {:extern} TryParse(input: System.String) returns (p: ParseResult)
  }
}

datatype REPLError =
  | EOF()
  | StackOverflow()
  | FailedParse(pmsg: string)
  | ResolutionError(rmsg: string)
  | TranslationError(te: Translator.TranslationError)
  | InterpError(ie: Interp.InterpError)
  | Unsupported(e: AST.Expr)
{
  function method ToString() : string {
    match this
      case EOF() =>
        "EOF"
      case StackOverflow() =>
        "Stack overflow"
      case FailedParse(msg) =>
        "Parse error:\n" + msg
      case ResolutionError(msg) =>
        "Resolution error:\n" + msg
      case TranslationError(te) =>
        "Translation error: " + te.ToString()
      case InterpError(ie) =>
        "Execution error: " + ie.ToString()
      case Unsupported(ex) =>
        "Unsupported expression" // FIXME change checker to return the unsupported subexpression
  }
}

type REPLResult<+A> = Result<A, REPLError>

datatype Named<+A> = Named(fullName: string, shortName: string, body: A)

class REPL {
  var state: REPLInterop.REPLState;
  var globals: Interp.Context;
  var counter: int;

  constructor() {
    state := new REPLInterop.REPLState();
    globals := map[];
    counter := 0;
  }

  static method ReadLine(prompt: string)
    returns (o: Option<string>)
    decreases *
  {
    while true
      decreases *
    {
      print prompt;
      var line := REPLInterop.Utils.ReadLine();
      if line == null {
        return None;
      } else {
        var line := TypeConv.AsString(line);
        if line == "" {
          continue;
        }
        return Some(line);
      }
    }
  }

  method Read() returns (r: REPLResult<REPLInterop.SuccessfulParse>)
    modifies this`counter
    decreases *
  {
    var prompt := "dfy[" + Lib.Str.of_int(counter) + "] ";
    var input: string := "";
    counter := counter + 1;
    while true
      invariant |prompt| > 0
      decreases *
    {
      var ln := ReadLine(prompt);
      var line :- ln.ToSuccessOr(EOF());

      input := input + line + "\n";
      var parsed: REPLInterop.ParseResult :=
        state.TryParse(StringUtils.ToCString(input));

      if parsed is REPLInterop.FailedParse {
        var p := parsed as REPLInterop.FailedParse; // BUG(https://github.com/dafny-lang/dafny/issues/1731)
        if p.Incomplete {
          prompt := if prompt[0] == '.' then prompt
                   else seq(|prompt| - 1, _ => '.') + " ";
          continue;
        }
        return Failure(FailedParse(TypeConv.AsString(p.Message)));
      } else {
        parsed.Sealed();
        return Success(parsed as REPLInterop.SuccessfulParse);
      }
    }
  }

  function method AbsOfFunction(fn: C.Function)
    : Result<AST.Expr, Translator.TranslationError>
    reads *
  {
    var inParams := Lib.Seq.MapFilter(CSharpInterop.ListUtils.ToSeq(fn.Formals), (f: C.Formal) reads * =>
      if f.InParam then Some(TypeConv.AsString(f.Name)) else None);
    var body :- Translator.TranslateExpression(fn.Body);
    Success(AST.Exprs.Abs(inParams, body))
  }

  function method TranslateBody(input: REPLInterop.UserInput)
    : Result<AST.Expr, Translator.TranslationError>
    reads *
  {
    if input is REPLInterop.MemberDeclInput then
      var ei := input as REPLInterop.MemberDeclInput;
      if ei.Decl is C.ConstantField then
        var cf := ei.Decl as C.ConstantField;
        Translator.TranslateExpression(cf.Rhs)
      else if ei.Decl is C.Function then
        AbsOfFunction(ei.Decl as C.Function)
      else
        Failure(Translator.UnsupportedMember(ei.Decl))
    else
      (input.Sealed();
       Lib.ControlFlow.Unreachable())
  }

  function method TranslateInput(input: REPLInterop.UserInput)
    : REPLResult<Named<Interp.Expr>>
    reads *
  {
    var fullName := TypeConv.AsString(input.FullName);
    var shortName := TypeConv.AsString(input.ShortName);
    var body :- TranslateBody(input).MapFailure(e => TranslationError(e));
    :- Need(Interp.SupportsInterp(body), Unsupported(body));
    Success(Named(fullName, shortName, body))
  }

  method ReadResolve() returns (r: REPLResult<seq<Named<Interp.Expr>>>)
    modifies this`counter
    decreases *
  {
    var inputs :- Read();

    var tcRes: REPLInterop.ResolutionResult := inputs.Resolve();
    if tcRes is REPLInterop.ResolutionError {
      var err := tcRes as REPLInterop.ResolutionError;
      return Failure(ResolutionError(TypeConv.AsString(err.Message)));
    }

    tcRes.Sealed();
    var newInputs :=
      var tp := tcRes as REPLInterop.TypecheckedProgram;
      CSharpInterop.ListUtils.ToSeq(tp.NewInputs);
    return Lib.Seq.MapResult(newInputs, TranslateInput);
  }

  static const MAX_FUEL := 1024;
  static const FRAME_SIZE := 1024 * 1024;

  static method InterpExpr(e: Interp.Expr, env: Interp.Environment)
    returns (r: REPLResult<Interp.InterpReturn<Interp.Value>>)
    requires env.fuel < MAX_FUEL
  {
    var stackSize := FRAME_SIZE * env.fuel;
    var fn := (_: ()) => Interp.Eval(e, env, Interp.State.Empty).MapFailure(e => InterpError(e));
    r := REPLInterop.Utils.RunWithCustomStack(fn, (), stackSize as System.int32);
  }

  static method Eval(e: Interp.Expr, globals: Interp.Context) returns (r: REPLResult<Interp.Value>)
    decreases *
  {
    var fuel: nat := 4;
    while true
      invariant fuel < MAX_FUEL
      decreases *
    {
      var env := Interp.Environment(fuel := fuel, globals := globals);
      var v := InterpExpr(e, env);
      match v
        case Success(Return(val, _)) =>
          return Success(val);
        case Failure(InterpError(OutOfFuel(_))) =>
          fuel := fuel * 2;
          if fuel >= MAX_FUEL {
            return Failure(StackOverflow);
          } else {
            print "Fuel exhausted, trying again with fuel := ", fuel, "\n";
          }
        case Failure(err) =>
          return Failure(err);
    }
  }

  method ReadEval()
    returns (r: REPLResult<seq<Named<Interp.Value>>>)
    modifies this`counter, this`globals
    decreases *
  {
    var rds :- ReadResolve();

    var idx := 0;
    var outputs := [];
    for idx := 0 to |rds| {
      var Named(fullName, shortName, body) := rds[idx];
      var val :- Eval(body, globals);
      globals := globals[fullName := val];
      outputs := outputs + [Named(fullName, shortName, val)];
    }

    return Success(outputs);
  }
}

method Main()
  decreases *
{
  REPLInterop.Utils.Initialize();
  var repl := new REPL();
  while true
    decreases * {
    var r := repl.ReadEval();
    match r {
      case Failure(EOF()) =>
        return;
      case Failure(err) =>
        print err.ToString();
      case Success(results) =>
        for idx := 0 to |results| {
          var Named(_, shortName, val) := results[idx];
          print shortName, " := ", Interp.Printer.ToString(val);
        }
    }
    print "\n";
  }
}
