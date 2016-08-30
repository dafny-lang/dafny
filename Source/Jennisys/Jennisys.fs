// This project type requires the F# PowerPack at http://fsharppowerpack.codeplex.com/releases
// Learn more about F# at http://fsharp.net
// Original project template by Jomo Fisher based on work of Brian McNamara, Don Syme and Matt Valerio
// This posting is provided "AS IS" with no warranties, and confers no rights.
module Main

open System
open System.IO
open Microsoft.FSharp.Text.Lexing

open Ast
open AstUtils
open Lexer
open Options
open Parser
open Printer
open TypeChecker
open Analyzer

let readAndProcess (filename: string) =
  printfn "// Jennisys, Copyright (c) 2011, Microsoft."
  // lex
  let f = if filename = null then Console.In else new StreamReader(filename) :> TextReader
  let lexbuf = LexBuffer<char>.FromTextReader(f)
  lexbuf.EndPos <- { pos_bol = 0;
                     pos_fname=if filename = null then "stdin" else filename; 
                     pos_cnum=0;
                     pos_lnum=1 }
  
  let sprog = 
    try 
      // parse
      Parser.start Lexer.tokenize lexbuf
    with
    | ex ->
        let pos = lexbuf.EndPos
        printfn "  [PARSE ERROR]: %s(%d,%d): %s" pos.FileName pos.Line pos.Column ex.Message
        Environment.Exit(1)
        failwith ""
  match TypeCheck sprog with
  | None -> ()  // errors have already been reported
  | Some(prog) ->
      Analyze prog filename
  

try 
  let args = Environment.GetCommandLineArgs()
  ParseCmdLineArgs (List.ofArray args |> List.tail)
  if CONFIG.breakIntoDebugger then ignore (System.Diagnostics.Debugger.Launch()) else ()
  if CONFIG.help then 
    printfn "%s" PrintHelpMsg
  else 
    if CONFIG.inputFilename = "" then
      printfn "*** Error: No input file was specified."
    else
      readAndProcess CONFIG.inputFilename
with
  | InvalidCmdLineOption(msg) 
  | InvalidCmdLineArg(msg) as ex -> 
      printfn "  [ERROR] %s" msg; 
      printfn "%s" PrintHelpMsg
  | EvalFailed(msg) as ex -> 
      printfn "  [EVALUATION ERROR]  %s" msg
      printfn "%O" ex.StackTrace 

//let mc = MethodOutSelect (MethodCall(IdLiteral("left"),"SetNode","Find",[VarLiteral("n")]), "ret")
//let expr = BinaryOr (BinaryOr (BinaryEq (VarLiteral("a")) (VarLiteral("b"))) mc) (mc) 
//printfn "%s" (PrintExpr 0 expr)
//printfn ""
//
//let stmt = ExprStmt(expr)
//printfn "%s" (DafnyPrinter.PrintStmt stmt 0 false)