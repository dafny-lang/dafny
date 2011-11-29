// This project type requires the F# PowerPack at http://fsharppowerpack.codeplex.com/releases
// Learn more about F# at http://fsharp.net
// Original project template by Jomo Fisher based on work of Brian McNamara, Don Syme and Matt Valerio
// This posting is provided "AS IS" with no warranties, and confers no rights.
module Main

open System
open System.IO
open Microsoft.FSharp.Text.Lexing

open Ast
open Lexer
open Options
open Parser
open Printer
open TypeChecker
open Analyzer

let readAndProcess (filename: string) =
  try
    printfn "// Jennisys, Copyright (c) 2011, Microsoft."
    // lex
    let f = if filename = null then Console.In else new StreamReader(filename) :> TextReader
    let lexbuf = LexBuffer<char>.FromTextReader(f)
    lexbuf.EndPos <- { pos_bol = 0;
                       pos_fname=if filename = null then "stdin" else filename; 
                       pos_cnum=0;
                       pos_lnum=1 }
    try
      // parse
      let sprog = Parser.start Lexer.tokenize lexbuf
      match TypeCheck sprog with
      | None -> ()  // errors have already been reported
      | Some(prog) ->
          Analyze prog filename
    with
      | ex ->
          let pos = lexbuf.EndPos
          printfn "%s(%d,%d): %s" pos.FileName pos.Line pos.Column ex.Message
          printfn "%s" (ex.StackTrace.ToString())
  with
    | ex ->
        printfn "Unhandled Exception: %s" ex.Message
        printfn "%s" (ex.StackTrace.ToString())

try 
  let args = Environment.GetCommandLineArgs()
  ParseCmdLineArgs (List.ofArray args)
  readAndProcess CONFIG.inputFilename
with
  | InvalidCmdLineOption(msg) as ex -> printfn "%s" msg; printfn "%s" ex.StackTrace