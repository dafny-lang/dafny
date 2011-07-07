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
open Parser
open Printer
open TypeChecker
open Analyzer

let readAndProcess tracing analyzing (filename: string) =
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
            // print the given Jennisys program
            if tracing then
                printfn "---------- Given Jennisys program ----------"
                printfn "%s" (Print sprog)
            else ()
            match TypeCheck sprog with
              | None -> ()  // errors have already been reported
              | Some(prog) ->
                  if analyzing then
                    // output a Dafny program with the constraints to be solved
                    Analyze prog filename
                  else ()
            // that's it
            if tracing then printfn "----------" else ()
        with
          | ex ->
              let pos = lexbuf.EndPos
              printfn "%s(%d,%d): %s" pos.FileName pos.Line pos.Column ex.Message
              printfn "%s" (ex.StackTrace.ToString())

    with
     | ex ->
        printfn "Unhandled Exception: %s" ex.Message
        printfn "%s" (ex.StackTrace.ToString())

let rec start n (args: string []) tracing analyzing filename =
  if n < args.Length then
    let arg = args.[n]
    if arg = "/break" then ignore (System.Diagnostics.Debugger.Launch()) else ()
    let filename = if arg.StartsWith "/" then filename else arg
    start (n+1) args (tracing || arg = "/trace") (analyzing && arg <> "/noAnalysis") filename
  else
    readAndProcess tracing analyzing filename

let args = Environment.GetCommandLineArgs()
try 
  start 1 args false true null
with 
  | Failure(msg) as e -> printfn "WHYYYYYYYYYYYYYYY: %s" msg; printfn "%s" e.StackTrace