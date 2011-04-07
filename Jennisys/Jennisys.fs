// This project type requires the F# PowerPack at http://fsharppowerpack.codeplex.com/releases
// Learn more about F# at http://fsharp.net
// Original project template by Jomo Fisher based on work of Brian McNamara, Don Syme and Matt Valerio
// This posting is provided "AS IS" with no warranties, and confers no rights.

open System
open Microsoft.FSharp.Text.Lexing

open Ast
open Lexer
open Parser

/// Evaluate a factor
let rec evalFactor factor =
    match factor with
    | Float x   -> x
    | Integer x -> float x
    | ParenEx x -> evalExpr x

/// Evaluate a term
and evalTerm term =
    match term with
    | Times (term, fact)  -> (evalTerm term) * (evalFactor fact)
    | Divide (term, fact) -> (evalTerm term) / (evalFactor fact)
    | Factor fact         -> evalFactor fact

/// Evaluate an expression
and evalExpr expr =
    match expr with
    | Plus (expr, term)  -> (evalExpr expr) + (evalTerm term)
    | Minus (expr, term) -> (evalExpr expr) - (evalTerm term)
    | Term term          -> evalTerm term

/// Evaluate an equation
and evalEquation eq =
    match eq with
    | Equation expr -> evalExpr expr

printfn "Calculator"

let rec readAndProcess() =
    printf ":"
    match Console.ReadLine() with
    | "quit" -> ()
    | expr ->
        try
            printfn "Lexing [%s]" expr
            let lexbuff = LexBuffer<char>.FromString(expr)
            
            printfn "Parsing..."
            let equation = Parser.start Lexer.tokenize lexbuff
            
            printfn "Evaluating Equation..."
            let result = evalEquation equation
            
            printfn "Result: %s" (result.ToString())
            
        with ex ->
            printfn "Unhandled Exception: %s" ex.Message

        readAndProcess()

readAndProcess()