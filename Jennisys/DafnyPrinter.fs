module DafnyPrinter

open Ast
open Printer

let rec PrintType ty =
  match ty with
  | NamedType(id) -> id
  | InstantiatedType(id,arg) -> sprintf "%s<%s>" id (PrintType arg) 

let rec PrintExpr ctx expr =
  match expr with
  | IntLiteral(n) -> sprintf "%O" n
  | IdLiteral(id) -> id
  | Star -> assert false; "" // I hope this won't happen
  | Dot(e,id) -> sprintf "%s.%s" (PrintExpr 100 e) id
  | UnaryExpr(op,e) -> sprintf "%s%s" op (PrintExpr 90 e)
  | BinaryExpr(strength,op,e0,e1) ->
      let op =
        match op with
          | "=" -> "=="
          | "div" -> "/"
          | "mod" -> "%"
          | _ -> op
      let needParens = strength <= ctx
      let openParen = if needParens then "(" else ""
      let closeParen = if needParens then ")" else ""
      sprintf "%s%s %s %s%s" openParen (PrintExpr strength e0) op (PrintExpr strength e1) closeParen
  | SelectExpr(e,i)   -> sprintf "%s[%s]" (PrintExpr 100 e) (PrintExpr 0 i)
  | UpdateExpr(e,i,v) -> sprintf "%s[%s := %s]" (PrintExpr 100 e) (PrintExpr 0 i) (PrintExpr 0 v)
  | SequenceExpr(ee)  -> sprintf "[%s]" (ee |> PrintSep ", " (PrintExpr 0))
  | SeqLength(e)      -> sprintf "|%s|" (PrintExpr 0 e)
  | ForallExpr(vv,e)  ->
      let needParens = true
      let openParen = if needParens then "(" else ""
      let closeParen = if needParens then ")" else ""
      sprintf "%sforall %s :: %s%s" openParen (vv |> PrintSep ", " PrintVarDecl) (PrintExpr 0 e) closeParen

let PrintTypeParams typeParams = 
  match typeParams with
  | [] -> ""
  | _ -> sprintf "<%s>" (typeParams |> PrintSep ", " (fun tp -> tp))

let PrintFields vars indent = 
  vars |> List.fold (fun acc v -> match v with 
                                  | Var(nm,None)     -> acc + (sprintf "%svar %s;%s" (Indent indent) nm newline)
                                  | Var(nm,Some(tp)) -> acc + (sprintf "%svar %s: %s;%s" (Indent indent) nm (PrintType tp) newline)) ""