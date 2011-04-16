module Printer

open Ast

let rec PrintSep sep f list =
  match list with
  | [] -> ()
  | [a] -> f a
  | a :: more -> f a ; printf "%s" sep ; PrintSep sep f more
  
let rec PrintType ty =
  match ty with
  | NamedType(id) -> printf "%s" id
  | InstantiatedType(id,arg) -> printf "%s[" id ; PrintType arg ; printf "]"

let PrintVarDecl vd =
  match vd with
  | Var(id,None) -> printf "%s" id
  | Var(id,Some(ty)) -> printf "%s: " id ; PrintType ty

let rec PrintExpr ctx expr =
  match expr with
  | IntLiteral(n) -> printf "%O" n
  | IdLiteral(id) -> printf "%s" id
  | Star -> printf "*"
  | Dot(e,id) -> PrintExpr 100 e ; printf ".%s" id
  | UnaryExpr(op,e) -> printf "%s" op ; PrintExpr 90 e
  | BinaryExpr(strength,op,e0,e1) ->
      let needParens = strength <= ctx
      if needParens then printf "(" else ()
      PrintExpr strength e0 ; printf " %s " op ; PrintExpr strength e1
      if needParens then printf ")" else ()
  | SelectExpr(e,i) -> PrintExpr 100 e ; printf "[" ; PrintExpr 0 i ; printf "]"
  | UpdateExpr(e,i,v) -> PrintExpr 100 e ; printf "[" ; PrintExpr 0 i ; printf " := " ; PrintExpr 0 v ; printf "]"
  | SequenceExpr(ee) -> printf "[" ; ee |> PrintSep ", " (PrintExpr 0) ; printf "]"
  | SeqLength(e) -> printf "|" ; PrintExpr 0 e ; printf "|"
  | ForallExpr(vv,e) ->
      let needParens = ctx <> 0
      if needParens then printf "(" else ()
      printf "forall " ; vv |> PrintSep ", " PrintVarDecl ; printf " :: " ; PrintExpr 0 e
      if needParens then printf ")" else ()

let PrintSig signature =
  match signature with
  | Sig(ins, outs) ->
      printf "("
      ins |> PrintSep ", " PrintVarDecl
      printf ")"
      if outs <> [] then
        printf " returns ("
        outs |> PrintSep ", " PrintVarDecl
        printf ")"
      else ()

let rec ForeachConjunct f expr =
  match expr with
  | IdLiteral("true") -> ()
  | BinaryExpr(_,"&&",e0,e1) -> ForeachConjunct f e0 ; ForeachConjunct f e1
  | _ -> f expr

let rec Indent i =
  if i = 0 then () else printf " " ; Indent (i-1)

let rec PrintStmt stmt indent =
  match stmt with
  | Block(stmts) ->
      Indent indent ; printfn "{"
      PrintStmtList stmts (indent + 2)
      Indent indent ; printfn "}"
  | Assign(lhs,rhs) -> Indent indent ; PrintExpr 0 lhs ; printf " := " ; PrintExpr 0 rhs ; printfn ""
and PrintStmtList stmts indent =
  stmts |> List.iter (fun s -> PrintStmt s indent)

let PrintRoutine signature pre body =
  PrintSig signature
  printfn ""
  pre |> ForeachConjunct (fun e -> printf "    requires " ; PrintExpr 0 e ; printfn "")
  PrintStmtList body 4

let PrintMember m =
  match m with
  | Field(vd) -> printf "  var " ; PrintVarDecl vd ; printfn ""
  | Constructor(id,signature,pre,body) -> printf "  constructor %s" id ; PrintRoutine signature pre body
  | Method(id,signature,pre,body) -> printf "  method %s" id ; PrintRoutine signature pre body
      
let PrintTopLevelDeclHeader kind id typeParams =
  printf "%s %s" kind id
  match typeParams with
    | [] -> ()
    | _ -> printf "[" ; typeParams |> PrintSep ", " (fun tp -> printf "%s" tp) ; printf "]"
  printfn " {"

let PrintDecl d =
  match d with
  | Class(id,typeParams,members) ->
      PrintTopLevelDeclHeader "class" id typeParams
      List.iter PrintMember members
      printfn "}"
  | Model(id,typeParams,vars,frame,inv) ->
      PrintTopLevelDeclHeader "model" id typeParams
      vars |> List.iter (fun vd -> printf "  var " ; PrintVarDecl vd ; printfn "")
      printfn "  frame"
      frame |> List.iter (fun fr -> printf "    " ; PrintExpr 0 fr ; printfn "")
      printfn "  invariant"
      inv |> ForeachConjunct (fun e -> printf "    " ; PrintExpr 0 e ; printfn "")
      printfn "}"
  | Code(id,typeParams) ->
      PrintTopLevelDeclHeader "code" id typeParams
      printfn "}"

let Print prog =
  match prog with
  | SProgram(decls) -> List.iter PrintDecl decls
