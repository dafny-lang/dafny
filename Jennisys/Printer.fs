module Printer

open Ast
open AstUtils

let newline = System.Environment.NewLine // "\r\n"

let PrintGenSym name =
  sprintf "gensym%s" name

let rec PrintSep sep f list =
  match list with
  | [] -> ""
  | [a] -> f a
  | a :: more -> (f a) + sep + (PrintSep sep f more)
  
let rec PrintType ty =
  match ty with
  | IntType                   -> "int"
  | BoolType                  -> "bool"
  | NamedType(id, args)       -> if List.isEmpty args then id else (PrintSep ", " (fun s -> s) args)
  | SeqType(t)                -> sprintf "seq[%s]" (PrintType t)
  | SetType(t)                -> sprintf "set[%s]" (PrintType t)
  | InstantiatedType(id,args) -> sprintf "%s[%s]" id (PrintSep ", " (fun a -> PrintType a) args)

let PrintVarDecl vd =
  match vd with
  | Var(id,None) -> id
  | Var(id,Some(ty)) -> sprintf "%s: %s" id (PrintType ty)

let PrintVarName vd =
  match vd with
  | Var(id,_) -> id

let rec PrintExpr ctx expr =
  match expr with
  | IntLiteral(n)     -> sprintf "%d" n
  | BoolLiteral(b)    -> sprintf "%b" b
  | IdLiteral(id)     -> id
  | Star              -> "*"
  | Dot(e,id)         -> sprintf "%s.%s" (PrintExpr 100 e) id
  | UnaryExpr(op,e)   -> sprintf "%s%s" op (PrintExpr 90 e)
  | BinaryExpr(strength,op,e0,e1) ->
      let needParens = strength <= ctx
      let openParen = if needParens then "(" else ""
      let closeParen = if needParens then ")" else ""
      sprintf "%s%s %s %s%s" openParen (PrintExpr strength e0) op (PrintExpr strength e1) closeParen
  | IteExpr(c,e1,e2)  -> sprintf "%s ? %s : %s" (PrintExpr 25 c) (PrintExpr 25 e1) (PrintExpr 25 e2)
  | SelectExpr(e,i)   -> sprintf "%s[%s]" (PrintExpr 100 e) (PrintExpr 0 i) 
  | UpdateExpr(e,i,v) -> sprintf "%s[%s := %s]" (PrintExpr 100 e) (PrintExpr 0 i) (PrintExpr 0 v)
  | SequenceExpr(ee)  -> sprintf "[%s]" (ee |> PrintSep " " (PrintExpr 0))
  | SeqLength(e)      -> sprintf "|%s|" (PrintExpr 0 e)
  | SetExpr(ee)       -> sprintf "{%s}" (ee |> PrintSep " " (PrintExpr 0))
  | ForallExpr(vv,e)  ->
      let needParens = ctx <> 0
      let openParen = if needParens then "(" else ""
      let closeParen = if needParens then ")" else ""
      sprintf "%sforall %s :: %s%s" openParen (vv |> PrintSep ", " PrintVarDecl) (PrintExpr 0 e) closeParen

let PrintSig signature =
  match signature with
  | Sig(ins, outs) ->
      let returnClause = 
        if outs <> [] then sprintf " returns (%s)" (outs |> PrintSep ", " PrintVarDecl)
        else ""
      sprintf "(%s)%s" (ins |> PrintSep ", " PrintVarDecl) returnClause

let rec Indent i =
  if i = 0 then "" else " " + (Indent (i-1))

let rec PrintStmt stmt indent =
  let idt = (Indent indent)
  match stmt with
  | Block(stmts) ->
      idt + "{" + newline +
      (PrintStmtList stmts (indent + 2)) +
      idt + "}" + newline
  | Assign(lhs,rhs) -> sprintf "%s%s := %s%s" idt (PrintExpr 0 lhs) (PrintExpr 0 rhs) newline
and PrintStmtList stmts indent =
  stmts |> List.fold (fun acc s -> acc + (PrintStmt s indent)) ""

let PrintRoutine signature pre body =
  let preStr = pre |> ForeachConjunct (fun e -> sprintf "    requires %s%s" (PrintExpr 0 e) newline)
  sprintf "%s%s%s%s" (PrintSig signature) newline preStr (PrintExpr 0 body)  
  
let PrintMember m =
  match m with
  | Field(vd) -> sprintf "  var %s%s" (PrintVarDecl vd) newline 
  | Method(id,signature,pre,body,true) -> sprintf "  constructor %s%s" id (PrintRoutine signature pre body)
  | Method(id,signature,pre,body,false) -> sprintf "  method %s%s" id (PrintRoutine signature pre body)
  | Invariant(_) -> ""  // invariants are handled separately
      
let PrintTopLevelDeclHeader kind id typeParams =
  let typeParamStr = 
    match typeParams with
    | [] -> ""
    | _ -> sprintf "[%s]" (typeParams |> PrintSep ", " (fun tp -> tp))
  sprintf "%s %s%s {%s" kind id typeParamStr newline
  
let PrintDecl d =
  match d with
  | Class(id,typeParams,members) ->
      sprintf "%s%s}%s" (PrintTopLevelDeclHeader "class" id typeParams)
                        (List.fold (fun acc m -> acc + (PrintMember m)) "" members)
                        newline
  | Model(id,typeParams,vars,frame,inv) ->
      (PrintTopLevelDeclHeader "model" id typeParams) + 
      (vars |> List.fold (fun acc vd -> acc + "  var " + (PrintVarDecl vd) + newline) "") +
      "  frame" + newline +
      (frame |> List.fold (fun acc fr -> acc + "    " + (PrintExpr 0 fr) + newline) "") +
      "  invariant" + newline + 
      (inv |> ForeachConjunct (fun e -> "    " + (PrintExpr 0 e) + newline)) +
      "}" + newline
  | Code(id,typeParams) ->
      (PrintTopLevelDeclHeader "code" id typeParams) + "}" + newline

let Print prog =
  match prog with
  | SProgram(decls) -> List.fold (fun acc d -> acc + (PrintDecl d)) "" decls

let rec PrintConst cst = 
  match cst with 
  | IntConst(v)        -> sprintf "%d" v
  | BoolConst(b)       -> sprintf "%b" b
  | SetConst(cset)     -> sprintf "{%s}" (PrintSep ", " (fun c -> PrintConst c) (Set.toList cset))
  | SeqConst(cseq)     -> 
      let seqCont = cseq |> List.fold (fun acc c ->
                                         let sep = if acc = "" then "" else ", "
                                         acc + sep + (PrintConst c)                                         
                                      ) ""
      sprintf "[%s]" seqCont
  | NullConst          -> "null"
  | NoneConst          -> "<none>"
  | ThisConst(_,_)     -> "this"
  | NewObj(name,_)     -> PrintGenSym name
  | ExprConst(e)       -> PrintExpr 0 e
  | Unresolved(name)   -> sprintf "Unresolved(%s)" name