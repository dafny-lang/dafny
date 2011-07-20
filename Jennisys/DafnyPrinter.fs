module DafnyPrinter

open Ast
open AstUtils
open Printer

let rec PrintType ty =
  match ty with
  | IntType                   -> "int"
  | BoolType                  -> "bool"
  | SeqType(t)                -> sprintf "seq<%s>" (PrintType t)
  | SetType(t)                -> sprintf "set<%s>" (PrintType t)
  | NamedType(id,args)        -> if List.isEmpty args then id else sprintf "%s<%s>" id (PrintSep ", " (fun s -> s) args)
  | InstantiatedType(id,args) -> sprintf "%s<%s>" id (PrintSep ", " (fun t -> PrintType t) args)

let rec PrintExpr ctx expr =
  match expr with
  | IntLiteral(d)     -> sprintf "%d" d
  | BoolLiteral(b)    -> sprintf "%b" b
  | ObjLiteral(id)
  | VarLiteral(id)
  | IdLiteral(id) -> id
  | Star -> assert false; "" // I hope this won't happen
  | Dot(e,id) -> sprintf "%s.%s" (PrintExpr 100 e) id
  | UnaryExpr(op,UnaryExpr(op2, e2))   -> sprintf "%s(%s)" op (PrintExpr 90 (UnaryExpr(op2, e2)))
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
  | IteExpr(c,e1,e2)  -> sprintf "(if %s then %s else %s)" (PrintExpr 25 c) (PrintExpr 25 e1) (PrintExpr 25 e2)
  | SelectExpr(e,i)   -> sprintf "%s[%s]" (PrintExpr 100 e) (PrintExpr 0 i)
  | UpdateExpr(e,i,v) -> sprintf "%s[%s := %s]" (PrintExpr 100 e) (PrintExpr 0 i) (PrintExpr 0 v)
  | SequenceExpr(ee)  -> sprintf "[%s]" (ee |> PrintSep ", " (PrintExpr 0))
  | SeqLength(e)      -> sprintf "|%s|" (PrintExpr 0 e)
  | SetExpr(ee)       -> sprintf "{%s}" (ee |> PrintSep ", " (PrintExpr 0))
  | ForallExpr(vv,e)  ->
      let needParens = true
      let openParen = if needParens then "(" else ""
      let closeParen = if needParens then ")" else ""
      sprintf "%sforall %s :: %s%s" openParen (vv |> PrintSep ", " PrintVarDecl) (PrintExpr 0 e) closeParen

let rec PrintConst cst = 
  match cst with 
  | IntConst(v)        -> sprintf "%d" v
  | BoolConst(b)       -> sprintf "%b" b
  | VarConst(v)        -> sprintf "%s" v
  | SetConst(cset)     -> sprintf "{%s}" (PrintSep ", " (fun c -> PrintConst c) (Set.toList cset))
  | SeqConst(cseq)     -> sprintf "[%s]" (PrintSep ", " (fun c -> PrintConst c) cseq)
  | NullConst          -> "null"
  | NoneConst          -> "<none>"
  | ThisConst(_,_)     -> "this"
  | NewObj(name,_)     -> PrintGenSym name
  | Unresolved(name)   -> sprintf "Unresolved(%s)" name

let PrintTypeParams typeParams = 
  match typeParams with
  | [] -> ""
  | _ -> sprintf "<%s>" (typeParams |> PrintSep ", " (fun tp -> tp))

let PrintFields vars indent ghost = 
  let ghostStr = if ghost then "ghost " else ""
  vars |> List.fold (fun acc v -> match v with 
                                  | Var(nm,None)     -> acc + (sprintf "%s%svar %s;%s" (Indent indent) ghostStr nm newline)
                                  | Var(nm,Some(tp)) -> acc + (sprintf "%s%svar %s: %s;%s" (Indent indent) ghostStr nm (PrintType tp) newline)) ""

let rec PrintStmt stmt indent =
  let idt = (Indent indent)
  match stmt with
  | Block(stmts) ->
      idt + "{" + newline +
      (PrintStmtList stmts (indent + 2)) +
      idt + "}" + newline
  | Assign(lhs,rhs) -> sprintf "%s%s := %s;%s" idt (PrintExpr 0 lhs) (PrintExpr 0 rhs) newline
and PrintStmtList stmts indent =
  stmts |> List.fold (fun acc s -> acc + (PrintStmt s indent)) ""