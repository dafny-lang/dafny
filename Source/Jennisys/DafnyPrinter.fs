module DafnyPrinter

open Ast
open Getters
open AstUtils
open PrintUtils

let rec PrintType ty =
  match ty with
  | IntType                   -> "int"
  | BoolType                  -> "bool"
  | SeqType(t)                -> sprintf "seq<%s>" (PrintType t)
  | SetType(t)                -> sprintf "set<%s>" (PrintType t)
  | NamedType(id,args)        -> if List.isEmpty args then id else sprintf "%s<%s>" id (PrintSep ", " (fun s -> s) args)
  | InstantiatedType(id,args) -> if List.isEmpty args then id else sprintf "%s<%s>" id (PrintSep ", " (fun t -> PrintType t) args)

let PrintVarDecl vd =
  let name = GetExtVarName vd
  match GetVarType vd with
  | None     -> name
  | Some(ty) -> sprintf "%s: %s" name (PrintType ty)

let rec PrintExpr ctx expr =
  match expr with
  | IntLiteral(d)     -> sprintf "%d" d
  | BoolLiteral(b)    -> sprintf "%b" b
  | BoxLiteral(id)    -> sprintf "box_%s" id
  | ObjLiteral(id)
  | VarLiteral(id)
  | IdLiteral(id) -> id
  | VarDeclExpr(vlist, declare) -> 
      let decl = if declare then "var " else ""
      let vars = PrintSep ", " PrintVarDecl vlist
      sprintf "%s%s" decl vars
  | Star -> "*"
  | Dot(e,id) -> sprintf "%s.%s" (PrintExpr 100 e) id
  | LCIntervalExpr(e) -> sprintf "%s.." (PrintExpr 90 e)
  | OldExpr(e) -> sprintf "old(%s)" (PrintExpr 90 e)
  | UnaryExpr(op,UnaryExpr(op2, e2))   -> sprintf "%s(%s)" op (PrintExpr 90 (UnaryExpr(op2, e2)))
  | UnaryExpr(op,e) -> sprintf "%s%s" op (PrintExpr 90 e)
  | BinaryExpr(strength,"in",lhs,BinaryExpr(_,"...",lo,hi)) ->
      let needParens = strength <= ctx
      let openParen = if needParens then "(" else ""
      let closeParen = if needParens then ")" else ""
      let loStr = PrintExpr strength lo
      let hiStr = PrintExpr strength hi
      let lhsStr = PrintExpr strength lhs
      sprintf "%s%s <= %s && %s <= %s%s" openParen loStr lhsStr lhsStr hiStr closeParen
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
  | AssertExpr(e)     -> sprintf "assert %s" (PrintExpr 0 e)
  | AssumeExpr(e)     -> sprintf "assume %s" (PrintExpr 0 e)
  | ForallExpr(vv,e)  ->
      let needParens = true
      let openParen = if needParens then "(" else ""
      let closeParen = if needParens then ")" else ""
      sprintf "%sforall %s :: %s%s" openParen (vv |> PrintSep ", " PrintVarDecl) (PrintExpr 0 e) closeParen
  | MethodCall(rcv,_,name,aparams) ->
      sprintf "%s.%s(%s)" (PrintExpr 0 rcv) name (aparams |> PrintSep ", " (PrintExpr 0))
  | MethodOutSelect(mth,name)      ->      
      // TODO: this can only work if there is only 1 out parameter
      sprintf "%s" (PrintExpr 0 mth) 

let rec PrintConst cst = 
  match cst with 
  | IntConst(v)        -> sprintf "%d" v
  | BoolConst(b)       -> sprintf "%b" b
  | BoxConst(id)       -> sprintf "box_%s" id
  | VarConst(v)        -> sprintf "%s" v
  | SetConst(cset)     -> sprintf "{%s}" (PrintSep ", " (fun c -> PrintConst c) (Set.toList cset))
  | SeqConst(cseq)     -> sprintf "[%s]" (PrintSep ", " (fun c -> PrintConst c) cseq)
  | NullConst          -> "null"
  | NoneConst          -> "<none>"
  | ThisConst(_,_)     -> "this"
  | NewObj(name,_)     -> PrintGenSym name
  | Unresolved(name)   -> sprintf "Unresolved(%s)" name

let PrintSig signature =
  match signature with
  | Sig(ins, outs) ->
      let returnClause = 
        if outs <> [] then sprintf " returns (%s)" (outs |> PrintSep ", " PrintVarDecl)
        else ""
      sprintf "(%s)%s" (ins |> PrintSep ", " PrintVarDecl) returnClause

let PrintTypeParams typeParams = 
  match typeParams with
  | [] -> ""
  | _ -> sprintf "<%s>" (typeParams |> PrintSep ", " (fun tp -> tp))

let PrintFields vars indent ghost = 
  let ghostStr = if ghost then "ghost " else ""
  vars |> List.fold (fun acc v -> match GetVarType v with 
                                  | None     -> acc + (sprintf "%s%svar %s;%s" (Indent indent) ghostStr (GetExtVarName v) newline)
                                  | Some(tp) -> acc + (sprintf "%s%svar %s: %s;%s" (Indent indent) ghostStr (GetExtVarName v) (PrintType tp) newline)) ""

let rec _PrintStmt stmt indent printNewline =
  let idt = Indent indent
  let nl = if printNewline then newline else ""
  match stmt with
  | Block(stmts) ->
      idt + "{" + nl +
      (_PrintStmtList stmts (indent + 2) true) +
      idt + "}" + nl
  | Assign(lhs,rhs) -> sprintf "%s%s := %s;%s" idt (PrintExpr 0 lhs) (PrintExpr 0 rhs) nl
  | ExprStmt(expr) -> sprintf "%s%s;%s" idt (PrintExpr 0 expr) nl
and _PrintStmtList stmts indent printNewLine =
  let idt = Indent indent
  let str = stmts |> PrintSep newline (fun s -> _PrintStmt s indent false)
  if printNewLine then
    str + newline
  else
    str

let PrintStmt stmt indent printNewline =
  let stmts = PullUpMethodCalls stmt
  _PrintStmtList stmts indent printNewline

let PrintStmtList stmts indent printNewLine =
  stmts |> List.fold (fun acc s -> acc + (PrintStmt s indent printNewLine)) ""