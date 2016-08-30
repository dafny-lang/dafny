module Printer

open Ast
open Getters
open AstUtils
open PrintUtils     
  
let rec PrintType ty =
  match ty with
  | IntType                   -> "int"
  | BoolType                  -> "bool"
  | NamedType(id, args)       -> if List.isEmpty args then id else (PrintSep ", " (fun s -> s) args)
  | SeqType(t)                -> sprintf "seq[%s]" (PrintType t)
  | SetType(t)                -> sprintf "set[%s]" (PrintType t)
  | InstantiatedType(id,args) -> sprintf "%s[%s]" id (PrintSep ", " (fun a -> PrintType a) args)

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
  | IdLiteral(id)     -> id
  | VarDeclExpr(vlist, declare) -> 
      let decl = if declare then "var " else ""
      let vars = PrintSep ", " PrintVarDecl vlist
      sprintf "%s%s" decl vars
  | Star              -> "*"
  | Dot(e,id)         -> sprintf "%s.%s" (PrintExpr 100 e) id
  | LCIntervalExpr(e) -> sprintf "%s.." (PrintExpr 90 e)
  | OldExpr(e)        -> sprintf "old(%s)" (PrintExpr 90 e)
  | UnaryExpr(op,UnaryExpr(op2, e2))   -> sprintf "%s(%s)" op (PrintExpr 90 (UnaryExpr(op2, e2)))
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
  | AssertExpr(e)     -> sprintf "assert %s" (PrintExpr 0 e)
  | AssumeExpr(e)     -> sprintf "assume %s" (PrintExpr 0 e)
  | ForallExpr(vv,e)  ->
      let needParens = ctx <> 0
      let openParen = if needParens then "(" else ""
      let closeParen = if needParens then ")" else ""
      sprintf "%sforall %s :: %s%s" openParen (vv |> PrintSep ", " PrintVarDecl) (PrintExpr 0 e) closeParen
  | MethodCall(rcv,_,name,aparams) ->
      sprintf "%s.%s(%s)" (PrintExpr 0 rcv) name (aparams |> PrintSep ", " (PrintExpr 0))
  | MethodOutSelect(mth,name)      ->
      sprintf "%s[\"%s\"]" (PrintExpr 0 mth) name

let rec PrintConst cst = 
  match cst with 
  | IntConst(v)        -> sprintf "%d" v
  | BoolConst(b)       -> sprintf "%b" b
  | BoxConst(id)       -> sprintf "box_%s" id
  | VarConst(v)        -> sprintf "%s" v
  | SetConst(cset)     -> sprintf "{%s}" (PrintSep " " (fun c -> PrintConst c) (Set.toList cset))
  | SeqConst(cseq)     -> sprintf "[%s]" (PrintSep " " (fun c -> PrintConst c) cseq)
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

let rec PrintStmt stmt indent printNewline =
  let idt = (Indent indent)
  let nl = if printNewline then newline else ""
  match stmt with
  | Block(stmts) ->
      idt + "{" + nl +
      (PrintStmtList stmts (indent + 2) true) +
      idt + "}" + nl
  | Assign(lhs,rhs) -> sprintf "%s%s := %s%s" idt (PrintExpr 0 lhs) (PrintExpr 0 rhs) nl
  | ExprStmt(expr) -> sprintf "%s%s%s" idt (PrintExpr 0 expr) nl
and PrintStmtList stmts indent printNewline =
  stmts |> List.fold (fun acc s -> acc + (PrintStmt s indent printNewline)) ""

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
  | Interface(id,typeParams,members) ->
      sprintf "%s%s}%s" (PrintTopLevelDeclHeader "interface" id typeParams)
                        (List.fold (fun acc m -> acc + (PrintMember m)) "" members)
                        newline
  | DataModel(id,typeParams,vars,frame,inv) ->
      (PrintTopLevelDeclHeader "model" id typeParams) + 
      (vars |> List.fold (fun acc vd -> acc + "  var " + (PrintVarDecl vd) + newline) "") +
      "  frame" + newline +
      (frame |> List.fold (fun acc fr -> acc + "    " + (PrintExpr 0 fr) + newline) "") +
      "  invariant" + newline + 
      (inv |> ForeachConjunct (fun e -> "    " + (PrintExpr 0 e) + newline)) +
      "}" + newline
  | Code(id,typeParams) ->
      (PrintTopLevelDeclHeader "code" id typeParams) + "}" + newline

let PrintMethodSignFull indent comp m = 
  let idt = Indent indent
  let __PrintPrePost pfix expr = SplitIntoConjunts expr |> PrintSep newline (fun e -> pfix + (PrintExpr 0 e) + ";")
  let compName = GetComponentName comp
  match m with
  | Method(methodName, sgn, pre, post, isConstr) ->  
      let mc = if isConstr then "constructor" else "method"
      let preStr = (__PrintPrePost (idt + "  requires ") pre)
      let postStr = (__PrintPrePost (idt + "  ensures ") post)
      idt + mc + " " + compName + "." + methodName + (PrintSig sgn) + newline +
      preStr + (if preStr = "" then "" else newline) +
      postStr      
  | _ -> failwithf "not a method: %O" m

let Print prog =
  match prog with
  | SProgram(decls) -> List.fold (fun acc d -> acc + (PrintDecl d)) "" decls

let PrintObjRefName o = 
  match o with
  | ThisConst(_,_) -> "this";
  | NewObj(name, _) -> PrintGenSym name
  | _ -> failwith ("unresolved object ref: " + o.ToString())