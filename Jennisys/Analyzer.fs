module Analyzer

open Ast
open Printer

let rec PrintType ty =
  match ty with
  | NamedType(id) -> printf "%s" id
  | InstantiatedType(id,arg) -> printf "%s<" id ; PrintType arg ; printf ">"

let rec PrintExpr ctx expr =
  match expr with
  | IntLiteral(n) -> printf "%O" n
  | IdLiteral(id) -> printf "%s" id
  | Star -> assert false // I hope this won't happen
  | Dot(e,id) -> PrintExpr 100 e ; printf ".%s" id
  | UnaryExpr(op,e) -> printf "%s" op ; PrintExpr 90 e
  | BinaryExpr(strength,op,e0,e1) ->
      let op =
        match op with
          | "=" -> "=="
          | "div" -> "/"
          | "mod" -> "%"
          | _ -> op
      let needParens = strength <= ctx
      if needParens then printf "(" else ()
      PrintExpr strength e0 ; printf " %s " op ; PrintExpr strength e1
      if needParens then printf ")" else ()
  | SelectExpr(e,i) -> PrintExpr 100 e ; printf "[" ; PrintExpr 0 i ; printf "]"
  | UpdateExpr(e,i,v) -> PrintExpr 100 e ; printf "[" ; PrintExpr 0 i ; printf " := " ; PrintExpr 0 v ; printf "]"
  | SequenceExpr(ee) -> printf "[" ; ee |> PrintSep ", " (PrintExpr 0) ; printf "]"
  | SeqLength(e) -> printf "|" ; PrintExpr 0 e ; printf "|"
  | ForallExpr(vv,e) ->
      let needParens = true
      if needParens then printf "(" else ()
      printf "forall " ; vv |> PrintSep ", " PrintVarDecl ; printf " :: " ; PrintExpr 0 e
      if needParens then printf ")" else ()

let VarsAreDifferent aa bb =
  printf "false"
  List.iter2 (fun (_,Var(a,_)) (_,Var(b,_)) -> printf " || %s != %s" a b) aa bb

let Fields members =
  members |> List.choose (function Field(vd) -> Some(vd) | _ -> None)

let Rename suffix vars =
  vars |> List.map (function Var(nm,tp) -> nm, Var(nm + suffix, tp))

let ReplaceName substMap nm =
  match Map.tryFind nm substMap with
    | Some(Var(name, tp)) -> name
    | None -> nm

let rec Substitute substMap = function
  | IdLiteral(s) -> IdLiteral(ReplaceName substMap s)
  | Dot(e,f) -> Dot(Substitute substMap e, ReplaceName substMap f)
  | UnaryExpr(op,e) -> UnaryExpr(op, Substitute substMap e)
  | BinaryExpr(n,op,e0,e1) -> BinaryExpr(n, op, Substitute substMap e0, Substitute substMap e1)
  | SelectExpr(e0,e1) -> SelectExpr(Substitute substMap e0, Substitute substMap e1)
  | UpdateExpr(e0,e1,e2) -> UpdateExpr(Substitute substMap e0, Substitute substMap e1, Substitute substMap e2)
  | SequenceExpr(ee) -> SequenceExpr(List.map (Substitute substMap) ee)
  | SeqLength(e) -> SeqLength(Substitute substMap e)
  | ForallExpr(vv,e) -> ForallExpr(vv, Substitute substMap e)
  | expr -> expr

let rec PrintStmt stmt indent =
  match stmt with
  | Block(stmts) ->
      Indent indent ; printfn "{"
      PrintStmtList stmts (indent + 2)
      Indent indent ; printfn "}"
  | Assign(lhs,rhs) -> Indent indent ; PrintExpr 0 lhs ; printf " := " ; PrintExpr 0 rhs ; printfn ";"
and PrintStmtList stmts indent =
  stmts |> List.iter (fun s -> PrintStmt s indent)

let GenerateCode methodName signature pre stmts inv assumeInvInitially =
  printfn "  method %s()" methodName
  printfn "    modifies this;"
  printfn "  {"
  if assumeInvInitially then
    // assume invariant
    printf "    assume " ; PrintExpr 0 inv ; printfn ";"
  else ()
  // print signature as local variables
  match signature with
    | Sig(ins,outs) ->
        List.concat [ins; outs] |> List.iter (fun vd -> printf "    var " ; PrintVarDecl vd ; printfn ";")
  // assume preconditions
  printf "    assume " ; PrintExpr 0 pre ; printfn ";"
  // do statements
  stmts |> List.iter (fun s -> PrintStmt s 4)
  // assume invariant
  printf "    assume " ; PrintExpr 0 inv ; printfn ";"
  // if the following assert fails, the model hints at what code to generate; if the verification succeeds, an implementation would be infeasible
  printfn "    assert false;"
  printfn "}"

let AnalyzeComponent c =
  match c with
  | Component(Class(name,typeParams,members), Model(_,_,cVars,frame,inv), code) ->
      let aVars = Fields members
      let aVars0 = Rename "0" aVars
      let aVars1 = Rename "1" aVars
      let allVars = List.concat [aVars; List.map (fun (a,b) -> b) aVars0; List.map (fun (a,b) -> b) aVars1; cVars]
      let inv0 = Substitute (Map.ofList aVars0) inv
      let inv1 = Substitute (Map.ofList aVars1) inv
      // Now print it as a Dafny program
      printf "class %s" name
      match typeParams with
        | [] -> ()
        | _ -> printf "<" ; typeParams |> PrintSep ", " (fun tp -> printf "%s" tp) ; printf ">"
      printfn " {"
      // the fields: original abstract fields plus two more copies thereof, plus and concrete fields
      allVars |> List.iter (function Var(nm,None) -> printfn "  var %s;" nm | Var(nm,Some(tp)) -> printf "  var %s: " nm ; PrintType tp ; printfn ";")
      // the method
      printfn "  method %s_checkInjective() {" name
      printf "    assume " ; VarsAreDifferent aVars0 aVars1 ; printfn ";"
      printf "    assume " ; PrintExpr 0 inv0 ; printfn ";"
      printf "    assume " ; PrintExpr 0 inv1 ; printfn ";"
      printfn "    assert false;" // {:msg "Two abstract states map to the same concrete state"}
      printfn "  }"
      // generate code
      members |> List.iter (function
        | Constructor(methodName,signature,pre,stmts) -> GenerateCode methodName signature pre stmts inv false
        | Method(methodName,signature,pre,stmts) -> GenerateCode methodName signature pre stmts inv true
        | _ -> ())
      // the end of the class
      printfn "}"
  | _ -> assert false  // unexpected case

let Analyze prog =
  match prog with
  | Program(components) ->
      components |> List.iter AnalyzeComponent
