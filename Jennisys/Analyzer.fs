module Analyzer

open Ast
open AstUtils
open Printer
open DafnyPrinter
open TypeChecker

let VarsAreDifferent aa bb =
  printf "false"
  List.iter2 (fun (_,Var(a,_)) (_,Var(b,_)) -> printf " || %s != %s" a b) aa bb

let Fields members =
  members |> List.choose (function Field(vd) -> Some(vd) | _ -> None)

let Methods prog = 
  match prog with
  | Program(components) ->
      components |> List.fold (fun acc comp -> 
        match comp with
        | Component(Class(_,_,members), Model(_,_,_,_,_), _) -> List.concat [acc ; members]            
        | _ -> acc) []

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

let GenerateMethodCode methodName signature pre post assumeInvInitially =
  "  method " + methodName + "()" + newline +
  "    modifies this;" + newline +
  "  {" + newline + 
  (if assumeInvInitially then "    assume Valid();" else "") +
  // print signature as local variables
  (match signature with
    | Sig(ins,outs) ->
        List.concat [ins; outs] |> List.fold (fun acc vd -> acc + (sprintf "    var %s;" (PrintVarDecl vd)) + newline) "") +
  // assume preconditions
  "    // assume precondition" + newline +
  "    assume " + (PrintExpr 0 pre) + ";" + newline + 
  // assume invariant and postcondition
  "    // assume invariant and postcondition" + newline + 
  "    assume Valid();" + newline +
  "    assume " + (PrintExpr 0 post) + ";" + newline +
  // if the following assert fails, the model hints at what code to generate; if the verification succeeds, an implementation would be infeasible
  "    // assert false to search for a model satisfying the assumed constraints" + newline + 
  "    assert false;" + newline + 
  "  }" + newline                                      

let GetFieldValidExpr (name: string) : Expr = 
  BinaryImplies (BinaryNeq (IdLiteral(name)) (IdLiteral("null"))) (Dot(IdLiteral(name), "Valid()"))

let GetFieldsForValidExpr (allFields: VarDecl list) prog : VarDecl list =
  allFields |> List.filter (function Var(name, tp) when IsUserType prog tp -> true
                                     | _                                   -> false)

let GetFieldsValidExprList (allFields: VarDecl list) prog : Expr list =
  let fields = GetFieldsForValidExpr allFields prog
  fields |> List.map (function Var(name, _) -> GetFieldValidExpr name)

let GenValidFunctionCode clsMembers modelInv vars prog : string = 
  let invMembers = clsMembers |> List.filter (function Invariant(_) -> true | _ -> false)
  let clsInvs = invMembers |> List.choose (function Invariant(exprList) -> Some(exprList) | _ -> None) |> List.concat
  let allInvs = modelInv :: clsInvs
  let fieldsValid = GetFieldsValidExprList vars prog
  let idt = "    "
  let invsStr = List.concat [fieldsValid ; allInvs] |> List.fold (fun acc (e: Expr) -> 
                                                                  if acc = "" then
                                                                    sprintf "%s%s" idt (PrintExpr 0 e)
                                                                  else
                                                                    acc + " &&" + newline + sprintf "%s%s" idt (PrintExpr 0 e)) ""
  "  function Valid(): bool" + newline +
  "    reads *;" + newline +
  "  {" + newline + 
  invsStr + newline +
  "  }" + newline

let AnalyzeMethod prog mthd : string =
  match prog with
  | Program(components) -> components |> List.fold (fun acc comp -> 
      match comp with  
      | Component(Class(name,typeParams,members), Model(_,_,cVars,frame,inv), code) ->
        let aVars = Fields members
        let allVars = List.concat [aVars ; cVars];
        // Now print it as a Dafny program
        acc + 
        (sprintf "class %s%s {" name (PrintTypeParams typeParams)) + newline +       
        // the fields: original abstract fields plus concrete fields
        (sprintf "%s" (PrintFields allVars 2)) + newline +                           
        // generate the Valid function
        (sprintf "%s" (GenValidFunctionCode members inv allVars prog)) + newline +
        // generate code for the given method
        (if List.exists (fun a -> a = mthd) members then
           match mthd with 
           | Constructor(methodName,signature,pre,post) -> (GenerateMethodCode methodName signature pre post false) + newline
           | Method(methodName,signature,pre,post)      -> (GenerateMethodCode methodName signature pre post true) + newline
           | _ -> ""
         else
           "") +
        // the end of the class
        "}" + newline + newline
      | _ -> assert false; "") ""

let scratchFileName = "scratch.dfy"

let Analyze prog =
  let methods = Methods prog

  // synthesize constructors
  methods |> List.iter (fun m -> 
    match m with
    | Constructor(methodName,signature,pre,post) -> 
        use file = System.IO.File.CreateText(scratchFileName)
        let code = AnalyzeMethod prog m
        printfn "printing code for method %s:\r\n%s" methodName code
        printfn "-------------------------"
        fprintf file "%s" code
    | _ -> ())


//let AnalyzeComponent_rustan c =
//  match c with
//  | Component(Class(name,typeParams,members), Model(_,_,cVars,frame,inv), code) ->
//      let aVars = Fields members
//      let aVars0 = Rename "0" aVars
//      let aVars1 = Rename "1" aVars
//      let allVars = List.concat [aVars; List.map (fun (a,b) -> b) aVars0; List.map (fun (a,b) -> b) aVars1; cVars]
//      let inv0 = Substitute (Map.ofList aVars0) inv
//      let inv1 = Substitute (Map.ofList aVars1) inv
//      // Now print it as a Dafny program
//      printf "class %s" name
//      match typeParams with
//        | [] -> ()
//        | _  -> printf "<%s>"  (typeParams |> PrintSep ", " (fun tp -> tp))
//      printfn " {"
//      // the fields: original abstract fields plus two more copies thereof, plus and concrete fields
//      allVars |> List.iter (function Var(nm,None) -> printfn "  var %s;" nm | Var(nm,Some(tp)) -> printfn "  var %s: %s;" nm (PrintType tp))
//      // the method
//      printfn "  method %s_checkInjective() {" name
//      printf "    assume " ; (VarsAreDifferent aVars0 aVars1) ; printfn ";"
//      printfn "    assume %s;" (PrintExpr 0 inv0)
//      printfn "    assume %s;" (PrintExpr 0 inv1)
//      printfn "    assert false;" // {:msg "Two abstract states map to the same concrete state"}
//      printfn "  }"
//      // generate code
//      members |> List.iter (function
//        | Constructor(methodName,signature,pre,stmts) -> printf "%s" (GenerateCode methodName signature pre stmts inv false)
//        | Method(methodName,signature,pre,stmts) -> printf "%s" (GenerateCode methodName signature pre stmts inv true)
//        | _ -> ())
//      // the end of the class
//      printfn "}"
//  | _ -> assert false  // unexpected case