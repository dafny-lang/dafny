module Analyzer

open Ast
open AstUtils
open CodeGen
open DafnyModelUtils
open PipelineUtils
open Printer
open DafnyPrinter

open Microsoft.Boogie
                    
let VarsAreDifferent aa bb =
  printf "false"
  List.iter2 (fun (_,Var(a,_)) (_,Var(b,_)) -> printf " || %s != %s" a b) aa bb

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

let GenMethodAnalysisCode methodName signature pre post assumeInvInitially =
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
             
let MethodAnalysisPrinter onlyForThisCompMethod comp mthd = 
  match onlyForThisCompMethod with
  | (c,m) when c = comp && m = mthd -> 
    match m with 
    | Constructor(methodName, sign, pre, post) -> (GenMethodAnalysisCode methodName sign pre post false) + newline
    | _ -> ""
  | _ -> ""
                           
let AnalyzeConstructor prog comp methodName signature pre post =
  let m = Constructor(methodName, signature, pre, post)
  use file = System.IO.File.CreateText(dafnyScratchFile)
  file.AutoFlush <- true
  let code = PrintDafnyCodeSkeleton prog (MethodAnalysisPrinter (comp,m))
  printfn "analyzing constructor %s" methodName 
  fprintf file "%s" code
  file.Close()
  RunDafny dafnyScratchFile dafnyModelFile
  use modelFile = System.IO.File.OpenText(dafnyModelFile)
        
  let models = Microsoft.Boogie.Model.ParseModels modelFile
  if models.Count = 0 then
    printfn "spec for method %s.%s is inconsistent (no valid solution exists)" (GetClassName comp) methodName
    None //failwith "inconsistent spec"      // TODO: instead of failing, just continue
  else 
    if models.Count > 1 then failwith "why did we get more than one model for a single constructor analysis???"
    let model = models.[0]
    Some(ReadFieldValuesFromModel model prog comp m)

let rec AnalyzeMethods prog methods = 
  match methods with
  | (comp,m) :: rest -> 
      match m with
      | Constructor(methodName,signature,pre,post) -> 
          let solOpt = AnalyzeConstructor prog comp methodName signature pre post
          match solOpt with
          | Some(heap,env,ctx) -> AnalyzeMethods prog rest |> Map.add (comp,m) (heap,env,ctx)
          | None -> AnalyzeMethods prog rest
      | _ -> AnalyzeMethods prog rest
  | [] -> Map.empty

let Analyze prog =
  let solutions = AnalyzeMethods prog (Methods prog)
  use file = System.IO.File.CreateText(dafnySynthFile)
  file.AutoFlush <- true
  let synthCode = PrintImplCode prog solutions
  fprintfn file "%s" synthCode
  ()

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