module Analyzer

open Ast
open AstUtils
open CodeGen
open DafnyModelUtils
open PipelineUtils
open Options
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

let GenMethodAnalysisCode comp methodName signature pre post =
  "  method " + methodName + "()" + newline +
  "    modifies this;" + newline +
  "  {" + newline + 
  // print signature as local variables
  (match signature with
    | Sig(ins,outs) ->
        List.concat [ins; outs] |> List.fold (fun acc vd -> acc + (sprintf "    var %s;" (PrintVarDecl vd)) + newline) "") +
  "    // assume precondition" + newline +
  "    assume " + (PrintExpr 0 pre) + ";" + newline + 
  "    // assume invariant and postcondition" + newline + 
  "    assume Valid();" + newline +
  "    assume " + (PrintExpr 0 post) + ";" + newline +
  "    // assume user defined invariant again because assuming Valid() doesn't always work" + newline +
  (GetInvariantsAsList comp |> PrintSep newline (fun e -> "    assume " + (PrintExpr 0 e) + ";")) + newline +
  // if the following assert fails, the model hints at what code to generate; if the verification succeeds, an implementation would be infeasible
  "    // assert false to search for a model satisfying the assumed constraints" + newline + 
  "    assert false;" + newline + 
  "  }" + newline
             
let MethodAnalysisPrinter onlyForThisCompMethod comp mthd = 
  match onlyForThisCompMethod with
  | (c,m) when c = comp && m = mthd -> 
    match m with 
    | Method(methodName, sign, pre, post, true) -> (GenMethodAnalysisCode comp methodName sign pre post) + newline
    | _ -> ""
  | _ -> ""

/// Returns whether the code synthesized for the given method can be verified with Dafny
let VerifySolution (heap,env,ctx) prog comp mthd =
  // print the solution to file and try to verify it with Dafny
  let solution = Map.empty |> Map.add (comp,mthd) (heap,env,ctx)
  let code = PrintImplCode prog solution (fun p -> [comp,mthd])
  use file = System.IO.File.CreateText(dafnyVerifyFile)
  file.AutoFlush <- true  
  fprintfn file "%s" code
  file.Close()
  // run Dafny
  RunDafny dafnyVerifyFile dafnyVerifyModelFile
  // read models from the model file
  use modelFile = System.IO.File.OpenText(dafnyVerifyModelFile)
  let models = Microsoft.Boogie.Model.ParseModels modelFile
  // if there are no models, verification was successful
  models.Count = 0
                           
let AnalyzeConstructor prog comp m =
  let methodName = GetMethodName m
  // generate Dafny code for analysis first
  let code = PrintDafnyCodeSkeleton prog (MethodAnalysisPrinter (comp,m))
  printfn "  [*] analyzing constructor %s" methodName 
  printf  "       - searching for a solution       ..."
  use file = System.IO.File.CreateText(dafnyScratchFile)
  file.AutoFlush <- true
  fprintf file "%s" code
  file.Close()
  // run Dafny
  RunDafny dafnyScratchFile dafnyModelFile
  // read models
  use modelFile = System.IO.File.OpenText(dafnyModelFile)        
  let models = Microsoft.Boogie.Model.ParseModels modelFile
  if models.Count = 0 then
    // no models means that the "assert false" was verified, which means that the spec is inconsistent
    printfn " !!! SPEC IS INCONSISTENT !!!"
    None
  else 
    if models.Count > 1 then 
      printfn " FAILED "
      failwith "internal error (more than one model for a single constructor analysis)"
    printfn " OK "
    let model = models.[0]
    let heap,env,ctx = ReadFieldValuesFromModel model prog comp m
    if _opt_verifySolutions then
      printf "       - verifying synthesized solution ..."
      if VerifySolution (heap,env,ctx) prog comp m then
        printfn " OK"
        Some(heap,env,ctx)
      else 
        printfn " NOT VERIFIED"
        Some(heap,env,ctx)
    else
      Some(heap,env,ctx)

let rec AnalyzeMethods prog members = 
  match members with
  | (comp,m) :: rest -> 
      match m with
      | Method(_,_,_,_,true) -> 
          let solOpt = AnalyzeConstructor prog comp m
          match solOpt with
          | Some(heap,env,ctx) -> AnalyzeMethods prog rest |> Map.add (comp,m) (heap,env,ctx)
          | None -> AnalyzeMethods prog rest
      | _ -> AnalyzeMethods prog rest
  | [] -> Map.empty

let Analyze prog =
  let solutions = AnalyzeMethods prog (GetMethodsToAnalyze prog)
  use file = System.IO.File.CreateText(dafnySynthFile)
  file.AutoFlush <- true
  printfn "Printing synthesized code"
  let synthCode = PrintImplCode prog solutions GetMethodsToAnalyze
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