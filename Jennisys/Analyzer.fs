module Analyzer

open Ast
open AstUtils
open CodeGen
open DafnyModelUtils
open PipelineUtils
open Options
open Printer
open Resolver
open DafnyPrinter
open Utils

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

let GenMethodAnalysisCode comp m assertion =
  let methodName = GetMethodName m
  let signature = GetMethodSig m 
  let ppre,ppost = GetMethodPrePost m 
  let pre = Desugar ppre
  let post = Desugar ppost
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
  "    assert " + (PrintExpr 0 assertion) + ";" + newline + 
  "  }" + newline
             
let MethodAnalysisPrinter onlyForThisCompMethod assertion comp mthd = 
  match onlyForThisCompMethod with
  | (c,m) when c = comp && m = mthd -> 
    match m with 
    | Method(methodName, sign, pre, post, true) -> (GenMethodAnalysisCode comp m assertion) + newline
    | _ -> ""
  | _ -> ""

let rec IsArgsOnly args expr = 
  match expr with
  | IdLiteral(id) -> args |> List.exists (function Var(varName,_) when varName = id -> true | _ -> false)
  | UnaryExpr(_,e) -> IsArgsOnly args e
  | BinaryExpr(_,_,e1,e2) -> (IsArgsOnly args e1) && (IsArgsOnly args e2)
  | Dot(e,_) -> IsArgsOnly args e
  | SelectExpr(e1, e2) -> (IsArgsOnly args e1) && (IsArgsOnly args e2)
  | UpdateExpr(e1, e2, e3) -> (IsArgsOnly args e1) && (IsArgsOnly args e2) && (IsArgsOnly args e3)
  | SequenceExpr(exprs) -> exprs |> List.fold (fun acc e -> acc && (IsArgsOnly args e)) true
  | SeqLength(e) -> IsArgsOnly args e
  | ForallExpr(vars,e) -> IsArgsOnly (List.concat [args; vars]) e
  | IntLiteral(_) -> true
  | Star -> true

let rec GetUnifications expr args (heap,env,ctx) = 
  match expr with
  | IntLiteral(_)
  | IdLiteral(_)
  | Star         
  | Dot(_)
  | SelectExpr(_)   // TODO: handle select expr
  | UpdateExpr(_)   // TODO: handle update expr
  | SequenceExpr(_) 
  | SeqLength(_)    
  | ForallExpr(_)   // TODO: handle forall expr
  | UnaryExpr(_)   -> Set.empty
  | BinaryExpr(strength,op,e0,e1) ->
      if op = "=" then
        let v0 = Eval e0 (heap,env,ctx)
        let v1 = Eval e1 (heap,env,ctx)
        let argsOnly0 = IsArgsOnly args e0
        let argsOnly1 = IsArgsOnly args e1
        match v0,argsOnly1,argsOnly0,v1 with
        | Some(c0),true,_,_ -> 
               Logger.DebugLine ("      - adding unification " + (PrintConst c0) + " <--> " + (PrintExpr 0 e1));
               Set.ofList [c0, e1]
        | _,_,true,Some(c1) -> 
               Logger.DebugLine ("      - adding unification " + (PrintConst c1) + " <--> " + (PrintExpr 0 e0));
               Set.ofList [c1, e0]
        | _ -> Logger.TraceLine ("      - couldn't unify anything from " + (PrintExpr 0 expr));
               Set.empty
      else 
        GetUnifications e0 args (heap,env,ctx) |> Set.union (GetUnifications e1 args (heap,env,ctx))

let rec GetArgValueUnifications args env = 
  match args with
  | Var(name,_) :: rest -> 
      match Map.tryFind (VarConst(name)) env with
      | Some(c) ->
          Logger.DebugLine ("      - adding unification " + (PrintConst c) + " <--> " + name);
          Set.ofList [c, IdLiteral(name)] |> Set.union (GetArgValueUnifications rest env)
      | None -> failwith ("couldn't find value for argument " + name)
  | [] -> Set.empty

let rec _GetObjRefExpr o (heap,env,ctx) visited = 
  if Set.contains o visited then 
    None
  else 
    let newVisited = Set.add o visited
    let refName = PrintObjRefName o (env,ctx)
    match refName with
    | Exact "this" _ -> Some(IdLiteral(refName))
    | _ -> 
        let rec __fff lst = 
          match lst with
          | ((o,Var(fldName,_)),l) :: rest -> 
              match _GetObjRefExpr o (heap,env,ctx) newVisited with
              | Some(expr) -> Some(Dot(expr, fldName))
              | None -> __fff rest
          | [] -> None
        let backPointers = heap |> Map.filter (fun (_,_) l -> l = o) |> Map.toList
        __fff backPointers      

let GetObjRefExpr o (heap,env,ctx) = 
  _GetObjRefExpr o (heap,env,ctx) (Set.empty)

let rec UpdateHeapEnv prog comp mthd unifs (heap,env,ctx) = 
  let __CheckUnif o f e idx =
    let objRefExpr = GetObjRefExpr o (heap,env,ctx) |> Utils.ExtractOptionMsg ("Couldn't find a path from this to " + (PrintObjRefName o (env,ctx)))
    let fldName = PrintVarName f                             
    let lhs = Dot(objRefExpr, fldName) |> Utils.IfDo1 (not (idx = -1)) (fun e -> SelectExpr(e, IntLiteral(idx)))
    let assertionExpr = BinaryEq lhs e 
    // check if the assertion follows and if so update the env
    let code = PrintDafnyCodeSkeleton prog (MethodAnalysisPrinter (comp,mthd) assertionExpr)
    Logger.Debug("        - checking assertion: " + (PrintExpr 0 assertionExpr) + " ... ")
    CheckDafnyProgram code ("unif_" + (GetMethodFullName comp mthd))

  match unifs with
  | (c,e) :: rest -> 
      let restHeap,env,ctx = UpdateHeapEnv prog comp mthd rest (heap,env,ctx)
      let newHeap = restHeap |> Map.fold (fun acc (o,f) l ->
                                            let value = TryResolve l (env,ctx)
                                            if value = c then
                                              if __CheckUnif o f e -1 then
                                                Logger.DebugLine " HOLDS"
                                                // change the value to expression
                                                acc |> Map.add (o,f) (ExprConst(e))
                                              else
                                                Logger.DebugLine " DOESN'T HOLDS"
                                                // don't change the value
                                                acc |> Map.add (o,f) l
                                            else 
                                              // see if it's a list, then try to match its elements, otherwise leave it as is
                                              match value with
                                              | SeqConst(clist) -> 
                                                  let rec __UnifyOverLst lst cnt =
                                                    match lst with
                                                    | lstElem :: rest when lstElem = c ->
                                                        if __CheckUnif o f e cnt then
                                                          Logger.DebugLine " HOLDS"
                                                          ExprConst(e) :: __UnifyOverLst rest (cnt+1)
                                                        else 
                                                          Logger.DebugLine " DOESN'T HOLDS"
                                                          lstElem :: __UnifyOverLst rest (cnt+1)
                                                    | lstElem :: rest ->
                                                        lstElem :: __UnifyOverLst rest (cnt+1)
                                                    | [] -> []
                                                  let newLstConst = __UnifyOverLst clist 0
                                                  acc |> Map.add (o,f) (SeqConst(newLstConst))
                                              | _ -> 
                                                  acc |> Map.add (o,f) l
                                         ) restHeap
      (newHeap,env,ctx)
  | [] -> (heap,env,ctx)

let GeneralizeSolution prog comp mthd (heap,env,ctx) =
  match mthd with
  | Method(mName,Sig(ins, outs),pre,post,_) -> 
      let args = List.concat [ins; outs]
      match args with 
      | [] -> (heap,env,ctx)
      | _  -> 
          let unifs = GetUnifications (BinaryAnd pre post |> Desugar) args (heap,env,ctx)    //TODO: we shouldn't use desugar here, but in UpdateHeapEnv
                    |> Set.union (GetArgValueUnifications args env)
          UpdateHeapEnv prog comp mthd (Set.toList unifs) (heap,env,ctx)
  | _ -> failwith ("not a method: " + mthd.ToString())

//  ====================================================================================
/// Returns whether the code synthesized for the given method can be verified with Dafny
//  ====================================================================================
let VerifySolution prog comp mthd (heap,env,ctx) =
  // print the solution to file and try to verify it with Dafny
  let solution = Map.empty |> Map.add (comp,mthd) (heap,env,ctx)
  let code = PrintImplCode prog solution (fun p -> [comp,mthd])
  CheckDafnyProgram code dafnyVerifySuffix
   
//  ============================================================================
/// Attempts to synthesize the initialization code for the given constructor "m"
///
/// Returns a (heap,env,ctx) tuple
//  ============================================================================                           
let AnalyzeConstructor prog comp m =
  let methodName = GetMethodName m
  // generate Dafny code for analysis first
  let code = PrintDafnyCodeSkeleton prog (MethodAnalysisPrinter (comp,m) FalseLiteral)
  Logger.InfoLine ("  [*] analyzing constructor " + methodName + (PrintSig (GetMethodSig m)))
  Logger.Info      "      - searching for a solution       ..."
  let models = RunDafnyProgram code (dafnyScratchSuffix + "_" + (GetMethodFullName comp m))  
  if models.Count = 0 then
    // no models means that the "assert false" was verified, which means that the spec is inconsistent
    Logger.WarnLine " !!! SPEC IS INCONSISTENT !!!"
    None
  else 
    if models.Count > 1 then 
      Logger.WarnLine " FAILED "
      failwith "internal error (more than one model for a single constructor analysis)"
    Logger.InfoLine " OK "
    let model = models.[0]
    let heap,env,ctx = ReadFieldValuesFromModel model prog comp m
                       |> GeneralizeSolution prog comp m
    if _opt_verifySolutions then
      Logger.InfoLine "      - verifying synthesized solution ... "
      let verified = VerifySolution prog comp m (heap,env,ctx)
      Logger.Info "      "      
      if verified then
        Logger.InfoLine "~~~ VERIFIED ~~~"
        Some(heap,env,ctx)
      else 
        Logger.InfoLine "!!! NOT VERIFIED !!!"
        Some(heap,env,ctx)
    else
      Some(heap,env,ctx)
  

// ============================================================================
/// Goes through a given list of methods of the given program and attempts to 
/// synthesize code for each one of them.
///
/// Returns a map from (component * method) |--> (heap,env,ctx)
// ============================================================================
let rec AnalyzeMethods prog members = 
  match members with
  | (comp,m) :: rest -> 
      match m with
      | Method(_,_,_,_,true) -> 
          let solOpt = AnalyzeConstructor prog comp m
          Logger.InfoLine ""
          match solOpt with
          | Some(heap,env,ctx) -> AnalyzeMethods prog rest |> Map.add (comp,m) (heap,env,ctx)
          | None -> AnalyzeMethods prog rest
      | _ -> AnalyzeMethods prog rest
  | [] -> Map.empty

let Analyze prog filename =
  let solutions = AnalyzeMethods prog (GetMethodsToAnalyze prog)
  let progName = System.IO.Path.GetFileNameWithoutExtension(filename)
  use file = System.IO.File.CreateText(dafnySynthFileNameTemplate.Replace("###", progName))
  file.AutoFlush <- true
  Logger.InfoLine "Printing synthesized code"
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