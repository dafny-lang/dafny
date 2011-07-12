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
  | IntLiteral(_)                        -> true
  | BoolLiteral(_)                       -> true
  | Star                                 -> true
  | IdLiteral(id)                        -> args |> List.exists (function Var(varName,_) when varName = id -> true | _ -> false)
  | UnaryExpr(_,e)                       -> IsArgsOnly args e
  | BinaryExpr(_,_,e1,e2)                -> (IsArgsOnly args e1) && (IsArgsOnly args e2)
  | IteExpr(c,e1,e2)                     -> (IsArgsOnly args c) && (IsArgsOnly args e1) && (IsArgsOnly args e2)
  | Dot(e,_)                             -> IsArgsOnly args e
  | SelectExpr(e1, e2)                   -> (IsArgsOnly args e1) && (IsArgsOnly args e2)
  | UpdateExpr(e1, e2, e3)               -> (IsArgsOnly args e1) && (IsArgsOnly args e2) && (IsArgsOnly args e3)
  | SequenceExpr(exprs) | SetExpr(exprs) -> exprs |> List.fold (fun acc e -> acc && (IsArgsOnly args e)) true
  | SeqLength(e)                         -> IsArgsOnly args e
  | ForallExpr(vars,e)                   -> IsArgsOnly (List.concat [args; vars]) e

let GetUnifications expr args (heap,env,ctx) =
  // - first looks if the give expression talks only about method arguments (args)
  // - then checks if it doesn't already exist in the unification map
  // - then it tries to evaluate it to a constant
  // - if all of these succeed, it adds a unification rule e <--> val(e) to the given unifMap map
  let __AddUnif e unifMap =
    let builder = new CascadingBuilder<_>(unifMap)
    builder {
      let! argsOnly = IsArgsOnly args e |> Utils.BoolToOption
      let! notAlreadyAdded = Map.tryFind e unifMap |> Utils.IsNoneOption |> Utils.BoolToOption
      let! v = Eval (heap,env,ctx) e                       
      Logger.DebugLine ("      - adding unification " + (PrintExpr 0 e) + " <--> " + (PrintConst v));
      return Map.add e v unifMap
    }
  // just recurses on all expressions
  let rec __GetUnifications expr args unifs = 
    let unifs = __AddUnif expr unifs
    match expr with
    | IntLiteral(_)
    | BoolLiteral(_)
    | IdLiteral(_)
    | Star                   -> unifs
    | Dot(e, _)
    | SeqLength(e)
    | ForallExpr(_,e)  
    | UnaryExpr(_,e)         -> unifs |> __GetUnifications e args
    | SelectExpr(e1, e2)      
    | BinaryExpr(_,_,e1,e2)  -> unifs |> __GetUnifications e1 args |> __GetUnifications e2 args
    | IteExpr(e1,e2,e3)
    | UpdateExpr(e1, e2, e3) -> unifs |> __GetUnifications e1 args |> __GetUnifications e2 args |> __GetUnifications e3 args
    | SetExpr(elst)
    | SequenceExpr(elst)     -> elst |> List.fold (fun acc e -> acc |> __GetUnifications e args) unifs 
  (* --- function body starts here --- *)
  __GetUnifications expr args Map.empty

//  =======================================================
/// Returns a map (Expr |--> Const) containing unifications
/// found for the given method and heap/env/ctx
//  =======================================================
let GetUnificationsForMethod comp m (heap,env,ctx) =
  let rec GetArgValueUnifications args env = 
    match args with
    | Var(name,_) :: rest -> 
        match Map.tryFind (Unresolved(name)) env with
        | Some(c) ->
            Logger.DebugLine ("      - adding unification " + (PrintConst c) + " <--> " + name);
            Map.ofList [IdLiteral(name), c] |> Utils.MapAddAll (GetArgValueUnifications rest env)
        | None -> failwith ("couldn't find value for argument " + name)
    | [] -> Map.empty
  (* --- function body starts here --- *)
  match m with
  | Method(mName,Sig(ins, outs),pre,post,_) -> 
      let args = List.concat [ins; outs]
      match args with 
      | [] -> Map.empty
      | _  -> GetUnifications (BinaryAnd pre post) args (heap,env,ctx)
              |> Utils.MapAddAll (GetArgValueUnifications args env)
  | _ -> failwith ("not a method: " + m.ToString())

//  =========================================================================
/// For a given constant "o" (which is an object, something like "gensym32"), 
/// finds a path of field references from "this". 
///
/// Implements a backtracking search over the heap entries to find that
/// path.  It starts from the given object, and follows the backpointers
/// until it reaches the root ("this")
//  ========================================================================= 
let objRef2ExprCache = new System.Collections.Generic.Dictionary<Const, Expr>()
let GetObjRefExpr o (heap,env,ctx) = 
  let rec __GetObjRefExpr o (heap,env,ctx) visited = 
    if Set.contains o visited then 
      None
    else 
      let newVisited = Set.add o visited
      let refName = PrintObjRefName o (env,ctx)
      match refName with
      | "this" -> Some(IdLiteral(refName))
      | _ -> 
          let rec __fff lst = 
            match lst with
            | ((o,Var(fldName,_)),l) :: rest -> 
                match __GetObjRefExpr o (heap,env,ctx) newVisited with
                | Some(expr) -> Some(Dot(expr, fldName))
                | None -> __fff rest
            | [] -> None
          let backPointers = heap |> Map.filter (fun (_,_) l -> l = o) |> Map.toList
          __fff backPointers 
  (* --- function body starts here --- *)
  if objRef2ExprCache.ContainsKey(o) then
    Some(objRef2ExprCache.[o])
  else
      let res = __GetObjRefExpr o (heap,env,ctx) (Set.empty)
      match res with 
      | Some(e) -> objRef2ExprCache.Add(o, e)
      | None -> ()
      res

//  =======================================================
/// Applies given unifications onto the given heap/env/ctx
/// 
/// If "conservative" is true, applies only those that 
/// can be verified to hold, otherwise applies all of them
//  =======================================================
let rec ApplyUnifications prog comp mthd unifs (heap,env,ctx) conservative = 
  let __CheckUnif o f e idx =
    if not conservative then 
      true 
    else
      let objRefExpr = GetObjRefExpr o (heap,env,ctx) |> Utils.ExtractOptionMsg ("Couldn't find a path from 'this' to " + (PrintObjRefName o (env,ctx)))
      let fldName = PrintVarName f                             
      let lhs = Dot(objRefExpr, fldName)
      let assertionExpr = match f with
                          | Var(_, Some(SeqType(_))) when not (idx = -1) -> BinaryEq (SelectExpr(lhs, IntLiteral(idx))) e
                          | Var(_, Some(SetType(_))) when not (idx = -1) -> BinaryIn e lhs
                          | _                                            -> BinaryEq lhs e 
      // check if the assertion follows and if so update the env
      let code = PrintDafnyCodeSkeleton prog (MethodAnalysisPrinter (comp,mthd) assertionExpr)
      Logger.Debug ("      - checking assertion: " + (PrintExpr 0 assertionExpr) + " ... ")
      let ok = CheckDafnyProgram code ("unif_" + (GetMethodFullName comp mthd))
      if ok then
        Logger.DebugLine " HOLDS"
      else
        Logger.DebugLine " DOESN'T HOLD"
      ok
  (* --- function body starts here --- *)
  match unifs with
  | (e,c) :: rest -> 
      let restHeap,env,ctx = ApplyUnifications prog comp mthd rest (heap,env,ctx) conservative
      let newHeap = restHeap |> Map.fold (fun acc (o,f) l ->
                                            let value = TryResolve (env,ctx) l
                                            if value = c then
                                              if __CheckUnif o f e -1 then                                                
                                                // change the value to expression
                                                Logger.TraceLine (sprintf "      - applied: %s.%s --> %s" (PrintConst o) (GetVarName f) (PrintExpr 0 e) )
                                                acc |> Map.add (o,f) (ExprConst(e))
                                              else
                                                // don't change the value unless "conservative = false"
                                                acc |> Map.add (o,f) l
                                            else 
                                              let rec __UnifyOverLst lst cnt =
                                                    match lst with
                                                    | lstElem :: rest when lstElem = c ->
                                                        if __CheckUnif o f e cnt then
                                                          Logger.TraceLine (sprintf "      - applied: %s.%s[%d] --> %s" (PrintConst o) (GetVarName f) cnt (PrintExpr 0 e) )
                                                          ExprConst(e) :: __UnifyOverLst rest (cnt+1)
                                                        else  
                                                          lstElem :: __UnifyOverLst rest (cnt+1)
                                                    | lstElem :: rest ->
                                                        lstElem :: __UnifyOverLst rest (cnt+1)
                                                    | [] -> []
                                              // see if it's a list, then try to match its elements, otherwise leave it as is
                                              match value with
                                              | SeqConst(clist) -> 
                                                  let newLstConst = __UnifyOverLst clist 0
                                                  acc |> Map.add (o,f) (SeqConst(newLstConst))
                                              | SetConst(cset) ->
                                                  let newLstConst = __UnifyOverLst (Set.toList cset) 0
                                                  acc |> Map.add (o,f) (SetConst(newLstConst |> Set.ofList))
                                              | _ -> 
                                                  acc |> Map.add (o,f) l
                                         ) restHeap
      (newHeap,env,ctx)
  | [] -> (heap,env,ctx)

//  ====================================================================================
/// Returns whether the code synthesized for the given method can be verified with Dafny
//  ====================================================================================
let VerifySolution prog comp mthd (heap,env,ctx) =
  // print the solution to file and try to verify it with Dafny
  let solution = Map.empty |> Map.add (comp,mthd) (heap,env,ctx)
  let code = PrintImplCode prog solution (fun p -> [comp,mthd])
  CheckDafnyProgram code dafnyVerifySuffix

let TryInferConditionals prog comp m unifs (heap,env,ctx) = 
  let heap2,env2,ctx2 = ApplyUnifications prog comp m unifs (heap,env,ctx) false
  // get expressions to evaluate:
  //   - go through all objects on the heap and assert its invariant
  //   - add pre and post conditions

  Some(heap2,env2,ctx2)
   
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
  Logger.Info      "      - searching for an instance      ..."
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
    let unifs = GetUnificationsForMethod comp m (heap,env,ctx) |> Map.toList
    let heap,env,ctx = ApplyUnifications prog comp m unifs (heap,env,ctx) true
    if Options.CONFIG.verifySolutions then
      Logger.InfoLine "      - verifying synthesized solution ... "
      let verified = VerifySolution prog comp m (heap,env,ctx)
      Logger.Info "      "      
      if verified then
        Logger.InfoLine "~~~ VERIFIED ~~~"
        Some(heap,env,ctx)
      else 
        Logger.InfoLine "!!! NOT VERIFIED !!!"
        Logger.InfoLine "Trying to infer conditionals"
        TryInferConditionals prog comp m unifs (heap,env,ctx)
    else
      Some(heap,env,ctx)

let GetMethodsToAnalyze prog =
  let mOpt = Options.CONFIG.methodToSynth;
  if mOpt = "*" then
    (* all *)
    FilterMembers prog FilterConstructorMembers   
  elif mOpt = "paramsOnly" then
    (* only with parameters *)
    FilterMembers prog FilterConstructorMembersWithParams 
  else
    let allMethods,neg = 
      if mOpt.StartsWith("~") then
        mOpt.Substring(1), true
      else
        mOpt, false
    (* exactly one *)
    let methods = allMethods.Split([|','|])
    let lst = methods |> Array.fold (fun acc m -> 
                                       let compName = m.Substring(0, m.LastIndexOf("."))
                                       let methName = m.Substring(m.LastIndexOf(".") + 1)
                                       let c = FindComponent prog compName |> Utils.ExtractOptionMsg ("Cannot find component " + compName)
                                       let mthd = FindMethod c methName |> Utils.ExtractOptionMsg ("Cannot find method " + methName + " in component " + compName)
                                       (c,mthd) :: acc
                                    ) []
    if neg then
      FilterMembers prog FilterConstructorMembers |> List.filter (fun e -> not (Utils.ListContains e lst))
    else
      lst
  

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