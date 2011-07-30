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

let MergeSolutions sol1 sol2 = 
  let rec __Merge sol1map sol2lst res =
    match sol2lst with
    | ((c2,m2), lst2) :: rest -> 
        match sol1map |> Map.tryFindKey (fun (c1,m1) lst1 -> GetComponentName c1 = GetComponentName c2 && GetMethodName m1 = GetMethodName m2) with
        | Some(c1,m1) -> 
            let lst1 = sol1map |> Map.find(c1,m1)
            let newRes = res |> Map.add (c1,m1) (lst1 @ lst2)
            __Merge sol1map rest newRes
        | None -> 
            let newRes = res |> Map.add (c2,m2) lst2
            __Merge sol1map rest newRes
    | [] -> res
  (* --- function body starts here --- *)
  __Merge sol1 (sol2 |> Map.toList) sol1 
                   
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
             
let rec MethodAnalysisPrinter onlyForThese assertion comp = 
  let cname = GetComponentName comp
  match onlyForThese with
  | (c,m) :: rest when GetComponentName c = cname -> 
    match m with 
    | Method(methodName, sign, pre, post, true) -> 
        (GenMethodAnalysisCode c m assertion) + newline +
        (MethodAnalysisPrinter rest assertion comp)
    | _ -> ""
  | _ :: rest -> MethodAnalysisPrinter rest assertion comp
  | [] -> ""

let rec IsArgsOnly args expr = 
  match expr with                                                
  | IntLiteral(_)                        -> true
  | BoolLiteral(_)                       -> true
  | Star                                 -> true
  | ObjLiteral(id)                       -> true
  | VarLiteral(id)
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
  | MethodCall(rcv,_,aparams)            -> rcv :: aparams |> List.fold (fun acc e -> acc && (IsArgsOnly args e)) true

let AddUnif indent e v unifMap =
  let idt = Indent indent
  let builder = new CascadingBuilder<_>(unifMap)
  builder {
    let! notAlreadyAdded = Map.tryFind e unifMap |> Utils.IsNoneOption |> Utils.BoolToOption
    Logger.DebugLine (idt + "    - adding unification " + (PrintExpr 0 e) + " <--> " + (PrintConst v))
    return Map.add e v unifMap
  }

//TODO: unifications should probably by "Expr <--> Expr" instead of "Expr <--> Const"
let rec GetUnifications indent args heapInst unifs expr =
  let idt = Indent indent
  // - first looks if the give expression talks only about method arguments (args)
  // - then checks if it doesn't already exist in the unification map
  // - then it tries to evaluate it to a constant
  // - if all of these succeed, it adds a unification rule e <--> val(e) to the given unifMap map
  let __AddUnif e unifsAcc =
    let builder = new CascadingBuilder<_>(unifsAcc)
    builder {
      let! argsOnly = IsArgsOnly args e |> Utils.BoolToOption
      let! v = try Some(Eval heapInst (fun _ -> true) e |> Expr2Const) with ex -> None
      return AddUnif indent e v unifsAcc
    }
  (* --- function body starts here --- *)
  AstUtils.DescendExpr2 __AddUnif expr unifs

//  =======================================================
/// Returns a map (Expr |--> Const) containing unifications
/// found for the given method and heap/env/ctx
//  =======================================================
let GetUnificationsForMethod indent comp m heapInst =
  let idt = Indent indent
  let rec GetArgValueUnifications args = 
    match args with
    | Var(name,_) :: rest -> 
        match Map.tryFind name heapInst.methodArgs with
        | Some(c) ->
            GetArgValueUnifications rest |> AddUnif indent (VarLiteral(name)) c
        | None -> failwith ("couldn't find value for argument " + name)
    | [] -> Map.empty
  (* --- function body starts here --- *)
  match m with
  | Method(mName,Sig(ins, outs),pre,post,_) -> 
      let args = List.concat [ins; outs]
      match args with 
      | [] -> Map.empty
      | _  -> let unifs = GetArgValueUnifications args
              GetUnifications indent args heapInst unifs (BinaryAnd pre post)
              
  | _ -> failwith ("not a method: " + m.ToString())

//  =========================================================================
/// For a given constant "o" (which is an object, something like "gensym32"), 
/// finds a path of field references from "this". 
///
/// Implements a backtracking search over the heap entries to find that
/// path.  It starts from the given object, and follows the backpointers
/// until it reaches the root ("this")
//  ========================================================================= 
let objRef2ExprCache = new System.Collections.Generic.Dictionary<string, Expr>()
let GetObjRefExpr objRefName (heapInst: HeapInstance) = 
  let rec __GetObjRefExpr objRefName visited = 
    if Set.contains objRefName visited then 
      None
    else 
      let newVisited = Set.add objRefName visited
      match objRefName with
      | "this" -> Some(ObjLiteral("this"))
      | _ -> 
          let rec __fff lst = 
            match lst with
            | ((o,Var(fldName,_)),_) :: rest -> 
                match __GetObjRefExpr o.name newVisited with
                | Some(expr) -> Some(Dot(expr, fldName))
                | None -> __fff rest
            | [] -> None
          let backPointers = heapInst.assignments |> List.filter (fun ((_,_),l) -> l = ObjLiteral(objRefName))
          __fff backPointers 
  (* --- function body starts here --- *)
  if objRef2ExprCache.ContainsKey(objRefName) then
    Some(objRef2ExprCache.[objRefName])
  else
    let res = __GetObjRefExpr objRefName (Set.empty)
    match res with 
    | Some(e) -> objRef2ExprCache.Add(objRefName, e)
    | None -> ()
    res

//  =======================================================
/// Applies given unifications onto the given heap/env/ctx
/// 
/// If "conservative" is true, applies only those that 
/// can be verified to hold, otherwise applies all of them
//  =======================================================
let rec ApplyUnifications indent prog comp mthd unifs heapInst conservative = 
  let idt = Indent indent
  let __CheckUnif o f e idx =
    if not conservative || not Options.CONFIG.checkUnifications then 
      true 
    else
      let objRefExpr = GetObjRefExpr o heapInst |> Utils.ExtractOptionMsg ("Couldn't find a path from 'this' to " + o)
      let fldName = PrintVarName f                             
      let lhs = Dot(objRefExpr, fldName)
      let assertionExpr = match f with
                          | Var(_, Some(SeqType(_))) when not (idx = -1) -> BinaryEq (SelectExpr(lhs, IntLiteral(idx))) e
                          | Var(_, Some(SetType(_))) when not (idx = -1) -> BinaryIn e lhs
                          | _                                            -> BinaryEq lhs e 
      // check if the assertion follows and if so update the env
      let code = PrintDafnyCodeSkeleton prog (MethodAnalysisPrinter [comp,mthd] assertionExpr) false
      Logger.Debug (idt + "    - checking assertion: " + (PrintExpr 0 assertionExpr) + " ... ")
      let ok = CheckDafnyProgram code ("unif_" + (GetMethodFullName comp mthd))
      if ok then
        Logger.DebugLine " HOLDS"
      else
        Logger.DebugLine " DOESN'T HOLD"
      ok
  (* --- function body starts here --- *)
  match unifs with
  | (e,c) :: rest -> 
      let heapInst = ApplyUnifications indent prog comp mthd rest heapInst conservative
      let newHeap = heapInst.assignments|> List.fold (fun acc ((o,f),value) ->
                                                       if value = Const2Expr c then
                                                         if __CheckUnif o.name f e -1 then                                                
                                                           // change the value to expression
                                                           //Logger.TraceLine (sprintf "%s    - applied: %s.%s --> %s" idt (PrintConst o) (GetVarName f) (PrintExpr 0 e) )
                                                           Utils.ListMapAdd (o,f) e acc 
                                                         else
                                                           // don't change the value unless "conservative = false"
                                                           Utils.ListMapAdd (o,f) value acc
                                                       else 
                                                         let rec __UnifyOverLst lst cnt =
                                                               match lst with
                                                               | lstElem :: rest when lstElem = Const2Expr c ->
                                                                   if __CheckUnif o.name f e cnt then
                                                                     //Logger.TraceLine (sprintf "%s    - applied: %s.%s[%d] --> %s" idt (PrintConst o) (GetVarName f) cnt (PrintExpr 0 e) )
                                                                     e :: __UnifyOverLst rest (cnt+1)
                                                                   else  
                                                                     lstElem :: __UnifyOverLst rest (cnt+1)
                                                               | lstElem :: rest ->
                                                                   lstElem :: __UnifyOverLst rest (cnt+1)
                                                               | [] -> []
                                                         // see if it's a list, then try to match its elements, otherwise leave it as is
                                                         match value with
                                                         | SequenceExpr(elist) -> 
                                                             let newExprList = __UnifyOverLst elist 0
                                                             Utils.ListMapAdd (o,f) (SequenceExpr(newExprList)) acc
                                                         | SetExpr(elist) ->
                                                             let newExprList = __UnifyOverLst elist 0
                                                             Utils.ListMapAdd (o,f) (SetExpr(newExprList)) acc
                                                         | _ -> 
                                                             Utils.ListMapAdd (o,f) value acc
                                                     ) heapInst.assignments
      {heapInst with assignments = newHeap }
  | [] -> heapInst

//  ====================================================================================
/// Returns whether the code synthesized for the given method can be verified with Dafny
//  ====================================================================================
let VerifySolution prog solutions genRepr =
  // print the solution to file and try to verify it with Dafny
  //let prog = Program(solutions |> Utils.MapKeys |> Map.ofList |> Utils.MapKeys)
  let code = PrintImplCode prog solutions genRepr
  CheckDafnyProgram code dafnyVerifySuffix

let rec DiscoverAliasing exprList heapInst = 
  match exprList with
  | e1 :: rest -> 
      let eqExpr = rest |> List.fold (fun acc e -> 
                                        if Eval heapInst (fun _ -> true) (BinaryEq e1 e) = TrueLiteral then
                                          BinaryAnd acc (BinaryEq e1 e)
                                        else
                                          acc
                                     ) TrueLiteral
      BinaryAnd eqExpr (DiscoverAliasing rest heapInst)
  | [] -> TrueLiteral

//  =============================================================================
/// Returns an expression that combines the post-condition of a given method with
/// invariants for all objects present on the heap
//  =============================================================================
let GetHeapExpr prog mthd heapInst = 
  // get expressions to evaluate:
  //   - add post (and pre?) conditions                                     
  //   - go through all objects on the heap and assert their invariants  
  let pre,post = GetMethodPrePost mthd
  let prepostExpr = post //TODO: do we need the "pre" here as well?
  let heapObjs = heapInst.assignments |> List.fold (fun acc ((o,_),_) -> acc |> Set.add o) Set.empty
  heapObjs |> Set.fold (fun acc o -> 
                          let receiverOpt = GetObjRefExpr o.name heapInst
                          let receiver = Utils.ExtractOption receiverOpt
                          let objComp = FindComponent prog (GetTypeShortName o.objType) |> Utils.ExtractOption
                          let objInvs = GetInvariantsAsList objComp
                          let objInvsUpdated = objInvs |> List.map (ChangeThisReceiver receiver)
                          objInvsUpdated |> List.fold (fun a e -> BinaryAnd a e) acc
                      ) prepostExpr

// ------------------------------- Modularization stuff ---------------------------------

let GetModularBranch prog comp meth hInst = 
  let rec __AddDirectChildren e acc = 
    match e with
    | ObjLiteral(_) when not (e = ThisLiteral || e = NullLiteral) -> acc |> Set.add e
    | SequenceExpr(elist)
    | SetExpr(elist) -> elist |> List.fold (fun acc2 e2 -> __AddDirectChildren e2 acc2) acc
    | _ -> acc
  let __GetDirectChildren = 
    let thisRhsExprs = hInst.assignments |> List.choose (function ((obj,_),e) when obj.name = "this" -> Some(e) | _ -> None)
    thisRhsExprs |> List.fold (fun acc e -> __AddDirectChildren e acc) Set.empty 
                 |> Set.toList
  let directChildren = lazy (__GetDirectChildren)
  let __IsAbstractField ty var = 
    let builder = CascadingBuilder<_>(false)
    let varName = GetVarName var
    builder {
      let! comp = FindComponent prog (GetTypeShortName ty)
      let! fld = GetAbstractFields comp |> List.fold (fun acc v -> if GetVarName v = varName then Some(varName) else acc) None
      return true
    }
  let __GetAbsFldAssignments objLitName = 
    hInst.assignments |> List.choose (fun ((obj,var),e) ->
                                        if obj.name = objLitName && __IsAbstractField obj.objType var then
                                          Some(var,e)
                                        else
                                          None)
  let rec __ExamineAndFix x e = 
    match e with
    | ObjLiteral(id) when not (Utils.ListContains e (directChildren.Force())) -> 
        let absFlds = __GetAbsFldAssignments id
        absFlds |> List.fold (fun acc (Var(vname,_),vval) -> BinaryAnd acc (BinaryEq (Dot(x, vname)) vval)) TrueLiteral
    | SequenceExpr(elist) ->
        let rec __fff lst acc cnt = 
          match lst with
          | fsExpr :: rest -> 
              let acc = BinaryAnd acc (__ExamineAndFix (SelectExpr(x, IntLiteral(cnt))) fsExpr)
              __fff rest acc (cnt+1)
          | [] -> 
              let lenExpr = BinaryEq (SeqLength(x)) (IntLiteral(cnt)) 
              BinaryAnd lenExpr acc
        __fff elist TrueLiteral 0
    | _ -> BinaryEq x e

  let __GetSpecFor objLitName =
    let absFieldAssignments = __GetAbsFldAssignments objLitName
    absFieldAssignments |> List.fold (fun acc (Var(name,_),e) -> BinaryAnd acc (__ExamineAndFix (IdLiteral(name)) e)) TrueLiteral
  let __GetArgsUsed expr = 
    let args = GetMethodArgs meth
    let argSet = DescendExpr2 (fun e acc ->
                                 match e with
                                 | VarLiteral(vname) ->
                                     match args |> List.tryFind (function Var(name,_) when vname = name -> true | _ -> false) with
                                     | Some(var) -> acc |> Set.add var
                                     | None -> acc
                                 | _ -> acc
                               ) expr Set.empty
    argSet |> Set.toList
  let rec __GetDelegateMethods objs acc = 
    match objs with
    | ObjLiteral(name) as obj :: rest ->
        let mName = sprintf "_synth_%s_%s" (GetMethodFullName comp meth |> String.map (fun c -> if c = '.' then '_' else c)) name
        let pre = TrueLiteral
        let post = __GetSpecFor name
        let ins = __GetArgsUsed (BinaryAnd pre post)
        let sgn = Sig(ins, [])
        let m = Method(mName, sgn, pre, post, true)
        __GetDelegateMethods rest (acc |> Map.add obj m)
    | _ :: rest -> failwith "internal error: expected to see only ObjLiterals"
    | [] -> acc
  let __FindObj objName = 
    try 
      hInst.assignments |> List.find (fun ((obj,_),_) -> obj.name = objName) |> fst |> fst
    with
      | ex -> failwithf "obj %s not found for method %s" objName (GetMethodFullName comp meth)
  (* --- function body starts here --- *)
  let delegateMethods = __GetDelegateMethods (directChildren.Force()) Map.empty
  let initChildrenExprList = delegateMethods |> Map.toList
                                             |> List.map (fun (receiver, mthd) -> 
                                                            let key = __FindObj (PrintExpr 0 receiver), Var("", None)
                                                            let args = GetMethodArgs mthd |> List.map (fun (Var(name,_)) -> VarLiteral(name))
                                                            let e = MethodCall(receiver, GetMethodName mthd, args)
                                                            (key, e)
                                                         )
  let newAssgns = hInst.assignments |> List.filter (fun ((obj,_),_) -> if obj.name = "this" then true else false)
  let newProg, newComp, newMethodsLst = delegateMethods |> Map.fold (fun acc receiver newMthd ->
                                                                       let obj = __FindObj (PrintExpr 0 receiver)
                                                                       match acc with
                                                                       | accProg, accComp, accmList ->
                                                                           let oldComp = FindComponent accProg (GetTypeShortName obj.objType) |> Utils.ExtractOption
                                                                           let prog', mcomp' = AddReplaceMethod accProg oldComp newMthd None
                                                                           let mList' = (mcomp', newMthd) :: accmList
                                                                           let comp' = if accComp = oldComp then mcomp' else accComp
                                                                           prog', comp', mList'
                                                                    ) (prog, comp, [])
  newProg, newComp, newMethodsLst, { hInst with assignments = initChildrenExprList @ newAssgns }

let rec MakeModular indent prog comp m cond heapInst = 
  let idt = Indent indent
  if Options.CONFIG.genMod then   
    Logger.InfoLine (idt + "    - delegating to method calls     ...")
    let newProg, newComp, newMthdLst, newHeapInst = GetModularBranch prog comp m heapInst
    let msol = Utils.MapSingleton (newComp,m) [cond, newHeapInst]
    newMthdLst |> List.fold (fun acc (c,m) -> 
                                  acc |> MergeSolutions (Utils.MapSingleton (c,m) []) 
                              ) msol     
  else 
    Utils.MapSingleton (comp,m) [cond, heapInst]

//let GetModularSol prog sol = 
//  let comp = fst (fst sol)
//  let meth = snd (fst sol)
//  let rec __xxx prog lst = 
//    match lst with
//    | (cond, hInst) :: rest -> 
//        let newProg, newComp, newMthdLst, newhInst = GetModularBranch prog comp meth hInst
//        let newProg, newRest = __xxx newProg rest
//        newProg, ((cond, newhInst) :: newRest)
//    | [] -> prog, []
//  let newProg, newSolutions = __xxx prog (snd sol)
//  let newComp = FindComponent newProg (GetComponentName comp) |> Utils.ExtractOption
//  newProg, ((newComp, meth), newSolutions)
//
//let Modularize prog solutions = 
//  let rec __Modularize prog sols acc = 
//    match sols with
//    | sol :: rest -> 
//        let (newProg, newSol) = GetModularSol prog sol
//        let newAcc = acc |> Map.add (fst newSol) (snd newSol)
//        __Modularize newProg rest newAcc 
//    | [] -> (prog, acc)
//  (* --- function body starts here --- *) 
//  __Modularize prog (Map.toList solutions) Map.empty 

// --------------------------------------------------------------------------------------

//  ============================================================================
/// Attempts to synthesize the initialization code for the given constructor "m"
///
/// Returns a (heap,env,ctx) tuple
//  ============================================================================                           
let rec AnalyzeConstructor indent prog comp m =
  let idt = Indent indent
  let methodName = GetMethodName m
  let pre,post = GetMethodPrePost m
  // generate Dafny code for analysis first
  let code = PrintDafnyCodeSkeleton prog (MethodAnalysisPrinter [comp,m] FalseLiteral) false
  Logger.InfoLine (idt + "[*] Analyzing constructor")
  Logger.InfoLine (idt + "------------------------------------------")
  Logger.InfoLine (PrintMethodSignFull (indent + 4) m)
  Logger.InfoLine (idt + "------------------------------------------")
  Logger.Info     (idt + "    - searching for an instance      ...")
  let models = RunDafnyProgram code (dafnyScratchSuffix + "_" + (GetMethodFullName comp m))  
  if models.Count = 0 then
    // no models means that the "assert false" was verified, which means that the spec is inconsistent
    Logger.WarnLine (idt + " !!! SPEC IS INCONSISTENT !!!")
    Map.empty
  else 
    if models.Count > 1 then 
      Logger.WarnLine " FAILED "
      failwith "internal error (more than one model for a single constructor analysis)"
    Logger.InfoLine " OK "
    let model = models.[0]
    let hModel = ReadFieldValuesFromModel model prog comp m
    let heapInst = ResolveModel hModel
    let unifs = GetUnificationsForMethod indent comp m heapInst |> Map.toList
    let heapInst = ApplyUnifications indent prog comp m unifs heapInst true
        
    // split into method calls
    let sol = MakeModular indent prog comp m TrueLiteral heapInst

    if Options.CONFIG.verifySolutions then
      Logger.InfoLine (idt + "    - verifying synthesized solution ... ")
      let verified = VerifySolution prog sol Options.CONFIG.genRepr
      Logger.Info (idt + "    ")
      if verified then
        Logger.InfoLine "~~~ VERIFIED ~~~"
        sol
      else 
        Logger.InfoLine "!!! NOT VERIFIED !!!"
        if Options.CONFIG.inferConditionals then
          Logger.InfoLine (idt + "    Strengthening the pre-condition")
          TryInferConditionals (indent + 4) prog comp m unifs heapInst
        else
          sol      
    else
      sol
and TryInferConditionals indent prog comp m unifs heapInst = 
  let idt = Indent indent
  let wrongSol = Utils.MapSingleton (comp,m) [TrueLiteral, heapInst]
  let heapInst2 = ApplyUnifications indent prog comp m unifs heapInst false
  let expr = GetHeapExpr prog m heapInst2
  // now evaluate and see what's left
  let newCond = Eval heapInst2 (function VarLiteral(_) -> false | _ -> true) expr
  try
    if newCond = TrueLiteral then
      Logger.InfoLine (sprintf "%s    - no more interesting pre-conditions" idt)
      wrongSol
    else
      let candCond = 
        if newCond = FalseLiteral then
          // it must be because there is some aliasing going on between method arguments, 
          // so we should try that as a candidate pre-condition
          let tmp = DiscoverAliasing (GetMethodArgs m |> List.map (function Var(name,_) -> VarLiteral(name))) heapInst2
          if tmp = TrueLiteral then failwith ("post-condition evaluated to false and no aliasing was discovered")
          tmp
        else 
          newCond
      Logger.InfoLine (sprintf "%s    - candidate pre-condition: %s" idt (PrintExpr 0 candCond))
      let p2,c2,m2 = AddPrecondition prog comp m candCond
      let sol = MakeModular indent p2 c2 m2 candCond heapInst2
      Logger.Info (idt + "    - verifying partial solution ... ")
      let verified = 
        if Options.CONFIG.verifyPartialSolutions then
          VerifySolution p2 sol Options.CONFIG.genRepr
        else 
          true
      if verified then
        if Options.CONFIG.verifyPartialSolutions then
          Logger.InfoLine "VERIFIED"
        else 
          Logger.InfoLine "SKIPPED"
        let p3,c3,m3 = AddPrecondition prog comp m (UnaryNot(candCond))
        MergeSolutions sol (AnalyzeConstructor (indent + 2) p3 c3 m3)
      else 
        Logger.InfoLine "NOT VERIFIED"
        wrongSol                     
  with
    ex -> raise ex
      
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
                                       let idx = m.LastIndexOf(".")
                                       if idx = -1 || idx = m.Length - 1 then
                                         raise (InvalidCmdLineArg("Invalid method full name: " + m))
                                       let compName = m.Substring(0, idx)
                                       let methName = m.Substring(idx + 1)
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
/// Returns a map from (component * method) |--> Expr * HeapInstance
// ============================================================================
let rec AnalyzeMethods prog members = 
  let rec __AnalyzeConstructorDeep prog mList = 
    match mList with
    | (comp,mthd) :: rest -> 
        let sol = AnalyzeConstructor 2 prog comp mthd
        let unsolved = sol |> Map.filter (fun (c,m) lst -> lst = []) |> Utils.MapKeys
        sol |> MergeSolutions (__AnalyzeConstructorDeep prog (rest@unsolved))
    | [] -> Map.empty
  (* --- function body starts here --- *)
  match members with
  | (comp,m) :: rest -> 
      match m with
      | Method(_,_,_,_,true) -> 
          let sol = __AnalyzeConstructorDeep prog [comp,m]
          Logger.InfoLine ""
          AnalyzeMethods prog rest |> MergeSolutions sol
      | _ -> AnalyzeMethods prog rest
  | [] -> Map.empty

let Analyze prog filename =
  let rec __AddMethodsFromProg methods solutions = 
    match methods with
    | (c,m) :: rest -> 
        let exists = solutions |> Map.tryFindKey (fun (c1,m1) _ -> GetComponentName c = GetComponentName c1 && GetMethodName m = GetMethodName m1)
        match exists with
        | Some(_) -> __AddMethodsFromProg rest solutions
        | None -> __AddMethodsFromProg rest (solutions |> Map.add (c,m) [])
    | [] -> solutions
  /// Prints given solutions to a file
  let __PrintSolution prog outFileName solutions = 
    use file = System.IO.File.CreateText(outFileName)
    file.AutoFlush <- true  
    //let prog = Program(solutions |> Utils.MapKeys |> Map.ofList |> Utils.MapKeys)
    // add all other methods (those for which we don't have synthesized solution) as well
    let allMethods = FilterMembers prog FilterConstructorMembers
    let extSolutions = solutions //__AddMethodsFromProg allMethods solutions
    let synthCode = PrintImplCode prog extSolutions Options.CONFIG.genRepr
    fprintfn file "%s" synthCode
  (* --- function body starts here --- *)
  let solutions = AnalyzeMethods prog (GetMethodsToAnalyze prog)
  let progName = System.IO.Path.GetFileNameWithoutExtension(filename)
  let outFlatSolFileName = dafnySynthFileNameTemplate.Replace("###", progName)
  Logger.InfoLine "Printing synthesized code"
  __PrintSolution prog outFlatSolFileName solutions
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