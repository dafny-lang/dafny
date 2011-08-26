module Analyzer

open Ast
open AstUtils
open CodeGen
open DafnyModelUtils
open DafnyPrinter
open FixpointSolver 
open MethodUnifier
open Modularizer
open Options
open PipelineUtils
open PrintUtils
open Resolver  
open TypeChecker
open Utils

open Microsoft.Boogie

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
  let ghostPre = GetMethodGhostPrecondition m |> Desugar 
  //let sigStr = PrintSig signature
  let sigVars = 
    match signature with
    | Sig(ins,outs) ->
        List.concat [ins; outs] |> List.fold (fun acc vd -> acc + (sprintf "    var %s;" (PrintVarDecl vd)) + newline) ""
  "  method " + methodName + "()" + newline +
  "    modifies this;" + newline +
  "  {" + newline + 
  // print signature as local variables
  sigVars +
  "    // assume precondition" + newline +
  "    assume " + (PrintExpr 0 pre) + ";" + newline +
  "    // assume ghost precondition" + newline +
  "    assume " + (PrintExpr 0 ghostPre) + ";" + newline +
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
    | Method(_) -> 
        (GenMethodAnalysisCode c m assertion) + newline +
        (MethodAnalysisPrinter rest assertion comp)
    | _ -> ""
  | _ :: rest -> MethodAnalysisPrinter rest assertion comp
  | [] -> ""     

//  =========================================================================
/// For a given constant "objRefName" (which is an object, something like 
/// "gensym32"), finds a path of field references from "this" (e.g. something
/// like "this.next.next"). 
///
/// Implements a backtracking search over the heap entries to find that
/// path.  It starts from the given object, and follows the backpointers
/// until it reaches the root ("this")
//  ========================================================================= 
// let objRef2ExprCache = new System.Collections.Generic.Dictionary<string, Expr>()
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
          let backPointers = heapInst.assignments |> List.choose (function 
                                                                    FieldAssignment (x,l) -> 
                                                                      if l = ObjLiteral(objRefName) then Some(x,l) else None
                                                                    |_ -> None)
          __fff backPointers 
  (* --- function body starts here --- *)
  __GetObjRefExpr objRefName (Set.empty)
// THIS DOESN'T WORK BECAUSE THE CACHE HAS TO BE PURGED AFTER EVERY METHOD
//  if objRef2ExprCache.ContainsKey(objRefName) then
//    Some(objRef2ExprCache.[objRefName])
//  else
//    let res = __GetObjRefExpr objRefName (Set.empty)
//    match res with 
//    | Some(e) -> objRef2ExprCache.Add(objRefName, e)
//    | None -> ()
//    res

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
  let heapObjs = heapInst.assignments |> List.fold (fun acc asgn ->
                                                      match asgn with
                                                      | FieldAssignment((o,_),_) -> acc |> Set.add o
                                                      | _ -> acc) Set.empty
  heapObjs |> Set.fold (fun acc o -> 
                          let receiverOpt = GetObjRefExpr o.name heapInst
                          let receiver = Utils.ExtractOption receiverOpt
                          let objComp = FindComponent prog (GetTypeShortName o.objType) |> Utils.ExtractOption
                          let objInvs = GetInvariantsAsList objComp
                          let objInvsUpdated = objInvs |> List.map (ChangeThisReceiver receiver)
                          objInvsUpdated |> List.fold (fun a e -> BinaryAnd a e) acc
                      ) prepostExpr

let IsUnmodConcrOnly prog (comp,meth) expr = 
  let isConstr = IsConstructor meth
  let rec __IsUnmodOnly args expr = 
    let __IsUnmodOnlyLst elist = 
      elist |> List.fold (fun acc e -> acc && (__IsUnmodOnly args e)) true
    match expr with                                                
    | IntLiteral(_)
    | BoolLiteral(_)
    | BoxLiteral(_)
    | Star        
    | VarDeclExpr(_)
    | ObjLiteral(_)                         -> true
    | VarLiteral(id)                        -> args |> List.exists (function Var(varName,_) when varName = id -> true | _ -> false)
    | IdLiteral("null") | IdLiteral("this") -> true
    | IdLiteral(id)                         -> 
        not (isConstr || IsAbstractField comp id)
    | Dot(e, fldName)                       -> //if isConstr then false else __IsUnmodOnlyLst [e] 
        if isConstr then
          false
        else
          // assume it is unmodifiable, because it is a method, so just check if it's concrete
          let lhsType = InferType prog comp (MethodArgChecker prog meth) e |> Utils.ExtractOptionMsg (sprintf "Inference failed for %s" (PrintExpr 0 e))
          IsConcreteField lhsType fldName          
    | AssertExpr(e)
    | AssumeExpr(e)
    | SeqLength(e)
    | LCIntervalExpr(e)
    | MethodOutSelect(e,_)   
    | UnaryExpr(_,e)                        -> __IsUnmodOnlyLst [e]
    | SelectExpr(e1, e2)
    | BinaryExpr(_,_,e1,e2)                 -> __IsUnmodOnlyLst [e1; e2]
    | IteExpr(e3, e1, e2)         
    | UpdateExpr(e1, e2, e3)                -> __IsUnmodOnlyLst [e1; e2; e3]
    | SequenceExpr(exprs) | SetExpr(exprs)  -> __IsUnmodOnlyLst exprs
    | MethodCall(rcv,_,_,aparams)           -> __IsUnmodOnlyLst (rcv :: aparams)
    | ForallExpr(vars,e)                    -> __IsUnmodOnly (args @ vars) e
  (* --- function body starts here --- *)
  __IsUnmodOnly (GetMethodInArgs meth) expr

let AddUnif indent e v unifMap =
  let idt = Indent indent
  let builder = new CascadingBuilder<_>(unifMap)
  builder {
    let! notAlreadyAdded = Map.tryFind e unifMap |> Utils.IsNoneOption |> Utils.BoolToOption
    Logger.DebugLine (idt + "    - adding unification " + (PrintExpr 0 e) + " <--> " + (PrintConst v))
    return Map.add e v unifMap
  }

//TODO: unifications should probably by "Expr <--> Expr" instead of "Expr <--> Const"
let rec GetUnifications prog indent (comp,meth) heapInst unifs expr =
  let idt = Indent indent
  // - first looks if the give expression talks only about method arguments (args)
  // - then it tries to evaluate it to a constant
  // - if all of these succeed, it adds a unification rule e <--> val(e) to the given unifMap map
  let __AddUnif e unifsAcc =
    if IsConstExpr e then
      unifsAcc
    else      
      let builder = new CascadingBuilder<_>(unifsAcc)
      builder {
        let! argsOnly = IsUnmodConcrOnly prog (comp,meth) e |> Utils.BoolToOption
        let! v = try Some(EvalFull heapInst e |> Expr2Const) with ex -> None
        return AddUnif indent e v unifsAcc
      }
  (* --- function body starts here --- *)
  AstUtils.DescendExpr2 __AddUnif expr unifs

//  =======================================================
/// Returns a map (Expr |--> Const) containing unifications
/// found for the given method and heap/env/ctx
//  =======================================================
let GetUnificationsForMethod indent prog comp m heapInst =
  let idt = Indent indent
  let rec GetArgValueUnifications args = 
    match args with
    | Var(name,_) :: rest -> 
        match Map.tryFind name heapInst.methodArgs with
        | Some(c) ->
            GetArgValueUnifications rest |> AddUnif indent (VarLiteral(name)) c
        | None -> failwith ("couldn't find value for argument " + name)
    | [] -> Map.empty
  let rec GetFldValueUnifications unifs = 
    heapInst.assignments |> List.fold (fun acc asgn ->  
                                         match asgn with 
                                         | FieldAssignment((obj,Var(vname,_)), fldVal) -> 
                                             try 
                                               let comp = obj.objType |> FindComponentForType prog |> Utils.ExtractOption
                                               if IsConcreteField comp vname then
                                                 let path = GetObjRefExpr obj.name heapInst |> Utils.ExtractOption
                                                 let c = Expr2Const fldVal
                                                 AddUnif indent (Dot(path, vname)) c acc
                                               else
                                                 acc
                                             with
                                             | ex -> 
                                                 Logger.WarnLine ("[WARN]: error during getting field value unifications: " + ex.Message)
                                                 acc
                                         | _ -> acc
                                      ) unifs

  (* --- function body starts here --- *)
  let unifs = GetArgValueUnifications (GetMethodInArgs m)
  let unifs = 
    //TODO: it should really read the "modifies" clause and figure out modifiable fields from there
    if not (IsConstructor m) then 
      GetFldValueUnifications unifs
    else
      unifs
  GetUnifications prog indent (comp,m) heapInst unifs (GetMethodPrePost m |> fun x -> BinaryAnd (fst x) (snd x))

//  =======================================================
/// Applies given unifications onto the given heap/env/ctx
/// 
/// If "conservative" is true, applies only those that 
/// can be verified to hold, otherwise applies all of them
//  =======================================================
let rec ApplyUnifications indent prog comp mthd unifs heapInst conservative = 
  let idt = Indent indent
  /// 
  let __CheckUnif o f e idx =
    if not conservative || not Options.CONFIG.checkUnifications then 
      true 
    else
      let lhs = if o = NoObj then
                  VarLiteral(GetVarName f)
                else
                  let objRefExpr = GetObjRefExpr o.name heapInst |> Utils.ExtractOptionMsg ("Couldn't find a path from 'this' to " + o.name)
                  let fldName = GetVarName f                             
                  Dot(objRefExpr, fldName)
      let assertionExpr = match f with
                          | Var(_, Some(SeqType(_))) when not (idx = -1) -> BinaryEq (SelectExpr(lhs, IntLiteral(idx))) e
                          | Var(_, Some(SetType(_))) when not (idx = -1) -> BinaryIn e lhs
                          | _                                            -> BinaryEq lhs e 
      // check if the assertion follows and if so update the env
      let code = PrintDafnyCodeSkeleton prog (MethodAnalysisPrinter [comp,mthd] assertionExpr) true
      Logger.Debug (idt + "    - checking assertion: " + (PrintExpr 0 assertionExpr) + " ... ")
      let ok = CheckDafnyProgram code ("unif_" + (GetMethodFullName comp mthd))
      if ok then
        Logger.DebugLine " HOLDS"
      else
        Logger.DebugLine " DOESN'T HOLD"
      ok
  ///
  let __Apply (o,f) c e value= 
    if value = Const2Expr c then
      if __CheckUnif o f e -1 then                                                
        // change the value to expression
        //Logger.TraceLine (sprintf "%s    - applied: %s.%s --> %s" idt (PrintConst o) (GetVarName f) (PrintExpr 0 e) )
        e 
      else
        value
    else 
      let rec __UnifyOverLst lst cnt =
        match lst with
        | lstElem :: rest when lstElem = Const2Expr c ->
            if __CheckUnif o f e cnt then
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
          SequenceExpr(newExprList)
      | SetExpr(elist) ->
          let newExprList = __UnifyOverLst elist 0
          SetExpr(newExprList)
      | _ -> 
          value

  (* --- function body starts here --- *)
  match unifs with
  | (e,c) :: rest -> 
      let heapInst = ApplyUnifications indent prog comp mthd rest heapInst conservative
      let newHeap = heapInst.assignments|> List.fold (fun acc asgn ->
                                                        match asgn with
                                                        | FieldAssignment((o,f),value) when heapInst.modifiableObjs |> Set.contains o ->
                                                            let e2 = __Apply (o,f) c e value
                                                            acc @ [FieldAssignment((o,f),e2)] 
                                                        | _ -> acc @ [asgn]
                                                     ) [] 
      let newRetVals = heapInst.methodRetVals |> Map.fold (fun acc key value ->
                                                             let e2 = __Apply (NoObj,Var(key, None)) c e value
                                                             acc |> Map.add key e2
                                                          ) Map.empty
      {heapInst with assignments = newHeap; methodRetVals = newRetVals}
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
                                        if EvalFull heapInst (BinaryEq e1 e) = TrueLiteral then
                                          BinaryAnd acc (BinaryEq e1 e)
                                        else
                                          acc
                                     ) TrueLiteral
      BinaryAnd eqExpr (DiscoverAliasing rest heapInst)
  | [] -> TrueLiteral

//
let DontResolveUnmodifiableStuff prog comp meth expr =
  let methodArgs = GetMethodInArgs meth
  let __IsMethodArg argName = methodArgs |> List.exists (fun (Var(vname,_)) -> vname = argName)
  let isConstr = IsConstructor meth
  match expr with
  | VarLiteral(id) when __IsMethodArg id -> false 
  | IdLiteral(id) when id = "this" || id = "null" -> true
  | IdLiteral(id) | Dot(_, id) -> 
      // this must be a field, so resolve it only if constructor
      isConstr
  | _ -> true

/// Descends down a given expression and returns bunch of sub-expressions that all evaluate to true
let FindClauses resolverFunc heapInst expr = 
  let MyFun expr acc =
    try
      match expr with
      // skip binary logical operators because we want to find smallest sub-expressions
      | BinaryExpr(_,op,_,_) when IsLogicalOp op -> acc 
      | _ ->
          let exprEval = Eval heapInst resolverFunc expr
          match exprEval with
          | _ when exprEval = TrueLiteral -> acc
          | _ ->
              let exprAllResolved = EvalFull heapInst expr
              match exprAllResolved with
              | BoolLiteral(true) -> acc @ [exprEval]
              | BoolLiteral(false) -> acc @ [UnaryNot exprEval]
              | _ -> acc
    with
    | _ -> acc
  (* --- function body starts here --- *)
  DescendExpr2 MyFun expr []

/// Descends down a given expression and returns all sub-expressions that evaluate to TrueLiteral
let FindTrueClauses resolverFunc heapInst expr = 
  let MyFun expr acc =
    try
      match expr with
      // skip binary logical operators because we want to find smallest sub-expressions
      | BinaryExpr(_,op,_,_) when IsLogicalOp op -> acc 
      | _ ->
          let exprEval = EvalAndCheckTrue heapInst resolverFunc expr
          match exprEval with
          | _ when exprEval = TrueLiteral -> acc
          | _ ->
              let exprAllResolved = EvalFull heapInst expr
              match exprAllResolved with
              | BoolLiteral(true) -> acc @ [exprEval]
              | _ -> acc
    with
    | _ -> acc
  (* --- function body starts here --- *)
  DescendExpr2 MyFun expr []

/// Returns a list of boolean expressions obtained by combining (in some way) 
/// the two given list of conditions conditions
let GetAllPossibleConditions specConds argConds aliasingConds = 
  let __Conjoin lst = lst |> List.fold (fun acc e -> BinaryAnd acc e) TrueLiteral
  let __Preproc lst = lst |> List.map SplitIntoConjunts |> List.concat |> Utils.ListDeduplicate

  // 0. aliasing conditions
  // 1. conjunction of spec conditions
  // 2. individual arg conditions
  // 3. conjunction of arg conditions
  // 4. individual spec conditions
  let aliasing = aliasingConds |> __Preproc
  let specIndi = specConds |> __Preproc
  let specConj = [__Conjoin specIndi]
  let argsIndi = argConds |> __Preproc
  let argsConj = [__Conjoin argsIndi]
  
  let allConds = aliasing @ specConj @ argsIndi @ specIndi @ argsConj
  allConds |> List.filter (fun e -> not (e = TrueLiteral)) 
           |> Utils.ListDeduplicate

//  ============================================================================
/// Attempts to synthesize the initialization code for the given constructor "m"
///
/// Returns a (heap,env,ctx) tuple
//  ============================================================================                           
let rec AnalyzeConstructor indent prog comp m callGraph =
  let idt = Indent indent
  let TryFindAndVerify m = 
    match TryFindExistingAndConvertToSolution indent comp m TrueLiteral callGraph with
    | Some(sol) ->
        if VerifySolution prog sol Options.CONFIG.genRepr then
          Logger.InfoLine (idt +  "    ~~~ VERIFIED ~~~")
          Some(sol)
        else 
          Logger.InfoLine (idt +  "    !!! NOT VERIFIED !!!")
          None
    | None -> None

  Logger.InfoLine (idt + "[*] Analyzing constructor")
  Logger.InfoLine (idt + "------------------------------------------")
  Logger.InfoLine (Printer.PrintMethodSignFull (indent + 4) comp m)
  Logger.InfoLine (idt + "------------------------------------------")
  match TryFindAndVerify m with
  | Some(sol) -> sol
  | None -> 
      let methodName = GetMethodName m
      let pre,post = GetMethodPrePost m
      // generate Dafny code for analysis first
      let code = PrintDafnyCodeSkeleton prog (MethodAnalysisPrinter [comp,m] FalseLiteral) true
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
        let heapInst = ResolveModel hModel m
        let unifs = GetUnificationsForMethod indent prog comp m heapInst |> Map.toList
        let heapInst = ApplyUnifications indent prog comp m unifs heapInst true
        
        // split into method calls
        let sol = MakeModular indent prog comp m TrueLiteral heapInst callGraph |> FixSolution comp m

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
              TryRecursion (indent + 4) prog comp m unifs heapInst callGraph
            else
              sol      
        else
          sol             
and TryRecursion indent prog comp m unifs heapInst callGraph = 
  let idt = Indent indent

  /// checks whether an expression is ok, meaning 
  ///   - only immediate concrete fields of the "this" object are used,
  ///   - no recursion on the same object with the same parameters
  ///   - not a constant
  let __IsOk hInst expr = 
    let compName = GetComponentName comp
    let methName = GetMethodName m
    try
      expr |> EvalNone hInst |> Expr2Const |> ignore
      false
    with
    | _ -> 
        DescendExpr2 (fun expr acc ->
                        if not acc then
                          false
                        else
                          match expr with
                          | Dot(discr, fldName) -> 
                              let obj = EvalFull heapInst discr
                              match obj with 
                              | ObjLiteral(id) when id = "this" -> 
                                  try 
                                    IsConcreteField (InferType prog comp (MethodArgChecker prog m) discr |> Utils.ExtractOption) fldName
                                  with
                                    | _ -> false
                              | ObjLiteral(id) -> false
                              | _ -> failwithf "Didn't expect the discriminator of a Dot to not be ObjLiteral"
                          | MethodCall(receiver, cn, mn, elst) when receiver = ThisLiteral && cn = compName && mn = methName -> 
                              elst |> List.exists (function VarLiteral(_) -> false | _ -> true)
                          | _ -> true                          
                      ) expr true

  /// Finds all modifiable fields in a given hInst, and checks if an "ok" 
  /// expression exists for each one of them.
  ///
  /// Returns all possible combinations of "ok" solutions (these are not verified yet).
  let __GetAllAssignments hInst premises = 
    let rec __IterVars vars = 
      match vars with
      | lhs :: [] -> 
          let lhsOptions = premises |> Set.toList 
                                    |> List.choose (function
                                                      | BinaryExpr(_,"=",l,r) -> if l = lhs then Some(r) elif r = lhs then Some(l) else None
                                                      | _ -> None)
                                    |> List.filter (__IsOk hInst)
                                    |> List.map (fun e -> [lhs,e])
          lhsOptions
      | lhs :: rest -> 
          let lhsOptions = __IterVars [lhs]
          if List.isEmpty lhsOptions then
            List.empty
          else 
            let restOptions = __IterVars rest 
            Utils.ListCombine (fun t1 t2 -> t1 @ t2) lhsOptions restOptions
      | [] -> List.empty
                                                              
    let stmts = ConvertToStatements hInst true
    let modVars = stmts |> List.choose (function
                                          | Assign(lhs,_) -> Some(lhs)
                                          | _ -> None)
    __IterVars modVars

  /// Print a given list of assignments
  let rec __PrintSol indent s = 
    let idt = Indent indent
    match s with
    | (l,r) :: [] -> 
        sprintf "%s%s := %s" idt (PrintExpr 0 l) (PrintExpr 0 r)
    | (l,r) :: rest -> 
        let str = __PrintSol indent [l,r]
        str + newline + (__PrintSol indent rest)  
    | [] -> ""      
      
  /// Returns a given method's postcondition where 
  ///   - all input variables are renamed so that their names start with "$" and 
  ///     (so that the unifier know that it's ok to try to unify those variables)
  ///   - all output variables are rewritten as $this.<method_name>(<args>)["<out_var_name>"]
  ///     (so that it is clear that they are results of a method call)
  let __GetMethodPostTemplate comp m = 
    let compName = GetComponentName comp
    let methName = GetMethodName m
    let ins = GetMethodInArgs m
    let outs = GetMethodOutArgs m
    let post = GetMethodPrePost m |> snd 
    post |> RewriteWithCtx (fun ctx e -> 
                              match e with 
                              | VarLiteral(id) when not (IsInVarList ctx id) -> 
                                  if IsInVarList outs id then
                                    let mcall = MethodCall(ThisLiteral, compName, methName, ins |> List.map (function Var(name,_) -> VarLiteral("$" + name)))
                                    let outSel = MethodOutSelect(mcall, id)
                                    Some(outSel)
                                  else
                                    Some(VarLiteral("$" + id)) 
                              | _ -> None) []
        |> ChangeThisReceiver (VarLiteral("$this"))

  /// Merges ...
  let __MergeSolutions hInst s = 
    let __FindRhs lhs = s |> List.choose (fun (l,r) -> if l = lhs then Some(r) else None) |> Utils.ListToOption
    let rec __FixAssignments asgs = 
      match asgs with
      | asg :: rest -> 
          let newAsg = 
            match asg with
            | FieldAssignment((obj,Var(fldName,_)) as discr,valExpr) -> 
                let objPath = GetObjRefExpr obj.name hInst |> Utils.ExtractOption
                let lhs = Dot(objPath, fldName)
                match __FindRhs lhs with
                | Some(rhs) -> FieldAssignment(discr,rhs)
                | None -> asg
            | _ -> asg
          newAsg :: (__FixAssignments rest)              
      | [] -> []
    let rec __FixRetValues retVals = 
      match retVals with
      | (varName,varExpr) :: rest -> 
          let lhs = VarLiteral(varName)
          let newVarExpr = 
            match __FindRhs lhs with
            | Some(rhs) -> rhs
            | None -> varExpr
          __FixRetValues rest |> Map.add varName newVarExpr
      | [] -> Map.empty
    if s = [] then 
      hInst
    else 
      // fix assignments
      let newAsgs = __FixAssignments hInst.assignments
      // fix return values
      let newRetVals = __FixRetValues (hInst.methodRetVals |> Map.toList)
      {hInst with assignments   = newAsgs; 
                  methodRetVals = newRetVals}


  /// For a given heap instance and a list of possible solutions, it iterates 
  /// trough all of them and returns whichever verifies first. 
  let rec __IterSolutions hInst premises wrongSol sList = 
    match sList with
    | s :: rest -> 
        Logger.InfoLine (idt + "Candidate solution:")
        Logger.InfoLine (__PrintSol (indent + 4) s)
        let hInst' = __MergeSolutions hInst s
        let sol = Utils.MapSingleton (comp,m) [TrueLiteral, hInst']
        if not (hInst' = hInst) && VerifySolution prog sol Options.CONFIG.genRepr then
          Logger.InfoLine (idt + "  ~~~ VERIFIED ~~~")
          sol
        else 
          Logger.InfoLine (idt + "  !!! NOT VERIFIED !!!")  
          match TryInferConditionals indent prog comp m unifs hInst' callGraph premises with
          | Some(candCond,solThis) -> 
              let m' = AddPrecondition prog comp m (UnaryNot(candCond))
              let solRest = AnalyzeConstructor (indent + 2) prog comp m' callGraph
              MergeSolutions solThis solRest |> FixSolution comp m
          | None -> 
              __IterSolutions hInst premises wrongSol rest    
    | [] -> wrongSol

  (* --- function body starts here --- *) 
  let loggerFunc = fun e -> Logger.TraceLine (sprintf "%s    --> %s" idt (PrintExpr 0 e))
  let expandOnlyModVarsFunc = fun e ->
    let __CheckExpr l = 
      //TODO: FIX THIS!!!!!
      let str = PrintExpr 0 l
      str.Contains("ret")
    match e with
    | BinaryExpr(_,"=",l,_) -> 
        //TODO: it should really check both lhs and rhs
        __CheckExpr l
    | _ -> __CheckExpr e

  let wrongSol = Utils.MapSingleton (comp,m) [TrueLiteral, heapInst]
  let heapInst = ApplyUnifications indent prog comp m unifs heapInst false
  let methodArgs = GetMethodInArgs m
  let heapExpr = GetHeapExpr prog m heapInst

  // find set of premises (don't resolve anything)
  let premises = heapExpr |> FindClauses (fun e -> false) heapInst 

  Logger.TraceLine (sprintf "%s Premises:" idt)
  premises |> List.iter loggerFunc  
                                                     
  // add only recursive call for now
  let post = __GetMethodPostTemplate comp m
    
  let premiseSet = premises |> Set.ofList |> Set.add post 
  let closedPremises = ComputeClosure heapInst expandOnlyModVarsFunc premiseSet
     
  Logger.TraceLine (idt + "Closed premises with methods")
  closedPremises |> Set.iter loggerFunc

  let s = __GetAllAssignments heapInst closedPremises
  if s = [] then
    // have at least one empty sol so that the original heapInst is not missed
    __IterSolutions heapInst closedPremises wrongSol [[]]
  else 
    __IterSolutions heapInst closedPremises wrongSol s
  
and TryInferConditionals indent prog comp m unifs heapInst callGraph premises = 
  let idt = Indent indent
  let loggerFunc = fun e -> Logger.TraceLine (sprintf "%s    --> %s" idt (PrintExpr 0 e))
  let methodArgs = GetMethodInArgs m

  /// Iterates through a given list of boolean conditions and checks
  /// which one suffices.  If it finds such a condition, it returns
  /// the following three things: 
  ///   - the condition itself
  ///   - the method with this condition added to its preconditions
  ///   - a solution
  /// Otherwise returns None.
  let rec __TryOutConditions heapInst candidateConditions =
    let idt = Indent indent
    match candidateConditions with 
    | [] ->
        Logger.InfoLine (sprintf "%s    - no more interesting pre-conditions" idt)
        None
    | candCond :: rest ->
        Logger.InfoLine (sprintf "%s    ________________________" idt)
        Logger.InfoLine (sprintf "%s    candidate pre-condition: %s" idt (PrintExpr 0 candCond))
        Logger.InfoLine (sprintf "%s    ------------------------" idt)
        let idt = idt + "  "
        let m2 = AddPrecondition prog comp m candCond
        let sol = MakeModular (indent+2) prog comp m2 candCond heapInst callGraph
        Logger.Info (idt + "    - verifying partial solution ... ")
        let verified = 
          if Options.CONFIG.verifyPartialSolutions then
            VerifySolution prog sol Options.CONFIG.genRepr
          else 
            true
        if verified then
          if Options.CONFIG.verifyPartialSolutions then Logger.InfoLine "VERIFIED" else Logger.InfoLine "SKIPPED"
          Some(candCond,m2,sol)
        else 
          Logger.InfoLine "NOT VERIFIED"
          __TryOutConditions heapInst rest

  if IsSolution1stLevelOnly heapInst then
    // try to find a non-recursive solution
    Logger.InfoLine (idt + "Strengthening the pre-condition")
    let expr = GetHeapExpr prog m heapInst
    let specConds1 = expr |> FindTrueClauses (DontResolveUnmodifiableStuff prog comp m) heapInst
    let specConds2 = premises |> Set.toList
    
    let isConstFunc = fun e -> try 
                                 EvalNone heapInst e |> Expr2Const |> ignore 
                                 true
                               with
                               | _ -> false
    let unmodConcrFunc = IsUnmodConcrOnly prog (comp,m)
    let is1stLevelFunc = __Is1stLevelExpr false heapInst
    
    let specConds = (specConds1 @ specConds2) 
                       |> List.map SimplifyExpr 
                       |> List.filter (fun e -> is1stLevelFunc e && unmodConcrFunc e && not (isConstFunc e))
    
    let aliasingCond = lazy(DiscoverAliasing (methodArgs |> List.map (function Var(name,_) -> VarLiteral(name))) heapInst) 
    let argConds = heapInst.methodArgs |> Map.fold (fun acc name value -> acc @ [BinaryEq (VarLiteral(name)) (Const2Expr value)]) []
    let allConds = GetAllPossibleConditions specConds argConds [aliasingCond.Force()]
    allConds |> List.iter loggerFunc

    match __TryOutConditions heapInst allConds with
    | Some(candCond,m2,sol) ->
        let solThis = match TryFindExistingAndConvertToSolution indent comp m2 candCond callGraph with
                      | Some(sol2) -> sol2
                      | None -> sol 
        let solThis = solThis |> FixSolution comp m                
        Some(candCond,solThis)
    | None -> 
        Logger.InfoLine (idt + "!!! Giving up !!!")
        None
  else
    // the solution is not immediate
    None
    


//  ===========================================================
/// Reads CONFIG.methodToSynth to return a list of methods 
/// that Jennisys should attempt to synthesize.
//  ===========================================================
let GetMethodsToAnalyze prog =
  let __ReadMethodsParam = 
    let mOpt = Options.CONFIG.methodToSynth;
    if mOpt = "*" then
      (* all *)
      FilterMembers prog FilterMethodMembers
    else
      let allMethods,neg = 
        if mOpt.StartsWith("~") then
          mOpt.Substring(1), true
        else
          mOpt, false
      (* exact list *)
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
        FilterMembers prog FilterMethodMembers |> List.filter (fun e -> not (Utils.ListContains e lst))
      else
        lst
  (* --- function body starts here --- *)
  let meths = __ReadMethodsParam
  if Options.CONFIG.constructorsOnly then
    meths |> List.filter (fun (c,m) -> IsConstructor m)
  else 
    meths

// ============================================================================
/// Goes through a given list of methods of the given program and attempts to 
/// synthesize code for each one of them.
///
/// Returns a map from (component * method) |--> Expr * HeapInstance
// ============================================================================
let rec AnalyzeMethods prog members solutionsSoFar = 
  let __IsAlreadySolved c m solutionMap = 
      let existingKey = solutionMap |> Map.tryFindKey (fun (cc,mm) v -> CheckSameMethods (c,m) (cc,mm) && not (v = [])) 
      match existingKey with
      | Some(_) -> true
      | None -> false

  let rec __AnalyzeConstructorDeep prog mList solutionsSoFar =
    let callGraph = GetCallGraph (solutionsSoFar |> Map.toList) Map.empty
    match mList with
    | (comp,mthd) :: rest -> 
        if not (__IsAlreadySolved comp mthd solutionsSoFar) then
          let sol = AnalyzeConstructor 2 prog comp mthd callGraph
          let unsolved = sol |> Map.filter (fun (c,m) lst -> lst = [] && not(__IsAlreadySolved c m solutionsSoFar)) |> Utils.MapKeys
          let newSols = solutionsSoFar |> MergeSolutions sol
          __AnalyzeConstructorDeep prog (rest@unsolved) newSols
        else
          __AnalyzeConstructorDeep prog rest solutionsSoFar
    | [] -> solutionsSoFar
  
  (* --- function body starts here --- *)
  match members with
  | (comp,m) :: rest -> 
      match m with
      | Method(_,_,_,_,_) -> 
          let sol = __AnalyzeConstructorDeep prog [comp,m] solutionsSoFar
          Logger.InfoLine ""
          AnalyzeMethods prog rest sol
      | _ -> AnalyzeMethods prog rest solutionsSoFar
  | [] -> solutionsSoFar

let Analyze prog filename =
  let rec __AddMethodsFromProg methods solutions = 
    match methods with
    | (c,m) :: rest -> 
        let exists = solutions |> Map.tryFindKey (fun (c1,m1) _ -> CheckSameMethods (c,m) (c1,m1))
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
  let solutions = AnalyzeMethods prog (GetMethodsToAnalyze prog) Map.empty
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