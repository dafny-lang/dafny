module Modularizer

open Ast
open Getters
open AstUtils
open MethodUnifier
open PrintUtils
open Resolver
open Utils

//  =======================================================================
/// Merges two solution maps so that if there are multiple entries for a
/// single (comp,method) pair it concatenates them (corresponds to multiple 
/// branches).
//  =======================================================================
let MergeSolutions sol1 sol2 = 
  let rec __Merge sol1map sol2lst res =
    match sol2lst with
    | ((c2,m2), lst2) :: rest -> 
        match sol1map |> Map.tryFindKey (fun (c1,m1) lst1 -> CheckSameMethods (c1,m1) (c2,m2)) with
        | Some(c1,m1) -> 
            let lst1 = sol1map |> Map.find(c1,m1)
            let newRes = res |> Map.add (c1,m1) (lst1@lst2)
            __Merge sol1map rest newRes
        | None -> 
            let newRes = res |> Map.add (c2,m2) lst2
            __Merge sol1map rest newRes
    | [] -> res
  (* --- function body starts here --- *)
  __Merge sol1 (sol2 |> Map.toList) sol1 
 
//  ===========================================                   
///
//  ===========================================                   
let rec MakeModular indent prog comp meth cond hInst callGraph = 
  let directChildren = lazy (GetDirectModifiableChildren hInst)

  let __IsAbstractField ty var = 
    let builder = CascadingBuilder<_>(false)
    let varName = GetVarName var
    builder {
      let! comp = FindComponent prog (GetTypeShortName ty)
      let! fld = GetAbstractFields comp |> List.fold (fun acc v -> if GetVarName v = varName then Some(varName) else acc) None
      return true
    }

  let __FindObj objName = 
    try 
      //hInst.assignments |> List.find (fun ((obj,_),_) -> obj.name = objName) |> fst |> fst
      hInst.assignments |> List.choose (function FieldAssignment((obj,_),_) -> 
                                                   if (obj.name = objName) then Some(obj) else None 
                                                 | _ -> None)
                        |> List.head
    with
      | ex -> failwithf "obj %s not found for method %s" objName (GetMethodFullName comp meth)

  let __GetObjLitType objLitName = 
    (__FindObj objLitName).objType

  //  ===============================================================================
  /// Goes through the assignments of the heapInstance and returns only those 
  /// assignments that correspond to abstract fields of the given "objLitName" object
  //  ===============================================================================
  let __GetAbsFldAssignments objLitName = 
    hInst.assignments |> List.choose (function
                                        FieldAssignment ((obj,var),e) ->
                                          if obj.name = objLitName && __IsAbstractField obj.objType var then
                                            Some(var,e)
                                          else
                                            None
                                        | _ -> None)

  //  ===============================================================================
  /// The given assignment is: 
  ///   x := e
  ///
  /// If e is an object (e.g. gensym32) with e.g. two abstract fields "a" and "b", 
  /// with values 3 and 8 respectively, then the "x := e" spec is fixed as following: 
  ///   x.a := 3 && x.b := 8
  /// 
  /// List values are handled similarly, e.g.:
  ///   x := [gensym32]
  /// is translated into
  ///   |x| = 1 && x[0].a = 3 && x[0].b = 8
  //  ===============================================================================
  let rec __ExamineAndFix x e = 
    match e with
    | ObjLiteral(id) when not (Utils.ListContains e (directChildren.Force())) -> //TODO: is it really only non-direct children?
        let absFlds = __GetAbsFldAssignments id
        absFlds |> List.fold (fun acc (var,vval) -> BinaryAnd acc (BinaryEq (Dot(x, GetVarName var)) vval)) TrueLiteral
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

  //  ================================================================================
  /// The spec for an object consists of assignments to its abstract fields with one 
  /// caveat: if some assignments include non-direct children objects of "this", then 
  /// those objects cannot be used directly in the spec; instead, their properties must 
  /// be expanded and embeded (that's what the "ExamineAndFix" function does)
  //  ================================================================================
  let __GetSpecFor objLitName =
    let absFieldAssignments = __GetAbsFldAssignments objLitName
    let absFldAssgnExpr = absFieldAssignments |> List.fold (fun acc (var,e) -> BinaryAnd acc (__ExamineAndFix (IdLiteral(GetVarName var)) e)) TrueLiteral
    let retValExpr = hInst.methodRetVals |> Map.fold (fun acc varName varValueExpr -> BinaryAnd acc (BinaryEq (VarLiteral(varName)) varValueExpr)) TrueLiteral
    BinaryAnd absFldAssgnExpr retValExpr
  
  //  ================================================================================================
  /// Simply traverses a given expression and returns all arguments of the "meth" method that are used
  //  ================================================================================================
  let __GetArgsUsed expr = 
    let args = GetMethodArgs meth
    let argSet = DescendExpr2 (fun e acc ->
                                 match e with
                                 | VarLiteral(vname) ->
                                     match args |> List.tryFind (fun var -> GetVarName var = vname) with
                                     | Some(var) -> acc |> Set.add var
                                     | None -> acc
                                 | _ -> acc
                               ) expr Set.empty
    argSet |> Set.toList

  let rec __GetDelegateMethods objs acc = 
    match objs with
    | ObjLiteral(name) as obj :: rest ->
        let mName = sprintf "_synth_%s_%s" (GetMethodFullName comp meth |> String.map (fun c -> if c = '.' then '_' else c)) name
        let pre,_ = GetMethodPrePost meth //TrueLiteral
        let post = __GetSpecFor name
        let ins = __GetArgsUsed (BinaryAnd pre post)
        let sgn = Sig(ins, [])
        let m = Method(mName, sgn, pre, post, true)
        let c = FindComponent prog (name |> __GetObjLitType |> GetTypeShortName) |> Utils.ExtractOption
        let m',unifs = TryFindExisting c m
        let args = ApplyMethodUnifs obj (c,m') unifs
        __GetDelegateMethods rest (acc |> Map.add obj (c,m',args))
    | _ :: rest -> failwith "internal error: expected to see only ObjLiterals"
    | [] -> acc

  //  =======================================================================
  /// Tries to make a given solution for a given method into more modular, 
  /// by delegating some statements (initialization of inner objects) to 
  /// method calls. 
  //  =======================================================================
  let __GetModularBranch = 
    let delegateMethods = __GetDelegateMethods (directChildren.Force()) Map.empty
    let initChildrenExprList = delegateMethods |> Map.toList
                                               |> List.map (fun (_, (_,_,asgs)) -> asgs)
                                               |> List.concat
    let newAssgns = hInst.assignments |> List.filter (function FieldAssignment((obj,_),_) -> obj.name = "this" | _ -> false)
    let newMethodsLst = delegateMethods |> Map.fold (fun acc receiver (c,newMthd,_) ->
                                                       (c,newMthd) :: acc
                                                    ) []
    newMethodsLst, { hInst with assignments = initChildrenExprList @ newAssgns }

  (* --- function body starts here --- *)
  let idt = Indent indent
  if Options.CONFIG.genMod then   
    Logger.InfoLine (idt + "    - delegating to method calls ...")
    // first try to find a match for the entire method (based on the given solution)
    let postSpec = __GetSpecFor "this"
    let meth' = match meth with
                | Method (mname, msig, mpre, _, isConstr) -> Method(mname, msig, mpre, postSpec, isConstr)
                | _ -> failwithf "internal error: expected a Method but got %O" meth
    match TryFindExistingAndConvertToSolution indent comp meth' cond callGraph with
    | Some(sol) -> sol |> FixSolution comp meth
    | None -> 
        // if not found, try to split into parts
        let newMthdLst, newHeapInst = __GetModularBranch
        let msol = Utils.MapSingleton (comp,meth) [cond, newHeapInst]
        newMthdLst |> List.fold (fun acc (c,m) -> 
                                   acc |> MergeSolutions (Utils.MapSingleton (c,m) []) 
                                 ) msol     
  else 
    Utils.MapSingleton (comp,meth) [cond, hInst]

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
