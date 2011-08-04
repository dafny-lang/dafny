module Modularizer

open Ast
open AstUtils
open MethodUnifier
open Printer 
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
                   
//  =======================================================================
/// Tries to make a given solution for a given method into more modular, 
/// by delegating some statements (initialization of inner objects) to 
/// method calls. 
//  =======================================================================
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

  let __FindObj objName = 
    try 
      hInst.assignments |> List.find (fun ((obj,_),_) -> obj.name = objName) |> fst |> fst
    with
      | ex -> failwithf "obj %s not found for method %s" objName (GetMethodFullName comp meth)

  let __GetObjLitType objLitName = 
    (__FindObj objLitName).objType

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
        let pre,_ = GetMethodPrePost meth //TrueLiteral
        let post = __GetSpecFor name
        let ins = __GetArgsUsed (BinaryAnd pre post)
        let sgn = Sig(ins, [])
        let m = Method(mName, sgn, pre, post, true)
        let c = FindComponent prog (name |> __GetObjLitType |> GetTypeShortName) |> Utils.ExtractOption
        let m',unifs = TryFindExisting c m
        let args = ApplyMethodUnifs m' unifs
        __GetDelegateMethods rest (acc |> Map.add obj (c,m',args))
    | _ :: rest -> failwith "internal error: expected to see only ObjLiterals"
    | [] -> acc

  (* --- function body starts here --- *)
  let delegateMethods = __GetDelegateMethods (directChildren.Force()) Map.empty
  let initChildrenExprList = delegateMethods |> Map.toList
                                             |> List.map (fun (receiver, (cmp,mthd,args)) -> 
                                                            let key = __FindObj (PrintExpr 0 receiver), Var("", None)
                                                            let e = MethodCall(receiver, GetMethodName mthd, args)
                                                            (key, e))
  let newAssgns = hInst.assignments |> List.filter (fun ((obj,_),_) -> if obj.name = "this" then true else false)
  let newProg, newComp, newMethodsLst = delegateMethods |> Map.fold (fun acc receiver (c,newMthd,_) ->
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
