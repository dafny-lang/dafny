//  #########################################################################
///   Utilities for reading/building models from Boogie Visual Debugger files
///
///   author: Aleksandar Milicevic (t-alekm@microsoft.com)
//  #########################################################################

module DafnyModelUtils

(*
   The heap maps objects and fields to locations.
      heap: Const * VarDecl option |--> Const

   The environment maps locations to values (except that it can also 
   be locations to locations, because not all values are explicitly 
   present in the model.
      envMap: Const |--> Const

   The context is just a list of equality constraints collected on the way
      ctx: Set<Set<Const>>, where the inner set contains exactly two constants
*)

open Ast
open AstUtils
open Utils

open Microsoft.Boogie
                                         
let GetElemFullName (elem: Model.Element) = 
  elem.Names |> Seq.filter (fun ft -> ft.Func.Arity = 0)
             |> Seq.choose (fun ft -> Some(ft.Func.Name))
             |> Utils.SeqToOption
           
let GetElemName (elem: Model.Element) = 
  let fullNameOpt = GetElemFullName elem
  match fullNameOpt with
  | Some(fullName) ->
      let dotIdx = fullName.LastIndexOf(".")
      let fldName = fullName.Substring(dotIdx + 1)
      let clsName = if dotIdx = -1 then "" else fullName.Substring(0, dotIdx)
      Some(clsName, fldName)
  | None -> None
                                                   
let GetRefName (ref: Model.Element) = 
  match ref with
  | :? Model.Uninterpreted as uref -> uref.Name
  | _ -> failwith ("not a ref (Uninterpreted) but: " + ref.GetType().Name)
  
let ConvertValue (model: Model) (refVal: Model.Element) = 
  match refVal with 
  | :? Model.Number        as ival -> IntConst(ival.AsInt())
  | :? Model.Boolean       as bval -> BoolConst(bval.Value)
  | :? Model.Array         as aval -> failwith "reading array values from model not implemented"
  | :? Model.Uninterpreted as uval -> Unresolved(uval.Name) (* just a symbolic name for now, which we'll hopefully resolve later*)
  | _ -> failwith ("unexpected model element kind: " + refVal.ToString())

let GetInt (elem: Model.Element) = 
  match elem with
  | :? Model.Number as ival -> ival.AsInt()
  | _ -> failwith ("not an int element: " + elem.ToString())

let GetBool (elem: Model.Element) = 
  match elem with
  | :? Model.Boolean as bval -> bval.Value
  | _ -> failwith ("not a bool element: " + elem.ToString())

let GetType (e: Model.Element) prog = 
  let fNameOpt = GetElemFullName e
  match fNameOpt with
  | Some(fname) -> match fname with
                   | "intType"               -> Some(IntType)
                   | Prefix "class." clsName -> 
                       match FindComponent prog clsName with
                       | Some(comp) -> Some(GetClassType comp)
                       | None -> None
                   | _ -> None
  | None -> None

let GetLoc (e: Model.Element) =
  Unresolved(GetRefName e)

let FindSeqInEnv env key =
  match Map.find key env with
  | SeqConst(lst) -> lst
  | _ as x-> failwith ("not a SeqConst but: " + x.ToString())

let TryFindSetInEnv env key = 
  match Map.tryFind key env with
  | Some(SetConst(s)) -> Some(s)
  | Some(x) -> failwith ("not a SetConst but: " + x.ToString())
  | None -> None
                                   
let AddConstr c1 c2 ctx = 
  if c1 = c2 then
    ctx
  else
    match c1, c2 with
    | Unresolved(_), _ | _, Unresolved(_) -> 
        // find partitions
        let s1Opt = ctx |> Set.filter (fun ss -> Set.contains c1 ss) |> Utils.SetToOption
        let s2Opt = ctx |> Set.filter (fun ss -> Set.contains c2 ss) |> Utils.SetToOption
        match s1Opt, s2Opt with
        // both already exist --> so just merge them
        | Some(s1), Some(s2) -> ctx |> Set.remove s1 |> Set.remove s2 |> Set.add (Set.union s1 s2)
        // exactly one already exists --> add to existing
        | Some(s1), None -> ctx |> Set.remove s1 |> Set.add (Set.add c2 s1)
        | None, Some(s2) -> ctx |> Set.remove s2 |> Set.add (Set.add c1 s2)
        // neither exists --> create a new one
        | None, None -> ctx |> Set.add (Set.ofList [c1; c2])
    | _ -> failwith ("trying to add an equality constraint between two constants: " + c1.ToString() + ", and " + c2.ToString())
                                           
let rec UpdateContext lst1 lst2 ctx = 
  match lst1, lst2 with
  | fs1 :: rest1, fs2 :: rest2 -> 
      match fs1, fs2 with 
      | NoneConst,_ | _,NoneConst -> UpdateContext rest1 rest2 ctx
      | _ -> UpdateContext rest1 rest2 (AddConstr fs1 fs2 ctx)
  | [], [] -> ctx
  | _ -> failwith "lists are not of the same length"   

let UnboxIfNeeded (model: Microsoft.Boogie.Model) (e: Model.Element) = 
  let f_unbox = model.MkFunc("$Unbox", 2)
  let unboxed = f_unbox.Apps |> Seq.filter (fun ft -> if (GetLoc ft.Args.[1]) = (GetLoc e) then true else false)
                             |> Seq.choose (fun ft -> Some(ft.Result))
                             |> Utils.SeqToOption
  match unboxed with
  | Some(e) -> ConvertValue model e
  | None    -> GetLoc e

let ReadHeap (model: Microsoft.Boogie.Model) prog = 
  let f_heap_select = model.MkFunc("[3]", 3)
  let values = f_heap_select.Apps
  values |> Seq.fold (fun acc ft -> 
                        assert (ft.Args.Length = 3)
                        let ref = ft.Args.[1]
                        let fld = ft.Args.[2]
                        assert (Seq.length fld.Names = 1)
                        let fldFullName = (Seq.nth 0 fld.Names).Func.Name
                        let dotIdx = fldFullName.LastIndexOf(".")
                        let fldName = fldFullName.Substring(dotIdx + 1)
                        let clsName = if dotIdx = -1 then "" else fldFullName.Substring(0, dotIdx)
                        let refVal = ft.Result
                        let refObj = Unresolved(GetRefName ref)
                        let fldVarOpt = FindVar prog clsName fldName
                        match fldVarOpt with
                        | Some(fldVar) ->
                            let fldType = match fldVar with 
                                          | Var(_,t) -> t
                            let fldVal = ConvertValue model refVal
                            acc |> Map.add (refObj, fldVar) fldVal
                        | None -> acc
                      ) Map.empty

//  ====================================================================
/// Reads values that were assigned to given arguments. Those values
/// can be in functions with the same name as the argument name appended
/// with an "#" and some number after it.
//  ====================================================================
let rec ReadArgValues (model: Microsoft.Boogie.Model) args = 
  match args with 
  | Var(name,_) as v :: rest -> 
      let farg = model.Functions |> Seq.filter (fun f -> f.Arity = 0 && f.Name.StartsWith(name + "#")) |> Utils.SeqToOption
      match farg with
      | Some(func) -> 
          let fldVar = v
          assert (Seq.length func.Apps = 1)
          let ft = Seq.head func.Apps
          let fldVal = ConvertValue model (ft.Result)
          ReadArgValues model rest |> Map.add (Unresolved(name)) fldVal
      | None -> failwith ("cannot find corresponding function for parameter " + name)
  | [] -> Map.empty

//  ==============================================================
/// Reads stuff about sequences from a given model and ads it to 
/// the given "envMap" map and a "ctx" set. The relevant stuff is
/// fetched from the following functions:
///   Seq#Length, Seq#Index, Seq#Build, Seq#Append
//  ==============================================================
let ReadSeq (model: Microsoft.Boogie.Model) (envMap,ctx) =
  // reads stuff from Seq#Length
  let rec __ReadSeqLen (model: Microsoft.Boogie.Model) (len_tuples: Model.FuncTuple list) (envMap,ctx) =
    match len_tuples with
    | ft :: rest -> 
        let len = GetInt ft.Result
        let emptyList = Utils.GenList len NoneConst
        let newMap = envMap |> Map.add (GetLoc ft.Args.[0]) (SeqConst(emptyList))
        __ReadSeqLen model rest (newMap,ctx)
    | _ -> (envMap,ctx)

  // reads stuff from Seq#Index
  let rec __ReadSeqIndex (model: Microsoft.Boogie.Model) (idx_tuples: Model.FuncTuple list) (envMap,ctx) = 
    match idx_tuples with
    | ft :: rest -> 
        let srcLstKey = GetLoc ft.Args.[0]
        let oldLst = FindSeqInEnv envMap srcLstKey
        let idx = GetInt ft.Args.[1]
        let lstElem = UnboxIfNeeded model ft.Result
        let newLst = Utils.ListSet idx lstElem oldLst
        let newCtx = UpdateContext oldLst newLst ctx
        let newEnv = envMap |> Map.add srcLstKey (SeqConst(newLst))
        __ReadSeqIndex model rest (newEnv,newCtx)
    | _ -> (envMap,ctx)

  // reads stuff from Seq#Build
  let rec __ReadSeqBuild (model: Microsoft.Boogie.Model) (bld_tuples: Model.FuncTuple list) (envMap,ctx) = 
    match bld_tuples with
    | ft :: rest -> 
        let srcLstLoc = GetLoc ft.Args.[0]
        let dstLstLoc = GetLoc ft.Result
        let oldLst = FindSeqInEnv envMap srcLstLoc
        let idx = GetInt ft.Args.[1]
        let lstElemVal = UnboxIfNeeded model ft.Args.[2]
        let dstLst = FindSeqInEnv envMap dstLstLoc
        let newLst = Utils.ListBuild oldLst idx lstElemVal dstLst
        let newCtx = UpdateContext dstLst newLst ctx
        let newEnv = envMap |> Map.add dstLstLoc (SeqConst(newLst))
        __ReadSeqBuild model rest (newEnv,newCtx)
    | _ -> (envMap,ctx)

  // reads stuff from Seq#Append
  let rec __ReadSeqAppend (model: Microsoft.Boogie.Model) (app_tuples: Model.FuncTuple list) (envMap,ctx) = 
    match app_tuples with
    | ft :: rest -> 
        let srcLst1Loc = GetLoc ft.Args.[0]
        let srcLst2Loc = GetLoc ft.Args.[1]
        let dstLstLoc = GetLoc ft.Result
        let oldLst1 = FindSeqInEnv envMap srcLst1Loc
        let oldLst2 = FindSeqInEnv envMap srcLst2Loc
        let dstLst = FindSeqInEnv envMap dstLstLoc
        let newLst = List.append oldLst1 oldLst2
        let newCtx = UpdateContext dstLst newLst ctx
        let newEnv = envMap |> Map.add dstLstLoc (SeqConst(newLst))
        __ReadSeqAppend model rest (newEnv,newCtx)
    | _ -> (envMap,ctx)  

  let f_seq_len = model.MkFunc("Seq#Length", 1)
  let f_seq_idx = model.MkFunc("Seq#Index", 2)
  let f_seq_bld = model.MkFunc("Seq#Build", 4)
  let f_seq_app = model.MkFunc("Seq#Append", 2)
  (envMap,ctx) |> __ReadSeqLen model (List.ofSeq f_seq_len.Apps)
               |> __ReadSeqIndex model (List.ofSeq f_seq_idx.Apps)
               |> __ReadSeqBuild model (List.ofSeq f_seq_bld.Apps)
               |> __ReadSeqAppend model (List.ofSeq f_seq_app.Apps)


//  =====================================================
/// Reads stuff about sets from a given model and adds it 
/// to the given "envMap" map and "ctx" set.
//  =====================================================
let ReadSet (model: Microsoft.Boogie.Model) (envMap,ctx) =
  // reads stuff from Set#Empty
  let rec __ReadSetEmpty (empty_tuples: Model.FuncTuple list) (envMap,ctx) =
    match empty_tuples with
    | ft :: rest -> 
        let newMap = envMap |> Map.add (GetLoc ft.Result) (SetConst(Set.empty))
        __ReadSetEmpty rest (newMap,ctx)
    | [] -> (envMap,ctx)

  // reads stuff from [2]
  let rec __ReadSetMembership (set_tuples: Model.FuncTuple list) (env,ctx) = 
    match set_tuples with
    | ft :: rest -> 
        if GetBool ft.Result then
          let srcSetKey = GetLoc ft.Args.[0]
          let srcSet = match TryFindSetInEnv env srcSetKey with
                       | Some(s) -> s
                       | None -> Set.empty
          let elem = UnboxIfNeeded model ft.Args.[1]
          let newEnv = env |> Map.add srcSetKey (SetConst(Set.add elem srcSet))
          __ReadSetMembership rest (newEnv,ctx)
        else
          __ReadSetMembership rest (env,ctx)
    | [] -> (env,ctx)

  let t_set_empty = Seq.toList (model.MkFunc("Set#Empty", 1).Apps)    
  let t_set = Seq.toList (model.MkFunc("[2]", 2).Apps)
  (envMap,ctx) |> __ReadSetEmpty t_set_empty
               |> __ReadSetMembership t_set

(* More complicated way which now doesn't seem to be necessary *)
//let ReadSet (model: Microsoft.Boogie.Model) (envMap,ctx) =
//  // reads stuff from Set#Empty
//  let rec __ReadSetEmpty (empty_tuples: Model.FuncTuple list) (envMap,ctx) =
//    match empty_tuples with
//    | ft :: rest -> 
//        let newMap = envMap |> Map.add (GetLoc ft.Result) (SetConst(Set.empty))
//        __ReadSetEmpty rest (newMap,ctx)
//    | [] -> (envMap,ctx)
//
//  // reads stuff from Set#UnionOne and Set#Union
//  let rec __ReadSetUnions (envMap,ctx) = 
//    // this one goes through a given list of "UnionOne" tuples, updates 
//    // the env for those set that it was able to resolve, and returns a 
//    // list of tuples for which it wasn't able to resolve sets
//    let rec ___RSU1 (tuples: Model.FuncTuple list) env unprocessed =
//      match tuples with
//      | ft :: rest -> 
//          let srcSetKey = GetLoc ft.Args.[0]
//          match TryFindSetInEnv env srcSetKey with
//          | Some(oldSet) ->
//              let elem = UnboxIfNeeded model ft.Args.[1]
//              let newSet = Set.add elem oldSet
//              // update contex?
//              let newEnv = env |> Map.add (GetLoc ft.Result) (SetConst(newSet))
//              ___RSU1 rest newEnv unprocessed
//          | None -> ___RSU1 rest env (ft :: unprocessed)          
//      | [] -> (env,unprocessed)
//    // this one goes through a given list of "Union" tuples, updates 
//    // the env for those set that it was able to resolve, and returns a 
//    // list of tuples for which it wasn't able to resolve sets
//    let rec ___RSU (tuples: Model.FuncTuple list) env unprocessed =
//      match tuples with
//      | ft :: rest -> 
//          let set1Key = GetLoc ft.Args.[0]
//          let set2Key = GetLoc ft.Args.[1]
//          match TryFindSetInEnv env set1Key, TryFindSetInEnv env set2Key with
//          | Some(oldSet1), Some(oldSet2) ->
//              let newSet = Set.union oldSet1 oldSet2
//              // update contex?
//              let newEnv = env |> Map.add (GetLoc ft.Result) (SetConst(newSet))
//              ___RSU rest newEnv unprocessed
//          | _ -> ___RSU rest env (ft :: unprocessed)          
//      | [] -> (env,unprocessed)
//    // this one keeps looping as loong as the list of unprocessed tuples
//    // is decreasing, it ends when if falls down to 0, or fails if 
//    // the list stops decreasing
//    let rec ___RSU_until_fixpoint u1tuples utuples env =      
//      let newEnv1,unprocessed1 = ___RSU1 u1tuples env []
//      let newEnv2,unprocessed2 = ___RSU utuples newEnv1 []
//      let oldLen = (List.length u1tuples) + (List.length utuples)
//      let totalUnprocLen = (List.length unprocessed1) + (List.length unprocessed2)
//      if totalUnprocLen = 0 then
//        newEnv2
//      elif totalUnprocLen < oldLen then
//        ___RSU_until_fixpoint unprocessed1 unprocessed2 newEnv2
//      else
//        failwith "cannot resolve all sets in Set#UnionOne/Set#Union"
//    // finally, just invoke the fixpoint function for UnionOne and Union tuples
//    let t_union_one = Seq.toList (model.MkFunc("Set#UnionOne", 2).Apps)
//    let t_union = Seq.toList (model.MkFunc("Set#Union", 2).Apps)
//    let newEnv = ___RSU_until_fixpoint t_union_one t_union envMap
//    (newEnv,ctx)
//
//  let f_set_empty = model.MkFunc("Set#Empty", 1)    
//  (envMap,ctx) |> __ReadSetEmpty (List.ofSeq f_set_empty.Apps)
//               |> __ReadSetUnions

//  ======================================================
/// Reads staff about the null constant from a given model 
/// and adds it to the given "envMap" map and "ctx" set. 
//  ======================================================
let ReadNull (model: Microsoft.Boogie.Model) (envMap,ctx) = 
  let f_null = model.MkFunc("null", 0)
  assert (f_null.AppCount = 1)
  let e = (f_null.Apps |> Seq.nth 0).Result
  let newEnv = envMap |> Map.add (GetLoc e) NullConst
  (newEnv,ctx)
  
//  ============================================================================================
/// Reads the evinronment map and the context set.
///
/// It starts by reading the model for the "dtype" function to discover all objects on the heap, 
/// and then proceeds by reading stuff about the null constant, about sequences, and about sets.
//  ============================================================================================
let ReadEnv (model: Microsoft.Boogie.Model) prog = 
  let f_dtype = model.MkFunc("dtype", 1)
  let refs = f_dtype.Apps |> Seq.choose (fun ft -> Some(ft.Args.[0]))
  let envMap = f_dtype.Apps |> Seq.fold (fun acc ft -> 
                                           let locName = GetRefName ft.Args.[0]
                                           let elemName = GetElemFullName ft.Args.[0]
                                           let loc = Unresolved(locName)
                                           let locType = GetType ft.Result prog
                                           let value = match elemName with
                                                       | Some(n) when n.StartsWith("this") -> ThisConst(locName.Replace("*", ""), locType)
                                                       | _                                 -> NewObj(locName.Replace("*", ""), locType)
                                           acc |> Map.add loc value
                                        ) Map.empty
  (envMap, Set.ofList([])) |> ReadNull model
                           |> ReadSeq model 
                           |> ReadSet model

let ReadFieldValuesFromModel (model: Microsoft.Boogie.Model) prog comp meth =
  let heap = ReadHeap model prog
  let env0,ctx = ReadEnv model prog
  let env = env0 |> Utils.MapAddAll (ReadArgValues model (GetMethodArgs meth))
  heap,env,ctx