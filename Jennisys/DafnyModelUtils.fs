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

let GetType (e: Model.Element) = 
  let fNameOpt = GetElemFullName e
  match fNameOpt with
  | Some(fname) -> match fname with
                   | Exact "intType" _       -> Some(IntType)
                   | Prefix "class." clsName -> Some(NamedType(clsName))
                   | _ -> None
  | None -> None

let GetLoc (e: Model.Element) =
  Unresolved(GetRefName e)

let GetSeqFromEnv env key = 
  match Map.find key env with
  | SeqConst(lst) -> lst
  | _ as x-> failwith ("not a SeqConst but: " + x.ToString())
                                   
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
      | Some(c1), Some(c2) -> UpdateContext rest1 rest2 (AddConstr c1 c2 ctx)
      | _ -> UpdateContext rest1 rest2 ctx
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

let rec ReadSeqLen (model: Microsoft.Boogie.Model) (len_tuples: Model.FuncTuple list) (envMap,ctx) =
  match len_tuples with
  | ft :: rest -> 
      let len = GetInt ft.Result
      let emptyList = Utils.GenList len
      let newMap = envMap |> Map.add (GetLoc ft.Args.[0]) (SeqConst(emptyList))
      ReadSeqLen model rest (newMap,ctx)
  | _ -> (envMap,ctx)

let rec ReadSeqIndex (model: Microsoft.Boogie.Model) (idx_tuples: Model.FuncTuple list) (envMap,ctx) = 
  match idx_tuples with
  | ft :: rest -> 
      let srcLstKey = GetLoc ft.Args.[0]
      let oldLst = GetSeqFromEnv envMap srcLstKey
      let idx = GetInt ft.Args.[1]
      let lstElem = UnboxIfNeeded model ft.Result
      let newLst = Utils.ListSet idx (Some(lstElem)) oldLst
      let newCtx = UpdateContext oldLst newLst ctx
      let newEnv = envMap |> Map.add srcLstKey (SeqConst(newLst))
      ReadSeqIndex model rest (newEnv,newCtx)
  | _ -> (envMap,ctx)

let rec ReadSeqBuild (model: Microsoft.Boogie.Model) (bld_tuples: Model.FuncTuple list) (envMap,ctx) = 
  match bld_tuples with
  | ft :: rest -> 
      let srcLstLoc = GetLoc ft.Args.[0]
      let dstLstLoc = GetLoc ft.Result
      let oldLst = GetSeqFromEnv envMap srcLstLoc
      let idx = GetInt ft.Args.[1]
      let lstElemVal = UnboxIfNeeded model ft.Args.[2]
      let dstLst = GetSeqFromEnv envMap dstLstLoc
      let newLst = Utils.ListBuild oldLst idx (Some(lstElemVal)) dstLst
      let newCtx = UpdateContext dstLst newLst ctx
      let newEnv = envMap |> Map.add dstLstLoc (SeqConst(newLst))
      ReadSeqBuild model rest (newEnv,newCtx)
  | _ -> (envMap,ctx)

let rec ReadSeqAppend (model: Microsoft.Boogie.Model) (app_tuples: Model.FuncTuple list) (envMap,ctx) = 
  match app_tuples with
  | ft :: rest -> 
      let srcLst1Loc = GetLoc ft.Args.[0]
      let srcLst2Loc = GetLoc ft.Args.[1]
      let dstLstLoc = GetLoc ft.Result
      let oldLst1 = GetSeqFromEnv envMap srcLst1Loc
      let oldLst2 = GetSeqFromEnv envMap srcLst2Loc
      let dstLst = GetSeqFromEnv envMap dstLstLoc
      let newLst = List.append oldLst1 oldLst2
      let newCtx = UpdateContext dstLst newLst ctx
      let newEnv = envMap |> Map.add dstLstLoc (SeqConst(newLst))
      ReadSeqAppend model rest (newEnv,newCtx)
  | _ -> (envMap,ctx)

let ReadSeq (model: Microsoft.Boogie.Model) (envMap,ctx) =
  let f_seq_len = model.MkFunc("Seq#Length", 1)
  let f_seq_idx = model.MkFunc("Seq#Index", 2)
  let f_seq_bld = model.MkFunc("Seq#Build", 4)
  let f_seq_app = model.MkFunc("Seq#Append", 2)
  (envMap,ctx) |> ReadSeqLen model (List.ofSeq f_seq_len.Apps)
               |> ReadSeqIndex model (List.ofSeq f_seq_idx.Apps)
               |> ReadSeqBuild model (List.ofSeq f_seq_bld.Apps)
               |> ReadSeqAppend model (List.ofSeq f_seq_app.Apps)


let ReadSet (model: Microsoft.Boogie.Model) (envMap,ctx) =
  (envMap,ctx)

let ReadNull (model: Microsoft.Boogie.Model) (envMap,ctx) = 
  let f_null = model.MkFunc("null", 0)
  assert (f_null.AppCount = 1)
  let e = (f_null.Apps |> Seq.nth 0).Result
  let newEnv = envMap |> Map.add (GetLoc e) NullConst
  (newEnv,ctx)
  
let ReadEnv (model: Microsoft.Boogie.Model) = 
  let f_dtype = model.MkFunc("dtype", 1)
  let refs = f_dtype.Apps |> Seq.choose (fun ft -> Some(ft.Args.[0]))
  let envMap = f_dtype.Apps |> Seq.fold (fun acc ft -> 
                                           let locName = GetRefName ft.Args.[0]
                                           let elemName = GetElemFullName ft.Args.[0]
                                           let loc = Unresolved(locName)
                                           let locType = GetType ft.Result
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
  let env,ctx = ReadEnv model
  heap,env,ctx