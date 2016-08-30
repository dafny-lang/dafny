module Getters

open Ast

let RenameToOld name = 
  "old_" + name

let RenameFromOld (name: string) = 
  if name.StartsWith("old_") then
    name.Substring(4)
  else
    name

// --- search functions ---

//  ==================================
/// Returns variable name
//  ==================================
let GetVarName var =
  match var with
  | Var(name,_,_) -> name

let GetExtVarName var = 
  match var with
  | Var(id, _, false) -> id
  | Var(id, _, true) -> RenameToOld id

let IsOldVar var =
  match var with
  | Var(_,_,isOld) -> isOld

//  ==================================
/// Returns variable type
//  ==================================
let GetVarType var = 
  match var with
  | Var(_,t,_) -> t

//  ===============================================
/// Returns whether there exists a variable 
/// in a given VarDecl list with a given name (id)
//  ===============================================
let IsInVarList varLst id = 
  varLst |> List.exists (fun var -> GetVarName var = id)

                     
//  =========================================================
/// Out of all "members" returns only those that are "Field"s                                               
//  =========================================================
let FilterFieldMembers members =
  members |> List.choose (function Field(vd) -> Some(vd) | _ -> None)

//  =============================================================
/// Out of all "members" returns only those that are constructors
//  =============================================================
let FilterConstructorMembers members = 
  members |> List.choose (function Method(_,_,_,_, true) as m -> Some(m) | _ -> None)

//  =============================================================
/// Out of all "members" returns only those that are 
/// constructors and have at least one input parameter
//  =============================================================
let FilterConstructorMembersWithParams members = 
  members |> List.choose (function Method(_,Sig(ins,outs),_,_, true) as m when not (List.isEmpty ins) -> Some(m) | _ -> None)

//  ==========================================================
/// Out of all "members" returns only those that are "Method"s
//  ==========================================================
let FilterMethodMembers members = 
  members |> List.choose (function Method(_,_,_,_,_) as m -> Some(m) | _ -> None)

//  =======================================================================
/// Returns all members of the program "prog" that pass the filter "filter"
//  =======================================================================
let FilterMembers prog filter = 
  match prog with
  | Program(components) ->
      components |> List.fold (fun acc comp -> 
        match comp with
        | Component(Interface(_,_,members),_,_) -> List.concat [acc ; members |> filter |> List.choose (fun m -> Some(comp, m))]            
        | _ -> acc) []

let GetAbstractFields comp = 
  match comp with 
  | Component(Interface(_,_,members), _, _) -> FilterFieldMembers members
  | _ -> failwithf "internal error: invalid component: %O" comp
    
let GetConcreteFields comp = 
  match comp with 
  | Component(_, DataModel(_,_,cVars,_,_), _) -> cVars
  | _ -> failwithf "internal error: invalid component: %O" comp
     
//  =================================
/// Returns all fields of a component
//  =================================
let GetAllFields comp = 
  List.concat [GetAbstractFields comp; GetConcreteFields comp]
    
//  ===========================================================
/// Returns a map (Type |--> Set<Var>) where all 
/// the given fields are grouped by their type
///
/// ensures: forall v :: v in ret.values.elems ==> v in fields
/// ensures: forall k :: k in ret.keys ==> 
///            forall v1, v2 :: v1, v2 in ret[k].elems ==> 
///              v1.type = v2.type
//  ===========================================================
let rec GroupFieldsByType fields = 
  match fields with
  | Var(name, ty, old) :: rest -> 
      let map = GroupFieldsByType rest
      let fldSet = Map.tryFind ty map |> Utils.ExtractOptionOr Set.empty
      map |> Map.add ty (fldSet |> Set.add (Var(name, ty, old)))
  | [] -> Map.empty
 
let IsConcreteField comp fldName = GetConcreteFields comp |> List.exists (fun var -> GetVarName var = fldName)
let IsAbstractField comp fldName = GetAbstractFields comp |> List.exists (fun var -> GetVarName var = fldName)
                    
//  =================================
/// Returns class name of a component
//  =================================
let GetClassName comp =
  match comp with
  | Component(Interface(name,_,_),_,_) -> name
  | _ -> failwith ("unrecognized component: " + comp.ToString())

let GetClassType comp = 
  match comp with
  | Component(Interface(name,typeParams,_),_,_) -> NamedType(name, typeParams)
  | _ -> failwith ("unrecognized component: " + comp.ToString())

//  ========================
/// Returns name of a method
//  ========================
let GetMethodName mthd = 
  match mthd with
  | Method(name,_,_,_,_) -> name
  | _ -> failwith ("not a method: " + mthd.ToString())

//  ===========================================================
/// Returns full name of a method (= <class_name>.<method_name>
//  ===========================================================
let GetMethodFullName comp mthd = 
  (GetClassName comp) + "." + (GetMethodName mthd)

//  =============================
/// Returns signature of a method
//  =============================
let GetMethodSig mthd = 
  match mthd with
  | Method(_,sgn,_,_,_) -> sgn
  | _ -> failwith ("not a method: " + mthd.ToString())

//  =========================================================
/// Returns all arguments of a method (both input and output)
//  =========================================================
let GetSigVars sign = 
  match sign with
  | Sig(ins, outs) -> List.concat [ins; outs]

let GetMethodInArgs mthd = 
  match mthd with
  | Method(_,Sig(ins, _),_,_,_) -> ins
  | _ -> failwith ("not a method: " + mthd.ToString())

let GetMethodOutArgs mthd = 
  match mthd with
  | Method(_,Sig(_, outs),_,_,_) -> outs
  | _ -> failwith ("not a method: " + mthd.ToString())

let GetMethodArgs mthd = 
  let ins = GetMethodInArgs mthd
  let outs = GetMethodOutArgs mthd
  List.concat [ins; outs]

let IsConstructor mthd = 
  match mthd with
  | Method(_,_,_,_,isConstr) -> isConstr
  | _ -> failwithf "expected a method but got %O" mthd

let rec GetTypeShortName ty =
  match ty with
  | IntType -> "int"
  | BoolType -> "bool"
  | SetType(_) -> "set"
  | SeqType(_) -> "seq"
  | NamedType(n,_) | InstantiatedType(n,_) -> n

//  ==================================
/// Returns component name
//  ==================================
let GetComponentName comp = 
  match comp with
  | Component(Interface(name,_,_),_,_) -> name
  | _ -> failwithf "invalid component %O" comp

let GetComponentTypeParameters comp = 
  match comp with
  | Component(Interface(_,tp,_),_,_) -> tp
  | _ -> failwithf "invalid component %O" comp


//  ==================================
/// Returns all members of a component
//  ==================================
let GetMembers comp =
  match comp with
  | Component(Interface(_,_,members),_,_) -> members
  | _ -> failwith ("unrecognized component: " + comp.ToString())

//  ====================================================
/// Finds a component of a program that has a given name
//  ====================================================
let FindComponent (prog: Program) clsName = 
  match prog with
  | Program(comps) -> comps |> List.filter (function Component(Interface(name,_,_),_,_) when name = clsName -> true | _ -> false)
                            |> Utils.ListToOption

let FindComponentForType prog ty = 
  FindComponent prog (GetTypeShortName ty)

let FindComponentForTypeOpt prog tyOpt = 
  match tyOpt with
  | Some(ty) -> FindComponentForType prog ty
  | None -> None

let CheckSameCompType comp ty = 
  GetComponentName comp = GetTypeShortName ty

let GetComponentType comp = 
  NamedType(GetComponentName comp, GetComponentTypeParameters comp)

//  ===================================================
/// Finds a method of a component that has a given name
//  ===================================================
let FindMethod comp methodName =
  let x = GetMembers comp
  let y = x |> FilterMethodMembers
  let z = y |> List.filter (function Method(name,_,_,_,_) when name = methodName -> true | _ -> false)
  GetMembers comp |> FilterMethodMembers |> List.filter (function Method(name,_,_,_,_) when name = methodName -> true | _ -> false)
                                         |> Utils.ListToOption

//  ==============================================
/// Finds a field of a class that has a given name
//  ==============================================
//let FindCompVar prog clsName fldName =
//  let copt = FindComponent prog clsName
//  match copt with
//  | Some(comp) -> 
//      GetAllFields comp |> List.filter (function Var(name,_) when name = fldName -> true | _ -> false)
//                        |> Utils.ListToOption
//  | None -> None

let FindVar comp fldName =
  GetAllFields comp |> List.filter (fun var -> GetVarName var = fldName)
                    |> Utils.ListToOption

//  ======================================
/// Returns the frame of a given component
//  ======================================
let GetFrame comp = 
  match comp with 
  | Component(_, DataModel(_,_,_,frame,_), _) -> frame
  | _ -> failwithf "not a valid component %O" comp

let GetFrameFields comp =
  let frame = GetFrame comp
  frame |> List.choose (function IdLiteral(name) -> Some(name) | _ -> None) // TODO: is it really enough to handle only IdLiteral's
        |> List.choose (fun varName -> 
                          let v = FindVar comp varName
                          Utils.ExtractOptionMsg ("field not found: " + varName) v |> ignore
                          v
                       )

//  ==============================================
/// Checks whether two given methods are the same.
///
/// Methods are the same if their names are the 
/// same and their components have the same name.
//  ==============================================
let CheckSameMethods (c1,m1) (c2,m2) = 
  GetComponentName c1 = GetComponentName c2 && GetMethodName m1 = GetMethodName m2

////////////////////////