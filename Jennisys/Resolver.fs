//  ####################################################################
///   Utilities for resolving the "Unresolved" constants with respect to 
///   a given context (heap/env/ctx)
///
///   author: Aleksandar Milicevic (t-alekm@microsoft.com)
//  ####################################################################

module Resolver

open Ast
open AstUtils 
open Printer
open EnvUtils
open DafnyModelUtils

type Obj = { name: string; objType: Type }

type HeapInstance = {
   assignments: ((Obj * VarDecl) * Expr) list; // the first string is the symbolic name of an object literal
   methodArgs: Map<string, Const>;
   globals: Map<string, Expr>;
}

// resolving values
exception ConstResolveFailed of string
 
//  ================================================================
/// Resolves a given Const (cst) with respect to a given env/ctx. 
///
/// If unable to resolve, it just delegates the task to the
/// failResolver function
//  ================================================================
let rec ResolveCont hModel failResolver cst =
  match cst with
  | Unresolved(_) as u -> 
      // see if it is in the env map first
      let envVal = Map.tryFind cst hModel.env
      match envVal with
      | Some(c) -> ResolveCont hModel failResolver c
      | None -> 
          // not found in the env map --> check the equality sets
          let eq = hModel.ctx |> Set.filter (fun eqSet -> Set.contains u eqSet)
                              |> Utils.SetToOption
          match eq with 
          | Some(eqSet) -> 
              let cOpt = eqSet |> Set.filter (function Unresolved(_) -> false | _ -> true)
                               |> Utils.SetToOption
              match cOpt with 
              | Some(c) -> c
              | _ -> failResolver cst hModel
          | None ->
              // finally, see if it's a method argument
              let m = hModel.env |> Map.filter (fun k v -> v = u && match k with VarConst(name) -> true | _ -> false) |> Map.toList
              match m with 
              | (vc,_) :: [] -> vc
              | _ -> failResolver cst hModel
  | SeqConst(cseq) -> 
      let resolvedLst = cseq |> List.rev |> List.fold (fun acc c -> ResolveCont hModel failResolver c :: acc) []
      SeqConst(resolvedLst)
  | SetConst(cset) ->
      let resolvedSet = cset |> Set.fold (fun acc c -> acc |> Set.add (ResolveCont hModel failResolver c)) Set.empty
      SetConst(resolvedSet)
  | _ -> cst

//  =====================================================================
/// Tries to resolve a given Const (cst) with respect to a given env/ctx. 
///
/// If unable to resolve, just returns the original Unresolved const.
//  =====================================================================
let TryResolve hModel cst = 
  ResolveCont hModel (fun c _ -> c) cst

//  ==============================================================
/// Resolves a given Const (cst) with respect to a given env/ctx. 
///
/// If unable to resolve, raises a ConstResolveFailed exception
//  ==============================================================
let Resolve hModel cst =
  ResolveCont hModel (fun c _ -> raise (ConstResolveFailed("failed to resolve " + c.ToString()))) cst
 
//  ==================================================================
/// Evaluates a given expression with respect to a given heap instance       
//  ==================================================================
let Eval heapInst resolveExprFunc expr = 
  let rec __EvalResolver expr fldNameOpt = 
    if not (resolveExprFunc expr) then
      match fldNameOpt with
      | None -> expr
      | Some(n) -> Dot(expr, n)
    else
      match fldNameOpt with
      | None -> 
          match expr with
          | ObjLiteral("this") | ObjLiteral("null") -> expr
          | IdLiteral("this")  | IdLiteral("null") -> failwith "should never happen anymore" //TODO
          | VarLiteral(id) -> 
              let argValue = heapInst.methodArgs |> Map.tryFind id |> Utils.ExtractOptionMsg ("cannot find value for method parameter " + id)
              argValue |> Const2Expr
          | IdLiteral(id) ->
              let globalVal = heapInst.globals |> Map.tryFind id
              match globalVal with
              | Some(e) -> e
              | None -> __EvalResolver ThisLiteral (Some(id))      
          | _ -> raise (EvalFailed(sprintf "I'm not supposed to resolve %O" expr))
      | Some(fldName) -> 
          match expr with
          | ObjLiteral(objName) -> 
              let h2 = heapInst.assignments |> List.filter (fun ((o, Var(varName,_)), v) -> o.name = objName && varName = fldName)
              match h2 with
              | ((_,_),x) :: [] -> x
              | _ :: _ -> raise (EvalFailed(sprintf "can't evaluate expression deterministically: %s.%s resolves to multiple locations" objName fldName))
              | [] -> raise (EvalFailed(sprintf "can't find value for %s.%s" objName fldName))  // TODO: what if that value doesn't matter for the solution, and that's why it's not present in the model???
          | _ -> Dot(expr, fldName)
  (* --- function body starts here --- *)
  EvalSym __EvalResolver expr

//  =====================================================================
/// Takes an unresolved model of the heap (HeapModel), resolves all 
/// references in the model and returns an instance of the heap 
/// (HeapInstance), where all fields for all objects have explicit 
/// assignments.
//  =====================================================================
let ResolveModel hModel = 
  let hmap = hModel.heap |> Map.fold (fun acc (o,f) l ->
                                        let objName, objType = match Resolve hModel o with
                                                               | ThisConst(_,t) -> "this", t;
                                                               | NewObj(name, t) -> PrintGenSym name, t
                                                               | _ -> failwith ("unresolved object ref: " + o.ToString())
                                        let objType = objType |> Utils.ExtractOptionMsg "unknown object type"
                                        let value = TryResolve hModel l |> Const2Expr
                                        Utils.ListMapAdd ({name = objName; objType = objType}, f) value acc 
                                     ) []
  let argmap = hModel.env |> Map.fold (fun acc k v -> 
                                         match k with
                                         | VarConst(name) -> acc |> Map.add name (Resolve hModel v)
                                         | _ -> acc
                                      ) Map.empty 
  { assignments = hmap; 
    methodArgs  = argmap; 
    globals     = Map.empty }

let rec GetCallGraph solutions graph = 
  match solutions with
  | ((comp,m), sol) :: rest -> 
        let callees = sol |> List.fold (fun acc (cond, hInst) ->
                                          let mcalls = hInst.assignments |> List.choose (fun ((obj,_),e) ->
                                                                                          match e with 
                                                                                          | MethodCall(_,mname,_) -> 
                                                                                              let targetCompName = GetTypeShortName obj.objType
                                                                                              Some(targetCompName, mname)
                                                                                          | _ -> None)
                                          acc |> Set.union (mcalls |> Set.ofList)
                                      ) Set.empty
        let graph' = graph |> Map.add (comp,m) callees
        GetCallGraph rest graph'
  | [] -> graph