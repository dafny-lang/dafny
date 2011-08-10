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

type AssignmentType = 
  | FieldAssignment of (Obj * VarDecl) * Expr // the first string is the symbolic name of an object literal
  | ArbitraryStatement of Stmt

type HeapInstance = {
   objs: Map<string, Obj>;
   assignments: AssignmentType list
   methodArgs: Map<string, Const>;
   methodRetVals: Map<string, Expr>;
   globals: Map<string, Expr>;
}

let NoObj = { name = ""; objType = NamedType("", []) }

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
  ResolveCont hModel (fun c _ -> 
                        match c with
                        | Unresolved(id) -> BoxConst(id)
                        | _ -> failwithf "internal error: expected Unresolved but got %O" c
                     ) cst //fun c _ -> raise (ConstResolveFailed("failed to resolve " + c.ToString()))
 
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
              match heapInst.methodArgs |> Map.tryFind id with
              | Some(argValue) -> argValue |> Const2Expr
              | None -> 
                  match heapInst.methodRetVals |> Map.tryFind id with
                  | Some(e) -> e
                  | None -> raise (EvalFailed("cannot find value for method parameter " + id))              
          | IdLiteral(id) ->
              let globalVal = heapInst.globals |> Map.tryFind id
              match globalVal with
              | Some(e) -> e
              | None -> __EvalResolver ThisLiteral (Some(id))      
          | _ -> raise (EvalFailed(sprintf "I'm not supposed to resolve %O" expr))
      | Some(fldName) -> 
          match expr with
          | ObjLiteral(objName) -> 
              let h2 = heapInst.assignments |> List.filter (function FieldAssignment((o, Var(varName,_)), v) -> o.name = objName && varName = fldName | _ -> false)
              match h2 with
              | FieldAssignment((_,_),x) :: [] -> x
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
let ResolveModel hModel outArgs = 
  let hmap = hModel.heap |> Map.fold (fun acc (o,f) l ->
                                        let objName, objTypeOpt = match Resolve hModel o with
                                                                  | ThisConst(_,t) -> "this", t;
                                                                  | NewObj(name, t) -> PrintGenSym name, t
                                                                  | _ -> failwith ("unresolved object ref: " + o.ToString())
                                        let objType = objTypeOpt |> Utils.ExtractOptionMsg "unknown object type"
                                        let obj = {name = objName; objType = objType}
                                        let value = TryResolve hModel l |> Const2Expr
                                        Utils.ListMapAdd (obj, f) value acc 
                                     ) []
                         |> List.map (fun el -> FieldAssignment(el))
  let objs = hmap |> List.fold (fun acc asgn -> 
                                  match asgn with
                                  | FieldAssignment((obj,_),_) -> acc |> Map.add obj.name obj
                                  | _ -> acc) Map.empty
  let argmap, retvals = hModel.env |> Map.fold (fun (acc1,acc2) k v -> 
                                                  match k with
                                                  | VarConst(name) -> 
                                                      if outArgs |> List.exists (function Var(varName, _) -> varName = name) then
                                                        acc1, acc2 |> Map.add name (Resolve hModel v |> Const2Expr)
                                                      else
                                                        acc1 |> Map.add name (Resolve hModel v), acc2
                                                  | _ -> acc1, acc2
                                               ) (Map.empty, Map.empty)
  { objs          = objs;
    assignments   = hmap; 
    methodArgs    = argmap; 
    methodRetVals = retvals;
    globals       = Map.empty }

let rec GetCallGraph solutions graph = 
  let rec __SearchExprsForMethodCalls elist acc = 
    match elist with
    | e :: rest ->
        match e with 
        // no need to descend for, just check if the top-level one is MEthodCall
        | MethodCall(_,cname,mname,_) -> __SearchExprsForMethodCalls rest (acc |> Set.add (cname,mname))
        | _ -> __SearchExprsForMethodCalls rest acc 
    | [] -> acc
  match solutions with
  | ((comp,m), sol) :: rest -> 
        let callees = sol |> List.fold (fun acc (cond, hInst) ->
                                          hInst.assignments |> List.fold (fun acc asgn -> 
                                                                            match asgn with
                                                                            | FieldAssignment(_,e) ->
                                                                                __SearchExprsForMethodCalls [e] acc
                                                                            | ArbitraryStatement(stmt) -> 
                                                                                let exprs = ExtractTopLevelExpressions stmt
                                                                                __SearchExprsForMethodCalls exprs acc
                                                                         ) acc
                                       ) Set.empty
        let graph' = graph |> Map.add (comp,m) callees
        GetCallGraph rest graph'
  | [] -> graph