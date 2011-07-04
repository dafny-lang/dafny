/// Utility functions for manipulating AST elements
///
/// author: Aleksandar Milicevic (t-alekm@microsoft.com)

module AstUtils

open Ast

/// Returns a binary AND of the two given expressions with short-circuiting
let BinaryAnd (lhs: Expr) (rhs: Expr) = 
    match lhs, rhs with
    | IdLiteral("true"), _  -> rhs
    | IdLiteral("false"), _ -> IdLiteral("false")
    | _, IdLiteral("true")  -> lhs
    | _, IdLiteral("false") -> IdLiteral("false")
    | _, _                  -> BinaryExpr(30, "&&", lhs, rhs)

/// Returns a binary OR of the two given expressions with short-circuiting
let BinaryOr (lhs: Expr) (rhs: Expr) = 
    match lhs, rhs with
    | IdLiteral("true"), _  -> IdLiteral("true")
    | IdLiteral("false"), _ -> rhs
    | _, IdLiteral("true")  -> IdLiteral("true")
    | _, IdLiteral("false") -> lhs
    | _, _                  -> BinaryExpr(30, "||", lhs, rhs)

/// Returns a binary IMPLIES of the two given expressions (TODO: with short-circuiting)
let BinaryImplies lhs rhs = BinaryExpr(20, "==>", lhs, rhs)

/// Returns a binary NEQ of the two given expressions
let BinaryNeq lhs rhs = BinaryExpr(40, "!=", lhs, rhs)

/// Returns TRUE literal
let TrueLiteral = IdLiteral("true")
/// Returns FALSE literal
let FalseLiteral = IdLiteral("false")

/// Splits "expr" into a list of its conjuncts
let rec SplitIntoConjunts expr = 
  match expr with
  | IdLiteral("true") -> []
  | BinaryExpr(_,"&&",e0,e1) -> List.concat [SplitIntoConjunts e0 ; SplitIntoConjunts e1]
  | _ -> [expr]

/// Applies "f" to each conjunct of "expr"
let rec ForeachConjunct f expr =
  SplitIntoConjunts expr |> List.fold (fun acc e -> acc + (f e)) ""

// --- search functions ---
                     
/// Out of all "members" returns only those that are "Field"s                                               
let FilterFieldMembers members =
  members |> List.choose (function Field(vd) -> Some(vd) | _ -> None)

/// Out of all "members" returns only those that are constructors
let FilterConstructorMembers members = 
  members |> List.choose (function Method(_,_,_,_, true) as m -> Some(m) | _ -> None)

/// Out of all "members" returns only those that are "Method"s
let FilterMethodMembers members = 
  members |> List.choose (function Method(_,_,_,_,_) as m -> Some(m) | _ -> None)

/// Returns all members of the program "prog" that pass the filter "filter"
let FilterMembers prog filter = 
  match prog with
  | Program(components) ->
      components |> List.fold (fun acc comp -> 
        match comp with
        | Component(Class(_,_,members),_,_) -> List.concat [acc ; members |> filter |> List.choose (fun m -> Some(comp, m))]            
        | _ -> acc) []

/// Returns all fields of a component
let GetAllFields comp = 
  match comp with
  | Component(Class(_,_,members), Model(_,_,cVars,_,_), _) ->
      let aVars = FilterFieldMembers members
      List.concat [aVars ; cVars]
  | _ -> []
                    
/// Returns the class name of a component                              
let GetClassName comp =
  match comp with
  | Component(Class(name,_,_),_,_) -> name
  | _ -> failwith ("unrecognized component: " + comp.ToString())

/// Returns the name of a method
let GetMethodName mthd = 
  match mthd with
  | Method(name,_,_,_,_) -> name
  | _ -> failwith ("not a method: " + mthd.ToString())

/// Returns all invariants of a component as a list of expressions
let GetInvariantsAsList comp = 
  match comp with
  | Component(Class(_,_,members), Model(_,_,_,_,inv), _) -> 
      let clsInvs = members |> List.choose (function Invariant(exprList) -> Some(exprList) | _ -> None) |> List.concat
      List.append (SplitIntoConjunts inv) clsInvs
  | _ -> failwith ("unexpected kinf of component: %s" + comp.ToString())

/// Returns all members of a component
let GetMembers comp =
  match comp with
  | Component(Class(_,_,members),_,_) -> members
  | _ -> failwith ("unrecognized component: " + comp.ToString())

/// Finds a component of a program that has a given name
let FindComponent (prog: Program) clsName = 
  match prog with
  | Program(comps) -> comps |> List.filter (function Component(Class(name,_,_),_,_) when name = clsName -> true | _ -> false)
                            |> Utils.ListToOption

/// Finds a method of a component that has a given name
let FindMethod comp methodName =
  GetMembers comp |> FilterMethodMembers |> List.filter (function Method(name,_,_,_,_) when name = methodName -> true | _ -> false)
                                         |> Utils.ListToOption

/// Finds a field of a class that has a given name
let FindVar (prog: Program) clsName fldName =
  let copt = FindComponent prog clsName
  match copt with
  | Some(comp) -> 
      GetAllFields comp |> List.filter (function Var(name,_) when name = fldName -> true | _ -> false)
                        |> Utils.ListToOption
  | None -> None