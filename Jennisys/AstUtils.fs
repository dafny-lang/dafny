module AstUtils

open Ast

let BinaryAnd (lhs: Expr) (rhs: Expr) = 
    match lhs, rhs with
    | IdLiteral("true"), _  -> rhs
    | IdLiteral("false"), _ -> IdLiteral("false")
    | _, IdLiteral("true")  -> lhs
    | _, IdLiteral("false") -> IdLiteral("false")
    | _, _                  -> BinaryExpr(30, "&&", lhs, rhs)

let BinaryOr (lhs: Expr) (rhs: Expr) = 
    match lhs, rhs with
    | IdLiteral("true"), _  -> IdLiteral("true")
    | IdLiteral("false"), _ -> rhs
    | _, IdLiteral("true")  -> IdLiteral("true")
    | _, IdLiteral("false") -> lhs
    | _, _                  -> BinaryExpr(30, "||", lhs, rhs)

let BinaryImplies lhs rhs = BinaryExpr(20, "==>", lhs, rhs)

let BinaryNeq lhs rhs = BinaryExpr(40, "!=", lhs, rhs)

let TrueLiteral = IdLiteral("true")
let FalseLiteral = IdLiteral("false")

// --- search functions ---
                                               
let FilterFieldMembers members =
  members |> List.choose (function Field(vd) -> Some(vd) | _ -> None)

let FilterConstructorMembers members = 
  members |> List.choose (function Constructor(_,_,_,_) as m -> Some(m) | _ -> None)

let FilterMethodMembers members = 
  members |> List.choose (function Method(_,_,_,_) as m -> Some(m) | _ -> None)

let Methods prog = 
  match prog with
  | Program(components) ->
      components |> List.fold (fun acc comp -> 
        match comp with
        | Component(Class(_,_,members),_,_) -> List.concat [acc ; members |> List.choose (fun m -> Some(comp, m))]            
        | _ -> acc) []

let AllFields c = 
  match c with
  | Component(Class(_,_,members), Model(_,_,cVars,_,_), _) ->
      let aVars = FilterFieldMembers members
      List.concat [aVars ; cVars]
  | _ -> []

let GetClassName comp =
  match comp with
  | Component(Class(name,_,_),_,_) -> name
  | _ -> failwith ("unrecognized component: " + comp.ToString())

let FindComponent (prog: Program) clsName = 
  match prog with
  | Program(comps) -> comps |> List.filter (function Component(Class(name,_,_),_,_) when name = clsName -> true | _ -> false)
                            |> Utils.ListToOption

let FindVar (prog: Program) clsName fldName =
  let copt = FindComponent prog clsName
  match copt with
  | Some(comp) -> 
      AllFields comp |> List.filter (function Var(name,_) when name = fldName -> true | _ -> false)
                     |> Utils.ListToOption
  | None -> None