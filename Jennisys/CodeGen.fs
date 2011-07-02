module CodeGen

open Ast
open AstUtils
open Utils
open Printer   
open TypeChecker
open DafnyPrinter

let numLoopUnrolls = 2

let rec GetUnrolledFieldValidExpr fldExpr fldName validFunName numUnrolls : Expr = 
  if numUnrolls = 0 then
    TrueLiteral
  else
    BinaryImplies (BinaryNeq fldExpr (IdLiteral("null")))
                  (BinaryAnd (Dot(fldExpr, validFunName))
                             (GetUnrolledFieldValidExpr (Dot(fldExpr, fldName)) fldName validFunName (numUnrolls-1)))

let GetFieldValidExpr fldName validFunName numUnrolls : Expr = 
  GetUnrolledFieldValidExpr (IdLiteral(fldName)) fldName validFunName numUnrolls
  //BinaryImplies (BinaryNeq (IdLiteral(fldName)) (IdLiteral("null"))) (Dot(IdLiteral(fldName), validFunName))

let GetFieldsForValidExpr allFields prog : VarDecl list =
  allFields |> List.filter (function Var(name, tp) when IsUserType prog tp -> true
                                     | _                                   -> false)

let GetFieldsValidExprList clsName allFields prog : Expr list =
  let fields = GetFieldsForValidExpr allFields prog
  fields |> List.map (function Var(name, t) -> 
                                 let validFunName, numUnrolls = 
                                   match t with
                                   | Some(ty) when clsName = (PrintType ty) -> "Valid_self()", numLoopUnrolls
                                   | _ -> "Valid()", 1
                                 GetFieldValidExpr name validFunName numUnrolls
                     )

let PrintValidFunctionCode clsName clsMembers modelInv vars prog : string = 
  let invMembers = clsMembers |> List.filter (function Invariant(_) -> true | _ -> false)
  let clsInvs = invMembers |> List.choose (function Invariant(exprList) -> Some(exprList) | _ -> None) |> List.concat
  let allInvs = modelInv :: clsInvs
  let fieldsValid = GetFieldsValidExprList clsName vars prog
  let idt = "    "
  let PrintInvs invs = 
    invs |> List.fold (fun acc e -> List.concat [acc ; SplitIntoConjunts e]) []
         |> PrintSep (" &&" + newline) (fun e -> sprintf "%s(%s)" idt (PrintExpr 0 e))
         |> fun s -> if s = "" then (idt + "true") else s
  // TODO: don't hardcode decr vars!!!
//  let decrVars = if List.choose (function Var(n,_) -> Some(n)) vars |> List.exists (fun n -> n = "next") then
//                   ["list"]
//                 else
//                   []
//  (if List.isEmpty decrVars then "" else sprintf "    decreases %s;%s" (PrintSep ", " (fun a -> a) decrVars) newline) +
  "  function Valid_self(): bool" + newline +
  "    reads *;" + newline +
  "  {" + newline + 
  (PrintInvs allInvs) + newline +
  "  }" + newline +
  newline +
  "  function Valid(): bool" + newline +
  "    reads *;" + newline +
  "  {" + newline + 
  "    this.Valid_self() &&" + newline +
  (PrintInvs fieldsValid) + newline +
  "  }" + newline

let PrintDafnyCodeSkeleton prog methodPrinterFunc: string =
  match prog with
  | Program(components) -> components |> List.fold (fun acc comp -> 
      match comp with  
      | Component(Class(name,typeParams,members), Model(_,_,cVars,frame,inv), code) ->
        let aVars = FilterFieldMembers members
        let allVars = List.concat [aVars ; cVars];
        let compMethods = FilterConstructorMembers members
        // Now print it as a Dafny program
        acc + 
        (sprintf "class %s%s {" name (PrintTypeParams typeParams)) + newline +       
        // the fields: original abstract fields plus concrete fields
        (sprintf "%s" (PrintFields aVars 2 true)) + newline +     
        (sprintf "%s" (PrintFields cVars 2 false)) + newline +                           
        // generate the Valid function
        (sprintf "%s" (PrintValidFunctionCode name members inv allVars prog)) + newline +
        // call the method printer function on all methods of this component
        (compMethods |> List.fold (fun acc m -> acc + (methodPrinterFunc comp m)) "") +
        // the end of the class
        "}" + newline + newline
      | _ -> assert false; "") ""
  
let PrintAllocNewObjects (heap,env,ctx) indent = 
  let idt = Indent indent
  env |> Map.fold (fun acc l v ->
                     match v with 
                     | NewObj(_,_) -> acc |> Set.add v
                     | _ -> acc
                  ) Set.empty
      |> Set.fold (fun acc newObjConst ->
                    match newObjConst with
                    | NewObj(name, Some(tp)) -> acc + (sprintf "%svar %s := new %s;%s" idt (PrintGenSym name) (PrintType tp) newline)
                    | _ -> failwith ("NewObj doesn't have a type: " + newObjConst.ToString())
                  ) ""

let PrintObjRefName o (env,ctx) = 
  match Resolve o (env,ctx) with
  | ThisConst(_,_) -> "this";
  | NewObj(name, _) -> PrintGenSym name
  | _ -> failwith ("unresolved object ref: " + o.ToString())

let PrintVarAssignments (heap,env,ctx) indent = 
  let idt = Indent indent
  heap |> Map.fold (fun acc (o,f) l ->
                      let objRef = PrintObjRefName o (env,ctx)
                      let fldName = PrintVarName f
                      let value = Resolve l (env,ctx) |> PrintConst
                      acc + (sprintf "%s%s.%s := %s;" idt objRef fldName value) + newline
                   ) ""

let PrintHeapCreationCode (heap,env,ctx) indent = 
  (PrintAllocNewObjects (heap,env,ctx) indent) +
  (PrintVarAssignments (heap,env,ctx) indent)

let GenConstructorCode mthd body =
  printfn "Printing code for method %s." (GetMethodName mthd)
  match mthd with
  | Method(methodName, sign, pre, post, _) -> 
      "  method " + methodName + (PrintSig sign) + newline +
      "    modifies this;" + newline +
      "    requires " + (PrintExpr 0 pre) + ";" + newline +
      "    ensures " + (PrintExpr 0 post) + ";" + newline + 
      "    ensures Valid(); " + newline +
      "  {" + newline + 
      body + 
      "  }" + newline
  | _ -> ""

// NOTE: insert here coto to say which methods to analyze
let GetMethodsToAnalyze prog =
  let c = FindComponent prog "IntList" |> Utils.ExtractOption
  let m = FindMethod c "OneTwo" |> Utils.ExtractOption
  [c, m]
  //FilterMembers prog FilterConstructorMembers

// solutions: (comp, constructor) |--> (heap, env, ctx) 
let PrintImplCode prog solutions =
  let methods = GetMethodsToAnalyze prog
  PrintDafnyCodeSkeleton prog (fun comp mthd ->
                                 if Utils.ListContains (comp,mthd) methods  then
                                   let mthdBody = match Map.tryFind (comp,mthd) solutions with
                                                  | Some(heap,env,ctx) -> PrintHeapCreationCode (heap,env,ctx) 4
                                                  | _ -> "    //unable to synthesize" + newline
                                   (GenConstructorCode mthd mthdBody) + newline
                                 else
                                   ""
                              )