//  ####################################################################
///   This module is intended to store and handle configuration options
///
///   author: Aleksandar Milicevic (t-alekm@microsoft.com)
//  ####################################################################

module Options

open Utils

type Config = {
   inputFilename: string;
   methodToSynth: string;
   verifyPartialSolutions: bool;
   verifySolutions: bool;
   checkUnifications: bool;
   genRepr: bool;
   timeout: int;
   numLoopUnrolls: int;
}

let defaultConfig: Config = {
  inputFilename     = "";
  methodToSynth     = "*";
  verifyPartialSolutions = true;
  verifySolutions   = true;
  checkUnifications = false;
  genRepr           = false;
  timeout           = 0;
  numLoopUnrolls    = 2;
}

/// Should not be mutated outside the ParseCmdLineArgs method, which is 
/// typically called only once at the beginning of the program execution 
let mutable CONFIG = defaultConfig

exception InvalidCmdLineArg of string
exception InvalidCmdLineOption of string

let ParseCmdLineArgs args = 
  let __StripSwitches str =
    match str with 
    | Prefix "--" x 
    | Prefix "-" x
    | Prefix "/" x -> x
    | _ -> str

  let __Split (str: string) =
    let stripped = __StripSwitches str
    if stripped = str then
      ("",str) 
    else
      let splits = stripped.Split([| ':' |])
      if splits.Length > 2 then raise (InvalidCmdLineOption("more than 2 colons in " + str))
      if splits.Length = 2 then
        let opt = splits.[0]
        let value = splits.[1]
        (opt,value)
      else
        let x = __StripSwitches splits.[0]
        (x, "")

  let __CheckNonEmpty value optName =
    if value = "" then raise (InvalidCmdLineArg("A value for option " + optName + " must not be empty"))

  let __CheckInt value optName =
    try 
      System.Int32.Parse value
    with 
      | ex -> raise (InvalidCmdLineArg("A value for option " + optName + " must be a boolean"))

  let __CheckBool value optName =
    if value = "" then
      true
    else
      try 
        System.Boolean.Parse value
      with 
        | ex -> raise (InvalidCmdLineArg("A value for option " + optName + " must be an integer"))
               
  let rec __Parse args cfg =
    match args with
    | fs :: rest -> 
        let opt,value = __Split fs
        match opt with
        | "method"    -> 
            __CheckNonEmpty value opt
            __Parse rest { cfg with methodToSynth = value }
        | "verifyParSol" -> 
            let b = __CheckBool value opt
            __Parse rest { cfg with verifyPartialSolutions = b }
        | "noVerifyParSol" -> 
            let b = __CheckBool value opt
            __Parse rest { cfg with verifyPartialSolutions = not b }
        | "verifySol" -> 
            let b = __CheckBool value opt
            __Parse rest { cfg with verifySolutions = b }
        | "noVerifySol" -> 
            let b = __CheckBool value opt
            __Parse rest { cfg with verifySolutions = not b }
        | "checkUnifs" -> 
            let b = __CheckBool value opt
            __Parse rest { cfg with checkUnifications = b }
        | "noCheckUnifs" -> 
            let b = __CheckBool value opt
            __Parse rest { cfg with checkUnifications = not b }
        | "genRepr" -> 
            let b = __CheckBool value opt
            __Parse rest { cfg with genRepr = b }
        | "noGenRepr" -> 
            let b = __CheckBool value opt
            __Parse rest { cfg with genRepr = not b }
        | "timeout" ->
            let t = __CheckInt value opt
            __Parse rest { cfg with timeout = t }
        | "unrolls" ->
            let t = __CheckInt value opt
            __Parse rest { cfg with numLoopUnrolls = t }
        | "" -> 
            __Parse rest { cfg with inputFilename = value }
        | _ -> 
            raise (InvalidCmdLineOption("Unknown option: " + opt))
    | [] -> cfg   
    
  (* --- function body starts here --- *)           
  CONFIG <- __Parse args defaultConfig

