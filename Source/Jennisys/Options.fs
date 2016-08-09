//  ####################################################################
///   This module is intended to store and handle configuration options
///
///   author: Aleksandar Milicevic (t-alekm@microsoft.com)
//  ####################################################################

module Options

open Utils

type Config = {
   help                      : bool;
   inputFilename             : string;
   methodToSynth             : string;
   constructorsOnly          : bool;
   inferConditionals         : bool;
   verifyPartialSolutions    : bool;
   verifySolutions           : bool;
   checkUnifications         : bool;
   genRepr                   : bool;
   genMod                    : bool;
   timeout                   : int;
   numLoopUnrolls            : int;
   recursiveValid            : bool;
   breakIntoDebugger         : bool;
   minimizeGuards            : bool; 
}

type CfgOption<'a> = {
   optionName: string; 
   optionType: string;
   optionSetter: 'a -> Config -> Config;
   descr: string;
}

exception InvalidCmdLineArg of string
exception InvalidCmdLineOption of string
 
let CheckNonEmpty value optName =
  if value = "" then raise (InvalidCmdLineArg("A value for option " + optName + " must not be empty")) else value

let CheckInt value optName =
  try 
    System.Int32.Parse value
  with 
    | ex -> raise (InvalidCmdLineArg("A value for option " + optName + " must be a boolean"))

let CheckBool value optName =
  if value = "" then
    true
  else
    try 
      System.Boolean.Parse value
    with 
      | ex -> raise (InvalidCmdLineArg("A value for option " + optName + " must be an integer"))

let cfgOptions = [
  { optionName = "help";            optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with help                   =      CheckBool v "help"});           descr = "prints out the available switches"; }
  { optionName = "method";          optionType = "string"; optionSetter = (fun v (cfg: Config) -> {cfg with methodToSynth          = CheckNonEmpty v "method"});          descr = "select methods to synthesize; method names are in the form <ClassName>.<MethodName>; multiple methods can be given as a list of comma separated values"; }
  { optionName = "constrOnly";      optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with constructorsOnly       =      CheckBool v "constrOnly"});     descr = "synthesize constructors only"; }
  { optionName = "inferConds";      optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with inferConditionals      =      CheckBool v "inferConds"});     descr = "try to infer conditions"; }
  { optionName = "noInferConds";    optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with inferConditionals      = not (CheckBool v "inferConds")});    descr = "don't try to infer conditions"; }
  { optionName = "verifyParSol";    optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with verifyPartialSolutions =      CheckBool v "verifyParSol"});   descr = "verify partial solutions"; }
  { optionName = "noVerifyParSol";  optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with verifyPartialSolutions = not (CheckBool v "verifyParSol")});  descr = "don't verify partial solutions"; }
  { optionName = "verifySol";       optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with verifySolutions        =      CheckBool v "verifySol"});      descr = "verify final solution"; }
  { optionName = "noVerifySol";     optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with verifySolutions        = not (CheckBool v "verifySol")});     descr = "don't verify final solution"; } 
  { optionName = "checkUnifs";      optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with checkUnifications      =      CheckBool v "checkUnifs"});     descr = "verify unifications"; } 
  { optionName = "noCheckUnifs";    optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with checkUnifications      = not (CheckBool v "noCheckUnifs")});  descr = "don't verify unifications"; }
  { optionName = "genRepr";         optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with genRepr                =      CheckBool v "genRepr"});        descr = "generate Repr field"; }
  { optionName = "noGenRepr";       optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with genRepr                = not (CheckBool v "noGenRepr")});     descr = "don't generate Repr field"; }
  { optionName = "genMod";          optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with genMod                 =      CheckBool v "genMod"});         descr = "generate modular code (delegate to methods)"; }
  { optionName = "noGenMod";        optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with genMod                 = not (CheckBool v "noGenMod")});      descr = "dont generate modular code (delegate to methods)"; }
  { optionName = "timeout";         optionType = "int";    optionSetter = (fun v (cfg: Config) -> {cfg with timeout                =      CheckInt v "timeout"});         descr = "timeout"; }
  { optionName = "unrolls";         optionType = "int";    optionSetter = (fun v (cfg: Config) -> {cfg with numLoopUnrolls         =      CheckInt v "unrolls"});         descr = "number of unrolls of the Valid() function"; }
  { optionName = "recValid";        optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with recursiveValid         =      CheckBool v "recValid"});       descr = "generate recursive Valid() function"; }
  { optionName = "noRecValid";      optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with recursiveValid         = not (CheckBool v "noRecValid")});    descr = "unroll Valid() function"; }
  { optionName = "break";           optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with breakIntoDebugger      =      CheckBool v "break"});          descr = "launches debugger upon start-up"; }
  { optionName = "minGuards";       optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with minimizeGuards         =      CheckBool v "minGuards"});      descr = "tries to remove unnecessary clauses from the inferred guards"; }
  { optionName = "noMinGuards";     optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with minimizeGuards         = not (CheckBool v "noMinGuards")});   descr = "don't minimize guards"; }
]

let cfgOptMap = cfgOptions |> List.fold (fun acc o -> acc |> Map.add o.optionName o) Map.empty

let newline = System.Environment.NewLine

let PrintHelpMsg = 
  let maxw = cfgOptions |> List.fold (fun acc o -> if String.length o.optionName > acc then String.length o.optionName else acc) 0
  let maxwStr = sprintf "%d" (maxw + 2)
  let strf = new Printf.StringFormat<_>("  %-" + maxwStr + "s: %-6s | %s")
  let rec __PrintHelp optLst = 
    match optLst with
    | fs :: []   -> (sprintf strf fs.optionName fs.optionType fs.descr)
    | fs :: rest -> (sprintf strf fs.optionName fs.optionType fs.descr) + newline + (__PrintHelp rest)
    | [] -> ""
  (* --- function body starts here --- *)
  newline +
  "Jennisys usage: Jennisys [ option ... ] filename" + newline +
  "  where <option> is one of " + newline + newline +
  "  ----- General options -----------------------------------------------------" + newline + 
  "        (available switches are: /, -, --)" + newline + newline +
  (__PrintHelp cfgOptions)

let defaultConfig: Config = {
  help              = false;
  inputFilename     = "";
  inferConditionals = true;
  methodToSynth     = "*";
  constructorsOnly  = false;
  verifyPartialSolutions = true;
  verifySolutions   = true;
  checkUnifications = false;
  genRepr           = true;
  genMod            = false;
  timeout           = 0;
  numLoopUnrolls    = 2;
  recursiveValid    = true;
  breakIntoDebugger = false;
  minimizeGuards    = true;
}

/// Should not be mutated outside the ParseCmdLineArgs method, which is 
/// typically called only once at the beginning of the program execution 
let mutable CONFIG = defaultConfig

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
                 
  let rec __Parse args cfg =
    match args with
    | fs :: rest -> 
        let opt,value = __Split fs
        if opt = "" then
          __Parse rest { cfg with inputFilename = CheckNonEmpty value opt }
        else 
          match Map.tryFind opt cfgOptMap with
          | Some(opt) -> __Parse rest (opt.optionSetter value cfg)
          | None -> raise (InvalidCmdLineOption("Unknown option: " + opt))
    | [] -> cfg   
    
  (* --- function body starts here --- *)           
  CONFIG <- __Parse args defaultConfig

