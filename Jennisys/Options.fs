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
   verifySolutions: bool;
}

let defaultConfig: Config = {
  inputFilename   = "";
  methodToSynth   = "*";
  verifySolutions = true;
}

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
               
  let rec __Parse args cfg =
    match args with
    | fs :: rest -> 
        let opt,value = __Split fs
        match opt with
        | "method"    -> 
            if value = "" then raise (InvalidCmdLineArg("Must provide method name"))
            __Parse rest { cfg with methodToSynth = value }
        | "verifySol" -> 
            __Parse rest { cfg with verifySolutions = true }
        | "" -> 
            __Parse rest { cfg with inputFilename = value }
        | _ -> 
            raise (InvalidCmdLineOption("Unknown option: " + opt))
    | [] -> cfg    
  CONFIG <- __Parse args defaultConfig

