module PipelineUtils
  
let dafnyScratchFile = @"c:\tmp\jennisys-scratch.dfy"
let dafnyModelFile = @"c:\tmp\jennisys-scratch.model"
let dafnyOutFile = @"c:\tmp\jennisys-scratch.out"
let dafnySynthFile = @"c:\tmp\jennisys-synth.dfy"

let RunDafny inputFile modelFile =
  async {
    use proc = new System.Diagnostics.Process()
    proc.StartInfo.FileName  <- @"c:\tmp\StartDafny-jen.bat"
    proc.StartInfo.Arguments <- "/mv:" + modelFile + " " + inputFile
    assert proc.Start()
    proc.WaitForExit() 
  } |> Async.RunSynchronously     
