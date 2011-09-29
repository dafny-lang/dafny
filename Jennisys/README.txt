1. Installation instructions
----------------------------

  - create c:\tmp folder
  - copy the Jennisys\scripts\StartDafny-jen.bat script into c:\tmp

2. Running the examples
----------------------------

  $ cd Jennisys
  $ bin/Debug/Jennisys.exe examples/<name>.jen /genRepr /genMod

  /genRepr - generate Repr field 
  /genMod  - generate modular code (delegate to methods)

  Currenty, in the List.jen example, methods SkipFew and Index cannot
  be synthesized.  All other methods in List.jen, List2.jen, List3.jen, 
  Set.jen, Number.jen, and NumberMethods.jen should be synthesizable.
