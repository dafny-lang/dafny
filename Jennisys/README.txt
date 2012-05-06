1. Installation instructions
----------------------------

  - download the entire boogie source distribution and place it in c:\boogie
  - create c:\tmp folder
  - copy the Jennisys\scripts\StartDafny-jen.bat script into c:\tmp

2. Running the examples
----------------------------

    $ cd Jennisys
    $ bin/Debug/Jennisys.exe examples/<name>.jen 

  The most current and complete set of examples is in the
  "examples/oopsla12" folder.  No additional Jennisys switches need be
  passed for either of them.

  Synthesized programs will be generated in "c:\tmp", and their file
  names will follow the following pattern:

    "jennisys-synth_<example-name>.dfy"

  To verify the correctness of the synthesized programs, run

    $ Dafny /compile:0 jennisys-synth_<example-name>.dfy

  Expected outputs (i.e., synthesized Dafny programs) for the examples
  in "examples/oopsla12" can be found in the same folder. 
