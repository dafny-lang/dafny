## This small script takes as first argument either
## an integer literal (n) or the string '-z',
## then the rest of the arguments are a command to run, with its
## command-line arguments.
## The script runs the command and then checks whether the exit code
## is non-zero, if -z is the argument, or
## equals the given integer, exiting with 0 if it does and 1 (plus an
## error message) if it does not.

import sys
import subprocess

nz = False
if sys.argv[1] == "-z":
  nz = True
else: 
  ec = int(sys.argv[1])
p = subprocess.run( sys.argv[2:] )
if (nz and p.returncode == 0) :
    print( 'Expected non-zero exit code' )
    exit(1)
if (not nz and p.returncode != ec) :
    print( 'Expected exit code ', ec, 'instead of ', p.returncode )
    exit(1)
exit(0)
