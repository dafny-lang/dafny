## This small script takes as first argument a test indicator
## and the rest of the arguments are a command to run, with its
## command-line arguments.
## The script runs the command and then if the first argument is
## (1) -any -- returns success, ignoring the exit code of the command
## (2) -z  -- returns success iff the exit code is non-zero
## (3) some integer literal -- return success iff the exit code 
##     matches the given integer
## (4) -skip -- does not run the command and just exits with success

import sys
import subprocess

arg = sys.argv[1]
if arg == "-skip":
    print( 'Skipping' )
    exit(0)

p = subprocess.run( sys.argv[2:] )

if arg == "-any":
    exit(0)
if arg == "-z":
    if p.returncode == 0 :
        print( 'Expected non-zero exit code' )
        exit(1)
    else:
        exit(0)
if p.returncode != int(arg) :
    print( 'Expected exit code', arg, ', actual result is', p.returncode )
    exit(1)

exit(0)
