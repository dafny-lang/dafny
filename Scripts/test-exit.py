import sys
import subprocess

ec = int(sys.argv[1])
p = subprocess.run( sys.argv[2:] )
if p.returncode != ec :
    print( 'Expected exit code ', ec, 'instead of ', p.returncode )
    exit(1)
exit(0)
