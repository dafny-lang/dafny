#!/bin/sh
# Author: Clement Pit Claudel
#
# Finds the precise commit when a file stopped verifying.
#
# Usage
# Inside a Dafny folder
# - Copy this script from the scripts/folder to outside of the folder
# - Place file_name.dfy and run:
# bisect-dafny.sh vgood.old.revision vbad.new.revision file_name.dfy

if [ $# -ne 3 ]; then
  echo "Usage:"
  echo "Inside a Dafny folder, place the file file_name.dfy that is no longer verifying and"
  echo "$0 vgood.old.revision vbad.new.revision file_name.dfy"
  exit
fi

cat > script.sh << EOF
#!/bin/sh
set -e
dotnet build Source/DafnyDriver/DafnyDriver.csproj > /dev/null
EOF
echo -n "./Binaries/Dafny verify " >> script.sh
echo -n $3 >> script.sh
cat >> script.sh << EOF
 > /dev/null
EOF
chmod +x script.sh

git bisect start
git bisect good $1
git bisect bad $2

git bisect run ./script.sh
rm script.sh