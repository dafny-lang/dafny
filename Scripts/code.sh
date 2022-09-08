SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd)
export DAFNY_SERVER_OVERRIDE=$SCRIPT_DIR/../Binaries/DafnyLanguageServer.dll
code -n
