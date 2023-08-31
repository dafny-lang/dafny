#!/bin/bash
LIB_VERSION=$(grep Boogie.ExecutionEngine Source/DafnyCore/DafnyCore.csproj | cut -d "\"" -f 4)
TOOL_VERSION=$(./Scripts/dafny_boogie.sh -version | cut -d ' ' -f 5 | cut -d . -f 1-3)
if [ "$LIB_VERSION" != "$TOOL_VERSION" ] ; then
  echo "Mismatched Boogie versions."
  echo "Library version is ${LIB_VERSION}"
  echo "dotnet tool version is ${TOOL_VERSION}"
  exit 1
else
  echo "Boogie versions match (${LIB_VERSION})"
fi
