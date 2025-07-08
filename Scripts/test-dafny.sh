#!/bin/bash

# Check for required environment variables
if [ -z "$DIR" ]; then
  echo "Error: DIR environment variable is not set."
  exit 1
fi

if [ -z "$name" ]; then
  echo "Error: name environment variable is not set."
  exit 1
fi

# Set the default build flag
NO_BUILD=${NO_BUILD:-false}

# Locate files matching the specified pattern
files=$(cd "${DIR}/Source/IntegrationTests/TestFiles/LitTests/LitTest" && find . -type f -wholename "*$name*" | grep -E '\.dfy$')

if [ -z "$files" ]; then
  echo "No files found matching pattern: $name"
  exit 1
else
  count=$(echo "$files" | wc -l)
  echo "$files"
  echo "$count test files found."
  for file in $files; do
    filedir=$(dirname "$file")
    (
      cd "${DIR}/Source/IntegrationTests/TestFiles/LitTests/LitTest/$filedir" || exit
      
      build_flag=""
      [ "$NO_BUILD" = "true" ] && build_flag="--no-build"

      dotnet run $build_flag --project "${DIR}/Source/Dafny" -- ${action} "$(basename "$file")"
    )
  done
fi