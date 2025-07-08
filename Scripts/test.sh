#!/bin/bash
set -e

# Ensure name is provided
if [ -z "$name" ]; then
  echo "Syntax: make test name=<integration test filter> [update=true] [build=false]"
  exit 1
fi

# Default values for update and build
update_flag=${update:-false}
build_flag=${build:-true}

# Set the integration tests folder
integration_tests_dir="${DIR}/Source/IntegrationTests"
lit_tests_dir="${integration_tests_dir}/TestFiles/LitTests/LitTest"

# Handle no-build logic
if [ "$build_flag" = "false" ]; then
  echo ""
  echo "Build is disabled. Copying test files to the output directory..."
  
  framework_dir=$(find "${integration_tests_dir}/bin/Debug" -maxdepth 1 -type d -name "net*" | sort | tail -n 1)
  if [ -z "$framework_dir" ]; then
    echo "Error: Could not find target framework directory in bin/Debug. Please run at least once with build=true."
    exit 1
  fi
  output_dir="${framework_dir}/TestFiles/LitTests/LitTest"

  # Find and copy all matching files to the output directory
  files=$(cd "$lit_tests_dir" && find . -type f -regex '.*\.\(check\|dfy\|expect\)' -wholename "*$name*")
  if [ -z "$files" ]; then
    echo "No files found matching pattern: $name"
    exit 1
  fi
  
  # Create output directory if it doesn't exist
  mkdir -p "$output_dir"
  
  # Copy files
  echo "$files" | while IFS= read -r file; do
    echo "Copying $file to $output_dir"
    cp "$lit_tests_dir/$file" "$output_dir/$file"
  done
fi

# Check if update flag is true
if [ "$update_flag" = "true" ]; then
  echo ""
  echo "Update mode enabled."
  echo "Going to update the .expect files to match the current Dafny output."
fi

# Run dotnet test
echo "Running integration tests..."
DAFNY_INTEGRATION_TESTS_UPDATE_EXPECT_FILE="$update_flag" \
dotnet test "$integration_tests_dir" \
  $( [ "$build_flag" = "false" ] && echo "--no-build" ) \
  --filter "DisplayName~$name"
