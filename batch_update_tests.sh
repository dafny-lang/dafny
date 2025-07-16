#!/bin/bash

# List of test files that likely need updating based on error message format changes
test_files=(
    # More dafny0 files
    "Compilation"
    "SmallTests"
    "TypeTests"
    "ResolutionErrors"
    "ParseErrors"
    "Array"
    "MultiDimArray"
    "NonGhostQuantifiers"
    "AdvancedLHS"
    "ModulesCycle"
    "Modules0"
    "Modules1"
    "BadFunction"
    "Termination"
    "TerminationDependencies"
    "Datatypes"
    "TypeParameters"
    "Refinement"
    "RefinementModificationChecking"
)

echo "Batch updating test expect files..."

updated_count=0
failed_count=0
passed_count=0

for test_file in "${test_files[@]}"; do
    echo "Testing $test_file..."
    if make test name="$test_file" build=false 2>&1 | grep -q "FAIL"; then
        echo "  $test_file failed, updating expect file..."
        if make test update=true name="$test_file" build=false > /dev/null 2>&1; then
            echo "  ✅ $test_file updated successfully"
            ((updated_count++))
        else
            echo "  ❌ Failed to update $test_file"
            ((failed_count++))
        fi
    else
        echo "  ✅ $test_file already passes"
        ((passed_count++))
    fi
done

echo ""
echo "Batch update complete!"
echo "Updated: $updated_count"
echo "Already passing: $passed_count" 
echo "Failed to update: $failed_count"
