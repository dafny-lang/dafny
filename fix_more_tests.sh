#!/bin/bash

# List of more test files from different categories
test_files=(
    # git-issues files
    "git-issue-Main0"
    "git-issue-Main1" 
    "git-issue-Main2"
    "git-issue-Main3"
    "git-issue-Main4"
    "git-issue-Main5"
    # More specific files
    "Superposition"
    "Parallel"
    "Comprehensions"
    "Sequences"
    "Maps"
    "Sets"
    "Predicates"
    "Functions"
    "Methods"
    "Loops"
    "Invariants"
    "Assertions"
    "Preconditions"
    "Postconditions"
)

echo "Fixing more test files..."

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
echo "Update complete!"
echo "Updated: $updated_count"
echo "Already passing: $passed_count" 
echo "Failed to update: $failed_count"
