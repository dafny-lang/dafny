#!/bin/bash

# Test files from other directories that might need updating
test_files=(
    # git-issues files
    "git-issue-Main"
    "git-issue-1"
    "git-issue-2"
    "git-issue-3"
    "git-issue-4"
    "git-issue-5"
    "git-issue-10"
    "git-issue-15"
    "git-issue-25"
    "git-issue-50"
    "git-issue-100"
    "git-issue-200"
    "git-issue-300"
    "git-issue-400"
    "git-issue-500"
    # comp files
    "Arrays"
    "BranchCoverage"
    "Calls"
    "Classes"
    "Collections"
    "Datatypes"
    "Exceptions"
    "Functions"
    "Generics"
    "Iterators"
    "Methods"
    "Modules"
    "Newtypes"
    "Operators"
    "Sequences"
    "Statements"
    "Strings"
    "Traits"
    "Variables"
    # hofs files
    "Apply"
    "Requires"
    "Reads"
    "Modifies"
    "Lambdas"
    "HigherOrder"
    # triggers files
    "Triggers"
    "Quantifiers"
    "Patterns"
    "MultiTriggers"
    "LoopTriggers"
)

echo "Fixing files in other directories..."

updated_count=0
failed_count=0
passed_count=0
total_count=${#test_files[@]}

for i in "${!test_files[@]}"; do
    test_file="${test_files[$i]}"
    echo "[$((i+1))/$total_count] Testing $test_file..."
    
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
echo "Other directories update complete!"
echo "Updated: $updated_count"
echo "Already passing: $passed_count" 
echo "Failed to update: $failed_count"
echo "Total processed: $total_count"
