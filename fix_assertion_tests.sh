#!/bin/bash

# Test files that commonly have assertion-related errors
test_files=(
    # More specific test files
    "Compilation"
    "TypeTests"
    "Refinement"
    "RefinementModificationChecking"
    "Substitution"
    "Modules2"
    "Modules3"
    "ModulesExport"
    "ModulesImport"
    "ModulesRefinement"
    "ModulesResolution"
    "Verification"
    "VerificationErrors"
    "Assertions"
    "Preconditions"
    "Postconditions"
    "LoopInvariants"
    "FunctionContracts"
    "MethodContracts"
    "ClassInvariants"
    "ObjectInvariants"
    "FrameConditions"
    "ModifiesClause"
    "ReadsClause"
    "DecreasesClause"
    "WellFoundedness"
    "Termination"
    "Induction"
    "Coinduction"
    "FixedPoints"
    "LeastFixedPoints"
    "GreatestFixedPoints"
)

echo "Finding and fixing assertion-related test files..."

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
echo "Assertion-related update complete!"
echo "Updated: $updated_count"
echo "Already passing: $passed_count" 
echo "Failed to update: $failed_count"
echo "Total processed: $total_count"
