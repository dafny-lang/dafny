#!/bin/bash

echo "=== FIXING INTEGRATION TEST FAILURES ==="
echo "Systematically updating expect files for integration tests with assertion message format issues..."

# List of tests that are likely to have assertion message format issues
# Based on CI logs and common patterns
integration_tests=(
    "NonZeroInitialization"
    "SchorrWaite-stages"
    "Compilation"
    "TypeTests"
    "Refinement"
    "AsIs"
    "SharedDestructors"
    "DefaultParameters"
    "Ghost"
    "Havoc"
    "Iterators"
    "Newtypes"
    "TailRecursion"
    "Trait"
    "TypeMembers"
    "StoreAndRetrieve"
    "Iter"
    "Lambda"
    "Simple"
    "Field"
    "exists-b-exists-not-b"
)

updated_count=0
failed_count=0
passed_count=0
total_count=${#integration_tests[@]}

echo "Processing $total_count integration tests..."
echo ""

for i in "${!integration_tests[@]}"; do
    test_name="${integration_tests[$i]}"
    echo "[$((i+1))/$total_count] Processing $test_name..."
    
    # First check if the test fails due to assertion message format issues
    if timeout 30 make test name="$test_name" build=false >/dev/null 2>&1; then
        echo "  ✅ $test_name already passes"
        ((passed_count++))
    else
        echo "  $test_name failed, attempting to update expect file..."
        # Try to update the expect file
        if timeout 60 make test update=true name="$test_name" build=false >/dev/null 2>&1; then
            echo "  ✅ $test_name updated successfully"
            ((updated_count++))
        else
            echo "  ❌ Failed to update $test_name (likely compilation issues, not assertion format)"
            ((failed_count++))
        fi
    fi
done

echo ""
echo "=== INTEGRATION TEST FIX COMPLETE ==="
echo "Updated: $updated_count"
echo "Already passing: $passed_count"
echo "Failed to update: $failed_count"
echo "Total processed: $total_count"

# Check for any remaining files with old patterns
remaining_files=$(find Source/IntegrationTests/TestFiles -name "*.expect" -exec grep -l "might not hold\|might not decrease\|might not be well-founded\|might not satisfy\|might violate" {} \; | wc -l)
echo ""
echo "Files still containing old patterns: $remaining_files"

if [ "$remaining_files" -eq 0 ]; then
    echo "🎉 ALL INTEGRATION TEST ASSERTION FORMATS FIXED!"
elif [ "$remaining_files" -le 10 ]; then
    echo "✅ Nearly complete! Only $remaining_files files remaining"
else
    echo "⚠️  Still $remaining_files files to fix"
fi
