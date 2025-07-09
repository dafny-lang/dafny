#!/bin/bash

echo "=== FINAL COMPREHENSIVE ASSERTION MESSAGE FIX ==="
echo "Searching for all remaining files with old assertion message patterns..."

# Find all files that still contain old patterns
files_with_old_patterns=$(find Source/IntegrationTests/TestFiles -name "*.expect" -exec grep -l "might not hold\|might not decrease\|might not be well-founded\|might not terminate\|might not be satisfied" {} \;)

echo "Found files with old patterns:"
echo "$files_with_old_patterns"
echo ""

if [ -z "$files_with_old_patterns" ]; then
    echo "✅ No files found with old assertion message patterns!"
    exit 0
fi

total_files=$(echo "$files_with_old_patterns" | wc -l)
echo "Total files to check: $total_files"
echo ""

updated_count=0
failed_count=0
passed_count=0
skipped_count=0

i=1
for file_path in $files_with_old_patterns; do
    # Extract test name from file path - handle various patterns
    test_name=$(basename "$file_path")
    test_name=${test_name%.expect}
    test_name=${test_name%.dfy}
    test_name=${test_name%.refresh}
    test_name=${test_name%.testdafny}
    test_name=${test_name%.verifier}
    test_name=${test_name%.transcript}
    
    # Get the directory structure for more specific test names
    dir_path=$(dirname "$file_path")
    if [[ "$dir_path" == *"metatests"* ]]; then
        echo "[$i/$total_files] Skipping metatest: $test_name (from $file_path)"
        echo "  ⏭️  Metatests intentionally use old format for testing"
        ((skipped_count++))
        ((i++))
        continue
    fi
    
    echo "[$i/$total_files] Testing $test_name (from $file_path)..."
    
    # Try to run the test
    if timeout 30 make test name="$test_name" build=false >/dev/null 2>&1; then
        echo "  ✅ $test_name already passes"
        ((passed_count++))
    else
        echo "  $test_name failed, attempting to update expect file..."
        if timeout 60 make test update=true name="$test_name" build=false >/dev/null 2>&1; then
            echo "  ✅ $test_name updated successfully"
            ((updated_count++))
        else
            echo "  ❌ Failed to update $test_name"
            ((failed_count++))
        fi
    fi
    
    ((i++))
done

echo ""
echo "=== FINAL ASSERTION MESSAGE FIX COMPLETE ==="
echo "Updated: $updated_count"
echo "Already passing: $passed_count"
echo "Skipped (metatests): $skipped_count" 
echo "Failed to update: $failed_count"
echo "Total processed: $total_files"

# Check how many files still have old patterns
remaining_files=$(find Source/IntegrationTests/TestFiles -name "*.expect" -exec grep -l "might not hold\|might not decrease\|might not be well-founded\|might not terminate\|might not be satisfied" {} \; | wc -l)
echo ""
echo "Files still containing old patterns: $remaining_files"

if [ "$remaining_files" -eq 0 ]; then
    echo "🎉 ALL ASSERTION MESSAGE FORMATS FIXED!"
elif [ "$remaining_files" -le 3 ]; then
    echo "✅ Nearly complete! Only $remaining_files files remaining (likely metatests)"
else
    echo "⚠️  Still $remaining_files files to fix"
fi
