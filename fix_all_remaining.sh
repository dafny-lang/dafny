#!/bin/bash

echo "Finding all files with old error message patterns..."

# Find all files that still contain the old patterns
files_with_old_patterns=$(find Source/IntegrationTests/TestFiles -name "*.expect" -exec grep -l "might not hold\|might not decrease\|might not be well-founded" {} \;)

echo "Found $(echo "$files_with_old_patterns" | wc -l) files with old error patterns"

updated_count=0
failed_count=0
passed_count=0
total_count=$(echo "$files_with_old_patterns" | wc -l)

i=1
for file_path in $files_with_old_patterns; do
    # Extract test name from file path
    test_name=$(basename "$file_path" .dfy.expect)
    test_name=$(basename "$test_name" .expect)
    
    echo "[$i/$total_count] Testing $test_name (from $file_path)..."
    
    if make test name="$test_name" build=false 2>&1 | grep -q "FAIL"; then
        echo "  $test_name failed, updating expect file..."
        if make test update=true name="$test_name" build=false > /dev/null 2>&1; then
            echo "  ✅ $test_name updated successfully"
            ((updated_count++))
        else
            echo "  ❌ Failed to update $test_name"
            ((failed_count++))
        fi
    else
        echo "  ✅ $test_name already passes"
        ((passed_count++))
    fi
    
    ((i++))
done

echo ""
echo "All remaining files update complete!"
echo "Updated: $updated_count"
echo "Already passing: $passed_count" 
echo "Failed to update: $failed_count"
echo "Total processed: $total_count"
