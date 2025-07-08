#!/bin/bash

# Comprehensive script to fix all test expectation files for PR #3324
# This applies both position format changes and error message updates

set -e

echo "Applying comprehensive test expectation fixes for PR #3324..."

# Function to fix a single file
fix_file() {
    local file="$1"
    echo "Processing: $file"
    
    # Create a backup
    cp "$file" "$file.bak"
    
    # Fix position format: (line,col) -> (line:col-line:col)
    sed -i 's/\([^(]*\)(\([0-9]\+\),\([0-9]\+\)):/\1(\2:\3-\2:\3):/g' "$file"
    
    # Fix all error message patterns comprehensively
    
    # Main "might not hold" patterns
    sed -i 's/assertion might not hold/assertion could not be proved/g' "$file"
    sed -i 's/postcondition might not hold/postcondition could not be proved/g' "$file"
    sed -i 's/precondition might not hold/precondition could not be proved/g' "$file"
    sed -i 's/invariant might not hold/invariant could not be proved/g' "$file"
    sed -i 's/loop invariant might not hold/loop invariant could not be proved/g' "$file"
    
    # Contextual patterns
    sed -i 's/might not hold on entry/could not be proved on entry/g' "$file"
    sed -i 's/might not hold on this return path/could not be proved on this return path/g' "$file"
    sed -i 's/might not hold on a return path/could not be proved on a return path/g' "$file"
    sed -i 's/might not hold for this call/could not be proved for this call/g' "$file"
    
    # Maintenance and decrease patterns
    sed -i 's/might not be maintained by the loop/could not be proved to be maintained by the loop/g' "$file"
    sed -i 's/might not be maintained/could not be proved to be maintained/g' "$file"
    sed -i 's/might not decrease/could not be proved to decrease/g' "$file"
    sed -i 's/might not terminate/could not be proved to terminate/g' "$file"
    
    # Update patterns
    sed -i 's/assignment might update/assignment could update/g' "$file"
    sed -i 's/might update/could update/g' "$file"
    sed -i 's/might violate/could violate/g' "$file"
    sed -i 's/might be uninitialized/could be uninitialized/g' "$file"
    
    # Specific phrases from PR description
    sed -i 's/Could not prove this assertion/this assertion could not be proved/g' "$file"
    sed -i 's/This postcondition might not hold on a return path/this postcondition could not be proved on a return path/g' "$file"
    sed -i 's/A postcondition might not hold on this return path/a postcondition could not be proved on this return path/g' "$file"
    sed -i 's/the calculation step between the previous line and this line might not hold/the calculation step between the previous line and this line could not be proved/g' "$file"
    sed -i 's/This loop invariant might not hold on entry/this loop invariant could not be proved on entry/g' "$file"
    sed -i 's/A precondition for this call might not hold/a precondition for this call could not be proved/g' "$file"
    sed -i 's/This is the precondition that might not hold/this is the precondition that could not be proved/g' "$file"
    sed -i 's/function precondition might not hold/function precondition could not be proved/g' "$file"
    
    # Ensure consistency: "proven" -> "proved"
    sed -i 's/could not be proven/could not be proved/g' "$file"
    
    # Capitalization fixes - make error messages start with lowercase
    sed -i 's/Error: A postcondition/Error: a postcondition/g' "$file"
    sed -i 's/Error: A precondition/Error: a precondition/g' "$file"
    sed -i 's/Error: This assertion/Error: this assertion/g' "$file"
    sed -i 's/Error: This postcondition/Error: this postcondition/g' "$file"
    sed -i 's/Error: This precondition/Error: this precondition/g' "$file"
    sed -i 's/Error: This loop invariant/Error: this loop invariant/g' "$file"
    sed -i 's/Error: The calculation/Error: the calculation/g' "$file"
    
    # Remove trailing periods from error messages
    sed -i 's/could not be proved\./could not be proved/g' "$file"
    sed -i 's/divisor is always non-zero\./divisor is always non-zero/g' "$file"
    sed -i 's/This assertion holds\./this assertion holds/g' "$file"
    sed -i 's/All preconditions hold for this call\./all preconditions hold for this call/g' "$file"
    sed -i 's/This precondition holds\./this precondition holds/g' "$file"
    sed -i 's/All postconditions hold for this return path\./all postconditions hold for this return path/g' "$file"
    sed -i 's/This postcondition holds\./this postcondition holds/g' "$file"
    sed -i 's/This loop invariant holds on entry\./this loop invariant holds on entry/g' "$file"
    sed -i 's/This loop invariant is maintained by the loop\./this loop invariant is maintained by the loop/g' "$file"
    
    # Fix capitalization of positive messages too
    sed -i 's/This assertion holds/this assertion holds/g' "$file"
    sed -i 's/All preconditions hold for this call/all preconditions hold for this call/g' "$file"
    sed -i 's/This precondition holds/this precondition holds/g' "$file"
    sed -i 's/All postconditions hold for this return path/all postconditions hold for this return path/g' "$file"
    sed -i 's/This postcondition holds/this postcondition holds/g' "$file"
    sed -i 's/This loop invariant holds on entry/this loop invariant holds on entry/g' "$file"
    sed -i 's/This loop invariant is maintained by the loop/this loop invariant is maintained by the loop/g' "$file"
    
    # Check if file was actually changed
    if ! cmp -s "$file" "$file.bak"; then
        echo "  Updated: $file"
    fi
    
    # Remove backup
    rm "$file.bak"
}

# Process all .expect files in the test directories
echo "Processing test expectation files..."
find ./Source/IntegrationTests/TestFiles -name "*.expect" -type f | while read -r file; do
    fix_file "$file"
done

# Also process documentation files
echo "Processing documentation expectation files..."
find ./docs -name "*.expect" -type f | while read -r file; do
    fix_file "$file"
done

echo "Comprehensive fix complete!"
echo "Files modified:"
git status --porcelain | wc -l
