#!/bin/bash

# Final comprehensive cleanup of all error message patterns
set -e

echo "Performing final comprehensive cleanup of error messages..."

# Function to find and fix all remaining patterns
comprehensive_fix() {
    echo "Applying comprehensive error message fixes..."
    
    find ./Source/IntegrationTests/TestFiles -name "*.expect" -type f | while read -r file; do
        cp "$file" "$file.bak"
        
        # All variations of "might not hold"
        sed -i 's/assertion might not hold/assertion could not be proved/g' "$file"
        sed -i 's/postcondition might not hold/postcondition could not be proved/g' "$file"
        sed -i 's/precondition might not hold/precondition could not be proved/g' "$file"
        sed -i 's/invariant might not hold/invariant could not be proved/g' "$file"
        sed -i 's/loop invariant might not hold/loop invariant could not be proved/g' "$file"
        
        # Specific patterns with context
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
        
        # Fix "proven" vs "proved" consistency - use "proved" as per PR
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
        
        if ! cmp -s "$file" "$file.bak"; then
            echo "  Final cleanup: $file"
        fi
        
        rm "$file.bak"
    done
    
    # Also fix documentation files
    find ./docs -name "*.expect" -type f | while read -r file; do
        cp "$file" "$file.bak"
        
        # Apply all the same fixes to docs
        sed -i 's/assertion might not hold/assertion could not be proved/g' "$file"
        sed -i 's/postcondition might not hold/postcondition could not be proved/g' "$file"
        sed -i 's/precondition might not hold/precondition could not be proved/g' "$file"
        sed -i 's/invariant might not hold/invariant could not be proved/g' "$file"
        sed -i 's/loop invariant might not hold/loop invariant could not be proved/g' "$file"
        sed -i 's/might not hold on entry/could not be proved on entry/g' "$file"
        sed -i 's/might not hold on this return path/could not be proved on this return path/g' "$file"
        sed -i 's/might not hold on a return path/could not be proved on a return path/g' "$file"
        sed -i 's/might not hold for this call/could not be proved for this call/g' "$file"
        sed -i 's/might not be maintained by the loop/could not be proved to be maintained by the loop/g' "$file"
        sed -i 's/might not be maintained/could not be proved to be maintained/g' "$file"
        sed -i 's/might not decrease/could not be proved to decrease/g' "$file"
        sed -i 's/might not terminate/could not be proved to terminate/g' "$file"
        sed -i 's/assignment might update/assignment could update/g' "$file"
        sed -i 's/might update/could update/g' "$file"
        sed -i 's/might violate/could violate/g' "$file"
        sed -i 's/might be uninitialized/could be uninitialized/g' "$file"
        sed -i 's/could not be proven/could not be proved/g' "$file"
        
        # Capitalization and periods
        sed -i 's/Error: A postcondition/Error: a postcondition/g' "$file"
        sed -i 's/Error: A precondition/Error: a precondition/g' "$file"
        sed -i 's/Error: This assertion/Error: this assertion/g' "$file"
        sed -i 's/Error: This postcondition/Error: this postcondition/g' "$file"
        sed -i 's/Error: This precondition/Error: this precondition/g' "$file"
        sed -i 's/Error: This loop invariant/Error: this loop invariant/g' "$file"
        sed -i 's/could not be proved\./could not be proved/g' "$file"
        
        if ! cmp -s "$file" "$file.bak"; then
            echo "  Final cleanup doc: $file"
        fi
        
        rm "$file.bak"
    done
}

# Function to check for any remaining problematic patterns
check_remaining_issues() {
    echo "Checking for any remaining problematic patterns..."
    
    echo "Remaining 'might not' patterns:"
    find ./Source/IntegrationTests/TestFiles -name "*.expect" -type f -exec grep -l "might not" {} \; | wc -l
    
    echo "Remaining 'might' in error contexts:"
    find ./Source/IntegrationTests/TestFiles -name "*.expect" -type f -exec grep -l "Error.*might" {} \; | wc -l
    
    echo "Inconsistent 'proven' vs 'proved':"
    find ./Source/IntegrationTests/TestFiles -name "*.expect" -type f -exec grep -l "could not be proven" {} \; | wc -l
}

# Main execution
main() {
    echo "=== Final Comprehensive Cleanup ==="
    
    # Apply comprehensive fixes
    comprehensive_fix
    
    # Check for remaining issues
    check_remaining_issues
    
    echo "Checking git status..."
    git status --porcelain | head -10
    
    echo "Final cleanup complete!"
}

# Run main function
main
