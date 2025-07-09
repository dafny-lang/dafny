#!/bin/bash

# Script to resolve merge conflicts during rebase
set -e

echo "Resolving merge conflicts..."

# Handle modify/delete conflicts - remove files that were deleted in HEAD
echo "Removing files that were deleted in master..."
git status --porcelain | grep "^DU " | cut -c4- | while read file; do
    echo "Removing deleted file: $file"
    git rm "$file" 2>/dev/null || true
done

# Handle content conflicts in .expect files
echo "Resolving content conflicts in .expect files..."
git status --porcelain | grep "^UU " | cut -c4- | while read file; do
    if [[ "$file" == *.expect ]]; then
        echo "Resolving conflict in: $file"
        
        # For .expect files, we'll take our version (the one with updated error messages)
        # and apply the position format fix
        git checkout --ours "$file"
        
        # Apply position format fix: (line,col) -> (line:col-line:col)
        sed -i 's/\([^(]*\)(\([0-9]\+\),\([0-9]\+\)):/\1(\2:\3-\2:\3):/g' "$file"
        
        # Apply error message updates
        sed -i 's/assertion might not hold/assertion could not be proved/g' "$file"
        sed -i 's/postcondition might not hold/postcondition could not be proved/g' "$file"
        sed -i 's/precondition might not hold/precondition could not be proved/g' "$file"
        sed -i 's/invariant might not hold/invariant could not be proved/g' "$file"
        sed -i 's/loop invariant might not hold/loop invariant could not be proved/g' "$file"
        sed -i 's/might not decrease/could not be proved to decrease/g' "$file"
        sed -i 's/might not terminate/could not be proved to terminate/g' "$file"
        sed -i 's/might not be maintained/could not be proved to be maintained/g' "$file"
        sed -i 's/assignment might update/assignment could update/g' "$file"
        sed -i 's/might update/could update/g' "$file"
        sed -i 's/might violate/could violate/g' "$file"
        sed -i 's/might be uninitialized/could be uninitialized/g' "$file"
        
        # Fix capitalization
        sed -i 's/Error: A postcondition/Error: a postcondition/g' "$file"
        sed -i 's/Error: A precondition/Error: a precondition/g' "$file"
        sed -i 's/Error: This assertion/Error: this assertion/g' "$file"
        sed -i 's/Error: This postcondition/Error: this postcondition/g' "$file"
        sed -i 's/Error: This precondition/Error: this precondition/g' "$file"
        sed -i 's/Error: This loop invariant/Error: this loop invariant/g' "$file"
        
        # Remove trailing periods
        sed -i 's/could not be proved\./could not be proved/g' "$file"
        sed -i 's/could not be proven/could not be proved/g' "$file"
        
        git add "$file"
        echo "  Resolved: $file"
    fi
done

# Handle source code conflicts - take theirs (master) for source files
echo "Resolving source code conflicts..."
git status --porcelain | grep "^UU " | cut -c4- | while read file; do
    if [[ "$file" == *.cs ]] || [[ "$file" == *.dfy ]] && [[ "$file" != *.expect ]]; then
        echo "Taking master version for source file: $file"
        git checkout --theirs "$file"
        git add "$file"
    fi
done

# Handle documentation conflicts
echo "Resolving documentation conflicts..."
if [ -f "docs/DafnyRef/UserGuide.md" ]; then
    echo "Resolving UserGuide.md conflict..."
    git checkout --theirs "docs/DafnyRef/UserGuide.md"
    git add "docs/DafnyRef/UserGuide.md"
fi

echo "Conflict resolution complete!"
echo "Remaining conflicts:"
git status --porcelain | grep "^UU " || echo "No remaining conflicts"
