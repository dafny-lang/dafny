#!/usr/bin/env bash

# This file enables splitting code off from an existing file while keeping the history of the split off code intact
# Using this script, a history preserving copy can be made of the original file
# The user must then manually prune both the existing and new file so no duplicate code is left.
if [ $# -lt 2 ]; then
    echo "Usage: git cp <src> <dst>"
    exit 1
fi

src=$1
dst=$2
temp_branch=git-cp-$RANDOM

git checkout -b "$temp_branch"
git mv "$src" "$dst"
git commit -m "git: mv $src $dst"

# This commit makes `git rebase --rebase-merges` work.
git checkout HEAD~ "$src"
git commit -m "git: checkout $src"
# --

git checkout -
git merge --no-ff -m "git: cp $src $dst" "$temp_branch"
git branch -d "$temp_branch"
