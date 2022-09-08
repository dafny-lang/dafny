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
