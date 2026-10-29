# Latest Dafny changes

Each file in the `docs/dev/news/` folder describes one change in Dafny since the latest release.

`docs/dev/news/` is the only directory the release script reads.  A note file put anywhere else is silently dropped and its text will never reach `RELEASE_NOTES.md`; `make news-check` catches that, and catches names the release script cannot classify.  Don't hand-edit `RELEASE_NOTES.md` either: the release script writes each new section from these files, and a bullet added by hand under `# Upcoming` ends up inside whichever version ships next.

Files in this directory are named `<issue number>.<kind>` (e.g. `1234.fix`) or `<description>.<kind>` (`assign-such-that-null.fix`) and each contains release notes for one merged PR.  `kind` is `break` (for breaking changes), `feat` (for new features and enhancements) or `fix` (for bug fixes).  The kind always comes **last**: `1234.fix` is a release note, whereas `fix.1234` is an unrecognized file that will abort the next release.

No need to include a link to a PR or issue in the file: it will be added automatically.  Specifically:

- With `<issue number>.<kind>`, the link will point to that issue number.
- With `<description>.<kind>`, the number is recovered from the Git history: the release script scans the commits that added the file, newest first, and takes the number from the first subject line *ending* in `(#1234)`.  So a note that is removed and later restored links to the PR that restored it — unless that PR's subject does not end in `(#1234)`, in which case the scan falls through to an older adding commit.  If none of them ends that way, the bullet ships with no link at all.

You can also use `<PR number>.<kind>` to link to a PR manually.  This is useful when using a a follow-up PR to add missing release notes for an already-merged feature (since the notes should contain a link to the original PR, not the follow-up one).

## Examples

- `1234.fix`

   ```
   Dafny will now detect and report burning toast.
   ```

- `new-toast-patterns.feat`

  ```
  Two new toast patterns:
  - Dafny waterfall logo
  - Dafny haircut logo
  (They are the same.)
  ```

At release time, these two files become bullet points in a new section of `RELEASE_NOTES.md` with links to the corresponding PRs, like this:

```
## New features

- Two new toast patterns:
  - Dafny waterfall logo
  - Dafny haircut logo
  (They are the same.)
  (https://github.com/dafny-lang/dafny/pull/5678)

## Bug fixes

- Dafny will now detect and report burning toast. (https://github.com/dafny-lang/dafny/pull/1234)
```

Note that a newline is added before the link only if the original is more than one line long.  For a `<description>.<kind>` file the PR number is computed by scanning the Git history, as described above; use `<PR number>.<kind>` when you want to pin a particular link.
