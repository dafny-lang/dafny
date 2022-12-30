# Latest Dafny changes

Each file in this folder describes one change in Dafny since the latest release.

Files in this directory are named `<PR or issue number>.<kind>` (e.g. `1234.fix`) or `<description>.kind` (`assign-such-that-null.fix`) and each contains release notes for one merged PR.  `kind` is `break` (for breaking changes), `feat` (for new features and enhancements) or `fix` (for bug fixes).  No need to include a link to the PR in the file: it will be added automatically.

- If `<PR number>` is present, a link to the PR is added to the release notes for that entry.
- If `<description>` is used instead, the PR number is determined automatically from the git history.

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

Note that a newline is added before the link only if the original is more than one line long.  The link to the first PR is computed automatically by scanning the Git history.
