# Latest Dafny changes

Each file in this folder describes one change in Dafny since the latest release.

Files in this directory are named `<issue number>.<kind>` (e.g. `1234.fix`) or `<description>.kind` (`assign-such-that-null.fix`) and each contains release notes for one merged PR.  `kind` is `break` (for breaking changes), `feat` (for new features and enhancements) or `fix` (for bug fixes).  

No need to include a link to a PR or issue in the file: it will be added automatically.  Specifically:

- With `<issue number>.<kind>`, the link will point to that issue number.
- With `<description>.<kind>`, the link will point to the PR that introduced the release note file (which should be the PR for the corresponding feature or fix; its number is determined automatically by the release script from the commit history).

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

Note that a newline is added before the link only if the original is more than one line long.  The link to the first PR is computed automatically by scanning the Git history.
