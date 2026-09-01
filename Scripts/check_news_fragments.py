#!/usr/bin/env python3
"""Check that release notes are where the release script will find them.

`prepare_release.py` reads only its `NEWSFRAGMENTS_PATH`. A note written anywhere
else is silently dropped: seven accumulated in `docs/news/` and shipped past two
releases. A note that is in the right directory but misnamed is worse -- it aborts
the release on release day.

Names only, no `git log`, so the answer is the same on a shallow clone.
Run with `make news-check`.
"""

import os
import subprocess
import sys

from pathlib import Path
from typing import List

sys.path.insert(0, str(Path(__file__).resolve().parent))

# pylint: disable=wrong-import-position
from prepare_release import NewsFragments, Release

CANONICAL = Path(Release.NEWSFRAGMENTS_PATH)

def repo_root() -> Path:
    try:
        proc = subprocess.run(["git", "rev-parse", "--show-toplevel"],
                              capture_output=True, check=True, encoding="utf-8")
    except (OSError, subprocess.CalledProcessError) as e:
        sys.exit(f"Could not locate the root of the repository: {e}")
    return Path(proc.stdout.strip())

def unclassifiable_fragments() -> List[str]:
    """Names in `CANONICAL` that `NewsFragments._read_directory` would reject."""
    if not CANONICAL.is_dir():
        return []
    return sorted(p.name for p in CANONICAL.iterdir()
                  if p.suffix not in NewsFragments.KNOWN_EXTENSIONS
                  and p.name not in NewsFragments.IGNORED)

def stray_fragments() -> List[str]:
    """Notes outside `CANONICAL`, from two sources because neither finds everything.

    `git ls-files` with `--others` covers any `news/` directory including files not
    yet added; the disk glob covers `docs/dev/` itself, which `.gitignore` hides.

    Filtered by ignored *name*, deliberately not by known extension: three of the
    seven real strays were `fix.NNNN`, whose suffix is `.NNNN`, so an extension
    filter would wave through exactly what this exists to catch.
    """
    strays = set()
    proc = subprocess.run(["git", "ls-files", "-z", "--full-name",
                           "--cached", "--others", "--exclude-standard",
                           "--", "news/*", "*/news/*"],
                          capture_output=True, check=True, encoding="utf-8")
    for path in proc.stdout.split("\0"):
        candidate = Path(path) if path else None
        if (candidate and candidate.parent != CANONICAL
                and candidate.name not in NewsFragments.IGNORED):
            strays.add(path)
    for ext in NewsFragments.KNOWN_EXTENSIONS:
        strays.update(str(p) for p in CANONICAL.parent.glob(f"*{ext}"))
    return sorted(strays)

def main() -> None:
    os.chdir(repo_root())
    problems = []

    if strays := stray_fragments():
        problems.append(
            f"These release notes are not in `{CANONICAL}`, so the release script "
            f"will never see them:\n" + "".join(f"  {s}\n" for s in strays)
            + f"Move them into `{CANONICAL}`.")

    if bad := unclassifiable_fragments():
        kinds = ", ".join(sorted(NewsFragments.KNOWN_EXTENSIONS))
        problems.append(
            f"These files in `{CANONICAL}` cannot be classified and would abort "
            f"the next release:\n" + "".join(f"  {b}\n" for b in bad)
            + f"The kind comes last: `<PR or issue number>.<kind>` (e.g. `1234.fix`)"
            f" or `<description>.<kind>`, where `<kind>` is one of {kinds}."
            f" See docs/dev/README.md.")

    if problems:
        print("\n\n".join(problems), file=sys.stderr)
        sys.exit(1)
    print(f"All release notes are in {CANONICAL} and correctly named.")

if __name__ == "__main__":
    main()
