#!/usr/bin/env python3
"""Tests for `check_news_fragments.py`. Run with `make news-check-test`.

The cases are the real ones: the seven notes that accumulated in `docs/news/` were
a mix of `NNNN.fix` and `fix.NNNN`, and `.gitignore` hides `docs/dev/*.fix`, so no
single detection strategy finds all of them.

Exercised as a subprocess, because the exit code is the whole contract.
"""

import subprocess
import sys
import tempfile
import unittest

from pathlib import Path

SCRIPT = Path(__file__).resolve().parent / "check_news_fragments.py"
CANONICAL = "docs/dev/news"
GITIGNORE = "docs/dev/*.fix\ndocs/dev/*.feat\ndocs/dev/*.break\n"

def git(*args: str, cwd: Path) -> subprocess.CompletedProcess:
    return subprocess.run(["git", *args], cwd=cwd,
                          capture_output=True, check=True, encoding="utf-8")

class GuardFixture(unittest.TestCase):
    def setUp(self) -> None:
        self._tmpdir = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmpdir.cleanup)
        self.repo = Path(self._tmpdir.name) / "dafny"
        (self.repo / CANONICAL).mkdir(parents=True)

        git("init", "--quiet", "--initial-branch=master", ".", cwd=self.repo)
        for key, value in (("user.name", "Dafny Test"),
                           ("user.email", "test@example.com"),
                           ("commit.gpgsign", "false"),
                           ("core.hooksPath", str(self.repo / ".no-such-hooks"))):
            git("config", key, value, cwd=self.repo)

        (self.repo / ".gitignore").write_text(GITIGNORE, encoding="utf-8")
        self.write("docs/dev/news/1234.fix", "Fix the thing")
        git("add", "--all", ".", cwd=self.repo)
        git("commit", "--quiet", "--message=Fixture (#1)", cwd=self.repo)

    def write(self, relpath: str, contents: str) -> None:
        path = self.repo / relpath
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(contents + "\n", encoding="utf-8")

    def assertFlags(self, name: str) -> None:
        result = subprocess.run([sys.executable, str(SCRIPT)], cwd=self.repo,
                                capture_output=True, check=False, encoding="utf-8")
        self.assertEqual(result.returncode, 1, f"expected {name} to be reported")
        self.assertIn(name, result.stdout + result.stderr)

    def assertClean(self) -> None:
        result = subprocess.run([sys.executable, str(SCRIPT)], cwd=self.repo,
                                capture_output=True, check=False, encoding="utf-8")
        self.assertEqual(result.returncode, 0, result.stderr)

class TestNewsCheck(GuardFixture):
    def test_clean_repository_passes(self) -> None:
        self.assertClean()

    def test_note_in_docs_news_is_reported(self) -> None:
        self.write("docs/news/3809.fix", "Fix something")
        git("add", "--all", ".", cwd=self.repo)
        self.assertFlags("docs/news/3809.fix")

    def test_kind_first_note_in_docs_news_is_reported(self) -> None:
        # `Path("fix.3809").suffix` is ".3809", so filtering strays by known
        # extension would wave this through -- and three of the seven real strays
        # were named exactly like this.
        self.write("docs/news/fix.3809", "Fix something")
        git("add", "--all", ".", cwd=self.repo)
        self.assertFlags("docs/news/fix.3809")

    def test_unstaged_note_is_reported(self) -> None:
        # Covers `--others`: not added yet, which is when the message helps most.
        self.write("docs/news/3809.fix", "Fix something")
        self.assertFlags("docs/news/3809.fix")

    def test_gitignored_note_one_directory_too_high_is_reported(self) -> None:
        # Covers the disk glob: `.gitignore` hides this from git entirely.
        self.write("docs/dev/9999.fix", "Fix something")
        self.assertFlags("docs/dev/9999.fix")

    def test_readme_in_an_unrelated_news_directory_is_ignored(self) -> None:
        self.write("tools/news/README.md", "Not a release note")
        git("add", "--all", ".", cwd=self.repo)
        self.assertClean()

    def test_misnamed_note_in_the_canonical_directory_is_reported(self) -> None:
        self.write(f"{CANONICAL}/fix.9999", "A kind-first name")
        git("add", "--all", ".", cwd=self.repo)
        self.assertFlags("fix.9999")

if __name__ == "__main__":
    unittest.main()
