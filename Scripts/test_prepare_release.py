#!/usr/bin/env python3
"""Tests for `prepare_release.py`.

Run with `make prepare-release-test`.

The release script is otherwise executed for the first time each cycle by hand,
on the live repository, on release day. These tests exercise it against a
throwaway repository instead, so that a mistake costs a red CI run rather than a
half-prepared release branch.

Every test that would touch the network is stubbed (see `ReleaseFixture.offline`).
Nothing contacts a real remote: the tests that push use a bare repository on disk
(`ReleaseFixture.add_bare_origin`). Pushing for real rather than mocking the push
is what gives the dry-run assertions teeth -- a missing `@mutating` shows up as a
ref appearing in that bare repository.
"""

# Tests reach into the checks they are testing.
# pylint: disable=protected-access

import doctest
import os
import subprocess
import sys
import tempfile
import unittest

from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))

# pylint: disable=wrong-import-position
import prepare_release
from prepare_release import NewsFragments, Release

BUILD_PROPS = """<Project>
  <PropertyGroup>
    <VersionPrefix>4.11.0</VersionPrefix>
  </PropertyGroup>
</Project>
"""

RELEASE_NOTES = f"""# Upcoming

{Release.RELEASE_NOTES_MARKER}

# 4.11.0

## Bug fixes

- An older fix. (https://github.com/dafny-lang/dafny/pull/1)
"""

def git(*args: str, cwd: Path) -> subprocess.CompletedProcess:
    return subprocess.run(["git", *args], cwd=cwd,
                          capture_output=True, check=True, encoding="utf-8")

class ReleaseFixture(unittest.TestCase):
    """A throwaway repository shaped like dafny-lang/dafny, with the CWD inside it.

    `Release` resolves every path relative to the working directory, so the tests
    have to run from inside the fixture.
    """

    def setUp(self) -> None:
        self._original_cwd = Path.cwd()
        self._tmpdir = tempfile.TemporaryDirectory()
        self.addCleanup(self._restore)

        self.repo = Path(self._tmpdir.name) / "dafny"
        (self.repo / "Source").mkdir(parents=True)
        (self.repo / Release.NEWSFRAGMENTS_PATH).mkdir(parents=True)

        git("init", "--quiet", "--initial-branch=master", ".", cwd=self.repo)
        # Do not inherit the developer's global git configuration: commit.gpgsign
        # or a global core.hooksPath would make these tests fail on their machine
        # and nowhere else.
        for key, value in (("user.name", "Dafny Test"),
                           ("user.email", "test@example.com"),
                           ("commit.gpgsign", "false"),
                           ("tag.gpgsign", "false"),
                           ("core.hooksPath", str(self.repo / ".no-such-hooks"))):
            git("config", key, value, cwd=self.repo)

        self.build_props = self.repo / "Source/Directory.Build.props"
        self.release_notes = self.repo / "RELEASE_NOTES.md"
        self.build_props.write_text(BUILD_PROPS, encoding="utf-8")
        self.release_notes.write_text(RELEASE_NOTES, encoding="utf-8")
        self.write_fragment("1234.fix", "Fix the thing")
        self.commit("Initial commit (#1000)")

        os.chdir(self.repo)

    def _restore(self) -> None:
        os.chdir(self._original_cwd)
        self._tmpdir.cleanup()

    def fragment_path(self, name: str) -> Path:
        return self.repo / Release.NEWSFRAGMENTS_PATH / name

    def write_fragment(self, name: str, contents: str) -> Path:
        path = self.fragment_path(name)
        path.write_text(contents + "\n", encoding="utf-8")
        return path

    def commit(self, message: str) -> None:
        git("add", "--all", ".", cwd=self.repo)
        git("commit", "--quiet", f"--message={message}", cwd=self.repo)

    def add_bare_origin(self) -> Path:
        """Give the fixture a real `origin` on disk that it can push to."""
        origin = Path(self._tmpdir.name) / "origin.git"
        git("init", "--quiet", "--bare", "--initial-branch=master", str(origin),
            cwd=self.repo)
        git("remote", "add", "origin", str(origin), cwd=self.repo)
        git("push", "--quiet", "origin", "master", cwd=self.repo)
        return origin

    @staticmethod
    def refs_of(repo: Path) -> str:
        # `git show-ref` exits 1 when there are no refs at all, so do not check.
        return subprocess.run(["git", "show-ref"], cwd=repo, capture_output=True,
                              check=False, encoding="utf-8").stdout

    def offline(self) -> None:
        """Stub the only two checks that need the network."""
        for name in ("_head_up_to_date", "_no_release_blocking_issues"):
            patcher = mock.patch.object(Release, name, return_value=True)
            patcher.start()
            self.addCleanup(patcher.stop)

    def render(self) -> str:
        fragments = NewsFragments.from_directory(Release.NEWSFRAGMENTS_PATH)
        fragments.check()
        return fragments.render()

class TestRendering(ReleaseFixture):
    def test_render_survives_an_unresolvable_pr_number(self) -> None:
        # A description-named fragment whose add-commit subject has no "(#N)"
        # resolves to `pr = None`. Sorting that against an `int` used to raise
        # TypeError from render(), which prepare() calls only after it has created
        # the release branch and rewritten the build props.
        self.write_fragment("mystery.fix", "Something unattributed")
        self.commit("A commit with no PR number in its subject")

        rendered = self.render()

        self.assertIn("Fix the thing", rendered)
        self.assertIn("Something unattributed", rendered)
        # Unresolved entries sort last.
        self.assertLess(rendered.index("Fix the thing"),
                        rendered.index("Something unattributed"))

    def test_entry_with_no_link_has_no_trailing_separator(self) -> None:
        self.write_fragment("mystery.fix", "Something unattributed")
        self.commit("A commit with no PR number in its subject")

        self.assertTrue(self.render().endswith("Something unattributed"),
                        "a link-less bullet should not end in the separator")

class TestChecks(ReleaseFixture):
    def test_no_release_tag_sees_an_existing_unsigned_annotated_tag(self) -> None:
        release = Release("4.12.0", "master")
        self.assertTrue(release._no_release_tag())

        # Exactly the kind of tag `_tag_release` creates: annotated, unsigned.
        git("tag", "--annotate", "--message=Dafny v4.12.0", "v4.12.0", cwd=self.repo)

        self.assertFalse(release._no_release_tag(),
                         "an existing tag must block the release")

    def test_head_up_to_date_reports_a_failed_fetch(self) -> None:
        # `git fetch` in a repository with no remote at all is a successful no-op,
        # so point `origin` somewhere unreachable to get the failure this guards
        # against: without it, the check falls through to `git status` and passes
        # against stale remote-tracking refs.
        git("remote", "add", "origin", str(self.repo / "no-such-repo"), cwd=self.repo)

        self.assertFalse(Release("4.12.0", "master")._head_up_to_date())

class TestSetNextVersion(ReleaseFixture):
    def test_set_next_version_rewrites_the_build_props(self) -> None:
        # Step 9 of the release checklist, run on the release branch every cycle,
        # and until now exercised only through DryRunRelease -- which does nothing.
        Release("4.12.1", "master").set_next_version()

        self.assertIn("<VersionPrefix>4.12.1</VersionPrefix>",
                      self.build_props.read_text(encoding="utf-8"))

class TestDryRun(ReleaseFixture):
    def test_dry_run_does_not_rewrite_the_build_props(self) -> None:
        # DryRunRelease overrode eight methods but not _update_build_props_file,
        # so a dry run left a bogus version in the tree, contradicting its own
        # help text.
        prepare_release.DryRunRelease("9.9.9", "master").set_next_version()

        self.assertIn("4.11.0", self.build_props.read_text(encoding="utf-8"))
        self.assertEqual(git("status", "--porcelain", cwd=self.repo).stdout, "")

class TestPrepare(ReleaseFixture):
    def test_prepare_writes_notes_deletes_fragments_and_commits(self) -> None:
        self.offline()
        release = Release("4.12.0", "master")

        with mock.patch.object(Release, "_push_release_branch"):
            release.prepare()

        notes = self.release_notes.read_text(encoding="utf-8")
        self.assertIn("# 4.12.0", notes)
        self.assertIn("Fix the thing", notes)
        # The marker has to survive: it is where the next release splices itself in.
        self.assertIn(Release.RELEASE_NOTES_MARKER, notes)
        self.assertIn("# 4.11.0", notes, "older sections must be preserved")

        self.assertFalse(self.fragment_path("1234.fix").exists())
        self.assertEqual(git("branch", "--show-current", cwd=self.repo).stdout.strip(),
                         "release-4.12.0")
        self.assertEqual(git("log", "-1", "--format=%s", cwd=self.repo).stdout.strip(),
                         "Release Dafny 4.12.0")
        self.assertIn("4.12.0", self.build_props.read_text(encoding="utf-8"))

    def test_prepare_refuses_an_unrecognized_fragment_name(self) -> None:
        self.offline()
        self.write_fragment("fix.4328", "A kind-first name")
        self.commit("Add a badly named fragment (#3000)")

        # `assert_one` turns the underlying ValueError into CannotReleaseError,
        # which `main()` reports as exit code 1.
        with self.assertRaises(prepare_release.CannotReleaseError) as caught:
            Release("4.12.0", "master").prepare()

        self.assertIsInstance(caught.exception.__cause__, ValueError)
        # Nothing should have been touched: the failure is a preflight check.
        self.assertEqual(git("status", "--porcelain", cwd=self.repo).stdout, "")
        self.assertEqual(
            git("branch", "--show-current", cwd=self.repo).stdout.strip(), "master")

class TestRelease(ReleaseFixture):
    def test_release_tags_the_release_branch_and_pushes_the_tag(self) -> None:
        origin = self.add_bare_origin()
        git("branch", "release-4.12.0", cwd=self.repo)
        # Move master on, so the release branch is not at HEAD. Without this,
        # "tag the release branch" and "tag HEAD" are indistinguishable and the
        # assertion below would hold even if `_tag_release` tagged the wrong ref.
        (self.repo / "later.txt").write_text("later\n", encoding="utf-8")
        self.commit("A later commit on master (#4000)")

        Release("4.12.0", "master").release()

        self.assertEqual(git("cat-file", "-t", "v4.12.0", cwd=self.repo).stdout.strip(),
                         "tag", "the release tag must be annotated")
        tagged = git("rev-parse", "v4.12.0^{commit}", cwd=self.repo).stdout.strip()
        branch_head = git("rev-parse", "release-4.12.0", cwd=self.repo).stdout.strip()
        head = git("rev-parse", "HEAD", cwd=self.repo).stdout.strip()
        self.assertEqual(tagged, branch_head)
        self.assertNotEqual(tagged, head, "must tag the release branch, not HEAD")
        self.assertIn("refs/tags/v4.12.0", self.refs_of(origin),
                      "the tag must reach origin, which is what triggers the release")

    def test_release_fails_loudly_when_the_tag_push_fails(self) -> None:
        # Pushing the tag is what triggers the publish workflow. A silently
        # ignored failure leaves a local tag and nothing on origin: the release
        # looks done, never publishes, and the local tag now blocks re-running
        # `prepare` via `_no_release_tag`.
        git("remote", "add", "origin", str(self.repo / "no-such-repo"), cwd=self.repo)
        git("branch", "release-4.12.0", cwd=self.repo)

        with self.assertRaises(prepare_release.CannotReleaseError):
            Release("4.12.0", "master").release()

def load_tests(loader, tests, ignore):  # pylint: disable=unused-argument
    """Run the doctests in `prepare_release.py` as part of this suite."""
    tests.addTests(doctest.DocTestSuite(prepare_release))
    return tests

if __name__ == "__main__":
    unittest.main()
