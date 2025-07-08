#!/usr/bin/env python3
import argparse
import json
import re
import subprocess
import sys

import datetime
from pathlib import Path
from textwrap import indent
from urllib.request import Request, urlopen
from shlex import quote
from xml.etree import ElementTree

from typing import Any, Callable, Dict, List, Optional, TypeVar, NamedTuple

SKIP_ALL_CHECKS = False

class CannotReleaseError(Exception):
    pass

def progress(msg: str="", **kwargs) -> None:
    print(msg, **{"file": sys.stderr, "flush": True, **kwargs})

def git(cmd: str, *args: str, **kwargs) -> subprocess.CompletedProcess:
    return subprocess.run(["git", cmd, *args], # pylint: disable=subprocess-run-check
        **{"capture_output": True, "check": False, "encoding": "utf-8", **kwargs})

A = TypeVar(name="A")
def with_error(fn: Callable[[], A]) -> A:
    try:
        return fn()
    except Exception as e:
        progress(f"failed: {e}")
        if isinstance(e, subprocess.CalledProcessError):
            progress("Process output: ")
            progress(e.stdout)
            progress(e.stderr)
        raise CannotReleaseError() from e

def assert_one(msg: str, condition: Callable[[], Any]):
    assert msg.endswith("?")
    progress(msg + " ", end="")
    if not SKIP_ALL_CHECKS and not with_error(condition):
        progress("no, exiting.")
        raise CannotReleaseError()
    progress("yes.")

def run_one(msg: str, operation: Callable[[], None]):
    assert msg.endswith("...")
    progress(msg + " ", end="")
    with_error(operation)
    progress("done.")

def unwrap(opt: Optional[A]) -> A:
    assert opt
    return opt

class NewsFragment(NamedTuple):
    pr: Optional[int]
    contents: str
    path: Optional[Path]

    PR_NUM_FORMAT = re.compile(r"[(]#(?P<num>[0-9]+)[)]$", re.MULTILINE)

    @classmethod
    def resolve_pr_from_git(cls, pth: Path) -> Optional[int]:
        """Find the PR that introduced `pth`."""
        proc = git("log", "--diff-filter=A", "--format=oneline", "--", str(pth))
        if proc.returncode == 0:
            if m := cls.PR_NUM_FORMAT.search(proc.stdout.strip()):
                return int(m.group("num"))
        return None

    @classmethod
    def resolve_pr(cls, pth: Path) -> Optional[int]:
        if re.match("^[0-9]+$", pth.stem):
            return int(pth.stem)
        return cls.resolve_pr_from_git(pth)

    @classmethod
    def from_file(cls, pth: Path) -> "NewsFragment":
        return NewsFragment(cls.resolve_pr(pth), pth.read_text(encoding="utf-8"), pth)

    @property
    def link(self) -> str:
        if self.pr is not None:
            return f"(https://github.com/dafny-lang/dafny/pull/{self.pr})"
        return ""

    @property
    def sortkey(self):
        return self.pr, self.path

class NewsFragments:
    r"""A collection of release note entries.

    >>> import tempfile
    >>> with tempfile.TemporaryDirectory() as tmpdir:
    ...   fpath = Path(tmpdir) / "1234.fix"
    ...   _ = fpath.write_text("Dafny will now detect and report burning toast.\n\n", encoding="utf-8")
    ...   fpath = Path(tmpdir) / "5678.feat"
    ...   _ = fpath.write_text("Two new toast patterns:\n- Dafny waterfall logo\n- Dafny haircut logo\n(They are the same.)", encoding="utf-8")
    ...   print(NewsFragments.from_directory(tmpdir).render())
    ## New features
    <BLANKLINE>
    - Two new toast patterns:
      - Dafny waterfall logo
      - Dafny haircut logo
      (They are the same.)
      (https://github.com/dafny-lang/dafny/pull/5678)
    <BLANKLINE>
    ## Bug fixes
    <BLANKLINE>
    - Dafny will now detect and report burning toast. (https://github.com/dafny-lang/dafny/pull/1234)
    """

    IGNORED = {".gitignore", "README.md"}
    KNOWN_EXTENSIONS = {".break": "Breaking changes",
                        ".feat": "New features",
                        ".fix": "Bug fixes"}

    def __init__(self) -> None:
        self.fragments: Dict[str, List[NewsFragment]] = {}
        self.unrecognized: List[Path] = []

    @staticmethod
    def from_directory(dirpath: str) -> "NewsFragments":
        ns = NewsFragments()
        ns._read_directory(Path(dirpath))
        return ns

    def _read_directory(self, dirpath: Path) -> None:
        if dirpath.exists():
            for fpath in dirpath.iterdir():
                if fpath.suffix in self.KNOWN_EXTENSIONS:
                    fragment = NewsFragment.from_file(fpath)
                    self.fragments.setdefault(fpath.suffix, []).append(fragment)
                elif fpath.name not in self.IGNORED:
                    self.unrecognized.append(fpath)

    def check(self):
        if self.unrecognized:
            names = ', '.join(quote(f.name) for f in sorted(self.unrecognized))
            raise ValueError(f"Not sure what to do with {names}.")

    def render(self) -> str:
        rendered = []
        for ext, title in self.KNOWN_EXTENSIONS.items():
            if ext not in self.fragments:
                continue
            rendered.append(f"## {title}")
            for fr in sorted(self.fragments[ext], key=lambda f: f.sortkey):
                contents = fr.contents.strip()
                sep = "\n" if fr.link and "\n" in contents else " "
                entry = indent(f"- {contents}{sep}{fr.link}", "  ").lstrip()
                rendered.append(entry)
        return "\n\n".join(rendered)

    def delete(self):
        for _, fragment in self.fragments.items():
            for fr in fragment:
                if fr.path is not None:
                    fr.path.unlink()

class Version(NamedTuple):
    """Support functions for version numbers.

    >>> v = Version.from_string("3.8.2-xyz")
    >>> v.string
    '3.8.2-xyz'
    """

    VERSION_NUMBER_PATTERN = re.compile("^(?P<prefix>[0-9]+[.][0-9]+[.][0-9]+)(?P<identifier>-.+)?$")

    main: str # Main version number (1.2.3)
    identifier: str # Optional marker ("alpha")

    @classmethod
    def from_string(cls, vernum: str) -> Optional["Version"]:
        """Parse a short version string into a `Version` object."""
        if m := cls.VERSION_NUMBER_PATTERN.match(vernum):
            prefix, identifier = m.group("prefix", "identifier")
            return Version(prefix, identifier or "")
        return None

    @property
    def string(self):
        return f"{self.main}{self.identifier}"

class Release:
    REMOTE = "origin"
    NEWSFRAGMENTS_PATH = "docs/dev/news"

    def __init__(self, version: str, source_branch: str) -> None:
        self.version = version
        self.source_branch_name = source_branch
        self.source_branch_path = f"refs/heads/{self.source_branch_name}"
        self.release_branch_name = f"release-{version}"
        self.release_branch_path = f"refs/heads/{self.release_branch_name}"
        self.tag = f"v{version}"
        self.build_props_path = Path("Source/Directory.Build.props")
        self.release_notes_md_path = Path("RELEASE_NOTES.md")
        self.newsfragments = NewsFragments.from_directory(self.NEWSFRAGMENTS_PATH)

    @staticmethod
    def _in_git_root() -> bool:
        return Path(".git").exists()

    def _has_origin(self) -> bool:
        return git("remote", "url", self.REMOTE).returncode == 0

    @staticmethod
    def _has_git() -> bool:
        return git("rev-parse", "--verify", "HEAD").returncode == 0

    def _has_news(self) -> bool:
        self.newsfragments.check()
        return bool(self.newsfragments.fragments)

    def _build_props_file_exists(self) -> bool:
        return self.build_props_path.is_file()

    def _parse_build_props_file(self) -> ElementTree.ElementTree:
        parser = ElementTree.XMLParser(target=ElementTree.TreeBuilder(insert_comments=True))
        return ElementTree.parse(self.build_props_path, parser=parser)

    def _build_props_file_parses(self) -> bool:
        try:
            self._parse_build_props_file()
            return True
        except ElementTree.ParseError as e:
            print(e)
            return False

    def _release_notes_file_exists(self) -> bool:
        return self.release_notes_md_path.is_file()

    RELEASE_NOTES_MARKER = "See [docs/dev/news/](docs/dev/news/)."
    def _release_notes_have_header(self) -> bool:
        contents = self.release_notes_md_path.read_text(encoding="utf-8")
        return self.RELEASE_NOTES_MARKER in contents

    def _version_number_is_fresh(self) -> bool:
        contents = self.release_notes_md_path.read_bytes()
        return b"# " + self.version.encode("utf-8") not in contents

    @staticmethod
    def _get_branch(check: bool) -> str:
        return git("symbolic-ref", "--quiet", "HEAD", check=check).stdout.strip()

    def _parse_vernum(self) -> Optional[Version]:
        return Version.from_string(self.version)

    def _is_release_branch(self) -> bool:
        return self._get_branch(check=False) in (self.source_branch_path, self.release_branch_path)

    @staticmethod
    def _is_repo_clean() -> bool:
        return git("status", "--short", "--untracked-files=no").stdout.strip() == ""

    @classmethod
    def _head_up_to_date(cls) -> bool:
        git("fetch")
        return "behind" not in git("status", "--short", "--branch").stdout

    @staticmethod
    def _no_release_blocking_issues() -> bool:
        progress("Checking... ", end="")
        HEADERS = {"Accept": "application/vnd.github.v3+json"}
        ENDPOINTS = (
            "https://api.github.com/repos/dafny-lang/dafny/issues?labels=release-blocker",
            "https://api.github.com/repos/dafny-lang/ide-vscode/issues?labels=severity%3A+release-blocker",
        )
        for endpoint in ENDPOINTS:
            with urlopen(Request(endpoint, data=None, headers=HEADERS)) as fs:
                response = fs.read().decode("utf-8")
                if json.loads(response) != []:
                    return False
        return True

    def _no_release_branch(self) -> bool:
        return git("rev-parse", "--quiet", "--verify", self.release_branch_path).returncode == 1

    def _no_release_tag(self) -> bool:
        return git("tag", "--verify", self.tag).returncode == 1

    def _update_build_props_file(self) -> None:
        vernum = Version.from_string(self.version)
        assert vernum
        xml = self._parse_build_props_file()
        for version_element in xml.iter("VersionPrefix"):
            tail = version_element.tail
            version_element.clear()
            version_element.tail = tail
            version_element.text = vernum.string
        xml.write(self.build_props_path, encoding="utf-8")

    def _create_release_branch(self):
        git("checkout", "-b", self.release_branch_name, check=True)

    def _consolidate_news_fragments(self):
        news = self.newsfragments.render()
        new_section = f"\n\n# {self.version}\n\n{news.rstrip()}"
        contents = self.release_notes_md_path.read_text(encoding="utf-8")
        nl = "\r\n" if "\r\n" in contents else "\n"
        replacement = self.RELEASE_NOTES_MARKER + new_section.replace("\n", nl)
        contents = contents.replace(self.RELEASE_NOTES_MARKER, replacement)
        self.release_notes_md_path.write_text(contents, encoding="utf-8")

    def _delete_news_fragments(self):
        self.newsfragments.delete()

    def _commit_changes(self):
        git("commit", "--quiet", "--all",
            "--no-verify", "--no-post-rewrite",
            f"--message=Release Dafny {self.version}",
            check=True)

    def _push_release_branch(self):
        git("push", "--force-with-lease", "--set-upstream",
            self.REMOTE, f"{self.release_branch_path}:{self.release_branch_path}",
            check=True)

    def set_next_version(self):
        assert_one(f"Is {self.version} a valid version number?",
                   self._parse_vernum)
        assert_one(f"Can we find `{self.build_props_path}`?",
                   self._build_props_file_exists)
        assert_one(f"Can we parse `{self.build_props_path}`?",
                   self._build_props_file_parses)
        assert_one(f"Can we create a section for `{self.version}` in `{self.release_notes_md_path}`?",
                   self._version_number_is_fresh)
        run_one(f"Updating `{self.build_props_path}`...",
                self._update_build_props_file)

    # Still TODO:
    # - Run deep test as part of release workflow

    def prepare(self):
        assert_one("Can we run `git`?",
                   self._has_git)
        assert_one(f"Is {self.version} a valid version number?",
                   self._parse_vernum)
        assert_one("Are we running from the root of a git repo?",
                   self._in_git_root)
        assert_one(f"Can we find `{self.build_props_path}`?",
                   self._build_props_file_exists)
        assert_one(f"Can we parse `{self.build_props_path}`?",
                   self._build_props_file_parses)
        assert_one(f"Can we find `{self.release_notes_md_path}`?",
                   self._release_notes_file_exists)
        assert_one(f"Does `{self.release_notes_md_path}` have a header?",
                   self._release_notes_have_header)
        assert_one(f"Can we create a section for `{self.version}` in `{self.release_notes_md_path}`?",
                   self._version_number_is_fresh)
        assert_one(f"Do we have news in {self.NEWSFRAGMENTS_PATH}?",
                   self._has_news)
        assert_one(f"Is the current branch `{self.source_branch_name}` or `{self.release_branch_name}`?",
                   self._is_release_branch)
        assert_one("Is repo clean (all changes committed)?",
                   self._is_repo_clean)
        assert_one("Is HEAD is up to date?",
                   self._head_up_to_date)
        assert_one("Are all release-blocking issues closed in both dafny and ide-vscode?",
                   self._no_release_blocking_issues)
        assert_one(f"Can we create release tag `{self.tag}`?",
                   self._no_release_tag)
        if self._get_branch(check=False) != self.release_branch_path:
            assert_one(f"Can we create release branch `{self.release_branch_name}`?",
                       self._no_release_branch)
            run_one(f"Creating release branch {self.release_branch_path}...",
                    self._create_release_branch)
        else:
            progress("Note: Release branch already checked out, so not creating it.")
        run_one(f"Updating `{self.build_props_path}`...",
                self._update_build_props_file)
        run_one(f"Updating `{self.release_notes_md_path}` from `{self.NEWSFRAGMENTS_PATH}`...",
                self._consolidate_news_fragments)
        run_one("Deleting news fragments...",
                self._delete_news_fragments)
        run_one("Creating commit...",
                self._commit_changes)
        run_one("Pushing release branch...",
                self._push_release_branch)

        progress("Done!")
        progress()

        DEEPTESTS_URL = "https://github.com/dafny-lang/dafny/actions/workflows/nightly-build.yml"
        progress(f"Now, start a deep-tests workflow manually for branch {self.release_branch_name} at\n"
                 f"<{DEEPTESTS_URL}>\n"
                 f"To do so, click Run workflow, use workflow from {self.release_branch_name},\n"
                 f"Once it completes, just re-run this script as `./Scripts/prepare_release.py {self.version} release` to tag the branch and push it to trigger the release.")
        progress()

    def _tag_release(self):
        git("tag", "--annotate", f"--message=Dafny {self.tag}",
            self.tag, self.release_branch_path, capture_output=False).check_returncode()

    def _push_release_tag(self):
        git("push", self.REMOTE, f"{self.tag}",
            capture_output=False).check_returncode()

    def release(self):
        run_one("Tagging release...",
                self._tag_release)
        run_one("Pushing tag...",
                self._push_release_tag)

        progress("Done!")
        progress()

        PR_URL = f"https://github.com/dafny-lang/dafny/pull/new/{self.release_branch_name}"
        progress("You can merge this branch by opening a PR at\n"
                 f"<{PR_URL}>.")

class DryRunRelease(Release):
    def _create_release_branch(self):
        pass
    def _consolidate_news_fragments(self):
        pass
    def _delete_news_fragments(self):
        pass
    def _commit_changes(self):
        pass
    def _push_release_branch(self):
        pass
    def _create_release_branch(self):
        pass
    def _tag_release(self):
        pass
    def _push_release_tag(self):
        pass
    def _push_release_tag(self):
        pass

def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Dafny release helper")
    parser.add_argument("--dry-run", help="Do not make any modifications (no file updates, no git commands).",
                        action="store_true")
    parser.add_argument("--source-branch", help="Which branch to release from (optional, defaults to 'master')", default="master")
    parser.add_argument("version", help="Version number for this release (A.B.C-xyz)")
    parser.add_argument("action", help="Which part of the release process to run",
                        choices=["prepare", "release", "set-next-version"])
    return parser.parse_args()

def main() -> None:
    args = parse_arguments()
    try:
        release = (DryRunRelease if args.dry_run else Release)(args.version, args.source_branch)
        {"prepare": release.prepare,
         "set-next-version": release.set_next_version,
         "release": release.release}[args.action]()
    except CannotReleaseError:
        sys.exit(1)

if __name__ == "__main__":
    main()
