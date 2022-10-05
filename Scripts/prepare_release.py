#!/usr/bin/env python
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
    pr: str
    contents: str
    path: Optional[Path]

    @classmethod
    def from_file(cls, pth: Path) -> "NewsFragment":
        return NewsFragment(pth.stem, pth.read_text(encoding="utf-8"), pth)

class NewsFragments:
    r"""A collection of release note entries.

    >>> import tempfile
    >>> with tempfile.TemporaryDirectory() as tmpdir:
    ...   fpath = Path(tmpdir) / "1234.fix"
    ...   _ = fpath.write_text("Improved toaster settings.\nDafny will not burn toast again.", encoding="utf-8")
    ...   print(NewsFragments.from_directory(tmpdir).render())
    ## Bug fixes
    <BLANKLINE>
    - Improved toaster settings.
      Dafny will not burn toast again.
      (https://github.com/dafny-lang/dafny/pull/1234)
    """

    IGNORED = {".gitignore", "README.md"}
    KNOWN_EXTENSIONS = {".feat": "New features",
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
            for fr in self.fragments[ext]:
                link = f"(https://github.com/dafny-lang/dafny/pull/{fr.pr})"
                entry = indent(f"- {fr.contents}\n{link}", "  ").lstrip()
                rendered.append(entry)
        return "\n\n".join(rendered)

    def delete(self):
        for _, fragment in self.fragments.items():
            for fr in fragment:
                if fr.path is not None:
                    fr.path.unlink()

class Version(NamedTuple):
    VERSION_NUMBER_PATTERN = re.compile("^(?P<prefix>[0-9]+[.][0-9]+[.][0-9]+)(?P<suffix>-.+)?$")

    prefix: str # Main version number (1.2.3)
    date: datetime.date # Release date
    suffix: str # Optional marker ("alpha")

    @classmethod
    def from_string(cls, vernum: str, date: Optional[datetime.date]=None) -> Optional["Version"]:
        """Parse a short version string into a `Version` object."""
        if m := cls.VERSION_NUMBER_PATTERN.match(vernum):
            prefix, suffix = m.group("prefix", "suffix")
            date = date or datetime.date.today()
            return Version(prefix, date, suffix or "")
        return None

    @property
    def year_delta(self):
        return self.date.year - 2018

    @property
    def short(self):
        return f"{self.prefix}{self.suffix}"

    @property
    def timestamp(self):
        return str((self.year_delta * 100 + self.date.month) * 100 + self.date.day)

    @property
    def full(self):
        return f"{self.prefix}.{self.timestamp}{self.suffix}"

    @property
    def comment(self):
        return (f"Version {self.short}, year 2018+{self.year_delta}, " +
                f"month {self.date.month}, day {self.date.day}.")

class Release:
    NEWSFRAGMENTS_PATH = "docs/dev/news"

    def __init__(self, version: str) -> None:
        self.version = version
        self.remote = "origin"
        self.branch_name = f"release-{version}"
        self.branch_path = f"refs/heads/{self.branch_name}"
        self.master_branch = "refs/heads/master"
        self.tag = f"v{version}"
        self.build_props_path = Path("Source/Directory.Build.props")
        self.release_notes_md_path = Path("RELEASE_NOTES.md")
        self.newsfragments = NewsFragments.from_directory(self.NEWSFRAGMENTS_PATH)

    @staticmethod
    def in_git_root() -> bool:
        return Path(".git").exists()

    def has_origin(self) -> bool:
        return git("remote", "url", self.remote).returncode == 0

    @staticmethod
    def has_git() -> bool:
        return git("rev-parse", "--verify", "HEAD").returncode == 0

    def has_news(self) -> bool:
        self.newsfragments.check()
        return bool(self.newsfragments.fragments)

    def build_props_file_exists(self) -> bool:
        return self.build_props_path.is_file()

    def parse_build_props_file(self) -> ElementTree.ElementTree:
        parser = ElementTree.XMLParser(target=ElementTree.TreeBuilder(insert_comments=True))
        return ElementTree.parse(self.build_props_path, parser=parser)

    def build_props_file_parses(self) -> bool:
        try:
            self.parse_build_props_file()
            return True
        except ElementTree.ParseError as e:
            print(e)
            return False

    def release_notes_file_exists(self) -> bool:
        return self.release_notes_md_path.is_file()

    RELEASE_NOTES_MARKER = "See [docs/dev/news/](docs/dev/news/)."
    def release_notes_have_header(self) -> bool:
        contents = self.release_notes_md_path.read_text(encoding="utf-8")
        return self.RELEASE_NOTES_MARKER in contents

    def version_number_is_fresh(self) -> bool:
        contents = self.release_notes_md_path.read_bytes()
        return b"# " + self.version.encode("utf-8") not in contents

    @staticmethod
    def get_branch(check: bool) -> str:
        return git("symbolic-ref", "--quiet", "HEAD", check=check).stdout.strip()

    def parse_vernum(self) -> Optional[Version]:
        return Version.from_string(self.version)

    def is_release_branch(self) -> bool:
        return self.get_branch(check=False) in (self.master_branch, self.branch_path)

    @staticmethod
    def is_repo_clean() -> bool:
        return git("status", "--short", "--untracked-files=no").stdout.strip() == ""

    @classmethod
    def head_up_to_date(cls) -> bool:
        git("fetch")
        return "behind" not in git("status", "--short", "--branch").stdout

    @staticmethod
    def no_release_blocking_issues() -> bool:
        progress("Checking... ", end="")
        HEADERS = {"Accept": "application/vnd.github.v3+json"}
        ENDPOINT = 'https://api.github.com/repos/dafny-lang/dafny/issues?labels=severity%3A+release-blocker'
        with urlopen(Request(ENDPOINT, data=None, headers=HEADERS)) as fs:
            response = fs.read().decode("utf-8")
        return json.loads(response) == []

    def no_release_branch(self) -> bool:
        return git("rev-parse", "--quiet", "--verify", self.branch_path).returncode == 1

    def no_release_tag(self) -> bool:
        return git("tag", "--verify", self.tag).returncode == 1

    def update_build_props_file(self) -> None:
        vernum = Version.from_string(self.version)
        assert vernum
        xml = self.parse_build_props_file()
        for version_element in xml.iter("VersionPrefix"):
            tail = version_element.tail
            version_element.clear()
            version_element.tail = tail
            version_element.text = vernum.full
            comment = ElementTree.Comment(vernum.comment)
            version_element.append(comment)
        xml.write(self.build_props_path, encoding="utf-8")

    def create_release_branch(self):
        git("checkout", "-b", self.branch_name, check=True)

    def consolidate_news_fragments(self):
        news = self.newsfragments.render()
        new_section = f"\n\n# {self.version}\n\n{news.rstrip()}"
        contents = self.release_notes_md_path.read_text(encoding="utf-8")
        nl = "\r\n" if "\r\n" in contents else "\n"
        replacement = self.RELEASE_NOTES_MARKER + new_section.replace("\n", nl)
        contents = contents.replace(self.RELEASE_NOTES_MARKER, replacement)
        self.release_notes_md_path.write_text(contents, encoding="utf-8")

    def delete_news_fragments(self):
        self.newsfragments.delete()

    def commit_changes(self):
        git("commit", "--quiet", "--all",
            "--no-verify", "--no-post-rewrite",
            f"--message=Release Dafny {self.version}",
            check=True)

    def push_release_branch(self):
        git("push", "--force-with-lease", "--set-upstream",
            self.remote, f"{self.branch_path}:{self.branch_path}",
            check=True)

    # Still TODO:
    # - Run deep test as part of release workflow

    def prepare(self):
        assert_one("Can we run `git`?",
                   self.has_git)
        assert_one(f"Is {self.version} a valid version number?",
                   self.parse_vernum)
        assert_one("Are we running from the root of a git repo?",
                   self.in_git_root)
        assert_one(f"Can we find `{self.build_props_path}`?",
                   self.build_props_file_exists)
        assert_one(f"Can we parse `{self.build_props_path}`?",
                   self.build_props_file_parses)
        assert_one(f"Can we find `{self.release_notes_md_path}`?",
                   self.release_notes_file_exists)
        assert_one(f"Does `{self.release_notes_md_path}` have a header?",
                   self.release_notes_have_header)
        assert_one(f"Can we create a section for `{self.version}` in `{self.release_notes_md_path}`?",
                   self.version_number_is_fresh)
        assert_one(f"Do we have news in {self.NEWSFRAGMENTS_PATH}?",
                   self.has_news)
        assert_one(f"Is the current branch `master` or `{self.branch_name}`?",
                   self.is_release_branch)
        assert_one("Is repo clean (all changes committed)?",
                   self.is_repo_clean)
        assert_one("Is HEAD is up to date?",
                   self.head_up_to_date)
        assert_one("Are all release-blocking issues closed?",
                   self.no_release_blocking_issues)
        assert_one(f"Can we create release tag `{self.tag}`?",
                   self.no_release_tag)
        if self.get_branch(check=False) != self.branch_path:
            assert_one(f"Can we create release branch `{self.branch_name}`?",
                       self.no_release_branch)
            run_one(f"Creating release branch {self.branch_path}...",
                    self.create_release_branch)
        else:
            progress("Note: Release branch already checked out, so not creating it.")
        run_one(f"Updating `{self.build_props_path}`...",
                self.update_build_props_file)
        run_one(f"Updating `{self.release_notes_md_path}` from `{self.NEWSFRAGMENTS_PATH}`...",
                self.consolidate_news_fragments)
        run_one("Creating commit...",
                self.commit_changes)
        run_one("Pushing release branch...",
                self.push_release_branch)
        run_one("Deleting news fragments...",
                self.delete_news_fragments)

        progress("Done!")
        progress()

        DEEPTESTS_URL = "https://github.com/dafny-lang/dafny/actions/workflows/deep-tests.yml"
        progress(f"Now, start a deep-tests workflow manually for branch {self.branch_name} at\n"
                 f"<{DEEPTESTS_URL}>.\n"
                 "Once it completes, re-run this script with argument `release`.")
        progress()

    def tag_release(self):
        git("tag", "--annotate", f"--message=Dafny {self.tag}",
            self.tag, self.branch_path, capture_output=False).check_returncode()

    def push_release_tag(self):
        git("push", self.remote, f"{self.tag}",
            capture_output=False).check_returncode()

    def release(self):
        run_one("Tagging release...",
                self.tag_release)
        run_one("Pushing tag...",
                self.push_release_tag)

        progress("Done!")
        progress()

        PR_URL = f"https://github.com/dafny-lang/dafny/pull/new/{self.branch_name}"
        progress("You can merge this branch by opening a PR at\n"
                 f"<{PR_URL}>.")

def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Dafny release helper")
    parser.add_argument("version", help="Version number for this release (A.B.C-xyz)")
    parser.add_argument("action", help="Which part of the release process to run",
                        choices=["prepare", "release"])
    return parser.parse_args()

def main() -> None:
    args = parse_arguments()
    try:
        release = Release(args.version)
        {"prepare": release.prepare,
         "release": release.release}[args.action]()
    except CannotReleaseError:
        sys.exit(1)

if __name__ == "__main__":
    main()
