#!/usr/bin/env python3

from fnmatch import fnmatch
from os import path
import argparse
import json
import os
import stat
import re
import subprocess
import sys
import time
from urllib import request
from http.client import IncompleteRead
from urllib.error import HTTPError
import zipfile
import shutil
import ntpath

# Configuration

Z3_VERSIONS = [ "4.8.5", "4.12.1" ]
Z3_URL_BASE = "https://github.com/dafny-lang/solver-builds/releases/download/snapshot-2023-02-17"

## How many times we allow ourselves to try to download Z3
Z3_MAX_DOWNLOAD_ATTEMPTS = 5

## Allowed Dafny release names
DAFNY_RELEASE_REGEX = re.compile("\\d+\\.\\d+\\.\\d+(-[\w\d_-]+)?$")

## Where are the sources?
SOURCE_DIRECTORY = "Source"

## Where do the binaries get put?
BINARIES_DIRECTORY = "Binaries"
## Where do we store the built packages and cache files?
DESTINATION_DIRECTORY = "Package"

## What's the root folder of the archive?
DAFNY_PACKAGE_PREFIX = path.join("dafny")
## What sub-folder of the packages does z3 go into?
Z3_PACKAGE_PREFIX = path.join("z3", "bin")

## On unix systems, which Dafny files should be marked as executable? (Glob syntax; Z3's permissions are preserved)
UNIX_EXECUTABLES = ["dafny", "dafny-server"]

# Constants

THIS_FILE = path.realpath(__file__)
ROOT_DIRECTORY = path.dirname(path.dirname(THIS_FILE))
SOURCE_DIRECTORY = path.join(ROOT_DIRECTORY, SOURCE_DIRECTORY)
BINARIES_DIRECTORY = path.join(ROOT_DIRECTORY, BINARIES_DIRECTORY)
DESTINATION_DIRECTORY = path.join(ROOT_DIRECTORY, DESTINATION_DIRECTORY)
CACHE_DIRECTORY = path.join(DESTINATION_DIRECTORY, "cache")

OTHERS = ( [ "Scripts/quicktest.sh" , "Scripts/quicktest.out", "Scripts/allow_on_mac.sh" ] ) ## Other files to include in zip
OTHER_UPLOADS = ( ["docs/DafnyRef/out/DafnyRef.pdf"] )

gitHubToDotNetOSMapping = {
    "ubuntu": "linux",
    "macos": "osx",
    "windows": "win"
}


def flush(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()

class Release:

    def __init__(self, os, platform, version, out):
        self.z3_zips = [ "z3-{}-{}-bin.zip".format(z3_version, os) for z3_version in Z3_VERSIONS ]
        self.platform, self.os = platform, os
        self.os_name = self.os.split("-")[0]
        self.dafny_name = "dafny-{}-{}-{}.zip".format(version, self.platform, self.os)
        if out != None:
            self.dafny_name = out
        self.target = "{}-{}".format(gitHubToDotNetOSMapping[self.os_name], self.platform)
        self.dafny_zip = path.join(DESTINATION_DIRECTORY, self.dafny_name)
        self.buildDirectory = path.join(BINARIES_DIRECTORY, self.target, "publish")

    def url(self, z3_zip):
        return "{}/{}".format(Z3_URL_BASE, z3_zip)

    def local_zip(self, z3_zip):
        return path.join(CACHE_DIRECTORY, z3_zip)

    @property
    def cached(self):
        for z3_zip in self.z3_zips:
          if not path.exists(self.local_zip(z3_zip)):
              return False
        return True

    def download(self):
        if self.cached:
            print("cached!")
        else:
            flush("downloading ...")
            for z3_zip in self.z3_zips:
                for currentAttempt in range(Z3_MAX_DOWNLOAD_ATTEMPTS):
                    try:
                        with request.urlopen(self.url(z3_zip)) as reader:
                            with open(self.local_zip(z3_zip), mode="wb") as writer:
                                writer.write(reader.read())
                        flush("done!")
                        break
                    except (IncompleteRead, HTTPError):
                        if currentAttempt == Z3_MAX_DOWNLOAD_ATTEMPTS - 1:
                            raise


    @staticmethod
    def zipify_path(fpath):
        """Zip entries always use '/' as the path separator."""
        return fpath.replace(os.path.sep, '/')

    def run_publish(self, project, framework = None):
        env = dict(os.environ)
        env["RUNTIME_IDENTIFIER"] = self.target
        flush("   + Publishing " + project)
        remaining = 3
        exitStatus = 1
        while 0 < remaining and exitStatus != 0:
            remaining -= 1
            publish_args = [
                "--nologo",
                "-o", self.buildDirectory,
                "-r", self.target,
                "--self-contained",
                "-c", "Release", 
                *(["-f", framework] if framework else [])]
            projectFile = path.join(SOURCE_DIRECTORY, project, project + ".csproj")
            exitStatus = subprocess.call(["dotnet", "publish", projectFile, *publish_args], env=env)
            if exitStatus != 0:
                if remaining == 0:
                    flush("failed! (Is Dafny or the Dafny server running?)")
                    sys.exit(1)
                else:
                    flush("failed! (Retrying another %s)" %
                        ("time" if remaining == 1 else f"{remaining} times"))
        flush("done!")

    def build(self):
        os.chdir(ROOT_DIRECTORY)
        flush("  - Building")

        if path.exists(self.buildDirectory):
            shutil.rmtree(self.buildDirectory)
        run(["make", "--quiet", "clean"])
        self.run_publish("DafnyLanguageServer")
        self.run_publish("DafnyServer")
        self.run_publish("DafnyRuntime", "netstandard2.0")
        self.run_publish("DafnyRuntime", "net452")
        self.run_publish("Dafny")

    def pack(self):
        try:
            os.remove(self.dafny_zip)
        except FileNotFoundError:
            pass
        missing = []
        with zipfile.ZipFile(self.dafny_zip, 'w',  zipfile.ZIP_DEFLATED) as archive:
            z3_files_count = 0
            for z3_zip in self.z3_zips:
                with zipfile.ZipFile(self.local_zip(z3_zip)) as Z3_archive:
                    for fileinfo in Z3_archive.infolist():
                        fname = fileinfo.filename
                        z3_files_count += 1
                        contents = Z3_archive.read(fileinfo)
                        fileinfo.filename = Release.zipify_path(path.join(DAFNY_PACKAGE_PREFIX, Z3_PACKAGE_PREFIX, fname))
                        if self.os_name != 'windows':
                            # http://stackoverflow.com/questions/434641/
                            fileinfo.external_attr = 0o100755 << 16
                            fileinfo.create_system = 3  # lie about this zip file's source OS to preserve permissions
                        archive.writestr(fileinfo, contents)
            uppercaseDafny = path.join(self.buildDirectory, "Dafny")
            if os.path.exists(uppercaseDafny):
                lowercaseDafny = path.join(self.buildDirectory, "dafny")
                shutil.move(uppercaseDafny, lowercaseDafny)
                os.chmod(lowercaseDafny, stat.S_IEXEC| os.lstat(lowercaseDafny).st_mode)
            for fpath in pathsInDirectory(self.buildDirectory) + OTHERS:
                if os.path.isdir(fpath) or fpath.endswith(".pdb"):
                    continue
                fname = ntpath.basename(fpath)
                if path.exists(fpath):
                    fileinfo = zipfile.ZipInfo(fname, time.localtime(os.stat(fpath).st_mtime)[:6])
                    if self.os_name != 'windows':
                        # http://stackoverflow.com/questions/434641/
                        fileinfo.external_attr = 0o100755 << 16
                        fileinfo.create_system = 3  # lie about this zip file's source OS to preserve permissions
                    contents = open(fpath, mode='rb').read()
                    fileinfo.compress_type = zipfile.ZIP_DEFLATED
                    fileinfo.filename = Release.zipify_path(path.join(DAFNY_PACKAGE_PREFIX, fname))
                    archive.writestr(fileinfo, contents)
                else:
                    missing.append(fname)
        for fpath in OTHER_UPLOADS:
            shutil.copy(fpath, DESTINATION_DIRECTORY)
        flush("done! (imported {} files from z3's sources)".format(z3_files_count))
        if missing:
            flush("      WARNING: Not all files were found: {} were missing".format(", ".join(missing)))

def path_leaf(path):
    head, tail = ntpath.split(path)
    return tail or ntpath.basename(head)

def pathsInDirectory(directory):
    return [path.join(directory, file) for file in os.listdir(directory)]

def download(releases):
    flush("  - Downloading {} z3 archives".format(len(releases)))
    for release in releases:
        flush("    + {}-{}:".format(release.os, release.platform), end=' ')
        release.download()

def run(cmd):
    flush("    + {}...".format(" ".join(cmd)), end=' ')
    retv = subprocess.call(cmd)
    if retv != 0:
        flush("failed! (Is Dafny or the Dafny server running?)")
        sys.exit(1)
    else:
        flush("done!")

def pack(args, releases):
    flush("  - Packaging {} Dafny archives".format(len(releases)))
    for release in releases:
        flush("    + {}:".format(release.dafny_name), end=' ')
        release.build()
        release.pack()
    if not args.skip_manual:
        run(["make", "--quiet", "refman"])

def check_version_cs(args):
    # Checking Directory.Build.props
    with open(path.join(SOURCE_DIRECTORY, "Directory.Build.props")) as fp:
        match = re.search(r'\<VersionPrefix\>([0-9]+.[0-9]+.[0-9]+).([0-9]+)', fp.read())
        if match:
            (v1, v2) = match.groups()
        else:
            flush("The AssemblyVersion attribute in Directory.Build.props could not be found.")
            return False
    now = time.localtime()
    year = now[0]
    month = now[1]
    day = now[2]
    v3 = str(year-2018) + str(month).zfill(2) + str(day).zfill(2)
    if v2 != v3:
        flush("The date in Directory.Build.props does not agree with today's date: " + v3 + " vs. " + v2)
    if "-" in args.version:
        hy = args.version[:args.version.index('-')]
    else:
        hy = args.version
    if hy != v1:
        flush("The version number in Directory.Build.props does not agree with the given version: " + hy + " vs. " + v1)
    if (v2 != v3 or hy != v1):
        return False
    flush("Creating release files for release \"" + args.version + "\" and internal version information: " + v1 + "." + v2)
    return True

def parse_arguments():
    parser = argparse.ArgumentParser(description="Prepare a Dafny release. Configuration is hardcoded; edit the `# Configuration' section of this script to change it.")
    parser.add_argument("version", help="Version number for this release")
    parser.add_argument("--os", help="operating system name for which to make a release")
    parser.add_argument("--platform", help="platform for which to make a release")
    parser.add_argument("--skip_manual", help="do not create the reference manual")
    parser.add_argument("--trial", help="ignore Directory.Build.props version discrepancies")
    parser.add_argument("--github_secret", help="access token for making an authenticated GitHub call, to prevent being rate limited.")
    parser.add_argument("--out", help="output zip file")
    return parser.parse_args()

def main():
    args = parse_arguments()
    if not args.trial:
        if not DAFNY_RELEASE_REGEX.match(args.version):
            flush("Release number is in wrong format: should be d.d.d or d.d.d-text without spaces")
            return
        if not check_version_cs(args):
            return

    os.makedirs(CACHE_DIRECTORY, exist_ok=True)

    # Z3
    flush("* Downloading Z3 releases")
    releases = [ Release("macos-11",       "x64", args.version, args.out),
                 Release("macos-11",     "arm64", args.version, args.out),
                 Release("ubuntu-20.04",   "x64", args.version, args.out),
                 Release("windows-2019",   "x64", args.version, args.out) ]
    if args.os:
        releases = list(filter(lambda release: release.os_name == args.os, releases))
    if args.platform:
        releases = list(filter(lambda release: release.platform == args.platform, releases))
    download(releases)

    flush("* Building and packaging Dafny")
    pack(args, releases)

if __name__ == '__main__':
    main()
