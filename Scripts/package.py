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

## Where do we fetch the list of releases from?
## Get the latest Z3 release like this:
## Z3_RELEASES_URL = "https://api.github.com/repos/Z3Prover/z3/releases/latest"
## Get a specific Z3 release like this:
Z3_RELEASES_URL = "https://api.github.com/repos/Z3Prover/z3/releases/tags/Z3-4.8.5"
## How do we extract info from the name of a Z3 release file?
Z3_RELEASE_REGEXP = re.compile(r"^(?P<directory>z3-[0-9a-z\.]+-(?P<platform>x86|x64)-(?P<os>[a-z0-9\.\-]+)).zip$", re.IGNORECASE)
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
Z3_PACKAGE_PREFIX = path.join("z3")

## What do we take from the z3 archive? (Glob syntax)
Z3_INTERESTING_FILES = ["LICENSE.txt", "bin/*"]

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

z3ToDotNetOSMapping = {
    "ubuntu": "linux",
    "debian": "linux",
    "osx": "osx",
    "win": "win"
}


def flush(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()

class Release:
    @staticmethod
    def parse_zip_name(name):
        m = Z3_RELEASE_REGEXP.match(name)
        if not m:
            raise Exception("{} does not match Z3_RELEASE_REGEXP".format(name))
        return m.group('platform'), m.group('os'), m.group("directory")

    def __init__(self, js, version, out):
        self.z3_name = js["name"]
        self.size = js["size"]
        self.url = js["browser_download_url"]
        self.platform, self.os, self.directory = Release.parse_zip_name(js["name"])
        self.os_name = self.os.split("-")[0]
        self.z3_zip = path.join(CACHE_DIRECTORY, self.z3_name)
        self.dafny_name = "dafny-{}-{}-{}.zip".format(version, self.platform, self.os)
        if out != None:
            self.dafny_name = out
        self.target = "{}-{}".format(z3ToDotNetOSMapping[self.os_name], self.platform)
        self.dafny_zip = path.join(DESTINATION_DIRECTORY, self.dafny_name)
        self.buildDirectory = path.join(BINARIES_DIRECTORY, self.target, "publish")

    @property
    def cached(self):
        return path.exists(self.z3_zip) and path.getsize(self.z3_zip) == self.size

    @property
    def MB(self):
        return self.size / 1e6

    def download(self):
        if self.cached:
            print("cached!")
        else:
            flush("downloading {:.2f}MB...".format(self.MB), end=' ')
            for currentAttempt in range(Z3_MAX_DOWNLOAD_ATTEMPTS):
                try:
                    with request.urlopen(self.url) as reader:
                        with open(self.z3_zip, mode="wb") as writer:
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

    def run_publish(self, project):
        env = dict(os.environ)
        env["RUNTIME_IDENTIFIER"] = self.target
        flush("   + Publishing " + project)
        remaining = 3
        exitStatus = 1
        while 0 < remaining and exitStatus != 0:
            remaining -= 1
            exitStatus = subprocess.call(["dotnet", "publish", path.join(SOURCE_DIRECTORY, project, project + ".csproj"),
                "--nologo",
                "-f", "net6.0",
                "-o", self.buildDirectory,
                "-r", self.target,
                "--self-contained",
                "-c", "Release"], env=env)
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
        self.run_publish("DafnyDriver")

    def pack(self):
        try:
            os.remove(self.dafny_zip)
        except FileNotFoundError:
            pass
        missing = []
        with zipfile.ZipFile(self.dafny_zip, 'w',  zipfile.ZIP_DEFLATED) as archive:
            with zipfile.ZipFile(self.z3_zip) as Z3_archive:
                z3_files_count = 0
                for fileinfo in Z3_archive.infolist():
                    fname = path.relpath(fileinfo.filename, self.directory)
                    if any(fnmatch(fname, pattern) for pattern in Z3_INTERESTING_FILES):
                        z3_files_count += 1
                        contents = Z3_archive.read(fileinfo)
                        fileinfo.filename = Release.zipify_path(path.join(DAFNY_PACKAGE_PREFIX, Z3_PACKAGE_PREFIX, fname))
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
                    if self.os_name != 'win':
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

def discover(args):
    flush("  - Getting information about latest release")
    options = {"Authorization": "Bearer " + args.github_secret} if args.github_secret else {}
    req = request.Request(Z3_RELEASES_URL, None, options)
    with request.urlopen(req) as reader:
        js = json.loads(reader.read().decode("utf-8"))

        for release_js in js["assets"]:
            release = Release(release_js, args.version, args.out)
            if release.platform == "x64":
                flush("    + Selecting {} ({:.2f}MB, {})".format(release.z3_name, release.MB, release.size))
                yield release
            else:
                flush("    + Rejecting {}".format(release.z3_name))

def path_leaf(path):
    head, tail = ntpath.split(path)
    return tail or ntpath.basename(head)

def pathsInDirectory(directory):
    return [path.join(directory, file) for file in os.listdir(directory)]

def download(releases):
    flush("  - Downloading {} z3 archives".format(len(releases)))
    for release in releases:
        flush("    + {}:".format(release.z3_name), end=' ')
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
        run(["make", "--quiet", "refman-release"])

def check_version_cs(args):
    # Checking version.cs
    fp = open(path.join(SOURCE_DIRECTORY,"version.cs"))
    lines = fp.readlines()
    qstart = lines[2].index('"')
    qend = lines[2].index('"', qstart+1)
    lastdot = lines[2].rindex('.',qstart)
    v1 = lines[2][qstart+1:lastdot]
    v2 = lines[2][lastdot+1:qend]
    now = time.localtime()
    year = now[0]
    month = now[1]
    day = now[2]
    v3 = str(year-2018) + str(month).zfill(2) + str(day).zfill(2)
    if v2 != v3:
        flush("The date in version.cs does not agree with today's date: " + v3 + " vs. " + v2)
    if "-" in args.version:
        hy = args.version[:args.version.index('-')]
    else:
        hy = args.version
    if hy != v1:
        flush("The version number in version.cs does not agree with the given version: " + hy + " vs. " + v1)
    if (v2 != v3 or hy != v1) and not args.trial:
        return False
    fp.close()
    flush("Creating release files for release \"" + args.version + "\" and internal version information: "+ lines[2][qstart+1:qend])
    return True

def parse_arguments():
    parser = argparse.ArgumentParser(description="Prepare a Dafny release. Configuration is hardcoded; edit the `# Configuration' section of this script to change it.")
    parser.add_argument("version", help="Version number for this release")
    parser.add_argument("--os", help="operating system name for which to make a release")
    parser.add_argument("--skip_manual", help="do not create the reference manual")
    parser.add_argument("--trial", help="ignore version.cs discrepancies")
    parser.add_argument("--github_secret", help="access token for making an authenticated GitHub call, to prevent being rate limited.")
    parser.add_argument("--out", help="output zip file")
    return parser.parse_args()

def main():
    args = parse_arguments()
    if not DAFNY_RELEASE_REGEX.match(args.version):
        flush("Release number is in wrong format: should be d.d.d or d.d.d-text without spaces")
        return
    os.makedirs(CACHE_DIRECTORY, exist_ok=True)

    if not check_version_cs(args):
        return

    # Z3
    flush("* Finding and downloading Z3 releases")
    releases = list(discover(args))
    if args.os:
        releases = list(filter(lambda release: release.os_name == args.os, releases))
    download(releases)

    flush("* Building and packaging Dafny")
    pack(args, releases)

if __name__ == '__main__':
    main()
