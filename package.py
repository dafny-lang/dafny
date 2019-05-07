#!/usr/bin/env python3

from fnmatch import fnmatch
from os import path
import argparse
import json
import os
import re
import subprocess
import sys
import time
import urllib.request
import zipfile

# Configuration

## Where do we fetch the list of releases from?
## Get the latest release like this:
## RELEASES_URL = "https://api.github.com/repos/Z3Prover/z3/releases/latest"
## Get a specific release like this:
RELEASES_URL = "https://api.github.com/repos/Z3Prover/z3/releases/tags/z3-4.8.4"
## How do we extract info from the name of a release file?
RELEASE_REGEXP = re.compile(r"^(?P<directory>z3-[0-9a-z\.]+-(?P<platform>x86|x64)-(?P<os>[a-z0-9\.\-]+)).zip$", re.IGNORECASE)

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

## What do we take from Dafny's Binaries folder?
DLLs = ["BoogieAbsInt",
        "BoogieBasetypes",
        "BoogieCodeContractsExtender",
        "BoogieConcurrency",
        "BoogieCore",
        "DafnyPipeline",
        "BoogieDoomed",
        "BoogieExecutionEngine",
        "BoogieGraph",
        "BoogieHoudini",
        "BoogieModel",
        "BoogieModelViewer",
        "BoogieParserHelper",
        "Provers.SMTLib",
        "BoogieVCExpr",
        "BoogieVCGeneration"]
EXEs = ["Dafny", "DafnyServer"]
ETCs = UNIX_EXECUTABLES + ["DafnyPrelude.bpl", "DafnyRuntime.cs", "DafnyRuntime.js", "DafnyRuntime.go", "DafnyLanguageService.vsix"]

# Constants

THIS_FILE = path.realpath(__file__)
ROOT_DIRECTORY = path.dirname(THIS_FILE)
SOURCE_DIRECTORY = path.join(ROOT_DIRECTORY, SOURCE_DIRECTORY)
BINARIES_DIRECTORY = path.join(ROOT_DIRECTORY, BINARIES_DIRECTORY)
DESTINATION_DIRECTORY = path.join(ROOT_DIRECTORY, DESTINATION_DIRECTORY)
CACHE_DIRECTORY = path.join(DESTINATION_DIRECTORY, "cache")

MONO = sys.platform not in ("win32", "cygwin")
DLL_PDB_EXT = ".pdb"
EXE_PDB_EXT = ".pdb"
ARCHIVE_FNAMES = ([dll + ".dll" for dll in DLLs] + [dll + DLL_PDB_EXT for dll in DLLs] +
                  [exe + ".exe" for exe in EXEs] + [exe + EXE_PDB_EXT for exe in EXEs] +
                  ETCs)

# Code

def flush(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()

class Release:
    @staticmethod
    def parse_zip_name(name):
        m = RELEASE_REGEXP.match(name)
        if not m:
            raise Exception("{} does not match RELEASE_REGEXP".format(name))
        return m.group('platform'), m.group('os'), m.group("directory")

    def __init__(self, js, version):
        self.z3_name = js["name"]
        self.size = js["size"]
        self.url = js["browser_download_url"]
        self.platform, self.os, self.directory = Release.parse_zip_name(js["name"])
        self.z3_zip = path.join(CACHE_DIRECTORY, self.z3_name)
        self.dafny_name = "dafny-{}-{}-{}.zip".format(version, self.platform, self.os)
        self.dafny_zip = path.join(DESTINATION_DIRECTORY, self.dafny_name)

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
            with urllib.request.urlopen(self.url) as reader:
                with open(self.z3_zip, mode="wb") as writer:
                    writer.write(reader.read())
            flush("done!")

    @staticmethod
    def zipify_path(fpath):
        """Zip entries always use '/' as the path separator."""
        return fpath.replace(os.path.sep, '/')

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
            for fname in ARCHIVE_FNAMES:
                fpath = path.join(BINARIES_DIRECTORY, fname)
                if path.exists(fpath):
                    fileinfo = zipfile.ZipInfo(fname, time.localtime(os.stat(fpath).st_mtime)[:6])
                    if any(fnmatch(fname, pattern) for pattern in UNIX_EXECUTABLES):
                        # http://stackoverflow.com/questions/434641/
                        fileinfo.external_attr = 0o100755 << 16
                        fileinfo.create_system = 3  # lie about this zip file's source OS to preserve permissions
                    contents = open(fpath, mode='rb').read()
                    fileinfo.compress_type = zipfile.ZIP_DEFLATED
                    fileinfo.filename = Release.zipify_path(path.join(DAFNY_PACKAGE_PREFIX, fname))
                    archive.writestr(fileinfo, contents)
                else:
                    missing.append(fname)
        flush("done! (imported {} files from z3's sources)".format(z3_files_count))
        if missing:
            flush("      WARNING: Not all files were found: {} were missing".format(", ".join(missing)))

def discover(version):
    flush("  - Getting information about latest release")
    with urllib.request.urlopen(RELEASES_URL) as reader:
        js = json.loads(reader.read().decode("utf-8"))

        for release_js in js["assets"]:
            release = Release(release_js, version)
            if release.platform == "x64":
                flush("    + Selecting {} ({:.2f}MB, {})".format(release.z3_name, release.MB, release.size))
                yield release
            else:
                flush("    + Rejecting {}".format(release.z3_name))

def download(releases):
    flush("  - Downloading {} z3 archives".format(len(releases)))
    for release in releases:
        flush("    + {}:".format(release.z3_name), end=' ')
        release.download()

def run(cmd):
    flush("    + {}...".format(" ".join(cmd)), end=' ')
    retv = subprocess.call(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    if retv != 0:
        flush("failed! (Is Dafny or the Dafny server running?)")
        sys.exit(1)
    else:
        flush("done!")

def build():
    os.chdir(ROOT_DIRECTORY)
    flush("  - Building")
    builder = "msbuild"
    try:
        run([builder, "Source/Dafny.sln", "/p:Configuration=Checked", "/p:Platform=Any CPU", "/t:Clean"])
        run([builder, "Source/Dafny.sln", "/p:Configuration=Checked", "/p:Platform=Any CPU", "/t:Rebuild"])
    except FileNotFoundError:
        flush("Could not find '{}'!".format(builder))
        flush("On Windows, you need to run this from the VS native tools command prompt.")
        flush("On Mac/Linux, you might need a more recent version of Mono.")
        sys.exit(1)

def pack(releases):
    flush("  - Packaging {} Dafny archives".format(len(releases)))
    for release in releases:
        flush("    + {}:".format(release.dafny_name), end=' ')
        release.pack()

def parse_arguments():
    parser = argparse.ArgumentParser(description="Prepare a Dafny release. Configuration is hardcoded; edit the `# Configuration' section of this script to change it.")
    parser.add_argument("version", help="Version number for this release")
    return parser.parse_args()

def main():
    args = parse_arguments()
    os.makedirs(CACHE_DIRECTORY, exist_ok=True)

    # Z3
    flush("* Finding and downloading Z3 releases")
    releases = list(discover(args.version))
    download(releases)

    flush("* Building and packaging Dafny")
    build()
    pack(releases)

if __name__ == '__main__':
    main()
