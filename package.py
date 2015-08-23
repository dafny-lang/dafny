import argparse
import json
import os
from os import path
import re
import urllib.request
import sys
import zipfile
import subprocess
import shutil

# Configuration

RELEASES_URL = "https://api.github.com/repos/Z3Prover/z3/releases/latest"
RELEASE_REGEXP = r"^(?P<directory>z3-[0-9\.]+-(?P<platform>x86|x64)-(?P<os>[a-z0-9\.\-]+)).zip$"

SOURCE_DIRECTORY = "Source"
BINARIES_DIRECTORY = "Binaries"
DESTINATION_DIRECTORY = "Package"

Z3_ARCHIVE_PREFIX = path.join("z3", "bin")

DLLs = ["AbsInt",
        "Basetypes",
        "CodeContractsExtender",
        "Concurrency",
        "Core",
        "DafnyPipeline",
        "Doomed",
        "ExecutionEngine",
        "Graph",
        "Houdini",
        "Model",
        "ModelViewer",
        "ParserHelper",
        "Provers.SMTLib",
        "VCExpr",
        "VCGeneration"]
EXEs = ["Dafny", "DafnyServer"]
ETCs = ["dafny", "DafnyPrelude.bpl", "DafnyRuntime.cs"]

# Constants

THIS_FILE = path.realpath(__file__)
ROOT_DIRECTORY = path.dirname(THIS_FILE)
SOURCE_DIRECTORY = path.join(ROOT_DIRECTORY, SOURCE_DIRECTORY)
BINARIES_DIRECTORY = path.join(ROOT_DIRECTORY, BINARIES_DIRECTORY)
DESTINATION_DIRECTORY = path.join(ROOT_DIRECTORY, DESTINATION_DIRECTORY)
CACHE_DIRECTORY = path.join(DESTINATION_DIRECTORY, "cache")

RELEASE_REGEXP = re.compile(RELEASE_REGEXP, re.IGNORECASE)

MONO = sys.platform not in ("win32", "cygwin")
DLL_PDB_EXT = ".dll.mdb" if MONO else ".pdb"
EXE_PDB_EXT = ".exe.mdb" if MONO else ".pdb"
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
        self.z3_directory = path.join(CACHE_DIRECTORY, self.directory)
        self.z3_bin_directory = path.join(self.z3_directory, "bin")
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

    def unpack(self):
        shutil.rmtree(self.z3_directory)
        with zipfile.ZipFile(self.z3_zip) as archive:
            archive.extractall(CACHE_DIRECTORY)
            flush("done!")

    def pack(self):
        try:
            os.remove(self.dafny_zip)
        except FileNotFoundError:
            pass
        missing = []
        with zipfile.ZipFile(self.dafny_zip, 'w',  zipfile.ZIP_DEFLATED) as archive:
            for root, _, files in os.walk(self.z3_bin_directory):
                for f in files:
                    fpath = path.join(root, f)
                    arcpath = path.join(Z3_ARCHIVE_PREFIX, path.relpath(fpath, self.z3_bin_directory))
                    archive.write(fpath, arcpath)
            for fname in ARCHIVE_FNAMES:
                fpath = path.join(BINARIES_DIRECTORY, fname)
                if path.exists(fpath):
                    archive.write(fpath, fname)
                else:
                    missing.append(fname)
        flush("done!")
        if missing:
            flush("      WARNING: Not all files were found: {} were missing".format(", ".join(missing)))

def discover(version):
    flush("  - Getting information about latest release")
    with urllib.request.urlopen("https://api.github.com/repos/Z3Prover/z3/releases/latest") as reader:
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

def unpack(releases):
    flush("  - Unpacking {} z3 archives".format(len(releases)))
    for release in releases:
        flush("    + {}:".format(release.z3_name), end=' ')
        release.unpack()

def run(cmd):
    flush("    + {}...".format(" ".join(cmd)), end=' ')
    retv = subprocess.call(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    if retv != 0:
        flush("failed!")
        sys.exit(1)
    else:
        flush("done!")

def build():
    os.chdir(ROOT_DIRECTORY)
    flush("  - Building")
    builder = "xbuild" if MONO else "xbuild"
    run([builder, "Source/Dafny.sln", "/t:Clean"])
    run([builder, "Source/Dafny.sln", "/p:Configuration=Checked", "/t:Rebuild"])

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
    flush("* Finding, downloading, and unpacking Z3 releases")
    releases = list(discover(args.version))
    download(releases)
    unpack(releases)

    flush("* Building and packaging Dafny")
    build()
    pack(releases)

if __name__ == '__main__':
    main()
