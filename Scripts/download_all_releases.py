#!/usr/bin/env python
# This script downloads all released versions of Dafny to ``dafny_releases/binaries``
# (This is useful for finding when a bug was introduced.)

from typing import Iterable, List, Dict, NamedTuple, Optional

from fnmatch import fnmatch
from pathlib import Path
from urllib.request import Request, urlopen
import json
import platform
import sys
import shutil
import zipfile

RELEASES_API_ENDPOINT = "https://api.github.com/repos/dafny-lang/dafny/releases"

API_HEADERS = {
    "Accept": "application/vnd.github.v3+json"
}

class Asset(NamedTuple):
    name: str
    url: str

    def matches_platform(self, glob: str) -> bool:
        return fnmatch(self.name, glob)

def progress(msg):
    print(msg, file=sys.stderr, flush=True)

def find_releases(cache_file: Path) -> Dict[str, List[Asset]]:
    if cache_file.exists():
        progress(f"Reusing list of releases cached in {cache_file}")
        bs = cache_file.read_bytes()
    else:
        progress("Downloading list of releases")
        req = Request(RELEASES_API_ENDPOINT, data=None, headers=API_HEADERS)
        with urlopen(req) as fs:
            bs = fs.read()
            cache_file.write_bytes(bs)
    js = json.loads(bs.decode("utf-8"))
    return { r["tag_name"]: [Asset(a["name"], a["browser_download_url"])
                             for a in r["assets"]]
             for r in js }

def find_asset(assets: Iterable[Asset], platform_glob: str) -> Optional[Asset]:
    for a in assets:
        if a.matches_platform(platform_glob):
            return a
    return None

def download(url: str, target: Path) -> None:
    if target.exists():
        progress(f"Reusing cached download {target}")
        return
    progress(f"Downloading {target}")
    with urlopen(url) as fs:
        target.write_bytes(fs.read())

def removeprefix(s: str, prefix: str) -> str: # Compatibility
    if s.startswith(prefix):
        return s[len(prefix):]
    return s

def unzip(asset_file: Path, target_dir: Path):
    try:
        target_dir.mkdir()
        progress(f"Extracting {asset_file}")
        with zipfile.ZipFile(asset_file, 'r') as zf:
            for zipinfo in zf.infolist():
                zipinfo.filename = removeprefix(zipinfo.filename, "dafny/")
                zf.extract(zipinfo, target_dir)
    except:
        shutil.rmtree(target_dir)
        raise

def get_platform_glob() -> str:
    system = platform.system()
    if system == 'Linux':
        return '*ubuntu*'
    if system == 'Darwin':
        return '*osx*'
    if system == 'Windows':
        return '*win*'
    raise ValueError("Unknown platform")

def main():
    root = Path("dafny_releases")
    platform_glob = get_platform_glob()

    releases_dir, cache_dir = root / "binaries", root / "assets"
    releases_dir.mkdir(parents=True, exist_ok=True)
    cache_dir.mkdir(parents=True, exist_ok=True)
    cache_file = root / "releases.json"

    for (tag, assets) in reversed(find_releases(cache_file).items()):
        target_dir = releases_dir / tag

        if target_dir.exists():
            progress(f"Skipping existing release {target_dir}")
            continue

        if asset := find_asset(assets, platform_glob):
            asset_file = cache_dir / asset.name
            download(asset.url, asset_file)
            unzip(asset_file, target_dir)
        else:
            progress(f"!! No asset found for this platform in release {tag}")

if __name__ == "__main__":
    main()
