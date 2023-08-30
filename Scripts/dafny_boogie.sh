#!/bin/bash
ROOT=$(dirname $(dirname "${BASH_SOURCE[0]}"))
BOOGIE_ARGS=$(sed -e 's|^|-|' "${ROOT}"/Test/boogie-args.cfg | sed -e "s|{ROOT}|$ROOT|")
dotnet tool run boogie $BOOGIE_ARGS "$@"
