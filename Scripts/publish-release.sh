#! /bin/bash

echo Uploading github release

if [ $# -ne 1 ] ; then echo "Version number required as argument"; exit 1; fi
if [ ! -e ~/github.token ] ; then echo "No authorization token exists -- generate a GitHub personal authorization token and store it in ~/github.token"; exit 1; fi

# find the source directory for this script even if it's been symlinked [issue #185]
# from https://stackoverflow.com/questions/59895/
SOURCE="${BASH_SOURCE[0]}"
while [ -h "$SOURCE" ]; do
    DIR="$( cd -P "$( dirname "$SOURCE" )" && pwd )"
    SOURCE="$(readlink "$SOURCE")"
    [[ $SOURCE != /* ]] && SOURCE="$DIR/$SOURCE"
done
DAFNY_ROOT="$( cd -P "$( dirname $( dirname "$SOURCE" ))" && pwd )"

ver="$1"
vers=`echo "$ver" | sed -e 's/-/ /g'`
token=`cat ~/github.token | head -n 1`

echo $ver
echo $vers

curl -s -X POST -H "Authorization: token $token" -d "{\"tag_name\":\"v$ver\", \"name\":\"Dafny $vers\", \"draft\":true, \"body\":\"Publishing release $ver\"}" "https://api.github.com/repos/dafny-lang/dafny/releases" > /tmp/post

upload_url=`jq -r '.upload_url' < /tmp/post`
upload_url="${upload_url%\{*}"
id=`jq -r '.id' < /tmp/post`

cd $DAFNY_ROOT/Package
files=`ls dafny-${ver}*`

echo Uploading DafnyRef.pdf
curl -s -X POST -H "Authorization: token $token"  \
        -H "Content-Type: application/pdf" \
        --data-binary @DafnyRef.pdf  \
        "$upload_url?name=DafnyRef.pdf&label=DafnyRef.pdf" > /tmp/upload
if [ $? -ne 0 ]; then echo Upload failed; fi
for f in $files; do
echo Uploading file $f
curl -s -X POST -H "Authorization: token $token"  \
        -H "Content-Type: application/zip" \
        --data-binary @$f  \
        "$upload_url?name=$f&label=$f" > /tmp/upload
if [ $? -ne 0 ]; then echo Upload failed; fi
done

echo "Manually paste the release notes into the release page on github, and then push the publish button"

#echo Publishing release
#curl -s -X PATCH -H "Authorization: token $token" -d "{ \"draft\":$draft}" "https://api.github.com/repos/OpenJML/OpenJML/releases/$id" > /tmp/patch


