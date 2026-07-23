FROM alpine/curl:8.14.1 AS bin-download
ARG DAFNY_VERSION=4.11.0
ENV DAFNY_SRC="https://github.com/dafny-lang/dafny/releases/download/v$DAFNY_VERSION/dafny-$DAFNY_VERSION-x64-ubuntu-22.04.zip"
WORKDIR /tmp
RUN curl -Lo dafny.zip $DAFNY_SRC && unzip dafny.zip

# base image supports dafny verify
FROM ubuntu:22.04 AS dafny-base
ENV DOTNET_CLI_TELEMETRY_OPTOUT=1
ARG DAFNY_VERSION=4.11.0
ENV DAFNY_VERSION=$DAFNY_VERSION
# install dotnet runtime 8
WORKDIR /tmp
RUN apt update && apt install -y dotnet-runtime-8.0 libicu-dev && rm -rf /var/lib/apt/lists/*
# setup dafny cli
COPY --from=bin-download /tmp/dafny /opt/dafny
RUN ln -s /opt/dafny/dafny /usr/local/bin/dafny
# launch dafny cli
WORKDIR /dafny
ENTRYPOINT ["dafny"]
CMD ["-h"]