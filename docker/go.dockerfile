FROM alpine/curl:8.14.1 AS go-download
# all go versions can be found at https://go.dev/dl/
# Dafny targeting Go produces Go source content consistent with Go 1.18.
ARG GO_VERSION=1.25.4
ENV GO_SRC="https://go.dev/dl/go$GO_VERSION.linux-amd64.tar.gz"
WORKDIR /tmp
RUN curl -Lo go.tar.gz $GO_SRC && tar xzf go.tar.gz

# add support to compile to go to the dafny-base
FROM dafny-base AS dafny-go
ARG GO_VERSION=1.25.4
# last verision compatable with go v1.25.4 -- change if changing version of go
# see https://pkg.go.dev/golang.org/x/tools?tab=versions
ARG GOIMPORTS_VERSION=0.38.0
ENV GO_VERSION=$GO_VERSION
# update go path
ENV PATH=$PATH:/usr/local/go/bin:/root/go/bin
# install go and dependencies
RUN apt update && apt install -y ca-certificates && rm -rf /var/lib/apt/lists/*
COPY --from=go-download /tmp/go /usr/local/go
RUN go install "golang.org/x/tools/cmd/goimports@v$GOIMPORTS_VERSION"
# launch dafny cli
WORKDIR /dafny
ENTRYPOINT ["dafny"]
CMD ["-h"]
