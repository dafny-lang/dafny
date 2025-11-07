FROM alpine/curl:8.14.1 AS node-download
# all node versions can be found at https://nodejs.org/en/download
# Dafny targeting Go produces Go source content consistent with Go 1.18.
ARG NODE_VERSION=24.11.0
ENV NODE_SRC="https://nodejs.org/dist/v$NODE_VERSION/node-v$NODE_VERSION-linux-x64.tar.xz"
WORKDIR /tmp
RUN curl -Lo node.tar.xz $NODE_SRC && tar xf node.tar.xz
RUN mv node-v$NODE_VERSION-linux-x64 node

# add support to compile to Javascript to the dafny-base
FROM dafny-base AS dafny-js

#update node PATH
ENV PATH=$PATH:/usr/local/node/bin

COPY --from=node-download /tmp/node /usr/local/node

# install dependencies to run dafny with JS
RUN npm install --global bignumber.js

# launch dafny cli
WORKDIR /dafny
ENTRYPOINT ["dafny"]
CMD ["-h"]
