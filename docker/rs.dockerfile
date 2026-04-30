# add support to compile to Rust to the dafny-base
FROM dafny-base AS dafny-rs

ENV RUSTUP_SRC="https://sh.rustup.rs"

# installing Rust using the Rustup installer with default profile
RUN apt update && apt install -y  curl gcc && rm -rf /var/lib/apt/lists/*
RUN curl --proto '=https' --tlsv1.2 -sSf $RUSTUP_SRC | sh -s -- -y --profile minimal
RUN apt remove -y curl

# launch dafny cli
WORKDIR /dafny
ENTRYPOINT ["dafny"]
CMD ["-h"]
