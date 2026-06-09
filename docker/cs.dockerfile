# add support to compile to C# to the dafny-base
FROM dafny-base AS dafny-cs

# install .NET SDK 8.0 to support C#
RUN apt update && apt install -y dotnet-sdk-8.0 && rm -rf /var/lib/apt/lists/*

# launch dafny cli
WORKDIR /dafny
ENTRYPOINT ["dafny"]
CMD ["-h"]
