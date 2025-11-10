FROM dafny-base AS dafny-java

# Install java 8
RUN apt update && apt install -y openjdk-8-jdk && \
    rm -rf /var/lib/apt/lists/*

# set java version to Java 8
RUN update-alternatives --set java /usr/lib/jvm/java-8-openjdk-amd64/jre/bin/java && \
    update-alternatives --set javac /usr/lib/jvm/java-8-openjdk-amd64/bin/javac

# launch dafny cli
WORKDIR /dafny
ENTRYPOINT ["dafny"]
CMD ["-h"]