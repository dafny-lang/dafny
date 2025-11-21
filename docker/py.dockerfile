# add support to compile to python to the dafny-base
FROM dafny-base AS dafny-py

# Dafny targeting Python produces Python source content consistent with Python 3
# all python versions from deadsnakes can be found at https://github.com/deadsnakes
ARG PYTHON_VERSION=3.7

# install python and dependencies
RUN apt update && apt install -y  software-properties-common && rm -rf /var/lib/apt/lists/*
RUN add-apt-repository ppa:deadsnakes/ppa && apt update && apt install -y python$PYTHON_VERSION && rm -rf /var/lib/apt/lists/*

# link python executable to python3
RUN update-alternatives --install /usr/bin/python python /usr/bin/python3 1

# launch dafny cli
WORKDIR /dafny
ENTRYPOINT ["dafny"]
CMD ["-h"]
