# See here for image contents: https://github.com/microsoft/vscode-dev-containers/tree/v0.194.0/containers/dotnet/.devcontainer/base.Dockerfile

# [Choice] .NET version: 5.0, 3.1, 2.1
ARG VARIANT="5.0"
FROM mcr.microsoft.com/vscode/devcontainers/dotnet:0-${VARIANT}

# [Choice] Node.js version: none, lts/*, 16, 14, 12, 10
ARG NODE_VERSION="16"
RUN if [ "${NODE_VERSION}" != "none" ]; then su vscode -c "umask 0002 && . /usr/local/share/nvm/nvm.sh && nvm install ${NODE_VERSION} 2>&1"; fi

# [Option] Install Azure CLI
ARG INSTALL_AZURE_CLI="false"
COPY library-scripts/*.sh library-scripts/*.env /tmp/library-scripts/
RUN if [ "$INSTALL_AZURE_CLI" = "true" ]; then bash /tmp/library-scripts/azcli-debian.sh; fi \
    && apt-get clean -y && rm -rf /var/lib/apt/lists/* /tmp/library-scripts

# [Optional] Uncomment this section to install additional OS packages.
RUN apt-get update && export DEBIAN_FRONTEND=noninteractive \
    && apt-get -y install --no-install-recommends python3-pip golang openjdk-11-jdk libgomp1 make

# [Optional] Uncomment this line to global local node packages.
# RUN su vscode -c "source /usr/local/share/nvm/nvm.sh && npm install -g <packages>" 2>&1

# Gradle 7.2
RUN sudo mkdir /opt/gradle                                                                \
    && cd /opt/gradle ; wget https://services.gradle.org/distributions/gradle-7.2-bin.zip \
    && unzip -d /opt/gradle gradle-7.2-bin.zip                                            \
    && sudo rm -f /opt/gradle/gradle-7.2-bin.zip
ENV PATH="${PATH}:/opt/gradle/gradle-7.2/bin"

# z3 4.8.5
RUN sudo mkdir /opt/z3                                                                                           \
    && cd /opt/z3 ; wget https://github.com/Z3Prover/z3/releases/download/Z3-4.8.5/z3-4.8.5-x64-ubuntu-16.04.zip \
    && unzip -d /opt/z3 z3-4.8.5-x64-ubuntu-16.04.zip                                                            \
    && sudo rm -f /opt/z3/z3-4.8.5-x64-ubuntu-16.04.zip
ENV PATH="${PATH}:/opt/z3/z3-4.8.5-x64-ubuntu-16.04/bin"

# pip3: pre-commit lit outputcheck
RUN su vscode -c "pip3 install pre-commit lit outputcheck" 2>&1
