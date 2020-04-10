FROM gitpod/workspace-full

RUN sudo apt-get update \
 && sudo apt-get install mono-complete -y \
 && sudo rm -rf /var/lib/apt/lists/* \
 && sudo wget https://github.com/dafny-lang/dafny/releases/download/v2.3.0/dafny-2.3.0.10506-x64-ubuntu-16.04.zip \
 && sudo unzip -d /opt/ dafny-2.3.0.10506-x64-ubuntu-16.04.zip \
 && sudo rm dafny-2.3.0.10506-x64-ubuntu-16.04.zip \
 && sudo chmod -R +r /opt/dafny/ \
 && sudo chmod 755 /opt/dafny/*.exe

