FROM ubuntu:20.04
LABEL org.opencontainers.image.source https://github.com/konn/computational-algebra

ENV LD_LIBRARY_PATH $MPI/lib:$LD_LIBRARY_PATH

RUN apt-get update -y -qq && apt-get install -y -qq wget gnupg2 sudo
RUN echo 'Dir::Bin::Methods::ftp "ftp";' >> /etc/apt/apt.conf.d/99local-ftp

# Adding Singular repo to apt
RUN echo "deb ftp://jim.mathematik.uni-kl.de/repo/ubuntu20 focal main" >> /etc/apt/sources.list && \
  wget -O - ftp://jim.mathematik.uni-kl.de/repo/extra/gpg | apt-key add

# Adds LLVM repo to apt
RUN echo "deb http://apt.llvm.org/focal llvm-toolchain-focal-9 main" >> /etc/apt/sources.list && \
  wget -O - https://apt.llvm.org/llvm-snapshot.gpg.key | apt-key add
RUN apt-get update -y -qq
RUN apt-get install -y -qq singular41 libgmp3-dev libgsl0-dev liblapack-dev clang-9 llvm-9 llvm-9-dev libllvm9

# Sets up curl, apt-add-repository, and stack
RUN apt-get install -y -qq curl software-properties-common && \
  wget -qO- https://get.haskellstack.org/ | sh

# Althoug contradictory to GitHub documents, we need to add new
# users and call USER to get permission just right.
RUN addgroup --system --gid 121 github \
    && adduser --system --gid 121 --home /github/home --uid 1001 runner

# We have to grant github to be sudoer.
RUN usermod -aG sudo runner && usermod -aG root runner && sed -i "s/%sudo\tALL=(ALL:ALL) ALL/%sudo\tALL=NOPASSWD: ALL/" /etc/sudoers
RUN echo "C.UTF-8" > /etc/locale.conf

USER runner:github

ENV TAR_OPTIONS --no-same-owner
ENV PATH "/github/home/.local/bin:/usr/local/bin:${PATH}"
ENV LANG "C.UTF-8"
ENV LC_CTYPE "C.UTF-8"
ENV LC_TIME "C.UTF-8"
ENV LC_MESSAGES "C.UTF-8"
ENV LC_ALL "C.UTF-8"
ENV LANGUAGE "C.UTF-8"
