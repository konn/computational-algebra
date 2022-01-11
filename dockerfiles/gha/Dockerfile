FROM ubuntu:20.04
LABEL org.opencontainers.image.source https://github.com/konn/computational-algebra

ENV PATH /root/.local/bin:$PATH
ENV LD_LIBRARY_PATH $MPI/lib:$LD_LIBRARY_PATH

RUN apt-get update -y -qq && apt-get install -y -qq wget gnupg2
RUN echo 'Dir::Bin::Methods::ftp "ftp";' >> /etc/apt/apt.conf.d/99local-ftp

# Adding Singular repo to apt
RUN echo "deb ftp://jim.mathematik.uni-kl.de/repo/ubuntu20 focal main" >> /etc/apt/sources.list && \
  wget -O - ftp://jim.mathematik.uni-kl.de/repo/extra/gpg | apt-key add

# Adds LLVM repo to apt
RUN echo "deb http://apt.llvm.org/focal llvm-toolchain-focal-9 main" >> /etc/apt/sources.list && \
  wget -O - https://apt.llvm.org/llvm-snapshot.gpg.key | apt-key add
RUN apt-get update -y -qq
RUN apt-get install -y -qq singular41 libgmp3-dev libgsl0-dev liblapack-dev clang-9 llvm-9 llvm-9-dev libllvm9
