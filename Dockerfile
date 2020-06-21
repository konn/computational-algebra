FROM fpco/stack-build:lts-14.20
ARG LTS=lts-14.20
ARG GHC_LLVM_LLC_PATH=llc-6.0
ARG GHC_LLVM_OPT_PATH=opt-6.0

ENV PATH /root/.local/bin:$PATH
ENV LD_LIBRARY_PATH $MPI/lib:$LD_LIBRARY_PATH

RUN apt-get update -y -qq && apt-get install -y -qq wget
RUN wget ftp://jim.mathematik.uni-kl.de/repo/extra/gpg && apt-key add gpg && rm gpg
RUN echo "deb ftp://jim.mathematik.uni-kl.de/repo/ubuntu18 bionic main" >> /etc/apt/sources.list
RUN apt-get update -y -qq
RUN apt-get install -y -qq singular41 libgmp3-dev libgsl0-dev liblapack-dev
RUN stack upgrade

