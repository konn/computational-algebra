FROM registry.gitlab.com/konn/computational-algebra/build-pre:0.6.0.0

RUN mkdir /skeleton
COPY computational-algebra/ /skeleton/computational-algebra
COPY algebraic-prelude/ /skeleton/algebraic-prelude
COPY halg-algebraic/ /skeleton/halg-algebraic
COPY halg-algorithms/ /skeleton/halg-algorithms
COPY halg-bridge-singular/ /skeleton/halg-bridge-singular
COPY halg-core/ /skeleton/halg-core
COPY halg-core-test/ /skeleton/halg-core-test
COPY halg-factor/ /skeleton/halg-factor
COPY halg-galois-fields/ /skeleton/halg-galois-fields
COPY halg-heaps/ /skeleton/halg-heaps
COPY halg-matrices/ /skeleton/halg-matrices
COPY halg-polyn-parser/ /skeleton/halg-polyn-parser
COPY halg-polynomials/ /skeleton/halg-polynomials

ENV GHC=804
COPY stack-${GHC}.yaml /skeleton

WORKDIR /skeleton
ENV STACK_YAML=stack-${GHC}.yaml
RUN stack build --only-dependencies --test --no-run-tests

ENV GHC_LLVM_LLC_PATH=llc-5.0
ENV GHC_LLVM_OPT_PATH=opt-5.0

RUN echo "deb http://apt.llvm.org/xenial/ llvm-toolchain-xenial-5.0 main" >> /etc/apt/sources.list && wget -O - https://apt.llvm.org/llvm-snapshot.gpg.key | sudo apt-key add - && apt-get update && apt-get -y install clang-5.0 lld-5.0
