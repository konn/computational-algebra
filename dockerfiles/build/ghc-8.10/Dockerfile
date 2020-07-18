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

ENV GHC=810
COPY stack-${GHC}.yaml /skeleton

WORKDIR /skeleton
ENV STACK_YAML=stack-${GHC}.yaml
RUN stack setup
RUN stack build --only-dependencies --test --no-run-tests
