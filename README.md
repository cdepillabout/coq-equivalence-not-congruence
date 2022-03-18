<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Equivalence Not Congruence for Imp

[![Docker CI][docker-action-shield]][docker-action-link]
[![Nix CI][nix-action-shield]][nix-action-link]
[![coqdoc][coqdoc-shield]][coqdoc-link]

[docker-action-shield]: https://github.com/cdepillabout/coq-equivalence-not-congruence/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/cdepillabout/coq-equivalence-not-congruence/actions?query=workflow:"Docker%20CI"

[nix-action-shield]: https://github.com/cdepillabout/coq-equivalence-not-congruence/workflows/Nix%20CI/badge.svg?branch=master
[nix-action-link]: https://github.com/cdepillabout/coq-equivalence-not-congruence/actions?query=workflow:"Nix%20CI"


[coqdoc-shield]: https://img.shields.io/badge/docs-coqdoc-blue.svg
[coqdoc-link]: https://cdepillabout.github.io/coq-equivalence-not-congruence


This projects contains a Coq proof of an equivalence relation on the Imp
language that is not congruent. This answers a question from the Program
Equivalence (Equiv) chapter of Programming Language Foundations, which is the
second book of Software Foundations.

## Meta

- Author(s):
  - Dennis Gosnell (initial)
- License: [BSD 3-Clause "New" or "Revised" License](LICENSE)
- Compatible Coq versions: 8.12 or later
- Additional dependencies: none
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of Equivalence Not Congruence for Imp
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-coq-equivalence-not-congruence
```

To instead build and install manually, do:

``` shell
git clone https://github.com/cdepillabout/coq-equivalence-not-congruence.git
cd coq-equivalence-not-congruence
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Documentation
