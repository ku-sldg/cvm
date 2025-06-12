<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# CVM

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/ku-sldg/cvm/actions/workflows/docker-action.yml/badge.svg?branch=main
[docker-action-link]: https://github.com/ku-sldg/cvm/actions/workflows/docker-action.yml




The Copland Virtual Machine (CVM) is a Rocq library that formalizes a virtual machine for the Copland Domain Specific Language for layered remote attestation.

## Meta

- Author(s):
  - Will Thomas
- License: [Creative Commons Attribution Share Alike 4.0 International](LICENSE)
- Compatible Coq versions: 9.0 later
- Compatible OCaml versions: 4.12 or later
- Additional dependencies:
  - [RocqCandy](https://github.com/ku-sldg/rocq-candy)
  - [Copland Spec](https://github.com/ku-sldg/copland-spec)
  - [Dune](https://dune.build) 3.17 or later
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of CVM
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add -a --set-default ku-sldg/opam-repo https://github.com/ku-sldg/opam-repo.git
opam repo add coq-released https://coq.inria.fr/opam/released
opam install rocq-cvm
```

To instead build and install manually, do:

``` shell
git clone https://github.com/ku-sldg/cvm.git
cd cvm
dune build
dune install
```



