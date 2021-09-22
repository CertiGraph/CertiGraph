# CertiGraph

A library for verifying graph-manipulating programs.

Powered by [Coq](https://coq.inria.fr) and [VST](https://vst.cs.princeton.edu/). Compatible with [CompCert](https://compcert.org/).

## Contributors

* Aquinas Hobor
* Shengyi Wang
* Anshuman Mohan

## Installing

The library can be installed using [opam](https://opam.ocaml.org/). Different packages are offered for different targets:

### `x86_64-linux`

```console
$ opam install ./coq-certigraph.opam
```

### `x86_32-linux`

```console
$ opam install ./coq-certigraph-32.opam
```

### Manual build

Alternatively, if you would prefer to perform a manual build, see `BUILDING.md`.