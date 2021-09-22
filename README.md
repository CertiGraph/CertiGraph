# CertiGraph

A library for verifying graph-manipulating programs.

Powered by [Coq](https://coq.inria.fr) and [VST](https://vst.cs.princeton.edu/). Compatible with [CompCert](https://compcert.org/).


## Contributors

* Aquinas Hobor
* Shengyi Wang
* Anshuman Mohan


## Papers

* [Functional Correctness of C Implementations of Dijkstra's, Kruskal's, and Prim's Algorithms](https://www.comp.nus.edu.sg/~hobor/Publications/2021/CertiDKP.pdf) (CAV 2021). Aquinas Hobor, Anshuman Mohan, Wei Xiang Leow.
* [Mechanized verification of graph-manipulating programs](https://www.comp.nus.edu.sg/~hobor/Teaching/SW-PhD.pdf) (Thesis). Shengyi Wang.
* [A Machine-Checked C Implementation of Dijkstra's Shortest Path Algorithm](https://www.comp.nus.edu.sg/~hobor/Publications/2020/CertifiedDijkstra.pdf). Aquinas Hobor, Anshuman Mohan, Shengyi Wang.
* [Certifying Graph-Manipulating C Programs via Localizations within Data Structures](https://www.comp.nus.edu.sg/~hobor/Publications/2019/Localize.pdf) (OOPSLA 2019). Aquinas Hobor, Shengyi Wang, Qinxiang Cao, Anshuman Mohan.


## Installing

The library can be installed using [opam](https://opam.ocaml.org/). Different packages are offered for different target architectures.

### `x86_64-linux`

```console
$ opam install ./coq-certigraph.opam
```

### `x86_32-linux`

```console
$ opam install ./coq-certigraph-32.opam
```

## Building without installing

It is possible to build CertiGraph without installing it as a library. This is useful if you simply want to check out the examples, or if you want to hack on CertiGraph itself.

The accompanying `Makefile` provides several useful targets:

### Library and examples

First, edit the `CONFIGURE` file to reflect your build environment. Then:

```console
$ make clean
$ make lib-and-examples
```

The `lib-and-examples` target builds the library and all examples. It also generates a [`_CoqProject`](https://coq.inria.fr/refman/practical-tools/utilities.html#building-a-coq-project-with-coq-makefile) file. This is particularly useful if you want to step through the examples in [`vs-coq`](https://github.com/coq-community/vscoq).

### Just the library

First, edit the `CONFIGURE` file to reflect your build environment. Then:

```console
$ make clean
$ make lib
```

The `lib` target builds the library but not the examples.
