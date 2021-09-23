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

The library can be installed using [opam](https://opam.ocaml.org/). Different packages are offered for different target architectures. You can install multiple targets side-by-side.

### `x86_64-linux`

```console
$ opam install ./coq-certigraph.opam
```

### `x86_32-linux`

```console
$ opam install ./coq-certigraph-32.opam
```

## Building without installing

It is possible to build CertiGraph without installing it as a library. This is useful if you simply want to check out the examples or if you want to hack on CertiGraph itself.

Consult the `opam` files for a list of dependencies.

Manual builds can be performed using the included `Makefile`. See the subsections below for information about different use cases.

### Configuring the build

By default, the build process will:
* Provide a build for the `x86_64-linux` target;
* Execute only one job at a time (ala `make -j1`);
* Attempt to locate CompCert and VST using `coqc -where`.

There are two ways to override these settings:
1. By editing the `CONFIGURE` file.
2. By passing `VAR=VALUE` argument pairs to `make`.

See `CONFIGURE` for more information.

### Building the library and examples

The `lib-and-examples` target builds the library and all examples. It also generates a [`_CoqProject`](https://coq.inria.fr/refman/practical-tools/utilities.html#building-a-coq-project-with-coq-makefile) file. This is particularly useful if you want to step through the examples in [`vs-coq`](https://github.com/coq-community/vscoq).

Edit the commands below to reflect your desired build settings (see `CONFIGURE` for more information):

```console
$ make clean
$ make BITSIZE=64 J=4 lib-and-examples
```

### Building just the library

The `lib` target builds the library but not the examples.

Edit the commands below to reflect your desired build settings (see `CONFIGURE` for more information):

```console
$ make clean
$ make BITSIZE=64 J=4 lib
```
