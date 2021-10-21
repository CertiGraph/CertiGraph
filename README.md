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

### `x86_64-linux`

First, make sure you have all of the dependencies. This can be done via opam:

```console
$ opam install --deps-only ./coq-certigraph.opam
```

Alternatively, you can fetch and compile the dependencies by hand. In that case, be sure to edit the `CONFIGURE` file to specify the path to CompCert and/or VST.

Once the dependencies are in place you can perform the build:

```console
$ make clean
$ make depend
$ make -j4
```

### `x86_32-linux`

First, make sure you have all of the dependencies. This can be done via opam:

```console
$ opam install --deps-only ./coq-certigraph-32.opam
```

Alternatively, you can fetch and compile the dependencies by hand. In that case, be sure to edit the `CONFIGURE` file to specify the path to CompCert and/or VST.

Once the dependencies are in place you can perform the build:

```console
$ make BITSIZE=32 clean
$ make BITSIZE=32 depend
$ make BITSIZE=32 -j4
```


## Developing within CertiGraph

1. Add our C source and clightgen output to the CertiGraph directory:
	1. Write your `newfile.c` inside CertiGraph.
	1. `path_to_clightgen/clightgen -DCOMPCERT -normalize -isystem . newfile.c`
	1. Add `newfile.v` to the list of sources in `Makefile`
	1. `make depend` (this is for every time you edit the makefile)
	1. `make path_to_newfile/newfile.vo` (note the .vo)
1. Create the file `verif_newfile.v`. Now something like `Require Import CertiGraph.path.to.newfile.` will go through inside `verif_newfile.v`.
