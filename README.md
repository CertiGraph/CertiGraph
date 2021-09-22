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