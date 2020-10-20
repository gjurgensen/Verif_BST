This repo is an ongoing attempt to verify a binary search tree data structure in C, using the "Verifiable C" framework for Coq.

Proofs are currently incomplete.

## Misc. notes 

To generate `bst.v` from `bst.c`, use `clightgen`:

```sh
clightgen -normalize bst.c
```
