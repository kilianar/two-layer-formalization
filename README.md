# Autoformalization of "Two ReLU layers is all you need"

A Lean formalization of the result that the maximum of `n` real numbers can be computed by a ReLU
network with two hidden layers. It was produced using Opus 5.5 with minimal human input, based on a
preliminary version of [arXiv:2610.28587](https://arxiv.org/abs/2610.28587).

The main results are `max_mem_reluNet` and `exists_twoLayerNet_eq_max` in
[`TwoHiddenLayers/Main.lean`](TwoHiddenLayers/Main.lean). The definitions and the statements of
the main results were checked by humans to ensure they faithfully reproduce the paper.

## Building

```
lake exe cache get
lake build
```
