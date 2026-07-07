# Cubicle

Cubicle is an experimental proof assistant based on a one-dimensional cubical type theory developed by Jon Sterling, Carlo Angiuli, and Daniel Gratzer <a id="1">[1]</a><a id="1">[2]</a>. Its name is a pun based on the fact that the system only deals with a small space partitioned off within a larger spaces studied in univalent foundations. To be precise, Cubicle runs on a cubical reconstruction of extensional type theory that enjoys a judgmental version of the unicity of identity proofs principle (UIP), meaning that any two elements of the same path type are the same up to judgmental identity. 

## Installation

To install and use Cubicle, you need OCaml version 4.14.2 or greater. We also recommend relying on the [opam](https://opam.ocaml.org/) package manager for installation. You will also need [menhir](https://opam.ocaml.org/packages/menhir/) for the LR(1) parser generator, and [dune](https://github.com/ocaml/dune) for building the project. Both can be installed using opam. It is best to ensure that your opam is up-to-date before installing the dependencies:

```
$ opam update && opam upgrade
$ opam install menhir dune
```

Next, clone the repository and build the project using dune:

```
$ git clone https://github.com/bbentzen/cubicle.git
$ cd cubicle
$ dune build
```

This will create the executable `main.exe` which you can run on any `.cube` file to typecheck its contents with Cubicle. Since this compiled executable is typically be found under a subfolder such as `_build/default/bin`, you can run it as follows:

```
$ dune exec _build/default/bin/main.exe [filename].cube
```

However, we recommend using the cubicle-vscode extension for verification support. This extension is available on the VSCode marketplace as cubicle-vscode. 
It supports syntax highlighting, snippet completion, bracket matching, bracket autoclosing, bracket autosurrounding, 
comment toggling (`Ctrl` + `/`), and Unicode abbreviations for transforming `\to` into `→`, `\to` into `→`, `\lambda` and `\let` into `λ`, `\Pi` into `Π`, `\Sigma` into `Σ`, `\times` into `×`, `\vdash` into `⊢`, `\nat` into `ℕ`, and `\I` into `𝕀`, using VS Code's native IntelliSense engine.

## Usage

We assume that the user is relatively familiar with cubical type theory. See <a id="1">[3]</a> for a friendly introduction. 

## Support

This work was partly supported by the US Air Force Office of Scientific Research (AFOSR) grant FA9550-18-1-0120. Any opinions, findings and conclusions, or recommendations expressed in this material are those of the author and do not necessarily reflect the views of the AFOSR.

## References
<a id="1">[1]</a> 
Jonathan Sterling, Carlo Angiuli, Daniel Gratzer. 
Cubical syntax for reflection-free extensional equality. 
In Herman Geuvers (ed.), 4th International Conference on Formal Structures for Computation and Deduction (FSCD 2019), volume 131 of Leibniz International Proceedings in Informatics (LIPIcs), pages 31:1-31:25.
[doi:10.4230/LIPIcs.FSCD.2019.31](https://doi.org/10.4230/LIPIcs.FSCD.2019.31), [arXiv:1904.08562](https://arxiv.org/abs/1904.08562).

<a id="1">[2]</a> 
Jonathan Sterling, Carlo Angiuli, Daniel Gratzer. 
A Cubical Language for Bishop Sets. 
Logical Methods in Computer Science, 18 (1), 2022.
[doi:10.46298/lmcs-18(1:43)2022](https://doi.org/10.46298/lmcs-18(1:43)2022), [arXiv:2003.01491](https://arxiv.org/abs/2003.01491).

<a id="1">[3]</a> 
Bruno Bentzen. Naive cubical type theory. 
Mathematical Structures in Computer Science, 31, pp. 1205–1231, 2021.
[doi:10.1017/S096012952200007X](https://doi.org/10.1017/S096012952200007X), [arXiv:1911.05844](https://arxiv.org/abs/1911.05844).
