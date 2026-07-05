# Cubo

Cubo is an experimental proof assistant based on the cubical type theory developed by Jon Sterling, Carlo Angiuli, and Daniel Gratzer <a id="1">[1]</a><a id="1">[2]</a> , a cubical reconstruction of extensional type theory that enjoys canonicity, function extensionality, and a judgmental version of the unicity of identity proofs principle (UIP): any two elements of the same identity type are judgmentally equal. 

## Installation

Cubo runs on OCaml version 4.14.2 or greater and uses [opam](https://opam.ocaml.org/), [menhir](https://opam.ocaml.org/packages/menhir/), and [dune](https://github.com/ocaml/dune).

Clone the repository and build the project using dune:

```
$ git clone https://github.com/bbentzen/cubo.git
$ cd cubo
$ opam update
$ dune build
```

We also recommend to use the cubo-vscode extension for verification support. This extension is available on the VSCode marketplace as cubo-vscode. 
It supports syntax highlighting, snippet completion, bracket matching, bracket autoclosing, bracket autosurrounding, 
comment toggling (`Ctrl` + `/`), and Unicode abbreviations for transforming `\to` into `→`, `\to` into `→`, `\lambda` and `\let` into `λ`, `\Pi` into `Π`, `\Sigma` into `Σ`, `\times` into `×`, `\vdash` into `⊢`, `\nat` into `ℕ`, and `\I` into `𝕀`, using VS Code's native IntelliSense engine.

## Usage

There are essentially four main kinds of commands for entering the proof environment, importing files and modularizing proofs, declaring variables and universe levels, and extracting and priting terms from definitions and theorems:

### Proof environment

The proof environment is the main command where definitions are stated and theorems and lemmas are proven. Syntactically speaking, there is no difference between defintitions and theorems and lemmas. Users can use `def`, `definition`, `thm`, `theorem`, `lem`, and `lemma` interchangeably.

```
  def [name-of-theorem] [context] 
  ⊢ [type] := [term]
```

Contexts are lists of variable declarations. Explicit variables are enclosed with `(` and `)` and must be passed as parameters when the definition or theorem is reused later. Implicit variables are enclosed with curly braces `{` and `}` and can be inferred by the elaborator. Multiple variables of the same type can be declared at the same time.

Types and their terms are determined by Cubo's core language. Currently, it contains the following type-formers, constructors, and eliminators for the function type, product type, sum type, unit type, empty type, boolean type, natural number type, dependent function type, dependent product type, dependent path type, interval, and universe types, where A and B denote arbitrary types, x arbitrary variables, and M, N arbitrary terms:

Type names | Notation | Constructors | Eliminators
------------ | ------------- | ------------- | -------------
Function type | A → B |  λ x , M | app M N
Product type | A × B | ( M , N ) | fst M and snd M
Sum type | A + B |	inl M and inr M	| case M N1 N2
Unit type	| unit | ()	| let M N
Empty type | empty | | abort M
Boolean type | bool | true  and  false | if M N1 N2
Natural Numbers	| nat or ℕ | 0  and  s	| natrec	M N1 N2
Dependent function type	| Π (x : A) B | λ x , M | app M N
Dependent product type | Σ (x : A) B | ( M , N ) | fst M and snd M
Dependent path type | pathd A x y | < x > M | M @ N
Interval | I or 𝕀 | i0 and i1 | 
Universe type | type n | 

Moreover, the language also contains two primitive functions known as Kan operations:

- Coercion. This is a cubical generalization of Leibniz's indiscernibility of identicals. Essentially, coercion states that, given any line type I → A and any term M : A i, where i j : I, we have a term of the type A j, called the coercion of M in A, and denoted by `coe i j A M`.

- Composition. Simply put, composition states that any open box has a lid. More precisely, given any three lines M N N' : I → A such that (i) the initial point of M is judgmentally equal to the initial point of N and (ii) the terminal point of M is judgmentally equal to the initial point of N', the composition also asserts the existence of square I → I → A whose top face is M, left face is N, right face is N'. The composition is written `hfill M | i0 → N0 | i1 → N1`.

Because the unicity of identity proofs holds judgmentally, Cubo rests on a simplified version of composition in which, unlike other cubical type theories, there are no higher-dimensional composition scenarios. 

### File import

This command imports a specified file into the current file. The syntax is 

`import [filename]`

### Universe declaration 

This declares a universe level variable according to the syntax 

`universe [id]`

### Term extraction 

This extracts and prints the term corresponding to a definition or theorem with the syntax 

`print [name]`


### Examples

For a simple example, consider nondependent and dependent function application,

````
def ap {A B : type l} (f : A → B) {a b : A} 
⊢ path A a b → path B (app f a) (app f b) :=
λp, <i> app f (p @ i)
 
def apd {A : type l} {B : A → type l} (f : Π (x : A) app B x) {a b : A} (p : path A a b)
⊢ pathd (λi, app B (p @ i)) (app f a) (app f b) :=
<i> app f (p @ i)
````

Function extensionality can be easily proven as follows:

````
def funext {A : type l} {B : A → type l} (f g : Π (x : A) app B x) 
⊢ (Π (x : A) path (app B x) (app f x) (app g x)) → path (Π (x : A) app B x) f g :=
λh, <i> (λ x, (app h x) @ i)
````

For a definition of based path induction (otherwise known as J): 

````
def pathrec {A : type l} {a : A} (C : Π (x : A) (path A a x → type l)) {b : A} (p : path A a b) (c : app app C a (<_> a)) 
⊢ app app C b p := 
coe i0 i1 (λ i, app app C (p @ i) (app meet p @ i)) c 
````

A comprehensive list of examples can be found [here](https://github.com/bbentzen/cubo/blob/master/tests/success/).

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