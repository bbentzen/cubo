# Cubo

This repository describes an experimental proof assistant implementing the cubical extensional type theory developed by Jon Sterling, Carlo Angiuli, and Daniel Gratzer in [Cubical Syntax for Reflection-Free Extensional Equality](https://arxiv.org/abs/1904.08562).

## The syntax

### 1 The language

Cubo is based on the following term language:

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

where A and B denote arbitrary types, x arbitrary variables, and M, N arbitrary terms.

### 2 Enviroments

#### 2.1 The proof environment

The proof environment of Cubo consists of the following syntax:

````
[command] [name-of-theorem] [context-goes-here]
⊢ [type-goes-here] :=
[term-to-be-checked]
````
where the [command] tag stands for 'definition', 'theorem', or 'lemma'.

### 3 Examples

Function application and dependent function application:

````
def ap (A B : type 1) (f : A → B) (a b : A) 
⊢ path A a b → path B (app f a) (app f b) :=
λp, <i> app f (p @ i)

def apd (A : type 1) (B : A → type 1) (f : Π (x : A) app B x) (a b : A) (p : pathd A a b)
⊢ pathd (λi, app B (p @ i)) (app f a) (app f b) :=
<i> app f (p @ i)
````

Function extensionality:

````
def funext (A : type 1) (B : A → type 1) (f g : Π (x : A) app B x) 
⊢ (Π (x : A) path (app B x) (app f x) (app g x)) → path (Π (x : A) app B x) f g :=
λh, <i> (λ x, (app h x) @ i)
````

A comprehensive list of examples can be found [here](https://github.com/bbentzen/cubo/blob/master/tests/success/examples.cubo).

