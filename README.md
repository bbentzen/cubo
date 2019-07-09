# Cubo

Cubo is an experimental proof assistant based on the cubical type theory developed by Jon Sterling, Carlo Angiuli, and Daniel Gratzer in [Cubical Syntax for Reflection-Free Extensional Equality](https://arxiv.org/abs/1904.08562), a cubical reconstruction of extensional type theory that enjoys canonicity, function extensionality, and a judgmental version of the unicity of identity proofs principle (UIP): any two elements of the same identity type are judgmentally equal. 


## Summary

### 1 Language

Cubo's core language contains the following type-formers, constructors, and eliminators:

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

Moreover, the language also contains two primitive functions known as Kan operations:

- Coercion. This is a cubical generalization of Leibniz's indiscernibility of identicals. Essentially, coercion states that, given any line type I → A and any term M : A i, where i j : I, we have a term of the type A j, called the coercion of M in A, and denoted by `coe i j A M`.

- Composition. Simply put, composition states that any open box has a lid. More precisely, given any three lines M N N' : I → A such that (i) the initial point of M is judgmentally equal to the initial point of N and (ii) the terminal point of M is judgmentally equal to the initial point of N', the composition also asserts the existence of square I → I → A whose top face is M, left face is N, right face is N'. The composition is written `hfill M | i0 → N0 | i1 → N1`.

Because the unicity of identity proofs holds judgmentally, Cubo rests on a simplified version of composition in which, unlike other cubical type theories, there are no higher-dimensional composition scenarios. 

### 2 The Proof Enviroment

Cubo's main environment is the proof environment, which consists of the syntax:

<dl>
  <dd>[<em>command</em>] [<em>name-of-theorem</em>] [<em>context</em>] ⊢ [<em>type</em>] := [<em>term</em>]</dd>
</dl>

where the [*command*] tag stands for one of the following: 'def', 'definition', 'thm', 'theorem', 'lem', 'lemma'.

#### 2.1 Examples

Some notable examples include nondependent and dependent function application,

````
def ap {A B : type l} (f : A → B) {a b : A} 
⊢ path A a b → path B (app f a) (app f b) :=
λp, <i> app f (p @ i)
 
def apd {A : type l} {B : A → type l} (f : Π (x : A) app B x) {a b : A} (p : path A a b)
⊢ pathd (λi, app B (p @ i)) (app f a) (app f b) :=
<i> app f (p @ i)
````

function extensionality,

````
def funext {A : type l} {B : A → type l} (f g : Π (x : A) app B x) 
⊢ (Π (x : A) path (app B x) (app f x) (app g x)) → path (Π (x : A) app B x) f g :=
λh, <i> (λ x, (app h x) @ i)
````

and path induction (otherwise known as J), 

````
def pathrec {A : type l} {a : A} (C : Π (x : A) (path A a x → type l)) {b : A} (p : path A a b) (c : app app C a (<_> a)) 
⊢ app app C b p := 
coe i0 i1 (λ i, app app C (p @ i) (app meet p @ i)) c 
````

A comprehensive list of examples can be found [here](https://github.com/bbentzen/cubo/blob/master/tests/success/).
