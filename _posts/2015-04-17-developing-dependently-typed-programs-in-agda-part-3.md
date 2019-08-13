---
title: 'Developing Dependently Typed Programs in Agda - Part 3'
date: 2015-04-17
permalink: /posts/2015/04/developing-dependently-typed-programs-agda-3/
tags:
  - Agda
---

And finally I've decided to start the third part of my post series on
_Developing Dependently Typed Programs in Agda_. In this post, I'll
explain how to use Agda to develop a certified interpreter for the
simply typed \\(\lambda\\)-calculus.

# The simply typed \\(\lambda\\)-calculus

In a very simplistic way, the simply typed \\(lambda\\)-calculus can
be seen as a bare-bones statically typed functional programming
language without polymorphism. By statically typed, I mean that every
that error can be detected by a compiler without running the code, a
very desirable property.

In this section I'll describe the syntax, semantics and type rules for
the calculus using math notation.

## Syntax definition

We will consider a \\(\lambda\\)-calculus with one base type:
boolean. In our definitions, we will use the following convention for
meta-variable usage:  \\(\tau\\) will denote types;\\(x\\),
variables; \\(e\\), term expressions. All these meta-variables can
appear primed or subscripted.

Syntax for types is given below:

\\[
\begin{array}{lcl}
\tau & ::= & \texttt{Bool} \\
       & \mid & \tau \to \tau \\
\end{array}
\\]

Term syntax have boolean constants and usual
variables, abstraction and application.

\\[
\begin{array}{lcll}
e & ::=    & true  \\
& \mid & false \\
& \mid & x    \\
&\mid & \lambda x : \tau. e \\
& \mid & e \: e  \\
\end{array}
\\]

## Semantics

The semantics that we will consider is a traditional call-by-value
small-step semantics. We will denote the semantics as a relation \((e
\Rightarrow e'\)), that means "\\(e\\) can take a step of evaluation
and produce \\(e'\\)". Before presenting the semantic rules, we need
to specify what are the values of the language. In semantics, we
consider as values terms that can be seen as a answer to the program
executed. As usual, we wil consider as values abstractions and boolean
constants (values will be represented by meta-variable \\(v\\)):

\\[
\begin{array}{lcl}
v & ::= & \lambda x. e \\
& \mid & true \\
& \mid & false
\end{array}
\\]

The main issue on operational semantics for \\(\lambda\\)-calculus is
the so-called \\(\beta\\) reduction that allow us to perform
computation in a application:

\\[
 (\lambda x : \tau .e)\: v \Rightarrow [x \mapsto v]\:e
\\]

Note that, we always perform \\(beta\\) reductions on applications
formed by a abstraction (obvious...) and a value, i.e., in order to
reduce a application, its argument must be fully reduced.

A next obvious questions is how to reduce a application that does not
fit this previous "shape"? This is done by these following rules:

\\[
\frac{e\_{1} \Rightarrow e\_{1}'}{e\_{1}e\_{2}\Rightarrow e\_{1}' e\_{2}}
\\]

\\[
\frac{e\_{2} \Rightarrow e\_{2}'}{v\_{1}e\_{2}\Rightarrow v\_{1} e\_{2}'}
\\]

Together, these rules show that in any application, we must reduce its
left hand side until we reach a value and only then, we reduce its
right hand side.

Using these rules, we should be able to reduce any _typeable_ term
until we reach a value. But, for untypeable terms, we can reach a
_normal form_ (a term that cannot be further reduced) that isn't a
value. An example of a normal form that isn't a value is _true false_.
Normal forms that aren't values are usually called stuck terms. The
motivation for the use of type systems in programming languages is to
statically detect stuck terms, since these terms does not have a well
defined semantics, they can produce weird results when executed by a
machine.

In the next subsection, I'll explain the type system for the simply
typed \\(\lambda\\)-calculus.

## Type system

The type system for the simply typed \\(\lambda\\)-calculus is a
syntax directed proof system for deduce judgements of the form
\\(\Gamma \vdash e : \tau\\). The meta-variable \\((\Gamma\\) stands
for a typing context. A typing context is a set of pairs formed by
variables and their types. Usually, we represente such pairs by \\(x : \tau\\).

Now we proceed to type system itself. Type rules for boolean constants are obvious:

\\[
\frac{}{\Gamma \vdash true : \texttt{Bool}}
\\]


\\[
\frac{}{\Gamma \vdash false : \texttt{Bool}}
\\]

We can say that a variable \\(x\\) is well typed if it has an
assumption in typing context \\(\Gamma\\):

\\[
\frac{x : \tau \in \Gamma}{\Gamma\vdash x : \tau}
\\]

A abstraction is well typed if we can type its body using as
additional assumption its parameter:

\\[
\frac{\Gamma,x : \tau' \vdash e : \tau}{\Gamma \vdash \lambda x : \tau' .e : \tau' \to \tau}
\\]
The notation \\(\Gamma,x : \tau'\\) means \\(\Gamma \cup \\{x : \tau'\\}\\).
Finally, a application is well typed if its parameter type matches the
argument type.

\\[
\frac{\Gamma \vdash e : \tau' \to \tau\qquad \Gamma\vdash e' : \tau'}{\Gamma\vdash e\ e' : \tau}
\\]

These rules are sufficient to ensure the following properties:

**Progress**: If \\( \Gamma\vdash e : \tau \\) then \\( e \\) is a value or
exists \\( e' \\) such that \\(e \Rightarrow e'\\).

**Preservation**: If \\( \Gamma\vdash e : \tau \\) e \\(e \Rightarrow e'\\) then \\(\Gamma\vdash e' : \tau \\).

The first property ensures that any well typed term isn't stuck and
the second, that evaluation preserves types. Together, these
properties, ensures that any well typed program does not  "crash" when
executed, a fact that many programming languages does not have.

Next, I'll describe how to implement this whole theory using Agda.

# Agda Implementation

## Syntax

In order to represent the \\(\lambda\\)-calculus syntax, I'll follow a
quite standard approach, representing variables using [DeBruijn
indexes](http://en.wikipedia.org/wiki/De_Bruijn_index). Basically, the idea is to representing variables by a natural number
that represents that the current variable is bound to the k'th enclosing
\\(\lambda\\).

{%highlight agda%}
data Exp : Set where
  val : Bool → Exp
  var : ℕ → Exp
  abs : Ty → Exp → Exp
  app : Exp → Exp → Exp
{%endhighlight%}

Exp's constructors have a
straightforward meaning: *const* represents boolean constants; *var*, variables;
*abs* , abstractions and *app*, applications. Note that in *abs*
constructor, note that we **must** provide parameter's
type. Otherwise, we'll need to deal with unification, that is a other history...

Type syntax has a straightforward definition:

{%highlight agda %}
data Ty : Set where
	bool   : Ty
    _=>_ : Ty -> Ty -> Ty
{%endhighlight %}
We'll represent typing contexts using lists:
{%highlight agda %}
Ctx : Set
Ctx = List Ty
{% endhighlight %}

## Type checker

The diligent reader may have noticed that our contexts only store
types, but what about variable identifiers? Since variables are
DeBruijn indexes, they are just natural numbers, or even better,
a position of its corresponding type in a typing context! We'll
explore this fact using
the following data type will be used to represent context membership
proofs:
{%highlight agda%}
data _∈_ {A : Set} : A → List A → Set where
  here  : ∀ {x xs} → x ∈ x ∷ xs
  there : ∀ {x y xs} → y ∈ xs → y ∈ (x ∷ xs)
{% endhighlight %}
Using this type, we can retrive a variable index:
{%highlight agda %}
index : ∀ {A : Set}{x : A}{xs : List A} → x ∈ xs → ℕ
index here      = zero
index (there n) = suc (index n)
{%endhighlight%}
Now, we are ready to define a data type to represent the result of a
lookup function.
{%highlight agda %}
data Lookup {A}(xs : List A) : ℕ → Set where
  inside  : ∀ x (p : x ∈ xs) → Lookup xs (index p)
  outside : ∀ m → Lookup xs (length xs + m)
  {% endhighlight %}
The data type *Lookup* encode two possible results of looking up a
position in a list: the position can be inside the list - constructor
**inside**; or the position is outside the list - constructor
**outside**. The *inside* constructor takes a proof that some value
*x* is in the list *xs* and indexes the *Lookup* type by the list
position induced by such a proof. A position is outside the list, if
it is greater or equal the list length.

With all equipment set, we can implement a lookup function that
returns a value of type *Lookup*, that give us a lot of information
about list searching execution.

{%highlight agda%}
lookup : {A : Set}(xs : List A)(n : ℕ) → Lookup xs n
lookup [] n = outside n
lookup (x ∷ xs) zero = inside x here
lookup (x ∷ xs) (suc n) with lookup xs n
lookup (x ∷ xs) (suc .(index p)) | inside y p = inside y (there p)
lookup (x ∷ xs) (suc .(length xs + m)) | outside m = outside m
{% endhighlight %}

Next, the following type represent type derivations:

{%highlight agda %}
data _⊢_ (G : Ctx) : Ty → Set where
  tval : G ⊢ bool
  tvar : ∀ {t} (p : t ∈ G) → G ⊢ t
  tabs : ∀ t {t'} → G , t ⊢ t' → G ⊢ t => t'
  tapp : ∀ {t t'} → G ⊢ (t => t') → G ⊢ t → G ⊢ t'
{% endhighlight %}
From a given type derivation, we can get its corresponding term using
a erasure fuction:
{%highlight agda %}
erase : ∀ {G t} → G ⊢ t → Exp
erase tval = val
erase (tvar p) = var (index p)
erase (tabs t p) = abs t (erase p)
erase (tapp p p') = app (erase p) (erase p')
{% endhighlight %}
The result of a type-checker execution is given by the following type:
{%highlight agda %}
data TypeCheck (G : Ctx) : Exp → Set where
  ok : ∀ {t}(d : G ⊢ t) → TypeCheck G (erase d)
  bad : ∀ {e} → TypeCheck G e
  {%endhighlight%}
A type checker can only give two possible results: success, if the
term passed is typable or failure, if the term is untypeable. These
two situations are expressed by the constructors of *TypeCheck* data
type.

Now, we can finally proceed to the type checking function:
{%highlight agda%}
tc : ∀ G (e : Exp) → TypeCheck G e
tc G val = ok tval
tc G (var x) with lookup G x
tc G (var .(index p))      | inside x p = ok (tvar p)
tc G (var .(length G + m)) | outside m = bad
{%endhighlight%}
The constants case are immediate. Next,
we deal with the variable case. To search the typing
context, we will use *lookup* function, and return the appropriate
value of *TypeCheck* in each situation.
{% highlight agda %}
tc G (abs t e) with tc (G , t) e
tc G (abs t .(erase d)) | ok d = ok (tabs t d)
tc G (abs t e)          | bad = bad
{% endhighlight %}
In abstraction case, we just call the type checking function
recursively for abstraction body and a modified typing context with
abstraction parameter type.
{% highlight agda %}
tc G (app e e') with tc G e | tc G e'
tc G (app ._ ._ ) | ok {t => _} d | ok {t'} d₁ with t == t'
tc G (app ._ ._)  | ok {t => z} d | ok d₁ | eq = ok (tapp d d₁)
tc G (app ._ ._)  | ok {t => z} d | ok d₁ | neq = bad
tc G (app e e')   | _       | _ = bad
{% endhighlight %}
The last case of type checking function, deals with
applications. In applications, we must call the type checker
recursively for two components and check if

     1. The left component must be a function type.
     2. The right component type must match the left component function
     argument type.
 	 3 . The components must be type correct.
Each equation deals with one of these three options, respectively.


## Interpreter

Implementing interpreters in total languages is a rather problematic
task, due to totality restrictions. Other complication with a
interpreter for \\(\lambda\\)-calculus is dealing with
substitution. But, do not fear... We can use a very smart trick to
interpret \\(\lambda\\)-calculus. The idea is to interpret
\\(\lambda\\) calculus types as Agda types. This translation is given
bellow:
{%highlight agda %}
⟦_⟧T : Ty → Set
⟦ bool ⟧T = Bool
⟦ t => t' ⟧T = ⟦ t ⟧T → ⟦ t' ⟧T
{% endhighlight %}
Now, we need to translate contexts to right nested tuples of types
ended with a *tt*, a trivial value of trivial type.
{%highlight agda %}
⟦_⟧C : Ctx →(Ty → Set) → Set
⟦ [] ⟧C f = tt
⟦ t :: ts ⟧C f = ⟦ t ⟧T × ⟦ ts ⟧C f
{% endhighlight %}
The translation of context membership proofs to a type is done by the
following function.
{% highlight agda %}
⟦_⟧V : ∀ {C t V} → t ∈ C → ⟦ C ⟧C V → V t
⟦ here ⟧V   (gam , t)  = t
⟦ there i ⟧V  (gam , s)  = ⟦ i ⟧V gam
{% endhighlight %}
Glueing all pieces, we built the interpreter. The idea is simple:
translate \\(\lambda\\) terms to its corresponding Agda terms using
the previous semantic interpretation functions.
{%highlight agda %}
⟦_⟧ : ∀ {C t} → C ⊢ t → ⟦ C ⟧C ⟦_⟧T → ⟦ t ⟧T
⟦ tval ⟧  _ = false
⟦ var x⟧ C = ⟦ x ⟧V C
⟦ abs t ⟧ C = \ s -> ⟦ t ⟧T (s :: C)
⟦ app l r ⟧ C = ⟦ l ⟧ C (⟦ r ⟧ C)
{%endhighlight%}
Note that abstraction is translated to a anonymous function and
application, to a application. Simple, no?

# Conclusion

In this post I give a simple formalization of the simply
\\(\lambda\\)-calculus in Agda. I have formalized its type checker and
give a simple interpreter based on an denotational semantics of the
\\(\lambda\\) calculus.
