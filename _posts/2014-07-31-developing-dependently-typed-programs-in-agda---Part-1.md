---
title: 'Developing Dependently Typed Programs in Agda - Part 1'
date: 2014-07-13
permalink: /posts/2014/07/developing-dependently-typed-programs-agda-1/
tags:
  - Agda
---

# Fist things, first...

Since I'm spending some time writing
[Agda](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.HomePage)
code, I've decided to write a port of Connor's talk [Developing
Dependently Typed Programs in LEGO](http://www.dcs.ed.ac.uk/home/ctm/dtp99/01cover.html) to Agda. I hope that this should
help me to understand dependently typed tricks used by McBride and
also could help others to understand and use Agda.

The complete code for this tutorial series will be avaliable in the
following [github repo](https://github.com/rodrigogribeiro/developing-dependently-typed-programs-agda).

With proper references done, let's get our hands dirty and write some
cool dependently typed code!

# Installation prerequisites.

From this point, I'll assume that you have installed Agda and its
emacs mode (trust me, you _must_ use emacs). The best way to install
Agda is using cabal:

  cabal update
	cabal install agda
	agda-mode setup

The last step should configure agda-mode in your emacs instalation
putting some elisp code in your .emacs config file. If have some
trouble in installing Agda, the best place to solve these is
Agda's freenode channel.

I'll also assume that you read the following
[guide to edit and compile Agda code](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.QuickGuideToEditingTypeCheckingAndCompilingAgdaCode).

# What we will do?

When we start to learn a dependently typed language one of the very
first examples that we must do is to prove that addition over natural
numbers is a commutative operation. So, in this post, I'll introduce
features of Agda in order to prove this property.

In Connor's talk, he shows how to define natural numbers and its
induction principle. In order to stay consistent with
our objective to port this talk,  I'll do the same here and then prove
that addition is commutative.

# Representing natural numbers

We will represent natural numbers using a Agda data type to encode
[Peano notation](http://en.wikipedia.org/wiki/Peano_axioms), as
follows:

{%highlight agda%}
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{%endhighlight%}

Note that Agda supports unicode characters and its syntax is inspired
by Haskell's. So, data type definitions in Agda will look quite the
same as Haskell's GADT's (Generalized Algebraic Data Types).

Using the previously defined type, we can represent the n-th natural number by n-`suc`s
followed by a `zero`. For exemple, the number `2` is represented as
`suc (suc zero)`. Of course, writing `suc`'s to represent numbers,
isn't a good idea. In order to avoid this kind of `suc`'hell, Agda
provide some pragmas that allow us to write arabic numbers instead of
sequences of type `suc`'s and `zero`.

# Induction over natural numbers

Every kid learns on its discrete math course that induction on natural
numbers is _the way_ one should use to prove \\(\forall n. P
(n)\\), where \\(n\\) is a natural number. Intuitively, induction says that if you can prove that a
property _P_ is true for \\(0\\) and if can prove that this same
property is true for \\((n + 1)\\) using the fact that \\(P(n)\\) is true,
then it is the case that \\(\forall n. P(n)\\) holds. This fact is
expressed by the following formula of logic:

$$
\left (P(0) \to \forall n. P(n) \to P(n + 1) \right) \to \forall n. P(n)
$$

Thanks to
[Curry-Howard correspondence](http://en.wikipedia.org/wiki/Curry–Howard_correspondence),
we can write a simple function that corresponds to the induction
principle for natural numbers. In fact, this function represents the
way we can define functions by structural recursion over natural
numbers.

Below, I present the definition of `ℕ-Elim` in Agda's notation:

{%highlight agda%}
ℕ-Elim : ∀ (P : ℕ → Set) → P 0 → (∀ (n : ℕ) → P n → P (suc n)) → ∀ (n : ℕ) → P n
ℕ-Elim P pz ih zero = pz
ℕ-Elim P pz ih (suc n) = ih n (ℕ-Elim P pz ih n)
{%endhighlight%}

The type of `ℕ-Elim` is just a encoding of the induction principle for
natural numbers in Agda syntax. It's definition is made by pattern
matching on `n`, the natural number bound in the conclusion `P
n` and the definition of each equation have no surprises.

# Definition of natural number addition

We can define addition over natural numbers by structural recursion
over its first parameter:

{%highlight agda %}
_+_ : ℕ → ℕ → ℕ
zero + m  = m
suc n + m = suc (n + m)
{%endhighlight%}

We can also define addition using `ℕ-Elim`:

{%highlight agda %}
_`+_ : ℕ → ℕ → ℕ
n `+ m = ℕ-Elim (λ _ → ℕ) m (λ _ ac → suc ac) n
{% endhighlight%}

The idea of the last definition is quite simple. The first parameter
of `ℕ-Elim` is a function that takes a natural number and returns a
type. So, in order to define addition, we pass a function that always
return type `ℕ`: `(λ _ → ℕ)`. The second parameter is the value that
is returned when recursion reaches `zero`: `m` and the third argument
is a function to represent how to combine the recursive call of
`ℕ-Elim`: we just use `suc` constructor. Finally, the last parameter
is the natural number that we will recurse on: `n`.

If the reader is a skeptical persion, like me, you are probably asking: "These definitions really define the
same function?". The answer is yes and we will prove this. But first we must take a little break and
talk about equality in type theory.

# A Little Digression: Equality

Equality is a very contentious subject in type theory, because there
at least 2 definitions of equality and the way the they interact with
each other is one of the aspects that we must understand in order to
use type theory based proof assistants (or dependently-typed
languages).

We will briefly talk about two equality definitions: the definitional
equality and propositional equality. The definitional equality is the
equality used by the type checker to assert that two things are equal
(of course, things are considered equal up to variable renaming). To
check equality, type checkers reduce terms to their repective normal
forms and, then compare for equality. So,
definitional equality is strong connected with reduction, since in
order to check that two terms are equal, some reduction may be
necessary. This is one of the reasons why Agda (and other similar
languages) impose restrictions in order to ensure totality of
definitions, since partial ones does not guarantee that reduction
behave well and always terminates. Since definitional equality is used
internally by the type checker, we cannot use it in our code to
express a type that says _these two terms are equal_. In order to do
that, we can define a data type that represents proofs of equality:
{% highlight agda %}
  data _≡_ {l}{A : Set l}(x : A) : A → Set l where
    refl : x ≡ x
{%endhighlight %}
The equality type only has one constructor: `refl`, which says that
a value `x` is only equal to itself. How this could be useful? The
point is that propositional equality is an _evidence_ of definitional
equality. Consider the following example:
{%highlight agda %}
test1 : 2 + 2 ≡ 4
test1 = refl
{%endhighlight%}
Definition `test1` is a proof that the equality `2 + 2 ≡ 4` holds. How
this happens? The point is that in order to assert that the terms on
both sides of the equality are the same in order to use the
constructor `refl`, the type checker must reduce `2 + 2`, which is
obviously equal to `4`.

Some properties of equality, like symmetry, transitivity and
congruence are easily stated as Agda functions:
{%highlight agda %}
sym : ∀ {l}{A : Set l}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {l}{A : Set l}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {l}{A B : Set l}{x y : A}(f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl
{% endhighlight %}

In order to make equality  proofs more readable, Agda programmers
usually define operators to resemble paper-and-pencil like chain based
equality proofs. Here is a possible definition of such operators:
{%highlight agda%}
_≡⟨_⟩_ : ∀ {l}{A : Set l}(x : A) {y z} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ xy ⟩ yz = trans xy yz

_∎ : ∀ {l}{A : Set l}(x : A) → x ≡ x
x ∎ = refl
{%endhighlight%}
With this, we have the tools needed to finish our job: 1) prove that
the two definitions of addition are equivalente and, 2) prove that
addition is a commutative operation.

# Proving the equivalence of addition definitions

After this digression on equality, we can go back to our regular
schedule and prove that our two definitions of addition are
equivalent. This property can be stated as:
{%highlight agda %}
equivalent : ∀ (n m : ℕ) → n + m ≡ n `+ m
equivalent n m = ?
{%endhighlight %}
Using emacs Agda mode facilities, we can do a case split on `n`
getting:
{%highlight agda %}
equivalent : ∀ (n m : ℕ) → n + m ≡ n `+ m
equivalent zero m = ?
equivalent (suc n) m = ?
{%endhighlight %}
and, since the first equation holds definitionally, constructor `refl`
finishes its definition.
{%highlight agda %}
equivalent : ∀ (n m : ℕ) → n + m ≡ n `+ m
equivalent zero m = refl
equivalent (suc n) m = ?
{%endhighlight %}
but in the `suc n` equation, we got stuck... This stuckness is due to
the lack of reduction on expression `suc n '+ m`. In order to convince
the type checker that `suc n '+ m` is the same as `suc (n '+ m)`, we
must prove a simple lemma:
{%highlight agda%}
lemma : ∀ (n m : ℕ) → (suc n) `+ m ≡ suc (n `+ m)
lemma zero m = refl
lemma (suc n) m = refl
{%endhighlight%}
Now, our equivalence proof can be finished using this lemma:
{%highlight agda%}
equivalent : ∀ (n m : ℕ) → n + m ≡ n `+ m
equivalent zero m = refl
equivalent (suc n) m = sym (trans (lemma n m) (cong suc (sym (equivalent n m))))
{%endhighlight%}
Pretty unreadable, huh? Using equality chain combinators we can do
better:
{%highlight agda %}
equivalent' : ∀ (n m : ℕ) → n + m ≡ n `+ m
equivalent' zero m = refl
equivalent' (suc n) m = suc (n + m)   ≡⟨ cong suc (equivalent' n m) ⟩
                         suc (n `+ m) ≡⟨ cong suc refl ⟩
                         suc n `+ m
                        ∎
{%endhighlight%}
With the first mission done, let us prove that addition is commutative.

# Proving commutativity of addition

To prove that addition is commutative we will proceed by induction
over the recursive argument of addition. To do it, we just make a case
split over `n`, getting:
{%highlight agda %}
+-comm : forall (n m : ℕ) → n + m ≡ m + n
+-comm zero m = ?
+-comm (suc n) m = ?
{%endhighlight %}
Now, agda leave us with the following types in the holes:
{%highlight agda %}
zero + m ≡ m + zero
suc n + m ≡ m + suc n
{%endhighlight %}
for each hole we will state and prove a lemma. Note that, due to the
way addition was defined, we do not have definitionally that `n + 0 =
n`. This is because addition was defined by recursion over its first
argument, so Agda cannot reduce `n+ 0` to `n`. In order to get the
desired equality, we need to do a simple inductive proof:
{%highlight agda%}
+-zeror : ∀ (n : ℕ) → n + 0 ≡ n
+-zeror zero = refl
+-zeror (suc n) = cong suc (+-zeror n)
{%endhighlight%}
The next proof is necessary in order to conclude the second goal:
{% highlight agda %}
+-suc : ∀ (n m : ℕ) → suc (n + m) ≡ n + suc m
+-suc zero m = refl
+-suc (suc n) m = cong suc (+-suc n m)
{% endhighlight %}
Now, the commutativity of addition is a simple matter of glue the
previous lemmas:
{%highlight agda %}
+-comm : forall (n m : ℕ) → n + m ≡ m + n
+-comm zero m = sym (+-zeror m)
+-comm (suc n) m = suc (n + m) ≡⟨ cong suc (+-comm n m) ⟩
                   suc (m + n) ≡⟨ +-suc m n ⟩
                   m + suc n
                 ∎
{%endhighlight %}
and this finishes the prove that addition is a commutative operation.

# Finishing up

This concludes the first post of my version of _Developing Dependently
Typed Programs in Agda_. I hope this post has motivated the reader to
continue their journey in learning Agda. See you on the next post!
