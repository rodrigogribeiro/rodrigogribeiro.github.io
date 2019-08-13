---
title: 'Developing Dependently Typed Programs in Agda - Part 2'
date: 2014-07-13
permalink: /posts/2014/07/developing-dependently-typed-programs-agda-2/
tags:
  - Agda
---

# Introduction

Here we are again in our mission to understand Agda programming
language and how dependent types eases the task of construct correct
software. As I have said before, I am basing this tutorial on a Connor
McBride's talk _Developing Dependently Typed Programs in LEGO_,
extending it here or there...

In this post, I will discuss the type of finite sets, a very useful data
type. But, first we need to understand what is a dependent type and
how it can help us in our task to build better software. To this end,
first I will present vectors, or size indexed lists, as they are a
cannonical example of dependent types.

# Vector as cannonical example of dependent types

Lists are a very useful data type that are part of every functional
programmer toolbox.
Below is the definition of lists and a function that returns
the head of a given list.
{%highlight agda%}
data List (A : Set) : Set where
	[] : List A

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

headList : ∀ {A : Set} → List A → Maybe A
headList [] = nothing
headList (x ∷ _) = just x
{%endhighlight%}

Lists are useful, but have some drawbacks. For example,  how can we define a head
function that exclude applications on empty lists? On languages that
do not support dependent types, the solution is use a dummy value to
be returned in the case that the list passed as an argument is empty
or use a data type like `Maybe` or `Either` (Haskell terminology...)
that can be used to represent something like exceptions in a pure
setting.

The main issue with lists is that its data type definition give us no
information on how many elements their values have. To solve this
problem, we can use a similar data type, indexed by a natural number
that represents the number of elements in the list. We call such type
a `Vector` and its definition is:

{% highlight agda %}
data Vec {l}(A : Set l) : ℕ → Set l where
  [] : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)
{% endhighlight %}

Using type theory terminology, `Vector` data type defines an _indexed
type family_. This means that for each natural number \\(n\\) we have a
type `Vec A n`. Note that, unlike Haskell and ML that support
parametric polymorphism, Agda types can be parameterized not just by
types but also by _values_. Defining types that have arbitrary values
as parameters is what we call a _dependent type_.

The `head` function for vectors does not have to use  `Maybe` or other
tricks to deal with empty list. Since vectors carry their size in its
type, we can just specify that the function should be applied just to
non-empty vectors, i.e., values with type of the form `Vec A (suc n)`.
The code for this function is given below:

{%highlight agda %}
head : ∀ {A : Set}{n : ℕ} → Vec A (suc n) → A
head (x ∷ _) = x
{% endhighlight %}

Other function that we need to use tricks to implement it in Haskell,
is `zip`, that combine two lists in a list of pairs. What should be
returned when the lists does not have the same length? The Haskell
library's solution is to return a empty list when one of the
parameters become empty.
{%highlight agda%}
zipList : ∀ {A B} → List A → List B → List (A × B)
zipList [] ys = []
zipList (x ∷ xs) [] = []
zipList (x ∷ xs) (y ∷ ys) = (x , y) ∷ zipList xs ys
{%endhighlight%}
Again, the problem is that list data type does not give us enough
information about "garbage" values, so we are forced to use some trick
like discard the remaining elements of the greater list.

With vectors, we avoid this situation by requiring that the vectors
passed as arguments does have the same length. As a bonus, we have
that the `zip` function type also guarantee that the result list does
have the same size of the input lists.
{%highlight agda %}
zip : ∀ {A B n} → Vec A n → Vec B n → Vec (A × B) n
zip [] [] = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip xs ys
{%endhighlight%}

The reader must noticed that I said nothing about pairs. Next section
will fix this little mistake.

# A little digression: Dependent Products

Dependent products, or Σ-types, are a generalization of
product types present in Haskell and ML in such a way that second
component's type depends on first component's value.

Dependent products have the following definition in Agda:

{%highlight agda %}
  record Σ {l l'}(A : Set l)(B : A → Set l') : Set (l ⊔ l') where
    constructor _,_
    field
      fst : A
      snd : B fst
{% endhighlight %}

I have defined this type using record notation. Records allow us to
define fields for some components of the type being defined. Also
fields automatically generate record projection functions, as in
Haskell. In the previous definition, the record \\(\Sigma\\) has the
projection functions _fst_, that returns the first component
of a dependent product, and _snd_ that returns the second component.

Since Haskell (or ML) like products are a special case of dependent
products, we can easily define one in terms of the other. Such
definition is presented below:
{%highlight agda%}
_×_ : ∀ (A B : Set) → Set
A × B = Σ A (λ _ → B)
{% endhighlight %}
As an aside, each record declaration defines a module. So, we can open
a record definition, like a module, in order to bring to the scope the
projection functions and constructors defined in the record.

# Finite set type

Finite sets are a \\(\mathbb{N}\\)-indexed type with \\(n : \mathbb{N}\\)
elements:
{%highlight agda%}
data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)
{%endhighlight%}
You should noticed that:

- There's no value of _Fin 0_, since all _Fin_'s constructors have
  indices of shape _suc n_, for some \\(n : \mathbb{N}\\).
- The type _Fin n_ is inhabited by exactly \\(n\\) elements, i.e, the
  type _Fin 2_ has the following elements: _zero : Fin 2_ and _suc
  zero : Fin 2_. If _v : Fin n_ then _suc v_ has type _Fin (suc n)_
  and the effect of using _Fin_'s _suc_ constructor is that we are
  increasing the finite set's size by one.

Here I'll not present the elimination principle for _Fin_ because its
type is long and it doesn't render well to html. It's defined in the
Agda source code of this post on
[github](https://github.com/rodrigogribeiro/developing-dependently-typed-programs-agda).

# Using finite sets to define a safe lookup function

Defining a function for looking up a element in a given position of a
list is quite straightforward:
{%highlight agda%}
lookupList : ∀ {A} → ℕ → List A → Maybe A
lookupList _ [] = nothing
lookupList zero (x ∷ _) = just x
lookupList (suc n) (_ ∷ xs) = lookupList n xs
{%endhighlight%}
the problem here is that we are using _Maybe_ type just to ensure that
this function is total.

The use of _Maybe_ is just to avoid the case that we pass an invalid
index to  _lookupList_ function (invalid means that the index passed
is greater than the list length). We can just rule out this using
finite sets and vectors, since both are indexed by natural numbers, we
can guarantee, using a type, that only valid indexes can be
passed. Below is the code for the _lookup_ function that uses finite
sets and vectors:
{% highlight agda %}
lookup : ∀ {A : Set}{n} → Fin n → Vec A n → A
lookup zero (x ∷ xs) = x
lookup (suc n') (_ ∷ xs) = lookup n' xs
{% endhighlight %}
Since _Vec A n_ is a type of vectors with _n_ elements and _Fin n_ is
a type of _n_ elements, using an index of type _Fin n_ in a vector of
type _Vec A n_ simply rule out all invalid indexes! Cool!

# Closing up

In this post I've presented examples of indexed data types -
vectors and finite sets - and used them to define a safe lookup
function. In the next posts we will continue our adventure through
Agda programming language and its wonderful world of dependently typed
programming.

See you on the next chapter of this series...
