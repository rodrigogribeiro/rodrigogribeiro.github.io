---
title: 'Records, Modules and Instance Arguments in Agda'
date: 2016-09-05
permalink: /posts/2016/09/records-and-modules-in-agda/
tags:
  - Agda
---

Lately, I'm having some trouble with records and its relation with
modules in Agda. Basically, I'm trying to formalize some results
from category theory and algebra in Agda and I'm using records
to represent a hierarchy of algebraic structures.

So far, so good. Since scope issues in Agda records / modules are
causing to me some headaches, I've decided to spent some time
making experiments on how these features behaves with respect
to scoping rules.

Other recent addition to Agda is the so-called instance arguments.

The main source for this post is
[Dependently typed programming in Agda](http://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf),
by Ulf Norell and James Chapman and some pages about records, modules
and instance arguments on [Agda Wiki](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.HomePage).


Records
=====

In Agda, record definitions are declared using record keyword and its
fields are specified using field keyword. Next, we can see a simple
record definition for a semigroup:

{% highlight agda %}
record Semigroup : Set where
    field
        S : Set
        _∙_ : S → S → S
{% endhighlight %}

In algebra, we say that a semigroup is a algebraic structure formed by
a type (here, named S) and an associative binary operator, _∙_.
Our semigroup definition, doesn't say that ∙ is a
associative. Following the pattern used by Agda standard library,
we divide the _computational content_ and _logical specification_
of algebraic structures in two record types, as follows:

{% highlight agda %}
record IsSemigroup {S : Set}(_∙_ : S → S → S) : Set where
   field
      assoc : ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z

record Semigroup : Set where
    field
        S : Set
        _∙_ : S → S → S
        isSemigroup : Semigroup _∙_
    open IsSemigroup isSemigroup public
{% endhighlight %}

In semigroup definition, we have opened IsSemigroup record
to bring into scope all of its definitions. Now, we can access
the associativive property of a binary operator using
Semigroup.assoc.

But why I've opened IsSemigroup like a module definition?
In Agda, records are just like modules (or modules are like
records...), so to bring stuff defined in a record into scope
we need to open, like we open a module.

Modules
=======

Agda has a very simple, yet useful, module system. Modules can have
types and functions as parameters but, unlike ML, modules cannot be
parameter of another modules.

An interesting feature of Agda's module system is that we can open
a module locally within an expression. For example:

{% highlight agda %}
test : (x y z : Nat) ->
   let open Semigroup natSemigroup in
   x + y + z ≡ (x + y) + z
test x y z = ?
{% endhighlight %}

We can also rename things during a module opening to avoid name clash
conflicts. Next source code piece, shows a definition of a
commutative semiring and how can we bring two diferent commutative
monoid definitions into context.

{% highlight agda %}
record IsCommutativeSemiring {l}{A : Set l}
          (_+_ _*_ : Op₂ A)
          (0# 1# : A) : Set l where
	field
      +-isCommutativeMonoid : IsCommutativeMonoid _+_ 0#
      *-isCommutativeMonoid : IsCommutativeMonoid _*_ 1#
      *-distributesOver-+   : _*_ DistributesOver _+_
      *-zero                : Zero 0# _*_

open IsCommutativeMonoid +-isCommutativeMonoid
	renaming ( assoc to +-assoc
                    ; comm to +-comm
                    ; identity to +-identity
                    ; isMonoid to +-isMonoid
                    ; isSemigroup to +-isSemigroup
                    ) public

open IsCommutativeMonoid *-isCommutativeMonoid
	renaming ( assoc to *-assoc
                   ; comm to *-comm
                   ; identity to *-identity
                   ; isMonoid to *-isMonoid
                   ; isSemigroup to *-isSemigroup
                   ) public
{% endhighlight %}

Notice that we opened the commutative monoid definition for sum and
for multiplication but give different names for properties like
identity to avoid name clashes when using such algebraic structure in
a formalization.

Instance Arguments
=============

In some sense, Agda instance arguments are the equivalent of Haskell's
type classes. Technically, instance arguments are resolved by instance
resolution that searchs current context for a unique solution of the
required type.

Using instance arguments we can code things almost equal
Haskell. Consider the following equality function type:

{% highlight agda %}
_==_ : {A : Set} {{eqA : Eq A}} → A → A → Bool
{% endhighlight%}

Instance arguments are specified in double curly braces, so parameter
eqA : Eq A is a instance argument for _==_. Using this function, we
can  define:

{% highlight agda %}
elem : {A : Set} {{eqA : Eq A}} → A → List A → Bool
elem x (y ∷ xs) = x == y || elem x xs
elem x []       = false
{% endhighlight%}

In the previous source code piece, instance argument is solved based
on type A. But we can also provide instance arguments explicitly using
double curly braces in a way similar to explicitly passing implicit
arguments in Agda. Next, we present elem function passing explicitly
an instance argument.

{% highlight agda %}
elem : {A : Set} {{eqA : Eq A}} → A → List A → Bool
elem {{eqA}} x (y ∷ xs) = _==_ {{eqA}} x y || elem {{eqA}} x xs
elem         x []       = false
{% endhighlight%}

Combining records with instance arguments provides a simple approach
to Haskell style type classes. As example, consider:

{%highlight agda%}
record Monoid {a} (A : Set a) : Set a where
  field
    mempty : A
    _<>_   : A → A → A

open Monoid {{...}}
{%endhighlight%}

This defines a Agda record that models a monoid and next we opened it
using instance arguments syntax. After that, all fields will have
Monoid parameter as a instance argument, this will make types of
monoid fields be:

{%highlight agda%}
mempty : ∀ {a} {A : Set a} {{_ : Monoid A}} → A
_<>_   : ∀ {a} {A : Set a} {{_ : Monoid A}} → A → A → A
{% endhighlight %}

To declare a value as an instance we can use the instance keyword,
that starts a block of definitions that can be used for instance
resolution. Next sample, declares an instance for the list monoid.

{%highlight agda%}
instance
  ListMonoid : ∀ {a} {A : Set a} → Monoid (List A)
  ListMonoid = record { mempty = []; _<>_ = _++_ }
{%endhighlight%}

One of the most interesting uses of instance arguments is to build
some simple proof search procedures. As an example, consider the
following type that encondes a list membership proof.

{%highlight agda%}
data _∈_ {A : Set} (x : A) : List A → Set where
  instance
    zero : ∀ {xs} → x ∈ x ∷ xs
    suc  : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs
{%endhighlight%}

In previous data type definition, we define its constructors as
possible instances for the search procedure defining them in a
instance block.

To automatically generate proofs, we use the following function
that returns a instance argument as a solution for a given goal.

{%highlight agda%}
it : ∀ {a} {A : Set a} {{_ : A}} → A
it {{x}} = x
{%endhighlight%}

Now, a simple proof of membership can be automatically built, using
the it function.

{%highlight agda%}
ex : {A : Set} (x y : A) (xs : List A) → x ∈ y ∷ y ∷ x ∷ xs
ex x y xs = it  -- suc (suc zero)
{%endhighlight%}

Conclusion
=======

This simple post just shows how Agda records, modules and instance
arguments can be used. My intention is just to give simple examples
of these features and how these interact. I intend to use these
features to formalize a library about categoric structures of matrix algebra.

