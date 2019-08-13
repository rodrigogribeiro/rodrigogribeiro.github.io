---
title: 'Formalizing a list-zipper library in Coq'
date: 2018-01-16
permalink: /posts/2018/01/list-zipper-coq
tags:
  - Coq
---

These days I've been thinking a lot about formalizations 
about low level code, specially about AVR microcontrollers. When you
think about low level code, one annoying thing is how to implement
jump-like instructions in a purely functional way. One possible solution
is to use functional zippers. In this post, I'll discuss a simple implementation 
of functional zippers, inspired by 
[ListZipper](http://hackage.haskell.org/package/ListZipper) Haskell package. 
In fact, the formalization that I'll describe is a certification of this library 
using Coq proof assistant.

What are zippers?
=============

[Functional zippers](https://wiki.haskell.org/Zipper) 
are an elegant idea. Originally described by 
[Huet](https://www.st.cs.uni-saarland.de/edu/seminare/2005/advanced-fp/docs/huet-zipper.pdf), 
the zipper provides a simple and purely functional way of changing and 
navigating a data structure.

A zipper for a data type, T, 
consists of a new data type representing a "one-hole context" for T 
(the "context"), together with a value of type T (the "focus"). The 
pair can be thought of as a purely functional cursor into a data type. 
We get functions for making edits at this cursor (by simply replacing 
the focus), and relative movements (by shifting the focus into the 
hole of the context, and moving the hole elsewhere), all using pure 
functions. The name "zipper" comes from the idea that the focus and 
context interlock much like the teeth on either side of a zipper being 
pulled apart or coming together. Amazingly, these one-hole contexts for 
a type T can be computed generically by taking the derivative of T–
[a fact that was worked out by Conor McBride](http://strictlypositive.org/diff.pdf).

For lists, we are interested in move the focus left or right. In this way, 
the library ListZipper uses the following data type to represent list zippers

```haskell
data Zipper a = Zip ![a] ![a] deriving (Eq,Show)
```

and the library considers that the cursor is at second list's head:

```haskell
cursor :: Zipper a -> a
cursor (Zip _ (a:_)) = a
```

and moving the cursor left or right is easy as a pie.

```haskell
left :: Zipper a -> Zipper a
left  (Zip (a:ls) rs) = Zip ls (a:rs)
left  z               = z

right :: Zipper a -> Zipper a
right (Zip ls (a:rs)) = Zip (a:ls) rs
right z               = z
```

Note that moving the cursor left or right consists in 
moving the correspondent list head from one list to another. The ListZipper package
also provides other functions like one to restart the zipper, tests on zippers (is it in the end? 
is it empty?), folds and so on. On this post, I'll focus (no pun intended) on the correctness of 
these three functions: cursor, left and right.

Writing the ListZipper in the Coq proof assistant
====================

First things first: formalizing list zippers on Coq isn't a new idea. 
[Wouter Swierstra](http://www.staff.science.uu.nl/~swier004/publications/2012-haskell.pdf) 
already proved the correctness of a list zipper used by [XMonad](http://xmonad.org), 
a window manager, that uses list zippers to control which window is currently focused.

In order to formalize these three functions, I decided to first use QuickChick, a 
property-based testing plug-in for Coq and, only after all my definitions are ok w.r.t. 
the intended specifications, I started the formal proofs. 

What properties are interesting to be proved about the previous three functions? The main issue 
in a zipper is to keep the cursor position correct, i.e., if we call left the cursor should be 
at the list previous element and similary for right. In order to discuss such properties properly,
we need some basic Coq definitions.

Basic definitions, properties and QuickChick.
--------------------

We start by defining an inductive type for represent the zipper:

```coq
Inductive zipper (A : Type) : Type :=
| Zip : list A -> list A -> zipper A.
```
We could use a parameter `A : Set`, but it will rejected by QuickChick's automatic
instance generators (I simply don't know why...), so I generalize the sort of `zipper`
to `Type`.

In order to define the revelant properties about `left` and `right` functions, we need 
some projections to get the elements before the cursor and the ones after (and including) 
the cursor. These can be straightfowardly implemented as:

```coq
  Definition past (z : zipper A) : list A :=
    match z with
    | Zip ls _ => ls
    end.

  Definition future (z : zipper A) : list A :=
    match z with
    | Zip _ rs => rs
    end.
```

We also need some basic functions to insert an element in a list and to get the second 
element on a list (if it exists).

```coq
Definition second (xs : list A) : option A :=
  match xs with
  | (_ :: x :: _) => Some x
  | _             => None
  end.

Definition combine (x : option A)(xs : list A) : list A :=
  match x with
  | Some y => y :: xs
  | _      => xs
  end.
```
Function combine takes an `option A` and, in case that it is different from `None`, inserts 
its value in the list `xs`. Using this functions, we can code the correctness property for `right`.

```coq
Definition right_correct (z : zipper nat) :=
  (safe_cursor (right z) == (second (future z))) &&
  (past (right z) == (combine (safe_cursor z) (past z))).
```

We say that `right` is correct if after executing it on a zipper `z`, its cursor is 
the second element of `future z` and the cursor of `z` is the head of `past (right z)`, 
the list of the previous items of the zipper. The property for `left` is defined similarly, 
using the Coq list library function `hd_error` that returns the parameter list head or `None`,
if the input list is empty.

```coq
Definition left_correct (z : zipper nat) :=
  (past (left z) == tl (past z)) && 
  (safe_cursor (left z) == (hd_error (combine (hd_error (past z)) (future z)))).
```

With these properties defined, we need to implement random zipper generators or use QuickChick's 
commands to automatically derive instances for type classes `Show` and `Arbitrary`. In the formalization,
we use the instance generation facilities.

```coq
Derive Show for zipper.
Derive Arbitrary for zipper.
```

Now we just need to invoke the QuickChick command on the previously defined properties.

```coq
QuickChick right_correct.
QuickChick left_correct.
```

and QuickChick responds that everything seems to be all right.

```coq
QuickChecking right_correct
+++ Passed 10000 tests (0 discards)

real	0m0.039s
user	0m0.030s
sys	0m0.003s

QuickChecking left_correct
+++ Passed 10000 tests (0 discards)

real	0m0.035s
user	0m0.024s
sys	0m0.003s
```

Defining the cursor function
---------------------------

The definition of `left` and `right` functions is straightfoward 
(defining its correctness properties, is another history...). Function `cursor` 
can't be simply translated from Haskell to Coq because its Haskell version isn't 
total. Note that 

```haskell
cursor :: Zipper a -> a
cursor (Zip _ (a:_)) = a
```

will generate a run-time error if zipper's second list is empty. Since in Coq all 
functions must be total, the direct translation of it to Coq code will not be 
accepted by Coq's totality checker. One obvious way to circunvent this limitation is to 
use `option` type in the function's result type.

```coq
  Definition safe_cursor (z : zipper A) : option A :=
    match z with
    | Zip _ (r :: _) => Some r
    | _              => None
    end.
```

I also have flerted with using a simple dependent type to avoid using `option`. First, I had 
defined the following type.

```coq
  Definition endp (z : zipper A) : bool :=
    match z with
    | Zip _ [] => true
    | _        => false
    end.

 Definition cursor_type (z : zipper A) : Type :=
    if negb (endp z) then A else unit. 
```

which is equivalent to type `A`, when the zipper has an element at the cursor or 
equivalent to `unit`, otherwise. Using this type, we can easy build the 
cursor function  using tactics.

```coq
  Definition cursor (z : zipper A) : cursor_type z.
    destruct (endp z) eqn : Ha ; unfold cursor_type ; rewrite Ha ; simpl.
    exact tt.
    destruct z.
    destruct l0 ; simpl in *.
    congruence.
    exact a.
  Defined.
```

One inconvenient of this definition is that it generates a horrible extracted 
function (after executing command to extract it to Haskell code):

```haskell
cursor :: (Zipper a1) -> Cursor_type a1
cursor z =
  let {b = endp z} in
  case b of {
   True -> eq_rect_r True (unsafeCoerce Tt) (endp z);
   False ->
    eq_rect_r False
      (case z of {
        Zip _ l0 -> case l0 of {
                     Nil -> false_rect;
                     Cons a _ -> unsafeCoerce a}}) (endp z)}
```

So, we probably prefer to keep and use the `safe_cursor` function.

Proving the correctness properties.
---------------------

After defining and testing the functions `left` and `right`, now one last
step remains: prove its correctness properties. In the QuickChick properties
we have used boolean functions for equality and conjunction. In the statement
of our proofs, these boolean functions are replaced by the propositional 
equality and the conjunction on `Prop`, respectively.

The proofs are easy as a pie, using some tactics for automation.

```coq
  Lemma right_correct : forall (z : zipper A),
      safe_cursor (right z) = (second (future z)) /\
      (past (right z) = (combine (safe_cursor z) (past z))).
  Proof.
    intros z ; destruct z ; destruct l0 ; crush.
  Qed.

  Lemma left_correct : forall (z : zipper A),
      (past (left z) = tl (past z)) /\
      (safe_cursor (left z) = (hd_error (combine (hd_error (past z)) (future z)))).
  Proof.
    intros z ; destruct z ; destruct l ; crush.
  Qed.
```

Note that both theorems are the `Prop` analogues of the previously defined
QuickChick properties. Both proofs are simple case analysis on the structure 
of the zipper.

Lessons learned
---------------

Formalizing the ListZipper library was a fun exercice. I have spent more time
developing the tests and thinking about the correctness properties than proving
the properties about `left`, `right` and other library functions. 

All I have to say is: the usage of property based testing helped **a lot** the 
developing of this formalization. As a next step, I intend to do some code cleaning,
build a extraction script and upload the certified version of ListZipper to hackage.
Other possible continuation of this work is to use dependent types to avoid the need
of using `option` in `cursor` return type.
