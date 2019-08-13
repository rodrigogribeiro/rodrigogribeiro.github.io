---
title: 'Intrinsically typed linear logic in Coq'
date: 2019-02-28
permalink: /posts/2019/02/linear-logic-syntax-coq
tags:
  - Coq
  - Linear logic
---

Introduction
=============

In this post, I will present an encoding of linear logic (linear \\(\lambda\\)-calculus)
using an intrinsically typed syntax using Coq proof assistant. Dependent
types are a great way to enforce, statically, invariants on any sort of
data structure, like in our case, a syntax tree.

Before diving into the technical details of the Coq code, I believe that
we should spent some time on linear logic and, specially, on how it is related
to classic / intuitionistic logic.


Prelude: Intuitionistic logic - the logic of true truth
-----------------------------------------------------

Computer scientists had a good understanding of classical logics, since it
pervasive through several areas like artificial intelligence, digital circuit
design and programming language semantics.

The syntax of classical logic propositions is presented below.

\\[ P ::= V \,\mid\, P \land P \,\mid\, P \to P \,\mid\, P \lor P \\]

In introductory courses on discrete mathematics, logics is usually presented
using the Tarsky semantics, in which, each connective is denoted by its
"truth-table". Here, we will represent each boolean function by its
semantics using natural deduction. In natural deduction, we specify the
semantics of formulas using _judgments_. We will follow common practice and
let \\(\Gamma \vdash P\\) denote that formulat \\(P\\) can be deduced from
the sequence of formulas \\(\Gamma\\) using the rules of natural deduction,
which are specified next.

The first rule is identity, which specifies the rather obvious fact that
a formula \\(P\\) is provable from itself.
\\[
   \dfrac{}{P \vdash P}(id)
\\]
The next set of rules are known as structural, since they show how we can
manipulate the sequence of assumptions in a proof.
\\[
\begin{array}{ccc}
\dfrac{\Gamma,\Delta \vdash P}{\Delta,\Gamma \vdash P}(exchange) &
\dfrac{\Gamma, A, A \vdash B}{\Gamma, A \vdash B}(contraction) &
\dfrac{\Gamma \vdash B}{\Gamma,A \vdash B}(weakening)
\end{array}
\\]
The rule exchange specified that provability is closed under assumptions
permutations, contraction allows the duplication of a certain hypothesis and
weakening allows us to discard some formula from the assumptions. Most
presentations of natural deduction didn't mention such structual rules because
they can be avoided if we consider a set of assumptions instead of a sequence.
But, the true reason behind linear logic only become apparent if we use
sequences.

For connectives, we have two kind of rules: introduction and elimination.
Introduction rules allow us to conclude a formula having a certain connective,
while elimination allow us to use a formula with a certain connective. The
first connective we consider is conjunction, whose rules are shown below.
\\[
\begin{array}{cc}
\dfrac{\Gamma \vdash A\,\,\,\,\,\,\,\,\,\,\Delta \vdash B}{\Gamma,\Delta \vdash A \land B}(\land_I) &
\dfrac{\Gamma \vdash A \land B \,\,\,\,\,\,\,\,\,\,\Delta,A,B\vdash C}{\Gamma,\Delta \vdash C}(\land_E)
\end{array}
\\]
The first rule says that if we have a proof of \\(A\\) and another for \\(B\\)
we can build a proof for \\(A\land B\\). The conjunction elimination rule
specifies that if we have a proof of \\(A\land B\\) we can use both \\(A\\)
and \\(B\\) as additional assumptions for proving another formula, \\(C\\).

For disjunction, we have two introduction rules, since we can prove \\(A \lor B\\)
from a proof of \\(A\\)  or from a proof of \\(B\\).

\\[
\begin{array}{cc}
\dfrac{\Gamma\vdash A}{\Gamma\vdash A \lor B}(\lor_{IL}) &
\dfrac{\Gamma\vdash B}{\Gamma\vdash A \lor B}(\lor_{IR})
\end{array}
\\]

The elimination specifies that we can conclude a formula \\(C\\) from
\\(A \lor B\\) if we can prove \\(C\\) from \\(A\\) and from \\(B\\).

\\[
\dfrac{\Gamma\vdash A\lor B \,\,\,\,\,\,\,\,\,\, \Delta,A \vdash C\,\,\,\,\,\,\,\,\,\, \Delta, B \vdash C}
{\Gamma,\Delta\vdash A \lor B}(\lor_{IL})
\\]

The last set of rules is for implication. Implication elimination rule (also
   known as _modus ponens_) reflects our intuitive understanding of deduction.
We can deduce \\(B\\) from proofs of \\(A \to B\\) and \\(A\\). Implication
introduction specifies that we can deduce \\(A\to B\\) from a proof of \\(B\\)
which uses \\(A\\) as an additional assumption.
\\[
\begin{array}{cc}
\dfrac{\Gamma,A \vdash B}{\Gamma \vdash A \to B}(\to_I) &
\dfrac{\Gamma \vdash A \to B \,\,\,\,\,\,\,\,\,\, \Delta\vdash A}{\Gamma,\Delta \vdash B}(\to_E)
\end{array}
\\]

The previous rules for the propositional logic form what is called
_intuitionistic logic_, in which the semantics of formulas is based
on _evidence_,instead of relying on a vacuously notion of truth, like
classical logic and its axiom of excluded middle.
Next, we present linear logic which restrict the usage of structural rules aiming
to control assumptions as resources.

Linear logic: the logic of food
===============================

Traditional logics deal with truth and it (in principle) is forever. If
something is true, according to classical (and intuitionistic logic) it will
remain true forever. As an example of how such view of validity can be problematic,
consider the following sentences:

- If eat a cake then I'll become full.
- I have a cake

Using traditional logics, these can be represented by the following formula,
where proposition \\(A\\) represents "I have a cake" and \\(B\\) denotes
"I'm full":

- \\(A \to B\\)
- \\(B\\)

Note that, using natural deduction, we can prove the following
\\[
\{A\to B, A\}\vdash A \land B
\\]
the formula in the conclusion means that you have a cake and is full. So far,
so good. But, what if you have only one cake? It is not the case that you
are full, after eat it, and still have it: it is cheating!

The main idea of linear logic is that it imposes a strict control on the usage
of hypothesis. In such logic, it is not possible to reuse assumptions as you
wish.
