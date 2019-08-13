---
title: "Ambiguity and context-dependent overloading"
collection: publications
permalink: /publication/2013-03-01-ambiguity-context
date: 2013-03-01
venue: 'Journal of the Brazilian Computer Society'
paperurl: 'http://academicpages.github.io/files/ambiguity-context.pdf'
---
This paper discusses ambiguity in the context of languages that support context-dependent 
overloading, such as Haskell. A type system for a Haskell-like programming language, that 
supports context-dependent overloading and follow the Hindley-Milner approach of providing 
context-free type instantiation, allows distinct derivations of the same type for ambiguous 
expressions. Such expressions are usually rejected by the type inference algorithm, which is 
thus not complete with respect to the type system.
Following the standard definition of ambiguity, satisfiability is tested - i.e. “the world is closed” — if only
if overloading is (or should have been) resolved, that is, if and only if there exist unreachable variables 
in the constraints on types of expressions. Nowadays satisfiability is tested in Haskell, in the presence of 
multi-parameter type classes, only upon the presence of functional dependencies or an alternative mechanism 
that specifies conditions for closing the world, and that may happen when there exist or not unreachable type 
variables in constraints. The satisfiability trigger condition is then given automatically, by the existence 
of unreachable variables in constraints, and does not need to be specified by programmers, using an extra 
mechanism.

[Download paper here](http://rodrigogribeiro.github.io/files/ambiguity-context.pdf)
