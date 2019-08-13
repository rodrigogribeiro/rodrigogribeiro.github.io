---
title: "Terminating Constraint Set Satisfiability and Simplification Algorithms for Context-Dependent Overloading"
collection: publications
permalink: /publication/2013-02-01-terminating-constraint-set
date: 2013-02-01
venue: 'Journal of the Brazilian Computer Society'
paperurl: 'http://academicpages.github.io/files/decidable-sat.pdf'
---

Algorithms for constraint set satisfiability and simplification of Haskell type class constraints 
are used during type inference in order to allow the inference of more accurate types and to detect 
ambiguity. Unfortunately, both constraint set satisfiability and simplification are in general undecidable, 
and the use of these algorithms may cause non-termination of type inference. This paper presents 
algorithms for these problems that terminate on any given input, based on the use of a criterion that is 
tested on each recursive step.

The use of this criterion eliminates the need of imposing syntactic conditions on Haskell type class and 
instance declarations in order to guarantee termination of type inference in the presence of multi-parameter 
type classes, and allows program compilation without the need of compiler flags for lifting such restrictions. 
Undecidability of the problems implies the existence of instances for which the algorithm incorrectly reports 
unsatisfiability, but we are not aware of any practical example where this occurs.

[Download paper here](http://academicpages.github.io/files/decidable-sat.pdf)
