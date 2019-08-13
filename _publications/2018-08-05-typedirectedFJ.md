---
title: "A Type-Directed Algorithm to Generate Well-Typed Featherweight Java Programs"
collection: publications
permalink: /publication/2018-08-05-typedirectedFJ
date: 2018-08-03
venue: 'SBMF - Brazilian Syposium on Formal Methods'
paperurl: 'http://rodrigogribeiro.github.io/files/typedirectedFJ.pdf'
---

Property-based testing of compilers or programming languages semantics is difficult to accomplish 
because it is hard to design a random generator for valid programs. Most compiler test tools do not 
have a well-specified way of generating type-correct programs, which is a requirement for such 
testing activities. In this work, we formalize a type-directed procedure to generate random
well-typed programs in the context of Featherweight Java, a well-known object-oriented calculus 
for the Java programming language. We implement the approach using the Haskell programming language 
and verify it against relevant properties using QuickCheck, a library for property-based testing.

[Download paper here](http://rodrigogribeiro.github.io/files/typedirectedFJ.pdf)
