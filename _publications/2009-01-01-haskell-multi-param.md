---
title: "A Solution to Haskell's Multi-Parameter Type Class Dilemma"
collection: publications
permalink: /publication/2009-01-01-haskell-multi-param
date: 2009-01-01
venue: 'XIII Simpósio Brasileiro de Linguagens de Programação'
paperurl: 'http://rodrigogribeiro.github.io/files/multiparam.pdf'
---

The introduction of multi-parameter type classes in Haskell has been hindered because of problems associated to ambiguity, which occur due to the lack of type specialization during type inference. This paper proposes a
minimalist, simple solution to this problem, which requires only a small change to the type inference algorithm and to what has been considered ambiguity in Haskell. It does not depend on the use of programmer specified functional dependencies between type class parameters nor any other extra mechanism, such as associated types. A type system and a type inference algorithm, sound and complete with respect to the type system, are presented.


[Download paper here](http://rodrigogribeiro.github.io/files/multiparam.pdf)
