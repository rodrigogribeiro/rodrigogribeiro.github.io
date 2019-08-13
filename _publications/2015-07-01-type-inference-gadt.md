---
title: "Type inference for GADTs and anti-unification"
collection: publications
permalink: /publication/2015-07-01-type-inference-gadt
date: 2015-07-01
venue: 'Programming Languages - 19th Brazilian Symposium on Programming Languages.'
paperurl: 'http://rodrigogribeiro.github.io/files/gadt.pdf'
---
Nowadays the support of generalized algebraic data types (GADTs) in extensions of Haskell 
allows functions defined over GADTs to be written without the need for type annotations in 
some cases and requires type annotations in other cases. In this paper we present a type 
inference algorithm for GADTs that is based on a closed-world approach to overloading and 
uses anti-unification and constraint-set satisfiability to infer the relationship between 
the types of function arguments and result. Through some examples, we show how the proposed 
algorithm allows more functions defined over GADTs to be written without the need for type annotations.

[Download paper here](http://rodrigogribeiro.github.io/files/gadt.pdf)
