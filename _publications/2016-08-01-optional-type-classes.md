---
title: "Optional type classes for Haskell"
collection: publications
permalink: /publication/2016-08-01-optional-type-classes
date: 2016-08-01
venue: 'Programming Languages - 20th Brazilian Symposium on Programming Languages.'
paperurl: 'http://rodrigogribeiro.github.io/files/optional.pdf'
---
This paper explores an approach for allowing type classes to be optionally declared by programmers, 
i.e. programmers can overload symbols without declaring their types in type classes.
The type of an overloaded symbol is, if not explicitly defined in a type class, automatically 
determined from the anti-unification of instance types defined for the symbol in the relevant module.
This depends on a modularization of instance visibility, as well as on a redefinition of Haskell’s 
ambiguity rule. The paper presents the modifications to Haskell’s module system that are necessary 
for allowing instances to have a modular scope, based on previous work by the authors. The definition 
of the type of overloaded symbols as the anti-unification of available instance types and the redefined 
ambiguity rule are also based on previous works by the authors.
The added flexibility to Haskell-style of overloading is illustrated by defining a type system and by showing 
how overloaded record fields can be easily allowed with such a type system.

[Download paper here](http://rodrigogribeiro.github.io/files/optional.pdf)
