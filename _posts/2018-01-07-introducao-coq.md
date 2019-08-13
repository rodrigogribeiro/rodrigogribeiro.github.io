---
title: 'Uma introdução ao assistente de provas Coq'
date: 2018-01-07
permalink: /posts/2018/01/intro-coq-parte1
tags:
  - Coq
---

Uma justificativa...
-------------------------

Após um longo período trabalhando com a linguagem Agda, cheguei a conclusão 
que não essa não é adequada para meus projetos de pesquisa, devido aos 
seguintes fatos:

1 - O seu compilador não é capaz de gerar código com qualidade. Os programas 
produzidos são extremamente ineficientes.

2 - A biblioteca padrão da linguagem não possui documentação, o que dificulta
muito a sua utilização.

Por esse motivo, resolvi voltar a utilizar o assistente de provas Coq, que 
permite extrair código para Haskell (que pode ser compilado de maneira eficiente 
pelo GHC) e possui uma biblioteca melhor documentada e uma ampla comunidade.

Justificativa apresentada, nessa série de posts pretendo apresentar o 
assistente de provas Coq e como esse pode ser utilizado para verificar programas. 
Assumo que o leitor possui conhecimentos elementares de lógica e programação funcional.


Sobre essa série de posts
-------------------------------

Esses posts são parte do material utilizado em um curso introdutório sobre 
Coq ministrado por mim na UFPel. O código utilizado durante esse curso (incluindo
os exercícios presentes no texto, sem solução, evidentemente...), estão disponíveis
[aqui](https://rodrigogribeiro.github.io/files/code.zip)


Bibliografia
---------------

Material desenvolvido por Rodrigo Ribeiro a partir das seguintes fontes bibliográficas:

- Bertot, Yves; Casterrán, Pierre - Interactive Theorem Proving
  and Program Development; The Coq'art - The calculus of inductive
      constructions
- Chlipala, Adam - Certified Programming with Dependent Types
- Pierce, Benjamin - Software Foundations.
- Girard, Y. Jean - Proofs and Types
