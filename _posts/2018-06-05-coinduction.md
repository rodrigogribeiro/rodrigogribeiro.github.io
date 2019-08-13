---
title: 'Co-indução e tipos co-indutivos'
date: 2018-06-05
permalink: /posts/2018/06/coinduction
tags:
  - Coq
---

Introdução
======

Em linguagens funcionais *lazy*, como Haskell, estruturas de dados infinitas são
lugar comum. Listas infinitas e outros tipos de dados mais exóticos funcionam 
como abstrações convenientes para comunicação entre diferentes partes de um programa.
Porém, essa expressividade possui um custo: é muito fácil produzir programas que 
entram em loop ao invés de *produzir* uma lista infinita de resultados na qual 
podemos obter prefixos em tempo finito.

Porém, em Coq tal liberdade não é tão simples e imediata como em Haskell. Devido a 
correspondência entre programas e provas, restrições devem ser impostas para 
garantir a consistência de Coq  como uma lógica. 

Coq provê suporte aos chamados tipos co-indutivos, que podem ser entendidos como
uma versão *bem comportada* de tipos de dados da linguagem Haskell. De maneira 
simples, tipos co-indutivos em Coq permitem a construção de valores (e provas) 
infinitas que podem ser forçadas em um tempo finito de maneira similar ao uso
de lazy evaluation em Haskell.

Neste post pretendo apresentar a co-indução utilizando alguns exemplos envolvendo 
listas infinitas e resultados sobre estas. Ao final do post, será mostrado como
listas infinitas pode ser utilizadas para modelar uma máquina de Turing em Coq.

Ao infinito e além
======================

O primeiro (e mais simples) exemplo de tipo co-indutivo é o tipo `stream`, que 
corresponde a listas infinitas:

```coq
CoInductive stream (A : Type) : Type :=
| Cons : A -> stream A -> stream A.
```

A definição é simples. A priori, notamos o uso da palavra chave `CoInductive`, ao 
invés de `Inductive` e que o tipo `stream` não possui o caso base para a lista 
vazia. Porém, resta a pergunta: como podemos criar ou utilizar esse tipo? 

Tipos indutivos podem ser usados por funções recursivas. Por sua vez, tipos 
co-indutivos devem ser construídos por funções co-recursivas. A seguir apresentamos 
um exemplo simples.

```coq
CoFixpoint zeroes : stream nat := Cons 0 zeroes.
```

A função `zeroes` cria uma lista infinita contendo apenas 0's. Outra função útil sobre
o tipo `stream` é a função `approx`, que retorna uma lista (finita) contendo um prefixo
de `n` elementos do `stream` de entrada.

```coq
Fixpoint approx {A : Type}(s : stream A)(n : nat) : list A :=
  match n with
  | O => []
  | S n' =>
    match s with
    | Cons x xs => x :: approx xs n'
    end
  end.
```

Observe que a definição de `approx` é feita por recursão sobre o número `n`. 
A seguir, apresentamos uma função similar a `map` para streams.

```coq
CoFixpoint comap {A B : Type}(f : A -> B)(s : stream A) : stream B :=
  match s with
  | Cons x s' => Cons (f x ) (comap f s')
  end.
```

Usando approx e zeroes, podemos  conjecturar que todo prefixo 
finito de `zeroes` é formado apenas por 0's.  O seguinte teorema ilustra esse fato.

```coq
Lemma approx_zero 
    : forall n xs, xs = approx zeroes n ->
       forallb (fun x => Nat.eqb x 0) xs = true.
Proof.
  induction n ; intros xs Hxs ; simpl in * ; subst ; simpl ; auto.
Qed.
```

Provas Coindutivas
============

Considere as seguintes definições de `streams` formados de 1's e que desejamos 
mostrar que essas são equivalentes.

```coq
CoFixpoint ones : stream nat := Cons 1 ones.

Definition ones' := comap S zeroes.
```

Podemos imaginar que o teorema que afirma que esses streams são iguais é:

```coq
Theorem ones_eq : ones = ones'
```

Porém, como iniciar essa prova? Aparentemente não podemos fazer indução, análise
de caso ou outra técnica de prova já conhecida. Na verdade, da forma em que este 
teorema está expresso, ele não é provável. Isso se deve ao fato de que a igualdade
proposicional (tipo eq, notação "=") só pode ser demonstrada por um número finito 
de passos. Na verdade, para provarmos essa equivalência, vamos precisar de uma 
outra noção de igualdade conhecida como *bissimilaridade*.

Bissimilaridade
-------------------

O tópico de bissimilaridade e de relações de bissimulação é um vasto tópico na 
semântica formal de sistemas concorrentes. Logo, apresentaremos apenas as definições
em Coq justificando-as informalmente, sem o devido cuidado matemático.

```coq
CoInductive stream_eq {A : Type} : stream A -> stream A -> Prop :=
| Stream_eq : forall x xs xs',
    stream_eq xs xs' ->
    stream_eq (Cons x xs) (Cons x xs').
```

O tipo `stream_eq` denota provas de igualdade de streams. Basicamente, podemos
considerar que streams `x <:> xs` e `y <:> ys` são iguais se `x = y` e `xs = ys`. 
Esse fato é expresso pelo construtor `Stream_eq`. Note que, como o tipo `stream_eq` é 
co-indutivo, não temos um caso base. Usando essa noção de igualdade, podemos 
retornar a demonstração de igualdade entre os streams.

```coq
Theorem ones_eq : stream_eq ones ones'.
```

Para demonstrar fatos sobre tipos de dados co-indutivos usualmente iniciamos com 
a tática `cofix`, que começa a estrutura de uma prova por co-indução.

```coq
  cofix CH.
```

executando a tática `cofix CH` obtemos o seguinte estado de prova.

```coq
CH : stream_eq ones ones'
==============================
stream_eq ones ones'
```

Ao observamos as hipóteses, podemos pensar que essa prova é mais simples do que 
parece. Porém ao executarmos

```coq
  assumption.
Qed.
```
obtemos a seguinte mensagem de erro
```coq
Error: 
Recursive definition of ones_eq is ill-formed. 
unguarded recursive call in "ones_eq"
```
A mensagem de erro se refere a chamada *guardness condition*, que especifica que 
chamadas co-recursivas devem ser argumentos imediatos para construtores de 
do tipo co-indutivo construído. Logo, para sermos capazes de usar a hipótese de 
co-indução, devemos expor os construtores de stream de forma que o uso da hipótese
seja válido. Para isso, vamos primeiramente definir uma função e um teorema 
aparentemente inócuos.

```coq
Definition frob {A : Type} (s : stream A) : stream A :=
  match s with
  | Cons x xs => Cons x xs
  end.

Lemma frob_eq {A : Type} : forall (s : stream A), s = frob s.
Proof.
  destruct s ; reflexivity.
Qed.
```
Porém, esse teorema é exatamente o que necessitamos para avançar na demonstração 
desse fato.

```coq
Theorem ones_eq : stream_eq ones ones'.
Proof.
  cofix CHones_eq.
  rewrite (frob_eq ones) ; rewrite (frob_eq ones').
```

Após a reescrita dos dois streams obtemos: 

```coq
CH : stream_eq ones ones'
========================================
stream_eq (frob ones) (frob ones')
```

Com isso, a tática `simpl` é capaz de reduzí-los da seguinte forma: 

```coq
CH : stream_eq ones ones'
========================================
stream_eq (Cons 1 ones) (Cons 1 (comap S zeroes))
```

Note que agora ambos os streams estão como argumentos do construtor `Cons`. Logo,
podemos usar o construtor de `stream_eq`, `Stream_eq`, que nos deixa com a seguinte
prova

```coq
CH : stream_eq ones ones'
=================================
 stream_eq ones (comap S zeroes)
```

que corresponde exatamente a hipótese de co-indução, a menos da expansão de ones'.
O script completo da demonstração segue abaixo.

```coq
Theorem ones_eq : stream_eq ones ones'.
Proof.
  cofix CHones_eq.
  rewrite (frob_eq ones) ; rewrite (frob_eq ones').
  simpl.
  constructor.
  assumption.
Qed.
```

Modelando uma máquina de Turing
======================================

Informalmente, uma máquina de Turing consiste de um conjunto de estados, uma função 
de transição e de um predicado para testar se um dado estado é final ou não. Em nossa
modelagem de máquinas de Turing, procuraremos seguir essa descrição informal. 
Para isso, primeiramente, vamos definir um tipo para `streams` e um tipo para 
representar computações possivelmente infinitas (`Delay`).

```coq
CoInductive stream (A : Type) : Type :=
| Cons : A -> stream A -> stream A.

Infix "<:>" := Cons (at level 60, right associativity).

CoInductive Delay (A : Type) : Type :=
| Now : A -> Delay A
| Later : Delay A -> Delay A.
```

O tipo `Delay` representa computações possivelmente infinitas. Um valor do tipo 
`Delay A` ou é o resultado final da computação (construtor `Now`) ou é uma computação
que ainda não terminou (construtor `Later`). Usaremos o tipo `Delay` para representar
a computação em uma máquina de Turing.

Além disso, usaremos o tipo `nat` para representar o conjunto de estados `Q` e 
os símbolos do alfabeto `S`. O tipo de dados `move` representa a direção em que 
devemos mover o cabeçote da fita.

```coq
  Definition Q := nat. (** espaço de estados *)
  Definition S := nat. (** símbolos de finta *)

  Inductive move : Set := Left : move | Right : move.
```

A função de transição é simplesmente uma função entre pares de estados e símbolos
de fita para triplas de estados, símbolos de fita e direção para mover o cabeçote.

```coq
  Definition d (input : Q * S) : option (Q * S * move) :=
    let (q,s) := input in Some (q + 1, q, Right).
```

Utilizamos como transição uma função simples. Porém, qualquer outra definição pode
ser aplicada. A definição seguinte especifica que o estado 1000 é final.

```coq
  Definition f (q : Q) : bool :=
    match q with
    | 1000 => true
    | _    => false
    end.
```

Para finalizar nossa modelagem, falta a representação da fita. Utilizaremos uma
lista finita para representar os símbolos à esquerda do cabeçote da fita e 
um stream para representar o símbolo atual (cabeça do stream) e o restante da fita.
A seguinte função realiza uma transição de configuração na máquina de Turing.

```coq
  Definition tm (tape_left : list S)
                (tape_right : stream S)
                (q : Q)
    : option (Q * list S * stream S) :=
    match tape_right with
    | s <:> ss =>
      match d (q,s) with
      | None => Some (q , tape_left , tape_right)
      | Some (q', s', dir) =>
        match dir with
        | Left =>
          match tape_left with
          | [] => None
          | x :: xs => Some (q', xs, x <:> s' <:> ss)
          end 
        | Right => Some (q', s' :: tape_left , ss)
        end
      end
    end.
```
Utilizamos o tipo `option` para representar a possibilidade de uma certa transição 
ser indefinida (construtor `None`). 

Inicialmente, consideraremos que a fita é iniciada com um número infinito de 
0's.

```coq
  CoFixpoint zeroes := 0 <:> zeroes.
```
A última peça do quebra-cabeça é a função `compute` que iterativamente constrói 
um valor `Delay` a partir das transições realizadas pela função `tm`.

```coq
  CoFixpoint compute
             (tape_left : list S)
             (tape_right : stream S)
             (q : Q) : Delay Q :=
    if f q then Now q
    else match tm tape_left tape_right q with
         | Some (q', left', right') =>
           Later (compute left' right' q')
         | None => Now q 
         end.
```

Conclusão
============

Nesse post apresentamos como tipos co-indutivos podem ser utilizados em Coq para 
modelagem de estruturas de dados infinitas. Utilizamos tais tipos para provar 
uma simples bissimulação entre streams equivalentes e também para modelar uma 
máquina de Turing usando um tipo para representar computações possivelmente 
infinitas (tipo `Delay`).

Como exercício, recomendamos ao leitor a modelagem de um intepretador para 
uma linguagem imperativa com comandos de repetição, o que pode ser feito de maneira
simples utilizando o tipo de dados `Delay`.

Todo o código desse post está disponível nos seguintes endereços: 
[coindução](https://gist.github.com/rodrigogribeiro/f7ca97492a62d31a0b723f21ef2b8f53) e
[máquinas de Turing](https://gist.github.com/rodrigogribeiro/02bd3a0283104e166f8078e69d60526a). 
