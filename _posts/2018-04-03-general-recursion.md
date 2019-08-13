---
title: 'Recursão não estrutural em Coq'
date: 2018-04-03
permalink: /posts/2018/04/general-recursion
tags:
  - Coq
---

Introdução
============

Um problema comum a pessoas que começam a utilizar um assistente de provas, 
como Coq, é como definir funções que não usam recursão estrutural. Linguagens
que suportam tipos dependentes usam verificadores de totalidade para exigir
que todas as computações terminam e são bem definidas, garantindo assim a 
consistência lógica do sistema.

Motivação
-----------

Mas, porquê tal restrição é importante? Fica fácil entender o motivo ao 
considerarmos que Coq (ou outro assistente de provas) aceitasse a seguinte
definição:

```coq
Fixpoint loop (x : nat) : False := loop x.
```

Com isso, a expressão `loop 0` possui o tipo `False` e, portanto, pode ser 
utilizada para deduzir qualquer teorema usando a tática `contradiction`.

Nesse post vou apresentar algumas técnicas para permitir a definição de funções
que utilizam recursão não estrutural em Coq. Para isso, utilizarei a seguinte 
definição:

```coq
Fixpoint merge (xs ys : list nat) : list nat :=
  match xs, ys with
  | nil , ys => ys
  | xs , nil => xs
  | (x :: xs) , (y :: ys) =>
    match le_gt_dec x y with 
    | left _ _ =>  x :: (merge xs (y :: ys))
    | right _ _ => y :: (merge (x :: xs) ys)
    end
  end.
```

que faz a intercalação de duas listas de números naturais. Tal função 
é utilizada como componente do algoritmo mergesort. Apesar desta função terminar
de maneira óbvia, Coq apresenta a seguinte mensagem de erro:

```
Error: Cannot guess decreasing argument of fix.
```

que é exibida sempre que uma função não é aceita pelo verificador de terminação.


Uso de "combustível"
=========================

Uma técnica simples para definir funções recursivas é utilizar um parâmetro numérico
que limita o número máximo de chamadas recursivas realizadas pelo algoritmo. Essa
técnica é conhecida como ``fuel-based recursion'', uma vez que a função termina 
sua execução quando o combustível acaba ou quando o cálculo realizado pela função
é finalizado.

A seguir apresentamos a definição de `merge`, utilizando essa técnica.

```coq
Fixpoint merge_fuel (xs ys : list nat)(fuel : nat) : option (list nat) :=
  match fuel with
  | O => None
  | S fuel' =>
    match xs, ys with
    | nil , ys => Some ys
    | xs , nil => Some xs
    | (x :: xs) , (y :: ys) =>
      match le_gt_dec x y with 
      | left _ _ =>
        match merge_fuel xs (y :: ys) fuel' with
        | Some r => Some (x :: r)
        | None   => None
        end
      | right _ _ =>
        match merge_fuel (x :: xs) ys fuel' with
        | Some r => Some (y :: r)
        | None   => None
        end
      end
    end
  end.
```

Note que o resultado de `merge_fuel` usa o tipo `option`, retornando o valor `None`,
sempre que a função extrapola o número máximo de chamadas recursivas especificadas
pelo parâmetro `fuel`.

Apesar de simples definição, essa técnica possui alguns inconvenientes: 1) Nem sempre 
é fácil determinar o quanto de "combustível" é necessário para se calcular o 
resultado completo de uma função. Para o exemplo de `merge`, basta fornermos como
entrada o valor `length xs + length ys`, visto que essa função executa um número de 
passos proporcional ao tamanho das duas listas. 2) Outro inconveniente é que o 
parâmetro `fuel` é preservado durante a _extração_ de código para Haskell e OCaml.
Tal parâmetro não possui nenhum valor computacional e não deveria estar presente 
no código dessa função.

O ideal seria o uso de uma técnica que permita que o código extraído seja o mais
próximo possível do que desenvolveríamos em linguagens como Haskell ou OCaml. A 
próxima técnica atende parcialmente esse requisito.

Uso de relações bem formadas.
============================

Seja R uma relação binária sobre um conjunto A. Dizemos que R é uma relação bem 
formada se todo subconjunto X de A possui um elemento minimal com respeito a R.

Outra maneira de caracterizar a boa formação de uma relação é em termos de 
uma noção chamada acessibilidade. Dizemos que um elemento x é acessível com 
respeito a uma relação R se: 1) x é minimal com respeito a R; ou 2) todo elemento y 
menor que x com respeito a R, R y x, é acessível. A acessibilidade é facilmente
definida em Coq da seguinte maneira:

```coq
Inductive Acc (A:Type) (R:A->A->Prop) (x:A) : Prop :=
  Acc_intro :
      (forall y : A, R y x -> Acc R y) -> Acc R x.
```

Finalmente, dizemos que uma relação R é bem formada se todos os elementos de um
conjunto A são acessíveis com respeito a R.

```coq
Definition well_founded (A:Type) (R:A->A->Prop) :=
    forall a, Acc R a.
```

Com isso, podemos provar que a relação < (`lt`), sobre os números naturais, é bem 
formada. Os teoremas seguintes provam esse resultado.

```coq
Theorem lt_Acc : forall n : nat, Acc lt n.
Proof.
  induction n.
  split ; intros p H ; inversion H.
  split.
  intros y H0.
  case (le_lt_or_eq _ _ H0) ; intros.
  +
    eapply Acc_inv ; eauto ; try omega.
  +
    injection H ; intros ; subst ; eauto.
Qed.

Theorem ltnat_wf : well_founded lt.
Proof.
  exact lt_Acc.
Qed.
```

Porém, construir relações bem formadas não é uma tarefa simples. A biblioteca 
padrão de Coq possui diversos combinadores para criar novas relações a partir
de relações existentes. Sabe-se que relações bem formadas são fechadas sobre
fechamento transitivo, imagem inversa entre outras operações.

Recursão sobre relações bem formadas
-------------------

O uso da relação de acessibilidade fornece uma maneira prática de garantir
que uma definição recursiva sempre termina. De forma simples, a idéia é 
implementar a função por recursão sobre uma prova de acessibilidade. Porém,
como já visto em posts anteriores, o casamento de padrão envolvendo tipos 
dependentes exige diversas anotações tornando-o verboso e, em muitas situações,
complexo. Dessa forma, a biblioteca de Coq, fornece diversas funções que 
encapsulam o processo de recursão sobre uma prova de acessibilidade entre
valores de um tipo que possui uma relação bem formada. Uma delas é a função 
`well-founded-induction`, cujo tipo é apresentado abaixo:
```coq
well_founded_induction
     : forall (A : Type) 
              (R : A -> A -> Prop),
              well_founded R ->
              forall (P : A -> Set),
              (forall x : A, 
                 (forall y : A, R y x -> P y) -> P x) -> 
    forall a : A, P a
```
Apesar de parecer complicada, o tipo dessa função é bem simples de ser entendido:

1. O primeiro argumento é `A : Set`, que representa o tipo dos valores de 
entrada para a função.

2. O segundo argumento, `R : A -> A -> Prop`, é uma relação binária sobre `A`.

3. O terceiro argumento é uma prova de que `R` é uma relação bem formada.

4. O quarto argumento é uma função, `P : A -> Set`, utilizado para descrever
o tipo do resultado. Isso permite usarmos `well-founded-induction` para 
definir funções cujo resultado é um tipo dependente.

5. O quinto argumento é uma função que recebe dois argumentos:

   a) O primeiro é um argumento `x : A` que denota o valor de entrada
      para a função que estamos definindo.
      
   
   b) O segundo é uma função de dois parâmetros: o primeiro é um valor
      `y : A` que deve ser um predecessor de `x` em `R`, isto é
      deve ser possível provar `R y x`. O valor de retorno dessa função 
      possui tipo `P y`. Essa função é utilizada para representar as 
      chamadas recursivas da função que estamos definindo. Note que a 
      prova `R y x` especifica que só podemos fazer chamadas recursivas
      sobre elementos `y` "menores" que `x` em `R`. Uma vez que `R` é
      bem formada, não existem cadeias decrescentes infinitas e isso é 
      suficiente para garantir a terminação da função que estamos 
      definindo.
      
A maior dificuldade é o que deve ser fornecido como o 5o argumento de 
`well-founded-induction`. De maneira simples, deve ser uma função que 
permite chamadas recursivas somente a termos que são menores que o parâmetro 
de entrada de acordo com a relação R utilizada. No caso da função `merge`,
utilizaremos funcionalidades da biblioteca de Coq para construir a relação e sua 
prova de boa formação.

Primeiramente, definimos o seguinte tipo para representar entradas para a função `merge`

```coq
  Definition merge_input := sigT (fun _ : list nat => list nat).
```

O tipo `sigT` é a representação do produto dependente em Coq. Logo, podemos entender o tipo 
`merge_input` como um par de listas de números naturais. Utilizamos o tipo `sigT` ao invés de 
pares porquê o tipo de `well-founded-induction` retorna uma função de tipo dependente. As definições
seguintes são usadas para construir valores e obter componentes do tipo `merge_input`.


```coq
Definition mk_input (xs ys : list nat) : merge_input := existT _ xs ys.

Definition list1 (inp : merge_input) : list nat :=
  let (xs,_) := inp in xs.

Definition list2 (inp : merge_input) : list nat :=
  let (_,ys) := inp in ys.
```

Definimos a relação de ordem entre entradas para o algoritmo `merge` da seguinte maneira: Sejam xs,ys, xs' e ys' 
listas quaisquer. Dizemos que (xs,ys) < (xs',ys') se (xs < xs') \/ ((xs = xs') /\ ys < ys'). Porém, isso corresponde
exatamente a noção de ordem lexicográfica entre pares de valores. É fácil demonstrar que dadas duas relações 
bem formadas a ordem lexicográfica de pares de valores dessas relações é também uma relação bem formada. 
A demonstração desse fato está presente na biblioteca padrão de Coq. Para utilizarmos essa demonstração 
precisamos primeiro construir a ordem lexicográfica usando a função `lexprod`, que recebe como parâmetros os 
tipos de cada componente do par e a relação de ordem de cada um destes tipos.

```coq
Definition merge_input_lt : merge_input -> merge_input -> Prop
  := lexprod (list nat)
             (fun _ => list nat)
             (fun (xs xs' : list nat) => length xs < length xs')
             (fun _ (ys ys' : list nat) => length ys < length ys').
```

De posse da ordem lexicográfica, podemos construir sua prova de boa formação usando a função `wf_lexprod`, que recebe como
parâmetros o tipo de cada componente, suas respectivas ordenadações e provas de boa formação produzindo, como resultado, 
a prova de que a ordem lexicográfica é também bem formada.

```coq
Definition merge_input_lt_wf : well_founded merge_input_lt
  := @wf_lexprod (list nat)
                 (fun _ => list nat)
                 (fun (xs xs' : list nat) => length xs < length xs')
                 (fun _ (ys ys' : list nat) => length ys < length ys')
                 (well_founded_ltof (list nat) (@length nat))
                 (fun _ => well_founded_ltof (list nat) (@length nat)).
```

A seguir, definimos dois lemmas que mostram que os valores passados para as chamadas recursivas de `merge` são menores
de acordo com a ordem definida. 


```coq
Lemma mergeF_obligation1
  : forall x y xs ys, merge_input_lt (mk_input xs (y :: ys))
                                (existT _ (x :: xs) (y :: ys)).
Proof.
  intros ; apply left_lex ; simpl ; try omega.
Qed.

Lemma mergeF_obligation2
  : forall x y xs ys, merge_input_lt (mk_input (x :: xs) ys)
                                (existT _ (x :: xs) (y :: ys)).
Proof.
  intros ; apply right_lex ; simpl ; try omega.
Qed.
```

Agora, definimos o corpo da função `merge`, que recebe como parâmetro, uma função que permite a recursão sobre valores 
que são menores de acordo com a ordem definida. 

```coq
Definition mergeF
  : forall inp : merge_input,
    (forall inp' : merge_input, merge_input_lt inp' inp -> list nat) -> list nat.
  refine (fun inp canRec =>
            match inp as inp' return inp = inp' -> list nat with
            | existT _ nil ys => fun _ => ys
            | existT _ xs nil => fun _ => xs
            | existT _ (x :: xs) (y :: ys) => fun _ => 
              if le_gt_dec x y then x :: canRec (mk_input xs (y :: ys)) _
                  else y :: canRec (mk_input (x :: xs) ys) _
            end (eq_refl inp)) ; subst ; auto.
Defined.
```

Finalmente, podemos definir a função `merge` utilizando `well-founded-induction` da seguinte maneira:

```coq
Definition merge_wf (xs ys : list nat) : list nat :=
  well_founded_induction merge_input_lt_wf (fun _ => list nat) mergeF (mk_input xs ys).
```

O uso de relações bem formadas permite definir funções com padrões de recursão quaisquer, desde que seja possível
demonstrar que em todas as chamadas recursivas, o valor utilizado nessas chamadas é menor que o passado como 
entrada para a função em questão.

Recursão sobre um predicado de domínio
-------------

Na seção anterior descrevemos como utilizar recursão sobre provas de boa formação de uma relação para definir 
funções recursivas. Outra possibilidade é utilizar um predicado que descreva quais valores 
pertencem ao domínio da função a ser definida. Dessa forma, realizamos a recursão sobre a estrutura desse predicado.
Usualmente, o predicado de domínio de uma função descreve o formato dos parâmetros para os casos base e chamadas
recursivas de maneira a caracterizar o grafo de chamadas da função definida.

O predicado `merge_acc` define o domínio da função `merge`. Note que cada constructor do predicado, caracteriza uma 
das equações da definição da função.

```coq
Inductive merge_acc : list nat -> list nat -> Prop :=
| Merge1 : forall xs, merge_acc xs nil
| Merge2 : forall ys, merge_acc nil ys 
| Merge3 : forall x y xs ys,
    x <= y -> merge_acc xs (y :: ys) -> merge_acc (x :: xs) (y :: ys)
| Merge4 : forall x y xs ys,
    x > y -> merge_acc (x :: xs) ys -> merge_acc (x :: xs) (y :: ys).
```

De posse desse predicado, definimos dois lemmas que serão utilizados para permitir as chamadas recursivas a `merge` 
utilizando sub-termos desse predicado.

```coq
Ltac inv H := inversion H ; subst ; clear H.

Lemma merge_acc_inv3
     : forall xs ys x y xxs yys,
        xxs = x :: xs -> yys = y :: ys ->
        merge_acc xxs yys ->
        x <= y ->
        merge_acc xs yys.
 Proof.
    intros xs ys x y xxs yys eqx eqy H Hle;
    subst; inv H ; eauto ; try omega.
 Defined.

 Lemma merge_acc_inv4
    : forall xs ys x y xxs yys,
      xxs = x :: xs -> yys = y :: ys ->
      merge_acc xxs yys ->
      x > y ->
     merge_acc xxs ys.
 Proof.
   intros xs ys x y xxs yys eqx eqy H Hxy ;
   subst ; inv H ; eauto ; try omega.
 Defined.
```

Usando esses lemas, podemos definir a função por recursão sob provas de `merge_acc` como se segue:

```coq
Fixpoint merge_bc1
     (xs ys : list nat)(H : merge_acc xs ys) {struct H}: list nat :=
   (match xs as us, ys as vs return xs = us -> ys = vs -> list nat with
     | nil, ys => fun _ _ => ys
     | xs , nil => fun _ _ => xs
     | (x :: xs) , (y :: ys) =>
        match le_gt_dec x y with
        | left _ h1 => fun eqx eqy =>
            let H' := merge_acc_inv3 _ _ x y _ _ eqx eqy H h1
            in x :: merge_bc1 _ _ H'
        | right _ h2 => fun eqx eqy =>
            let H' := merge_acc_inv4 _ _ x y _ _ eqx eqy H h2
            in y :: merge_bc1 _ _ H'
        end 
     end) eq_refl eq_refl.
```

Note que a definição anterior precisa de uma prova de que o predicado é verdadeiro para as listas 
fornecidas como parâmetro. Para criação dessa demonstração, devemos provar que o predicado `merge_acc` é 
demonstrável para quaisquer listas `xs` e `ys`. A prova é como se segue.

```coq
Definition merge_acc_intro : forall xs ys, merge_acc xs ys.
  induction xs as [| x xs IHxs]; destruct ys as [| y ys] ;
    try solve [econstructor ; eauto].
  +
    destruct (le_gt_dec x y) ; eauto.
    induction ys as [| y' ys' IHys'].
    *
      apply Merge4 ; eauto.
    *
      apply Merge4.
      assumption.
      inv IHys'. try omega.
      destruct (le_gt_dec x y') ; try omega ; auto.
Defined.
```

De posse da prova de que o predicado é verdadeiro para quaisquer listas xs e ys e da função `merge_bc1`, podemos
criar a função de intercalação de maneira direta.

```coq
Definition merge_bc (xs ys : list nat) : list nat.
  apply (merge_bc1 xs ys).
  apply merge_acc_intro.
Defined.
```

Conclusão
===========

Nesse post apresentamos três técnicas para definição de funções que não utilizam recursão estrutural em Coq. 
Utilizamos um exemplo clássico --- a rotina de intercalação de listas do algoritmo *merge sort* --- para 
apresentar de maneira suscinta cada uma das técnicas. Explicações mais detalhadas sobre cada uma destas
técnicas podem ser encontradas nos livros Certified Programming with Dependent Types e Interactive Theorem Proving and 
Program Developement.

O código completo deste post está disponível no seguinte [gist](https://gist.github.com/rodrigogribeiro/5bcfc0e96f645d9c007fd19b96980534).
