(* Rel *)

(* Propriedades das Relações *)

(* Este capítulo curto (e opcional) desenvolve algumas definições básicas e alguns teoremas 
sobre relações binárias no Rocq. As definições principais são repetidas onde elas são de 
fato usadas (no capítulo Smallstep de Programming Language Foundations), então leitores que 
já estão confortáveis com essas ideias podem ler por cima ou pular este capítulo com 
segurança. No entanto, as relações também são uma boa fonte de exercícios para desenvolver 
familiaridade com os recursos básicos de raciocínio do Rocq, podendo ser útil olhar para 
este material logo após o capítulo IndProp. *)

Set Warnings "-notation-overridden".
Require Import LFPTBR.j_IndPrinciples.a_IndPrinciples.

(**************************************** Relações *****************************************)

(* Uma relação binária em um conjunto X é uma família de proposições parametrizada por dois 
elementos de X — ou seja, uma proposição sobre pares de elementos de X. *)

Definition relation (X: Type) := X -> X -> Prop.

(* De forma um tanto confusa, a biblioteca padrão do Rocq ''sequestra'' o termo genérico 
''relação'' para essa instância específica da ideia. Para manter a consistência com a 
biblioteca, faremos o mesmo. Assim, doravante, o identificador relation no Rocq sempre se 
referirá a uma relação binária em algum conjunto (entre o conjunto e ele mesmo), ao passo 
que no inglês matemático comum a palavra ''relation'' pode se referir tanto a esse conceito 
específico quanto ao conceito mais geral de uma relação entre um número qualquer de 
conjuntos possivelmente diferentes. O contexto da discussão deve sempre deixar claro qual 
dos sentidos está em questão.

Um exemplo de relação em nat é le, a relação de menor ou igual, que geralmente escrevemos 
n1 ≤ n2.*)

Print le.
(* ====> Inductive le (n : nat) : nat -> Prop :=
             le_n : n <= n
           | le_S : forall m : nat, n <= m -> n <= S m *)
Check le : nat -> nat -> Prop.
Check le : relation nat.

(* (Por que escrevemos dessa forma em vez de começar com Inductive le : relation nat...? 
Porque queríamos colocar o primeiro nat à esquerda do :, o que faz o Rocq gerar um princípio 
de indução um tanto mais agradável para raciocinar sobre ≤.) *)

(********************************** Propriedades Básicas ***********************************)

(* Como sabe qualquer pessoa que tenha cursado uma disciplina de matemática discreta na 
graduação, há muito a ser dito sobre relações em geral, incluindo formas de classificar 
relações (como reflexivas, transitivas, etc.), teoremas que podem ser provados de forma 
genérica sobre certos tipos de relações, construções que geram uma relação a partir de outra, 
etc. Por exemplo... *)

(*** Funções Parciais ***)

(* Uma relação R em um conjunto X é uma função parcial se, para todo x, houver no máximo um y 
tal que R x y — isto é, R x y_1 e R x y_2 juntos implicam y_1 = y_2. *)

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

(* Por exemplo, a relação next_nat é uma função parcial. *)

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Check next_nat : relation nat.

Theorem next_nat_partial_function :
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H2.
  reflexivity. Qed.

(* No entanto, a relação ≤ sobre os números não é uma função parcial. (Assuma, por absurdo, que 
≤ seja uma função parcial. Porém, visto que 0 ≤ 0 e 0 ≤ 1, segue-se que 0 = 1. Isso é um 
absurdo, logo nossa suposição era contraditória.) *)

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense. {
    apply Hc with (x := 0).
    - apply le_n.
    - apply le_S. apply le_n. }
  discriminate Nonsense. Qed.

(* Exercício *)

(* Mostre que a total_relation (relacao_total) definida em (um exercício de) IndProp não é 
uma função parcial.

Copie a definição de total_relation (relacao_total) do seu arquivo IndProp para cá, de modo 
que este arquivo possa ser avaliado de forma independente. *)

Inductive total_relation : nat -> nat -> Prop :=
  | tot_rel (n m : nat) : total_relation n m.

Theorem total_relation_not_partial_function :
  ~ (partial_function total_relation).
Proof.
    unfold not.
    unfold partial_function.
    intros H.
    assert (Hcontra : 0 = 1). {
      apply H with (x := 0) (y1 := 0) (y2 := 1).
      - apply tot_rel.
      - apply tot_rel. }
    discriminate Hcontra.
Qed.

(* Mostre que a empty_relation (relacao_vazia) definida em (um exercício de) IndProp é uma 
função parcial.

Copie a definição de empty_relation (relacao_vazia) do seu arquivo IndProp para cá, de modo
que este arquivo possa ser avaliado de forma independente. *)

Inductive empty_relation : nat -> nat -> Prop := .

Theorem empty_relation_partial_function :
  partial_function empty_relation.
Proof.
    unfold partial_function.
    intros x y1 y2 Hxy1 Hxy2.
    inversion Hxy1.
Qed.

(*** Relações Reflexivas ***)

(* Uma relação reflexiva sobre um conjunto X é aquela em que todo elemento de X está 
relacionado consigo mesmo. *)

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n. Qed.

(*** Relações Transitivas ***)

(* Uma relação R é transitiva se R a c for válido sempre que R a b e R b c o forem. *)

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  - (* le_n *) apply Hnm.
  - (* le_S *) apply le_S. apply IHHmo. Qed.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo. Qed.

(* Exercício *)
(* Também podemos provar lt_trans de forma mais trabalhosa por indução, sem usar le_trans. 
Faça isso.*)

Theorem lt_trans' :
  transitive lt.
Proof.
    (* Prove isto por indução sobre a evidência de que m é menor que o. *)
    unfold lt. unfold transitive.
    intros n m o Hnm Hmo.
    induction Hmo as [| m' Hm'o].
    - apply le_S in Hnm. apply Hnm.
    - apply le_S in IHHm'o. apply IHHm'o.
Qed.

(* Prove a mesma coisa novamente por indução sobre o. *)

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  - apply le_S in Hnm.
    inversion Hmo.
  - inversion Hmo as [ | o'' Hle ].
    + apply le_S. rewrite <- H. apply Hnm.
    + apply le_S. apply IHo'. apply Hle. 
Qed.

(* A transitividade de le, por sua vez, pode ser usada para provar alguns fatos que serão 
úteis mais tarde (por exemplo, para a prova de antimetria abaixo)... *)

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
  - apply le_S. apply le_n.
  - apply H.
Qed.

Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
    intros n m HS.
    inversion HS as [ | m' Hle ].
    - apply le_n.
    - apply le_Sn_le. apply Hle.
Qed.

(* Forneça uma prova informal do seguinte teorema:

Teorema: Para todo n, ¬ (S n ≤ n)

Uma prova formal disso é um exercício opcional abaixo, mas tente escrever uma prova 
informal sem fazer a prova formal primeiro.

Prova: 
Queremos mostrar que é impossível que o sucessor de um número (S n) seja menor ou igual ao 
próprio número (n). Faremos isso por indução sobre n:

    Caso Base (n = 0):
        - Queremos provar que ¬ (S 0 ≤ 0), ou seja, que 1 ≤ 0 é falso.
        - Por definição da relação ''menor ou igual'' ( ≤ ) nos números naturais, 0 é o 
          menor elemento possível; nenhum número natural é menor do que 0. Portanto, 1 ≤ 0 é 
          impossível. O caso base é válido.
          
    Passo Indutivo:
        - Hipótese de Indução (H.I.): Assumimos que a propriedade é verdadeira para um número 
          arbitrário n, ou seja, que ¬ (S n ≤ n) é verdade (o que significa que supomos por 
          absurdo que S n ≤ n é falso).
        - Tese: Queremos mostrar que a propriedade vale para o sucessor de n, isto é, 
          ¬ (S (S n) ≤ S n).
        - Demonstração por Contradição:
            - Suponha, por absurdo, que S (S n) ≤ S n seja verdadeiro.
            - Pelas regras da relação ≤ nos naturais, se o sucessor de um número é menor ou 
              igual ao sucessor de outro (S a ≤ S b), então o número original deve ser menor 
              ou igual ao outro (a ≤ b).
            - Aplicando isso à nossa suposição, se S (S n) ≤ S n, então necessariamente 
              devemos ter S n ≤ n.
            - No entanto, a nossa Hipótese de Indução diz exatamente o oposto: que 
              S n ≤ n é falso (¬ (S n ≤ n)).
            - Chegamos a uma contradição insustentável. Logo, a nossa suposição inicial de 
              que S (S n) ≤ S n deve ser falsa.
    
Como o caso base e o passo indutivo foram demonstrados, conclui-se que ¬ (S n ≤ n) é 
verdadeiro para todo n. ☐ *)

Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
    intros n. unfold not.
    intros H. induction n as [ | n' IHn].
    - inversion H.
    - apply IHn. apply le_S_n in H. apply H.
Qed.

(* Reflexividade e transitividade são os principais conceitos de que precisaremos para os 
capítulos posteriores, mas, para praticar um pouco mais o trabalho com relações no Rocq, 
vamos analisar algumas outras bem comuns... *)

(*** Relações Simétricas e Antissimétricas ***)

(* Uma relação R é simétrica se R a b implica R b a. *)

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

(* Exercício *)
Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
    unfold not.
    unfold symmetric. intros H.
    assert (Hcontra :  le 1  0). {
        apply H with (a := 0) (b := 1).
        apply le_S. apply le_n.  }
    inversion Hcontra.
Qed.

(* Uma relação R é antissimétrica se R a b e R b a juntos implicam a = b -- ou seja, se os 
únicos ''ciclos'' em R forem os triviais. *)

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

(* Exercício *)

Theorem le_antisymmetric :
  antisymmetric le.
Proof.
    unfold antisymmetric.
    intros a b Hab.
    induction Hab as [ | b' Hab' IH].
    - intros Haa. reflexivity.
    - intros Hb'a. 
      assert (H : S b' <= b'). {
        apply (le_trans (S b') a b').
        apply Hb'a.
        apply Hab'.
      }
      apply le_Sn_n in H.
      inversion H.
Qed.

Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
  intros n m p Hnm.
  induction Hnm as [ | m' Hnm' IH].
  - intros Hsnsp.
    apply le_S_n in Hsnsp.
    apply Hsnsp.
  - intros Hsm'sp.
    apply IH.
    apply le_S_n in Hsm'sp.
    apply le_S.
    apply Hsm'sp.
Qed.

(*** Relações de Equivalência ***)

(* Uma relação é de equivalência se for reflexiva, simétrica e transitiva. *)

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

(*** Ordens Parciais e Pré-ordens ***)

(* Uma relação é uma ordem parcial quando é reflexiva, antissimétrica e transitiva. Na 
biblioteca padrão do Rocq, ela é chamada simplesmente de ''ordem''. *)

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

(* Uma pré-ordem é quase como uma ordem parcial, mas não precisa ser antissimétrica. *)

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  unfold order. split.
    - (* refl *) apply le_reflexive.
    - split.
      + (* antisym *) apply le_antisymmetric.
      + (* transitive. *) apply le_trans. Qed.

(******************************* Fecho Reflexivo e Transitivo ******************************)

(* O fecho reflexivo e transitivo de uma relação R é a menor relação que contém R e que é 
tanto reflexiva quanto transitiva. Formalmente, ele é definido desta forma no módulo 
Relations da biblioteca padrão do Rocq: *)

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
  | rt_step x y (H : R x y) : clos_refl_trans R x y
  | rt_refl x : clos_refl_trans R x x
  | rt_trans x y z
        (Hxy : clos_refl_trans R x y)
        (Hyz : clos_refl_trans R y z) :
        clos_refl_trans R x z.

(* Por exemplo, o fecho reflexivo e transitivo da relação next_nat coincide com a relação le. *)

Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
  - (* -> *)
    intro H. induction H.
    + (* le_n *) apply rt_refl.
    + (* le_S *)
      apply rt_trans with m. apply IHle. apply rt_step.
      apply nn.
  - (* <- *)
    intro H. induction H.
    + (* rt_step *) inversion H. apply le_S. apply le_n.
    + (* rt_refl *) apply le_n.
    + (* rt_trans *)
      apply le_trans with y.
      apply IHclos_refl_trans1.
      apply IHclos_refl_trans2. Qed.

(* A definição acima do fecho reflexivo e transitivo é natural: ela diz, explicitamente, que 
o fecho reflexivo e transitivo de R é a menor relação que inclui R e que está fechada sob as 
regras de reflexividade e transitividade. No entanto, acontece que essa definição não é
 muito conveniente para realizar demonstrações, visto que o ''não determinismo'' da regra 
 rt_trans pode, às vezes, levar a induções trabalhosas. Aqui está uma definição mais útil: *)

 Inductive clos_refl_trans_1n {A : Type}
                             (R : relation A) (x : A)
                             : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A)
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z.

(* Nossa nova definição de fecho reflexivo e transitivo ''agrupa'' as regras rt_step e 
rt_trans em uma única regra step. A premissa à esquerda desse passo é um uso único de R, o 
que leva a um princípio de indução muito mais simples.

Antes de prosseguirmos, devemos verificar se as duas definições de fato definem a mesma 
relação...

Primeiro, provamos dois lemas mostrando que clos_refl_trans_1n imita o comportamento dos dois 
construtores ''faltantes'' de clos_refl_trans. *)

Lemma rsc_R : forall (X:Type) (R:relation X) (x y : X),
  R x y -> clos_refl_trans_1n R x y.
Proof.
  intros X R x y H.
  apply rt1n_trans with y. apply H. apply rt1n_refl. Qed.

(* Exercício *)

Lemma rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y ->
      clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.
Proof.
  intros X R x y z H1 H2.
  induction H1 as [ x' | x' y' z' Hxy Hrest IH ].
  - apply H2.
  - apply rt1n_trans with y'.
    + apply Hxy.
    + apply IH. apply H2.
Qed.

(* Então usamos esses fatos para provar que as duas definições de fecho reflexivo e 
transitivo de fato definem a mesma relação. *)

Theorem rtc_rsc_coincide :
  forall (X:Type) (R: relation X) (x y : X),
    clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof.
  intros X R x y. split.
  - (* -> *)
    intros H.
    induction H.
    + apply rsc_R. apply H.
    + apply rt1n_refl.
    + apply rsc_trans with y.
      * apply IHclos_refl_trans1.
      * apply IHclos_refl_trans2.
  - (* <- *)
    intros H.
    induction H.
    + apply rt_refl.
    + apply rt_trans with y.
      * apply rt_step. apply Hxy.
      * apply IHclos_refl_trans_1n.
Qed.