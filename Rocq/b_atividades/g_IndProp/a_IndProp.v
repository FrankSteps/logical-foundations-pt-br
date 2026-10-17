(* Require Import LFPTBR.pasta.arquivo. *)

Set Warnings "-notation-overridden".
Require Import Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import LFPTBR.a_Basico.i_Provas.
Require Import LFPTBR.f_Logica_em_Rocq.a_Logica.
Require Import LFPTBR.b_Inducao.a_Inducao.
Require Import LFPTBR.d_Polimorfismo_e_Funcoes_de_Alta_Ordem.b_Funcoes_de_Alta_Ordem.


(******************* Proposições Indutivamente Definidas *********************)

(* No capítulo de Lógica, vimos várias maneiras de escrever proposições, 
incluindo conjunção, disjunção e quantificação existencial. Neste capítulo, 
trazemos mais uma nova ferramenta para o contexto: proposições definidas 
indutivamente. Para começar, alguns exemplos... *)

(*** Exemplo: A Conjectura de Collatz ***)

(* A Conjectura de Collatz é um famoso problema em aberto na teoria dos números. 
O seu enunciado é bastante simples. Primeiro, definimos uma função csf sobre 
números da seguinte forma (onde csf significa ''Collatz step function'' — função 
de passo de Collatz): *)

Fixpoint div2 (n : nat) : nat :=
  match n with
    0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Definition csf (n : nat) : nat :=
  if even n then div2 n
  else (3 * n) + 1.

(* Em seguida, analisamos o que acontece quando aplicamos csf repetidamente a 
um determinado número inicial. Por exemplo, csf 12 é 6, e csf 6 é 3, portanto, 
ao aplicar csf repetidamente, obtemos a sequência 12, 6, 3, 10, 5, 16, 8, 4, 2, 
1. 

Da mesma forma, se começarmos com 19, obtemos a sequência mais longa 19, 58, 
29, 88, 44, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8, 4, 2, 1. 

Ambas as sequências partualmente chegam a 1. A pergunta feita por Collatz foi: 
A sequência que começa a partir de qualquer número natural positivo tem garantia 
de partualmente chegar a 1? 

Para formalizar essa questão no Rocq, podemos tentar definir uma função recursiva 
que calcule o número total de passos que tal sequência leva para alcançar 1. *)

Fail Fixpoint alcanca1_em (n : nat) : nat :=
  if n =? 1 then 0
  else 1 + alcanca1_em (csf n).

(* Você pode escrever essa definição em uma linguagem de programação padrão. 
No entanto, essa definição é rejeitada pelo verificador de terminação do Rocq, 
já que o argumento para a chamada recursiva, csf n, não é 'obviamente menor' do 
que n.

De fato, esta não é apenas uma limitação sem propósito: as funções no Rocq devem 
ser totais para garantir a consistência lógica. 

Além disso, não podemos corrigir isso criando um verificador de terminação mais 
inteligente: decidir se essa função específica é total seria equivalente a 
resolver a Conjectura de Collatz!

Outra ideia seria expressar o conceito de 'partualmente alcançar 1 na 
sequência de Collatz' como uma propriedade de números definida recursivamente: 
Collatz_vale_para : nat → Prop. *)

Fail Fixpoint Collatz_vale_para (n : nat) : Prop :=
  match n with
  | 0 => False
  | 1 => True
  | _ => if par n then Collatz_vale_para (div2 n)
                   else Collatz_vale_para ((3 * n) + 1)
  end.

(* Esta função recursiva também é rejeitada pelo verificador de terminação, já que,
embora possamos em princípio convencer o Rocq de que div2 n é menor do que n, com 
certeza não podemos convencê-lo de que (3 × n) + 1 é menor do que n! Felizmente, 
há outra maneira de fazer isso: podemos expressar o conceito ''atinge 1 
partualmente na sequência de Collatz'' como uma propriedade de números definida 
indutivamente. Intuitivamente, essa propriedade é definida por um conjunto de 
regras:
               
-------------------------------------------- (Cvp_um) 
          Collatz_vale_para 1

par n = true   Collatz_vale_para (div2 n)  
-------------------------------------------- (Cvp_par) 
          Collatz_vale_para n


par n = false    Collatz_vale_para ((3 * n) + 1)
--------------------------------------------- (Cvp_impar)  
          Collatz_vale_para n 
 

Portanto, há três maneiras de provar que um número n partualmente atinge 1 na 
sequência de Collatz:
  - n é 1;
  - n é par e div2 n partualmente atinge 1;
  - n é ímpar e (3 × n) + 1 partualmente atinge 1.

Podemos provar que um número atinge 1 construindo uma derivação (finita) usando 
essas regras. Por exemplo, aqui está a derivação provando que 12 atinge 1 (onde 
omitimos as premissas de paridade):

                   -------------------- (Cvp_um)
                    Collatz_vale_para 1
                    -------------------- (Cvp_par)
                    Collatz_vale_para 2
                    -------------------- (Cvp_par)
                    Collatz_vale_para 4
                    -------------------- (Cvp_par)
                    Collatz_vale_para 8
                    -------------------- (Cvp_par)
                    Collatz_vale_para 16
                    -------------------- (Cvp_impar)
                    Collatz_vale_para 5
                    -------------------- (Cvp_par)
                    Collatz_vale_para 10
                    -------------------- (Cvp_impar)
                    Collatz_vale_para 3
                    -------------------- (Cvp_par)
                    Collatz_vale_para 6
                    -------------------- (Cvp_par)
                    Collatz_vale_para 12

Formalmente no Rocq, a propriedade Collatz_vale_para é definida indutivamente: *)

Inductive Collatz_vale_para : nat -> Prop :=
  | Cvp_um : Collatz_vale_para 1
  | Cvp_par (n : nat) : even n = true ->
                         Collatz_vale_para (div2 n) ->
                         Collatz_vale_para n
  | Cvp_impar (n : nat) : even n = false ->
                         Collatz_vale_para ((3 * n) + 1) ->
                         Collatz_vale_para n.


Example Collatz_vale_para_12 : Collatz_vale_para 12.
Proof.
  apply Cvp_par. reflexivity. simpl.
  apply Cvp_par. reflexivity. simpl.
  apply Cvp_impar. reflexivity. simpl.
  apply Cvp_par. reflexivity. simpl.
  apply Cvp_impar. reflexivity. simpl.
  apply Cvp_par. reflexivity. simpl.
  apply Cvp_par. reflexivity. simpl.
  apply Cvp_par. reflexivity. simpl.
  apply Cvp_par. reflexivity. simpl.
  apply Cvp_um.
Qed.

(* A conjectura de Collatz afirma então que a sequência iniciada a partir de 
qualquer número positivo chega a 1: *)

Conjecture collatz : forall n, n <> 0 -> Collatz_vale_para n.

(* Se você conseguir provar essa conjectura, terá um futuro brilhante como 
teórico dos números! Mas não perca muito tempo com ela — ela está em aberto 
desde 1937. *)

(*** Exemplo: Relação binária para comparar números ***)

(* Uma relação binária em um conjunto X tem o tipo Rocq X -> X -> Prop. Esta é 
uma família de proposições parametrizada por dois elementos de X — ou seja, uma 
proposição sobre pares de elementos de X. 

Por exemplo, uma relação binária familiar em nat é le : nat → nat → Prop, a relação 
''menor ou igual a'', que pode ser definida indutivamente pelas duas regras 
seguintes: 

                     ---------------- (le_n)  
                         le n n	

                         le n m	
                     ---------------- (le_S) 
                         le n (S m)	

Estas regras dizem que existem duas maneiras de mostrar que um número é menor ou 
igual a outro: seja observando que eles são o mesmo número, ou, se o segundo 
tiver a forma S m, fornecendo evidências de que o primeiro é menor ou igual a m. 

Isso corresponde à seguinte definição indutiva em Rocq: *)

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m -> le n (S m).
Notation "n <= m" := (le n m) (at level 70).

(* Esta definição é um pouco mais simples e elegante do que a função booleana leb 
(menorigualb) que definimos em Básico. Como de costume, le e leb são equivalentes, 
e há um exercício sobre isso mais adiante. *)

Example le_3_5 : 3 <= 5.
Proof.
  apply le_S. apply le_S. apply le_n. Qed.

(*** Exemplo: Fecho transitivo ***)

(* Outro exemplo: O fecho transitivo de uma relação R é a menor relação que 
contém R e que é transitiva. Isso pode ser definido pelas duas regras seguintes: 

                      R x y	
                 ---------------- (passo_base)
                 fech_trans R x y	

        fech_trans R x y    fech_trans R y z	
        ------------------------------------ (passo_trans)  
                 fech_trans R x z

Em Rocq, isso se apresenta da seguinte forma: *)

Inductive fecho_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | passo_base (x y : X) :
      R x y ->
      fecho_trans R x y
  | passo_trans (x y z : X) :
      fecho_trans R x y ->
      fecho_trans R y z ->
      fecho_trans R x z.

(* Por exemplo, suponha que definamos uma relação ''genitor de'' em um grupo de 
pessoas... *)

Inductive Pessoa : Type := Sage | Cleo | Ridley | Moss.
Inductive genitor_de : Pessoa -> Pessoa -> Prop :=
  gd_SC : genitor_de Sage Cleo
| gd_SR : genitor_de Sage Ridley
| gd_CM : genitor_de Cleo Moss.

(* Neste exemplo, Sage é o genitor tanto de Cleo quanto de Ridley; e Cleo é o 
genitor de Moss. 

A relação genitor_de não é transitiva, mas podemos definir uma relação 
ancestral_de como seu fecho transitivo:*)

Definition ancestral_de : Pessoa -> Pessoa -> Prop :=
  fecho_trans genitor_de.

(* Aqui está uma derivação mostrando que Sage é um ancestral de Moss: 

 -------------------(gd_SC)        -------------------(gd_CM)
 genitor_de Sage Cleo              genitor_de Cleo Moss
---------------------(passo-base)  ---------------------(passo-base)
ancestral_de Sage Cleo             ancestral_de Cleo Moss
----------------------------------------------------(passo-trans)
                ancestral_de Sage Moss 

*)

Example ancestral_de_ex : ancestral_de Sage Moss.
Proof.
  unfold ancestral_de. apply passo_trans with Cleo.
  - apply passo_base. apply gd_SC.
  - apply passo_base. apply gd_CM. Qed.

(* O cálculo do fecho transitivo pode ser indecidível mesmo para uma relação R que 
seja decidível (por exemplo, a relação cms abaixo), portanto, em geral, não 
podemos esperar definir o fecho transitivo como uma função booleana. Felizmente, o 
Rocq nos permite definir o fecho transitivo como uma relação indutiva. 

O fecho transitivo de uma relação binária não pode, em geral, ser expresso em 
lógica de primeira ordem. A lógica do Rocq é, no entanto, muito mais poderosa e 
pode definir facilmente tais relações indutivas. *)

(*** Exemplo: Fecho Reflexivo e Transitivo ***)

(* Como outro exemplo, o fecho reflexivo e transitivo de uma relação R é a menor 
relação que contém R e que é reflexiva e transitiva. Isso pode ser definido pelas 
três regras seguintes (onde adicionamos uma regra de reflexividade a fecho_trans): 

                          R x y	
                ------------------------- (rt_passo)  
                 fecho_refl_trans R x y	
  	  
                ---------------------- (rt_refl)
                 fecho_refl_trans R x x	

            fecho_refl_trans R x y    fecho_refl_trans R y z	
         ----------------------------------------------------- (rt_trans)  
                          fecho_refl_trans R x z

*)

Inductive fecho_refl_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | rt_passo (x y : X) :
      R x y ->
      fecho_refl_trans R x y
  | rt_refl (x : X) :
      fecho_refl_trans R x x
  | rt_trans (x y z : X) :
      fecho_refl_trans R x y ->
      fecho_refl_trans R y z ->
      fecho_refl_trans R x z.
  
(* Por exemplo, isso permite uma definição equivalente da conjectura de Collatz. 
Primeiro, definimos uma relação binária correspondente à ''função de passo de 
Collatz'' (csf): *)

Definition cs (n m : nat) : Prop := csf n = m.

(* Esta relação de passo de Collatz pode ser usada em conjunto com a operação de 
fecho reflexivo e transitivo para definir uma relação de múltiplos passos de 
Collatz (cms), expressando que um número n alcança outro número m em zero ou mais 
passos de Collatz *)

Definition cms n m := fecho_refl_trans cs n m.
Conjecture collatz' : forall n, n <> 0 -> cms n 1.

(* Esta relação cms definida em termos de fecho_refl_trans permite derivações mais 
interessantes do que as lineares da relação Collatz_vale_para definida 
diretamente: 

csf 16 = 8         csf 8 = 4           csf 4 = 2         csf 2 = 1
--------(rt_passo)  -------(rt_passo)  -------(rt_passo)  -------(rt_passo)
cms 16 8           cms 8 4              cms 4 2           cms 2 1
-------------------------(rt_trans)  ------------------------(rt_trans)
        cms 16 4                              cms 4 1
        ---------------------------------------------(rt_trans)
                           cms 16 1

*)

(* Exercício *)
(* Como você modificaria a definição de fecho_refl_trans acima para definir 
o fecho reflexivo, simétrico e transitivo? 

Resposta:
Modificaria com uma regra a mais:

fecho_trans_refl_sim R y x
--------------------------- rts_sim
fecho_trans_refl_sim R x y

Ficaria assim:
Inductive fecho_refl_trans_sim {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | rts_passo (x y : X) :
      R x y ->
      fecho_refl_trans_sim R x y
  | rts_refl (x : X) :
      fecho_refl_trans_sim R x x
  | rts_trans (x y z : X) :
      fecho_refl_trans_sim R x y ->
      fecho_refl_trans_sim R y z ->
      fecho_refl_trans_sim R x z
  | rts_sim (x y : X) : fecho_refl_trans_sim R y x -> 
      fecho_refl_trans_sim R x y. *)

(*** Exemplo: Permutações ***)

(* O conceito matemático familiar de permutação também possui uma formulação 
elegante como uma relação indutiva. Por simplicidade, vamos nos focar em 
permutações de listas com exatamente três elementos.

Podemos definir tais permutações pelas seguintes regras: 

   	                  
                ------------------------ (perm3_troca12) )
                Perm3 [a;b;c] [b;a;c] 	
     
                ------------------------- (perm3_troca23)
                Perm3 [a;b;c] [a;c;b] 	

               Perm3 l1 l2       Perm3 l2 l3 	
               ------------------------------ (perm3_trans)  
                      Perm3 l1 l3

Por exemplo, podemos derivar Perm3 [1;2;3] [3;2;1] da seguinte forma:

--------(perm_troca12)  ---------------------(perm_troca23)
    Perm3 [1;2;3] [2;1;3]  Perm3 [2;1;3] [2;3;1]
    ------------------------------(perm_trans)  ------------(perm_troca12)
        Perm3 [1;2;3] [2;3;1]                   Perm [2;3;1] [3;2;1]
        -----------------------------------------------------(perm_trans)
                          Perm3 [1;2;3] [3;2;1]

Esta definição diz:

    - Se l2 pode ser obtida a partir de l1 trocando o primeiro e o segundo 
    elementos, então l2 é uma permutação de l1.

    - Se l2 pode ser obtida a partir de l1 trocando o segundo e o terceiro 
    elementos, então l2 é uma permutação de l1.

   - Se l2 é uma permutação de l1 e l3 é uma permutação de l2, então l3 é 
   uma permutação de l1.

No Rocq, Perm3 recebe a seguinte definição indutiva: *)

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_troca12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_troca23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

(* Exercício*)
(* De acordo com esta definição, [1;2;3] é uma permutação de si mesmo? 

Resposta: Sim *)

(*** Exemplo: Paridade (mais uma vez) ***)

(* Já vimos duas maneiras de enunciar a proposição de que um número n é par: Podemos dizer

(1) even n = true (usando a função booleana recursiva even), ou

(2) ∃ k, n = double k (usando um quantificador existencial).

Uma terceira possibilidade, que usaremos como um exemplo contínuo simples 
neste capítulo, é dizer que um número é par se pudermos estabelecer sua 
paridade a partir das seguintes duas regras: 

                      -------------	(ev_0)  
                          ev 0 	
        
                          ev n 	
                      ------------- (ev_SS)  
                       ev (S (S n)) 	

Intuitivamente, essas regras dizem que:

    - O número 0 é par.

    - Se n é par, então S (S n) é par.

(Definir a paridade dessa forma pode parecer um pouco confuso, já que já v
imos duas maneiras perfeitamente boas de fazer isso. Ela serve como um 
exemplo prático conveniente por ser simples e compacta, mas logo 
retornaremos aos exemplos mais convincentes citados acima.)

Para ilustrar como essa nova definição de paridade funciona, vamos imaginar 
usá-la para mostrar que 4 é par:

                           ---- (ev_0)
                           ev 0
                       ------------ (ev_SS)
                       ev (S (S 0))
                   -------------------- (ev_SS)
                   ev (S (S (S (S 0))))

Em palavras, para mostrar que 4 é par, pela regra ev_SS, basta mostrar que 2 
é par. Isso, por sua vez, é garantido novamente pela regra ev_SS, desde que 
possamos mostrar que 0 é par. Mas esse último fato decorre diretamente da 
regra ev_0.

Podemos traduzir a definição informal de paridade acima em uma declaração 
Inductive formal, onde cada ''forma como um número pode ser par'' 
corresponde a um construtor separado: *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(* Tais definições são diferentemente interessantes em comparação aos usos 
anteriores de Inductive para definir tipos de dados indutivos como nat ou 
list. Por um lado, não estamos definindo um Tipo (como nat) ou uma função 
que produz um Tipo (como list), mas sim uma função de nat para Prop — ou 
seja, uma propriedade de números. Mas o que há de realmente novo é que, como 
o argumento nat de ev aparece à direita dos dois-pontos na primeira linha, 
ele tem permissão para assumir valores diferentes nos tipos de construtores 
diferentes: 0 no tipo de ev_0 e S (S n) no tipo de ev_SS. Consequentemente, 
o tipo de cada construtor deve ser especificado explicitamente (após os 
dois-pontos), e o tipo de cada construtor deve ter a forma ev n para algum 
número natural n.

Em contraste, lembre-se da definição de list:
 Inductive list (X:Type) : Type :=
      | nil
      | cons (x : X) (l : list X).
  
ou (equivalentemente, mas de forma mais explícita):
  Inductive list (X:Type) : Type :=
  | nil                       : list X
  | cons (x : X) (l : list X) : list X.

Esta definição introduz o parâmetro X globalmente, à esquerda dos 
dois-pontos, forçando o resultado de nil e cons a ser o mesmo tipo (ou seja, 
list X). Mas se tivéssemos tentado trazer nat para a esquerda dos dois-pontos 
ao definir ev, teríamos visto um erro: *)
 
Fail Inductive wrong_ev (n : nat) : Prop :=
  | wrong_ev_0 : wrong_ev 0
  | wrong_ev_SS (H: wrong_ev n) : wrong_ev (S (S n)).
(* ===> Error: Last occurrence of "wrong_ev" must have "n" as 1st
        argument in "wrong_ev 0". *)

(* Em uma definição indutiva, um argumento para o construtor de tipo à 
esquerda dos dois-pontos é chamado de ''parâmetro'', enquanto um argumento à 
direita é chamado de ''índice'' ou ''anotação''.

Por exemplo, em Inductive list (X : Type) := ..., o X é um parâmetro, 
enquanto em Inductive ev : nat → Prop := ..., o argumento nat sem nome é um 
índice.

Podemos pensar na definição indutiva de ev como definindo uma propriedade do 
Rocq ev : nat → Prop, juntamente com dois 'construtores de evidência'': *)

Check ev_0 : ev 0.
Check ev_SS : forall (n : nat), ev n -> ev (S (S n)).

(* De fato, o Rocq também aceita a seguinte definição equivalente de ev: *)

Module EvExperimental.
Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS : forall (n : nat), ev n -> ev (S (S n)).
End EvExperimental.

(* Esses construtores de evidência podem ser pensados como ''evidência 
primitiva de paridade'', e eles podem ser usados mais tarde exatamente como 
teoremas provados. Em particular, podemos usar a tática apply do Rocq com os 
nomes dos construtores para obter evidência de ev para números específicos... *)

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(* ... ou podemos usar a sintaxe de aplicação de função para combinar 
vários construtores: *)

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(* Dessa forma, também podemos provar teoremas que possuem hipóteses 
envolvendo ev. *)

Theorem ev_mais4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn. apply ev_SS. apply ev_SS. apply Hn.
Qed.

(* Exercício *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
    intros n. unfold double. induction n as [ | n' IHn'].
    - apply ev_0.
    - apply ev_SS. apply IHn'.
    Qed.

(**************** Construindo evidências para permutações *****************)

(* Da mesma forma, podemos aplicar os construtores de evidência para obter 
evidências de Perm3 [1;2;3] [3;2;1]: *)

Lemma Perm3_rev : Perm3 [1;2;3] [3;2;1].
Proof.
  apply perm3_trans with (l2:=[2;3;1]).
  - apply perm3_trans with (l2:=[2;1;3]).
    + apply perm3_troca12.
    + apply perm3_troca23.
  - apply perm3_troca12.
Qed.

(* E, mais uma vez, podemos usar de forma equivalente a sintaxe de aplicação 
de função para combinar vários construtores. (Note que o verificador de 
tipos do Rocq pode inferir não apenas os tipos, mas também nats e listas, 
quando eles forem claros a partir do contexto.) *)

Lemma Perm3_rev' : Perm3 [1;2;3] [3;2;1].
Proof.
  apply (perm3_trans _ [2;3;1] _
          (perm3_trans _ [2;1;3] _
            (perm3_troca12 _ _ _)
            (perm3_troca23 _ _ _))
          (perm3_troca12 _ _ _)).
Qed.

(* Portanto, as árvores de derivação informais que desenhamos acima não 
estão muito distantes do que está acontecendo formalmente. Formalmente, 
estamos usando os construtores de evidência para construir árvores de 
evidência, de forma semelhante às árvores finitas que construímos usando os 
construtores de tipos de dados como nat, list, árvores binárias, etc. *)

(* Exercício *)

Lemma Perm3_ex1 : Perm3 [1;2;3] [2;3;1].
Proof.
  apply perm3_trans with (l2 := [2;1;3]). 
  - apply perm3_troca12.
  - apply perm3_troca23.
  Qed.

(* O mesmo, só que agora usando a sintaxe de aplicação de função, para testar *)
Lemma Perm3_ex1' : Perm3 [1;2;3] [2;3;1].
Proof.
  apply (perm3_trans _ [2;1;3] _ (perm3_troca12 _ _ _) (perm3_troca23 _ _ _)). 
  Qed.


Lemma Perm3_refl : forall (X : Type) (a b c : X),
  Perm3 [a;b;c] [a;b;c].
Proof.
  intros X a  b c. apply perm3_trans with (l2 := [a;c;b]).
  - apply perm3_troca23.
  - apply perm3_troca23.
  Qed.

Lemma Perm3_refl' : forall (X : Type) (a b c : X),
  Perm3 [a;b;c] [a;b;c].
Proof.
  intros X a  b c.
   apply (perm3_trans _ [a;c;b] _ (perm3_troca23 _ _ _)(perm3_troca23 _ _ _)).
  Qed.
  
(*********************** Usando evidências em provas ***********************)

(* Além de construir evidências de que números são pares, também podemos 
desconstruir tais evidências, raciocinando sobre como elas poderiam ter sido 
construídas.

Definir ev com uma declaração Inductive diz ao Rocq não apenas que os 
construtores ev_0 e ev_SS são maneiras válidas de construir evidências de que 
um determinado número é ev, mas também que esses dois construtores são as 
únicas maneiras de construir evidências de que números são ev.

Em outras palavras, se alguém nos der uma evidência E para a proposição ev n, 
então sabemos que E deve ser uma de duas coisas:

   - E = ev_0 e n = O, ou
   - E = ev_SS n' E' e n = S (S n'), onde E' é uma evidência para ev n'.

Isso sugere que deve ser possível analisar uma hipótese da forma ev n da mesma 
maneira que fazemos com estruturas de dados definidas indutivamente; em 
particular, deve ser possível argumentar seja por análise de casos, seja por 
indução sobre essa evidência. Vejamos alguns exemplos para ver o que isso 
significa na prática. *)

(*** Desconstrução e Inversão de Evidências ***)

(* Suponha que estejamos provando algum fato envolvendo um número n, e nos seja 
dada `ev n` como hipótese. Já sabemos como realizar uma análise de casos em n 
usando `destruct` ou `induction`, gerando submetas separadas para o caso em que 
n = O e o caso em que n = S n' para algum n'. No entanto, para algumas provas, 
podemos querer analisar a evidência para `ev n` diretamente.

Como uma ferramenta para tais provas, podemos formalizar a caracterização 
intuitiva que demos acima para a evidência de `ev n`, usando `destruct`. *)

Lemma ev_inversao : forall (n : nat),
    ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E. destruct E as [ | n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

(* Fatos como este são frequentemente chamados de ''lemas de inversão'' porque 
nos permitem ''inverter'' alguma informação dada para raciocinar sobre todas as 
diferentes maneiras pelas quais ela poderia ter sido derivada. Aqui, há duas 
maneiras de provar `ev n`, e o lema de inversão torna isso explícito. *)

(* Exercício *)
(* Vamos provar um lema de inversão semelhante para `le`. *)

Lemma le_inversao : forall (n m : nat),
  le n m ->
  (n = m) \/ (exists m', m = S m' /\ le n m').
Proof.
  intros n m Hle.
  (* Definição de le em Rocq:
   le_n : forall n, le n n
   le_S : forall n m, le n m -> le n (S m) *)
  destruct Hle as [ | n' m' l] eqn:EL.
  - left. reflexivity.
  - right. exists m'. split.
     + reflexivity.
     + apply l.
     Qed.

(* Podemos usar o lema de inversão que provamos acima para ajudar a estruturar 
provas: *)

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E. apply ev_inversao in E. destruct E as [H0|H1].
  - discriminate H0.
  - destruct H1 as [n' [Hnn' E']]. injection Hnn' as Hnn'.
    rewrite Hnn'. apply E'.
Qed.

(* Observe como o lema de inversão produz duas submetas, que 
correspondem às duas maneiras de provar `ev`. A primeira 
submeta é uma contradição que é descartada com `discriminate`. 
A segunda submeta faz uso de `injection` e `rewrite`.

O Rocq fornece uma tática útil chamada `inversion` que isola 
esse padrão comum, nos poupando do trabalho de declarar e 
provar explicitamente um lema de inversão para cada definição 
`Inductive` que fazemos.

Aqui, a tática `inversion` consegue detectar (1) que o 
primeiro caso, onde n = 0, não se aplica e (2) que o n' que 
aparece no caso `ev_SS` deve ser o mesmo que n. Ela inclui 
uma anotação ''as'' semelhante ao `destruct`, permitindo-nos 
atribuir nomes em vez de deixar que o Rocq os escolha. *)

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E as [ | n' E' Hnn'].
  (* Nós estamos no caso E = ev_SS n' E' agora. *)
  apply E'.
Qed.

(* A tática inversion pode aplicar o princípio da explosão a hipóteses 
''obviamente contraditórias'' envolvendo propriedades definidas indutivamente, 
algo que exige um pouco mais de trabalho ao usar nosso lema de inversão. Compare: *)

Theorem um_nao_e_par : ~ ev 1.
Proof.
  intros H. apply ev_inversao in H. destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem um_nao_e_par' : ~ ev 1.
Proof. intros H. inversion H. Qed.

(* Exercício *)
(* Prove o seguinte resultado usando inversion. (Para praticar mais, você também 
pode prová-lo usando o lema de inversão.) *)

Theorem SSSSev__par : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H. inversion H as [ |n' Hev]. 
  apply evSS_ev in Hev. apply Hev.
  Qed.

Theorem SSSSev__par' : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n Hev4. apply ev_inversao in Hev4. destruct Hev4 as [H0 | H1].
  - discriminate H0.
  - destruct H1 as [n' [Hseq Hev]]. 
    injection Hseq as Hseq. apply evSS_ev. rewrite Hseq. apply Hev.
    Qed.

(* Prove o seguinte resultado usando inversion. *)

Theorem ev5_sem_sentido :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros Hev5. inversion Hev5 as [ |n' Hev3].
  inversion Hev3 as [ | n'' Hev1].
  inversion Hev1.
  Qed.

(* A tática `inversion` realiza bastante trabalho. Por exemplo, quando aplicada 
a uma hipótese de igualdade, ela executa o trabalho tanto de `discriminate` 
quanto de `injection`. Além disso, ela realiza os comandos `intros` e `rewrites` 
que tipicamente são necessários no caso de `injection`. Ela também pode ser 
aplicada para analisar evidências de proposições definidas indutivamente 
arbitrárias, e não apenas igualdade. Como exemplos, vamos usá-la para reprovar 
alguns teoremas do capítulo de Mais_Taticas_Basicas. (Aqui estamos sendo um 
pouco preguiçosos ao omitir a cláusula `as` do `inversion`, pedindo assim que o 
Rocq escolha os nomes para as variáveis e hipóteses que ele introduz.) *)

Theorem inversao_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversao_ex2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

(* Eis como a inversão funciona em geral. 

 - Suponha que o nome H se refira a uma hipótese P no contexto atual, onde P 
   foi definido por uma declaração Inductive.

 - Então, para cada um dos construtores de P, inversion H gera uma submeta na 
   qual H foi substituído pelas condições específicas sob as quais esse 
   construtor poderia ter sido usado para provar P.
   
 - Algumas dessas submetas serão autocontraditórias; a inversão as descarta.

 - As que restam representam os casos que devem ser provados para estabelecer a 
   meta original. Para essas, a inversão adiciona ao contexto de prova todas as 
   equações que devem valer para os argumentos fornecidos a P — por exemplo, n' 
   = n na prova de evSS_ev).
   
O exercício ev_double acima nos permite mostrar facilmente que nossa nova noção 
de paridade é implicada pelas duas anteriores (já que, por par_bool_prop no 
capítulo f_Logica_em_Rocq, já sabemos que elas são equivalentes entre si). Para 
mostrar que todas as três coincidem, precisamos apenas do seguinte lema. *)

Lemma ev_Par_primeira_tentativa : forall n,
  ev n -> Par n.
Proof.
  (* TRABALHADO EM AULA *) 
  unfold Par. intros n E.

(* Começamos instanciando o existencial com div2 n: *)
  exists (div2 n).

(* Resta-nos provar que n = double (div2 n) sabendo que E : ev n.

Poderíamos tentar prosseguir por análise de casos ou indução sobre n. No entanto, 
como `ev` é mencionado em E, essa estratégia parece pouco promissora, pois (como 
já notamos antes) a hipótese de indução tratará de n-1 (que não é par!). Assim, 
parece melhor tentar primeiro a inversão na evidência E. De fato, o primeiro 
caso pode ser resolvido trivialmente. *)
  inversion E as [EQ' | n' E' EQ'].
  - (* E = ev_0 *) reflexivity.
  - (* E = ev_SS n' E' *)
    simpl. f_equal. f_equal.

(* Infelizmente, o segundo caso é mais difícil. Precisamos mostrar que n' = 
double (div2 n'), mas esta é apenas outra instância do fato sobre double e div2 
que estávamos tentando provar antes, só que para n' em vez de n. 

Nós temos a evidência E' : ev n', mas o que está faltando é uma hipótese de 
indução correspondente a essa evidência.

Então, estamos travados! *)

  Abort.

(*** Indução sobre Evidência ***)

(* Se esta história parece familiar, não é coincidência: encontramos problemas 
semelhantes no capítulo b_Inducao, ao tentar usar a análise de casos para provar 
resultados que exigiam indução. E, mais uma vez, a solução é... indução!

O comportamento da indução sobre evidência é o mesmo que o seu comportamento 
sobre dados: faz com que o Rocq gere um subgoal para cada construtor que poderia 
ter sido usado para construir essa evidência, ao mesmo tempo em que fornece uma 
hipótese de indução para cada ocorrência recursiva da propriedade em questão.

Para provar que uma propriedade de n vale para todos os números pares (ou seja, 
aqueles para os quais `ev n` é verdadeiro), podemos usar indução sobre `ev n`. 
Isso exige que provemos duas coisas, correspondendo às duas maneiras pelas quais 
`ev n` poderia ter sido construído. Se foi construído por `ev_0`, então n = 0 e 
a propriedade deve valer para 0. Se foi construído por `ev_SS`, então a evidência 
de `ev n` é da forma `ev_SS n' E'`, onde n = S (S n') e E' é a evidência para 
`ev n'`. Nesse caso, a hipótese de indução diz que a propriedade que estamos 
tentando provar vale para n'.

Vamos tentar provar esse lema novamente: *)

Lemma ev_Par : forall n,
  ev n -> Par n.
Proof.
  unfold Par. intros n E. exists (div2 n).
  induction E as [ |n' E' IH].
  - (* E = ev_0 *)
    reflexivity.
  - (* E = ev_SS n' E',  com IH : n' = double (div2 n') *)
    simpl. f_equal. f_equal. apply IH.
Qed.

(* Aqui, podemos ver que o Rocq produziu uma IH que corresponde a E′, a única 
ocorrência recursiva de ev em sua própria definição. Como E′ menciona n′, a 
hipótese de indução fala sobre n′, em vez de n ou de algum outro número.

A equivalência entre a segunda e a terceira definições de paridade agora 
decorre. *)

Theorem ev_Par_sse : forall n,
  ev n <-> Par n.
Proof.
  intros n. split.
  - (* -> *) apply ev_Par.
  - (* <- *) unfold Par. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(* Como veremos em capítulos posteriores, a indução sobre evidência é uma 
técnica recorrente em muitas áreas — em particular para a formalização da 
semântica de linguagens de programação.

Os exercícios a seguir fornecem exemplos mais simples dessa técnica, para ajudar 
você a se familiarizar com ela. *)

(* Exercício *)

Theorem ev_soma : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m Hevn Hevm. induction Hevn as [ | n' Hevn' IH].
  - apply Hevm.
  - simpl. apply ev_SS. apply IH.
  Qed. 

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
  (* Dica: Existem duas evidências sobre as quais você pode tentar fazer indução 
     aqui. Se uma não funcionar, tente a outra. *)
Proof.
  intros n m Hevnm Hevn.
  induction Hevn as [ | n' Hevn' IH].
  - apply Hevnm.
  - simpl in Hevnm. apply IH. apply evSS_ev in Hevnm. apply Hevnm.
    Qed.

(* Este exercício pode ser concluído sem indução ou análise de casos. No entanto, 
você precisará de uma asserção inteligente e de alguma reescrita trabalhosa.
Dica: (n + m) + (n + p) é par? *)

Theorem ev_mais_mais : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p.

  (* n + n é sempre par, independente de qualquer hipótese *)
  assert (Hnn: ev (n + n)).
  { induction n as [ | n' IH].
    - simpl. apply ev_0.
    - simpl. rewrite <- mais_n_Sm. apply ev_SS. apply IH. }

  intros Hnm Hnp.

  (* soma de dois pares é par: junta as duas hipóteses num só fato *)
  assert (Hsum: ev ((n+m) + (n+p))).
  { apply ev_soma. apply Hnm. apply Hnp. }

  (* reorganiza (n+m)+(n+p) como (n+n)+(m+p), só trocando associação/ordem *)
  assert (Heq: (n+m) + (n+p) = (n+n) + (m+p)).
  { rewrite <- add_associativo.
    rewrite (add_associativo m n p).
    rewrite (add_comutativo m n).
    rewrite <- (add_associativo n n (m+p)).
    rewrite <- add_associativo.
    reflexivity. }

  (* agora Hsum já está na forma ''ev ((n+n) + (m+p))'' *)
  rewrite Heq in Hsum.

  (* cancela a parte par (n+n), sobrando só ev (m+p) *)
  apply ev_ev__ev with (n := n+n).
  - apply Hsum.
  - apply Hnn.
Qed.

(*** Múltiplas Hipóteses de Indução ***)

(* Relembre a definição do fecho reflexivo e transitivo de uma relação:

Inductive fecho_refl_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | rt_passo (x y : X) :
      R x y ->
      fecho_refl_trans R x y
  | rt_refl (x : X) :
      fecho_refl_trans R x x
  | rt_trans (x y z : X) :
      fecho_refl_trans R x y ->
      fecho_refl_trans R y z ->
      fecho_refl_trans R x z. 
      
Digamos que uma relação em um tipo X é diagonal se ela refina a relação de 
identidade — ou seja, se R x y implica x = y. *)

Definition eDiagonal {X : Type} (R: X -> X -> Prop) :=
  forall x y, R x y -> x = y.

(* Agora considere o seguinte lema sobre relações diagonais: *)
Lemma fechamento_da_diagonal_e_diagonal: forall X (R: X -> X -> Prop),
  eDiagonal R ->
  eDiagonal (fecho_refl_trans R).
Proof.
  intros X R eDiag x y H.
  induction H as [ x y H | x | x y z H IH H' IH' ].
  (* Os dois primeiros casos correm como você esperaria... *)
  - specialize (eDiag x y H). rewrite -> eDiag. reflexivity.
  - reflexivity.
  - (* ...mas algo interessante acontece aqui: há duas hipóteses de 
     indução, IH e IH'! Se você pensar bem, não é tão estranho: 
     estamos no caso `srt_trans`, que possui dois componentes 
     recursivos, H, relacionando x a y, e H', relacionando y a z. 
     Portanto, podemos querer (e de fato precisaremos) de uma hipótese 
     de indução para H e outra para H' — chamadas aqui de IH e IH'. Em 
     geral, o Rocq sempre gerará uma hipótese de indução por 
     construtor recursivo do tipo sobre o qual a indução está sendo 
     feita. *)
   rewrite -> IH, <- IH'. reflexivity.
Qed.

(* Exercício *)
(* Em geral, pode haver várias maneiras de definir uma propriedade 
indutivamente. Por exemplo, aqui está uma definição alternativa 
(ligeiramente forçada) para ev: *)

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

(* Prove que esta definição é logicamente equivalente à antiga. Para 
simplificar a prova, use a técnica (do capítulo a_Logica) de aplicar 
teoremas a argumentos, e observe que a mesma técnica funciona com 
construtores de proposições definidas indutivamente. *)

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n. split.
  (* -> *)
  - intros Hev'. induction Hev' as [ | |n' m' Hn' IHn Hm' IHm].
    + apply ev_0.
    + apply (ev_SS _ (ev_0)).
    + apply (ev_soma). apply IHn.  apply IHm.
  (* <- *)
  - intros Hev. induction Hev as [ | n' evn'].
    + apply ev'_0.
    + apply (ev'_sum 2 n').
      -- apply ev'_2.
      -- apply IHevn'.
      Qed.

(* Podemos fazer provas por indução semelhantes na relação Perm3, que 
definimos anteriormente da seguinte forma: *)

Module Perm3Relembrando.
Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_troca12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_troca23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.
End Perm3Relembrando.

Lemma Perm3_simetrico : forall (X : Type) (l1 l2 : list X),
  Perm3 l1 l2 -> Perm3 l2 l1.
Proof.
  intros X l1 l2 E.
  induction E as [a b c | a b c | l1 l2 l3 E12 IH12 E23 IH23].
  - apply perm3_troca12.
  - apply perm3_troca23.
  - apply (perm3_trans _ l2 _).
    + apply IH23.
    + apply IH12.
Qed.

(* Exercìcio *)
Lemma Perm3_In : forall (X : Type) (x : X) (l1 l2 : list X),
    Perm3 l1 l2 -> In x l1 -> In x l2.
Proof.
  intros X x l1 l2 E. 
  induction E as [ a b c| a b c | l1 l2 l3 E12 IH12 E23 IH23].
   (* [a,b,c] -> [b,a,c] *)
  - intros [H1 | [H3 | H4]].
    + right. left. apply H1.
    + left. apply H3.
    + right. right. apply H4.
    (* [a,b,c] -> [a,c,b] *)
  - intros [H1 | [H2 | [H3 | H4]]].
    + left. apply H1.
    + right. right. left. apply H2.
    + right. left. apply H3.
    + right. right. right. apply H4.
    (* transitividade *)
  - intros H. apply IH23. apply IH12. apply H.
  Qed.

Lemma Perm3_NaoIn : forall (X : Type) (x : X) (l1 l2 : list X),
    Perm3 l1 l2 -> ~ In x l1 -> ~ In x l2.
Proof.
 intros X x l1 l2 Hp Hil1 Hil2.
 apply Hil1.
 apply (Perm3_In _ x l2 l1). apply Perm3_simetrico.
 - apply Hp.
 - apply Hil2.
 Qed.

(* Demonstrar que algo NÃO é uma permutação é bastante trabalhoso. Algumas das 
lemas acima, como o Perm3_In, podem ser úteis para isso. *)

Example Perm3_exemplo2 : ~ Perm3 [1;2;3] [1;2;4].
Proof.
  intros P.
  apply (Perm3_NaoIn _ 4) in P.
  - apply P. right. right. left. reflexivity.
  - intros H_in. simpl in H_in.
    destruct H_in as [H14 | [H24 | [H34 | HF]]].
     + discriminate H14.
     + discriminate H24.
     + discriminate H34.
     + apply HF.
     Qed.
(********************** Exercitando com Relações Indutivas *********************)  
   
(* Uma proposição parametrizada por um número (como ev) pode ser vista como uma 
propriedade — ou seja, ela define um subconjunto de nat, especificamente aqueles 
números para os quais a proposição é provável. Da mesma forma, uma proposição de 
dois argumentos pode ser pensada como uma relação — ou seja, ela define um 
conjunto de pares para os quais a proposição é provável. *)

Module Experimento.

(* Assim como as propriedades, as relações também podem ser definidas 
indutivamente. Um exemplo útil é a relação ''menor ou igual a'' sobre números que 
vimos brevemente acima. *)

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).
Notation "n <= m" := (le n m).

(* (Escrevemos a definição um pouco diferente desta vez, dando nomes explícitos 
aos argumentos dos construtores e movendo-os para a esquerda dos dois-pontos.)

Provas de fatos sobre ≤ usando os construtores le_n e le_S seguem os mesmos 
padrões que as provas sobre propriedades, como ev acima. Podemos aplicar os 
construtores para provar metas de ≤ (por exemplo, para mostrar que 3 ≤ 3 ou 
3 ≤ 6), e podemos usar táticas como inversion para extrair informações de 
hipóteses de ≤ no contexto (por exemplo, para provar que (2 ≤ 1) → 2+2=5.

Aqui estão algumas verificações de sanidade (sanity checks) sobre a definição. 
(Note que, embora estes sejam o mesmo tipo de ''testes unitários'' simples que 
fornecemos para as funções de teste que escrevemos nas primeiras aulas, devemos 
construir suas provas explicitamente — simpl e reflexivity não funcionam, porque 
as provas não se tratam apenas de simplificar computações.) *)

Theorem teste_le1 :
  3 <= 3.
Proof.
  (* TRABALHADO EM AULA  *)
  apply le_n. Qed.

Theorem teste_le2 :
  3 <= 6.
Proof.
  (* TRABALHADO EM AULA *)
  apply le_S. apply le_S. apply le_S. apply le_n. Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* TRABALHADO EM AULA *)
  intros H. inversion H. inversion H2. Qed.

(* A relação ''estritamente menor que'' n < m agora pode ser 
definida em termos de le. *)

Definition lt (n m : nat) := le (S n) m.
Notation "n < m" := (lt n m).

(* A operação ≥ é definida em termos de ≤. *)
Definition ge (m n : nat) : Prop := le n m.
Notation "m >= n" := (ge m n).

End Experimento.

(* A partir da definição de le, podemos descrever o comportamento 
de destruct, inversion e induction em uma hipótese H que fornece 
evidências da forma le e1 e2. Fazendo destruct H gerará dois 
casos. No primeiro, e1 = e2, e ele substituirá as instâncias de 
e2 por e1 na meta e no contexto. No segundo, e2 =S n'  para 
algum n' para o qual le e1 n' seja válido, e ele substituirá as 
instâncias de e2 por S n'. Fazendo inversion H removerá casos 
impossíveis e adicionará igualdades geradas ao contexto para uso 
posterior. Fazendo induction H vai, no segundo caso, adicionar a 
hipótese de indução de que a meta é válida quando e2 é 
substituído por n'.

Aqui estão vários fatos sobre as relações ≤ e < de que 
precisaremos mais adiante no curso. As provas são excelentes 
exercícios práticos. *)

(* Exercício *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o Hmn Hno.
  induction Hno as [ |n' o' no'].
  - apply Hmn.
  - apply le_S. apply IHno'. apply Hmn.
  Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - apply le_n.
  - inversion IHn'.
    + apply le_S. apply le_n.
    + apply le_S. rewrite H1. apply IHn'.
    Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m Hnlem.
  induction Hnlem as [ | n' m' nm'].
  - apply le_n.
  - apply le_S. apply IHnm'.
  Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m Hsnlesm.
  inversion Hsnlesm.
  - apply le_n.
  - apply (le_trans n (S n) m).
    + apply le_S. apply le_n.
    + apply H1.    
  Qed.  

Theorem le_mais_l : forall a b,
  a <= a + b.
Proof.
  intros a b.
  induction a as [ | a' IHa].
  - apply O_le_n.
  - simpl. apply n_le_m__Sn_le_Sm. apply IHa.
  Qed.

Theorem mais_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
  intros n1 n2 m Hmais.
  inversion Hmais.
  - split.
    + apply le_mais_l. 
    + rewrite add_comutativo. apply le_mais_l.
  - split. 
     + rewrite H1. apply (le_trans n1 (n1 + n2) m).
       * apply le_mais_l.
       * apply Hmais.
     + rewrite H1.  apply (le_trans n2 (n1 + n2) m).
       * rewrite add_comutativo. apply le_mais_l.
       * apply Hmais.
  Qed.

Theorem mais_le_casos : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.

(* Dica: Pode ser mais fácil de provar por indução em n. *)
Proof.
  intros n.
  induction n as [ | n' IHn].
  - intros m p q H. 
    left. apply O_le_n.
  - intros m p q Hnmpq.
    destruct p as [ | p']. 
    + right. simpl in Hnmpq. simpl in IHn. apply le_S in Hnmpq.
      apply Sn_le_Sm__n_le_m in Hnmpq. apply (le_trans m (n' + m) q).
      * rewrite add_comutativo. apply le_mais_l.
      * apply Hnmpq.
    + simpl in Hnmpq. apply Sn_le_Sm__n_le_m in Hnmpq.
      destruct (IHn m p' q Hnmpq) as [Hn_le_p | Hm_le_q].
      * left. apply n_le_m__Sn_le_Sm. apply Hn_le_p.
      * right. apply Hm_le_q.
      Qed.

Theorem mais_le_compat_esquerda : forall n m p,
  n <= m ->
  p + n <= p + m.
Proof.
  intros n m p Hnm.
  induction p as [ | p' IHp].
  - simpl. apply Hnm.
  - apply n_le_m__Sn_le_Sm in IHp. simpl. apply IHp.
  Qed.

Theorem mais_le_compat_direita : forall n m p,
  n <= m ->
  n + p <= m + p.
Proof.
  intros n m p Hnm.
  destruct p as [ | p'].
  - rewrite add_0_r. rewrite (add_0_r m). apply Hnm.
  - rewrite add_comutativo. rewrite (add_comutativo m (S p')).
    apply mais_le_compat_esquerda. apply Hnm.
    Qed.

Theorem le_mais_trans : forall n m p,
  n <= m ->
  n <= m + p.
Proof.
  intros n m p Hnm.
  apply (le_trans n m (m + p)).
  - apply Hnm.
  - apply le_mais_l.
  Qed.

(* Usando as definições de ge e lt vistas anteriormente: *)
Definition lt (n m : nat) := le (S n) m.
Notation "n < m" := (lt n m).

Definition ge (m n : nat) : Prop := le n m.
Notation "m >= n" := (ge m n).

Theorem lt_ge_casos : forall n m,
  n < m \/ n >= m.
Proof.
  intros n m.
  induction m as [ | m' IHm].
  - right. apply O_le_n.
  - destruct IHm as [ Hnltm | Hngem].
    + left. unfold lt. unfold lt in Hnltm. apply n_le_m__Sn_le_Sm.
       apply le_S in Hnltm. apply Sn_le_Sm__n_le_m in Hnltm.
       apply Hnltm.
    + inversion Hngem.
       * left. unfold lt. apply le_n.
       * right. unfold ge. apply n_le_m__Sn_le_Sm. apply H.
  Qed. 
  
Theorem n_lt_m__n_le_m : forall n m,
  n < m ->
  n <= m.
Proof.
  intros n m Hnm.
  unfold lt in Hnm.
  apply (le_trans n (S n) m).
  - apply le_S. apply le_n.
  - apply Hnm.
  Qed.

Theorem mais_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  intros n1 n2 m Hn1n2m.
  split.
  - unfold lt. unfold lt in Hn1n2m. 
    apply (le_trans (S n1) (S (n1 + n2)) m).
    + apply n_le_m__Sn_le_Sm. apply le_mais_l.
    + apply Hn1n2m.
  - unfold lt. unfold lt in Hn1n2m.
     apply (le_trans (S n2) (S (n1 + n2)) m).
     + apply n_le_m__Sn_le_Sm. rewrite add_comutativo. apply le_mais_l.
     + apply Hn1n2m.
    Qed.

Theorem leb_corretude : forall n m,
  n <=? m = true -> n <= m.
Proof.
  intros n.
  induction n as [ | n' IHn].
  - intros m IHnlebm. apply O_le_n.
  - intros m IHnlebm. destruct m as [ | m'].
    + discriminate IHnlebm.
    + simpl in IHnlebm.
      apply n_le_m__Sn_le_Sm.
      apply IHn.
      apply IHnlebm.
      Qed.

Theorem leb_completude : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
  intros n.
  induction n as [ | n' IHn].
  - intros m Hnlem. reflexivity.
  - intros m Hnlem. destruct m as [ | m'].
   + inversion Hnlem.
   + simpl. apply IHn. apply Sn_le_Sm__n_le_m in Hnlem.
     apply Hnlem.
   Qed.

(* Dica: As duas próximas podem ser facilmente provadas sem usar indução. *)

Theorem leb_sse : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  intros n m.
  split.
  (* -> *)
  - apply leb_corretude.
  (* <- *)
  - apply leb_completude.
  Qed.

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros n m o Hnm Hmo.
  apply leb_corretude in Hnm.
  apply leb_corretude in Hmo.
  apply leb_completude.
  apply (le_trans n m o).
  - apply Hnm.
  - apply Hmo.
  Qed.
  
Module R.
(* Exercício *)
(* Podemos definir relações ternárias (de três lugares), relações quaternárias 
(de quatro lugares), etc., exatamente da mesma maneira que as relações binárias. 
Por exemplo, considere a seguinte relação ternária sobre os números: *)

Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 m n o (H : R m n o ) : R (S m) n (S o)
  | c3 m n o (H : R m n o ) : R m (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
  | c5 m n o (H : R m n o ) : R n m o.

(* Quais das seguintes proposições são demonstráveis?
   - R 1 1 2 (E provável !)
   - R 2 2 6  (Não é provável)

Se removêssemos o construtor c5 da definição de R, o conjunto de proposições 
demonstráveis mudaria? Explique sua resposta brevemente (em 1 frase).
R: Não, pois o conjunto não muda: a comutatividade de m e n já pode ser obtida 
aplicando os construtores c2 e c3 na ordem desejada.

Se removêssemos o construtor c4 da definição de R, o conjunto de proposições 
demonstráveis mudaria? Explique sua resposta brevemente (em 1 frase).
R: Não, pois qualquer proposição provável já pode ser derivada partindo do caso 
base c1 e aplicando c2 e c3 para construir os números ''para a frente'', sem 
nunca precisar do passo de simplificação do c4.   
*)

(* Exercício *)
(* A relação R acima na verdade codifica uma função familiar. Descubra qual é 
essa função; depois, enuncie e prove essa equivalência no Rocq. *)

Definition fR : nat -> nat -> nat :=
  fun a b =>  a +  b.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
  intros m n o. 
  split.
  (* -> *)
  - intros HR. induction HR.
    + reflexivity.
    + simpl. rewrite IHHR. reflexivity.
    + rewrite <- IHHR. unfold fR. rewrite mais_n_Sm. reflexivity.
    + unfold fR. unfold fR in IHHR. simpl in IHHR. injection IHHR as H_igual.
      * rewrite <- mais_n_Sm in H_igual. injection H_igual. intros Hmno.
        apply Hmno.
    + unfold fR. unfold fR in IHHR. rewrite add_comutativo. apply IHHR.
  (* <- *)
  - intros Heq. unfold fR in Heq.
    generalize dependent o.
    induction n as [ | n' IHn]; intros o Heq.
     + (* n = 0 *)
      rewrite add_0_r in Heq.
      generalize dependent o.
      induction m as [ | m' IHm]; intros o Heq.
       * (* m = 0 *)
        rewrite <- Heq. apply c1.
       * (* m = S m' *)
         rewrite <- Heq. apply c2. apply IHm. reflexivity.
     + (* n = S n' *)
      rewrite <- plus_n_Sm in Heq.
      rewrite <- Heq.
      apply c3.
      apply IHn.
      reflexivity.
    Qed.
  
End R.

(* Exercício *)
(* Uma lista é uma subsequência de outra lista se todos os elementos da primeira 
lista ocorrem na mesma ordem na segunda lista, possivelmente com alguns elementos 
extras no meio. Por exemplo:

        [1;2;3] 
é uma subsequência de cada uma das listas:

        [1;2;3]

        [1;1;1;2;2;3]

        [1;2;7;3]

        [5;6;1;9;9;2;7;3;8]

    Mas não é uma subsequência de nenhuma das listas:

        [1;2]

        [1;3]

        [5;6;2;1;7;3;8]

    - Defina uma proposição indutiva subseq sobre list nat que capture o que 
    significa ser uma subsequência. Há várias maneiras corretas de fazer isso. 
    Você deve garantir que sua definição se comporte corretamente em todos os 
    exemplos positivos e negativos acima, mas não precisa provar isso formalmente.

    - Prove subseq_refl de que a relação de subsequência é reflexiva — ou seja, 
    qualquer lista é uma subsequência de si mesma.

    - Prove subseq_app de que para quaisquer listas l1, l2 e l3, se l1 é uma 
    subsequência de l2, então l1 também é uma subsequência de l2 ++ l3.

    - (Mais difícil) Prove subseq_trans de que a relação de subsequência é 
    transitiva — ou seja, se l1 é uma subsequência de l2 e l2 é uma subsequência 
    de l3, então l1 é uma subsequência de l3. *)

Inductive subseq : list nat -> list nat -> Prop :=
  | subseq_nil : subseq [] []
  | subseq_mantem (x : nat) (l1 l2 : list nat )(H: subseq l1 l2) : subseq (x:: l1)(x :: l2)
  | subseq_pula (x : nat)(l1 l2 : list nat)(H: subseq l1 l2) : subseq l1 (x :: l2).

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  intros l. induction l as [ | h t IHl].
  - apply subseq_nil.
  - inversion IHl.
    + apply subseq_mantem. apply subseq_nil.
    + apply subseq_mantem. apply subseq_mantem. apply H1.
    + apply subseq_mantem. rewrite H1. apply IHl.
    Qed.


Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  intros l1 l2 l3 H. 
  induction H as [ | x l1 l2 H IH | x l1 l2 H IH].
  - simpl. induction l3 as [ | h3 t3 IHl3].
    + apply subseq_nil.
    + apply subseq_pula. apply IHl3.
  - simpl. apply subseq_mantem. apply IH.
  - simpl. apply subseq_pula. apply IH.
     Qed.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  intros l1 l2 l3 Hl1l2 Hl2l3.
  generalize dependent l1.
  induction Hl2l3 as [ | x l2' l3' H IH | x l2' l3' H IH].

  - (* subseq_nil *)
    intros l1 H1. inversion H1. apply subseq_nil.

  - (* subseq_mantem *)
    intros l1 H1.
    inversion H1 as [ | x' l1' l2'' Hrel Heq1 Heq2 | x' l1'' l2''' Hrel Heq1 Heq2 ].
    + destruct Heq1. destruct Heq2.
      apply subseq_mantem. apply IH. apply Hrel.
    + destruct Heq2.
      apply subseq_pula. apply IH. apply Hrel.

  - (* subseq_pula *)
    intros l1 H1.
    apply subseq_pula. apply IH. apply H1.
    Qed.

(* Exercício *)
(* Suponha que forneçamos a seguinte definição ao Rocq: 
Inductive R : nat → list nat → Prop :=
  | c1                    : R 0     []
  | c2 n l (H: R n     l) : R (S n) (n :: l)
  | c3 n l (H: R (S n) l) : R n     l.

Quais das seguintes proposições são prováveis?

    - R 2 [1;0] (É provável)

    - R 1 [1;2;1;0] (É provável)

    - R 6 [3;2;1;0] (Não é provável)

*)

(* Exercício *)
(* Defina uma relação binária indutiva relacao_total que vale entre todo par de 
números naturais. *)

Inductive relacao_total : nat -> nat -> Prop :=
  | rel_tot (n m : nat) : relacao_total n m.

Theorem relacao_total_e_total: forall n m, relacao_total n m.
Proof.
  intros n m.
  apply rel_tot.
  Qed.

(* Defina uma relação binária indutiva relacao_vazia (sobre números) que nunca 
vale *)

Inductive relacao_vazia : nat -> nat -> Prop := .

Theorem relacao_vazia_e_vazia : forall n m, ~ relacao_vazia n m.
  Proof.
  intros n m.
  intros H. inversion H.
  Qed.

(******************** Estudo de Caso: Expressões Regulares ********************)

(* Muitos dos exemplos acima foram simples e — no caso da propriedade ev — até 
um pouco artificiais. Para dar uma noção melhor do poder das proposições 
definidas indutivamente, agora mostramos como usá-las para modelar um conceito 
clássico em ciência da computação: expressões regulares. *)

(*** Definições ***)

(* Expressões regulares são uma linguagem natural para descrever conjuntos de 
strings. A sua sintaxe é definida da seguinte forma: *)

Inductive exp_reg (T : Type) : Type :=
  | ConjuntoVazio
  | CadeiaVazia
  | Char (t : T)
  | Concatenar (r1 r2 : exp_reg T)
  | Uniao (r1 r2 : exp_reg T)
  | Estrela (r : exp_reg T).

Arguments ConjuntoVazio {T}.
Arguments CadeiaVazia {T}.
Arguments Char {T} _.
Arguments Concatenar {T} _ _.
Arguments Uniao {T} _ _.
Arguments Estrela {T} _.

(* Note que esta definição é polimórfica: expressões regulares em exp_reg T 
descrevem cadeias com caracteres extraídos de T — que, neste exercício, 
representamos como listas com elementos de T. 

(Nota técnica: Nós nos afastamos levemente da prática padrão ao não exigir que o 
tipo T seja finito. Isso resulta em uma teoria de expressões regulares um pouco 
diferente, mas a diferença não é significativa para os propósitos atuais.)

Nós conectamos expressões regulares e cadeias definindo quando uma expressão 
regular casa com (matches) alguma cadeia.

Informalmente, isso funciona da seguinte forma:

  - A expressão regular ConjuntoVazio não casa com nenhuma cadeia.
  - CadeiaVazia casa com a cadeia vazia [].
  - Char x casa com a cadeia de um único caractere [x].
  - Se er1 casa com c1, e er2 casa com c2, então Concatenar er1 er2 casa com 
    c1 ++ c2.
  - Se pelo menos uma entre er1 e er2 casa com c, então Uniao er1 er2 casa com c.
  - Finalmente, se pudermos escrever alguma cadeia c como a concatenação de uma 
    sequência de cadeias c = c_1 ++ ... ++ c_k, e a expressão er casa com cada 
    uma das cadeias c_i, então Estrela er casa com c.
    
  Em particular, a sequência de cadeias pode estar vazia, de modo que Estrela er 
  sempre casa com a cadeia vazia [], não importa qual seja er.

Podemos traduzir facilmente essa intuição em um conjunto de regras, onde 
escrevemos c =~ er para dizer que er casa com c: 
             	 
         ------------------- (MVazio)   
          [] =~ EmptyStr 	

   	 
        -------------------- (MChar)                
         [x] =~ (Char x) 
             
            c1 =~ er1     c2 =~ er2 
       --------------------------------- (MConcatenar)  
      (c1 ++ c2) =~ (Concatenar er1 er2) 	

               c1 =~ er1 	
        ------------------------- (MUniaoDireita)
          c1 =~ (Uniao er1 er2) 	

              c2 =~ er2 	
        ------------------------- (MUniaoEsquerda)  
          c2 =~ (Uniao er1 er2) 	
   	
        ---------------------- (MEstrela0)
          [] =~ (Estrela er) 	

             c1 =~ er 	
          c2 =~ (Estrela er) 	
       --------------------------- (MSEstrelaConcatenar)  
       (c1 ++ c2) =~ (Estrela er) 	

Isso corresponde diretamente à seguinte definição Indutiva. Usamos a notação 
c =~ er no lugar de exp_match c er. (Ao ''reservar'' a notação antes de definir 
o tipo Indutivo, podemos usá-la na própria definição.) *)

Reserved Notation "c =~ er" (at level 80).

Inductive exp_match {T} : list T ->  exp_reg T -> Prop :=
  | MVazio : [] =~ CadeiaVazia
  | MChar x : [x] =~ (Char x)
  | MConcatenar c1 er1 c2 er2
             (H1 : c1 =~ er1)
             (H2 : c2 =~ er2)
           : (c1 ++ c2) =~ (Concatenar er1 er2)
  | MUniaoEsquerda c1 er1 er2
                (H1 : c1 =~ er1)
              : c1 =~ (Uniao er1 er2)
  | MUniaoDireita c2 er1 er2
                (H2 : c2 =~ er2)
              : c2 =~ (Uniao er1 er2)
  | MEstrela0 er : [] =~ (Estrela er)
  | MEstrelaConcatenar c1 c2 er
                 (H1 : c1 =~ er)
                 (H2 : c2 =~ (Estrela er))
               : (c1 ++ c2) =~ (Estrela er)

    where "c =~ er" := (exp_match c er).

(* Note que essas regras não são exatamente iguais à intuição que fornecemos no 
início da seção. Primeiro, não precisamos incluir uma regra afirmando 
explicitamente que nenhuma cadeia é correspondida por ConjuntoVazio; de fato, a 
sintaxe das definições indutivas nem sequer nos permite fornecer tal ''regra 
negativa''. Nós simplesmente não incluímos nenhuma regra que faria com que o 
ConjuntoVazio correspondesse a alguma cadeia.

Segundo, a intuição que demos para Uniao e Estrela corresponde a dois construtores 
cada: MUniaoEsquerda / MUniaoDireita e MEstrela0 / MEstrelaConcatenar. O resultado 
é logicamente equivalente à intuição original, mas mais conveniente de usar no 
Rocq, uma vez que as ocorrências recursivas de exp_match são fornecidas como 
argumentos diretos para os construtores, facilitando a realização de indução sobre 
a evidência. (Os exercícios exp_match_ex1 e exp_match_ex2 abaixo pedem que você 
prove que os construtores fornecidos na declaração indutiva e aqueles que 
surgiriam de uma transcrição mais literal da intuição são de fato equivalentes.)

Vamos ilustrar essas regras com alguns exemplos. *)

(*** Exemplos ***)
Example exp_reg_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example exp_reg_ex2 : [1; 2] =~ Concatenar (Char 1) (Char 2).
Proof.
  apply (MConcatenar [1]).
  - apply MChar.
  - apply MChar.
Qed.

(* Note como o último exemplo aplica MConcatenar diretamente à cadeia [1]. Como o 
objetivo menciona [1; 2] em vez de [1] ++ [2], o Rocq não conseguiria descobrir 
como dividir a cadeia por conta própria.

Usando inversion, também podemos mostrar que certas cadeias não correspondem a uma 
expressão regular: *)

Example exp_reg_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

(* Podemos definir funções auxiliares para escrever expressões regulares. A função 
exp_reg_de_lista constrói uma expressão regular que corresponde exatamente à cadeia 
que ela recebe como argumento: *)

Fixpoint exp_reg_de_lista {T} (l : list T) :=
  match l with
  | [] => CadeiaVazia
  | x :: l' => Concatenar (Char x) (exp_reg_de_lista l')
  end.

Example exp_reg_ex4 : [1; 2; 3] =~ exp_reg_de_lista [1; 2; 3].
Proof.
  simpl. apply (MConcatenar [1]).
  { apply MChar. }
  apply (MConcatenar [2]).
  { apply MChar. }
  apply (MConcatenar [3]).
  { apply MChar. }
  apply MVazio.
Qed.

(* Também podemos provar fatos gerais sobre exp_match. Por exemplo, o lema a 
seguir mostra que toda cadeia c correspondida por er também é correspondida por 
Estrela er. *)

Lemma MEstrela1 :
  forall T c (er : exp_reg T) ,
    c =~ er ->
    c =~ Estrela er.
Proof.
  intros T c er H.
  rewrite <- (juntar_nil_r _ c).
  apply MEstrelaConcatenar.
  - apply H.
  - apply MEstrela0.
Qed.

(* (Note o uso de juntar_nil_r para alterar o objetivo do teorema exatamente para 
o formato esperado por MEstrelaConcatenar.) *)

(* Exercício *)
(* Os seguintes lemas mostram que a intuição sobre a correspondência fornecida no 
início do capítulo pode ser obtida a partir da definição indutiva formal. *)

Lemma ConjuntoVazio_e_vazio  : forall T (c : list T),
  ~ (c =~ ConjuntoVazio).
Proof.
  intros T c H.
  inversion H.
  Qed.

Lemma MUniao' : forall T (c : list T) (er1 er2 : exp_reg T),
  c =~ er1 \/ c =~ er2 ->
  c =~  Uniao er1 er2.
Proof.
  intros T c er1 er2 H.
  destruct H as [Her1 | Her2].
  - apply (MUniaoEsquerda c er1 er2 Her1).
  - apply (MUniaoDireita c er1 er2 Her2).
  Qed. 

(* O próximo lema é enunciado em termos da função fold do capítulo sobre 
Polimorfismo (Poly): se ss : list (list T) representa uma sequência de cadeias s_1,
..., s_n, então fold app ss [] é o resultado de concatenar todas elas juntas. *)

Definition juntar {T : Type} (l1 l2 : list T) : list T :=
  l1 ++ l2.

Lemma MEstrela' : forall T (cc : list (list T)) (er : exp_reg T),
  (forall c, In c cc -> c =~ er) ->
  fold juntar cc [] =~ Estrela er. 
Proof.
  intros T cc er H.
  induction cc as [ | h t IHcc].
  - simpl. apply MEstrela0.
  - simpl. apply (MEstrelaConcatenar h (fold juntar t [])).
    + apply H. simpl. left. reflexivity.
    + apply IHcc. intros c HIn. apply H. simpl. right. apply HIn.
    Qed. 

(* Exercício *)
(* Acontece que o construtor CadeiaVazia na verdade não é necessário, já que a 
expressão regular que corresponde à cadeia vazia também pode ser definida a partir 
de Estrela e ConjuntoVazio: *)

Definition CadeiaVazia' {T:Type} := @Estrela T (ConjuntoVazio).

(* Enuncie e prove que esta definição de CadeiaVazia' corresponde exatamente às 
mesmas cadeias que o construtor CadeiaVazia. *)
Lemma cadeia_vazia_equiv : forall T (c : list T),
  c =~ CadeiaVazia <-> c =~ CadeiaVazia'.
Proof.
  intros T c.
  split.
  - intros H. inversion H. unfold CadeiaVazia'. apply MEstrela0.
  - intros H. inversion H. 
    + apply MVazio.
    + inversion H2.
    Qed.

(* Como a definição de exp_match tem uma estrutura recursiva, podemos esperar que 
provas envolvendo expressões regulares frequentemente exijam indução sobre evidências.

Por exemplo, suponha que queiramos provar o seguinte fato intuitivo que é verdadeiro 
em nosso cenário simples: Se uma cadeia c for combinada (matched) por uma expressão 
regular er, então todos os elementos de c devem ocorrer como literais de caractere 
em algum lugar de er.

Para enunciar isso como um teorema, primeiro definimos uma função er_chars que lista 
todos os caracteres que ocorrem em uma expressão regular: *)

Fixpoint er_chars {T} (er : exp_reg T) : list T :=
  match er with
  | ConjuntoVazio => []
  | CadeiaVazia => []
  | Char x => [x]
  | Concatenar er1 er2 => er_chars er1 ++ er_chars er2
  | Uniao er1 er2 => er_chars er1 ++ er_chars er2
  | Estrela er => er_chars er
  end.

(* Agora, o teorema principal: *)

Theorem in_re_match : forall T (c : list T) (er : exp_reg T) (x : T),
  c =~ er ->
  In x c ->
  In x (er_chars er).
Proof.
  intros T c er x Hmatch Hin.
  induction Hmatch
    as [ | x'
         | c1 er1 c2 er2 Hmatch1 IH1 Hmatch2 IH2
         | c1 er1 er2 Hmatch IH | c2 er1 er2 Hmatch IH
         | er | c1 c2 er Hmatch1 IH1 Hmatch2 IH2].
  (* TRABALHADO EM AULA *)
  - (* MVazio *)
    simpl in Hin. destruct Hin.
  - (* MChar *)
    simpl. simpl in Hin.
    apply Hin.
  - (* MConcatenar *)
    simpl.

(* Algo interessante acontece no caso MConcatenar. Nós obtemos duas hipóteses de 
indução: Uma que se aplica quando x ocorre em c1 (que é combinada por er1), e uma 
segunda que se aplica quando x ocorre em c2 (combinada por er2).*)

    rewrite In_juntar_sse in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUniaoEsquerda *)
    simpl. rewrite In_juntar_sse.
    left. apply (IH Hin).
  - (* MUniaoDireita *)
    simpl. rewrite In_juntar_sse.
    right. apply (IH Hin).
  - (* MEstrela0 *)
    destruct Hin.
  - (* MEstrelaConcatenar *)
    simpl.

(* Aqui novamente obtemos duas hipóteses de indução, e elas ilustram por que 
precisamos de indução sobre evidências para exp_match, em vez de indução sobre a 
expressão regular er: esta última forneceria apenas uma hipótese de indução para 
cadeia que combinam com er, o que não nos permitiria raciocinar sobre o caso In x c2, 
onde c2 combina apenas com Estrela er e não com er. *)
    rewrite In_juntar_sse in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

(* Exercício *)
(* Escreva uma função recursiva er_nao_vazia que testa se uma expressão regular 
combina com alguma string. Prove que sua função está correta. *)

Fixpoint er_nao_vazia {T : Type} (er : exp_reg T) : bool :=
    match er with
    | ConjuntoVazio => false
    | CadeiaVazia => true
    | Char x => true
    | Concatenar er1 er2 => er_nao_vazia er1 && er_nao_vazia er2
    | Uniao er1 er2 => er_nao_vazia er1 || er_nao_vazia er2
    | Estrela er => true
    end.

Lemma er_nao_vazia_correto : forall T (er : exp_reg T),
  (exists c, c =~ er) <-> er_nao_vazia er = true.
Proof.
  intros T er.
  split.
  (* -> *)
  - intros H. inversion H. induction H0 as [ | x'
         | c1 er1 c2 er2 Hmatch1 IH1 Hmatch2 IH2
         | c1 er1 er2 Hmatch IH | c2 er1 er2 Hmatch IH
         | er | c1 c2 er Hmatch1 IH1 Hmatch2 IH2]. 
     (* MCadeiaVazia*)
    + simpl. reflexivity.
     (* MChar *)
    + simpl. reflexivity.
    (* MConcatenar *)
    + simpl. rewrite IH1. rewrite IH2. reflexivity .
      * exists c2. apply Hmatch2.
      * exists c1. apply Hmatch1.
    (* MUniaoEsquerda *)
    + simpl. rewrite IH. reflexivity.
      * exists c1. apply Hmatch.
    (* MUniaoDireita *)
    + simpl. rewrite IH. destruct (er_nao_vazia er1).
      * reflexivity.
      * reflexivity.
      * exists c2. apply Hmatch.
    (* MEstrela0 *)
    + reflexivity.
    (* MEstrelaConcatenar *)
    + reflexivity.
   
   (* <- *)
   - intros H. induction  er as [ | | x' | er1 IHer1 er2 IHer2 
         | er1 IHer1 er2 IHer2| er].
      (* ConjuntoVazio *)
      + discriminate H.
      (* CadeiaVazia *)
      + exists []. apply MVazio.
      (* Char *)
      + exists [x']. apply MChar.
      (* Concatenar *)
      + destruct (er_nao_vazia er1) eqn:E1. destruct (er_nao_vazia er2) eqn:E2. 
        * destruct (IHer1 eq_refl) as [c1 Hmatch1]. 
          destruct (IHer2 eq_refl) as [c2 Hmatch2].
          exists (c1 ++ c2). apply MConcatenar. apply Hmatch1. apply Hmatch2.
        * simpl in H. rewrite E1, E2 in H. discriminate H.
        * simpl in H. rewrite E1 in H. discriminate H.
      (* Uniao *)
      + destruct (er_nao_vazia er1) eqn:E1. destruct (er_nao_vazia er2) eqn:E2. 
        * destruct (IHer1 eq_refl) as [c1 Hmatch1]. exists c1. 
          apply MUniaoEsquerda. apply Hmatch1.
        * destruct (IHer1 eq_refl) as [c1 Hmatch1]. exists c1. 
          apply MUniaoEsquerda. apply Hmatch1.
        * destruct (er_nao_vazia er2) eqn:E2.
          -- destruct (IHer2 eq_refl) as [c2 Hmatch2]. exists c2. 
           apply MUniaoDireita. apply Hmatch2.
          -- simpl in H. rewrite E1, E2 in H. discriminate H.
      (* Estrela *)
      + exists []. apply MEstrela0.
    Qed.

(*** A Tática remember *)

(* Uma característica potencialmente confusa da tática induction é que ela permite 
que você tente realizar uma indução sobre um termo que não é suficientemente geral. 
O efeito disso é perder informações (assim como o destruct sem uma cláusula eqn: 
pode fazer), deixando você incapaz de concluir a demonstração. Aqui está um exemplo: *)

Lemma estrela_concatenar: forall T (c1 c2 : list T) (er : exp_reg T),
  c1 =~ Estrela er ->
  c2 =~ Estrela er ->
  c1 ++ c2 =~ Estrela er.
Proof.
  intros T c1 c2 er H1.

(* Agora, apenas fazer um inversion em H1 não nos levará muito longe nos casos 
recursivos. (Experimente!). Portanto, precisamos de indução (sobre a evidência). 
Aqui está uma primeira tentativa ingênua. *)
   induction H1
    as [ |x'|c1 er1 c2' er2 Hmatch1 IH1 Hmatch2 IH2
        |c1 er1 er2 Hmatch IH|er1 c2' er2 Hmatch IH
        |er''|c1 c2' er'' Hmatch1 IH1 Hmatch2 IH2].

(* Mas agora, embora tenhamos sete casos (como esperaríamos pela definição de 
exp_match), perdemos um pedaço muito importante de informação de H1: o fato de que 
c1 correspondia a algo da forma Estrela er. Isso significa que temos que fornecer 
demonstrações para todos os sete construtores dessa definição, mesmo que todos, 
exceto dois deles (MEstrela0 e MEstrelaConcatenar), sejam contraditórios. Ainda 
conseguimos fazer a demonstração passar para alguns construtores, como MVazio... *)
     - (* MVazio *)
    simpl. intros H. apply H.


(* ... mas a maioria dos casos fica travada. Para MChar, por exemplo, devemos 
mostrar

                  c2 =~ Char x' →
                  x'::c2 =~ Char x' 

o que é claramente impossível. *)

        - (* MChar. *) intros H. simpl. (* Estamos presos... *)
Abort.

(* O problema aqui é que a indução sobre uma hipótese do tipo Prop só funciona 
corretamente com hipóteses que sejam 'totalmente gerais', ou seja, aquelas em que 
todos os argumentos são apenas variáveis, em vez de expressões mais específicas 
como Estrela er.

(A este respeito, a indução sobre evidências se comporta mais como o destruct sem eqn 
do que como o inversion.)

Uma maneira possível, porém deselegante, de resolver esse problema é 'generalizar 
manualmente' sobre as expressões problemáticas, adicionando hipóteses de igualdade 
explícitas ao lema: *)

Lemma estrela_concatenar: forall T (c1 c2 : list T) (er er' : exp_reg T),
  er' = Estrela er ->
  c1 =~ er' ->
  c2 =~ Estrela er ->
  c1 ++ c2 =~ Estrela er.

(* Agora podemos prosseguir realizando a indução sobre a evidência diretamente, 
porque o argumento da primeira hipótese é suficientemente geral, o que significa 
que podemos descartar a maioria dos casos invertendo a igualdade er' = Estrela er 
no contexto. Isso funciona, mas torna o enunciado do lema um pouco feio. Felizmente, 
há uma maneira melhor... *)
Abort.

(* A tática remember e as x eqn:Eq faz com que o Rocq (1) substitua todas as 
ocorrências da expressão e pela variável x, e (2) adicione uma equação Eq : x = e 
ao contexto. Veja como podemos usá-la para demonstrar o resultado acima: *)

Lemma estrela_concatenar: forall T (c1 c2 : list T) (er : exp_reg T),
  c1 =~ Estrela er ->
  c2 =~ Estrela er ->
  c1 ++ c2 =~ Estrela er.
Proof.
  intros T c1 c2 er H1.
  remember (Estrela er) as er' eqn:Eq.

(* Agora temos Eq : er' = Estrela er *)
  induction H1
    as [ |x'|c1 er1 c2' er2 Hmatch1 IH1 Hmatch2 IH2
        |c1 er1 er2 Hmatch IH|er1 c2' er2 Hmatch IH
        |er''|c1 c2' er'' Hmatch1 IH1 Hmatch2 IH2].
      
(* O Eq é contraditório na maioria dos casos, o que nos permite concluir 
imediatamente. *)

  - (* MVazio *)discriminate.
  - (* MChar *) discriminate.
  - (* MConcatenar *) discriminate.
  - (* MUniaoEsquerda *) discriminate.
  - (* MUniaoDireita *) discriminate.

(* Os casos interessantes são aqueles que correspondem a Estrela. *)
  - (* MEstrela0 *)
    intros H. apply H.
  - (* MEstrelaConcatenar *)
    intros H1. rewrite <- app_assoc.
    apply MEstrelaConcatenar.
    + apply Hmatch1.
    + apply IH2.
      * apply Eq.
      * apply H1.

(* Note que a hipótese de indução IH2 no caso MEstrelaConcatenar menciona uma 
premissa adicional Estrela er'' = Estrela er, que resulta da igualdade gerada pelo 
remember. *)

Qed.

(* Exercício *)
(* O lema MEstrela'' abaixo (combinado com sua recíproca, o exercício MEstrela' 
acima) mostra que nossa definição de exp_match para Estrela é equivalente à 
informal dada anteriormente. *)

Lemma MEstrela'' : forall T (c : list T) (er : exp_reg T),
  c =~ Estrela er ->
  exists cc : list (list T),
    c = fold juntar cc []
    /\ forall c', In c' cc -> c' =~ er.
Proof.
  intros T c er H1.
  remember (Estrela er) as er' eqn:Eq.
  induction H1 as [ |x'|c1 er1 c2' er2 Hmatch1 IH1 Hmatch2 IH2
        |c1 er1 er2 Hmatch IH|er1 c2' er2 Hmatch IH
        |er''|c1 c2' er'' Hmatch1 IH1 Hmatch2 IH2].
  (* MVazio *)
  - discriminate.
  (* MChar *)
  - discriminate.
  (* MConcatenar *)
  - discriminate.
  (* MUniaoEsquerda *)
  - discriminate.
  (* MUniaoDireita *)
  - discriminate.
  (* MEstrela0*)
  - exists []. simpl. split.
    + reflexivity.
    + intros c H. destruct H as [].
  (* MEstrelaConcatenar *)
  - inversion Eq. 
    + rewrite H0 in IH1, IH2. destruct (IH2 eq_refl) as [cc [Heq Hall]].
      * exists (c1 :: cc). split.
        ++  simpl. rewrite <- Heq. unfold juntar. reflexivity.
        ++ simpl. rewrite H0 in Hmatch1. intros c' H. destruct H as [H1 | H2].
           ** rewrite <- H1. apply Hmatch1.
           ** apply Hall. apply H2.
Qed.

(*** O Lema do Bombeamento ''Fraco'' ***)

(* Um dos primeiros teoremas realmente interessantes na teoria das expressões 
regulares é o chamado lema do bombeamento (pumping lemma), que afirma, informalmente, 
que qualquer cadeia c suficientemente longa que corresponda a uma expressão regular 
er pode ser 'bombeada' repetindo alguma seção intermediária de c um número 
arbitrário de vezes para produzir uma nova cadeia que também corresponda a er. 
Por questão de simplicidade, este exercício considera um teorema um pouco mais 
fraco do que o normalmente enunciado em cursos de teoria de autômatos — daí o nome 
bombeamento_fraco. A versão mais forte pode ser encontrada mais abaixo.

Para começar, precisamos definir 'suficientemente longa'. Como estamos trabalhando 
em uma lógica construtiva, na verdade precisamos ser capazes de calcular, para cada 
expressão regular er, um comprimento mínimo para as cadeias c de modo a garantir a 
'bombeabilidade'. *)

Module Bombeamento.
Fixpoint constante_de_bombeamento {T} (er : exp_reg T) : nat :=
  match er with
  | ConjuntoVazio => 1
  | CadeiaVazia => 1
  | Char _ => 2
  | Concatenar er1 er2 =>
      constante_de_bombeamento er1 + constante_de_bombeamento er2
  | Uniao er1 er2 =>
      constante_de_bombeamento er1 + constante_de_bombeamento er2
  | Estrela r => constante_de_bombeamento r
  end.

(* Você pode achar estes lemas sobre a constante de bombeamento úteis ao demonstrar 
o lema do bombeamento abaixo. *)

Lemma constante_de_bombeamento_maior_igual_1 :
  forall T (er : exp_reg T),
    constante_de_bombeamento er >= 1.
Proof.
  intros T er. induction er.
  - (* ConjuntoVazio *)
    apply le_n.
  - (* CadeiaVazia *)
    apply le_n.
  - (* Char *)
    apply le_S. apply le_n.
  - (* Concatenar *)
    simpl.
    apply le_trans with (n:=constante_de_bombeamento er1).
    apply IHer1. apply le_mais_l.
  - (* Uniao *)
    simpl.
    apply le_trans with (n:=constante_de_bombeamento er1).
    apply IHer1. apply le_mais_l.
  - (* Estrela *)
    simpl. apply IHer.
Qed.

Lemma bombeamento_constante_0_falso :
  forall T (er : exp_reg T),
    constante_de_bombeamento er = 0 -> False.
Proof.
  intros T er H.
  assert (Hp1 : constante_de_bombeamento er >= 1).
  { apply constante_de_bombeamento_maior_igual_1. }
  rewrite H in Hp1. inversion Hp1.
Qed.

(* Em seguida, é útil definir uma função auxiliar que repete uma cadeia 
(concatenando-a consigo mesma) um determinado número de vezes. *)

Fixpoint nconc {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ nconc n' l
  end.

(* Este lema auxiliar também pode ser útil na sua demonstração do lema do 
bombeamento. *)

Lemma nconc_mais: forall T (n m : nat) (l : list T),
  nconc (n + m) l = nconc n l ++ nconc m l.
Proof.
  intros T n m l.
  induction n as [ |n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma conc_estrela :
  forall T m c1 c2 (er : exp_reg T),
    c1 =~ er -> c2 =~ Estrela er ->
    nconc m c1 ++ c2 =~ Estrela er.
Proof.
  intros T m c1 c2 er Hc1 Hc2.
  induction m.
  - simpl. apply Hc2.
  - simpl. rewrite <- app_assoc. 
    apply MEstrelaConcatenar.
    + apply Hc1.
    + apply IHm.
Qed.

(* O próprio lema do bombeamento (fraco) diz que, se c =~ er e se o comprimento de 
c for pelo menos a constante de bombeamento de er, então c pode ser dividido em 
três subcadeias c1 ++ c2 ++ c3 de tal forma que c2 pode ser repetido qualquer 
número de vezes e o resultado, quando combinado com c1 e c3, ainda corresponderá a 
er. Como também é garantido que c2 não é a cadeia vazia, isso nos dá uma maneira 
(construtiva!) de gerar cadeias correspondentes a er tão longas quanto quisermos.

Esta demonstração é bastante longa, então, para torná-la mais gerenciável, nós a 
dividimos em várias subdemonstrações, que depois montamos para provar o lema 
principal.

Seu trabalho é completar as demonstrações dos lemas auxiliares; o lema principal 
depende deles. Vários lemas sobre le (menor ou igual) que estavam em um exercício 
opcional mais cedo neste capítulo podem ser úteis aqui — em particular, lt_ge_casos 
e mais_le. *)

Lemma bombeamento_fraco_char : forall (T : Type) (x : T),
  constante_de_bombeamento (Char x) <= length [x] ->
  exists c1 c2 c3 : list T,
    [x] = c1 ++ c2 ++ c3 /\
    c2 <> [ ] /\
    (forall m : nat, c1 ++ nconc m c2 ++ c3 =~ Char x).
Proof.
  intros T x H. simpl in H. inversion H. inversion H2.
  Qed.

(* Lema Auxiliar - de Polimorfismo *)
Lemma juntar_tamanho : forall (X : Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
  
Proof.
  intros X l1 l2.
  induction l1 as [ | h1 t1 IHl1].
  - reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.

(* Lema Auxiliar *)
Lemma cancela_soma_esquerda : forall n m p,
  n + m <= n + p -> m <= p.
Proof.
  induction n as [ | n' IH].
  - intros m p H. simpl in H. apply H.
  - intros m p H. simpl in H. apply IH. apply Sn_le_Sm__n_le_m. apply H.
Qed.

Lemma bombeamento_fraco_concatenar : forall (T : Type)
                         (c1 c2 : list T) (er1 er2 : exp_reg T),
  c1 =~ er1 ->
  c2 =~ er2 ->
  (constante_de_bombeamento er1 <= length c1 ->
  exists c2 c3 c4 : list T,
    c1 = c2 ++ c3 ++ c4 /\
    c3 <> [ ] /\
    (forall m : nat, c2 ++ nconc m c3 ++ c4 =~ er1)) ->
  (constante_de_bombeamento er2 <= length c2 ->
    exists c1 c3 c4 : list T,
      c2 = c1 ++ c3 ++ c4 /\
      c3 <> [ ] /\
      (forall m : nat, c1 ++ nconc m c3 ++ c4 =~ er2)) ->
  constante_de_bombeamento (Concatenar er1 er2) <= length (c1 ++ c2) ->
  exists c0 c3 c4 : list T,
    c1 ++ c2 = c0 ++ c3 ++ c4 /\
    c3 <> [ ] /\
    (forall m : nat, c0 ++ nconc m c3 ++ c4 =~ Concatenar er1 er2).
Proof.
  simpl. intros T c1 c2 er1 er2 Hmatch1 Hmatch2 IH1 IH2 Hlen.
  assert (H : constante_de_bombeamento er1 <= length c1 \/
            constante_de_bombeamento er2 <= length c2).
{
  destruct (lt_ge_casos (constante_de_bombeamento er1) (length c1)) as [Hlt | Hge].
  - left. apply n_lt_m__n_le_m. apply Hlt.
  - right.
    rewrite juntar_tamanho in Hlen.
    apply mais_le_compat_direita with (p := constante_de_bombeamento er2) in Hge.
    (* Hge : length c1 + constante_de_bombeamento er2
             <= constante_de_bombeamento er1 + constante_de_bombeamento er2 *)
    assert (Hcomb : length c1 + constante_de_bombeamento er2
                    <= length c1 + length c2).
    { apply (le_trans _ (constante_de_bombeamento er1 + constante_de_bombeamento er2)).
      - apply Hge.
      - apply Hlen. }
    apply cancela_soma_esquerda in Hcomb.
    apply Hcomb.
}
  destruct H as [Hle | Hle].

- (* bomb er1 <= length c1: quebra c1 *)
  destruct (IH1 Hle) as [c2' [c3' [c4' [Heq [Hne Hall]]]]].
  exists c2', c3', (c4' ++ c2).
  split.
  + rewrite Heq.
    rewrite app_assoc.
    rewrite app_assoc.
    rewrite <- app_assoc.
    reflexivity.
  + split.
    * apply Hne.
    * intros m.
      assert (Heq2 : c2' ++ nconc m c3' ++ c4' ++ c2
                    = (c2' ++ nconc m c3' ++ c4') ++ c2).
      { rewrite app_assoc. rewrite app_assoc. rewrite app_assoc.
reflexivity. }
      rewrite Heq2.
      apply MConcatenar.
      -- apply Hall.
      -- apply Hmatch2.

- (* bomb er2 <= length c2: quebra c2 *)
  destruct (IH2 Hle) as [c1' [c3' [c4' [Heq [Hne Hall]]]]].
  exists (c1 ++ c1'), c3', c4'.
  split.
  + rewrite Heq.
    rewrite app_assoc.
    reflexivity.
  + split.
    * apply Hne.
    * intros m.
      assert (Heq2 : (c1 ++ c1') ++ nconc m c3' ++ c4'
                    = c1 ++ (c1' ++ nconc m c3' ++ c4')).
      { rewrite app_assoc. rewrite app_assoc. rewrite <- app_assoc.
       reflexivity. }
      rewrite Heq2.
      apply MConcatenar.
      -- apply Hmatch1.
      -- apply Hall.
Qed.
  
Lemma bombeamento_fraco_uniao_esquerda : forall T (c1 : list T) (er1 er2 : exp_reg T),
  c1 =~ er1 ->
  (constante_de_bombeamento er1 <= length c1 ->
    exists c2 c3 c4 : list T,
      c1 = c2 ++ c3 ++ c4 /\
      c3 <> [ ] /\
      (forall m : nat, c2 ++ nconc m c3 ++ c4 =~ er1)) ->
  constante_de_bombeamento (Uniao er1 er2) <= length c1 ->
  exists c0 c2 c3 : list T,
    c1 = c0 ++ c2 ++ c3 /\
    c2 <> [ ] /\
    (forall m : nat, c0 ++ nconc m c2 ++ c3 =~ Uniao er1 er2).
Proof.
  simpl. intros T c1 er1 er2 Hmatch IH Hlen.
  assert (H : constante_de_bombeamento er1 <= length c1).
  {
     apply (le_trans _ (constante_de_bombeamento er1 + constante_de_bombeamento er2)).
     - apply le_mais_l.
     - apply Hlen.
  }
   destruct (IH H) as [c2' [c3' [c4' [Heq [Hne Hall]]]]].
   exists c2', c3', c4'.
   split.
   - apply Heq.
   - split.
    + apply Hne.
    + intros m. apply MUniaoEsquerda. apply Hall.
  Qed.
  

Lemma bombeamento_fraco_uniao_direita : forall T (c2 : list T) (er1 er2 : exp_reg T),
  c2 =~ er2 ->
  (constante_de_bombeamento  er2 <= length c2 ->
    exists c1 c3 c4 : list T,
      c2 = c1 ++ c3 ++ c4 /\
      c3 <> [ ] /\
      (forall m : nat, c1 ++ nconc m c3 ++ c4 =~ er2)) ->
  constante_de_bombeamento  (Uniao er1 er2) <= length c2 ->
  exists c1 c0 c3 : list T,
    c2 = c1 ++ c0 ++ c3 /\
    c0 <> [ ] /\
    (forall m : nat, c1 ++ nconc m c0 ++ c3 =~ Uniao er1 er2).
Proof.
  (* Simétrico ao anterior... *)
  simpl. intros T c2 er1 er2 Hmatch IH Hlen.
   assert (H : constante_de_bombeamento er2 <= length c2).
  {
     apply (le_trans _ (constante_de_bombeamento er1 + constante_de_bombeamento er2)).
     rewrite add_comutativo. apply le_mais_l. apply Hlen.
  }
    destruct (IH H) as [c1' [c3' [c4' [Heq [Hne Hall]]]]].
    exists c1', c3', c4'.
    split.
    - apply Heq.
    - split.
      + apply Hne.
      + intros m. apply MUniaoDireita. apply Hall.
      Qed.
  
Lemma bombeamento_fraco_estrela_zero : forall T (er : exp_reg T),
  constante_de_bombeamento (Estrela er) <= @length T [] ->
  exists c1 c2 c3 : list T,
    [ ] = c1 ++ c2 ++ c3 /\
    c2 <> [ ] /\
    (forall m : nat, c1 ++ nconc m c2 ++c3 =~ Estrela er).
Proof.
  intros T er Hlen.
  assert (Hineq : forall (er : exp_reg T), constante_de_bombeamento er <> 0). 
    {       
      intros er'. induction er' as [ | | x | er1 IH1 er2 IH2 | er1 IH1 er2 IH2 | er1 IH1].
      - discriminate.
      - discriminate.
      - discriminate.
      - simpl. destruct (constante_de_bombeamento er1) eqn:E1.
        + exfalso. apply IH1. reflexivity.
        + discriminate.
      - simpl. destruct (constante_de_bombeamento er1) eqn:E1.
        + exfalso. apply IH1. reflexivity.
        + discriminate.
      - simpl. apply IH1. 
   }
    exfalso. 
    simpl in Hlen.
    destruct (constante_de_bombeamento er) eqn:E.
    - apply (Hineq er). apply E.
    - inversion Hlen.
    Qed.

  
(* Auxiliar 1: a ''volta'' construtiva do MEstrela'' — se todo elemento de cc
   casa com er, a concatenação de todos eles casa com Estrela er. *)
Lemma fold_estrela : forall T (er : exp_reg T) (cc : list (list T)),
  (forall c', In c' cc -> c' =~ er) ->
  fold juntar cc [] =~ Estrela er.
Proof.
  intros T er cc.
  induction cc as [ | h t IH].
  - intros _. simpl. apply MEstrela0.
  - intros Hall. simpl. apply MEstrelaConcatenar.
    + apply Hall. left. reflexivity.
    + apply IH. intros c' Hin. apply Hall. right. apply Hin.
Qed.

(* Auxiliar 2: se a concatenação de cc é não-vazia, existe um elemento
   NÃO-VAZIO x (pulando os vazios do início) tal que fold = x ++ resto,
   com resto ainda casando com Estrela er. *)
Lemma extrai_nao_vazio : forall T (er : exp_reg T) (cc : list (list T)),
  (forall c', In c' cc -> c' =~ er) ->
  fold juntar cc [] <> [] ->
  exists x resto, fold juntar cc [] = x ++ resto /\
                  x <> [] /\ x =~ er /\ resto =~ Estrela er.
Proof.
  intros T er cc.
  induction cc as [ | h t IH].
  - intros _ Hne. exfalso. apply Hne. reflexivity.
  - intros Hall Hne.
    destruct h as [ | a h'].
    + (* h vazio: contribui nada, pula pra IH em t *)
      simpl in Hne. simpl.
      apply IH.
      * intros c' Hin. apply Hall. right. apply Hin.
      * apply Hne.
    + (* h = a::h' <> []: é o pedaço bombeável *)
      exists (a :: h'), (fold juntar t []).
      simpl. split.
      * reflexivity.
      * split.
        -- discriminate.
        -- split.
           ++ apply Hall. left. reflexivity.
           ++ apply fold_estrela. intros c' Hin. apply Hall. right. apply Hin.
Qed.

Lemma bombeamento_fraco_estrela_concatenar : forall T (c1 c2 : list T) (er : exp_reg T),
  c1 =~ er ->
  c2 =~ Estrela er ->
  (constante_de_bombeamento er <= length c1 ->
    exists c2 c3 c4 : list T,
      c1 = c2 ++ c3 ++ c4 /\ c3 <> [ ] /\
      (forall m : nat, c2 ++ nconc m c3 ++ c4 =~ er)) ->
  (constante_de_bombeamento (Estrela er) <= length c2 ->
    exists c1 c3 c4 : list T,
      c2 = c1 ++ c3 ++ c4 /\ c3 <> [ ] /\
      (forall m : nat, c1 ++ nconc m c3 ++ c4 =~ Estrela er)) ->
  constante_de_bombeamento (Estrela er) <= length (c1 ++ c2) ->
  exists c0 c3 c4 : list T,
    c1 ++ c2 = c0 ++ c3 ++ c4 /\ c3 <> [ ] /\
    (forall m : nat, c0 ++ nconc m c3 ++ c4 =~ Estrela er).
Proof.
  simpl. intros T c1 c2 er Hmatch1 Hmatch2 IH1 IH2 Hlen.
  rewrite juntar_tamanho in *.
  assert (Hc1er1 : length c1 = 0
                \/ (length c1 <> 0 /\ length c1 < constante_de_bombeamento er)
                \/ constante_de_bombeamento er <= length c1).
  { destruct c1 as [ | h c1'].
    - left. reflexivity.
    - right. destruct (lt_ge_casos (length (h :: c1')) (constante_de_bombeamento er)) as [Hlt | Hge].
      + left. split.
        * discriminate.
        * apply Hlt.
      + right. unfold ge in Hge. apply Hge.
  }
  destruct Hc1er1 as [Heq | [Hineq | Hbomb]].

  - (* CASO 1: c1 vazia — usa IH2 direto *)
    rewrite Heq in Hlen. simpl in Hlen.
    destruct (IH2 Hlen) as [c1' [c3' [c4' [Heq2 [Hne Hall]]]]].
    assert (Hc1nil : c1 = []).
    { destruct c1 as [ | h t].
      - reflexivity.
      - discriminate Heq. }
    rewrite Hc1nil. simpl.
    exists c1', c3', c4'.
    split. { apply Heq2. }
    split. { apply Hne. }
    apply Hall.

  - (* CASO 2: c1 não-vazia mas curta — o caso difícil *)
    destruct Hineq as [H0 Her].
    (* Passo 1: mostra que c2 não pode ser vazia, ''cancelando'' c1 da soma *)
    assert (Hstep : length c1 + 1 <= length c1 + length c2).
    { rewrite add_comutativo.
      apply (le_trans _ (constante_de_bombeamento er)).
      - apply Her.
      - apply Hlen. }
    apply cancela_soma_esquerda in Hstep.
    assert (Hc2ne : c2 <> []).
    { intros Hc2eq. rewrite Hc2eq in Hstep. simpl in Hstep. inversion Hstep. }
    (* Passo 2: decompõe c2 em blocos via MEstrela'' *)
    destruct (MEstrela'' T c2 er Hmatch2) as [cc [Hccfold Hccall]].
    rewrite Hccfold in Hc2ne.
    (* Passo 3: acha o primeiro bloco não-vazio dentro de cc *)
    destruct (extrai_nao_vazio T er cc Hccall Hc2ne)
      as [x [resto [Hxeq [Hxne [Hxer Hrestoer]]]]].
    exists c1, x, resto.
    split. { rewrite Hccfold. rewrite Hxeq. reflexivity. }
    split. { apply Hxne. }
    intros m.
    assert (Hxm : nconc m x ++ resto =~ Estrela er).
    { induction m as [ | m' IHm].
      - simpl. apply Hrestoer.
      - simpl. 
        (* Reassocia para separar o 'x' do restante *)
        rewrite <- app_assoc.
        apply MEstrelaConcatenar.
        + apply Hxer.
        + apply IHm. }
    apply MEstrelaConcatenar.
    + apply Hmatch1.
    + apply Hxm.

  - (* CASO 3: c1 longa o bastante — igual ao caso Concatenar, mas MEstrelaConcatenar no final *)
    destruct (IH1 Hbomb) as [c2' [c3' [c4' [Heq [Hne Hall]]]]].
    exists c2', c3', (c4' ++ c2).
    split.
    { rewrite Heq. rewrite app_assoc. rewrite app_assoc. rewrite <- app_assoc.
      reflexivity. }
    split. { apply Hne. }
    intros m.
    assert (Heq2 : c2' ++ nconc m c3' ++ c4' ++ c2
                  = (c2' ++ nconc m c3' ++ c4') ++ c2).
    { rewrite app_assoc. rewrite app_assoc. rewrite app_assoc. reflexivity. }
    rewrite Heq2.
    apply MEstrelaConcatenar.
    + apply Hall.
    + apply Hmatch2.
Qed.

Lemma bombeamento_fraco : forall T (er : exp_reg T) c,
  c =~ er ->
  constante_de_bombeamento er <= length c ->
  exists c1 c2 c3,
    c = c1 ++ c2 ++ c3 /\
    c2 <> [] /\
    forall m, c1 ++ nconc m c2 ++ c3 =~ er.
Proof.
  intros T er c Hmatch.
  induction Hmatch
    as [ | x | c1 er1 c2 er2 Hmatch1 IH1 Hmatch2 IH2
       | c1 er1 er2 Hmatch IH | c2 er1 er2 Hmatch IH
       | er | c1 c2 er Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MVazio *)
    simpl. intros contra. inversion contra.
  - apply bombeamento_fraco_char.
  - apply bombeamento_fraco_concatenar; assumption.
  - apply bombeamento_fraco_uniao_esquerda; assumption.
  - apply bombeamento_fraco_uniao_direita; assumption.
  - apply bombeamento_fraco_estrela_zero.
  - apply bombeamento_fraco_estrela_concatenar; assumption.
Qed.

(*** O Lema do Bombeamento (Forte) ***)

(* Agora, eis a versão usual do lema do bombeamento. Além de exigir que c2 ≠ [], 
ela também reforça o resultado ao incluir a reivindicação de que o comprimento de 
c1 mais o comprimento de c2 é menor ou igual à constante de bombeamento 
(length c1 + length c2 ≤ constante_de_bombeamento er. ). *)

Lemma bombeamento : forall T (er : exp_reg T) c,
  c =~ er ->
  constante_de_bombeamento er <= length c ->
  exists c1 c2 c3,
    c = c1 ++ c2 ++ c3 /\
    c2 <> [] /\
    length c1 + length c2 <= constante_de_bombeamento er /\
    forall m, c1 ++ nconc m c2 ++ c3 =~ er.

(* Você talvez queira copiar sua prova de bombeamento_fraco abaixo. *)

Proof.
  intros T er c Hmatch.
  induction Hmatch
    as [ | x | c1 er1 c2 er2 Hmatch1 IH1 Hmatch2 IH2
       | c1 er1 er2 Hmatch IH | c2 er1 er2 Hmatch IH
       | er | c1 c2 er Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MVazio *)
    simpl. intros contra. inversion contra.
    (* MChar *)
  - simpl. intros contra. inversion contra. inversion H1.
    (* MConcatenar *)
  - simpl. destruct (lt_ge_casos (constante_de_bombeamento er1) (length c1)) as [Hle | Hlt].
    + apply n_lt_m__n_le_m in Hle. apply IH1 in Hle. intros Hsum. 
      destruct Hle as [sa1 [sa2 [sa3 [H_eq [H_ne [H_len H_bombeamento]]]]]].
      exists sa1, sa2, (sa3 ++ c2). split.
        * rewrite H_eq.
          rewrite app_assoc. rewrite app_assoc. rewrite app_assoc.
          reflexivity.
        * split.
          -- apply H_ne.
          -- split.
            ++ apply (le_trans (length sa1 + length sa2) (constante_de_bombeamento er1) 
            (constante_de_bombeamento er1 + constante_de_bombeamento er2) H_len).
            apply le_mais_l.
            ++ intros m. rewrite app_assoc. rewrite app_assoc. apply MConcatenar.
               ** rewrite <- app_assoc. apply (H_bombeamento m).
               ** apply Hmatch2. 
    + intros Hsum.
       rewrite length_app in Hsum.
       unfold ge in Hlt.
      (* c2 sozinho já alcança a constante de er2 *)
      assert (Hc2 : constante_de_bombeamento er2 <= length c2).
        { apply (cancela_soma_esquerda (constante_de_bombeamento er1)).
          apply (le_trans _ (length c1 + length c2)).
          - apply Hsum.
          - apply mais_le_compat_direita. apply Hlt. }
      destruct (IH2 Hc2) as [s1 [s2 [s3 [Heq [Hne [Hlen Hall]]]]]].
      (* c1 inteiro fica na frente do bloco bombeável, que vem de c2 *)
      exists (c1 ++ s1), s2, s3.
      split.
      { rewrite Heq. rewrite app_assoc. reflexivity. }
      split.
      { apply Hne. }
      split.
      { rewrite length_app. rewrite <- add_associativo.
        apply (le_trans _ (constante_de_bombeamento er1 + (length s1 + length s2))).
        - apply mais_le_compat_direita. apply Hlt.
        - apply mais_le_compat_esquerda. apply Hlen. }
      intros m.
      assert (Hrw : (c1 ++ s1) ++ nconc m s2 ++ s3 = c1 ++ s1 ++ nconc m s2 ++ s3).
        { symmetry. apply app_assoc. }
      rewrite Hrw.
      apply MConcatenar.
        * apply Hmatch1.
        * apply Hall.
  (* MUniaoEsquerda *)
  - intros Hsum.
    assert (Hle1 : constante_de_bombeamento er1 <= length c1).
      {
       apply (le_trans (constante_de_bombeamento er1) 
       (constante_de_bombeamento (Uniao er1 er2)) (length c1)).
       - simpl. apply le_mais_l.
       - apply Hsum. 
     }
    apply IH in Hle1.
    destruct Hle1 as [sc1 [sc2 [sc3 [H_eq [H_ne [H_len H_bombeamento]]]]]].
    exists sc1, sc2, sc3.
    split.
      + apply H_eq.
      + split.
        * apply H_ne.
        * split.
          -- apply (le_trans (length sc1 + length sc2) 
                (constante_de_bombeamento er1) 
                (constante_de_bombeamento (Uniao er1 er2))).
              apply H_len.
              apply le_mais_l.
          -- intros m. apply MUniaoEsquerda. apply H_bombeamento.
  (* MUniaoDireita *)
  - intros Hsum.
    assert (Hle2 : constante_de_bombeamento er2 <= length c2).
      {
       apply (le_trans (constante_de_bombeamento er2) 
       (constante_de_bombeamento (Uniao er1 er2)) (length c2)).
       - simpl. rewrite add_comutativo. apply le_mais_l.
       - apply Hsum. 
     }
    apply IH in Hle2.
    destruct Hle2 as [sc1 [sc2 [sc3 [H_eq [H_ne [H_len H_bombeamento]]]]]].
    exists sc1, sc2, sc3.
    split.
      + apply H_eq.
      + split.
        * apply H_ne.
        * split.
          -- apply (le_trans (length sc1 + length sc2) 
                (constante_de_bombeamento er2) 
                (constante_de_bombeamento (Uniao er1 er2))).
              apply H_len. simpl. rewrite add_comutativo.
              apply le_mais_l.
          -- intros m. apply MUniaoDireita. apply H_bombeamento.
  (* MEstrela0 *)
  - assert (Hmin : 1 <= constante_de_bombeamento er).
     {
      induction er.
      - simpl. apply le_n.
      - apply le_n.
      - apply le_S. apply le_n.
      - apply (le_trans 1 (constante_de_bombeamento er1) 
        (constante_de_bombeamento er1 + constante_de_bombeamento er2)).
        + apply IHer1.
        + apply le_mais_l.
      - apply (le_trans 1 (constante_de_bombeamento er1) 
        (constante_de_bombeamento er1 + constante_de_bombeamento er2)).
        + apply IHer1.
        + apply le_mais_l.
      - apply IHer.
     }
     intros contra. inversion contra. rewrite H1 in Hmin. inversion Hmin.
  (* MEstrelaConcatenar *)
  - intros Hsum.
    destruct (lt_ge_casos (constante_de_bombeamento er) (length c1)) as [Hle | Hlt].
    + apply n_lt_m__n_le_m in Hle.
      apply IH1 in Hle.
      destruct Hle as [sa1 [sa2 [sa3 [H_eq [H_ne [H_len H_bombeamento]]]]]].
      exists sa1, sa2, (sa3 ++ c2). split.
      * rewrite H_eq. rewrite app_assoc. rewrite app_assoc. rewrite app_assoc. reflexivity.
      * split.
        -- apply H_ne.
        -- simpl. split.
            ++ apply H_len.
            ++ intros m. rewrite app_assoc. rewrite app_assoc. apply MEstrelaConcatenar.
                ** rewrite <- app_assoc. apply (H_bombeamento m).
                ** apply Hmatch2.
    + unfold ge in Hlt.
      (* repetir c1 e depois c2 continua casando com Estrela er *)
      assert (Hbomb : forall m, nconc m c1 ++ c2 =~ Estrela er).
      { induction m as [ | m' IHm].
        - simpl. apply Hmatch2.
        - simpl. rewrite <- app_assoc.
          apply MEstrelaConcatenar.
          + apply Hmatch1.
          + apply IHm. }
      destruct c1 as [ | h c1'].
      * (* c1 = [] : tudo vem de c2, a IH2 resolve *)
        destruct (IH2 Hsum) as [s1 [s2 [s3 [Heq [Hne [Hlen Hall]]]]]].
        exists s1, s2, s3.
        split. { simpl. apply Heq. }
        split. { apply Hne. }
        split. { apply Hlen. }
        apply Hall.
      * (* c1 não-vazio e curto : o próprio c1 é o bloco bombeável *)
        exists [], (h :: c1'), c2.
        split. { reflexivity. }
        split. { discriminate. }
        split. { simpl. apply Hlt. }
        intros m. simpl. apply (Hbomb m).
Qed.

End Bombeamento.

(********************** Estudo de Caso: Aprimorando a Reflexão ********************)

(* Vimos no capítulo de Lógica que às vezes precisamos relacionar computações 
booleanas a declarações em Prop. No entanto, realizar essa conversão como 
fizemos lá pode resultar em scripts de prova tediosos. Considere a prova do seguinte 
teorema:*)
 
Theorem filter_nao_vazio_In : forall n l,
  filter (fun x => n =? x) l <> [] -> In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = nil *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (n =? m) eqn:H.
    + (* n =? m = true *)
      intros _. rewrite eqb_eq in H.
      rewrite H. left. reflexivity.
    + (* n =? m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(* Na primeira ramificação após o destruct, aplicamos explicitamente o lema eqb_eq à 
equação gerada ao aplicar destruct em n =? m, para converter a hipótese n =? m = true 
na hipótese n = m; somente então podemos reescrever usando essa hipótese para completar 
o caso.

Podemos otimizar esse tipo de raciocínio definindo uma proposição indutiva que produza 
um princípio de análise de casos melhor para n =? m. Em vez de gerar a hipótese 
(n =? m) = true, que geralmente exige algum ajuste antes de podermos usá-la, este 
princípio nos dá imediatamente a hipótese de que realmente precisamos: n = m.

Seguindo a terminologia introduzida em Lógica, chamamos isso de ''princípio de reflexão 
para a igualdade em números'' (reflection principle for equality on numbers), e dizemos
que o booleano n =? m está refletido na proposição n = m.*)

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT (H : P) : reflect P true
  | ReflectF (H : ~ P) : reflect P false.

(* A propriedade reflect recebe dois argumentos: uma proposição P e um booleano b. Ela 
afirma que a propriedade P reflete (intuitivamente, é equivalente a) o booleano b: 
isto é, P é válida se, e somente se, b = true.

Para ver isso, note que, por definição, a única maneira de produzirmos uma evidência 
para reflect P true é mostrando P e, em seguida, usando o construtor ReflectT. Se 
invertermos essa afirmação, isso significa que podemos extrair uma evidência para P a 
partir de uma prova de reflect P true.

Da mesma forma, a única maneira de mostrar reflect P false é rotulando uma evidência 
para ¬ P com o construtor ReflectF.

Para colocar essas observações em prática, primeiro provamos que as afirmações 
P ↔ b = true e reflect P b são de fato equivalentes. Primeiro, a implicação da 
esquerda para a direita: *)

Theorem sse_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* TRABALHADO EM AULA *)
  intros P b H. destruct b eqn:Eb.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. unfold negacao. rewrite H. intros H'. discriminate.
Qed.

(* Agora prove a implicação da direita para a esquerda: *)

(* Exercício *)
Theorem reflect_sse : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H. inversion H.
  - split.
    + intros Hp. reflexivity.
    + intros Heq. apply H0.
  - split.
    + intros Hp. unfold negacao in H0. apply H0 in Hp. inversion Hp.
    + intros Heq. discriminate Heq. 
  Qed.

(* Portanto, podemos pensar em reflect como uma variante do conectivo usual ''se e 
somente se''. A vantagem do reflect é que, ao aplicar destruct em uma hipótese ou lema 
da forma reflect P b, podemos realizar uma análise de casos em b gerando, ao mesmo 
tempo, hipóteses apropriadas nos dois ramos (P na primeira submeta e ¬ P na segunda).
Vamos usar o reflect para produzir uma prova mais fluida de filter_nao_vazio_In.

Começamos reescrevendo o lema eqb_eq em termos de reflect: *) 

Lemma eqb_spec : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply sse_reflect. rewrite eqb_eq. reflexivity.
Qed.

(* A prova de filter_nao_vazio_In agora é a seguinte. Note como as chamadas para 
destruct e rewrite na prova anterior deste teorema são combinadas aqui em uma única 
chamada para destruct.

(Para ver isso claramente, execute as duas provas de filter_nao_vazio_In com o Rocq e 
observe as diferenças no estado da prova no início do primeiro caso do destruct.) *)

Theorem filter_nao_vazio_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l =  *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqb_spec n m) as [EQnm | NEQnm].
    + (* n = m *)
      intros _. rewrite EQnm. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.
  
(* Exercício *)
(* Use eqb_spec como acima para provar o seguinte: *)

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqb_spec_pratica : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l Hcount. induction l as [| m l' IHl'].
  - simpl. intros Hf. apply Hf.
  - destruct (eqb_spec n m).
   (* Subcaso 1: n = m (refletido por ReflectT) *)
    + unfold negacao. intros H_in. 
      simpl in Hcount. rewrite <- H in Hcount. rewrite eqb_refl in Hcount. 
      discriminate Hcount.
    (* Subcaso 2: n <> m (refletido por ReflectF) *)
    + unfold negacao. intros H_in. destruct H_in as [Hmn | Hinnl'].
    (* Se n = m, contradição com H *)
      * unfold negacao in H. apply H. symmetry. apply Hmn.
    (* Se n está em l', usamos a IH *)
      * apply IHl'.
        -- simpl in Hcount. destruct (n =? m) eqn:Heq.
          ++ exfalso. apply H. apply eqb_eq. apply Heq.
          ++ apply Hcount.
        -- apply Hinnl'.
        Qed.

(* Este pequeno exemplo mostra a reflexão nos proporcionando um pequeno ganho em 
conveniência; em desenvolvimentos maiores, usar a reflexão de forma consistente pode 
frequentemente levar a scripts de prova visivelmente mais curtos e claros. Veremos 
muitos outros exemplos em capítulos posteriores e em Programming Language Foundations.

Essa forma de usar a reflexão foi popularizada pelo SSReflect, uma biblioteca do Rocq 
que tem sido usada para formalizar resultados importantes em matemática, incluindo o 
teorema das quatro cores e o teorema de Feit-Thompson. O nome SSReflect significa 
small-scale reflection (reflexão em pequena escala), ou seja, o uso generalizado da 
reflexão para otimizar pequenos passos de prova, transformando-os em computações 
booleanas. *)

(******************************* Exercícios Adicionais *******************************)

(* Formular definições indutivas de propriedades é uma habilidade importante que você 
precisará neste curso. Tente resolver este exercício sem nenhuma ajuda. Dizemos que 
uma lista ''gagueja'' se ela repete o mesmo elemento consecutivamente. (Isso é 
diferente de não conter duplicatas: a sequência [1;4;1] tem duas ocorrências do 
elemento 1, mas não gagueja.) A propriedade naogaguejar minhalista significa que 
minhalista não gagueja. Formule uma definição indutiva para nao_gagueja. *)

Inductive nao_gagueja {X:Type} : list X -> Prop :=
  | nao_gagueja_nil : nao_gagueja []
  | nao_gagueja_um (x : X) : nao_gagueja [x]
  | nao_gagueja_mais_de_um (x y : X) (l : list X) : x <> y -> nao_gagueja (y :: l) ->
    nao_gagueja (x :: y :: l).

(* Certifique-se de que cada um desses testes seja bem-sucedido, mas fique à vontade 
para alterar a prova sugerida (nos comentários) caso a fornecida não funcione para 
você. Sua definição pode ser diferente da nossa e ainda assim estar correta, caso em 
que os exemplos podem precisar de uma prova diferente. (Você perceberá que as provas 
sugeridas usam várias táticas sobre as quais ainda não conversamos, para torná-las 
mais robustas a diferentes maneiras possíveis de definir o nao_gagueja. Provavelmente 
você pode apenas descomentar e usá-las como estão, mas também pode provar cada exemplo 
com táticas mais básicas.) *)
  
Example teste_nao_gagueja_1: nao_gagueja [3;1;4;1;5;6].
Proof.
  repeat constructor; apply eqb_neq; auto.
  Qed.

Example teste_nao_gagueja_2: nao_gagueja (@nil nat).
Proof.
   repeat constructor; apply eqb_neq; auto.
  Qed.
  
Example teste_nao_gagueja_3: nao_gagueja [5].
Proof. 
  repeat constructor; auto. Qed.

Example teste_nao_gagueja_4: ~ (nao_gagueja [3;1;1;4]).
Proof.
  intro.
  repeat match goal with
    h: nao_gagueja _ |- _ => inversion h; clear h; subst
  end.
  contradiction; auto. Qed.

(* Vamos provar que nossa definição de filter do capítulo Polimorfismo corresponde a 
uma especificação abstrata. Aqui está a especificação, escrita informalmente em português:

Uma lista l é uma 'mesclagem em ordem' (in-order merge) de l1 e l2 se ela contém todos 
os mesmos elementos de l1 e l2, na mesma ordem que l1 e l2, mas possivelmente 
intercalados. Por exemplo, 
        [1;4;6;2;3] 
é uma mesclagem em ordem de
         [1;6;2] 
           e 
         [4;3].

Agora, suponha que temos um conjunto X, uma função teste: X -> bool e uma lista l do 
tipo list X. Suponha ainda que l é uma mesclagem em ordem de duas listas, l1 e l2, de 
tal forma que cada item em l1 satisfaz o teste e nenhum item em l2 satisfaz o teste. 
Então, filter test l = l1.

Primeiro, defina o que significa para uma lista ser uma mesclagem de outras duas. 
Faça isso usando uma relação indutiva, e não um Fixpoint. *)

Inductive merge {X:Type} : list X -> list X -> list X -> Prop :=
  | merge_nil : merge [] [] []
  | merge_l1 (x : X) (l1 l2 l : list X) (resto : merge l1 l2 l) : 
    merge (x :: l1) l2 (x :: l)
  | merge_l2 (x : X) (l1 l2 l : list X) (resto : merge l1 l2 l) :
    merge l1 (x :: l2) (x :: l).

Theorem merge_filter : forall (X : Set) (teste: X -> bool) (l l1 l2 : list X),
  merge l1 l2 l ->
  All (fun n => teste n = true) l1 ->
  All (fun n => teste n = false) l2 ->
  filter teste l = l1.

Proof.
  intros X teste l l1 l2 Hmerge.
  induction Hmerge as [ | x l1' l2' l' Hmerge' IH' | x l1' l2' l' Hmerge' IH'].
  (* merge_nil *)
  - intros Hallt Hallf. reflexivity.
  (* merge_l1 *)
  - intros Hallt Hallf.
    simpl in Hallt. destruct Hallt as [Hx Hrestt].
    simpl. rewrite Hx. f_equal.
    apply (IH' Hrestt Hallf).
  (* merge_l2 *)
  - intros Hallt Hallf.
    simpl in Hallf. destruct Hallf as [Hx Hrestf].
    simpl. rewrite Hx. apply (IH' Hallt Hrestf).
Qed.

(* Uma maneira diferente de caracterizar o comportamento de filter é a seguinte: Entre 
todas as subsequências de l com a propriedade de que o teste avalia para verdadeiro em 
todos os seus membros, filter test l é a mais longa. Formalize essa afirmação e prove-a. *)

Theorem filter_subseq_mais_longa : forall (teste : nat -> bool) (l l1 : list nat), 
  All (fun x => teste x = true) l1 -> subseq l1 l -> length l1 <= length (filter teste l).

Proof.
  intros teste l l1 Hall Hsubseq.
  induction Hsubseq as [ | x l' l1' H IH| x l' l1' H IH].
  (* subseq_nil *)
  - simpl. apply le_n.
  (* subseq_mantem *)
  - simpl. simpl in Hall. destruct Hall as [Hteste Hfun].
     apply IH in Hfun. rewrite Hteste. simpl. apply n_le_m__Sn_le_Sm.
     apply Hfun.
  (* subseq_pula *)
  - simpl. simpl in Hall. destruct (teste x) eqn:E.
    + simpl. apply le_S. apply IH. apply Hall.
    + apply IH. apply Hall.
Qed. 

(* Um palíndromo é uma sequência que se lê da mesma forma de trás para frente e de 
frente para trás.

- Defina uma proposição indutiva pal sobre a lista X que capture o que significa ser um 
palíndromo. (Dica: Você precisará de três casos.)

- Prove (pal_app_rev) que 
    ∀ l, pal (l ++ rev l).

- Prove (pal_rev) que
    ∀ l, pal l → l = rev l.

Para crédito extra, tente provar os mesmos teoremas com uma definição alternativa que
 possua um único construtor deste tipo: 
    ∀ l, l = rev l → pal l 
*)

Inductive pal {X:Type} : list X -> Prop :=
  | pal_nil : pal []
  | pal_um (x : X) : pal [x]
  | pal_mais_de_um (x : X) (l : list X) (H : pal l): pal (x :: l ++ [x]).

Theorem pal_app_rev : forall (X:Type) (l : list X),
  pal (l ++ (rev l)).
Proof.    
  intros X l.
  induction l as [ | h t IHl].
  (* l : []*)
  - apply pal_nil.
  (* l : h :: t *)
  - simpl. rewrite app_assoc. apply (pal_mais_de_um h (t ++ (rev t)) IHl).
  Qed.

Theorem pal_rev : forall (X:Type) (l: list X) , pal l -> l = rev l.
Proof.
  intros X l Hpal.
  induction Hpal as [ | x | x l' H IHl'].
  (* pal_nil *)
  - reflexivity.
  (* pal_um *)
  - reflexivity.
  (* pal_mais_de_um *)
  - simpl. rewrite (rev_app_distr l' [x]).
    simpl. rewrite <- IHl'. reflexivity.
 Qed.

Inductive pal_alt {X : Type} : list X -> Prop :=
  | pal_intro : forall l, l = rev l -> pal_alt l.

Theorem pal_alt_app_rev : forall (X:Type) (l : list X),
  pal_alt (l ++ (rev l)).
Proof.
  intros X l.
  induction l as [ | h t IHl].
  (* l : *)
  - apply pal_intro. reflexivity.
  (* l : h :: t *)
  - apply pal_intro. rewrite rev_app_distr. inversion IHl.
    rewrite rev_involutive. reflexivity.
    Qed.

Theorem pal_alt_rev : forall (X:Type) (l: list X) , pal_alt l -> l = rev l.
Proof.
  intros X l Hpal.
  induction Hpal as [l' IHl'].
  apply IHl'.
  Qed. 

(* Novamente, a direção recíproca é significativamente mais difícil, devido à falta de 
evidência. Usando a sua definição de pal do exercício anterior, prove que: 
       ∀ l, l = rev l → pal l.
*)

Theorem palindromo_reciproco: forall (X:Type) (l: list X),
  l = rev l -> pal l.
Proof.
  intros X l Heq.
  (* Generalização com limite de tamanho n, para permitir indução forte *)
  assert (Haux : forall n (l0 : list X), length l0 <= n -> l0 = rev l0 -> pal l0).
{
  induction n as [ | n' IHn].
  - intros l0 Hlen Heq0. 
    destruct l0 as [ | x l1].
    (* l0 : []*)
    + apply pal_nil.
    (* l0 : x :: l1 *)
    + simpl in Hlen. inversion Hlen.

  - intros l0 Hlen Heq0.
    destruct l0 as [ | x l1].
    + apply pal_nil.
    + revert Heq0 Hlen.
    apply (rev_ind (fun l1 => x :: l1 = rev (x :: l1) ->
                               length (x :: l1) <= S n' ->
                               pal (x :: l1))).
    * (* l1 = [] *)
      intros Heq0 Hlen.
      apply pal_um.
    * (* l1 = l1' ++ [y] *)
      intros y l1' _ Heq0 Hlen.
      simpl in Heq0.
      rewrite rev_app_distr in Heq0.
      simpl in Heq0.
      injection Heq0 as Hxy Hmid.
      rewrite <- Hxy in Hmid.
      apply app_inj_tail in Hmid.
      destruct Hmid as [Hl1'rev _].
      rewrite Hxy.
      apply pal_mais_de_um.
      apply (IHn l1').
      -- simpl in Hlen.
         rewrite length_app in Hlen. simpl in Hlen.
         apply Sn_le_Sm__n_le_m in Hlen.
         apply (le_trans (length l1') (length l1' + 1) n').
         ++ apply le_mais_l.
         ++ apply Hlen.
      -- apply Hl1'rev.
}
 (* Haux no caso específico em que n é length l e l0 é l *)
  apply (Haux (length l) l).
  - apply le_n.
  - apply Heq.
  Qed.

(* Relembre a definição da propriedade In do capítulo de Lógica, que afirma que um 
valor x aparece pelo menos uma vez em uma lista l: *)

Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
     match l with
     | [] => False
     | x' :: l' => x' = x \/ In A x l'
     end.

(* Sua primeira tarefa é usar In para definir uma proposição disjunta X l1 l2, que deve 
ser provável exatamente quando l1 e l2 são listas (com elementos do tipo X) que não 
têm elementos em comum. *)

Definition disjunta (X : Type) (l1 l2 : list X) : Prop :=
  forall (x : X), In X x l1 -> ~ (In X x l2).

(* Em seguida, use In para definir uma proposição indutiva NoDup X l, que deve ser 
provável exatamente quando l for uma lista (com elementos do tipo X) na qual todos os 
membros são diferentes entre si. Por exemplo, NoDup nat [1;2;3;4] e NoDup bool [] devem 
ser prováveis, enquanto NoDup nat [1;2;1] e NoDup bool [true;true] não devem ser. *)

Inductive NoDup {X : Type} : list X -> Prop :=
  | NoDup_nil : NoDup []
  | NoDup_cons (x : X) (l : list X) : ~ (In X x l) -> NoDup l -> NoDup (x :: l).

(* Por fim, formule e prove um ou mais teoremas interessantes que relacionem disjunta, 
NoDup e ++ (concatenação de listas). *)

Theorem NoDup_disjunta_app : forall (X : Type) (l1 l2 : list X),
  NoDup l1 -> NoDup l2 -> disjunta X l1 l2 -> NoDup (l1 ++ l2).
Proof.
  intros X l1 l2 Hndl1 Hndl2 Hdl1l2.
  induction Hndl1 as [ | x l Hin Hnd IH].
  - (* l1 = [] : l1++l2 = l2, já é NoDup *)
    simpl. apply Hndl2.
  - (* l1 = x::l : precisa x não estar em l++l2, e l++l2 ser NoDup *)
    simpl. apply NoDup_cons.
    + unfold negacao. intros Hin'.
      rewrite In_juntar_sse in Hin'. destruct Hin' as [Hinl | Hinl2].
      * apply Hin. apply Hinl. (* x em l: contradiz Hin *)
      * apply (Hdl1l2 x).      (* x em l2: contradiz disjunção *)
        -- simpl. left. reflexivity.
        -- apply Hinl2.
    + apply IH. unfold disjunta. intros y Hiny.
      apply Hdl1l2. simpl. right. apply Hiny.
Qed.

Theorem NoDup_app_disjunta : forall (X : Type) (l1 l2 : list X),
  NoDup (l1 ++ l2) -> disjunta X l1 l2.
Proof.
  intros X l1 l2 Hndl1l2.

  (* Indução sobre a primeira lista *)
  induction l1 as [ | h1 t1 IHl1].

  - (* Caso base: l1 = [].  A lista vazia é disjunta de qualquer lista. *)
    unfold disjunta. intros x Hinxnil.
    unfold negacao. intros Hinxl2.
    simpl in Hinxnil. apply Hinxnil.
  - (* Caso indutivo: l1 = h1 :: t1. Pela ausência de duplicatas, h1 não aparece no 
     restante da lista. *)
    inversion Hndl1l2. unfold disjunta.
    intros y Hiny. destruct Hiny as [Heq | Hin_t1].
      + (* Caso y = h1 *)
        intros Hin_l2. apply H1. rewrite Heq.
        (* y pertence à concatenação se pertence a t1 ou a l2. *)
        rewrite (In_juntar_sse X t1 l2 y).
        right.
        apply Hin_l2.
      + (* Caso y pertence a t1. Usamos a hipótese de indução sobre t1 e l2. *)
        unfold negacao. intros Hin_l2. apply ((IHl1 H2) y). apply Hin_t1. apply Hin_l2.
Qed.

(* O princípio da casa dos pombos estabelece um fato básico sobre contagem: se 
distribuirmos mais do que n itens em n casas de pombos, alguma casa de pombos deve 
conter pelo menos dois itens. Como costuma acontecer, esse fato aparentemente trivial 
sobre números requer um maquinário não trivial para ser provado, mas agora temos o 
suficiente... Primeiro, prove um lema fácil e útil. *)

Lemma in_split : forall (X : Type) (x : X) (l:list X),
  In X x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros X x l Hin.
  induction l as [ | h t IHl].
  - inversion Hin.
  - simpl in Hin. destruct Hin as [Heq | Hinxt].
    + rewrite Heq. exists []. simpl. rewrite <- Heq. exists t. reflexivity.
    + destruct (IHl Hinxt) as [l1 [l2 Heq]].
      exists (h :: l1). exists l2. simpl. rewrite <- Heq. reflexivity.
Qed.

(* Agora defina uma propriedade repeats de tal forma que repeats X l afirme que l 
contém pelo menos um elemento repetido (do tipo X).   *)

Inductive repeats {X:Type} : list X  -> Prop :=
  | repeats_head (h : X) (l : list X) :  In X h l -> repeats (h :: l)
  | repeat_cons (x : X) (l : list X) (H : repeats l) : repeats (x :: l).

(* Agora, aqui está uma maneira de formalizar o princípio da casa dos pombos. Suponha 
que a lista l2 represente uma lista de rótulos de casas dos pombos, e a lista l1 
represente os rótulos atribuídos a uma lista de itens. Se houver mais itens do que 
rótulos, pelo menos dois itens devem ter o mesmo rótulo — ou seja, a lista l1 deve 
conter repetições.

Esta demonstração é muito mais fácil se você usar a hipótese do terceiro excluído para 
mostrar que o predicado In é decidível, isto é, ∀ x l, (In x l) ∨ ¬ (In x l). No 
entanto, também é possível fazer a demonstração funcionar sem assumir que In é 
decidível; se você conseguir fazer isso, não precisará da hipótese do terceiro excluído. *)

Theorem principio_da_casa_dos_pombos: terceiro_excluido ->
  forall (X:Type) (l1 l2:list X),
  (forall x, In X x l1 -> In X x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof.
  intros EM X l1. induction l1 as [ |x l1' IHl1'].
  (* l1 : [] *)
  - intros l2 Hin Hlt. inversion Hlt.
  (* l1 : x :: l1' *)
  - intros l2 Hin Hlt. unfold terceiro_excluido in EM.
    destruct (EM (In X x l1')) as [Hp | Hnp].
    (* x está em l1' *)
    + apply (repeats_head x l1' Hp).
    (* x não está em l1' - a repetição precisa estar em l1' sozinha *)
    +  (* x precisa estar em l2, já que l1 = x::l1' mapeia inteiro em l2 *)
      assert (Hinxl2 : In X x l2).
      { apply Hin. simpl. left. reflexivity. }
      (* separa l2 em antes/depois de x, para ''remover'' x de l2 *)
      destruct (in_split X x l2 Hinxl2) as [l2a [l2b Heql2]].
      apply repeat_cons.
      (* aplica IH em l1' contra l2 sem o x (l2a++l2b) *)
      apply (IHl1' (l2a ++ l2b)).
      (* mostra que todo elemento de l1' ainda mapeia em l2a++l2b *)
      * intros x0 Hinx0.
        assert (Hx0l2 : In X x0 l2).
        { apply Hin. simpl. right. apply Hinx0. }
        rewrite Heql2 in Hx0l2.
        apply In_juntar_sse in Hx0l2.
        apply In_juntar_sse.
        destruct Hx0l2 as [H1 | H2].
        -- left. apply H1.
        -- simpl in H2. destruct H2 as [Heqx0 | H2].
           (* x0 = x seria absurdo: x0 está em l1', mas x não está (Hnp) *)
           ++ exfalso. apply Hnp. rewrite Heqx0. apply Hinx0.
           ++ right. apply H2.
      (* mostra que l2a++l2b (sem o x removido) ainda é menor que l1' *)
      * assert (Hlen : length l2 = length l2a + S (length l2b)).
        { rewrite Heql2. apply length_app. }
        rewrite length_app.
        simpl in Hlt.
        rewrite Hlen in Hlt.
        rewrite <- mais_n_Sm in Hlt.
        apply Sn_le_Sm__n_le_m in Hlt.
        apply Hlt.
Qed.

(*** Um Casador de Expressões Regulares Verificado ***)

(* Definimos agora uma relação de casamento (match) sobre expressões regulares e 
listas polimórficas. Podemos usar tal definição para provar manualmente que uma dada 
expressão regular casa com uma dada string, mas isso não nos fornece um programa que 
possamos executar para determinar um casamento automaticamente.

Seria razoável esperar que pudéssemos traduzir as definições das regras indutivas 
para a construção de evidências da relação de casamento em casos de uma função 
recursiva que reflete a relação, fazendo recursão sobre uma dada expressão regular. 
No entanto, não parece simples definir tal função na qual a dada expressão regular seja 
uma variável de recursão reconhecida pelo Rocq. Como resultado, o Rocq não aceitará 
que a função sempre termine.

Casadores de expressões regulares fortemente otimizados realizam o casamento 
traduzindo uma dada expressão regular em uma máquina de estados e determinando se a 
máquina de estados aceita uma dada string. No entanto, o casamento de expressões 
regulares também pode ser implementado usando um algoritmo que opera puramente em 
strings e expressões regulares, sem definir e manter tipos de dados adicionais, como 
máquinas de estados. Implementaremos tal algoritmo e verificaremos se o seu valor 
reflete a relação de casamento.

Implementaremos um casador de expressões regulares que casa strings representadas 
como listas de caracteres ASCII: *)

From Stdlib Require Import Strings.Ascii.
Definition string := list ascii.

(* A biblioteca padrão do Rocq contém uma definição indutiva distinta de strings de 
caracteres ASCII. No entanto, usaremos a definição de strings acima como listas de 
caracteres ASCII para aplicar a definição existente da relação de casamento (match).

Poderíamos também definir um casador de expressões regulares sobre listas polimórficas, 
e não especificamente sobre listas de caracteres ASCII. O algoritmo de casamento que 
implementaremos precisa ser capaz de testar a igualdade de elementos em uma dada 
lista e, portanto, precisa receber uma função de teste de igualdade. Generalizar as 
definições, os teoremas e as provas que definimos para tal cenário é um pouco 
entediante, mas viável.

A prova de corretude do casador de expressões regulares combinará propriedades da 
função de casamento de expressões regulares com propriedades da relação de casamento 
que não dependem da função de casamento. Vamos em frente e provar esta última classe 
de propriedades agora. A maioria delas tem provas diretas, que foram fornecidas a 
você, embora existam alguns lemas principais que foram deixados para você provar.

Cada Prop provável é equivalente a True. *)

Lemma equiv_true_provavel : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

(* Cada Prop cuja negação é provável é equivalente a False.*)

Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. destruct H0.
Qed.

(* O conjunto vazio não casa com nenhuma string. *)

Lemma nulo_nao_casa_com_nada : forall (s : string), (s =~ ConjuntoVazio) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold negacao. intros. inversion H.
Qed.

(* CadeiaVazia só se casa com a cadeia vazia *)

Lemma vazia_casa_com_cadv : forall (s : string), s =~ CadeiaVazia <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MVazio.
Qed.

(* CadeiaVazia não casa com nenhuma cadeia não vazia. *)

Lemma vazia_nao_casa_nv : forall (a : ascii) s, (a :: s =~ CadeiaVazia) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold negacao. intros. inversion H.
Qed.

(* Char a não casa com nenhuma cadeia que comece com um caractere diferente de a.*)

Lemma char_nao_casa_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold negacao.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.

(* Se Char a casa com uma cadeia não vazia, então o restante (cauda) da cadeia é vazio.*)

Lemma char_sufixo_vazio : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

(* Concateanr er0 er1 casa com a cadeia s se e somente se s = s0 ++ s1, com s0 casando com 
er0 e s1 casando com er1. *)

Lemma concatenar_existe : forall (s : string) er0 er1,
  s =~ Concatenar er0 er1 <->
  exists s0 s1, s = s0 ++ s1 /\ s0 =~ er0 /\ s1 =~ er1.
Proof.
  intros.
  split.
  - intros. inversion H. exists c1, c2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MConcatenar s0 _ s1 _ Hmat0 Hmat1).
Qed.

(* Exercício *)
(* Concatenar er0 er1 corresponde a a::s se, e somente se, er0 corresponde à cadeia vazia e 
a::s corresponde a er1, ou s = s0 ++ s1, onde a::s0 corresponde a er0 e s1 corresponde a re1. 

Embora esta seja uma propriedade puramente da relação de casamento (match), ela é uma 
observação fundamental por trás do design do nosso correspondedor de regex (matcher). 
Portanto, (1) tire um tempo para compreendê-la, (2) prove-a e (3) procure como você a usará 
mais tarde. *)

Lemma concatenar_nv : forall (a : ascii) s er0 er1,
  a :: s =~ (Concatenar er0 er1) <->
  ([ ] =~ er0 /\ a :: s =~ er1) \/
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ er0 /\ s1 =~ er1.
Proof.
  intros.
  split.
  (* -> *)
  - intros. inversion H. destruct c1 as [ | a0 s0]. 
  (* c1 : [ ] *)
    + left. split.
      * apply H3.
      * simpl. apply H4.
  (* c1 : a0 :: s0*)
    + right. exists s0, c2. split.
    (* s = s0 ++ c2, direto da equação *)
      * simpl in H1. injection H1. intros. rewrite H5. reflexivity.
      * split.
      (* a :: s0 =~ er0, usando a = a0 pra ajustar H3 *)
        -- injection H1. intros. rewrite <- H6. apply H3.
        -- apply H4.
  (* <- *)
  - intros [[H1 H2]| H3].
     + apply (MConcatenar [] er0 (a :: s) er1).
      * apply H1.
      * apply H2.
     + destruct H3 as [s0 [s1 [H4 [H5 H6]]]].
      rewrite H4. apply (MConcatenar (a :: s0) er0 s1 er1).
        * apply H5.
        * apply H6.
Qed.

(* s é casado por Uniao er0 er1 se e somente se s é casado por er0 ou s é casado por er1. *)

Lemma uniao_disj : forall (s : string) er0 er1,
  s =~ Uniao er0 er1 <-> s =~ er0 \/ s =~ er1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H1.
  - intros [ H | H ].
    + apply MUniaoEsquerda. apply H.
    + apply MUniaoDireita. apply H.
Qed.

(* Exercício *)

(* a::s é correspondido por Estrela er se e somente se s = s0 ++ s1, onde a::s0 é 
correspondido por er e s1 é correspondido por Estrela er. Assim como concatenar_nv, essa 
observação é crítica, então compreenda-a, prove-a e mantenha-a em mente.

Dica: você precisará realizar indução. Há um bom número de candidatos razoáveis para Props a 
serem provados por indução. O único que funcionará é dividir o ''se e somente se'' em duas 
implicações e provar uma delas por indução sobre a evidência de a :: s =~ Estrela er. A outra 
implicação pode ser provada sem indução.

Para conseguir provar a propriedade correta por indução, você precisará reescrever a :: s =~ 
Estrela er para que seja um Prop sobre variáveis gerais, usando a tática remember. *)

Lemma estrela_nv : forall (a : ascii) s er,
  a :: s =~ Estrela er <->
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ er /\ s1 =~ Estrela er.
Proof.
  intros a s er.
  split.
  (* -> *) 
  - intros Hmatch.
    remember (a :: s) as x eqn: Ex.
    remember (Estrela er) as er' eqn: Eq.
    induction Hmatch.
    (* MVazio *)
    + discriminate Eq.
    (* MChar *)
    + discriminate Eq.
    (* MConcatenar *)
    + discriminate Eq.
    (* MUniaoEsquerda*)
    + discriminate Eq.
    (* MUniaoDireita *)
    + discriminate Eq.
    (* MEstrela0 *)
    + discriminate Ex.
    (* MEstrelaConcatenar *)
    + inversion Eq. 
      rewrite H0 in IHHmatch2.
      destruct c1 as [ | h1 c1'].
        * simpl in Ex.
        apply IHHmatch2.
        -- apply Ex.
        -- reflexivity.
        * injection Ex as Hn Hs.
          exists c1', c2. split.
          -- symmetry. apply Hs.
          -- split.
            ++ rewrite H0 in Hmatch1. rewrite <- Hn. apply Hmatch1.
            ++ rewrite H0 in Hmatch2. apply Hmatch2.
  (* <- *)
  - intros H. destruct H as [s0 [s1 [Hs [Hmatcher Hmatchestrela]]]].
    rewrite Hs. 
    apply (MEstrelaConcatenar(a :: s0) s1 er Hmatcher Hmatchestrela).
Qed.

(* A definição do nosso verificador de expressões regulares (regex) incluirá duas funções de 
ponto fixo. A primeira função, dada a regex er, será avaliada para um valor que reflete se er 
corresponde à string vazia. A função satisfará a seguinte propriedade: *)

Definition refl_casa_cadv m :=
  forall er : exp_reg ascii, reflect ([ ] =~ er) (m er).

(* Exercício *)
(* Complete a definição de casa_cadv para que ela teste se uma dada regex corresponde à 
string vazia: *)

Fixpoint casa_cadv (er: exp_reg ascii) : bool :=
  match er with
  | ConjuntoVazio => false
  | CadeiaVazia => true
  | Char t => false
  | Concatenar r1 r2 => andb (casa_cadv r1) (casa_cadv r2)
  | Uniao r1 r2 => orb (casa_cadv r1) (casa_cadv r2)
  | Estrela r => true
  end.

(* Agora, prove que casa_cadv de fato testa se uma dada regex corresponde à string vazia. 
(Dica: Você vai querer usar os lemas de reflexão ReflectT e ReflectF.) *)

Lemma casa_cadv_refl : refl_casa_cadv casa_cadv.
Proof.
  unfold refl_casa_cadv.
  intros er.
  assert (Hnil : forall (c1 c2 : list ascii), c1 ++ c2 = [] -> c1 = [] /\ c2 = []). {
    intros c1 c2 H. split.
    - destruct c1.
      + reflexivity.
      + discriminate H.
    - destruct c1.
      + apply H.
      + discriminate H.
  }
  induction er as [ | | t | r1 IHr1 r2 IHr2 | r1 IHr1 r2 IHr2 |r IHr ].
  (* ConjuntoVazio *)
  - apply ReflectF. intros contra. inversion contra.
  (* CadeiaVazia *)
  - apply ReflectT. apply MVazio.
  (* Char *)
  - apply ReflectF. intros contra. inversion contra.
  (* Concatenar *)
  - simpl. destruct IHr1 as [H1 | H1]. destruct IHr2 as [H2 | H2].
    + apply ReflectT. apply (MConcatenar [] r1 [] r2 H1 H2).
    + apply ReflectF. intros contra. inversion contra.
      apply H2. apply Hnil in H0. 
      destruct H0 as [Hc1 Hc2]. rewrite Hc2 in H5. apply H5.
    + apply ReflectF. intros contra. apply H1. inversion contra.
      apply Hnil in H0. destruct H0 as [Hc1 Hc2].
      rewrite Hc1, Hc2. simpl. rewrite Hc1 in H3. apply H3.
   (* Uniao *)
  - simpl. destruct IHr1 as [H1 | H1]. destruct IHr2 as [H2 | H2].
    + apply ReflectT. apply (MUniaoEsquerda [] r1 r2 H1).
    + apply ReflectT. apply (MUniaoEsquerda [] r1 r2 H1).
    + simpl. destruct IHr2 as [H2 | H2].
      * apply ReflectT. apply (MUniaoDireita [] r1 r2 H2).
      * apply ReflectF. intros contra. inversion contra.
        -- apply H1. apply H3.
        -- apply H2. apply H3.
    (* Estrela *)
  - apply ReflectT. apply MEstrela0.
    Qed.

(* Nós definiremos outras funções que usam casa_cadv. No entanto, a única propriedade de 
casa_cadv que você precisará usar em todas as provas sobre essas funções é casa_cadv_refl.

A operação principal que será executada pelo nosso verificador de expressões regulares 
(regex) consistirá em construir iterativamente uma sequência de derivadas de regex. Para 
cada caractere a e regex er, a derivada de er em relação a a é uma regex que corresponde a
todos os sufixos de strings correspondidas por er que começam com a. Ou seja, er' é uma 
derivada de er em relação a a se elas satisfizerem a seguinte relação: *)

Definition e_der er (a : ascii) er' :=
  forall s, a :: s =~ er <-> s =~ er'.

(* Uma função d deriva strings se, dado um caractere a e um regex er, ela avalia a derivada de 
er em a. Ou seja, d satisfaz a seguinte propriedade: *)
Definition deriva d := forall a er, e_der er a (d a er).

(* Exercício *)
(* Defina derive para que ele derive strings (ou seja, produza derivadas de regex). Uma 
implementação natural usa casa_cadv em alguns casos para determinar se um regex chave 
corresponde à string vazia *)

Fixpoint derive (a : ascii) (er : exp_reg ascii) : exp_reg ascii :=
  match er with
  | ConjuntoVazio => ConjuntoVazio
  | CadeiaVazia => ConjuntoVazio  
  | Char t => if nat_of_ascii a =? nat_of_ascii t then CadeiaVazia else ConjuntoVazio
  | Concatenar r1 r2 => 
      if casa_cadv r1 
      then Uniao (Concatenar (derive a r1) r2) (derive a r2)
      else Concatenar (derive a r1) r2
  | Uniao r1 r2 => Uniao (derive a r1) (derive a r2)
  | Estrela r => Concatenar (derive a r) (Estrela r)
  end.

(* A função derive deve passar nos testes a seguir. Cada teste estabelece uma igualdade entre 
uma expressão que será avaliada pelo nosso verificador de regex e o valor final que o 
verificador deve retornar. Cada teste está anotado com o fato de casamento que ele reflete. *)

Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

(* ''c'' =~ ConjuntoVazio: *)
Example teste_der0 : casa_cadv (derive c (ConjuntoVazio)) = false.
Proof.
  reflexivity.
Qed.

(* ''c'' =~ Char c: *)
Example teste_der1 : casa_cadv (derive c (Char c)) = true.
Proof.
  reflexivity.
Qed.

(* ''c'' =~ Char d: *)
Example teste_der2 : casa_cadv (derive c (Char d)) = false.
Proof.
  reflexivity.
Qed.

(* ''c'' =~ Concatenar (Char c) CadeiaVazia: *)
Example teste_der3 : casa_cadv (derive c (Concatenar (Char c) CadeiaVazia)) = true.
Proof.
  reflexivity.
Qed.

(* ''c'' =~ Concatenar CadeiaVazia (Char c): *)
Example teste_der4 : casa_cadv (derive c (Concatenar CadeiaVazia (Char c))) = true.
Proof.
  reflexivity.
Qed.

(* ''c'' =~ Estrela c: *)
Example teste_der5 : casa_cadv (derive c (Estrela (Char c))) = true.
Proof.
  reflexivity.
Qed.

(* ''cd'' =~ App (Char c) (Char d): *)
Example teste_der6 :
  casa_cadv (derive d (derive c (Concatenar (Char c) (Char d)))) = true.
Proof.
  reflexivity.
Qed.

(* ''cd'' =~ Concatenar (Char d) (Char c): *)
Example test_der7 :
  casa_cadv (derive d (derive c (Concatenar (Char d) (Char c)))) = false.
Proof.
  reflexivity.
Qed.

(* Exercício *)
(* Prove que derive de fato sempre deriva strings.

Dica: uma prova faz indução em er, mas você precisará escolher com cuidado a propriedade que 
vai provar por indução, generalizando os termos apropriados.

Dica: se a sua definição de derive aplica casa_cadv a uma regex er em particular, então uma
prova natural vai aplicar casa_cadv_refl a er e fazer destruct no resultado, gerando casos 
com as hipóteses de que er casa ou não casa com a string vazia.

Dica: você pode economizar bastante trabalho usando os lemas provados acima. Em particular, 
para provar muitos dos casos da indução, você pode reescrever uma Prop sobre uma regex 
complicada (por exemplo, s =~ Uniao er0 er1) como uma combinação booleana de Props sobre 
regexes simples (por exemplo, s =~ er0 ∨ s =~ er1), usando os lemas dados acima que são 
equivalências lógicas. Depois você pode raciocinar sobre essas Props de forma natural, 
usando intro e destruct. *)

Lemma derive_corr : deriva derive.
Proof. 
  unfold deriva.
  intros a er.
  (* n =? n é sempre true *)
  assert (Heqb_refl : forall n : nat, (n =? n) = true).
  { intros n. induction n as [ | n' IHn].
    - reflexivity.
    - simpl. apply IHn. }
  (* n =? m = true implica n = m *)
  assert (Heqb_true : forall n m : nat, (n =? m) = true -> n = m).
  { intros n. induction n as [ | n' IHn]; intros m Hm.
    - destruct m as [ | m'].
      + reflexivity.
      + discriminate Hm.
    - destruct m as [ | m'].
      + discriminate Hm.
      + simpl in Hm. apply IHn in Hm. rewrite Hm. reflexivity. }
  induction er as [ | | t | r1 IHr1 r2 IHr2 | r1 IHr1 r2 IHr2 | r IHr].
  - (* ConjuntoVazio *)
    unfold e_der. intros s. split.
    + intros H. inversion H.
    + intros H. inversion H.
  - (* CadeiaVazia *)
    unfold e_der. intros s. split.
    + intros H. inversion H.
    + intros H. inversion H.
  - (* Char *)
    unfold e_der. intros s. simpl. split.
    + intros H. inversion H.
      rewrite Heqb_refl. apply MVazio.
    + destruct (nat_of_ascii a =? nat_of_ascii t) eqn:E.
      * intros H. inversion H.
        apply Heqb_true in E.
        assert (Hinj : a = t).
        { rewrite <- (ascii_nat_embedding a). rewrite E.
          apply ascii_nat_embedding. }
        rewrite Hinj. apply MChar.
      * intros H. inversion H.
  - (* Concatenar *)
    unfold e_der in *. intros s. simpl.
    destruct (casa_cadv_refl r1) as [H1 | H1].
    + (* H1 : [] =~ r1, o derive é um Uniao *)
      rewrite concatenar_nv, uniao_disj, concatenar_existe.
      split.
      * intros [[_ H2] | [s0 [s1 [Hs [H2 H3]]]]].
        -- (* r1 já terminou, o a é consumido por r2 *)
           right. apply (proj1 _ _ (IHr2 s)). apply H2.
        -- (* o a é consumido por r1 *)
           left. exists s0, s1. split.
           ++ apply Hs.
           ++ split.
              ** apply (proj1 _ _ (IHr1 s0)). apply H2.
              ** apply H3.
      * intros [[s0 [s1 [Hs [H2 H3]]]] | H2].
        -- right. exists s0, s1. split.
           ++ apply Hs.
           ++ split.
              ** apply (proj2 _ _ (IHr1 s0)). apply H2.
              ** apply H3.
        -- left. split.
           ++ apply H1.
           ++ apply (proj2 _ _ (IHr2 s)). apply H2.
    + (* H1 : ~ [] =~ r1, o derive é só um Concatenar *)
      rewrite concatenar_nv, concatenar_existe.
      split.
      * intros [[H2 _] | [s0 [s1 [Hs [H2 H3]]]]].
        -- (* o primeiro lado exige [] =~ r1, absurdo *)
           exfalso. apply H1. apply H2.
        -- exists s0, s1. split.
           ++ apply Hs.
           ++ split.
              ** apply (proj1 _ _ (IHr1 s0)). apply H2.
              ** apply H3.
      * intros [s0 [s1 [Hs [H2 H3]]]].
        right. exists s0, s1. split.
        -- apply Hs.
        -- split.
           ++ apply (proj2 _ _ (IHr1 s0)). apply H2.
           ++ apply H3.
  - (* Uniao *)
    unfold e_der in *. intros s. simpl.
    rewrite uniao_disj, uniao_disj.
    split.
    + intros [H | H].
      * left. apply (proj1 _ _ (IHr1 s)). apply H.
      * right. apply (proj1 _ _ (IHr2 s)). apply H.
    + intros [H | H].
      * left. apply (proj2 _ _ (IHr1 s)). apply H.
      * right. apply (proj2 _ _ (IHr2 s)). apply H.
  - (* Estrela *)
    unfold e_der in *. intros s. simpl.
    rewrite estrela_nv, concatenar_existe.
    split.
    + intros [s0 [s1 [Hs [H0 H1]]]]. exists s0, s1. split.
      * apply Hs.
      * split.
        -- apply (proj1 _ _ (IHr s0)). apply H0.
        -- apply H1.
    + intros [s0 [s1 [Hs [H0 H1]]]]. exists s0, s1. split.
      * apply Hs.
      * split.
        -- apply (proj2 _ _ (IHr s0)). apply H0.
        -- apply H1.
Qed.

(* Vamos definir o matcher (avaliador de correspondência) de expressões regulares usando o 
derive. No entanto, a única propriedade de derive que você precisará usar em todas as 
demonstrações das propriedades do matcher é derive_corr.

Uma função m corresponde a expressões regulares se, dadas uma string s e uma expressão regular 
er, ela é avaliada em um valor que reflete se er corresponde a s. Ou seja, m satisfaz a 
seguinte propriedade:*)

Definition casa_regex m : Prop :=
  forall (s : string) er, reflect (s =~ er) (m s er).

(* Exercício *)
(* Complete a definição de regex_casa para que ela case com expressões regulares. *)
Fixpoint regex_casa (s : string) (er : exp_reg ascii) : bool :=
    match s with
    | [] => casa_cadv er
    | a :: s' => regex_casa s' (derive a er)
    end.

(* Finalmente, prove que regex_casa de fato corresponde a expressões regulares.

Dica: se a sua definição de regex_casa aplica casa_cadv à expressão regular er, então uma 
prova natural aplica casa_cadv_refl a er e faz o destruct do resultado para gerar casos nos 
quais você pode assumir que er casa (ou não) com a cadeia vazia.

Dica: se a sua definição de regex_casa aplica derive ao caractere x e à expressão regular er, 
então uma prova natural aplica derive_corr a x e re para provar que x :: s =~ er dado 
s =~ derive x er, e vice-versa. *)

Theorem regex_casa_correto : casa_regex regex_casa.
Proof.
  unfold casa_regex.
  intros s. induction s as [ | a s' IHs].
    - apply casa_cadv_refl.
    - simpl. intros er. destruct (IHs (derive a  er)) as [H1 | H1'].  
      + apply ReflectT.  apply derive_corr. apply H1.
      + apply ReflectF. intros contra. apply H1'.
      apply derive_corr. apply contra.
Qed.