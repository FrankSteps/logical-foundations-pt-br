(* Require Import LFPTBR.pasta.arquivo. *)

Set Warnings "-notation-overridden".
Require Import Nat.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import LFPTBR.a_Basico.i_Provas.
Require Import LFPTBR.f_Logica_em_Rocq.a_Logica.
Require Import LFPTBR.b_Inducao.a_Inducao.

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
  induction Hno as [|n' o' no'].
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

Theorem mais_le_compat_l : forall n m p,
  n <= m ->
  p + n <= p + m.
Proof.
  
