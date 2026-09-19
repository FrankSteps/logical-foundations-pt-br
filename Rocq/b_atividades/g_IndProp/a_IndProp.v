(* Require Import LFPTBR.pasta.arquivo. *)

Set Warnings "-notation-overridden".
Require Import Nat.
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