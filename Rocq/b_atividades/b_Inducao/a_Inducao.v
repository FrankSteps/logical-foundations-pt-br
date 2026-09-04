Require Import Arith.
Require Import Nat.

(* Provar o próximo teorema usando 'reflexivity não funciona, pois o n é um número arbitrário *)

Theorem add_0_r_primeiratentativa :
   forall n : nat,
   n + 0 = n.

Proof.
   intros n.
   simpl. (* Não faz nada *)
Abort.

Theorem add_0_r_segundatentativa :
   forall n : nat,
   n + 0 = n.

(* Mesmo fazendo vários destruct, não acontece nada, pois n pode ser arbitrariamente grande *)
Proof.
   intros n.
   destruct n as [ | n'].
   reflexivity.
   simpl. (* Não faz nada *)
Abort.

(* Casos como esse podem ser resolvidos através de recursão *)
(* Queremos provar P(n) -- Primeiro, temos o subgoal P(0) -- Segundo, temos o subgoal P(n') -> P(S n') *)
Theorem add_0_r :
   forall n : nat,
   n + 0 = n.

Proof.
    intros n. induction n as [ | n' IHn']. (* Nomes das variáveis a serem introduzidas como subgoal *)
    - reflexivity.
    - simpl. rewrite -> IHn'. reflexivity. 
Qed.

Theorem menos_n_n:
   forall n: nat, minus n n = 0.

Proof.
   intros n. induction n as [ | n' IHn'].
   - simpl. reflexivity.
   - simpl. rewrite -> IHn'. reflexivity.
Qed.

(* Exercício *)
Theorem nult_0_r:
   forall n: nat, mult n 0 = 0.

Proof.
   intros n. induction n as [ | n' IHn'].
   - simpl. reflexivity.
   - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mais_n_Sm:
   forall n m: nat, S(n + m) = n + S(m).

Proof.
   intros n m. induction n as [ | n' IHn'].
   - simpl. reflexivity.
   - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_comutativo:
   forall n m: nat, n + m = m + n.

Proof.
   intros n m. induction n as [ | n' IHn'].
   - induction m as [ | m' IHm'].
    + reflexivity.
    + simpl. rewrite <- IHm'. simpl. reflexivity.
   - simpl. rewrite IHn'. rewrite <- mais_n_Sm. reflexivity.
Qed.

Theorem add_associativo:
   forall n m p: nat, 
   n + (m + p) = (n + m) + p.

Proof.
   intros n m p. induction n as [ | n' IHn'].
   - simpl. reflexivity.
   - simpl. rewrite -> IHn'. reflexivity.
Qed.

(* Exercício *)

Fixpoint double (n : nat) :=
   match n with
   | 0 => 0
   | S n' => S (S (double n'))
   end.

Lemma double_mais:
   forall n, double n = n + n.

Proof.
   intros n. induction n as [ | n' IHn'].
   - simpl. reflexivity.
   - simpl. rewrite -> IHn'. rewrite -> mais_n_Sm. reflexivity.
Qed.

(* Exercício *)

Theorem eqb_refl:
   forall n: nat, (n =? n) = true.

Proof.
   intros n. induction n as [ | n' IHn'].
   - simpl. reflexivity.
   - simpl. rewrite IHn'. reflexivity.
Qed.

(* Exercício -- Descrição alternativa de par de (S n) que funciona melhor para indução *)

Theorem negb_involutivo: (* Necessário mais tarde *)
   forall b : bool,
   negb (negb b) = b.

Proof.
   intros b. destruct b eqn: E.
   - reflexivity.
- reflexivity. Qed.

Theorem S_par:
   forall n: nat, even (S n) = negb (even n).

Proof.
   intros n. induction n as [ | n' IHn'].
   - simpl. reflexivity.
   - rewrite IHn'. simpl. rewrite negb_involutivo. reflexivity.

(* Provas dentro de provas *)
(* Usando a tática assertion *)

Theorem mult_0_mais : forall n m: nat,
   (n + 0 + 0) * m = n * m.

Proof.
   intros n m.
   assert (H: n + 0 + 0 = n). (* O nome da asserção é H. Queremos provar ess asserção *)
      { Set Printing Parentheses. rewrite add_comutativo. simpl. rewrite add_comutativo. reflexivity. }
       (* Set Printin Parentheses, faz com que o Rocq coloque toda a expressão entre parênteses *)
       rewrite -> H.
       reflexivity. Qed.

Theorem rearranjo_adicao_1tentativa : forall n m p q : nat,
   (n + m) + (p + q) = (m + n) + (p + q).

Proof.
   intros n m p q.
   Set Printing Parentheses. rewrite add_comutativo. (* Não irá funcionar, pois vai trocar a ordem da soma mais exterior *)
Abort.

(* Para resolver isso, vamos usar assert *)
Theorem rearranjo_adicao : forall n m p q : nat,
   (n + m) + (p + q) = (m + n) + (p + q).

Proof.
   intros n m p q.
   assert(H: n + m = m + n). (* Quando um rewrite não encontra a instância exata desejada, 'assert' a instância desejada, prove com um teorema auxiliar e rewrite com a hipótese introduzida pelo assert *)
   {
      rewrite add_comutativo. reflexivity.
   }
   rewrite H. reflexivity. Qed.

(* Usando a tática 'replace' *)
Theorem mult_0_mais' : forall n m : nat,
   (n + 0 + 0) * m = n * m.

Proof.
   intros n m.
   replace(n + 0 + 0) with n. (* Introduz dois subgoals -- um igual ao anterior substituindo pelo que desejamos, o outro para provar que o que acabou de ser introduzido é igual ao anterior *)
   - reflexivity.
   - rewrite add_comutativo. simpl. rewrite add_comutativo. reflexivity.
Qed.

Theorem rearranjo_adicao' : forall n m p q : nat,
   (n + m) + (p + q) = (m + n) + (p + q).

Proof.
   intros n m p q.
   replace (n + m) with (m + n).
   - reflexivity.
   - rewrite add_comutativo. reflexivity.
Qed.

(* Provas Formais e Informais *)
(* Prova Formal - pode ser difícil para um humano compreender *)
Theorem add_associativo' : forall n m p: nat,
   n + (m + p) = (n + m) + p.

Proof.
   intros n m p. induction n as [ | n' IHn']. reflexivity.
   simpl. rewrite IHn'. reflexivity.  Qed.

(* Para facilitar o entendimento, comentários e bullets (-) podem ser usados para tornar semelhante a uma prova informal, que será mais facilmente compreendida pelo leitor *)
Theorem add_associativo'' : forall n m p: nat,
   n + (m + p) = (n + m) + p.

Proof.
   intros n m p. induction n as [ | n' IHn']. 
   - (* n = 0 *)
   reflexivity.
   - (* n = S n' *)
   simpl. rewrite IHn'. reflexivity.  Qed.

(* Uma prova poderia ser escrite em linguagem natural como:
   Teorema: Para qualquer n, m e p.
        n + (m + p) = (n + m) + p.
   Prova : Por indução de n.
   -Primeiro, suponha que n = 0. Devemos provar que
      0 + (m + p) = (0 + m) + p.
      Isso segue da definição de + (soma).
   - Depois, suponha que n = S n', onde
      n' + (m + p) = (n' + m) + p.
   Nós devemos mostrar agora que 
      (S n') + (m + p) = ((S n') + m) + p.
   Pela definição de +, segue que
      S(n' + (m + p)) = S((n' + m) + p),
   que é imediato da hipótese de indução. Qed.
 *)

 (* Exercício *)

 (* 
    Prova: Por indução em n e, em cada caso, por indução em m.

    Caso n = 0:
    Devemos mostrar que 0 + m = m + 0. Fazemos indução em m:

        Se m = 0:
        Devemos mostrar que 0 + 0 = 0 + 0, o que é imediato por reflexividade.

        Se m = S m', com a hipótese de indução (0 + m' = m' + 0):
        Devemos mostrar que 0 + (S m') = (S m') + 0.
        Por simplificação e usando a hipótese de indução de m, a igualdade
        se mantém, completando o caso n = 0.

    Caso n = S n', com a hipótese de indução (n' + m = m + n'):
    Devemos mostrar que (S n') + m = m + (S n').
    Por simplificação e reescrita usando a hipótese de indução de n,
    junto com o lema mais_n_Sm para ajustar o sucessor, o objetivo
    é reduzido a uma identidade.
    Isso encerra todos os casos. Qed.
    *)


Theorem add_rearranjo3 : forall n m p: nat,
   n + (m + p) = m + (n + p).

Proof.
    intros n m p.
    rewrite add_associativo.
    replace ( n + m) with (m + n).
    - rewrite add_associativo. reflexivity.
    - rewrite add_comutativo. reflexivity.
Qed.

(* Exercício : Agora prove a comutatividade da multiplicação. Você provavelmente vai querer olhar para (ou definir e provar) um teorema "helper" para ser usado nessa prova. Dica: o que é n × (1 + k)?*)

(* Helper 1 *)
Lemma mul_0_r : forall n : nat,
  n * 0 = 0.

Proof.
   intros n.
   induction n as [ | n' IHn'].
   - simpl. reflexivity.
   - simpl. rewrite -> IHn'. reflexivity.
Qed. 

(* Helper 2 *)
Lemma mul_S_r : forall n k : nat,
  n * S k = n * k + n.

Proof.
  intros n k.
  induction n as [ | n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. replace (S k + (n' * k + n')) with (k + n' * k + S n').
  rewrite add_associativo.
  rewrite mais_n_Sm. 
  reflexivity.

  rewrite add_associativo.
  simpl.
  rewrite mais_n_Sm.
  reflexivity.
Qed.

Theorem mul_comutativo: forall m n: nat,
   m * n = n * m.

Proof.
   intros m n.
   induction m as [ | m' IHm'].
   simpl. rewrite mul_0_r. reflexivity.
   simpl. rewrite mul_S_r. rewrite add_comutativo. rewrite IHm'. reflexivity.
Qed. 

Theorem leb_reflexivo: forall n: nat,
   (n <=? n) = true.

Proof.
   intros n.
   induction n as [ | n' IHn'].
   simpl. reflexivity.
   simpl. rewrite  IHn'. reflexivity.
Qed.


Theorem zero_neqb_S: forall n: nat,
   0 =? (S n) = false.

Proof.
   intros n.
   simpl. reflexivity.
Qed.


Theorem andb_false_r : forall b : bool,
   andb b false  = false.

Proof.
   intros b.
   destruct b.
   - simpl. reflexivity.
   - simpl. reflexivity.
Qed.

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.

Proof.
   intros n.
   simpl. reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 
   1 * n = n.

Proof.
   intros n.
   simpl.
   induction n as [ | n' IHn'].
   - reflexivity.
   - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
   orb
     (andb b c)
     (orb (negb b)
          (negb c))
   = true.

Proof.
   intros b c. destruct b.
   - destruct c.
   + simpl. reflexivity.
   +simpl. reflexivity.
   - destruct c.
   + simpl. reflexivity.
   + simpl. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p: nat,
   (n + m) * p = (n * p) + (m * p).

Proof.
   intros n m p. induction n as [ | n' IHn'].
   - simpl. reflexivity.
   - simpl. rewrite IHn'. rewrite add_associativo. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
   n * (m * p) = (n * m) * p.

Proof.
   intros n m p. induction n as [ | n' IHn'].
   - simpl. reflexivity.
   - simpl. rewrite mult_plus_distr_r. rewrite IHn'. reflexivity.
Qed.

(* Natural para Binário e de volta para Natural *)

(* Retomando o tipo bin *)
Inductive bin : Type :=
   | Z 
   | B0 (n : bin)
   | B1 (n : bin).

(* Retomando com as definições do módulo Básico *)
Fixpoint incr (m : bin) : bin :=
   match m with
   | Z => B1 Z
   | B0 x => B1 x
   | B1 x => B0 (incr x)
   end.

Fixpoint bin_para_nat (m:bin) : nat :=
   match m with
   | Z => 0
   | B0 x => mult 2 (bin_para_nat x)
   | B1 x => (mult 2 (bin_para_nat x)) + 1
   end.

(* Incrementar um número binário e depois converter para natural (unário) é o mesmo que convertê-lo para natural primeiro e depois incrementá-lo *)

Theorem mais_1_l :
   forall (n : nat), 1 + n = S n. (* Sucessor*)
Proof.
   intros n. reflexivity. Qed.

Theorem bin_to_nat_pres_incr : forall b : bin,
   bin_para_nat (incr b) = 1 + bin_para_nat b.

Proof.
   intros b. induction b as [ | B0 IHB0' | B1' IHB1'].
   - simpl. reflexivity.
   - simpl. rewrite add_comutativo. rewrite mais_1_l. reflexivity.
   - simpl. rewrite IHB1'. rewrite add_0_r. rewrite mais_1_l. rewrite plus_Sn_m. f_equal. rewrite add_0_r. rewrite <- mais_1_l. rewrite <- add_associativo. rewrite (add_comutativo _ 1). reflexivity.
Qed.

(* Função que converte números naturais para binários *)
Fixpoint nat_para_bin (n : nat) : bin:=
   match n with
   | 0 => Z 
   | S n' => incr (nat_para_bin n')
   end.

Theorem nat_bin_nat : forall n,
   bin_para_nat (nat_para_bin n) = n.

Proof.
   intros n. induction n as [ | n' IHn'].
   simpl. reflexivity.
   simpl. rewrite bin_to_nat_pres_incr. rewrite IHn'. rewrite mais_1_l. reflexivity.
Qed.

(* Converte bin para nat e depois de novo para bin dá problema *)
Theorem bin_nat_bin_falha : forall b, 
   nat_para_bin (bin_para_nat b) = b.
Abort.

(* Como visto, converter binário para natural e de volta para binário dá problema. Uma versão modificada vai ser provada usando os próximos lemas *)
Lemma  double_incr : forall n : nat,
   double (S n) = S (S (double n)).

Proof.
   intros n. induction n as [ | n' IHn'].
   simpl. reflexivity.
   simpl. rewrite <- IHn'. reflexivity.
Qed. 

(* Definindo o dobro de um número binário *)
Definition double_bin (b : bin) : bin :=
   match b with
   | Z => Z 
   | B0 x => B0 (B0 x)
   | B1 x => B0 (B1 x)
   end.

Example double_bin_zero : double_bin Z = Z.
Proof. simpl. reflexivity. Qed.

Lemma double_incr_bin : forall b,
   double_bin (incr b) = incr (incr (double_bin b)).

Proof.
   intros b. induction b as [ | BO' IHBO' | B1' IHB1'].
   simpl. reflexivity.
   simpl. reflexivity.
   simpl. reflexivity.
Qed.

(* Voltando par bin_nat_bin_falha, ele falha porque depois de conveter de volta para o binário ele gera um número equivalente à b, mas não é visto como igual pelo Rocq *)
(* POR QUE O TEOREMA FALHA:
   
   O teorema falha porque a representação em binário (`bin`) não é única. 
   É possível ter múltiplos termos `bin` que representam o mesmo número 
   natural (devido a "zeros extras", como a diferença entre 5 e 005).

   1. `bin_to_nat` transforma a forma "inflada" (ex: 005) no `nat` único (5).
   2. `nat_to_bin` reconverte esse `nat` na forma binária limpa/simplificada (5).

   Como o Coq exige igualdade estrutural estrita, o teorema falha porque 
   a forma simplificada de volta não é idêntica à forma inflada original.
   Exemplo: `nat_to_bin (bin_to_nat (B0 Z)) = Z`, mas `Z ≠ B0 Z`.
*)

(* Criando uma função de normalização que seleciona o binário mais simples *)
Fixpoint normalize (b : bin) : bin :=
  match b with
  | Z => Z
  | B1 m => B1 (normalize m)
  | B0 m => 
      match normalize m with
      | Z => Z  
      | n => B0 n 
      end
  end.

Example teste_normalize_1 : 
  normalize (B1 (B0 (B1 Z))) = B1 (B0 (B1 Z)).

Proof.
simpl. reflexivity. Qed.

Example teste_normalize_2 : 
  normalize (B0 (B0 (B1 Z))) = B0 (B0 (B1 Z)).

Proof.
simpl. reflexivity. Qed.

Example test_normalize_3 : 
  normalize (B0 (B0 (B0 Z))) = Z.

Proof.
simpl. reflexivity. Qed.

(* Agora provando o teorema principal *)
Theorem bin_nat_bin: forall b, 
   nat_para_bin (bin_para_nat b) = normalize b.
   
Proof.
   intros b. induction b as [ | B0' IHB0'| B1' IHB1'].
   -simpl. reflexivity.
   -simpl. rewrite add_0_r. rewrite <- double_mais. assert (H_double : forall n, nat_para_bin (double n) = double_bin (nat_para_bin n)).
{
  induction n as [ | n' IHn].
  - simpl. reflexivity.
  - simpl. rewrite double_incr_bin. rewrite IHn. reflexivity.
}
  rewrite H_double. rewrite IHB0'. reflexivity.
  - simpl. rewrite add_0_r. rewrite <- add_associativo. rewrite <- mais_n_Sm. rewrite add_0_r. rewrite <- mais_n_Sm. rewrite <- double_mais. simpl. assert (H_double : forall n, nat_para_bin (double n) = double_bin (nat_para_bin n)).
{
  induction n as [ | n' IHn].
  - simpl. reflexivity.
  - simpl. rewrite double_incr_bin. rewrite IHn. reflexivity.
}
  rewrite H_double. rewrite IHB1'. destruct (normalize B1').
     + reflexivity.
     + reflexivity.
     + reflexivity.
Qed. 