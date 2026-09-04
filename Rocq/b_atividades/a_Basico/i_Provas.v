(* Prova por Simplificação *)

(* Teorema: para todo n pertencente aos naturais, n + 0 = n*)
(* O comando 'Theorem' é ""igual"" ao 'Example' para o Rocq, mas para os leitores, 'Theorem' seria algo mais importante do que um exemplo*)
Theorem mais_0_n :
   forall (n : nat), (O + n = n).
Proof. 
   intros n. simpl. reflexivity. Qed.  (* A tática 'intros' significa: dado um um número arbitrário 'n' pertencente ao conjunto dos naturais *)

(* Esse teorema também pode ser demonstrado de outra maneira *)
Theorem mais_0_n' :
   forall (n : nat), (O + n = n).
Proof. 
   intros n. reflexivity. Qed.

(* Outra letra pode ser usada na prova *)
Theorem mais_0_n'' :
   forall (n : nat), (O + n = n).
Proof. 
   intros m. reflexivity. Qed.

(* Obs: 'intros', 'simpl' e 'reflexivity são táticas - comandos que são usados entre 'Proof' e 'Qed' *)

(* Outros Teoremas *)
Theorem mais_1_l :
   forall (n : nat), 1 + n = S n. (* Sucessor*)
Proof.
   intros n. reflexivity. Qed.

Theorem mult_0_1 :
   forall (n : nat), O * n = 0.
Proof.
   intros n. reflexivity. Qed.

(* Na maioria dos casos usamos 'simp' desnecessariamente, pois 'reflexivity' acaba a demonstração. 'simpl' foi usada muitas vezes para visualizar *)

(* Prova por Reescrita *)
Theorem mais_id_exemplo :
   forall (n m : nat) ,
   n = m -> n + n = m + m.

Proof.
   intros n m. (* Move ambos os quantificadores para o contexto*)
   intros H. (* Move a hipótese - chamamos de H - para o contexto *)
   rewrite -> H. (* Reesreve 'goal' usando a hipótese *)
reflexivity. Qed.

(* Exercício *)
Theorem mais_id_o:
   forall (n m o : nat),
   n = m -> m = o -> n + m = m + o.

Proof.
   intros n m o.
   intros H0.
   intros H1.
   rewrite -> H0.
   rewrite -> H1.
   reflexivity.
Qed.

(* O comando 'Check' também pode ser usado para examinar a sentença de lemas e teoremas previamente declarados -- Como exemplo, teoremas da biblioteca do Rocq *)
Check mult_n_O. (* forall n :nat, 0 = n * 0 *)

Check mult_n_Sm. (* forall n m : nat, n * m + n = n * S m*)

Theorem mult_n_0_m_0: 
   forall p q : nat,
   (p * 0) + (q * 0) = 0.

Proof.
   intros p q.
   rewrite <- mult_n_O.
   rewrite <- mult_n_O.
reflexivity. Qed.

(* Exercício *)
Theorem mult_n_1:
   forall p : nat,
   p * 1 = p.

Proof.
   intros p.
   rewrite <- mult_n_Sm.
   rewrite <- mult_n_O.
reflexivity. Qed.

(* Prova por Análise de Casos *)
Fixpoint igualb (n m : nat) : bool :=
   match n with 
   | O => match m with
          | O => true
          | S m' => false
          end
   | S n' => match m with
             | O => false
             | S m' => igualb n' m'
             end
   end.

Notation "x =? y" := (igualb x y)(at level 70): nat_scope.

Theorem mais_1_nig_o_primeiratentativa:
   forall n : nat,
   (n + 1) =? 0 = false.

Proof.
   intros n. 
   simpl. (* Não funciona nesse caso *)
Abort. (* Significa que desistimos da prova *)

(* A tática para considerar diferentes casos se chama 'destruct' *)
Theorem mais_1_nig_o :
   forall n : nat,
   (n + 1) =? 0 = false.

Proof.
   intros n. destruct n as [ | n'] eqn : E. (* Dividido em dois casos - [ | n] indica o nome introduzido em cada subgoal, 0 não recebe nenhum argumento e S recebe 1 *) (* 'E' diz para destruct dar esse nome para cada equação do subgoal *)
   - reflexivity.
   - reflexivity. Qed.

(* Provando que a negação é involutiva *)
Theorem negb_involutivo:
   forall b : bool,
   negb (negb b) = b.

Proof.
   intros b. destruct b eqn: E.
   - reflexivity.
- reflexivity. Qed.

(* É possível usar 'destruct' dentro de um subgoal, fazendo uma estrutura aninhada *)
Theorem andb_comutativo :
   forall b c,
   andb b c = andb c b.

Proof.
   intros b c. destruct b eqn: Eb.
   - destruct c eqn: Ec.
     + reflexivity.     (* O símbolo + uma repetição de símbolos '-', o que é igual a escrever '--' *)
     + reflexivity.
   - destruct c eqn : Ec.
     + reflexivity.
     + reflexivity.
Qed.

(* Nós também podemos fechar subgoals com chaves *)
Theorem andb_comutativo' :
   forall b c,
   andb b c = andb c b.

Proof.
   intros b c. destruct b eqn: Eb.
   { destruct c eqn: Ec.
     { reflexivity. }    (* O símbolo + uma repetição de símbolos '-', o que é igual a escrever '--' *)
     { reflexivity. }}
   { destruct c eqn : Ec.
     { reflexivity. }
     { reflexivity. }}
Qed.

(* Nós podemos usar chaves para indicar diferentes níveis de subgoals , além de poder reaproveitar o símbolo '-' em diferentes níveis *)
Theorem andb3_troca :
    forall b c d, andb (andb b c) d = andb (andb b d) c.

Proof.
   intros b c d. destruct b eqn: Eb.
   - destruct c eqn: Ec.
     { destruct d eqn: Ed.
        - reflexivity.
        - reflexivity. }
      {destruct d eqn: Ed.
        - reflexivity.
        - reflexivity. }
   - destruct c eqn : Ec.
      { destruct d eqn: Ed.
        - reflexivity.
        - reflexivity. }
      {destruct d eqn: Ed.
        - reflexivity.
        - reflexivity. }
Qed.

(* Exercício *)
 Theorem and_true_elim2 : forall b c : bool,
    andb b c = true -> c = true.

Proof.
   intros b c H.
   destruct c eqn: Ec.
      { destruct b eqn : Eb.
          - reflexivity.
          - reflexivity. }
      { destruct b eqn : Eb.
          - rewrite <- H. reflexivity.
          - rewrite <- H. reflexivity. }
Qed.

(* Outra solução *)
Theorem and_true_elim2' : forall b c : bool,
    andb b c = true -> c = true.

Proof.
   intros b c H.
   destruct b eqn : Eb.
    - simpl in H. (* H vira c = true *)
      rewrite H. reflexivity.
    - simpl in H. (* H vira false = true *)
         destruct c eqn: Ec.
         + reflexivity.
         + rewrite <- H. reflexivity.
Qed.
   

(* Exercício *)
Theorem zero_nbeq_plus_1 : forall n : nat,
   0 =? (n + 1) = false.

Proof.
   intros n. destruct n as [ |n'] eqn: E.
   - simpl. reflexivity.
   - simpl. reflexivity.   Qed.