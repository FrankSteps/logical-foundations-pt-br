Require Import Arith.
Require Import Nat.

Inductive listanatural : Type :=
   | nil (* lista vazia *)
   | cons (n : nat) (l : listanatural). (* lista construída com outros dois tipos de dados - um número natural e outra lista *)

Definition minhalista := cons 1 (cons 3 nil).

(* Nova notação *)
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* Agora todas essas definições significam a mesma coisa *)
Definition minhalist1 := 1 :: (2 :: (3 :: nil)).
Definition minhalist2 := 1 :: 2 :: 3 :: [].
Definition minhalist3 := [1;2;3].

(* Funções em Listas *)

Fixpoint repete (n count : nat): listanatural :=
   match count with
   | 0 => nil
   | S count' => n :: (repete n count')
   end.

Compute repete 42 3. (* [42; 42; 42]*)


Fixpoint tamanho (lst : listanatural) : nat :=
   match lst with
   | nil => 0
   | h :: t => S (tamanho t)  (* h : head (cabeça), t: tail (calda) *)
   end.

Compute tamanho (repete 42 3). (* = 3 : nat *)


Fixpoint juntar (l1 l2 : listanatural) : listanatural :=
   match l1 with
   | [] => l2
   | h :: t => h :: (juntar t l2)
   end.

Compute juntar [1;2;3][4;5;6]. (* [1; 2; 3; 4; 5; 6]*)

(* Mudando notação de juntar *)
Notation "x ++ y" := (juntar x y)(right associativity, at level 60).

Example teste_juntar1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.

Example teste_juntar2: [] ++ [4;5] = [4;5].
Proof. reflexivity. Qed.

Example teste_juntar3: [1;2;3] ++ [] = [1;2;3].
Proof. reflexivity. Qed.

(* Funções Head e Tail *)
Definition hd (default: nat) (l : listanatural) : nat :=
   match l with
   | [] => default (* Lista vazia não tem head, ao invés de levantar exceção ele passa um valor default *)
   | h :: t => h
   end.

Definition tl (l : listanatural) : listanatural :=
   match l with 
   | [] => []
   | h :: t => t
   end.


Example teste_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.

Example teste_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.

Example teste_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

(********************* Exercícios ***********************)
Fixpoint sem_zeros (l:listanatural) : listanatural :=
   match l with 
   | [] => []
   | h :: t =>
            match h with
            | 0 => (sem_zeros t)
            | _ => h :: (sem_zeros t)
            end
   end.

Example teste_sem_zeros:
sem_zeros [0;1;0;2;3;0;0] = [1;2;3].

Proof.
reflexivity. Qed.

(* Função auxiliar que diz se número é ímpar *)
Fixpoint e_impar (n : nat) : bool :=
   match n with
   | 0 => false
   | S 0 => true 
   | S (S n') => e_impar n'
   end.

 Fixpoint membros_impares (l: listanatural) : listanatural :=
    match l with
    | [] => []
    | h :: t =>
               match e_impar h with
               | true => h :: membros_impares t
               | false => membros_impares t 
               end
   end.

Example teste_membros_impares:
membros_impares [0;1;0;2;3;0;0] = [1;3].

Proof.
reflexivity. Qed.

Definition contar_numeros_impares (l:listanatural) : nat :=
   match l with
   | [] => 0
   | _ => tamanho (membros_impares l)
   end.

Example teste_contar_numeros_impares1:
contar_numeros_impares [1;0;3;1;4;5] = 4.

Proof.
reflexivity. Qed.

Example teste_contar_numeros_impares2:
contar_numeros_impares [0;2;4] = 0.

Proof.
reflexivity. Qed.

Example teste_contar_numeros_impares3:
contar_numeros_impares nil = 0.

Proof.
reflexivity. Qed.

(* Lista que é a alternância de duas listas *)
Fixpoint alternar (l1 l2 : listanatural) : listanatural :=
   match l1, l2 with 
   | [] , _ => l2
   | _ , [] => l1
   | h1 :: t1 , h2 :: t2 => h1 :: h2 :: (alternar t1 t2)
   end.

Example teste_alternar1:
alternar [1;2;3] [4;5;6] = [1;4;2;5;3;6].

Proof.
reflexivity. Qed.

Example teste_alternar2:
alternar [1] [4;5;6] = [1;4;5;6].

Proof.
reflexivity. Qed.

Example teste_alternar3:
alternar [1;2;3] [4] = [1;4;2;3].

Proof.
reflexivity. Qed.

Example teste_alternar:
alternar [] [20;30] = [20;30].

Proof.
reflexivity. Qed.


(* Bags via Listas*)
(* Um bag (ou multiconjunto) é como um conjunto, exceto 
que cada elemento pode aparecer múltiplas vezes,
ao invés de apenas uma *)

(* Uma das maneiras de representar um bag de números 
é como uma lista *)

Definition bag := listanatural.

(* Exercícios *)

(* Conta quantas vezes um número 'v' aparece na bag *)
Fixpoint count (v : nat) (s : bag) : nat :=
   match s with
   | [] => 0
   | h :: t => if v =? h
               then S (count v t)
               else count v t
   end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof.
reflexivity.   Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. 
reflexivity. Qed.

(* bag que contem todos os elementos de a e de b *)
Definition sum : bag -> bag -> bag := juntar.

Example teste_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof.
reflexivity. Qed.

(* Adicona um valor v como head da bag *)
Definition add (v : nat) (s : bag) : bag :=
   match s with
   | [] => v :: nil
   | h :: t => v :: s
   end.

Example teste_add1: count 1 (add 1 [1;4;1]) = 3.
Proof.
reflexivity. Qed.
 
Example teste_add2: count 5 (add 1 [1;4;1]) = 0.
Proof.
reflexivity. Qed.

(* Se um valor é membro ou não do bag *)
Fixpoint membro (v : nat) (s : bag) : bool :=
   match s with 
   | [] => false
   | h :: t => if v =? h
               then true
               else membro v t     
   end.


Example teste_membro1: membro 1 [1;4;1] = true.
Proof.
reflexivity. Qed.

Example teste_membro2: membro 2 [1;4;1] = false.
Proof.
reflexivity. Qed.

(* Remove a primeira ocorrência de um número da bag *)
Fixpoint remove_um (v : nat) (s : bag) : bag :=
   match s with
   | [] => []
   | h :: t =>
              if v =? h
              then t
              else h :: remove_um v t
   end.


Example teste_remove_um1:
count 5 (remove_um 5 [2;1;5;4;1]) = 0.

Proof.
reflexivity. Qed.
  
Example teste_remove_um2:
count 5 (remove_um 5 [2;1;4;1]) = 0.

Proof.
reflexivity. Qed.
 
Example teste_remove_um3:
count 4 (remove_um 5 [2;1;4;5;1;4]) = 2.

Proof.
reflexivity. Qed.
 
Example teste_remove_um4:
count 5 (remove_um 5 [2;1;5;4;5;1;4]) = 1.

Proof.
reflexivity. Qed.

(* Remove todas as ocorrências de um valor na bag *)
Fixpoint remove_todos (v:nat) (s:bag) : bag :=
   match s with
   | [] => []
   | h :: t =>
              if v =? h
              then remove_todos v t
              else h :: remove_todos v t
   end.


Example teste_remove_todos1: 
count 5 (remove_todos 5 [2;1;5;4;1]) = 0.

Proof.
reflexivity. Qed.

Example teste_remove_todos2: 
count 5 (remove_todos 5 [2;1;4;1]) = 0.

Proof.
reflexivity. Qed.

Example teste_remove_todos3: 
count 4 (remove_todos 5 [2;1;4;5;1;4]) = 2.

Proof.
reflexivity. Qed.

Example teste_remove_todos4: 
count 5 (remove_todos 5 [2;1;5;4;5;1;4;5;1;4]) = 0.

Proof.
reflexivity. Qed.


Fixpoint incluido (s1 : bag) (s2 : bag) : bool :=
   match s1 with
   | [] => true
   | h1 :: t1 => 
                if (membro h1 s2) (* se membro h1 s2 for true *)
                then incluido t1 (remove_um h1 s2)
                else false
   end.

Example teste_incluido1: incluido [1;2] [2;1;4;1] = true.

Proof.
reflexivity. Qed.
 
Example test_incluido2: incluido [1;2;2] [2;1;4;1] = false.

Proof.
reflexivity. Qed.


(*Adicionar um valor a bag deveria incrementar o valor de
 count em um *)

Theorem add_inc_count : forall (v : nat)(b : bag),
   tamanho (add v b) = S(tamanho b).

Proof.
   intros v b.
   induction b as [ | h t IHb].
   - reflexivity.
   - reflexivity.
Qed.
    

(* Teorema com Listas *)
Theorem nil_juntar : forall (lst : listanatural),
   [] ++ lst = lst.
Proof. reflexivity. Qed.

Theorem tl_tamanho_predecessor: forall (lst:listanatural),
   pred (tamanho lst) = tamanho (tl lst). (* tamanho da lista - 1 = tamanho do tail *)

Proof.
    intros lst. destruct lst as [ | h t].
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

(* Usando induções em teoremas de listas *)
Theorem juntar_assoc : forall (lst1 lst2 lst3 : listanatural),
   (lst1 ++ lst2) ++ lst3 = lst1 ++ (lst2 ++ lst3).

Proof.
   intros lst1 lst2 lst3. induction lst1 as [ | h1 t1].
   reflexivity.
   simpl. rewrite -> IHt1. reflexivity.
Qed.

(* Reverte Lista *)
Fixpoint rev (lst : listanatural) : listanatural :=
   match lst with
   | [] => []
   | h :: t => rev t ++ [h]
   end.

Example teste_rev1:     rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example teste_rev2:     rev [] = [].
Proof. reflexivity. Qed.

(* Tamnho do inverso da lista é o mesmo que o original *)
Theorem rev_tamanho_primeira_tentativa : forall (lst : listanatural),
   tamanho (rev lst) = tamanho lst.

Proof.
   intros lst. induction lst as [ | h t].
   - reflexivity.
   - simpl. rewrite <- IHt.
Abort.

(* Temos que provar um lema antes *)
Theorem juntar_tamanho : forall (lst1 lst2 : listanatural),
   tamanho (lst1 ++ lst2) = (tamanho lst1) + (tamanho lst2).

Proof.
   intros lst1 lst2. induction lst1 as [ | h1 t1].
   - reflexivity.
   - simpl. rewrite IHt1. reflexivity.
Qed.

(* Agora provando *)
Theorem rev_tamanho : forall (lst : listanatural),
   tamanho (rev lst) = tamanho lst.

Proof.
   intros lst. induction lst as [ | h t].
   - reflexivity.
   - simpl. rewrite -> juntar_tamanho.
     simpl. rewrite -> IHt. rewrite Nat.add_comm. (* importado da biblioteca *)
     reflexivity.
Qed.

(************************* Search ***********************)
(* Para ajudar a lembrar o nome ou a forma de teorema,
o Rocq possui o comando 'Search' *)
Search rev. (* Mostra uma lista de todos os teoremas envolvendo rev *)

Search (_ + _ = _ + _). (* Procura todos os teoremas com essa forma, da biblioteca *)

(* Criação de Module para o próximo exemplo *)
Module Induction.
   Theorem ex_search_simples : forall (a b : nat),
  a + b = a + b.
Proof.
  intros a b.
  reflexivity.
Qed.

End Induction.

Search (_ + _ = _ + _) inside Induction. (* Pesquisar em um Module particular *)

Search (?x + ?y = ?y + ?x). (* Ao invés de usar o coringa '_', dá para usar variáveis na pesquisa de padrões *)

(********************** Lista de Exercícios - Parte 1 *********************)
(* Exercício - Listas *)
Theorem juntar_nil_r : forall l : listanatural,
  l ++ [] = l.

Proof.
   intros l. induction l as [ | h t IHl].
   - reflexivity.
   - simpl. rewrite <- nil_juntar. assert (Haux : t ++ [] = t). {
      induction t as [ | h' t' IHt'].
      - reflexivity.
      - rewrite IHl. reflexivity.
   }
   rewrite Haux. reflexivity.
Qed.

Theorem rev_juntar_distr: forall l1 l2 : listanatural,
  rev (l1 ++ l2) = rev l2 ++ rev l1.

Proof.
   intros l1 l2.
   induction l1 as [ | h1 t1 IHl1].
   - simpl. rewrite juntar_nil_r. reflexivity.
   - simpl. rewrite <- juntar_assoc. rewrite IHl1. reflexivity.
Qed.

(* Uma involução é uma função que é a sua própia inversa, isso é, aplicando ela duas vezes volta para a entrada original *)
Theorem rev_involutivo : forall l : listanatural,
  rev (rev l) = l.

Proof.
   intros l.
   induction l as [ | h t IHl].
   - simpl. reflexivity.
   - simpl. rewrite rev_juntar_distr. simpl. rewrite IHl. reflexivity.
Qed.

Theorem juntar_assoc4 : forall l1 l2 l3 l4 : listanatural,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.

Proof.
   intros l1 l2 l3 l4.
   induction l1 as [ | h1 t1 IHl1].
   - simpl. rewrite juntar_assoc. reflexivity.
   - simpl. rewrite <- IHl1. reflexivity.
Qed.

Lemma sem_zeros_juntar : forall l1 l2 : listanatural,
  sem_zeros (l1 ++ l2) = (sem_zeros l1) ++ (sem_zeros l2).

Proof.
   intros l1 l2.
   induction l1 as [ | h1 t1 IHl1].
   - simpl. reflexivity.
   - simpl. destruct h1.
     + rewrite IHl1. reflexivity.
     + simpl. Set Printing Parentheses. rewrite IHl1. reflexivity.
Qed. 

(* Exercícios - eqblist *)
Fixpoint eqblist (l1 l2 : listanatural) : bool :=
   match l1, l2 with
   | [] , [] => true
   | [] , _ => false
   | _ , [] => false
   | h1 :: t1 , h2 :: t2 =>
                           if eqb h1 h2
                           then eqblist t1 t2
                           else false
  end.


Example teste_eqblist1 : (eqblist nil nil = true).
Proof.
reflexivity. Qed.

Example teste_eqblist2 : eqblist [1;2;3] [1;2;3] = true.
Proof.
reflexivity. Qed.

Example teste_eqblist3 : eqblist [1;2;3] [1;2;4] = false.
Proof.
reflexivity. Qed.

(* Lema Auxiliar *)
Lemma eqb_refl : forall n : nat, eqb n n = true.
Proof.
  induction n as [ | n' IHn].
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem eqblist_refl : forall l: listanatural,
  true = eqblist l l.
Proof.
 intros l. induction l as [ | h t IHl].
 - reflexivity.
 - simpl. rewrite eqb_refl. rewrite <- IHl. reflexivity.
Qed.


(****************************** Lista de Exercícios - Parte 2 *****************************)
(* Teoremas sobre bags *)
Theorem count_membro_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.

Proof.
   intros s.
   reflexivity. Qed.

(* O seguinte lema sobre leb pode ser útil no próximo exercício (e nos próximos capítulos) *)
Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [ | n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

(* Exercício - 3 estrelas *)

(* Lema Auxiliar *)
Lemma le_succ_diag_r : forall n : nat,
  (n <=? S n) = true.
Proof.
  induction n as [ | n' IHn].
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem remove_nao_incrementa_count : forall (s : bag),
  (count 0 (remove_um 0 s)) <=? (count 0 s) = true.

Proof.
  intros s. induction s as [ | h t IHs'].
  - reflexivity.
  - simpl. destruct h.
    +  simpl. rewrite le_succ_diag_r. reflexivity.
    + simpl. rewrite IHs'. reflexivity.
Qed.

(* Prove que toda involução é injetiva *)
Theorem involucao_injetiva : forall (f : nat -> nat),
    (forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).

Proof.
   intros f Hinv n1 n2 Heq.
   rewrite (Hinv n1).
   rewrite Heq.
   rewrite <- (Hinv n2).
   reflexivity.
Qed.

 
 


(********************* Options **************************)

(* Função para retornar o n-ésimo elemento de uma lista*)
Fixpoint enesimo_ruim (lst : listanatural)(n : nat) : nat :=
   match lst with
   | [] => 42 (* Valor arbitrário *)
   | h :: t =>
       match n with
       | 0 => h
       | S k => enesimo_ruim t k
       end
   end.

(* Fazendo melhorias *)
(* A função acima é parcial e  não total, pois tem 
valores que não produzem saída válida. Para funções 
parciais, uma solução possível é criar um novo tipo,
que indica se tem ou não tem um valor como retorno *)
Inductive natoption : Type :=
   | Some (n : nat)  (* Se tiver algo para retornar*)
   | None.           (* Se não tiver nada para retornar*)

Fixpoint enesimo_erro (lst : listanatural) (n : nat) : natoption :=
   match lst with
   | [] => None
   | h :: t =>
        match n with
        | 0 => Some h
        | S k => enesimo_erro t k
        end
   end.

Example teste_enesimo_erro1 : enesimo_erro [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.

Example teste_enesimo_erro2 : enesimo_erro [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.

Example teste_enesimo_erro3 : enesimo_erro [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

(* Um casamento de padrão simultâneo deixa o código mais limpo *)
Fixpoint enesimo_erro' (lst : listanatural) (n : nat) : natoption :=
   match lst, n with
   | [], _ => None
   | h :: _, 0 => Some h
   | _ :: t, S k => enesimo_erro' t k
   end.

Example teste_enesimo_erro1' : enesimo_erro [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.

Example teste_enesimo_erro2' : enesimo_erro [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.

Example teste_enesimo_erro3' : enesimo_erro [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

(********************** Partial Maps ********************)

(* Semelhante a dicionário *)
(* Mapas podem ser parciais, porque podem existir chaves que não são mapeadas *)

Inductive partial_map : Type :=
| Empty
| Binding (k : nat)(v : nat)(m : partial_map).

(* Fazer um update do binding da chave k para o valor v num mapa existente m *)
Definition update (k : nat)(v : nat)(m : partial_map) : partial_map :=
   Binding k v m.

(* Implementando uma função de busca *)
Fixpoint busca (k : nat)(m : partial_map) : natoption :=
   match m with 
   | Empty => None
   | Binding k2 v m' =>
       if k =? k2 then Some v else busca k m'
       end.

Theorem busca_update : forall (m : partial_map)(k v : nat),
   busca k (update k v m) = Some v.

Proof.
   intros m k v. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.