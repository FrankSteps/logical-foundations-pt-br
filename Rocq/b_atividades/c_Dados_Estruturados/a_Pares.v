(* Pares de Números *)
 
Inductive produto_cartesiano_nat : Type :=
   | par (n1 n2 : nat).

Check (par 3 5) : produto_cartesiano_nat.

Definition primeiro (p: produto_cartesiano_nat) : nat :=
   match p with
   | par x y => x
   end.

Definition segundo (p: produto_cartesiano_nat ) : nat :=
   match p with
   | par x y => y
   end.

Compute (primeiro (par 3 5)).
(* = 3  : nat *)

(* Mudando a notação - Agora par é (x , y)*)
Notation "( x , y )" := (par x y).

(* Usando a nova notação *)
Compute (primeiro (3 , 5)).

Definition primeiro' (p : produto_cartesiano_nat) : nat :=
   match p with
   | (x,y) => x
   end.

Definition segundo' (p: produto_cartesiano_nat ) : nat :=
   match p with
   | (x,y) => y
   end.

(* Trocando os pares *)
Definition troca_par (p : produto_cartesiano_nat) : produto_cartesiano_nat :=
   match p with
   | (x,y) => (y,x)
   end.

(* Obs: Casamento de padrões em um par é diferente da sintaxe do casamento de múltiplos padrões - que é sem parênteses - cuidado para não fazer definições de maneira incorreta *)

(* Às vezes, se algumas propriedades de pares forem declaradas de determinada maneira, é possível provar só com reflexivity *)
Theorem emparelhamento_sobrejetor' : forall (n m : nat),
   (n,m) = (primeiro (n,m) , segundo (n,m)).
Proof.
reflexivity. Qed.

(* Mas, às vezes reflexivity não é suficiente se o lema for declarado de uma maneira mais natural *)
Theorem emparelhamento_sobrejetor_preso' : forall (p : produto_cartesiano_nat),
   p  = (primeiro p , segundo p).
Proof.
   simpl. (* Não reduz nada! *)
Abort.

(* Então é necessário destrinchar (destruct) a estrutura de p para que simpl possa fazer o casamento de padrões em primeiro e segundo *)
Theorem emparelhamento_sobrejetor : forall (p : produto_cartesiano_nat),
   p  = (primeiro p , segundo p).
Proof.
   intros p. destruct p as [n m]. simpl. reflexivity.
Qed.

(* Exercício *)
Theorem segundo_primeiro_igual_troca :
   forall (p : produto_cartesiano_nat),
   (segundo p , primeiro p) = troca_par p.

Proof.
   intros p. destruct p as [n m]. simpl. reflexivity.
Qed.

Theorem primeiro_troca_igual_segundo :
   forall (p : produto_cartesiano_nat),
   primeiro (troca_par p) = segundo p.

Proof.
   intros p. destruct p as [n m]. simpl. reflexivity.
Qed.