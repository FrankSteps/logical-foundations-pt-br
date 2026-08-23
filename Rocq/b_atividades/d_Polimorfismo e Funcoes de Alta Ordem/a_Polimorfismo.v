(* Listas polifórmicas *)
(* Ao invés de criarmos uma lista para cada tipo, podemos
 usar uma definição polifórmica que permite implementar 
 listas de qualquer tipo *)

 Inductive lista (X : Type) : Type := (* Parecido com Generics em Java *)
 | nil 
 | cons (x : X)(l : lista X). (* x seria head do tipo X passado e l seria tail do tipo X passado *)

 (* list é uma função de types para types *)
 Check lista : Type -> Type.

 (* O 'X' na definição de 'lista' se torna um parâmetro  para os construtores da lista 'nil' e 'cons' *)
 Check (nil nat) : lista nat.

 Check (cons nat 3 (nil nat)) : lista nat.

 Check nil : forall (X : Type), lista X.

 Check cons : forall (X : Type), X -> lista X -> lista X.

 Check (cons nat 2 (cons nat 1 (nil nat))) : lista nat.

 (* Versões polimórficas de funções apresentadas anteriormente *)

 Fixpoint repete (X : Type)(x : X)(count : nat) : lista X :=
    match count with
    | 0 => nil X 
    | S count' => cons X x (repete X x count')
    end.

Example teste_repete1 :
   repete nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).

Proof.
reflexivity. Qed.

Example teste_repete2 :
   repete bool false 1 = cons bool false (nil bool).

Proof.
reflexivity. Qed.

(* Exercício *)
(* Considere os dois seguintes tipos definidos indutivamente. *)
Module MumbleGrumble.
Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.
Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).
(* Quais das seguintes são elementos bem tipados de grumble X para algum 
tipo X? (Adicione SIM ou NÃO a cada linha. )

    d (b a 5) (* NÃO *)
    d mumble (b a 5) (* SIM *)
    d bool (b a 5) (* SIM *)
    e bool true (* SIM *)
    e mumble (b c 0) (* SIM *)
    e bool (b c 0) (* NÃO *)
    c  (* NÃO *) *)

End MumbleGrumble.

(* Simplificando a notação *)
(* Podemos usar a inferência de tipos do Rocq *)

Fixpoint repete' X x count : lista X :=
   match count with
   | 0 => nil X
   | S count' => cons X x (repete' X x count')
   end.

Check repete' 
   : forall X : Type, X -> nat -> lista X.
Check repete
   : forall X : Type, X -> nat -> lista X.

(* Podemos substituir o X pelo coringa '_' nas definições *)
Fixpoint repete'' X x count : lista X :=
   match count with
   | 0 => nil _
   | S count' => cons _ x (repete'' _ x count')
   end.

Definition lista123' :=
   cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* Ao invés de escrevermos esses símbolos repetidamente, 
podemos dizer ao Rocq para inferir isso, através do comando
Argument. Argument diz para sempre tratar um argumento c
omo implícito *)

Arguments nil {X}. (* nil - nome da função ou construtor ou qualque valor que estamos tratando. X - o argumento que vai ser tratado implicitamente *)
Arguments cons {X}.
Arguments repete {X}.

Definition lista123'' := cons 1 (cons 2 (cons 3 nil)).

(* Podemos fazer isso já na definição da função.
Ao invés de usarmos Arguments, usamos '{}' na declaração 
da função *)

Fixpoint repete''' {X : Type}(x : X)(count : nat) : lista X :=
   match count with
   | 0 => nil
   | S count' => cons x (repete''' x count')
   end.

(* Versões polimórficas de funções vistas anteriormente *)

Fixpoint juntar {X : Type}(l1 l2 : lista X) : lista X :=
   match l1 with
   | nil => l2
   | cons h t => cons h (juntar t l2)
   end.

Fixpoint reverter {X : Type}(l : lista X) : lista X :=
   match l with
   | nil => nil
   | cons h t => juntar (reverter t) (cons h nil)
   end.

Fixpoint tamanho {X : Type}(l : lista X) : nat :=
   match l with
   | nil => 0
   | cons _ l' => S(tamanho l')
   end.

Example teste_rev1 :
   reverter (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof.
reflexivity. Qed.

Example teste_rev2 :
   reverter (cons true nil) = cons true nil.
Proof.
reflexivity. Qed.

Example teste_tamanho1 :
   tamanho (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof.
reflexivity. Qed.

(* Provendo Tyoe Arguments explicitamente *)

Fail Definition meu_nil := nil. (* Rocq não vai saber inferir o tipo de nil *)

(* Podemos dar um argumento explicitamente *)
Definition meu_nil : lista nat := nil.

(* Ou podemos usar @ para tornar explícitos argumentos que eram implícitos *)
Check @nil : forall X : Type, lista X.

Definition meu_nil' := @nil nat.

(* Tornando as notações padrões *)
Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y [])..).

Notation "x ++ y" := (juntar x y)
                     (at level 60, right associativity).
                  
Definition lista123''' := [1;2;3].

(* Provando teoremas com as novas notações *)

Theorem juntar_assoc : forall X (lst1 lst2 lst3 : lista X),
   lst1 ++ lst2 ++ lst3 = (lst1 ++ lst2) ++ lst3.

Proof.
   intros X lst1 lst2 lst3. induction lst1 as [| h1 t1].
   - simpl. reflexivity.
   - simpl. rewrite IHt1. reflexivity.
Qed.

(* Pares Polimórficos *)
(* Semelhantemente a como definimos listas *)

Inductive prod ( X Y : Type) : Type :=
   | par (x : X)(y : Y).

(* Tornando implícito *)
Arguments par {X} {Y}.

Notation "( x , y )" := (par x y).

Notation "X * Y" := (prod X Y) : type_scope. (* type_scope serve para dizer que nesse escopo * significa produto cartesiano*)

(* Agora podemos escrever funções com pares *)
Definition primeiro {X Y : Type}{p : X * Y} : X :=
   match p with
   | (x , y) => x 
   end.

Definition segundo {X Y : Type}{p : X * Y} : Y :=
   match p with
   | (x , y) => y
   end.

(* Função que combina duas listas como pares *)
Fixpoint combine {X Y : Type} (lx: lista X) (ly : lista Y) : lista (X * Y) :=
   match lx, ly with
   | [], _ => []
   | _, [] => []
   | x :: tx, y :: ty => (x, y) :: (combine tx ty)
   end.

Example combine_ex : combine [1;2] [3;4] = [(1,3); (2,4)].

Proof.
   reflexivity. Qed.

(* Options Polimórficos *)

Module OptionPlayground.

Inductive option ( X : Type) : Type :=
   | Some (x : X)
   | None.

Arguments Some {X}.
Arguments None {X}.

End OptionPlayground.

(* Função que nos dá o enésimo elemento de uma lista de um tipo qualquer *)
Fixpoint enesimo_erro {X : Type}(l : lista X)(n : nat) : option X :=
   match l with 
   | [] => None
   | a :: l' => match n with   
                   | O => Some a
                   | S n' => enesimo_erro l' n'
                   end
   end.

Example teste_enesimo_erro1 : enesimo_erro [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example teste_enesimo_erro2 : enesimo_erro [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example teste_enesimo_erro3 : enesimo_erro [true] 2 = None.
Proof. reflexivity. Qed.