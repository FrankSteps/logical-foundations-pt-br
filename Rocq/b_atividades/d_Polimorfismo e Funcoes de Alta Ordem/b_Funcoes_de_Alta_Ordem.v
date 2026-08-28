Require Import List.
Import ListNotations.
Require Import Nat.

(* Funções de Alta Ordem *)
(* Funções que manipulam outras funções*)

Definition facaisso3vezes {X : Type} (f : X -> X) (n : X) : X :=
   f (f (f n)).

Check @facaisso3vezes : forall X : Type, (X -> X) -> X -> X.

(* Usando a função vista inicialmente no capítulo inicial *)
Definition SubtraiDois (n : nat) : nat :=
   match n with
   | 0 => 0
   | S 0 => 0
   | S (S (n')) => n'
   end.

Example teste_facaisso3vezes: facaisso3vezes SubtraiDois 9 = 3.
Proof. reflexivity. Qed.

Example teste_facaisso3vezes': negb true = false.
Proof. reflexivity. Qed.

(* Filter *)
(* A função filter serve para filtrar elementos de uma lista que satisfazem 
um predicado *)
Fixpoint filter {X : Type} (teste : X -> bool) (l : list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if teste h then h :: (filter teste t)
    else filter teste t
  end.

Example teste_filter1: filter Nat.even [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition tamanho_e_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.

Example teste_filter2:  filter tamanho_e_1
    [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ] = [ [3]; [4]; [8] ].


Proof. reflexivity. Qed.

Definition contanumerosimpares' (l : list nat) : nat :=
  length (filter odd l).

Example teste_contanumerosimpares'1: contanumerosimpares' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_contanumerosimpares'2: contanumerosimpares' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_contanumerosimpares'3: contanumerosimpares' nil = 0.
Proof. reflexivity. Qed.

(* Funções Anônimas *)
(* Não precisa dar um nome para funções *)
Example teste_anon_fun':
  facaisso3vezes (fun n => n * n) 2 = 256. (* Função que recebe n e dá n * n *)

Proof. reflexivity. Qed.

Example teste_filter2':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ] = [ [3]; [4]; [8] ].

Proof. reflexivity. Qed.

(* Exercício *)
(* Função que mantem elementos que são pares e maiores que 7*)
Definition filter_par_maior_que_7 (l : list nat) : list nat :=
     filter (fun x => andb (7 <? x) (even x)) l.

Example teste_filter_par_maior_que_7_1 :
  filter_par_maior_que_7 [1;2;6;9;10;3;12;8] = [10;12;8].

Proof.
  reflexivity.
Qed.

Example teste_filter_par_maior_que_7_2 :
  filter_par_maior_que_7 [5;2;6;19;129] = [].

Proof.
  reflexivity.
Qed.

  
Definition particao {X : Type} (teste : X -> bool) (l : list X) : list X * list X :=
  (filter teste l, filter(fun x => negb (teste x))l).
  
Example teste_particao1: particao odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof.
  reflexivity.
Qed.

Example teste_particao2: particao (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof.
  reflexivity.
Qed.


(* Outras duas funções de alta ordem importantes são Map e Fold *)

(* Map *)
(* Transforma todos os elementos de uma coleção *)
Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Example teste_map1: map (fun x => 3 + x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Example teste_map2: map odd [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.

Example teste_map3:
    map (fun n => [even n;odd n]) [2;1;2;5]
    = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

(* Exercício *)

(* Lema Auxiliar *)
Lemma juntar_map : forall (X Y: Type)(f: X -> Y)(l1 l2: list X),
map f (l1 ++ l2) = map f l1 ++ map f l2.

Proof.
  intros X Y f l1 l2.
  induction l1 as [| h1 t1 IHl1].
  - reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.


Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).

Proof.
  intros X Y f l.
  induction l as [| h t IHl].
  - reflexivity.
  - simpl. rewrite juntar_map. simpl. rewrite IHl. reflexivity.
Qed.

(* Exercício *)
Fixpoint mapeamento_achatado {X Y: Type} (f: X -> list Y) (l: list X) : list Y :=
   match l with
   | [] => []
   | h :: t => (f h) ++ mapeamento_achatado f t
   end.
 
Example teste_mapeamento_achatado1:
  mapeamento_achatado (fun n => [n;n;n]) [1;5;4] = [1; 1; 1; 5; 5; 5; 4; 4; 4].
 
Proof.
  reflexivity.
Qed.

(* Usando map com options *)
 Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

(* Exercício *)
Fixpoint filter' (X : Type) (teste : X -> bool) (l : list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if teste  h then  h :: (filter' X teste t)
    else filter' X teste t
  end.

Fixpoint map' (X Y : Type) (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map' X Y f t)
  end.

(* Fold *)
(* Combina elementos de uma lista em um único valor *)
Fixpoint fold {X Y: Type} (f : X -> Y -> Y) (l : list X) (b : Y): Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(* fold é similar com outra função chamada reduce de map/reduce *)

Check (fold andb) : list bool -> bool -> bool.

Example fold_exemplo1 :
   fold mult [2;3;4] 1 = 24. (* 2 * ( 3 * ( 4 * 1)) *)
Proof. reflexivity. Qed.

Example fold_exemplo2 :
   fold andb [true;true;false;true] true = false. 
   (* T && ( T && (F && ( T && T))) *)
Proof. reflexivity. Qed.

Example fold_exemplo3 :
   fold (@app nat) [[1];[];[2;3];[4];[]] [] = [1;2;3;4].
   (* [1] ++ ([] ++ ([2;3] ++ ([4] ++ []))) *)
Proof. reflexivity. Qed.

(* Funções que constroem outras funções *)
Definition constfun {X : Type} (x : X) : nat -> X :=
  fun (k:nat) => x.

Definition ftrue := constfun true. (* true sempre vai ser o que vai ser passado de volta *)

Example constfun_examplo1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_examplo2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(* Funções com dois ou mais argumentos são, na verdade, funções que tomam 
um argumento e retornam uma função *)
Check plus : nat -> nat -> nat.

Definition plus3 := plus 3.
Check plus3 : nat -> nat.

Example teste_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example teste_plus3' : facaisso3vezes plus3 0 = 9.
Proof. reflexivity. Qed.
Example teste_plus3'' : facaisso3vezes (plus 3) 0 = 9.
Proof. reflexivity. Qed.

(* Exercícios Adicionais *)

(* Muitas funções comuns em listas podem ser implementadas em termos de 
fold. Por exemplo, aqui está uma definição alternativa de tamanho: *)

Definition fold_tamanho {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example teste_fold_tamanho1 : fold_tamanho [4;7;0] = 3.
Proof.
  reflexivity.
Qed.

(* Prove a corretude de fold_length.

Dica: Você pode acabar em uma situação em que sente que o simpl deveria 
ser capaz de simplificar fold_length, mas ele não faz nada. Nesses casos, 
você pode usar a tática unfold para expandir a definição de uma função antes 
da simplificação, por exemplo: unfold fold_length. simpl. Essa tática será 
discutida mais a fundo no próximo capítulo.*)


Theorem fold_length_correct : forall X (l : list X),
  fold_tamanho l = length l.

Proof.
   intros X l.
   unfold fold_tamanho. induction l as [| h t IHl].
   - reflexivity.
   - simpl. rewrite IHl. reflexivity.
Qed.

(* Também podemos definir o map em termos de fold. Termine o fold_map abaixo. *)

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
  fold (fun x acc => (f x) :: acc ) l [].

(* O tipo X→Y→Z pode ser lido como descrevendo funções que recebem dois 
argumentos, um do tipo X e outro do tipo Y, e retornam uma saída do tipo Z. 
Lembre-se da nossa discussão sobre aplicação parcial de que este tipo é 
escrito como X→(Y→Z) quando totalmente parentesizado. Ou seja, se tivermos 
f:X→Y→Z, e dermos a f uma entrada do tipo X, ela nos dará como saída uma 
função do tipo Y→Z. Se então dermos a essa função uma entrada do tipo Y, 
ela retornará uma saída do tipo Z. Em outras palavras, toda função em Rocq 
aceita apenas uma entrada, mas algumas funções retornam uma função como 
saída. Isso é exatamente o que permite a aplicação parcial, como vimos 
acima com plus3.

Em contrapartida, funções do tipo X×Y→Z — que, quando totalmente 
parentesizadas, são escritas como (X×Y)→Z — exigem que sua única entrada 
seja um par. Ambos os argumentos devem ser fornecidos de uma só vez; não há 
possibilidade de aplicação parcial.

É possível converter uma função entre esses dois tipos. A conversão de X×Y→Z 
para X→Y→Z é chamada de currificação (currying), em homenagem ao lógico 
Haskell Curry. A conversão de X→Y→Z para X×Y→Z é chamada de descurrificação 
(uncurrying).

Podemos definir a currificação da seguinte forma:*)
Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(* Como exercício, defina seu inverso, prod_uncurry. Em seguida, prove os 
teoremas abaixo para mostrar que os dois são realmente inversos. *)
Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
   match p with
   | (x, y) =>  f x y
   end.

(* Como um exemplo (trivial) da utilidade da currificação, podemos usá-la 
para encurtar um dos exemplos que vimos acima: *)
Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
    prod_curry (prod_uncurry f) x y = f x y.

Proof.
  intros X Y Z f x y. 
  unfold prod_uncurry. unfold prod_curry. reflexivity.
Qed.