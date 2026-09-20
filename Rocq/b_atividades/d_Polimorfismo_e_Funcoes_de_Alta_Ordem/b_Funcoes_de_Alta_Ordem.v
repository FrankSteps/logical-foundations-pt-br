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
  induction l1 as [ | h1 t1 IHl1].
  - reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.


Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).

Proof.
  intros X Y f l.
  induction l as [ | h t IHl].
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
   unfold fold_tamanho. induction l as [ | h t IHl].
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

(* Exercício de reflexão: antes de executar os seguintes comandos, você 
consegue calcular os tipos de prod_curry e prod_uncurry? *)

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
    prod_curry (prod_uncurry f) x y = f x y.

Proof.
  intros X Y Z f x y. 
  unfold prod_uncurry. unfold prod_curry. reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.

Proof.
  intros X Y Z f p. 
  destruct p. unfold prod_curry. unfold prod_uncurry. reflexivity.
Qed.

(* Lembre-se da definição da função enesimo_erro: 

Fixpoint enesimo_erro {X : Type} (l : list X) (n : nat) : option X :=
     match l with
     | [] => None
     | a :: l' => if n =? O then Some a else enesimo_erro l' (pred n)
     end.

Escreva uma demonstração informal detalhada do seguinte teorema: ∀ X l n, 
length l = n → @nth_error X l n = None. Certifique-se de declarar 
explicitamente a hipótese de indução. *)

(* Teorema:
   forall X l n, length l = n -> enesimo_erro X l n = None

   Demonstração:
   Prosseguimos por indução sobre a estrutura da lista l. Seja X um tipo 
   arbitrário.

   1. Caso Base: l = []
   - Objetivo: Devemos mostrar que para todo n, se length [] = n, então
    enesimo_erro [] n = None.
   - Demonstração: 
     Por definição, length [] = 0. Portanto, temos n = 0. 
     Precisamos avaliar enesimo_erro [] 0. Pela definição de enesimo_erro 
     para a lista vazia, enesimo_erro [] 0 = None. Isso conclui o caso base.

   2. Passo Indutivo
   - Hipótese de Indução (HI): Assuma que para alguma lista l' e para 
     qualquer número natural n', se length l' = n', então 
     enesimo_erro l' n' = None.
   - Objetivo: Devemos mostrar que para qualquer elemento x em X e qualquer 
     número natural n, se length (x :: l') = n, então 
     enesimo_erro (x :: l') n = None.
   - Demonstração: 
     Seja l = x :: l'. Como length (x :: l') = n e a definição de length 
     para uma lista não vazia é S (length l'), deve ser o caso que n = S n' 
     para algum número natural n', onde length l' = n'.

     Precisamos avaliar:
     enesimo_erro (x :: l') (S n')

     Pela definição de enesimo_erro em uma lista não vazia com um índice 
     sucessor:
     enesimo_erro (x :: l') (S n') = enesimo_erro l' n'

     Pela nossa Hipótese de Indução, visto que length l' = n', sabemos que:
     enesimo_erro l' n' = None

     Portanto, enesimo_erro (x :: l') (S n') = None, o que conclui o passo 
     indutivo. ■
*)



(* Numerais de Church (Avançado) *)

(* Os exercícios a seguir exploram uma maneira alternativa de definir 
números naturais usando os numerais de Church, que levam o nome de seu 
inventor, o matemático Alonzo Church. Podemos representar um número natural n 
como uma função que recebe uma função f como parâmetro e retorna f iterada n 
vezes. *)

Module Church. 
  
Definition cnat := forall X : Type, (X -> X) -> X -> X.

(* Vamos ver como escrever alguns números com esta notação. Iterar uma 
função uma vez deve ser o mesmo que apenas aplicá-la. Portanto: *)

Definition um : cnat := fun (X : Type) (f : X -> X) (x : X) => f x.

(* Da mesma forma, o dois deve aplicar f duas vezes ao seu argumento: *)

Definition dois : cnat := fun (X : Type) (f : X -> X) (x : X) => f (f x).

(* Definir o zero é um pouco mais complicado: como podemos ''aplicar uma 
função zero vezes''? A resposta na verdade é simples: basta retornar o 
argumento inalterado. *)

Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

(* Mais geralmente, um número $n$ pode ser escrito como `fun X f x => 
f (f ... (f x) ...)`, com n ocorrências de `f`. Vamos denotar isso 
informalmente como `fun X f x => f^n x`, com a convenção de que `f^0 x` é 
apenas `x`. Note como a função `facaisso3vezes` que definimos anteriormente 
é na verdade apenas a representação de Church de 3. *)

Definition tres : cnat := @facaisso3vezes.

(* Portanto, n X f x representa ''faça isso n vezes'', onde n é um numeral 
de Church e ''isso'' significa aplicar f começando com x.

Outra maneira de pensar sobre a representação de Church é que a função f 
representa a operação de sucessor em X, e o valor x representa o elemento 
zero de X. Poderíamos até reescrever com esses nomes para deixar mais claro: *)

Definition zero' : cnat :=
  fun (X : Type) (sucessor : X -> X) (zero : X) => zero.

Definition um' : cnat :=
  fun (X : Type) (sucessor : X -> X) (zero : X) => sucessor zero.

Definition dois' : cnat :=
  fun (X : Type) (sucessor : X -> X) (zero : X) => sucessor (sucessor zero).

(** Se tivessemos passado S como sucessor e 0 como zero, nós até conseguiriamos os
naturais de Peano como resultado: *)



Example zero_church_peano : zero nat S O = 0. Proof. reflexivity. Qed.
Example um_church_peano : um nat S O = 1. Proof. reflexivity. Qed.
Example dois_church_peano : dois nat S O = 2. Proof. reflexivity. Qed. 

(* Uma implicação muito interessante dos numerais de Church é que não 
precisamos estritamente que os números naturais sejam nativos em uma 
linguagem de programação funcional, nem mesmo que sejam definíveis com um 
tipo de dados indutivo. É possível representá-los puramente (ainda que não 
de forma eficiente) usando apenas funções.

É claro que não basta apenas ''representar'' os numerais; precisamos ser 
capazes de realizar operações aritméticas com essa representação. Mostre que 
isso é possível completando as definições das seguintes funções. Certifique-se 
de que os testes unitários correspondentes passem ao prová-los com 
reflexividade. *)

(* Exercício *)
(* Defina uma função que calcula o sucessor de um numeral de Church.

Dado um numeral de Church n, seu sucessor scc n deve iterar seu argumento de 
função uma vez a mais do que n. Ou seja, dado fun X f x => f^n x como 
entrada, scc deve produzir fun X f x => f^(n+1) x como saída. Em outras 
palavras, faça-o n vezes, depois faça-o mais uma vez. *)

Definition scc (n : cnat) : cnat :=
   fun X f x => f (n X f x).

Example scc_1 : scc zero = um. Proof. reflexivity. Qed.
Example scc_2 : scc um = dois. Proof. reflexivity. Qed.
Example scc_3 : scc dois = tres. Proof. reflexivity. Qed.

(* Defina uma função que calcula a adição de dois numerais de Church. Dados 
fun X f x => f^n x e fun X f x => f^m x como entrada, adicao deve produzir 
fun X f x => f^(n + m) x como saída. Em 
outras palavras, faça-o n vezes, depois faça-o mais m vezes. Dica: o 
argumento ''zero'' de um numeral de Church não precisa ser apenas x. *)


Definition adicao (n m : cnat) : cnat :=
  fun X f x => n X f (m X f x).

Example adicao_1 : adicao zero um = um. Proof. reflexivity. Qed.

Example adicao_2 : adicao dois tres = adicao tres dois. 
Proof. reflexivity. Qed.

Example adicao_3 : adicao (adicao dois dois) tres = adicao um (adicao tres tres). 
Proof. reflexivity. Qed.

(* Defina uma função que calcule a multiplicação de dois 
numerais de Church. 
Dica: o argumento ''sucessor'' para um numeral de Church não 
precisa ser apenas f.
Aviso: o Rocq não deixará você passar cnat como o argumento 
de tipo X para um numeral de Church; você receberá um erro 
de ''inconsistência de universo'' (Universe inconsistency). 
Essa é a maneira do Rocq de evitar um paradoxo no qual um 
tipo contém a si mesmo. Portanto, deixe o argumento de tipo 
inalterado. *)

Definition mult (n m : cnat) : cnat :=
   fun X f x => m X (n X f) x.

Example mult_1 : mult um um = um. Proof. reflexivity. Qed.

Example mult_2 : mult zero (adicao tres tres) = zero. 
Proof. reflexivity. Qed.

Example mult_3 : mult dois tres = adicao tres tres. 
Proof. reflexivity. Qed.

(** Exponenciação: *)

(** Defina uma função que calcule a exponenciação de dois 
numerais de Church.

Dica: o argumento de tipo para um numeral de Church não 
precisa ser apenas X.
Mas, novamente, você não pode passar `cnat` em si como o a
rgumento de tipo.
Encontrar o tipo correto pode ser complicado. *)

Definition exp (n m : cnat) : cnat :=
  fun X f x => m (X -> X) (n X) f x.

Example exp_1 : exp dois dois = adicao dois dois. 
Proof. reflexivity. Qed.

Example exp_2 : exp tres zero = um. 
Proof. reflexivity. Qed.

Example exp_3 : exp tres dois = 
adicao (mult dois (mult dois dois)) um. 
Proof. reflexivity. Qed.

End Church.
