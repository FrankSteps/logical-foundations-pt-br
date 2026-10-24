Set Warnings "-notation-overridden,-notation-incompatible-prefix".
Require Import LFPTBR.g_IndProp.a_IndProp.
From Stdlib Require Import Lists.List.
Import ListNotations.
(* ''Algoritmos são o conteúdo computacional das provas.'' (Robert Harper)

Vimos que o Rocq possui mecanismos tanto para programação, usando tipos de dados 
indutivos como nat ou list e funções sobre esses tipos, quanto para provar propriedades desses 
programas, usando proposições indutivas (como ev), implicação, quantificação universal e
afins.

Até agora, tratamos esses mecanismos principalmente como se fossem bem separados, e para 
muitos propósitos essa é uma boa forma de pensar. Mas também vimos indícios de que os 
recursos de programação e de prova do Rocq estão intimamente relacionados. Por exemplo, 
a palavra-chave Inductive é usada para declarar tanto tipos de dados quanto proposições, e 
→ é usada tanto para descrever o tipo de funções sobre dados quanto a implicação lógica. 
Isso não é apenas um acidente sintático! De fato, programas e provas no Rocq são quase a 
mesma coisa. Neste capítulo, estudaremos essa conexão em mais detalhes.

Já vimos a ideia fundamental: a provabilidade no Rocq é sempre testemunhada por evidências. 
Quando construímos a prova de uma proposição básica, estamos na verdade construindo uma 
árvore de evidências, que pode ser pensada como uma estrutura de dados concreta.

Se a proposição for uma implicação como A → B, então sua prova é um transformador de 
evidências: uma receita para converter evidências de A em evidências de B. Portanto, em 
um nível fundamental, as provas são simplesmente programas que manipulam evidências.

Pergunta: Se a evidência são dados, o que são as próprias proposições?

Resposta: Elas são tipos!

Olhe novamente para a definição formal da propriedade ev.*)

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(* Podemos pronunciar o : aqui como ''tem o tipo'' ou ''é uma prova de''. Por exemplo, a 
segunda linha na definição de ev declara que ev_0 : ev 0. Em vez de ''ev_0 tem o tipo ev 0'', 
podemos dizer que ''ev_0 é uma prova de ev 0''.

Esse duplo sentido entre tipos e proposições — entre o : como ''tem o tipo'' e o : como 
''é uma prova de'' ou ''é evidência para'' — é chamado de correspondência de Curry-Howard.
Ela propõe uma conexão profunda entre o mundo da lógica e o mundo da computação: 

                    proposições ~ tipos
                    provas      ~ programas
                    
Veja [Wadler 2015] para um breve histórico e exposição moderna.

Muitas intuições úteis decorrem dessa conexão. Para começar, ela nos dá uma interpretação 
natural do tipo do construtor ev_SS: *)

Check ev_SS
  : forall n,
      ev n ->
      ev (S (S n)).

(* Isso pode ser lido como: ''ev_SS é um construtor que aceita dois argumentos — um número 
n e uma evidência para a proposição ev n — e produz uma evidência para a proposição 
ev (S (S n)).''

Agora vamos olhar novamente para uma prova anterior envolvendo ev. *)

Theorem ev_4 : ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.

(* Assim como acontece com valores de dados e funções comuns, podemos usar o comando Print 
para ver o objeto de prova que resulta desse script de prova. *)

Print ev_4.
(* ===> ev_4 = ev_SS 2 (ev_SS 0 ev_0)
      : ev 4  *)

(* De fato, também podemos escrever esse objeto de prova diretamente, sem nenhuma
necessidade de um script de prova: *)

Check (ev_SS 2 (ev_SS 0 ev_0))
  : ev 4.

(* A expressão ev_SS 2 (ev_SS 0 ev_0) instancia o construtor parametrizado ev_SS com os
argumentos específicos 2 e 0, mais os objetos de prova correspondentes para suas premissas
ev 2 e ev 0.
Alternativamente, podemos pensar em ev_SS como um ''construtor de evidências'' primitivo 
que, quando aplicado a um determinado número, deseja ser aplicado posteriormente à 
evidência de que esse número é par; o seu tipo,
                      ∀ n, ev n → ev (S (S n)),
expressa essa funcionalidade, da mesma forma que o tipo polimórfico ∀ X, list X expressa o 
fato de que o construtor nil pode ser visto como uma função de tipos para listas vazias com 
elementos desse tipo.

Vimos no capítulo de Lógica que podemos usar a sintaxe de aplicação de função para 
instanciar variáveis quantificadas universalmente em lemas, bem como para fornecer 
evidências para as premissas que esses lemas impõem. Por exemplo: *)

Theorem ev_4': ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

(*********************************** Scripts de Prova ************************************)

(* Os objetos de prova que temos discutido estão no núcleo de como o Rocq opera. Quando o 
Rocq está seguindo um script de prova, o que acontece internamente é que ele está construindo 
gradualmente um objeto de prova — um termo cujo tipo é a proposição que está sendo provada. As 
táticas entre Proof e Qed dizem a ele como construir um termo do tipo necessário. Para ver 
esse processo em ação, vamos usar o comando Show Proof para exibir o estado atual da árvore 
de prova em vários pontos na seguinte prova baseada em táticas. *)

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

(* Em qualquer momento dado, o Rocq construiu um termo com um ''buraco'' (indicado por ?Goal 
aqui e assim por diante), e ele sabe que tipo de evidência é necessária para preencher esse 
buraco. 

Cada falha corresponde a um subobjetivo, e a prova está concluída quando não há mais 
subobjetivos. Neste ponto, a evidência que construímos é armazenada no contexto global sob o 
nome dado no comando Theorem. 

Provas por táticas são convenientes, mas não são essenciais no Rocq: em princípio, sempre 
podemos construir simplesmente a evidência necessária à mão. Depois, podemos usar Definition 
(ao invés de Theorem) para introduzir um nome global para essa evidência. *)

Definition ev_4''' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

(* Todas essas diferentes formas de construir a prova levam exatamente à mesma evidência 
sendo salva no contexto global.*)

Print ev_4.
(* ===> ev_4    =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4'.
(* ===> ev_4'   =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4''.
(* ===> ev_4''  =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4'''.
(* ===> ev_4''' =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)

(* Exercício *)
(* Forneça uma prova por tática e um objeto de prova demonstrando que ev 8 é verdadeiro
(ou seja, que 8 é par). *)

Theorem ev_8 : ev 8.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Definition ev_8' : ev 8 :=
  (ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0)))).

(*********************** Quantificadores, Implicações, Funções ************************)

(* No universo computacional do Rocq (onde vivem estruturas de dados e programas), há 
dois tipos de valores cujos tipos contêm setas: construtores introduzidos por tipos de 
dados definidos indutivamente (Inductively defined data types), e funções.

Da mesma forma, no universo lógico do Rocq (onde realizamos provas), há duas maneiras 
de fornecer evidências para uma implicação: construtores introduzidos por proposições 
definidas indutivamente (Inductively defined propositions), e... funções!

Por exemplo, considere esta afirmação: *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

(* Qual é o objeto de prova correspondente a ev_plus4?

Estamos procurando por uma expressão cujo tipo é ∀ n, ev n → ev (4 + n) — ou seja, uma 
função que recebe dois argumentos (um número e uma evidência) e retorna uma evidência!

Aqui está ela:*)

Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) =>
    ev_SS (S (S n)) (ev_SS n H).

(* Lembre-se de que fun n => blah significa ''a função que, dado n, produz blah'', e que o 
Rocq trata 4 + n e S (S (S (S n))) como sinônimos. Outra maneira equivalente de escrever 
esta definição é: *)

Definition ev_plus4'' (n : nat) (H : ev n)
                    : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4'' : forall n : nat, ev n -> ev (4 + n).

(* Quando encaramos a proposição provada por ev_plus4 como um tipo de função, um ponto 
interessante se torna evidente: o tipo do segundo argumento, ev n, menciona o valor do 
primeiro argumento, n.

Embora esses tipos dependentes (dependent types) não sejam encontrados na maioria das 
linguagens de programação tradicionais, eles também podem ser bastante úteis na 
programação, como demonstra o intenso movimento na comunidade de programação funcional 
nas últimas décadas.

Note que tanto a implicação (→) quanto a quantificação (∀) correspondem a funções sobre 
evidências. Na verdade, elas são essencialmente a mesma coisa: → é apenas um atalho 
para um uso degenerado de ∀ onde não há dependência, ou seja, onde não há necessidade
de dar um nome ao tipo no lado esquerdo da seta:
                            ∀ (x:nat), nat
                         =  ∀ (_:nat), nat
                         =  nat          → nat
Por exemplo, considere esta proposição: *)

Definition ev_plus2 : Prop :=
  forall n, forall (E : ev n), ev (n + 2).

(* Um termo de prova que habita esta proposição seria uma função com dois argumentos: um 
número n e alguma evidência E de que n é par. Mas o nome E para essa evidência não é 
usado no restante da declaração, então é meio bobo se dar ao trabalho de inventar um 
nome para ela. Em vez disso, poderíamos escrevê-la assim, usando o identificador 
coringa _ no lugar de um nome real. *)

Definition ev_plus2' : Prop :=
  forall n, forall (_ : ev n), ev (n + 2).

(* Ou, de forma equivalente, podemos escrevê-la de uma maneira mais familiar: *)

Definition ev_plus2'' : Prop :=
  forall n, ev n -> ev (n + 2).

(* Em geral, ''P → Q'' é apenas um ''açúcar sintático'' para ''∀ (_:P), Q''. *)

(********************************* Progração com Táticas *******************************)

(* Se podemos construir provas fornecendo termos explícitos em vez de executar scripts 
de táticas, você pode se perguntar se podemos construir programas usando táticas em vez 
de escrever termos explícitos.

Naturalmente, a resposta é sim!*)

Definition add2 : nat -> nat.
intros n.
Show Proof.
apply S.
Show Proof.
apply S.
Show Proof.
apply n. Defined.
Print add2.
(* ==>
    add2 = fun n : nat => S (S n)
          : nat -> nat
*)
Compute add2 2.
(* ==> 4 : nat *)

(* Note que encerramos a definição com um . em vez de usar := seguido de um termo. Isso 
informa ao Rocq para entrar no modo de script de prova para construir um objeto do tipo 
nat → nat. Também encerramos a prova com Defined em vez de Qed; isso torna a definição 
transparente, de modo que pode ser usada em computação como uma função normalmente 
definida. (Objetos definidos com Qed são opacos durante a computação.)

Esta funcionalidade é principalmente útil para escrever funções com tipos dependentes, o 
que não exploraremos muito mais neste livro. Mas ela ilustra a uniformidade e 
ortogonalidade das ideias básicas no Rocq. *)

(*********************** Conectivos Lógicos como Tipos Indutivos ***********************)

(* Definições indutivas são poderosas o suficiente para expressar a maioria dos 
conectivos lógicos que temos visto até agora. De fato, apenas a quantificação universal 
(com implicação como caso especial) é incorporada ao Rocq; todos os demais são definidos 
indutivamente.

Vamos ver como *)

Module Props.

(** Conjunção **)

(* Para provar que P ∧ Q é válido, precisamos apresentar evidência para ambos P e Q. 
Assim, faz sentido definir um objeto de prova para P ∧ Q como um par de duas provas: uma 
para P e outra para Q. Isso leva à seguinte definição. *)
Module And.

Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.

Arguments conj [P] [Q].

Notation "P /\ Q" := (and P Q) : type_scope.

(* Note a semelhança com a definição do tipo prod, apresentada no capítulo de Polimorfismo; 
a única diferença é que prod toma argumentos do tipo Type, enquanto and toma argumentos
do tipo Prop.*)

Print prod.
(* ===>
   Inductive prod (X Y : Type) : Type :=
   | pair : X -> Y -> X * Y. *)

(* Esta semelhança deve esclarecer porque os padrões destruct e intros podem ser usados 
em uma hipótese conjuntiva. A análise de casos permite-nos considerar todas as formas 
possíveis pelas quais P ∧ Q foi provada — aqui apenas uma (o construtor conj).*)

Theorem proj1' : forall P Q,
  P /\ Q -> P.
Proof.
  intros P Q HPQ. destruct HPQ as [HP HQ]. apply HP.
  Show Proof.
Qed.

(* Da mesma forma, a tática split funciona para qualquer proposição definida 
indutivamente com exatamente um construtor. Em particular, ela funciona para and:  *)

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HQ HP]. split.
    + apply HP.
    + apply HQ.
Qed.

End And.

(* Isso mostra por que a definição indutiva de and pode ser manipulada por táticas como 
temos estado fazendo. Também podemos usá-la para construir provas diretamente, usando 
casamento de padrões (pattern-matching). Por exemplo: *)

Definition proj1'' P Q (HPQ : P /\ Q) : P :=
  match HPQ with
  | conj HP HQ => HP
  end.

Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

(* Exercício *)
(* Construa um objeto de prova para a seguinte proposição *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R := 
  fun P Q R HPQ HQR => conj (proj1'' P Q HPQ) (proj1'' R Q (and_comm'_aux Q R HQR)).

(** Disjunção **)

(* A definição indutiva de disjunção usa dois construtores, um para cada lado da 
disjunção: *) 

Module Or.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Arguments or_introl [P] [Q].
Arguments or_intror [P] [Q].

Notation "P \/ Q" := (or P Q) : type_scope.

(* Esta declaração explica o comportamento da tática destruct em uma hipótese disjuntiva,
uma vez que as submetas geradas correspondem ao formato dos construtores or_introl e 
or_intror. 

Mais uma vez, também podemos escrever diretamente objetos de prova para teoremas 
envolvendo ou, sem recorrer a táticas. *)

Definition inj_l : forall (P Q : Prop), P -> P \/  Q :=
  fun P Q HP => or_introl HP.

Theorem inj_l' : forall (P Q : Prop), P -> P \/ Q.
Proof.
  intros P Q HP. left. apply HP.
  Show Proof.
Qed.

Definition or_elim : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R :=
  fun P Q R HPQ HPR HQR =>
    match HPQ with
    | or_introl HP => HPR HP
    | or_intror HQ => HQR HQ
    end.

Theorem or_elim' : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R.
Proof.
  intros P Q R HPQ HPR HQR.
  destruct HPQ as [HP | HQ].
  - apply HPR. apply HP.
  - apply HQR. apply HQ.
Qed.

End Or.

(* Exercício *)
(* Construa um objeto de prova para a seguinte proposição. *)

Definition or_commut' : forall P Q, P \/ Q -> Q \/ P :=
  fun P Q HPQ => match HPQ with
  | or_introl HP => or_intror HP
  | or_intror HQ => or_introl HQ
  end.

(** Quantificação Existencial **)
(* Para dar evidência a um quantificador existencial, nós empacotamos uma testemunha x 
junto com uma prova de que x satisfaz a propriedade P: *)

Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  | ex_intro : forall x : A, P x -> ex P.

Notation "'exists' x , p" :=
  (ex (fun x => p))
    (at level 200, right associativity) : type_scope.
    
End Ex.

(* Isso provavelmente precisa de um pouco de detalhamento. A definição central é de um 
formador de tipos (ou construtor de tipos) ex que pode ser usado para construir 
proposições da forma ex P, onde o próprio P é uma função que mapeia valores testemunha no 
tipo A para proposições. O construtor ex_intro oferece então uma maneira de construir 
evidência para ex P, dada uma testemunha x e uma prova de P x. 

A notação na biblioteca padrão é uma pequena extensão do texto acima, permitindo formas 
sintáticas como ∃ x y, P x y. 

A forma mais familiar ∃ x, ev x  é traduzida (desugarizada) para uma expressão 
envolvendo ex: *)

Check ex (fun n => ev n) : Prop.

(* Veja como definir um objeto de prova explícito envolvendo ex: *)

Definition some_nat_is_even : exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

(* Exercício *)
(* Construa um objeto de prova para a seguinte proposição. *)

Definition ex_ev_Sn : ex (fun n => ev (S n)) :=
  ex_intro (fun n => ev (S n)) 3 (ev_SS 2 (ev_SS 0 ev_0)).

(* Para fazer a destruição (destruct) de existenciais em um termo de prova, nós 
simplesmente usamos o match: *)

Definition dist_exists_or_term (X:Type) (P Q : X -> Prop) :
  (exists x, P x \/ Q x) -> (exists x, P x) \/ (exists x, Q x) :=
  fun H => match H with
           | ex_intro _ x Hx =>
               match Hx with
               | or_introl HPx => or_introl (ex_intro _ x HPx)
               | or_intror HQx => or_intror (ex_intro _ x HQx)
               end
           end.

(* Exercício *)
(* Construa um objeto de prova para a seguinte proposição: *)

Definition ex_match : forall (A : Type) (P Q : A -> Prop),
  (forall x, P x -> Q x) ->
  (exists x, P x) -> (exists x, Q x) :=
  fun A P Q HPQ HP => match HP with
                    | ex_intro _ x Hx => ex_intro _ x (HPQ x Hx)
                    end.

(** Verdadeiro e Falso **)

(* A definição indutiva da proposição Verdadeira é simples: *)

Inductive True : Prop :=
  | I : True.

(* Ela tem apenas um construtor (portanto, toda prova de Verdadeiro é a mesma, logo 
receber uma prova de Verdadeiro não é informativo). *)

Definition p_implies_true : forall P, P -> True :=
  fun _ _ => I.

(* O False é igualmente simples — na verdade, tão simples que pode parecer sintaticamente 
errado à primeira vista! *)

Inductive False : Prop := .

(* Ou seja, o False é um tipo indutivo sem construtores — isto é, sem nenhuma maneira de 
construir evidências para ele. Por exemplo, não há como completar a seguinte definição 
para que ela seja bem-sucedida. *)

Fail
  Definition contra : False :=
  42.

(* Mas é possível fazer o destruct de False por pattern matching (casamento de padrões). 
Não pode haver nenhum padrão que combine com ele, já que ele não tem construtores. 
Portanto, o pattern match também é tão simples que pode parecer sintaticamente errado 
à primeira vista! *)

Definition false_implies_zero_eq_one : False -> 0 = 1 :=
  fun contra => match contra with end.

(* Como não há ramos para avaliar, pode-se considerar que a expressão match tem qualquer 
tipo que quisermos, incluindo 0 = 1. Felizmente, é impossível fazer com que o match seja 
avaliado, porque nunca conseguiremos construir um valor do tipo False para passá-lo para a 
função. *)

(* Exercício *)
(* Construa um objeto de prova para a seguinte proposição. *)

Definition ex_falso_quodlibet' : forall P, False -> P :=
  fun _ contra => match contra with end.

End Props.

(*** Igualdade ***)

(* Até mesmo a relação de igualdade do Rocq não vem embutida. Podemos defini-la nós 
mesmos: *)

Module EqualityPlayground.
Inductive eq {X:Type} : X -> X -> Prop :=
  | eq_refl : forall x, eq x x.
Notation "x == y" := (eq x y)
                       (at level 70, no associativity)
                     : type_scope.

(* A maneira de pensar sobre essa definição (que é apenas uma leve variante da 
biblioteca padrão) é que, dado um conjunto $X$, ela define uma família de proposições 
'x é igual a y', indexada por pares de valores (x e y) de X. Há apenas uma maneira de 
construir evidências para os membros dessa família: aplicando o construtor eq_refl a um 
tipo X e a um único valor x : X, o que produz a evidência de que x é igual a x. 

Outros tipos da forma eq x y onde x e y não são o mesmo são, portanto, inabitados. 

Podemos usar eq_refl para construir evidências de que, por exemplo, 2 = 2. Podemos 
também usá-lo para construir evidências de que 1 + 1 = 2? Sim, podemos. Na verdade, é 
exatamente a mesma evidência! 

A razão é que o Rocq trata como 'o mesmo' quaisquer dois termos que sejam conversíveis 
de acordo com um conjunto simples de regras de computação. Essas regras, que são 
semelhantes às usadas pelo Compute, incluem a avaliação de aplicação de funções, expansão 
de definições (inlining) e simplificação de match. *)

Lemma four: 2 + 2 == 1 + 3.
Proof.
  apply eq_refl.
Qed.

(* A tática reflexivity que usamos até agora para provar igualdades é essencialmente 
apenas um atalho para apply eq_refl. 

Em provas de igualdade baseadas em táticas, as regras de conversão ficam normalmente 
ocultas em usos de simpl (seja explícito ou implícito em outras táticas, como reflexivity). 

Mas você pode vê-las em ação diretamente nos seguintes objetos de prova explícitos: *)

Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X:Type) (x:X), []++[x] == x::[] :=
  fun (X:Type) (x:X) => eq_refl [x].

(* Também podemos fazer pattern-matching em uma prova de igualdade: *)

Definition eq_add : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2) :=
  fun n1 n2 Heq =>
    match Heq with
    | eq_refl n => eq_refl (S n)
    end.

(* Fazendo pattern-matching (correspondência de padrões) em n1 == n2, obtemos um termo n 
que substitui n1 e n2 no tipo que temos de produzir, então em vez de (S n1) == (S n2), 
agora precisamos produzir algo do tipo (S n) == (S n), o que estabelecemos por 
eq_refl (S n). 

Uma prova baseada em táticas encontra algumas dificuldades se tentarmos usar nosso 
repertório usual de táticas, como rewrite e reflexivity. Elas funcionam com relações de 
setoid que o Rocq conhece, como =, mas não com o nosso ==. Poderíamos provar ao Rocq 
que == é um setoid, mas uma maneira mais simples é usar destruct e apply em vez disso. *)

Theorem eq_add' : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2).
Proof.
  intros n1 n2 Heq.
  Fail rewrite Heq. (* não funciona para a nossa relação == *)
  destruct Heq as [n]. (* n1 e n2 substituídos por n na meta! *)
  Fail reflexivity. (* não funciona para a nossa relação == *)
  apply eq_refl.
Qed.

(* Exercício *)
(* Construa o objeto de prova para o seguinte teorema. Faça pattern matching nas 
hipóteses de igualdade. *)
Definition eq_cons : forall (X : Type) (h1 h2 : X) (t1 t2 : list X),
    h1 == h2 -> t1 == t2 -> h1 :: t1 == h2 :: t2 :=
    fun X h1 h2 t1 t2 Heqh Heqt => match Heqh with
                                  | eq_refl h => match Heqt with
                                                  | eq_refl t => eq_refl (h :: t)
                                                  end
                                  end.

(* A definição indutiva de igualdade implica a igualdade de Leibniz: o que queremos 
dizer quando afirmamos que 'x e y são iguais' é que toda propriedade sobre P que é 
verdadeira para x também é verdadeira para y. Prove isso. *)

Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
  x == y -> forall (P : X -> Prop), P x -> P y.
Proof.
  intros X x y H P HPx.
  destruct H as [n].
  apply HPx.
Qed.

(* Construa o objeto de prova para o exercício anterior. Tudo o que ele requer são funções 
anônimas e pattern-matching; o grande termo de prova construído por táticas no exercício 
anterior é desnecessariamente complicado. 
Dica: faça o pattern-matching o mais cedo possível. *)

Definition equality__leibniz_equality_term : forall (X : Type) (x y: X),
    x == y -> forall P : (X -> Prop), P x -> P y :=
    fun X x y Hxy => match Hxy with
                         | eq_refl z => fun P HP => HP
                         end.

(* Mostre que, de fato, a definição indutiva de igualdade é equivalente à igualdade de 
Leibniz. Dica: a prova é bem curta; tudo o que você precisa fazer é inventar uma 
propriedade inteligente P para instanciar o antecedente *)

Lemma leibniz_equality__equality : forall (X : Type) (x y: X),
  (forall P:X->Prop, P x -> P y) -> x == y.
Proof.
  intros X x y H.
  apply H with (P := fun z => x == z).
  apply eq_refl.
Qed.

End EqualityPlayground.

(** Inversão, Novamente **)

(* Vimos a inversão ser usada tanto com hipóteses de igualdade quanto com hipóteses 
sobre proposições definidas indutivamente. Agora que vimos que estas são, na verdade, 
a mesma coisa, estamos em posição de analisar mais de perto como a inversão se comporta.

Em geral, a tática de inversão... 
  - pega uma hipótese H cujo tipo P é definido indutivamente, e
  - para cada construtor C na definição de P, 
    * gera uma nova submeta na qual assumimos que H foi construído com C,
    * adiciona os argumentos (premissas) de C ao contexto da submeta como 
      hipóteses extras,
    * faz a correspondência (match) da conclusão (tipo de resultado) de C contra o 
      objetivo atual e calcula um conjunto de igualdades que devem valer para que C seja 
      aplicável,
    * adiciona essas igualdades ao contexto (e, por conveniência, reescreve-as no 
      objetivo), e
    * se as igualdades não forem satisfazíveis (por exemplo, se envolverem coisas como 
      S n = 0), resolve a submeta imediatamente.

Exemplo: Se invertermos uma hipótese construída com or (ou), há dois construtores, logo 
duas submetas são geradas. A conclusão (tipo de resultado) do construtor (P ∨ Q) não 
impõe nenhuma restrição sobre a forma de P ou Q, portanto não obtemos nenhuma igualdade 
extra no contexto da submeta.

Exemplo: Se invertermos uma hipótese construída com and (e), há apenas um construtor, 
logo apenas uma submeta é gerada. Novamente, a conclusão (tipo de resultado) do 
construtor (P ∧ Q) não impõe nenhuma restrição sobre a forma de P ou Q, de modo que não 
obtemos igualdades extras no contexto da submeta. No entanto, o construtor possui dois 
argumentos, e estes podem ser vistos no contexto da submeta.

Exemplo: Se invertermos uma hipótese construída com eq (igualdade), há novamente apenas 
um construtor, logo apenas uma submeta é gerada. Agora, contudo, a forma do construtor 
eq_refl nos dá alguma informação extra: ele nos diz que os dois argumentos de eq devem 
ser iguais! A tática de inversão adiciona esse fato ao contexto. *)

(********** A Base de Computação Confiável do Rocq (Trusted Computing Base) ************)

(* Uma questão que surge com qualquer assistente de provas automatizado é ''por que 
devemos confiar nele?'' — isto é, e se houver um bug na implementação que torne todo o 
seu raciocínio suspeito?

Embora seja impossível dissipar totalmente essas preocupações, o fato de o Rocq ser 
baseado na correspondência Curry-Howard confere-lhe uma base sólida. Como as proposições 
são apenas tipos e as provas são apenas termos, verificar se uma suposta prova de uma 
proposição é válida resume-se a fazer a checagem de tipos (type-checking) do termo. Os 
verificadores de tipos são programas relativamente pequenos e diretos, de modo que a 
''base de computação confiável'' (trusted computing base) do Rocq — a parte do código em 
que precisamos acreditar que está operando corretamente — também é pequena.

O que um verificador de tipos deve fazer? O seu trabalho principal é garantir que, em 
cada aplicação de função, os tipos de argumentos esperados e reais coincidam; que os ramos 
de uma expressão match sejam padrões de construtores pertencentes ao tipo indutivo sobre 
o qual o match está sendo feito; que todos os ramos do match retornem o mesmo tipo, e 
assim por diante.

Há algumas nuances adicionais:

Primeiro, como os tipos do Rocq podem ser eles próprios expressões, o verificador deve 
normalizá-los (usando as regras de computação) antes de compará-los.

Segundo, o verificador deve garantir que as expressões match sejam exaustivas. Ou seja, 
deve haver um ramo para cada construtor possível. Para ver o porquê, considere o seguinte 
suposto objeto de prova: *)

Fail Definition or_bogus : forall P Q, P \/ Q -> P :=
  fun (P Q : Prop) (A : P \/ Q) =>
    match A with
    | or_introl H => H
    end.

(* Todos os tipos aqui combinam corretamente, mas o match considera apenas um dos 
construtores possíveis para o or. A verificação de exaustividade do Rocq rejeitará esta 
definição.

Terceiro, o verificador deve garantir que cada função recursiva termine. Ele faz isso 
usando uma verificação sintática para garantir que cada chamada recursiva ocorra sobre 
uma subexpressão do argumento original. Para ver por que isso é essencial, considere esta 
suposta prova: *)

Fail Fixpoint infinite_loop {X : Type} (n : nat) {struct n} : X :=
  infinite_loop n.

Fail Definition falso : False := infinite_loop 0.

(* A função recursiva infinite_loop finge retornar um valor de qualquer tipo X que você 
desejar. (A anotação de estrutura (struct) na função diz ao Rocq que ela recursiona sobre 
o argumento n, e não sobre X.) Se o Rocq permitisse infinite_loop, então falso seria 
definível, fornecendo assim evidência para o False. Portanto, o Rocq rejeita infinite_loop.

Note que a solidez (soundness) do Rocq depende apenas da corretidão deste motor de 
verificação de tipos (type-checking), e não do mecanismo de táticas. Se houver um bug 
na implementação de uma tática (o que acontece ocasionalmente), essa tática poderá 
construir um termo de prova inválido. Mas quando você digita Qed, o Rocq verifica a 
validade do termo do zero. Apenas teoremas cujas provas passam pelo verificador de 
tipos podem ser usados em desenvolvimentos de provas posteriores. *)

(********************************** Mais Exercícios ************************************)

(* A maioria dos teoremas a seguir já foi provada com táticas em Logic. Agora, construa 
os objetos de prova para eles diretamente. *)

Definition and_assoc : forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R :=
    fun P Q R H => match H with
                  | conj p (conj q r) => conj (conj p q) r
                  end. 

Definition or_distributes_over_and : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R) :=
    fun P Q R =>
    conj
      (* Direção da ida: P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R) *)
      (fun H =>
         match H with
         | or_introl p => conj (or_introl p) (or_introl p)
         | or_intror (conj q r) => conj (or_intror q) (or_intror r)
         end)
      (* Direção da volta: (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R) *)
      (fun H =>
         match H with
         | conj (or_introl p) _ => or_introl p
         | conj (or_intror q) (or_introl p) => or_introl p
         | conj (or_intror q) (or_intror r) => or_intror (conj q r)
         end).
        
Definition double_neg : forall P : Prop,
    P -> ~~P :=
    fun P p h => h p.

Definition contradiction_implies_anything : forall P Q : Prop,
    (P /\ ~P) -> Q :=
    fun P Q H => match H with
                | conj p np => match np p with end
                end.
               
Definition de_morgan_not_or : forall P Q : Prop,
    ~ (P \/ Q) -> ~P /\ ~Q :=
    fun P Q H => conj (fun p => H (or_introl p)) (fun q => H (or_intror q)).

Definition curry : forall P Q R : Prop,
    ((P /\ Q) -> R) -> (P -> (Q -> R)) :=
    fun P Q R HPQR => fun p q => HPQR (conj p q).
               
Definition uncurry : forall P Q R : Prop,
    (P -> (Q -> R)) -> ((P /\ Q) -> R) :=
    fun P Q R H Hpq =>  match Hpq with
                      | conj p q => H p q
                      end.

(************************* Irrelevância de Provas (Avançado) ***************************)

(* Em Lógica, vimos que a extensionalidade funcional podia ser adicionada ao Rocq. Uma 
noção semelhante sobre proposições também pode ser definida (e adicionada como um axioma, 
se desejado): *)

Definition propositional_extensionality : Prop :=
  forall (P Q : Prop), (P <-> Q) -> P = Q.

(* A extensionalidade proposicional afirma que se duas proposições são equivalentes — 
isto é, cada uma implica a outra — então elas são, de fato, iguais. Os objetos de prova 
para as proposições podem ser termos sintaticamente diferentes. Mas a extensionalidade 
proposicional ignora isso, assim como a extensionalidade funcional ignora as diferenças 
sintáticas entre as funções. *)
    
(* Exercício *)
(* Prove a seguinte consequência da extensionalidade proposicional. *)

Theorem pe_implies_or_eq :
  propositional_extensionality ->
  forall (P Q : Prop), (P \/ Q) = (Q \/ P).
Proof.
  intros pe P Q.
  unfold propositional_extensionality in pe.
  apply pe. split.
  - intros HPQ. destruct HPQ as [HP | HQ].
    + right. apply HP.
    + left. apply HQ.
  - intros HQP. destruct HQP as [HQ | HP].
    + right. apply HQ.
    + left. apply HP.
Qed.

(* Prove que se uma proposição P é provável, então ela é igual a True — como consequência 
da extensionalidade proposicional. *)

Lemma pe_implies_true_eq :
  propositional_extensionality ->
  forall (P : Prop), P -> True = P.
Proof.
  intros pe P HP.
  unfold propositional_extensionality in pe.
  apply pe.
  split.
  - intros HT. apply HP.
  - intros HP'. apply I.
Qed.

(* (Agradecimento: este teorema e sua técnica de prova são inspirados no manuscrito de 
Gert Smolka Modeling and Proving in Computational Type Theory Using the Coq Proof 
Assistant, 2021. 

Outra consequência, talvez surpreendente, da extensionalidade proposicional é que ela 
implica a irrelevância de provas, que afirma que todos os objetos de prova para uma 
proposição são iguais.) *)

Definition proof_irrelevance : Prop :=
  forall (P : Prop) (pf1 pf2 : P), pf1 = pf2.

(* Prove esse fato. Use pe_implies_true_eq para estabelecer que a proposição P em
proof_irrelevance é igual a True. Utilize essa igualdade para estabelecer que ambos os 
objetos de prova pf1 e pf2 devem ser apenas I. *)

Theorem pe_implies_pi :
  propositional_extensionality -> proof_irrelevance.
Proof.
  intros pe. unfold propositional_extensionality in pe.
  unfold proof_irrelevance. intros P pf1 pf2.
  destruct (pe_implies_true_eq pe P pf1).
  destruct pf1. destruct pf2.
  reflexivity.
Qed.