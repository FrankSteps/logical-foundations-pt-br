Require Import Nat.
Require Import List.
Import List.
Import ListNotations.
Require Import Lia.
(* LÓGICA *)
(* LÓGICA EM ROCQ*)

(* Agora já vimos muitos exemplos de afirmações factuais (ou seja, 
proposições) e maneiras de apresentar evidências de sua verdade (provas). 
Em particular, trabalhamos extensivamente com proposições de igualdade 
(e1 ​= e2​), implicações (P → Q) e proposições quantificadas (forallx, P). 
Neste capítulo, veremos como o Rocq pode ser usado para realizar outras 
formas familiares de raciocínio lógico.

Antes de mergulhar nos detalhes, precisamos falar um pouco sobre o status 
das declarações matemáticas no Rocq. O Rocq é uma linguagem tipada, o que 
significa que toda expressão sensata tem um tipo associado. As afirmações 
lógicas não são exceção: qualquer declaração que possamos tentar provar no 
Rocq tem um tipo, a saber, Prop, o tipo das proposições. Podemos ver isso 
com o comando Check: *)

Check (forall n m : nat, n + m = m + n) : Prop.

(* Note que todas as proposições sintaticamente bem formadas têm o tipo 
Prop no Rocq, independentemente de serem verdadeiras ou não.

Simplesmente ser uma proposição é uma coisa; ser provável é uma coisa 
totalmente diferente! *)
Check 2 = 2 : Prop.
Check 3 = 2 : Prop.
Check forall n : nat, n = 2 : Prop.

(* De fato, as proposições não têm apenas tipos — elas são entidades de p
rimeira classe que podem ser manipuladas exatamente da mesma forma que 
qualquer outra coisa no mundo do Rocq.

Até agora, vimos um lugar principal onde as proposições podem aparecer: em 
declarações de Theorem (além de Lemma e Example). *)
Theorem plus_2_2_is_4 :
  2 + 2 = 4.

Proof. reflexivity. Qed.

(* Mas as proposições podem ser usadas de outras maneiras. Por exemplo,
 podemos dar um nome a uma proposição usando uma Definition, assim como 
 damos nomes a outros tipos de expressões. *)
Definition afirmacao_soma : Prop := 2 + 2 = 4.
Check afirmacao_soma : Prop.

(* Podemos usar esse nome posteriormente em qualquer situação onde uma 
proposição seja esperada — por exemplo, como a afirmação em uma declaração 
de Theorem. *)
Theorem afirmacao_soma_e_verdade :
  afirmacao_soma.

Proof. reflexivity. Qed.

(* Também podemos escrever proposições parametrizadas — ou seja, funções 
que aceitam argumentos de algum tipo e retornam uma proposição.

Por exemplo, a função a seguir recebe um número e retorna uma proposição 
afirmando que esse número é igual a três: *)
Definition e_tres (n : nat) : Prop :=
  n = 3.

Check e_tres : nat -> Prop.

(* No Rocq, diz-se que funções que retornam proposições definem 
propriedades de seus argumentos.

Por exemplo, aqui está uma propriedade (polimórfica) que define a noção 
familiar de uma função injetiva. *)
Definition injetivo {A B} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injetivo S.

Proof.
  intros x y H. injection H as H1. apply H1.
Qed.

(* O operador de igualdade familiar = é uma função (binária) que retorna um 
Prop.

A expressão n = m é uma forma abreviada para eq n m (definida na biblioteca 
padrão do Rocq usando o mecanismo de Notação). 

Como eq pode ser usado com elementos de qualquer tipo, ele também é 
polimórfico: *)

Check @eq : forall A : Type, A -> A -> Prop.

(* (Note que escrevemos @eq em vez de eq: o argumento de tipo A para eq é 
declarado como implícito, e precisamos desativar a inferência desse argumento 
implícito para ver o tipo completo de eq.) *)

(*************************** Conectivos Lógicos *****************************)

(******************************** Conjunção *******************************)
(* A conjunção, ou 'e' lógico, das proposições A e B é escrita como A ∧ B;
ela representa a afirmação de que tanto A quanto B são verdadeiros. *)

Notation "A /\ B" := (and A B) : type_scope.
Example e_exemplo : 3 + 4 = 7 /\ 2 * 2 = 4.

(* Para provar uma conjunção, comece com a tática split. Isso gerará duas 
submetas, uma para cada parte da afirmação: *)
Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 * 2 = 4 *) reflexivity.
Qed.

(* Para quaisquer proposições A e B, se assumirmos que A e B são verdadeiras 
individualmente, podemos concluir que A ∧ B também é verdadeira. A 
biblioteca do Rocq fornece uma função 'conj' que faz isso *)
Check @conj : forall A B : Prop, A -> B -> A /\ B.

(* Como a aplicação de um teorema com hipóteses a um objetivo tem o efeito 
de gerar tantas submetas quantas forem as hipóteses desse teorema, podemos 
aplicar conj para alcançar o mesmo efeito que a tática split. *)
Example e_exemplo' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply conj.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(* Exercício *)
Example adicao_e_O :
  forall  n m : nat, n + m = 0 -> n = 0 /\ m = 0.

Proof.
   intros n m H.
   apply conj.
   - destruct n.
     + reflexivity.
     + discriminate H.
   - destruct m.
     + destruct n.
       * reflexivity.
       * discriminate H.
     + destruct n.
       * discriminate H.
       * discriminate H.
Qed. 

(* Por enquanto é isso sobre provar proposições conjuntas. Para ir na 
direção oposta — isto é, usar uma hipótese conjuntiva para ajudar a provar 
outra coisa — podemos usar nossa boa e velha tática destruct.

Quando o contexto atual da prova contém uma hipótese H da forma A ∧ B, 
escrever destruct H as [HA HB] removerá H do contexto e a substituirá por 
duas novas hipóteses: HA, afirmando que A é verdadeira, e HB, afirmando que 
B é verdadeira. *)
    
Lemma e_exemplo2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.

Proof.
  (* TRABALHADO EM AULA *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.
      
(* Como de costume, também podemos destruir H logo no momento em que a 
introduzimos, em vez de introduzi-la primeiro e depois destruí-la: *)

Lemma e_exemplo2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.

Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(* Você deve estar se perguntando por que nos demos ao trabalho de empacotar 
as duas hipóteses n = 0 e m = 0 em uma única conjunção, já que também 
poderíamos ter enunciado o teorema com duas premissas separadas: *)

Lemma e_exemplo2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.

Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(* Para este teorema específico, ambas as formulações funcionam bem. Mas é 
importante entender como trabalhar com hipóteses conjuntivas porque as 
conjunções frequentemente surgem de etapas intermediárias em provas, 
especialmente em desenvolvimentos maiores. Aqui está um exemplo simples: *)

 Lemma e_exemplo3 :
  forall n m : nat, n + m = 0 -> n * m = 0.

Proof.
  intros n m H.
  apply adicao_e_O in H.
  destruct H as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

(* Outra situação comum é que sabemos A ∧ B, mas em algum contexto precisamos 
apenas de A ou apenas de B. Nesses casos, podemos fazer um destruct 
(possivelmente de forma implícita, como parte de um intros) e usar um padrão 
de sublinhado (_) para indicar que a parte da conjunção que não precisamos 
deve simplesmente ser descartada. *)

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.

Proof.
  intros P Q HPQ.
  destruct HPQ as [HP _].
  apply HP. Qed.

(* Exercício *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.

Proof.
  intros P Q HPQ.
  destruct HPQ as [_ HQ].
  apply HQ. Qed.

(* Finalmente, às vezes precisamos reorganizar a ordem das conjunções e/ou 
o agrupamento de conjunções de várias vias (múltiplas). Podemos ver isso em 
ação nas provas dos seguintes teoremas de comutatividade e associatividade: *)

Theorem e_comut : forall P Q : Prop,
  P /\ Q -> Q /\ P.

Proof.
  intros P Q [HP HQ].
  split.
    - (* esquerda *) apply HQ.
    - (* direita *) apply HP. Qed.

(* Exercício *)
(* Na prova de associatividade a seguir, note como o padrão de intros 
aninhado decompõe a hipótese H : P ∧ (Q ∧ R) em HP : P, HQ : Q e HR : R. 
Termine a prova. *)
Theorem e_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.

Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
Qed.

(* A notação infixa ∧ é, na verdade, apenas uma notação simplificada 
para and A B. Ou seja, and é um operador do Rocq (Coq) que recebe duas 
proposições como argumentos e produz uma proposição. *)
Check and : Prop -> Prop -> Prop.
  
(******************************** Disjunção *******************************)

(* Outro conectivo importante é a disjunção, ou o ou lógico, de duas 
proposições: A ∨ B é verdadeiro quando pelo menos A ou B for verdadeiro. 
Essa notação infixa representa or A B, onde or : Prop -> Prop -> Prop.
Para usar uma hipótese disjuntiva em uma prova, procedemos por análise de 
casos — a qual, assim como com outros tipos de dados como nat, pode ser 
feita explicitamente com destruct ou implicitamente com um padrão de intros: *)
Notation "A \/ B" := (or A B) : type_scope.

Lemma fator_e_O:
  forall n m : nat, n = 0 \/  m = 0 -> n * m = 0.

Proof.
  (* Esse padrão de intros implicitamente faz análise de casos em
     n = 0 ∨ m = 0... *)
  intros n m [Hn | Hm].
  - (* Aqui, n = 0 *)
    rewrite Hn. reflexivity.
  - (* Aqui, m = 0 *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

(* Podemos ver neste exemplo que, quando realizamos uma análise de casos em 
uma disjunção A ∨ B, devemos cumprir separadamente duas obrigações de prova, 
cada uma mostrando que a conclusão é válida sob uma premissa diferente — A 
no primeiro subobjetivo e B no segundo.

O padrão de análise de casos [Hn | Hm] permite-nos nomear as hipóteses que 
são geradas para os subobjetivos.

Por outro lado, para mostrar que uma disjunção é verdadeira, basta 
demonstrar que um dos seus lados é válido. Isso pode ser feito por meio das 
táticas 'left' e 'right'. Como os próprios nomes indicam, a primeira exige 
provar o lado esquerdo da disjunção, enquanto a segunda exige provar o lado 
direito. Aqui está um uso trivial... *)

Lemma ou_intro_l : forall A B : Prop, A -> A \/ B.

Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

(* ... e aqui está um exemplo um pouco mais interessante que exige tanto o 
left quanto o right: *)
Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).

Proof.
  (* TRABALHADO EM AULA *)
  intros [ |n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.

(* Exercício *)
Lemma mult_e_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.

Proof.
  intros [ | n'].
  - left. reflexivity.
  - right. destruct m.
    + reflexivity.
    + discriminate H.
Qed.

Theorem ou_comut : forall P Q : Prop,
  P \/ Q -> Q \/ P.

Proof.
  intros P Q [HP | HQ].
  right. apply HP.
  left. apply HQ.
Qed.

(*************************** Falsidade e Negação **************************)

(* Até este ponto, estivemos principalmente preocupados em provar afirmações 
''positivas'' — a adição é comutativa, a concatenação de listas é 
associativa, etc. Às vezes, também nos interessamos por resultados 
negativos, demonstrando que determinada proposição não é verdadeira. Tais 
afirmações são expressas com o operador de negação lógica ¬. Para ver como a 
negação funciona, lembre-se do princípio da explosão do capítulo de Táticas, 
o qual afirma que, se assumirmos uma contradição, qualquer outra proposição 
poderá ser derivada.Seguindo essa intuição, poderíamos definir ¬ P (''não P'') 
como  forall Q, P → Q. Na verdade, o Rocq faz uma escolha equivalente, mas 
ligeiramente diferente, definindo ¬ P como P → False, onde False é uma 
proposição específica não provável definida na biblioteca padrão. *)
 
Definition negacao (P: Prop) := P -> False.

Check negacao : Prop -> Prop.

Notation "~ x" := (negacao x) : type_scope.

(* Como False é uma proposição contraditória, o princípio da explosão 
também se aplica a ela. Se conseguirmos inserir False no contexto, 
poderemos usar destruct nele para completar qualquer objetivo: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.

Proof.
  intros P contra.
  destruct contra. Qed.

(* A expressão em latim ex falso quodlibet significa, literalmente, 
''da falsidade segue-se o que você quiser''; este é outro nome comum para o 
princípio da explosão. *)

(* Exercício *)
(* Mostre que a definição de negação do Rocq implica a definição intuitiva 
mencionada acima.

Dica: Enquanto você se acostuma com a definição de negação (not) do Rocq, 
pode ser útil usar 'unfold negacao' próximo ao início das provas. *)

Theorem negacao_implica_nossa_negacao : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).

Proof.
  intros P HNP Q HP.
  unfold negacao in HNP.
  apply HNP in HP.
  destruct HP.
Qed.

(* A desigualdade é uma forma muito comum de declaração negada, por isso 
existe uma notação especial para ela: *)

Notation "x <> y" := (~(x = y)) : type_scope.

(*Por exemplo*)
Theorem zero_nao_one : 0 <> 1.
Proof.
  
(* A proposição 0 ≠ 1 é exatamente a mesma que ~(0 = 1) — ou seja, negacao
(0 = 1) — que se desdobra em (0 = 1) → False. (Usamos unfold negacao 
explicitamente para ilustrar esse ponto, mas geralmente ele pode ser 
omitido). *)
   unfold negacao.

(* Para provar uma desigualdade, podemos assumir a igualdade oposta... *)
   intros contra.

(* e deduzir uma contradição a partir dela. Aqui, a igualdade O = S O 
contradiz a disjuntiva dos construtores O e S, então o comando 
`discriminate` cuida disso *)
    discriminate contra.
Qed.

(* É preciso um pouco de prática para se acostumar a trabalhar com a negação 
no Rocq. Mesmo que você veja perfeitamente bem por que uma afirmação 
envolvendo negação é verdadeira, pode ser um pouco complicado no início 
entender como fazer o Rocq compreendê-la!

Aqui estão as demonstrações de alguns fatos familiares para ajudar a 
aquecer. *)

Theorem negacao_False :
  ~ False.

Proof.
  unfold negacao. intros H. destruct H. Qed.

Theorem contradicao_implica_qualquer_coisa : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* TRABALHADO EM AULA *)
  intros P Q [HP HNP]. unfold negacao in HNP.
  apply HNP in HP. destruct HP. Qed.

Theorem dupla_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* TRABALHADO EM AULA *)
  intros P H. unfold negacao. intros G. apply G. apply H. Qed.

(* Exercício *)

(* Escreva uma prova informal de double_neg:

Teorema: P implica ~~P, para qualquer proposição P. 

Seja P uma proposição arbitrária. Queremos demonstrar que P implica ¬¬P, ou 
seja, P→¬¬P.

    Assumimos que P é verdadeira (seja H essa premissa).

    Pela definição de negação, provar ¬¬P significa provar ¬P → False, ou 
    seja, que assumir ¬P leva a uma contradição.

    Introduzimos então a hipótese auxiliar ¬P (ou seja, P→False) e a 
    chamamos de G.

    Como nosso objetivo atual é alcançar uma contradição (o absurdo False), 
    podemos aplicar a nossa hipótese G, sabendo que para usá-la precisamos 
    fornecer uma prova de P.

    Fornecemos exatamente a prova de P que tínhamos inicialmente na hipótese 
    H, fechando a contradição e provando o teorema. *)

Theorem contrapositiva : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).

Proof.
  intros P Q H HNQ HP.
  unfold negacao in HNQ. apply H in HP. apply HNQ in HP. apply HP.
Qed.


Theorem negacao_ambos_verdadeiro_e_falso : forall P : Prop,
  ~ (P /\ ~P).

Proof.
 intros P H.
  destruct H as [HP HnP].
  unfold negacao in HnP.
  apply HnP.
  apply HP.
Qed.

(* Escreva uma prova informal da proposição forall P : Prop, ~(P ∧ ¬P).

Seja P uma proposição arbitrária. Queremos demonstrar que é impossível que 
P e sua negação ocorram simultaneamente, ou seja, ~(P ∧ ¬P).

Seja P uma proposição qualquer, e assuma por hipótese que a conjunção 
(P ∧ ¬P) é verdadeira (chamemos essa premissa de H).

Como H é uma conjunção, podemos dividi-la em duas partes: chamamos o lado 
esquerdo (P) de HP e o lado direito (¬P) de HnP.

Expandimos a definição de negação em HnP, transformando-o na implicação 
P → False. 

Para alcançar uma contradição (o objetivo False), aplicamos a hipótese HnP, o 
que nos obriga a provar P.

Usamos diretamente a parte HP para satisfazer esse objetivo, concluindo a 
demonstração. *)

(* As Leis de De Morgan, batizadas em homenagem a Augustus De Morgan, 
descrevem como a negação interage com a conjunção e a disjunção. A lei a 
seguir diz que a ''negação de uma disjunção é a conjunção das negações''. 
Há uma lei dual de_morgan_not_and_not à qual retornaremos no final deste 
capítulo. *)

Theorem de_morgan_negacao_ou : forall (P Q : Prop),
    ~ (P \/ Q) -> ~P /\ ~Q.

Proof.
  intros P Q H.
  split.
  (* ~P *)
  intro HP.
  unfold negacao in H.
  destruct H. 
  left. apply HP.
  (* ~Q *)
  intro HQ.
  unfold negacao in H.
  destruct H.
  right. apply HQ.
Qed.

(* Como estamos trabalhando com números naturais, podemos demonstrar que 
S e pred não são inversos um do outro: *)
Lemma negacao_S_pred_n : ~(forall n : nat, S (pred n) = n).

Proof.
   intros Hn. 
   specialize Hn with (n := O) . discriminate.
Qed.

(* Como a desigualdade envolve uma negação, também é preciso um pouco de 
prática para conseguir trabalhar com ela fluentemente. Aqui está um truque 
útil. 
Se você está tentando provar um objetivo que não faz sentido (por exemplo, 
o estado do objetivo é false = true), aplique ex_falso_quodlibet para mudar 
o objetivo para False.
Isso facilita o uso de hipóteses da forma ¬P que possam estar disponíveis 
no contexto — em particular, hipóteses da forma x ≠ y. *)

Theorem negacao_true_e_false : forall b : bool,
  b <> true -> b = false.

Proof.
  intros b H. destruct b eqn:HE.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

(* Como o raciocínio com ex_falso_quodlibet é bastante comum, o Rocq 
fornece uma tática nativa, exfalso, para aplicá-lo. *)

Theorem negacao_true_e_false' : forall b : bool,
  b <> true -> b = false.

Proof.
  intros [] H. (* note o destruct b implícito aqui! *)
  - (* b = true *)
    unfold not in H.
    exfalso. (* <=== *)
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.

(********************************** Verdade *******************************)

(* Além de False, a biblioteca padrão do Rocq também define True, uma 
proposição que é trivialmente verdadeira. Para prová-la, usamos a constante 
I : True, que também está definida na biblioteca padrão: *)

Lemma True_e_verdadeiro : True.
Proof. apply I. Qed.

(* Ao contrário de False, que é usado extensivamente, True é usado 
relativamente pouco: é trivial (e, portanto, desinteressante) de provar 
como um objetivo, e não fornece nenhuma informação útil quando aparece como 
uma hipótese.

No entanto, True pode ser bastante útil ao definir Props complexas usando 
condicionais ou como um parâmetro para Props de ordem superior. Voltaremos a 
isso mais tarde.

Por ora, vamos dar uma olhada em como podemos usar True e False para alcançar 
um efeito semelhante ao da tática discriminate, sem usar literalmente o 
discriminate.

A correspondência de padrões (pattern-matching) nos permite fazer coisas 
diferentes para diferentes construtores. Se o resultado de aplicar dois 
construtores diferentes fosse hipoteticamente igual, poderíamos usar match 
para converter uma declaração improvável (como False) em uma que seja 
provável (como True). *)

Definition disc_fn (n: nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.

Theorem disc_example : forall n, ~ (O = S n).

Proof.
  intros n contra.
  assert (H : disc_fn O). { simpl. apply I. }
  rewrite contra in H. simpl in H. apply H.
Qed.

(* Para generalizar isso para outros construtores, precisamos apenas 
fornecer uma variante apropriada de disc_fn. Para generalizá-lo para 
outras conclusões, podemos usar exfalso para substituí-las por False.

A tática integrada discriminate cuida de tudo isso para nós. *)

(* Utilize a mesma técnica acima para mostrar que nil ≠ x :: xs. Não utilize 
a tática discriminate. *)

Definition disc_fn' {X : Type} (l: list X) : Prop :=
  match l with
  | [] => True
  | h :: t => False
  end.

Theorem nil_e_negacao_de_cons : forall X (x : X) (xs : list X), 
~ (nil = x :: xs).

Proof.
   intros X x xs contra.
   assert (H : @disc_fn' X []). { simpl. apply I. }
   rewrite contra in H. simpl in H. apply H.
Qed.
  
(******************************* Equivalência Lógica **********************)

(* O útil conectivo ''se e somente se'', que afirma que duas proposições têm 
o mesmo valor de verdade, é simplesmente a conjunção de duas implicações. *)
Print "<->".

(* ===>
     Notation ''A <-> B'' := (iff A B)

     iff = fun A B : Prop => (A -> B) /\ (B -> A)
         : Prop -> Prop -> Prop

     Arguments iff (A B) *)

Theorem sse_simetrico : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).

Proof.
  (* TRABALHADO EM AULA *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB. Qed.

Lemma negacao_true_sse_false : forall b,
  b <> true <-> b = false.

Proof.
  intros b. split.
  - (* -> *) apply negacao_true_e_false.
  - (* <- *)
    intros H. rewrite H. intros H'. discriminate H'.
Qed.

(* Também podemos usar o apply com um ↔ em qualquer direção, sem pensar 
explicitamente no fato de que ele é, na verdade, um ''e'' subjacente. *)

Lemma apply_sse_exemplo1:
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
  
Proof.
  intros P Q R Hsse H HP. apply H. apply Hsse (* P -> Q *). apply HP.
Qed.

Lemma apply_sse_examplo2:
  forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
  
Proof.
  intros P Q R Hsse H HQ. apply H. apply Hsse (* Q -> P *). apply HQ.
Qed.

(* Exercício *)
(* Usando a prova acima de que ↔ é simétrico (sse_simetrico) como guia, 
prove que ele também é reflexivo e transitivo. *)
Theorem sse_refl : forall P : Prop,
  P <-> P.

Proof.
  intros P.
  split.
  - intros HP. apply HP.
  - intros HP. apply HP.
Qed.

Theorem sse_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).

Proof.
  intros P Q R [HPQ HQP] HbiQR. destruct HbiQR.
  split. 
  (* P -> R*)
  - intros HP. apply H. apply HPQ. apply HP.
  (* R -> P *)
  - intros HR. apply HQP. apply H0. apply HR.
Qed.

Theorem ou_distributiva_sobre_e : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R). 

Proof.
   intros P Q R.
   split.
   - intros [HP | [HQ HR]]. 
     + split. left. apply HP. left. apply HP.
     + split. right. apply HQ. right. apply HR.
   - intros [[HP | HQ] [HP' | HR]].
    + left. apply HP.
    + left. apply HP.
    + left. apply HP'. 
    + right. split. apply HQ. apply HR.
Qed.

(********************** Setoides e Equivalência Lógica ********************)

(* Algumas táticas do Rocq tratam sentenças sse (iff) de maneira especial, 
evitando parte da manipulação de baixo nível do estado de prova. Em 
particular, rewrite e reflexivity podem ser usadas com sentenças sse, e não 
apenas com igualdades. Para habilitar esse comportamento, precisamos 
importar a biblioteca do Rocq que dá suporte a isso: *)
From Stdlib Require Import Setoids.Setoid.

(* Um ''setoide'' é um conjunto equipado com uma relação de equivalência — 
isto é, uma relação que é reflexiva, simétrica e transitiva. Quando dois 
elementos de um conjunto são equivalentes de acordo com a relação, `rewrite` 
pode ser usado para substituir um pelo outro.

Já vimos isso antes com a relação de igualdade `=` no Rocq: quando `x = y`, 
podemos usar `rewrite` para substituir `x` por `y` ou vice-versa.

Da mesma forma, a relação de equivalência lógica `↔` é reflexiva, simétrica 
e transitiva, então podemos usá-la para substituir uma parte de uma 
proposição por outra: se `P ↔ Q`, podemos usar `rewrite` para substituir `P` 
por `Q`, ou vice-versa.

Aqui está um exemplo simples demonstrando como essas táticas funcionam com 
`sse`.

Primeiro, vamos provar algumas equivalências básicas de `sse`. (Para essas 
provas, ainda não estamos usando setoides.) *)

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.

Proof.
  split.
  - apply mult_e_O.
  - apply fator_e_O.
Qed.

Theorem ou_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
  
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

(* Podemos agora usar esses fatos com rewrite e reflexivity para provar uma 
versão ternária do fato mult_eq_0 acima, sem precisar dividir o sse de nível 
superior: *)

Lemma mul_eq_0_ternario :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0
  .
Proof.
  intros n m p.
  rewrite mul_eq_0. rewrite mul_eq_0. rewrite ou_assoc.
  reflexivity.
Qed.

(************************* Quantificação Existencial **********************)

(* Outro conectivo lógico fundamental é a quantificação existencial. Para 
dizer que existe algum x do tipo T tal que alguma propriedade P é válida 
para x, escrevemos exists x : T, P. Assim como com o forall, a anotação de tipo : T 
pode ser omitida se o Rocq for capaz de inferir a partir do contexto qual 
deveria ser o tipo de x.
Para provar uma afirmação da forma exists x, P, devemos mostrar que P é válida 
para alguma escolha específica de x, conhecida como a testemunha (witness) 
da quantificação existencial. Isso é feito em duas etapas: primeiro, dizemos 
explicitamente ao Rocq qual testemunha t temos em mente invocando a tática 
exists t. Em seguida, provamos que P é válida após todas as ocorrências de x 
serem substituídas por t. *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Definition Par x := exists n : nat, x = double n.

Check Par : nat -> Prop.

Lemma quatro_e_Par : Par 4.

Proof.
  unfold Par. exists 2. reflexivity.
Qed.

(* Por outro lado, se temos uma hipótese existencial exists x, P no contexto, 
podemos usar destruct nela para obter uma testemunha x e uma hipótese 
afirmando que P é válida para x. *)

Theorem existe_examplo_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).

Proof.
  (* TRABALHADO EM AULA *)
  intros n [m Hm]. (* note o destruct implícito aqui *)
  exists (2 + m).
  apply Hm. Qed.

(* Exercício *)
(* Prove que ''P é válido para todo x'' implica ''não existe x para o qual 
P não seja válido''. (Dica: destruct H as [x E] funciona em hipóteses 
existenciais!) *)
Theorem dist_nao_existe : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).

Proof.
  intros X P Hf He.
  destruct He as [x E].
  unfold negacao in E. apply E. apply Hf.
Qed.

(* Prove que a quantificação existencial se distribui sobre a disjunção. *)
Theorem dist_existe_ou : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).

Proof.
   intros X P Q. 
   split.
   - intros [x H]. destruct H.
    + left. exists x. apply H.
    + right. exists x. apply H.
   - intros [HeP | HeQ]. destruct HeP.
    + exists x. left. apply H.
    + destruct HeQ. exists x. right. apply H.
Qed.

Theorem leb_mais_existe : forall n m, n <=? m = true -> exists x, m = n + x.

Proof.
 intros n.
 induction n as [ | n' IHn'].
 - intros m H.
   exists m. reflexivity.
 - intros m H.
   destruct m as [ | m'].
   + discriminate H.
   + simpl in H.
     apply IHn' in H.
     destruct H as [x Hx].
     exists x. simpl. rewrite Hx. reflexivity.
Qed.

Theorem mais_existe_leb : forall n m, 
    (exists x, m = n + x) -> n <=? m = true.

Proof.
  intros n.
  induction n as [ | n' IHn'].
  - intros m H. 
     reflexivity.
  - intros m H. destruct H as [x E].
     + destruct m as [ | m'].
       discriminate E.
       simpl. apply IHn'. exists x. injection E as E. apply E.
Qed.

(************** Recapitulação -- Conectivos lógicos no Rocq ***************)

(* Conectivos básicos:

    and (e) : Prop → Prop → Prop (conjunção): 
    introduzido com a tática split; 
    eliminado com destruct H as [H1 H2]

    or (ou) : Prop → Prop → Prop (disjunção): 
    introduzido com as táticas left e right; 
    eliminado com destruct H as [H1 | H2]

    False : Prop 
    eliminado com destruct H as []

    True : Prop 
    introduzido com apply I, mas não tão útil

    ex : forall A:Type, (A → Prop) → Prop (existencial): 
    introduzido com exists w; 
    eliminado com destruct H as [x H]

Conectivos derivados:

    not (negacao) : Prop → Prop (negação): 
    not P definido como P → False

    iff (sse) : Prop → Prop → Prop (equivalência lógica): 
    iff P Q definido como (P → Q) ∧ (Q → P)

Conectivos fundamentais que estamos usando desde o início:

    igualdade (e1 = e2)

    implicação (P → Q)

    quantificação universal (forall x, P) *)

(*********************** Programação com Proposições **********************)

(* Os conectivos lógicos que vimos fornecem um vocabulário rico para 
definir proposições complexas a partir de outras mais simples. Para 
ilustrar, vamos ver como expressar a afirmação de que um elemento x ocorre 
em uma lista $l$. Note que essa propriedade tem uma estrutura recursiva 
simples:Se l é a lista vazia, então x não pode ocorrer nela, logo a 
propriedade ''x aparece em l'' é simplesmente falsa. Caso contrário, l tem a 
forma x' :: l'. Nesse caso, x ocorre em l se for igual a x' ou se ocorrer em 
l'. Podemos traduzir isso diretamente para uma função recursiva direta que 
recebe um elemento e uma lista e retorna... uma proposição! *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

(* Quando In é aplicado a uma lista concreta, ele se expande em uma 
sequência concreta de disjunções aninhadas. *)

Example In_examplo_1 : In 4 [1; 2; 3; 4; 5].

Proof.
  (* TRABALHADO EM AULA *)
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_examplo_2 :
  forall n, In n [2; 4] -> Par n.

Proof.
  (* TRABALHADO EM AULA *)
  intros n H. unfold Par. simpl in H.
  destruct H as [H | [H | []]].
  - rewrite <- H. exists 1. reflexivity.
  - rewrite <- H. exists 2. reflexivity.
Qed.

(* (Note o uso do padrão vazio para descartar o último caso en passant.)

Também podemos raciocinar sobre declarações mais genéricas envolvendo o In. *)

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
         In x l ->
         In (f x) (map f l).

Proof.
  intros A B f l x H.
  induction l as [ |x' l' IHl'].
  - (* l = nil, contradição *)
    simpl. simpl in H. destruct H as [].
  - (* l = x' :: l' *)
    simpl. simpl in H. destruct H as [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(* (Note aqui como o In começa aplicado a uma variável e só é expandido 
quando fazemos análise de casos nessa variável.)

Essa forma de definir proposições recursivamente é muito conveniente em 
alguns casos, e menos em outros. Em particular, ela está sujeita às 
restrições usuais do Rocq referentes a definições de funções recursivas, 
por exemplo, a exigência de que sejam ''obviamente terminantes'' 
(garantidas como finitas).

No próximo capítulo, veremos como definir proposições indutivamente — uma 
técnica diferente com suas próprias forças e limitações. *)

(* Exercício *)
Theorem In_map_sse :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
         In y (map f l) <->
         exists x, f x = y /\ In x l.

Proof.
  intros A B f l y. split.
  (* -> *)
  - induction l as [ |x l' IHl'].
    + simpl. intros H. destruct H as []. (* Lista vazia: absurdo *)
    + simpl. intros [H | H].
      * exists x. split.
        -- apply H.             (* f x = y *)
        -- left. reflexivity.   (* x é o primeiro elemento *)
      * apply IHl' in H as [x0 [H1 H2]].
        exists x0. split.
        -- apply H1.
        -- right. apply H2.     (* x0 está na cauda *)
  (* <- *)
  - intros [x [H1 H2]].
    rewrite <- H1.
    induction l as [ |x' l' IHl'].
    + destruct H2 as [].        (* Lista vazia contradiz H2 *)
    + simpl in H2. destruct H2 as [H2 | H2].
      * subst x'. simpl. left. reflexivity.  (* x é a cabeça *)
      * simpl. right. apply IHl'. apply H2.  (* x está na cauda *)
Qed.

Theorem In_juntar_sse : forall A l l' (a:A),
  In a (l ++ l') <-> In a l \/ In a l'.

Proof.
  intros A l. induction l as [ |a' l' IH]. split. 
   (* lista vazia *)
  - simpl. intros H_in. right. apply H_in. (* -> *)
   (* <- *)
  - simpl. intros H_ou. destruct H_ou as [H | H].
    + destruct H as [].
    + apply H.
  (* lista com head e tail *) 
  - split.
     (* -> *) 
     + intros H_in. simpl. simpl in H_in. destruct H_in as [H | H].
       * left. left. apply H.
       * apply IH in H. destruct H as [H | H].
          -- left. right. apply H.
          -- right. apply H.
      (* <- *)
      + intros H_in. simpl. simpl in H_in. destruct H_in as [H | H].
        * destruct H as [H | H].
          -- left. apply H.
          -- right. apply IH. left. apply H.
        * right. apply IH. right. apply H.
Qed.

(* Observamos acima que funções que retornam proposições podem ser vistas 
como propriedades de seus argumentos. Por exemplo, se P tem o tipo 
nat → Prop, então P n afirma que a propriedade P é válida para n.
Buscando inspiração em In, escreva uma função recursiva All afirmando que 
alguma propriedade P é válida para todos os elementos de uma lista l. Para 
garantir que sua definição está correta, prove o lema All_In abaixo. 
(Naturalmente, sua definição não deve apenas reescrever o lado esquerdo de 
All_In.) *)

(* Todos os elementos tem que satisfazer a proposição ao mesmo tempo*)
Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
   match l with
   |[] => True
   | x :: l' => P x /\ All P l'
   end.
  
Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.

Proof.
 intros T P  l. 
 split.
 (* -> *)
 - induction l as [ | h t IHl'].
 (* [ ] *)
   + reflexivity.
 (* h :: t*)
   + simpl. intros H. split.
     ++ apply H. left. reflexivity.
     ++ apply IHl'. intros x H1.
        -- apply H. right. apply H1.
  (* <- *)
  - intros H. intros x. induction l as [ | h t IHl'].
  (* [ ] *)
     + intros H_in. simpl in H_in. destruct H_in as [].
  (* h :: t *)
     + simpl in IHl'. simpl in H. intros H_in. simpl in H_in. 
     destruct H as [H1 H2]. destruct H_in as [H | H].
      ++ rewrite <- H. apply H1.
      ++ apply IHl'. apply H2. apply H.
Qed.

(* Complete a definição de combine_odd_even abaixo. Ela recebe como 
argumentos duas propriedades de números, Ppar e Pimpar, e deve retornar uma 
propriedade P tal que P n seja equivalente a Pimpar n quando n for ímpar e 
equivalente a Ppar n caso contrário. *)

Definition combine_impar_par (Pimpar Ppar : nat -> Prop) : nat -> Prop :=
   fun n => if  Nat.odd n then Pimpar n else Ppar n.

(* Para testar sua definição, prove os seguintes fatos: *)
Theorem combine_impar_par_intro :
  forall (Pimpar Ppar : nat -> Prop) (n : nat),
    (Nat.odd n = true -> Pimpar n) ->
    (Nat.odd n = false -> Ppar n) ->
    combine_impar_par Pimpar Ppar n.
    
Proof. 
  intros Pimpar Ppar n H1 H2.
  unfold combine_impar_par. destruct (Nat.odd n) eqn:H.
  - apply H1. reflexivity.
  - apply H2. reflexivity.
Qed.

Theorem combine_impar_par_elim_impar :
  forall (Pimpar Ppar : nat -> Prop) (n : nat),
    combine_impar_par Pimpar Ppar n ->
    Nat.odd n = true ->
    Pimpar n.

Proof.
  intros Pimpar Ppar n H1 H2.
  unfold combine_impar_par in H1.
  destruct (Nat.odd n) eqn:H.
  - apply H1.
  - discriminate H2.
Qed.


Theorem combine_impar_par_elim_par :
  forall (Pimpar Ppar : nat -> Prop) (n : nat),
    combine_impar_par Pimpar Ppar n ->
    Nat.odd n = false ->
    Ppar n.

Proof.
  intros Pimpar Ppar n H1 H2.
  unfold combine_impar_par in H1. destruct (Nat.odd n) eqn:H.
  - discriminate H2.
  - apply H1.
Qed.

(********************* Aplicando Teoremas a Argumentos *******************)

(* Uma característica que diferencia o Rocq de outros assistentes de prova 
populares (por exemplo, ACL2 e Isabelle) é que ele trata provas como 
objetos de primeira classe.

Há muito o que dizer sobre isso, mas não é necessário entender tudo para 
usar o Rocq. Esta seção dá apenas uma amostra, deixando uma exploração 
mais profunda para os capítulos opcionais ProofObjects e IndPrinciples.

Vimos que podemos usar Check para pedir ao Rocq que verifique se uma 
expressão possui um determinado tipo: *)

Check plus : nat -> nat -> nat.
Check @rev : forall X, list X -> list X.

(* Também podemos usá-lo para verificar a qual teorema um determinado 
identificador se refere: *)

(* Teoremas visto anteriormente *)
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

Theorem mais_id_exemplo :
   forall (n m : nat) ,
   n = m -> n + n = m + m.

Proof.
   intros n m. (* Move ambos os quantificadores para o contexto*)
   intros H. (* Move a hipótese - chamamos de H - para o contexto *)
   rewrite -> H. (* Reesreve 'goal' usando a hipótese *)
reflexivity. Qed.


Check add_comutativo : forall n m : nat, n + m = m + n.
Check mais_id_exemplo : forall n m : nat, n = m -> n + n = m + m.

(* O Rocq verifica as declarações dos teoremas add_comutativo e 
mais_id_exemplo da mesma forma que verifica o tipo de qualquer termo (por 
exemplo, plus). Se omitirmos os dois-pontos e o tipo, o Rocq imprimirá esses 
tipos para nós.

Por quê?

O motivo é que o identificador add_comutativo na verdade se refere a um 
objeto de prova — uma derivação lógica que estabelece a verdade da 
declaração forall n m : nat, n + m = m + n. O tipo desse objeto é a 
proposição da qual ele é uma prova. O tipo de uma função comum nos diz o 
que podemos fazer com ela. Se temos um termo do tipo nat -> nat -> nat,
podemos fornecer a ele dois números naturais como argumentos e obter um 
natural de volta.

Da mesma forma, a declaração de um teorema nos diz para que podemos usar 
esse teorema. Se temos um termo do tipo forall n m, n = m -> n + n = m + m 
e fornecemos a ele dois números n e m e um terceiro ''argumento'' do tipo 
n = m, obtemos de volta um objeto de prova do tipo n + n = m + m.

Operacionalmente, essa analogia vai ainda mais longe: ao aplicar um teorema 
como se fosse uma função — ou seja, aplicando-o a valores e hipóteses com 
tipos correspondentes —, podemos especializar seu resultado sem precisar 
recorrer a asserções intermediárias. Por exemplo, suponha que quiséssemos 
provar o seguinte resultado: *)

Lemma add_comutativo3 :
  forall x y z, x + (y + z) = (z + y) + x.

(* À primeira vista, parece que deveríamos ser capazes de provar isso 
reescrevendo com add_comutativo duas vezes para fazer os dois lados 
coincidirem. O problema é que a segunda reescrita desfará o efeito da 
primeira. *)

Proof.
  intros x y z.
  rewrite add_comutativo.
  rewrite add_comutativo.
  (* Voltamos de onde começamos... *)
Abort.

(* Encontramos problemas semelhantes no capítulo Indução, e vimos uma 
maneira de contorná-los usando assert para derivar uma versão especializada 
de add_comutativo que pode ser usada para reescrever exatamente onde 
queremos.*)


Lemma add_comutativo3_tentativa2 :
  forall x y z, x + (y + z) = (z + y) + x.

Proof.
  intros x y z.
  rewrite add_comutativo.
  assert (H : y + z = z + y).
    { rewrite add_comutativo. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

(* Uma alternativa mais elegante é aplicar add_comutativo diretamente aos 
argumentos com os quais queremos instanciá-lo, da mesma forma que aplicamos 
uma função polimórfica a um argumento de tipo. *)

Lemma add_comutativo3_tentativa3 :
  forall x y z, x + (y + z) = (z + y) + x.

Proof.
  intros x y z.
  rewrite add_comutativo.
  rewrite (add_comutativo y z).
  reflexivity.
Qed.

(* Se nós realmente quiséssemos, poderíamos de fato fazer isso para ambas 
as reescritas. *)

Lemma add_comutativo_tentativa4 :
  forall x y z, x + (y + z) = (z + y) + x.

Proof.
  intros x y z.
  rewrite (add_comutativo x (y + z)).
  rewrite (add_comutativo y z).
  reflexivity.
Qed.

(* Aqui está outro exemplo do uso de um teorema sobre listas como uma 
função. Suponha que tenhamos provado o seguinte fato simples sobre listas... *)

Theorem in_nao_e_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].

Proof.
  intros A x l H. unfold negacao. intro Hl.
  rewrite Hl in H.
  simpl in H.
  apply H.
Qed.

(* (Ou seja, se uma lista l contém algum elemento x, então l deve ser não 
vazia.)Note que uma variável quantificada (x) não aparece na conclusão 
(l ≠ []).Intuitivamente, deveríamos ser capazes de usar este teorema para 
provar o caso especial em que x é 42. No entanto, simplesmente invocar a 
tática apply in_nao_e_nil vai falhar porque ela não consegue inferir o 
valor de x. *)

Lemma in_nao_e_nil_42 :
  forall l : list nat, In 42 l -> l <> [].

Proof.
  intros l H.
  Fail apply in_nao_e_nil.
Abort.

(* Há várias maneiras de contornar isso:
Podemos usar apply ... with ... : *)

Lemma in_nao_e_nil_42_tentativa2 :
  forall l : list nat, In 42 l -> l <> [].

Proof.
  intros l H.
  apply in_nao_e_nil with (x := 42).
  apply H.
Qed.

(* Ou podemos usar apply ... in ...: *)

Lemma in_nao_e_nil_42_tentativa3 :
  forall l : list nat, In 42 l -> l <> [].
  
Proof.
  intros l H.
  apply in_nao_e_nil in H.
  apply H.
Qed.

(* Ou — esta é a novidade — podemos aplicar explicitamente o lema ao valor 
42 para x: *)

Lemma in_nao_e_nil_42_tentativa4 :
  forall l : list nat, In 42 l -> l <> [].

Proof.
  intros l H.
  apply (in_nao_e_nil nat 42).
  apply H.
Qed.

(* Também podemos aplicar explicitamente o lema a uma hipótese, fazendo com 
que os valores dos outros parâmetros sejam inferidos: *)
Lemma in_nao_e_nil_42_tentativa5 :
  forall l : list nat, In 42 l -> l <> [].

Proof.
  intros l H.
  apply (in_nao_e_nil _ _ _ H).
Qed.

(* Você pode ''usar um teorema como uma função'' dessa maneira com quase 
qualquer tática que possa receber o nome de um teorema como argumento.

Note também que a aplicação de teoremas usa os mesmos mecanismos de 
inferência que a aplicação de funções; portanto, é possível, por exemplo, 
fornecer curingas (wildcards) como argumentos a serem inferidos, ou 
declarar algumas hipóteses de um teorema como implícitas por padrão. Esses 
recursos são ilustrados na prova abaixo. (Os detalhes de como essa prova 
funciona não são críticos — o objetivo aqui é apenas ilustrar a aplicação 
de teoremas a argumentos.) *)

(* Lema Auxiliar *)
Lemma mul_0_r : forall n : nat,
  n * 0 = 0.

Proof.
   intros n.
   induction n as [ | n' IHn'].
   - simpl. reflexivity.
   - simpl. rewrite -> IHn'. reflexivity.
Qed. 


Example lemma_aplicacao_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.

Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_sse _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mul_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

(* Veremos muitos outros exemplos nos próximos capítulos. *)

(******** Trabalhando com Propriedades Decidíveis *********)

(* Vimos duas maneiras diferentes de expressar afirmações 
lógicas em Rocq: com booleanos (do tipo bool) e com 
proposições (do tipo Prop).

Aqui estão as principais diferenças entre bool e Prop:


                                           bool     Prop
                                           ====     ====
           decidível?                      sim      não
           utilizável com match?           sim      não
           funciona com a tática rewrite?  não      sim

A diferença crucial entre os dois mundos é a decidibilidade. 
Toda expressão (fechada) de Rocq do tipo bool pode ser 
simplificada em um número finito de passos para true ou 
false — ou seja, existe um procedimento mecânico terminante 
para decidir se ela é verdadeira ou não.

Isso significa que, por exemplo, o tipo nat → bool é 
habitado apenas por funções que, dado um nat, sempre 
produzem true ou false em tempo finito; e isso, por sua vez, 
significa (por um argumento padrão de computabilidade) que 
não há nenhuma função em nat → bool que verifique se um 
determinado número é o código de uma máquina de Turing que 
termina.

Em contrapartida, o tipo Prop inclui proposições matemáticas 
tanto decidíveis quanto indecidíveis; em particular, o tipo 
nat → Prop contém funções que representam propriedades como 
''a n-ésima máquina de Turing para''.

A segunda linha da tabela decorre diretamente dessa 
diferença essencial. Para avaliar uma correspondência de 
padrões (pattern match ou condicional) em um booleano, 
precisamos saber se o objeto avaliado resulta em true ou 
false; isso só funciona para bool, não para Prop.

A terceira linha destaca uma diferença prática importante: 
funções de igualdade como eqb_nat que retornam um booleano 
não podem ser usadas diretamente para justificar a reescrita 
com a tática rewrite; a igualdade proposicional é necessária 
para isso.

Como Prop inclui propriedades tanto decidíveis quanto 
indecidíveis, temos duas opções quando queremos formalizar 
uma propriedade que por acaso é decidível: podemos 
expressá-la como uma computação booleana ou como uma função 
em Prop. *)

Example par_42_bool : Nat.even 42 = true.
Proof. reflexivity. Qed.

(* ... ou que existe algum k tal que n = double k *)

Example par_42_prop : Par 42.
Proof. unfold Par. exists 21. reflexivity. Qed.

(* É claro que seria profundamente estranho se essas duas 
caracterizações da paridade não descrevessem o mesmo 
conjunto de números naturais!

Felizmente, elas descrevem!

Para provar isso, primeiro precisamos de dois lemas 
auxiliares. *)

Lemma par_double : forall k, even (double k) = true.
Proof.
  intros k. induction k as [ |k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(* Exercício *)
(* Dica: Use the lema S_par de a_Inducao.v. *)
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
Qed.

Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
  
Proof.
  intros n. 
  induction n as [ | n' IHn'].
  - exists O. reflexivity.
  - destruct IHn' as [k IHk]. destruct (even n') eqn: Heven.
    + exists k. rewrite IHk. rewrite S_par. rewrite par_double. simpl. reflexivity.
    + exists (S k). rewrite IHk. rewrite S_par. rewrite <- IHk. rewrite Heven. 
      simpl. rewrite <- IHk. reflexivity.
Qed.

(* Agora o teorema principal: *)

Theorem par_bool_prop : forall n,
  even n = true <-> Par n.

Proof.
  intros n. split.
  - intros H. destruct (even_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. 
    rewrite Hk. 
    apply par_double.
Qed.

(* Em vista deste teorema, podemos dizer que o cálculo booleano even n 
reflete-se na veracidade da proposição ∃ k, n = double k. 

Da mesma forma, para afirmar que dois números n e m são iguais, podemos dizer 
que 
(1) n =? m retorna true, ou 
(2) n = m. 
Mais uma vez, essas duas noções são equivalentes: *)

(* Teoremas Auxiliares *)
Theorem eqb_true : forall (n m : nat ),
  n =? m = true -> n = m.

Proof.
  intros n. induction n as [ | n' IHn'].
  - intros m eq. induction m as [ | m'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros m eq. destruct m as [ | m'] eqn:E. 
    + discriminate eq.
+ f_equal. apply IHn'. simpl in eq. apply eq. Qed.

Theorem eqb_refl:
   forall n: nat, (n =? n) = true.

Proof.
   intros n. induction n as [ | n' IHn'].
   - simpl. reflexivity.
   - simpl. rewrite IHn'. reflexivity.
Qed.

(* Teorema Principal *)
Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite eqb_refl. reflexivity.
Qed.

(* Então, o que devemos fazer em situações em que uma determinada afirmação 
pode ser formalizada tanto como uma proposição quanto como uma computação 
booleana? Qual delas devemos escolher?

Em geral, ambas podem ser úteis. 

Por exemplo, os booleanos são mais úteis para definir computações. Não há 
uma maneira efetiva de testar se um Prop é verdadeiro ou não, por isso não 
podemos usar Props em expressões condicionais. A seguinte definição é 
rejeitada: *)

Fail
Definition e_par_primo n :=
  if n = 2 then true
  else false.

(* O Rocq reclama que n = 2 tem o tipo Prop, enquanto ele espera um elemento 
de bool (ou algum outro tipo indutivo com dois construtores). Isso tem a ver 
com a natureza computacional da linguagem principal do Rocq, que é projetada 
para que cada função que ela consiga expressar seja computável e total. (Uma 
razão para isso é permitir a extração de programas executáveis a partir de 
desenvolvimentos em Rocq.) Como consequência, Prop no Rocq não possui uma 
operação universal de análise de casos que informe se uma dada proposição é 
verdadeira ou falsa, já que tal operação nos permitiria escrever funções não 
computáveis. 

Em vez disso, temos que declarar essa definição usando um teste de igualdade 
booleano. *)

Definition e_par_primo n :=
  if n =? 2 then true
  else false.

(* Além do fato de que propriedades não computáveis são, em geral, 
impossíveis de serem formuladas como computações booleanas, muitas 
propriedades computáveis também são mais fáceis de expressar usando Prop do 
que bool, uma vez que as definições de funções recursivas no Rocq estão 
sujeitas a restrições significativas. Por exemplo, o próximo capítulo mostra 
como definir a propriedade de que uma expressão regular corresponde a uma 
dada string usando Prop. Fazer o mesmo com bool equivaleria a escrever um 
algoritmo de correspondência de expressões regulares, o que seria mais 
complicado, mais difícil de entender e mais difícil de raciocinar a respeito 
do que uma definição simples (não algorítmica) dessa propriedade.

Por outro lado, um benefício colateral importante de declarar fatos usando 
booleanos é possibilitar certa automação de provas por meio da computação 
com termos do Rocq, uma técnica conhecida como prova por reflexão (proof by 
reflection). 

Considere a seguinte afirmação: *)

Example par_1000 : Par 1000.

(* A maneira mais direta de provar isso é fornecer o valor de k 
explicitamente. *)

Proof. unfold Par. exists 500. reflexivity. Qed.