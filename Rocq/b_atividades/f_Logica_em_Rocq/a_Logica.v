(* LÓGICA *)
(* LÓGICA EM ROCQ*)

(* Agora já vimos muitos exemplos de afirmações factuais (ou seja, 
proposições) e maneiras de apresentar evidências de sua verdade (provas). 
Em particular, trabalhamos extensivamente com proposições de igualdade 
(e1 ​= e2​), implicações (P → Q) e proposições quantificadas (∀x, P). 
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
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.

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
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.

(* Exercício *)
Lemma mult_e_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.

Proof.
  intros [| n'].
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
como  ∀ Q, P → Q. Na verdade, o Rocq faz uma escolha equivalente, mas 
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

(* Escreva uma prova informal da proposição ∀ P : Prop, ~(P ∧ ¬P).

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