Require Import LFPTBR.b_Inducao.a_Inducao.
Require Import LFPTBR.g_IndProp.a_IndProp.

(* IndPrinciples *)
(* Princípios de Indução *)

(* Toda vez que declaramos um novo tipo de dado indutivo (Inductive datatype), o Rocq gera 
automaticamente um princípio de indução para esse tipo. Esse princípio de indução é um 
teorema como qualquer outro: se t é definido indutivamente, o princípio de indução 
correspondente é chamado de t_ind. *)

(*********************************** Noções Básicas ***************************************)

(* Aqui está o princípio de indução para os números naturais: *)

Check nat_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n.

(* Em linguagem natural: Suponha que P seja uma propriedade dos números naturais (ou seja, 
P n é um Prop para todo n). Para mostrar que P n vale para todo n, basta mostrar que:
    - P vale para 0;
    - para qualquer n, se P vale para n, então P vale para S n.
    
A tática induction é um wrapper direto que, em sua essência, simplesmente executa apply 
t_ind. Para ver isso mais claramente, vamos experimentar usar diretamente apply nat_ind, em 
vez da tática induction, para realizar algumas demonstrações. Aqui, por exemplo, está uma 
demonstração alternativa de um teorema que vimos no capítulo Induction. *)

Theorem mul_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  - (* n = O *) reflexivity.
  - (* n = S n' *) simpl. intros n' IHn'. rewrite -> IHn'.
    reflexivity. Qed.

(* Esta demonstração é basicamente a mesma que a anterior, mas vale a pena observar algumas 
pequenas diferenças.

Primeiro, no passo de indução da demonstração (o caso S), precisamos fazer um pouco de 
organização manual (os intros) que a tática induction faz automaticamente.

Segundo, não introduzimos n no contexto antes de aplicar o nat_ind — a conclusão de nat_ind 
é uma fórmula quantificada, e o apply exige que essa conclusão corresponda exatamente ao 
formato do estado da meta, incluindo o quantificador. Por outro lado, a tática induction 
funciona tanto com uma variável no contexto quanto com uma variável quantificada na meta.

Terceiro, tivemos que fornecer manualmente o nome do princípio de indução com o apply, mas 
o induction descobre isso por conta própria.

Essas facilidades tornam o uso do induction mais agradável na prática do que aplicar 
princípios de indução como o nat_ind diretamente. No entanto, é importante perceber que, 
descontando esses pequenos detalhes de manipulação de contexto, aplicar o nat_ind é o que 
estamos realmente fazendo. *)

(* Exercício *)
(* Complete esta demonstração sem usar a tática induction. *)

Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros n' IHn'.
    rewrite IHn'. reflexivity.
Qed.

(* O Rocq gera princípios de indução para cada tipo de dado definido com Inductive, 
incluindo aqueles que não são recursivos. Embora, é claro, não precisemos da técnica de 
demonstração por indução para provar propriedades de tipos de dados não recursivos, a ideia 
de um princípio de indução ainda faz sentido para eles: ela fornece uma maneira de provar 
que uma propriedade é válida para todos os valores do tipo.

Esses princípios gerados seguem um padrão semelhante. Se definirmos um tipo t com os 
construtores c1 ... cn, o Rocq gera um teorema com este formato:

      t_ind : ∀ P : t → Prop,
                ... caso para c1 ... →
                ... caso para c2 ... → ...
                ... caso para cn ... →
                ∀ n : t, P n

O formato específico de cada caso depende dos argumentos do construtor correspondente. 

Antes de tentar escrever uma regra geral, vamos ver mais alguns exemplos. Primeiro, um 
exemplo em que os construtores não recebem argumentos: *)

Inductive time : Type :=
  | day
  | night.

Check time_ind :
  forall P : time -> Prop,
    P day ->
    P night ->
    forall t : time, P t.

(* Exercício *)
(* Escreva o princípio de indução que o Rocq gerará para o seguinte tipo de dados. Escreva 
sua resposta em um papel ou digite-a em um comentário e, em seguida, compare-a com o que o 
Rocq exibe. *)

Inductive rgb : Type :=
  | red
  | green
  | blue.

(* Check rgb_ind : 
  forall P : rgb -> Prop,
    P red ->
    P green ->
    P blue ->
    forall r : rgb, P r *)
Check rgb_ind. 

(* Aqui está outro exemplo, desta vez com um dos construtores recebendo alguns argumentos. *)

Inductive natlist : Type :=
  | nnil
  | ncons (n : nat) (l : natlist).

Check natlist_ind :
  forall P : natlist -> Prop,
    P nnil ->
    (forall (n : nat) (l : natlist),
        P l -> P (ncons n l)) ->
    forall l : natlist, P l.

(* Em geral, o princípio de indução gerado automaticamente para o tipo indutivo t é 
formado da seguinte forma: 
    - Cada construtor c gera um caso do princípio.
    - Se c não recebe argumentos, esse caso é:
            ''P vale para c''
    - Se c recebe argumentos x1:a1 ... xn:an, esse caso é:
            ''Para todo x1:a1 ... xn:an,
              se P vale para cada um dos argumentos do tipo t,
              então P vale para c x1 ... xn''

    Mas isso simplifica um pouco demais. Uma suposição sobre P valer para um argumento x do 
    tipo t ocorre, na verdade, imediatamente após a quantificação de x.

Por exemplo, suponha que tivéssemos escrito a definição de natlist um pouco diferente: *)

Inductive natlist' : Type :=
  | nnil'
  | nsnoc (l : natlist') (n : nat).

(* Agora, o caso do princípio de indução para nsnoc é um pouco diferente do caso anterior 
para ncons: *)

Check natlist'_ind :
  forall P : natlist' -> Prop,
    P nnil' ->
    (forall l : natlist', P l -> forall n : nat, P (nsnoc l n)) ->
    forall n : natlist', P n.

(* Exercício *)
(* Aqui está um tipo para árvores que contêm um valor booleano em cada folha e ramo. *)

Inductive booltree : Type :=
  | bt_empty
  | bt_leaf (b : bool)
  | bt_branch (b : bool) (t1 t2 : booltree).

(* Qual é o princípio de indução para booltree? É claro que você poderia perguntar ao Rocq, 
mas tente não fazer isso. Em vez disso, escreva-o você mesmo no papel. Em seguida, olhe 
para a definição de booltree_ind_type abaixo. Ela tem três partes faltando, que são 
fornecidas pelas definições entre aqui e lá. Preencha essas definições com base no que você 
escreveu no papel. *)

(* Check booltree_ind :
   forall P : booltree -> Prop,
   P bt_empty ->
   (forall b : bool, P (bt_leaf b)) ->
   (forall (b : bool)(t1 : booltree), 
   P t1 -> forall t2 : booltree, P t2 -> P (bt_branch b t1 t2)) ->
   forall b : booltree, P b. *)


Definition booltree_property_type : Type := booltree -> Prop.

Definition base_case (P : booltree_property_type) : Prop :=
  P bt_empty.

Definition leaf_case (P : booltree_property_type) : Prop :=
  forall b : bool, P (bt_leaf b).

Definition branch_case (P : booltree_property_type) : Prop :=
  forall (b : bool)(t1 : booltree), P t1 -> forall t2 : booltree, P t2 ->
  P (bt_branch b t1 t2).

Definition booltree_ind_type :=
  forall (P : booltree_property_type),
    base_case P ->
    leaf_case P ->
    branch_case P ->
    forall (b : booltree), P b.

(* Agora verifique a correção das suas respostas provando o seguinte teorema. Se você 
tiver acertado, poderá concluir a prova com apenas uma tática: exact booltree_ind. Isso 
funcionará porque o princípio de indução gerado automaticamente booltree_ind tem o mesmo 
tipo que você acabou de definir. *)

Theorem booltree_ind_type_correct : booltree_ind_type.
Proof.
  exact booltree_ind.
Qed.

(* Aqui está um princípio de indução para um tipo de brinquedo (toy type): 
     ∀ P : Toy → Prop,
      (∀ b : bool, P (con1 b)) →
      (∀ (n : nat) (t : Toy), P t → P (con2 n t)) →
     ∀ t : Toy, P t
     
Dê uma definição indutiva de Toy tal que o princípio de indução que o Rocq gera seja o 
fornecido acima: *)

Inductive Toy : Type :=
  | con1 (b : bool)
  | con2 (n : nat) (t : Toy).

(* Mostre que a sua definição está correta provando o seguinte teorema. Você deve ser 
capaz de instanciar f e g com os seus dois construtores e, em seguida, finalizar a prova 
imediatamente com exact Toy_ind. Assim como no exercício anterior, isso funcionará porque 
o princípio de indução gerado automaticamente Toy_ind terá o mesmo tipo. *)

Theorem Toy_correct : exists f g,
  forall P : Toy -> Prop,
    (forall b : bool, P (f b)) ->
    (forall (n : nat) (t : Toy), P t -> P (g n t)) ->
    forall t : Toy, P t.
Proof.
  exists con1, con2.
  exact Toy_ind.
Qed.

(*************************************** Polimorfismo ************************************)

(* E quanto aos tipos de dados polimórficos? A definição indutiva de listas polimórficas:
          Inductive list (X:Type) : Type :=
          | nil : list X
          | cons : X → list X → list X. 
          
é muito semelhante à de natlist. A principal diferença é que, aqui, toda a definição é 
parametrizada por um tipo X: ou seja, estamos definindo uma família de tipos indutivos 
list X, um para cada X. (Note que, onde quer que list apareça no corpo da declaração, ela 
é sempre aplicada ao parâmetro X.)

O princípio de indução é, da mesma forma, parametrizado por X:
          list_ind :
            ∀ (X : Type) (P : list X → Prop),
               P [] →
               (∀ (x : X) (l : list X), P l → P (x :: l)) →
               ∀ l : list X, P l
               
Note que todo o princípio de indução é parametrizado por X. Ou seja, list_ind pode ser 
pensado como uma função polimórfica que, quando aplicada a um tipo X, nos devolve um 
princípio de indução especializado para o tipo list X. *)

(* Exercício *)
(* Escreva o princípio de indução que o Rocq gerará para o seguinte tipo de dado. Compare 
sua resposta com o que o Rocq exibe. *)

Inductive tree (X:Type) : Type :=
  | leaf (x : X)
  | node (t1 t2 : tree X).

(* Check tree_ind: 
   forall (X : Type ) (P : tree X -> Prop),
    (forall x : X, P (leaf X x)) ->
    (forall t1 : tree X, P t1 ->
    forall t2 : tree X, P t2 -> 
    P (node X t1 t2)) ->
    forall t : tree X, P t. *)

Check tree_ind.

(* Encontre uma definição indutiva que dê origem ao seguinte princípio de indução: 
       mytype_ind :
        ∀ (X : Type) (P : mytype X → Prop),
            (∀ x : X, P (constr1 X x)) →
            (∀ n : nat, P (constr2 X n)) →
            (∀ m : mytype X, P m →
               ∀ n : nat, P (constr3 X m n)) →
            ∀ m : mytype X, P m
*)

Inductive mytype (X:Type) : Type :=
  | constr1 (x : X)
  | constr2 (n : nat)
  | constr3 (m : mytype X) (n : nat).

(* Encontre uma definição indutiva que dê origem ao seguinte princípio de indução: 
      foo_ind :
        ∀ (X Y : Type) (P : foo X Y → Prop),
             (∀ x : X, P (bar X Y x)) →
             (∀ y : Y, P (baz X Y y)) →
             (∀ f1 : nat → foo X Y,
               (∀ n : nat, P (f1 n)) → P (quux X Y f1)) →
             ∀ f2 : foo X Y, P f2
*)

Inductive foo (X Y : Type) : Type :=
  | bar (x : X)
  | baz (y : Y)
  | quux (f1 : nat -> foo X Y).

(* Considere a seguinte definição indutiva: *)
Inductive foo' (X:Type) : Type :=
  | C1 (l : list X) (f : foo' X)
  | C2.

(* Que princípio de indução o Coq irá gerar para foo'? (Preencha as lacunas, 
em seguida verifique sua resposta com o Coq.)

      foo'_ind :
        ∀ (X : Type) (P : foo' X → Prop),
              (∀ (l : list X) (f : foo' X),
                   (1) _______________________ →
                    (2) _______________________   ) →
            (3) ___________________________________________ →
             ∀ f : foo' X, (4) ________________________ 
             
(1) P f 
(2) P (C1 X l f)
(3) P (C2 X)
(4) P f *)

(************************** Hipóteses de Indução ****************************)

(* Onde a frase ''hipótese de indução'' se encaixa nesta história?

O princípio de indução para números:
      ∀ P : nat → Prop,
         P 0 →
         (∀ n : nat, P n → P (S n)) →
         ∀ n : nat, P n

É uma afirmação genérica que vale para todas as proposições P (ou, mais 
rigorosamente falando, para todas as famílias de proposições P indexadas por 
um número n). Cada vez que usamos este princípio, estamos escolhendo P como 
uma expressão particular de tipo nat → Prop.

Podemos tornar as provas por indução mais explícitas dando a esta expressão 
um nome. Por exemplo, em vez de declarar o teorema mul_0_r como 
''∀ n, n × 0 = 0'', podemos escrevê-lo como ''∀ n, P_m0r n'', onde P_m0r é 
definido como... *)

Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.

(* ... ou de forma equivalente: *)

Definition P_m0r' : nat -> Prop :=
  fun n => n * 0 = 0.

(* Agora fica mais fácil ver onde P_m0r aparece na prova. *)

Theorem mul_0_r'' : forall n:nat,
  P_m0r n.
Proof.
  apply nat_ind.
  - (* n = O *) reflexivity.
  - (* n = S n' *)
    (* Observe o estado da prova neste ponto! *)
    intros n IHn.
    unfold P_m0r in IHn. unfold P_m0r. simpl. apply IHn. Qed.

(* Esta etapa extra de dar nome não é algo que fazemos em demonstrações 
normais, mas é útil fazê-la explicitamente para um ou dois exemplos, porque 
nos permite ver exatamente qual é a hipótese de indução. Se provarmos 
∀ n, P_m0r n por indução em n (usando induction ou apply nat_ind), vemos que 
a primeira submeta requer que provemos P_m0r 0 ('P vale para zero'), enquanto 
a segunda submeta requer que provemos ∀ n', P_m0r n' → P_m0r (S n') (ou seja, 
'P vale para S n' se vale para n'' ou, de forma mais elegante, 'P é 
preservado por S'). A hipótese de indução é a premissa desta última implicação 
— a suposição de que P vale para n', a qual temos permissão para usar ao 
provar que P vale para S n' *)

(********************** Mais sobre a tática de indução *********************)

(* A tática de indução na verdade faz um trabalho de controle (bookkeeping) 
de baixo nível ainda maior para nós do que o discutido acima. 

Lembre-se da afirmação informal do princípio de indução para números naturais:
  - Se P n é alguma proposição envolvendo um número natural n, e queremos 
    mostrar que P vale para todos os números n, podemos raciocinar assim:
      - mostre que P 0 vale
      - mostre que, se P n' vale, então P (S n') também vale
      - conclua que P n vale para todo n.
Portanto, quando começamos uma demonstração com intros n e depois induction n, 
estamos primeiro dizendo ao Rocq para considerar um n particular 
(introduzindo-o no contexto) e depois dizendo a ele para provar algo sobre 
todos os números (usando a indução). 

O que o Rocq realmente faz nessa situação, internamente, é 're-generalizar' a 
variável sobre a qual realizamos a indução. Por exemplo, em nossa 
demonstração original de que a adição é associativa. *)

Theorem add_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* ...primeiro introduzimos todas as 3 variáveis no contexto, o que 
    equivale a dizer 'Considere n, m e p arbitrários... *)
  intros n m p.
  (* ...Agora usamos a tática de indução para provar P n (ou seja, 
   n + (m + p) = (n + m) + p) para todos os n, e consequentemente também para 
   o n particular que está no contexto no momento. *)
  induction n as [| n'].
  - (* n = O *) reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity. Qed.
    
(* Também funciona aplicar a indução a uma variável que está quantificada no 
objetivo. *) 

Theorem add_comm' : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [| n'].
  - (* n = O *) intros m. rewrite -> add_0_r. reflexivity.
  - (* n = S n' *) intros m. simpl. rewrite -> IHn'.
    rewrite <- plus_n_Sm. reflexivity. Qed.

(* Note que induction n deixa m ainda quantificado (bound) no objetivo — ou 
seja, o que estamos provando indutivamente é uma afirmação que começa com ∀ m. 

Se fizermos indução em uma variável que está quantificada no objetivo após 
alguns outros quantificadores, a tática de indução introduzirá automaticamente 
as variáveis quantificadas por esses quantificadores no contexto. *)

Theorem add_comm'' : forall n m : nat,
  n + m = m + n.
Proof.
  (* Vamos fazer a indução em m desta vez, em vez de n... *)
  induction m as [| m']. (* n já está introduzido no contexto *)
  - (* m = O *) simpl. rewrite -> add_0_r. reflexivity.
  - (* m = S m' *) simpl. rewrite <- IHm'.
    rewrite <- plus_n_Sm. reflexivity. Qed.

(* Exercício *)
(* Reescreva tanto add_assoc' quanto add_comm' e suas demonstrações no mesmo 
estilo de mul_0_r'' acima — ou seja, para cada teorema, forneça uma 
Definition explícita da proposição que está sendo provada por indução, e 
enuncie o teorema e a demonstração em termos dessa proposição definida. *)

Definition P_assoc (n m p : nat) : Prop :=
  n + (m + p) = (n + m) + p.

Theorem add_assoc'' : forall (n m p : nat),
  P_assoc n m p.
Proof.
  intros n m p.
  apply nat_ind.
  - (* p = 0*)
    unfold P_assoc. rewrite add_0_r. rewrite add_0_r. reflexivity.
  - (* p = S n0 *)
    intros n0 IH. unfold P_assoc in IH. unfold P_assoc.
    rewrite <- plus_n_Sm. rewrite <- plus_n_Sm. rewrite IH.
    rewrite <- plus_n_Sm. reflexivity.
Qed.

Definition P_comm (n m : nat) : Prop :=
  n + m = m + n.

Theorem add_comm''' : forall (n m : nat),
  P_comm n m.
Proof.
  intros n m.
  apply nat_ind.
  - (* m = 0 *)
    unfold P_comm. simpl. rewrite add_0_r. reflexivity.
  - (* m = S n0 *)
    intros n0 IH. unfold P_comm in IH. unfold P_comm.
    simpl. rewrite <- IH. rewrite plus_n_Sm. reflexivity.
Qed.

(****************** Princípios de Indução para Proposições *****************)

(* Definições indutivas de proposições também fazem com que o Rocq gere 
princípios de indução. Por exemplo, relembre nossa proposição ev de IndProp: *)

Print ev.
(* ===>

  Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS : forall n : nat, ev n -> ev (S (S n)))

*)

Check ev_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, ev n -> P n -> P (S (S n))) ->
    forall n : nat, ev n -> P n.

(* Em português, ev_ind afirma: Suponha que P é uma propriedade de números 
naturais. Para mostrar que P n vale sempre que n é par, basta mostrar:
  
  - P vale para 0,
  - para qualquer n, se n é par e P vale para n, então P vale para S (S n).

Como esperado, podemos aplicar ev_ind diretamente em vez de usar indução. Por 
exemplo, podemos usá-lo para mostrar que ev' (a definição alternativa um pouco 
incômoda da paridade que vimos em um exercício do capítulo IndProp) é 
equivalente à definição indutiva mais limpa ev: *)

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Theorem ev_ev' : forall n, ev n -> ev' n.
Proof.
  apply ev_ind.
  - (* ev_0 *)
    apply ev'_0.
  - (* ev_SS *)
    intros m Hm IH.
    apply (ev'_sum 2 m).
    + apply ev'_2.
    + apply IH.
Qed.

(* A forma exata de uma definição indutiva pode afetar o princípio de indução 
que o Rocq gera. *)

Inductive le1 : nat -> nat -> Prop :=
  | le1_n : forall n, le1 n n
  | le1_S : forall n m, (le1 n m) -> (le1 n (S m)).

Notation "m <=1 n" := (le1 m n) (at level 70).

(* Essa definição pode ser um pouco simplificada observando que o argumento 
esquerdo n é o mesmo em toda a definição, de modo que podemos torná-lo um 
'parâmetro geral' para toda a definição, em vez de um argumento para cada 
construtor. *)

Inductive le2 (n:nat) : nat -> Prop :=
  | le2_n : le2 n n
  | le2_S m (H : le2 n m) : le2 n (S m).

Notation "m <=2 n" := (le2 m n) (at level 70).

(* A segunda é melhor, mesmo parecendo menos simétrica. Por quê? Porque ela nos 
dá um princípio de indução mais simples. *)

Check le1_ind :
  forall P : nat -> nat -> Prop,
    (forall n : nat, P n n) ->
    (forall n m : nat, n <=1 m -> P n m -> P n (S m)) ->
    forall n n0 : nat, n <=1 n0 -> P n n0.

Check le2_ind :
  forall (n : nat) (P : nat -> Prop),
    P n ->
    (forall m : nat, n <=2 m -> P m -> P (S m)) ->
    forall n0 : nat, n <=2 n0 -> P n0.

(****** Outra Forma de Princípios de Indução sobre Proposições (Opcional) ******)

(* O princípio de indução que o Rocq gerou para ev era parametrizado por um 
número natural n. Ele poderia ter sido adicionalmente parametrizado pela 
evidência de que n é par, o que teria levado a este princípio de indução: 

    ∀ P : (∀ n : nat, ev'' n → Prop),
      P O ev_0 →
      (∀ (m : nat) (E : ev'' m),
        P m E → P (S (S m)) (ev_SS m E)) →
      ∀ (n : nat) (E : ev'' n), P n E

... porque:

  - Como ev é indexado por um número n (cada objeto de evidência E de ev é uma 
    peça de evidência de que algum número específico n é par), a proposição P 
    é parametrizada tanto por n quanto por E — ou seja, o princípio de indução 
    pode ser usado para provar asserções envolvendo tanto um número par quanto 
    a evidência de que ele é par.
    
  - Como há duas maneiras de fornecer evidência de paridade (o predicado ev 
    possui dois construtores), a aplicação do princípio de indução gera duas 
    submetas:
      - Devemos provar que P vale para O e ev_0.
      - Devemos provar que, sempre que m for um número par e E for uma 
        evidência de sua paridade, se P vale para m e E, então ele também vale 
        para S (S m) e ev_SS m E.
        
  - Se essas submetas puderem ser provadas, então o princípio de indução nos diz 
    que P é verdadeiro para todos os números pares n e evidências E de sua 
    paridade.
    
Isso oferece mais flexibilidade do que normalmente precisamos ou queremos: nos 
dá uma maneira de provar asserções lógicas onde a asserção envolve propriedades 
de alguma evidência de paridade, enquanto tudo o que realmente nos importa é 
provar propriedades de números que são pares — estamos interessados em asserções 
sobre números, e não sobre evidências. Portanto, seria mais conveniente ter um 
princípio de indução para provar proposições P que são parametrizadas apenas 
por n e cuja conclusão estabelece P para todos os números pares n:       

    ∀ P : nat → Prop,
     ... →
    ∀ n : nat,
      even n → P n

É por isso que o Rocq realmente gera o princípio de indução ev_ind que vimos 
antes. *)

(******************* Provas Formais vs. Informais por Indução ******************)

(* Pergunta: Qual é a relação entre uma prova formal de uma proposição P e uma 
prova informal da mesma proposição P

Resposta: Esta última deve ensinar ao leitor tudo o que ele precisaria entender 
para ser capaz de produzir a primeira.

Pergunta: Quanto de detalhe isso requer?

Infelizmente, não há uma única resposta certa; em vez disso, há uma gama de 
escolhas.

Em uma das pontas do espectro, podemos essencialmente dar ao leitor a prova 
formal inteira (ou seja, a prova ''informal'' equivalerá apenas a transcrever a 
formal para palavras). Isso pode dar ao leitor a capacidade de reproduzir a 
formal por si mesmo, mas provavelmente não lhe ensina muita coisa.

Na outra ponta do espectro, podemos dizer: ''O teorema é verdadeiro e você pode 
descobrir o porquê por conta própria se pensar sobre isso com afinco suficiente.'' 
Essa também não é uma boa estratégia de ensino, porque muitas vezes escrever a 
prova exige um ou mais insights significativos sobre a coisa que estamos provando, 
e a maioria dos leitores desistirá antes de redescobrir todos os mesmos insights 
que nós.

No meio está o justo meio-termo (golden mean) — uma prova que inclui todos os 
insights essenciais (poupando o leitor do trabalho árduo pelo qual passamos para 
encontrar a prova em primeiro lugar) além de sugestões de alto nível para as 
partes mais rotineiras (evitando que o leitor gaste muito tempo reconstruindo-as — 
por exemplo, o que a IH diz e o que deve ser mostrado em cada caso de uma prova 
por indução), mas não com tantos detalhes a ponto de obscurecer as ideias 
principais.

Como passamos boa parte deste capítulo olhando ''sob o capô'' de provas formais 
por indução, agora é um bom momento para falar um pouco sobre provas informais 
por indução.

No mundo real da comunicação matemática, as provas escritas variam desde 
extremamente longas e pedantes até extremamente breves e telegráficas. Embora o 
ideal fique em algum lugar no meio, enquanto se está acostumando com o estilo, é 
melhor começar na ponta pedante. Além disso, durante a fase de aprendizado, 
provavelmente é útil ter um padrão claro para comparar. Com isso em mente, 
oferecemos dois modelos — um para provas por indução sobre dados (ou seja, onde a 
coisa sobre a qual estamos fazendo indução vive em Type) e um para provas por 
indução sobre evidências (ou seja, onde a coisa definida indutivamente vive em 
Prop).*)

(*** Indução sobre um Conjunto Definido Indutivamente ***)

(* Modelo:
  
  - Teorema: <Proposição quantificada universalmente da forma ''Para todo n:S, 
    P(n),'' em que S é um conjunto definido indutivamente.>

  Prova: Por indução em n.
  <um caso para cada construtor c de S...>
    - Suponha n = c a1 ... ak, onde <...e aqui enunciamos a IH para cada um dos 
    a's que possui o tipo S, se houver>. Devemos mostrar <...e aqui reescrevemos 
    P(c a1 ... ak)>.
    
    <continue e prove P(n) para finalizar o caso...>
    
    - <Os demais casos de forma análoga...> ☐
    
Exemplo:
  - Teorema: Para todos os conjuntos X, listas l : list X e números n, se 
    length l = n, então index (S n) l = None. 
    
    Prova: Por indução em l.
      - Suponha l = []. Devemos mostrar, para todos os números n, que, se 
        length [] = n, então (S n) [] = None. 
        Isso decorre imediatamente da definição de index.
      
      - Suponha l = x :: l' para alguns x e l', onde length l' = n implica 
        (S n') l' = None, para qualquer número n'. Devemos mostrar, para todo n, 
        que, se length (x::l') = n, então index (S n) (x::l') = None.
        Seja n um número com length l = n. Como
            length l = length (x::l') = S (length l'),
        basta mostrar que
            index (S (length l')) l' = None.
        Mas isso decorre diretamente da hipótese de indução, escolhendo n' como 
        sendo length l'. ☐ *)

(*** Indução sobre uma Proposição Definida Indutivamente ***)

(* Como objetos de prova definidos indutivamente são frequentemente chamados de 
''árvores de derivação'', esta forma de prova também é conhecida como indução em 
derivações.

Modelo:
  
  - Teorema: <Proposição da forma ''Q → P'', em que Q é alguma proposição definida 
    indutivamente (mais geralmente, ''Para todo x y z, Q x y z → P x y z'')>
    
    Prova: Por indução em uma derivação de Q. <Ou, mais geralmente, ''Suponha que 
    nos sejam dados x, y e z. Mostramos que Q x y z implica P x y z, por indução 
    em uma derivação de Q x y z''...>
    
    <um caso para cada construtor c de Q...>
      - Suponha que a regra final usada para mostrar Q seja c. Então <...e aqui 
        enunciamos os tipos de todos os a's junto com quaisquer igualdades que 
        decorrem da definição do construtor e a IH para cada um dos a's que 
        possui o tipo Q, se houver alguma>. Devemos mostrar <...e aqui 
        reescrevemos P>
        
        <continue e prove P para finalizar o caso...>

      - <Os demais casos de forma análoga...> ☐
        
Exemplo:
  -Teorema: A relação ≤ é transitiva — ou seja, para todos os números n, m e o, 
    se n ≤ m e m ≤ o, então n ≤ o.
    
  Prova: Por indução em uma derivação de m ≤ o.
    - Suponha que a regra final usada para mostrar m ≤ o seja le_n. 
      Então m = o e devemos mostrar que n ≤ m, o que é imediato por hipótese.
      
    - Suponha que a regra final usada para mostrar m ≤ o seja le_S. Então o = S o' 
      para algum o' com m ≤ o'. Devemos mostrar que n ≤ S o'. Pela hipótese de 
      indução, n ≤ o'. 
      Mas então, por le_S,  n ≤ S o'. ☐ *)

(****************** Objetos de Prova Explícitos para Indução ********************)

(* Embora as provas baseadas em táticas sejam normalmente muito mais fáceis de 
manusear, a capacidade de escrever um termo de prova diretamente às vezes é muito 
útil, particularmente quando queremos que o Rocq faça algo um pouco fora do padrão.

Lembre-se novamente do princípio de indução sobre os naturais que o Rocq gera 
automaticamente para nós a partir da declaração Inductive para nat. *)

Check nat_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n.

(* Não há nada de mágico neste lema de indução: ele é apenas mais um lema do Rocq 
que requer uma prova. O Rocq gera a prova automaticamente também... *)

Print nat_ind.

(* Podemos reescrever isso de forma mais limpa da seguinte maneira: *)

Fixpoint build_proof
         (P : nat -> Prop)
         (evPO : P 0)
         (evPS : forall n : nat, P n -> P (S n))
         (n : nat) : P n :=
  match n with
  | 0 => evPO
  | S k => evPS k (build_proof P evPO evPS k)
  end.

Definition nat_ind_tidy := build_proof.

(* Podemos ler build_proof da seguinte forma: Suponha que temos a evidência evPO 
de que P vale para 0, e a evidência evPS de que ∀ n:nat, P n → P (S n). Então 
podemos provar que P vale para um nat n arbitrário usando a função recursiva 
build_proof, que faz correspondência de padrões (pattern matching) em n:

  - Se n for 0, build_proof retorna evPO para mostrar que P n vale.
  - Se n for S k, build_proof aplica-se recursivamente a k para obter a evidência 
    de que P k vale; então ela aplica evPS nessa evidência para mostrar que 
    P (S n) vale.
    
A função recursiva build_proof, portanto, faz correspondência de padrões contra n, 
fazendo recursão até chegar em 0, e construindo uma prova à medida que retorna.

O nat_ind real que o Rocq gera usa uma função recursiva F definida com fix em vez de 
Fixpoint.

Podemos usar nosso próprio princípio de indução codificado à mão no lugar do 
princípio de indução gerado automaticamente com a variante 
induction ... using ... da tática de indução usual. *)

Theorem mul_0_r''' : forall n:nat,
  n * 0 = 0.
Proof.
  induction n as [ | n' IHn'] using nat_ind_tidy.
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

(* Podemos adaptar essa abordagem de prova de nat_ind para ajudar a provar 
princípios de indução não-padrão também. Como exemplo motivador, suponha que 
queiramos provar o seguinte lema, relacionando diretamente o predicado ev que 
definimos em IndProp com a função even definida em Basics. *)

Lemma even_ev : forall n: nat, Nat.even n = true -> ev n.
Proof.
  induction n; intros.
  - apply ev_0.
  - destruct n.
    + simpl in H. inversion H.
    + simpl in H.
      apply ev_SS.
Abort.

(* Tentativas de provar isso por indução padrão sobre n falham no caso para 
S (S n), porque a hipótese de indução só nos diz algo sobre S n, o que é inútil. 
Há várias maneiras de contornar (hack around) esse problema; por exemplo, podemos 
usar indução ordinária sobre n para provar isso (tente!): *)

Lemma even_ev' : forall n : nat, 
    (Nat.even n = true -> ev n) /\ (Nat.even (S n) = true -> ev (S n)).
Proof.
  induction n; intros.
  - split.
    + intros. apply ev_0.
    + intros H. inversion H.
  - split.
    + intros H. destruct IHn as [H1 H2].
      apply H2 in H. apply H.
    + intros H. destruct IHn as [H1 H2].
      apply ev_SS. apply H1. apply H.
Qed.
      
(* Mas podemos fazer uma prova muito melhor definindo e provando um princípio de 
indução não-padrão que avança ''de dois em dois'': *)

Definition nat_ind2 :
  forall (P : nat -> Prop),
  P 0 ->
  P 1 ->
  (forall n : nat, P n -> P (S(S n))) ->
  forall n : nat , P n :=
    fun P => fun P0 => fun P1 => fun PSS =>
      fix f (n:nat) := match n with
                         0 => P0
                       | 1 => P1
                       | S (S n') => PSS n' (f n')
                       end.
                      
(* Uma vez que você pega o jeito, é perfeitamente simples fornecer um termo de 
prova explícito para princípios de indução como este. Provar isso como um lema 
usando táticas é muito menos intuitivo. A variante da tática induction ... using 
oferece uma maneira conveniente de utilizar um princípio de indução não-padrão 
como este. *)

Lemma even_ev : forall n, Nat.even n = true -> ev n.
Proof.
  intros.
  induction n as [ | |n'] using nat_ind2.
  - apply ev_0.
  - simpl in H.
    inversion H.
  - simpl in H.
    apply ev_SS.
    apply IHn'.
    apply H.
Qed.

(* Exercício *)
(* E se quiséssemos definir árvores binárias da seguinte forma, usando um 
construtor que agrupa os filhos e o valor em um nó em uma tupla? *)

Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Inductive t_tree (X : Type) : Type :=
| t_leaf
| t_branch : (t_tree X * X * t_tree X) -> t_tree X.

Arguments t_leaf {X}.
Arguments t_branch {X}.

(* Infelizmente, o princípio de indução gerado automaticamente não é tão forte 
quanto precisamos. Ele não introduz hipóteses de indução para as subárvores *)

Check t_tree_ind.

(* Isso nos causará problemas se quisermos provar algo por indução, tal como o 
fato de que reflect é uma involução. *)

Fixpoint reflect {X : Type} (t : t_tree X) : t_tree X :=
  match t with
  | t_leaf => t_leaf
  | t_branch (l, v, r) => t_branch (reflect r, v, reflect l)
  end.

Theorem reflect_involution : forall (X : Type) (t : t_tree X),
    reflect (reflect t) = t.
Proof.
  intros X t. induction t.
  - reflexivity.
  - destruct p as [[l v] r]. simpl. Abort.

(* Ficamos presos, porque não temos hipótese de indução para l ou r. Portanto, 
precisamos definir nosso próprio princípio de indução personalizado e usá-lo 
para concluir a prova.

Primeiro, defina o tipo do princípio de indução que você deseja usar. Há muitas 
respostas possíveis. Lembre-se de que você pode usar match como parte da 
definição. *)

Definition better_t_tree_ind_type : Prop :=
  forall (X : Type) (P : t_tree X -> Prop),
  P t_leaf -> 
  (forall p : t_tree X * X * t_tree X, 
    (match p with 
      | (l, v , r) => P l /\ P r
      end) -> P (t_branch p)) ->
  forall t : t_tree X, P t.

(* Segundo, defina o princípio de indução fornecendo um termo desse tipo. Use os 
exemplos sobre nat, acima, como modelo. *)

Definition better_t_tree_ind : better_t_tree_ind_type :=
        fun X => fun P => fun Pleaf => fun Pbranch =>
          fix f (p : t_tree X) := 
                  match p with
                   |  t_leaf => Pleaf
                   | t_branch p' => Pbranch  p' (match p' with
                                                 | (l, v, r) => conj (f l)(f r)
                                                 end)
                                              
                     end.

(* Finalmente, prove o teorema. Se o comando induction...using der um erro sobre 
''Cannot recognize an induction scheme'', não se preocupe. A tática induction é 
bastante exigente quanto à forma (estrutura) do teorema que você passa para ela, 
mas ela não fornece muitas informações para ajudar a depurar o que está errado com 
essa forma. Em vez disso, você pode usar apply, como vimos no início deste arquivo. *)

Theorem reflect_involution : forall (X : Type) (t : t_tree X),
    reflect (reflect t) = t.
Proof.
  intros X t.
  apply (better_t_tree_ind X (fun t => reflect (reflect t) = t)).
  - reflexivity.
  - intros p H. 
    destruct p as [[l v] r]. destruct H as [H1 H2].
    simpl. rewrite H1, H2. reflexivity.
Qed.