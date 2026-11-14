(* Curry-Howard *)

(* Um Desenvolvimento Formal da Correspondência de Curry-Howard *)

(* Em i_Correspondencia_de_Curry_Howard, aprendemos que as táticas do Rocq constroem objetos 
de prova: programas que manipulam evidências na linguagem de programação do Rocq, a Gallina. 
Cada passo de tática corresponde à construção de um pedaço de um programa, e a prova 
concluída é um termo totalmente construído cujo tipo expressa a afirmação que está sendo 
provada. Nesse sentido, provar um teorema não é apenas uma questão de raciocínio lógico — é 
também o ato de escrever um programa.

Essa perspectiva sugere uma conexão mais profunda. A prova de uma proposição pode ser 
compreendida como um programa que transforma evidências de suas premissas em evidências de 
sua conclusão. Da mesma forma, uma função transforma entradas em saídas. Desse ponto de vista, 
os programas podem ser vistos como provas, e os tipos dos programas como proposições. Essa 
relação entre programas e provas, e entre tipos e proposições, é a essência da 
correspondência de Curry–Howard.

Neste capítulo, tornamos essa correspondência precisa. Em vez de depender da lógica e do 
sistema de tipos embutidos do Rocq, definimos nosso próprio sistema de provas para a lógica e 
nosso próprio sistema de tipos para programas dentro do Rocq. Em seguida, provamos que, 
sempre que um programa é bem-tipado, seu tipo pode ser traduzido em uma proposição que é 
provável no sistema de provas correspondente. Em outras palavras, derivações de tipagem 
podem ser transformadas sistematicamente em provas lógicas. Por outro lado, também 
mostraremos que, sempre que uma proposição é provável, existe um programa bem-tipado cujo 
tipo corresponde a essa proposição. Assim, programas e provas correspondem-se em ambas as 
direções. O próprio programa serve como um objeto de prova, assim como no Rocq, mas agora a 
conexão é tornada explícita e formal.

Por que essa correspondência é tão empolgante? Ela mostra que a lógica e a programação não 
são meramente análogas; em vez disso, elas são fundamentalmente o mesmo tipo de estrutura 
vista de duas perspectivas diferentes. Conectivos lógicos correspondem a construções de 
programação, e provas correspondem a programas executáveis. Como resultado, escrever um 
programa correto torna-se uma forma de provar um teorema, e provar um teorema torna-se uma 
maneira de construir um programa. Essa unificação ajuda a explicar por que sistemas como o 
Rocq funcionam da maneira que funcionam, e ela forma a fundação para ideias modernas em 
linguagens de programação e verificação formal.

Nota histórica: Haskell B. Curry descobriu essa correspondência na década de 1930 em seu 
trabalho sobre lógica combinatória. William A. Howard mais tarde a adaptou para outro 
sistema lógico, o cálculo de sequentes, em 1969, e estendeu a analogia para mostrar que a 
computação corresponde à simplificação de provas. Construindo sobre essa conexão, Per 
Martin-Löf desenvolveu a teoria dos tipos construtiva (sobre a qual o próprio Rocq é baseado) 
na década de 1970. A apresentação neste capítulo segue [Sørensen e Urzyczyn 2006]. *)

From Stdlib Require Import List String.
Import ListNotations.

(* Primeiramente, desenvolveremos a correspondência em um cenário que foca na implicação. 
Posteriormente, adicionaremos a conjunção e a disjunção. *)

(**************************************** Lógica ******************************************)

(* Até agora temos feito lógica com o Rocq — isto é, com suas definições de conectivos 
lógicos como conjunção e disjunção, e com suas regras sobre como as provas podem ser 
formadas. Mas, para tornar a correspondência precisa, precisamos fazer lógica embutida no 
Rocq — ou seja, definir a sintaxe de proposições lógicas com um tipo indutivo, e definir as 
regras de prova com uma proposição definida indutivamente. 

A lógica formalizada aqui é conhecida como lógica construtiva proposicional. Ela é 
proposicional porque não contém quantificadores. Ela é construtiva pelas mesmas razões que 
estudamos em Lógica: ela não inclui o princípio do terceiro excluído (ou um axioma 
equivalente). *)

(*** Proposições ***)

(* Comecemos modelando as proposições.
    - Um átomo é uma proposição atômica, muito semelhante 
      a P em P : Prop, como estamos acostumados no Rocq. As proposições atômicas recebem nomes 
      usando strings do Rocq.

    - Uma implicação é a usual P → Q.
    
    - A proposição contraditória é chamada de false. *)

Inductive proposition :=
  | atom (id : string)
  | implies (p q : proposition)
  | false.

(* A partir desse ponto de partida, podemos definir a negação e a verdade em termos de 
outras proposições. *)

Definition not (p : proposition) : proposition :=
  implies p false.

Definition true : proposition :=
  implies false false.

(* Aqui estão alguns exemplos de proposições. *)

Definition ex_P :=
  (* P -> P *)
  implies (atom "P") (atom "P").

Definition ex_PQ :=
  (* P -> Q -> P *)
  implies (atom "P") (implies (atom "Q") (atom "P")).

Definition ex_PQR :=
  (* (P -> Q -> R) -> (P -> Q) -> P -> R *)
  implies
    (implies (atom "P") (implies (atom "Q") (atom "R")))
    (implies (implies (atom "P") (atom "Q")) (implies (atom "P") (atom "R"))).

(*** Provas ***)

(* O que é uma prova? O que torna uma prova correta ou incorreta? No estudo da lógica formal, 
um sistema de provas é uma coleção de axiomas e regras de inferência que descrevem como 
formar provas corretas. Aqui apresentamos um sistema de provas conhecido como dedução 
natural. Ele se baseia em uma relação de provabilidade, que caracteriza quando uma 
proposição é provável a partir de um conjunto de premissas.

A relação de provabilidade é escrita como A ⊢ p, onde p é uma proposição, A é um conjunto 
de proposições (as premissas), e o símbolo de torniquete ⊢ é pronunciado como 'prova'. Ele
é definido com estas regras de inferência, nas quais escrevemos A, p para significar a 
união de A e {p}:

              	------------- (axiom)  
                  A, p ⊢ p	

                  A, p ⊢ q	
               ---------------- (implies intro)  
                 A ⊢ p -> q	

                A ⊢ p -> q   A ⊢ p	
              ----------------------- (implies elim)  
                      A ⊢ q	

                    A ⊢ false	
                 -------------- (false elim)  
                     A ⊢ p	

As regras podem ser interpretadas da seguinte forma:

    - Axioma: a partir de um conjunto de premissas que inclui p, conclui-se que p é 
      provável — ou seja, p é válido 'por premissa'.

    - Introdução da implicação: se for possível provar q a partir da premissa de A, p, então 
      conclui-se que p → q é provável a partir da premissa de A. Ou seja, uma prova de p → q 
      é uma maneira de transformar a premissa de p em uma prova de q. O nome da regra indica 
      que o conectivo de implicação → é introduzido na conclusão; ele não estava presente na 
      premissa.

    - Eliminação da implicação: se for possível provar p → q, bem como p, a partir de A, 
      então conclui-se que q é provável a partir de A. Ou seja, visto que há uma maneira de 
      transformar uma premissa de p em uma prova de q, e visto que há uma prova de p, é 
      possível usá-las em conjunto para construir uma prova de q. O nome da regra indica 
      que → é eliminado na conclusão; ele estava presente nas premissas. Esta regra é 
      comumente conhecida como 'modus ponens'.

    - Eliminação do falso: se for possível provar o falso a partir de A, então o conjunto 
      de premissas é inconsistente, logo conclui-se que é possível provar qualquer coisa a 
      partir de A — incluindo uma proposição arbitrária p. Este é o princípio 'ex falso 
      quodlibet'. Observe que não há regra de inferência para a introdução do falso, já que 
      nunca devemos ser capazes de provar o falso a partir de um conjunto consistente de 
      premissas.

As regras de inferência da dedução natural são diretas de formalizar no Rocq. É conveniente 
representar o conjunto de premissas como uma lista, já que já temos muita experiência com 
esse tipo. *)

Inductive provable : list proposition -> proposition -> Prop :=
  | axiom : forall A p,
      In p A ->
      provable A p
  | implies_intro : forall A p q,
      provable (p :: A) q ->
      provable A (implies p q)
  | implies_elim : forall A p q,
      provable A (implies p q) ->
      provable A p ->
      provable A q
  | false_elim : forall A p,
      provable A false ->
      provable A p.

(* Aqui estão alguns exemplos de uso do sistema de provas. *)

Example ex_P_provable : provable [] ex_P.
(*
         -------------------- (axiom)
                p ⊢ p
         -------------------- (implies intro)
              ⊢ p -> p
*)
Proof.
  unfold ex_P. apply implies_intro.
  apply axiom. simpl. left. reflexivity.
Qed.

Example ex_PQ_provable : provable [] ex_PQ.
(*
      ------------------- (axiom)
           P, Q ⊢ P
      ------------------- (implies intro)
          P ⊢ Q -> P
      ------------------- (implies intro)
        ⊢ P -> Q -> P
*)
Proof.
  (* TRABALHADO EM AULA *)
  unfold ex_PQ. apply implies_intro. apply implies_intro.
  apply axiom. simpl. right. left. reflexivity.
Qed.

Example ex_mp : forall (P Q : string),
  provable [implies (atom P) (atom Q); (atom P)] (atom Q).
(*
    ------------------- (axiom)     -------------- (axiom)
    P -> Q, P ⊢ P -> Q             P -> Q, P ⊢ P
    ---------------------------------------------- (implies elim)
                   P -> Q, P ⊢ Q
*)
Proof.
  (* TRABALHADO EM AULA *)
  intros P Q. apply implies_elim with (atom P).
  - apply axiom. simpl. left. reflexivity.
  - apply axiom. simpl. right. left. reflexivity.
Qed.

(* O uso da regra de axioma seguido de raciocínio sobre In torna-se entediante. Podemos 
automatizá-lo com a seguinte pequena tática personalizada. As técnicas usadas na tática 
serão explicadas em Auto (ou, alternativamente, em AltAuto). *)

Ltac by_assumption :=
  constructor;
  repeat match goal with
  | |- In ?p (?h :: ?t) => simpl
  | |- (?x = ?y) \/ ?p => first [left; reflexivity | right]
  | |- False => idtac "by_assumption failed: not in assumptions"; fail
  end.

Example in_assumptions : provable [atom "P"] (atom "P").
Proof.
  by_assumption.
Qed.

Example not_in_assumptions : provable [atom "Q"] (atom "P").
Proof.
  by_assumption.
Abort.

Example ex_P_provable' : provable [] ex_P.
Proof.
  unfold ex_P. apply implies_intro.
  by_assumption.
Qed.

(* Exercício *)
(* Mostre que a terceira proposição de exemplo que demos originalmente é provável. 
Primeiro, como aquecimento, prove uma equivalente a ela no Rocq. *)

Theorem ex_PQR_provable_rocq : forall (P Q R : Prop),
  (P -> Q -> R) -> (P -> Q) -> P -> R.
Proof.
  intros P Q R HPQR HPQ HP.   
  apply HPQR.
  - apply HP.
  - apply HPQ. apply HP.
Qed.

(* Segundo, prove-a usando dedução natural. 

Dica: tente esboçar a derivação com as regras de inferência no papel primeiro. A parte 
complicada é encontrar as proposições corretas para instanciar implies_elim a cada vez. *)

Theorem ex_PQR_provable_nd : provable [] ex_PQR.
Proof.
  unfold ex_PQR. apply implies_intro.
  apply implies_intro. apply implies_intro.
  apply implies_elim with (atom "Q").  
  -  apply implies_elim with (atom "P"). 
      + apply axiom. simpl. right. right. left. reflexivity.
      + apply axiom. simpl. left. reflexivity.
  - apply implies_elim with (atom "P").
      + apply axiom. simpl. right. left. reflexivity.
      + apply axiom. simpl. left. reflexivity.
Qed.

(* Obs: Poderia ter sido usado 'by_assumption' em cada bullet '+', mas a opção foi de 
tornar a prova mais explícita *)

(* Exercício *)
(* Prove cada uma das seguintes proposições. *)

Theorem implies_trans : forall (P Q R : string),
  provable []
  (implies (implies (atom P) (atom Q))
           (implies (implies (atom Q) (atom R))
                    (implies (atom P) (atom R)))).
Proof.
  intros P Q R. apply implies_intro.
  apply implies_intro. apply implies_intro.
  apply implies_elim with (atom Q).
  - apply axiom. simpl. right. left. reflexivity.
  - apply implies_elim with (atom P).  
    + apply axiom. simpl. right. right. left. reflexivity.
    + apply axiom. simpl. left. reflexivity.
Qed.

Theorem exfalso_quodlibet : forall  (P : string),
  provable [] (implies false (atom P)).
Proof.
  intros P. apply implies_intro.
  apply false_elim. apply axiom. simpl.
  left. reflexivity.
Qed.

Theorem contrapositive : forall (P Q : string),
  provable []
  (implies (implies (atom P) (atom Q))
           (implies (not (atom Q)) (not (atom P)))).
Proof.
  intros P Q. 
  apply implies_intro. apply implies_intro.
  apply implies_intro. unfold not.
  apply implies_elim with (atom Q).
  - by_assumption.
  - apply implies_elim with (atom P).
    + by_assumption.
    + by_assumption.
Qed.

(******************************************** Programas ************************************)

(* Assim como acabamos de embutir a lógica no Rocq, agora precisamos embutir uma linguagem 
de programação no Rocq. Ou seja, modelamos a sintaxe dos programas com tipos indutivos e a 
verificação de tipos com uma proposição definida indutivamente. 

A linguagem que formalizamos é o cálculo lambda puro simplesmente tipado. É um núcleo 
pequeno, mas expressivo, da programação funcional: os programas consistem em variáveis, 
funções e aplicação de funções. Nesse nível de detalhe, a correspondência entre programas e 
provas pode ser enunciada de forma clara e provada com precisão. Além disso, este cálculo já 
captura a estrutura essencial subjacente às linguagens funcionais tipadas, de modo que os 
resultados que obtemos aqui se generalizam bem além deste cenário minimalista. *)

(*** Sintaxe ***)

(* Começamos modelando os tipos dos programas. 

  - Uma variável de tipo representa um tipo desconhecido, muito parecida com o X em X : Type 
    que usamos ao definir listas polimórficas no Rocq. Novamente, usamos strings do Rocq 
    como identificadores.
    
  - Uma seta representa um tipo de função, como  t1 → t2 no Rocq. *)

Inductive type :=
  | tvar (id : string)
  | arrow (t1 t2 : type).

(* Em seguida, modelamos as expressões de programas (também conhecidas como termos). 

  - Como de costume, temos variáveis.

  - Uma função, também conhecida como abstração, é como fun (x : t) => e no Rocq. Ela vincula 
    uma variável, declara explicitamente o tipo dessa variável e possui uma expressão como 
    seu corpo.

  - Uma aplicação aplica uma função a um argumento, como e1 e2 no Rocq. *)

Inductive expr :=
  | var (id : string)
  | abs (id : string) (t : type) (e : expr)
  | app (e1 e2 : expr).

(* Aqui estão alguns exemplos de programas. *)

Definition e_I : expr :=
  (* fun (x:T) => x *)
  abs "x" (tvar "T") (var "x").

Definition e_K : expr :=
  (* fun (x:T) (y:U) => x *)
  abs "x" (tvar "T") (abs "y" (tvar "U") (var "x")).

Definition e_S : expr :=
  (* fun (x:T->U->V) (y:T->U) (z:T) => x z (y z) *)
  abs "x" (arrow (tvar "T") (arrow (tvar "U") (tvar "V")))
    (abs "y" (arrow (tvar "T") (tvar "U"))
      (abs "z" (tvar "T")
        (app (app (var "x") (var "z"))
             (app (var "y") (var "z"))))).

(*** Verificação de Tipos ***)

(* Um sistema de tipos é uma coleção de axiomas e regras de inferência para determinar se um 
programa possui tipagem correta (well-typed). Como nossa pequena linguagem de programação 
declara explicitamente o tipo de cada variável como parte da sintaxe abs, é bastante fácil 
construir um sistema de tipos para a linguagem. Em particular, não precisamos inferir nenhum 
tipo.

A base para o nosso sistema de tipos é uma relação de tipagem escrita E ⊢ e : t, onde e é 
uma expressão, t é um tipo, E é um ambiente de tipagem que registra os tipos das variáveis e, 
como de costume, os dois-pontos são lidos como ''tem o tipo''.

O ambiente de tipagem pode ser visto como um mapa parcial que associa identificadores a 
tipos. Escrevemos E, x:t para denotar o mapa que contém todas as associações de E, bem como 
uma associação de x para t. Assumimos nessa notação (sem perda de generalidade — as 
variáveis podem ser renomeadas conforme necessário) que x já não estava associado em E.

A relação de tipagem é definida com as seguintes regras de inferência: 

  	          -------------------(t-var)  
              E, x : t ⊢ x : t	

                    E, x : t1 ⊢ e : t2
              ---------------------------------- (t-abs)  
              E ⊢ fun (x : t1) => e : t1 -> t2	

              E ⊢ e1 : t1 -> t2    E ⊢ e2 : t1	
              ----------------------------------- (t-app)  
                       E ⊢ e1 e2 : t2	


As regras podem ser interpretadas da seguinte forma:
  - T-Var: se o ambiente de tipagem associa x a t, então x tem o tipo t nesse ambiente.

  - T-Abs: se e tem o tipo t_2 em um ambiente de tipagem que associa x a t_1, então a função 
    `fun (x : t1) => e`, criada pela abstração de x, tem o tipo t1 → t2.

  - T-App: se e_1 é uma função com o tipo t1 → t2 e e_2 tem o tipo t_1, então aplicar e_1 à 
    entrada e_2 produz uma saída do tipo t_2.

 Como uma representação simples de mapas parciais, usamos uma lista de associação, ou seja, 
 uma lista de pares, onde o primeiro componente do par é uma chave e o segundo componente é 
 o valor ao qual essa chave está associada. Para simplificar, omitimos qualquer verificação 
 para proibir chaves duplicadas.*)

Definition tenv := list (string * type).

(* As regras de inferência do sistema de tipos são diretas de formalizar no Rocq. *)

Inductive hastype : tenv -> expr -> type -> Prop :=
  | t_var : forall E x t,
      In (x, t) E ->
      hastype E (var x) t
  | t_abs : forall E x t1 e t2,
      hastype ((x, t1) :: E) e t2 ->
      hastype E (abs x t1 e) (arrow t1 t2)
  | t_app : forall E e1 t1 t2 e2,
      hastype E e1 (arrow t1 t2) ->
      hastype E e2 t1 ->
      hastype E (app e1 e2) t2.
    
(* Os programas de exemplo dados acima são todos bem tipados. Nossa tática by_assumption 
continua funcionando igualmente bem para listas de associação. *)

Example e_I_typable :
  hastype [] e_I (arrow (tvar "T") (tvar "T")).
(*
        ---------------------------- (t-var)
               x : T ⊢ x : T
        ---------------------------- (t-abs)
        ⊢ fun (x : T) => x : T -> T
*)
Proof.
  unfold e_I. apply t_abs. by_assumption.
Qed.

Example e_K_typable :
  hastype [] e_K (arrow (tvar "T") (arrow (tvar "U") (tvar "T"))).
(*
      ------------------------------------------------ (t-var)
                   x : T, y : U ⊢ x : T
      ------------------------------------------------ (t-abs)
            x : T ⊢ fun (y : U) => x : U -> T
      ------------------------------------------------ (t-abs)
      ⊢ fun (x : T) => fun (y : U) => x : T -> U -> T
*)
Proof.
  (* TRABALHADO EM AULA *)
  unfold e_K. apply t_abs. apply t_abs. by_assumption.
Qed.

(* Exercício *)