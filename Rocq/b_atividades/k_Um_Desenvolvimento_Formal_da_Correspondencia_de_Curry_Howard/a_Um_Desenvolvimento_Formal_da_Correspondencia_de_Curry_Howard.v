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

Module Implicational.

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
(* Mostre que o terceiro programa de exemplo acima é tipável. Dica: tente rascunhar a prova 
no papel primeiro. *)

Theorem e_S_typable :
  hastype [] e_S
    (arrow (arrow (tvar "T") (arrow (tvar "U") (tvar "V")))
           (arrow (arrow (tvar "T") (tvar "U"))
                  (arrow (tvar "T") (tvar "V")))).
Proof.  
  unfold e_S. apply t_abs. apply t_abs. apply t_abs. 
  apply t_app with (t1 := tvar "U").
  - apply t_app with (t1 := tvar "T").
    + by_assumption.
    + by_assumption.
  - apply t_app with (t1 := tvar "T").
    + by_assumption.
    + by_assumption.
Qed.

Definition prog_B :=
  (abs "g" (arrow (tvar "Y") (tvar "Z"))
    (abs "f" (arrow (tvar "X") (tvar "Y"))
      (abs "x" (tvar "X")
        (app (var "g") (app (var "f") (var "x")))))).

Theorem prog_B_typable : exists (T : type),
  hastype [] prog_B T.
Proof.
  unfold prog_B. 
  exists (arrow (arrow (tvar "Y") (tvar "Z")) 
  (arrow (arrow (tvar "X") (tvar "Y")) (arrow (tvar "X") (tvar "Z")))).
  apply t_abs. apply t_abs. apply t_abs. 
  apply t_app with (t1 := tvar "Y").
  - by_assumption.
  - apply t_app with (t1 := tvar "X").
    + by_assumption.
    + by_assumption.
Qed.

Definition prog_C :=
  (abs "f" (arrow (tvar "X") (arrow (tvar "Y") (tvar "Z" )))
    (abs "y" (tvar "Y")
      (abs "x" (tvar "X")
        (app (app (var "f") (var "x")) (var "y"))))).

Theorem prog_C_typable : exists (T : type),
  hastype [] prog_C T. 
Proof.
  unfold prog_C.
  exists (arrow (arrow (tvar "X") (arrow (tvar "Y") (tvar "Z" ))) 
  (arrow (tvar "Y") (arrow (tvar "X") (tvar "Z")))).
  apply t_abs. apply t_abs. apply t_abs.
  apply t_app with (t1 := tvar "Y").
  - apply t_app with (t1 := tvar "X").
    + by_assumption.
    + by_assumption.
  - by_assumption.
Qed.

Definition prog_W_type :=
  arrow (arrow (tvar "X") (arrow (tvar "X") (tvar "Y")))
        (arrow (tvar "X") (tvar "Y")).

Theorem prog_W_typable : exists (e : expr),
  hastype [] e prog_W_type.
Proof.
  unfold prog_W_type.
  exists  (abs "f" (arrow (tvar "X") (arrow (tvar "X") (tvar "Y")))
    (abs "g" (tvar "X")
        (app (app(var "f") (var "g"))(var "g")))).
  apply t_abs. apply t_abs. 
  apply t_app with (t1 := tvar "X").
  - apply t_app with (t1 := tvar "X").
    + by_assumption.
    + by_assumption.
  - by_assumption.
Qed.
  
(*********************************** A Correspondência **********************************)

(* Usando as formalizações de provabilidade e tipabilidade, agora podemos tornar a 
correspondência de Curry-Howard precisa. Em vez de tratá-la como uma analogia informal, 
compararemos as regras de inferência do sistema de provas com as do sistema de tipos. 

A ideia principal é que cada regra lógica possui uma regra de tipagem correspondente, e 
que as derivações de tipagem podem ser vistas como derivações de prova com conteúdo 
computacional adicional. Para ver isso, examinamos as regras lado a lado e observamos 
como elas expressam a mesma estrutura subjacente. *)

(*** Eliminação da Seta ***)

(* Primeiro, considere as regras que envolvem a eliminação de uma seta, seja ela uma seta 
de tipo função ou uma seta de implicação: 

                E ⊢ e1 : t1 -> t2    E ⊢ e2 : t1	
                ---------------------------------- (t-app)  
                          E ⊢ e1 e2 : t2	

                  A ⊢ p -> q         A ⊢ p	
                  ----------------------------- (implies elim)  
                              A ⊢ q	

Observe o que acontece se apagarmos de t-app tudo entre cada torniquete ⊢ (exclusivo) e 
os dois-pontos (inclusivo): 

                   E ⊢ t1 -> t2       E ⊢ t1	
                  -------------------------- (t-app-erased)  
                           E ⊢ t2	

                  A ⊢ p -> q         A ⊢ p	
                  --------------------------- (implies elim)  
                           A ⊢ q
                           
A regra resultante (mesmo que já não seja uma regra de tipagem bem-formada) se parece 
exatamente com a implies elim. Isso não é por acaso!

Lembre-se de que podemos pensar na implicação como uma transformação: ela pega uma prova 
de p e a transforma em uma prova de q. Da mesma forma, um tipo seta é uma transformação: 
ele pega uma entrada do tipo t_1 e a transforma em uma saída do tipo t_2.

Portanto, a regra de tipagem t-app expressa a mesma ideia que a regra de provabilidade de 
eliminação da implicação, mas a complementa com o código e_1 que realiza a transformação. *)

(*** Introdução da Seta ***)

(* Segundo, considere as regras que envolvem a introdução de uma seta: 

                             E, x : t1 ⊢ e : t2	
                     ------------------------------- (t-abs)  
                     E ⊢ fun (x : t1) => e : t1 -> t2	

                                A, p ⊢ q	
                              ------------ (implies intro)  
                              A ⊢ p -> q	

Como antes, se apagarmos os programas de t-abs, obtemos uma regra que se parece exatamente 
com a introdução da implicação

                               E, t1 ⊢ t2	
                             --------------- (t-abs-erased)  
                              E ⊢ t1 -> t2	

                               A, p ⊢ q	
                              ------------- (implies intro)  
                              A ⊢ p -> q	

Novamente, isso não é por acaso. Ambas expressam a ideia de como criar um transformador, 
seja ele uma implicação ou uma função. A regra de tipagem t-abs é apenas mais explícita ao 
fornecer o código fun (x : t1) => e que implementa a transformação. *)

(*** Premissas (ou Suposições) ***)

(* Terceiro e finalmente, considere as regras que envolvem premissas e a eliminação da 
regra de tipagem: 

                            ----------------- (t-var)  
                            E, x : t ⊢ x : t

  	                         ---------- (t-var-erased)  
                             E, t ⊢ t	

  	                          ------------ (axiom)  
                              A, p ⊢ p	

Mais uma vez, t-var-erased se parece exatamente com sua contraparte lógica, axiom. As 
regras estão expressando o mesmo princípio básico de raciocínio ''por premissa'' (ou 
''por suposição''). *)

(*** Demonstrando a Correspondência ***)

(* Vimos acima que, ao apagarmos os programas das regras de tipabilidade, ficamos 
essencialmente com regras de provabilidade. Portanto, qualquer derivação do tipo de um 
programa também estabelece uma derivação da provabilidade de uma proposição 
correspondente. 

Por exemplo, aqui está a derivação do tipo X → (Y → X) de um programa: 

        ------------------------------------------------- (t-var)
                         x:X, y:Y ⊢ x : X
        ------------------------------------------------- (t-abs)
                  x:X ⊢ fun (y:Y) => x : Y -> X
        ------------------------------------------------- (t-abs)
        ⊢ fun (x:X) => (fun (y:Y) => x)) : X -> (Y -> X)

E, ao apagarmos o código dessa derivação, resta-nos uma derivação da provabilidade de 
X → (Y → X):      
        
        ---------------- (axiom)
            X, Y ⊢ X
        ---------------- (implies introduction)
          X ⊢ Y -> X
        ---------------- (implies introduction)
        ⊢ X -> (Y -> X)

Portanto, as regras do nosso sistema de prova lógica estão em correspondência com as 
regras do nosso sistema de tipos: 

  - axiom corresponde a t-var.

  - implies_intro corresponde a t-abs.

  - implies_elim corresponde a t-app.

E, portanto, há uma correspondência entre os conectivos lógicos e os recursos de 
linguagens de programação:

  - Variáveis proposicionais correspondem a variáveis de programas.

  - A implicação corresponde a funções e aplicação.
 
No entanto, há uma pequena discrepância entre nossas estruturas de dados para tipos e 
proposições. Podemos usar a seguinte função para converter um tipo em uma proposição: *)

Fixpoint proposition_of_type (t : type) : proposition :=
  match t with
  | tvar x => atom x
  | arrow t1 t2 =>
    implies (proposition_of_type t1) (proposition_of_type t2)
  end.

Example pot_XY :
  proposition_of_type
    (arrow (tvar "X") (arrow (tvar "Y") (tvar "X")))
  =
    (implies (atom "X") (implies (atom "Y") (atom "X"))).
Proof. reflexivity. Qed.

(* Com a ajuda dessa função, podemos converter um ambiente de tipos em uma lista de 
premissas (ou suposições): *)

Definition assumptions_of_tenv (E : tenv) : list proposition :=
  map proposition_of_type (map snd E).

Example aot_XY :
  assumptions_of_tenv
    [("x"%string, tvar "X"); ("y"%string, tvar "Y")]
  =
    [atom "X"; atom "Y"].
Proof. reflexivity. Qed.

(* Exercício *)
(* O seguinte lema deve ser útil no teorema principal abaixo. Dica: prossiga por indução 
em l. *)

Lemma in_snd : forall (X Y Z : Type) (x : X) (y : Y) (f : Y -> Z) (l : list (X*Y)),
  In (x, y) l -> In (f y) (map f (map snd l)).
Proof.
  intros X Y Z x y f l Hxy.
  induction l as [ | h t IHl].
  - inversion Hxy.
  - destruct Hxy as [Hhead | HIn].
    + simpl. left. rewrite Hhead. reflexivity.
    + simpl. right. apply IHl. apply HIn.
Qed.

(* Por fim, podemos enunciar o primeiro de dois teoremas principais da correspondência 
de Curry-Howard: se E ⊢ e : t, então E ⊢ t após aplicar as funções de conversão 
apropriadas a E e t. Ou seja, uma derivação de tipabilidade para um programa também 
produz uma derivação de provabilidade para uma proposição. (Retornaremos ao segundo dos 
dois principais teoremas no final do capítulo.)

Dica: prossiga por indução sobre a evidência para hastype. *)

Theorem curry_howard : forall E e t,
  hastype E e t ->
  provable (assumptions_of_tenv E) (proposition_of_type t).
Proof.
  intros E e t Hht.
  induction Hht.
  - (* t_var *)
    apply axiom. unfold assumptions_of_tenv.
    apply (in_snd _ _ _ x t proposition_of_type E H).
  - (* t_abs *)
    simpl. apply implies_intro. unfold assumptions_of_tenv.
    unfold assumptions_of_tenv in IHHht. simpl in IHHht.
    apply IHHht.
  - (* t_app *)
    unfold assumptions_of_tenv. 
    simpl in IHHht1.
    apply (implies_elim _ _ _ IHHht1).
    apply IHHht2.
Qed.
    
End Implicational.

(******************** Estendendo a Correspondência para Sistemas Maiores *******************)

Module Propositional.

(*** Lógica: Adicionando a Conjunção e a Disjunção ***)

(* Agora estendemos o desenvolvimento para uma lógica proposicional completa com conjunção e 
disjunção. *)

Inductive proposition :=
  | atom (id : string)
  | implies (p q : proposition)
  | and (p q : proposition)
  | or (p q : proposition)
  | false.

Definition not (f : proposition) : proposition :=
  implies f false.

Definition true : proposition :=
  implies false false.

Definition iff (p q : proposition) :=
  and (implies p q) (implies q p).

(* As novas regras do sistema de prova são as seguintes: 

                  A ⊢ p   A ⊢ q	
                  --------------- (and intro)  
                    A ⊢ p /\ q	

                    A ⊢ p /\ q	
                    ---------- (and elim L)  
                      A ⊢ p	

                    A ⊢ p /\ q	
                    ---------- (and elim R)  
                      A ⊢ q	

                      A ⊢ p	
                    ---------- (or intro L)  
                    A ⊢ p \/ q	
                    
                      A ⊢ q	
                    ---------- (or intro R)  
                    A ⊢ p \/ q	

             A, p ⊢ r    A, q ⊢ r    A ⊢ p \/ q	
             ----------------------------------- (or elim)  
                           A ⊢ r

As novas regras podem ser interpretadas da seguinte forma:

  - Introdução da conjunção: se for possível provar tanto p quanto q a partir de A, então 
    segue-se que p ∧ q é provável a partir de A. Isto é, uma prova de uma conjunção consiste 
    em uma prova de cada componente.
    
  - Eliminação da conjunção (à esquerda): se for possível provar p ∧ q a partir de A, então 
    segue-se que p é provável a partir de A. Isto é, a partir de uma prova de uma conjunção, 
    podemos extrair seu primeiro componente.
    
  - Eliminação da conjunção (à direita): se for possível provar p ∧ q a partir de A, então 
    segue-se que q é provável a partir de A.
    
  - Introdução da disjunção (à esquerda): se for possível provar p a partir de A, então 
    segue-se que p ∨ q é provável a partir de A. Isto é, para provar uma disjunção, basta 
    provar um de seus componentes e identificar qual componente provamos (escolhendo a regra 
    à esquerda ou à direita).
    
  - Introdução da disjunção (à direita): se for possível provar q a partir de A, então 
    segue-se que p ∨ q é provável a partir de A.
    
  - Eliminação da disjunção: se a partir de A, p podemos provar r, e a partir de A, q podemos 
    provar r, e também temos uma prova de p ∨ q a partir de A, então segue-se que r é 
    provável a partir de A. Isto é, para usar uma prova de uma disjunção, devemos considerar 
    ambos os casos — assumindo p e assumindo q — e mostrar que a mesma conclusão r decorre 
    em cada caso.
    
Formalizamos essas regras da seguinte forma. *)

Inductive provable : list proposition -> proposition -> Prop :=
  (* As quatro primeiras regras faziam parte do nosso desenvolvimento anterior. *)
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
      provable A p
  (* As seis regras seguintes são novas. *)
  | and_intro : forall A p q,
      provable A p ->
      provable A q ->
      provable A (and p q)
  | and_elim_L : forall A p q,
      provable A (and p q) ->
      provable A p
  | and_elim_R : forall A p q,
      provable A (and p q) ->
      provable A q
  | or_intro_L : forall A p q,
      provable A p ->
      provable A (or p q)
  | or_intro_R : forall A p q,
      provable A q ->
      provable A (or p q)
  | or_elim : forall A p q r,
      provable (p :: A) r ->
      provable (q :: A) r ->
      provable A (or p q) ->
      provable A r.

Ltac by_assumption :=
  constructor;
  repeat match goal with
  | |- In ?p (?h :: ?t) => simpl
  | |- (?x = ?y) \/ ?p => first [left; reflexivity | right]
  | |- False => idtac "by_assumption failed: not in assumptions"; fail
  end.

(* Exercício *)
(* Prove que o falso é equivalente a uma inconsistência. *)

Theorem false_iff_inconsistency : forall (p : proposition),
  provable [] (iff false (and p (not p))).
Proof.
  intros p.
  unfold not. unfold iff.
  apply and_intro.
  - (* -> *)
    apply implies_intro.
    apply false_elim. by_assumption.
  - (* <- *)
    apply implies_intro.
    apply implies_elim with p.
    + apply and_elim_R with p. by_assumption.
    + apply and_elim_L with (q := (implies p false)).
      by_assumption.
Qed.

(* Prove que a conjunção é comutativa*)

Theorem and_comm : forall (p q : proposition),
  provable [] (iff (and p q) (and q p)).
Proof.
  intros p q.
  unfold iff.
  apply and_intro.
  - (* -> *)
    apply implies_intro.
    apply and_intro.
    + apply and_elim_R with p. by_assumption.
    + apply and_elim_L with q. by_assumption.
  - (* <- *)
    apply implies_intro.
    apply and_intro.
    +  apply and_elim_R with q. by_assumption.
    + apply and_elim_L with p. by_assumption.
Qed. 

(* Prove que a disjunção é comutativa*)

Theorem or_comm : forall (p q : proposition),
  provable [] (iff (or p q) (or q p)).
Proof.
  intros p q.
  unfold iff.
  apply and_intro.
  - (* -> *)
    apply implies_intro. apply or_elim with p q.
    + apply or_intro_R. by_assumption.
    + apply or_intro_L. by_assumption.
    + by_assumption.
  - (* <- *)
    apply implies_intro. apply or_elim with q p.
    + apply or_intro_R. by_assumption.
    + apply or_intro_L. by_assumption.
    + by_assumption.
Qed.

(* Prove que a conjunção é distributiva sobre a disjunção *)

Theorem and_distr_or : forall (p q r : proposition),
  provable [] (iff (and p (or q r)) (or (and p q) (and p r))).
Proof.
  intros p q r.
  unfold iff. 
  apply and_intro.
  - (* -> *)
    apply implies_intro.
    apply or_elim with q r.
    + apply or_intro_L. apply and_intro.
      * apply and_elim_L with (or q r). by_assumption.
      * by_assumption.
    + apply or_intro_R. apply and_intro.
      * apply and_elim_L with (or q r). by_assumption.
      * by_assumption.
    + apply and_elim_R with p. by_assumption.
  - (* <- *)
    apply implies_intro. apply or_elim with (and p q) (and p r).
    + apply and_intro.
      * apply and_elim_L with q. by_assumption.
      * apply or_intro_L. apply and_elim_R with p. by_assumption.
    + apply and_intro.
      * apply and_elim_L with r. by_assumption.
      * apply or_intro_R. apply and_elim_R with p. by_assumption.
    + by_assumption.
Qed.
   
(* Prove que a disjunção é distributiva sobre a conjunção *)

Theorem or_distr_and : forall (p q r : proposition),
  provable [] (iff (or p (and q r)) (and (or p q) (or p r))).
Proof.
  intros p q r.
  unfold iff.
  apply and_intro.
  - (* -> *)
    apply implies_intro.
    apply or_elim with p (and q r).
    + apply and_intro.
      * apply or_intro_L. by_assumption.
      * apply or_intro_L. by_assumption.
    + apply and_intro.
      * apply or_intro_R. apply and_elim_L with r. by_assumption.
      * apply or_intro_R. apply and_elim_R with q. by_assumption.
    + by_assumption.
  - (* <- *)
    apply implies_intro.
    apply or_elim with p q.
    + apply or_intro_L. by_assumption.
    + apply or_elim with p r.
      * apply or_intro_L. by_assumption.
      * apply or_intro_R. apply and_intro.
        -- by_assumption.
        -- by_assumption.
      *  apply and_elim_R with (or p q). by_assumption.
    + apply and_elim_L with (or p r). by_assumption.
Qed.    

(*** Programas: Adicionando Produtos, Somas e o Tipo Vazio ***)

(* Em seguida, estendemos nossa linguagem de programação para incluir pares e variantes.

Um par é exatamente igual aos pares de dois elementos que usamos anteriormente no Rocq, por 
exemplo, (1, true). Cada componente do par tem um tipo potencialmente diferente. O tipo de 
um par é um produto. Informalmente, escrevemos um tipo produto como t1 × t2. Introduzimos as 
funções de projeção fst e snd para retornar o primeiro e o segundo componente dos pares.

Uma variante é como o seguinte tipo do Rocq: 
                      
    Inductive sum (T1 T2 : Type) :=
    | inl : T1 → sum T1 T2
    | inr : T2 → sum T1 T2.
    
Ou seja, ele possui dois construtores chamados inl e inr. Estas são as chamadas funções de 
injeção, que recebem um único valor e o injetam no tipo soma. O l e o r significam ''esquerda'' 
(left) e ''direita'' (right), ou seja, indicam se o tipo é T_1 à esquerda da soma ou T_2 à 
direita. Um valor de um tipo soma é, portanto, um valor de tipo T_1 ou T_2, acompanhado de uma 
tag (o construtor) que diz de qual tipo ele veio. Informalmente, escrevemos um tipo soma como 
T_1 + T_2.

Para fazer uso de uma soma, adicionamos uma expressão case, que indica como calcular um 
resultado com base em se o valor sendo examinado está rotulado com inl ou inr. Informalmente, 
a representamos como

    case e of (x1 : t1) => e1 | (x2 : t2) => e2 end
    
Isso é muito parecido com a seguinte expressão do Rocq: 

    match e with (x1 : t1) ⇒ e1 | (x2 : t2) ⇒ e2 end 

Na verdade, usaríamos com prazer ''match'' como nome para ela, mas essa palavra é reservada 
pelo Rocq. As anotações de tipo são obrigatórias em nossa expressão case para evitarmos 
qualquer preocupação com inferência ou reconstrução de tipos.

Também aproveitamos esta oportunidade para introduzir um novo tipo e expressão de que 
precisaremos muito mais tarde para completar o segundo dos principais teoremas de 
Curry-Howard. Introduzimos o tipo vazio, que não possui valores. Ele corresponde à 
proposição falsa.

E introduzimos o programa magic, onde magic t e é ''magicamente'' uma expressão de tipo t 
desde que e : empty — o que, é claro, é impossível, já que não há valores do tipo vazio. O 
programa magic se assemelha um pouco a uma conversão de tipos (type cast), exceto que 
conversões de tipos em algumas linguagens permitem conversões arbitrárias sem justificativa, 
enquanto o magic é justificado por uma premissa impossível (um valor do tipo vazio).*)

Inductive type :=
  | tvar (id : string)
  | arrow (t1 t2 : type)
  | product (t1 t2 : type)
  | sum (t1 t2 : type)
  | empty.
  
Inductive expr :=
  | var (id : string)
  | abs (id : string) (t : type) (e : expr)
  | app (e1 e2 : expr)
  | magic (t : type) (e : expr)
  | pair (e1 e2 : expr)
  | fst (e : expr)
  | snd (e : expr)
  | inl (e1 : expr)
  | inr (e2 : expr)
  | case (e : expr) (id1 : string) (t1 : type) (e1 : expr)
                    (id2 : string) (t2 : type) (e2 : expr).

(* As regras do novo sistema de tipos são as seguintes: 

                E ⊢ e : empty	
               ------------------- (t-magic)  
               E ⊢ magic t e : t	

           E ⊢ e1 : t1    E ⊢ e2 : t2	
           --------------------------- (t-pair)  
             E ⊢ pair e1 e2 : t1 * t2	

              E ⊢ e : t1 * t2	
              ---------------- (t-fst)  
              E ⊢ fst e : t1	

              E ⊢ e : t1 * t2	
              ---------------- (t-snd)  
              E ⊢ snd e : t2	

                E ⊢ e : t1	
              -------------------- (t-inl)  
              E ⊢ inl e : t1 + t2	

                E ⊢ e : t2	
              -------------------- (t-inr)  

              E ⊢ inr e : t1 + t2	

        E ⊢ e : t1 + t2   E, x1:t1 ⊢ e1 : t   E, x2:t2 ⊢ e2 : t	
        -------------------------------------------------------- (t-case)  
        E ⊢ case e of (x1 : t1) => e1 | (x2 : t2) => e2 end : t	

As novas regras podem ser interpretadas da seguinte forma: 
  
  - T-Magic: se e tem o tipo empty, então magic t e tem o tipo t para qualquer t. Ou seja, a 
    partir de um valor impossível (um do tipo empty), podemos produzir um valor de qualquer 
    tipo. 
    
  - T-Pair: se e_1 tem o tipo t_1 e e_2 tem o tipo t_2, então o par pair e1 e2 tem o tipo t1 × t2. 
    Ou seja, um par empacota dois valores, um de cada tipo.
    
  - T-Fst: se e tem o tipo t1 × t2, então fst e tem o tipo t_1. Ou seja, a partir de um par, 
    podemos extrair seu primeiro componente.
    
  - T-Snd: se e tem o tipo t1 × t2, então snd e tem o tipo t_2. Ou seja, a partir de um par, 
    podemos extrair seu segundo componente.
    
  - T-Inl: se e tem o tipo t_1, então inl e tem o tipo t_1 + t_2 para qualquer tipo t_2. 
    Ou seja, podemos injetar um valor no lado esquerdo de um tipo soma.
    
  - T-Inr: se e tem o tipo t_2, então inr e tem o tipo t_1 + t_2 para qualquer tipo t_1. Ou seja, 
    podemos injetar um valor no lado direito de um tipo soma.
    
  - T-Case: se e tem o tipo t_1 + t_2, e se assumindo x_1 : t_1 pudermos mostrar que e_1 tem o 
    tipo t, e assumindo x_2 : t_2 pudermos mostrar que e_2 tem o tipo t, então a expressão case 
    tem o tipo t. Ou seja, para usar um valor de um tipo soma, devemos considerar ambas as 
    possibilidades, uma para cada injeção, e garantir que ambos os ramos produzam o mesmo 
    tipo de resultado.
    
Formalizamos isso da seguinte forma. *)

Definition tenv := list (string * type).

Inductive hastype : tenv -> expr -> type -> Prop :=
  (* As três primeiras regras faziam parte do nosso desenvolvimento anterior. *)
  | t_var : forall E x t,
      In (x, t) E ->
      hastype E (var x) t
  | t_abs : forall E x t1 e t2,
      hastype ((x, t1) :: E) e t2 ->
      hastype E (abs x t1 e) (arrow t1 t2)
  | t_app : forall E e1 t1 t2 e2,
      hastype E e1 (arrow t1 t2) ->
      hastype E e2 t1 ->
      hastype E (app e1 e2) t2
  (* As próximas sete regras são novas. *)
  | t_magic : forall E e t,
      hastype E e empty ->
      hastype E (magic t e) t
  | t_pair : forall E e1 e2 t1 t2,
      hastype E e1 t1 ->
      hastype E e2 t2 ->
      hastype E (pair e1 e2) (product t1 t2)
  | t_fst : forall E e t1 t2,
      hastype E e (product t1 t2) ->
      hastype E (fst e) t1
  | t_snd : forall E e t1 t2,
      hastype E e (product t1 t2) ->
      hastype E (snd e) t2
  | t_inl : forall E e t1 t2,
      hastype E e t1 ->
      hastype E (inl e) (sum t1 t2)
  | t_inr : forall E e t1 t2,
      hastype E e t2 ->
      hastype E (inr e) (sum t1 t2)
  | t_case : forall E e x1 t1 e1 x2 t2 e2 t,
      hastype E e (sum t1 t2) ->
      hastype ((x1, t1) :: E) e1 t ->
      hastype ((x2, t2) :: E) e2 t ->
      hastype E (case e x1 t1 e1 x2 t2 e2) t.

(* Exercício *)
(* Mostre que existe um programa capaz de trocar produtos. *)

Theorem swap_product :
  forall (t1 t2 : type), exists (e : expr),
    hastype [] e (arrow (product t1 t2) (product t2 t1)).
Proof.
  intros t1 t2.
  exists (abs "p" (product t1 t2) (pair (snd (var "p")) (fst (var "p")))).
  apply t_abs.
  apply t_pair.
  - apply t_snd with t1.
    by_assumption.
  - apply t_fst with t2.
    by_assumption.
Qed.

(* Mostre que existe um programa capaz de trocar somas. *)

Theorem swap_sum :
  forall (t1 t2 : type), exists (e : expr),
    hastype [] e (arrow (sum t1 t2) (sum t2 t1)).
Proof.
  intros t1 t2.
  exists (abs "s" (sum t1 t2) (case (var "s") "x1" t1 (inr (var "x1")) "x2" t2 (inl (var "x2"))) ).
   apply t_abs.
   apply t_case.
   - by_assumption.
   - apply t_inr. by_assumption.
   - apply t_inl. by_assumption.
Qed.

(* Mostre que existe um programa capaz de distribuir um produto sobre uma soma. *)

Theorem product_of_sum__sum_of_product :
  forall (t1 t2 t3 : type), exists (e : expr),
    hastype [] e (arrow (product t1 (sum t2 t3))
                        (sum (product t1 t2) (product t1 t3))).
Proof.
  intros t1 t2 t3.
  exists (abs "x" (product t1 (sum t2 t3))
           (case (snd (var "x"))
             "y2" t2 (inl (pair (fst (var "x")) (var "y2")))
             "y3" t3 (inr (pair (fst (var "x")) (var "y3"))))).
  apply t_abs.
  apply t_case.
  - apply t_snd with t1. by_assumption.
  - apply t_inl. apply t_pair.
    + apply t_fst with (sum t2 t3). by_assumption.
    + by_assumption.
  - apply t_inr. apply t_pair.
    + apply t_fst with (sum t2 t3). by_assumption.
    + by_assumption.
Qed.

(*** Provando a Correspondência Estendida ***)

(* As novas regras que adicionamos também estão em correspondência: 

  - false_elim corresponde a t_magic.
  - and_intro corresponde a t_pair.
  - and_elim_L corresponde a t_fst.
  - and_elim_R corresponde a t_snd.
  - or_intro_L corresponde a t_inl.
  - or_intro_R corresponde a t_inr.
  - or_elim corresponde a t_case. 
  
E, portanto, há uma correspondência estendida entre os conectivos lógicos e os recursos de 
linguagens de programação:

  - (Variáveis proposicionais correspondem a variáveis de programa.)
  - (A implicação corresponde a funções e aplicação.)
  - Falso corresponde ao tipo vazio.
  - Conjunção corresponde a pares.
  - Disjunção corresponde a variantes.   
  
Agora podemos re-provar o primeiro dos dois principais teoremas de Curry-Howard para nossa 
lógica estendida e linguagem de programação. Primeiro, estendemos nossa função de conversão 
para converter produtos em conjunções, e somas em disjunções.*)
  
Fixpoint proposition_of_type (t : type) : proposition :=
  match t with
  | tvar x => atom x
  | arrow t1 t2 =>
    implies (proposition_of_type t1) (proposition_of_type t2)
  | product t1 t2 =>
    and (proposition_of_type t1) (proposition_of_type t2)
  | sum t1 t2 =>
    or (proposition_of_type t1) (proposition_of_type t2)
  | empty => false
  end.

Definition assumptions_of_tenv (E : tenv) : list proposition :=
  map proposition_of_type (map Datatypes.snd E).

(* Exercício *)

(* A derivação de tipabilidade para um programa continua produzindo uma derivação de 
provabilidade para uma proposição.

Dica: os três primeiros casos da prova devem prosseguir com alterações mínimas em relação à 
sua versão anterior. Os novos casos devem ter uma dificuldade semelhante à dos casos 
anteriores. *)
Lemma in_snd : forall (X Y Z : Type) (x : X) (y : Y) (f : Y -> Z) (l : list (X*Y)),
  In (x, y) l -> In (f y) (map f (map Datatypes.snd l)).
Proof.
  intros X Y Z x y f l Hxy.
  induction l as [ | h t IHl].
  - inversion Hxy.
  - destruct Hxy as [Hhead | HIn].
    + simpl. left. rewrite Hhead. reflexivity.
    + simpl. right. apply IHl. apply HIn.
Qed.

Theorem curry_howard_extended : forall E e t,
  hastype E e t ->
  provable (assumptions_of_tenv E) (proposition_of_type t).
Proof.
  intros E e t Hht.
  induction Hht.
  - (* t_var *)
    apply axiom. unfold assumptions_of_tenv.
    apply (in_snd _ _ _ x t proposition_of_type E H).

  - (* t_abs *)
    simpl. apply implies_intro. unfold assumptions_of_tenv.
    unfold assumptions_of_tenv in IHHht. simpl in IHHht.
    apply IHHht.
   
  - (* t_app *)
    unfold assumptions_of_tenv. 
    simpl in IHHht1.
    apply (implies_elim _ _ _ IHHht1).
    apply IHHht2.

  - (* t_magic *)
    unfold assumptions_of_tenv.
    simpl in IHHht.
    unfold assumptions_of_tenv in IHHht.
    apply false_elim. apply IHHht.

  - (* t_pair *)
    unfold assumptions_of_tenv. 
    unfold assumptions_of_tenv in IHHht1, IHHht2.
    simpl. apply and_intro.
    + apply IHHht1.
    + apply IHHht2.

  - (* t_fst *)
    unfold assumptions_of_tenv.
    unfold assumptions_of_tenv in IHHht.
    simpl in IHHht.
    apply and_elim_L in IHHht.
    apply IHHht.

  - (* t_snd *)
    unfold assumptions_of_tenv.
    unfold assumptions_of_tenv in IHHht.
    simpl in IHHht.
    apply and_elim_R in IHHht.
    apply IHHht.

  - (* t_inl *)
    unfold assumptions_of_tenv.
    simpl. apply or_intro_L.
    apply IHHht.

  - (* t_inr *)
    unfold assumptions_of_tenv.
    simpl. apply or_intro_R.
    apply IHHht.

  - (* t_case *)
    unfold assumptions_of_tenv.
    unfold assumptions_of_tenv in 
    IHHht1, IHHht2, IHHht3.
    simpl in IHHht1, IHHht2, IHHht3.
    apply or_elim with (proposition_of_type t1) (proposition_of_type t2).
    + apply IHHht2.
    + apply IHHht3.
    + apply IHHht1.
Qed.

(************** O Segundo Teorema Principal da Correspondência (Avançado) *****************)

(* Até agora, mostramos que, se E ⊢ e : t, então E ⊢ t após aplicarmos as funções de 
conversão apropriadas a E e t. Ou seja, uma derivação de tipabilidade para um programa 
também produz uma derivação de demonstrabilidade para uma proposição.

E quanto à direção inversa? Poderíamos obter uma derivação de tipabilidade a partir de uma 
derivação de demonstrabilidade? A resposta é sim — mas isso dá mais trabalho. O motivo é 
que, na direção original, podíamos apagar informações (os programas) das derivações para 
fazer a conversão. Nessa nova direção, precisamos sintetizar os programas que estão 
faltando.

Primeiro, definimos uma função que converte uma proposição em uma representação em string 
(cadeia de caracteres). *)

Fixpoint string_of_proposition (p : proposition) : string :=
  match p with
  | atom id => "(" ++ id ++ ")"
  | implies p q =>
    "(implies " ++ (string_of_proposition p) ++ " "
                ++ (string_of_proposition q) ++ ")"
  | and p q =>
    "(and " ++ (string_of_proposition p) ++ " "
            ++ (string_of_proposition q) ++ ")"
  | or p q =>
    "(or " ++ (string_of_proposition p) ++ " "
           ++ (string_of_proposition q) ++ ")"
  | false => "(false)"
  end.

(* Em segundo lugar, definimos uma função que converte uma proposição em seu tipo equivalente. *)

Fixpoint type_of_proposition (p : proposition) : type :=
  match p with
  | atom id => tvar id
  | implies p q => arrow (type_of_proposition p) (type_of_proposition q)
  | and p q => product (type_of_proposition p) (type_of_proposition q)
  | or p q => sum (type_of_proposition p) (type_of_proposition q)
  | false => empty
  end.

(* Em terceiro lugar, definimos uma função para converter premissas (ou hipóteses) em um 
ambiente de tipos. Cada premissa recebe um nome, que é a sua conversão para uma string. *)

Definition tenv_of_assumptions (A : list proposition) : tenv :=
  map (fun p => (string_of_proposition p, type_of_proposition p)) A.

(* Agora estamos prontos para o segundo dos principais teoremas de Curry-Howard. *)

(* Exercício *)

(* Demonstre que, se uma proposição é demonstrável, então existe um programa bem-tipado 
cujo tipo corresponde a essa proposição.

Dica: proceda por indução sobre a evidência de que p é demonstrável. Nos (muitos) casos 
indutivos, use as hipóteses indutivas para derivar a existência de algumas subexpressões e, 
em seguida, monte-as em uma expressão com o tipo exigido. *)

(* | axiom : forall A p,
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
      provable A p
  (* As seis regras seguintes são novas. *)
  | and_intro : forall A p q,
      provable A p ->
      provable A q ->
      provable A (and p q)
  | and_elim_L : forall A p q,
      provable A (and p q) ->
      provable A p
  | and_elim_R : forall A p q,
      provable A (and p q) ->
      provable A q
  | or_intro_L : forall A p q,
      provable A p ->
      provable A (or p q)
  | or_intro_R : forall A p q,
      provable A q ->
      provable A (or p q)
  | or_elim : forall A p q r,
      provable (p :: A) r ->
      provable (q :: A) r ->
      provable A (or p q) ->
      provable A r. *)

Theorem curry_howard_converse : forall A p,
  provable A p ->
  exists e, hastype (tenv_of_assumptions A) e (type_of_proposition p).
Proof. 
  intros A p Hprov.
  induction Hprov.
  - (* axiom *)
    exists (var (string_of_proposition p)).
    apply t_var.
    unfold tenv_of_assumptions.
    apply (in_map (fun p0 => (string_of_proposition p0, type_of_proposition p0))).
    apply H.
  - (* implies_intro *)
    destruct IHHprov.
    simpl in H.
     exists (abs (string_of_proposition p) (type_of_proposition p) x).
     simpl. apply t_abs.
     apply H.
  - (* implies_elim *)
    destruct IHHprov1 as [e1 He1], IHHprov2 as [e2 He2].
    exists (app e1 e2). apply (t_app _ _ _ _ _ He1 He2).
  - (* false_elim *)
    destruct IHHprov as [e He].
    simpl in He.
    exists (magic (type_of_proposition p) e).
    apply t_magic. apply He.
  - (* and_intro *)
    destruct IHHprov1 as [e1 He1], IHHprov2 as [e2 He2].
    exists (pair e1 e2).
    apply (t_pair _ _ _ _ _ He1 He2).
  - (* and_elim_L *)
    destruct IHHprov as [e He].
    simpl in He. 
    exists (fst e).
    apply t_fst with (type_of_proposition q).
    apply He.
  - (* and_elim_R *)
    destruct IHHprov as [e He].
    simpl in He.
    exists (snd e).
    apply t_snd with (type_of_proposition p).
    apply He.
  - (* or_intro_L *)
    destruct IHHprov as [e He].
    simpl. exists (inl e).
    apply (t_inl _ _ _ _ He).
  - (* or_intro_R *)
    destruct IHHprov as [e He].
    simpl. exists (inr e).
    apply (t_inr _ _ _ _ He).
  - (* or_elim *) 
    destruct IHHprov1 as [e1 He1], 
    IHHprov2 as [e2 He2], 
    IHHprov3 as [e He].
    simpl in He1, He2, He.
    exists (case e (string_of_proposition p) (type_of_proposition p) e1 
    (string_of_proposition q) (type_of_proposition q) e2).
    apply (t_case _ _ _ _ _ _ _ _ _ He He1 He2).
Qed. 

End Propositional.

(********************************** Extensões Adicionais **********************************)

(* A correspondência de Curry–Howard vai muito além dos sistemas que estudamos neste 
capítulo. O que vimos aqui é apenas o começo de uma conexão muito mais rica entre lógica e 
programação. 

Muitas outras construções lógicas correspondem a recursos de linguagens de programação, 
incluindo:

  - Axiomas clássicos, que correspondem a operadores de controle de fluxo (por exemplo, 
    mecanismos relacionados a exceções e desvios não locais).

  - Quantificação universal de primeira ordem, que corresponde a tipos dependentes, nos
    quais os tipos podem depender de valores.

  - Quantificação existencial de primeira ordem, que corresponde a tipos abstratos, que 
    ocultam detalhes de implementação.

  - Quantificação proposicional de segunda ordem, que corresponde a polimorfismo, em que 
    programas podem ser escritos de forma genérica sobre tipos.

Essas correspondências não são apenas curiosidades: elas formam a base dos sistemas de 
tipos modernos, dos assistentes de provas e de técnicas para construir software confiável. 
As mesmas ideias que você viu aqui reaparecem no projeto de linguagens de programação, na 
verificação de sistemas críticos e nas pesquisas em andamento na fronteira entre lógica e 
computação.

Veja [Sørensen e Urzyczyn 2006] para uma exploração mais aprofundada. *)