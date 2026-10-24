(* Neste capítulo, examinamos de forma mais aprofundada como usar o Rocq como uma 
ferramenta para estudar outras coisas. Nosso estudo de caso é uma linguagem de programação 
imperativa simples chamada Imp, que incorpora um pequeno fragmento central de linguagens 
convencionais e populares, como C e Java. Aqui está uma função matemática familiar 
escrita em Imp: 

Z := X;
Y := 1;
while Z ≠ 0 do
  Y := Y × Z;
  Z := Z - 1
end

Concentramo-nos aqui em definir a sintaxe e a semântica do Imp; mais tarde, em 
Programming Language Foundations (Software Foundations, volume 2), desenvolvemos uma teoria 
de equivalência de programas e introduzimos a Lógica de Hoare, uma lógica popular para 
raciocinar sobre programas imperativos. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String.
Require Import LFPTBR.h_Mapas_Totais_e_Parciais.a_Mapas_Totais_e_Parciais.

(*************************** Expressões Aritméticas e Booleanas **************************)

(* Apresentaremos o Imp em três partes: primeiro, uma linguagem central de expressões 
aritméticas e booleanas; depois, uma extensão destas com variáveis; e, por fim, uma 
linguagem de comandos que inclui atribuição, condicionais, sequenciamento e loops. *)

(*** Sintaxe ***)

Module AExp.

(* Estas duas definições especificam a sintaxe abstrata de expressões aritméticas e 
booleanas. *)
Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(* Neste capítulo, nós vamos basicamente omitir a tradução da sintaxe concreta que um 
programador realmente escreveria para estas árvores de sintaxe abstrata — o processo que, 
por exemplo, traduziria a string ''1 + 2 × 3'' para a AST. 
                APlus (ANum 1) (AMult (ANum 2) (ANum 3)). 
                
O capítulo opcional ImpParser desenvolve um analisador léxico e um parser simples que 
podem realizar essa tradução. Você não precisa entender aquele capítulo para entender 
este, mas, se ainda não fez um curso onde essas técnicas são abordadas (por exemplo, um 
curso de compiladores), pode querer dar uma olhada rápida nele. Para comparação, aqui 
está uma gramática convencional em BNF (Backus-Naur Form) que define a mesma sintaxe 
abstrata:
      a := nat
        | a + a
        | a - a
        | a × a

       b := true
        | false
        | a = a
        | a ≠ a
        | a ≤ a
        | a > a
        | ¬b
        | b && b
        
Comparada à versão do Rocq acima... 

  - A BNF é mais informal — por exemplo, ela dá algumas sugestões sobre a sintaxe de 
    superfície das expressões (como o fato de a operação de adição ser escrita com um + 
    infixo), enquanto deixa outros aspectos da análise léxica e sintática (como a 
    precedência relativa de +, - e ×, o uso de parênteses para agrupar subexpressões, etc.) 
    não especificados. Alguma informação adicional — e inteligência humana — seria 
    necessária para transformar essa descrição em uma definição formal, por exemplo, para 
    implementar um compilador. 

    A versão do Rocq consistentemente omite todas essas informações e se concentra 
    apenas na sintaxe abstrata.

  - Por outro lado, a versão BNF é mais leve e fácil de ler. Sua informalidade a torna 
    flexível, o que é uma grande vantagem em situações como discussões no quadro-negro, 
    onde transmitir ideias gerais é mais importante do que fixar cada detalhe com 
    precisão. 
    
    De fato, existem dezenas de Notações Estilo-BNF e as pessoas alternam livremente 
    entre elas — geralmente sem se incomodar em dizer qual tipo de BNF estão usando, 
    porque não há necessidade: uma compreensão informal aproximada e prática 
    (''grosseira, mas pronta'') é tudo o que importa.

É bom estar familiarizado com ambos os tipos de notação: as informais para a comunicação 
entre humanos e as formais para a realização de implementações e provas. *)

(*** Avaliação ***)

(* Avaliar uma expressão aritmética produz um número. *)

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example teste_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

(* Analogamente, a avaliação de uma expressão booleana produz um resultado booleano. *)

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval a1) =? (aeval a2)
  | BNeq a1 a2 => negb ((aeval a1) =? (aeval a2))
  | BLe a1 a2 => (aeval a1) <=? (aeval a2)
  | BGt a1 a2 => negb ((aeval a1) <=? (aeval a2))
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

(*** Otimização ***)

(* Ainda não definimos muito, mas podemos já tirar proveito das definições existentes. Suponha 
que definamos uma função que receba uma expressão aritmética e a simplifique levemente, 
substituindo cada ocorrência de 0 + e (isto é, (APlus (ANum 0) e)), por apenas e.*)

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

(* Para ganhar confiança de que nossa otimização está fazendo a coisa certa, podemos 
testá-la em alguns exemplos e verificar se a saída parece correta. *)

Example teste_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

(* Mas se queremos ter certeza de que a otimização está correta — isto é, que avaliar uma
expressão otimizada sempre produz o mesmo resultado que a original — devemos prová-la! *)
Theorem optimize_0plus_corretude: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n eqn:En.
      * (* n = 0 *) simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity. Qed.

(************************************* Automação do Rocq *************************************)

(* A quantidade de repetição nesta última prova é um pouco irritante. E se tanto a linguagem 
das expressões aritméticas quanto a otimização cuja corretude fosse significativamente mais 
complexa, isso começaria a ser um problema sério. 

Até agora, temos feito todas as nossas provas usando apenas um pequeno punhado de táticas do
Rocq e ignorando completamente suas poderosas facilidades para construir partes das provas 
automaticamente. Esta seção introduz algumas dessas facilidades, e veremos mais ao longo dos
próximos capítulos. Aproveitar-se delas exigirá algum esforço — a automação do Rocq é uma
ferramenta poderosa — mas permitirá que ampliemos nossos esforços para definições mais 
complexas e propriedades mais interessantes sem nos deixarmos esmagados por detalhes chatos,
repetitivos e de baixo nível *)

(*** Tacticals ***)

(* Tacticals é o termo do Rocq para táticas que aceitam outras táticas como argumentos — 
'táticas de ordem superior', se quiser dizer assim. *)

(** O Tactical try **)

(* Se T for uma tática, então try T é uma tática exatamente igual a T, exceto pelo fato de que, 
se T falhar, try T simplesmente não faz absolutamente nada com sucesso (em vez de falhar). *)

Theorem bobinho1 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (* A reflexividade pura teria falhado. *)
  apply HP. (* Ainda podemos concluir a prova de outra forma. *)
Qed.

Theorem bobinho2 : forall ae, aeval ae = aeval ae.
Proof.
    try reflexivity. (* Isso faz apenas a reflexividade. *)
Qed.

(* Não há muita razão para usar o try em provas totalmente manuais como estas, mas ele é muito 
útil para fazer provas automatizadas em conjunto com o tactical ;, que mostraremos a seguir. *)

(** O Tactical ; (Forma Simples) **)

(* Na sua forma mais comum, o tactical ; recebe duas táticas como argumentos. 
A tática composta T;T' primeiro executa T e depois executa T' em cada submeta 
gerada por T. 

Por exemplo, considere o seguinte lema trivial: *)

Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n.
    (* Deixa duas submetas, que são resolvidas de forma idêntica...  *)
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
Qed.

(* Podemos simplificar esta prova usando o tactical ; : *)

Lemma foo' : forall n, 0 <=? n = true.
Proof.
  intros.
  (* faça o destruct da meta atual *)
  destruct n;
  (* depois aplique simpl em cada submeta resultante *)
  simpl;
  (* e aplique reflexivity em cada submeta resultante *)
  reflexivity.
Qed.

(* Usando try e ; juntos, podemos eliminar a repetição na prova que estava nos 
incomodando há pouco *)

Theorem optimize_0plus_corretude': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* A maioria dos casos decorre diretamente da IH... *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    (* mas os casos restantes -- ANum e APlus -- 
       são diferentes: *)
  - (* ANum *) reflexivity.
  - (* APlus *)
    destruct a1 eqn:Ea1;
      (* Novamente, a maioria dos casos decorre diretamente da IH: *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    (* O caso interessante, no qual o try... 
       não faz nada, é quando e1 = ANum n. Neste 
       caso, precisamos aplicar destruct em n (para ver
        se a otimização se aplica) e reescrever com a 
        hipótese de indução. *)
    + (* a1 = ANum n *) destruct n eqn:En;
      simpl; rewrite IHa2; reflexivity. Qed.

(* Especialistas em Rocq frequentemente usam esse idioma ...; try... após uma 
tática como induction para cuidar de vários casos semelhantes de uma só vez. 
De fato, essa prática tem um análogo em provas informais. Por exemplo, aqui 
está uma prova informal do teorema de otimização que corresponde à estrutura 
da formal: 

Teorema: Para todas as expressões aritméticas a,
    aeval (optimize_0plus a) = aeval a.
    
Prova: Por indução em a. A maioria dos casos decorre diretamente da IH. 
Os casos restantes são os seguintes:

    - Suponha que a = ANum n para algum n. Devemos mostrar que:
                    aeval (optimize_0plus (ANum n)) = aeval (ANum n).
      Isso é imediato a partir da definição de optimize_0plus.
      
    - Suponha que a = APlus a1 a2 para alguns a1 e a2. Devemos mostrar que:
                    aeval (optimize_0plus (APlus a1 a2)) = aeval (APlus a1 a2).
      Considere as formas possíveis de a1. Para a maioria delas, optimize_0plus 
      simplesmente chama a si mesma recursivamente para as subexpressões e 
      reconstrói uma nova expressão da mesma forma que a1; nesses casos, o 
      resultado decorre diretamente da IH. 
      
      O caso interessante é quando a1 = ANum n para algum n. Se n = 0, então:
                  optimize_0plus (APlus a1 a2) = optimize_0plus a2
      e a IH para a2 é exatamente o que precisamos. Por outro lado, se n = S n' 
      para algum n', então, novamente, optimize_0plus simplesmente chama a si 
      mesma recursivamente, e o resultado decorre da IH. ☐

No entanto, esta prova ainda pode ser aprimorada: o primeiro caso (para 
a = ANum n) é muito trivial — ainda mais trivial do que os casos que dissemos 
simplesmente decorrer da IH — e, mesmo assim, optamos por escrevê-lo por 
extenso. Seria melhor e mais claro omiti-lo e apenas dizer, no início, ''A 
maioria dos casos é imediata ou decorre diretamente da IH. O único caso 
interessante é o de APlus...''. Podemos fazer a mesma melhoria em nossa prova 
formal também. Eis como ela fica: *)

Theorem optimize_0plus_corretude'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* A maioria dos casos decorre diretamente da IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... ou são imediatos por definição *)
    try reflexivity.
  (* O caso interessante é quando a = APlus a1 a2. *)
  - (* APlus *)
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

(** O Tactical ; (Forma Geral) **)

(* O tactical ; também possui uma forma mais geral do que a simples T;T' que 
vimos acima. Se T, T_1, ..., T_n são táticas, então: 
      T; [T1 | T2 | ... | Tn]
é uma tática que primeiro executa T e, em seguida, executa T1 no primeiro 
subobjetivo gerado por T, executa T2 no segundo subobjetivo, e assim por 
diante.

Portanto, T;T' é apenas uma notação especial para o caso em que todos os 
T_i são a mesma tática; ou seja, T;T' é uma abreviação para:
          T; [T' | T' | ... | T']  *)

(** O tactical repeat **)

(* O tactical repeat pega outra tática e continua aplicando-a até que ela falhe ou até que seja 
bem-sucedida, mas sem fazer nenhum progresso. 

Aqui está um exemplo provando que 10 está em uma lista longa usando o repeat.*)

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

(* A tática repeat T nunca falha: se a tática T não se aplica ao objetivo original, então o 
repeat é bem-sucedido sem alterar o objetivo (ou seja, ele se repete zero vezes). *)
Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat simpl.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.

(* A tática repeat T não tem limite superior para o número de vezes que aplica T. Se T for uma 
tática que sempre é bem-sucedida (e faz progresso), então o repeat T entrará em loop infinito. *)
Theorem repeat_loop : forall (m n : nat),
  m + n = n + m.
Proof.
  intros m n.
  (* Descomente a próxima linha para ver o loop infinito ocorrer. Em seguida, você precisará 
     interromper o Rocq para que ele volte a responder. (No Proof General, C-c C-c faz isso.) *)
  (* repeat rewrite Nat.add_comm. *)
Admitted.

(* Espere — nós acabamos de escrever um loop infinito no Rocq?!?!

Mais ou menos. Enquanto a avaliação na linguagem de termos do Rocq, a Gallina, tem garantia de 
término, a avaliação de táticas não tem. No entanto, isso não afeta a consistência lógica do 
Rocq, já que o trabalho do repeat e de outras táticas é guiar o Rocq na construção de provas;
se o processo de construção diverge (ou seja, não termina), isso significa apenas que falhamos
em construir uma prova, e não que construímos uma prova ruim. *)

(* Exercício *)
(* Como a transformação optimize_0plus não altera o valor das aexps, devemos ser capazes de 
aplicá-la a todas as aexps que aparecem em uma bexp sem alterar o valor da bexp. Escreva uma 
função que realize essa transformação em bexps e prove que ela é correta. Use os tacticals que 
acabamos de ver para tornar a prova o mais curta e elegante possível. *)

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
 match b with
   | BTrue => BTrue
   | BFalse => BFalse
   | BEq a1 a2 => BEq (optimize_0plus a1)(optimize_0plus a2)
   | BNeq a1 a2 => BNeq (optimize_0plus a1)(optimize_0plus a2)
   | BLe a1 a2 => BLe (optimize_0plus a1)(optimize_0plus a2)
   | BGt a1 a2 => BGt (optimize_0plus a1) (optimize_0plus a2)
   | BNot b1 =>  BNot (optimize_0plus_b b1)
   | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
   end.

Example optimize_0plus_b_teste1:
  optimize_0plus_b (BNot (BGt (APlus (ANum 0) (ANum 4)) (ANum 8))) =
                   (BNot (BGt (ANum 4) (ANum 8))).
Proof.
  unfold optimize_0plus_b; try reflexivity.
Qed.

Example optimize_0plus_b_teste2:
  optimize_0plus_b (BAnd (BLe (APlus (ANum 0) (ANum 4)) (ANum 5)) BTrue) =
                   (BAnd (BLe (ANum 4) (ANum 5)) BTrue).
Proof.
  unfold optimize_0plus_b; try reflexivity.
Qed.

Theorem optimize_0plus_b_corretude : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros b.
  induction b; simpl;
  repeat rewrite optimize_0plus_corretude;
  try rewrite IHb; 
  try rewrite IHb1, IHb2;
  reflexivity.
Qed.

(* Exercício *)
(* Exercício de projeto: A otimização implementada pela nossa função optimize_0plus é 
apenas uma das muitas otimizações possíveis em expressões aritméticas e booleanas. 
Escreva um otimizador mais sofisticado e prove que ele está correto. (Você provavelmente 
achará mais fácil começar pequeno — adicione apenas uma otimização simples e sua 
respectiva prova de correção — e construa incrementalmente algo mais interessante.) *)

Fixpoint optimize_1times (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus e1 e2 => APlus (optimize_1times e1) (optimize_1times e2)
  | AMinus e1 e2 => AMinus (optimize_1times e1) (optimize_1times e2)
  | AMult (ANum 1) e2 => optimize_1times e2
  | AMult e1 e2 => AMult (optimize_1times e1) (optimize_1times e2)
  end.
  
Example teste_1times :
optimize_1times (AMult (ANum 1) (AMult (ANum 1) (ANum 7))) = ANum 7.
Proof. reflexivity. Qed.

Theorem optimize_1times_corretude : forall a,
  aeval (optimize_1times a) = aeval a.

Proof.
  intros a.
  induction a;
  try (simpl; rewrite IHa1, IHa2; reflexivity).
  try reflexivity.
  - destruct a1 as [n | e1 e2 | e1 e2 | e1 e2];
    try (simpl in *; rewrite IHa1, IHa2; reflexivity);
    destruct n as [ | [ | n'']]; simpl; try reflexivity;
     rewrite IHa2; try rewrite add_0_r; try reflexivity.
Qed.

(*** Definindo Novas Táticas ***)