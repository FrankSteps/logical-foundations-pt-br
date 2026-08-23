Require Import Arith.
Require Import List.
Import ListNotations.
Import List.

(* Tática Apply *)

(* Frequentemente encontramos situações onde o goal a ser provado é 
exatamente o mesmo que alguma hipótese no contexto ou um lema provado
anteriormente *)

Theorem bobinho1 : forall (n m : nat),
   n = m -> n = m.
   intros n m eq.
   apply eq. Qed.

(* A tática apply também funciona com hipóteses e lemas condicionais: 
se a sentença sendo aplicada for uma implicação, então as premissas 
dessa implicação serão adicionadas a lista de subgoals a serem provadas. 
apply também funciona com hipóteses condicionais: *)
Theorem bobinho2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.

(* O comando apply H faz o Rocq deduzir automaticamente os valores das 
variáveis universais de H ao comparar a conclusão da regra com o seu 
objetivo atual. *)
Theorem bobinho2a : forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

(* Exercício 
Complete a seguinte prova usando apenas intros e apply. *)
Theorem bobinho_ex : forall p,
  (forall n, Nat.even n = true -> Nat.even (S n) = false) ->
  (forall  n, Nat.even n = false -> Nat.odd n = true) ->
  Nat.even p = true -> Nat.odd (S p) = true.
Proof.
  intros n p q eq1.
  apply q. apply p. apply eq1.
Qed.

(* Para usar a tática apply, a (conclusão do) fato sendo aplicado deve 
corresponder exatamente ao objetivo (goal) atual (talvez após alguma 
simplificação), por exemplo, o apply não funcionará se os lados esquerdo e 
direito de uma igualdade estiverem invertidos. *)
Theorem bobinho3 : forall (n m : nat),
  n = m ->
  m = n.
Proof.
  intros n m H.

(* Aqui não podemos usar 'apply' diretamente *)
Fail apply H.

(* ...mas nós podemos usar a tática 'symmetric', que troca o lado esquerdo e
direito de uma igualdade em um goal. *)
symmetry. apply H. Qed.

(* Exercício
Você pode usar o apply com teoremas definidos anteriormente, não apenas com
hipóteses que já estão no seu contexto. Use o comando Search para encontrar
um teorema previamente definido sobre rev no módulo de listas (Lists). 
Use esse teorema como parte da sua solução (que é relativamente curta) para 
este exercício. Você não precisa usar indução.*)

Theorem rev_exercicio1 : forall (l l' : list nat),
  l = rev l' -> l' = rev l.
Proof.
  intros l l' H.
  Search rev inside Coq.Lists.List.
  rewrite H.
  symmetry.
  apply List.rev_involutive.
Qed.

(* Exercício: 1 estrela
Explique brevemente a diferença entre as táticas apply e rewrite. 
Quais são as situações em que ambas podem ser aplicadas de forma útil?*)

(* o rewrite funciona como um buscar e substituir que usa uma igualdade 
(A = B) para trocar um termo pelo outro no objetivo, 
enquanto o apply realiza um raciocínio lógico inverso (de trás para frente) 
usando uma implicação (P -> Q): se o seu objetivo atual é exatamente a 
conclusão Q, a tática o substitui pela premissa P que ainda precisa ser 
provada (ou fecha o objetivo na hora, caso a hipótese seja um fato direto 
P). *)
  

(********************* A tática apply ... with ... **********************)

(* O exemplo a seguir usa dois 'rewrites' em seguida par ir de [a;b] para
[e;f]. *)

Example trans_eq_exemplo : forall  (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. apply eq2. Qed.

  (* Como esse é um padrão comum, gostariamos de considerá-lo um lema que 
  mostra, de uma vez por todas, o fato que a igualdade é transiiva *)

Theorem trans_eq : forall (X:Type) (x y z : X),
  x = y -> y = z -> x = z.

Proof.
  intros X x y z eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

(* Agora, estamos aptos a usa trans_eq para provar o exemplo acima. 
No entanto, para fazer isso prcecisamos de um pequeno refinamento
da tática 'apply'. *)
Example trans_eq_exemplo' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f]->
     [a;b] = [e;f].

Proof.
  intros a b c d e f eq1 eq2.

(* Se simplesmente dissertermos ao Rocq para executar 'apply trans_eq' neste
ponto, ele conseguirá identificar (ao comparar o objetivo atual com a 
conclusão do lema) que deve instanciar X com [nat], x com [a,b] e z com [e,f]. 
No entanto, esse processo de correspondência não determina uma instanciação 
para y: precisamos fornecer uma explicitamente adicionando with (y:=[c,d]) 
à chamada do apply.*)

apply trans_eq with (y:=[c;d]).
apply eq1. apply eq2. Qed.

(* Na verdade, o nome y na cláusula with não é obrigatório, já que o Rocq 
geralmente é inteligente o suficiente para descobrir qual variável estamos 
instanciando. Em vez disso, poderíamos simplesmente escrever apply trans_eq 
with [c;d].
O Rocq também possui uma tática integrada chamada transitivity que cumpre
o mesmo propósito que aplicar trans_eq. A tática exige que declaremos a 
instanciação que queremos, assim como o apply with faz. *)
Example trans_eq_exemplo'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1. apply eq2. Qed.

(* Exercício *)
Definition SubtraiDois (n : nat) : nat :=
   match n with
   | 0 => 0
   | S 0 => 0
   | S (S (n')) => n'
   end.

Example trans_eq_exercicio : forall (n m o p : nat),
     m = (SubtraiDois o) ->
     (n + p) = m ->
     (n + p) = (SubtraiDois o).

Proof.
  intros n m o p eq1 eq2.
  transitivity m.
  apply eq2. apply eq1. Qed.

(***************** As Táticas 'injection' e 'discriminate' *****************)

(* Relembre a definição de números naturais:     
Inductive nat : Type :=
   | O
   | S (n : nat).
  
 É óbvio a partir desta definição que todo número possui uma de duas formas: 
ou ele é o construtor O, ou ele é construído aplicando o construtor S a outro 
número. Mas há mais nisso do que aparenta: implícitos na definição estão 
dois fatos adicionais:

  * O construtor S é injetivo (ou seja, um para um). Isto é, se S n = S m, 
    também deve ser verdade que n = m.

  * Os construtores O e S são disjuntos. Isto é, O não é igual a S n para 
  nenhum n.

Princípios semelhantes se aplicam a todo tipo definido indutivamente: todos 
os construtores são injetivos, e os valores construídos a partir de 
construtores distintos nunca são iguais. Para listas, o construtor cons é 
injetivo e a lista vazia nil é diferente de qualquer lista não vazia. 
Para booleanos, true e false são diferentes. (Como true e false não recebem 
argumentos, sua injetividade não faz diferença.) E assim por diante.

Podemos provar a injetividade de S usando a função pred definida em 
g_Naturais.v *)

Definition pred (n : nat) : nat :=
   match n with
   | O => O
   | S n' => n'
   end.


Theorem S_injetivo : forall (n m : nat),
  S n = S m ->
  n = m.
  
Proof.
  intros n m H1.
  assert (H2 : n = pred (S n)). 
  { reflexivity. }
  rewrite H2. rewrite H1. simpl. reflexivity.
Qed.

(* A tática assert do Rocq, usada acima, adiciona a hipótese fornecida ao 
contexto, mas primeiro exige que você prove a hipótese como um novo objetivo.

Essa técnica para injetividade pode ser generalizada para qualquer 
construtor escrevendo o equivalente a pred -- ou seja, escrevendo uma função 
que ''desfaz'' uma aplicação do construtor. *)

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
  
Proof.
  intros n m H.

(* Ao escrever injection H as Hmn neste ponto, estamos pedindo ao Rocq que 
gere todas as equações que ele pode inferir de H usando a injetividade dos 
construtores (no presente exemplo, a equação n = m). Cada uma dessas 
equações é adicionada como uma hipótese (chamada de Hmn neste caso) ao 
contexto. *)

  injection H as Hnm. apply Hnm.
Qed.

(* Aqui está um exemplo mais interessante que mostra como 'injection' pode
derivar múltiplas equações de uma vez *)

Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.

Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

(* Exercício *)
Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.

Proof.
  intros X x y z l j eq1 eq2.
  injection eq1 as H1 H2.
  rewrite H1.  rewrite eq2 in H2. 
  injection H2.
  symmetry.
  apply H.
Qed.

(* Chega de injetividade de construtores. E quanto à disjunção?

O princípio da disjunção diz que dois termos que começam com construtores 
diferentes (como O e S, ou true e false) nunca podem ser iguais. Isso 
significa que, sempre que nos encontrarmos em um contexto onde assumimos 
que dois termos desse tipo são iguais, estamos justificados em concluir 
qualquer coisa que quisermos, já que a premissa é sem sentido.

A tática discriminate incorpora esse princípio: ela é usada em uma hipótese 
que envolve uma igualdade entre construtores diferentes (por exemplo, 
false = true), e resolve o objetivo atual imediatamente. Alguns exemplos: *)
Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.

Proof.
  intros n m contra. discriminate contra. Qed.

Theorem discriminate_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.

Proof.
  intros n contra. discriminate contra. Qed.

(* Estes exemplos são instâncias de um princípio lógico conhecido como o 
princípio da explosão, o que afirma que uma hipótese contraditória implica 
qualquer coisa (mesmo coisas manifestamente falsas!).

Se você achar o princípio da explosão confuso, lembre-se de que essas provas 
não estão mostrando que a conclusão da afirmação é verdadeira. Em vez disso, 
elas estão mostrando que, se a situação sem sentido descrita pela premissa 
de alguma forma ocorresse, então a conclusão sem sentido também ocorreria -- 
porque estaríamos vivendo em um universo inconsistente onde toda declaração
é verdadeira.

Exploraremos o princípio de explosão com mais detalhes no próximo capítulo. *)

(* Exercício *)
Example discriminate_ex3 : forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.

Proof.
  intros X x y z l j H.
  discriminate H.

(* Para um exemplo mais útil, podemos usar discriminate para fazer uma 
conexão entre as duas noções diferentes de igualdade (= e =?) que vimos para 
os números naturais. *)
Notation "x =? y" := 
  ((fun {X : Type} (a b : X) => false) _ x y) 
  (at level 70).

Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.

(* Podemos prosseguir fazendo uma análise de casos em n. O primeiro caso é 
trivial. *)
destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    intros H. reflexivity.

(* No entanto, o segundo não parece tão simples: assumindo 0 =?(S n′) = true, 
devemos mostrar que S n′= 0! O caminho a seguir é observar que a própria 
premissa não faz sentido: *)
   - (* n = S n' *)
    simpl.

(* Se usarmos discriminate nessa hipótese, o Rocq confirma que o subobjetivo 
em que estamos trabalhando é impossível e o remove de considerações futuras. *)
   intros H. discriminate H.
Qed.

(* A injetividade dos construtores nos permite deduzir que forall (n m : nat)
, S n = S m -> n = m. A recíproca dessa implicação é um caso particular de 
um fato mais geral sobre construtores e funções, o qual acharemos útil mais 
adiante: *)
Theorem f_igual : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.

Theorem eq_implica_succ_igual : forall (n m : nat),
  n = m -> S n = S m.
Proof. intros n m H. apply f_igual. apply H. Qed.

(* De fato, há também uma tática chamada f_equal que pode provar esses t
eoremas diretamente. Dado um objetivo da forma f a1 ... an = g b1 ... bn, 
a tática f_equal produzirá subobjetivos da forma f = g, a1 = b1, ..., 
an = bn. Ao mesmo tempo, qualquer um desses subobjetivos que seja simples o 
suficiente (por exemplo, imediatamente provável por reflexividade) será 
descartado automaticamente. *)
Theorem eq_implica_succ_igual' : forall (n m : nat),
  n = m -> S n = S m.

Proof. intros n m H. f_equal. apply H. Qed.

(******************* Usando Táticaas em Hipóteses **************************)

(* Por padrão, a maioria das táticas atua sobre a fórmula do objetivo e 
deixa o contexto inalterado. No entanto, a maioria das táticas também 
possui uma variante que executa uma operação semelhante em uma afirmação 
presente no contexto.Por exemplo, a tática simpl in H realiza simplificação 
na hipótese H dentro do contexto. *)
Theorem S_inj : forall (n m : nat) (b : bool),
  ((S n) =? (S m)) = b ->
  (n =? m) = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.

(* Similarmente, apply L in H casa alguma instrução condicional L (da forma 
X -> Y, por exemplo) com uma hipótese H presente no contexto. No entanto, 
ao contrário do apply comum (que reescreve um objetivo que casa com Y em um 
subobjetivo X), o apply L in H casa H com X e, se bem-sucedido, o substitui 
por Y.Em outras palavras, apply L in H nos dá uma forma de "raciocínio para a 
frente" (forward reasoning): dados X -> Y e uma hipótese que casa com X, ele 
produz uma hipótese que casa com Y.Em contrapartida, o apply L realiza 
"raciocínio para trás" (backward reasoning): ele diz que, se sabemos X -> Y 
e estamos tentando provar Y, basta provar X.Aqui está uma variante de uma 
demonstração anterior, usando raciocínio para a frente do início ao fim em 
vez de raciocínio para trás. *)
Theorem bobinho4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.

Proof.
  intros n m p q EQ H.
  symmetry in H. apply EQ in H. symmetry in H.
  apply H. Qed.

(* O raciocínio para a frente (forward reasoning) parte do que é dado 
(premissas, teoremas previamente provados) e extrai conclusões iterativamente 
a partir deles até que o objetivo seja alcançado. O raciocínio para trás 
(backward reasoning) parte do objetivo e raciocina iterativamente sobre o que 
implicaria o objetivo, até que premissas ou teoremas previamente provados 
sejam atingidos.

As demonstrações informais vistas em aulas de matemática ou ciência da 
computação tendem a usar o raciocínio para a frente. Em contrapartida, o uso 
idiomático do Rocq geralmente favorece o raciocínio para trás, embora em 
algumas situações o estilo para a frente possa ser mais fácil de conceber. *)

(************************ Especializando Hipóteses ************************)

(* Outra tática útil para manipular hipóteses é o specialize. Ela é 
essencialmente uma combinação de assert e apply, mas frequentemente oferece 
uma maneira agradavelmente fluida de refinar hipóteses excessivamente gerais. 
Ela funciona assim:Se H é uma hipótese quantificada no contexto atual — ou 
seja, H : forall (x : T), P —, então specialize H with (x := e) alterará H 
para que ela se pareça com P com x substituído por e. Por exemplo: *)

(* Teorema Auxiliar trazido do Módulo de Indução *)
Theorem mult_1_l : forall n : Datatypes.nat, 
   1 * n = n.

Proof.
   intros n.
   simpl.
   induction n as [| n' IHn'].
   - reflexivity.
   - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem specialize_exemplo: forall n,
     (forall m, m*n = 0)
  -> n = 0.
  
Proof.
  intros n H.
  specialize H with (m := 1).
  rewrite mult_1_l in H.
  apply H. Qed.

(* Exercício *)

(* Função Auxiliar *)
Fixpoint enesimo_erro {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => enesimo_erro l' n'
               end
  end.

(* Use specialize para provar o seguinte lema, seguindo o modelo de 
specialize_exemplo acima. Não use indução. *)
Lemma enesimo_erro_sempre_none: forall (l : list nat),
  (forall i, enesimo_erro l i = None) ->
  l = [].

Proof.
  intros l H.
  specialize H with (i :=  O).
  destruct l.
  - reflexivity.
  - discriminate.
Qed.
  
(* Usar specialize antes de apply nos dá mais uma maneira de controlar onde 
o apply faz o seu trabalho. *)
Example trans_eq_exemplo''' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].

Proof.
  intros a b c d e f eq1 eq2.
  specialize trans_eq with (y:=[c;d]) as H.
  apply H.
  apply eq1.
  apply eq2. Qed.

(* Pontos a observar: 
- Podemos especializar fatos no contexto global, não apenas hipóteses locais.
- A cláusula as... no final diz ao specialize como nomear a nova hipótese 
nesse caso. *)

(********************** Variando a Hipótese de Indução ********************) 

(* Às vezes, é importante controlar a forma exata da hipótese de indução ao 
realizar provas por indução no Rocq. Em particular, podemos precisar ter 
cuidado sobre qual das suposições movemos (usando intros) do objetivo para o 
contexto antes de invocar a tática de indução.

Por exemplo, suponha que queremos mostrar que double é injetiva — isto é, que 
ela mapeia argumentos diferentes para resultados diferentes:

Theorem double_injetivo: ∀ n m,
  double n = double m →
  n = m.

A maneira como começamos esta prova é um pouco delicada: se começarmos com 
intros n. induction n., então tudo correrá bem. Mas se começarmos 
introduzindo ambas as variáveis intros n m. induction n., ficaremos travados 
no meio do caso indutivo... *)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem double_injetivo_FALHA : forall n m,
  double n = double m ->
  n = m.

Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) f_equal.
(* Nesse ponto, a hipótese de indução (IHn') não nos dá n' = m' — há um 
S extra no caminho — portanto, o objetivo não é provável. *)
Abort.

(* O que deu errado?
O problema é que, no ponto em que invocamos a hipótese de indução, já 
introduzimos m no contexto — intuitivamente, dissemos ao Rocq: "Vamos 
considerar um n e um m particulares..." e agora temos que provar que, se 
double n = double m para esses n e m particulares, então n = m.

A tática seguinte, induction n, diz ao Rocq: Vamos mostrar o objetivo por 
indução em n. Ou seja, vamos provar, para todo n, que a proposição
P n = "se double n = double m, então n = m"
vale, mostrando

P O
(ou seja, "se double O = double m então O = m") e

P n → P (S n)
(ou seja, "se double n = double m então n = m" implica "se double (S n) = 
double m então S n = m").

Se olharmos de perto para a segunda afirmação, ela está dizendo algo bastante 
estranho: que, para um m particular, se sabemos

"se double n = double m então n = m"

então podemos provar

"se double (S n) = double m então S n = m".

Para ver por que isso é estranho, vamos pensar em um m particular — digamos, 
5. A afirmação está dizendo então que, se sabemos

Q = "se double n = 10 então n = 5"

então podemos provar

R = "se double (S n) = 10 então S n = 5".

Mas saber Q não nos ajuda em absolutamente nada para provar R! Se tentássemos 
provar R a partir de Q, começaríamos com algo como "Suponha que double (S n) 
= 10..." mas aí ficaríamos travados: saber que double (S n) é 10 não nos diz 
nada útil sobre se double n é 10 (na verdade, sugere fortemente que double n 
não é 10!!), então Q é inútil.

Tentar realizar esta prova por indução em n quando m já está no contexto não 
funciona porque estamos então tentando provar uma afirmação envolvendo todo 
n, mas apenas um m particular.

Uma prova bem-sucedida de double_injective mantém m quantificado 
universalmente na declaração do objetivo no ponto em que a tática de 
indução é invocada em n: *)

Theorem double_injetivo : forall n m,
  double n = double m ->
  n = m.

Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *)

(* Note que tanto o objetivo quanto a hipótese de indução são diferentes 
desta vez: o objetivo nos pede para provar algo mais geral (ou seja, devemos 
provar a afirmação para todo m), mas a hipótese de indução IH' é 
correspondentemente mais flexível, permitindo-nos escolher qualquer m que 
quisermos ao aplicá-la. *)

intros m eq.

(* Agora escolhemos um m particular e introduzimos a suposição de que double 
n = double m. Como estamos fazendo uma análise de casos em n, também 
precisamos de uma análise de casos em m para manter os dois em sincronia. *)

destruct m as [| m'] eqn:E.

+ (* m = O *)

(* O caso 0 é trivial: *)

discriminate eq.
+ (* m = S m' *)
  f_equal.

(* Como agora estamos no segundo ramo do destruct m, o m' mencionado no 
contexto é o predecessor do m sobre o qual começamos a falar. Como também 
estamos no ramo S da indução, isso é perfeito: se instanciarmos o m genérico 
na hipótese de indução com o m' atual (essa instanciação é realizada 
automaticamente pelo apply no próximo passo), então IHn' nos dá exatamente o 
que precisamos para terminar a prova. *)


  apply IHn'. simpl in eq. injection eq as goal. apply goal. Qed.

(* O principal aprendizado de tudo isso é que você precisa ter cuidado, ao usar a indução, para não tentar provar algo específico demais: ao provar uma propriedade quantificada sobre as variáveis n e m por indução em n, às vezes é crucial deixar m "genérico".

O exercício a seguir, que fortalece ainda mais o vínculo entre =? e =, segue o mesmo padrão. *)

(* Exercício *)
Theorem eqb_true : forall (n m : nat ),
  n =? m = true -> n = m.

Proof.
  intros n. induction n as [| n' IHn'].
  - intros m eq. induction m as [| m'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros m eq. destruct m as [| m'] eqn:E. 
    + discriminate eq.
+ f_equal. apply IHn'. simpl in eq. discriminate eq. Qed.

(* Exercício *)
(* Teorema: ∀(nm:nat),n=?m=true⟹n=m.

Dê uma prova informal cuidadosa de eqb_true, declarando explicitamente a 
hipótese de indução e sendo o mais explícito possível sobre os 
quantificadores em todos os lugares.

Prova: Por indução matemática em n.

    Caso Base (n=0):
    Queremos provar que para todo m, se 0=?m=true, então 0=m.
    Seja m um número natural qualquer. Fazemos análise de casos em m:

        Se m=0, temos 0=?0=true, o que é verdade por definição, e 0=0 é 
        trivial.

        Se m=Sm′, temos 0=?Sm′=true, o que resulta em false = true, uma 
        contradição. Logo, este subcaso é trivialmente verdadeiro.

    Passo Indutivo (n=Sn′):
    Assumimos a hipótese de indução (IH) para n′:
    ∀(m:nat),n′=?m=true⟹n′=m

    Queremos mostrar que para todo m, se Sn′=?m=true, então Sn′=m.
    Seja m um número natural qualquer. Analisamos os casos de m:

        Se m=0, temos Sn′=?0=true, gerando a contradição false = true.

        Se m=Sm′, por definição, a hipótese Sn′=?Sm′=true simplifica para 
        n′=?m′=true. Aplicando a hipótese de indução com m′, deduzimos que 
        n′=m′. Aplicando o sucesor S em ambos os lados, obtemos Sn′=Sm′, 
        o que conclui a prova. ■ *)


(* Exercício *)
(* Além de tomar cuidado com a forma como você usa o intros, pratique o uso 
de variantes com "in" nesta prova. (Dica: use mais_n_Sm.) *)
 Theorem mais_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.

Proof.
   intros n m. induction n as [| n' IHn'].
   - simpl. reflexivity.
   - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.

Proof.
  intros n. induction n as [| n' IHn'].
  - intros m eq. induction m as [| m'] eqn:E.
    + reflexivity.
    + discriminate.
  - intros m eq. induction m as [| m'] eqn:E.
    + discriminate.
    + f_equal. simpl in eq. rewrite <- mais_n_Sm in eq. rewrite <- E in eq. 
      injection eq as eq_nova. rewrite E in eq_nova. 
      rewrite <- mais_n_Sm in eq_nova. injection eq_nova as eq2. 
      apply IHn' in eq2. apply eq2.
Qed.

(* A estratégia de fazer menos intros antes de uma indução para obter uma IH 
(hipótese de indução) mais geral nem vezes funciona; às vezes, alguma 
reorganização das variáveis quantificadas é necessária. Suponha, por exemplo, 
que quiséssemos provar double_injective fazendo indução em m em vez de em n. *)

Theorem double_injetivo_tentativa2_FALHA : forall n m,
  double n = double m ->
  n = m.

Proof.
  intros n m. induction m as [| m' IHm'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) f_equal.
        (* Nós estamos presos aqui, como antes. *)
Abort.

(* O problema é que, para fazer indução em m, devemos primeiro introduzir n. 
(Se simplesmente dissermos induction m sem introduzir nada antes, o Rocq 
introduzirá automaticamente n para nós!)O que podemos fazer em relação a 
isso? Uma possibilidade é reescrever o enunciado do lema para que m seja 
quantificado antes de n. Isso funciona, mas não é elegante: nós não queremos 
ter que distorcer os enunciados dos lemas para atender às necessidades de 
uma estratégia específica para prová-los! Em vez disso, queremos enunciá-los 
da maneira mais clara e natural possível. O que podemos fazer em vez disso é 
primeiro introduzir todas as variáveis quantificadas e, em seguida, 
regeneralizar uma ou mais delas, tirando seletivamente variáveis do contexto 
e colocando-as de volta no início do objetivo. A tática generalize 
dependent faz exatamente isso. *)

Theorem double_injetivo_tentativa2 : forall n m,
  double n = double m ->
  n = m.

Proof.
  intros n m.
  (* n e m estão ambos no contexto *)
  generalize dependent n.
  (* Agora n está novamente no goal e nós podemos fazer indução em
     m e conseguir uma IH suficientemente geral. *)
  induction m as [| m' IHm'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) f_equal.
      apply IHm'. injection eq as goal. apply goal. Qed.

(* Vamos ver uma prova informal deste teorema. 
Note que a proposição que provamos por indução deixa n quantificado, o que 
corresponde ao uso de generalize dependent em nossa prova formal.

Teorema: Para quaisquer números naturais n e m, se double n = double m, 
então n = m.

Prova: Seja m um número natural. Provamos por indução em m que, para qualquer 
n, se double n = double m, então n = m.

-Primeiro, suponha m = 0, e suponha que n seja um número tal que double n = 
double m. Devemos mostrar que n = 0.
Como m = 0, pela definição de double, temos double n = 0. Há dois casos a 
considerar para n. Se n = 0, terminamos, já que m = 0 = n, conforme exigido. 
Caso contrário, se n = S n' para algum n', chegamos a uma contradição: pela 
definição de double, podemos calcular double n = S (S (double n')), mas isso 
contradiz a suposição de que double n = 0.

-Segundo, suponha m = S m' e que n seja novamente um número tal que double n 
= double m. Devemos mostrar que n = S m', com a hipótese de indução de que 
para todo número s, se double s = double m', então s = m'.Pelo fato de que 
m = S m' e pela definição de double, temos double n = S (S (double m')). Há 
dois casos a considerar para n.Se n = 0, então por definição double n = 0, o 
que é uma contradição.Portanto, podemos assumir que n = S n' para algum n', 
e novamente pela definição de double temos S (S (double n')) = S (S (double 
m')), o que implica por injetividade que double n' = double m'. Instanciar 
a hipótese de indução com n' nos permite, portanto, concluir que n' = m', e 
segue-se imediatamente que S n' = S m'. Como S n' = n e S m' = m, isso é 
exatamente o que queríamos mostrar. ☐ *)


(**************** Reescrita com declarações condicionais *******************)

(* Suponha que queiramos mostrar que a adição é a inversa da subtração. Como 
estamos trabalhando com números naturais, precisamos de uma premissa para 
evitar que a subtração trunque seu resultado. Com essa premissa, a hipótese 
de indução se torna ∀ m, n' <=? m = true → (m - n') + n' = m. O início da 
prova usa técnicas que já vimos — em particular, note como fazemos indução 
em n antes de introduzir m, de modo que a hipótese de indução se torne 
suficientemente geral. *)

(* Auxiliares *)
Notation "x <=? y" := (Nat.leb x y) (at level 70) : nat_scope.
Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. Qed.

(* Lema que queremos demostrar *)
Lemma sub_add_leb : forall n m, n <=? m = true -> (m - n) + n = m.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - (* n = 0 *)
    intros m H. rewrite add_0_r. destruct m as [| m'].
    + (* m = 0 *)
      reflexivity.
    + (* m = S m' *)
      reflexivity.
  - (* n = S n' *)
    intros m H. destruct m as [| m'].
    + (* m = 0 *)
      discriminate.
    + (* m = S m' *)
      simpl in H. simpl. rewrite <- mais_n_Sm.

(* Neste ponto, precisamos mostrar S ((m' - n') + n') = S m' a partir da 
premissa (n' ≤ m') = true.  Poderíamos usar a tática assert para provar 
(m' - n') + n' = m' a partir da hipótese de indução. No entanto, também 
podemos apenas usar o rewrite diretamente: se fizermos uma reescrita com uma 
declaração condicional da forma P → a = b, o Rocq tentará reescrever com a = 
b e, em seguida, pedirá que provemos P em um novo subobjetivo. 
Se a declaração tiver mais de uma premissa, obteremos um subobjetivo para 
cada premissa. *)

   rewrite IHn'.
      ++ reflexivity.
      ++ apply H.
Qed.

(* Exercício *)
(* Prove isso por indução em l *)
Theorem enesimo_erro_apos_ultimo: forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.

Proof.
  intros n.
  induction n as [| n' IHn'].
  - intros X l H. destruct l as [| l'].
    + reflexivity.
    + simpl. discriminate.
  -  intros X l H. destruct l as [| l'].
    + simpl. discriminate.
    + simpl. 
    rewrite IHn'.
      ++ reflexivity.
      ++ simpl in H. injection H as H'. apply H'.
Qed.
         

(*************************** Expandindo Definições ************************)

(* Às vezes acontece de precisarmos expandir (unfold) manualmente um nome 
que foi introduzido por uma Definition, de modo que possamos manipular a 
expressão que ele representa.

Por exemplo, se definirmos... *)
Definition quadrado n := n * n.

(* ...e tentarmos provar um fato simples sobre o quadrado... *)
  Lemma quadrado_mult : forall n m, quadrado (n * m) = 
  quadrado n * quadrado m.

Proof.
  intros n m.
  simpl.

(* ...parecemos estar travados: o simpl não simplifica nada e, como não 
provamos nenhum outro fato sobre o quadrado, não há nada que possamos 
aplicar (apply) ou reescrever (rewrite).

Para avançar, podemos expandir manualmente a definição de quadrado: *)
unfold quadrado.

(* Agora temos bastante material para trabalhar: ambos os lados da igualdade 
são expressões envolvendo multiplicação, e temos vários fatos sobre a 
multiplicação à nossa disposição. Em particular, sabemos que ela é 
comutativa e associativa, e a partir disso não é difícil concluir a prova. *)
rewrite Nat.mul_assoc.
  assert (H : n * m  * n = n * n * m).
    { rewrite Nat.mul_comm. apply Nat.mul_assoc. }
  rewrite H. rewrite Nat.mul_assoc. reflexivity.
Qed.

(* Neste ponto, uma discussão um pouco mais aprofundada sobre a expansão 
a simplificação é oportuna.

Já observamos que táticas como simpl, reflexivity e apply frequentemente 
expandem as definições de funções automaticamente quando isso lhes permite 
avançar. Por exemplo, se definirmos foo m como a constante 5... *)
Definition foo (x: nat) := 5.

(* ... então a tática simpl na demonstração a seguir (ou a reflexivity, se 
omitir o simpl) vai expandir foo m para (fun x => 5) m e simplificar 
ainda mais essa expressão para apenas 5. *)
Fact fato_bobinho_1 : forall m, foo m + 1 = foo (m + 1) + 1.

Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

(* Mas essa expansão automática é um tanto conservadora. Por exemplo, se 
definirmos uma função um pouco mais complicada envolvendo um 
casamento de padrões... *)
Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

(* ...então a demonstração análoga ficará travada: *)
Fact fato_bobinho_2_FALHA : forall m, bar m + 1 = bar (m + 1) + 1.

Proof.
  intros m.
  simpl. (* Não faz nada! *)
Abort.

(* O motivo pelo qual o simpl não avança aqui é que ele percebe que, após 
expandir temporariamente bar m, ele fica com um match cujo escrutínio, m, é 
uma variável, de modo que o match não pode ser simplificado ainda mais. Ele 
não é inteligente o suficiente para notar que os dois ramos do match são 
idênticos, então ele desiste de expandir bar m e o deixa como está.

Da mesma forma, expandir temporariamente bar (m+1) deixa um match cujo 
escrutínio é uma aplicação de função (que por si só não pode ser 
simplificada, mesmo após expandir a definição de +), então o simpl o deixa 
como está.

Neste ponto, existem duas maneiras de progredir. Uma delas é usar destruct 
m para quebrar a demonstração em dois casos, cada um focando em uma escolha 
mais concreta de m (O vs S _). Em cada caso, o match dentro de bar agora 
pode progredir, e a demonstração é fácil de concluir. *)
Fact fato_bobinho_2 : forall m, bar m + 1 = bar (m + 1) + 1.

Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* Esta abordagem funciona, mas depende de reconhecermos que o match oculto 
dentro de bar era o que estava nos impedindo de avançar.

Um caminho mais direto é instruir explicitamente o Rocq a expandir bar. *)
Fact fato_bobinho_2' : forall m, bar m + 1 = bar (m + 1) + 1.

Proof.
  intros m.
  unfold bar.

(* Agora fica evidente que estamos travados nas expressões match em ambos 
os lados do =, e podemos usar o destruct para concluir a demonstração sem 
precisar pensar tanto. *)
 destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

(**************** Usando Destruct em Expressões Compostas ******************)

(* Já vimos muitos exemplos em que o destruct é usado para realizar uma 
análise de casos sobre o valor de alguma variável. Às vezes, precisamos 
raciocinar por casos com base no resultado de alguma expressão. Também 
podemos fazer isso com o destruct.

Aqui estão alguns exemplos: *)
Definition bobinhodivertido (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem bobinhodivertido_falso : forall (n : nat),
  bobinhodivertido n = false.

Proof.
  intros n. unfold bobinhodivertido.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity. Qed.

(* Após expandir bobinhodivertido na demonstração acima, descobrimos que 
estamos travados em if (n =? 3) then ... else .... Mas ou n é igual a 3 ou 
não é, então podemos usar destruct (eqb n 3) para nos permitir raciocinar 
sobre os dois casos.

Em geral, a tática destruct pode ser usada para realizar uma análise de 
casos sobre os resultados de computações arbitrárias. Se e for uma 
expressão cujo tipo é algum tipo indutivo T, então, para cada construtor c 
de T, destruct e gera um subobjetivo no qual todas as ocorrências de e 
(no objetivo e no contexto) são substituídas por c. *)

(* Exercício *)
(* Aqui está una implementação da função 'fatia' mencionada no capítulo de 
Polimorfismo:  *)
Fixpoint fatia {X Y : Type} (l : list (X * Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match fatia t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end. 

(* Prove que fatia e combine são inversos no seguinte sentido: *)
Theorem combine_fatia : forall X Y (l : list (X * Y)) l1 l2,
  fatia l = (l1, l2) ->
  combine l1 l2 = l.

Proof.
  intros X Y l.
  induction l as [| h t IH].
- (* l = [] *)
  intros l1 l2 H.
  injection H as H1 H2.
  rewrite <- H1. rewrite <- H2. reflexivity.
- (* l = h :: t *)
   intros l1 l2 H.
   destruct h as [a b].
   simpl in H.
   destruct (fatia t) as [t1 t2] eqn:E.
   injection H as H1 H2.
    rewrite <- H1. rewrite <- H2.
    simpl.
    rewrite -> IH.
    + reflexivity.
    + reflexivity.
Qed.

(* A parte eqn: da tática destruct é opcional; embora tenhamos escolhido 
incluí-la na maioria das vezes, por questão de documentação, ela geralmente 
pode ser omitida sem prejuízo.

Um exemplo em que ela não pode ser omitida é quando estamos fazendo o 
destruct de expressões compostas; aqui, a informação gravada pelo eqn: pode 
ser de fato crítica e, se a omitirmos, o destruct poderá apagar informações 
de que precisamos para concluir uma demonstração. Por exemplo, suponha que 
definamos uma função bobinhodivertido1 assim: *)
Definition bobinhodivertido1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

(* Agora suponha que queremos convencer o Rocq de que bobinhodivertido1 n 
produz true apenas quando n é ímpar. Se começarmos a prova assim 
(sem o eqn: no destruct): *)
Theorem bobinhodivertido1_impar_FALHA : forall (n : nat),
  bobinhodivertido1 n = true ->
  Nat.odd n = true.

Proof.
  intros n eq. unfold bobinhodivertido1 in eq.
  destruct (n =? 3).
  (* ficamos presos... *)
Abort.

(* ... então ficamos travados neste ponto porque o contexto não contém 
informações suficientes para provar o objetivo! O problema é que a 
substituição realizada pelo destruct é bastante brutal — neste caso, ele 
joga fora todas as ocorrências de n =? 3, mas precisamos manter alguma 
memória dessa expressão e de como ela foi destruturada, porque precisamos 
ser capazes de raciocinar que, uma vez que estamos assumindo n =? 3 = true 
neste ramo da análise de casos, deve ser o caso de que n = 3, do qual 
decorre que n é ímpar. 

O que queremos aqui é substituir todas as ocorrências existentes de n =? 3, 
mas ao mesmo tempo adicionar uma equação ao contexto que registre em qual 
caso estamos. É exatamente isso que o modificador eqn: faz. *)
Theorem bobinhodivertido1_impar : forall (n : nat),
  bobinhodivertido1 n = true ->
  Nat.odd n = true.

Proof.
  intros n eq. unfold bobinhodivertido1 in eq.
  destruct (n =? 3) eqn:Heqe3.

(* Agora estamos no mesmo estado do ponto em que ficamos travados acima, 
exceto que o contexto contém uma suposição de igualdade extra, que é 
exatamente o que precisamos para avançar. *)

    - (* e3 = true *) apply eqb_true with (n := n) (m := 5) in Heqe3.
      rewrite -> Heqe3. reflexivity.
    - (* e3 = false *)

(* Quando chegamos ao segundo teste de igualdade no corpo da função sobre 
a qual estamos raciocinando, podemos usar o eqn: novamente da mesma forma, 
permitindo-nos concluir a demonstração. *)
    destruct (n =? 5) eqn:Heqe5.
        + (* e5 = true *)
          apply eqb_true with (n := n) (m := 5) in Heqe5.
          rewrite -> Heqe5. reflexivity.
        + (* e5 = false *) discriminate eq. Qed.

(* Exercício *)
Theorem bool_fn_aplicada_tres_vezes :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.

Proof.
  intros f b. 
  destruct b.
  destruct (f true) eqn:E1.
  - rewrite E1. rewrite E1. reflexivity.
  - destruct (f false) eqn:E2.
    + apply E1.
    + apply E2.
  - destruct (f false) eqn:E3.
    + destruct (f true) eqn:E4.
      ++ apply E4.
      ++ apply E3.
    + rewrite E3. apply E3. 
Qed.
  
(********************************** Revisão *******************************)
(* Já falamos sobre muitas das táticas mais fundamentais do Rocq. 
Vamos introduzir mais algumas nos próximos capítulos e, mais adiante, 
veremos algumas táticas de automação mais poderosas que fazem com que o 
Rocq nos ajude com detalhes de baixo nível. Mas, basicamente, já temos o 
que precisamos para realizar o trabalho. Aqui estão as que já vimos:

- intros: move hipóteses/variáveis da meta para o contexto.
- reflexivity: finaliza a prova (quando a meta se parece com e = e).
- apply: prova a meta usando uma hipótese, lema ou construtor.
- apply... in H: aplica uma hipótese, lema ou construtor a uma hipótese no 
contexto (raciocínio para a frente).
- apply... with...: especifica explicitamente valores para variáveis que 
não podem ser determinados por casamento de padrão (pattern matching).
- specialize (H ...): refinaria uma hipótese fixando algumas de suas 
variáveis.
- simpl: simplifica computações na meta.
- simpl in H: ... ou em uma hipótese.
- rewrite: usa uma hipótese de igualdade (ou lema) para reescrever a meta.
- rewrite ... in H: ... ou em uma hipótese.
- symmetry: altera uma meta da forma t = u para u = t.
- symmetry in H: altera uma hipótese da forma t = u para u = t.
- transitivity y: prova uma meta x = z provando duas novas submetas: x = y 
e y = z.
- unfold: substitui uma constante definida pelo seu lado direito na meta.
- unfold... in H: ... ou em uma hipótese.
- destruct... as...: análise de casos sobre valores de tipos definidos 
indutivamente.
- destruct... eqn:...: especifica o nome de uma equação a ser adicionada 
ao contexto, registrando o resultado da análise de casos.
- induction... as...: indução sobre valores de tipos definidos 
indutivamente.
- injection... as...: raciocina por injetividade em igualdades entre 
valores de tipos definidos indutivamente.
- discriminate: raciocina pela disjunção de construtores em igualdades 
entre valores de tipos definidos indutivamente.
- replace x with y: substitui x por y em todos os lugares da meta atual, 
criando uma submeta de que x = y.
- assert (H: e) (ou assert (e) as H): introduz um lema local 'e' e o chama 
de H.
- generalize dependent x: move a variável x (e qualquer outra coisa que 
dependa dela) do contexto de volta para uma hipótese explícita na fórmula 
da meta.
- f_equal: transforma uma meta da forma f x = f y em x = y. *)

(************************* Exercícios Adicionais **************************)
Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).

Proof.
  intros n m.
  destruct n.
  - reflexivity.
  - reflexivity.
Qed.

(* Dê uma prova informal deste lema que corresponda à sua prova formal 
acima:

Teorema: Para quaisquer naturais n m, (n =? m) = (m =? n).

Prova: 

Fazemo análise de casos em n.
Caso 1 (n = 0): Queremos provar que (0 =? m) = 
(m =? 0). Como o Rocq avalia computacionalmente a função de igualdade 
estrutural com base nos argumentos, ao substituir n por 0, a expressão se 
simplifica diretamente para uma identidade booleana (false = false), que é 
trivialmente verdadeira por reflexividade.
Caso 2 (n = S n'): Queremos provar que (S n' =? m) = (m =? S n'). Da mesma 
forma, substituindo o construtor do sucessor e avaliando a função de 
comparação em ambos os lados, a equação se reduz a uma igualdade de valores 
booleanos idênticos (false = false), sendo imediatamente resolvida. 
Portanto, em ambos os casos, a igualdade é válida. *)

(* Exercício *)
Theorem eqb_trans : forall (n m p : nat),
  n =? m = true ->
  m =? p = true ->
  n =? p = true.

Proof.
  intros n m p H1 H2.
  induction n as [| n' IHn'].
  - discriminate H1.
  - discriminate H1.
Qed.
  
(* Exercício *)
Theorem filter_exercicio : forall (X : Type) (test : X -> bool)
                                 (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true.

Proof.
  intros X test x l lf H.
  unfold filter in H.
  induction l as [| h t IHl].
  - discriminate H.
  - destruct (test h) eqn:E.
    + injection H as H1 H2. rewrite H1 in E. apply E.
    + apply IHl in H. apply H.
Qed.

(* Defina dois Fixpoints recursivos, paratodob e existeb. O primeiro 
verifica se cada elemento em uma lista satisfaz um dado predicado:

    paratodob impar [1;3;5;7;9] = true

    paratodob negb [false;false] = true

    paratodob par [0;2;4;5] = false

    paratodob (eqb 5) [] = true

O segundo verifica se existe algum elemento na lista que satisfaz um dado 
predicado:

    existeb (eqb 5) [0;2;3;6] = false

    existeb (andb true) [true;true;false] = true

    existeb impar [1;0;0;0;0;3] = true

    existeb par [] = false

Em seguida, defina uma versão não recursiva de existsb — chame-a de 
existeb' — usando paratodob e negb.

Por fim, prove um teorema existeb_existeb' afirmando que existeb' e existeb 
têm o mesmo comportamento. *)

Fixpoint paratodob {X : Type}(teste: X -> bool)(l : list X) : bool :=
   match l with
   | [] => true
   | h :: t => andb (teste h) (paratodob teste t)
   end.

Example teste_paratodob_1 : paratodob Nat.odd [1;3;5;7;9] = true.
Proof. 
reflexivity. Qed.

Example teste_paratodob_2 : paratodob negb [false;false] = true.
Proof.
reflexivity. Qed.

Example teste_paratodob_3 : paratodob Nat.even [0;2;4;5] = false.
Proof.
reflexivity. Qed.

Fixpoint existeb {X : Type}(teste : X -> bool)(l : list X) : bool :=
   match l with
   | [] => false
   | h :: t => orb (teste h) (existeb teste t)
   end.

Example teste_existeb_1 : existeb (Nat.eqb 5) [0;2;3;6] = false.
Proof.
reflexivity. Qed.

Example test_existeb_2 : existeb (andb true) [true;true;false] = true.
Proof.
reflexivity. Qed.

Example teste_existeb_3 : existeb Nat.odd [1;0;0;0;0;3] = true.
Proof.
reflexivity. Qed.

Example teste_existeb_4 : existeb Nat.even [] = false.
Proof.
reflexivity. Qed.

Definition existeb' {X : Type} (teste : X -> bool) (l : list X) : bool :=
  negb (paratodob (fun x => negb (teste x)) l).

Theorem existeb_existeb' : forall (X : Type) (teste : X -> bool) (l : list X),
  existeb teste l = existeb' teste l.

Proof.
  intros X teste l.
  induction l as [| h t IHl].
  - reflexivity.
  - simpl. rewrite IHl. destruct (teste h) eqn:E.
    + simpl. unfold existeb'. simpl. rewrite E. reflexivity.
    + simpl. unfold existeb'. simpl. rewrite E. reflexivity.
Qed.