(* MAPAS *)
(* MAPAS TOTAIS E PARCIAIS *)

(* Mapas (ou dicionários) são estruturas de dados onipresentes tanto na programação 
comum quanto na teoria de linguagens de programação; vamos precisar deles em vários 
lugares nos próximos capítulos.

Eles também servem como um ótimo estudo de caso usando ideias que vimos em capítulos 
anteriores, incluindo a construção de estruturas de dados a partir de funções de alta 
ordem (de Básico e Polimorfismo) e o uso de reflexão para otimizar provas (de IndProp).

Definiremos dois tipos de mapas: mapas totais, que incluem um elemento ''padrão'' a ser 
retornado quando a chave buscada não existe, e mapas parciais, que em vez disso 
retornam uma opção para indicar sucesso ou falha. Os mapas parciais são definidos em 
termos de mapas totais, usando None como o elemento padrão. *)

(******************************* A Biblioteca Padrão *********************************)

(* Um pequeno desvio antes de começarmos... 

Ao contrário dos capítulos que vimos até agora, este não requer a importação do capítulo 
anterior (ou, de forma transitiva, de todos os capítulos anteriores). Em vez disso, 
neste capítulo e daqui em diante, vamos importar as definições e teoremas de que 
precisamos diretamente da biblioteca padrão do Rocq. Você não deve notar muita 
diferença, no entanto, porque fomos cuidadosos para nomear nossas próprias definições e 
sempre que se sobrepõem, com os mesmos nomes de suas contrapartes na biblioteca padrão. *)

From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Export Strings.String.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import List.
Import ListNotations.

(* A documentação da biblioteca padrão pode ser encontrada em 
https://rocq-prover.org/doc/V9.0.0/stdlib/index.html.

O comando Search é uma boa maneira de procurar por teoremas envolvendo objetos de tipos 
específicos. Consulte Listas para relembrar como usá-lo.

Se você quiser descobrir como ou onde uma notação é definida, o comando Locate é útil. 
Por exemplo, onde a operação de adição natural é definida na biblioteca padrão? *)

Locate "+".

(* (Há vários usos da notação +, mas apenas um para os números naturais.) *)

Print Init.Nat.add.

(* Veremos mais alguns usos de Locate no capítulo Imp. *)

(*********************************** Identificadores **********************************)

(* Para definir mapas, primeiro precisamos de um tipo para as chaves que usaremos para 
indexar nossos mapas. No Lists.v, introduzimos um novo tipo id para um propósito 
semelhante; aqui e para o restante de Software Foundations, usaremos o tipo string da 
biblioteca padrão do Rocq. Para comparar strings, usamos a função eqb_refl do módulo 
String na biblioteca padrão. *)

Check String.eqb_refl :
  forall x : string, (x =? x)%string = true.

(* Frequentemente usaremos algumas propriedades básicas da igualdade de strings... *)

Check String.eqb_eq :
  forall n m : string, (n =? m)%string = true <-> n = m.
Check String.eqb_neq :
  forall n m : string, (n =? m)%string = false <-> n <> m.
Check String.eqb_spec :
  forall x y : string, reflect (x = y) (String.eqb x y).

(************************************* Mapas Totais ***********************************)

(* O nosso principal trabalho neste capítulo será construir uma definição de mapas 
parciais que seja semelhante em comportamento àquela que vimos no capítulo de Listas, 
com os respectivos lemas sobre o seu comportamento. 

Desta vez, no entanto, vamos usar funções, em vez de listas de pares chave-valor, para 
construir os mapas. A vantagem dessa representação é que ela oferece uma visão mais 
''extensional'' dos mapas: dois mapas que respondem a consultas da mesma forma serão 
representados exatamente como a mesma função, em vez de apenas como estruturas de listas 
''equivalentes''. Isso simplifica as demonstrações que utilizam mapas.

Construímos o conceito de mapas parciais em duas etapas. Primeiro, definimos um tipo de 
mapas totais que retornam um valor padrão quando consultamos uma chave que não está 
presente no mapa. *)

Definition mapa_total (A : Type) := string -> A.

(* Intuitivamente, um mapa total sobre um tipo de elemento A é apenas uma função que pode 
ser usada para consultar strings, resultando em As. 

A função t_vazia gera um mapa total vazio, dado um elemento padrão; esse mapa sempre 
retorna o elemento padrão quando aplicado a qualquer string. *)

Definition t_vazia {A : Type} (v : A) : mapa_total A :=
  (fun _ => v).

(* Mais interessante é a função de atualização de mapa que, (como sempre) recebe um mapa m, 
uma chave x e um valor v, e retorna um novo mapa que mapeia x para v e mapeia qualquer 
outra chave para o que m já mapeava. A novidade aqui é que alcançamos esse efeito 
envolvendo uma nova função ao redor da antiga. *)

Definition t_atualiza {A : Type} (m : mapa_total A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

(* Esta definição é um belo exemplo de programação de ordem superior: t_atualiza recebe 
uma função m e gera uma nova função fun x' => ... que se comporta como o mapa desejado. 

Por exemplo, podemos construir um mapa que mapeia strings para booleanos (bools), onde 
''foo'' e ''bar'' são mapeados para verdadeiro (true) e qualquer outra chave é mapeada 
para falso (false), assim: *)

Definition mapaexemplo :=
  t_atualiza (t_atualiza (t_vazia false) "foo" true)
           "bar" true.
      
(* Em seguida, vamos introduzir algumas notações para facilitar o trabalho com mapas. 
Primeiro, usamos a seguinte notação para representar um mapa total vazio com um valor 
padrão. *)

Notation "'__' '!->' v" := (t_vazia v)
  (at level 100, right associativity).

Example examplo_vazio := ( false).

(* A seguir, introduzimos uma notação simbólica para estender um mapa existente com uma 
nova associação (binding).*)

Notation "x '!->' v ';' m" := (t_atualiza m x v)
                                (at level 100, v constr at level 100, right associativity).

(* O mapa de exemplo acima agora pode ser definido da seguinte forma: *)

Definition mapaexemplo' :=
  ( "bar" !-> true;
    "foo" !-> true;
    __ !-> false
  ).

(* Isto conclui a definição de mapas totais. Note que não precisamos definir uma operação 
de busca (find) nesta representação de mapas porque ela é simplesmente a aplicação de função!

Quando usarmos mapas em capítulos futuros, precisaremos de vários fatos fundamentais 
sobre como eles se comportam. 

Mesmo que você não faça os exercícios a seguir, certifique-se de compreender 
profundamente os enunciados dos lemas! 

(Algumas das provas exigem o axioma da extensionalidade funcional, que foi discutido no 
capítulo de Lógica). *)

(* Exercício *)
(* Primeiro, o mapa vazio retorna seu elemento padrão para todas as chaves: *)

Lemma t_aplicando_vazia : forall (A : Type) (x : string) (v : A),
  (__ !-> v) x = v.
Proof.  
  intros A x v.
  unfold t_vazia. reflexivity.
Qed.

(* A seguir, se atualizarmos um mapa m em uma chave x com um novo valor v e depois 
consultarmos x no mapa resultante da atualização, obteremos v de volta: *)

Lemma t_atualiza_eq : forall (A : Type) (m : mapa_total A) x v,
  (x !-> v ; m) x = v.
Proof.
  intros A m x v.
  unfold t_atualiza.
  rewrite eqb_refl.
  reflexivity.
Qed. 

(* Por outro lado, se atualizarmos um mapa m na chave x1 e depois consultarmos uma chave 
diferente x2 no mapa resultante, obtemos o mesmo resultado que m teria fornecido *)

Theorem t_atualiza_neq : forall (A : Type) (m : mapa_total A) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.
Proof.
  intros A m x1 x2 v H.
  unfold t_atualiza. 
  rewrite <- eqb_neq in H.
  rewrite H. reflexivity.
Qed. 

(* Se atualizarmos um mapa m na chave x com um valor v1 e depois atualizarmos novamente 
com a mesma chave x e outro valor v2, o mapa resultante comporta-se da mesma forma 
(fornece o mesmo resultado ao ser aplicado a qualquer chave) que o mapa mais simples 
obtido ao realizar apenas a segunda atualização sobre m: *)

Lemma t_atualiza_ofusca : forall (A : Type) (m : mapa_total A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros A m x v1 v2.
  apply functional_extensionality. intros y.
  destruct (eqb_spec x y) as [H | H].
  - rewrite H. rewrite t_atualiza_eq.
   symmetry. apply t_atualiza_eq.
  - rewrite t_atualiza_neq.
    + rewrite (t_atualiza_neq A m x y v1 H).
      symmetry. apply (t_atualiza_neq A m x y v2).
      apply H.
    + apply H.
Qed.  
   
(* Dadas as strings x1 e x2, podemos usar a tática destruct (eqb_spec x1 x2) para realizar 
simultaneamente uma análise de casos sobre o resultado de String.eqb x1 x2 e gerar hipóteses 
sobre a igualdade (no sentido de =) de x1 e x2. Tendo o exemplo no capítulo IndProp como 
modelo, use String.eqb_spec para provar o seguinte teorema, que afirma que se atualizarmos 
um mapa para atribuir à chave x o mesmo valor que ela já possui em m, então o resultado é 
igual a m: *)

Theorem t_atualiza_igual : forall (A : Type) (m : mapa_total A) x,
  (x !-> m x ; m) = m.
Proof.
  intros A m x.
  apply functional_extensionality.
  intros y. destruct (eqb_spec x y) as [H | H].
  - rewrite H. apply t_atualiza_eq.
  - rewrite t_atualiza_neq.
    + reflexivity.
    + apply H.
Qed.

(* Similarmente, use String.eqb_spec para provar uma última propriedade da função update: se 
atualizarmos um mapa m em duas chaves distintas, não importa a ordem em que fazemos as 
atualizações. *)
Theorem t_atualiza_permuta : forall (A : Type) (m : mapa_total A)
                                  v1 v2 x1 x2,
  x2 <> x1 ->
  (x1 !-> v1 ; x2 !-> v2 ; m)
  =
  (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros A m v1 v2 x1 x2 H.
  (* dois mapas são iguais se concordam em todo ponto y *)
  apply functional_extensionality.
  intros y. unfold t_atualiza.
  destruct (eqb_spec x1 y) as [E1 | E1].
  - destruct (eqb_spec x2 y) as [E2 | E2].
    + (* x1 = y e x2 = y: então x2 = x1, o que contradiz H *)
      rewrite E1, E2 in H. destruct H as [ ].
      reflexivity.
    + (* x1 = y e x2 <> y: os dois lados devolvem v1 *)
      reflexivity.
  - destruct (eqb_spec x2 y) as [E2 | E2].
    + (* x1 <> y e x2 = y: os dois lados devolvem v2 *)
      reflexivity.
    + (* x1 <> y e x2 <> y: os dois lados caem em m y *)
      reflexivity.
Qed.
  
(*************************************** Mapas Parciais ***********************************)

(* Por fim, definimos mapas parciais sobre mapas totais. Um mapa parcial com elementos do 
tipo A é simplesmente um mapa total com elementos do tipo option A e elemento padrão None. *)

Definition mapa_parcial (A : Type) := mapa_total (option A).

Definition vazia {A : Type} : mapa_parcial A :=
  t_vazia None.

Definition atualiza {A : Type} (m : mapa_parcial A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

(* Apresentamos uma notação semelhante para mapas parciais: *)

Notation "x '⊢>' v ';' m" := (atualiza m x v)
  (at level 0, x constr, v at level 200, right associativity).

(* Também podemos ocultar o último caso quando ele for vazio. *)

Notation "x '⊢>' v" := (atualiza vazia x v)
  (at level 0, x constr, v at level 200).

Definition exemplomapa :=
  ("Church" ⊢> true ; "Turing" ⊢> false).

(* Agora estendemos diretamente todos os lemas básicos sobre mapas totais para mapas 
parciais. *)

Lemma aplica_vazia : forall (A : Type) (x : string),
  @vazia A x = None.
Proof.
  intros. unfold vazia. rewrite t_aplicando_vazia.
  reflexivity.
Qed.

Lemma atualiza_eq : forall (A : Type) (m : mapa_parcial A) x v,
  (x ⊢> v ; m) x = Some v.
Proof.
  intros. unfold atualiza. rewrite t_atualiza_eq.
  reflexivity.
Qed.

(* O lema atualiza_eq é utilizado com muita frequência em demonstrações. Adicioná-lo 
à 'base de dicas' (hint database) global do Rocq permite que táticas de automação de
provas, como o auto, o encontrem.*)

#[global] Hint Resolve atualiza_eq : core.

Theorem atualiza_neq : forall (A : Type) (m : mapa_parcial A) x1 x2 v,
  x2 <> x1 ->
  (x2 ⊢> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold atualiza. rewrite t_atualiza_neq.
  - reflexivity.
  - apply H.
Qed.

Lemma atualiza_ofusca : forall (A : Type) (m : mapa_parcial A) x v1 v2,
  (x ⊢> v2 ; x ⊢> v1 ; m) = (x ⊢> v2 ; m).
Proof.
  intros A m x v1 v2. unfold atualiza. rewrite t_atualiza_ofusca.
  reflexivity.
Qed.

Theorem atualiza_igual : forall (A : Type) (m : mapa_parcial A) x v,
  m x = Some v ->
  (x ⊢> v ; m) = m.
Proof.
  intros A m x v H. unfold atualiza. rewrite <- H.
  apply t_atualiza_igual.
Qed.

Theorem atualiza_permuta : forall (A : Type) (m : mapa_parcial A)
                                x1 x2 v1 v2,
  x2 <> x1 ->
  (x1 ⊢> v1 ; x2 ⊢> v2 ; m) = (x2 ⊢> v2 ; x1 ⊢> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold atualiza.
  apply t_atualiza_permuta.
Qed.

(* Para finalizar: Para mapas parciais, é conveniente introduzir uma noção de inclusão de 
mapas, afirmando que todas as entradas em um mapa também estão presentes em outro: *)

Definition incluiem {A : Type} (m m' : mapa_parcial A) :=
  forall x v, m x = Some v -> m' x = Some v.

(* Podemos então mostrar que a atualização de mapas preserva a inclusão de mapas, isto é: *)

Lemma incluiem_atualiza : forall (A : Type) (m m' : mapa_parcial A)
                                 (x : string) (vx : A),
  incluiem m m' ->
  incluiem (x ⊢> vx ; m) (x ⊢> vx ; m').
Proof.
  unfold incluiem.
  intros A m m' x vx H.
  intros y vy.
  destruct (eqb_spec x y) as [Hxy | Hxy].
  - rewrite Hxy.
    rewrite atualiza_eq. rewrite atualiza_eq. intro H1. apply H1.
  - rewrite atualiza_neq.
    + rewrite atualiza_neq.
      * apply H.
      * apply Hxy.
    + apply Hxy.
Qed.

(* Esta propriedade é bastante útil para o raciocínio sobre linguagens com ligação de 
variáveis -- por exemplo, o Cálculo Lambda Simplesmente Tipado, que veremos em 
Fundamentação de Linguagens de Programação (Programming Language Foundations), onde os 
mapas são usados para rastrear quais variáveis de programa estão definidas em um dado
escopo.*)