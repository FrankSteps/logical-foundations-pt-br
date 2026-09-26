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