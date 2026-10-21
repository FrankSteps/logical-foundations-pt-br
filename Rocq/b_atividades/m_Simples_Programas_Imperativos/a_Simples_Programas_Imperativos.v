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