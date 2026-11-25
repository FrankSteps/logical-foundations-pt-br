(* ImpCEvalFun *)

(* Uma Função de Avaliação para Imp*)

(* Vimos no capítulo sobre Imp como uma abordagem ingênua para definir uma função que 
represente a avaliação de Imp esbarra em dificuldades. Lá, adotamos a solução de mudar de 
uma definição funcional para uma definição relacional de avaliação. Neste capítulo opcional, 
consideramos estratégias para fazer a abordagem funcional funcionar. *)

(******************************* Um Avaliador com Defeito **********************************)

Set Warnings "-notation-overridden,-notation-incompatible-prefix".
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
Import Nat.
From Stdlib Require Import EqNat.
Require Import LFPTBR.m_Simples_Programas_Imperativos.a_Simples_Programas_Imperativos.
Require Import LFPTBR.h_Mapas_Totais_e_Parciais.a_Mapas_Totais_e_Parciais.
Local Open Scope com_scope.

(* Aqui está a nossa primeira tentativa de uma função de avaliação para comandos, omitindo o 
while. *)

Fixpoint ceval_step1 (st : estado) (c : com) : estado :=
  match c with
    | <{ skip }> =>
        st
    | <{ l := a1 }> =>
        (l !-> aeval st a1 ; st)
    | <{ c1 ; c2 }> =>
        let st' := ceval_step1 st c1 in
        ceval_step1 st' c2
    | <{ if b then c1 else c2 end }> =>
        if (beval st b)
          then ceval_step1 st c1
          else ceval_step1 st c2
    | <{ while b1 do c1 end }> =>
        st (* provisório *)
  end.

(* Como observamos no capítulo Imp, em uma linguagem de programação funcional tradicional 
como ML ou Haskell, poderíamos escrever o caso do while da seguinte forma: 

          | while b1 do c1 end =>
              if (beval st b1) then
                ceval_step1 st <{ c1; while b1 do c1 end }>
              else st 
        
O Rocq não aceita essa definição (Error: Cannot guess decreasing argument of fix — Erro: Não 
é possível deduzir o argumento decrescente de fix) porque não há garantia de que a função que 
queremos definir irá terminar. De fato, a função ceval_step1 modificada, quando aplicada ao 
programa loop de Imp.v, nunca terminaria. Como o Rocq não é apenas uma linguagem de 
programação funcional, mas também uma lógica consistente, qualquer função que potencialmente 
não termine precisa ser rejeitada. Aqui está um programa Rocq inválido(!) que mostra o que 
daria errado se o Rocq permitisse funções recursivas que não terminam:  

          Fixpoint loop_false (n : nat) : False := loop_false n.
        
Ou seja, proposições como False se tornariam demonstráveis (por exemplo, loop_false 0 seria uma 
prova de False), o que seria um desastre para a consistência lógica do Rocq.

Portanto, como não termina para todas as entradas, a versão completa de ceval_step1 não 
pode ser escrita no Rocq — pelo menos não sem um truque adicional... *)

(**************************** Um Avaliador Indexado por Passos *****************************)

(* O truque de que precisamos é passar um parâmetro adicional para a função de avaliação que 
diga por quanto tempo ela deve executar. Informalmente, iniciamos o avaliador com uma certa 
quantidade de ''combustível'' em seu tanque e permitimos que ele execute até que termine da 
maneira habitual ou fique sem combustível — ponto em que simplesmente paramos a avaliação e 
dizemos que o resultado final é a memória vazia. (Também poderíamos dizer que o resultado é o 
estado atual no momento em que o avaliador fica sem combustível — isso realmente não importa, 
porque o resultado estará errado de qualquer maneira!) *)

Fixpoint ceval_step2 (st : estado) (c : com) (i : nat) : estado :=
  match i with
  | O => empty_st
  | S i' =>
    match c with
      | <{ skip }> =>
          st
      | <{ l := a1 }> =>
          (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i'
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step2 st c1 i'
            else ceval_step2 st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then let st' := ceval_step2 st c1 i' in
               ceval_step2 st' c i'
          else st
    end
  end.

(* Nota: É tentador pensar que o índice i aqui está contando o ''número de passos de 
avaliação''. Mas, se você observar com atenção, verá que esse não é o caso: por exemplo, na 
regra de sequenciamento, o mesmo i é passado para ambas as chamadas recursivas. Entender a 
maneira exata como i é tratado será importante na demonstração de ceval__ceval_step, que é 
dada como exercício abaixo.

Uma coisa que não é tão boa nesse avaliador é que não conseguimos saber, a partir do seu 
resultado, se ele parou porque o programa terminou normalmente ou porque ficou sem 
combustível. Nossa próxima versão retorna um option state em vez de apenas um state, para 
que possamos distinguir entre o término normal e o anormal. *)

Fixpoint ceval_step3 (st : estado) (c : com) (i : nat)
                    : option estado :=
  match i with
  | O => None
  | S i' =>
    match c with
      | <{ skip }> =>
          Some st
      | <{ l := a1 }> =>
          Some (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None => None
          end
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step3 st c1 i'
            else ceval_step3 st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then match (ceval_step3 st c1 i') with
               | Some st' => ceval_step3 st' c i'
               | None => None
               end
          else Some st
    end
  end.

(* Podemos tornar esta versão mais legível introduzindo uma notação auxiliar simples para 
esconder a repetição de verificações (matching) em estados opcionais. *)

Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

Fixpoint ceval_step (st : estado) (c : com) (i : nat)
                    : option estado :=
  match i with
  | O => None
  | S i' =>
    match c with
      | <{ skip }> =>
          Some st
      | <{ l := a1 }> =>
          Some (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.

Definition test_ceval (st:estado) (c:com) :=
  match ceval_step st c 500 with
  | None => None
  | Some st => Some (st X, st Y, st Z)
  end.

Example example_test_ceval :
     test_ceval empty_st

     <{ X := 2;
        if (X <= 1)
        then Y := 3
        else Z := 4
        end }>

     = Some (2, 0, 4).
Proof. reflexivity. Qed.

(* Exerício *)
(* Escreva um programa em Imp que some os números de 1 até X (inclusive — ou seja, 1 + 2 + 
... + X) na variável Y. Certifique-se de que a sua solução passe no teste que vem a seguir. *)

Definition pup_to_n : com :=
  <{ Y := 0;
     while (X > 0) do
     Y := X + Y;
     X := X - 1 end
  }>.

Example pup_to_n_1 :
  test_ceval (X !-> 5) pup_to_n
  = Some (0, 15, 0).
Proof.
  reflexivity. Qed.

(* Escreva um programa em Imp que defina Z como 0 se X for par e defina Z como 1 caso 
contrário. Use test_ceval para testar o seu programa. *)


Definition imp_z_zero_one : com :=
  <{ Y := X;
     while Y > 1 do
       Y := Y - 2
     end;
     if Y = 0 then
       Z := 0
     else
       Z := 1
     end
  }>.

Example test_imp_z_zero_one_1 :
  test_ceval (X !-> 5) imp_z_zero_one =
  Some (5, 1, 1).
Proof.
 reflexivity. Qed.

Example test_imp_z_zero_one_2 :
  test_ceval (X !-> 6) imp_z_zero_one =
  Some (6, 0, 0).
Proof.
  reflexivity. Qed.

Example test_imp_z_zero_one_3 :
  test_ceval (X !-> 2000) imp_z_zero_one =
  None.
Proof.
  reflexivity. Qed.

(****************** Avaliação Relacional vs. Avaliação Indexada por Passos *****************)

(* Assim como ocorre com as expressões aritméticas e booleanas, esperamos que as duas 
definições alternativas de avaliação acabem dando no mesmo (sejam equivalentes no fim das 
contas). Esta seção mostra que é exatamente isso que acontece. *)

Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      st =[ c ]=> st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].
  - (* i = 0 -- contraditorio *)
    intros c st st' H. discriminate H.
  - (* i = S i' *)
    intros c st st' H.
    destruct c;
           simpl in H; inversion H; subst; clear H.
      + (* skip *) apply E_Skip.
      + (* := *) apply E_Asgn. reflexivity.
      + (* ; *)
        destruct (ceval_step st c1 i') eqn:Heqr1.
        * (* Avaliacao de c1 termina normalmente com estado e *)
          apply E_Seq with e.
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. assumption.
        * (* caso contrario -- contradicao *)
          discriminate H1.
      + (* if *)
        destruct (beval st b) eqn:Heqr.
        * (* b = true *)
          apply E_IfTrue. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
        * (* b = false *)
          apply E_IfFalse. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
      + (* while *) destruct (beval st b) eqn :Heqr.
        * (* b = true *)
         destruct (ceval_step st c i') eqn:Heqr1.
         { (* b1 = Some e *)
           apply E_WhileTrue with e. rewrite Heqr.
           reflexivity.
           apply IHi'. rewrite Heqr1. reflexivity.
           apply IHi'. assumption. }
         { (* b1 = None *) discriminate H1. }
        * (* b = false *)
          injection H1 as H2. rewrite <- H2.
          apply E_WhileFalse. apply Heqr. Qed.

(* Exercício *)
(* Escreva uma prova informal de ceval_step__ceval, seguindo o modelo habitual. (O modelo 
para análise de casos sobre um valor definido indutivamente deve se parecer com o de indução, 
exceto por não haver hipótese de indução.) Faça com que a sua prova comunique as ideias 
principais a um leitor humano; não se limite a transcrever os passos da prova formal. *)

(* Teorema: Para todos os comandos c e estados st, st', se existe um número i tal que 
            ceval_step st c i = Some st', então st =[ c ]=> st'.
            
   - Prova: Sejam c, st e st' arbitrários e suponha que exista i tal que ceval_step st c i = 
     Some st'. Provamos por indução em i que, para quaisquer c, st e st', se 
     ceval_step st c i = Some st', então st =[ c ]=> st'.
   
  - Suponha i = 0. Pela definição de ceval_step, avaliar qualquer comando com 0 passos 
    resulta em None, o que contradiz ceval_step st c 0 = Some st'.
    
  - Suponha i = S i', onde a hipótese de indução afirma que, para quaisquer c₀, st₀ e st₀', 
    se ceval_step st₀ c₀ i' = Some st₀', então st₀ =[ c₀ ]=> st₀'. Fazemos análise de casos 
    sobre c (sem hipóteses de indução adicionais sobre os subcomandos):
    
      - Suponha c = skip. Então ceval_step st skip (S i') = Some st, o que exige st' = st. 
        Por E_Skip, segue que st =[ skip ]=> st'.
        
      - Suponha c = (x := a). Para o resultado ser Some st', ceval_step avalia a no estado 
        st e produz st' = (x !-> aeval st a; st). Pela regra E_Asgn, temos 
        st =[ x := a ]=> st'.
        
      - Suponha c = (c1; c2). Para obter Some st', a execução de c1 em i' passos deve 
        terminar com algum estado intermediário e (pois, se retornasse None, a sequência 
        inteira falharia), e em seguida c2 deve avaliar de e até st' em i' passos. 
        Aplicando a hipótese de indução a c1 (de st a e) e a c2 (de e a st'), obtemos 
        st =[ c1 ]=> e e também e =[ c2 ]=> st'. Pela regra E_Seq, concluímos que 
        st =[ c1; c2 ]=> st'.
        
      - Suponha c = if b then c1 else c2. Devemos mostrar st =[ if b then c1 else c2 ]=> st'. 
        Analisamos o valor de beval st b:
        
          - Se beval st b = true, então ceval_step prossegue avaliando c1 em i' passos até 
            Some st'. Pela hipótese de indução, st =[ c1 ]=> st', e pela regra E_IfTrue segue 
            st =[ if b then c1 else c2 ]=> st'.
            
          - Se beval st b = false, então ceval_step avalia c2 em i' passos até Some st'. Pela 
            hipótese de indução, st =[ c2 ]=> st', e pela regra E_IfFalse segue 
            st =[ if b then c1 else c2 ]=> st'.
            
      - Suponha c = while b do c1 end. Devemos mostrar st =[ while b do c1 end ]=> st'. 
        Analisamos beval st b:
          
          - Se beval st b = false, o laço termina imediatamente sem alterar o estado, de modo 
            que st' = st. Pela regra E_WhileFalse, temos st =[ while b do c1 end ]=> st'.
            
          - Se beval st b = true, o corpo c1 precisa terminar em i' passos com algum estado e 
            (o caso None é impossível), e a execução restante do while a partir de e deve 
            alcançar st' em i' passos. Pela hipótese de indução, st =[ c1 ]=> e e também
            e =[ while b do c1 end ]=> st'. Aplicando E_WhileTrue, obtemos 
            st =[ while b do c1 end ]=> st'. ☐ *)

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 ->
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Proof.
induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  - (* i1 = 0 *)
    simpl in Hceval. discriminate Hceval.
  - (* i1 = S i1' *)
    destruct i2 as [|i2']. inversion Hle.
    assert (Hle': i1' <= i2') by lia.
    destruct c.
    + (* skip *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* := *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* ; *)
      simpl in Hceval. simpl.
      destruct (ceval_step st c1 i1') eqn:Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* st1'o = None *)
        discriminate Hceval.
    + (* if *)
      simpl in Hceval. simpl.
      destruct (beval st b); apply (IHi1' i2') in Hceval;
        assumption.
    + (* while *)
      simpl in Hceval. simpl.
      destruct (beval st b); try assumption.
      destruct (ceval_step st c i1') eqn: Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite -> Heqst1'o.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* i1'o = None *)
        discriminate Hceval. Qed.

(* Exercício *)
(* Termine a prova a seguir. Você precisará de ceval_step_more em alguns lugares, bem como 
de alguns fatos básicos sobre ≤ e plus (soma). *)

Theorem ceval__ceval_step: forall c st st',
      st =[ c ]=> st' ->
      exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  induction Hce.
  - (* E_Skip *)
    exists (S 0). simpl. reflexivity.
  - (* E_Asgn *)
    exists (S 0). simpl. rewrite H. reflexivity.
  - (* E_Seq *)
     destruct IHHce1 as [e1 He1].
     destruct IHHce2 as [e2 He2].
     assert (H1lt : e1 <= e1 + e2). {
      lia.
     }
     assert (H2lt : e2 <= e1 + e2). {
      lia.
     }
    apply (ceval_step_more e1 (e1 + e2)) in He1.
    apply (ceval_step_more e2 (e1 + e2)) in He2.
    exists (S (e1 + e2)). simpl. rewrite He1. apply He2.
      + apply H2lt.
      + apply H1lt.
  - (* E_IfTrue *) 
    destruct IHHce as [e He].
    exists (S e). simpl.
    rewrite H. apply He.
  - (* E_IfFalse *)
    destruct IHHce as [e He].
    exists (S e). simpl.
    rewrite H. apply He.
  - (* E_WhileFalse *)
    exists (S 0). simpl. rewrite H.
    reflexivity.
  - (* E_WhileTrue *)
    destruct IHHce1 as [e1 He1].
    destruct IHHce2 as [e2 He2].
    assert (H1lt : e1 <= e1 + e2). {
      lia.
     }
     assert (H2lt : e2 <= e1 + e2). {
      lia.
     }
    apply (ceval_step_more e1 (e1 + e2)) in He1.
    apply (ceval_step_more e2 (e1 + e2)) in He2.
    exists (S (e1 + e2)). simpl. rewrite H.
    rewrite He1. apply He2. 
      + apply H2lt.
      + apply H1lt.
Qed.

Theorem ceval_and_ceval_step_coincide: forall c st st',
      st =[ c ]=> st'
  <-> exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.

(***************************** Determinismo da Avaliação Novamente ************************)

(* Usando o fato de que a definição relacional e a definição indexada por passos da 
avaliação são iguais, podemos dar uma prova mais elegante (ou ''mais esperta'' / mais 
direta) de que a relação de avaliação é determinística. *)

Theorem ceval_deterministic' : forall c st st1 st2,
     st =[ c ]=> st1 ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 He1 He2.
  apply ceval__ceval_step in He1.
  apply ceval__ceval_step in He2.
  inversion He1 as [i1 E1].
  inversion He2 as [i2 E2].
  apply ceval_step_more with (i2 := i1 + i2) in E1.
  apply ceval_step_more with (i2 := i1 + i2) in E2.
  rewrite E1 in E2. inversion E2. reflexivity.
  lia. lia. Qed.