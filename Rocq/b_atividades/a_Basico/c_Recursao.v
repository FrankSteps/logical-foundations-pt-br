(*
    Fixpoint é a notação para funções recursivas. 

    Uma função recursiva chamada fatorial recebe um número do tipo natural e retorna um número do tipo natural.
    Após isso, o `match` é aplicado para verificar o valor de entrada, se comportando como um "if" mais elaborado
    e funcional.

    Caso o valor seja 0, o resultado final é 1 :D
    Caso contrário, entramos no caso sucessor `S k`, ou seja, estamos dizendo que n = k + 1.

    Nesse ponto, a função faz:
        n * fatorial(k)

    Traduzindo: fatorial(n) = n * fatorial(n - 1)

    O `end` só fecha o `match`, não a recursão. Rocq exige que a função seja decrescente! Se a função for infinita, 
    Rocq não permite!
*)

Fixpoint fatorial (n : nat) : nat :=
    match n with
    | 0 => 1
    | S k => n * fatorial  k
    end.


Compute fatorial 7.