(* Definição de tipos de dados*)

Inductive dia : Type := (* registrando uma nova definição para um tipo - dia é o nome do tipo e := serve como símbolo de atribuição*)
 |segunda
 |terca
 |quarta
 |quinta
 |sexta
 |sabado
 |domingo. (* Não esquecer do '.' para finalizar, semelhantemente como o ';' faz em várias linguagens*)

 
(* Definindo uma função*)
Definition proximo_dia_util_da_semana (d: dia) : dia := (* o nome da função é proximo_dia_da_semana- o nome do argumento é 'd' do tipo dia - o retorno é do tipo dia*)
  match d with (* Casamento de padrões - se d for segunda retorna terca, etc*)
  |segunda => terca
  |terca => quarta
  |quarta => quinta
  |quinta => sexta
  |sexta => segunda
  |sabado => segunda
  |domingo => segunda
  end.

(* Computar o resultado da aplicação da função proximo_dia_da_semana em sexta*)
Compute (proximo_dia_util_da_semana sexta). (* o resultado é ' =segunda : dia' *)

Compute(proximo_dia_util_da_semana (proximo_dia_util_da_semana sabado)). (* o resultado é ' =terca : dia' *)