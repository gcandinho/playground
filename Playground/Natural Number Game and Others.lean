import Mathlib.Tactic.NthRewrite
-- Here, are the exercises from the "Natural number game"
-- Aqui, estão exercicios do jogo "Natural number game"

theorem thsv_eq_thsv (x q : Nat) : 37*x + q = 37*x + q := by
  rfl
  -- rfl is the same as reflexivity
  -- rfl é o mesmo que reflexitividade

#check thsv_eq_thsv

-- Note: The syntax of LEAN is as follow
-- theorem (theorem name) (hypotesis) ... (hypotheses) : (goal) := by
--  tatics
-- Nota: A sintaxe do LEAN é a seguinte
-- theorem (nome do teorema) (hipotese) ... (hipotese) : (objetivo) := by
--  tática

theorem ty_eq_txps (x y : Nat) (h : y = x + 7) : 2*y = 2*(x + 7) := by
  rw[h]
  -- The natural number game, says that the reflexivity is necessary
  -- The lean mathlib doens't seen to require that.
  -- O jogo natural number game, diz que a reflexitivade é necessária
  -- A biblioteca mathlib parece que não requer isso.

#check ty_eq_txps

-- (1) This is along one, prove that 2 + 2 = 4, ussing successor.
-- Essa é uma longa, prove que 2 + 2 = 4, usando sucessores.

theorem one_eq_succ_zero : (1 : Nat) = Nat.succ 0 :=
  rfl

#check one_eq_succ_zero

theorem two_eq_succ_one : (2 : Nat) = Nat.succ 1 :=
  rfl

#check two_eq_succ_one

theorem three_eq_succ_two : (3 : Nat) = Nat.succ 2 :=
  rfl

#check three_eq_succ_two

theorem four_eq_succ_three : (4 : Nat) = Nat.succ 3 :=
  rfl

#check four_eq_succ_three

-- Before we prove that 2 + 2 = 4, the game ask to prove that 2
-- is the successor of the succesor of zero
-- Antes de provarmos que 2 + 2 = 4, o jogo pede para provar que 2 é o sucessor do sucessor de zero
theorem t_eq_succ_succ_z : (2 : Nat) = Nat.succ (Nat.succ 0) := by
  calc
    (2 : Nat)
        = Nat.succ 1 := two_eq_succ_one
    _   = Nat.succ (Nat.succ 0) := by
          rw [one_eq_succ_zero]

-- Essa demonstração em especial requer uma certa explicação do porque escrevi desta forma
-- O LEAN verifica quando um objetivo já é completado, ou seja, processos extras são ignorados
-- e tratados como erros.
-- A documentação de calc pode ser lida em https://leanprover-community.github.io/extras/calc.html
-- Basicamente, permite que você crie o seu prórprio caminho para a demonstração
-- Pois, segundo o lean, uma demonstração curta e direta seria
-- theorem t_eq_succ_succ_z_s : (2 : Nat) = Nat.succ (Nat.succ 0 ) := by
--  rfl

#check t_eq_succ_succ_z

-- Proof that a + (b + 0) + (c + 0) = a + b + c
-- Prova que a + (b + 0) + (c + 0) = a + b + c
theorem a_p_b_p_c (a b c : Nat) : a + (b + 0) + (c + 0) = a + b + c := by
  rw [Nat.add_zero]
  rw [Nat.add_zero]

#check a_p_b_p_c

-- Proof that a + (b + 0) + (c + 0) = a + b + c
-- Explicitamente dizendo onde a tatica rw (rewrite) must be done
-- Prova que a + (b + 0) + (c + 0) = a + b + c
-- Explicitamente dizendo onde a tatica rw (reescrever) deve ser realizada
theorem a_p_b_p_c_two (a b c : Nat) : a + (b + 0) + (c + 0) = a + b + c := by
  rw [Nat.add_zero c]
  rw [Nat.add_zero b]

theorem succ_eq_add_one (n : Nat) : Nat.succ n = n + 1 := by
  rw [one_eq_succ_zero]

#check succ_eq_add_one

-- Finally going back to (1). Need some importation
-- Finalmente voltamos para o problema 1
-- theorem two_pl_two_eq_four : (2 : Nat) + 2 = 4 := by
--  rw [four_eq_succ_three]
--  rw [three_eq_succ_two]
--  nth_rewrite 2 [two_eq_succ_one]
--  rw [add_succ]
--  rw [← succ_eq_add_one]
--  rfl

-- Notas extras sobre syntaxe

-- While both ordinary mathematical notation and the majority of programming languages
-- use parentheses (e.g. f(x))
-- to apply a function to its arguments, Lean simply writes the function next
-- to its arguments (e.g. f x).
-- Function application is one of the most common operations, so it pays to keep it concise.
-- Rather than writing
-- #eval String.append("Hello, ", "Lean!")
-- to compute "Hello, Lean!", one would instead write
-- #eval String.append "Hello, " "Lean!"
-- Enquanto tanto a notação matemática usual quanto a maioria das linguagens de programação
-- usam parênteses (ex.: f(x))
-- para aplicar uma função aos seus argumentos, o Lean simplesmente escreve a função ao lado dos
-- seus argumentos (ex.: f x).
-- A aplicação de função é uma das operações mais comuns, então vale a pena mantê-la concisa.
-- Em vez de escrever
-- #eval String.append("Hello, ", "Lean!")
-- para calcular "Hello, Lean!", escreve-se
-- #eval String.append "Hello, " "Lean!"

-- Lean's type system is unusually expressive. Types can encode strong
-- specifications like “this sorting function returns a permutation of its input
-- ” and flexible specifications like “this function has different return types,
-- depending on the value of its argument”. The type system can even be used as
-- a full-blown logic for proving mathematical theorems. This cutting-edge
-- expressive power doesn't make simpler types unnecessary, however, and
-- understanding these simpler types is a prerequisite for using the more
-- advanced features.
-- O sistema de tipos do Lean é incomumente expressivo. Tipos podem codificar
-- especificações fortes como “esta função de ordenação retorna uma permutação
-- de sua entrada” e especificações flexíveis como “esta função tem diferentes
-- tipos de retorno, dependendo do valor do seu argumento”. O sistema de tipos
-- pode até ser usado como uma lógica completa para provar teoremas matemáticos.
-- Esse poder expressivo de ponta não torna os tipos mais simples desnecessários,
-- no entanto, e entender esses tipos mais simples é um pré-requisito para usar
-- os recursos mais avançados.

-- Important syntax notation:
-- In Lean, new names are defined using the colon-equal operator := rather than =.
-- This is because = is used to describe equalities between existing expressions,
-- and using two different operators helps prevent confusion. Does this apply
-- to the LEAN4 prover.
-- Em Lean, novos nomes são definidos usando o operador dois-pontos igual := em vez de =.
-- Isso ocorre porque = é usado para descrever igualdades entre expressões existentes,
-- e usar dois operadores diferentes ajuda a evitar confusão. Isso se aplica
-- ao provador LEAN4?
