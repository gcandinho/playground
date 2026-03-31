import Mathlib

#eval 1 + 2
#eval 1 + 2 * 5
#eval String.append "Hello " "World"
#eval String.append "great " (String.append "oak " "tree")
#eval 42 + 19
#eval String.append "A" (String.append "B" "C")
#eval if 3 == 3 then 5 else 7
#eval if 3 == 4 then "equal" else "not equal"
#eval (1 - 2: Nat)
#eval (1 - 2: Int)
#check (1 - 2: Int)

-- #check String.append ["hello", ""] "world"
-- Returns an erro
-- Application type mismatch: The argument
--  ["hello", ""]
-- has type
--  List String
-- but is expected to have type
--  String
-- in the application
--  String.append ["hello", ""]

def lean : String := "Lean"
-- This does not define a function tha return "Lean", but associates the
-- "variable" lean with the strign "Lean"

-- Do define a function, it's necessary to provide at least one argument
def add_one (n : Nat) : Nat := n + 1
-- Syntax: def (function name) (argument : type) : (return type) := (algorithm)
def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else n

-- Example
#eval maximum (5+8) (2 * 7)
-- maximum (5 + 8) (2 * 7) =>
-- maximum 13 14 =>
-- if 13 < 14 then 14 else 13 =>
-- 14 (returned value)

def spaceBetween (before : String) (after : String) : String :=
  String.append before (String.append " " after)

def joinStringWith (first : String) (second : String) (third : String) : String :=
  String.append second (String.append first third)

#eval joinStringWith ", " "one" "and another"

#check joinStringWith ": "
-- String -> String -> String

def volume (h : Nat) (w : Nat) (d : Nat) : Nat :=
  h * w * d

#eval volume 22 15 22

-- As functional programming is basicaly a type of lambda calculus
-- There's no "two arguments functions" everything is threated as
-- A function, that creates a functions and so on.
-- Let's do a math example f(x) = 2x + 1, could be the writen as
-- g(x) = x + 1, h(x) = 2x => h(g(x)) = f(x)
-- Read: https://en.wikipedia.org/wiki/Lambda_calculus

-- There's two ways to define a type
def Str : Type := String
-- and
abbrev Str_Abr : Type := String

-- There is an error which occurs because Lean allows number literals to be overloaded.
-- When it makes sense to do so, natural number literals can be used for new types,
-- just as if those types were built in to the system
-- This is usefull because different branches of mathematics uses number notation
-- for diferente purposes. (An example which I can whink is group theory, permutation groups)
-- Behind the scenes, some definitions are internally marked as being unfoldable during overload
-- resolution,
-- while others are not.
-- Definitions that are to be unfolded are called reducible

-- Sometimes to solve a particular problems it's helpful to create a struct (which is in principle,
-- made with simpler types)
-- strucutres are similar to structs in C and Rust or records in C#

-- Let's create two structures, one for represent points in R^2 using cartesian coordinates and
-- another to represent
-- points using polar coordinates
structure Cartesian_Point where
  x : Float
  y : Float

structure Polar_Point where
  r : ℝ
  θ : ℝ
  θ_nonneg : 0 ≤ θ
  θ_le_360 : θ ≤ 360
