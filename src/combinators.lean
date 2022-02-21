namespace my

inductive combinator : Type
| var : ℕ → combinator
| app : combinator → combinator → combinator
| S : combinator
| K : combinator
| I : combinator

open combinator

def same : combinator → combinator → bool
| (var n) (var m) := ite (m = n) tt ff
| (app c₁ c₂) (app d₁ d₂) := band (same c₁ d₁) (same c₂ d₂)
| S S := tt
| K K := tt
| I I := tt
| _ _ := ff

notation ` £ ` := app

def x := var 0
def y := var 1
def z := var 2
def w := var 3

protected def combinator.to_string_aux : combinator → bool → string
-- second argument indicates whether brackets need to be included for
-- an application
| (var 0) _ := "x"
| (var 1) _ := "y"
| (var 2) _ := "z"
| (var 3) _ := "w"
| (var (n + 4)) _ := "u" ++ has_to_string.to_string n
| (app c₁ c₂) tt := "(" ++ combinator.to_string_aux c₁ ff
                        ++ combinator.to_string_aux c₂ tt ++ ")"
| (app c₁ c₂) ff := combinator.to_string_aux c₁ ff
                 ++ combinator.to_string_aux c₂ tt
| S _ := "S"
| K _ := "K"
| I _ := "I"

protected def combinator.to_string : combinator → string :=
λ c, combinator.to_string_aux c ff

instance combinator_to_string : has_to_string combinator :=
⟨combinator.to_string⟩

def succ := £ S (£ (£ S (£ K S)) (£ (£ S (£ K K)) I))

def nat_to_combinator : ℕ → combinator
| 0 := £ K I
| 1 := I
| (nat.succ n) := £ succ (nat_to_combinator n)

instance nat_has_coe_to_combinator : has_coe nat combinator :=
⟨nat_to_combinator⟩

#eval succ.to_string

meta def combinator.reduce_aux : combinator → bool → combinator
-- second argument indicates whether first term is reduced in an application
| (app I c) _ := combinator.reduce_aux c ff
| (app (app K c₁) c₂) _ := combinator.reduce_aux c₁ ff
| (app (app (app S c₁) c₂) c₃) _ :=
  combinator.reduce_aux (app (app c₁ c₃) (app c₂ c₃)) ff
| (app c₁ c₂) ff :=
  combinator.reduce_aux (app (combinator.reduce_aux c₁ ff) c₂) tt
| (app c₁ c₂) tt := app c₁ (combinator.reduce_aux c₂ ff)
| (var n) _ := var n
| S _ := S
| K _ := K
| I _ := I

meta def combinator.reduce : combinator → combinator :=
λ c, combinator.reduce_aux c ff

#eval (combinator.reduce (£ (£ ↑3 x) y)).to_string

def numeral : ℕ → combinator → combinator → combinator
| 0 x y := y
| (nat.succ n) x y :=  app x (numeral n x y)

#eval (numeral 3 w z).to_string

meta def extensionally_n (c : combinator) (n : ℕ) : bool :=
same (combinator.reduce (£ (£ c x) y)) (numeral n x y)

def pow_combinator : combinator :=
£ (£ S (£ K (£ S I))) (£ (£ S (£ K K)) I)

def combinator.pow (base : combinator) (exponent : combinator) : combinator :=
£ (£ pow_combinator base) exponent

#eval extensionally_n (combinator.pow ↑3 ↑4) 81

def mul_combinator : combinator := £ (£ S (£ K S)) K

def combinator.mul (first : combinator) (second : combinator) : combinator :=
£ (£ mul_combinator first) second

#eval extensionally_n (combinator.mul ↑3 ↑4) 12

def add_combinator : combinator :=
£ (£ S (£ K S)) (£ (£ S (£ K (£ S (£ K S)))) (£ S (£ K K)))

def combinator.add (first : combinator) (second : combinator) : combinator :=
£ (£ add_combinator first) second

#eval extensionally_n (combinator.add ↑3 ↑4) 7

end my