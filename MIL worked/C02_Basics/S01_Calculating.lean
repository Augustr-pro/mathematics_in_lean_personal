import MIL.Common
import Mathlib.Data.Real.Basic
-- An example.
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- example but pretty
example
  (a b c : ℝ)
  : a * b * c = b * (a * c) :=
    calc
      a * b * c = b * a * c     := by rw [mul_comm a b]
      _          = b * (a * c)  := by rw [mul_assoc b a c]

-- Try these.
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a]
  rw [mul_comm c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc a b c]
  rw [mul_comm a b]
  rw [mul_assoc b a c]


-- An example.
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [mul_comm a]
  rw [mul_assoc b]
  rw [mul_comm a]

-- Using facts from the local context.
example
  (a b c d e f : ℝ)
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
    by
    rw [h2]
    rw [← mul_assoc]
    rw [h1]
    rw [mul_assoc]

-- trad
example
(a b c d e f : ℝ)
(h : b * c = e * f)
 : a * b * c * d = a * e * f * d :=
  by
    rw [mul_assoc a b c]
    rw [h]
    rw [← mul_assoc a e f]

-- pretty
example
(a b c d e f : ℝ)
(h : b * c = e * f)
 : a * b * c * d = a * e * f * d :=
  calc
    a * b * c * d = a * b * c * d       := by rw []
    _             = a * (b * c) * d     := by rw [mul_assoc a b c]
    _             = a * (e * f) * d     := by rw [h]
    _             = a * e * f * d       := by rw [← mul_assoc a e f]


-- trad
theorem e1
(a b c d : ℝ)
(hyp : c = b * a - d)
(hyp' : d = a * b)
: c = 0 :=
  by
    rw [hyp]
    rw [hyp']
    rw [mul_comm b a]
    rw [sub_self (a*b)]

#print e1

-- pretty
theorem e2
(a b c d : ℝ)
(hyp : c = b * a - d)
(hyp' : d = a * b)
: c = 0 :=
  calc
    c = c                   := by rw []
    _ = b * a - d           := by rw [hyp]
    _ = b * a - a * b       := by rw [hyp']
    _ = a * b - a * b       := by rw [mul_comm b a]
    _ = 0                   := by rw [sub_self (a*b)]

#print e2
-- looks different in the printout, wonder about runtime on check

-- sans.tactic
theorem e1.st : ∀ (a b c d : ℝ), c = b * a - d → d = a * b → c = 0 :=
fun a b c d hyp hyp' =>
  Eq.mpr (id (congrArg (fun _a => _a = 0) hyp))
    (Eq.mpr (id (congrArg (fun _a => b * a - _a = 0) hyp'))
      (Eq.mpr (id (congrArg (fun _a => _a - a * b = 0) (mul_comm b a)))
        (Eq.mpr (id (congrArg (fun _a => _a = 0) (sub_self (a * b)))) (Eq.refl 0))))

#print e1.st
#check e1.st

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

--sec1
section

variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

end
--sec1

--sec2
section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end
--sec2

-- sec3
section
variable (a b : ℝ)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

-- I see the vision, but it disgusts me
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      sorry
    _ = a * a + (b * a + a * b) + b * b := by
      sorry
    _ = a * a + 2 * (a * b) + b * b := by
      sorry

end
-- sec3

-- Try these. For the second, use the theorems listed underneath.
-- sec4
section
variable (a b c d : ℝ)

-- pure
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [mul_add, add_mul, add_mul, ← add_assoc, add_assoc (a*c), add_comm (b*c) (a*d), ← add_assoc (a*c)]

-- structured
example
: (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
  calc
    (a + b) * (c + d) = (a + b) * c + (a + b) * d           := by rw [mul_add]
    _                 = a * c + b * c + (a + b) * d         := by rw [add_mul]
    _                 = a * c + b * c + (a * d + b * d)     := by rw [add_mul]
    _                 = a * c + b * c + a * d + b * d       := by rw [← add_assoc]
    _                 = a * c + (b * c + a * d) + b * d     := by rw [add_assoc (a*c)]
    _                 = a * c + (a * d + b * c) + b * d     := by rw [add_comm (b*c) (a*d)]
    _                 = a * c + a * d + b * c + b * d       := by rw [← add_assoc (a*c)]



example
(a b : ℝ)
: (a + b) * (a - b) = a ^ 2 - b ^ 2 :=
  calc
    (a + b) * (a - b) = a ^ 2 - a * b + b * a - b ^ 2  := by rw [add_mul, mul_sub, mul_sub, add_sub, ← pow_two, ← pow_two]
    _ = a ^ 2 + (a * b - b * a) - b ^ 2                := by ring
    _ = a ^ 2 + 0 - b ^ 2                              := by ring
    _ = a ^ 2 - b ^ 2                                  := by rw [add_zero]

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a

end
-- sec4

-- Examples.

-- sec5
section
variable (a b c d : ℝ)

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp

example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end
-- sec5

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
