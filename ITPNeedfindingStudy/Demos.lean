import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

example {a b c d: ℤ} (h1 : Odd a) (h2 : Odd c) (h3 : Odd (b + d)): Odd (a * b + c * d) := by
  obtain ⟨k1, hk1⟩ := h1 -- assume     a = 2 * k1 + 1
  obtain ⟨k2, hk2⟩ := h2 -- assume     c = 2 * k2 + 1
  obtain ⟨k3, hk3⟩ := h3 -- assume b + d = 2 * k3 + 1
  use k1 * b + k2 * d + k3 -- show that a * b + c * d = 2 * (k1 * b + k2 * d + k3) + 1
  calc
    a * b + c * d = (2 * k1 + 1) * b + (2 * k2 + 1) * d := by rw [hk1, hk2] -- substitution
    _ = 2 * (k1 * b + k2 * d) + (b + d) := by ring -- simplification
    _ = 2 * (k1 * b + k2 * d) + (2 * k3 + 1) := by rw [hk3] -- substitution
    _ = 2 * (k1 * b + k2 * d + k3) + 1 := by ring -- simplification


example {n : ℤ} (h: 5 ∣ (n + 7)) : 5 ∣ (n ^ 2 + 1) := by
  obtain ⟨k, hk⟩ := h -- assume n + 7 = 5 * k
  have hn : n = 5 * k - 7 := by linarith -- rearrange n = 5 * k - 7
  use 5 * k ^ 2 - 14 * k + 10 -- show that n ^ 1 + 1 = 5 * (5 * k ^ 2 - 14 * k + 10)
  calc
    n ^ 2 + 1 = (5 * k - 7) ^ 2 + 1 := by rw [hn] -- substitution
    _ = (25 * k ^ 2 - 70 * k + 49) + 1 := by ring -- simplification
    _ = 5 * (5 * k ^ 2 - 14 * k + 10) := by ring  -- simplification


example {n a b x y : ℤ} (h1 : n ∣ a) (h2 : n ∣ b) : (n ∣ (a * x + b * y)) := by
  obtain ⟨j, hj⟩ := h1 -- assume a = n * j
  obtain ⟨k, hk⟩ := h2 -- assume b = n * k
  use j * x + k * y -- show that a * x + b * y = n * (j * x + k * y)
  calc
    a * x + b * y = (n * j) * x + (n * k) * y := by rw [hj, hk] -- substitution
    _ = n * (j * x + k * y) := by ring -- simplification


example : ∀ n : ℤ, 2 ∣ n → 2 ∣ (n ^ 3 + n ^ 2) := by
  intro n hn -- let n be an arbitrary integer divisible by 2
  obtain ⟨k, hk⟩ := hn -- assume n = 2 * k
  use 4 * k ^ 3 + 2 * k ^ 2 -- show that n ^ 3 + n ^ 2 = 2 * (4 * k ^ 3 + 2 * k ^ 2)
  calc
    n ^ 3 + n ^ 2 = (2 * k) ^ 3 + (2 * k) ^ 2 := by rw [hk] -- substitution
    _ = 8 * k ^ 3 + 4 * k ^ 2 := by ring -- simplification
    _ = 2 * (4 * k ^ 3 + 2 * k ^ 2) := by ring -- simplification


example : ¬(∀ x : ℝ, ∀ y : ℝ, x > y → x ^ 2 > y ^ 2) := by
  push_neg -- push negation inward
  use 1 -- use x = 1
  use -3 -- use y = -3
  constructor -- break 1 > -3 and 1 ^ 2 <= (-3) ^ 2 into cases
  · norm_num  -- prove 1 > -3
  · norm_num  -- prove 1 ^ 2 <= (-3) ^ 2


example {n : ℕ} : Even (n ^ 2) → Even n := by
  contrapose -- prove ¬Even n → ¬Even (n ^ 2)
  intro h -- assume the antecedent ¬Even n
  rw [Nat.not_even_iff_odd] at h -- rewrite antecedent as Odd n
  rw [Nat.not_even_iff_odd] -- rewrite conclusion as Odd (n ^ 2)
  obtain ⟨k, hk⟩ := h -- assume n = 2 * k + 1
  use 2 * k ^ 2 + 2 * k -- show that n ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1
  calc
    n ^ 2 = (2 * k + 1) ^ 2 := by rw [hk] -- substitution
    _ = 4 * k ^ 2 + 4 * k + 1 := by ring -- simplification
    _ = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring -- simplification
