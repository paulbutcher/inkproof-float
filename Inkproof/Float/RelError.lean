/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Float.FloatValue

/-! Relative-error lemmas about `Rat.abs` with the error constant `k` a variable, so that they hold
of any format: instantiate `k` with `2 ^ -prec` or a multiple of it. -/

namespace Inkproof.Float

/-- Composing a rounding error `k` of `q` about `p + d` with `p` within `k` of `m`. -/
theorem rel_error_step (q p m d k : Rat) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (h1 : (p - m).abs ≤ m.abs * k)
    (h2 : (q - (p + d)).abs ≤ (p + d).abs * k) :
    (q - (m + d)).abs ≤ 4 * (m.abs + d.abs) * k := by
  have a1 := rat_abs_add_le (q - (p + d)) (p - m)
  have a2 := rat_abs_add_le p d
  have a3 := rat_abs_add_le (p - m) m
  have n1 := (Rat.abs_nonneg (x := m))
  have n2 := (Rat.abs_nonneg (x := d))
  have e : q - (m + d) = (q - (p + d)) + (p - m) := by grind
  rw [e]
  have k1 : m.abs * k ≤ m.abs * 1 := Rat.mul_le_mul_of_nonneg_left hk1 n1
  have k2 : (p + d).abs * k ≤ (3 * m.abs + d.abs) * k :=
    Rat.mul_le_mul_of_nonneg_right (by grind) hk0
  have := Rat.mul_nonneg n2 hk0
  grind

private theorem mulLe {a b c d : Rat} (h1 : a ≤ c) (h2 : b ≤ d) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * b ≤ c * d :=
  Rat.le_trans (Rat.mul_le_mul_of_nonneg_right h1 hb) (Rat.mul_le_mul_of_nonneg_left h2 hc)

/-- The relative error of a product. -/
theorem rel_error_mul (x y a b c1 c2 : Rat) (hc1 : 0 ≤ c1)
    (h1 : (x - a).abs ≤ a.abs * c1) (h2 : (y - b).abs ≤ b.abs * c2) :
    (x * y - a * b).abs ≤ (a * b).abs * (c1 + c2 + c1 * c2) := by
  have e : x * y - a * b = (x - a) * (y - b) + (x - a) * b + a * (y - b) := by grind
  have t1 := rat_abs_add_le ((x - a) * (y - b) + (x - a) * b) (a * (y - b))
  have t2 := rat_abs_add_le ((x - a) * (y - b)) ((x - a) * b)
  have m1 : ((x - a) * (y - b)).abs ≤ (a.abs * c1) * (b.abs * c2) := by
    rw [rat_abs_mul]
    exact mulLe h1 h2 (Rat.abs_nonneg) (Rat.mul_nonneg (Rat.abs_nonneg) hc1)
  have m2 : ((x - a) * b).abs ≤ (a.abs * c1) * b.abs := by
    rw [rat_abs_mul]
    exact Rat.mul_le_mul_of_nonneg_right h1 (Rat.abs_nonneg)
  have m3 : (a * (y - b)).abs ≤ a.abs * (b.abs * c2) := by
    rw [rat_abs_mul]
    exact Rat.mul_le_mul_of_nonneg_left h2 (Rat.abs_nonneg)
  rw [e, rat_abs_mul a b]
  grind

/-- A rounding step of relative error `k` on top of a value within `c` of `r`. -/
theorem rel_error_round (z x r c k : Rat) (hk : 0 ≤ k)
    (h1 : (x - r).abs ≤ r.abs * c) (h2 : (z - x).abs ≤ x.abs * k) :
    (z - r).abs ≤ r.abs * (c + k + c * k) := by
  have t := rat_abs_add_le (z - x) (x - r)
  have t' := rat_abs_add_le (x - r) r
  have e : z - r = (z - x) + (x - r) := by grind
  have m := Rat.mul_le_mul_of_nonneg_right (show x.abs ≤ r.abs + r.abs * c by grind) hk
  rw [e]
  grind

/-- The relative error of a quotient: `v * t3 = t4` with `t4` within `c4` of `A * B` and `t3` within
`k` of `C`, where `u * C = A * B`. -/
theorem rel_error_div (t4 t3 v A B C u c4 k c : Rat) (hk1 : k < 1)
    (hC : C ≠ 0) (hu : u * C = A * B)
    (h4 : (t4 - A * B).abs ≤ (A * B).abs * c4) (h3 : (t3 - C).abs ≤ C.abs * k)
    (hv : v * t3 = t4) (hc : c4 + k ≤ c * (1 - k)) :
    (v - u).abs ≤ u.abs * c := by
  have hCpos : 0 < C.abs := Rat.abs_pos_iff.mpr hC
  have e : (v - u) * t3 = (t4 - A * B) + u * (C - t3) := by grind
  have lhs : ((v - u) * t3).abs = (v - u).abs * t3.abs := rat_abs_mul _ _
  have t := rat_abs_add_le (t4 - A * B) (u * (C - t3))
  have hAB : (A * B).abs = u.abs * C.abs := by rw [← hu, rat_abs_mul]
  have hCt : (C - t3).abs = (t3 - C).abs := Rat.abs_sub_comm
  have m1 : (u * (C - t3)).abs ≤ u.abs * (C.abs * k) := by
    rw [rat_abs_mul, hCt]
    exact Rat.mul_le_mul_of_nonneg_left h3 (Rat.abs_nonneg)
  have t3b : C.abs * (1 - k) ≤ t3.abs := by
    have := rat_abs_add_le t3 (C - t3)
    have e3 : t3 + (C - t3) = C := by grind
    rw [e3] at this
    grind
  have nv := (Rat.abs_nonneg (x := (v - u)))
  have nu := (Rat.abs_nonneg (x := u))
  have hw : 0 < C.abs * (1 - k) := Rat.mul_pos hCpos (by grind)
  have step1 : (v - u).abs * (C.abs * (1 - k)) ≤ (v - u).abs * t3.abs :=
    Rat.mul_le_mul_of_nonneg_left t3b nv
  have step2 : (v - u).abs * t3.abs ≤ u.abs * C.abs * (c4 + k) := by
    rw [← lhs, e]
    rw [hAB] at h4
    grind
  have step3 : u.abs * C.abs * (c4 + k) ≤ u.abs * C.abs * (c * (1 - k)) :=
    Rat.mul_le_mul_of_nonneg_left hc (Rat.mul_nonneg nu (Rat.abs_nonneg))
  have : (v - u).abs * (C.abs * (1 - k)) ≤ (u.abs * c) * (C.abs * (1 - k)) := by
    grind
  exact Rat.le_of_mul_le_mul_right this hw

end Inkproof.Float
