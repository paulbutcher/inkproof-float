/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Float.FloatValue

universe u

namespace Inkproof.Float

theorem rat_sq_le_sq_of_nonneg {a b : Rat} (h0 : 0 ≤ a) (h : a ≤ b) : a * a ≤ b * b :=
  Rat.le_trans (Rat.mul_le_mul_of_nonneg_left h h0) (Rat.mul_le_mul_of_nonneg_right h (by grind))

theorem rat_sq_le_sq_of_nonpos {a b : Rat} (h0 : a ≤ 0) (h : b ≤ a) : a * a ≤ b * b := by
  have := rat_sq_le_sq_of_nonneg (a := -a) (b := -b) (by grind) (by grind)
  grind

/-- `a * a ≤ ρ * ρ` bounds `a` by `ρ` in magnitude. -/
theorem rat_abs_le_of_sq_le {a ρ : Rat} (hρ : 0 ≤ ρ) (h : a * a ≤ ρ * ρ) : -ρ ≤ a ∧ a ≤ ρ := by
  constructor
  · refine Decidable.byContradiction fun hc => ?_
    have := Rat.mul_pos (by grind : 0 < -ρ - a) (by grind : 0 < -a + ρ)
    grind
  · refine Decidable.byContradiction fun hc => ?_
    have := Rat.mul_pos (by grind : 0 < a - ρ) (by grind : 0 < a + ρ)
    grind

/-- `x` held to the interval from `lo` to `hi`. Only `<` is used, so a NaN `x` passes through
unchanged. -/
def clamp {α : Type u} [LT α] [DecidableLT α] (lo hi x : α) : α :=
  if x < lo then lo else if hi < x then hi else x

theorem rat_clamp_mem {lo hi x : Rat} (h : lo ≤ hi) : lo ≤ clamp lo hi x ∧ clamp lo hi x ≤ hi := by
  unfold clamp; grind

theorem rat_clamp_eq_max_min {lo hi x : Rat} (h : lo ≤ hi) : clamp lo hi x = max lo (min x hi) := by
  unfold clamp; grind

/-- The clamped point is no farther from `x` than any point of the interval. -/
theorem rat_clamp_sq_le {lo hi x p : Rat} (h : lo ≤ p) (h' : p ≤ hi) :
    (clamp lo hi x - x) * (clamp lo hi x - x) ≤ (p - x) * (p - x) := by
  unfold clamp
  by_cases h1 : x < lo
  · simp only [h1, ↓reduceIte]
    exact rat_sq_le_sq_of_nonneg (by grind) (by grind)
  by_cases h2 : hi < x
  · simp only [h1, h2, ↓reduceIte]
    exact rat_sq_le_sq_of_nonpos (by grind) (by grind)
  · simp only [h1, h2, ↓reduceIte]
    have : (x - x) = 0 := by grind
    rw [this, Rat.zero_mul]
    rcases Rat.le_total (a := 0) (b := p - x) with h3 | h3
    · exact Rat.mul_nonneg h3 h3
    · have := Rat.mul_nonneg (a := -(p - x)) (b := -(p - x)) (by grind) (by grind)
      grind
