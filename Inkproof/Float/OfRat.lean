/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Float.Exact
import Inkproof.Float.Axioms

/-! Conversion of a rational to a `Float`. -/

namespace Inkproof.Float

/-- The `Float` for `r`: its numerator divided by its denominator, which rounds once when both are
below `2 ^ 53` and otherwise rounds each operand too. -/
def _root_.Rat.toFloat (r : Rat) : Float :=
  let q := (OfNat.ofNat r.num.natAbs : Float) / (OfNat.ofNat r.den : Float)
  if r.num < 0 then -q else q

/-- A rational with numerator and denominator below `2 ^ 53` and in the normal range converts to a
float within half an ulp of it. -/
theorem _root_.Rat.approximates_toFloat {r : Rat} (hn : r.num.natAbs < 2 ^ 53)
    (hd : r.den < 2 ^ 53) (hr : NormalRange r) : Float.Approximates (Rat.toFloat r) r := by
  have hden : (r.den : Rat) ≠ 0 := by exact_mod_cast r.den_nz
  have hdiv : (r.num : Rat) / (r.den : Rat) = r := by
    have := Rat.num_divInt_den r
    rw [Rat.divInt_eq_div] at this
    exact_mod_cast this
  have hA := Float.toRat_ofNat hn
  have hB := Float.toRat_ofNat hd
  have hrn : NormalRange (-r) := by
    unfold NormalRange FloatFormat.NormalRange at hr ⊢
    rw [Rat.abs_neg]
    rcases hr with h | h
    · left; rw [h]; rfl
    · right; exact h
  unfold Rat.toFloat
  by_cases hneg : r.num < 0
  · have ha : ((r.num.natAbs : Nat) : Rat) = -(r.num : Rat) := by
      have : (r.num.natAbs : Int) = -r.num := by omega
      exact_mod_cast this
    have hnd : -(r.num : Rat) / (r.den : Rat) = -r := by
      rw [Rat.div_def, Rat.neg_mul, ← Rat.div_def, hdiv]
    have h := Float.approximates_div hA hB hden (by rw [ha, hnd]; exact hrn)
    rw [ha, hnd] at h
    simp only [hneg, ite_true]
    obtain ⟨q, hq, hb⟩ := h
    refine ⟨-q, ?_, ?_⟩
    · rw [Float.toRat_neg, hq]; rfl
    · have e : -q - r = -(q - -r) := by grind
      rw [e, Rat.abs_neg]
      rwa [Rat.abs_neg] at hb
  · have ha : ((r.num.natAbs : Nat) : Rat) = (r.num : Rat) := by
      have : (r.num.natAbs : Int) = r.num := by omega
      exact_mod_cast this
    have h := Float.approximates_div hA hB hden (by rw [ha, hdiv]; exact hr)
    rw [ha, hdiv] at h
    simp only [hneg, ite_false]
    exact h

end Inkproof.Float
