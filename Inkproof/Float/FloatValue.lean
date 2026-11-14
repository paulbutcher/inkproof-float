/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace Inkproof.Float

/-- `m * 2 ^ e` as a rational. -/
def scaleTwoPow (m : Nat) (e : Int) : Rat :=
  if 0 ≤ e then ((m * 2 ^ e.toNat : Nat) : Rat) else (m : Rat) / ((2 ^ (-e).toNat : Nat) : Rat)

theorem scaleTwoPow_of_nonneg (m : Nat) {e : Int} (h : 0 ≤ e) :
    scaleTwoPow m e = (m : Rat) * ((2 ^ e.toNat : Nat) : Rat) := by
  simp [scaleTwoPow, h]

theorem scaleTwoPow_of_neg (m : Nat) {e : Int} (h : e < 0) :
    scaleTwoPow m e = (m : Rat) / ((2 ^ (-e).toNat : Nat) : Rat) := by
  simp [scaleTwoPow, Int.not_le.mpr h]

theorem scaleTwoPow_zero (e : Int) : scaleTwoPow 0 e = 0 := by
  unfold scaleTwoPow
  split
  · simp
  · rw [Rat.div_def]; simp

theorem scaleTwoPow_one_pos (n : Nat) : (0 : Rat) < scaleTwoPow 1 n := by
  rw [scaleTwoPow_of_nonneg 1 (Int.natCast_nonneg n)]
  have : (0 : Nat) < 2 ^ n := Nat.two_pow_pos n
  simp only [Int.toNat_natCast]
  exact_mod_cast Nat.mul_pos Nat.one_pos this

/-- The exact value of a finite binary64 float, read from its bits; `none` for NaN and the
infinities. Both zeros give `0`. `Float.toRat_eq_value` states that this is the value of the float in
Lean's model. -/
def Float.toRat (x : Float) : Option Rat :=
  let b := x.toBits
  let e := ((b >>> 52) &&& 0x7ff).toNat
  let m := (b &&& 0xfffffffffffff).toNat
  if e = 0x7ff then none
  else
    let mag := if e = 0 then scaleTwoPow m (-1074) else scaleTwoPow (2 ^ 52 + m) (e - 1075)
    some (if b >>> 63 = 0 then mag else -mag)

/-- `x` is neither NaN nor infinite. -/
def Float.IsFinite (x : Float) : Prop := (Float.toRat x).isSome

/-- `|x| ≤ y` exactly when `-y ≤ x ≤ y`. -/
theorem rat_abs_le_iff {x y : Rat} : x.abs ≤ y ↔ -y ≤ x ∧ x ≤ y := by
  unfold Rat.abs; grind

/-- The triangle inequality for `Rat.abs`. -/
theorem rat_abs_add_le (x y : Rat) : (x + y).abs ≤ x.abs + y.abs := by
  unfold Rat.abs; grind

/-- `Rat.abs` of a product is the product of the absolute values. -/
theorem rat_abs_mul (x y : Rat) : (x * y).abs = x.abs * y.abs := by
  unfold Rat.abs
  have h : ∀ a b : Rat, 0 ≤ a → 0 ≤ b → 0 ≤ a * b := fun _ _ => Rat.mul_nonneg
  have := h x y
  have := h (-x) y
  have := h x (-y)
  have := h (-x) (-y)
  grind

/-- A binary floating-point format: `prec` significand bits including the implicit one, and the
largest exponent `maxExp`. The smallest normal exponent is `1 - maxExp`. -/
structure FloatFormat where
  prec : Nat
  maxExp : Nat

def FloatFormat.binary64 : FloatFormat := ⟨53, 1023⟩

def FloatFormat.binary32 : FloatFormat := ⟨24, 127⟩

/-- The largest finite value, `(2 ^ prec - 1) * 2 ^ (maxExp + 1 - prec)`. -/
def FloatFormat.maxFloat (f : FloatFormat) : Rat :=
  scaleTwoPow (2 ^ f.prec - 1) ((f.maxExp : Int) + 1 - f.prec)

/-- The smallest positive normal value, `2 ^ (1 - maxExp)`. -/
def FloatFormat.minNormalFloat (f : FloatFormat) : Rat := scaleTwoPow 1 (1 - (f.maxExp : Int))

/-- An exact result that is zero, or in the normal range of the format: no overflow, no subnormal
rounding. -/
def FloatFormat.NormalRange (f : FloatFormat) (r : Rat) : Prop :=
  r = 0 ∨ (f.minNormalFloat ≤ r.abs ∧ r.abs ≤ f.maxFloat)

instance (f : FloatFormat) (r : Rat) : Decidable (f.NormalRange r) := by
  unfold FloatFormat.NormalRange; infer_instance

/-- The largest finite binary64 value, `(2 ^ 53 - 1) * 2 ^ 971`. -/
def maxFloat : Rat := FloatFormat.binary64.maxFloat

/-- The smallest positive normal binary64 value, `2 ^ -1022`. -/
def minNormalFloat : Rat := FloatFormat.binary64.minNormalFloat

/-- `NormalRange` of binary64. -/
def NormalRange (r : Rat) : Prop := FloatFormat.binary64.NormalRange r

instance (r : Rat) : Decidable (NormalRange r) := by unfold NormalRange; infer_instance

/-- The exact value of a finite binary32 float, read from its bits; `none` for NaN and the
infinities. Both zeros give `0`. `Float32.toRat_eq_value` states that this is the value of the float in
Lean's model. -/
def Float32.toRat (x : Float32) : Option Rat :=
  let b := x.toBits
  let e := ((b >>> 23) &&& 0xff).toNat
  let m := (b &&& 0x7fffff).toNat
  if e = 0xff then none
  else
    let mag := if e = 0 then scaleTwoPow m (-149) else scaleTwoPow (2 ^ 23 + m) (e - 150)
    some (if b >>> 31 = 0 then mag else -mag)

/-- `x` is neither NaN nor infinite. -/
def Float32.IsFinite (x : Float32) : Prop := (Float32.toRat x).isSome

/-- `z` is the value of a finite float within a relative error of `2 ^ -prec`, half an ulp, of `r`. -/
def FloatFormat.Approx (f : FloatFormat) (z : Option Rat) (r : Rat) : Prop :=
  ∃ q, z = some q ∧ (q - r).abs ≤ r.abs / scaleTwoPow 1 f.prec

/-- `z` is finite and within a relative error of `2 ^ -53`, half an ulp, of `r`. -/
def Float.Approximates (z : Float) (r : Rat) : Prop := FloatFormat.binary64.Approx (Float.toRat z) r

/-- `z` is finite and within a relative error of `2 ^ -24`, half an ulp, of `r`. -/
def Float32.Approximates (z : Float32) (r : Rat) : Prop :=
  FloatFormat.binary32.Approx (Float32.toRat z) r

/-- The relative form of `Approx`: the value is `r * (1 + δ)` for some `|δ| ≤ 2 ^ -prec`. -/
theorem FloatFormat.Approx.rel {f : FloatFormat} {z : Option Rat} {r : Rat} (h : f.Approx z r) :
    ∃ q δ, z = some q ∧ δ.abs ≤ 1 / scaleTwoPow 1 f.prec ∧ q = r * (1 + δ) := by
  obtain ⟨q, hq, hb⟩ := h
  have hu := scaleTwoPow_one_pos f.prec
  by_cases hr : r = 0
  · subst hr
    have h0 : (q - 0).abs ≤ 0 := by simpa [Rat.div_def] using hb
    have hq0 : q = 0 := by unfold Rat.abs at h0; grind
    refine ⟨q, 0, hq, ?_, by rw [hq0]; simp⟩
    have : (0 : Rat).abs = 0 := Rat.abs_of_nonneg (Rat.le_refl)
    rw [this]
    simpa [Rat.div_def] using Rat.le_of_lt (Rat.inv_pos.mpr hu)
  · have hrr : r * r⁻¹ = 1 := Rat.mul_inv_cancel _ hr
    have hpos : 0 < r.abs := Rat.abs_pos_iff.mpr hr
    refine ⟨q, (q - r) * r⁻¹, hq, ?_, by grind⟩
    have hm : ((q - r) * r⁻¹).abs * r.abs = (q - r).abs := by
      rw [← rat_abs_mul, Rat.mul_assoc, Rat.inv_mul_cancel _ hr, Rat.mul_one]
    simp only [Rat.div_def] at *
    by_cases h : ((q - r) * r⁻¹).abs ≤ 1 * (scaleTwoPow 1 f.prec)⁻¹
    · exact h
    · have := Rat.mul_lt_mul_of_pos_right (Rat.not_le.mp h) hpos
      rw [hm] at this
      grind

/-- Error composition: if `z` approximates `r` and `r` is within `e` of `s`, then the value is
within `e + (|s| + e) / 2 ^ prec` of `s`. -/
theorem FloatFormat.Approx.error_step {f : FloatFormat} {z : Option Rat} {r s e : Rat}
    (h : f.Approx z r) (hs : (r - s).abs ≤ e) :
    ∃ q, z = some q ∧ (q - s).abs ≤ e + (s.abs + e) / scaleTwoPow 1 f.prec := by
  obtain ⟨q, hq, hb⟩ := h
  refine ⟨q, hq, ?_⟩
  have hu := scaleTwoPow_one_pos f.prec
  have hi : 0 ≤ (scaleTwoPow 1 f.prec)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hu)
  have h2 : r.abs ≤ s.abs + e := by unfold Rat.abs at *; grind
  have h3 := Rat.mul_le_mul_of_nonneg_left h2 hi
  have h4 := rat_abs_add_le (q - r) (r - s)
  simp only [Rat.div_def] at *
  have : q - s = (q - r) + (r - s) := by grind
  rw [this, Rat.mul_comm] at *
  grind

/-- The bound in ulps: a result within `k` ulps, for `k ≥ 1 / 2`, is within `2 * k * |r| / 2 ^ prec`,
as an ulp is at most `|r| * 2 ^ (1 - prec)`. Round to nearest gives `k = 1 / 2`, so the 1 ulp of GLSL
ES 3.00 for `+`, `-`, `*` and fused `a * b + c`, and its 2.5 ulp for `/`, follow. -/
theorem FloatFormat.Approx.ulps {f : FloatFormat} {z : Option Rat} {r k : Rat} (h : f.Approx z r)
    (hk : 1 / 2 ≤ k) :
    ∃ q, z = some q ∧ (q - r).abs ≤ 2 * k * r.abs / scaleTwoPow 1 f.prec := by
  obtain ⟨q, hq, hb⟩ := h
  refine ⟨q, hq, Rat.le_trans hb ?_⟩
  have hu := scaleTwoPow_one_pos f.prec
  have hi : 0 ≤ (scaleTwoPow 1 f.prec)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hu)
  have ha : 0 ≤ r.abs := Rat.abs_nonneg
  simp only [Rat.div_def]
  have h2 : 1 ≤ 2 * k := by grind
  have := Rat.mul_le_mul_of_nonneg_left h2 (Rat.mul_nonneg ha hi)
  grind

namespace Float

theorem Approximates.rel {z : Float} {r : Rat} (h : Float.Approximates z r) :
    ∃ q δ, Float.toRat z = some q ∧ δ.abs ≤ 1 / scaleTwoPow 1 53 ∧ q = r * (1 + δ) := by
  have := FloatFormat.Approx.rel h
  rwa [show ((FloatFormat.binary64.prec : Nat) : Int) = 53 from rfl] at this

theorem Approximates.error_step {z : Float} {r s e : Rat} (h : Float.Approximates z r)
    (hs : (r - s).abs ≤ e) :
    ∃ q, Float.toRat z = some q ∧ (q - s).abs ≤ e + (s.abs + e) / scaleTwoPow 1 53 := by
  have := FloatFormat.Approx.error_step h hs
  rwa [show ((FloatFormat.binary64.prec : Nat) : Int) = 53 from rfl] at this

end Float

namespace Float32

theorem Approximates.rel {z : Float32} {r : Rat} (h : Float32.Approximates z r) :
    ∃ q δ, Float32.toRat z = some q ∧ δ.abs ≤ 1 / scaleTwoPow 1 24 ∧ q = r * (1 + δ) := by
  have := FloatFormat.Approx.rel h
  rwa [show ((FloatFormat.binary32.prec : Nat) : Int) = 24 from rfl] at this

theorem Approximates.error_step {z : Float32} {r s e : Rat} (h : Float32.Approximates z r)
    (hs : (r - s).abs ≤ e) :
    ∃ q, Float32.toRat z = some q ∧ (q - s).abs ≤ e + (s.abs + e) / scaleTwoPow 1 24 := by
  have := FloatFormat.Approx.error_step h hs
  rwa [show ((FloatFormat.binary32.prec : Nat) : Int) = 24 from rfl] at this

end Float32

end Inkproof.Float
