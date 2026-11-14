/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Float.FloatValue

/-! Every axiom the library adds to Lean's, and nothing else. A check in the test subproject fails
if a published theorem depends on an axiom that is not here or in Lean itself. -/

namespace Inkproof.Float

/-- FP-3: the rounding model of Lean's `Float`, which is IEEE 754 binary64 with round to nearest even.
Three parts, all about the exact value `Float.toRat` of finite floats:
- `≤` agrees with `≤` on exact values.
- A literal `n`, for `n < 2 ^ 53`, is exactly `n`.
- Where the exact result of `+`, `-`, `*` or `/` (`y ≠ 0`) of two finite floats, or of the fused
  `Float.fma`, is zero or in the normal range, the computed float is finite and within half an ulp of
  it, which is a relative error of at most `2 ^ -53`.

Lean defines `Float` over a model of IEEE 754 binary64, but proves nothing about its rounding, so this
is assumed. The first two parts are provable from the model; the third needs the error theory of
round to nearest, which DESIGN.md assesses. What stays trusted is that Lean's compiled float
operations match the model. Binary32 has its own statement, `float32_rounding_model`. The test
subproject checks both against compiled code, natively and under Lasm. -/
axiom float_rounding_model :
    (∀ x y : Float, Float.IsFinite x → Float.IsFinite y →
      (x ≤ y ↔ ∃ a b, Float.toRat x = some a ∧ Float.toRat y = some b ∧ a ≤ b)) ∧
    (∀ n : Nat, n < 2 ^ 53 → Float.toRat (OfNat.ofNat n) = some (n : Rat)) ∧
    (∀ (x y : Float) (a b : Rat), Float.toRat x = some a → Float.toRat y = some b →
      (NormalRange (a + b) → Float.Approximates (x + y) (a + b)) ∧
      (NormalRange (a - b) → Float.Approximates (x - y) (a - b)) ∧
      (NormalRange (a * b) → Float.Approximates (x * y) (a * b)) ∧
      (b ≠ 0 → NormalRange (a / b) → Float.Approximates (x / y) (a / b))) ∧
    (∀ (x y z : Float) (a b c : Rat), Float.toRat x = some a → Float.toRat y = some b →
      Float.toRat z = some c → NormalRange (a * b + c) →
      Float.Approximates (Float.fma x y z) (a * b + c))

/-- FP-3 for `Float32`, IEEE 754 binary32 with round to nearest even: `float_rounding_model` with
precision 24, so integer literals are exact below `2 ^ 24` and the relative error is at most `2 ^ -24`. -/
axiom float32_rounding_model :
    (∀ x y : Float32, Float32.IsFinite x → Float32.IsFinite y →
      (x ≤ y ↔ ∃ a b, Float32.toRat x = some a ∧ Float32.toRat y = some b ∧ a ≤ b)) ∧
    (∀ n : Nat, n < 2 ^ 24 → Float32.toRat (OfNat.ofNat n) = some (n : Rat)) ∧
    (∀ (x y : Float32) (a b : Rat), Float32.toRat x = some a → Float32.toRat y = some b →
      (FloatFormat.binary32.NormalRange (a + b) → Float32.Approximates (x + y) (a + b)) ∧
      (FloatFormat.binary32.NormalRange (a - b) → Float32.Approximates (x - y) (a - b)) ∧
      (FloatFormat.binary32.NormalRange (a * b) → Float32.Approximates (x * y) (a * b)) ∧
      (b ≠ 0 → FloatFormat.binary32.NormalRange (a / b) → Float32.Approximates (x / y) (a / b))) ∧
    (∀ (x y z : Float32) (a b c : Rat), Float32.toRat x = some a → Float32.toRat y = some b →
      Float32.toRat z = some c → FloatFormat.binary32.NormalRange (a * b + c) →
      Float32.Approximates (Float32.fma x y z) (a * b + c))

namespace Float

theorem toRat_mono {x y : Float} {a b : Rat} (hx : Float.toRat x = some a) (hy : Float.toRat y = some b)
    (h : x ≤ y) : a ≤ b := by
  obtain ⟨a', b', ha, hb, hab⟩ :=
    (float_rounding_model.1 x y (by simp [IsFinite, hx]) (by simp [IsFinite, hy])).1 h
  simp_all

theorem le_of_toRat_le {x y : Float} {a b : Rat} (hx : Float.toRat x = some a) (hy : Float.toRat y = some b)
    (h : a ≤ b) : x ≤ y :=
  (float_rounding_model.1 x y (by simp [IsFinite, hx]) (by simp [IsFinite, hy])).2
    ⟨a, b, hx, hy, h⟩

theorem toRat_ofNat {n : Nat} (h : n < 2 ^ 53) : Float.toRat (OfNat.ofNat n : Float) = some (n : Rat) :=
  float_rounding_model.2.1 n h

theorem approximates_add {x y : Float} {a b : Rat} (hx : Float.toRat x = some a) (hy : Float.toRat y = some b)
    (h : NormalRange (a + b)) : Float.Approximates (x + y) (a + b) :=
  (float_rounding_model.2.2.1 x y a b hx hy).1 h

theorem approximates_sub {x y : Float} {a b : Rat} (hx : Float.toRat x = some a) (hy : Float.toRat y = some b)
    (h : NormalRange (a - b)) : Float.Approximates (x - y) (a - b) :=
  (float_rounding_model.2.2.1 x y a b hx hy).2.1 h

theorem approximates_mul {x y : Float} {a b : Rat} (hx : Float.toRat x = some a) (hy : Float.toRat y = some b)
    (h : NormalRange (a * b)) : Float.Approximates (x * y) (a * b) :=
  (float_rounding_model.2.2.1 x y a b hx hy).2.2.1 h

theorem approximates_div {x y : Float} {a b : Rat} (hx : Float.toRat x = some a) (hy : Float.toRat y = some b)
    (hb : b ≠ 0) (h : NormalRange (a / b)) : Float.Approximates (x / y) (a / b) :=
  (float_rounding_model.2.2.1 x y a b hx hy).2.2.2 hb h

theorem approximates_fma {x y z : Float} {a b c : Rat} (hx : Float.toRat x = some a)
    (hy : Float.toRat y = some b) (hz : Float.toRat z = some c) (h : NormalRange (a * b + c)) :
    Float.Approximates (Float.fma x y z) (a * b + c) :=
  float_rounding_model.2.2.2 x y z a b c hx hy hz h

end Float

namespace Float32

theorem toRat_mono {x y : Float32} {a b : Rat} (hx : Float32.toRat x = some a)
    (hy : Float32.toRat y = some b) (h : x ≤ y) : a ≤ b := by
  obtain ⟨a', b', ha, hb, hab⟩ :=
    (float32_rounding_model.1 x y (by simp [IsFinite, hx]) (by simp [IsFinite, hy])).1 h
  simp_all

theorem le_of_toRat_le {x y : Float32} {a b : Rat} (hx : Float32.toRat x = some a)
    (hy : Float32.toRat y = some b) (h : a ≤ b) : x ≤ y :=
  (float32_rounding_model.1 x y (by simp [IsFinite, hx]) (by simp [IsFinite, hy])).2
    ⟨a, b, hx, hy, h⟩

theorem toRat_ofNat {n : Nat} (h : n < 2 ^ 24) :
    Float32.toRat (OfNat.ofNat n : Float32) = some (n : Rat) :=
  float32_rounding_model.2.1 n h

theorem approximates_add {x y : Float32} {a b : Rat} (hx : Float32.toRat x = some a)
    (hy : Float32.toRat y = some b) (h : FloatFormat.binary32.NormalRange (a + b)) :
    Float32.Approximates (x + y) (a + b) :=
  (float32_rounding_model.2.2.1 x y a b hx hy).1 h

theorem approximates_sub {x y : Float32} {a b : Rat} (hx : Float32.toRat x = some a)
    (hy : Float32.toRat y = some b) (h : FloatFormat.binary32.NormalRange (a - b)) :
    Float32.Approximates (x - y) (a - b) :=
  (float32_rounding_model.2.2.1 x y a b hx hy).2.1 h

theorem approximates_mul {x y : Float32} {a b : Rat} (hx : Float32.toRat x = some a)
    (hy : Float32.toRat y = some b) (h : FloatFormat.binary32.NormalRange (a * b)) :
    Float32.Approximates (x * y) (a * b) :=
  (float32_rounding_model.2.2.1 x y a b hx hy).2.2.1 h

theorem approximates_div {x y : Float32} {a b : Rat} (hx : Float32.toRat x = some a)
    (hy : Float32.toRat y = some b) (hb : b ≠ 0) (h : FloatFormat.binary32.NormalRange (a / b)) :
    Float32.Approximates (x / y) (a / b) :=
  (float32_rounding_model.2.2.1 x y a b hx hy).2.2.2 hb h

theorem approximates_fma {x y z : Float32} {a b c : Rat} (hx : Float32.toRat x = some a)
    (hy : Float32.toRat y = some b) (hz : Float32.toRat z = some c)
    (h : FloatFormat.binary32.NormalRange (a * b + c)) :
    Float32.Approximates (Float32.fma x y z) (a * b + c) :=
  float32_rounding_model.2.2.2 x y z a b c hx hy hz h

end Float32

end Inkproof.Float
