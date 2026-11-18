/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Float.FloatValue

/-! A relative-tolerance comparison of floats. -/

namespace Inkproof.Float

/-- `a` and `b` are finite and differ by at most `tol * (1 + |a| + |b|)`: a relative tolerance for
large values and an absolute one near zero. Infinite operands are never near anything, since
`∞ ≤ tol * ∞` would otherwise hold. -/
def Float.near (a b : Float) (tol : Float := 1e-6) : Bool :=
  a.isFinite && b.isFinite && (a - b).abs ≤ tol * (1 + a.abs + b.abs)

theorem Float.near_iff {a b tol : Float} :
    Float.near a b tol = true ↔
      a.isFinite = true ∧ b.isFinite = true ∧ (a - b).abs ≤ tol * (1 + a.abs + b.abs) := by
  simp [Float.near, and_assoc]

theorem Float.near_isFinite {a b tol : Float} (h : Float.near a b tol = true) :
    a.isFinite = true ∧ b.isFinite = true :=
  ⟨(Float.near_iff.1 h).1, (Float.near_iff.1 h).2.1⟩

private theorem isFinite_false_of_isNaN {x : Float} (h : x.isNaN = true) : x.isFinite = false := by
  have h' : x.toModel.unpack.isNaN = true := by simpa [Float.isNaN, Float.Model.isNaN] using h
  simp only [Float.isFinite, Float.Model.isFinite]
  cases hu : x.toModel.unpack <;> simp_all [Float.Model.UnpackedFloat.isNaN,
    Float.Model.UnpackedFloat.isFinite]

/-- A NaN is not near anything, itself included. -/
theorem Float.near_nan_left {a : Float} (h : a.isNaN = true) (b tol : Float) :
    Float.near a b tol = false := by
  have := isFinite_false_of_isNaN h
  simp [Float.near, this]

theorem Float.near_nan_right (a : Float) {b : Float} (h : b.isNaN = true) (tol : Float) :
    Float.near a b tol = false := by
  have := isFinite_false_of_isNaN h
  simp [Float.near, this]

end Inkproof.Float
