/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Float.Internal.Exact

/-! `≤` and integer literals of `Float` and `Float32`, in terms of their exact values, proved from
Lean's model of the floats. -/

namespace Inkproof.Float

open Float.Model Internal.Exact

private theorem Float.le_iff_toRat {x y : Float} {a b : Rat} (hx : Float.toRat x = some a)
    (hy : Float.toRat y = some b) : x ≤ y ↔ a ≤ b := by
  rw [Float.toRat_eq_value] at hx hy
  exact compare_le_iff (by decide) (unpack_canon _) (unpack_canon _) hx hy

private theorem Float32.le_iff_toRat {x y : Float32} {a b : Rat} (hx : Float32.toRat x = some a)
    (hy : Float32.toRat y = some b) : x ≤ y ↔ a ≤ b := by
  rw [Float32.toRat_eq_value] at hx hy
  exact compare_le_iff (by decide) (unpack_canon32 _) (unpack_canon32 _) hx hy

theorem Float.toRat_mono {x y : Float} {a b : Rat} (hx : Float.toRat x = some a)
    (hy : Float.toRat y = some b) (h : x ≤ y) : a ≤ b :=
  (Float.le_iff_toRat hx hy).mp h

theorem Float.le_of_toRat_le {x y : Float} {a b : Rat} (hx : Float.toRat x = some a)
    (hy : Float.toRat y = some b) (h : a ≤ b) : x ≤ y :=
  (Float.le_iff_toRat hx hy).mpr h

theorem Float.toRat_ofNat {n : Nat} (h : n < 2 ^ 53) :
    Float.toRat (OfNat.ofNat n : Float) = some (n : Rat) := by
  have hf : (OfNat.ofNat n : Float) = n.toUInt64.toFloat * Float.ofBits 0x3FF0000000000000 := by
    show Float.ofScientific n false 0 = _
    unfold Float.ofScientific
    simp only [show n < 2 ^ 53 ∧ 0 ≤ 22 from ⟨h, by decide⟩]
    rfl
  have hn : n.toUInt64.toNat = n := by
    simp only [Nat.toUInt64]
    exact Nat.mod_eq_of_lt (by omega)
  have hlt : n < 2 ^ Format.binary64.mantissaBits := h
  have hA : n.toUInt64.toFloat.toModel.unpack = UnpackedFloat.ofNat Format.binary64 n := by
    have e1 : n.toUInt64.toFloat.toModel =
        Float.Model.pack (UnpackedFloat.ofNat Format.binary64 n.toUInt64.toNat) := rfl
    rw [e1, hn]
    exact unpack_pack_ofNat Format.binary64 hlt (by decide)
  have hB : (Float.ofBits 0x3FF0000000000000).toModel.unpack =   .finite .positive (2 ^ (Format.binary64.mantissaBits - 1))
      (-((Format.binary64.mantissaBits - 1 : Nat) : Int)) (Nat.two_pow_pos _) := rfl
  have hM : (n.toUInt64.toFloat * Float.ofBits 0x3FF0000000000000).toModel.unpack =
      UnpackedFloat.ofNat Format.binary64 n := by
    have e2 : (n.toUInt64.toFloat * Float.ofBits 0x3FF0000000000000).toModel =
        Float.Model.pack (UnpackedFloat.mul Format.binary64 n.toUInt64.toFloat.toModel.unpack
          (Float.ofBits 0x3FF0000000000000).toModel.unpack) := rfl
    rw [e2, hA, hB]
    show UnpackedFloat.unpack Format.binary64 (UnpackedFloat.pack Format.binary64 _) = _
    rw [mul_one_ofNat Format.binary64 hlt]
    exact unpack_pack_ofNat Format.binary64 hlt (by decide)
  rw [hf, Float.toRat_eq_value, hM]
  exact ofNat_value Format.binary64 hlt

theorem Float32.toRat_mono {x y : Float32} {a b : Rat} (hx : Float32.toRat x = some a)
    (hy : Float32.toRat y = some b) (h : x ≤ y) : a ≤ b :=
  (Float32.le_iff_toRat hx hy).mp h

theorem Float32.le_of_toRat_le {x y : Float32} {a b : Rat} (hx : Float32.toRat x = some a)
    (hy : Float32.toRat y = some b) (h : a ≤ b) : x ≤ y :=
  (Float32.le_iff_toRat hx hy).mpr h

theorem Float32.toRat_ofNat {n : Nat} (h : n < 2 ^ 24) :
    Float32.toRat (OfNat.ofNat n : Float32) = some (n : Rat) := by
  have hlt : n < 2 ^ Format.binary32.mantissaBits := h
  by_cases hs : n < 2 ^ 23
  · have hf : (OfNat.ofNat n : Float32) =
        n.toUInt64.toFloat32 * Float32.ofBits 0x3F800000 := by
      show Float32.ofScientific n false 0 = _
      unfold Float32.ofScientific
      simp only [show n < 2 ^ 23 ∧ 0 ≤ 10 from ⟨hs, by decide⟩]
      rfl
    have hn : n.toUInt64.toNat = n := by
      simp only [Nat.toUInt64]
      exact Nat.mod_eq_of_lt (by omega)
    have hA : n.toUInt64.toFloat32.toModel.unpack = UnpackedFloat.ofNat Format.binary32 n := by
      have e1 : n.toUInt64.toFloat32.toModel =
          Float32.Model.pack (UnpackedFloat.ofNat Format.binary32 n.toUInt64.toNat) := rfl
      rw [e1, hn]
      exact unpack_pack_ofNat Format.binary32 hlt (by decide)
    have hB : (Float32.ofBits 0x3F800000).toModel.unpack = .finite .positive
        (2 ^ (Format.binary32.mantissaBits - 1)) (-((Format.binary32.mantissaBits - 1 : Nat) : Int))
        (Nat.two_pow_pos _) := rfl
    have hM : (n.toUInt64.toFloat32 * Float32.ofBits 0x3F800000).toModel.unpack =
        UnpackedFloat.ofNat Format.binary32 n := by
      have e2 : (n.toUInt64.toFloat32 * Float32.ofBits 0x3F800000).toModel =
          Float32.Model.pack (UnpackedFloat.mul Format.binary32 n.toUInt64.toFloat32.toModel.unpack
            (Float32.ofBits 0x3F800000).toModel.unpack) := rfl
      rw [e2, hA, hB]
      show UnpackedFloat.unpack Format.binary32 (UnpackedFloat.pack Format.binary32 _) = _
      rw [mul_one_ofNat Format.binary32 hlt]
      exact unpack_pack_ofNat Format.binary32 hlt (by decide)
    rw [hf, Float32.toRat_eq_value, hM]
    exact ofNat_value Format.binary32 hlt
  · have hf : (OfNat.ofNat n : Float32) =
        Float32.ofModel (Float32.Model.ofScientific n 0) := by
      show Float32.ofScientific n false 0 = _
      unfold Float32.ofScientific
      simp only [show ¬(n < 2 ^ 23 ∧ 0 ≤ 10) from fun h => hs h.1]
      rfl
    have hM : (Float32.ofModel (Float32.Model.ofScientific n 0)).toModel.unpack =
        UnpackedFloat.ofNat Format.binary32 n := by
      show UnpackedFloat.unpack Format.binary32
        (UnpackedFloat.pack Format.binary32 (UnpackedFloat.ofScientific Format.binary32 n 0)) = _
      rw [ofScientific_eq_ofNat Format.binary32 (by show 2 ^ 23 ≤ n; omega) hlt]
      exact unpack_pack_ofNat Format.binary32 hlt (by decide)
    rw [hf, Float32.toRat_eq_value, hM]
    exact ofNat_value Format.binary32 hlt

end Inkproof.Float
