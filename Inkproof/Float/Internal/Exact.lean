/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Float.FloatModel

/-! Exact values of unpacked floats: the order of `Float.Model.UnpackedFloat.compare` and the
exactness of integers, for any format. -/

namespace Inkproof.Float.Internal.Exact

open Float.Model Float.Model.UnpackedFloat

theorem scaleTwoPow_eq_mul (m : Nat) (e : Int) : scaleTwoPow m e = (m : Rat) * scaleTwoPow 1 e := by
  unfold scaleTwoPow
  split
  · simp
  · simp [Rat.div_def]

theorem scaleTwoPow_succ (e : Int) : scaleTwoPow 1 (e + 1) = 2 * scaleTwoPow 1 e := by
  unfold scaleTwoPow
  by_cases h : 0 ≤ e
  · have h1 : 0 ≤ e + 1 := by omega
    have : (e + 1).toNat = e.toNat + 1 := by omega
    simp [h, h1, this, Nat.pow_succ]
    grind
  · by_cases h2 : 0 ≤ e + 1
    · have : e = -1 := by omega
      subst this
      simp [Rat.div_def]
      grind
    · have h3 : (-(e+1)).toNat + 1 = (-e).toNat := by omega
      simp only [h, h2, ite_false, Rat.div_def]
      rw [← h3]
      simp only [Nat.pow_succ]
      push_cast
      grind

theorem scaleTwoPow_pos (e : Int) : 0 < scaleTwoPow 1 e := by
  unfold scaleTwoPow
  split
  · have : (0 : Nat) < 2 ^ e.toNat := Nat.two_pow_pos _
    simp; exact_mod_cast this
  · simp [Rat.div_def]; exact Rat.inv_pos.mpr (by exact_mod_cast Nat.two_pow_pos _)

theorem scaleTwoPow_add_nat (e : Int) (k : Nat) :
    scaleTwoPow 1 (e + k) = (2 ^ k : Nat) * scaleTwoPow 1 e := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show e + ((k + 1 : Nat) : Int) = (e + k) + 1 by omega, scaleTwoPow_succ, ih, Nat.pow_succ]
    push_cast
    grind

/-- An unpacked float that is zero, or finite with the mantissa and exponent of a float of
precision `p` and smallest exponent `emin`. -/
def CanonFor (emin : Int) (p : Nat) : UnpackedFloat → Prop
  | .finite _ m e _ => emin ≤ e ∧ m < 2 ^ p ∧ (e = emin ∨ 2 ^ (p - 1) ≤ m)
  | _ => True

theorem scaleTwoPow_lt {p m m' : Nat} {e e' : Int} (hp : 1 ≤ p) (hm : m < 2 ^ p)
    (hm' : 2 ^ (p - 1) ≤ m') (he : e < e') : scaleTwoPow m e < scaleTwoPow m' e' := by
  obtain ⟨k, rfl⟩ : ∃ k : Nat, e' = e + ((k + 1 : Nat) : Int) := ⟨(e' - e - 1).toNat, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [scaleTwoPow_eq_mul, scaleTwoPow_eq_mul m', scaleTwoPow_add_nat]
  have hz := scaleTwoPow_pos e
  have h1 : (m : Rat) < ((2 ^ (q + 1) : Nat) : Rat) := by exact_mod_cast hm
  have h2 : (((2 ^ (q + 1) : Nat)) : Rat) ≤ (m' : Rat) * ((2 ^ (k + 1) : Nat) : Rat) := by
    have h5 : 2 ≤ 2 ^ (k + 1) := by
      have := Nat.one_lt_two_pow (n := k + 1) (by omega)
      omega
    have : 2 ^ (q + 1) ≤ m' * 2 ^ (k + 1) := by
      rw [Nat.pow_succ]
      exact Nat.mul_le_mul (by simpa using hm') h5
    exact_mod_cast this
  have h3 := Rat.mul_lt_mul_of_pos_right h1 hz
  have h4 := Rat.mul_le_mul_of_nonneg_right h2 (Rat.le_of_lt hz)
  rw [← Rat.mul_assoc]
  grind

theorem scaleTwoPow_pos' {m : Nat} (e : Int) (hm : 0 < m) : 0 < scaleTwoPow m e := by
  rw [scaleTwoPow_eq_mul]
  exact Rat.mul_pos (by exact_mod_cast hm) (scaleTwoPow_pos e)

theorem scaleTwoPow_lt_canon {emin : Int} {p m m' : Nat} {e e' : Int} (hp : 1 ≤ p)
    (hu : emin ≤ e ∧ m < 2 ^ p ∧ (e = emin ∨ 2 ^ (p - 1) ≤ m))
    (hv : emin ≤ e' ∧ m' < 2 ^ p ∧ (e' = emin ∨ 2 ^ (p - 1) ≤ m')) (he : e < e') :
    scaleTwoPow m e < scaleTwoPow m' e' := by
  refine scaleTwoPow_lt hp hu.2.1 ?_ he
  rcases hv.2.2 with h | h
  · omega
  · exact h

theorem scaleTwoPow_mono_mant {m m' : Nat} (e : Int) (h : m ≤ m') :
    scaleTwoPow m e ≤ scaleTwoPow m' e := by
  rw [scaleTwoPow_eq_mul, scaleTwoPow_eq_mul m']
  exact Rat.mul_le_mul_of_nonneg_right (by exact_mod_cast h) (Rat.le_of_lt (scaleTwoPow_pos e))

theorem scaleTwoPow_lt_mant {m m' : Nat} (e : Int) (h : m < m') :
    scaleTwoPow m e < scaleTwoPow m' e := by
  rw [scaleTwoPow_eq_mul, scaleTwoPow_eq_mul m']
  exact Rat.mul_lt_mul_of_pos_right (by exact_mod_cast h) (scaleTwoPow_pos e)

theorem canon_le_iff {emin : Int} {p m m' : Nat} {e e' : Int} (hp : 1 ≤ p)
    (hu : emin ≤ e ∧ m < 2 ^ p ∧ (e = emin ∨ 2 ^ (p - 1) ≤ m))
    (hv : emin ≤ e' ∧ m' < 2 ^ p ∧ (e' = emin ∨ 2 ^ (p - 1) ≤ m')) :
    ((compare e e').then (compare m m')).isLE = true ↔ scaleTwoPow m e ≤ scaleTwoPow m' e' := by
  rcases Int.lt_trichotomy e e' with h | h | h
  · have := scaleTwoPow_lt_canon hp hu hv h
    simp [Int.compare_eq_lt.mpr h, Ordering.then, Rat.le_of_lt this]
  · subst h
    simp only [Int.compare_eq_eq.mpr rfl, Ordering.then]
    by_cases h3 : m ≤ m'
    · have : compare m m' ≠ .gt := fun h => Nat.not_le.mpr (Nat.compare_eq_gt.mp h) h3
      have h5 : (compare m m').isLE = true := by
        cases h : compare m m' <;> simp_all [Ordering.isLE]
      simp [h5, scaleTwoPow_mono_mant e h3]
    · have h4 := scaleTwoPow_lt_mant e (Nat.not_le.mp h3)
      have : compare m m' = .gt := Nat.compare_eq_gt.mpr (Nat.not_le.mp h3)
      simp [this, Rat.not_le.mpr h4, Ordering.isLE]
  · have h4 := scaleTwoPow_lt_canon hp hv hu h
    simp [Int.compare_eq_gt.mpr h, Ordering.then, Rat.not_le.mpr h4]

theorem compare_le_iff {emin : Int} {p : Nat} (hp : 1 ≤ p) {u v : UnpackedFloat} {a b : Rat}
    (hu : CanonFor emin p u) (hv : CanonFor emin p v) (ha : unpackedValue u = some a)
    (hb : unpackedValue v = some b) : (u.compare v).any (·.isLE) = true ↔ a ≤ b := by
  rcases u with (_|_) | _ | (_|_) | ⟨(_|_), m, e, hm⟩ <;>
  rcases v with (_|_) | _ | (_|_) | ⟨(_|_), m', e', hm'⟩ <;>
  simp only [unpackedValue, Option.some.injEq, reduceCtorEq, CanonFor] at ha hb hu hv <;>
  subst ha hb <;>
  simp [UnpackedFloat.compare, Ordering.isLE]
  all_goals try have := scaleTwoPow_pos' e hm
  all_goals try have := scaleTwoPow_pos' e' hm'
  case finite.negative.finite.negative =>
    have key := canon_le_iff hp hv hu
    rw [← Int.compare_swap e e', ← Nat.compare_swap m m', ← Ordering.swap_then] at key
    exact key
  case finite.positive.finite.positive =>
    exact canon_le_iff hp hu hv
  all_goals grind

open FloatModel in
theorem unpack_canon (b : BitVec 64) : CanonFor (-1074) 53 (UnpackedFloat.unpack Format.binary64 b) := by
  refine unpack_cases b (CanonFor (-1074) 53) ?_ ?_ ?_ ?_ ?_ <;> intros <;> simp only [CanonFor]
  · have := Nat.mod_lt b.toNat (show 0 < 2 ^ 52 by decide)
    simp
    omega
  · have := Nat.mod_lt b.toNat (show 0 < 2 ^ 52 by decide)
    have := Nat.mod_lt (b.toNat / 2 ^ 52) (show 0 < 2 ^ 11 by decide)
    simp
    omega

open FloatModel in
theorem unpack_canon32 (b : BitVec 32) : CanonFor (-149) 24 (UnpackedFloat.unpack Format.binary32 b) := by
  refine unpack_cases32 b (CanonFor (-149) 24) ?_ ?_ ?_ ?_ ?_ <;> intros <;> simp only [CanonFor]
  · have := Nat.mod_lt b.toNat (show 0 < 2 ^ 23 by decide)
    simp
    omega
  · have := Nat.mod_lt b.toNat (show 0 < 2 ^ 23 by decide)
    have := Nat.mod_lt (b.toNat / 2 ^ 23) (show 0 < 2 ^ 8 by decide)
    simp
    omega

theorem log2_mul_two_pow {m : Nat} (k : Nat) (hm : m ≠ 0) : (m * 2 ^ k).log2 = m.log2 + k := by
  have hk : 0 < 2 ^ k := Nat.two_pow_pos k
  have h0 : m * 2 ^ k ≠ 0 := Nat.mul_ne_zero hm (by omega)
  rw [Nat.log2_eq_iff h0]
  have h1 := Nat.log2_self_le hm
  have h2 := @Nat.lt_log2_self m
  constructor
  · rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ h1
  · rw [show m.log2 + k + 1 = (m.log2 + 1) + k by omega, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right h2 hk

theorem totalExponent_mul_two_pow {m : Nat} (hm : m ≠ 0) (e : Int) (k : Nat) :
    totalExponent (m * 2 ^ k) (e - k) = totalExponent m e := by
  unfold totalExponent
  rw [log2_mul_two_pow k hm]
  omega

theorem totalExponent_canon {p : Nat} {m : Nat} {e emin : Int} (hm : m ≠ 0)
    (h : m < 2 ^ p ∧ (e = emin ∨ 2 ^ (p - 1) ≤ m)) (hp : 1 ≤ p) :
    totalExponent m e = e + p ∨ (e = emin ∧ totalExponent m e ≤ e + p) := by
  have hl := (Nat.log2_lt hm).mpr h.1
  unfold totalExponent
  rcases h.2 with h2 | h2
  · right; omega
  · left
    have := (Nat.le_log2 hm).mpr h2
    omega

theorem targetExponent_canon (spec : Format) {m : Nat} {e : Int} (hm : m ≠ 0)
    (h : spec.minExponent ≤ e ∧ m < 2 ^ spec.mantissaBits ∧
      (e = spec.minExponent ∨ 2 ^ (spec.mantissaBits - 1) ≤ m)) :
    spec.targetExponent (totalExponent m e) = e := by
  have hp : 1 ≤ spec.mantissaBits := by unfold Format.mantissaBits; omega
  unfold Format.targetExponent
  rcases totalExponent_canon hm h.2 hp with h1 | ⟨h1, h2⟩
  · omega
  · omega

theorem repeat_succ' {α : Type} (f : α → α) (n : Nat) (a : α) :
    Nat.repeat f (n + 1) a = Nat.repeat f n (f a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => rw [Nat.repeat, ih]; rfl

theorem shiftRight_exact (k m : Nat) :
    ((⟨m * 2 ^ k, false, false⟩ : ExtendedMantissa) >>> k) = ⟨m, false, false⟩ := by
  induction k generalizing m with
  | zero => simp; rfl
  | succ k ih =>
    show Nat.repeat ExtendedMantissa.shiftRightOne (k + 1) _ = _
    rw [repeat_succ']
    have : ExtendedMantissa.shiftRightOne ⟨m * 2 ^ (k + 1), false, false⟩ = ⟨m * 2 ^ k, false, false⟩ := by
      have h : m * 2 ^ (k + 1) = 2 * (m * 2 ^ k) := by rw [Nat.pow_succ]; ac_rfl
      simp [ExtendedMantissa.shiftRightOne, h]
    rw [this]
    exact ih m

/-- Rounding an exact value that is already a float of the format leaves it as it is, however many
trailing zero bits its mantissa carries. -/
theorem roundWithAccuracy_exact (spec : Format) (s : Sign) {m : Nat} {e : Int} (hm : 0 < m)
    (h : spec.minExponent ≤ e ∧ m < 2 ^ spec.mantissaBits ∧
      (e = spec.minExponent ∨ 2 ^ (spec.mantissaBits - 1) ≤ m)) (k : Nat) :
    roundWithAccuracy spec s (m * 2 ^ k) (e - k) .exact = .finite s m e hm := by
  have hm0 : m ≠ 0 := by omega
  have ht := targetExponent_canon spec hm0 h
  have ht' : spec.targetExponent (totalExponent (m * 2 ^ k) (e - k)) = e := by
    rw [totalExponent_mul_two_pow hm0]; exact ht
  have hk : ((e : Int) - (e - k)).toNat = k := by omega
  have h1 : shiftToTargetExponent spec (m * 2 ^ k) (e - k) .exact = (⟨m, false, false⟩, e) := by
    unfold shiftToTargetExponent shiftToExponent
    rw [ht']
    dsimp only
    rw [hk]
    have : ExtendedMantissa.ofMantissaAndAccuracy (m * 2 ^ k) .exact = ⟨m * 2 ^ k, false, false⟩ := rfl
    rw [this, shiftRight_exact]
    simp
  have h2 : shiftToTargetExponent spec m e .exact = (⟨m, false, false⟩, e) := by
    unfold shiftToTargetExponent shiftToExponent
    rw [ht]
    dsimp only
    simp
    rfl
  unfold roundWithAccuracy
  simp only [h1, ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
    Accuracy.roundToNearestEven, h2]
  simp [Nat.pos_iff_ne_zero.mp hm]

theorem unpackSign_packComponents {spec : Format} {sign exponent mantissa} :
    unpackSign (packComponents spec sign exponent mantissa) = sign.toBitVec := by
  ext i hi
  simp [unpackSign, packComponents, BitVec.getLsbD_append]
  split
  · omega
  · split
    · omega
    · rw [show _ - _ - _ = i by omega]
      simp [BitVec.getLsbD_eq_getElem hi]

theorem ofBitVec_toBitVec (s : Sign) : Sign.ofBitVec s.toBitVec = s := by
  cases s <;> decide

theorem negOne_toNat (w : Nat) : (-1#w).toNat = 2 ^ w - 1 := by
  simp [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes]

theorem unpack_pack_finite (spec : Format) (s : Sign) {m : Nat} {e : Int} (hm : 0 < m)
    (h : spec.minExponent ≤ e ∧ m < 2 ^ spec.mantissaBits ∧
      (e = spec.minExponent ∨ 2 ^ (spec.mantissaBits - 1) ≤ m))
    (hmax : e + spec.exponentBias + spec.mantissaBitsWithoutImplicit + 1 < ((2 ^ spec.exponentBits : Nat) : Int)) :
    UnpackedFloat.unpack spec (UnpackedFloat.pack spec (.finite s m e hm)) = .finite s m e hm := by
  have hB : 2 ^ spec.exponentBits = 2 * 2 ^ (spec.exponentBits - 1) := by
    rw [← Nat.pow_succ']; congr 1; have := spec.he; omega
  have hB2 : 2 ≤ 2 ^ (spec.exponentBits - 1) := by
    have := spec.he
    calc 2 = 2 ^ 1 := rfl
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have hmb := spec.hm
  obtain ⟨hmin, hlt, hc⟩ := h
  have hmant : spec.mantissaBits = 1 + spec.mantissaBitsWithoutImplicit := rfl
  have hbias : spec.exponentBias = 2 ^ (spec.exponentBits - 1) - 1 := rfl
  have hminE : spec.minExponent = 3 - ((2 ^ (spec.exponentBits - 1) : Nat) : Int) - spec.mantissaBits := by
    show _ = _
    push_cast
    rfl
  have hP2 : 2 ^ spec.mantissaBits = 2 * 2 ^ spec.mantissaBitsWithoutImplicit := by
    rw [hmant, ← Nat.pow_succ']; congr 1; omega
  have hP1 : 2 ^ (spec.mantissaBits - 1) = 2 ^ spec.mantissaBitsWithoutImplicit := by
    congr 1; omega
  have hlt' := hlt
  rw [hP2] at hlt
  rw [hP1] at hc
  have hbe : ¬ 2 ^ spec.exponentBits ≤ (e + spec.exponentBias + spec.mantissaBitsWithoutImplicit).toNat + 1 := by
    omega
  unfold UnpackedFloat.pack
  simp only [hbe, ite_false]
  have hnm : (e + spec.exponentBias + spec.mantissaBitsWithoutImplicit).toNat < 2 ^ spec.exponentBits - 1 := by
    omega
  have hE : (BitVec.ofNat spec.exponentBits (e + spec.exponentBias + spec.mantissaBitsWithoutImplicit).toNat).toNat
      = (e + spec.exponentBias + spec.mantissaBitsWithoutImplicit).toNat := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hM : (BitVec.ofNat spec.mantissaBitsWithoutImplicit m).toNat = m % 2 ^ spec.mantissaBitsWithoutImplicit :=
    BitVec.toNat_ofNat _ _
  have hn1 : ∀ x : BitVec spec.exponentBits, x.toNat < 2 ^ spec.exponentBits - 1 → x ≠ -1#spec.exponentBits := by
    intro x hx h
    have := congrArg BitVec.toNat h
    rw [negOne_toNat] at this
    omega
  split
  · rename_i hn
    have hl : m.log2 = spec.mantissaBitsWithoutImplicit := by omega
    obtain ⟨hl1, hl2⟩ := (Nat.log2_eq_iff (by omega)).mp hl
    have hmod : m % 2 ^ spec.mantissaBitsWithoutImplicit = m - 2 ^ spec.mantissaBitsWithoutImplicit := by
      rw [Nat.mod_eq_sub_mod hl1]
      exact Nat.mod_eq_of_lt (by rw [Nat.pow_succ] at hl2; omega)
    have hmant1 : (1#1 ++ BitVec.ofNat spec.mantissaBitsWithoutImplicit m).toNat = m := by
      rw [BitVec.toNat_append, hM]
      simp
      have := Nat.two_pow_add_eq_or_of_lt (i := spec.mantissaBitsWithoutImplicit)
        (Nat.mod_lt m (Nat.two_pow_pos _)) 1
      simp only [Nat.mul_one] at this
      rw [Nat.shiftLeft_eq, Nat.one_mul, ← this, hmod]
      omega
    unfold UnpackedFloat.unpack
    simp only [unpackMantissa_packComponents, unpackExponent_packComponents, unpackSign_packComponents,
      ofBitVec_toBitVec]
    have h0 : BitVec.ofNat spec.exponentBits (e + spec.exponentBias + spec.mantissaBitsWithoutImplicit).toNat ≠ 0#spec.exponentBits := by
      intro h
      have := congrArg BitVec.toNat h
      rw [hE, BitVec.toNat_zero] at this
      omega
    simp only [hn1 _ (by rw [hE]; exact hnm), h0, ite_false]
    simp only [UnpackedFloat.finite.injEq, true_and]
    rw [hmant1, hE]
    omega
  · rename_i hn
    have hl : m.log2 < spec.mantissaBitsWithoutImplicit := by
      have := (Nat.log2_lt (by omega : m ≠ 0)).mpr hlt'
      omega
    have hsm : m < 2 ^ spec.mantissaBitsWithoutImplicit := (Nat.log2_lt (by omega : m ≠ 0)).mp hl
    have hmod : m % 2 ^ spec.mantissaBitsWithoutImplicit = m := Nat.mod_eq_of_lt hsm
    have hz : (0#spec.exponentBits) ≠ -1#spec.exponentBits := by
      intro h
      have := congrArg BitVec.toNat h
      rw [negOne_toNat, BitVec.toNat_zero] at this
      omega
    have hM0 : BitVec.ofNat spec.mantissaBitsWithoutImplicit m ≠ 0#spec.mantissaBitsWithoutImplicit := by
      intro h
      have := congrArg BitVec.toNat h
      rw [hM, hmod, BitVec.toNat_zero] at this
      omega
    unfold UnpackedFloat.unpack
    simp only [unpackMantissa_packComponents, unpackExponent_packComponents, unpackSign_packComponents,
      ofBitVec_toBitVec]
    simp only [hz, hM0, ite_false, ite_true, dite_false]
    simp only [UnpackedFloat.finite.injEq, true_and]
    rw [hM, hmod, BitVec.toNat_zero]
    omega

theorem unpack_pack_zero (spec : Format) (s : Sign) :
    UnpackedFloat.unpack spec (UnpackedFloat.pack spec (.zero s)) = .zero s := by
  unfold UnpackedFloat.pack packedZero UnpackedFloat.unpack
  simp only [unpackMantissa_packComponents, unpackExponent_packComponents, unpackSign_packComponents,
    ofBitVec_toBitVec]
  simp
  have := spec.he
  omega

theorem emin_le (spec : Format) : spec.minExponent ≤ 1 - (spec.mantissaBits : Int) := by
  have hB2 : 2 ≤ 2 ^ (spec.exponentBits - 1) := by
    have := spec.he
    calc 2 = 2 ^ 1 := rfl
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have hminE : spec.minExponent = 3 - ((2 ^ (spec.exponentBits - 1) : Nat) : Int) - spec.mantissaBits := by
    show _ = _
    push_cast
    rfl
  omega

/-- `UnpackedFloat.ofNat` of a positive `n` below `2 ^ prec`: its mantissa is `n` shifted up to the
full precision, and its exponent undoes the shift. -/
theorem ofNat_eq (spec : Format) {n : Nat} (hn : 0 < n) (hlt : n < 2 ^ spec.mantissaBits) :
    ∃ (k : Nat) (hm : 0 < n * 2 ^ k), UnpackedFloat.ofNat spec n = .finite .positive (n * 2 ^ k) (-k) hm ∧
      spec.minExponent ≤ -(k : Int) ∧ n * 2 ^ k < 2 ^ spec.mantissaBits ∧
      2 ^ (spec.mantissaBits - 1) ≤ n * 2 ^ k := by
  have hn0 : n ≠ 0 := by omega
  have hp : 1 ≤ spec.mantissaBits := by unfold Format.mantissaBits; omega
  have hl := (Nat.log2_lt hn0).mpr hlt
  have hemin := emin_le spec
  refine ⟨spec.mantissaBits - (n.log2 + 1), Nat.mul_pos hn (Nat.two_pow_pos _), ?_⟩
  have hlog : (n * 2 ^ (spec.mantissaBits - (n.log2 + 1))).log2 = spec.mantissaBits - 1 := by
    rw [log2_mul_two_pow _ hn0]; omega
  have hb := (Nat.log2_eq_iff (Nat.mul_ne_zero hn0 (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)))).mp hlog
  have hb1 : 2 ^ (spec.mantissaBits - 1) ≤ n * 2 ^ (spec.mantissaBits - (n.log2 + 1)) := hb.1
  have hb2 : n * 2 ^ (spec.mantissaBits - (n.log2 + 1)) < 2 ^ spec.mantissaBits := by
    have := hb.2
    rwa [show spec.mantissaBits - 1 + 1 = spec.mantissaBits by omega] at this
  refine ⟨?_, by omega, hb2, hb1⟩
  have ht : spec.targetExponent (totalExponent n 0) = -((spec.mantissaBits - (n.log2 + 1) : Nat) : Int) := by
    unfold Format.targetExponent totalExponent
    omega
  have hs : ((0 : Int) - -((spec.mantissaBits - (n.log2 + 1) : Nat) : Int)).toNat = spec.mantissaBits - (n.log2 + 1) := by
    omega
  unfold UnpackedFloat.ofNat UnpackedFloat.ofInt normalize
  simp only [Int.compare_eq_gt.mpr (show (0 : Int) < n by omega)]
  unfold round decreaseExponent
  simp only [Int.toNat_natCast, ht, hs]
  have := roundWithAccuracy_exact spec .positive (Nat.mul_pos hn (Nat.two_pow_pos (spec.mantissaBits - (n.log2 + 1))))
    (e := -((spec.mantissaBits - (n.log2 + 1) : Nat) : Int)) ⟨by omega, hb2, Or.inr hb1⟩ 0
  simp only [Nat.pow_zero, Nat.mul_one, Int.sub_zero, Int.natCast_zero] at this
  rw [Nat.shiftLeft_eq, Int.zero_sub]
  exact this

theorem scaleTwoPow_shift (n k : Nat) : scaleTwoPow (n * 2 ^ k) (-(k : Int)) = n := by
  have h := scaleTwoPow_add_nat (-(k : Int)) k
  have h0 : scaleTwoPow 1 0 = 1 := by simp [scaleTwoPow]
  rw [show -(k : Int) + (k : Int) = 0 by omega] at h
  rw [scaleTwoPow_eq_mul]
  rw [h0] at h
  push_cast
  grind

theorem ofNat_value (spec : Format) {n : Nat} (hlt : n < 2 ^ spec.mantissaBits) :
    unpackedValue (UnpackedFloat.ofNat spec n) = some (n : Rat) := by
  by_cases h0 : n = 0
  · subst h0
    simp [UnpackedFloat.ofNat, UnpackedFloat.ofInt, normalize, unpackedValue]
  · obtain ⟨k, hm, he, -⟩ := ofNat_eq spec (Nat.pos_of_ne_zero h0) hlt
    rw [he]
    simp [unpackedValue, scaleTwoPow_shift]

theorem mul_one_ofNat (spec : Format) {n : Nat} (hlt : n < 2 ^ spec.mantissaBits) :
    UnpackedFloat.mul spec (UnpackedFloat.ofNat spec n)
      (.finite .positive (2 ^ (spec.mantissaBits - 1)) (-((spec.mantissaBits - 1 : Nat) : Int))
        (Nat.two_pow_pos _)) = UnpackedFloat.ofNat spec n := by
  by_cases h0 : n = 0
  · subst h0
    simp [UnpackedFloat.ofNat, UnpackedFloat.ofInt, normalize, UnpackedFloat.mul]
    rfl
  · obtain ⟨k, hm, he, hmin, hlt', hge⟩ := ofNat_eq spec (Nat.pos_of_ne_zero h0) hlt
    rw [he]
    have := roundWithAccuracy_exact spec .positive hm (e := -(k : Int)) ⟨hmin, hlt', Or.inr hge⟩
      (spec.mantissaBits - 1)
    rw [show -(k : Int) - ((spec.mantissaBits - 1 : Nat) : Int) = -(k : Int) + -((spec.mantissaBits - 1 : Nat) : Int)
      by omega] at this
    exact this

theorem unpack_pack_ofNat (spec : Format) {n : Nat} (hlt : n < 2 ^ spec.mantissaBits)
    (hb : spec.exponentBias + spec.mantissaBitsWithoutImplicit + 1 < 2 ^ spec.exponentBits) :
    UnpackedFloat.unpack spec (UnpackedFloat.pack spec (UnpackedFloat.ofNat spec n)) =
      UnpackedFloat.ofNat spec n := by
  by_cases h0 : n = 0
  · subst h0
    have : UnpackedFloat.ofNat spec 0 = .zero .positive := by
      simp [UnpackedFloat.ofNat, UnpackedFloat.ofInt, normalize]
    rw [this]
    exact unpack_pack_zero spec _
  · obtain ⟨k, hm, he, hmin, hlt', hge⟩ := ofNat_eq spec (Nat.pos_of_ne_zero h0) hlt
    rw [he]
    exact unpack_pack_finite spec .positive hm ⟨hmin, hlt', Or.inr hge⟩ (by omega)

theorem ofScientific_eq_ofNat (spec : Format) {n : Nat} (hge : 2 ^ (spec.mantissaBits - 1) ≤ n)
    (hlt : n < 2 ^ spec.mantissaBits) :
    UnpackedFloat.ofScientific spec n 0 = UnpackedFloat.ofNat spec n := by
  have hn : 0 < n := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hge
  have hp : 1 ≤ spec.mantissaBits := by unfold Format.mantissaBits; omega
  have hn0 : n ≠ 0 := by omega
  have hl : n.log2 = spec.mantissaBits - 1 := by
    rw [Nat.log2_eq_iff hn0]
    exact ⟨hge, by rwa [show spec.mantissaBits - 1 + 1 = spec.mantissaBits by omega]⟩
  obtain ⟨k, hm, he, hmin, hlt', -⟩ := ofNat_eq spec hn hlt
  have hk : k = 0 := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · exact hk
    exfalso
    have h2 : 2 ≤ 2 ^ k := by
      have := Nat.one_lt_two_pow (n := k) (by omega)
      omega
    have h3 : 2 * n ≤ n * 2 ^ k := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ h2
    have h4 : 2 ^ spec.mantissaBits = 2 * 2 ^ (spec.mantissaBits - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    omega
  subst hk
  have hmin' := emin_le spec
  have hfin : UnpackedFloat.ofNat spec n = .finite .positive n 0 hn := by
    simp only [Nat.pow_zero, Nat.mul_one, Int.natCast_zero, Int.neg_zero] at he
    exact he
  rw [hfin]
  have hB : (0 : Int) < 2 ^ spec.exponentBits := by exact_mod_cast Nat.two_pow_pos _
  unfold UnpackedFloat.ofScientific
  simp only [Nat.pos_iff_ne_zero.mp hn, dite_false]
  have h1 : ¬ ((0 : Int) > 2 ^ spec.exponentBits) := by omega
  have h2 : ¬ ((0 : Int) < -((2 ^ spec.exponentBits : Int) + n.log2)) := by omega
  simp only [h1, h2, ite_false, show (0 : Int) ≤ 0 by decide, ite_true]
  unfold UnpackedFloat.mul
  have := roundWithAccuracy_exact spec .positive hn (e := 0) ⟨by omega, hlt, Or.inr hge⟩ spec.mantissaBits
  simp only [Int.toNat_zero, Nat.pow_zero, Nat.mul_one, Int.zero_sub] at this ⊢
  rw [Nat.shiftLeft_eq, Int.add_zero]
  exact this

end Inkproof.Float.Internal.Exact
