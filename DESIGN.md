# Inkproof.Float design

## Floats

- `OrdFloat` wraps a `Float` with a proof that it is neither NaN nor `-0.0` (FP-2). `OrdFloat.ofFloat?` rejects NaN and turns `-0.0` into `0.0`, so equal values have one representation.
- `float_le_linear` is a theorem: `Float` is defined over `Float.Model`, an IEEE 754 binary64 model, and `Internal.FloatModel` unpacks its bits into an integer key that orders the non-NaN floats exactly as `≤` does. `OrdFloat`'s order instance rests on it. `Float.toRat_eq_value` shows `Float.toRat` is the value of the model's unpacked float.
- Absolute values of rationals use Lean core's `Rat.abs`, with its `abs_of_nonneg`, `abs_neg` and related lemmas. The library adds only what it lacks: `rat_abs_le_iff`, `rat_abs_add_le` and `rat_abs_mul`, and, for `Float.Approximates`, `rel` (the `r * (1 + δ)` form) and `error_step` (composing a rounding error with an existing bound). They are stated generally so consumers analyses are instances.
- A `FloatFormat` (precision and largest exponent) parameterises `maxFloat`, `minNormalFloat`, `NormalRange` and `Approx`; `binary64` and `binary32` are its instances, and `Float.Approximates` and `Float32.Approximates` are `Approx` of each. `Approx.rel`, `Approx.error_step` and `Approx.ulps` are stated once over any format. The unparameterised `maxFloat`, `minNormalFloat` and `NormalRange` stay as binary64.
- `Inkproof.Float.Exact` proves from Lean's model that `≤` agrees with the exact values and that integer literals below `2 ^ prec` are exact, for both formats. `Inkproof.Float.Axioms` holds the one axiom per format the library adds (FP-3, FP-5); what stays trusted is that Lean's compiled float operations match the model.
- Tests check the model against compiled code, natively and under Lasm: that `ofFloat?` keeps the value and removes `-0.0` (rejecting exactly NaN is proved), that `float_le_linear` holds of the platform's floats, and that the order, the literals and both rounding axioms do.

### Proving the rest of `float_rounding_model`

Assessed against Lean v4.35.0 core, which has no theory of its rounding: `Float.Model` states that it is not a basis for a float library and carries no lemmas beyond what the operations need. Nothing outside core was found to help. opencompl/fp-lean models bit-blasted IEEE floats on a nightly toolchain, is unfinished, and would need a proved equivalence with `Float.Model` before use, so it would add work rather than remove it.

- Done: the order and the literals, in `Internal.Exact`. `UnpackedFloat.round` of an exact value and the canonical order are lemmas the error proof can reuse.
- Still an axiom, the error bound of `+ - * /` and `fma`: it needs one error lemma about `UnpackedFloat.round` for inexact values (shifting by `targetExponent` with round and sticky bits, `roundToNearestEven`, the carry that re-shifts, and the bound on `totalExponent`), after which `add`, `sub` and `mul` are exact integer arithmetic followed by `round`. `div` additionally needs its quotient and remainder to give the right `Accuracy`. About 600 to 1200 lines more, one to three weeks.
- Everything is in modules that compile to nothing, so Lasm is unaffected; the proofs stay out of browser builds like the other theorems (PLAT-3). Adding no dependency keeps every consumer's build as it is.
- Proving it would shrink the trusted base to the compiled-versus-model match alone, which the tests already check. The human decides whether that is worth the weeks.

## Testing

- Tests live in the `test` subproject (CLAUDE.md's Test layout). `lake test` runs `Main.lean` natively, then with Lasm; the library depends on nothing, and the theorems here import no Mathlib.
- `InkproofFloatTest.AxiomCheck`, from inkproof-tools, fails compilation if a declaration depends on an axiom other than Lean's own and those in `Inkproof.Float.Axioms`.
