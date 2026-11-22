# Inkproof.Float

The floating-point model of Inkproof: the exact value of a `Float`, the rounding axioms and the error bounds they give, and floats that are linearly ordered. It depends on nothing and knows nothing of series, scales or charts. See `DESIGN.md`.

Require it at the current release:

```lean
require «inkproof-float» from git "https://github.com/paulbutcher/inkproof-float" @ "v0.5.1"
```

then `import Inkproof.Float`.

## What it does

- Exact value of a `Float` or `Float32` as a rational, `none` for NaN and infinities: `Float.toRat`, `Float32.toRat`, with `toRat_eq_value`, `toRat_ofNat` (small literals are exact) and `unpackedValue`.
- Compare floats by their exact values: `Float.toRat_mono`, `Float.le_of_toRat_le` (and the `Float32` versions).
- Which floats are finite or not NaN: `Float.IsFinite`, `Float.IsOrdered`, `Float32.IsFinite`.
- Rounding model for `+`, `-`, `*`, `/` and fused multiply-add: the axioms `float_rounding_model` and `float32_rounding_model`, and `Float.approximates_add`, `_sub`, `_mul`, `_div`, `_fma` (and the `Float32` versions) giving the result's error as an `Approximates` relation.
- Describe a float format and its limits: `FloatFormat` (`binary64`, `binary32`, `prec`, `maxExp`), `maxFloat`, `minNormalFloat`, `NormalRange`, and the rounding unit `2 ^ -prec` with `rounding_unit_pos`, `rounding_unit_le_eighth`, `pow_mul_rounding_unit`.
- State and use the error of a computed float against a real value: `Float.Approximates`, `Float32.Approximates`, `FloatFormat.Approx`, with the relative, absolute and ulp forms `Approximates.rel`, `Approx.abs_le`, `Approx.ulps`, and `Approximates.error_step` for chaining one more operation.
- Propagate relative error through arithmetic over `Rat`: `rel_error_step`, `rel_error_mul`, `rel_error_div`, `rel_error_round`, and `rat_abs_add_le`, `rat_abs_mul`, `rat_abs_le_iff`.
- Total order on floats: `OrdFloat` (floats that are not NaN), built with `OrdFloat.ofFloat?`, with `≤` a decidable linear order (`instIsLinearOrder`, `float_le_linear`), so floats can be sorted and compared.
- Exact scaling by powers of two over `Rat`: `scaleTwoPow` and its `_of_nonneg`, `_of_neg`, `_one_nat`, `_one_pos`, `_zero` lemmas.
- Compare two floats within a relative tolerance: `Float.near a b tol` (default `1e-6`; false if either is NaN or infinite), with `Float.near_iff`, `Float.near_isFinite`, `Float.near_nan_left`, `Float.near_nan_right`.
- Clamp a value into a range: `Float.clamp lo hi x` (any type with a decidable `<`), with `rat_clamp_eq_max_min`, `rat_clamp_mem` (the result lies in `[lo, hi]`) and `rat_clamp_sq_le` (it is the nearest point of the range).
- Convert a rational to the nearest `Float`: `Rat.toFloat`, with `Rat.approximates_toFloat` (within half an ulp when numerator and denominator are below 2^53), and `Float.toRat_neg` (negation is exact).
- Run a float function on a rational, or use a float function as a rational function; NaN and infinity become 0: `Float.onRat`, with `Float.onRat_eq` and `Float.onRat_of_toRat_eq_none`.
- The bit pattern of negative zero: `negZeroBits`.

Part of Inkproof. Released under the Apache 2.0 license; see `LICENSE`.
