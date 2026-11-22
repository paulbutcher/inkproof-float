# Changelog

## v0.7.1

- `scaleTwoPow` is defined with Lean core's `Rat` integer power and its lemmas derive from core's `Rat.zpow` lemmas; no public declaration is removed or its statement changed.
- Proofs use core's `Rat.abs_pos_iff`, `Rat.abs_sub_comm` and `Rat.abs_zero` instead of unfolding `Rat.abs`.

## v0.7.0

- `Rat.toFloat` converts a rational to a float, with a theorem that it is within half an ulp when the numerator and denominator are below 2^53.
- `Float.toRat_neg` shows negation of a float is exact.

## v0.6.1

- The README lists `Float.clamp`.

## v0.6.0

- `Float.near` compares two floats within a relative tolerance, with theorems that a NaN is never near anything.

## v0.5.2

- The README lists what the library does.

## v0.5.1

- The tests run under Lasm 0.8.0.

## v0.5.0

- Public `clamp` and `Rat` lemmas on squares, magnitude and clamping.

## v0.4.0

- Public lemmas over any `FloatFormat` for the absolute form of `Approx` and for `2 ^ -prec` (its bound and its product with `2 ^ k`).

## v0.3.0

- The order and integer literals of `Float` and `Float32` are proved from Lean's model, so `float_rounding_model` and `float32_rounding_model` now assume only the rounding error bounds.

## v0.2.0

- The rounding model is parameterised by a float format, with binary32 alongside binary64 and a fused multiply-add bound.
- The relative-error lemmas for composed steps, products, rounding and quotients are public.

## v0.1.0

The float model, its formats, ordered floats and error bounds, moved here from inkproof-core.
