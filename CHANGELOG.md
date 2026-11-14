# Changelog

## v0.3.0

- The order and integer literals of `Float` and `Float32` are proved from Lean's model, so `float_rounding_model` and `float32_rounding_model` now assume only the rounding error bounds.

## v0.2.0

- The rounding model is parameterised by a float format, with binary32 alongside binary64 and a fused multiply-add bound.
- The relative-error lemmas for composed steps, products, rounding and quotients are public.

## v0.1.0

The float model, its formats, ordered floats and error bounds, moved here from inkproof-core.
