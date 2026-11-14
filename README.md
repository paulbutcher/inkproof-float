# Inkproof.Float

The floating-point model of Inkproof: the exact value of a `Float` (`Float.toRat`), the rounding axiom `float_rounding_model` and the relative error it gives (`Float.Approximates`), the order and literals of `Float` proved from Lean's model, and `OrdFloat`, floats that are linearly ordered by `≤` (`float_le_linear`, proved from Lean's model of `Float`). It depends on nothing and knows nothing of series, scales or charts. See `DESIGN.md`.

Part of Inkproof. Released under the Apache 2.0 license; see `LICENSE`.
