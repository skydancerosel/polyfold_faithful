import Polyfold
/-! Blind formalization of V5_58 (the text's §5.4.2, Proposition 5.38, p. 197).

Text ("an immediate consequence of Theorem 5.37"): if the sc-Banach space admits smooth partitions
of unity, a local model `(O, C, E)` has the sc-smooth approximation property.

Choices:
- For every local model `M = (O, C, E)` (the project's `LocalModel`; levels of `E` in `Type`).
- "the sc-Banach space admits smooth partitions of unity": read as the CLASSICAL notion for the
  Banach space underlying `E`, i.e. `E = E₀` (the text writes `E` for `E₀`): every open cover of
  `E₀` has a subordinate partition of unity of `C^∞` (Fréchet-smooth) functions — the project's
  `AdmitsContDiffPartitionsOfUnity (E.lvl 0) ⊤` (checked with `#print`: for every index type and
  open cover of `E₀`, a Mathlib `PartitionOfUnity` subordinate to it, `tsupport ρ_i ⊆ U_i`, all of
  whose functions are `ContDiff ℝ ⊤`, `⊤ : ℕ∞` being `C^∞`).  "Smooth", not "sc-smooth"; this is
  also the form in which Corollary 5.44 feeds Theorem 5.43 (classical partitions of unity of `E₀`)
  into it.  Alternative reading, NOT used: `E`, as an M-polyfold, admits sc-smooth partitions of
  unity (a weaker hypothesis, since `C^∞` functions on `E₀` are sc-smooth).
- "has the sc-smooth approximation property": the project's `HasApproxProperty` (Definition 5.36,
  checked with `#print`; see `RoundTrip/Blind/V5_54.lean`).
- Nothing looks false to me (the "immediate" derivation from Theorem 5.37 is not formalized).
-/
namespace RoundTrip.V5_58
open Polyfold

/-- Proposition 5.38: if `E₀` admits `C^∞` partitions of unity, `(O, C, E)` has the sc-smooth
approximation property. -/
def B : Prop :=
  ∀ M : LocalModel, AdmitsContDiffPartitionsOfUnity (M.E.lvl 0) ⊤ → M.HasApproxProperty

end RoundTrip.V5_58
