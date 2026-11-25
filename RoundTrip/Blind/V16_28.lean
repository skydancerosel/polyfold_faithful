import Polyfold
/-! Blind formalization of V16_28 (the text's Part II, §16.4, Theorem 16.4.6, p. 732 of the
Springer 2021 book; 2017: Theorem 16.5).

Text: for `τ = [ω, (X, α)]` of degree `n - 1` and `θ̂` oriented, tame, compact, of dimension `n`:
`∫_θ̂ dτ = ∫_∂θ̂ τ` and `∮_θ̂ dτ = ∮_∂θ̂ τ` ("on the ep-groupoid level Stokes' Theorem holds and
consequently it holds in the polyfold context as well").

Choices:
- Setting: `Z : Type` (universe `0`), a polyfold `c`, an oriented branched suborbifold
  `θ̂ : c.OrientedSuborbifold` (Definition 16.4.4), `τ : c.ScForm m` (Definition 16.2.5).
- Degrees: `n = m + 1 ≥ 1` (degree `n - 1` of `τ` presupposes `n ≥ 1`).  The project's boundary
  integrals come in two forms, `OrientedRep.boundaryIntegral` for `m ≥ 1` and
  `OrientedRep.boundaryIntegralDim1` for `n = 1` (the boundary is `0`-dimensional, a weighted
  signed count); B is the conjunction of the two cases.  Same for the effective versions.
- Hypotheses on `θ̂`: compact = `θ̂.toBranched.IsCompact` (Definition 16.4.2 (2)); tame =
  `θ̂.toBranched.IsTame` (Definition 16.4.2 (5)); of dimension `n` =
  `θ̂.toBranched.IsNDimensional n`; and, needed for the integrals to be defined, `θ̂` tame
  oriented of dimension `n` (`θ̂.IsTameOriented n`, oriented tame structures describing the
  orientation, Definition 9.5.6).  I list all four (the last may make the second and third
  redundant).
- `∫_θ̂` and `∮_θ̂`: the project's `OrientedSuborbifold.integral` and `.integralEff`
  (2021 p. 732).  `∫_∂θ̂ τ`, `∮_∂θ̂ τ`: defined in the text through a representative
  `((Θ, T̂), (X, α))` of `θ̂` (the boundary measure of Theorems 9.5.15 / 9.5.16); the project has
  them only on representatives (`OrientedRep.boundaryIntegral[Eff][Dim1]`, which need the
  representative compact and tame oriented).  I state the equations for EVERY representative
  `a` of `θ̂` that is compact and tame oriented of dimension `n`, and add, so that this is not
  vacuous, the presupposition that `θ̂` has such a representative.
- No sc-smooth partitions of unity are assumed (the text's statement has none).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V16_28
open Polyfold

/-- The case `n = m + 1 ≥ 2` (the boundary has dimension `m ≥ 1`). -/
def Bgen : Prop :=
  ∀ (Z : Type) [TopologicalSpace Z] (c : PolyfoldClass Z) (θ : c.OrientedSuborbifold) (m : ℕ)
    (hc : θ.toBranched.IsCompact), θ.toBranched.IsTame → θ.toBranched.IsNDimensional (m + 1) →
    ∀ (ht : θ.IsTameOriented (m + 1)),
      -- `∂θ̂` is defined: a compact tame oriented representative exists
      (∃ a : c.OrientedRep, ⟦a⟧ = θ ∧ a.p.X.X.IsCompactBranched a.A.Θ ∧
        a.IsTameOriented (m + 1)) ∧
      (∀ (hm : 0 < m) (a : c.OrientedRep), ⟦a⟧ = θ →
        ∀ (hca : a.p.X.X.IsCompactBranched a.A.Θ) (hta : a.IsTameOriented (m + 1))
          (τ : c.ScForm m),
          θ.integral (Nat.succ_pos m) hc ht (PolyfoldClass.ScForm.d τ) =
              a.boundaryIntegral hm hca hta τ ∧
          θ.integralEff (Nat.succ_pos m) hc ht (PolyfoldClass.ScForm.d τ) =
              a.boundaryIntegralEff hm hca hta τ)

/-- The case `n = 1` (the boundary is `0`-dimensional). -/
def B1 : Prop :=
  ∀ (Z : Type) [TopologicalSpace Z] (c : PolyfoldClass Z) (θ : c.OrientedSuborbifold)
    (hc : θ.toBranched.IsCompact), θ.toBranched.IsTame → θ.toBranched.IsNDimensional (0 + 1) →
    ∀ (ht : θ.IsTameOriented (0 + 1)),
      (∃ a : c.OrientedRep, ⟦a⟧ = θ ∧ a.p.X.X.IsCompactBranched a.A.Θ ∧
        a.IsTameOriented (0 + 1)) ∧
      (∀ (a : c.OrientedRep), ⟦a⟧ = θ →
        ∀ (hca : a.p.X.X.IsCompactBranched a.A.Θ) (hta : a.IsTameOriented (0 + 1))
          (τ : c.ScForm 0),
          θ.integral (Nat.succ_pos 0) hc ht (PolyfoldClass.ScForm.d τ) =
              a.boundaryIntegralDim1 hca hta τ ∧
          θ.integralEff (Nat.succ_pos 0) hc ht (PolyfoldClass.ScForm.d τ) =
              a.boundaryIntegralEffDim1 hca hta τ)

/-- Theorem 16.4.6 (Stokes): `∫_θ̂ dτ = ∫_∂θ̂ τ` and `∮_θ̂ dτ = ∮_∂θ̂ τ`, for `τ` of degree `n - 1`
and `θ̂` compact, tame, oriented of dimension `n ≥ 1`. -/
def B : Prop := Bgen ∧ B1

end RoundTrip.V16_28
