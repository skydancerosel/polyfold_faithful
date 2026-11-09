import Polyfold
/-! Blind formalization of V8_21 (the text's Part II, §8.3, after Definition 8.3.1 = 2017
Definition 8.4, p. 375 / 2017 p. 271).

Text: for a strong bundle `(P, μ)` over the ep-groupoid `X`, `μ(ψ, ·) : W_x → W_y` is a linear
isomorphism if `ψ : x → y` is a morphism in `𝐗`; the data of a strong bundle over an ep-groupoid
prescribe how to lift morphisms to linear isomorphisms compatibly with compositions.

Choices:
- Setting as in my `RoundTrip/Blind/V8_20.lean`: `X : EpGroupoid Obj Mor`, `W : Type`,
  `B : StrongBundle X.PObj P`, and the strong bundle `(P, μ)` over `X` is a project
  `E : EpStrongBundle X B` (characterized as the text's Definition 8.3.1 in V8_20), `μ = E.μ`.
- `W_x = P⁻¹(x)` with its given linear structure (the instances); for `ψ : x → y` I take
  `x = s ψ`, `y = t ψ`, so `μ(ψ, ·) : W_{s ψ} → W_{t ψ}`, `w ↦ μ(ψ, w)` (`(ψ, w) ∈ 𝐗 ₛ×_P W`
  since `P w = s ψ`).  "Linear isomorphism" = a bijective linear map, Mathlib's `≃ₗ[ℝ]` (the
  algebraic notion; the text does not say "topological").
- The second sentence ("lift morphisms to linear isomorphisms compatibly with compositions") is
  read as: the family `L ψ = μ(ψ, ·)` of linear isomorphisms sends units to identities and
  composites to composites, `L(1_x) = id`, `L(ψ ∘ γ) = L(ψ) ∘ L(γ)` for `s ψ = t γ`; as the fibres
  `W_{s(ψ∘γ)}` and `W_{s γ}` are different types in Lean, this is stated on the underlying points
  of `W`.  B is the conjunction: one family `L` with all three properties.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_21
open Polyfold

/-- The fibre maps `μ(ψ, ·) : W_{s ψ} → W_{t ψ}` are linear isomorphisms, forming a lift of the
morphisms compatible with units and composition. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → Obj)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle X.PObj P)
    (E : EpStrongBundle X B),
    ∃ L : ∀ ψ : Mor, (P ⁻¹' {X.src ψ}) ≃ₗ[ℝ] (P ⁻¹' {X.tgt ψ}),
      -- `L ψ = μ(ψ, ·)`
      (∀ (ψ : Mor) (w : P ⁻¹' {X.src ψ}), (L ψ w : W) = E.μ ⟨(ψ, w.1), w.2⟩) ∧
      -- `L(1_x) = id`
      (∀ (x : Obj) (w : P ⁻¹' {X.src (X.unit x)}), (L (X.unit x) w : W) = w) ∧
      -- `L(ψ ∘ γ) = L(ψ) ∘ L(γ)` for composable `ψ`, `γ`
      (∀ (ψ γ : Mor), X.src ψ = X.tgt γ →
        ∀ (w : P ⁻¹' {X.src (X.comp ψ γ)}) (w' : P ⁻¹' {X.src γ}) (v : P ⁻¹' {X.src ψ}),
          (w : W) = w' → (v : W) = L γ w' → (L (X.comp ψ γ) w : W) = L ψ v)

end RoundTrip.V8_21
