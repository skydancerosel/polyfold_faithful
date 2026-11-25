import Polyfold
/-! Blind formalization of V17_33 (the text's §17.1, Theorem 17.1.28, p. 766 of the Springer 2021
book; 2017: Theorem 17.3).

Text: the full subcategory `C_1` is a GCT and carries the polyfold structure `(F¹, M_{F¹})` with
`F¹(α) = {Ψ¹}` and `M_{F¹}(Ψ¹, Ψ'¹) = (M(Ψ, Ψ'))¹` ("obvious").

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` with a polyfold structure
  `S : C.PolyfoldConstruction`, and `hc : S.HasCoveringUniformizers` (footprints of `F` cover
  `|C|`; the text's topology on `|C_1|` is transported from a covering set, so it presupposes
  one).
- "`C_1` is a GCT": the full subcategory `C_1` (objects of regularity `1`, p. 765/766; the
  project's `S.regSub 1`) is a groupoidal category automatically (full subcategory, finite
  morphism sets); the content is its natural metrizable topology.  I take the GCT to be the
  project's `S.levelOneGCT hc` (its groupoid is `S.regSub 1` by definition) and assert of it:
  `|C_1|` is metrizable (part of being a GCT, built into the structure) and its topology is the
  natural one, i.e. `|Γ_Ψ¹| : |X_Ψ¹| → |C_1|` (the project's `S.modelFunctorOne c.Ψ`, `Γ_Ψ` on
  level-`1` points) is a homeomorphism for EVERY covering set `Ψ`.
- `Ψ¹` = the project's `S.levelOneUnif hc Ψ` (the lift `G ⋉ O¹ → C_1` of `Ψ`, p. 766; the text's
  construction, from the vocabulary).  "`F¹(α) = {Ψ¹}`" read as
  `F¹(α) = {Ψ¹ | Ψ ∈ F(α)}` for every object `α` of `C_1`.
- "`M_{F¹}(Ψ¹, Ψ'¹) = (M(Ψ, Ψ'))¹` with the natural identification": the bijection
  `M(Ψ¹, Ψ'¹) ≃ M(Ψ, Ψ')¹`, `(q, φ, q') ↦ (q, φ, q')` (the project's `levelOneTransEquiv`) is a
  homeomorphism and an sc-diffeomorphism (sc-smooth both ways) between the M-polyfold
  `M_{F¹}(Ψ¹, Ψ'¹)` of the structure and the raised M-polyfold `M(Ψ, Ψ')¹` (Part I's `X¹`,
  the project's `MPolyfold.shift` of `S.transPolyfold Ψ Ψ'`).
- B asserts the existence of such a polyfold structure `S¹` on the GCT; the project's
  `levelOneConstruction` is not used.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_33
open Polyfold

/-- Theorem 17.1.28: `C_1` is a GCT with the natural topology and carries a polyfold structure
`(F¹, M_{F¹})` with `F¹(α) = {Ψ¹ | Ψ ∈ F(α)}` and `M_{F¹}(Ψ¹, Ψ'¹) = M(Ψ, Ψ')¹`. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (hc : S.HasCoveringUniformizers),
    (∀ c : S.CoveringFamily,
      @IsHomeomorph _ _ _ (S.levelOneGCT hc).top (S.modelFunctorOne c.Ψ).orbitMap) ∧
    ∃ S₁ : (S.levelOneGCT hc).PolyfoldConstruction,
      (∀ α : (S.levelOneGCT hc).Obj,
        S₁.F α = {L | ∃ Ψ : S.Unif, Ψ.1 ∈ S.F α.1 ∧
          L = S.levelOneUnif hc Ψ}) ∧
      ∀ (Ψ Ψ' : S.Unif) (h : ∃ α, S.levelOneUnif hc Ψ ∈ S₁.F α)
        (h' : ∃ α, S.levelOneUnif hc Ψ' ∈ S₁.F α),
        letI := S₁.topM ⟨_, h⟩ ⟨_, h'⟩
        letI := S₁.t2M ⟨_, h⟩ ⟨_, h'⟩
        letI := S₁.paraM ⟨_, h⟩ ⟨_, h'⟩
        IsHomeomorph (S.levelOneTransEquiv hc Ψ Ψ') ∧
        (S₁.M ⟨_, h⟩ ⟨_, h'⟩).IsScSmoothMap (S.transPolyfold Ψ Ψ').shift
          (S.levelOneTransEquiv hc Ψ Ψ') ∧
        (S.transPolyfold Ψ Ψ').shift.IsScSmoothMap (S₁.M ⟨_, h⟩ ⟨_, h'⟩)
          (S.levelOneTransEquiv hc Ψ Ψ').symm

end RoundTrip.V17_33
