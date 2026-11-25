import Polyfold
/-! Blind formalization of V17_63 (the text's §17.3, Proposition 17.3.6, p. 786 of the Springer
2021 book; 2017: Proposition 17.6).

Text: a subpolyfold `A`, as a GCT, inherits a natural polyfold structure `(F_A, M)`.

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` with a polyfold structure
  `S : C.PolyfoldConstruction`, and a set `A ⊆ obj(C)` which is a subpolyfold in the sense of
  Definition 17.3.1, written out here (`Def1`: `A` saturated, and `Ψ⁻¹(A)` a sub-M-polyfold of
  `O` for every `α ∈ A` and every `Ψ ∈ F(α)`); the project's `IsSubpolyfold` is not used.  The
  saturation proof `hA` (needed to form `Ψ_A`) is a separate, redundant hypothesis of B.
- "`A` as a GCT" = the project's `C.sub A` (the full subcategory on `A`, with `|A|` carrying the
  topology induced from `|C|`, pp. 785–786; the text's construction from the vocabulary).
- `Ψ_A : G ⋉ A_Ψ → A` = the project's `LocalUniformizer.restrict hA p` (p. 785), defined for a
  uniformizer `Ψ` whose `A_Ψ = Ψ⁻¹(A)` is a sub-M-polyfold (`p`).
- "natural polyfold structure `(F_A, M)`" (p. 786), my reading: there is a polyfold structure
  `S_A` on `C.sub A` with
  (1) `F_A(α) = {Ψ_A | Ψ ∈ F(α)}` for every object `α` of `A` (all such `Ψ` have `A_Ψ` a
      sub-M-polyfold, by `Def1`; I quantify over the witness `p`);
  (2) `M(Ψ_A, Ψ'_A)` is the set `s⁻¹(A_Ψ) ⊆ M(Ψ, Ψ')` with its structure as a sub-M-polyfold of
      `M(Ψ, Ψ')` (Lemma 17.3.5): the identification `(o, φ, o') ↦ (o, φ, o')` (the project's
      `restrictTransEquiv`, onto the project's `restrictTransSet Ψ Ψ' = {(q, φ, q') | Ψ(q) ∈ A}`)
      is a homeomorphism and an sc-diffeomorphism (sc-smooth both ways) between `S_A`'s
      M-polyfold `M(Ψ_A, Ψ'_A)` and the sub-M-polyfold `s⁻¹(A_Ψ)` (`MPolyfold.subPolyfold`; the
      sub-M-polyfold property itself, Lemma 17.3.5, is existentially quantified).
- The project's `subConstruction`, `subF`, `RTr`, `rtrPolyfold` are not used.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_63
open Polyfold

/-- Definition 17.3.1: `A` is a subpolyfold. -/
def Def1 {C : GCT.{0}} (S : C.PolyfoldConstruction) (A : Set C.Obj) : Prop :=
  C.toGroupoidStr.IsSaturated A ∧
    ∀ α ∈ A, ∀ Ψ ∈ S.F α, Ψ.P.IsSubMPolyfold (Ψ.obj ⁻¹' A)

/-- Proposition 17.3.6: the subpolyfold `A`, as a GCT, carries the polyfold structure
`(F_A, M)` with `F_A(α) = {Ψ_A | Ψ ∈ F(α)}` and `M(Ψ_A, Ψ'_A) = s⁻¹(A_Ψ) ⊆ M(Ψ, Ψ')` as a
sub-M-polyfold. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (A : Set C.Obj) (hA : C.toGroupoidStr.IsSaturated A),
    Def1 S A →
    ∃ SA : (C.sub A).PolyfoldConstruction,
      (∀ α : (C.sub A).Obj,
        SA.F α = {L | ∃ Ψ : S.Unif, Ψ.1 ∈ S.F α.1 ∧
          ∃ p : Ψ.1.P.IsSubMPolyfold (Ψ.1.obj ⁻¹' A), L = GCT.LocalUniformizer.restrict hA p}) ∧
      ∀ (Ψ Ψ' : S.Unif) (p : Ψ.1.P.IsSubMPolyfold (Ψ.1.obj ⁻¹' A))
        (p' : Ψ'.1.P.IsSubMPolyfold (Ψ'.1.obj ⁻¹' A))
        (h : ∃ α, GCT.LocalUniformizer.restrict hA p ∈ SA.F α)
        (h' : ∃ α, GCT.LocalUniformizer.restrict hA p' ∈ SA.F α),
        letI := SA.topM ⟨_, h⟩ ⟨_, h'⟩
        letI := SA.t2M ⟨_, h⟩ ⟨_, h'⟩
        letI := SA.paraM ⟨_, h⟩ ⟨_, h'⟩
        ∃ hsub : (S.transPolyfold Ψ Ψ').IsSubMPolyfold (S.restrictTransSet (A := A) Ψ Ψ'),
          IsHomeomorph (S.restrictTransEquiv hA Ψ Ψ' p p') ∧
          (SA.M ⟨_, h⟩ ⟨_, h'⟩).IsScSmoothMap (MPolyfold.subPolyfold hsub)
            (S.restrictTransEquiv hA Ψ Ψ' p p') ∧
          (MPolyfold.subPolyfold hsub).IsScSmoothMap (SA.M ⟨_, h⟩ ⟨_, h'⟩)
            (S.restrictTransEquiv hA Ψ Ψ' p p').symm

end RoundTrip.V17_63
