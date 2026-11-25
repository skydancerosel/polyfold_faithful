import Polyfold
/-! Blind formalization of V17_51 (the text's §17.2, Proposition 17.2.14, pp. 776–781 of the
Springer 2021 book; 2017: Proposition 17.3).

Text: the natural topology is metrizable, `s` and `t` are local homeomorphisms, `ι` a
homeomorphism, `u` and `m` continuous.

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` with a polyfold structure
  `S : C.PolyfoldConstruction`, and `hU : S.HasUniformizers` (needed because the project's tangent
  uniformizers on objects `TΨ = S.tangentUnifObj hU Ψ`, hence `M(TΨ₁, TΨ₂)`, are built with it;
  the text presupposes the reference uniformizers `Ψ_α ∈ F(α)`, pp. 769–771).
- `M(TΨ₁, TΨ₂)` = the project's `S.TTr hU Ψ₁ Ψ₂` (`#print`ed: the transition set in `TC` of
  `TΨ₁, TΨ₂ : TOᵢ → TC`), for all uniformizers `Ψ₁, Ψ₂, Ψ₃` of `F`.
- "The natural topology" (Definition 17.2.13): defined here myself (`natTop`) as the final
  topology of all the maps (17.42), `S.tangentTrChart hU T : TU(o) → M(TΨ₁, TΨ₂)` for every
  `o ∈ M(Ψ₁, Ψ₂)` and every admissible triple `T` at `o` (`TU(o) ⊆ TO₁` with the subspace
  topology of the tangent bundle).  The project's `tangentTrTopology` is not used.
- The structure maps are those of the transition sets (Definition 17.1.5, p. 746), i.e. the
  project's generic `GroupoidStr.TransitionSet.src/tgt/inv/unit/comp` in the groupoid `TC`:
  `s : M(TΨ₁, TΨ₂) → TO₁`, `t : → TO₂`, `ι : M(TΨ₁, TΨ₂) → M(TΨ₂, TΨ₁)`,
  `u : TO → M(TΨ, TΨ)`, `m : M(TΨ₂, TΨ₃) ₛ×ₜ M(TΨ₁, TΨ₂) → M(TΨ₁, TΨ₃)`.  `TOᵢ` carry the
  tangent-bundle topology of Part I.
- The fibred product of `m` is my own subtype `{(a, b) | s(a) = t(b)}` of the product, with the
  subspace topology of the product of natural topologies; `m(a, b) = a ∘ b` (`TransitionSet.comp`;
  the composability proof is derived from `s(a) = t(b)`).
- "local homeomorphism" = Mathlib's `IsLocalHomeomorph`; "homeomorphism" = `IsHomeomorph`.
- B is the conjunction of the five claims.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_51
open Polyfold

noncomputable section

/-- The natural topology (Definition 17.2.13): the final topology of the maps (17.42). -/
@[instance_reducible] def natTop {C : GCT.{0}} (S : C.PolyfoldConstruction) (hU : S.HasUniformizers)
    (Ψ₁ Ψ₂ : S.Unif) : TopologicalSpace (S.TTr hU Ψ₁ Ψ₂) :=
  ⨆ i : (o : S.Tr Ψ₁ Ψ₂) × S.AdmissibleTriple o,
    TopologicalSpace.coinduced (S.tangentTrChart hU i.2) inferInstance

/-- `M(TΨ₁, TΨ₂)` as a bare type carrying the natural topology. -/
def NT {C : GCT.{0}} (S : C.PolyfoldConstruction) (hU : S.HasUniformizers)
    (Ψ₁ Ψ₂ : S.Unif) : Type 1 := S.TTr hU Ψ₁ Ψ₂

instance {C : GCT.{0}} (S : C.PolyfoldConstruction) (hU : S.HasUniformizers)
    (Ψ₁ Ψ₂ : S.Unif) : TopologicalSpace (NT S hU Ψ₁ Ψ₂) := natTop S hU Ψ₁ Ψ₂

/-- `s(q, φ, q') = q`. -/
def src {C : GCT.{0}} (S : C.PolyfoldConstruction) (hU : S.HasUniformizers)
    (Ψ₁ Ψ₂ : S.Unif) (a : NT S hU Ψ₁ Ψ₂) : Ψ₁.1.P.TangentSpace :=
  GroupoidStr.TransitionSet.src (a : S.TTr hU Ψ₁ Ψ₂)

/-- `t(q, φ, q') = q'`. -/
def tgt {C : GCT.{0}} (S : C.PolyfoldConstruction) (hU : S.HasUniformizers)
    (Ψ₁ Ψ₂ : S.Unif) (a : NT S hU Ψ₁ Ψ₂) : Ψ₂.1.P.TangentSpace :=
  GroupoidStr.TransitionSet.tgt (a : S.TTr hU Ψ₁ Ψ₂)

/-- `ι(q, φ, q') = (q', φ⁻¹, q)`. -/
def inv {C : GCT.{0}} (S : C.PolyfoldConstruction) (hU : S.HasUniformizers)
    (Ψ₁ Ψ₂ : S.Unif) (a : NT S hU Ψ₁ Ψ₂) : NT S hU Ψ₂ Ψ₁ :=
  GroupoidStr.TransitionSet.inv (a : S.TTr hU Ψ₁ Ψ₂)

/-- `u(q) = (q, 1, q)`. -/
def unit {C : GCT.{0}} (S : C.PolyfoldConstruction) (hU : S.HasUniformizers)
    (Ψ : S.Unif) (q : Ψ.1.P.TangentSpace) : NT S hU Ψ Ψ :=
  (GroupoidStr.TransitionSet.unit q : S.TTr hU Ψ Ψ)

/-- The fibred product `M(TΨ₂, TΨ₃) ₛ×ₜ M(TΨ₁, TΨ₂)`. -/
def FP {C : GCT.{0}} (S : C.PolyfoldConstruction) (hU : S.HasUniformizers)
    (Ψ₁ Ψ₂ Ψ₃ : S.Unif) : Type 1 :=
  {p : NT S hU Ψ₂ Ψ₃ × NT S hU Ψ₁ Ψ₂ // src S hU Ψ₂ Ψ₃ p.1 = tgt S hU Ψ₁ Ψ₂ p.2}

instance {C : GCT.{0}} (S : C.PolyfoldConstruction) (hU : S.HasUniformizers)
    (Ψ₁ Ψ₂ Ψ₃ : S.Unif) : TopologicalSpace (FP S hU Ψ₁ Ψ₂ Ψ₃) :=
  instTopologicalSpaceSubtype

/-- `m((q', φ', q''), (q, φ, q')) = (q, φ' ∘ φ, q'')`. -/
def mul {C : GCT.{0}} (S : C.PolyfoldConstruction) (hU : S.HasUniformizers)
    (Ψ₁ Ψ₂ Ψ₃ : S.Unif) (p : FP S hU Ψ₁ Ψ₂ Ψ₃) : NT S hU Ψ₁ Ψ₃ :=
  GroupoidStr.TransitionSet.comp (p.1.1 : S.TTr hU Ψ₂ Ψ₃) (p.1.2 : S.TTr hU Ψ₁ Ψ₂) (by
    obtain ⟨⟨⟨s₁, m₁, t₁, hs₁, ht₁⟩, ⟨s₂, m₂, t₂, hs₂, ht₂⟩⟩, h⟩ := p
    change s₁ = t₂ at h
    subst h
    exact hs₁.trans ht₂.symm)

/-- Proposition 17.2.14: the natural topology is metrizable, `s, t` are local homeomorphisms,
`ι` is a homeomorphism, `u` and `m` are continuous. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (hU : S.HasUniformizers),
    (∀ Ψ₁ Ψ₂ : S.Unif, TopologicalSpace.MetrizableSpace (NT S hU Ψ₁ Ψ₂)) ∧
    (∀ Ψ₁ Ψ₂ : S.Unif, IsLocalHomeomorph (src S hU Ψ₁ Ψ₂)) ∧
    (∀ Ψ₁ Ψ₂ : S.Unif, IsLocalHomeomorph (tgt S hU Ψ₁ Ψ₂)) ∧
    (∀ Ψ₁ Ψ₂ : S.Unif, IsHomeomorph (inv S hU Ψ₁ Ψ₂)) ∧
    (∀ Ψ : S.Unif, Continuous (unit S hU Ψ)) ∧
    (∀ Ψ₁ Ψ₂ Ψ₃ : S.Unif, Continuous (mul S hU Ψ₁ Ψ₂ Ψ₃))

end

end RoundTrip.V17_51
