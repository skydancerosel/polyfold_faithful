import Polyfold.Chapter8.BundleOrbitParacompact2021
import Polyfold.Chapter7.Effective
import Polyfold.Chapter10.LocalizationLREffectiveBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 8,
§8.4, **Proposition 8.4.3** (p. 382, new in the 2021 edition).

# (LR) of an effective base passes to strong bundles

## The text, paraphrased

(Proposition 8.4.3) If the ep-groupoid `X` is effective and has the local regularity property
(LR) (Definition 7.4.19), every strong bundle `(P : W → X, μ)` has the local regularity property
of Definition 8.4.2.  *Proof*: a strong bundle isomorphism `B` of `W|U(x)` with `|B(w)| = |w|`
covers `β` with `|β(y)| = |y|`, so `β = g ∗ ·` by (LR); `C(w) = g⁻¹ ∗ B(w)` satisfies
`C(w) = g_w ∗ w`, and `g_w = 1` over the regular points, which are dense; by continuity
`C = id`, i.e. `B(w) = g ∗ w`.

## What is formalized

* `EpGroupoid.eq_of_isRegular_src`: two morphisms with the same source and target at a regular
  object are equal.
* `EpStrongBundle.exists_mor_of_π_eq`: `|Φ(w)| = |w|` gives a morphism `(ψ, w) : w → Φ(w)`, with
  `ψ : P(w) → β(P(w))`.
* **`EpStrongBundle.proposition_8_4_3`**: `X.IsEffective → X.IsLR → E.IsLR`, with the text's
  hypotheses only.

## The proof, and how it relates to the text's

The neighbourhood `U(x)` is the one given by (LR) for `X`.  Over a regular `P(w)` the morphism
`ψ : P(w) → β(P(w)) = g ∗ P(w)` equals `Γ(g, P(w))`, so `Φ(w) = μ(ψ, w) = g ∗ w` directly (the
text's `C(w) = w`).  The regular points are open and dense (Proposition 7.2.4), `P` is an open
map (`StrongBundle.isOpenMap_proj`, Chapter 10), so `P⁻¹(X_reg)` is dense in `W|U(x)`, and the
closed set `{Φ(w) = g ∗ w}` is all of `W|U(x)`.  The uniqueness of `g` (from effectiveness) is not
needed.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **At a regular object, morphisms are determined by source and target**: if `G_{s(ψ)}` is
trivial and `s(φ) = s(ψ)`, `t(φ) = t(ψ)`, then `φ = ψ` (`ψ⁻¹ ∘ φ ∈ G_{s(ψ)}`). -/
theorem eq_of_isRegular_src {φ ψ : Mor} (hreg : X.IsRegular (X.src ψ))
    (hs : X.src φ = X.src ψ) (ht : X.tgt φ = X.tgt ψ) : φ = ψ := by
  have hc : X.src (X.inv ψ) = X.tgt φ := by rw [X.src_inv, ht]
  have hk := hreg ⟨X.comp (X.inv ψ) φ, by rw [X.src_comp _ _ hc, hs],
    by rw [X.tgt_comp _ _ hc, X.tgt_inv]⟩
  have hk' := congrArg GroupoidStr.Isotropy.val hk
  rw [GroupoidStr.Isotropy.val_one] at hk'
  have h := GroupoidStr.eq_inv_of_comp_eq_unit' (G := X.toGroupoidStr) hc
    (hk'.trans (by rw [X.tgt_inv]))
  rwa [GroupoidStr.inv_inv] at h

end EpGroupoid

section Prop843

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B)

namespace EpStrongBundle

omit [ParacompactSpace (pullbackSpace P X.src)] in
/-- **A morphism `w → Φ(w)`**: if `Φ` covers `β` and `|Φ(w)| = |w|`, there is `ψ : P(w) → β(P(w))`
with `Φ(w) = μ(ψ, w)`. -/
theorem exists_mor_of_π_eq {β : Obj → Obj} {Φ : W → W} (hΦ : B.IsStrongBundleMap B β Φ) {w : W}
    (h : E.toGroupoidStr.π (Φ w) = E.toGroupoidStr.π w) :
    ∃ ψ : Mor, ∃ hψ : P w = X.src ψ, X.tgt ψ = β (P w) ∧ E.μ ⟨(ψ, w), hψ⟩ = Φ w := by
  obtain ⟨q, hqs, hqt⟩ := (GroupoidStr.π_eq_π_iff _).1 h.symm
  obtain ⟨⟨ψ, w'⟩, hq⟩ := q
  have hqs' : w' = w := hqs
  subst hqs'
  exact ⟨ψ, hq, (E.P_μ _).symm.trans ((congrArg P hqt).trans (hΦ.covers _)), hqt⟩

/-- **2021 Proposition 8.4.3**, p. 382 (new in the 2021 edition): if the ep-groupoid `X` is
effective (Definition 7.2.1) and has the local regularity property (LR) (Definition 7.4.19),
every strong bundle over `X` has the local regularity property of Definition 8.4.2.  The text's
statement, with no further hypothesis. -/
theorem proposition_8_4_3 (hX : X.IsEffective) (hLR : X.IsLR) : E.IsLR := by
  intro x O hO hxO
  obtain ⟨R, hRO, hR⟩ := hLR x O hO hxO
  refine ⟨R, hRO, fun β Φ hΦ hiso hπ => ?_⟩
  obtain ⟨β', hβ⟩ := hiso.isScDiffeoOn_base
  -- `β` covers `Φ`, so `|β(y)| = |y|` (test on the zero vector `0_y`), and `β = g ∗ ·` by (LR)
  have hβπ : ∀ y ∈ R.U, X.π (β y) = X.π y := fun y hy => by
    have h0 : P (fiberZero P y) = y := isSection_fiberZero y
    obtain ⟨ψ, hψ, hψt, -⟩ := E.exists_mor_of_π_eq hΦ (hπ (fiberZero P y) (by rw [h0]; exact hy))
    rw [h0] at hψ hψt
    exact (X.π_eq_π_iff.2 ⟨ψ, hψ.symm, hψt⟩).symm
  obtain ⟨g, hg⟩ := hR β β' hβ hβπ
  -- `{w | Φ(w) = g ∗ w}` is closed in `W|U(x)` and contains the dense set over `X_reg`
  have hcl : IsClosed {w : E.bundleU R | Φ w.1 = (g • w).1} :=
    isClosed_eq (hΦ.continuous.comp continuous_subtype_val)
      (continuous_subtype_val.comp (E.continuous_bundleSmul R g))
  have hdense : Dense (Subtype.val ⁻¹' (P ⁻¹' X.regularSet) : Set (E.bundleU R)) :=
    ((X.proposition_7_2_4 hX).2.preimage B.isOpenMap_proj).preimage
      (E.isOpen_bundleU R).isOpenMap_subtype_val
  have hsub : (Subtype.val ⁻¹' (P ⁻¹' X.regularSet) : Set (E.bundleU R)) ⊆
      {w | Φ w.1 = (g • w).1} := by
    intro w hw
    have hwU : P w.1 ∈ R.U := w.2
    obtain ⟨ψ, hψ, hψt, hμ⟩ := E.exists_mor_of_π_eq hΦ (hπ w.1 hwU)
    have hΓ : R.Γ g (P w.1) = ψ := X.eq_of_isRegular_src (by rw [← hψ]; exact hw)
      (by rw [R.src_Γ g _ hwU, hψ]) (by rw [R.tgt_Γ g _ hwU, hψt, hg _ hwU])
    change Φ w.1 = E.natLift R g w.1 w.2
    rw [← hμ]
    exact E.μ_congr_fst hψ hΓ.symm
  have h := hcl.closure_subset_iff.2 hsub
  rw [hdense.closure_eq] at h
  exact ⟨g, fun w hw => h (mem_univ ⟨w, hw⟩)⟩

end EpStrongBundle

end Prop843

end Polyfold
