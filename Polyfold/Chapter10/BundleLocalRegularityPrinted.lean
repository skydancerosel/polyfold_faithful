import Polyfold.Chapter8.BundleLocalRegularity2021
import Polyfold.Chapter10.LocalizationLRBundleBase

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 8,
§8.4, **Proposition 8.4.3** (p. 382, new in the 2021 edition), **with Definition 8.4.2 as
printed**.

# (LR) of an effective base passes to strong bundles, for isomorphisms of `W|U(x)`

Definition 8.4.2 as printed asks that every strong bundle isomorphism `B : W|U(x) → W|U(x)`
with `|B(w)| = |w|` be `w ↦ g ∗ w`; this is `EpStrongBundle.IsLRLocal`
(`Chapter10/LocalizationLRBundleBase.lean`, which uses `StrongBundle.IsLocalIsoOn`).  The form
`EpStrongBundle.IsLR` of Chapter 8 asks it only of strong bundle maps of `W`, and
`EpStrongBundle.proposition_8_4_3` (`Chapter8/BundleLocalRegularity2021.lean`) proves that form.
This file proves the printed form, by the text's proof.

## What is formalized

* `EpStrongBundle.exists_mor_of_π_eq_of_isLocalIsoOn`: for a strong bundle isomorphism `Φ` of
  `W|U` covering `β`, `P(w) ∈ U` and `|Φ(w)| = |w|` give a morphism `(ψ, w) : w → Φ(w)` with
  `ψ : P(w) → β(P(w))`.
* **`EpStrongBundle.proposition_8_4_3_isLRLocal`**: `X.IsEffective → X.IsLR → E.IsLRLocal`, with
  the text's hypotheses only.

## The proof

The neighbourhood `U(x)` is the one given by (LR) for `X`; the proof uses `B` only over `U(x)`.
Testing on the zero vectors gives `|β(y)| = |y|`, so `β = g ∗ ·` by (LR).  Over a regular `P(w)`
the morphism `ψ : P(w) → g ∗ P(w)` equals `Γ(g, P(w))`, so `B(w) = g ∗ w`.  The regular points are
open and dense (Proposition 7.2.4) and `P` is open, so `P⁻¹(X_reg)` is dense in `W|U(x)`; `B` is
continuous on `W|U(x)` (an sc-diffeomorphism there), so the closed set `{B(w) = g ∗ w}` is all of
`W|U(x)`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

section Prop843Printed

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B)

namespace EpStrongBundle

omit [ParacompactSpace (pullbackSpace P X.src)] in
/-- **A morphism `w → Φ(w)` for a strong bundle isomorphism of `W|U`**: if `Φ` is one, covering
`β`, `P(w) ∈ U` and `|Φ(w)| = |w|`, there is `ψ : P(w) → β(P(w))` with `Φ(w) = μ(ψ, w)`. -/
theorem exists_mor_of_π_eq_of_isLocalIsoOn {β : Obj → Obj} {Φ : W → W} {U : Set Obj}
    (hΦ : B.IsLocalIsoOn β Φ U) {w : W} (hw : P w ∈ U)
    (h : E.toGroupoidStr.π (Φ w) = E.toGroupoidStr.π w) :
    ∃ ψ : Mor, ∃ hψ : P w = X.src ψ, X.tgt ψ = β (P w) ∧ E.μ ⟨(ψ, w), hψ⟩ = Φ w := by
  obtain ⟨q, hqs, hqt⟩ := (GroupoidStr.π_eq_π_iff _).1 h.symm
  obtain ⟨⟨ψ, w'⟩, hq⟩ := q
  have hqs' : w' = w := hqs
  subst hqs'
  exact ⟨ψ, hq, (E.P_μ _).symm.trans ((congrArg P hqt).trans (hΦ.covers hw)), hqt⟩

/-- **2021 Proposition 8.4.3**, p. 382 (new in the 2021 edition), **with Definition 8.4.2 as
printed**: if the ep-groupoid `X` is effective (Definition 7.2.1) and has the local regularity
property (LR) (Definition 7.4.19), every strong bundle over `X` has the local regularity property
of Definition 8.4.2 for strong bundle isomorphisms `B : W|U(x) → W|U(x)`
(`EpStrongBundle.IsLRLocal`).  The text's statement, with no further hypothesis. -/
theorem proposition_8_4_3_isLRLocal (hX : X.IsEffective) (hLR : X.IsLR) : E.IsLRLocal := by
  intro x O hO hxO
  obtain ⟨R, hRO, hR⟩ := hLR x O hO hxO
  refine ⟨R, hRO, fun β Φ hΦ hπ => ?_⟩
  obtain ⟨β', hβ⟩ := hΦ.isScDiffeoOn_base
  obtain ⟨Ψ, hΨ⟩ := hΦ.isScDiffeoOn_zero
  -- `|β(y)| = |y|` (test on the zero vector `0_y`), so `β = g ∗ ·` by (LR)
  have hβπ : ∀ y ∈ R.U, X.π (β y) = X.π y := fun y hy => by
    have h0 : P (fiberZero P y) = y := isSection_fiberZero y
    have hy' : P (fiberZero P y) ∈ R.U := by rw [h0]; exact hy
    obtain ⟨ψ, hψ, hψt, -⟩ := E.exists_mor_of_π_eq_of_isLocalIsoOn hΦ hy' (hπ _ hy')
    rw [h0] at hψ hψt
    exact (X.π_eq_π_iff.2 ⟨ψ, hψ.symm, hψt⟩).symm
  obtain ⟨g, hg⟩ := hR β β' hβ hβπ
  -- `{w | Φ(w) = g ∗ w}` is closed in `W|U(x)` and contains the dense set over `X_reg`
  have hΦc : Continuous fun w : E.bundleU R => Φ w.1 :=
    hΨ.isScSmoothOn.continuousOn.domRestrict
  have hcl : IsClosed {w : E.bundleU R | Φ w.1 = (g • w).1} :=
    isClosed_eq hΦc (continuous_subtype_val.comp (E.continuous_bundleSmul R g))
  have hdense : Dense (Subtype.val ⁻¹' (P ⁻¹' X.regularSet) : Set (E.bundleU R)) :=
    ((X.proposition_7_2_4 hX).2.preimage B.isOpenMap_proj).preimage
      (E.isOpen_bundleU R).isOpenMap_subtype_val
  have hsub : (Subtype.val ⁻¹' (P ⁻¹' X.regularSet) : Set (E.bundleU R)) ⊆
      {w | Φ w.1 = (g • w).1} := by
    intro w hw
    have hwU : P w.1 ∈ R.U := w.2
    obtain ⟨ψ, hψ, hψt, hμ⟩ := E.exists_mor_of_π_eq_of_isLocalIsoOn hΦ hwU (hπ w.1 hwU)
    have hΓ : R.Γ g (P w.1) = ψ := X.eq_of_isRegular_src (by rw [← hψ]; exact hw)
      (by rw [R.src_Γ g _ hwU, hψ]) (by rw [R.tgt_Γ g _ hwU, hψt, hg _ hwU])
    change Φ w.1 = E.natLift R g w.1 w.2
    rw [← hμ]
    exact E.μ_congr_fst hψ hΓ.symm
  have h := hcl.closure_subset_iff.2 hsub
  rw [hdense.closure_eq] at h
  exact ⟨g, fun w hw => h (mem_univ ⟨w, hw⟩)⟩

end EpStrongBundle

end Prop843Printed

end Polyfold
