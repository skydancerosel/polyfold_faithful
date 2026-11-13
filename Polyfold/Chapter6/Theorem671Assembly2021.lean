import Polyfold.Chapter6.Theorem671_2021
import Polyfold.Chapter6.InvariantCobordism2021

/-!
# 2021 Theorem 6.7.1 (p. 277) and the case `∂X = ∅` (p. 279), under two cobordism hypotheses

`Theorem671_2021` proves Theorem 6.7.1 from the two steps of its proof, stated as `Prop`s:
(A) `PsiIndepAdmissible` (the invariant `psiAt` does not depend on the admissible section) and
(B) `PsiIndepHomotopy` (it is invariant under proper oriented homotopies).
`InvariantCobordism2021` proves the cobordism identity `psiAt_eq_of_cobordism`: for cobordism
data `Ŝ` (`IsCobordismData`) between `f₀ + s₀` and `f₀ + σ₁ = f₁ + s₁`,
`Ψ_{s₀}(f₀, o₀) = Ψ_{s₁}(f₁, o₁)`, given an orientation of the cobordism `S_F` of product form on
its ends (`CobordismOrientation`) and relative forms on it (`CobordismRelativeForms`). That file
does not state (A) and (B) themselves.

This file bridges the two. With the cobordism data of part (1) (`exists_isCobordismData`) and of
part (2) (`exists_homotopy_cobordism_data`), `psiAt_eq_of_admissible_hyp` and
`psiAt_eq_of_homotopy_hyp` prove (A) and (B) in exactly the form of `PsiIndepAdmissible` and
`PsiIndepHomotopy`, under two hypotheses: `CobordismOrientationHyp` and
`CobordismRelativeFormsHyp`, which say that 4b's `CobordismOrientation` and
`CobordismRelativeForms` hold for the cobordism data that parts (1) and (2) use. In (B) the two
pairs `(N₀, U₀)`, `(N₁, U₁)` are joined through `psiInvariant_eq_psiAt` (with (A)): the cobordism
is built for `N₀`, on a neighbourhood of `S_{f₁}` with the margin for `N₀`
(`exists_isAdmissible_nbhd`).

## Main declarations

* `CobordismOrientationHyp B hX`, `CobordismRelativeFormsHyp B hX`: the two remaining hypotheses
  (since proved, resp. no longer needed: `cobordismOrientationHyp`, `cobordismRelativeFormsInner`).
* `psiAt_eq_of_admissible_hyp`: (A), `PsiIndepAdmissible B hX hbump`.
* `psiAt_eq_of_homotopy_hyp`: (B), `PsiIndepHomotopy B hX hbump`.
* `theorem_6_7_1_hyp`: 2021 Theorem 6.7.1 under the two hypotheses.
* `theorem_6_7_1_noBoundary_hyp`: the case `∂X = ∅` (p. 279) under the two hypotheses.

## The two hypotheses, and what would discharge them

`CobordismOrientationHyp` says: for every cobordism `S_F` built in part (1) (between two sections
admissible for one `(N, U)`, both ends oriented by `o`) and in part (2) (along a proper oriented
homotopy, the right end oriented by `o₁ = o₀.sectionAdd S(1, ·)`), and every degree `k`, the
index-`(k+1)` part `S_F^{k+1}` carries a continuous orientation equal to `e ∧ o_{S_i}` on the two
product ends `(0, 1/8) × S₀` and `(7/8, 1) × S₁` (Remark 6.6.19; gap G.66). It would follow from
`SectionOrientation.prodFirst` (the orientation `e ∧ o` of `f̃` over `ℝ¹ × X`) and its value on the
end slices: the items 1–4, 6, 7 of `w1c2-prodor` (about 680 lines: the lift `liftProd` of
sc⁺-sections along `(τ, (t, x)) ↦ (τ, x)`; the stabilized kernels `ℝ × Λ`; continuation commuting
with `ê ∧ ·`; the push relation for `prodOrFirst`; the assembly through
`isSectionOrientation_iff`; `theorem_6_6_18_oriented` for `f̃ + Ŝ` with the value `e ∧ (o)` at the
end slices), with item 5 (`ChartPoint.orTransfer_prodPt_prodOrFirst`) already proved.
`CobordismRelativeFormsHyp` says: for every such cobordism, every closed relative form
`c = (ω, τ)` of degree `k` and integrands `a₀`, `a₁` of `c` on the ends (`IsPsiIntegrand`:
`a_i = ω|_{S_i} + dγ_i` with `γ_i` extending `−τ|_{∂S_i}`), there is a closed `C^∞` `k`-form `A` on
`S_F^{k+1}` with vanishing face restriction that reads as `a₀` and `a₁` on the ends. It would follow
from `A = p₁^*ω|_{S_F} + dγ_F`, with `γ_F` an extension of `−(p₁^*τ)|_{∂S_F}` equal to `p₁^*γ_i`
on the ends; the part `p₁^*ω|_{S_F}` is available (`isEndPullback_formsInftyRestrict_snd`), and
the rest is the face-form part of `w3b2-ends` (§2, "Face forms on ∂S_F", 600–1000 lines): the
pull-back of forms on `∂X` to `∂(ℝ¹ × X)` along `p₁` and its reading on the product charts of
the faces of `S_F`, the pull-back of `ManifoldForm`s along the end projection, and the extension
property (`IsExtendedBy`) at the face points of the ends. Neither hypothesis quantifies over all
orientations: the orientations are fixed by `o` (part (1)) and by `o₀`, `S` (part (2)), and the
relative forms do not involve orientations. No Lean witness of the two hypotheses is given here.

Superseded in part (2026-11-12). `SectionOrientation.prodFirst` is built
(`ProductSectionOrientation2021c`–`f`), and `CobordismOrientation2021` gives the continuous
orientation `cobOr` of `S_F` and reduces `CobordismOrientationHyp` to its product form on the two
ends (`cobordismOrientation_of_ends`); the end statement is proved in `CobordismOrientationEnds2021d`
(`cobordismOrientationHyp`). The relative form is
built on the inner ends (`cobordismRelativeFormsInner`, `CobordismRelativeForms2021b`), and
`theorem_6_7_1_of_orientation`, `theorem_6_7_1_noBoundary_of_orientation` state the theorem under
`CobordismOrientationHyp` alone. Theorem 6.7.1 without hypotheses on the cobordism is
`theorem_6_7_1`, `theorem_6_7_1_noBoundary` (`Theorem671Final2021`). `CobordismRelativeFormsHyp` and
the `_hyp` theorems here are kept.
-/

open Set

noncomputable section

namespace Polyfold

universe u v

open MPolyfold StrongBundle

section Hypotheses

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

variable (B : StrongBundle PX P) (hX : PX.IsTame)

/-- **The orientation of the cobordisms of the proof of 2021 Theorem 6.7.1** (Remark 6.6.19,
p. 276; proof of Theorem 6.7.1, p. 278–279; gap G.66): 4b's `CobordismOrientation` for
* part (1): cobordism data `Ŝ` between `f + s₀` and `f + s₁`, `s₀`, `s₁` admissible for one
  `(N, U)`, both ends oriented by `o`;
* part (2): cobordism data `Ŝ` between `f₀ + s₀` and `f₀ + (S(1, ·) + s₁) = f₁ + s₁` for a proper
  oriented homotopy `S` from `(f₀, o₀)` to `(f₁, o₁)` (`IsProperOrientedHomotopyBetween`).
Proved: `cobordismOrientationHyp` (`CobordismOrientationEnds2021d`), from
`SectionOrientation.prodFirst` (`ProductSectionOrientation2021f`), `cobordismOrientation_of_ends`
(`CobordismOrientation2021`) and the value `e ∧ o_{S_i}` of `cobOr` on the two ends
(`isEndProductOrientation_cobOr`). -/
def CobordismOrientationHyp : Prop :=
  haveI := paracompactSpace_rn_prod PX 1
  haveI := paracompactSpace_rn_pullback B 1
  (∀ (f : X → Y) (hf : B.IsScFredholmSectionTame f)
      (o : SectionOrientation f hf.toIsScFredholmSection) (N : B.One → ℝ) (U : Set X)
      (s₀ s₁ : X → Y) (hs₀ : B.IsAdmissible f N U s₀) (hs₁ : B.IsAdmissible f N U s₁)
      (Ŝ : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
      (hC : B.IsCobordismData f hf.isScSmooth.1 s₀ s₁ Ŝ) (k : ℕ),
      CobordismOrientation hX hf hs₀ o hf hs₁ o hC rfl k) ∧
  ∀ (f₀ : X → Y) (hf₀ : B.IsScFredholmSectionTame f₀)
    (o₀ : SectionOrientation f₀ hf₀.toIsScFredholmSection)
    (S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
    (hf₁ : B.IsScFredholmSectionTame (sectionAdd P f₀ (pullbackSlice S 1)))
    (o₁ : SectionOrientation (sectionAdd P f₀ (pullbackSlice S 1)) hf₁.toIsScFredholmSection),
    IsProperOrientedHomotopyBetween hf₀ o₀ S o₁ →
    ∀ (N₀ : B.One → ℝ) (U₀ : Set X) (s₀ : X → Y) (hs₀ : B.IsAdmissible f₀ N₀ U₀ s₀)
      (N₁ : B.One → ℝ) (U₁ : Set X) (s₁ : X → Y)
      (hs₁ : B.IsAdmissible (sectionAdd P f₀ (pullbackSlice S 1)) N₁ U₁ s₁)
      (Ŝ : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
      (hC : B.IsCobordismData f₀ hf₀.isScSmooth.1 s₀ (sectionAdd P (pullbackSlice S 1) s₁) Ŝ)
      (h₁ : sectionAdd P f₀ (sectionAdd P (pullbackSlice S 1) s₁) =
        sectionAdd P (sectionAdd P f₀ (pullbackSlice S 1)) s₁) (k : ℕ),
      CobordismOrientation hX hf₀ hs₀ o₀ hf₁ hs₁ o₁ hC h₁ k

/-- **The relative forms on the cobordisms of the proof of 2021 Theorem 6.7.1** (the form
`p₁^*ω − dβ` on `S_F`, p. 278): 4b's `CobordismRelativeForms` for all cobordism data `Ŝ` between
`f₀ + s₀` and `f₀ + σ₁ = f₁ + s₁` (orientations play no role). Not proved as stated (on the full
ends it would need a smooth extension across `t = 1/8`); no longer needed: the inner-end form
`cobordismRelativeFormsInner` (`CobordismRelativeForms2021b`) replaces it in
`theorem_6_7_1_of_orientation`. -/
def CobordismRelativeFormsHyp : Prop :=
  haveI := paracompactSpace_rn_prod PX 1
  haveI := paracompactSpace_rn_pullback B 1
  ∀ (f₀ : X → Y) (hf₀ : B.IsScFredholmSectionTame f₀) (N₀ : B.One → ℝ) (U₀ : Set X)
    (s₀ : X → Y) (hs₀ : B.IsAdmissible f₀ N₀ U₀ s₀) (f₁ : X → Y)
    (hf₁ : B.IsScFredholmSectionTame f₁) (N₁ : B.One → ℝ) (U₁ : Set X) (s₁ : X → Y)
    (hs₁ : B.IsAdmissible f₁ N₁ U₁ s₁) (σ₁ : X → Y)
    (Ŝ : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
    (hC : B.IsCobordismData f₀ hf₀.isScSmooth.1 s₀ σ₁ Ŝ)
    (h₁ : sectionAdd P f₀ σ₁ = sectionAdd P f₁ s₁) (k : ℕ),
    CobordismRelativeForms hX hf₀ hs₀ hf₁ hs₁ hC h₁ k

end Hypotheses

section Steps

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)

/-- **(A) of the proof of 2021 Theorem 6.7.1** (p. 277–279), under the two cobordism hypotheses:
`Ψ_{s₀} = Ψ_{s₁}` for two sections admissible for one `(N, U)` (`PsiIndepAdmissible`). The
cobordism data come from `exists_isCobordismData` (margin at `C = 2`), the identity from
`psiAt_eq_of_cobordism`. -/
theorem psiAt_eq_of_admissible_hyp (hOr : CobordismOrientationHyp B hX)
    (hRel : CobordismRelativeFormsHyp B hX) : PsiIndepAdmissible B hX hbump := by
  intro f hf _ o N hN U hU hSU hmar s₀ s₁ hs₀ hs₁ k
  have := paracompactSpace_rn_prod PX 1
  have := paracompactSpace_rn_pullback B 1
  obtain ⟨hOrA, -⟩ := hOr
  obtain ⟨Ŝ, hC⟩ := exists_isCobordismData hX hbump hf hN hU hSU (hmar 2 two_pos) hs₀.mem
    hs₁.mem hs₀.gp hs₁.gp
  exact psiAt_eq_of_cobordism hX hbump hf hs₀ o hf hs₁ o hC rfl k
    (hOrA f hf o N U s₀ s₁ hs₀ hs₁ Ŝ hC k) (hRel f hf N U s₀ hs₀ f hf N U s₁ hs₁ s₁ Ŝ hC rfl k)

/-- **(B) of the proof of 2021 Theorem 6.7.1** (p. 279, "the same homotopy argument"), under the
two cobordism hypotheses: `Ψ_{s₀}(f₀, o₀) = Ψ_{s₁}(f₁, o₁)` along a proper oriented homotopy
(`PsiIndepHomotopy`). The cobordism `exists_homotopy_cobordism_data` is built for `N₀`, on `U₀`
and on a neighbourhood `V₁` of `S_{f₁}` with the margin for `N₀`; `(N₀, U₀)` is reached by (A),
and `(N₀, V₁)` is compared with `(N₁, U₁)` through `psiInvariant_eq_psiAt`. -/
theorem psiAt_eq_of_homotopy_hyp (hOr : CobordismOrientationHyp B hX)
    (hRel : CobordismRelativeFormsHyp B hX) : PsiIndepHomotopy B hX hbump := by
  intro f₀ hf₀ o₀ S hf₁ o₁ hHB N₀ hN₀ U₀ hU₀ hSU₀ hmar₀ N₁ hN₁ U₁ hU₁ hSU₁ hmar₁ s₀ s₁ hs₀ hs₁ k
  have := paracompactSpace_rn_prod PX 1
  have := paracompactSpace_rn_pullback B 1
  have hA := psiAt_eq_of_admissible_hyp hX hbump hOr hRel
  obtain ⟨-, hOrB⟩ := hOr
  obtain ⟨hH, -⟩ := id hHB
  have hP₀ : B.IsProper f₀ := hH.isProper_zero
  have hP₁ : B.IsProper (sectionAdd P f₀ (pullbackSlice S 1)) := hH.isProper_one
  obtain ⟨V₁, hV₁, hSV₁, hmarV₁, -⟩ :=
    exists_isAdmissible_nbhd hX hbump hf₁ hH.isCompact_solutionSet_one hN₀
  obtain ⟨s₀', s₁', Ŝ, h₀', hgp₀', h₁', hgp₁', hC⟩ :=
    exists_homotopy_cobordism_data hX hbump hH hN₀ hU₀ hSU₀ hV₁ hSV₁
  have hs₀' : B.IsAdmissible f₀ N₀ U₀ s₀' := ⟨h₀', hgp₀'⟩
  have hs₁' : B.IsAdmissible (sectionAdd P f₀ (pullbackSlice S 1)) N₀ V₁ s₁' := ⟨h₁', hgp₁'⟩
  have h₁ : sectionAdd P f₀ (sectionAdd P (pullbackSlice S 1) s₁') =
      sectionAdd P (sectionAdd P f₀ (pullbackSlice S 1)) s₁' :=
    (sectionAdd_assoc hf₀.isScSmooth.1 hH.slice_one.1 hs₁'.isScPlusSection.1).symm
  calc psiAt hX hbump hf₀ hs₀ o₀ k = psiAt hX hbump hf₀ hs₀' o₀ k :=
        hA f₀ hf₀ hP₀ o₀ N₀ hN₀ U₀ hU₀ hSU₀ hmar₀ s₀ s₀' hs₀ hs₀' k
    _ = psiAt hX hbump hf₁ hs₁' o₁ k :=
        psiAt_eq_of_cobordism hX hbump hf₀ hs₀' o₀ hf₁ hs₁' o₁ hC h₁ k
          (hOrB f₀ hf₀ o₀ S hf₁ o₁ hHB N₀ U₀ s₀' hs₀' N₀ V₁ s₁' hs₁' Ŝ hC h₁ k)
          (hRel f₀ hf₀ N₀ U₀ s₀' hs₀' _ hf₁ N₀ V₁ s₁' hs₁' _ Ŝ hC h₁ k)
    _ = psiInvariant hX hbump hf₁ hP₁ o₁ k :=
        (psiInvariant_eq_psiAt hX hbump hA hf₁ hP₁ o₁ hN₀ hV₁ hSV₁ hmarV₁ hs₁' k).symm
    _ = psiAt hX hbump hf₁ hs₁ o₁ k :=
        psiInvariant_eq_psiAt hX hbump hA hf₁ hP₁ o₁ hN₁ hU₁ hSU₁ hmar₁ hs₁ k

end Steps

section Theorem

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- **2021 Theorem 6.7.1** (p. 277; preprint Theorem 6.43), under the two cobordism hypotheses.
The statement is that of `theorem_6_7_1_of_indep` (where the trace of each hypothesis to the text
is given); its hypotheses (A) and (B) are discharged by `psiAt_eq_of_admissible_hyp` and
`psiAt_eq_of_homotopy_hyp`. What remains are `CobordismOrientationHyp` (the orientation of the
cobordism `S_F`, Remark 6.6.19, gap G.66) and `CobordismRelativeFormsHyp` (a relative form on
`S_F`), which are steps of the text's proof, not hypotheses of the text. (2) is read as in R-d.
Superseded by `theorem_6_7_1` (`Theorem671Final2021`), the same statement without the two
hypotheses. -/
theorem theorem_6_7_1_hyp (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hOr : CobordismOrientationHyp B hX) (hRel : CobordismRelativeFormsHyp B hX) :
    ∃ Ψ : ∀ (f : X → Y) (hf : B.IsScFredholmSectionTame f), B.IsProper f →
        SectionOrientation f hf.toIsScFredholmSection → ∀ k : ℕ, relDeRham hX k →ₗ[ℝ] ℝ,
      (∀ (f : X → Y) (hf : B.IsScFredholmSectionTame f) (hP : B.IsProper f)
          (o : SectionOrientation f hf.toIsScFredholmSection) (N : B.One → ℝ), B.IsAuxNorm N →
        (∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
          ∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U | B.AuxLe N (f x) C})) ∧
        ∀ U : Set X, IsOpen U → solutionSet P f ⊆ U →
          (∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U | B.AuxLe N (f x) C})) →
          (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
          (∃ s, B.IsAdmissible f N U s) ∧
          ∀ (s : X → Y) (hs : B.IsAdmissible f N U s),
            IsCompact (solutionSet P (sectionAdd P f s)) ∧
            solutionSet P (sectionAdd P f s) = ⋃ k : ℕ, B.solPart f s k ∧
            ∀ k : ℕ, IsCompact (B.solPart f s k) ∧ SolPartIsOrientedManifold hX hf hs o k ∧
              ∀ c : LinearMap.ker (relD hX k),
                Ψ f hf hP o k (relDeRhamMk hX k c) =
                  solIntegral hX hbump hf hs o k c - solBoundaryIntegral hX hbump hf hs o k c) ∧
      ∀ (f₀ : X → Y) (hf₀ : B.IsScFredholmSectionTame f₀) (hP₀ : B.IsProper f₀)
        (o₀ : SectionOrientation f₀ hf₀.toIsScFredholmSection)
        (S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
        (hf₁ : B.IsScFredholmSectionTame (sectionAdd P f₀ (pullbackSlice S 1)))
        (hP₁ : B.IsProper (sectionAdd P f₀ (pullbackSlice S 1)))
        (o₁ : SectionOrientation (sectionAdd P f₀ (pullbackSlice S 1)) hf₁.toIsScFredholmSection),
        IsProperOrientedHomotopyBetween hf₀ o₀ S o₁ →
          ∀ k : ℕ, Ψ f₀ hf₀ hP₀ o₀ k = Ψ _ hf₁ hP₁ o₁ k :=
  theorem_6_7_1_of_indep hX hbump (psiAt_eq_of_admissible_hyp hX hbump hOr hRel)
    (psiAt_eq_of_homotopy_hyp hX hbump hOr hRel)

/-- **2021 p. 279, the case `∂X = ∅` of Theorem 6.7.1** (2017: after Theorem 6.4; preprint
p. 233), under the two cobordism hypotheses: the statement of
`theorem_6_7_1_noBoundary_of_indep` (`Φ([ω]) = ∫_{S_{f+s}} ω` in the degree `n` of the constant
index, `Φ = 0` in the other degrees, homotopy invariance), with (A) and (B) discharged as in
`theorem_6_7_1_hyp`. Superseded by `theorem_6_7_1_noBoundary` (`Theorem671Final2021`). -/
theorem theorem_6_7_1_noBoundary_hyp (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hbd : PX.IsWithoutBoundary) (hOr : CobordismOrientationHyp B hX)
    (hRel : CobordismRelativeFormsHyp B hX) :
    ∃ Φ : ∀ (f : X → Y) (hf : B.IsScFredholmSectionTame f), B.IsProper f →
        SectionOrientation f hf.toIsScFredholmSection →
          ∀ k : ℕ, (BundledMPolyfold.of PX).scDeRham k →ₗ[ℝ] ℝ,
      (∀ (f : X → Y) (hf : B.IsScFredholmSectionTame f) (hP : B.IsProper f)
          (o : SectionOrientation f hf.toIsScFredholmSection) (N : B.One → ℝ), B.IsAuxNorm N →
        (∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
          ∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U | B.AuxLe N (f x) C})) ∧
        ∀ U : Set X, IsOpen U → solutionSet P f ⊆ U →
          (∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U | B.AuxLe N (f x) C})) →
          (∃ s, B.IsAdmissible f N U s) ∧
          ∀ (s : X → Y) (hs : B.IsAdmissible f N U s) (n : ℕ),
            (∀ x ∈ PX.smoothSet, B.IsIndexAt f x n) →
            IsCompact (solutionSet P (sectionAdd P f s)) ∧
            B.solPart f s n = solutionSet P (sectionAdd P f s) ∧
            (∀ c : LinearMap.ker ((BundledMPolyfold.of PX).formsInftyD n),
              letI := solPartChartedSpace hX hf hs n
              haveI := isManifold_solPart hX hf hs n
              Φ f hf hP o n ((BundledMPolyfold.of PX).scDeRhamMk n c) =
                ManifoldForm.integral (solPartOr hX hf hs o n)
                  (formsInftyRestrict n (hasCornerStructureOfDim_solPart hX hf hs n)
                    (c : (BundledMPolyfold.of PX).formsInfty n))) ∧
            ∀ k : ℕ, k ≠ n → Φ f hf hP o k = 0) ∧
      ∀ (f₀ : X → Y) (hf₀ : B.IsScFredholmSectionTame f₀) (hP₀ : B.IsProper f₀)
        (o₀ : SectionOrientation f₀ hf₀.toIsScFredholmSection)
        (S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
        (hf₁ : B.IsScFredholmSectionTame (sectionAdd P f₀ (pullbackSlice S 1)))
        (hP₁ : B.IsProper (sectionAdd P f₀ (pullbackSlice S 1)))
        (o₁ : SectionOrientation (sectionAdd P f₀ (pullbackSlice S 1)) hf₁.toIsScFredholmSection),
        IsProperOrientedHomotopyBetween hf₀ o₀ S o₁ →
          ∀ k : ℕ, Φ f₀ hf₀ hP₀ o₀ k = Φ _ hf₁ hP₁ o₁ k :=
  theorem_6_7_1_noBoundary_of_indep hX hbump hbd (psiAt_eq_of_admissible_hyp hX hbump hOr hRel)
    (psiAt_eq_of_homotopy_hyp hX hbump hOr hRel)

end Theorem

end Polyfold
