import Polyfold.Chapter3.GoodPositionGerm
import Polyfold.Chapter3.GermFillerLinearization
import Polyfold.Chapter3.GermFillingChart

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6,
**Definition 3.6.6 (preprint 3.53)** (good position of an sc-Fredholm germ) and the linear part of the proof of
**Theorem 3.6.8 (preprint 3.54)**, **in the text's germ reading** of Definition 3.1.11 (preprint 3.11) (phase 2): the filling `g` is an
sc-smooth germ on a germ of neighbourhoods `G` of `0` whose levels may shrink, so `Dg(0)` is the
value at `0` of a derivative family `Dg` of the sc¹-germ `g` (`IsSc1GermWith G g Dg`), not
`scDeriv U g 0`.

# Good position of an sc-Fredholm germ, germ reading

## The text, paraphrased

See `GoodPositionGerm.lean`.  (Definition 3.6.6 (preprint 3.53)) `(f, x)` with `f(x) = 0` is in good position if
`f'(x) : T_xX → Y_x` is onto and `ker f'(x)` is in good position to `C_xX`.  (Proof of Theorem
3.54) `Dg(0)` is then onto, `ker Dg(0) = ker Tf̃(0) ⊕ {0}` is in good position to `C` in `E`, and
the same holds for the push-forward `Ψ_*(g) = h + t`.  The text works with germs throughout.

## What is formalized

* `Polyfold.IsFillingGerm.ker_deriv_le_range`, `IsFillingGerm.map_ker_fillerRestrict`: for a
  filling germ `g` with a derivative family `Dg` on a germ `G₁ ⊆ U`, `ker Dg(0) ⊆ T₀O = Dr(0)E`
  and `ker Tf̃(0) = ker Dg(0)` (the germ forms of the `IsFillerOf` lemmas).
* `Polyfold.IsGoodPositionAtGerm hU hR h0 Dg₀`: **Definition 3.6.6 (preprint 3.53) in the chart, parametrised by
  the linearization `Dg₀ : E₀ → F₀`** in place of `scDeriv U g 0`; `isGoodPositionAt_iff_germ`:
  the project's `IsGoodPositionAt` is the case `Dg₀ = scDeriv U g 0`;
  `IsSc1GermWith.deriv_zero_eq` / `IsSc1GermWith.deriv_zero_eq_scDeriv`: `Dg(0)` does not
  depend on the germ or the family, and is `scDeriv U g 0` when `g` is sc¹ on `U`.
* `Polyfold.theorem_3_6_8_linear` (and `_of_isTameWith_germ`): the linear part of Theorem 3.6.8 (preprint 3.54)
  for a filling germ: `Dg(0)` onto, `ker Dg(0)` in good position to `C` in `E`.
* `Polyfold.IsStrongBundleIso.exists_fiber_base_equiv` (`Γ(0)`, `Dψ(0)` as isomorphisms),
  `IsStrongBundleIso.pushforward_linearization`, `pushforward_surjective`,
  `pushforward_ker_isInGoodPosition`: the transfer to `Ψ_*(g)` for a germ `g`, with the
  push-forward germ on `pullGerm` and the derivative family `pushforwardDeriv`.
* `Polyfold.theorem_3_6_8_pushforward`: the step of Theorem 3.6.8 (preprint 3.54) before Theorem 3.5.11 (preprint 3.47) for a
  filling germ; **the Fredholm property of `Dg(0)` (Proposition 3.6.5 (preprint 3.52)) is a hypothesis** here — in
  the germ reading it is Proposition 3.6.5 (preprint 3.52) for germs (Stage 1 B, `FredholmGermLinearizationG.lean`).
* `Polyfold.StrongBundle.IsGoodPositionGerm f x₀`: **Definition 3.6.6 (preprint 3.53) for a section, germ
  reading** (the data of `IsScFredholmGerm` with `IsGoodPositionAtGerm` at `Dg(0)` for a derivative
  family `Dg` of `g` on a germ `G ⊆ U`); `IsGoodPositionGerm.isScFredholmGerm`,
  `IsGoodPositionGermWholeChart.isGoodPositionGerm` (project ⇒ germ reading),
  `isGoodPositionGerm_iff_germG_wholeChart` (the project's notion is the germ reading with `g`, `s`
  sc-smooth on the whole `U`), `IsGoodPositionGerm.forall_isGoodPositionAtGerm` (good position at
  the value `Dg(0)` of every derivative family on every germ; chart level:
  `IsGoodPositionAtGerm.of_isSc1GermWith`), and `theorem_3_6_8_pushforward_section`.

## What the text leaves implicit, and the choices made

* **`Dg(0)` of a germ is a parameter, not a choice.**  For a germ `g` there is no canonical
  `scDeriv U g 0` (on `U` it is junk when `g` is not sc¹ there); the definition takes the
  operator `Dg₀`, and the section-level notion asks for some derivative family `Dg` on some germ
  `G ⊆ U`.  This is no loss: `Dg(0)` is the same for all germs and families
  (`IsSc1GermWith.deriv_zero_eq`, uniqueness of the derivative at `0` on `G ∩ G'`, `C` a partial
  quadrant), so "some" and "every" agree (`IsGoodPositionGerm.forall_isGoodPositionAtGerm`).
* **Proposition 3.6.5 (preprint 3.52) is not re-proved here.**  The push-forward statements whose proofs used
  `proposition_3_6_5_local_wholeChart` (the Fredholm property of `Dg(0)`, and through it the finite
  dimension of `ker Dg(0)` needed by Lemma 3.5.9 (preprint 3.45)) take `IsFredholm (Dg 0)` as hypothesis; the
  section-level theorem states those parts under `IsFredholm (Dg 0) → …`.
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

variable {E F : ScBanach}

/-! ### Uniqueness of `Dg(0)` for a germ -/

section DerivZero

variable {C : Set (E 0)}

/-- **`Dg(0)` does not depend on the germ or on the derivative family** (germ reading, phase 2):
two derivative families of `g` on two germs agree at `0` (uniqueness of the derivative at `0`
within the level `1` of `G₁ ∩ G₂`, `C` quadrant-like). -/
theorem IsSc1GermWith.deriv_zero_eq (hC : IsQuadrantLike E C) {G₁ G₂ : ScNbhdGerm E C}
    {g : E 0 → F 0} {D₁ D₂ : E 1 → E 0 →L[ℝ] F 0} (h₁ : IsSc1GermWith G₁ g D₁)
    (h₂ : IsSc1GermWith G₂ g D₂) : D₁ 0 = D₂ 0 :=
  (h₁.mono (G₁.inter_subset_left G₂)).eq_of_uniqueDiffWithinAt
    (h₂.mono (G₁.inter_subset_right G₂)) ((G₁.inter G₂).zero_mem 1)
    ((G₁.inter G₂).uniqueDiffWithinAt hC 1 ((G₁.inter G₂).zero_mem 1))

/-- **For `g` sc¹ on the whole `U`, `Dg(0) = scDeriv U g 0`** for every derivative family `Dg` of
`g` on a germ `G ⊆ U` (germ reading, phase 2): the bridge from the germ statements to the
project's whole-chart ones. -/
theorem IsSc1GermWith.deriv_zero_eq_scDeriv {U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U)
    (h0 : (0 : E 0) ∈ U) {G₁ : ScNbhdGerm E C} (hG : G₁.U 0 ⊆ U) {g : E 0 → F 0}
    {Dg : E 1 → E 0 →L[ℝ] F 0} (hDg : IsSc1GermWith G₁ g Dg) (hg : IsSc1 U g) :
    Dg 0 = scDeriv U g 0 :=
  hDg.deriv_zero_eq hU.isPartialQuadrant.isQuadrantLike
    (hg.isSc1GermWith_of_subset hU.relOpen h0 hG)

end DerivZero

/-! ### The kernel of the linearization lies in `T₀O`, germ reading -/

section Kernel

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0} {G₁ : ScNbhdGerm E C}

open StrongRetr

namespace IsFillingGerm

variable {hU : IsRelOpenInQuadrant E C U} {hR : IsStrongBundleRetraction U R} {h0 : (0 : E 0) ∈ U}
  {fb g : E 0 → F 0} (hfg : IsFillingGerm hU hR h0 fb g)

include hfg in
/-- **`ker Dg(0) ⊆ T₀O = Dr(0)E` for a filling germ** (germ reading, phase 2; the germ form of
`IsFillerOf.ker_deriv_le_range`, the text's `ker Tf̃(0) ⊕ {0} = ker Dg(0)` in the proof of Theorem
3.54): by condition (3) of the filling germ, `(1 − ρ(0))Dg(0)` is injective on `ker Dr(0)`, and
`(1 − ρ(0))Dg(0)Dr(0) = 0`; `Dg` is any derivative family of `g` on a germ `G₁ ⊆ U`. -/
theorem ker_deriv_le_range (hG : G₁.U 0 ⊆ U) {Dg : E 1 → E 0 →L[ℝ] F 0}
    (hg : IsSc1GermWith G₁ g Dg) (hg0 : g 0 = 0) (h0O : (0 : E 0) ∈ r R '' U)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) :
    LinearMap.ker (Dg 0 : E 0 →ₗ[ℝ] F 0) ≤ rangeS (scDeriv U (r R) 0) := by
  intro x hx
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx
  obtain ⟨Φ, hΦ⟩ := hfg.exists_kerEquiv hU hR h0 hg0 h0O hg
  have hk : scDeriv U (r R) 0 (x - scDeriv U (r R) 0 x) = 0 := by
    rw [map_sub, scDeriv_r_idem hU hR h0O, sub_self]
  have hΦk : ((Φ ⟨x - scDeriv U (r R) 0 x, hk⟩ :
      ↥(LinearMap.ker ((ρCLM hR h0 : F 0 →L[ℝ] F 0) : F 0 →ₗ[ℝ] F 0))) : F 0) = 0 := by
    rw [hΦ ⟨x - scDeriv U (r R) 0 x, hk⟩]
    change Dg 0 (x - scDeriv U (r R) 0 x) - ρCLM hR h0 (Dg 0 (x - scDeriv U (r R) 0 x)) = 0
    rw [map_sub, hx, zero_sub, map_neg, hfg.ρ_deriv_comp_r hU hR h0 hg0 h0O hfK hG hg x, sub_self]
  have hk0 : (⟨x - scDeriv U (r R) 0 x, hk⟩ :
      ↥(LinearMap.ker ((scDeriv U (r R) 0 : E 0 →L[ℝ] E 0) : E 0 →ₗ[ℝ] E 0))) = 0 :=
    Φ.map_eq_zero_iff.1 (Subtype.ext (by rw [hΦk]; rfl))
  have hxk : x - scDeriv U (r R) 0 x = 0 := congrArg Subtype.val hk0
  exact ⟨x, by rw [sub_eq_zero] at hxk; exact hxk.symm⟩

include hfg in
/-- **The kernel of `Tf̃(0) = Dg(0)|_{T₀O}`, as a subspace of `E₀`, is `ker Dg(0)`**, for a filling
germ (germ reading, phase 2; the germ form of `IsFillerOf.map_ker_fillerRestrict`). -/
theorem map_ker_fillerRestrict (hG : G₁.U 0 ⊆ U) {Dg : E 1 → E 0 →L[ℝ] F 0}
    (hg : IsSc1GermWith G₁ g Dg) (hg0 : g 0 = 0) (h0O : (0 : E 0) ∈ r R '' U)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ))
    (h1 : ∀ x, ρCLM hR h0 (Dg 0 (scDeriv U (r R) 0 x)) = Dg 0 (scDeriv U (r R) 0 x)) :
    (LinearMap.ker (fillerRestrictₗ (scDeriv U (r R) 0) (ρCLM hR h0) (Dg 0) h1)).map
        (rangeS (scDeriv U (r R) 0)).subtype =
      LinearMap.ker (Dg 0 : E 0 →ₗ[ℝ] F 0) := by
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, hyk, rfl⟩
    have hyk' : fillerRestrictₗ (scDeriv U (r R) 0) (ρCLM hR h0) (Dg 0) h1 ⟨y, hy⟩ = 0 := hyk
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    exact congrArg Subtype.val hyk'
  · intro hx
    refine ⟨⟨x, hfg.ker_deriv_le_range hG hg hg0 h0O hfK hx⟩, ?_, rfl⟩
    change fillerRestrictₗ (scDeriv U (r R) 0) (ρCLM hR h0) (Dg 0) h1 ⟨x, _⟩ = 0
    exact Subtype.ext (by rw [fillerRestrictₗ_apply]; exact hx)

end IsFillingGerm

end Kernel

/-! ### Definition 3.6.6 (preprint 3.53) in the chart, parametrised by `Dg(0)` -/

section Def353

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0} {G₁ : ScNbhdGerm E C}

open StrongRetr

/-- **Definition 3.6.6 (preprint 3.53) in the chart of Definition 3.1.11 (preprint 3.11), germ reading** (phase 2): for the
linearization `Dg₀ = Dg(0) : E₀ → F₀` of the filling germ `g` at the zero `0` (the value at `0` of a
derivative family of `g`, `IsSc1GermWith`), the sc-Fredholm germ is **in good position** if (1)
`Tf̃(0) = Dg₀|_{T₀O} : T₀O → K₀` is onto, and (2) `ker Tf̃(0) = ker Dg₀` is in good position to the
partial cone `C₀O = T₀O ∩ C` inside `T₀O = Dr(0)E`.  The project's `IsGoodPositionAt hU hR h0 g`
is the case `Dg₀ = scDeriv U g 0` (`isGoodPositionAt_iff_germ`). -/
structure IsGoodPositionAtGerm (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (Dg₀ : E 0 →L[ℝ] F 0) : Prop where
  surj : ∀ y ∈ rangeS (ρCLM hR h0), ∃ x ∈ rangeS (scDeriv U (r R) 0), Dg₀ x = y
  kernel : IsInGoodPositionIn E (rangeS (scDeriv U (r R) 0)) C
    (LinearMap.ker (Dg₀ : E 0 →ₗ[ℝ] F 0))

/-- **The project's Definition 3.6.6 (preprint 3.53) in the chart is the germ one at `Dg₀ = scDeriv U g 0`**
(germ reading, phase 2). -/
theorem isGoodPositionAt_iff_germ {hU : IsRelOpenInQuadrant E C U}
    {hR : IsStrongBundleRetraction U R} {h0 : (0 : E 0) ∈ U} {g : E 0 → F 0} :
    IsGoodPositionAt hU hR h0 g ↔ IsGoodPositionAtGerm hU hR h0 (scDeriv U g 0) :=
  ⟨fun h => ⟨h.surj, h.kernel⟩, fun h => ⟨h.surj, h.kernel⟩⟩

/-- **Old ⇒ germ** (germ reading, phase 2): if the germ is in good position in the project's
sense (`IsGoodPositionAt`, `g` sc¹ on `U`), it is in good position at `Dg(0)` for every derivative
family `Dg` of `g` on a germ `G ⊆ U` (`Dg(0) = scDeriv U g 0`). -/
theorem IsGoodPositionAt.isGoodPositionAtGerm {hU : IsRelOpenInQuadrant E C U}
    {hR : IsStrongBundleRetraction U R} {h0 : (0 : E 0) ∈ U} {g : E 0 → F 0}
    (hgp : IsGoodPositionAt hU hR h0 g) (hg : IsSc1 U g) (hG : G₁.U 0 ⊆ U)
    {Dg : E 1 → E 0 →L[ℝ] F 0} (hDg : IsSc1GermWith G₁ g Dg) :
    IsGoodPositionAtGerm hU hR h0 (Dg 0) := by
  rw [hDg.deriv_zero_eq_scDeriv hU h0 hG hg]
  exact isGoodPositionAt_iff_germ.1 hgp

/-- Condition (1) of Definition 3.6.6 (preprint 3.53) (germ reading, phase 2) is the surjectivity of
`fillerRestrict` for `Dg₀`. -/
theorem IsGoodPositionAtGerm.surjective_fillerRestrict {hU : IsRelOpenInQuadrant E C U}
    {hR : IsStrongBundleRetraction U R} {h0 : (0 : E 0) ∈ U} {Dg₀ : E 0 →L[ℝ] F 0}
    (hgp : IsGoodPositionAtGerm hU hR h0 Dg₀)
    (h1 : ∀ x, ρCLM hR h0 (Dg₀ (scDeriv U (r R) 0 x)) = Dg₀ (scDeriv U (r R) 0 x)) :
    Surjective (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) Dg₀ h1) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, hxy⟩ := hgp.surj y hy
  exact ⟨⟨x, hx⟩, Subtype.ext (by rw [fillerRestrict_apply]; exact hxy)⟩

/-- `IsGoodPositionAtGerm` depends only on the operator (a congruence for rewriting `Dg(0)`). -/
theorem IsGoodPositionAtGerm.congr {hU : IsRelOpenInQuadrant E C U}
    {hR : IsStrongBundleRetraction U R} {h0 : (0 : E 0) ∈ U} {D D' : E 0 →L[ℝ] F 0}
    (h : IsGoodPositionAtGerm hU hR h0 D) (hDD' : D = D') : IsGoodPositionAtGerm hU hR h0 D' :=
  hDD' ▸ h

/-- **Definition 3.6.6 (preprint 3.53) does not depend on the derivative family** (germ reading, phase 2): if the
germ is in good position at `Dg(0)` for one derivative family `Dg` of `g` on a germ `G`, it is at
`Dg'(0)` for every derivative family `Dg'` of `g` on every germ `G'` (`Dg'(0) = Dg(0)`,
`IsSc1GermWith.deriv_zero_eq`). -/
theorem IsGoodPositionAtGerm.of_isSc1GermWith {hU : IsRelOpenInQuadrant E C U}
    {hR : IsStrongBundleRetraction U R} {h0 : (0 : E 0) ∈ U} (hC : IsQuadrantLike E C)
    {g : E 0 → F 0} {G G' : ScNbhdGerm E C} {Dg Dg' : E 1 → E 0 →L[ℝ] F 0}
    (hgp : IsGoodPositionAtGerm hU hR h0 (Dg 0)) (hDg : IsSc1GermWith G g Dg)
    (hDg' : IsSc1GermWith G' g Dg') : IsGoodPositionAtGerm hU hR h0 (Dg' 0) :=
  hgp.congr (hDg.deriv_zero_eq hC hDg')

variable {n : ℕ} {W : ScBanach}

/-- **Theorem 3.6.8 (preprint 3.54), the linear part, germ reading** (phase 2): let `g` be a filling germ of the
principal part `f̂` of a section at a zero (`f̂(0) = 0`), `Dg` a derivative family of `g` on a germ
`G₁ ⊆ U`, the germ in good position at `Dg(0)` (Definition 3.6.6 (preprint 3.53)), and `(1 − Dr(0))E ⊆ E₀`
(Proposition 2.5.3 (preprint 2.35) for the tame retraction `r`).  Then `Dg(0) : E → F` is surjective and `ker Dg(0)`
is in good position to `C` in `E`. -/
theorem theorem_3_6_8_linear (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    {fb g : E 0 → F 0} (hfill : IsFillingGerm hU hR h0 fb g) (hfb0 : fb 0 = 0)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) (hG : G₁.U 0 ⊆ U)
    {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G₁ g Dg)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hC : C = T 0 ⁻¹' quadrant n W 0)
    (hK : LinearMap.range (ContinuousLinearMap.id ℝ (E 0) - scDeriv U (r R) 0 : E 0 →ₗ[ℝ] E 0) ≤
      minimalSubspaceWith T 0)
    (hgp : IsGoodPositionAtGerm hU hR h0 (Dg 0)) :
    Surjective (Dg 0) ∧ IsInGoodPosition E C (LinearMap.ker (Dg 0 : E 0 →ₗ[ℝ] F 0)) := by
  have hg0 : g 0 = 0 := by rw [← hfill.eq_on.self_of_nhds h0O, hfb0]
  obtain ⟨h1, hsurj, -, -⟩ := hfill.proposition_3_1_5 hU hR h0 hg0 h0O hfK hG hg
  refine ⟨hsurj.1 (hgp.surjective_fillerRestrict h1), ?_⟩
  exact hgp.kernel.isInGoodPosition T hC (scDeriv U (r R) 0) (scDeriv_r_idem hU hR h0O) hK

/-- **Theorem 3.6.8 (preprint 3.54), the linear part, for a tame retraction, germ reading** (phase 2):
`theorem_3_6_8_linear` with `(1 − Dr(0))E ⊆ E₀` from Proposition 2.5.3 (preprint 2.35) for a tame
sc-retraction `Rr` with `Rr.U = U` and `Rr = r`. -/
theorem theorem_3_6_8_linear_of_isTameWith (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    {fb g : E 0 → F 0} (hfill : IsFillingGerm hU hR h0 fb g) (hfb0 : fb 0 = 0)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) (hG : G₁.U 0 ⊆ U)
    {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G₁ g Dg)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hC : C = T 0 ⁻¹' quadrant n W 0)
    (Rr : ScRetraction E C) (hRrU : Rr.U = U) (hRr : ⇑Rr = r R) (hRt : Rr.IsTameWith T)
    (hgp : IsGoodPositionAtGerm hU hR h0 (Dg 0)) :
    Surjective (Dg 0) ∧ IsInGoodPosition E C (LinearMap.ker (Dg 0 : E 0 →ₗ[ℝ] F 0)) := by
  refine theorem_3_6_8_linear hU hR h0 h0O hfill hfb0 hfK hG hg T hC ?_ hgp
  have h01 : (0 : E 1) ∈ E.lvlSet Rr.retract 1 := by
    rw [ScBanach.mem_lvlSet, map_zero, ScRetraction.retract, hRrU, hRr]
    exact h0O
  have hs : (0 : E 1) ∈ E.smoothLvl 1 := by
    change E.toBase 1 0 ∈ (E.smooth : Set (E 0))
    rw [map_zero]; exact E.smooth.zero_mem
  have h235 := (proposition_2_5_3 hC hRt h01 hs).1
  rw [map_zero] at h235
  have heq : scDeriv Rr.U Rr 0 = scDeriv U (r R) 0 := by rw [hRrU, hRr]
  rwa [heq] at h235

end Def353

/-! ### Transfer to the conjugated germ (`Ψ_*(g) = h + t`), germ reading -/

section Transfer

variable {E' F' : ScBanach} {C U : Set (E 0)} {C' U' : Set (E' 0)}
  {Ψ : E 0 × F 0 → E' 0 × F' 0} {Ψ' : E' 0 × F' 0 → E 0 × F 0} {G₁ : ScNbhdGerm E C}

/-- **The isomorphisms `Γ(0) : F → F'` and `Dψ(0) : E → E'`** of a strong bundle isomorphism with
`ψ(0) = 0` (proof of Theorem 3.6.8 (preprint 3.54)): `Γ(0)` is the fibre map `fiberCLM` over `0`, the inverse of
`S = Dψ(0)` is `Dψ'(0)`, and `x ∈ C ↔ Sx ∈ C'` (`scDeriv_mem_iff_of_inverse`). -/
theorem IsStrongBundleIso.exists_fiber_base_equiv (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsRelOpenInQuadrant E' C' U') (hΨ : IsStrongBundleIso U U' Ψ Ψ') (h0 : (0 : E 0) ∈ U)
    (hψ0 : IsStrongBundleMap.base Ψ 0 = 0) :
    ∃ (Γ : F 0 ≃L[ℝ] F' 0) (S : E 0 ≃L[ℝ] E' 0),
      (Γ : F 0 →L[ℝ] F' 0) = hΨ.toFun.fiberCLM h0 ∧
      (S.symm : E' 0 →L[ℝ] E 0) = scDeriv U' (IsStrongBundleMap.base Ψ') 0 ∧
      (∀ x, x ∈ C ↔ S x ∈ C') := by
  have h01 : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have h0U' : (0 : E' 0) ∈ U' := hψ0 ▸ hΨ.toFun.base_mem h0
  have h01' : (0 : E' 1) ∈ E'.lvlSet U' 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0U'
  set ψ := IsStrongBundleMap.base Ψ with hψdef
  set ψ' := IsStrongBundleMap.base Ψ' with hψ'def
  have hψψ' : ∀ u ∈ U, ψ' (ψ u) = u := fun u hu => hΨ.base_base hu
  have hψ'ψ : ∀ u' ∈ U', ψ (ψ' u') = u' := fun u' hu' => hΨ.base_base' hu'
  have hψ'0 : ψ' 0 = 0 := hΨ.base_zero' h0 hψ0
  have hψsm : IsScSmooth U ψ := hΨ.toFun.base_isScSmooth hU
  have hψ'sm : IsScSmooth U' ψ' := hΨ.invFun.base_isScSmooth hU'
  have hψU' : MapsTo ψ U U' := fun u hu => hΨ.toFun.base_mem hu
  have hψ'U : MapsTo ψ' U' U := fun u hu => hΨ.invFun.base_mem hu
  set Γ := hΨ.toFun.fiberCLM h0 with hΓ
  set Γ' := hΨ.invFun.fiberCLM h0U' with hΓ'
  have hΓΓ' : ∀ y, Γ (Γ' y) = y := fun y => by
    simp only [hΓ, hΓ']
    have h1 : Ψ' (0, y) = (ψ' 0, (Ψ' (0, y)).2) := hΨ.invFun.apply_eq h0U' y
    rw [hψ'0] at h1
    have h2 := congrArg Prod.snd (hΨ.right_inv (0, y) ⟨h0U', mem_univ _⟩)
    rw [h1] at h2
    exact h2
  have hΓ'Γ : ∀ y, Γ' (Γ y) = y := fun y => by
    simp only [hΓ, hΓ']
    have h1 : Ψ (0, y) = (ψ 0, (Ψ (0, y)).2) := hΨ.toFun.apply_eq h0 y
    rw [hψ0] at h1
    have h2 := congrArg Prod.snd (hΨ.left_inv (0, y) ⟨h0, mem_univ _⟩)
    rw [h1] at h2
    exact h2
  have hlevψ : levelMap ψ 1 (0 : E 1) = 0 :=
    levelMap_eq_of_toBase_eq (by rw [map_zero, map_zero, hψ0])
  have hlevψ' : levelMap ψ' 1 (0 : E' 1) = 0 :=
    levelMap_eq_of_toBase_eq (by rw [map_zero, map_zero, hψ'0])
  have hψψ'D : ∀ x, scDeriv U' ψ' 0 (scDeriv U ψ 0 x) = x := fun x => by
    have := scDeriv_comp_eq_self hU hU' hψsm.isSc1 hψ'sm.isSc1 hψU' hψψ' h01 x
    rwa [hlevψ] at this
  have hψ'ψD : ∀ x, scDeriv U ψ 0 (scDeriv U' ψ' 0 x) = x := fun x => by
    have := scDeriv_comp_eq_self hU' hU hψ'sm.isSc1 hψsm.isSc1 hψ'U hψ'ψ h01' x
    rwa [hlevψ'] at this
  exact ⟨ContinuousLinearEquiv.equivOfInverse Γ Γ' hΓ'Γ hΓΓ',
    ContinuousLinearEquiv.equivOfInverse (scDeriv U ψ 0) (scDeriv U' ψ' 0) hψψ'D hψ'ψD,
    rfl, rfl, fun x => scDeriv_mem_iff_of_inverse hU hU' hψsm hψ'sm hψU' hψ'U hψψ' h0 hψ0 x⟩

/-- **The linearization of the push-forward of a germ** (germ reading, phase 2; the germ form of
`IsStrongBundleIso.pushforward_linearization_wholeChart`): for `g` an sc-smooth germ on `G₁ ⊆ U` with a
derivative family `Dg` and `g(0) = 0`, `Ψ_*(g)` is an sc-smooth germ on `ψ'⁻¹(G₁)` (`pullGerm`)
with the derivative family `pushforwardDeriv`, `Ψ_*(g)(0) = 0`, and
`D(Ψ_*g)(0) = Γ(0) ∘ Dg(0) ∘ Dψ(0)⁻¹` with isomorphisms `Γ(0) : F → F'` and `Dψ(0) : E → E'`, the
latter carrying `C` onto `C'`. -/
theorem IsStrongBundleIso.pushforward_linearization (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsRelOpenInQuadrant E' C' U') (hΨ : IsStrongBundleIso U U' Ψ Ψ') (h0 : (0 : E 0) ∈ U)
    (hψ0 : IsStrongBundleMap.base Ψ 0 = 0) (hG : G₁.U 0 ⊆ U) {g : E 0 → F 0}
    (hg : IsScSmoothGerm G₁ g) {Dg : E 1 → E 0 →L[ℝ] F 0} (hDg : IsSc1GermWith G₁ g Dg)
    (hg0 : g 0 = 0) :
    IsScSmoothGerm (hΨ.pullGerm hU hU' h0 hψ0 G₁) (pushforward Ψ Ψ' g) ∧
      IsSc1GermWith (hΨ.pullGerm hU hU' h0 hψ0 G₁) (pushforward Ψ Ψ' g)
        (pushforwardDeriv U U' Ψ (IsStrongBundleMap.base Ψ') g Dg) ∧
      pushforward Ψ Ψ' g 0 = 0 ∧
      ∃ (Γ : F 0 ≃L[ℝ] F' 0) (S : E 0 ≃L[ℝ] E' 0), (∀ x, x ∈ C ↔ S x ∈ C') ∧
        pushforwardDeriv U U' Ψ (IsStrongBundleMap.base Ψ') g Dg 0 =
          (Γ : F 0 →L[ℝ] F' 0).comp ((Dg 0).comp (S.symm : E' 0 →L[ℝ] E 0)) := by
  obtain ⟨Γ, S, hΓ, hS, hSC⟩ := hΨ.exists_fiber_base_equiv hU hU' h0 hψ0
  refine ⟨hΨ.pushforward_isScSmoothGerm h0 hψ0 hU hU' hG hg,
    hΨ.pushforward_isSc1GermWith h0 hψ0 hU hU' hG hDg, ?_, Γ, S, hSC, ?_⟩
  · change (Ψ (IsStrongBundleMap.base Ψ' 0, g (IsStrongBundleMap.base Ψ' 0))).2 = 0
    rw [hΨ.base_zero' h0 hψ0, hg0]
    exact hΨ.toFun.snd_zero h0
  · rw [hΨ.pushforwardDeriv_zero h0 hψ0 hU hg0 Dg, hΓ, hS]

/-- **`D(Ψ_*g)(0)` is surjective if `Dg(0)` is** (germ reading, phase 2; the text's "`D(h + t)(0)`
is surjective", the germ form of `IsStrongBundleIso.pushforward_surjective_wholeChart`). -/
theorem IsStrongBundleIso.pushforward_surjective (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsRelOpenInQuadrant E' C' U') (hΨ : IsStrongBundleIso U U' Ψ Ψ') (h0 : (0 : E 0) ∈ U)
    (hψ0 : IsStrongBundleMap.base Ψ 0 = 0) {g : E 0 → F 0} (hg0 : g 0 = 0)
    {Dg : E 1 → E 0 →L[ℝ] F 0} (hsurj : Surjective (Dg 0)) :
    Surjective (pushforwardDeriv U U' Ψ (IsStrongBundleMap.base Ψ') g Dg 0) := by
  obtain ⟨Γ, S, hΓ, hS, -⟩ := hΨ.exists_fiber_base_equiv hU hU' h0 hψ0
  rw [hΨ.pushforwardDeriv_zero h0 hψ0 hU hg0 Dg, ← hΓ, ← hS]
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe]
  exact Γ.surjective.comp (hsurj.comp S.symm.surjective)

/-- **`N' = ker D(h + t)(0)` is in good position to `C'`** (germ reading, phase 2; the germ form
of `IsStrongBundleIso.pushforward_ker_isInGoodPosition_wholeChart`): the kernel of `D(Ψ_*g)(0)` is
`Dψ(0)(ker Dg(0))`, and good position is carried by `Dψ(0)` (Lemma 3.5.9 (preprint 3.45)). -/
theorem IsStrongBundleIso.pushforward_ker_isInGoodPosition (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsRelOpenInQuadrant E' C' U') (hΨ : IsStrongBundleIso U U' Ψ Ψ') (h0 : (0 : E 0) ∈ U)
    (hψ0 : IsStrongBundleMap.base Ψ 0 = 0) {g : E 0 → F 0} (hg0 : g 0 = 0)
    {Dg : E 1 → E 0 →L[ℝ] F 0} [FiniteDimensional ℝ (LinearMap.ker (Dg 0 : E 0 →ₗ[ℝ] F 0))]
    (hker : IsInGoodPosition E C (LinearMap.ker (Dg 0 : E 0 →ₗ[ℝ] F 0))) :
    IsInGoodPosition E' C' (LinearMap.ker
      (pushforwardDeriv U U' Ψ (IsStrongBundleMap.base Ψ') g Dg 0 : E' 0 →ₗ[ℝ] F' 0)) := by
  obtain ⟨Γ, S, hΓ, hS, hSC⟩ := hΨ.exists_fiber_base_equiv hU hU' h0 hψ0
  have hD : pushforwardDeriv U U' Ψ (IsStrongBundleMap.base Ψ') g Dg 0 =
      (Γ : F 0 →L[ℝ] F' 0).comp ((Dg 0).comp (S.symm : E' 0 →L[ℝ] E 0)) := by
    rw [hΨ.pushforwardDeriv_zero h0 hψ0 hU hg0 Dg, hΓ, hS]
  have hmap := hker.map S hSC
  convert hmap using 1
  ext y
  rw [LinearMap.mem_ker, Submodule.mem_map, ContinuousLinearMap.coe_coe, hD]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.map_eq_zero_iff, LinearMap.mem_ker]
  constructor
  · intro h
    exact ⟨S.symm y, h, S.apply_symm_apply y⟩
  · rintro ⟨x, hx, rfl⟩
    have : S.symm ((S : E 0 →ₗ[ℝ] E' 0) x) = x := S.symm_apply_apply x
    rw [this]
    exact hx

/-- **`D(Ψ_*g)(0)` is Fredholm if `Dg(0)` is** (germ reading, phase 2): it is
`Γ(0) ∘ Dg(0) ∘ Dψ(0)⁻¹`. -/
theorem IsStrongBundleIso.pushforward_isFredholm_germ (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsRelOpenInQuadrant E' C' U') (hΨ : IsStrongBundleIso U U' Ψ Ψ') (h0 : (0 : E 0) ∈ U)
    (hψ0 : IsStrongBundleMap.base Ψ 0 = 0) {g : E 0 → F 0} (hg0 : g 0 = 0)
    {Dg : E 1 → E 0 →L[ℝ] F 0} (hDgF : IsFredholm (Dg 0)) :
    IsFredholm (pushforwardDeriv U U' Ψ (IsStrongBundleMap.base Ψ') g Dg 0) := by
  obtain ⟨Γ, S, hΓ, hS, -⟩ := hΨ.exists_fiber_base_equiv hU hU' h0 hψ0
  rw [hΨ.pushforwardDeriv_zero h0 hψ0 hU hg0 Dg, ← hΓ, ← hS]
  exact (isFredholm_equiv_comp_equiv hDgF S.symm Γ).1

end Transfer

/-! ### Theorem 3.6.8 (preprint 3.54): the hypotheses of Theorem 3.5.11 (preprint 3.47) for the push-forward, germ reading -/

section Thm354

variable {E' F' : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0} {C' U' : Set (E' 0)}
  {Ψ : E 0 × F 0 → E' 0 × F' 0} {Ψ' : E' 0 × F' 0 → E 0 × F 0} {G₁ : ScNbhdGerm E C}

open StrongRetr

variable {n : ℕ} {W : ScBanach}

/-- **Theorem 3.6.8 (preprint 3.54), the step before Theorem 3.5.11 (preprint 3.47), germ reading** (phase 2; the germ form of
`theorem_3_6_8_pushforward_wholeChart`): let `g` be a filling germ of `f̂` at the zero `0`, sc-smooth on the
germ `G₁ ⊆ U` with a derivative family `Dg`, the germ in good position at `Dg(0)`
(`IsGoodPositionAtGerm`), `(1 − Dr(0))E ⊆ E₀` (Proposition 2.5.3 (preprint 2.35)), and `Dg(0)` Fredholm
(Proposition 3.6.5 (preprint 3.52), here a hypothesis: in the germ reading it is Proposition 3.6.5 (preprint 3.52) for germs).  Then
for **any** strong bundle isomorphism `Ψ : U ◁ F → U' ◁ F'` with `ψ(0) = 0` the push-forward
`Ψ_*(g) = h + t` is an sc-smooth germ on `ψ'⁻¹(G₁)` with the derivative family
`pushforwardDeriv`, vanishes at `0`, and `D(Ψ_*g)(0) : E' → F'` is a surjective Fredholm operator
whose kernel `N'` is in good position to `C'` in `E'` — the hypotheses of Theorem 3.5.11 (preprint 3.47) for
`h + t`. -/
theorem theorem_3_6_8_pushforward (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    {fb g : E 0 → F 0} (hfill : IsFillingGerm hU hR h0 fb g) (hfb0 : fb 0 = 0)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) (hG : G₁.U 0 ⊆ U)
    (hg : IsScSmoothGerm G₁ g) {Dg : E 1 → E 0 →L[ℝ] F 0} (hDg : IsSc1GermWith G₁ g Dg)
    (hDgF : IsFredholm (Dg 0))
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hC : C = T 0 ⁻¹' quadrant n W 0)
    (hK : LinearMap.range (ContinuousLinearMap.id ℝ (E 0) - scDeriv U (r R) 0 : E 0 →ₗ[ℝ] E 0) ≤
      minimalSubspaceWith T 0)
    (hgp : IsGoodPositionAtGerm hU hR h0 (Dg 0)) (hU' : IsRelOpenInQuadrant E' C' U')
    (hΨ : IsStrongBundleIso U U' Ψ Ψ') (hψ0 : IsStrongBundleMap.base Ψ 0 = 0) :
    IsScSmoothGerm (hΨ.pullGerm hU hU' h0 hψ0 G₁) (pushforward Ψ Ψ' g) ∧
      IsSc1GermWith (hΨ.pullGerm hU hU' h0 hψ0 G₁) (pushforward Ψ Ψ' g)
        (pushforwardDeriv U U' Ψ (IsStrongBundleMap.base Ψ') g Dg) ∧
      pushforward Ψ Ψ' g 0 = 0 ∧
      Surjective (pushforwardDeriv U U' Ψ (IsStrongBundleMap.base Ψ') g Dg 0) ∧
      IsFredholm (pushforwardDeriv U U' Ψ (IsStrongBundleMap.base Ψ') g Dg 0) ∧
      IsInGoodPosition E' C' (LinearMap.ker
        (pushforwardDeriv U U' Ψ (IsStrongBundleMap.base Ψ') g Dg 0 : E' 0 →ₗ[ℝ] F' 0)) := by
  have hg0 : g 0 = 0 := by rw [← hfill.eq_on.self_of_nhds h0O, hfb0]
  obtain ⟨hsurj, hker⟩ := theorem_3_6_8_linear hU hR h0 h0O hfill hfb0 hfK hG hDg T hC hK hgp
  have : FiniteDimensional ℝ (LinearMap.ker (Dg 0 : E 0 →ₗ[ℝ] F 0)) := hDgF.finite_ker
  obtain ⟨hsm, hsc1, hz, -⟩ := hΨ.pushforward_linearization hU hU' h0 hψ0 hG hg hDg hg0
  exact ⟨hsm, hsc1, hz, hΨ.pushforward_surjective hU hU' h0 hψ0 hg0 hsurj,
    hΨ.pushforward_isFredholm_germ hU hU' h0 hψ0 hg0 hDgF,
    hΨ.pushforward_ker_isInGoodPosition hU hU' h0 hψ0 hg0 hker⟩

end Thm354

/-! ### Definition 3.6.6 (preprint 3.53) for sections of strong bundles, germ reading -/

section Bundle

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

variable (B) in
/-- **Definition 3.6.6 (preprint 3.53) for a section, the text's germ reading** (phase 2): `(f, x₀)` is an
**sc-Fredholm germ in good position**: the data of Definition 3.1.11 (preprint 3.11) in the germ reading
(`IsScFredholmGerm`: a strong bundle chart centred at `x₀`, a filling germ `g` of `f̂`, an
sc⁺-germ `s` with `s(0) = g(0)` and `g − s` conjugated to a basic germ), and a derivative family
`Dg` of `g` on a germ `G ⊆ U` such that the germ is in good position in the chart at `Dg(0)`
(`IsGoodPositionAtGerm`: `Tf̃(0) : T₀O → K₀` onto, `ker Tf̃(0)` in good position to `C₀O` in
`T₀O`).  `Dg(0)` does not depend on `G` and `Dg`
(`IsGoodPositionGerm.forall_isGoodPositionAtGerm`).
The project's `IsGoodPositionGermWholeChart` is the special case with `g`, `s` sc-smooth on the whole `U`
(`isGoodPositionGerm_iff_germG_wholeChart`). -/
def StrongBundle.IsGoodPositionGerm (f : X → Y) (x₀ : X) : Prop :=
  x₀ ∈ PX.smoothSet ∧
  ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1),
    IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g ∧
    IsScPlusGerm c.φ.model.C c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
    IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u)) ∧
    ∃ (G : ScNbhdGerm c.φ.model.E c.φ.model.C) (Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0),
      G.U 0 ⊆ c.U ∧ IsSc1GermWith G g Dg ∧
      IsGoodPositionAtGerm c.relOpen c.isRetraction h0 (Dg 0)

/-- **A germ in good position is an sc-Fredholm germ** (germ reading, phase 2). -/
theorem StrongBundle.IsGoodPositionGerm.isScFredholmGerm {x₀ : X}
    (h : B.IsGoodPositionGerm f x₀) : B.IsScFredholmGerm f x₀ := by
  obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, -⟩ := h
  exact ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩

/-- **Project ⇒ germ reading** for Definition 3.6.6 (preprint 3.53) (phase 2): a germ in good position in the
project's sense (`IsGoodPositionGermWholeChart`) is one in the germ reading, with the germ `ofSet U` and
`Dg = scDeriv U g`. -/
theorem StrongBundle.IsGoodPositionGermWholeChart.isGoodPositionGerm {x₀ : X}
    (h : B.IsGoodPositionGermWholeChart f x₀) : B.IsGoodPositionGerm f x₀ := by
  obtain ⟨hx₀, c, hc, hx, hφ0, h0, g, s, hfill, hs, hs0, hconj, hgp⟩ := h
  exact ⟨hx₀, c, hc, hx, hφ0, h0, g, s, hfill.isFillingGerm c.relOpen c.isRetraction h0,
    ⟨ScNbhdGerm.ofSet c.relOpen.relOpen h0, fun _ hu => hu,
      hs.isScSmoothGerm c.isQuadrantLike c.relOpen.relOpen h0⟩, hs0, hconj,
    ScNbhdGerm.ofSet c.relOpen.relOpen h0, scDeriv c.U g, fun _ hu => hu,
    hfill.isScSmooth.isSc1.isSc1GermWith_ofSet c.relOpen.relOpen h0,
    isGoodPositionAt_iff_germ.1 hgp⟩

/-- **The good position holds at `Dg(0)` for every derivative family** (germ reading, phase 2):
the `∀`-form of `IsGoodPositionGerm`.  If `(f, x₀)` is in good position, then in the data of
Definition 3.1.11 (preprint 3.11) of the germ reading the germ is in good position at `Dg(0)` for **every**
derivative family `Dg` of `g` on **every** germ `G` (`IsGoodPositionAtGerm.of_isSc1GermWith`). -/
theorem StrongBundle.IsGoodPositionGerm.forall_isGoodPositionAtGerm {x₀ : X}
    (h : B.IsGoodPositionGerm f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1),
      IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g ∧
      IsScPlusGerm c.φ.model.C c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
      IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u)) ∧
      ∀ (G : ScNbhdGerm c.φ.model.E c.φ.model.C)
        (Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0), IsSc1GermWith G g Dg →
        IsGoodPositionAtGerm c.relOpen c.isRetraction h0 (Dg 0) := by
  obtain ⟨-, c, hc, hxV, hφ0, h0, g, s, hfill, hs, hs0, hconj, G₀, Dg₀, -, hDg₀, hgp₀⟩ := h
  exact ⟨c, hc, hxV, hφ0, h0, g, s, hfill, hs, hs0, hconj, fun _ _ hDg =>
    hgp₀.of_isSc1GermWith c.isQuadrantLike hDg₀ hDg⟩

/-- **The reduction for Definition 3.6.6 (preprint 3.53)** (germ reading, phase 2): `(f, x₀)` is in good position in
the project's sense iff it is in the germ reading **with `g` and `s` sc-smooth on the whole `U`**
(the analogue of `isScFredholmGerm_iff_germG_wholeChart`). -/
theorem StrongBundle.isGoodPositionGerm_iff_germG_wholeChart {x₀ : X} :
    B.IsGoodPositionGermWholeChart f x₀ ↔
    x₀ ∈ PX.smoothSet ∧
    ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1),
      (IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g ∧ IsScSmooth c.U g) ∧
      (IsScPlusGerm c.φ.model.C c.U s ∧ IsScSmooth (F := c.F.shift) c.U s) ∧
      c.F.toBase 1 (s 0) = g 0 ∧
      IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u)) ∧
      ∃ (G : ScNbhdGerm c.φ.model.E c.φ.model.C)
        (Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0),
        G.U 0 ⊆ c.U ∧ IsSc1GermWith G g Dg ∧
        IsGoodPositionAtGerm c.relOpen c.isRetraction h0 (Dg 0) := by
  constructor
  · intro h
    obtain ⟨hx₀, c, hc, hx, hφ0, h0, g, s, hfill, hs, hs0, hconj, hgp⟩ := h
    exact ⟨hx₀, c, hc, hx, hφ0, h0, g, s,
      ⟨hfill.isFillingGerm c.relOpen c.isRetraction h0, hfill.isScSmooth⟩,
      ⟨⟨ScNbhdGerm.ofSet c.relOpen.relOpen h0, fun _ hu => hu,
        hs.isScSmoothGerm c.isQuadrantLike c.relOpen.relOpen h0⟩, hs⟩, hs0, hconj,
      ScNbhdGerm.ofSet c.relOpen.relOpen h0, scDeriv c.U g, fun _ hu => hu,
      hfill.isScSmooth.isSc1.isSc1GermWith_ofSet c.relOpen.relOpen h0,
      isGoodPositionAt_iff_germ.1 hgp⟩
  · rintro ⟨hx₀, c, hc, hx, hφ0, h0, g, s, ⟨hfill, hg⟩, ⟨-, hs⟩, hs0, hconj, G, Dg, hG, hDg,
      hgp⟩
    refine ⟨hx₀, c, hc, hx, hφ0, h0, g, s,
      hfill.isFilledVersion c.relOpen c.isRetraction h0 hg, hs, hs0, hconj, ?_⟩
    rw [isGoodPositionAt_iff_germ, ← hDg.deriv_zero_eq_scDeriv c.relOpen h0 hG hg.isSc1]
    exact hgp

/-- **Theorem 3.6.8 (preprint 3.54), the step before Theorem 3.5.11 (preprint 3.47), for a section, germ reading** (phase 2; the germ
form of `theorem_3_6_8_pushforward_section_wholeChart`): let `f` be a section with `f(x₀) = 0` and `(f, x₀)` in
good position in the germ reading.  Then in the chart of Definition 3.6.6 (preprint 3.53) (centred at `x₀`, with a
filling germ `g` of `f̂`, sc-smooth on a germ `G ⊆ U` with a derivative family `Dg`), for every
presentation `T` of `C` with `(1 − Dr(0))E ⊆ E₀`: `Dg(0)` is surjective and `ker Dg(0)` is in good
position to `C` in `E`; and for every strong bundle isomorphism `Ψ : U ◁ F → U' ◁ F'` with
`ψ(0) = 0` the push-forward `Ψ_*(g)` is an sc-smooth germ on `ψ'⁻¹(G)` with the derivative family
`pushforwardDeriv`, vanishes at `0`, `D(Ψ_*g)(0)` is surjective, and — **if `Dg(0)` is Fredholm**
(Proposition 3.6.5 (preprint 3.52) for germs, not proved in this file) — `D(Ψ_*g)(0)` is Fredholm with kernel in
good position to `C'`. -/
theorem theorem_3_6_8_pushforward_section (hf : IsSection P f) {x₀ : X}
    (hg : B.IsGoodPositionGerm f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0)
      (_ : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
      (G : ScNbhdGerm c.φ.model.E c.φ.model.C) (Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0)
      (_ : G.U 0 ⊆ c.U) (_ : IsScSmoothGerm G g) (_ : IsSc1GermWith G g Dg),
      ∀ {n : ℕ} {W : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)),
        c.φ.model.C = T 0 ⁻¹' quadrant n W 0 →
        LinearMap.range (ContinuousLinearMap.id ℝ (c.φ.model.E 0) - scDeriv c.U (r c.R) 0 :
          c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) ≤ minimalSubspaceWith T 0 →
        (Surjective (Dg 0) ∧
          IsInGoodPosition c.φ.model.E c.φ.model.C
            (LinearMap.ker (Dg 0 : c.φ.model.E 0 →ₗ[ℝ] c.F 0))) ∧
        ∀ {E' F' : ScBanach} {C' U' : Set (E' 0)}
          {Ψ : c.φ.model.E 0 × c.F 0 → E' 0 × F' 0} {Ψ' : E' 0 × F' 0 → c.φ.model.E 0 × c.F 0}
          (hU' : IsRelOpenInQuadrant E' C' U') (hΨ : IsStrongBundleIso c.U U' Ψ Ψ')
          (hψ0 : IsStrongBundleMap.base Ψ 0 = 0),
          IsScSmoothGerm (hΨ.pullGerm c.relOpen hU' h0 hψ0 G) (pushforward Ψ Ψ' g) ∧
          IsSc1GermWith (hΨ.pullGerm c.relOpen hU' h0 hψ0 G) (pushforward Ψ Ψ' g)
            (pushforwardDeriv c.U U' Ψ (IsStrongBundleMap.base Ψ') g Dg) ∧
          pushforward Ψ Ψ' g 0 = 0 ∧
          Surjective (pushforwardDeriv c.U U' Ψ (IsStrongBundleMap.base Ψ') g Dg 0) ∧
          (IsFredholm (Dg 0) →
            IsFredholm (pushforwardDeriv c.U U' Ψ (IsStrongBundleMap.base Ψ') g Dg 0) ∧
            IsInGoodPosition E' C' (LinearMap.ker
              (pushforwardDeriv c.U U' Ψ (IsStrongBundleMap.base Ψ') g Dg 0 :
                E' 0 →ₗ[ℝ] F' 0))) := by
  obtain ⟨-, c, hc, hxV, hφ0, h0U, g, s, hfill, -, -, -, G₀, Dg₀, hG₀, hDg₀, hgp₀⟩ := hg
  -- the germ of the filling, on which `g` is sc-smooth
  obtain ⟨G, hGU, hgsm, -⟩ := hfill.germ
  set Dg := scDerivGerm G g with hDgdef
  have hDg : IsSc1GermWith G g Dg := (hgsm 1).isSc1.isSc1GermWith_scDerivGerm
  have hgp : IsGoodPositionAtGerm c.relOpen c.isRetraction h0U (Dg 0) :=
    hgp₀.of_isSc1GermWith c.isQuadrantLike hDg₀ hDg
  have h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := by
    rw [c.r_image, ← hφ0]; exact c.φ.mapsTo_model x₀ hxV
  have hfb0 : c.principal f 0 = 0 := by
    have := (c.isZeroAt_iff hf hxV).1 hx₀
    rwa [hφ0] at this
  have hfK : ∀ x ∈ r c.R '' c.U, (x, c.principal f x) ∈ c.R '' (c.U ×ˢ univ) := by
    intro x hx
    rw [c.r_image] at hx
    rw [← c.apply_section hf hx]
    change c (f (c.φ.symm x)) ∈ c.K
    rw [← c.image_source]
    exact ⟨_, c.mem_source_of_proj (by rw [hf]; exact c.φ.symm_mapsTo hx), rfl⟩
  have hg0 : g 0 = 0 := by rw [← hfill.eq_on.self_of_nhds h0O, hfb0]
  refine ⟨c, hc, hxV, hφ0, h0U, g, hfill, G, Dg, hGU, hgsm, hDg, fun T hC hK => ⟨?_, ?_⟩⟩
  · exact theorem_3_6_8_linear c.relOpen c.isRetraction h0U h0O hfill hfb0 hfK hGU hDg T hC hK
      hgp
  · intro E' F' C' U' Ψ Ψ' hU' hΨ hψ0
    obtain ⟨hsurj, hker⟩ := theorem_3_6_8_linear c.relOpen c.isRetraction h0U h0O hfill hfb0
      hfK hGU hDg T hC hK hgp
    obtain ⟨hsm, hsc1, hz, -⟩ :=
      hΨ.pushforward_linearization c.relOpen hU' h0U hψ0 hGU hgsm hDg hg0
    refine ⟨hsm, hsc1, hz, hΨ.pushforward_surjective c.relOpen hU' h0U hψ0 hg0 hsurj,
      fun hDgF => ?_⟩
    have : FiniteDimensional ℝ (LinearMap.ker (Dg 0 : c.φ.model.E 0 →ₗ[ℝ] c.F 0)) :=
      hDgF.finite_ker
    exact ⟨hΨ.pushforward_isFredholm_germ c.relOpen hU' h0U hψ0 hg0 hDgF,
      hΨ.pushforward_ker_isInGoodPosition c.relOpen hU' h0U hψ0 hg0 hker⟩

end Bundle

end Polyfold
