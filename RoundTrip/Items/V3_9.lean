import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_9

/-! Round trip for V3_9 (Definition 3.6: filled versions).  Refreshed 2026-11-02 (HEAD, germ
reading).

`A` is the conjunction of the types of the two listed theorems
`Polyfold.IsFilledVersion.isFillingGerm` (a whole-chart filled version is a germ filling) and
`Polyfold.IsFillingGerm.isFilledVersion` (a germ filling whose `g` is sc-smooth on the whole `U` is a
filled version), no universe parameters.  `IsFillingGerm` (the canonical, germ-reading filling of
Definitions 3.4/3.6) and `IsFilledVersion` (the whole-chart special case `G = ofSet U`) are
definitions (vocabulary).

* B (a) is proved outright (`B_part_a`): in a tame chart centred at `x₀`, `IsFilledVersion` is
  exactly "`g` sc-smooth on `U` and a filled version in the text's sense" (the glue of V3_7, copied
  here: `IsFillerOf ↔ IsFillingB` for `g` sc-smooth on `U`).
* B (b) `←` is proved (`B_part_b_mpr`): a project whole-chart filled version is a text filling.
* B (b) `→` is NOT proved and is believed false, as at the audit: B (b) names the whole-chart
  `IsFilledVersion` (`g` sc-smooth on `U ∩ E_m` for the chart's relatively open `U ∋ 0`), while the
  text's filling `g` is only an sc-smooth germ on levels that may shrink with `m`; condition (1)
  forces `g = 𝐟` on `O` near `0`, so when `𝐟 ∘ r` is germ-smooth but sc-smooth on no
  neighbourhood (`exists_isScSmoothGerm_not_isScSmooth`) no whole-chart filled version exists in
  any centred chart (not formalized: it needs the chart-transition calculus over all tame charts).
  The project itself now records this: `IsFillingGerm.isFilledVersion` needs `g` sc-smooth on `U`.
* New at the refresh: the canonical notion `IsFillingGerm` IS the text's filling, with no
  smoothness hypothesis on `g` (`germ_iff_B`, the glue of V3_7), so B (b) with `IsFillingGerm` in
  place of `IsFilledVersion` is proved (`B_part_b_germ`).  B's (b) targets the whole-chart variant,
  which is no longer the project's notion of filling (recorded as `B_issue`).
* `A → B` therefore fails (only through B (b) `→`); `B → A` is proved outright (B is not used):
  the two bridges are re-proved from non-banned lemmas (`IsSc1.isSc1GermWith_ofSet`,
  `fillDefect_isScSmooth`, uniqueness of the derivative on the germ). -/

namespace RoundTrip.V3_9
open Polyfold Set Filter Topology StrongRetr

/-- The project's statement (no universe parameters). -/
def A : Prop := (type_of% @Polyfold.IsFilledVersion.isFillingGerm) ∧
  (type_of% @Polyfold.IsFillingGerm.isFilledVersion)

theorem A_holds : A := ⟨@Polyfold.IsFilledVersion.isFillingGerm,
  @Polyfold.IsFillingGerm.isFilledVersion⟩

section Glue
variable {E F : ScBanach} {C U : Set (E.lvl 0)} {R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0}

/-- B's linearization at `0` is the project's derivative at `0 ∈ U₁`. -/
theorem linAt0_iff {F' : ScBanach} (k : E.lvl 0 → F'.lvl 0) (L : E.lvl 0 →L[ℝ] F'.lvl 0) :
    HasFDerivWithinAt (k ∘ E.toBase 1) (L.comp (E.toBase 1)) (E.lvlSet U 1) 0 ↔
      IsLinAt0B U k L := by
  rw [hasFDerivWithinAt_iff_tendsto, IsLinAt0B]
  refine Iff.of_eq ?_
  congr 1
  funext h
  simp [div_eq_inv_mul]

theorem linAt0_unique (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E.lvl 0) ∈ U) {F' : ScBanach}
    {k : E.lvl 0 → F'.lvl 0} {L₁ L₂ : E.lvl 0 →L[ℝ] F'.lvl 0} (h₁ : IsLinAt0B U k L₁)
    (h₂ : IsLinAt0B U k L₂) : L₁ = L₂ := by
  have h01 : (0 : E.lvl 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have h1 := (hU.isScDomain.uniqueDiffWithinAt 1 0 h01).eq ((linAt0_iff k L₁).2 h₁)
    ((linAt0_iff k L₂).2 h₂)
  have hd : Dense (Submodule.span ℝ (range (E.toBase 1)) : Set (E.lvl 0)) :=
    Dense.mono Submodule.subset_span (E.denseRange_inclK 0 1)
  refine ContinuousLinearMap.ext_on hd ?_
  rintro _ ⟨y, rfl⟩
  exact congrArg (fun L : E.lvl 1 →L[ℝ] F'.lvl 0 => L y) h1

theorem linAt0_scDeriv {F' : ScBanach} {k : E.lvl 0 → F'.lvl 0} (hk : IsSc1 U k)
    (h0 : (0 : E.lvl 0) ∈ U) : IsLinAt0B U k (scDeriv U k 0) := by
  have h01 : (0 : E.lvl 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  exact (linAt0_iff k _).1 (hk.isSc1With_scDeriv.hasFDerivWithinAt 0 h01)

/-- The map `y ↦ [1 − ρ(r(y))]g(y)` is sc-smooth for `g` sc-smooth (chain rule). -/
theorem k_isScSmooth (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    {g : E.lvl 0 → F.lvl 0} (hg : IsScSmooth U g) :
    IsScSmooth U fun y => g y - ρ R (r R y) (g y) := by
  have hrs : IsScSmooth U (r R) := r_isScSmooth hU hR
  have hpair := hrs.scPair hU.isScDomain hg
  have hfib : IsScSmooth (U ×ˢ univ) fun p : (E.prod F).lvl 0 => (R p).2 :=
    hR.isScSmooth_zero.snd (hU.prod_univ F).isScDomain
  have hcomp := IsScSmooth.comp hU.isScDomain (hU.prod_univ F).isScDomain hfib hpair
    fun y hy => ⟨r_mem hR hy, mem_univ _⟩
  exact (hg.sub hU.isScDomain hcomp).congr hU.isScDomain fun y _ => rfl

theorem proj_to_B (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E.lvl 0) ∈ U) {fb g : E.lvl 0 → F.lvl 0} (hg : IsScSmooth U g)
    (h : IsFillerOf hU hR h0 fb g) : IsFillingB C U R fb g := by
  have hQ := hU.isPartialQuadrant.isQuadrantLike
  refine ⟨⟨ScNbhdGerm.ofSet hU.relOpen h0, fun u hu => hu, hg.isScSmoothGerm hQ hU.relOpen h0⟩,
    h.eq_on, h.mem_of_fixed, ?_⟩
  obtain ⟨Φ, hΦ⟩ := h.linearization
  have hr1 : IsSc1 U (r R) := (r_isScSmooth hU hR).isSc1
  refine ⟨scDeriv U (r R) 0, scDeriv U (fun y => g y - ρ R (r R y) (g y)) 0,
    linAt0_scDeriv hr1 h0, linAt0_scDeriv h.isSc1 h0, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro v hv
    have := (Φ ⟨v, hv⟩).2
    rw [hΦ ⟨v, hv⟩] at this
    exact this
  · intro v₁ hv₁ v₂ hv₂ heq
    have : Φ ⟨v₁, hv₁⟩ = Φ ⟨v₂, hv₂⟩ := by
      apply Subtype.ext
      rw [hΦ, hΦ]
      exact heq
    exact congrArg Subtype.val (Φ.injective this)
  · intro w hw
    refine ⟨(Φ.symm ⟨w, hw⟩ : E.lvl 0), (Φ.symm ⟨w, hw⟩).2, ?_⟩
    have := hΦ (Φ.symm ⟨w, hw⟩)
    rw [ContinuousLinearEquiv.apply_symm_apply] at this
    exact this.symm
  · refine ⟨‖Φ.symm.toContinuousLinearMap‖, fun v hv => ?_⟩
    have h1 : (⟨v, hv⟩ : LinearMap.ker ((scDeriv U (r R) (0 : E.lvl 1) : E.lvl 0 →L[ℝ] E.lvl 0) :
        E.lvl 0 →ₗ[ℝ] E.lvl 0)) = Φ.symm (Φ ⟨v, hv⟩) := (Φ.symm_apply_apply _).symm
    have h2 : ‖v‖ = ‖(⟨v, hv⟩ : LinearMap.ker ((scDeriv U (r R) (0 : E.lvl 1) :
        E.lvl 0 →L[ℝ] E.lvl 0) : E.lvl 0 →ₗ[ℝ] E.lvl 0))‖ := rfl
    have h3 : ‖Φ ⟨v, hv⟩‖ = ‖scDeriv U (fun y => g y - ρ R (r R y) (g y)) 0 v‖ := by
      rw [← hΦ ⟨v, hv⟩]; rfl
    rw [h2, h1, ← h3]
    exact Φ.symm.toContinuousLinearMap.le_opNorm _

theorem B_to_proj (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E.lvl 0) ∈ U) {fb g : E.lvl 0 → F.lvl 0} (hg : IsScSmooth U g)
    (h : IsFillingB C U R fb g) : IsFillerOf hU hR h0 fb g := by
  obtain ⟨-, h1, h2, Lr, Lk, hLr, hLk, hbij, c, hc⟩ := h
  have hk := (k_isScSmooth hU hR hg).isSc1
  have hr1 : IsSc1 U (r R) := (r_isScSmooth hU hR).isSc1
  have eLr : Lr = scDeriv U (r R) 0 := linAt0_unique hU h0 hLr (linAt0_scDeriv hr1 h0)
  have eLk : Lk = scDeriv U (fun y => g y - ρ R (r R y) (g y)) 0 :=
    linAt0_unique hU h0 hLk (linAt0_scDeriv hk h0)
  subst eLr eLk
  refine ⟨h1, h2, hk, ?_⟩
  set p := scDeriv U (r R) (0 : E.lvl 1)
  set L := scDeriv U (fun y => g y - ρ R (r R y) (g y)) (0 : E.lvl 1)
  set q := ρCLM hR h0
  have hmaps : ∀ v : LinearMap.ker (p : E.lvl 0 →ₗ[ℝ] E.lvl 0),
      L v ∈ LinearMap.ker (q : F.lvl 0 →ₗ[ℝ] F.lvl 0) := fun v => hbij.1 v.2
  let φ : LinearMap.ker (p : E.lvl 0 →ₗ[ℝ] E.lvl 0) →ₗ[ℝ]
      LinearMap.ker (q : F.lvl 0 →ₗ[ℝ] F.lvl 0) :=
    ((L : E.lvl 0 →ₗ[ℝ] F.lvl 0).domRestrict _).codRestrict _ hmaps
  have hφ : ∀ v, (φ v : F.lvl 0) = L v := fun v => rfl
  have hinj : Function.Injective φ := by
    intro v₁ v₂ heq
    have : L v₁ = L v₂ := by rw [← hφ, ← hφ, heq]
    exact Subtype.ext (hbij.2.1 v₁.2 v₂.2 this)
  have hsurj : Function.Surjective φ := by
    intro w
    obtain ⟨v, hv, hvw⟩ := hbij.2.2 w.2
    exact ⟨⟨v, hv⟩, Subtype.ext hvw⟩
  let e := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have he : ∀ v, (e v : F.lvl 0) = L v := fun v => rfl
  refine ⟨e.toContinuousLinearEquivOfBounds ‖L‖ c (fun v => ?_) (fun w => ?_), fun v => he v⟩
  · rw [show ‖e v‖ = ‖L v‖ from congrArg norm (he v)]
    exact L.le_opNorm _
  · have h3 := hc (e.symm w) (e.symm w).2
    have h4 : L (e.symm w) = w := by rw [← he, e.apply_symm_apply]
    rw [h4] at h3
    exact h3

end Glue

section GermGlue
variable {E F : ScBanach} {C U : Set (E.lvl 0)} {R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0}

/-! ### The canonical germ-reading filling `IsFillingGerm` is the text's filling (from V3_7) -/

/-- On a germ `G` with `G₀ ⊆ U`, the level-`1` set `G₁` agrees with `U ∩ E₁` near `0`. -/
theorem germ_one_eq (hU : IsRelOpenInQuadrant E C U) (G : ScNbhdGerm E C) (hG : G.U 0 ⊆ U) :
    ∃ O₁ : Set (E.lvl 1), IsOpen O₁ ∧ (0 : E.lvl 1) ∈ O₁ ∧ E.lvlSet U 1 ∩ O₁ = G.U 1 := by
  obtain ⟨O₁, hO₁, hG1⟩ := G.relOpen 1
  have h01 : (0 : E.lvl 1) ∈ O₁ := by have := G.zero_mem 1; rw [hG1] at this; exact this.1
  refine ⟨O₁, hO₁, h01, ?_⟩
  have hUC : U ⊆ C := by obtain ⟨O, _, hO⟩ := hU.relOpen; rw [hO]; exact inter_subset_right
  ext x
  constructor
  · rintro ⟨hxU, hxO⟩
    rw [hG1]; exact ⟨hxO, hUC hxU⟩
  · intro hx
    refine ⟨hG (G.toBase_mem hx), ?_⟩
    rw [hG1] at hx; exact hx.1

theorem linAt0_germ_iff (hU : IsRelOpenInQuadrant E C U) (G : ScNbhdGerm E C) (hG : G.U 0 ⊆ U)
    {F' : ScBanach} (k : E.lvl 0 → F'.lvl 0) (L : E.lvl 0 →L[ℝ] F'.lvl 0) :
    HasFDerivWithinAt (k ∘ E.toBase 1) (L.comp (E.toBase 1)) (G.U 1) 0 ↔ IsLinAt0B U k L := by
  obtain ⟨O₁, hO₁, h01, heq⟩ := germ_one_eq hU G hG
  rw [← heq, hasFDerivWithinAt_inter (hO₁.mem_nhds h01)]
  exact linAt0_iff k L

theorem bij_of_equiv {Lr : E.lvl 0 →L[ℝ] E.lvl 0} {q : F.lvl 0 →L[ℝ] F.lvl 0}
    {L : E.lvl 0 →L[ℝ] F.lvl 0}
    (Φ : LinearMap.ker (Lr : E.lvl 0 →ₗ[ℝ] E.lvl 0) ≃L[ℝ] LinearMap.ker (q : F.lvl 0 →ₗ[ℝ] F.lvl 0))
    (hΦ : ∀ v, (Φ v : F.lvl 0) = L v) :
    Set.BijOn L {v | Lr v = 0} {w | q w = 0} ∧ ∃ c : ℝ, ∀ v, Lr v = 0 → ‖v‖ ≤ c * ‖L v‖ := by
  refine ⟨⟨?_, ?_, ?_⟩, ‖Φ.symm.toContinuousLinearMap‖, fun v hv => ?_⟩
  · intro v hv
    have := (Φ ⟨v, hv⟩).2
    rw [hΦ ⟨v, hv⟩] at this
    exact this
  · intro v₁ hv₁ v₂ hv₂ heq
    have : Φ ⟨v₁, hv₁⟩ = Φ ⟨v₂, hv₂⟩ := by
      apply Subtype.ext
      rw [hΦ, hΦ]
      exact heq
    exact congrArg Subtype.val (Φ.injective this)
  · intro w hw
    refine ⟨(Φ.symm ⟨w, hw⟩ : E.lvl 0), (Φ.symm ⟨w, hw⟩).2, ?_⟩
    have := hΦ (Φ.symm ⟨w, hw⟩)
    rw [ContinuousLinearEquiv.apply_symm_apply] at this
    exact this.symm
  · have h1 : (⟨v, hv⟩ : LinearMap.ker (Lr : E.lvl 0 →ₗ[ℝ] E.lvl 0)) = Φ.symm (Φ ⟨v, hv⟩) :=
      (Φ.symm_apply_apply _).symm
    have h2 : ‖v‖ = ‖(⟨v, hv⟩ : LinearMap.ker (Lr : E.lvl 0 →ₗ[ℝ] E.lvl 0))‖ := rfl
    have h3 : ‖Φ ⟨v, hv⟩‖ = ‖L v‖ := by rw [← hΦ ⟨v, hv⟩]; rfl
    rw [h2, h1, ← h3]
    exact Φ.symm.toContinuousLinearMap.le_opNorm _

theorem equiv_of_bij {Lr : E.lvl 0 →L[ℝ] E.lvl 0} {q : F.lvl 0 →L[ℝ] F.lvl 0}
    {L : E.lvl 0 →L[ℝ] F.lvl 0} (hbij : Set.BijOn L {v | Lr v = 0} {w | q w = 0}) (c : ℝ)
    (hc : ∀ v, Lr v = 0 → ‖v‖ ≤ c * ‖L v‖) :
    ∃ Φ : LinearMap.ker (Lr : E.lvl 0 →ₗ[ℝ] E.lvl 0) ≃L[ℝ]
        LinearMap.ker (q : F.lvl 0 →ₗ[ℝ] F.lvl 0), ∀ v, (Φ v : F.lvl 0) = L v := by
  have hmaps : ∀ v : LinearMap.ker (Lr : E.lvl 0 →ₗ[ℝ] E.lvl 0),
      L v ∈ LinearMap.ker (q : F.lvl 0 →ₗ[ℝ] F.lvl 0) := fun v => hbij.1 v.2
  let φ : LinearMap.ker (Lr : E.lvl 0 →ₗ[ℝ] E.lvl 0) →ₗ[ℝ]
      LinearMap.ker (q : F.lvl 0 →ₗ[ℝ] F.lvl 0) :=
    ((L : E.lvl 0 →ₗ[ℝ] F.lvl 0).domRestrict _).codRestrict _ hmaps
  have hφ : ∀ v, (φ v : F.lvl 0) = L v := fun v => rfl
  have hinj : Function.Injective φ := by
    intro v₁ v₂ heq
    have : L v₁ = L v₂ := by rw [← hφ, ← hφ, heq]
    exact Subtype.ext (hbij.2.1 v₁.2 v₂.2 this)
  have hsurj : Function.Surjective φ := by
    intro w
    obtain ⟨v, hv, hvw⟩ := hbij.2.2 w.2
    exact ⟨⟨v, hv⟩, Subtype.ext hvw⟩
  let e := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have he : ∀ v, (e v : F.lvl 0) = L v := fun v => rfl
  refine ⟨e.toContinuousLinearEquivOfBounds ‖L‖ c (fun v => ?_) (fun w => ?_), fun v => he v⟩
  · rw [show ‖e v‖ = ‖L v‖ from congrArg norm (he v)]
    exact L.le_opNorm _
  · have h3 := hc (e.symm w) (e.symm w).2
    have h4 : L (e.symm w) = w := by rw [← he, e.apply_symm_apply]
    rw [h4] at h3
    exact h3

theorem germ_to_B (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E.lvl 0) ∈ U) {fb g : E.lvl 0 → F.lvl 0} (h : IsFillingGerm hU hR h0 fb g) :
    IsFillingB C U R fb g := by
  obtain ⟨h1, h2, G, hGU, hg, Dk, hDk, Φ, hΦ⟩ := h
  have hr1 : IsSc1 U (r R) := (r_isScSmooth hU hR).isSc1
  obtain ⟨hb, c, hc⟩ := bij_of_equiv Φ hΦ
  exact ⟨⟨G, hGU, hg⟩, h1, h2, scDeriv U (r R) 0, Dk 0, linAt0_scDeriv hr1 h0,
    (linAt0_germ_iff hU G hGU _ _).1 (hDk.hasFDerivWithinAt 0 (G.zero_mem 1)), hb, c, hc⟩

theorem B_to_germ (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E.lvl 0) ∈ U) {fb g : E.lvl 0 → F.lvl 0} (h : IsFillingB C U R fb g) :
    IsFillingGerm hU hR h0 fb g := by
  obtain ⟨⟨G, hGU, hg⟩, h1, h2, Lr, Lk, hLr, hLk, hbij, c, hc⟩ := h
  obtain ⟨Dg, hDg⟩ := (hg 1).1
  have hDk := fillDefect_isSc1GermWith hU hR h0 hGU hDg
  have hr1 : IsSc1 U (r R) := (r_isScSmooth hU hR).isSc1
  have eLr : Lr = scDeriv U (r R) 0 := linAt0_unique hU h0 hLr (linAt0_scDeriv hr1 h0)
  have eLk : Lk = fillDefectDeriv U R g Dg 0 := linAt0_unique hU h0 hLk
    ((linAt0_germ_iff hU G hGU _ _).1 (hDk.hasFDerivWithinAt 0 (G.zero_mem 1)))
  subst eLr eLk
  obtain ⟨Φ, hΦ⟩ := equiv_of_bij (q := ρCLM hR h0) hbij c hc
  exact ⟨h1, h2, G, hGU, hg, _, hDk, Φ, hΦ⟩

/-- **The canonical germ-reading filling is the text's filling** (no hypothesis on `g`). -/
theorem germ_iff_B (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E.lvl 0) ∈ U) (fb g : E.lvl 0 → F.lvl 0) :
    IsFillingGerm hU hR h0 fb g ↔ IsFillingB C U R fb g :=
  ⟨germ_to_B hU hR h0, B_to_germ hU hR h0⟩

end GermGlue

section Bundle
set_option linter.unusedSectionVars false
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- B (a): the project's filled versions are the text's, for `g` sc-smooth on `U`. -/
theorem B_part_a (c : StrongBundleChart PX P) (f : X → Y)
    (h0 : (0 : c.φ.model.E.lvl 0) ∈ c.U) (g : c.φ.model.E.lvl 0 → c.F.lvl 0) :
    IsFilledVersion c.relOpen c.isRetraction h0 (principalB c f) g ↔
      IsScSmooth c.U g ∧ IsFilledVersionB c f g :=
  ⟨fun h => ⟨h.isScSmooth, proj_to_B c.relOpen c.isRetraction h0 h.isScSmooth h.filler⟩,
    fun h => ⟨h.1, B_to_proj c.relOpen c.isRetraction h0 h.1 h.2⟩⟩

/-- B (b), `←`: a project filled version in a tame centred chart is a text filling. -/
theorem B_part_b_mpr (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X)
    (h : ∃ c : StrongBundleChart PX P, Bd.IsTameChart c ∧ x₀ ∈ c.φ.source ∧
      c.φ.toPartialEquiv x₀ = 0 ∧
      ∃ (h0 : (0 : c.φ.model.E.lvl 0) ∈ c.U) (g : c.φ.model.E.lvl 0 → c.F.lvl 0),
        IsFilledVersion c.relOpen c.isRetraction h0 (principalB c f) g) :
    HasFillingB Bd f x₀ := by
  obtain ⟨c, hc, hx, hx0, h0, g, hg⟩ := h
  exact ⟨c, hc, hx, hx0, g, ((B_part_a c f h0 g).1 hg).2⟩

/-- B (b) with the canonical germ filling in place of the whole-chart `IsFilledVersion`: proved. -/
theorem B_part_b_germ (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X) :
    HasFillingB Bd f x₀ ↔
      ∃ c : StrongBundleChart PX P, Bd.IsTameChart c ∧ x₀ ∈ c.φ.source ∧
        c.φ.toPartialEquiv x₀ = 0 ∧
        ∃ (h0 : (0 : c.φ.model.E.lvl 0) ∈ c.U) (g : c.φ.model.E.lvl 0 → c.F.lvl 0),
          IsFillingGerm c.relOpen c.isRetraction h0 (principalB c f) g := by
  constructor
  · rintro ⟨c, hc, hx, hx0, g, hg⟩
    have h0 : (0 : c.φ.model.E.lvl 0) ∈ c.U := by
      obtain ⟨G, hGU, -⟩ := hg.1
      exact hGU (G.zero_mem 0)
    exact ⟨c, hc, hx, hx0, h0, g, (germ_iff_B c.relOpen c.isRetraction h0 _ g).2 hg⟩
  · rintro ⟨c, hc, hx, hx0, h0, g, hg⟩
    exact ⟨c, hc, hx, hx0, g, (germ_iff_B c.relOpen c.isRetraction h0 _ g).1 hg⟩

/-- B with (b) `→` assumed: everything else in B is proved. -/
theorem B_of_part_b_mp
    (hb : ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
      (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X),
      (∀ x, P (f x) = x) → IsScSmoothSectionGermB Bd f x₀ → HasFillingB Bd f x₀ →
        ∃ c : StrongBundleChart PX P, Bd.IsTameChart c ∧ x₀ ∈ c.φ.source ∧
          c.φ.toPartialEquiv x₀ = 0 ∧
          ∃ (h0 : (0 : c.φ.model.E.lvl 0) ∈ c.U) (g : c.φ.model.E.lvl 0 → c.F.lvl 0),
            IsFilledVersion c.relOpen c.isRetraction h0 (principalB c f) g) : B := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f x₀ hsec hgerm
  exact ⟨fun c _ _ _ h0 g => B_part_a c f h0 g,
    ⟨hb PX P Bd f x₀ hsec hgerm, B_part_b_mpr Bd f x₀⟩⟩

end Bundle

/-- A, re-proved from non-banned lemmas (the project's proofs). -/
theorem A_reproved : A := by
  refine ⟨?_, ?_⟩
  · intro E F C U R hU hR h0 fb g h
    have hQ := hU.isPartialQuadrant.isQuadrantLike
    obtain ⟨Φ, hΦ⟩ := h.filler.linearization
    exact ⟨h.filler.eq_on, h.filler.mem_of_fixed, ScNbhdGerm.ofSet hU.relOpen h0, fun u hu => hu,
      h.isScSmooth.isScSmoothGerm hQ hU.relOpen h0, scDeriv U (fillDefect R g),
      h.filler.isSc1.isSc1GermWith_ofSet hU.relOpen h0, Φ, hΦ⟩
  · intro E F C U R hU hR h0 fb g hg h
    obtain ⟨G, hGU, -, Dk, hDk, Φ, hΦ⟩ := h.germ
    have hQ := hU.isPartialQuadrant.isQuadrantLike
    have hk : IsSc1 U (fillDefect R g) := (fillDefect_isScSmooth hU hR hg).isSc1
    have hsub : ∀ m, G.U m ⊆ (ScNbhdGerm.ofSet hU.relOpen h0).U m := fun m x hx => by
      rw [ScNbhdGerm.ofSet_U, ScBanach.mem_lvlSet]
      exact hGU (G.toBase_mem hx)
    have hDk' : IsSc1GermWith G (fillDefect R g) (scDeriv U (fillDefect R g)) :=
      (hk.isSc1GermWith_ofSet hU.relOpen h0).mono hsub
    have heq : Dk 0 = scDeriv U (fillDefect R g) 0 :=
      hDk.eq_of_uniqueDiffWithinAt hDk' (G.zero_mem 1) (G.uniqueDiffWithinAt hQ 1 (G.zero_mem 1))
    refine ⟨hg, h.eq_on, h.mem_of_fixed, hk, Φ, fun v => ?_⟩
    rw [hΦ v, heq]
    rfl

/-- Proved outright (B is not used); flagged as vacuous. -/
theorem B_to_A : B → A := fun _ => A_reproved

#rt_check RoundTrip.V3_9.B_to_A [Polyfold.IsFilledVersion.isFillingGerm,
  Polyfold.IsFillingGerm.isFilledVersion]
#rt_check RoundTrip.V3_9.B_part_b_germ [Polyfold.IsFilledVersion.isFillingGerm,
  Polyfold.IsFillingGerm.isFilledVersion]
#rt_check RoundTrip.V3_9.B_part_a [Polyfold.IsFilledVersion.isFillingGerm,
  Polyfold.IsFillingGerm.isFilledVersion]
#rt_overlap RoundTrip.V3_9.B_to_A [Polyfold.IsFilledVersion.isFillingGerm,
  Polyfold.IsFillingGerm.isFilledVersion]

end RoundTrip.V3_9
