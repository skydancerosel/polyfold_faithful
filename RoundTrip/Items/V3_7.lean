import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_7

/-! Round trip for V3_7 (Definition 3.4: fillers).  Refreshed 2026-11-02 (HEAD, germ reading).

`A` is the conjunction of the types of the three listed theorems `Polyfold.StrongRetr.apply_eq`
(`R(u, h) = (r(u), ρ(u)h)`), `Polyfold.StrongRetr.ρ_ρ` (`ρ(x)` is a projection on `O`) and
`Polyfold.fillDefect_isScSmoothGerm` (the fill defect `k = [1 − ρ(r(·))]g` of an sc-smooth germ
`g` on `G` with `G₀ ⊆ U` is an sc-smooth germ on `G`), no universe parameters.  `IsFillingGerm`
(the canonical, germ-reading filling of Definitions 3.4/3.6), `fillDefect`, `IsFillerOf`,
`StrongRetr.r`, `StrongRetr.ρ`, `StrongRetr.ρCLM` are definitions (vocabulary).

* `A → B` is proved outright (A is not used).  B compares the project's whole-`U` conditions
  `IsFillerOf` with the text's filling under B's hypothesis `g` sc-smooth on `U`.  `rB`, `ρB`, `kB`
  are the project's `r`, `ρ`, `fillDefect R g` definitionally.  Conditions (1), (2) are literally
  the same.
  - project ⇒ B: `g` sc-smooth on `U` gives the section germ on `ofSet U`
    (`IsScSmooth.isScSmoothGerm`); the linearizations are `Lr = scDeriv U r 0`,
    `Lk = scDeriv U k 0` (`HasFDerivWithinAt` at `0 ∈ U₁` is B's quotient limit); the continuous
    linear equivalence `Φ` gives B's `BijOn` and the bound `‖v‖ ≤ ‖Φ⁻¹‖ ‖Lk v‖`.
  - B ⇒ project: the field `isSc1` (`k` sc¹ on `U`), which B does not contain, follows from the
    hypothesis `IsScSmooth U g` and the sc-smoothness of `R` by the chain rule (`scPair`, `comp`,
    `sub`); B's `Lr`, `Lk` equal the chosen `scDeriv`s by uniqueness of derivatives at `0 ∈ U₁`
    (unique differentiability + density of `E₁`); `Φ` is built from the bijection and B's bound
    (`LinearEquiv.toContinuousLinearEquivOfBounds`).
  B's hypotheses "tame", `r(0) = 0` and "`𝐟` an sc-smooth section germ of `K → O`" are not needed.
* New at the refresh: the canonical germ-reading notion `IsFillingGerm` is the text's filling
  `IsFillingB` **without** any smoothness hypothesis on `g` (`germ_iff_B`): the germ `G` of `g` is
  B's section germ; `Dk(0)` of the sc¹-germ `k` on `G` is B's linearization because `G₁` and
  `U ∩ E₁` agree near `0` (`linAt0_germ_iff`); conversely the derivative family `Dk` of `k` on `G`
  is the chain rule (`fillDefect_isSc1GermWith`) and B's `Lk` is `Dk(0)` by uniqueness.
* `B → A` is proved outright (B says nothing about `apply_eq`, `ρ_ρ`, `fillDefect_isScSmoothGerm`):
  the first two are re-proved from the fields of `IsStrongBundleRetraction`, the third by the
  project's germ chain rule (`r_isScSmoothGerm`, `pair`, `fiber_isScSmooth`, `comp_germ`, `sub`). -/

namespace RoundTrip.V3_7
open Polyfold Set Filter Topology StrongRetr

/-- The project's statement (no universe parameters). -/
def A : Prop := (type_of% @Polyfold.StrongRetr.apply_eq) ∧ (type_of% @Polyfold.StrongRetr.ρ_ρ) ∧
  (type_of% @Polyfold.fillDefect_isScSmoothGerm)

theorem A_holds : A :=
  ⟨@Polyfold.StrongRetr.apply_eq, @Polyfold.StrongRetr.ρ_ρ, @Polyfold.fillDefect_isScSmoothGerm⟩

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

theorem B_holds : B := by
  intro E F C U R hU hR h0 _ _ fb g _ hg
  exact ⟨proj_to_B hU hR h0 hg, B_to_proj hU hR h0 hg⟩

/-! ### The canonical germ-reading filling `IsFillingGerm` is the text's filling -/

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

/-- B's linearization at `0` is the derivative at `0` within the germ's level `G₁`. -/
theorem linAt0_germ_iff (hU : IsRelOpenInQuadrant E C U) (G : ScNbhdGerm E C) (hG : G.U 0 ⊆ U)
    {F' : ScBanach} (k : E.lvl 0 → F'.lvl 0) (L : E.lvl 0 →L[ℝ] F'.lvl 0) :
    HasFDerivWithinAt (k ∘ E.toBase 1) (L.comp (E.toBase 1)) (G.U 1) 0 ↔ IsLinAt0B U k L := by
  obtain ⟨O₁, hO₁, h01, heq⟩ := germ_one_eq hU G hG
  rw [← heq, hasFDerivWithinAt_inter (hO₁.mem_nhds h01)]
  exact linAt0_iff k L

/-- A topological isomorphism of the kernels given by `L` yields B's bijection and bound. -/
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

/-- B's bijection and bound yield a topological isomorphism of the kernels given by `L`. -/
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

end Glue

theorem A_to_B : A → B := fun _ => B_holds

/-- A, re-proved from the fields of `IsStrongBundleRetraction`. -/
theorem apply_eq' {E F : ScBanach} {U : Set (E.lvl 0)} {R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0}
    (hR : IsStrongBundleRetraction U R) {u : E.lvl 0} (hu : u ∈ U) (h : F.lvl 0) :
    R (u, h) = (r R u, ρ R u h) :=
  Prod.ext (hR.fst_independent u hu h 0) rfl

/-- `fillDefect_isScSmoothGerm`, re-proved by the project's germ chain rule. -/
theorem fillDefect_isScSmoothGerm' {E F : ScBanach} {C U : Set (E.lvl 0)}
    {R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0} {G₁ : ScNbhdGerm E C}
    (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R) (h0 : (0 : E.lvl 0) ∈ U)
    (hG : G₁.U 0 ⊆ U) {g : E.lvl 0 → F.lvl 0} (hg : IsScSmoothGerm G₁ g) :
    IsScSmoothGerm G₁ (fillDefect R g) := by
  have hQ := hU.isPartialQuadrant.isQuadrantLike
  have hpair : IsScSmoothGerm G₁ (pairMap (r R) g) := (r_isScSmoothGerm hU hR h0 hG).pair hQ hg
  have hcomp := (fiber_isScSmooth hU hR).comp_germ hQ (hU.prod_univ F).isScDomain hpair
    (pairMap_mapsTo hR hG g)
  exact hg.sub hQ hcomp

theorem B_to_A : B → A := by
  intro _
  refine ⟨@apply_eq', ?_, @fillDefect_isScSmoothGerm'⟩
  intro E F U R hR x hx h
  obtain ⟨u, hu, rfl⟩ := hx
  have hru : r R u ∈ U := (hR.mapsTo ⟨hu, mem_univ _⟩).1
  -- `r(r(u)) = r(u)`
  have hrr : r R (r R u) = r R u := by
    have := congrArg Prod.fst (hR.idem (u, 0) ⟨hu, mem_univ _⟩)
    rw [apply_eq' hR hu, apply_eq' hR hru] at this
    exact this
  have := congrArg Prod.snd (hR.idem (r R u, h) ⟨hru, mem_univ _⟩)
  rw [apply_eq' hR hru, hrr, apply_eq' hR hru, hrr] at this
  exact this

#rt_check RoundTrip.V3_7.A_to_B [Polyfold.StrongRetr.apply_eq, Polyfold.StrongRetr.ρ_ρ, Polyfold.fillDefect_isScSmoothGerm]
#rt_check RoundTrip.V3_7.B_to_A [Polyfold.StrongRetr.apply_eq, Polyfold.StrongRetr.ρ_ρ, Polyfold.fillDefect_isScSmoothGerm]
#rt_check RoundTrip.V3_7.germ_iff_B [Polyfold.StrongRetr.apply_eq, Polyfold.StrongRetr.ρ_ρ, Polyfold.fillDefect_isScSmoothGerm]
#rt_overlap RoundTrip.V3_7.B_to_A [Polyfold.StrongRetr.apply_eq, Polyfold.StrongRetr.ρ_ρ, Polyfold.fillDefect_isScSmoothGerm]

end RoundTrip.V3_7
