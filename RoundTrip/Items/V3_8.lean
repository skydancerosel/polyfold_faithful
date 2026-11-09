import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_8

/-! Round trip for V3_8 (the matrix of `Dg(0)` after Definition 3.4, and Proposition 3.5).
Refreshed 2026-11-02 against HEAD (germ reading of Definition 3.4; new conjuncts in the row).

`A` is the conjunction of the types of the listed theorems (universes at `0`):
the whole-chart filler lemmas `Polyfold.IsFillerOf.proposition_3_1_5`, `deriv_comp_r_eq_zero`,
`exists_kerEquiv`, `scDeriv_section_comp_r`, the abstract linear algebra `Polyfold.proposition_3_1_5_preprint`
(universes `0, 0`), `Polyfold.StrongRetr.scDeriv_fiber_zero`, the sc-form results
`Polyfold.IsScFredholm.restrict`, `IsFillerOf.proposition_3_1_5_sc`, `filler_condition_three_sc`,
`proposition_3_1_5_sc_converse`, `proposition_3_1_5_sc_iff`, and their germ versions
`Polyfold.IsFillingGerm.proposition_3_1_5`, `exists_kerEquiv`, `deriv_comp_r_eq_zero`,
`proposition_3_1_5_sc`, `filler_condition_three_sc`, `proposition_3_1_5_sc_converse`,
`proposition_3_1_5_sc_iff`.  `fillerRestrict`, `fillerRestrict_kerEquiv`, `fillerRestrict_cokerEquiv`
are definitions (vocabulary).

* `A → B` is now PROVED (`A_to_B`).  At the audit A only had whole-chart lemmas (filler `g`
  sc-smooth on all of `U`), which a germ filler does not satisfy.  A now contains the germ forms
  `IsFillingGerm.proposition_3_1_5` and `IsFillingGerm.exists_kerEquiv`, which take any derivative
  family `Dg` of the germ `g` on a germ `G ⊆ U`.  Glue: B's `IsFillingB` (with the section
  property globalised by `𝐟'(x) = ρ(x)𝐟(x)`) is an `IsFillingGerm` (the fill defect's derivative
  family is `fillDefectDeriv`, `Dk(0) = Lk` by uniqueness on the germ); B's `Lr, Lg, ρ₀` are
  `scDeriv U r 0`, `Dg(0)`, `ρCLM` by uniqueness of the derivative on the germ's level `1`
  (locally equal to `U₁`); B's `Lf = D(𝐟 ∘ r)(0) = D(g ∘ r)(0) = Dg(0)Dr(0)` by locality and the
  germ chain rule `IsSc1GermWith.comp_preimage` (a project lemma, not in A); then the germ
  `IsFillingGerm.proposition_3_1_5` and `exists_kerEquiv` give (ii)–(v); `restrictB Lf` is `fillerRestrict`, B's
  `IsFredholmB`/`indexB` are Mathlib's `IsFredholm`/`fredholmIndex` between Banach spaces.
  The audit's whole-chart special case `A_to_B_wholeU` is kept.
* `B → A` is NOT proved: A contains statements B does not speak about — the abstract
  linear-algebra `proposition_3_1_5_preprint` for arbitrary Banach spaces (B only concerns sc-spaces, whose
  level-0 spaces are separable), the fibre derivative `scDeriv_fiber_zero`, the sc-level
  statements (`IsScFredholm.restrict`, the `…_sc` lemmas: sc-Fredholmness of `Tf(0)` and `Dg(0)`
  on every level), and the whole-chart lemmas whose hypotheses (no germ-smooth `𝐟 ∘ r`, no given
  `Lf`) are not B's. -/

namespace RoundTrip.V3_8
open Polyfold Set Filter Topology StrongRetr Function

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.IsFillerOf.proposition_3_1_5) ∧ (type_of% @Polyfold.proposition_3_1_5_preprint.{0, 0}) ∧
    (type_of% @Polyfold.StrongRetr.scDeriv_fiber_zero) ∧
    (type_of% @Polyfold.IsFillerOf.deriv_comp_r_eq_zero) ∧
    (type_of% @Polyfold.IsFillerOf.exists_kerEquiv) ∧
    (type_of% @Polyfold.IsFillerOf.scDeriv_section_comp_r) ∧
    (type_of% @Polyfold.IsScFredholm.restrict) ∧
    (type_of% @Polyfold.IsFillerOf.proposition_3_1_5_sc) ∧
    (type_of% @Polyfold.IsFillerOf.filler_condition_three_sc) ∧
    (type_of% @Polyfold.IsFillerOf.proposition_3_1_5_sc_converse) ∧
    (type_of% @Polyfold.IsFillerOf.proposition_3_1_5_sc_iff) ∧
    (type_of% @Polyfold.IsFillingGerm.proposition_3_1_5) ∧
    (type_of% @Polyfold.IsFillingGerm.exists_kerEquiv) ∧
    (type_of% @Polyfold.IsFillingGerm.deriv_comp_r_eq_zero) ∧
    (type_of% @Polyfold.IsFillingGerm.proposition_3_1_5_sc) ∧
    (type_of% @Polyfold.IsFillingGerm.filler_condition_three_sc) ∧
    (type_of% @Polyfold.IsFillingGerm.proposition_3_1_5_sc_converse) ∧
    (type_of% @Polyfold.IsFillingGerm.proposition_3_1_5_sc_iff)

theorem A_holds : A :=
  ⟨@Polyfold.IsFillerOf.proposition_3_1_5, @Polyfold.proposition_3_1_5_preprint.{0, 0},
    @Polyfold.StrongRetr.scDeriv_fiber_zero, @Polyfold.IsFillerOf.deriv_comp_r_eq_zero,
    @Polyfold.IsFillerOf.exists_kerEquiv, @Polyfold.IsFillerOf.scDeriv_section_comp_r,
    @Polyfold.IsScFredholm.restrict, @Polyfold.IsFillerOf.proposition_3_1_5_sc,
    @Polyfold.IsFillerOf.filler_condition_three_sc, @Polyfold.IsFillerOf.proposition_3_1_5_sc_converse,
    @Polyfold.IsFillerOf.proposition_3_1_5_sc_iff, @Polyfold.IsFillingGerm.proposition_3_1_5,
    @Polyfold.IsFillingGerm.exists_kerEquiv, @Polyfold.IsFillingGerm.deriv_comp_r_eq_zero,
    @Polyfold.IsFillingGerm.proposition_3_1_5_sc, @Polyfold.IsFillingGerm.filler_condition_three_sc,
    @Polyfold.IsFillingGerm.proposition_3_1_5_sc_converse,
    @Polyfold.IsFillingGerm.proposition_3_1_5_sc_iff⟩

/-- B restricted to fillers `g` that are sc-smooth on the whole `U` (the project's setting). -/
def B_wholeU : Prop :=
  ∀ (E F : ScBanach) (C U : Set (E.lvl 0)) (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0)
    (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (_h0 : (0 : E.lvl 0) ∈ U),
    (IsStrongBundleRetraction.baseRetraction hU hR).IsTame → rB R 0 = 0 →
    ∀ fb g : E.lvl 0 → F.lvl 0, IsScSmooth U g →
    IsSectionGermKB C U R fb → IsFillingB C U R fb g → fb 0 = 0 →
    ∀ (Lr : E.lvl 0 →L[ℝ] E.lvl 0) (Lg Lf : E.lvl 0 →L[ℝ] F.lvl 0)
      (ρ₀ : F.lvl 0 →L[ℝ] F.lvl 0),
      IsLinAt0B U (rB R) Lr → IsLinAt0B U g Lg → IsLinAt0B U (fb ∘ rB R) Lf →
      (∀ w : F.lvl 0, ρ₀ w = ρB R 0 w) →
      (Lr.comp Lr = Lr ∧ ρ₀.comp ρ₀ = ρ₀) ∧
      (∀ v ∈ rangeB Lr, Lg v = Lf v ∧ Lg v ∈ rangeB ρ₀) ∧
      (Set.BijOn (fun v => Lg v - ρ₀ (Lg v)) (kerB Lr : Set (E.lvl 0))
          (kerB ρ₀ : Set (F.lvl 0)) ∧
        ∃ c : ℝ, ∀ v ∈ kerB Lr, ‖v‖ ≤ c * ‖Lg v - ρ₀ (Lg v)‖) ∧
      ((∀ w ∈ rangeB ρ₀, ∃ v ∈ rangeB Lr, Lf v = w) ↔ Function.Surjective Lg) ∧
      (∀ h : ∀ v : rangeB Lr, Lf v ∈ rangeB ρ₀,
        (IsFredholmB (restrictB Lf (rangeB Lr) (rangeB ρ₀) h) ↔ IsFredholmB Lg) ∧
        (IsFredholmB Lg → indexB (restrictB Lf (rangeB Lr) (rangeB ρ₀) h) = indexB Lg))

/-- `B_wholeU` is a specialisation of B. -/
theorem B_imp_B_wholeU : B → B_wholeU :=
  fun hB E F C U R hU hR h0 ht hr0 fb g _ => hB E F C U R hU hR h0 ht hr0 fb g

/-- B's Fredholm notion is Mathlib's between Banach spaces. -/
theorem fredB_iff {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] [CompleteSpace V'] (T : V →L[ℝ] V') :
    IsFredholmB T ↔ T.IsFredholm :=
  ⟨fun h => isFredholm_of_banach T h.1 h.2.1 h.2.2,
    fun h => ⟨h.finite_ker, h.isClosed_range, h.finite_coker⟩⟩

theorem indexB_eq {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] (T : V →L[ℝ] V') : indexB T = fredholmIndex T := rfl

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

theorem A_to_B_wholeU : A → B_wholeU := by
  intro hA E F C U R hU hR h0 _ht hr0 fb g hg hfK hfill hfb0 Lr Lg Lf ρ₀ hLr hLg hLf hρ₀
  obtain ⟨_, hP35lin, _, hdcr, hker, hsec, _⟩ := hA
  have hr0' : r R 0 = 0 := hr0
  have h0O : (0 : E.lvl 0) ∈ r R '' U := ⟨0, h0, hr0⟩
  have hg0 : g 0 = 0 := by rw [← hfb0]; exact (hfill.2.1.self_of_nhds h0O).symm
  have hF : IsFillerOf hU hR h0 fb g := B_to_proj hU hR h0 hg hfill
  -- globalise the section property: `𝐟' x = ρ(x)𝐟(x)`
  let fb' : E.lvl 0 → F.lvl 0 := fun x => ρ R x (fb x)
  have hF' : IsFillerOf hU hR h0 fb' g := by
    refine ⟨?_, hF.mem_of_fixed, hF.isSc1, hF.linearization⟩
    filter_upwards [hfK.1, hF.eq_on] with x h1 h2 hx
    have e1 : ρ R x (fb x) = fb x := h1 hx
    show ρ R x (fb x) = g x
    rw [e1, h2 hx]
  have hfK' : ∀ x ∈ r R '' U, (x, fb' x) ∈ R '' (U ×ˢ univ) := by
    intro x hx
    refine ⟨(x, fb x), ⟨mem_U_of_mem_O hR hx, mem_univ _⟩, ?_⟩
    rw [apply_eq hR (mem_U_of_mem_O hR hx), r_eq_self hR hx]
  -- the linearizations
  have hr1 : IsSc1 U (r R) := (r_isScSmooth hU hR).isSc1
  have eLr : Lr = scDeriv U (r R) 0 := linAt0_unique hU h0 hLr (linAt0_scDeriv hr1 h0)
  have eLg : Lg = scDeriv U g 0 := linAt0_unique hU h0 hLg (linAt0_scDeriv hg.isSc1 h0)
  have eρ : ρ₀ = ρCLM hR h0 := ContinuousLinearMap.ext fun w => hρ₀ w
  have hgr : IsSc1 U (g ∘ r R) :=
    (IsScSmooth.comp hU.isScDomain hU.isScDomain hg (r_isScSmooth hU hR)
      fun u hu => r_mem hR hu).isSc1
  have hFg : IsFillerOf hU hR h0 g g :=
    ⟨Eventually.of_forall fun _ _ => rfl, hF.mem_of_fixed, hF.isSc1, hF.linearization⟩
  have hDgr : scDeriv U (g ∘ r R) 0 = (scDeriv U g 0).comp (scDeriv U (r R) 0) :=
    hsec hFg hg h0O hgr
  -- `𝐟 ∘ r = g ∘ r` near `0` in `U`, so `Lf` is the linearization of `g ∘ r`
  have hev : ∀ᶠ y in 𝓝[U] (0 : E.lvl 0), fb (r R y) = g (r R y) := by
    have hrc : Tendsto (r R) (𝓝[U] 0) (𝓝 0) := by
      have := (r_isScSmooth hU hR).isSc1.isSc0.continuousOn_base 0 h0
      rwa [ContinuousWithinAt, hr0'] at this
    filter_upwards [hrc.eventually hF.eq_on, self_mem_nhdsWithin] with y hy hyU
    exact hy ⟨y, hyU, rfl⟩
  have ht : Tendsto (E.toBase 1) (𝓝[E.toBase 1 ⁻¹' U] (0 : E.lvl 1)) (𝓝[U] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h1 : Tendsto (E.toBase 1) (𝓝[E.toBase 1 ⁻¹' U] (0 : E.lvl 1)) (𝓝 (E.toBase 1 0)) :=
        ((E.toBase 1).continuous.tendsto 0).mono_left nhdsWithin_le_nhds
      rwa [map_zero] at h1
    · exact eventually_nhdsWithin_of_forall fun x hx => hx
  have hLf' : IsLinAt0B U (g ∘ r R) Lf := by
    refine Tendsto.congr' ?_ hLf
    filter_upwards [ht.eventually hev] with h hh
    have h00 : fb (rB R 0) = g (r R 0) := by
      show fb (r R 0) = g (r R 0)
      rw [hr0', hfb0, hg0]
    simp only [Function.comp_apply]
    rw [h00]
    show ‖fb (r R (E.toBase 1 h)) - _ - _‖ / _ = _
    rw [hh]
  have eLf : Lf = (scDeriv U g 0).comp (scDeriv U (r R) 0) := by
    rw [← hDgr]; exact linAt0_unique hU h0 hLf' (linAt0_scDeriv hgr h0)
  subst eLr eLg eρ eLf
  set p := scDeriv U (r R) (0 : E.lvl 1)
  set L := scDeriv U g (0 : E.lvl 1)
  set q := ρCLM hR h0
  have hp : ∀ x, p (p x) = p x := scDeriv_r_idem hU hR h0O
  have hq : ∀ y, q (q y) = q y := ρCLM_idem hR h0 h0O
  have h1 : ∀ x, q (L (p x)) = L (p x) := fun x =>
    (sub_eq_zero.1 (hdcr hF' hg hg0 h0O hfK' x)).symm
  obtain ⟨Φ, hΦ⟩ := hker hF' hg hg0 h0O
  obtain ⟨hsurj, hfred, hind⟩ := hP35lin hp hq h1 Φ hΦ
  have hLfL : ∀ v ∈ rangeB p, (L.comp p) v = L v := by
    rintro v ⟨w, rfl⟩
    show L (p (p w)) = L (p w)
    rw [hp]
  refine ⟨⟨ContinuousLinearMap.ext hp, ContinuousLinearMap.ext hq⟩, ?_, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · rintro v ⟨w, rfl⟩
    exact ⟨(hLfL _ ⟨w, rfl⟩).symm, ⟨L (p w), h1 w⟩⟩
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
    have e1 : (⟨v, hv⟩ : LinearMap.ker (p : E.lvl 0 →ₗ[ℝ] E.lvl 0)) = Φ.symm (Φ ⟨v, hv⟩) :=
      (Φ.symm_apply_apply _).symm
    have e2 : ‖v‖ = ‖(⟨v, hv⟩ : LinearMap.ker (p : E.lvl 0 →ₗ[ℝ] E.lvl 0))‖ := rfl
    have e3 : ‖Φ ⟨v, hv⟩‖ = ‖L v - q (L v)‖ := by rw [← hΦ ⟨v, hv⟩]; rfl
    rw [e2, e1, ← e3]
    exact Φ.symm.toContinuousLinearMap.le_opNorm _
  · rw [← hsurj]
    constructor
    · rintro H ⟨w, hw⟩
      obtain ⟨v, hv, hvw⟩ := H w hw
      refine ⟨⟨v, hv⟩, Subtype.ext ?_⟩
      rw [fillerRestrict_apply, ← hLfL v hv]
      exact hvw
    · intro H w hw
      obtain ⟨⟨v, hv⟩, hvw⟩ := H ⟨w, hw⟩
      refine ⟨v, hv, ?_⟩
      rw [hLfL v hv]
      exact congrArg Subtype.val hvw
  · intro h
    have heq : restrictB (L.comp p) (rangeB p) (rangeB q) h = fillerRestrict p q L h1 := by
      ext v
      exact hLfL v v.2
    have : CompleteSpace ↥(rangeS p) := (isClosed_range_of_idem p hp).completeSpace_coe
    have : CompleteSpace ↥(rangeS q) := (isClosed_range_of_idem q hq).completeSpace_coe
    have : CompleteSpace ↥(rangeB p) := (isClosed_range_of_idem p hp).completeSpace_coe
    have : CompleteSpace ↥(rangeB q) := (isClosed_range_of_idem q hq).completeSpace_coe
    rw [heq]
    refine ⟨?_, fun _ => ?_⟩
    · exact (fredB_iff _).trans (hfred.trans (fredB_iff _).symm)
    · exact (indexB_eq _).trans (hind.trans (indexB_eq _).symm)

#rt_check RoundTrip.V3_8.A_to_B_wholeU [Polyfold.IsFillerOf.proposition_3_1_5,
  Polyfold.proposition_3_1_5_preprint, Polyfold.StrongRetr.scDeriv_fiber_zero,
  Polyfold.IsFillerOf.deriv_comp_r_eq_zero, Polyfold.IsFillerOf.exists_kerEquiv,
  Polyfold.IsFillerOf.scDeriv_section_comp_r, Polyfold.IsScFredholm.restrict,
  Polyfold.IsFillerOf.proposition_3_1_5_sc, Polyfold.IsFillerOf.filler_condition_three_sc,
  Polyfold.IsFillerOf.proposition_3_1_5_sc_converse, Polyfold.IsFillerOf.proposition_3_1_5_sc_iff,
  Polyfold.IsFillingGerm.proposition_3_1_5, Polyfold.IsFillingGerm.exists_kerEquiv,
  Polyfold.IsFillingGerm.deriv_comp_r_eq_zero, Polyfold.IsFillingGerm.proposition_3_1_5_sc,
  Polyfold.IsFillingGerm.filler_condition_three_sc,
  Polyfold.IsFillingGerm.proposition_3_1_5_sc_converse, Polyfold.IsFillingGerm.proposition_3_1_5_sc_iff]

section GermGlue
variable {E F : ScBanach} {C U : Set (E.lvl 0)} {R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0}

/-- B's linearization at `0` is the value at `0` of any derivative of `k` on a germ `G ⊆ U`
(both are derivatives within the level `1`, which are locally the same set). -/
theorem linAt0_eq_germ (hU : IsRelOpenInQuadrant E C U) {F' : ScBanach} {G : ScNbhdGerm E C}
    (hG1 : ∀ x ∈ G.U 1, E.toBase 1 x ∈ U) {k : E.lvl 0 → F'.lvl 0}
    {L D : E.lvl 0 →L[ℝ] F'.lvl 0} (hL : IsLinAt0B U k L)
    (hD : HasFDerivWithinAt (k ∘ E.toBase 1) (D.comp (E.toBase 1)) (G.U 1) 0) : L = D := by
  have h1 := ((linAt0_iff k L).2 hL).mono fun x hx => (ScBanach.mem_lvlSet E).2 (hG1 x hx)
  have h2 := (G.uniqueDiffWithinAt hU.isPartialQuadrant.isQuadrantLike 1 (G.zero_mem 1)).eq h1 hD
  exact ContinuousLinearMap.ext_of_toBase_one fun y =>
    congrArg (fun T : E.lvl 1 →L[ℝ] F'.lvl 0 => T y) h2

/-- A bijection between kernels with a bounded inverse is a topological isomorphism. -/
theorem kerEquiv_of_bij {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (p : V →L[ℝ] V) (q : W →L[ℝ] W) (L : V →L[ℝ] W)
    (hbij : Set.BijOn L {v | p v = 0} {w | q w = 0}) (c : ℝ)
    (hc : ∀ v : V, p v = 0 → ‖v‖ ≤ c * ‖L v‖) :
    ∃ Φ : LinearMap.ker (p : V →ₗ[ℝ] V) ≃L[ℝ] LinearMap.ker (q : W →ₗ[ℝ] W),
      ∀ v, (Φ v : W) = L v := by
  have hmaps : ∀ v : LinearMap.ker (p : V →ₗ[ℝ] V), L v ∈ LinearMap.ker (q : W →ₗ[ℝ] W) :=
    fun v => hbij.1 v.2
  let φ : LinearMap.ker (p : V →ₗ[ℝ] V) →ₗ[ℝ] LinearMap.ker (q : W →ₗ[ℝ] W) :=
    ((L : V →ₗ[ℝ] W).domRestrict _).codRestrict _ hmaps
  have hφ : ∀ v, (φ v : W) = L v := fun v => rfl
  have hinj : Function.Injective φ := by
    intro v₁ v₂ heq
    have : L v₁ = L v₂ := by rw [← hφ, ← hφ, heq]
    exact Subtype.ext (hbij.2.1 v₁.2 v₂.2 this)
  have hsurj : Function.Surjective φ := by
    intro w
    obtain ⟨v, hv, hvw⟩ := hbij.2.2 w.2
    exact ⟨⟨v, hv⟩, Subtype.ext hvw⟩
  let e := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have he : ∀ v, (e v : W) = L v := fun v => rfl
  refine ⟨e.toContinuousLinearEquivOfBounds ‖L‖ c (fun v => ?_) (fun w => ?_), fun v => he v⟩
  · rw [show ‖e v‖ = ‖L v‖ from congrArg norm (he v)]
    exact L.le_opNorm _
  · have h3 := hc (e.symm w) (e.symm w).2
    have h4 : L (e.symm w) = w := by rw [← he, e.apply_symm_apply]
    rw [h4] at h3
    exact h3

end GermGlue

/-- **A ⇒ B** (the germ reading): through A's `IsFillingGerm.proposition_3_1_5` and
`IsFillingGerm.exists_kerEquiv`. -/
theorem A_to_B : A → B := by
  intro hA E F C U R hU hR h0 _ht hr0 fb g hfK hfill hfb0 Lr Lg Lf ρ₀ hLr hLg hLf hρ₀
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hP35, hker, -⟩ := hA
  have hQ := hU.isPartialQuadrant.isQuadrantLike
  have hr0' : r R 0 = 0 := hr0
  have h0O : (0 : E.lvl 0) ∈ r R '' U := ⟨0, h0, hr0⟩
  have hg0 : g 0 = 0 := by rw [← hfb0]; exact (hfill.2.1.self_of_nhds h0O).symm
  obtain ⟨⟨G, hGU, hgs⟩, h1, h2, Lr', Lk, hLr', hLk, hbij, c, hc⟩ := hfill
  obtain ⟨Dg, hDg⟩ := (hgs 1).isSc1
  have hG1 : ∀ x ∈ G.U 1, E.toBase 1 x ∈ U := fun x hx => hGU (G.toBase_mem hx)
  have hr1 : IsSc1 U (r R) := (r_isScSmooth hU hR).isSc1
  have hDk := fillDefect_isSc1GermWith hU hR h0 hGU hDg
  -- B's linearizations are the project's
  have eLr : Lr = scDeriv U (r R) 0 := linAt0_unique hU h0 hLr (linAt0_scDeriv hr1 h0)
  have eLr' : Lr' = scDeriv U (r R) 0 := linAt0_unique hU h0 hLr' (linAt0_scDeriv hr1 h0)
  have eLg : Lg = Dg 0 := linAt0_eq_germ hU hG1 hLg (hDg.hasFDerivWithinAt 0 (G.zero_mem 1))
  have eLk : Lk = fillDefectDeriv U R g Dg 0 :=
    linAt0_eq_germ hU hG1 hLk (hDk.hasFDerivWithinAt 0 (G.zero_mem 1))
  have eρ : ρ₀ = ρCLM hR h0 := ContinuousLinearMap.ext fun w => hρ₀ w
  subst eLr' eLk
  obtain ⟨Φ₀, hΦ₀⟩ := kerEquiv_of_bij (scDeriv U (r R) 0) (ρCLM hR h0) _ hbij c hc
  -- globalise the section property: `𝐟' x = ρ(x)𝐟(x)`
  let fb' : E.lvl 0 → F.lvl 0 := fun x => ρ R x (fb x)
  have hFG : IsFillingGerm hU hR h0 fb' g := by
    refine ⟨?_, h2, ⟨G, hGU, hgs, _, hDk, Φ₀, hΦ₀⟩⟩
    filter_upwards [hfK.1, h1] with x hx1 hx2 hx
    have e1 : ρ R x (fb x) = fb x := hx1 hx
    show ρ R x (fb x) = g x
    rw [e1, hx2 hx]
  have hfK' : ∀ x ∈ r R '' U, (x, fb' x) ∈ R '' (U ×ˢ univ) := by
    intro x hx
    refine ⟨(x, fb x), ⟨mem_U_of_mem_O hR hx, mem_univ _⟩, ?_⟩
    rw [apply_eq hR (mem_U_of_mem_O hR hx), r_eq_self hR hx]
  -- `Lf = D(g ∘ r)(0) = Dg(0)Dr(0)` (locality and the germ chain rule)
  have hrC : MapsTo (r R) ((ScNbhdGerm.ofSet hU.relOpen h0).U 0) C := fun u hu =>
    hU.subset_quadrant (r_mem hR hu)
  have hgr := hDg.comp_preimage hQ hU.relOpen h0 hr1 hr0' hrC
  set G' := (ScNbhdGerm.ofSet hU.relOpen h0).preimage G (hr1.isSc0.isSc0Germ hU.relOpen h0) hr0'
    hrC with hG'
  have hG'1 : ∀ x ∈ G'.U 1, E.toBase 1 x ∈ U := fun x hx => (G'.toBase_mem hx).1
  have hD1 := hgr.hasFDerivWithinAt 0 (G'.zero_mem 1)
  rw [levelMap_one_zero_of_zero hr0'] at hD1
  have hev : ∀ᶠ y in 𝓝[U] (0 : E.lvl 0), fb (r R y) = g (r R y) := by
    have hrc : Tendsto (r R) (𝓝[U] 0) (𝓝 0) := by
      have := hr1.isSc0.continuousOn_base 0 h0
      rwa [ContinuousWithinAt, hr0'] at this
    filter_upwards [hrc.eventually h1, self_mem_nhdsWithin] with y hy hyU
    exact hy ⟨y, hyU, rfl⟩
  have ht : Tendsto (E.toBase 1) (𝓝[E.toBase 1 ⁻¹' U] (0 : E.lvl 1)) (𝓝[U] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h1 : Tendsto (E.toBase 1) (𝓝[E.toBase 1 ⁻¹' U] (0 : E.lvl 1)) (𝓝 (E.toBase 1 0)) :=
        ((E.toBase 1).continuous.tendsto 0).mono_left nhdsWithin_le_nhds
      rwa [map_zero] at h1
    · exact eventually_nhdsWithin_of_forall fun x hx => hx
  have hLf' : IsLinAt0B U (g ∘ r R) Lf := by
    refine Tendsto.congr' ?_ hLf
    filter_upwards [ht.eventually hev] with h hh
    have h00 : fb (rB R 0) = g (r R 0) := by
      show fb (r R 0) = g (r R 0)
      rw [hr0', hfb0, hg0]
    simp only [Function.comp_apply]
    rw [h00]
    show ‖fb (r R (E.toBase 1 h)) - _ - _‖ / _ = _
    rw [hh]
  have eLf : Lf = (Dg 0).comp (scDeriv U (r R) 0) := linAt0_eq_germ hU hG'1 hLf' hD1
  subst eLr eLg eρ eLf
  set p := scDeriv U (r R) (0 : E.lvl 1)
  set L := Dg 0
  set q := ρCLM hR h0
  -- A's germ Proposition 3.5 and kernel isomorphism
  obtain ⟨hq1, hsurj, hfred, hind⟩ := hP35 hU hR h0 hFG hg0 h0O hfK' hGU hDg
  obtain ⟨Φ, hΦ⟩ := hker hU hR h0 hFG hg0 h0O hDg
  have hp : ∀ x, p (p x) = p x := scDeriv_r_idem hU hR h0O
  have hq : ∀ y, q (q y) = q y := ρCLM_idem hR h0 h0O
  have hLfL : ∀ v ∈ rangeB p, (L.comp p) v = L v := by
    rintro v ⟨w, rfl⟩
    show L (p (p w)) = L (p w)
    rw [hp]
  refine ⟨⟨ContinuousLinearMap.ext hp, ContinuousLinearMap.ext hq⟩, ?_, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · rintro v ⟨w, rfl⟩
    exact ⟨(hLfL _ ⟨w, rfl⟩).symm, ⟨L (p w), hq1 w⟩⟩
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
    have e1 : (⟨v, hv⟩ : LinearMap.ker (p : E.lvl 0 →ₗ[ℝ] E.lvl 0)) = Φ.symm (Φ ⟨v, hv⟩) :=
      (Φ.symm_apply_apply _).symm
    have e2 : ‖v‖ = ‖(⟨v, hv⟩ : LinearMap.ker (p : E.lvl 0 →ₗ[ℝ] E.lvl 0))‖ := rfl
    have e3 : ‖Φ ⟨v, hv⟩‖ = ‖L v - q (L v)‖ := by rw [← hΦ ⟨v, hv⟩]; rfl
    rw [e2, e1, ← e3]
    exact Φ.symm.toContinuousLinearMap.le_opNorm _
  · rw [← hsurj]
    constructor
    · rintro H ⟨w, hw⟩
      obtain ⟨v, hv, hvw⟩ := H w hw
      refine ⟨⟨v, hv⟩, Subtype.ext ?_⟩
      rw [fillerRestrict_apply, ← hLfL v hv]
      exact hvw
    · intro H w hw
      obtain ⟨⟨v, hv⟩, hvw⟩ := H ⟨w, hw⟩
      refine ⟨v, hv, ?_⟩
      rw [hLfL v hv]
      exact congrArg Subtype.val hvw
  · intro h
    have heq : restrictB (L.comp p) (rangeB p) (rangeB q) h = fillerRestrict p q L hq1 := by
      ext v
      exact hLfL v v.2
    have : CompleteSpace ↥(rangeS p) := (isClosed_range_of_idem p hp).completeSpace_coe
    have : CompleteSpace ↥(rangeS q) := (isClosed_range_of_idem q hq).completeSpace_coe
    have : CompleteSpace ↥(rangeB p) := (isClosed_range_of_idem p hp).completeSpace_coe
    have : CompleteSpace ↥(rangeB q) := (isClosed_range_of_idem q hq).completeSpace_coe
    rw [heq]
    refine ⟨?_, fun _ => ?_⟩
    · exact (fredB_iff _).trans (hfred.trans (fredB_iff _).symm)
    · exact (indexB_eq _).trans (hind.trans (indexB_eq _).symm)

#rt_check RoundTrip.V3_8.A_to_B [Polyfold.IsFillerOf.proposition_3_1_5,
  Polyfold.proposition_3_1_5_preprint, Polyfold.StrongRetr.scDeriv_fiber_zero,
  Polyfold.IsFillerOf.deriv_comp_r_eq_zero, Polyfold.IsFillerOf.exists_kerEquiv,
  Polyfold.IsFillerOf.scDeriv_section_comp_r, Polyfold.IsScFredholm.restrict,
  Polyfold.IsFillerOf.proposition_3_1_5_sc, Polyfold.IsFillerOf.filler_condition_three_sc,
  Polyfold.IsFillerOf.proposition_3_1_5_sc_converse, Polyfold.IsFillerOf.proposition_3_1_5_sc_iff,
  Polyfold.IsFillingGerm.proposition_3_1_5, Polyfold.IsFillingGerm.exists_kerEquiv,
  Polyfold.IsFillingGerm.deriv_comp_r_eq_zero, Polyfold.IsFillingGerm.proposition_3_1_5_sc,
  Polyfold.IsFillingGerm.filler_condition_three_sc,
  Polyfold.IsFillingGerm.proposition_3_1_5_sc_converse, Polyfold.IsFillingGerm.proposition_3_1_5_sc_iff]

end RoundTrip.V3_8
