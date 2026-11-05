import Polyfold.Chapter3.RestrictOpenGerms

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6, Theorem
3.54, and §6.1, the proof of Proposition 6.2 ("we do not need a sc-smooth partition of unity",
p. 202): the local constancy of the Fredholm index along the zero set of an sc-Fredholm section
with tame germ data, **without bump functions**.  Round-trip item V3.98 (b); Findings, Chapter 3,
items 360–369.

# The index along the zero set, without bump functions

## The text, paraphrased

To stabilize `f` at a zero `x₀` the text adds finitely many sc⁺-sections `sᵢ` with `sᵢ(x₀) = eᵢ`,
taken in a chart as `sᵢ(y) = R(y, eᵢ)` ("locally defined sc⁺-sections"), so that the
linearization of `F(λ, x) = f(x) + Σ λᵢ sᵢ(x)` is onto in good position at `(0, x₀)`; the implicit
function theorem then gives the local constancy of the index along the zero set.  No partition
of unity enters, since everything happens on the domain `V` of the chart.

## What is formalized

* `Polyfold.StrongBundle.HasScPlusSectionsThrough B`: **through every smooth point `e` of a fibre
  over a smooth point there is an sc⁺-section** (the conclusion of Lemma 5.11 without the support
  and the norm bound).  Two sources: `MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough`
  (Lemma 5.11) and `StrongBundle.hasScPlusSectionsThrough_of_chart` (**a strong bundle with a
  chart of the atlas whose base domain is the whole base**: the section `y ↦ Φ⁻¹(φ(y), R(φ(y), ê))`
  needs no cut-off).  The restriction `P|V` to a chart domain `V` has such a chart.
* `Polyfold.exists_spanning_sections_of_sections`, `exists_sections_isParamGP_of_sections`,
  `index_locally_constant_of_sections`: the stabilization and the local constancy of
  `IndexLocallyConstantG.lean`, with the bump functions replaced by `HasScPlusSectionsThrough`
  (the proofs are those of `exists_spanning_sections_germ`, `exists_sections_isParamGP_germ`,
  `index_locally_constant_of_admitsBumpFunctions`; the rescaling of the sections by the
  auxiliary norm is dropped).
* `Polyfold.index_locally_constant_tame` (**Theorem 3.54 / Proposition 6.2 along the zero set,
  with the text's hypotheses**): for an sc-Fredholm section `f` with tame germ data on any strong
  bundle and a zero `x₀`, there are an open `V ∋ x₀` and `i ∈ ℤ` with `f'(y)` Fredholm of index
  `i` in every chart at every zero `y ∈ V`.  Proof: the text's, on the restriction `P|V` to a
  chart domain (`RestrictOpen.lean`): `f|V` has tame germ data, `P|V` has sc⁺-sections through
  every smooth fibre point, `index_locally_constant_of_sections` on `P|V`, and the index is the
  same on `P` and `P|V` (`IsLinOfIndex.of_restrictOpen`).
  `theorem_3_54_index_locally_constant_general_tame` is its sc form.

## What the text leaves implicit, and the choices made

* The three copied proofs differ from the originals only in the source of the sections through
  the fibre points `eᵢ` (`HasScPlusSectionsThrough` in place of Lemma 5.11) and in dropping the
  support and norm bounds of the conclusions, which the index argument does not use.
* The text works in one chart throughout; here the chart domain `V` is made a strong bundle
  `P|V` in its own right so that Theorem 3.18 and the implicit function theorem (Theorem 3.54) can
  be applied verbatim, and the index is transported back through the germ datum
  (`RestrictOpenGerms.lean`).
-/

open Set Filter Topology Function Module ContinuousLinearMap
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

/-! ### Sections through the smooth fibre points -/

section Through

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

open StrongRetr

variable (B) in
/-- **Sc⁺-sections through the smooth fibre points** (the conclusion of Lemma 5.11 without
support and norm bound): for every smooth point `x` and every smooth point `e` of the fibre
`P⁻¹(x)` there is an sc⁺-section `s` with `s(x) = e`. -/
def StrongBundle.HasScPlusSectionsThrough : Prop :=
  ∀ x ∈ PX.smoothSet, ∀ e ∈ B.toMPolyfold0.smoothSet, P e = x →
    ∃ s : X → Y, B.IsScPlusSection s ∧ s x = e

/-- With bump functions, sc⁺-sections exist through every smooth fibre point (Lemma 5.11). -/
theorem MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough (hbump : PX.AdmitsBumpFunctions) :
    B.HasScPlusSectionsThrough := by
  intro x hx e he hex
  obtain ⟨N, hN⟩ := proposition_5_3_exists (B := B)
  obtain ⟨-, s, hs, hsx, -, -⟩ := lemma_5_11 hbump hN hx he hex one_pos isOpen_univ (mem_univ x)
  exact ⟨s, hs, hsx⟩

/-- **A strong bundle with a chart of the atlas over the whole base has sc⁺-sections through
every smooth fibre point, without bump functions**: the section `y ↦ Φ⁻¹(φ(y), R(φ(y), ê))`,
`ê = Φ(e)₂ ∈ F_∞`, is the text's `R(·, e)` (the proof of Lemma 5.11 with the cut-off `β = 1`;
`cutoffSection` with `β = 1`, `isScPlusSection_cutoffSection`). -/
theorem StrongBundle.hasScPlusSectionsThrough_of_chart {c : StrongBundleChart PX P}
    (hc : c ∈ B.atlas.charts) (hsrc : c.φ.source = univ) : B.HasScPlusSectionsThrough := by
  intro x _ e he hex
  have hxc : x ∈ c.φ.source := hsrc ▸ mem_univ x
  have hR := c.isRetraction
  have hPex : P e ∈ c.φ.source := by rw [hex]; exact hxc
  have hes : e ∈ c.toPartialEquiv.source := c.mem_source_of_proj hPex
  have hce : c e = (c.φ x, (c e).2) := Prod.ext (by rw [c.fst_apply hPex, hex]) rfl
  -- `ê = Φ(e)₂` is a smooth point of `F`
  have hsm : (c e).2 ∈ c.F.smooth := by
    refine c.F.mem_smooth_iff.2 fun m => ?_
    have hm : e ∈ B.toMPolyfold0.levelSet m := mem_iInter.1 he m
    rw [B.toMPolyfold0.mem_levelSet_iff (B.isChart_toMChart hc) hes] at hm
    obtain ⟨w, hw⟩ := hm
    have h2 := ScBanach.prod_toBase c.φ.model.E c.F m w
    have h3 : c e = _ := hw.symm.trans h2
    exact ⟨w.2, (congrArg Prod.snd h3).symm⟩
  set ê₁ : c.F 1 := Function.invFun (c.F.toBase 1) (c e).2 with hê₁def
  have hê₁ : c.F.toBase 1 ê₁ = (c e).2 := Function.invFun_eq (c.F.mem_smooth_iff.1 hsm 1)
  have hê₁s : ê₁ ∈ c.F.shift.smooth := by
    have h1 : ê₁ ∈ c.F.smoothLvl 1 := by
      change c.F.toBase 1 ê₁ ∈ c.F.smooth; rw [hê₁]; exact hsm
    rw [← c.F.shift_smoothLvl 0] at h1
    exact h1
  -- the local section `t(y) = R(φ(y), ê)`, principal part `τ`
  set τ : c.φ.model.E 0 → c.F 1 := fun z => (shiftFiber c.R (z, ê₁)).2 with hτdef
  have hOU : ∀ z ∈ c.φ.model.O, z ∈ c.U := fun z hz =>
    (hR.baseRetraction c.relOpen).retract_subset (by rw [c.base_retract]; exact hz)
  have hshift : ∀ z ∈ c.φ.model.O, shiftFiber c.R (z, ê₁) = (z, τ z) := fun z hz => by
    refine Prod.ext ?_ rfl
    change (c.R (z, c.F.toBase 1 ê₁)).1 = z
    rw [hR.apply_fst (hOU z hz)]
    exact (hR.baseRetraction c.relOpen).apply_eq_self_of_mem_retract
      (by rw [c.base_retract]; exact hz)
  have hτι : ∀ z ∈ c.φ.model.O, c.F.toBase 1 (τ z) = (c.R (z, (c e).2)).2 := fun z hz => by
    rw [← hê₁]; exact hR.toBase_shiftFiber_snd (p := (z, ê₁)) (hOU z hz)
  have hτ : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O
      (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ) (strongShiftOne c.K)
      (fun z => (z, τ z)) := by
    refine ⟨fun z hz => ?_, fun R' hR' => ?_⟩
    · change (z, τ z) ∈ strongShiftOne c.K
      rw [← hshift z hz]
      have := (hR.toScRetractionOne c.relOpen).apply_mem_retract
        (show ((z, ê₁) : (c.φ.model.E.prod c.F.shift) 0) ∈ c.U ×ˢ univ from ⟨hOU z hz, mem_univ _⟩)
      rw [hR.toScRetractionOne_retract c.relOpen] at this
      exact this
    · have hU' := R'.isScDomain
      have hRO : ∀ u ∈ R'.U, R' u ∈ c.φ.model.O := fun u hu => hR' ▸ R'.apply_mem_retract hu
      have hpair := R'.isScSmooth.scPair hU' (isScSmooth_const_of_mem_smooth hU' hê₁s)
      have hcomp := IsScSmooth.comp hU' (c.relOpen.prod_univ c.F.shift).isScDomain
        hR.isScSmooth_one hpair fun u hu => ⟨hOU _ (hRO u hu), mem_univ _⟩
      exact hcomp.congr hU' fun u hu => hshift _ (hRO u hu)
  have hτm := hτ.mapsTo
  have hRce : c.R (c e) = c e := by
    obtain ⟨q, hq, hqe⟩ : c e ∈ c.K := by rw [← c.image_source]; exact ⟨e, hes, rfl⟩
    rw [← hqe, hR.idem q hq]
  have hτx : c.F.toBase 1 (τ (c.φ x)) = (c e).2 := by
    rw [hτι _ (c.φ.mapsTo_model x hxc)]
    conv_rhs => rw [← hRce]
    rw [← hce]
  refine ⟨StrongBundle.cutoffSection c (fun _ => (1 : ℝ)) τ,
    StrongBundle.isScPlusSection_cutoffSection hc (isScSmoothMap_real_const 1)
      (by rw [hsrc]; exact subset_univ _) hτ, ?_⟩
  refine c.toPartialEquiv.injOn (StrongBundle.cutoffSection_mem_source hτm hxc) hes ?_
  rw [StrongBundle.apply_cutoffSection hτm hxc]
  simp only [one_smul]
  rw [hτx, ← hce]

end Through

/-! ### The stabilizing sections, from `HasScPlusSectionsThrough` -/

section SpanningLocal

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

open StrongRetr

/-- **Spanning sc⁺-sections at a zero, from sections through the fibre points** (the proof of
`exists_spanning_sections_germ` with `HasScPlusSectionsThrough` in place of Lemma 5.11 and
without the rescaling by an auxiliary norm): for an sc-Fredholm section `g` and a zero `y`,
finitely many sc⁺-sections `s₁, …, s_k` and a chart `c` centred at `y` with
`Lin(0)(T₀O) + span{ŝᵢ(0)} = K₀`. -/
theorem exists_spanning_sections_of_sections (hsec : B.HasScPlusSectionsThrough) {g : X → Y}
    (hg : B.IsScFredholmSection g) {y : X} (hy0 : IsZeroAt P g y) :
    ∃ (k : ℕ) (s : Fin k → X → Y), (∀ i, B.IsScPlusSection (s i)) ∧
      ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : y ∈ c.φ.source) (_ : c.φ y = 0),
        ∀ k', ((0 : c.φ.model.E 0), k') ∈ c.K →
          ∃ (u : ↥(rangeS (scDeriv c.U (r c.R) 0))) (a : Fin k → ℝ),
            linAt c.U c.R (c.principal g) 0 u + ∑ i, a i • c.principal (s i) 0 = k' := by
  classical
  have hgs : IsSection P g := hg.isScSmooth.1
  have hys : y ∈ PX.smoothSet := hg.mem_smoothSet_of_isZeroAt hy0
  obtain ⟨c, hc, hyV, hφ0, h0U, gf, hfill, G, -, -, Dg, hDg, h1, n, Nn, -, -, hFred, -⟩ :=
    proposition_3_52 hgs (hg.germ y hys) hy0
  have h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := by
    rw [c.r_image, ← hφ0]; exact c.φ.mapsTo_model y hyV
  have hfr : IsSc1 c.U (c.principal g ∘ r c.R) := hg.isScSmooth.isSc1_principal_comp_r hc
  set L := fillerRestrict (scDeriv c.U (r c.R) 0) (ρCLM c.isRetraction h0U) (Dg 0) h1
    with hLdef
  have hL : ∀ x, (L x : c.F 0) = linAt c.U c.R (c.principal g) 0 x := fun x =>
    hfill.fillerRestrict_eq_linAt c.relOpen c.isRetraction h0O hfr hDg h1 x
  have : CompleteSpace ↥(rangeS (ρCLM c.isRetraction h0U)) :=
    (isClosed_range_of_idem _ fun k => ρ_ρ c.isRetraction h0O k).completeSpace_coe
  -- the smooth vectors of `K₀` are dense
  have hρsm : ∀ h ∈ c.F.smooth, ρCLM c.isRetraction h0U h ∈ c.F.smooth := by
    intro h hh
    refine c.F.mem_smooth_iff.2 fun m => ?_
    obtain ⟨h', hh'⟩ := c.F.mem_smooth_iff.1 hh m
    exact (c.isRetraction.preserves_filtration m m (Nat.le_succ m) 0 h0U ⟨0, map_zero _⟩ h
      ⟨h', hh'⟩).2
  set D : Submodule ℝ ↥(rangeS (ρCLM c.isRetraction h0U)) :=
    c.F.smooth.comap (rangeS (ρCLM c.isRetraction h0U)).subtype with hDdef
  have hD : Dense (D : Set ↥(rangeS (ρCLM c.isRetraction h0U))) := by
    set ρ' : c.F 0 → ↥(rangeS (ρCLM c.isRetraction h0U)) :=
      fun h => ⟨ρCLM c.isRetraction h0U h, ⟨h, rfl⟩⟩ with hρ'
    have hcont : Continuous ρ' := (ρCLM c.isRetraction h0U).continuous.subtype_mk _
    have hdr : DenseRange ρ' := by
      refine Function.Surjective.denseRange ?_
      rintro ⟨k, k', hk'⟩
      exact ⟨k', Subtype.ext hk'⟩
    have hsm : Dense (c.F.smooth : Set (c.F 0)) := c.F.dense_smooth 0
    refine (hdr.dense_image hcont hsm).mono ?_
    rintro _ ⟨h, hh, rfl⟩
    exact hρsm h hh
  obtain ⟨k, d, hdD, hspan⟩ := exists_fin_mem_of_dense_of_closedComplemented
    hFred.closedComplemented_range hFred.finite_coker hD
  -- the vectors `eᵢ = dᵢ ∈ K₀ ∩ F_∞` as smooth points of `Y`
  have hdK : ∀ i, ((0 : c.φ.model.E 0), (d i : c.F 0)) ∈ c.K := fun i =>
    (mem_rangeS_ρCLM_iff c.isRetraction h0O h0U).1 (d i).2
  have hdsm : ∀ i, (d i : c.F 0) ∈ c.F.smooth := fun i => hdD i
  have hφsymm0 : c.φ.symm 0 = y := by rw [← hφ0]; exact c.φ.symm_apply_apply hyV
  set e : Fin k → Y := fun i => c.toPartialEquiv.symm (0, (d i : c.F 0)) with hedef
  have hPe : ∀ i, P (e i) = y := fun i => by
    change P (c.toPartialEquiv.symm (0, (d i : c.F 0))) = y
    rw [c.proj_symm (hdK i)]; exact hφsymm0
  have hesm : ∀ i, e i ∈ B.toMPolyfold0.smoothSet := fun i =>
    mem_smoothSet_toMPolyfold0_of_chart hc (hdK i) c.φ.model.E.smooth.zero_mem (hdsm i)
  -- a section through each `eᵢ`
  choose s hs hsy using fun i => hsec y hys (e i) (hesm i) (hPe i)
  refine ⟨k, s, hs, c, hc, hyV, hφ0, fun k' hk' => ?_⟩
  -- the spanning
  have hk'K : k' ∈ rangeS (ρCLM c.isRetraction h0U) :=
    (mem_rangeS_ρCLM_iff c.isRetraction h0O h0U).2 hk'
  obtain ⟨rr, hrr, a, hk'eq⟩ := hspan ⟨k', hk'K⟩
  obtain ⟨u, hu⟩ := LinearMap.mem_range.1 hrr
  refine ⟨u, a, ?_⟩
  have hprin : ∀ i, c.principal (s i) 0 = (d i : c.F 0) := fun i => by
    unfold StrongBundleChart.principal
    rw [hφsymm0, hsy i]
    change (c (c.toPartialEquiv.symm (0, (d i : c.F 0)))).2 = _
    rw [c.apply_symm (hdK i)]
  have hval : k' = (rr : c.F 0) + ∑ i, a i • (d i : c.F 0) := by
    have := congrArg Subtype.val hk'eq
    simpa using this
  have hu' : (rr : c.F 0) = linAt c.U c.R (c.principal g) 0 u := by
    rw [← hu]; exact hL u
  rw [hval, hu']
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [hprin i]


end SpanningLocal

section ConstructionLocal

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {g : X → Y}

open StrongRetr

set_option maxHeartbeats 3200000 in
-- the coordinates of the tame chart and Lemma 5.11 at finitely many points
/-- **Sections with (i)–(ii) at a zero, from sections through the fibre points** (the proof of
`exists_sections_isParamGP_germ` with `HasScPlusSectionsThrough` in place of Lemma 5.11, and
without support and norm bounds): for `g` with tame germ data, a zero `x` and a tame chart `c`
centred at `x` with presentation `T`, finitely many sc⁺-sections with (i)–(ii) at `(0, x)` in `c`
(`IsParamGP`). -/
theorem exists_sections_isParamGP_of_sections (hsec : B.HasScPlusSectionsThrough)
    (hgFt : B.IsScFredholmSectionTame g) {x : X} (hx0 : IsZeroAt P g x)
    {c : StrongBundleChart PX P} (hc : B.IsTameChart c) (hxV : x ∈ c.φ.source)
    (hφ0 : c.φ x = 0) {n : ℕ} {Wq : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0) :
    ∃ (k : ℕ) (s : Fin k → X → Y) (_ : ∀ i, B.IsScPlusSection (s i)), c.IsParamGP g s T := by
  classical
  have hgF := hgFt.toIsScFredholmSection
  have hxs : x ∈ PX.smoothSet := hgF.mem_smoothSet_of_isZeroAt hx0
  -- (i): the spanning sections, read in `c`
  obtain ⟨k₁, s₁, hs₁, c₁, hc₁, hxV₁, hφ₁, hspan₁⟩ :=
    exists_spanning_sections_of_sections hsec hgF hx0
  have := MPolyfold.paracompactSpace_prod (rnPolyfold k₁) PX
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin k₁ → ℝ) × X → X))
    ((rnPolyfold k₁).prod PX) B
  have hsurj₁ := isLinSurjAt_paramSection_zero_of_spanning_germ hgF hs₁ hc₁ hxV₁ hφ₁
    (paramSection g hgF.isScSmooth.1 s₁ (fun i => (hs₁ i).1) (0, x)) hspan₁
  have hspan := spanning_of_isLinSurjAt_germ hgF hs₁ hx0 hc.1 hxV hφ0 hsurj₁
  -- (ii): the coordinates of the tame chart
  set R := c.isRetraction.baseRetraction c.relOpen with hRdef
  have hRT : R.IsTameWith T := hc.2 n Wq T hT
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model x hxV
  have h0O' : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := c.r_image ▸ h0O
  have h0U : (0 : c.φ.model.E 0) ∈ c.U := mem_U_of_mem_O c.isRetraction h0O'
  have hz : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = c.φ x := by rw [map_zero, hφ0]
  have hzR : (0 : c.φ.model.E 1) ∈ c.φ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, c.base_retract, hz]; exact c.φ.mapsTo_model x hxV
  have hzs : (0 : c.φ.model.E 1) ∈ c.φ.model.E.smoothLvl 1 := by
    change c.φ.model.E.toBase 1 0 ∈ c.φ.model.E.smooth
    rw [map_zero]; exact c.φ.model.E.smooth.zero_mem
  set e := c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) with he
  have he0 : e = 0 := map_zero _
  set M := LinearMap.range (scDeriv R.U R 0 : c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) with hMdef
  set I := {i : Fin n // (T 0 e).1 i = 0} with hIdef
  set f : M →ₗ[ℝ] (I → ℝ) := (coordMapL T e : c.φ.model.E 0 →ₗ[ℝ] (I → ℝ)) ∘ₗ M.subtype
    with hf
  have hker : LinearMap.ker f = (reducedTangentSpaceWith R T 0).comap M.subtype := by
    ext ⟨v, hv⟩
    simp only [hf, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype,
      Submodule.mem_comap, reducedTangentSpaceWith, Submodule.mem_inf]
    exact ⟨fun h => ⟨hv, h⟩, fun h => h.2⟩
  have hq := quotDim_reducedTangentSpaceWith_eq hRT hzR hzs
  rw [quotDim, ← hker] at hq
  have hrange : LinearMap.range f = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← (LinearMap.quotKerEquivRange f).finrank_eq, hq, Module.finrank_fintype_fun_eq_card,
      Fintype.card_subtype]
    rfl
  -- smooth preimages
  obtain ⟨hMsc, -, -⟩ := proposition_2_36_partialCone hT hRT hzR hzs
  set D : Submodule ℝ (c.φ.model.E 0) := M ⊓ c.φ.model.E.smooth with hD
  set S : Submodule ℝ (I → ℝ) := D.map (coordMapL T e : c.φ.model.E 0 →ₗ[ℝ] (I → ℝ)) with hS
  have hSclosed : IsClosed (S : Set (I → ℝ)) := S.closed_of_finiteDimensional
  have hpre : ∀ v : I → ℝ, ∃ l ∈ D, coordMapL T e l = v := by
    intro v
    have hv : v ∈ LinearMap.range f := by rw [hrange]; exact Submodule.mem_top
    obtain ⟨⟨w, hwM⟩, hwv⟩ := hv
    have hwcl : w ∈ closure ((M : Set (c.φ.model.E 0)) ∩ c.φ.model.E.smoothLvl 0) := by
      have := hMsc.2 0 (show w ∈ c.φ.model.E.levelSub M 0 by
        rw [ScBanach.levelSub_zero]; exact hwM)
      rwa [ScBanach.levelSub_zero] at this
    have hvS : v ∈ S := by
      have h1 : coordMapL T e w ∈ closure ((coordMapL T e) ''
          ((M : Set (c.φ.model.E 0)) ∩ c.φ.model.E.smoothLvl 0)) :=
        image_closure_subset_closure_image (coordMapL T e).continuous ⟨w, hwcl, rfl⟩
      have h2 : closure ((coordMapL T e) ''
          ((M : Set (c.φ.model.E 0)) ∩ c.φ.model.E.smoothLvl 0)) ⊆ (S : Set (I → ℝ)) := by
        refine closure_minimal ?_ hSclosed
        rintro _ ⟨l, ⟨hlM, hls⟩, rfl⟩
        exact ⟨l, ⟨hlM, hls⟩, rfl⟩
      have h3 := h2 h1
      rwa [← hwv]
    obtain ⟨l, hlD, hl⟩ := hvS
    exact ⟨l, hlD, hl⟩
  choose l hlD hlv using fun i : I => hpre (Pi.single i 1)
  -- the smooth fibre points `Φ⁻¹(0, Lin_g(0) lᵢ)`
  have hgr : IsScSmooth c.U (c.principal g ∘ r c.R) :=
    (((hgF.isScSmooth.isScSmoothRetractMap hc.1).comp_isScSmooth
      (c.isRetraction.baseRetraction c.relOpen) c.base_retract).snd c.relOpen.isScDomain).congr
      c.relOpen.isScDomain fun _ _ => rfl
  have hz1U : (0 : c.φ.model.E 1) ∈ c.φ.model.E.lvlSet c.U 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0U
  have hop := hgr.isSc1.isSc1With_scDeriv.scOperator_deriv hz1U hzs
  set d : I → c.F 0 := fun i => linAt c.U c.R (c.principal g) 0 ⟨l i, (hlD i).1⟩ with hd
  have hdK : ∀ i, ((0 : c.φ.model.E 0), d i) ∈ c.K := fun i => by
    have hzO : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ r c.R '' c.U := by
      rw [map_zero]; exact h0O'
    have hmem := rho_scDeriv_comp_r c.relOpen c.isRetraction
      (hgF.isScSmooth.isSc1_principal_comp_r hc.1)
      (fun x hx => c.principal_mem_K hgF.isScSmooth.1 (c.r_image ▸ hx)) hzO
      (by rw [map_zero, ← hφ0]; exact (c.isZeroAt_iff hgF.isScSmooth.1 hxV).1 hx0) (l i)
    have hzU : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ c.U := by rw [map_zero]; exact h0U
    have : d i ∈ rangeS (ρCLM c.isRetraction hzU) := ⟨_, hmem⟩
    have h2 := (mem_rangeS_ρCLM_iff c.isRetraction hzO hzU).1 this
    rwa [map_zero] at h2
  have hdsm : ∀ i, d i ∈ c.F.smooth := fun i => by
    refine c.F.mem_smooth_iff.2 fun j => ?_
    obtain ⟨Tj, hTj⟩ := hop j
    obtain ⟨lj, hlj⟩ := c.φ.model.E.mem_smooth_iff.1 (hlD i).2 j
    exact ⟨Tj lj, by rw [hTj, hlj]; rfl⟩
  have hφsymm0 : c.φ.symm 0 = x := by rw [← hφ0]; exact c.φ.symm_apply_apply hxV
  set ef : I → Y := fun i => c.toPartialEquiv.symm (0, d i) with hefdef
  have hPe : ∀ i, P (ef i) = x := fun i => by
    change P (c.toPartialEquiv.symm (0, d i)) = x
    rw [c.proj_symm (hdK i)]; exact hφsymm0
  have hesm : ∀ i, ef i ∈ B.toMPolyfold0.smoothSet := fun i =>
    mem_smoothSet_toMPolyfold0_of_chart hc.1 (hdK i) c.φ.model.E.smooth.zero_mem (hdsm i)
  -- a section through each point
  choose s₂' hs₂'p hs₂x using fun i => hsec x hxs (ef i) (hesm i) (hPe i)
  have hprin : ∀ i, c.principal (s₂' i) 0 = d i := fun i => by
    unfold StrongBundleChart.principal
    rw [hφsymm0, hs₂x i]
    change (c (c.toPartialEquiv.symm (0, d i))).2 = _
    rw [c.apply_symm (hdK i)]
  -- the united family on `Fin (k₁ + k₂)`
  set k₂ := Fintype.card I with hk₂
  set eI := Fintype.equivFin I with heI
  set s : Fin (k₁ + k₂) → X → Y := Fin.append s₁ (fun j => s₂' (eI.symm j)) with hsdef
  have hsl : ∀ i, s (Fin.castAdd k₂ i) = s₁ i := fun i => Fin.append_left _ _ i
  have hsr : ∀ j, s (Fin.natAdd k₁ (eI j)) = s₂' j := fun j => by
    rw [hsdef, Fin.append_right, Equiv.symm_apply_apply]
  have hsp : ∀ i, B.IsScPlusSection (s i) := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_)
    · rw [hsl]; exact hs₁ i
    · rw [show Fin.natAdd k₁ j = Fin.natAdd k₁ (eI (eI.symm j)) by rw [Equiv.apply_symm_apply],
        hsr]
      exact hs₂'p _
  refine ⟨k₁ + k₂, s, hsp, ?_, ?_⟩
  · -- (i)
    intro k' hk'
    obtain ⟨u, a, hua⟩ := hspan k' hk'
    obtain ⟨a', ha'⟩ := exists_sum_comp_eq (Fin.castAdd k₂) a fun j => c.principal (s j) 0
    refine ⟨u, a', ?_⟩
    rw [ha', ← hua]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [hsl]
  · -- (ii)
    intro w
    set cw : I → ℝ := coordMapL T e w with hcw
    have hlM : ∀ i, l i ∈ M := fun i => (hlD i).1
    set u : ↥(rangeS (scDeriv c.U (r c.R) 0)) :=
      ⟨∑ i, cw i • l i, M.sum_mem fun i _ => M.smul_mem _ (hlM i)⟩ with hu
    have hLu : linAt c.U c.R (c.principal g) 0 u = ∑ i, cw i • d i := by
      have : u = ∑ i, cw i • (⟨l i, hlM i⟩ : ↥(rangeS (scDeriv c.U (r c.R) 0))) := by
        apply Subtype.ext; simp [hu]
      rw [this, map_sum]
      simp only [map_smul]
      rfl
    have hcoord : coordMapL T e (∑ i, cw i • l i) = cw := by
      rw [map_sum]
      simp only [map_smul, hlv]
      ext i
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero]
      rw [Finset.sum_eq_single i (fun b _ hb => if_neg (Ne.symm hb))
        (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]
    obtain ⟨a', ha'⟩ := exists_sum_comp_eq (fun i => Fin.natAdd k₁ (eI i))
      (fun i => -(cw i)) fun j => c.principal (s j) 0
    refine ⟨u, a', ?_, ?_⟩
    · rw [ha', hLu]
      simp only [hsr, hprin, neg_smul, Finset.sum_neg_distrib]
      rw [← sub_eq_add_neg, sub_self]
    · have hc0 : coordMapL T e ((w : c.φ.model.E 0) - (u : c.φ.model.E 0)) = 0 := by
        rw [map_sub]
        change cw - coordMapL T e (∑ i, cw i • l i) = 0
        rw [hcoord, sub_self]
      rw [← he0, mem_minimalSubspaceWith]
      intro i hi
      have := congrFun hc0 ⟨i, hi⟩
      rwa [coordMapL_apply] at this



end ConstructionLocal

/-! ### The index along the zero set -/

section IndexLocal

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

/-- **The index is locally constant along the zero set, from sections through the fibre
points** (the proof of `index_locally_constant_of_admitsBumpFunctions` with
`HasScPlusSectionsThrough` in place of the bump functions): for `f` with tame germ data and a
zero `x₀`, an open `V ∋ x₀` and `i ∈ ℤ` with `f'(y)` Fredholm of index `i` in every chart at every
zero `y ∈ V`. -/
theorem index_locally_constant_of_sections (hsec : B.HasScPlusSectionsThrough)
    (hf : B.IsScFredholmSectionTame f) {x₀ : X} (hx₀ : IsZeroAt P f x₀) :
    ∃ (V : Set X) (i : ℤ), IsOpen V ∧ x₀ ∈ V ∧ ∀ y ∈ V, IsZeroAt P f y → B.IsLinOfIndex f y i := by
  classical
  have hfF := hf.toIsScFredholmSection
  have hxs : x₀ ∈ PX.smoothSet := hfF.mem_smoothSet_of_isZeroAt hx₀
  obtain ⟨-, c, hc, hxV, hφ0, -⟩ := hf.germTame x₀ hxs
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  obtain ⟨k, s, hsp, hgp⟩ := exists_sections_isParamGP_of_sections hsec hf hx₀ hc hxV hφ0 T hT
  have := MPolyfold.paracompactSpace_prod (rnPolyfold k) PX
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin k → ℝ) × X → X))
    ((rnPolyfold k).prod PX) B
  have hFt := theorem_3_18_tame hf hsp
  set F := paramSection f hf.isScSmooth.1 s (fun i => (hsp i).1) with hFdef
  have hz0 : ∀ y, IsZeroAt P f y → IsZeroAt (pullbackProj P Prod.snd) F (0, y) := fun y hy => by
    rw [hFdef, isZeroAt_paramSection_iff]
    change IsZeroAt P (paramSlice f hf.isScSmooth.1 s (fun i => (hsp i).1) 0) y
    rw [paramSlice_zero]; exact hy
  have hgood := isGoodPositionGermTame_paramSection_of_isParamGP hf hsp hx₀ hc hxV hφ0 T hT hgp
  obtain ⟨Vx, d, hVo, hxVx, hall⟩ :=
    theorem_3_54_index_locally_constant hFt hgood (hz0 x₀ hx₀)
  refine ⟨Prod.mk (0 : Fin k → ℝ) ⁻¹' Vx, (d : ℤ) - k,
    hVo.preimage (continuous_const.prodMk continuous_id), hxVx, fun y hy hy0 => ?_⟩
  exact StrongBundle.isLinOfIndex_of_paramSection_isLinOfIndex hfF hsp hy0
    (hall (0, y) hy (hz0 y hy0)).isLinOfIndex


/-- **Theorem 3.54 / Proposition 6.2 along the zero set, with the text's hypotheses** (round-trip
item V3.98 (b); the bump functions of `index_locally_constant_of_admitsBumpFunctions` removed):
let `f` be an sc-Fredholm section with tame germ data (Definition 3.51) of a strong bundle
`P : Y → X` and `x₀` a zero of `f`.  Then there are an open `V ∋ x₀` and `i ∈ ℤ` such that at every
zero `y ∈ V`, `f'(y)` is Fredholm of index `i` in every strong bundle chart (`IsLinOfIndex`).
Proof: the text's device on the restriction `P|V` to the domain `V` of a chart around `x₀`
(`StrongBundle.restrictOpen`): `f|V` has tame germ data (`IsScFredholmSectionTame.restrictOpen`),
`P|V` has sc⁺-sections through every smooth fibre point without cut-off
(`hasScPlusSectionsThrough_of_chart`, the chart `c|V` has base domain `V`), so the index of
`f|V` is locally constant along its zero set (`index_locally_constant_of_sections`), and the index
at a zero is the same on `P` and `P|V` (`IsLinOfIndex.of_restrictOpen`). -/
theorem index_locally_constant_tame (hf : B.IsScFredholmSectionTame f) {x₀ : X}
    (hx₀ : IsZeroAt P f x₀) :
    ∃ (V : Set X) (i : ℤ), IsOpen V ∧ x₀ ∈ V ∧ ∀ y ∈ V, IsZeroAt P f y → B.IsLinOfIndex f y i := by
  obtain ⟨c, hc, hxc⟩ := StrongBundle.exists_chart_mem B x₀
  have hV : IsOpen c.φ.source := c.φ.isOpen_source
  have : Nonempty c.φ.source := ⟨⟨x₀, hxc⟩⟩
  have := PX.paracompactSpace_subtype c.φ.source
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : c.φ.source → X))
    (PX.restrictOpen hV) B
  have hfs : IsSection P f := hf.isScSmooth.1
  have hfV := hf.restrictOpen hV
  set cV := c.restrictTo B.continuous hV subset_rfl (restrictSection P c.φ.source f hfs ⟨x₀, hxc⟩)
    with hcV
  have hcVmem : cV ∈ (B.restrictOpen hV).atlas.charts :=
    StrongBundle.restrictTo_mem_restrictOpen_atlas hV (B.isChart_of_mem hc) subset_rfl _
  have hsrc : cV.φ.source = univ := eq_univ_of_forall fun v => v.2
  have hsec := StrongBundle.hasScPlusSectionsThrough_of_chart hcVmem hsrc
  obtain ⟨W, i, hWo, hxW, hall⟩ := index_locally_constant_of_sections hsec hfV
    ((isZeroAt_restrictSection_iff' hfs ⟨x₀, hxc⟩).2 hx₀)
  refine ⟨Subtype.val '' W, i, hV.isOpenMap_subtype_val W hWo, ⟨⟨x₀, hxc⟩, hxW, rfl⟩, ?_⟩
  rintro _ ⟨v, hvW, rfl⟩ hy0
  exact StrongBundle.IsLinOfIndex.of_restrictOpen hV hf.toIsScFredholmSection hy0 v.2
    (hall v hvW ((isZeroAt_restrictSection_iff' hfs v).2 hy0))

/-- **The index is locally constant along the zero set, sc form, with the text's hypotheses**
(`theorem_3_54_index_locally_constant_general` without bump functions): at every zero `y ∈ V`, in
every strong bundle chart around `y`, `Lin(z) : T_zO → K_z` is an sc-Fredholm operator, Fredholm of
index `i` on every level. -/
theorem theorem_3_54_index_locally_constant_general_tame (hf : B.IsScFredholmSectionTame f)
    {x₀ : X} (hx₀ : IsZeroAt P f x₀) :
    ∃ (V : Set X) (i : ℤ), IsOpen V ∧ x₀ ∈ V ∧
      ∀ y ∈ V, IsZeroAt P f y → ∀ (c : StrongBundleChart PX P) (_ : B.IsChart c)
        (_ : y ∈ c.φ.source) (z : c.φ.model.E 1) (_ : c.φ.model.E.toBase 1 z = c.φ y)
        (hzU : c.φ.model.E.toBase 1 z ∈ c.U),
        ∃ (hD : IsScOperator (scDeriv c.U (c.principal f ∘ r c.R) z))
          (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (r c.R) z)))
          (hK : c.F.IsScSubspace (rangeS (ρCLM c.isRetraction hzU)))
          (hTK : ∀ x ∈ rangeS (scDeriv c.U (r c.R) z),
            hD.toScOperator 0 x ∈ rangeS (ρCLM c.isRetraction hzU)),
          (∀ x : (c.φ.model.E.ofSubspace hT) 0,
            ((hD.toScOperator.restrict hT hK hTK 0 x).1 : c.F 0) =
              linAt c.U c.R (c.principal f) z ⟨x.1, x.2⟩) ∧
          IsScFredholm (hD.toScOperator.restrict hT hK hTK) ∧
          ∀ m, ((hD.toScOperator.restrict hT hK hTK) m).IsFredholm ∧
            fredholmIndex ((hD.toScOperator.restrict hT hK hTK) m) = i := by
  obtain ⟨V, i, hVo, hxV, hall⟩ := index_locally_constant_tame hf hx₀
  refine ⟨V, i, hVo, hxV, fun y hy hy0 c hc hyV z hz hzU => ?_⟩
  obtain ⟨hD, hT, hK, hTK, happ, hsc, hlvl⟩ :=
    StrongBundle.linAt_isScFredholm hf.toIsScFredholmSection hy0 hc hyV hz hzU
  have hmem : ∀ x : ↥(rangeS (scDeriv c.U (r c.R) z)),
      linAt c.U c.R (c.principal f) z x ∈ rangeS (ρCLM c.isRetraction hzU) := fun x => by
    have := hTK x x.2
    rwa [hD.toScOperator_zero] at this
  obtain ⟨hLF, hLind⟩ := hall y hy hy0 c hc hyV z hz hzU
    ((linAt c.U c.R (c.principal f) z).codRestrict _ hmem) fun _ => rfl
  obtain ⟨-, hind0⟩ := hD.toScOperator.isFredholm_restrict_zero hT hK hTK
    (L := (linAt c.U c.R (c.principal f) z).codRestrict _ hmem)
    (fun x => by rw [hD.toScOperator_zero]; rfl) hLF
  refine ⟨hD, hT, hK, hTK, happ, hsc, fun m => ⟨(hlvl m).1, ?_⟩⟩
  rw [(hlvl m).2.1, hind0, hLind]

end IndexLocal

end Polyfold
