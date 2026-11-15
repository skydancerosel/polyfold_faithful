import Polyfold.Chapter15.CylinderEndBranching
import Polyfold.Chapter15.CylinderFaceOnto

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703 (proof of
**Corollary 15.4.4**; 2017: Corollary 15.2), with Definition 15.3.5 and Theorem 15.2.5.

# The sheets on an end of the cylinder as solution sets

## The text, paraphrased

Near a point `(i, x)` of an end of the cylinder `[0, 1] × X`, `x ∈ supp Θᵢ`, the sheets of
`Θ̃ = Λ̃ ∘ f̃` are `M̃ⱼ = {f̃ = s̃ⱼ}` for a local sc⁺-section structure `(s̃ⱼ, σⱼ)` of `Λ̃`.  The
sections `sⱼ = s̃ⱼ(i, ·)` are a local sc⁺-section structure of `Λᵢ` near `x`, and
`∂M̃ⱼ = {i} × Mⱼ` with `Mⱼ = {f = sⱼ}`.  As `(f̃, Λ̃)` is in general position at `(i, y)`, the
operator `(f̃ − s̃ⱼ)'(i, y)` is onto on the reduced tangent space `0 × T_yX`, where it is
`(f − sⱼ)'(y)`; so `(f − sⱼ)'(y)` is onto and `T_yMⱼ = ker (f − sⱼ)'(y)`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `minimalSubspaceWith_eq_bot_of_finrank_eq`, `minimalSubspaceWith_cubeChartOn_zero`: at an end
  point of `[0, 1]` the reduced directions of the centred chart are `0`.
* **`isInGeneralPositionAt_cubeSecSlice`**: `d_X ≡ 0`, `q ∈ {0, 1}`, `Λ̃ = Λ` over `t = q`, and
  `(f̃, Λ̃)` in general position at `(q, y)` near which `Λ̃` has a local representation: then
  `(f, Λ)` is in general position at `y`.
* `KernelBranching.one_le_dim_of_mem_submanifoldBoundary`: a sheet with a boundary point has
  dimension at least `1`.
* **`sliceKernelStatement`**: the slice structure of `exists_slice_branching` is described by
  kernels (`SliceKernelStatement`), with the sections `s̃ⱼ(q, ·)`.
* **`exists_matched_kernel_branching_of_class`**, **`exists_matched_kernel_branching`**:
  `exists_matched_branching` with the structure on `X` described by kernels.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold

universe u

/-- **`E_x = 0` at a point of maximal degeneracy of a finite-dimensional model**: if
`dim E₀ = d(x)` for the presentation `T`, the only vector `v` with `(Tv)ᵢ = 0` for all `i` with
`(Tx)ᵢ = 0` is `0`. -/
theorem minimalSubspaceWith_eq_bot_of_finrank_eq {E : ScBanach} {n : ℕ} {W : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (x : E 0) [FiniteDimensional ℝ (E 0)]
    (h : finrank ℝ (E 0) = degIndexWith T x) : minimalSubspaceWith T x = ⊥ := by
  classical
  have hcard : finrank ℝ ({i : Fin n // (T 0 x).1 i = 0} → ℝ) = degIndexWith T x := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_subtype]
    rfl
  have hinj : Injective (coordMapL T x).toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (h.trans hcard.symm)).2
      (coordMapL_surjective T x)
  unfold minimalSubspaceWith
  exact LinearMap.ker_eq_bot.2 hinj

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP UnitCube

variable {A : SEP.{u}}

/-! ### The reduced directions of `[0, 1]` at an end point -/

/-- **At an end point `q` of `[0, 1]` the centred chart has no reduced direction**:
`E_0 = 0` for every presentation of its partial quadrant. -/
theorem minimalSubspaceWith_cubeChartOn_zero {q : Fin 1 → unitInterval}
    (hq : (q 0 : ℝ) = 0 ∨ (q 0 : ℝ) = 1) {J : Set (Fin 1 → unitInterval)}
    (hJ : J ⊆ (cChart q).source) (hJo : IsOpen J) {n : ℕ} {W : ScBanach}
    (T : ScIso (cubeChartOn q hJ hJo).model.E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : (cubeChartOn q hJ hJo).model.C = T 0 ⁻¹' quadrant n W 0) :
    minimalSubspaceWith T (0 : (cubeChartOn q hJ hJo).model.E 0) = ⊥ := by
  have : FiniteDimensional ℝ ((cubeChartOn q hJ hJo).model.E 0) :=
    inferInstanceAs (FiniteDimensional ℝ (Fin 1 → ℝ))
  have hfin : finrank ℝ ((cubeChartOn q hJ hJo).model.E 0) = 1 :=
    (Module.finrank_fin_fun ℝ : finrank ℝ (Fin 1 → ℝ) = 1)
  have hdeg : (cubePolyfold 1).degIndex q = 1 := by
    rw [cubePolyfold_degIndex, Finset.card_eq_one]
    refine ⟨0, Finset.eq_singleton_iff_unique_mem.2 ⟨by simpa using hq, fun i _ => ?_⟩⟩
    exact Subsingleton.elim i 0
  have hch := (cubePolyfold 1).degIndex_eq_chartDegIndex_of_isTameRetract (isChart_cChart q)
    ⟨cRetr q, cRetr_retract q, cRetr_isTame q⟩ (mem_cChart q)
  have h0C : (0 : (cubeChartOn q hJ hJo).model.E 0) ∈ (cubeChartOn q hJ hJo).model.C := by
    have h := (cChart q).apply_mem_C (mem_cChart q)
    rwa [cChart_self q] at h
  have hw : degIndexWith T (0 : (cubeChartOn q hJ hJo).model.E 0) = 1 := by
    rw [← degIndex_eq T hT h0C]
    have h2 : Polyfold.degIndex (cChart q).model.E (cChart q).model.C (cChart q q) = 1 :=
      hch.symm.trans hdeg
    rw [cChart_self q] at h2
    exact h2
  exact minimalSubspaceWith_eq_bot_of_finrank_eq T _ (hfin.trans hw.symm)

/-! ### General position on the slice -/

set_option maxHeartbeats 1600000 in
-- the product chart `χ × φ_c` and its presentation are unfolded
/-- **General position of `(f̃, Λ̃)` at a point `(q, y)` of an end gives general position of
`(f, Λ_q)` at `y`** (p. 703).  Let `d_X ≡ 0`, `q ∈ {0, 1}`, `Λ̃ = Λ` on the fibres over
`{q} × X`, and let `Λ̃` have a local representation on an open `Õ ∋ (q, y)`.  The reduced tangent
space of `[0, 1] × X` at `(q, y)` is `0 × T_yX`, and there
`(f̃ − s̃ᵢ)'(q, y) = (f − s̃ᵢ(q, ·))'(y)`; the slices `s̃ᵢ(q, ·)` represent `Λ` near `y`. -/
theorem isInGeneralPositionAt_cubeSecSlice (hd : ∀ x, A.X.PObj.degIndex x = 0) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ : A.W → ℚ≥0} {q : Fin 1 → unitInterval}
    (hq : (q 0 : ℝ) = 0 ∨ (q 0 : ℝ) = 1) (hΛq : ∀ w : A.W, Λ' (cubeFibLift q w) = Λ w)
    {Ot : Set (A.cubeSEP 1).Obj} (hOt : IsOpen Ot) {k : ℕ}
    {s : Fin k → (A.cubeSEP 1).Obj → (A.cubeSEP 1).W} {σ : Fin k → ℚ≥0}
    (hrep : IsLocalRepOn (A.cubeSEP 1) Λ' Ot s σ) {y : A.Obj}
    (hyO : ((q, y) : (A.cubeSEP 1).Obj) ∈ Ot)
    (hgp : IsInGeneralPositionAt (cubeLiftEp (n := 1) f hf.1.1.1) Λ' (q, y)) :
    IsInGeneralPositionAt f Λ y := by
  classical
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := A.B.paracompactSpace_pullback ((cubePolyfold 1).prod A.X.PObj)
    (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj)
  have hπ : ((cubePolyfold 1).prod A.X.PObj).IsScSmoothMap A.X.PObj
      (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj) := (A.X.cubeProj 1).isScSmoothMap_obj
  have hXP : A.X.PObj.IsTame := A.X.PObj.isTame_of_degIndex_eq_zero hd
  have hfC := isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft
  have hftC := isScFredholmSectionTame_cubeLiftEp (n := 1) hft
  obtain ⟨hp1, hred⟩ := hgp
  set p : (A.cubeSEP 1).Obj := (q, y) with hp
  set xt : (A.cubeSEP 1).X.PObj.Level 1 := (A.cubeSEP 1).X.PObj.levelMk 1 p hp1 with hxt
  have hy1 : y ∈ A.X.PObj.levelSet 1 :=
    (prod_cube_mem_levelSet_iff (n := 1) (PX := A.X.PObj) (z := p)).1 hp1
  refine ⟨hy1, ?_⟩
  set y₁ : A.X.PObj.Level 1 := A.X.PObj.levelMk 1 y hy1 with hy₁def
  intro L hL φ hφ hx m V T hT
  -- a box `J₀ × O₀` inside `Õ` and a tame chart of `W` around `y`, restricted to `O₀`
  obtain ⟨J₀, O₀, hJ₀, hO₀, hqJ₀, hyO₀, hbox⟩ := isOpen_prod_iff.1 hOt q y hyO
  obtain ⟨c₀, hc₀t, hyc₀⟩ := A.B.exists_isTameChart hXP y
  have hOco : IsOpen (O₀ ∩ c₀.φ.source) := hO₀.inter c₀.φ.isOpen_source
  set c := c₀.restrict inter_subset_right hOco with hcdef
  have hc : A.B.IsChart c := hc₀t.isChart.restrict inter_subset_right hOco
  have hyc : y ∈ c.φ.source := ⟨hyO₀, hyc₀⟩
  have hycs : A.X.PObj.levelVal 1 y₁ ∈ c.φ.source := hyc
  obtain ⟨nc, Wc, Tc, hTc⟩ := c.φ.model.isPartialQuadrant
  have htop : minimalSubspaceWith Tc (c.φ y) = ⊤ := by
    have htame : IsTameRetract c₀.φ.model.E c₀.φ.model.C c₀.φ.model.O :=
      ⟨_, c₀.base_retract, hc₀t.isTame⟩
    have hdeg := MPolyfold.degIndex_eq_chartDegIndex_of_isTameRetract (P := A.X.PObj)
      c₀.isChart htame hyc₀
    rw [hd y] at hdeg
    have hyC : c₀.φ y ∈ c₀.φ.model.C := c₀.φ.apply_mem_C hyc₀
    have hw : degIndexWith Tc (c₀.φ y) = 0 := by
      rw [← degIndex_eq Tc hTc hyC]; exact hdeg.symm
    exact minimalSubspaceWith_eq_top_of_mem_interior Tc hTc
      (mem_interior_of_degIndexWith_eq_zero Tc hTc hyC hw)
  -- the slice representation and the operator `L`
  have hrepX : IsLocalRepOn A Λ (O₀ ∩ c₀.φ.source) (fun j => cubeSecSlice (s j) q) σ :=
    (isLocalRepOn_cubeSecSlice hOt hrep q hΛq).mono hOco (fun y' hy' => hbox ⟨hqJ₀, hy'.1⟩)
  set dX : LocalLinData A Λ y₁ :=
    ⟨O₀ ∩ c₀.φ.source, hOco, k, _, σ, hrepX, c, hc, subset_rfl, hycs⟩
  rw [linearization_eq hf dX] at hL
  obtain ⟨i, hi, rfl⟩ := (mem_support_linSumIntr_iff hf.1.1.1 hrepX.1
    (fun i => (hrepX.2.1 i).1) subset_rfl hycs L).1 hL
  rw [reducedTangentFiber_eq hφ hx T c.isChart hycs Tc hT hTc]
  refine surjective_domRestrict_toIntr_subDeriv_of_chart hf.1.1 (hrepX.2.1 i) hc subset_rfl hycs
    hi.symm Tc fun kk hk => ?_
  -- the product chart `χ × φ_c` around `p`
  have hJo : IsOpen (J₀ ∩ (cChart q).source) := hJ₀.inter (cChart q).isOpen_source
  have hqJ : q ∈ J₀ ∩ (cChart q).source := ⟨hqJ₀, mem_cChart q⟩
  set pc := cubeChart q inter_subset_right hJo c (cubeLiftEp (n := 1) f hf.1.1.1 p) with hpcdef
  have hpc : (A.cubeSEP 1).B.IsChart pc :=
    PullbackChartData.isChart_toChart A.B hπ _ hc _
  have hpcsub : pc.φ.source ⊆ Ot := fun z hz => hbox ⟨hz.1.1, hz.2.1⟩
  have hpmem : p ∈ pc.φ.source := ⟨hqJ, hyc⟩
  obtain ⟨nχ, Wχ, Tχ, hTχ⟩ := (cubeChartOn q inter_subset_right hJo).model.isPartialQuadrant
  have hTpc : pc.φ.model.C = (prodPresentation Tχ Tc) 0 ⁻¹' quadrant (nχ + nc) (Wχ.prod Wc) 0 :=
    prod_eq_prodPresentation Tχ Tc hTχ hTc
  set z := levelLift c.φ 1 (A.X.PObj.levelVal 1 y₁) with hzdef
  set zt := levelLift pc.φ 1 p with hztdef
  have haz : c.φ.model.E.toBase 1 z = c.φ y :=
    A.X.PObj.toBase_levelLift c.isChart hycs (levelVal_mem y₁)
  have hyOc : c.φ y ∈ c.φ.model.O := c.φ.mapsTo_model y hyc
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U := by
    rw [haz]; exact mem_U_of_mem_O c.isRetraction (by rw [c.r_image]; exact hyOc)
  have hazt' : pc.φ.model.E.toBase 1 zt = pc.φ p :=
    (A.cubeSEP 1).X.PObj.toBase_levelLift pc.isChart hpmem (levelVal_mem xt)
  have hpcp : pc.φ p = ((0 : Fin 1 → ℝ), c.φ y) := Prod.ext (cChart_self q) rfl
  have hazt : pc.φ.model.E.toBase 1 zt = ((0 : Fin 1 → ℝ), c.φ.model.E.toBase 1 z) := by
    rw [hazt', haz]; exact hpcp
  -- the branch `s̃ᵢ` passes through `f̃(p)` and is in general position there
  have hi' : s i p = cubeLiftEp (n := 1) f hf.1.1.1 p :=
    cubeVal_injective (Prod.ext ((hrep.2.1 i).1 p hyO) hi)
  have : Nonempty Ot := ⟨⟨p, hyO⟩⟩
  have := (A.cubeSEP 1).X.PObj.paracompactSpace_subtype Ot
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : Ot → (A.cubeSEP 1).Obj))
    ((A.cubeSEP 1).X.PObj.restrictOpen hOt) (A.cubeSEP 1).B
  have hG := isGeneralPositionGerm_branch_at hfC hftC hred hOt hrep (x := xt) hyO hi'
  -- `K` of the product chart over `(0, φ_c(y))` is `K` of `c` over `φ_c(y)`
  have hkpc : (pc.φ p, kk) ∈ pc.K := by
    rw [hpcp]
    change _ ∈ pullbackRetraction (cubeChartData q inter_subset_right hJo c).c.R
      (cubeChartData q inter_subset_right hJo c).RZ (cubeChartData q inter_subset_right hJo c).g ''
      ((cubeChartData q inter_subset_right hJo c).RZ.U ×ˢ univ)
    rw [(cubeChartData q inter_subset_right hJo c).image_eq_Kg]
    have hg : (cubeChartData q inter_subset_right hJo c).g
        ((0 : Fin 1 → ℝ), c.φ y) = c.φ y := by
      change c.φ (c.φ.symm (c.φ y)) = c.φ y
      exact c.φ.apply_symm_apply hyOc
    refine ⟨?_, ?_⟩
    · rw [(cubeChartData q inter_subset_right hJo c).RZ_retract]
      rw [← hpcp]
      exact pc.φ.mapsTo_model p hpmem
    · change ((cubeChartData q inter_subset_right hJo c).g ((0 : Fin 1 → ℝ), c.φ y), kk) ∈ c.K
      rw [hg, ← haz]
      exact hk
  obtain ⟨w, hwR, hwT, hwk⟩ := exists_reduced_preimage_of_isGeneralPositionGerm hOt hftC
    (hrep.2.1 i) hpc hpcsub hpmem hi'.symm hG hazt' (prodPresentation Tχ Tc) hTpc hkpc
  -- `w = (0, v)`
  have hwmin := (SetLike.ext_iff.1 (minimalSubspaceWith_prodPresentation (T := Tχ) (T' := Tc)
    (pc.φ.model.E.toBase 1 zt : ((cubeChartOn q inter_subset_right hJo).model.E.prod
      c.φ.model.E) 0)) w).1 hwR.2
  have hw1 : (w : (Fin 1 → ℝ) × c.φ.model.E 0).1 = 0 := by
    have h : (w : (Fin 1 → ℝ) × c.φ.model.E 0).1 ∈ minimalSubspaceWith Tχ
        (pc.φ.model.E.toBase 1 zt : (Fin 1 → ℝ) × c.φ.model.E 0).1 :=
      (Submodule.mem_prod.1 hwmin).1
    have hb : (pc.φ.model.E.toBase 1 zt : (Fin 1 → ℝ) × c.φ.model.E 0).1 = 0 :=
      congrArg Prod.fst hazt
    rw [hb] at h
    have h' := (SetLike.ext_iff.1
      (minimalSubspaceWith_cubeChartOn_zero hq inter_subset_right hJo Tχ hTχ) _).1 h
    exact (Submodule.mem_bot ℝ).1 h'
  have hwe : w = ((0 : Fin 1 → ℝ), w.2) := Prod.ext hw1 rfl
  refine ⟨w.2, ?_, ?_, ?_⟩
  · -- `w.2 ∈ range Dr(z)`
    obtain ⟨w₀, hw₀⟩ := hwT
    have hrelχ := relOpen_cubeChartOn q inter_subset_right hJo
    have hzt2 : zt.2 = z := by
      apply c.φ.model.E.toBase_injective 1
      exact congrArg Prod.snd hazt
    have hztU : zt ∈ ((cubeChartOn q inter_subset_right hJo).model.E.prod c.φ.model.E).lvlSet
        ((cubeChartOn q inter_subset_right hJo).model.O ×ˢ c.U) 1 := by
      change pc.φ.model.E.toBase 1 zt ∈ (cubeChartOn q inter_subset_right hJo).model.O ×ˢ c.U
      rw [hazt]
      exact ⟨zero_mem_cubeChartOn_O q inter_subset_right hJo hqJ, hzU⟩
    have h1 := scDeriv_prodMap hrelχ c.relOpen (isScSmooth_id hrelχ.isScDomain)
      (c.isRetraction.baseRetraction c.relOpen).isScSmooth hztU
    have e := congrArg (fun M : pc.φ.model.E 0 →L[ℝ] pc.φ.model.E 0 => (M w₀).2) h1
    have hz2 : scDeriv c.U (r c.R) (zt : (Fin 1 → ℝ) × c.φ.model.E 1).2 =
        scDeriv c.U (r c.R) z := congrArg (fun u => scDeriv c.U (r c.R) u) hzt2
    exact ⟨w₀.2, (congrArg (fun M : c.φ.model.E 0 →L[ℝ] c.φ.model.E 0 => M w₀.2) hz2).symm.trans
      (e.symm.trans (congrArg Prod.snd hw₀))⟩
  · change w.2 ∈ minimalSubspaceWith Tc (c.φ y)
    rw [htop]; exact Submodule.mem_top
  · refine (subDeriv_cubeChart_inr hqJ hf.1.1.1 hfC.1.1 (hrep.2.1 i) _ hpc hpcsub hzU hazt
      w.2).symm.trans ?_
    exact (congrArg (fun u => subDeriv pc (cubeLiftEp (n := 1) f hf.1.1.1) (s i) zt u)
      hwe.symm).trans hwk

/-! ### A sheet with a boundary point is not a point -/

namespace KernelBranching

/-- **A sheet with a boundary point has dimension at least `1`**:
`1 ≤ d_M(y) = dim (T_yM / T^R_yM) ≤ dim T_yM` (Lemma 9.3.7). -/
theorem one_le_dim_of_mem_submanifoldBoundary {f : A.Obj → A.W} {Λ : A.W → ℚ≥0} {x : A.Obj}
    (K : KernelBranching A f Λ x) (j : K.ι) {y : A.Obj}
    (hy : y ∈ A.X.PObj.submanifoldBoundary (K.M j)) : 1 ≤ K.dim j := by
  obtain ⟨hS, hyM, h1⟩ := hy
  obtain ⟨c⟩ := A.X.PObj.nonempty_presentedChart y
  rw [MPolyfold.subDegIndex_eq_quotDim_span hS (K.hasTameInducedStructure j) hyM c] at h1
  obtain ⟨N, hN, hfin, hn⟩ := exists_submodule_chartVec_image c.isChart
    (K.isSubmanifoldOfDim j).1 ((K.isSubmanifoldOfDim j).2 y hyM) c.mem_source
  have hspan : Submodule.span ℝ (c.vec '' A.X.PObj.submanifoldTangent (K.M j) y) = N := by
    have h : c.vec '' A.X.PObj.submanifoldTangent (K.M j) y = (N : Set (c.φ.model.E 0)) :=
      hN.symm
    rw [h]
    exact Submodule.span_eq N
  rw [hspan] at h1
  have hle : quotDim N c.red ≤ finrank ℝ N := Submodule.finrank_quotient_le _
  rw [← hn]
  exact h1.trans hle

end KernelBranching

/-! ### The slice structure is described by kernels -/

set_option maxHeartbeats 1600000 in
-- the cylinder's ep-groupoid is unfolded in several places
open Classical in
/-- **The slice structure is described by kernels** (proof of Corollary 15.4.4, p. 703:
`Mⱼ = {f = s̃ⱼ(i, ·)}`).  Let `d_X ≡ 0`, `f` sc-Fredholm with tame germ data, `Λ̃` an
sc⁺-multisection with `Λ̃ = Λⁱ` over `t = i`, the face condition of Theorem 15.3.9 for the glued
data, `q ∈ {0, 1}` and `Λ̃ = Λ` on the fibres over `{q} × X`.  Let `K̃` be a local branching
structure of `Θ̃` at `(q, x)` described by kernels and `B` a tame local branching structure of
`Θ = Λ ∘ f` at `x` with the weights of `K̃`, `U = {y | (q, y) ∈ Ũ}`, sheets
`Mⱼ = {y | (q, y) ∈ M̃ⱼ}` of dimension `dim M̃ⱼ − 1`.  Then `B` is described by kernels, with the
sections `sⱼ = s̃ⱼ(q, ·)` on `{y | (q, y) ∈ Õ}`: `T_yMⱼ = ker (f − sⱼ)'(y)`, `(f − sⱼ)'(y)` is
onto, and `dim M̃ⱼ = dim Mⱼ + 1`. -/
theorem sliceKernelStatement (hd : ∀ x, A.X.PObj.degIndex x = 0) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ')
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁))
    {q : Fin 1 → unitInterval} (hq : (q 0 : ℝ) = 0 ∨ (q 0 : ℝ) = 1) {Λ : A.W → ℚ≥0}
    (hΛq : ∀ w : A.W, Λ' (cubeFibLift q w) = Λ w) {x : A.Obj}
    (K' : KernelBranching (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1) Λ' (q, x))
    (B : A.X.TameBranchingStructure (fun z => (Λ (f z) : ℚ)) x) (e : K'.ι ≃ B.ι)
    (hσ : ∀ j, K'.σ j = B.σ (e j))
    (hU : ∀ y, y ∈ B.U ↔ ((q, y) : (A.cubeSEP 1).Obj) ∈ K'.U)
    (hM : ∀ j, B.M (e j) = {y | ((q, y) : (A.cubeSEP 1).Obj) ∈ K'.M j})
    (hdim : ∀ j, A.X.PObj.IsSubmanifoldOfDim (B.M (e j)) (K'.dim j - 1)) :
    SliceKernelStatement hf.1.1.1 q K' B e := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hXC : (A.cubeSEP 1).X.IsTame := A.X.isTame_cubeProd 1 hX
  have hbd : ∀ w : (A.cubeSEP 1).W, (A.cubeSEP 1).P w ∈ (A.cubeSEP 1).X.PObj.boundary →
      Λ' w = cubeGlue Λ₀ Λ₁ w := fun w hw => by
    rcases (mem_boundary_cubeSEP_iff hX hd _).1 hw with h | h
    · exact (h0 w h).trans (cubeGlue_of_zero h).symm
    · exact (h1 w h).trans (cubeGlue_of_one h).symm
  have hfC := isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft
  have hftC := isScFredholmSectionTame_cubeLiftEp (n := 1) hft
  have hsec : IsSection A.P f := hf.1.1.1
  set O : Set A.Obj := {y | ((q, y) : (A.cubeSEP 1).Obj) ∈ K'.O} with hOdef
  have hO : IsOpen O := K'.isOpen_O.preimage (continuous_const.prodMk continuous_id)
  have hrepX : IsLocalRepOn A Λ O (fun i => cubeSecSlice (K'.sAll i) q) K'.σAll :=
    isLocalRepOn_cubeSecSlice K'.isOpen_O K'.isLocalRep q hΛq
  -- `f = s̃ᵢ(q, ·)` at `y` iff `f̃ = s̃ᵢ` at `(q, y)`
  have heq : ∀ (i : Fin K'.k) (y : A.Obj), ((q, y) : (A.cubeSEP 1).Obj) ∈ K'.O →
      (f y = cubeSecSlice (K'.sAll i) q y ↔
        cubeLiftEp (n := 1) f hf.1.1.1 (q, y) = K'.sAll i (q, y)) := fun i y hy =>
    ⟨fun h => by
        have h' : K'.sAll i (q, y) = cubeLiftEp (n := 1) f hf.1.1.1 (q, y) :=
          cubeVal_injective (Prod.ext ((K'.isLocalRep.2.1 i).1 (q, y) hy) h.symm)
        exact h'.symm,
      fun h => congrArg (fun w => (cubeVal w).2) h⟩
  have hMB : ∀ j, B.M (e j) = {z ∈ B.U | f z = cubeSecSlice (K'.sAll (K'.idx j)) q z} := by
    intro j
    rw [hM j, K'.M_eq j]
    ext z
    constructor
    · rintro ⟨hz, h⟩
      exact ⟨(hU z).2 hz, (heq _ z (K'.U_subset hz)).2 h⟩
    · rintro ⟨hz, h⟩
      exact ⟨(hU z).1 hz, (heq _ z (K'.U_subset ((hU z).1 hz))).1 h⟩
  -- general position at the points of the sheets in the face
  have hgpC : ∀ j, ∀ p ∈ K'.M j, p.1 = q →
      IsInGeneralPositionAt (cubeLiftEp (n := 1) f hf.1.1.1) Λ' p := by
    intro j p hpM hpq
    have hpb : p ∈ (A.cubeSEP 1).X.PObj.boundary :=
      (mem_boundary_cubeSEP_iff hX hd p).2 (by rw [hpq]; exact hq)
    have hpos : 0 < Λ' (cubeLiftEp (n := 1) f hf.1.1.1 p) := by
      have h := (K'.toLocalBranchingStructure.mem_supp_iff (K'.subset_U j hpM)).2 ⟨j, hpM⟩
      have h' : (0 : ℚ) < (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 p) : ℚ) := h
      exact_mod_cast h'
    exact isInGeneralPositionAt_of_isBoundaryFaceOnto hfC hftC hΛ' hbd honto hpb hpos
  -- the kernel description at the points of the slices
  have hpt : ∀ j, ∀ y ∈ B.M (e j), y ∈ A.X.PObj.smoothSet ∧
      ∀ c : StrongBundleChart A.X.PObj A.P, A.B.IsChart c → c.φ.source ⊆ O → y ∈ c.φ.source →
        ∀ z : c.φ.model.E 1, c.φ.model.E.toBase 1 z = c.φ y →
          chartVec c.isChart '' A.X.PObj.submanifoldTangent (B.M (e j)) y =
              kerSet c f (cubeSecSlice (K'.sAll (K'.idx j)) q) z ∧
            ChartOnto c (subDeriv c f (cubeSecSlice (K'.sAll (K'.idx j)) q) z) z := by
    intro j y hy
    have hyM' : ((q, y) : (A.cubeSEP 1).Obj) ∈ K'.M j := by rw [hM j] at hy; exact hy
    have hyO' : ((q, y) : (A.cubeSEP 1).Obj) ∈ K'.O := K'.U_subset (K'.subset_U j hyM')
    have hyO : y ∈ O := hyO'
    obtain ⟨hy1, hred⟩ := isInGeneralPositionAt_cubeSecSlice hd hf hft hq hΛq K'.isOpen_O
      K'.isLocalRep hyO' (hgpC j _ hyM' rfl)
    have hfy : f y = cubeSecSlice (K'.sAll (K'.idx j)) q y := by
      have h := hy
      rw [hMB j] at h
      exact h.2
    have hs := hrepX.2.1 (K'.idx j)
    have : Nonempty O := ⟨⟨y, hyO⟩⟩
    have := A.X.PObj.paracompactSpace_subtype O
    have := paracompactSpace_pullbackSpace (f := (Subtype.val : O → A.Obj))
      (A.X.PObj.restrictOpen hO) A.B
    have hG := isGeneralPositionGerm_branch_at hf hft hred hO hrepX
      (x := A.X.PObj.levelMk 1 y hy1) hyO hfy.symm
    have h0' : IsZeroAt (pullbackProj A.P (Subtype.val : O → A.Obj))
        (subRestrict (O := O) f (cubeSecSlice (K'.sAll (K'.idx j)) q) hft.isScSmooth.1)
        ⟨y, hyO⟩ := by
      unfold subRestrict
      rw [isZeroAt_restrictSection_iff]
      exact (isZeroAt_subSec_iff hft.isScSmooth.1 hs.1 hyO).2 hfy
    have hgood := hG.isGoodPositionGermTame (isScFredholmSectionTame_subRestrict hO hft hs) h0'
    obtain ⟨V, d, hVo, hyV, -, -, -, hall⟩ :=
      exists_branch_kernel hft hO hs hyO hfy ⟨hft.isScSmooth.1, hgood⟩
    obtain ⟨hys, hch⟩ := hall y hyV hfy
    refine ⟨hys, fun c hc hsub hyc z hz => ?_⟩
    obtain ⟨ht, hon⟩ := hch c hc hsub hyc z hz
    refine ⟨?_, hon⟩
    rw [← ht]
    have e1 : B.M (e j) ∩ V =
        {y ∈ V | f y = cubeSecSlice (K'.sAll (K'.idx j)) q y} ∩ B.U := by
      rw [hMB j]
      ext z'
      constructor
      · rintro ⟨⟨hz1, hz2⟩, hz3⟩; exact ⟨⟨hz3, hz2⟩, hz1⟩
      · rintro ⟨⟨hz3, hz2⟩, hz1⟩; exact ⟨⟨hz1, hz2⟩, hz3⟩
    rw [← submanifoldTangent_inter_isOpen (A := B.M (e j)) hVo hyV, e1,
      submanifoldTangent_inter_isOpen B.isOpen_U (B.subset_U _ hy)]
  have hes : ∀ i : B.ι, B.M i = B.M (e (e.symm i)) := fun i => by rw [e.apply_symm_apply]
  refine ⟨{ toTameBranchingStructure := B
            dim := fun i => K'.dim (e.symm i) - 1
            isSubmanifoldOfDim := fun i => by
              have h := hdim (e.symm i)
              rwa [e.apply_symm_apply] at h
            O := O
            isOpen_O := hO
            U_subset := fun y hy => K'.U_subset ((hU y).1 hy)
            k := K'.k
            sAll := fun i => cubeSecSlice (K'.sAll i) q
            σAll := K'.σAll
            isLocalRep := hrepX
            idx := fun i => K'.idx (e.symm i)
            idx_injective := fun a b h => e.symm.injective (K'.idx_injective h)
            σ_eq := fun i => by
              have h := hσ (e.symm i)
              rw [e.apply_symm_apply] at h
              rw [← h]
              exact K'.σ_eq (e.symm i)
            mem_range := fun j z hz h => by
              obtain ⟨i, hi⟩ := K'.mem_range j (q, z) ((hU z).1 hz)
                ((heq j z (K'.U_subset ((hU z).1 hz))).1 h)
              exact ⟨e i, by change K'.idx (e.symm (e i)) = j; rw [e.symm_apply_apply]; exact hi⟩
            M_eq := fun i => by
              have h := hMB (e.symm i)
              rwa [e.apply_symm_apply] at h
            smooth := fun i y hy => (hpt (e.symm i) y (by rw [← hes i]; exact hy)).1
            tangent_eq := fun i y hy c hc hsub hyc z hz => by
              have h := ((hpt (e.symm i) y (by rw [← hes i]; exact hy)).2 c hc hsub hyc z hz).1
              rwa [e.apply_symm_apply] at h
            onto := fun i y hy c hc hsub hyc z hz =>
              ((hpt (e.symm i) y (by rw [← hes i]; exact hy)).2 c hc hsub hyc z hz).2 },
    e, rfl, fun j => rfl, fun j => (hσ j).symm, fun j => ?_, fun j y _ hy' => ?_⟩
  · change K'.dim j = K'.dim (e.symm (e j)) - 1 + 1
    rw [e.symm_apply_apply]
    have hpM : ((q, x) : (A.cubeSEP 1).Obj) ∈ K'.M j := K'.mem_M j
    have hpb : ((q, x) : (A.cubeSEP 1).Obj) ∈ (A.cubeSEP 1).X.PObj.boundary :=
      (mem_boundary_cubeSEP_iff hX hd _).2 hq
    have h1' := K'.one_le_dim_of_mem_submanifoldBoundary j
      (K'.mem_submanifoldBoundary hXC hfC hftC j hpM hpb (hgpC j _ hpM rfl))
    omega
  · change cubeVal (K'.sAll (K'.idx j) (q, y)) =
      ((q, y), cubeSecSlice (K'.sAll (K'.idx (e.symm (e j)))) q y)
    rw [e.symm_apply_apply]
    exact Prod.ext ((K'.isScPlus j).1 (q, y) hy') rfl

/-! ### The matched structures, both described by kernels -/

/-- **Matching local branching structures at a point of an end of the cylinder, both described
by kernels, with the sheets of the end in a given class** (proof of Corollary 15.4.4, p. 703).
Under the hypotheses of `exists_matched_branching_of_class` there are local branching structures
`K̃` of `Θ̃ = Λ̃ ∘ f̃` at `(i, x)` and `K` of `Θ = Λ ∘ f` at `x`, both described by kernels, with a
bijection `e` of the index sets such that: the weights agree; `U = {y | (i, y) ∈ Ũ}`;
`Ũ ∩ ∂([0, 1] × X) ⊆ {i} × X`; `Mⱼ = {y | (i, y) ∈ M̃ⱼ}`; `∂₁M̃ⱼ = {i} × Mⱼ`;
`dim M̃ⱼ = dim Mⱼ + 1`; the sections of `K` are the restrictions `s̃ⱼ(i, ·)` of the sections of
`K̃`; and `Mⱼ` is in the class `S (dim Mⱼ)`. -/
theorem exists_matched_kernel_branching_of_class (hd : ∀ x, A.X.PObj.degIndex x = 0)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ')
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁))
    {i : unitInterval} (hi : (i : ℝ) = 0 ∨ (i : ℝ) = 1) {Λ : A.W → ℚ≥0}
    (hΛi : ∀ w, ((cubeVal w).1.1 0 : ℝ) = i → Λ' w = Λ (cubeVal w).2)
    {x : A.Obj} (hx : 0 < Λ (f x)) (S : ℕ → Set (Set A.Obj))
    (hS₁ : ∀ d N, A.X.PObj.IsSubmanifoldOfDim N d → x ∈ N →
      ∃ V : Set A.Obj, IsOpen V ∧ x ∈ V ∧ N ∩ V ∈ S d)
    (hS₂ : ∀ d N V, N ∈ S d → IsOpen V → N ∩ V ∈ S d) :
    ∃ (K' : KernelBranching (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1) Λ' ((fun _ => i), x))
      (K : KernelBranching A f Λ x) (e : K'.ι ≃ K.ι),
      (∀ j, K'.σ j = K.σ (e j)) ∧
      (∀ y, y ∈ K.U ↔ (((fun _ => i), y) : (A.cubeSEP 1).Obj) ∈ K'.U) ∧
      (∀ p ∈ K'.U, p ∈ (A.cubeSEP 1).X.PObj.boundary → p.1 = fun _ => i) ∧
      (∀ j, K.M (e j) = {y | (((fun _ => i), y) : (A.cubeSEP 1).Obj) ∈ K'.M j}) ∧
      (∀ j, (A.cubeSEP 1).X.PObj.boundaryStratum (K'.M j) =
        (cubeFaceIncl A (fun _ => i)).obj '' K.M (e j)) ∧
      (∀ j, K'.dim j = K.dim (e j) + 1) ∧
      (∀ j, ∀ y ∈ K.O, (((fun _ => i), y) : (A.cubeSEP 1).Obj) ∈ K'.O →
        cubeVal (K'.s j ((fun _ => i), y)) = (((fun _ => i), y), K.s (e j) y)) ∧
      ∀ j, K.M (e j) ∈ S (K.dim (e j)) := by
  obtain ⟨K', B, e, hσ, hU, hb, hM, hstr, hdim, hcls⟩ :=
    exists_matched_branching_of_class hd hf hft hΛ' h0 h1 honto hi hΛi hx S hS₁ hS₂
  obtain ⟨K, g, hKU, hKM, hKσ, hKd, hKs⟩ := sliceKernelStatement hd hf hft hΛ' h0 h1 honto
    (q := fun _ => i) hi (fun w => hΛi (cubeFibLift (fun _ => i) w) rfl) K' B e hσ hU hM hdim
  refine ⟨K', K, g, fun j => (hKσ j).symm, fun y => ?_, hb, fun j => ?_, fun j => ?_, hKd, hKs,
    fun j => ?_⟩
  · rw [hKU]; exact hU y
  · rw [hKM j]; exact hM j
  · rw [hKM j]; exact hstr j
  · have h := hcls j
    have hd' : K'.dim j - 1 = K.dim (g j) := by rw [hKd j]; exact Nat.add_sub_cancel _ _
    rw [hKM j, ← hd']
    exact h

/-- **Matching local branching structures at a point of an end of the cylinder, both described
by kernels** (`exists_matched_kernel_branching_of_class` without a class of sheets). -/
theorem exists_matched_kernel_branching (hd : ∀ x, A.X.PObj.degIndex x = 0) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ')
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁))
    {i : unitInterval} (hi : (i : ℝ) = 0 ∨ (i : ℝ) = 1) {Λ : A.W → ℚ≥0}
    (hΛi : ∀ w, ((cubeVal w).1.1 0 : ℝ) = i → Λ' w = Λ (cubeVal w).2)
    {x : A.Obj} (hx : 0 < Λ (f x)) :
    ∃ (K' : KernelBranching (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1) Λ' ((fun _ => i), x))
      (K : KernelBranching A f Λ x) (e : K'.ι ≃ K.ι),
      (∀ j, K'.σ j = K.σ (e j)) ∧
      (∀ y, y ∈ K.U ↔ (((fun _ => i), y) : (A.cubeSEP 1).Obj) ∈ K'.U) ∧
      (∀ p ∈ K'.U, p ∈ (A.cubeSEP 1).X.PObj.boundary → p.1 = fun _ => i) ∧
      (∀ j, K.M (e j) = {y | (((fun _ => i), y) : (A.cubeSEP 1).Obj) ∈ K'.M j}) ∧
      (∀ j, (A.cubeSEP 1).X.PObj.boundaryStratum (K'.M j) =
        (cubeFaceIncl A (fun _ => i)).obj '' K.M (e j)) ∧
      (∀ j, K'.dim j = K.dim (e j) + 1) ∧
      ∀ j, ∀ y ∈ K.O, (((fun _ => i), y) : (A.cubeSEP 1).Obj) ∈ K'.O →
        cubeVal (K'.s j ((fun _ => i), y)) = (((fun _ => i), y), K.s (e j) y) := by
  obtain ⟨K', K, e, h1', h2, h3, h4, h5, h6, h7, -⟩ := exists_matched_kernel_branching_of_class
    hd hf hft hΛ' h0 h1 honto hi hΛi hx (fun _ => univ)
    (fun _ _ _ _ => ⟨univ, isOpen_univ, mem_univ _, mem_univ _⟩) (fun _ _ _ _ _ => mem_univ _)
  exact ⟨K', K, e, h1', h2, h3, h4, h5, h6, h7⟩

end SBLocalization

end Polyfold
