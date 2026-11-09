import Polyfold.Chapter6.LinSet
import Polyfold.Chapter6.KernelFamily
import Polyfold.Chapter6.Stabilization

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5,
pp. 221–223: the stabilized section `F(t, y, λ) = f(y) − s(y, t) + Σ λᵢ sᵢ(y, t)` (before
Lemma 6.6.4 (preprint 6.29)), the kernels `L_t = ker F_t'(φ(t), 0)` (after Lemma 6.6.5 (preprint 6.30)) and **Lemma 6.6.6 (preprint 6.31)** (the
sequence (96) is exact), read at one point of the family in a fixed product chart *(book 2017:
Lemma 6.14, p. 209, sequence (6.12); see `BookConcordance.md`)*.

# The slice kernels of the stabilized section

## The text, paraphrased

Let `f` be an sc-Fredholm section of `P : Y → X`, `φ : [0, 1] → X` an sc-smooth path and `s` an
sc⁺-section of the pull-back to `X × [0, 1]` with `s(φ(t), t) = f(φ(t))`.  Adding sc⁺-sections
`s₁, …, s_k` gives the sc-Fredholm section `F(t, y, λ) = f(y) − s(y, t) + Σ λᵢ sᵢ(y, t)`, which
vanishes at the points `(t, φ(t), 0)`, and its slices `F_t(y, λ) = F(t, y, λ)`.  Lemma 6.6.4 (preprint 6.29)
chooses the `sᵢ` so that (P) every `F_t` is in general position at `(φ(t), 0)`, and
`L_t = ker F_t'(φ(t), 0)`.  For every `t` the sequence (96)
`0 → ker (f − s(·, t))'(φ(t)) →j ker F_t'(φ(t), 0) →p ℝᵏ →c Y_{φ(t)} / R((f − s(·, t))'(φ(t))) → 0`
is formed, with `j` the inclusion, `p` the projection to `ℝᵏ` and
`c(λ) = Σ λᵢ sᵢ(t, φ(t)) + R((f − s(·, t))'(φ(t)))`.  (Lemma 6.6.6 (preprint 6.31)) It is exact: a kernel vector
`(h, λ)` has `Σ λᵢ sᵢ` in the image of `(f − s(·, t))'(φ(t))`, and conversely; `c` is onto by (P).

## What is formalized

The parameter `t ∈ [0, 1]` is `q ∈ ℝⁿ`, as in `lemma_6_6_4`.  `G` is a section of
`π*P → ℝⁿ × X` (the case needed is `G = f̃ + S`, the text's `f − s`), and
`F(λ, (q, y)) = G(q, y) + Σ λᵢ sᵢ(q, y)` (`paramSection`) a section of the pull-back to
`ℝᵏ × (ℝⁿ × X)`.  Everything is read in the product chart `χ = (λ ↦ λ) × ((q ↦ q) × φ)` over a
chart point `p = (c, z)` of `x` (`ChartPoint`), at the level-`1` point `(0, (q, z))`.

* `StrongBundle.scDeriv_paramSection_ofProd_ofProd` (the linearization at a general point): the
  derivative of `F` at `(0, (q, z))` is `(λ, (σ, v)) ↦ D(ĝ_q ∘ r)(z) v + Σ λᵢ ŝᵢ(q, ·)(z) + D_q σ`,
  with `g_q = G(q, ·)` the slice and `D_q` (`StrongBundleChart.paramDerivAt`) the derivative of
  `Ĝ` in the `ℝⁿ`-directions.  It extends `linAt_paramSection_zero` and
  `StrongBundle.linAt_ofProd_slice`, which are at the centre of the chart.  The pieces:
  `PullbackChartData.ofProd_scDeriv_r_apply`, `PullbackChartData.ofProd_mem_tangent_iff` and
  `PullbackChartData.mem_K_ofProd_iff` (the tangent spaces and fibres of a product chart at a
  general point), `StrongBundle.scDeriv_ofProd_slice_apply` and
  `StrongBundle.scDeriv_paramSection_apply`.
* `linKer_inf_ker_sliceProj_eq_map` (the slice kernel):
  `ker Lin_F(0, (q, z)) ∩ ker ℓ = J(ker (T ⊕ φ))`, with `ℓ(λ, (σ, v)) = σ` (`sliceProj`),
  `J(v, λ) = (λ, (0, v))` (`sliceIncl`), `T = Lin_{g_q}(z) : T_zO → K_z` and
  `φ(λ) = Σ λᵢ ŝᵢ(q, ·)(φ(x))`; `exists_sliceOps` constructs `T` and `φ` at a zero of `g_q`.
* `mem_linSet_sectionAdd_pullbackSlice`: `T ∈ Lin(f, x)` for `G = f̃ + S` (Definition 6.2.1 (preprint 6.1) with
  `s = S(q, ·)` and `a = 0`).
* `surjective_coprod_of_isLinSurjAt`: `T ⊕ φ` is onto when `F'(0, (q, x))` is onto and
  `x = Φ(q)` for an sc-smooth `Φ : ℝⁿ → X` with `G(q', Φ(q')) = 0` near `q`.
* `exists_sliceKernel`: the three together for `G = f̃ + S`; `lemma_6_6_6`: with them the
  sequence (96) is the stabilization sequence of `T` and `φ` (`lemma_6_4_14`), hence exact.

## Reading

* `ker F_t'(φ(t), 0)` is read as the kernel of the linearization of the whole `F` cut by `σ = 0`
  (the text's fixed `t`): in `χ` the linearization of the slice `F_q` is `(v, λ) ↦ T v + φ λ`, and
  `J` identifies its kernel with `ker Lin_F(0, (q, z)) ∩ {σ = 0}`.  The text's `f − s(·, t)` is
  `G(q, ·) = f + S(q, ·)` (`sectionAdd`, signs as in `LinSet.lean`), its `Y_{φ(t)}` is `K_z` and
  its `R(…)` is the range of `T`.
* The text has `c` onto by (P), the general position of each slice `F_t`.  The project's
  `lemma_6_6_4` gives the general position of the whole `F` at `(0, (q, Φ(q)))`, hence
  `F'(0, (q, Φ(q)))` onto (`IsGeneralPositionGerm.isLinSurjAt`).  The surjectivity of `T ⊕ φ` then
  needs the `ℝⁿ`-directions to be absorbed: the derivative of the curve `q' ↦ (0, (q', Φ(q')))` of
  zeros of `F` lies in `ker Lin_F` (`fderiv_mem_linKer`), so `D_q σ` lies in the range of `T`.
  The hypotheses on `Φ` (sc-smooth, `G(q', Φ(q')) = 0` near `q`) are those of `lemma_6_6_4`.
* `PullbackChartData.toChart` takes a point of the total space, used off the domain of the
  chart; the statements hold for every choice (`q₀`, `q₁`).
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

universe u v

open StrongRetr

section ProdChart

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [ParacompactSpace ((Fin m → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))]

namespace PullbackChartData

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))] in
/-- `D(1 × r)(a, u) = 1 × Dr(u)` in the product chart, at every level-`1` point `(a, u)`. -/
lemma ofProd_scDeriv_r_apply (c : StrongBundleChart PX P) (r₀ : Fin m → ℝ)
    (q₀ : pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X)) (a : Fin m → ℝ)
    {u : c.φ.model.E 1} (hu : c.φ.model.E.toBase 1 u ∈ c.U) (v : (Fin m → ℝ) × c.φ.model.E 0) :
    scDeriv ((ofProd c r₀).toChart q₀).U (r ((ofProd c r₀).toChart q₀).R)
      ((a, u) : ((ofProd c r₀).toChart q₀).φ.model.E 1) v = (v.1, scDeriv c.U (r c.R) u v.2) := by
  have h0' : ((a, u) : (rnSc m |>.prod c.φ.model.E) 1) ∈
      (rnSc m |>.prod c.φ.model.E).lvlSet (univ ×ˢ c.U) 1 := by
    rw [lvlSet_prod]; exact ⟨mem_univ _, hu⟩
  have h1 := scDeriv_prodMap (F := rnSc m) (F' := c.φ.model.E) (rn_relOpen_univ m) c.relOpen
    (isScSmooth_id (isScDomain_univ (rnSc m)))
    (c.isRetraction.baseRetraction c.relOpen).isScSmooth h0'
  have e := congrArg (fun L : (rnSc m |>.prod c.φ.model.E) 0 →L[ℝ]
    (rnSc m |>.prod c.φ.model.E) 0 => L v) h1
  have h2 : scDeriv (E := rnSc m) (F := rnSc m) univ id (a : (rnSc m) 1) =
      ContinuousLinearMap.id ℝ (Fin m → ℝ) :=
    IsSc1.scDeriv_eqOn (isSc1With_id univ) ((rn_relOpen_univ m).isScDomain.uniqueDiffWithinAt 1)
      (by rw [ScBanach.mem_lvlSet]; exact mem_univ _)
  refine e.trans (Prod.ext ?_ rfl)
  exact congrArg (fun L : (rnSc m) 0 →L[ℝ] (rnSc m) 0 => L v.1) h2

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))] in
/-- The tangent space of the product chart at a level-`1` point `(a, u)`:
`T_{(a, u)}(ℝᵐ × O) = ℝᵐ × T_uO`. -/
lemma ofProd_mem_tangent_iff (c : StrongBundleChart PX P) (r₀ : Fin m → ℝ)
    (q₀ : pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X)) (a : Fin m → ℝ)
    {u : c.φ.model.E 1} (hu : c.φ.model.E.toBase 1 u ∈ c.U) (w : (Fin m → ℝ) × c.φ.model.E 0) :
    w ∈ rangeS (scDeriv ((ofProd c r₀).toChart q₀).U (r ((ofProd c r₀).toChart q₀).R)
      ((a, u) : ((ofProd c r₀).toChart q₀).φ.model.E 1)) ↔
      w.2 ∈ rangeS (scDeriv c.U (r c.R) u) := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y.2, congrArg Prod.snd ((ofProd_scDeriv_r_apply c r₀ q₀ a hu y).symm.trans hy)⟩
  · rintro ⟨y, hy⟩
    exact ⟨(w.1, y), (ofProd_scDeriv_r_apply c r₀ q₀ a hu (w.1, y)).trans (Prod.ext rfl hy)⟩

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))] in
/-- **The fibres of the product chart** over a point `(a, u)` with `u ∈ O` are the fibres of `c`
over `u`: `((a, u), k) ∈ K_g ↔ (u, k) ∈ K` (`g(a, u) = φ(φ⁻¹(u)) = u`). -/
lemma mem_K_ofProd_iff (c : StrongBundleChart PX P) (r₀ : Fin m → ℝ)
    (q₀ : pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X)) {w : (Fin m → ℝ) × c.φ.model.E 0}
    (hw : w.2 ∈ c.φ.model.O) (k : c.F 0) :
    ((w, k) : ((ofProd c r₀).toChart q₀).φ.model.E 0 × c.F 0) ∈ ((ofProd c r₀).toChart q₀).K ↔
      (w.2, k) ∈ c.K := by
  change _ ∈ pullbackRetraction (ofProd c r₀).c.R (ofProd c r₀).RZ (ofProd c r₀).g ''
    ((ofProd c r₀).RZ.U ×ˢ univ) ↔ _
  rw [(ofProd c r₀).image_eq_Kg]
  have hg : (ofProd c r₀).g w = w.2 := by
    change c.φ (c.φ.symm w.2) = w.2
    exact c.φ.apply_symm_apply hw
  have hR : w ∈ (ofProd c r₀).RZ.retract := by
    rw [(ofProd c r₀).RZ_retract]
    exact ⟨mem_univ _, hw⟩
  change w ∈ (ofProd c r₀).RZ.retract ∧ ((ofProd c r₀).g w, k) ∈ c.K ↔ _
  rw [hg]
  exact ⟨fun h => h.2, fun h => ⟨hR, h⟩⟩

end PullbackChartData

section Slice

variable {B : StrongBundle PX P}

/-- **The slice direction of the linearization, at a general level-`1` point**: for an sc-smooth
section `G` of `π*P` and the product chart `pc = (r ↦ r − t) × φ` over a chart `c` of `B`, at a
level-`1` point `(a, u)` of `pc`, the slice `G(a + t, ·)` has an sc¹ principal part
`ĝ ∘ r` on `U`, and `D(Ĝ ∘ (1 × r))(a, u)(0, v) = D(ĝ ∘ r)(u) v`. -/
theorem StrongBundle.scDeriv_ofProd_slice_apply {G : (Fin m → ℝ) × X → pullbackSpace P Prod.snd}
    (hG : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsScSmoothSection G)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (t : Fin m → ℝ)
    (q₀ : pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X)) (a : Fin m → ℝ)
    {u : c.φ.model.E 1} (hu : c.φ.model.E.toBase 1 u ∈ c.U) :
    IsSc1 c.U (c.principal (pullbackSlice G (a + t)) ∘ r c.R) ∧ ∀ v : c.φ.model.E 0,
      scDeriv ((PullbackChartData.ofProd c t).toChart q₀).U
        (((PullbackChartData.ofProd c t).toChart q₀).principal G ∘
          r ((PullbackChartData.ofProd c t).toChart q₀).R)
        ((a, u) : ((PullbackChartData.ofProd c t).toChart q₀).φ.model.E 1) ((0 : Fin m → ℝ), v) =
      scDeriv c.U (c.principal (pullbackSlice G (a + t)) ∘ r c.R) u v := by
  set pc := (PullbackChartData.ofProd c t).toChart q₀ with hpc
  have hpcc : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsChart pc :=
    (PullbackChartData.ofProd c t).isChart_toChart B _ hc q₀
  have hH : IsSc1 pc.U (pc.principal G ∘ r pc.R) := hG.isSc1_principal_comp_r hpcc
  have hU := c.relOpen.isScDomain
  have hconst : IsSc1 (E := c.φ.model.E) (F := rnSc m) c.U (fun _ => a) :=
    (IsScSmooth.of_contDiffOn_finiteDimensional hU contDiffOn_const).isSc1
  have hid : IsSc1With c.U (_root_.id : c.φ.model.E 0 → c.φ.model.E 0)
      fun _ => ContinuousLinearMap.id ℝ (c.φ.model.E 0) := isSc1With_id c.U
  set ι : c.φ.model.E 0 → pc.φ.model.E 0 :=
    scPair (F := rnSc m) (fun _ => a) (_root_.id : c.φ.model.E 0 → c.φ.model.E 0) with hιdef
  have hι : IsSc1 c.U ι := hconst.scPair' hid.isSc1
  have hmaps : MapsTo ι c.U pc.U := fun w hw => ⟨mem_univ _, hw⟩
  have hHι : (pc.principal G ∘ r pc.R) ∘ ι =
      c.principal (pullbackSlice G (a + t)) ∘ r c.R := rfl
  have hcomp := (theorem_1_3_1 c.relOpen pc.relOpen hι hH hmaps).1
  rw [hHι] at hcomp
  refine ⟨hcomp, fun v => ?_⟩
  have hu1 : u ∈ c.φ.model.E.lvlSet c.U 1 := hu
  have hchain := scDeriv_comp_apply' c.relOpen pc.relOpen hι hH hmaps hu1 v
  have hlev : levelMap ι 1 u = ((a, u) : pc.φ.model.E 1) := by
    apply levelMap_eq_of_toBase_eq
    change ((rnSc m).prod c.φ.model.E).toBase 1 (a, u) = _
    rw [ScBanach.prod_toBase]
    exact Prod.ext (ScBanach.const_toBase _ 1 a) rfl
  have hc0 : scDeriv (F := rnSc m) c.U (fun _ => a) u = 0 := by
    apply ContinuousLinearMap.ext_of_comp_toBase_one (E := c.φ.model.E)
    have d1 := hconst.isSc1With_scDeriv.hasFDerivWithinAt u hu1
    have d2 : HasFDerivWithinAt
        ((fun _ : c.φ.model.E 0 => (a : (rnSc m) 0)) ∘ c.φ.model.E.toBase 1)
        ((0 : c.φ.model.E 0 →L[ℝ] (rnSc m) 0).comp (c.φ.model.E.toBase 1))
        (c.φ.model.E.lvlSet c.U 1) u := by
      rw [ContinuousLinearMap.zero_comp]; exact hasFDerivWithinAt_const _ _ _
    exact (hU.uniqueDiffWithinAt 1 u hu1).eq d1 d2
  have hid0 : scDeriv c.U (_root_.id : c.φ.model.E 0 → c.φ.model.E 0) u =
      ContinuousLinearMap.id ℝ (c.φ.model.E 0) :=
    IsSc1.scDeriv_eqOn hid (hU.uniqueDiffWithinAt 1) hu1
  have hDι : scDeriv c.U ι u v = ((0 : Fin m → ℝ), v) := by
    have h := scDeriv_scPair c.relOpen hconst hid.isSc1 hu1
    refine (congrArg (fun T : c.φ.model.E 0 →L[ℝ] ((rnSc m).prod c.φ.model.E) 0 => T v) h).trans
      ?_
    simp only [ContinuousLinearMap.prod_apply, hc0, hid0, zero_apply,
      ContinuousLinearMap.id_apply]
  rw [hlev, hDι, hHι] at hchain
  exact hchain

/-- **The linearization of `F = f + Σ λᵢ sᵢ` in the product chart, at a general level-`1`
point** (`scDeriv_paramSection_of_isScSmoothSection` at the point `(a, w)` instead of `0`): in the
product chart `(r ↦ r − r₀) × φ`,
`D(F̂ ∘ (1 × r))(a, w)(δa, δu) = D(Ĝ ∘ r)(w) δu + Σ δaᵢ ŝᵢ(r(w))`, `Ĝ = f̂ + Σ (a + r₀)ᵢ ŝᵢ`. -/
theorem StrongBundle.scDeriv_paramSection_apply {f : X → Y}
    (hf : B.IsScSmoothSection f) {s : Fin m → X → Y} (hs : ∀ i, B.IsScPlusSection (s i))
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (r₀ : Fin m → ℝ)
    (q₀ : pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X)) (a : Fin m → ℝ)
    {w : c.φ.model.E 1} (hw : c.φ.model.E.toBase 1 w ∈ c.U) (v : (Fin m → ℝ) × c.φ.model.E 0) :
    scDeriv ((PullbackChartData.ofProd c r₀).toChart q₀).U
        (((PullbackChartData.ofProd c r₀).toChart q₀).principal
          (paramSection f hf.1 s fun i => (hs i).1) ∘
            r ((PullbackChartData.ofProd c r₀).toChart q₀).R)
        ((a, w) : ((PullbackChartData.ofProd c r₀).toChart q₀).φ.model.E 1) v =
      scDeriv c.U ((fun u => c.principal f u + ∑ i, (a + r₀) i • c.principal (s i) u) ∘
          r c.R) w v.2 +
        ∑ i, v.1 i • c.principal (s i) (r c.R (c.φ.model.E.toBase 1 w)) := by
  set d := PullbackChartData.ofProd (n := m) c r₀ with hd
  set c' := d.toChart q₀ with hc'
  set Fs := paramSection f hf.1 s fun i => (hs i).1 with hFs
  have hU := c.relOpen.isScDomain
  have hU' : IsRelOpenInQuadrant (rnSc m |>.prod c.φ.model.E) (univ ×ˢ c.φ.model.C)
      (univ ×ˢ c.U) := c.relOpen.univ_prod (Fin m → ℝ)
  -- the pieces on `U`
  have hfr : IsScSmooth c.U (c.principal f ∘ r c.R) :=
    (((hf.isScSmoothRetractMap hc).comp_isScSmooth
      (c.isRetraction.baseRetraction c.relOpen) c.base_retract).snd hU).congr hU fun _ _ => rfl
  have hsr : ∀ i, IsScSmooth c.U (c.principal (s i) ∘ r c.R) := fun i => by
    have hlift : IsScSmooth (F := c.F.shift) c.U
        fun u => c.principalLift (s i) (r c.R u) :=
      (((hs i).isScSmoothRetractMap_one hc).comp_isScSmooth
        (c.isRetraction.baseRetraction c.relOpen) c.base_retract).snd hU |>.congr hU
        fun _ _ => rfl
    exact (hlift.toBase_shift hU).congr hU fun u hu => (hs i).toBase_principalLift hc (c.r_mem_O hu)
  have hGr : IsScSmooth c.U ((fun u => c.principal f u + ∑ i, (a + r₀) i • c.principal (s i) u) ∘
      r c.R) := by
    have hconst : ∀ i, IsScSmooth (F := ScBanach.const ℝ) c.U fun _ => (a + r₀) i := fun i =>
      IsScSmooth.of_contDiffOn_finiteDimensional hU contDiffOn_const
    exact (hfr.add hU (IsScSmooth.finsetSum hU _ fun i _ => (hconst i).smul hU (hsr i))).congr hU
      fun _ _ => rfl
  -- the map `Φ = F̂ ∘ (1 × r)` is sc¹ on `ℝᵐ × U`, and equal there to
  -- `Ψ(b, u) = Ĝ(r(u)) + Σ (b − a)ᵢ ŝᵢ(r(u))`
  have hc'B : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsChart c' :=
    d.isChart_toChart B _ hc q₀
  have hFsm :
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsScSmoothSection Fs := by
    rw [hFs, paramSection_eq_sectionAdd]
    exact (hf.pullback _).sectionAdd (StrongBundle.isScPlusSection_paramComb hs)
  have hΦ : IsScSmooth (univ ×ˢ c.U) (c'.principal Fs ∘ r c'.R) :=
    (((hFsm.isScSmoothRetractMap hc'B).comp_isScSmooth
      (c'.isRetraction.baseRetraction c'.relOpen) c'.base_retract).snd hU'.isScDomain).congr
      hU'.isScDomain fun _ _ => rfl
  have hΦΨ : ∀ p ∈ (univ ×ˢ c.U : Set ((Fin m → ℝ) × c.φ.model.E 0)),
      (c'.principal Fs ∘ r c'.R) p =
        ((fun u => c.principal f u + ∑ i, (a + r₀) i • c.principal (s i) u) ∘ r c.R) p.2 +
          ∑ i, (p.1 i - a i) • (c.principal (s i) ∘ r c.R) p.2 := by
    intro p hp
    have hrp : r c.R p.2 ∈ c.φ.model.O := c.r_mem_O hp.2
    have := PullbackChartData.ofProd_principal_paramSection c r₀ q₀ hf.1
      (fun i => (hs i).1) (w := (p.1, r c.R p.2)) hrp
    refine this.trans ?_
    simp only [Function.comp_apply, Pi.add_apply, add_smul, sub_smul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    abel
  -- the derivative on level `1`
  have hw1 : w ∈ c.φ.model.E.lvlSet c.U 1 := hw
  have hp1 : ((a, w) : (rnSc m |>.prod c.φ.model.E) 1) ∈
      (rnSc m |>.prod c.φ.model.E).lvlSet (univ ×ˢ c.U) 1 := by
    rw [lvlSet_prod]; exact ⟨mem_univ _, hw⟩
  set D := scDeriv c.U ((fun u => c.principal f u + ∑ i, (a + r₀) i • c.principal (s i) u) ∘
    r c.R) w with hD
  set L : (Fin m → ℝ) × c.φ.model.E 0 →L[ℝ] c.F 0 :=
    D.comp (ContinuousLinearMap.snd ℝ (Fin m → ℝ) (c.φ.model.E 0)) +
      ∑ i, ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.fst ℝ (Fin m → ℝ) (c.φ.model.E 0))).smulRight
          (c.principal (s i) (r c.R (c.φ.model.E.toBase 1 w))) with hL
  have hmaps : MapsTo (Prod.snd : (Fin m → ℝ) × c.φ.model.E 1 → c.φ.model.E 1)
      ((rnSc m |>.prod c.φ.model.E).lvlSet (univ ×ˢ c.U) 1) (c.φ.model.E.lvlSet c.U 1) := by
    intro p hp
    have := hp
    rw [ScBanach.mem_lvlSet, ScBanach.prod_toBase] at this
    exact this.2
  have hb : ∀ p : (rnSc m |>.prod c.φ.model.E) 1,
      (rnSc m |>.prod c.φ.model.E).toBase 1 p = (p.1, c.φ.model.E.toBase 1 p.2) := fun p => by
    rw [ScBanach.prod_toBase, ScBanach.const_toBase]
  have hderG := (hGr.isSc1.isSc1With_scDeriv.hasFDerivWithinAt w hw1).comp
    ((a, w) : (rnSc m |>.prod c.φ.model.E) 1) hasFDerivWithinAt_snd hmaps
  have hderS : ∀ i ∈ (Finset.univ : Finset (Fin m)), HasFDerivWithinAt
      (fun p : (rnSc m |>.prod c.φ.model.E) 1 =>
        (p.1 i - a i) • ((c.principal (s i) ∘ r c.R) ∘ c.φ.model.E.toBase 1) p.2)
      ((((a, w) : (rnSc m |>.prod c.φ.model.E) 1).1 i - a i) •
          ((scDeriv c.U (c.principal (s i) ∘ r c.R) w).comp (c.φ.model.E.toBase 1)).comp
            (ContinuousLinearMap.snd ℝ (Fin m → ℝ) (c.φ.model.E 1)) +
        ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (Fin m → ℝ)
          (c.φ.model.E 1))).smulRight
          (((c.principal (s i) ∘ r c.R) ∘ c.φ.model.E.toBase 1)
            ((a, w) : (rnSc m |>.prod c.φ.model.E) 1).2))
      ((rnSc m |>.prod c.φ.model.E).lvlSet (univ ×ˢ c.U) 1) (a, w) := by
    intro i _
    have h1 : HasFDerivWithinAt (fun p : (rnSc m |>.prod c.φ.model.E) 1 => p.1 i - a i)
        ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (Fin m → ℝ)
          (c.φ.model.E 1))) ((rnSc m |>.prod c.φ.model.E).lvlSet (univ ×ˢ c.U) 1) (a, w) :=
      ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (Fin m → ℝ)
        (c.φ.model.E 1))).hasFDerivWithinAt.sub_const (a i)
    have h2 := ((hsr i).isSc1.isSc1With_scDeriv.hasFDerivWithinAt w hw1).comp
      ((a, w) : (rnSc m |>.prod c.φ.model.E) 1) hasFDerivWithinAt_snd hmaps
    exact h1.fun_smul h2
  have hderΨ := hderG.add (HasFDerivWithinAt.fun_sum hderS)
  have hderΦ : HasFDerivWithinAt ((c'.principal Fs ∘ r c'.R) ∘
      (rnSc m |>.prod c.φ.model.E).toBase 1) (L.comp ((rnSc m |>.prod c.φ.model.E).toBase 1))
      ((rnSc m |>.prod c.φ.model.E).lvlSet (univ ×ˢ c.U) 1) (a, w) := by
    refine (hderΨ.congr (fun p hp => ?_) ?_).congr_fderiv ?_
    · have := hΦΨ _ hp
      rw [hb] at this
      exact this
    · have := hΦΨ _ hp1
      rw [hb] at this
      exact this
    · refine ContinuousLinearMap.ext fun p => ?_
      simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
        FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', ContinuousLinearMap.proj_apply,
        sub_self, zero_smul, zero_add, hL, hb]
      rfl
  have hderΦ' := hΦ.isSc1.isSc1With_scDeriv.hasFDerivWithinAt _ hp1
  have heq := ContinuousLinearMap.ext_of_comp_toBase_one (E := rnSc m |>.prod c.φ.model.E)
    ((hU'.isScDomain.uniqueDiffWithinAt 1 _ hp1).eq hderΦ' hderΦ)
  have hv := congrArg (fun T : (rnSc m |>.prod c.φ.model.E) 0 →L[ℝ] c.F 0 => T v) heq
  refine hv.trans ?_
  simp only [hL, add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', ContinuousLinearMap.proj_apply]

end Slice

end ProdChart

/-! ### The stabilized section in the product chart over `ℝᵏ × ℝⁿ × X` -/

section Stab

variable {n k : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  [ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]

/-- **The parameter derivative of `G` at `(q, z)`**: `σ ↦ D(Ĝ ∘ r)(q, z)(σ, 0)`, the derivative
in the `ℝⁿ`-directions of the principal part of a section `G` of `π*P` in the product chart
`c_Z = (q ↦ q) × φ` (the `σ`-terms of the linearization of `F`). -/
def StrongBundleChart.paramDerivAt (c : StrongBundleChart PX P)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
    (G : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) (q : Fin n → ℝ)
    (z : c.φ.model.E 1) : (Fin n → ℝ) →L[ℝ] c.F 0 :=
  (scDeriv ((PullbackChartData.ofProd c 0).toChart q₀).U
    (((PullbackChartData.ofProd c 0).toChart q₀).principal G ∘
      r ((PullbackChartData.ofProd c 0).toChart q₀).R)
    ((q, z) : ((PullbackChartData.ofProd c 0).toChart q₀).φ.model.E 1)).comp
    (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (c.φ.model.E 0))

/-- **The linearization of the stabilized section at a general point**: for an sc-smooth section
`G` of `π*P → ℝⁿ × X`, sc⁺-sections `s₁, …, s_k` and `F(λ, (q, y)) = G(q, y) + Σ λᵢ sᵢ(q, y)`,
in the product chart `χ` over `c_Z = (q ↦ q) × φ` at the level-`1` point `(0, (q, z))`,
`D(F̂ ∘ r)(0, (q, z))(λ, (σ, v)) = D(ĝ_q ∘ r)(z) v + Σ λᵢ ŝᵢ(q, ·)(z) + D(Ĝ ∘ r)(q, z)(σ, 0)`,
with `g_q = G(q, ·)` the slice. -/
theorem StrongBundle.scDeriv_paramSection_ofProd_ofProd
    {G : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hG : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScSmoothSection G)
    {s : Fin k → (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection (s i))
    {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
    (q₁ : pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))
    (q : Fin n → ℝ) {z : c.φ.model.E 1} (hzO : c.φ.model.E.toBase 1 z ∈ c.φ.model.O)
    (w : (Fin k → ℝ) × ((Fin n → ℝ) × c.φ.model.E 0)) :
    scDeriv ((PullbackChartData.ofProd ((PullbackChartData.ofProd c 0).toChart q₀) 0).toChart q₁).U
        (((PullbackChartData.ofProd ((PullbackChartData.ofProd c 0).toChart q₀) 0).toChart
          q₁).principal (paramSection G hG.1 s fun i => (hs i).1) ∘
          r ((PullbackChartData.ofProd ((PullbackChartData.ofProd c 0).toChart q₀) 0).toChart
            q₁).R)
        ((0, (q, z)) : ((PullbackChartData.ofProd ((PullbackChartData.ofProd c 0).toChart q₀)
          0).toChart q₁).φ.model.E 1) w =
      scDeriv c.U (c.principal (pullbackSlice G q) ∘ r c.R) z w.2.2 +
        ∑ i, w.1 i • c.principal (pullbackSlice (s i) q) (c.φ.model.E.toBase 1 z) +
        c.paramDerivAt q₀ G q z w.2.1 := by
  set cZ := (PullbackChartData.ofProd c 0).toChart q₀ with hcZ
  have hcZc : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsChart cZ :=
    (PullbackChartData.ofProd c 0).isChart_toChart B _ hc q₀
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U := mem_U_of_mem_O c.isRetraction (c.r_image ▸ hzO)
  have hqzU : cZ.φ.model.E.toBase 1 ((q, z) : cZ.φ.model.E 1) ∈ cZ.U := by
    change ((rnSc n).prod c.φ.model.E).toBase 1 (q, z) ∈ univ ×ˢ c.U
    rw [ScBanach.prod_toBase]
    exact ⟨mem_univ _, hzU⟩
  have h1 := StrongBundle.scDeriv_paramSection_apply hG hs hcZc 0 q₁ 0 hqzU w
  have hfun : (fun u => cZ.principal G u + ∑ i, ((0 : Fin k → ℝ) + 0) i • cZ.principal (s i) u) =
      cZ.principal G := funext fun u => by simp
  rw [hfun] at h1
  refine h1.trans ?_
  have hsplit : w.2 = ((0 : Fin n → ℝ), w.2.2) + (w.2.1, (0 : c.φ.model.E 0)) := by
    ext <;> simp
  have hsl := (StrongBundle.scDeriv_ofProd_slice_apply hG hc 0 q₀ q hzU).2 w.2.2
  rw [add_zero] at hsl
  have hr : r c.R (c.φ.model.E.toBase 1 z) = c.φ.model.E.toBase 1 z :=
    r_eq_self c.isRetraction (c.r_image ▸ hzO)
  have hval : ∀ i, cZ.principal (s i) (r cZ.R (cZ.φ.model.E.toBase 1 ((q, z) : cZ.φ.model.E 1))) =
      c.principal (pullbackSlice (s i) q) (c.φ.model.E.toBase 1 z) := fun i => by
    have : cZ.principal (s i) (r cZ.R (cZ.φ.model.E.toBase 1 ((q, z) : cZ.φ.model.E 1))) =
        c.principal (pullbackSlice (s i) (q + 0)) (r c.R (c.φ.model.E.toBase 1 z)) := by
      change cZ.principal (s i) (r cZ.R (((rnSc n).prod c.φ.model.E).toBase 1 (q, z))) = _
      rw [ScBanach.prod_toBase, ScBanach.const_toBase]
      rfl
    rw [this, add_zero, hr]
  have key : scDeriv cZ.U (cZ.principal G ∘ r cZ.R) ((q, z) : cZ.φ.model.E 1) w.2 =
      scDeriv c.U (c.principal (pullbackSlice G q) ∘ r c.R) z w.2.2 +
        c.paramDerivAt q₀ G q z w.2.1 :=
    (congrArg (fun v => scDeriv cZ.U (cZ.principal G ∘ r cZ.R) ((q, z) : cZ.φ.model.E 1) v)
      hsplit).trans ((map_add _ _ _).trans (congrArg₂ (· + ·) hsl rfl))
  have hsum : ∑ i, w.1 i • cZ.principal (s i)
        (r cZ.R (cZ.φ.model.E.toBase 1 ((q, z) : cZ.φ.model.E 1))) =
      ∑ i, w.1 i • c.principal (pullbackSlice (s i) q) (c.φ.model.E.toBase 1 z) :=
    Finset.sum_congr rfl fun i _ => congrArg (fun y => w.1 i • y) (hval i)
  exact (congrArg₂ (· + ·) key hsum).trans (add_right_comm _ _ _)

/-- `ℓ(λ, (σ, v)) = σ`: the `ℝⁿ`-component of a vector of `ℝᵏ × ℝⁿ × E₀` (the text's `dt`). -/
def sliceProj (k n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (Fin k → ℝ) × ((Fin n → ℝ) × E) →L[ℝ] (Fin n → ℝ) :=
  (ContinuousLinearMap.fst ℝ (Fin n → ℝ) E).comp
    (ContinuousLinearMap.snd ℝ (Fin k → ℝ) ((Fin n → ℝ) × E))

omit [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- `ℓ(λ, (σ, v)) = σ`. -/
@[simp] lemma sliceProj_apply (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : (Fin k → ℝ) × ((Fin n → ℝ) × E)) : sliceProj k n E w = w.2.1 := rfl

/-- `J(v, λ) = (λ, (0, v))`: the inclusion `T ⊕ ℝᵏ → ℝᵏ × ℝⁿ × E₀` of the slice directions. -/
def sliceIncl (k n : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : Submodule ℝ E) : ↥T × (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) × ((Fin n → ℝ) × E) :=
  (ContinuousLinearMap.snd ℝ ↥T (Fin k → ℝ)).prod
    ((ContinuousLinearMap.inr ℝ (Fin n → ℝ) E).comp
      (T.subtypeL.comp (ContinuousLinearMap.fst ℝ ↥T (Fin k → ℝ))))

omit [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- `J(v, λ) = (λ, (0, v))`. -/
@[simp] lemma sliceIncl_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : Submodule ℝ E) (vμ : ↥T × (Fin k → ℝ)) :
    sliceIncl k n T vμ = (vμ.2, ((0 : Fin n → ℝ), (vμ.1 : E))) := rfl

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))] in
/-- **The tangent space of `χ` at `(0, (q, z))`**: `T_{(0, (q, z))}(ℝᵏ × ℝⁿ × O) = ℝᵏ × ℝⁿ × T_zO`
(`D(1 × 1 × r) = 1 × 1 × Dr`). -/
lemma mem_tangent_ofProd_ofProd_iff (c : StrongBundleChart PX P)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
    (q₁ : pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))
    (q : Fin n → ℝ) {z : c.φ.model.E 1} (hzU : c.φ.model.E.toBase 1 z ∈ c.U)
    (w : (Fin k → ℝ) × ((Fin n → ℝ) × c.φ.model.E 0)) :
    w ∈ rangeS (scDeriv
      ((PullbackChartData.ofProd ((PullbackChartData.ofProd c 0).toChart q₀) 0).toChart q₁).U
      (r ((PullbackChartData.ofProd ((PullbackChartData.ofProd c 0).toChart q₀) 0).toChart q₁).R)
      ((0, (q, z)) : ((PullbackChartData.ofProd ((PullbackChartData.ofProd c 0).toChart q₀)
        0).toChart q₁).φ.model.E 1)) ↔ w.2.2 ∈ rangeS (scDeriv c.U (r c.R) z) := by
  have hqzU : ((PullbackChartData.ofProd c 0).toChart q₀).φ.model.E.toBase 1
      ((q, z) : ((PullbackChartData.ofProd c 0).toChart q₀).φ.model.E 1) ∈
        ((PullbackChartData.ofProd c 0).toChart q₀).U := by
    change ((rnSc n).prod c.φ.model.E).toBase 1 (q, z) ∈ univ ×ˢ c.U
    rw [ScBanach.prod_toBase]
    exact ⟨mem_univ _, hzU⟩
  exact (PullbackChartData.ofProd_mem_tangent_iff _ 0 q₁ 0 hqzU w).trans
    (PullbackChartData.ofProd_mem_tangent_iff c 0 q₀ q hzU w.2)

/-- **The slice kernel** (the text's `L_t = ker F_t'(φ(t), 0)` and the middle of the exact
sequence (96)): in the product chart `χ` at `(0, (q, z))`, the vectors of `ker Lin_F` with
vanishing `ℝⁿ`-component are the images `J(v, λ) = (λ, (0, v))` of the kernel of
`T ⊕ φ : T_zO ⊕ ℝᵏ → K_z`, for `T = Lin_{G(q, ·)}(z)` and `φ(λ) = Σ λᵢ ŝᵢ(q, ·)(φ(x))`. -/
theorem linKer_inf_ker_sliceProj_eq_map
    {G : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hG : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScSmoothSection G)
    {s : Fin k → (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection (s i))
    {x : X} (p : ChartPoint B x) (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
    (q₁ : pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))
    (q : Fin n → ℝ) (T : ↥p.T →L[ℝ] ↥p.K)
    (hT : ∀ v, (T v : p.c.F 0) = linAt p.c.U p.c.R (p.c.principal (pullbackSlice G q)) p.z v)
    (φ : (Fin k → ℝ) →L[ℝ] ↥p.K)
    (hφ : ∀ μ, (φ μ : p.c.F 0) = ∑ i, μ i • p.c.principal (pullbackSlice (s i) q) (p.c.φ x)) :
    ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀) 0).toChart
        q₁).linKer (paramSection G hG.1 s fun i => (hs i).1)
        ((0, (q, p.z)) : ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀)
          0).toChart q₁).φ.model.E 1) ⊓
        LinearMap.ker (sliceProj k n (p.c.φ.model.E 0)).toLinearMap =
      (LinearMap.ker (T.coprod φ).toLinearMap).map (sliceIncl k n p.T).toLinearMap := by
  have hzO : p.c.φ.model.E.toBase 1 p.z ∈ p.c.φ.model.O := p.c.r_image ▸ p.mem_O
  have hform := StrongBundle.scDeriv_paramSection_ofProd_ofProd hG hs p.isChart q₀ q₁ q hzO
  have hval : ∀ μ : Fin k → ℝ, ∑ i, μ i • p.c.principal (pullbackSlice (s i) q)
      (p.c.φ.model.E.toBase 1 p.z) = (φ μ : p.c.F 0) := fun μ => by rw [hφ, p.toBase_z]
  refine Submodule.ext fun (w : (Fin k → ℝ) × ((Fin n → ℝ) × p.c.φ.model.E 0)) => ?_
  obtain ⟨μ, σ, v⟩ := w
  constructor
  · rintro ⟨hw1, hw2⟩
    have hσ : σ = 0 := hw2
    subst hσ
    obtain ⟨hwT, hlin⟩ := (StrongBundleChart.mem_linKer_iff _ _ _ _).1 hw1
    have hv : v ∈ p.T := (mem_tangent_ofProd_ofProd_iff p.c q₀ q₁ q p.mem_U _).1 hwT
    have h := (hform _).symm.trans ((linAt_apply _ _ _).symm.trans hlin)
    have h' : scDeriv p.c.U (p.c.principal (pullbackSlice G q) ∘ r p.c.R) p.z v +
        (φ μ : p.c.F 0) = 0 := by
      have h0 : p.c.paramDerivAt q₀ G q p.z 0 = 0 := map_zero _
      rw [← hval]
      exact (add_zero _).symm.trans ((congrArg (fun y => _ + y) h0).symm.trans h)
    refine ⟨(⟨v, hv⟩, μ), ?_, rfl⟩
    refine LinearMap.mem_ker.2 (Subtype.ext ?_)
    change ((T ⟨v, hv⟩ + φ μ : ↥p.K) : p.c.F 0) = 0
    rw [Submodule.coe_add, hT]
    exact h'
  · rintro ⟨⟨v', μ'⟩, hker, he⟩
    have hker' : ((T v' + φ μ' : ↥p.K) : p.c.F 0) = 0 := congrArg Subtype.val hker
    rw [Submodule.coe_add, hT] at hker'
    have he' : ((μ', ((0 : Fin n → ℝ), (v' : p.c.φ.model.E 0))) :
        (Fin k → ℝ) × ((Fin n → ℝ) × p.c.φ.model.E 0)) = (μ, σ, v) := he
    obtain ⟨h1, h2⟩ := Prod.mk.inj he'
    obtain ⟨h3, h4⟩ := Prod.mk.inj h2
    subst h1 h3 h4
    refine ⟨(StrongBundleChart.mem_linKer_iff _ _ _ _).2
      ⟨(mem_tangent_ofProd_ofProd_iff p.c q₀ q₁ q p.mem_U _).2 v'.2, ?_⟩, rfl⟩
    refine (hform _).trans ?_
    have h0 : p.c.paramDerivAt q₀ G q p.z 0 = 0 := map_zero _
    refine ((congrArg (fun y => _ + y) h0).trans (add_zero _)).trans ?_
    rw [hval]
    exact hker'

omit [ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))] in
/-- **The operators `T` and `φ` exist** at a zero `x` of the slice `G(q, ·)`:
`T = Lin_{G(q, ·)}(z) : T_zO → K_z` (its values lie in `K_z` at a zero, `rho_scDeriv_comp_r`)
and `φ(λ) = Σ λᵢ ŝᵢ(q, ·)(φ(x))` (each `ŝᵢ(q, ·)(φ(x))` lies in the fibre `K_z`). -/
theorem exists_sliceOps
    {G : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hG : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScSmoothSection G)
    {s : Fin k → (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection (s i))
    {x : X} (p : ChartPoint B x) (q : Fin n → ℝ) (hx0 : IsZeroAt P (pullbackSlice G q) x) :
    ∃ (T : ↥p.T →L[ℝ] ↥p.K) (φ : (Fin k → ℝ) →L[ℝ] ↥p.K),
      (∀ v, (T v : p.c.F 0) = linAt p.c.U p.c.R (p.c.principal (pullbackSlice G q)) p.z v) ∧
      ∀ μ, (φ μ : p.c.F 0) = ∑ i, μ i • p.c.principal (pullbackSlice (s i) q) (p.c.φ x) := by
  have hfr : IsSc1 p.c.U (p.c.principal (pullbackSlice G q) ∘ r p.c.R) := by
    have h := (StrongBundle.scDeriv_ofProd_slice_apply hG p.isChart 0 (G (q, x)) q p.mem_U).1
    rwa [add_zero] at h
  have hK : ∀ v, scDeriv p.c.U (p.c.principal (pullbackSlice G q) ∘ r p.c.R) p.z v ∈ p.K :=
    fun v => ⟨_, rho_scDeriv_comp_r p.c.relOpen p.c.isRetraction hfr
      (fun y hy => p.c.principal_mem_K (hG.1.pullbackSlice q) (p.c.r_image ▸ hy)) p.mem_O
      (by rw [p.toBase_z]; exact (p.c.isZeroAt_iff (hG.1.pullbackSlice q) p.mem_source).1 hx0) v⟩
  have he : ∀ i, p.c.principal (pullbackSlice (s i) q) (p.c.φ x) ∈ p.K := fun i => by
    refine (mem_rangeS_ρCLM_iff p.c.isRetraction p.mem_O p.mem_U).2 ?_
    rw [p.toBase_z]
    exact p.c.principal_mem_K ((hs i).1.pullbackSlice q) (p.c.φ.mapsTo_model x p.mem_source)
  refine ⟨((scDeriv p.c.U (p.c.principal (pullbackSlice G q) ∘ r p.c.R) p.z).comp
    p.T.subtypeL).codRestrict p.K fun v => hK v,
    ∑ i, (ContinuousLinearMap.proj i).smulRight (⟨_, he i⟩ : ↥p.K), fun v => rfl, fun μ => ?_⟩
  simp

/-- **`T` is in `Lin(f, x)`** (Definition 6.2.1 (preprint 6.1)): for `G = f̃ + S` with `f` sc-Fredholm and `S` an
sc⁺-section of `π*P`, the slice is `G(q, ·) = f + S(q, ·)` with `S(q, ·)` an sc⁺-section of `P`
(`IsScPlusSection.pullbackSlice`), so `T = Lin_{f + S(q, ·)}(z)` is `(f + s)'(x) + a` with
`s = S(q, ·)` and `a = 0` (Definition 6.2.1 (preprint 6.1)). -/
theorem mem_linSet_sectionAdd_pullbackSlice {f : X → Y} (hf : B.IsScFredholmSection f)
    {S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S)
    {x : X} (p : ChartPoint B x) (q : Fin n → ℝ)
    (hx0 : IsZeroAt P (sectionAdd P f (pullbackSlice S q)) x) (T : ↥p.T →L[ℝ] ↥p.K)
    (hT : ∀ v, (T v : p.c.F 0) =
      linAt p.c.U p.c.R (p.c.principal (sectionAdd P f (pullbackSlice S q))) p.z v) :
    T ∈ p.linSet f := by
  have hSq := hS.pullbackSlice q
  have hxs : x ∈ PX.smoothSet := (theorem_3_1_18_preprint hf hSq).mem_smoothSet_of_isZeroAt hx0
  exact ⟨_, hSq, hx0, 0, p.isScPlusOp_zero hxs, fun v => by rw [hT]; simp⟩

/-- A constant map `ℝᵐ → ℝⁿ` is an sc-smooth map of the M-polyfolds `ℝᵐ → ℝⁿ`. -/
private theorem isScSmoothMap_rn_const {m m' : ℕ} (b : Fin m' → ℝ) :
    (rnPolyfold m).IsScSmoothMap (rnPolyfold m') fun _ => b := by
  refine MPolyfold.isScSmoothMap_of_local fun x => ⟨rnChart m 0, rnChart m' 0, univ,
    isChart_rnChart 0, isChart_rnChart 0, isOpen_univ, mem_univ x, subset_univ _,
    mapsTo_univ _ _, ?_⟩
  have himg : rnChart m 0 '' univ = univ :=
    eq_univ_of_forall fun (r : Fin m → ℝ) => ⟨r, mem_univ _, show r - 0 = r from sub_zero r⟩
  rw [himg, rnChart_model_O]
  change IsScSmoothRetractMap (rnSc m) univ univ (rnSc m') univ univ (fun _ => b - 0)
  exact isScSmoothRetractMap_const_of_contDiff (V := Fin m → ℝ) (V' := Fin m' → ℝ) contDiff_const

/-- **`T ⊕ φ` is onto** (the surjectivity of `c` in the exact sequence (96)): let `G` be an
sc-smooth section of `π*P`, `Φ : ℝⁿ → X` sc-smooth with `G(q', Φ(q')) = 0` for `q'` near `q`,
`x = Φ(q)`, and `F(λ, (q', y)) = G(q', y) + Σ λᵢ sᵢ(q', y)` with `F'(0, (q, x))` onto
(`IsLinSurjAt`).  Then `T ⊕ φ : T_zO ⊕ ℝᵏ → K_z` is onto.  *Proof*: `Lin_F(0, (q, z))` is onto
`K_z` in the product chart `χ` (`linAt_surjective`); its value at `(λ, (σ, v))` is
`T v + φ λ + D_q σ` (`scDeriv_paramSection_ofProd_ofProd`), and `D_q σ = −T v'` for some
`v' ∈ T_zO`, since the derivative of the curve `q' ↦ (0, (q', Φ(q')))` of zeros of `F` lies in
`ker Lin_F` (`fderiv_mem_linKer`) and has components `(0, (σ, v'))`. -/
theorem surjective_coprod_of_isLinSurjAt
    {G : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hG : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScSmoothSection G)
    {s : Fin k → (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection (s i))
    {x : X} (p : ChartPoint B x) (q : Fin n → ℝ) {Φ : (Fin n → ℝ) → X}
    (hΦ : (rnPolyfold n).IsScSmoothMap PX Φ) (hΦq : Φ q = x)
    (hΦ0 : ∀ᶠ q' in 𝓝 q, IsZeroAt (pullbackProj P Prod.snd) G (q', Φ q'))
    (hsurj : ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold k) ((rnPolyfold n).prod PX))).IsLinSurjAt
        (paramSection G hG.1 s fun i => (hs i).1) (0, (q, x)))
    (T : ↥p.T →L[ℝ] ↥p.K)
    (hT : ∀ v, (T v : p.c.F 0) = linAt p.c.U p.c.R (p.c.principal (pullbackSlice G q)) p.z v)
    (φ : (Fin k → ℝ) →L[ℝ] ↥p.K)
    (hφ : ∀ μ, (φ μ : p.c.F 0) = ∑ i, μ i • p.c.principal (pullbackSlice (s i) q) (p.c.φ x)) :
    Surjective (T.coprod φ) := by
  subst hΦq
  obtain ⟨q₀⟩ : Nonempty (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) := ⟨G (q, Φ q)⟩
  obtain ⟨q₁⟩ : Nonempty (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X)) :=
    ⟨paramSection G hG.1 s (fun i => (hs i).1) (0, (q, Φ q))⟩
  set cZ := (PullbackChartData.ofProd p.c 0).toChart q₀ with hcZ
  set χ := (PullbackChartData.ofProd cZ 0).toChart q₁ with hχ
  have hcZc : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsChart cZ :=
    (PullbackChartData.ofProd p.c 0).isChart_toChart B _ p.isChart q₀
  have hχc : ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold k) ((rnPolyfold n).prod PX))).IsChart χ :=
    (PullbackChartData.ofProd cZ 0).isChart_toChart _ _ hcZc q₁
  have hsrc : ((0 : Fin k → ℝ), (q, Φ q)) ∈ χ.φ.source := ⟨mem_univ _, mem_univ _, p.mem_source⟩
  have hz' : χ.φ.model.E.toBase 1 ((0, (q, p.z)) : χ.φ.model.E 1) =
      χ.φ ((0 : Fin k → ℝ), (q, Φ q)) := by
    change ((rnSc k).prod ((rnSc n).prod p.c.φ.model.E)).toBase 1 (0, (q, p.z)) =
      ((0 : Fin k → ℝ) - 0, ((q : Fin n → ℝ) - 0, p.c.φ (Φ q)))
    rw [ScBanach.prod_toBase, ScBanach.prod_toBase, ScBanach.const_toBase, ScBanach.const_toBase,
      p.toBase_z, sub_zero, sub_zero]
  have hF0 : ∀ᶠ q' in 𝓝 q, IsZeroAt
      (pullbackProj (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X)) Prod.snd)
      (paramSection G hG.1 s fun i => (hs i).1) ((0 : Fin k → ℝ), (q', Φ q')) :=
    hΦ0.mono fun q' h => by
      rw [isZeroAt_paramSection_iff]
      change IsZeroAt _ (paramSlice G hG.1 s (fun i => (hs i).1) 0) (q', Φ q')
      rw [paramSlice_zero]
      exact h
  have hFsm : ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold k) ((rnPolyfold n).prod PX))).IsScSmoothSection
        (paramSection G hG.1 s fun i => (hs i).1) := by
    rw [paramSection_eq_sectionAdd]
    exact (hG.pullback _).sectionAdd (StrongBundle.isScPlusSection_paramComb hs)
  have hsurjχ := hsurj.linAt_surjective hFsm hF0.self_of_nhds hχc hsrc hz'
  have hzO : p.c.φ.model.E.toBase 1 p.z ∈ p.c.φ.model.O := p.c.r_image ▸ p.mem_O
  have hform := StrongBundle.scDeriv_paramSection_ofProd_ofProd hG hs p.isChart q₀ q₁ q hzO
  have hval : ∀ μ : Fin k → ℝ, ∑ i, μ i • p.c.principal (pullbackSlice (s i) q)
      (p.c.φ.model.E.toBase 1 p.z) = (φ μ : p.c.F 0) := fun μ => by rw [hφ, p.toBase_z]
  -- the curve `q' ↦ (0, (q', Φ(q')))` of zeros of `F`
  have hΓ : (rnPolyfold n).IsScSmoothMap ((rnPolyfold k).prod ((rnPolyfold n).prod PX))
      (fun q' => ((0 : Fin k → ℝ), (q', Φ q'))) :=
    MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_rn_const 0)
      (MPolyfold.IsScSmoothOn.prodMk MPolyfold.isScSmoothMap_id hΦ)
  have hcurve : ∀ σ : Fin n → ℝ, ∃ v ∈ p.T,
      scDeriv p.c.U (p.c.principal (pullbackSlice G q) ∘ r p.c.R) p.z v +
        p.c.paramDerivAt q₀ G q p.z σ = 0 := by
    intro σ
    obtain ⟨hd, hmem⟩ := fderiv_mem_linKer hFsm hχc hΓ hsrc hF0 _ hz' σ
    set Lv : (Fin k → ℝ) × ((Fin n → ℝ) × p.c.φ.model.E 0) :=
      fderiv ℝ (fun q' => χ.φ ((0 : Fin k → ℝ), (q', Φ q'))) q σ with hLv
    have hd' : HasFDerivAt (fun q' : Fin n → ℝ => (((0 : Fin k → ℝ) - 0, (q' - 0, p.c.φ (Φ q'))) :
        (Fin k → ℝ) × ((Fin n → ℝ) × p.c.φ.model.E 0)))
        (fderiv ℝ (fun q' => χ.φ ((0 : Fin k → ℝ), (q', Φ q'))) q :
          (Fin n → ℝ) →L[ℝ] (Fin k → ℝ) × ((Fin n → ℝ) × p.c.φ.model.E 0)) q :=
      hd.hasFDerivAt
    have h1 : Lv.1 = 0 := by
      have := hd'.fst.unique (hasFDerivAt_const ((0 : Fin k → ℝ) - 0) q)
      exact congrArg (fun L : (Fin n → ℝ) →L[ℝ] (Fin k → ℝ) => L σ) this
    have h2 : Lv.2.1 = σ := by
      have := hd'.snd.fst.unique ((hasFDerivAt_id q).sub_const 0)
      exact congrArg (fun L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => L σ) this
    obtain ⟨hLT, hLlin⟩ := (StrongBundleChart.mem_linKer_iff _ _ _ _).1 hmem
    refine ⟨Lv.2.2, (mem_tangent_ofProd_ofProd_iff p.c q₀ q₁ q p.mem_U Lv).1 hLT, ?_⟩
    have h := (hform Lv).symm.trans ((linAt_apply _ _ _).symm.trans hLlin)
    rw [h1, h2] at h
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] at h
    exact h
  have key : ∀ wv : (Fin k → ℝ) × ((Fin n → ℝ) × p.c.φ.model.E 0),
      wv ∈ rangeS (scDeriv χ.U (r χ.R) ((0, (q, p.z)) : χ.φ.model.E 1)) →
      ∃ u : ↥p.T × (Fin k → ℝ), ((T.coprod φ u : ↥p.K) : p.c.F 0) =
        scDeriv χ.U (χ.principal (paramSection G hG.1 s fun i => (hs i).1) ∘ r χ.R)
          ((0, (q, p.z)) : χ.φ.model.E 1) wv := by
    intro wv hwv
    obtain ⟨v', hv'T, hv'⟩ := hcurve wv.2.1
    have hvT : wv.2.2 - v' ∈ p.T :=
      sub_mem ((mem_tangent_ofProd_ofProd_iff p.c q₀ q₁ q p.mem_U wv).1 hwv) hv'T
    refine ⟨(⟨wv.2.2 - v', hvT⟩, wv.1), Eq.trans ?_ (hform wv).symm⟩
    change (T ⟨_, hvT⟩ : p.c.F 0) + (φ wv.1 : p.c.F 0) = _
    rw [hT, ← hval, linAt_apply]
    change scDeriv p.c.U (p.c.principal (pullbackSlice G q) ∘ r p.c.R) p.z (wv.2.2 - v') + _ = _
    rw [map_sub, eq_neg_of_add_eq_zero_right hv']
    abel
  intro y
  have hyc : (p.c.φ (Φ q), (y : p.c.F 0)) ∈ p.c.K := by
    have h := (mem_rangeS_ρCLM_iff p.c.isRetraction p.mem_O p.mem_U).1 y.2
    rwa [p.toBase_z] at h
  have hw2 : p.c.φ (Φ q) ∈ p.c.φ.model.O := p.c.φ.mapsTo_model _ p.mem_source
  have hw1 : cZ.φ (q, Φ q) ∈ cZ.φ.model.O := cZ.φ.mapsTo_model _ ⟨mem_univ _, p.mem_source⟩
  have hyK : (χ.φ ((0 : Fin k → ℝ), (q, Φ q)), (y : p.c.F 0)) ∈ χ.K :=
    (PullbackChartData.mem_K_ofProd_iff cZ 0 q₁ (w := ((0 : Fin k → ℝ) - 0, cZ.φ (q, Φ q)))
      hw1 _).2 ((PullbackChartData.mem_K_ofProd_iff p.c 0 q₀ (w := (q - 0, p.c.φ (Φ q)))
        hw2 _).2 hyc)
  obtain ⟨w, hw⟩ := hsurjχ _ hyK
  obtain ⟨u, hu⟩ := key w.1 w.2
  exact ⟨u, Subtype.ext (hu.trans ((linAt_apply _ _ _).symm.trans hw))⟩

/-- **The slice kernel of the stabilized section** (the text's `L_t` and the exact
sequence (96) at a point of `Φ`): let `f` be sc-Fredholm, `S` and `s₁, …, s_k` sc⁺-sections of
`π*P`, `G = f̃ + S`, `F(λ, (q', y)) = G(q', y) + Σ λᵢ sᵢ(q', y)`, and `Φ : ℝⁿ → X` sc-smooth with
`G(q', Φ(q')) = 0` near `q` and `F'(0, (q, x))` onto, `x = Φ(q)`.  At every chart point
`p = (c, z)` of `x` there are `T ∈ Lin(f, x)`, namely `T = Lin_{f + S(q, ·)}(z)`, and
`φ(λ) = Σ λᵢ ŝᵢ(q, ·)(φ(x))` with `T ⊕ φ : T_zO ⊕ ℝᵏ → K_z` onto and
`ker Lin_F(0, (q, z)) ∩ {σ = 0} = J(ker (T ⊕ φ))` in the product chart `χ`. -/
theorem exists_sliceKernel {f : X → Y} (hf : B.IsScFredholmSection f)
    {S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S)
    {s : Fin k → (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection (s i))
    {Φ : (Fin n → ℝ) → X} (hΦ : (rnPolyfold n).IsScSmoothMap PX Φ) {q : Fin n → ℝ} {x : X}
    (hΦq : Φ q = x)
    (hΦ0 : ∀ᶠ q' in 𝓝 q, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q', Φ q'))
    (hsurj : ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold k) ((rnPolyfold n).prod PX))).IsLinSurjAt
        (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
          ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (0, (q, x)))
    (p : ChartPoint B x) (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
    (q₁ : pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X)) :
    ∃ (T : ↥p.T →L[ℝ] ↥p.K) (φ : (Fin k → ℝ) →L[ℝ] ↥p.K),
      (∀ v, (T v : p.c.F 0) =
        linAt p.c.U p.c.R (p.c.principal (sectionAdd P f (pullbackSlice S q))) p.z v) ∧
      (∀ μ, (φ μ : p.c.F 0) = ∑ i, μ i • p.c.principal (pullbackSlice (s i) q) (p.c.φ x)) ∧
      T ∈ p.linSet f ∧ Surjective (T.coprod φ) ∧
      ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀) 0).toChart
          q₁).linKer
          (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
            ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1)
          ((0, (q, p.z)) : ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart
            q₀) 0).toChart q₁).φ.model.E 1) ⊓
          LinearMap.ker (sliceProj k n (p.c.φ.model.E 0)).toLinearMap =
        (LinearMap.ker (T.coprod φ).toLinearMap).map (sliceIncl k n p.T).toLinearMap := by
  have hfs := hf.isScSmooth
  have hG : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScSmoothSection
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs.1) S) :=
    (hfs.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).sectionAdd hS
  have hslice := pullbackSlice_sectionAdd_paramLift hfs.1 hS.1 q
  have hx0 : IsZeroAt P
      (pullbackSlice (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs.1) S) q) x := by
    subst hΦq
    exact (isZeroAt_pullback_iff_pullbackSlice hG.1 q (Φ q)).1 hΦ0.self_of_nhds
  obtain ⟨T, φ, hT, hφ⟩ := exists_sliceOps hG hs p q hx0
  have hT' : ∀ v, (T v : p.c.F 0) =
      linAt p.c.U p.c.R (p.c.principal (sectionAdd P f (pullbackSlice S q))) p.z v :=
    fun v => (hT v).trans (by rw [hslice])
  exact ⟨T, φ, hT', hφ,
    mem_linSet_sectionAdd_pullbackSlice hf hS p q (hslice ▸ hx0) T hT',
    surjective_coprod_of_isLinSurjAt hG hs p q hΦ hΦq hΦ0 hsurj T hT φ hφ,
    linKer_inf_ker_sliceProj_eq_map hG hs p q₀ q₁ q T hT φ hφ⟩

/-- **Lemma 6.6.6 (preprint 6.31)** (the sequence (96) is exact), at one point `q` of the family: in the setting
of `exists_sliceKernel`, `T = Lin_{f + S(q, ·)}(z) ∈ Lin(f, x)` and
`φ(λ) = Σ λᵢ ŝᵢ(q, ·)(φ(x))` make `0 → ker T →j ker (T ⊕ φ) →p ℝᵏ →c K_z / R(T) → 0` exact
(`lemma_6_4_14`, `T ⊕ φ` being onto), and `J` identifies `ker (T ⊕ φ)` with
`ker Lin_F(0, (q, z)) ∩ {σ = 0}`, the text's `ker F_t'(φ(t), 0)`. -/
theorem lemma_6_6_6 {f : X → Y} (hf : B.IsScFredholmSection f)
    {S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S)
    {s : Fin k → (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection (s i))
    {Φ : (Fin n → ℝ) → X} (hΦ : (rnPolyfold n).IsScSmoothMap PX Φ) {q : Fin n → ℝ} {x : X}
    (hΦq : Φ q = x)
    (hΦ0 : ∀ᶠ q' in 𝓝 q, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q', Φ q'))
    (hsurj : ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold k) ((rnPolyfold n).prod PX))).IsLinSurjAt
        (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
          ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (0, (q, x)))
    (p : ChartPoint B x) (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
    (q₁ : pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X)) :
    ∃ (T : ↥p.T →L[ℝ] ↥p.K) (φ : (Fin k → ℝ) →L[ℝ] ↥p.K),
      (∀ v, (T v : p.c.F 0) =
        linAt p.c.U p.c.R (p.c.principal (sectionAdd P f (pullbackSlice S q))) p.z v) ∧
      (∀ μ, (φ μ : p.c.F 0) = ∑ i, μ i • p.c.principal (pullbackSlice (s i) q) (p.c.φ x)) ∧
      T ∈ p.linSet f ∧
      ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart q₀) 0).toChart
          q₁).linKer
          (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
            ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1)
          ((0, (q, p.z)) : ((PullbackChartData.ofProd ((PullbackChartData.ofProd p.c 0).toChart
            q₀) 0).toChart q₁).φ.model.E 1) ⊓
          LinearMap.ker (sliceProj k n (p.c.φ.model.E 0)).toLinearMap =
        (LinearMap.ker (T.coprod φ).toLinearMap).map (sliceIncl k n p.T).toLinearMap ∧
      Injective (stabJ T φ) ∧ LinearMap.range (stabJ T φ) = LinearMap.ker (stabPi T φ) ∧
      LinearMap.range (stabPi T φ) = LinearMap.ker (stabClass T φ) ∧
      Surjective (stabClass T φ) := by
  obtain ⟨T, φ, hT, hφ, hlin, hsurj', hker⟩ :=
    exists_sliceKernel hf hS hs hΦ hΦq hΦ0 hsurj p q₀ q₁
  exact ⟨T, φ, hT, hφ, hlin, hker, lemma_6_4_14 hsurj'⟩

end Stab

end Polyfold
