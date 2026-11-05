import Polyfold.Chapter3.IndexAlongPaths

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.1,
**Proposition 6.2** (stability of `ind(f, x)` along sc-smooth paths, pp. 201–203), closed: the
two steps (E) and (S) left open in `IndexAlongPaths.lean` (round-trip item V3.98 (a); Findings,
Chapter 3, items 345–349).

# Proposition 6.2: the text's device, closed

## The text, paraphrased

See `IndexAlongPaths.lean`.  The two steps of the text's proof formalized here: the locally
defined sc⁺-section `s(t, x)` of the pull-back to `[0, 1] × X` with `s(t, φ(t)) = f(φ(t))`
("we do not need a sc-smooth partition of unity"), and the index count
`ind(F, (0, t, φ(t))) = ind(f, φ(t)) + m + p` along the graph of the path.

## What is formalized

* **Slices.**  `Polyfold.pullbackSlice S t` is the slice `x ↦ S(t, x)` of a section of `π*P`
  (`π : ℝⁿ × X → X`); `pullbackSlice_sectionAdd_paramLift` (`(f̃ + S)(t, ·) = f + S(t, ·)`),
  `isZeroAt_pullback_iff_pullbackSlice` (`G(t, x) = 0` iff the slice vanishes), and
  **`Polyfold.StrongBundle.IsScPlusSection.pullbackSlice`: the slice of an sc⁺-section of `π*P` is
  an sc⁺-section of `P`** (in the product chart of `Theorem 3.18`, the local representative of the
  slice is that of `S` composed with `u ↦ (0, u)`).
* **The slice relation (S).**  `Polyfold.StrongBundle.linAt_ofProd_slice`: in the product chart
  at `(t, x)`, `Lin_G(0)(0, δu) = Lin_{G(t,·)}(0) δu` (the chain rule with the sc-operator
  `u ↦ (0, u)`, Theorem 1.21); `Polyfold.StrongBundle.isLinOfIndex_pullbackSlice_of_isLinOfIndex`:
  **if `G'(t, x)` is Fredholm of index `i` then `G(t, ·)'(x)` is Fredholm of index `i − n`**
  (`Lin_G(0)(δa, δu) = Lin_{G(t,·)}(0) δu + Lin_G(0)(δa, 0)` and `fredholmIndex_eq_of_param`);
  `Polyfold.StrongBundle.isIndexAt_of_pullback_isLinOfIndex` is the hypothesis (S) of
  `proposition_6_2_of_sections_of_slice`.
* **The section along the path (E).**  `Polyfold.isScSmoothMap_rn_of_contDiff` (`C^∞` self-maps
  of `ℝⁿ` are sc-smooth), `Polyfold.exists_contDiff_eq_id_near_mapsTo` (a smooth reparametrization
  equal to the identity near `t₀` with values in a given ball), and
  **`Polyfold.exists_isScPlusSection_pullback_of_path`**: for an sc-smooth section `f`, an
  sc-smooth path `φ : ℝⁿ → X` and `t₀`, there is an sc⁺-section `S` of `π*P` with `f̃ + S = 0`
  along the graph of `φ` near `t₀`.  The section is the text's
  `S(t, x) = −β(x) R(x, Φ(f(φ(t)))₂)` in a strong bundle chart around `φ(t₀)`
  (`cutoffSection` in the product chart, `isScPlusSection_cutoffSection`).  The curve
  `t ↦ Φ(f(φ(t)))₂` is sc-smooth into `F¹` because sc-smooth maps are sc-smooth on the shifted
  spaces (Proposition 1.17, `IsScSmooth.shift`) and the shift of the constant structure `ℝⁿ` is
  `ℝⁿ`; the `[1]`-sc-smoothness of the bundle retraction is `IsStrongBundleMap.isScSmooth_one`.
* **`Polyfold.proposition_6_2`** (Proposition 6.2): for `X` admitting sc-smooth bump functions,
  `f` an sc-Fredholm section with tame germ data and `φ : ℝ → X` sc-smooth, `ind(f, φ(t))`
  (Definition 6.1) is one integer for all `t`.

## What the text leaves implicit, and the choices made

* **The path.**  The text's path is `φ : [0, 1] → X`, sc-smooth, and `[0, 1] × X` is used as a
  tame M-polyfold with boundary.  Here the path is an sc-smooth map `ℝ → X` (`Fin 1 → ℝ`, the
  M-polyfold `rnPolyfold 1`), so that `ℝ × X` is the product of Theorem 3.18 and no boundary
  enters; the parameter space is preconnected.  A path on `[0, 1]` which extends sc-smoothly to
  `ℝ` is covered.  The sc-smoothness of the path is used only in (E), through the sc-smoothness of
  `t ↦ f(φ(t))`; smooth points are automatic (`rnPolyfold_levelSet`).
* **The reparametrization.**  The chart around `φ(t₀)` need not contain the whole path, and the
  curve `t ↦ Φ(f(φ(t)))₂` is defined where it does.  The text's section is local in `t` as well;
  here the path is precomposed with a smooth `σ : ℝⁿ → ℝⁿ` equal to the identity near `t₀` with
  values in `φ⁻¹(dom φ_c)` (`exists_contDiff_eq_id_near_mapsTo`), which makes the section global
  on `ℝⁿ × X` and leaves the statement near `t₀` unchanged.
* **Hypotheses.**  Proposition 6.2 is proved with the hypotheses of item 240 (tame germ data, bump
  functions); the text assumes a tame M-polyfold and no bump functions (Findings, Chapter 3, item
  343).  The construction of `S` needs bump functions only to cut the chart-local section off
  (`proposition_5_30` at `φ(t₀)`); the index step (S) needs none.
-/

open Set Filter Topology Function Module ContinuousLinearMap
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

/-! ### The projection `((a, u), h) ↦ (u, h)` as an sc-operator -/

/-- The projection `(E₁ ⊕ E₂) ⊕ F → E₂ ⊕ F`, `((a, u), h) ↦ (u, h)`, as an sc-operator. -/
def ScBanach.prodSndLeftOp (E₁ E₂ F : ScBanach) : ScOperator ((E₁.prod E₂).prod F) (E₂.prod F) where
  lvl m := (ContinuousLinearMap.snd ℝ (E₁ m) (E₂ m)).prodMap (ContinuousLinearMap.id ℝ (F m))
  incl_comm _ _ := rfl

/-! ### Slices of sections of `π*P` -/

section Slice

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X} {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {B : StrongBundle PX P}

/-- The **slice** `x ↦ S(t, x)` (read in `Y`) of a section `S` of the pull-back
`π*P : π*Y → ℝⁿ × X` at the parameter `t`. -/
def pullbackSlice (S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
    (t : Fin n → ℝ) : X → Y :=
  fun x => (S (t, x)).1.2

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- The slice of a section is a section. -/
lemma IsSection.pullbackSlice {S : (Fin n → ℝ) × X → pullbackSpace P Prod.snd}
    (hS : IsSection (pullbackProj P Prod.snd) S) (t : Fin n → ℝ) :
    IsSection P (pullbackSlice S t) := fun x => by
  have h1 : P (S (t, x)).1.2 = (S (t, x)).1.1.2 := (S (t, x)).2
  have h2 : (S (t, x)).1.1 = (t, x) := hS (t, x)
  change P (S (t, x)).1.2 = x
  rw [h1, h2]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- `G(t, x) = 0` in `π*Y` iff the slice vanishes at `x`. -/
lemma isZeroAt_pullback_iff_pullbackSlice {G : (Fin n → ℝ) × X → pullbackSpace P Prod.snd}
    (hG : IsSection (pullbackProj P Prod.snd) G) (t : Fin n → ℝ) (x : X) :
    IsZeroAt (pullbackProj P Prod.snd) G (t, x) ↔ IsZeroAt P (pullbackSlice G t) x := by
  have h0 : fiberZero (pullbackProj P Prod.snd) (t, x) =
      ⟨((t, x), fiberZero P x), (0 : P ⁻¹' {x}).2⟩ := rfl
  have h1 : (G (t, x)).1.1 = (t, x) := hG (t, x)
  unfold IsZeroAt
  rw [h0]
  constructor
  · intro h
    exact congrArg (fun q : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X) => q.1.2) h
  · intro h
    refine Subtype.ext (Prod.ext h1 ?_)
    exact h

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- The slice of `f̃ + S` is `f + S(t, ·)` (`f̃ = f ∘ π`, the fibrewise sum of `π*Y`). -/
lemma pullbackSlice_sectionAdd_paramLift {f : X → Y} (hf : IsSection P f)
    {S : (Fin n → ℝ) × X → pullbackSpace P Prod.snd} (hS : IsSection (pullbackProj P Prod.snd) S)
    (t : Fin n → ℝ) :
    pullbackSlice (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf) S) t =
      sectionAdd P f (pullbackSlice S t) := by
  funext x
  have hL : IsSection (pullbackProj P Prod.snd) (paramLift (n := n) f hf) :=
    isSection_pullbackLift _
  set e := pullbackFiberEquiv P (Prod.snd : (Fin n → ℝ) × X → X) (t, x) with he
  have h1 : e ⟨paramLift (n := n) f hf (t, x), hL (t, x)⟩ = ⟨f x, hf x⟩ := Subtype.ext rfl
  have h2 : e ⟨S (t, x), hS (t, x)⟩ = ⟨pullbackSlice S t x, hS.pullbackSlice t x⟩ :=
    Subtype.ext rfl
  have h3 := pullbackFiberEquiv_add P (Prod.snd : (Fin n → ℝ) × X → X) (t, x)
    ⟨paramLift (n := n) f hf (t, x), hL (t, x)⟩ ⟨S (t, x), hS (t, x)⟩
  rw [h1, h2] at h3
  change (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf) S (t, x)).1.2 = _
  rw [sectionAdd_apply hL hS, sectionAdd_apply hf (hS.pullbackSlice t)]
  exact congrArg Subtype.val h3

variable [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- **The slice of an sc⁺-section of `π*P` is an sc⁺-section of `P`**: in a strong bundle chart `c`
of the atlas, the product chart `(r ↦ r − t) × φ` is a chart of the atlas of `π*P`, and the local
representative of `S(t, ·)` in `c` is that of `S` in the product chart composed with `u ↦ (0, u)`
and projected to `E ⊕ F¹`. -/
theorem StrongBundle.IsScPlusSection.pullbackSlice
    {S : (Fin n → ℝ) × X → pullbackSpace P Prod.snd}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S)
    (t : Fin n → ℝ) : B.IsScPlusSection (Polyfold.pullbackSlice S t) := by
  have hsec : IsSection P (Polyfold.pullbackSlice S t) := hS.1.pullbackSlice t
  refine ⟨hsec, fun c hc => ?_⟩
  set d := PullbackChartData.ofProd c t with hd
  set q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X) := S (t, c.φ.symm 0) with hq₀
  set pc := d.toChart q₀ with hpc
  have hmem : pc ∈ (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).atlas.charts :=
    ⟨d, q₀, hc, rfl⟩
  obtain ⟨hrange, hsm⟩ := hS.2 pc hmem
  have hsrc : ∀ x ∈ c.φ.source, (t, x) ∈ pc.φ.source := fun x hx => ⟨mem_univ _, hx⟩
  refine ⟨fun x hx => hrange (t, x) (hsrc x hx), ?_⟩
  have hO : IsScRetract c.φ.model.E c.φ.model.C c.φ.model.O := c.φ.model.isScRetract
  -- `ι : u ↦ (0, u)` as a map of retracts `O → ℝⁿ × O`
  have hι : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O pc.φ.model.E pc.φ.model.C
      pc.φ.model.O (ScBanach.prodInrOp (rnSc n) c.φ.model.E 0) :=
    (ScBanach.prodInrOp (rnSc n) c.φ.model.E).isScSmoothRetractMap hO
      fun u hu => show ((0 : Fin n → ℝ), u) ∈ univ ×ˢ c.φ.model.O from ⟨mem_univ _, hu⟩
  have hcomp := hsm.comp hι pc.φ.model.isScRetract
  -- the projection `((a, u), h) ↦ (u, h)`
  set π := ScBanach.prodSndLeftOp (rnSc n) c.φ.model.E c.F.shift with hπ
  refine ⟨fun z hz => ?_, fun R hR => ?_⟩
  · -- the local representative lands in `K[1]`
    have hzs := c.φ.symm_mapsTo hz
    exact c.liftOne_mem (c.mem_source_of_proj (by rw [hsec]; exact hzs)) (hrange (t, _) (hsrc _ hzs))
  · have hU := R.isScDomain
    have h1 := hcomp.comp_isScSmooth R hR
    have h2 := IsScSmooth.comp hU (isScDomain_univ _) (π.isScSmooth (isScDomain_univ _)) h1
      (mapsTo_univ _ _)
    refine h2.congr hU fun u hu => ?_
    have hRu : R u ∈ c.φ.model.O := by rw [← hR]; exact R.apply_mem_retract hu
    have hRs := c.φ.symm_mapsTo hRu
    -- `π (localRepOne pc S (0, R u)) = localRepOne c (S(t, ·)) (R u)`
    change ((StrongBundle.localRepOne pc S ((0 : Fin n → ℝ), R u)).1.2,
        (StrongBundle.localRepOne pc S ((0 : Fin n → ℝ), R u)).2) =
      StrongBundle.localRepOne c (Polyfold.pullbackSlice S t) (R u)
    have hsymm : pc.φ.symm ((0 : Fin n → ℝ), R u) = (t, c.φ.symm (R u)) := by
      change ((0 : Fin n → ℝ) + t, c.φ.symm (R u)) = _
      rw [zero_add]
    simp only [StrongBundle.localRepOne, hsymm]
    refine Prod.ext ?_ rfl
    change (pc.φ (S (t, c.φ.symm (R u))).1.1).2 = (c (Polyfold.pullbackSlice S t (c.φ.symm (R u)))).1
    have hS1 : (S (t, c.φ.symm (R u))).1.1 = (t, c.φ.symm (R u)) := hS.1 (t, c.φ.symm (R u))
    rw [hS1, c.fst_apply (by rw [hsec]; exact hRs), hsec]
    rfl

/-! ### The slice relation (S) -/

open StrongRetr

/-- `r_{pc}(a, u) = (a, r(u))` for the product chart. -/
lemma PullbackChartData.r_ofProd (c : StrongBundleChart PX P) (t : Fin n → ℝ)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) (p : (Fin n → ℝ) × c.φ.model.E 0) :
    r ((PullbackChartData.ofProd c t).toChart q₀).R p = (p.1, r c.R p.2) := rfl

/-- **The linearization of `G` on the slice direction, in the product chart**: for an sc-smooth
section `G` of `π*P`, a strong bundle chart `c` with `0 ∈ U` and the product chart
`pc = (r ↦ r − t) × φ`, `Lin_G(0)(0, δu) = Lin_{G(t,·)}(0) δu` for `(0, δu) ∈ T₀(ℝⁿ × O)`.  Proof:
the chain rule (Theorem 1.21, `scDeriv_comp_apply'`) for `H ∘ ι` with `H = Ĝ ∘ (1 × r)`,
`ι(u) = (0, u)` an sc-operator (`ScOperator.scDeriv_eq`), and `H ∘ ι = Ĝ(t, ·) ∘ r`. -/
theorem StrongBundle.linAt_ofProd_slice {G : (Fin n → ℝ) × X → pullbackSpace P Prod.snd}
    (hG : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScSmoothSection G)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (t : Fin n → ℝ)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) (h0U : (0 : c.φ.model.E 0) ∈ c.U)
    (v : ↥(rangeS (scDeriv ((PullbackChartData.ofProd c t).toChart q₀).U
      (r ((PullbackChartData.ofProd c t).toChart q₀).R)
      (0 : ((PullbackChartData.ofProd c t).toChart q₀).φ.model.E 1))))
    (hv : v.1.1 = 0) :
    linAt ((PullbackChartData.ofProd c t).toChart q₀).U ((PullbackChartData.ofProd c t).toChart q₀).R
        (((PullbackChartData.ofProd c t).toChart q₀).principal G) 0 v =
      linAt c.U c.R (c.principal (Polyfold.pullbackSlice G t)) 0
        ⟨v.1.2, PullbackChartData.ofProd_mem_tangent c t q₀ h0U v.2⟩ := by
  revert hv v
  set pc := (PullbackChartData.ofProd c t).toChart q₀ with hpc
  intro v hv
  have hpcc : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsChart pc :=
    (PullbackChartData.ofProd c t).isChart_toChart B _ hc q₀
  have hH : IsSc1 pc.U (pc.principal G ∘ r pc.R) := hG.isSc1_principal_comp_r hpcc
  set ι := ScBanach.prodInrOp (rnSc n) c.φ.model.E with hι
  have hι1 : IsSc1 (E := c.φ.model.E) (F := pc.φ.model.E) c.U (ι 0) :=
    ((ι.isScSmooth c.relOpen.isScDomain) 1).1
  have hι0 : IsSc0 c.φ.model.E pc.φ.model.E univ (ι 0) := ι.isSc0
  have hmaps : MapsTo (ι 0) c.U pc.U := fun w hw =>
    show ((0 : Fin n → ℝ), w) ∈ univ ×ˢ c.U from ⟨mem_univ _, hw⟩
  have h0 : (0 : c.φ.model.E 1) ∈ c.φ.model.E.lvlSet c.U 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0U
  have hchain := scDeriv_comp_apply' c.relOpen pc.relOpen hι1 hH hmaps h0 v.1.2
  have hlvl : levelMap (E := c.φ.model.E) (F := pc.φ.model.E) (ι 0) 1 (0 : c.φ.model.E 1) =
      (0 : pc.φ.model.E 1) := by
    apply pc.φ.model.E.toBase_injective 1
    rw [IsSc0.toBase_levelMap hι0 (by rw [ScBanach.mem_lvlSet]; exact mem_univ _)]
    simp only [map_zero]
    rfl
  have hDι : scDeriv (E := c.φ.model.E) (F := pc.φ.model.E) c.U (ι 0) 0 = ι 0 :=
    ι.scDeriv_eq c.relOpen.isScDomain h0
  rw [hlvl, hDι] at hchain
  have hHι : (pc.principal G ∘ r pc.R) ∘ ι 0 = c.principal (Polyfold.pullbackSlice G t) ∘ r c.R := by
    funext w
    have hz : (ι 0 w).1 + t = t := by
      show (0 : (rnSc n) 0) + t = t
      exact zero_add t
    change (c (G ((ι 0 w).1 + t, c.φ.symm (r c.R w))).1.2).2 =
      (c (G (t, c.φ.symm (r c.R w))).1.2).2
    rw [hz]
  rw [hHι] at hchain
  have hv' : v.1 = ι 0 v.1.2 := Prod.ext hv rfl
  change scDeriv pc.U (pc.principal G ∘ r pc.R) 0 v.1 =
    scDeriv c.U (c.principal (Polyfold.pullbackSlice G t) ∘ r c.R) 0 v.1.2
  conv_lhs => rw [hv']
  exact hchain

set_option maxHeartbeats 400000 in
/-- **The index of the slice from the index of the section on `ℝⁿ × X`** (the slice relation (S);
the analogue of `isLinOfIndex_of_paramSection_isLinOfIndex` for a `t`-dependent section): let `G`
be an sc-Fredholm section of `π*P` whose slice `g = G(t, ·)` is an sc-Fredholm section of `P` with
`g(x) = 0`, and suppose `G'(t, x)` is Fredholm of index `i` in every chart.  Then `g'(x)` is
Fredholm of index `i − n` in every chart.  Proof: in the product chart over the chart `c₁` of the
germ datum of `g` at `x`, `Lin_G(0)(δa, δu) = Lin_g(0) δu + Lin_G(0)(δa, 0)`
(`linAt_ofProd_slice` and linearity), so `i = ind Lin_g(0) + n` (`fredholmIndex_eq_of_param`), and
the index of `g'(x)` in every chart is that in `c₁` (`isLinOfIndex_of_conjugationData`). -/
theorem StrongBundle.isLinOfIndex_pullbackSlice_of_isLinOfIndex
    {G : (Fin n → ℝ) × X → pullbackSpace P Prod.snd}
    (hG : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScFredholmSection G)
    {t : Fin n → ℝ} {x : X} (hg : B.IsScFredholmSection (Polyfold.pullbackSlice G t))
    (hx : IsZeroAt P (Polyfold.pullbackSlice G t) x) {i : ℤ}
    (hi : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsLinOfIndex G (t, x) i) :
    B.IsLinOfIndex (Polyfold.pullbackSlice G t) x (i - n) := by
  classical
  set g := Polyfold.pullbackSlice G t with hgdef
  have hGs : IsSection (pullbackProj P Prod.snd) G := hG.isScSmooth.1
  have hgs : IsSection P g := hGs.pullbackSlice t
  have hz0 : IsZeroAt (pullbackProj P Prod.snd) G (t, x) :=
    (isZeroAt_pullback_iff_pullbackSlice hGs t x).2 hx
  -- the chart of the germ datum of `g` at `x`
  have hxs : x ∈ PX.smoothSet := hg.mem_smoothSet_of_isZeroAt hx
  obtain ⟨-, c₁, hc₁, hxV₁, hφ₁, h0₁, g₁, s₁, hfill₁, hs₁, hs0₁, hconj₁⟩ := hg.germ x hxs
  obtain ⟨d₁⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj₁
  have hidx₁ := StrongBundle.isLinOfIndex_of_conjugationData hg.isScSmooth hx hc₁ hxV₁ hφ₁
    h0₁ hfill₁ hs₁ hs0₁ d₁
  suffices hsuff : (finrank ℝ d₁.Pn - finrank ℝ d₁.Q : ℤ) = i - n by rw [← hsuff]; exact hidx₁
  -- `L₁ = Lin_g(0) : T₀O₁ → K₁` in `c₁`
  have h0O₁ : (0 : c₁.φ.model.E 0) ∈ c₁.φ.model.O := by
    rw [← hφ₁]; exact c₁.φ.mapsTo_model x hxV₁
  have h0O₁' : (0 : c₁.φ.model.E 0) ∈ r c₁.R '' c₁.U := c₁.r_image ▸ h0O₁
  have hz₁ : c₁.φ.model.E.toBase 1 (0 : c₁.φ.model.E 1) = c₁.φ x := by rw [map_zero, hφ₁]
  have hzU₁ : c₁.φ.model.E.toBase 1 (0 : c₁.φ.model.E 1) ∈ c₁.U := by rw [map_zero]; exact h0₁
  have hzO₁ : c₁.φ.model.E.toBase 1 (0 : c₁.φ.model.E 1) ∈ r c₁.R '' c₁.U := by
    rw [map_zero]; exact h0O₁'
  have hfr₁ : IsSc1 c₁.U (c₁.principal g ∘ r c₁.R) := hg.isScSmooth.isSc1_principal_comp_r hc₁
  have hfK₁ : ∀ y ∈ r c₁.R '' c₁.U, (y, c₁.principal g y) ∈ c₁.R '' (c₁.U ×ˢ univ) :=
    fun y hy => c₁.principal_mem_K hgs (c₁.r_image ▸ hy)
  have hfz₁ : c₁.principal g (c₁.φ.model.E.toBase 1 (0 : c₁.φ.model.E 1)) = 0 := by
    rw [hz₁]; exact (c₁.isZeroAt_iff hgs hxV₁).1 hx
  have hmem₁ : ∀ w : ↥(rangeS (scDeriv c₁.U (r c₁.R) (0 : c₁.φ.model.E 1))),
      linAt c₁.U c₁.R (c₁.principal g) 0 w ∈ rangeS (ρCLM c₁.isRetraction hzU₁) := fun w =>
    ⟨_, rho_scDeriv_comp_r c₁.relOpen c₁.isRetraction hfr₁ hfK₁ hzO₁ hfz₁ w⟩
  set L₁ := (linAt c₁.U c₁.R (c₁.principal g) 0).codRestrict _ hmem₁ with hL₁
  obtain ⟨hL₁F, hL₁ind⟩ := hidx₁ c₁ hc₁ hxV₁ 0 hz₁ hzU₁ L₁ fun _ => rfl
  -- the product chart `(r ↦ r − t) × φ₁` at `(t, x)` and `L_G = Lin_G(0)`
  set q₀ := G (t, x) with hq₀
  set pc := (PullbackChartData.ofProd c₁ t).toChart q₀ with hpc
  have hpcc : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsChart pc :=
    (PullbackChartData.ofProd c₁ t).isChart_toChart B _ hc₁ q₀
  have hzV : (t, x) ∈ pc.φ.source := ⟨mem_univ _, hxV₁⟩
  have hpc0 : pc.φ (t, x) = 0 := ofProd_apply_eq_zero c₁ t q₀ hφ₁
  have hzF : pc.φ.model.E.toBase 1 (0 : pc.φ.model.E 1) = pc.φ (t, x) := by
    rw [map_zero, hpc0]
  have hzUF : pc.φ.model.E.toBase 1 (0 : pc.φ.model.E 1) ∈ pc.U := by
    rw [map_zero]; exact ⟨mem_univ _, h0₁⟩
  have hzOF : pc.φ.model.E.toBase 1 (0 : pc.φ.model.E 1) ∈ r pc.R '' pc.U := by
    rw [pc.r_image, hzF]; exact pc.φ.mapsTo_model (t, x) hzV
  have hfrF : IsSc1 pc.U (pc.principal G ∘ r pc.R) := hG.isScSmooth.isSc1_principal_comp_r hpcc
  have hfKF : ∀ w ∈ r pc.R '' pc.U, (w, pc.principal G w) ∈ pc.R '' (pc.U ×ˢ univ) :=
    fun w hw => pc.principal_mem_K hGs (pc.r_image ▸ hw)
  have hfzF : pc.principal G (pc.φ.model.E.toBase 1 (0 : pc.φ.model.E 1)) = 0 := by
    rw [hzF]; exact (pc.isZeroAt_iff hGs hzV).1 hz0
  have hmemF : ∀ w : ↥(rangeS (scDeriv pc.U (r pc.R) (0 : pc.φ.model.E 1))),
      linAt pc.U pc.R (pc.principal G) 0 w ∈ rangeS (ρCLM pc.isRetraction hzUF) := fun w =>
    ⟨_, rho_scDeriv_comp_r pc.relOpen pc.isRetraction hfrF hfKF hzOF hfzF w⟩
  set LF := (linAt pc.U pc.R (pc.principal G) 0).codRestrict _ hmemF with hLF
  obtain ⟨hLFF, hLFind⟩ := hi pc hpcc hzV 0 hzF hzUF LF fun _ => rfl
  -- the fibres `K_{G,0}` and `K₁` agree
  have hKeq : ∀ k' : pc.F 0, k' ∈ rangeS (ρCLM pc.isRetraction hzUF) ↔
      k' ∈ rangeS (ρCLM c₁.isRetraction hzU₁) := by
    intro k'
    refine (mem_rangeS_ρCLM_iff pc.isRetraction hzOF hzUF).trans ?_
    refine Iff.trans ?_ (mem_rangeS_ρCLM_iff c₁.isRetraction hzO₁ hzU₁).symm
    rw [map_zero, map_zero]
    exact mem_K_ofProd_zero_iff c₁ t q₀ h0O₁ k'
  -- `T₀(ℝⁿ × O₁) = ℝⁿ × T₀O₁`
  have hTmem : ∀ (a : Fin n → ℝ) (w : ↥(rangeS (scDeriv c₁.U (r c₁.R) (0 : c₁.φ.model.E 1)))),
      ((a, (w : c₁.φ.model.E 0)) : (Fin n → ℝ) × c₁.φ.model.E 0) ∈
        rangeS (scDeriv pc.U (r pc.R) (0 : pc.φ.model.E 1)) := by
    intro a w
    obtain ⟨w₀, hw₀⟩ := w.2
    exact ⟨(a, w₀), (PullbackChartData.ofProd_scDeriv_r c₁ t q₀ h0₁ (a, w₀)).trans
      (Prod.ext rfl hw₀)⟩
  -- completeness of the four spaces
  obtain ⟨-, hT₁, hK₁, -, -, -, -⟩ :=
    StrongBundle.linAt_isScFredholm hg hx hc₁ hxV₁ hz₁ hzU₁
  obtain ⟨-, hTF, hKF, -, -, -, -⟩ :=
    StrongBundle.linAt_isScFredholm hG hz0 hpcc hzV hzF hzUF
  have : CompleteSpace ↥(rangeS (scDeriv c₁.U (r c₁.R) (0 : c₁.φ.model.E 1))) :=
    hT₁.isClosed.completeSpace_coe
  have : CompleteSpace ↥(rangeS (ρCLM c₁.isRetraction hzU₁)) := hK₁.isClosed.completeSpace_coe
  have : CompleteSpace ↥(rangeS (scDeriv pc.U (r pc.R) (0 : pc.φ.model.E 1))) :=
    hTF.isClosed.completeSpace_coe
  have : CompleteSpace ↥(rangeS (ρCLM pc.isRetraction hzUF)) := hKF.isClosed.completeSpace_coe
  -- the isomorphisms `ℝⁿ × T₀O₁ ≃ T₀(ℝⁿ × O₁)` and `K₁ ≃ K_{G,0}`
  set eT : ((Fin n → ℝ) × ↥(rangeS (scDeriv c₁.U (r c₁.R) (0 : c₁.φ.model.E 1)))) ≃L[ℝ]
      ↥(rangeS (scDeriv pc.U (r pc.R) (0 : pc.φ.model.E 1))) :=
    ContinuousLinearEquiv.equivOfInverse
      (((ContinuousLinearMap.id ℝ (Fin n → ℝ)).prodMap
        (rangeS (scDeriv c₁.U (r c₁.R) (0 : c₁.φ.model.E 1))).subtypeL).codRestrict _
          fun p => hTmem p.1 p.2)
      (((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (c₁.φ.model.E 0)).comp
          (rangeS (scDeriv pc.U (r pc.R) (0 : pc.φ.model.E 1))).subtypeL).prod
        (((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (c₁.φ.model.E 0)).comp
          (rangeS (scDeriv pc.U (r pc.R) (0 : pc.φ.model.E 1))).subtypeL).codRestrict _
            fun w => PullbackChartData.ofProd_mem_tangent c₁ t q₀ h0₁ w.2))
      (fun p => Prod.ext rfl (Subtype.ext rfl)) (fun w => Subtype.ext (Prod.ext rfl rfl))
    with heT
  set eK : ↥(rangeS (ρCLM c₁.isRetraction hzU₁)) ≃L[ℝ] ↥(rangeS (ρCLM pc.isRetraction hzUF)) :=
    restrictEquiv _ _ (ContinuousLinearMap.id ℝ (c₁.F 0)) (ContinuousLinearMap.id ℝ (c₁.F 0))
      (fun y hy => (hKeq y).2 hy) (fun y hy => (hKeq y).1 hy) (fun _ _ => rfl) (fun _ _ => rfl)
    with heK
  -- the finite-rank part `a ↦ Lin_G(0)(a, 0)`
  set Ef : (Fin n → ℝ) →L[ℝ] ↥(rangeS (ρCLM c₁.isRetraction hzU₁)) :=
    eK.symm.toContinuousLinearMap.comp
      (LF.comp (eT.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) _)))
    with hEf
  set M := L₁.comp (ContinuousLinearMap.snd ℝ (Fin n → ℝ) _) +
    Ef.comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) _) with hM
  -- the slice relation: `L_G(eT (0, w)) = eK (L₁ w)`
  have hslice : ∀ w : ↥(rangeS (scDeriv c₁.U (r c₁.R) (0 : c₁.φ.model.E 1))),
      LF (eT (0, w)) = eK (L₁ w) := by
    intro w
    apply Subtype.ext
    change linAt pc.U pc.R (pc.principal G) 0 (eT (0, w)) = (L₁ w : c₁.F 0)
    rw [StrongBundle.linAt_ofProd_slice hG.isScSmooth hc₁ t q₀ h0₁ (eT (0, w)) rfl]
    rfl
  -- the conjugation `L_G ∘ eT = eK ∘ M`
  have hconj : ∀ p, LF (eT p) = eK (M p) := by
    intro p
    have hp : p = (0, p.2) + (p.1, 0) := by ext <;> simp
    have h1 : eT p = eT (0, p.2) + eT (p.1, 0) := by rw [← map_add, ← hp]
    have h2 : M p = L₁ p.2 + Ef p.1 := rfl
    have hE : eK (Ef p.1) = LF (eT (p.1, 0)) := by
      change eK (eK.symm (LF (eT (p.1, 0)))) = _
      exact eK.apply_symm_apply _
    rw [h1, map_add, hslice, h2, map_add, hE]
  obtain ⟨hiff, hind⟩ := isFredholm_iff_of_conj hconj
  have hMF : M.IsFredholm := hiff.2 hLFF
  have hMind : fredholmIndex M = fredholmIndex L₁ + n := fredholmIndex_eq_of_param hL₁F Ef hM hMF
  have h1 := hind hMF
  rw [hLFind] at h1
  rw [← hL₁ind]
  omega

/-- **The hypothesis (S) of `proposition_6_2_of_sections_of_slice`**: for an sc-Fredholm section
`f`, an sc⁺-section `S` of `π*P` (`π : ℝ × X → X`) and a zero `(t, x)` of `f̃ + S` at which
`(f̃ + S)'(t, x)` has index `i`, `ind(f, x) = i − 1` (Definition 6.1, through the slice
`s = S(t, ·)`: `f + s` vanishes at `x` and `(f + s)'(x)` has index `i − 1`). -/
theorem StrongBundle.isIndexAt_of_pullback_isLinOfIndex [ParacompactSpace ((Fin 1 → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]
    {f : X → Y} (hf : B.IsScFredholmSection f) {S : (Fin 1 → ℝ) × X → pullbackSpace P Prod.snd}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S)
    {t : Fin 1 → ℝ} {x : X} {i : ℤ}
    (hz : IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (t, x))
    (hi : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsLinOfIndex
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (t, x) i) :
    B.IsIndexAt f x (i - 1) := by
  have hfs : IsSection P f := hf.isScSmooth.1
  have hG := theorem_3_15 hf.param hS
  have hGs : IsSection (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift (n := 1) f hfs) S) := hG.isScSmooth.1
  have hslice := pullbackSlice_sectionAdd_paramLift hfs hS.1 t
  have hz' : IsZeroAt P (sectionAdd P f (Polyfold.pullbackSlice S t)) x := by
    rw [← hslice]; exact (isZeroAt_pullback_iff_pullbackSlice hGs t x).1 hz
  have hg : B.IsScFredholmSection (sectionAdd P f (Polyfold.pullbackSlice S t)) :=
    theorem_3_15 hf (hS.pullbackSlice t)
  refine ⟨Polyfold.pullbackSlice S t, hS.pullbackSlice t, hz', ?_⟩
  have := StrongBundle.isLinOfIndex_pullbackSlice_of_isLinOfIndex hG (hslice ▸ hg) (hslice ▸ hz') hi
  rw [hslice] at this
  simpa using this

end Slice

/-! ### The section along the path (E) -/

section Device

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X} {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {B : StrongBundle PX P}

/-- A `C^∞` self-map of `ℝⁿ` is an sc-smooth self-map of the M-polyfold `ℝⁿ`. -/
theorem isScSmoothMap_rn_of_contDiff {σ : (Fin n → ℝ) → Fin n → ℝ} (hσ : ContDiff ℝ ∞ σ) :
    (rnPolyfold n).IsScSmoothMap (rnPolyfold n) σ := by
  refine MPolyfold.isScSmoothMap_of_local fun x => ⟨rnChart n 0, rnChart n 0, univ,
    isChart_rnChart 0, isChart_rnChart 0, isOpen_univ, mem_univ x, subset_univ _,
    mapsTo_univ _ _, ?_⟩
  rw [← rnChart_source 0, (rnChart n 0).image_source, rnChart_model_O]
  change IsScSmoothRetractMap (rnSc n) univ univ (rnSc n) univ univ (fun r => σ (r + 0) - 0)
  exact isScSmoothRetractMap_const_of_contDiff (V := Fin n → ℝ) (V' := Fin n → ℝ)
    ((hσ.comp (contDiff_id.add contDiff_const)).sub contDiff_const)

/-- **A smooth reparametrization**: a `C^∞` map `σ : ℝⁿ → ℝⁿ` equal to the identity near `t₀`
with all its values in the ball `B(t₀, ε)` (`σ(t) = t₀ + β(t − t₀)(t − t₀)` for a bump `β`
equal to `1` near `0` and supported in `B(0, ε/2)`). -/
theorem exists_contDiff_eq_id_near_mapsTo (t₀ : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : (Fin n → ℝ) → Fin n → ℝ, ContDiff ℝ ∞ σ ∧ (∀ᶠ t in 𝓝 t₀, σ t = t) ∧
      ∀ t, σ t ∈ Metric.ball t₀ ε := by
  let b : ContDiffBump (0 : Fin n → ℝ) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  refine ⟨fun t => t₀ + b (t - t₀) • (t - t₀), ?_, ?_, ?_⟩
  · exact contDiff_const.add ((b.contDiff.comp (contDiff_id.sub contDiff_const)).smul
      (contDiff_id.sub contDiff_const))
  · filter_upwards [Metric.closedBall_mem_nhds t₀ (show (0 : ℝ) < ε / 4 by positivity)] with t ht
    have h1 : t - t₀ ∈ Metric.closedBall (0 : Fin n → ℝ) b.rIn := by
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [Metric.mem_closedBall, dist_eq_norm] at ht
      exact ht
    simp only [b.one_of_mem_closedBall h1, one_smul, add_sub_cancel]
  · intro t
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg b.nonneg]
    by_cases h : ε / 2 ≤ ‖t - t₀‖
    · rw [b.zero_of_le_dist (by rwa [dist_zero_right]), zero_mul]; exact hε
    · rw [not_le] at h
      calc b (t - t₀) * ‖t - t₀‖ ≤ 1 * ‖t - t₀‖ := by gcongr; exact b.le_one
        _ < ε := by linarith

variable [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

set_option maxHeartbeats 800000 in
/-- **The text's sc⁺-section along the path (E)**: let `X` admit sc-smooth bump functions, `f` be
an sc-smooth section of `P`, `φ : ℝⁿ → X` an sc-smooth path and `t₀ ∈ ℝⁿ`.  Then there is an
sc⁺-section `S` of the pull-back `π*P` (`π : ℝⁿ × X → X`) with `f̃ + S = 0` along the graph
`t ↦ (t, φ(t))` near `t₀` (`f̃ = f ∘ π`).  Construction: a strong bundle chart `c` around
`φ(t₀)`; a smooth reparametrization `ψ = φ ∘ σ` with values in `dom φ_c` and `σ = id` near `t₀`;
the curve `ê₁(a) = Φ(f(ψ(a)))₂` lifted to `F¹`, sc-smooth from the constant structure `ℝⁿ`
(Proposition 1.17, `IsScSmooth.shift`); the local section `τ(a, u) = −R[1](u, ê₁(a + t₀))₂` of
`K[1]` in the product chart (the `[1]`-sc-smoothness of the bundle retraction); and the cut-off
`S = cutoffSection pc β τ` with a bump `β(t, x) = β₂(x)` equal to `1` near `φ(t₀)`
(`isScPlusSection_cutoffSection`).  At `(t, φ(t))`, `Φ(S(t, φ(t)))₂ = −R(φ_c(φ(t)), ê(t))₂ =
−Φ(f(φ(t)))₂` since `Φ(f(φ(t))) ∈ K`. -/
theorem exists_isScPlusSection_pullback_of_path (hbump : PX.AdmitsBumpFunctions) {f : X → Y}
    (hf : B.IsScSmoothSection f) {φ : (Fin n → ℝ) → X}
    (hφ : (rnPolyfold n).IsScSmoothMap PX φ) (t₀ : Fin n → ℝ) :
    ∃ S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X),
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S ∧
      ∀ᶠ t in 𝓝 t₀, IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.1) S) (t, φ t) := by
  classical
  have hfs : IsSection P f := hf.1
  have hφc : Continuous φ := continuousOn_univ.1 hφ.continuousOn
  -- a chart around `φ(t₀)` and a reparametrization of the path into its domain
  obtain ⟨c, hc, hxc⟩ := StrongBundle.exists_chart_mem B (φ t₀)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (c.φ.isOpen_source.preimage hφc) t₀ hxc
  obtain ⟨σ, hσ, hσid, hσball⟩ := exists_contDiff_eq_id_near_mapsTo t₀ hε
  set ψ : (Fin n → ℝ) → X := φ ∘ σ with hψdef
  have hψ : (rnPolyfold n).IsScSmoothMap PX ψ := hφ.comp (isScSmoothMap_rn_of_contDiff hσ)
  have hψc : ∀ t, ψ t ∈ c.φ.source := fun t => hball (hσball t)
  -- the curve `g(a) = Φ(f(ψ(a)))` is sc-smooth into `E ⊕ F`, hence into `E¹ ⊕ F¹`
  have hfψ : (rnPolyfold n).IsScSmoothMap B.toMPolyfold0 (f ∘ ψ) := hf.2.comp hψ
  have h1 := hfψ.smooth (rnChart n 0) (c.toMChart B.continuous) (isChart_rnChart 0)
    (B.isChart_toMChart hc) univ isOpen_univ (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
    (fun t _ => c.mem_source_of_proj (by rw [Function.comp_apply, hfs]; exact hψc t))
  rw [← rnChart_source 0, (rnChart n 0).image_source, rnChart_model_O] at h1
  set g : (Fin n → ℝ) → (c.φ.model.E.prod c.F) 0 := fun a => c (f (ψ (a + 0))) with hgdef
  have hg : IsScSmooth (E := rnSc n) (F := c.φ.model.E.prod c.F) univ g :=
    h1.comp_isScSmooth (ScRetraction.id (rn_relOpen_univ n)) (image_id _)
  have hg1 := hg.shift (isScDomain_univ _)
  have hlv : (rnSc n).lvlSet (univ : Set ((rnSc n) 0)) 1 = univ := by
    ext a; exact ⟨fun _ => mem_univ _, fun _ => mem_univ _⟩
  rw [hlv] at hg1
  have hg1' : IsScSmooth (E := rnSc n) (F := c.φ.model.E.shift.prod c.F.shift) univ
      (fun a => levelMap (E := rnSc n) (F := c.φ.model.E.prod c.F) g 1 a) := hg1
  set ê₁ : (Fin n → ℝ) → c.F 1 :=
    fun a => (levelMap (E := rnSc n) (F := c.φ.model.E.prod c.F) g 1 a).2 with hê₁def
  have hê₁ : IsScSmooth (E := rnSc n) (F := c.F.shift) univ ê₁ := hg1'.snd (isScDomain_univ _)
  have hê₁base : ∀ a, c.F.toBase 1 (ê₁ a) = (c (f (ψ a))).2 := fun a => by
    have h := IsSc0.toBase_levelMap (hg 0) (m := 1) (x := a)
      (by rw [ScBanach.mem_lvlSet]; exact mem_univ _)
    rw [ScBanach.prod_toBase, ScBanach.const_toBase] at h
    have h2 := congrArg Prod.snd h
    exact h2.trans (by simp only [hgdef, add_zero])
  -- the product chart at `t₀` over `c`
  set d := PullbackChartData.ofProd c t₀ with hd
  set q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X) := paramLift f hfs (t₀, φ t₀)
    with hq₀
  set pc := d.toChart q₀ with hpc
  have hpcmem : pc ∈ (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).atlas.charts :=
    ⟨d, q₀, hc, rfl⟩
  -- the local section `τ(a, u) = −R[1](u, ê₁(a + t₀))₂`
  set τ : ((rnSc n).prod c.φ.model.E) 0 → c.F 1 :=
    fun z => -(shiftFiber c.R (z.2, ê₁ (z.1 + t₀))).2 with hτdef
  have hRfib : ∀ u ∈ c.U, ∀ b, (c.R (u, c.F.toBase 1 (ê₁ b))).2 ∈ range (c.F.toBase 1) :=
    fun u hu b => (c.isRetraction.preserves_filtration 0 1 (by norm_num) u hu ⟨u, rfl⟩ _
      ⟨ê₁ b, rfl⟩).2
  have hτbase : ∀ z : ((rnSc n).prod c.φ.model.E) 0, z.2 ∈ c.U →
      c.F.toBase 1 (τ z) = -(c.R (z.2, c.F.toBase 1 (ê₁ (z.1 + t₀)))).2 := fun z hz => by
    simp only [hτdef, map_neg, shiftFiber]
    rw [Function.invFun_eq (hRfib z.2 hz _)]
  -- `(z, τ(z)) ∈ K[1]` for `z ∈ ℝⁿ × O`
  have hτK : ∀ z : ((rnSc n).prod c.φ.model.E) 0, z ∈ univ ×ˢ c.φ.model.O →
      (z, c.F.toBase 1 (τ z)) ∈ pc.K := fun z hz => by
    have hz2 : z.2 ∈ c.φ.model.O := hz.2
    have hzU : z.2 ∈ c.U := StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ hz2)
    change _ ∈ pullbackRetraction d.c.R d.RZ d.g '' (d.RZ.U ×ˢ univ)
    rw [d.image_eq_Kg]
    refine ⟨by rw [d.RZ_retract]; exact hz, ?_⟩
    have hgz : d.g z = z.2 := by
      change c.φ (c.φ.symm z.2) = z.2
      exact c.φ.apply_symm_apply hz2
    rw [hgz, hτbase z hzU]
    set h := c.F.toBase 1 (ê₁ (z.1 + t₀)) with hh
    have hR : c.R (z.2, h) ∈ c.K := ⟨_, ⟨hzU, mem_univ _⟩, rfl⟩
    have hr : (c.R (z.2, h)).1 = z.2 :=
      (c.isRetraction.fst_independent z.2 hzU h 0).trans
        (StrongRetr.r_eq_self c.isRetraction (c.r_image ▸ hz2))
    have hmem : (z.2, (c.R (z.2, h)).2) ∈ c.K := by
      have : (z.2, (c.R (z.2, h)).2) = c.R (z.2, h) := Prod.ext hr.symm rfl
      rw [this]; exact hR
    have := c.smul_mem_K hmem (-1)
    rwa [neg_one_smul] at this
  have hτ : IsScSmoothRetractMap pc.φ.model.E pc.φ.model.C pc.φ.model.O
      (pc.φ.model.E.prod pc.F.shift) (pc.φ.model.C ×ˢ univ) (strongShiftOne pc.K)
      (fun z => (z, τ z)) := by
    refine ⟨fun z hz => hτK z hz, fun R hR => ?_⟩
    · have hU := R.isScDomain
      set R' : pc.φ.model.E 0 → ((rnSc n).prod c.φ.model.E) 0 := fun w => R w with hR'def
      have hRO : ∀ w ∈ R.U, R' w ∈ univ ×ˢ c.φ.model.O := fun w hw => by
        change R w ∈ pc.φ.model.O
        rw [← hR]; exact R.apply_mem_retract hw
      have hRsm : IsScSmooth (E := pc.φ.model.E) (F := (rnSc n).prod c.φ.model.E) R.U R' :=
        R.isScSmooth
      have hadd : IsScSmooth (E := pc.φ.model.E) (F := rnSc n) R.U
          (fun w => (R' w).1 + t₀) :=
        (hRsm.fst hU).add hU (isScSmooth_const_of_mem_smooth hU
          ((rnSc n).mem_smooth_iff.2 fun m => ⟨t₀, ScBanach.const_toBase _ m _⟩))
      have hpair : IsScSmooth (E := pc.φ.model.E) (F := c.φ.model.E.prod c.F.shift) R.U
          (fun w => ((R' w).2, ê₁ ((R' w).1 + t₀))) :=
        IsScSmooth.scPair hU (hRsm.snd hU)
          (IsScSmooth.comp hU (isScDomain_univ _) hê₁ hadd (mapsTo_univ _ _))
      have hmaps : MapsTo (fun w => ((R' w).2, ê₁ ((R' w).1 + t₀))) R.U (c.U ×ˢ univ) :=
        fun w hw => ⟨StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ (hRO w hw).2),
          mem_univ _⟩
      have hsf := IsScSmooth.comp hU (c.relOpen.prod_univ c.F.shift).isScDomain
        c.isRetraction.isScSmooth_one hpair hmaps
      have hτR : IsScSmooth (E := pc.φ.model.E) (F := c.F.shift) R.U (τ ∘ R) :=
        ((hsf.snd hU).neg hU).congr hU fun _ _ => rfl
      exact (R.isScSmooth.scPair hU hτR).congr hU fun _ _ => rfl
  -- the bump `β(t, x) = β₂(x)`
  obtain ⟨β₂, hβ₂, -, -, hβ₂s, hβ₂1⟩ := proposition_5_30 hbump c.φ.isOpen_source hxc
  set β : (Fin n → ℝ) × X → ℝ := fun p => β₂ p.2 with hβdef
  have hβ : ((rnPolyfold n).prod PX).IsScSmoothMap realPolyfold β :=
    hβ₂.comp (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)
  have hβs : tsupport β ⊆ pc.φ.source := by
    have : tsupport β ⊆ Prod.snd ⁻¹' tsupport β₂ :=
      closure_minimal (fun p hp => subset_closure (show β₂ p.2 ≠ 0 from hp))
        (isClosed_closure.preimage continuous_snd)
    exact fun p hp => ⟨mem_univ _, hβ₂s (this hp)⟩
  set S := StrongBundle.cutoffSection pc β τ with hSdef
  have hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S :=
    StrongBundle.isScPlusSection_cutoffSection hpcmem hβ hβs hτ
  refine ⟨S, hS, ?_⟩
  have hGs : IsSection (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift (n := n) f hfs) S) :=
    (isSection_pullbackLift _).sectionAdd hS.1
  filter_upwards [hσid, hφc.continuousAt.eventually hβ₂1] with t hσt hβt
  have hxt : φ t ∈ c.φ.source := by
    have := hψc t
    simp only [hψdef, Function.comp_apply, hσt] at this
    exact this
  rw [isZeroAt_pullback_iff_pullbackSlice hGs t (φ t), pullbackSlice_sectionAdd_paramLift hfs hS.1 t]
  have hsl : IsSection P (Polyfold.pullbackSlice S t) := hS.1.pullbackSlice t
  refine (c.isZeroAt_iff (hfs.sectionAdd hsl) hxt).2 ?_
  change (c (sectionAdd P f (Polyfold.pullbackSlice S t) (c.φ.symm (c.φ (φ t))))).2 = 0
  rw [c.φ.symm_apply_apply hxt, sectionAdd_apply hfs hsl, c.snd_add hxt]
  -- the fibre component of the slice at `φ(t)`
  have hty : (t, φ t) ∈ pc.φ.source := ⟨mem_univ _, hxt⟩
  have hSval : (c (Polyfold.pullbackSlice S t (φ t))).2 =
      c.F.toBase 1 (β (t, φ t) • τ (pc.φ (t, φ t))) :=
    congrArg Prod.snd (StrongBundle.apply_cutoffSection hτ.mapsTo hty)
  change (c (f (φ t))).2 + (c (Polyfold.pullbackSlice S t (φ t))).2 = 0
  rw [hSval, show β (t, φ t) = 1 from hβt, one_smul]
  have hpcφ : pc.φ (t, φ t) = (t - t₀, c.φ (φ t)) := rfl
  rw [hpcφ, hτbase _ (StrongRetr.mem_U_of_mem_O c.isRetraction
    (c.r_image ▸ c.φ.mapsTo_model _ hxt))]
  change (c (f (φ t))).2 + -(c.R (c.φ (φ t), c.F.toBase 1 (ê₁ (t - t₀ + t₀)))).2 = 0
  rw [sub_add_cancel, hê₁base t]
  have hψt : ψ t = φ t := by simp [hψdef, hσt]
  rw [hψt]
  have hK : (c.φ (φ t), (c (f (φ t))).2) ∈ c.R '' (c.U ×ˢ univ) := by
    have h := c.toPartialEquiv.map_source (c.mem_source_of_proj (by rw [hfs]; exact hxt))
    rw [c.target_eq] at h
    have e : c (f (φ t)) = (c.φ (φ t), (c (f (φ t))).2) :=
      Prod.ext (by rw [c.fst_apply (by rw [hfs]; exact hxt), hfs]) rfl
    exact e ▸ h
  have hρ := StrongRetr.ρ_eq_self_of_mem_K c.isRetraction
    (StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ c.φ.mapsTo_model _ hxt)) hK
  change (c.R (c.φ (φ t), (c (f (φ t))).2)).2 = (c (f (φ t))).2 at hρ
  rw [hρ]
  exact add_neg_cancel _

end Device

/-! ### Proposition 6.2 -/

section Prop62

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- **Proposition 6.2 (stability of the index along sc-smooth paths)**: let `X` admit sc-smooth
bump functions, `f` be an sc-Fredholm section of `P : Y → X` with tame germ data (Definition 3.51)
and `φ : ℝ → X` an sc-smooth path.  Then `ind(f, φ(t))` (Definition 6.1) is one integer for all
`t`; in particular `ind(f, φ(0)) = ind(f, φ(1))`.  The text's proof, formalized: the sc⁺-section
`S` along the path (`exists_isScPlusSection_pullback_of_path`), the local constancy of the index
of `f̃ + S` along its zero set on `ℝ × X` (Theorem 3.18, Theorem 3.15, item 240), the index
count of the slice (`isIndexAt_of_pullback_isLinOfIndex`) and the preconnectedness of `ℝ`
(`proposition_6_2_of_sections_of_slice`). -/
theorem proposition_6_2 [ParacompactSpace ((Fin 1 → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]
    (hbump : PX.AdmitsBumpFunctions) {f : X → Y} (hf : B.IsScFredholmSectionTame f)
    {φ : (Fin 1 → ℝ) → X} (hφ : (rnPolyfold 1).IsScSmoothMap PX φ) :
    ∃ i : ℤ, ∀ t, B.IsIndexAt f (φ t) i :=
  proposition_6_2_of_sections_of_slice hbump hf (continuousOn_univ.1 hφ.continuousOn)
    (fun t₀ => exists_isScPlusSection_pullback_of_path hbump hf.isScSmooth hφ t₀)
    (fun _ hS _ _ hz hi =>
      StrongBundle.isIndexAt_of_pullback_isLinOfIndex hf.toIsScFredholmSection hS hz hi)

/-- **Proposition 6.2 with no instance arguments** (the paracompactness of `ℝ × X` and of `π*Y`
is supplied by Theorem 2.16, as in `theorem_3_18'`). -/
theorem proposition_6_2' (hbump : PX.AdmitsBumpFunctions) {f : X → Y}
    (hf : B.IsScFredholmSectionTame f) {φ : (Fin 1 → ℝ) → X}
    (hφ : (rnPolyfold 1).IsScSmoothMap PX φ) :
    ∃ i : ℤ, ∀ t, B.IsIndexAt f (φ t) i := by
  have := MPolyfold.paracompactSpace_prod (rnPolyfold 1) PX
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin 1 → ℝ) × X → X))
    ((rnPolyfold 1).prod PX) B
  exact proposition_6_2 hbump hf hφ

end Prop62

end Polyfold
