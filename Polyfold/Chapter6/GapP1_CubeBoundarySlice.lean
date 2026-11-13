import Polyfold.Chapter6.GapP1_CubeLemmas

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, Lemmas 6.6.4–6.6.5
(pp. 264–265; preprint Lemmas 6.29–6.30) for families on `[0, 1]ⁿ`: **the slices `F_q` at every
`q ∈ [0, 1]ⁿ` and the product chart centred at `(q, Φ(q))`**, the chart computations behind
property (P) at boundary points (gap G.65; rows V6.33, V6.34).

# Slices over `[0, 1]ⁿ × X` and the centred product chart

## What is formalized

* `prodSlice S t`: the slice `x ↦ S(t, x)` of a section of `pr₂*P` over `T × X` (the generic form
  of `pullbackSlice`), with `IsSection.prodSlice`, `isZeroAt_iff_prodSlice`,
  `prodSlice_sectionAdd_cubeLift`, `prodSlice_paramSlice`, and
  `IsScPlusSection.cubeSlice` (the slice at `q ∈ [0, 1]ⁿ` of an sc⁺-section is sc⁺).
* The product chart `pc = χ_q × φ_c` of `[0, 1]ⁿ × X` (`cubeProdData`) centred at `(q, Φ(q))`:
  its principal parts at `0` are those of the slices (`cubePC_principal_zero`), its fibre over `0`
  is that of `c` (`mem_K_cubePC_zero_iff`), its tangent space at `0` is `ℝⁿ × T₀O`
  (`cubePC_mem_tangent_iff`), and `Lin_G(0)(0, v) = Lin_{G(q, ·)}(0) v`
  (`linAt_cubePC_slice`).
* **The curve of zeros on the cube** (`exists_hasFDerivWithinAt_cubeCurve`): for an sc-smooth
  `Γ : [0, 1]ⁿ → X'` along which an sc-smooth section `g` vanishes, the reading
  `v ↦ φ'(Γ(χ_q⁻¹(v)))` has a derivative `D` at `0` within a relatively open `V₀ ⊆ C_{χ_q}`, and
  `D τ ∈ ker Lin_g` for **every** `τ ∈ ℝⁿ`, inward and outward directions included (the chain
  rule on the relatively open `V₀`, `scDeriv_mem_linKer_of_eqOn_zero`).
* `mem_minimalSubspaceWith_of_hasFDerivWithinAt` (**the reduced directions**): if `τ` lies in the
  reduced tangent space `E_0` of the cube chart at `0` (the coordinates of `q` in `(0, 1)`), the
  derivative of `v ↦ φ_c(Φ(χ_q⁻¹(v)))` in the direction `τ` lies in the reduced tangent space of
  `c` at `0` (a local minimum of each corner coordinate along the line `s ↦ sτ`, which stays in
  `C_{χ_q}`).  Outward directions `τ` (the coordinates with `qᵢ ∈ {0, 1}`) are not covered, and
  they need not be: this is the point at which the `ℝⁿ` argument
  (`fderiv_mem_minimalSubspaceWith_of_centre`) is adapted to the boundary.
-/

open Set Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Polyfold

universe u v w

open StrongRetr StrongBundle UnitCube

/-! ### Slices of sections of `pr₂*P` over `T × X` -/

section ProdSlice

variable {T : Type w} {X : Type u} {Y : Type v} {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})]

/-- The **slice** `x ↦ S(t, x)` (read in `Y`) of a section `S` of `pr₂*P` over `T × X`. -/
def prodSlice (S : T × X → pullbackSpace P (Prod.snd : T × X → X)) (t : T) : X → Y :=
  fun x => (S (t, x)).1.2

omit [∀ x, AddCommGroup (P ⁻¹' {x})] in
/-- The slice of a section is a section. -/
lemma IsSection.prodSlice {S : T × X → pullbackSpace P (Prod.snd : T × X → X)}
    (hS : IsSection (pullbackProj P Prod.snd) S) (t : T) :
    IsSection P (prodSlice S t) := fun x =>
  mem_fiber_of_isSection_pullback_snd hS (t, x)

/-- `G(t, x) = 0` in `pr₂*Y` iff the slice vanishes at `x`. -/
lemma isZeroAt_iff_prodSlice {G : T × X → pullbackSpace P (Prod.snd : T × X → X)}
    (hG : IsSection (pullbackProj P Prod.snd) G) (t : T) (x : X) :
    IsZeroAt (pullbackProj P Prod.snd) G (t, x) ↔ IsZeroAt P (prodSlice G t) x := by
  rw [isZeroAt_pullback_snd_iff hG]
  rfl

/-- The slice of `f̃ + S` is `f + S(t, ·)`. -/
lemma prodSlice_sectionAdd_pullbackLift {f : X → Y} (hf : IsSection P f)
    {S : T × X → pullbackSpace P (Prod.snd : T × X → X)}
    (hS : IsSection (pullbackProj P Prod.snd) S) (t : T) :
    prodSlice (sectionAdd (pullbackProj P Prod.snd)
      (pullbackLift Prod.snd (f ∘ Prod.snd) fun z => hf z.2) S) t =
      sectionAdd P f (prodSlice S t) := by
  funext x
  have hL : IsSection (pullbackProj P (Prod.snd : T × X → X))
      (pullbackLift Prod.snd (f ∘ Prod.snd) fun z => hf z.2) := isSection_pullbackLift _
  change (sectionAdd (pullbackProj P Prod.snd) _ S (t, x)).1.2 = _
  rw [sectionAdd_pullback_snd_apply hL hS (t, x), sectionAdd_apply hf (hS.prodSlice t)]
  rfl

end ProdSlice

/-! ### The slices at `q ∈ [0, 1]ⁿ` -/

section CubeSlice

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X} {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {B : StrongBundle PX P}

/-- The inverse of the centred chart sends `0` to `q`. -/
lemma cChart_symm_zero (q : Fin n → unitInterval) : (cChart q).symm 0 = q := by
  have h := (cChart q).symm_apply_apply (mem_cChart q)
  rwa [cChart_self q] at h

variable [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))]

/-- **The slice at `q ∈ [0, 1]ⁿ` of an sc⁺-section of `pr₂*P` is an sc⁺-section of `P`** (the
`[0, 1]ⁿ` form of `IsScPlusSection.pullbackSlice`): in a chart `c` of the atlas, the product
chart `χ_q × φ_c` is a chart of the atlas of `pr₂*P`, and the local representative of `S(q, ·)`
in `c` is that of `S` composed with `u ↦ (0, u)` and projected to `E ⊕ F¹`. -/
theorem StrongBundle.IsScPlusSection.cubeSlice
    {S : (Fin n → unitInterval) × X → pullbackSpace P Prod.snd}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection S)
    (q : Fin n → unitInterval) : B.IsScPlusSection (prodSlice S q) := by
  have hsec : IsSection P (prodSlice S q) := hS.1.prodSlice q
  refine ⟨hsec, fun c hc => ?_⟩
  set d := cubeProdData q c with hd
  set q₀ : pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X) :=
    S (q, c.φ.symm 0) with hq₀
  set pc := d.toChart q₀ with hpc
  have hmem : pc ∈ (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).atlas.charts :=
    ⟨d, q₀, hc, rfl⟩
  obtain ⟨hrange, hsm⟩ := hS.2 pc hmem
  have hsrc : ∀ x ∈ c.φ.source, (q, x) ∈ pc.φ.source := fun x hx => ⟨mem_cChart q, hx⟩
  refine ⟨fun x hx => hrange (q, x) (hsrc x hx), ?_⟩
  have hO : IsScRetract c.φ.model.E c.φ.model.C c.φ.model.O := c.φ.model.isScRetract
  have hι : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O pc.φ.model.E pc.φ.model.C
      pc.φ.model.O (ScBanach.prodInrOp (rnSc n) c.φ.model.E 0) :=
    (ScBanach.prodInrOp (rnSc n) c.φ.model.E).isScSmoothRetractMap hO
      fun u hu => show ((0 : Fin n → ℝ), u) ∈ (cChart q).model.O ×ˢ c.φ.model.O from
        ⟨zero_mem_cChart_O q, hu⟩
  have hcomp := hsm.comp hι pc.φ.model.isScRetract
  set π := ScBanach.prodSndLeftOp (rnSc n) c.φ.model.E c.F.shift with hπ
  refine ⟨fun z hz => ?_, fun R hR => ?_⟩
  · have hzs := c.φ.symm_mapsTo hz
    exact c.liftOne_mem (c.mem_source_of_proj (by rw [hsec]; exact hzs))
      (hrange (q, _) (hsrc _ hzs))
  · have hU := R.isScDomain
    have h1 := hcomp.comp_isScSmooth R hR
    have h2 := IsScSmooth.comp hU (isScDomain_univ _) (π.isScSmooth (isScDomain_univ _)) h1
      (mapsTo_univ _ _)
    refine h2.congr hU fun u hu => ?_
    have hRu : R u ∈ c.φ.model.O := by rw [← hR]; exact R.apply_mem_retract hu
    have hRs := c.φ.symm_mapsTo hRu
    change ((StrongBundle.localRepOne pc S ((0 : Fin n → ℝ), R u)).1.2,
        (StrongBundle.localRepOne pc S ((0 : Fin n → ℝ), R u)).2) =
      StrongBundle.localRepOne c (prodSlice S q) (R u)
    have hsymm : pc.φ.symm ((0 : Fin n → ℝ), R u) = (q, c.φ.symm (R u)) := by
      change ((cChart q).symm 0, c.φ.symm (R u)) = _
      rw [cChart_symm_zero]
    simp only [StrongBundle.localRepOne, hsymm]
    refine Prod.ext ?_ rfl
    change (pc.φ (S (q, c.φ.symm (R u))).1.1).2 = (c (prodSlice S q (c.φ.symm (R u)))).1
    have hS1 : (S (q, c.φ.symm (R u))).1.1 = (q, c.φ.symm (R u)) := hS.1 (q, c.φ.symm (R u))
    rw [hS1, c.fst_apply (by rw [hsec]; exact hRs), hsec]
    rfl

end CubeSlice

/-! ### The product chart `χ_q × φ_c` centred at `(q, y)` -/

section CubePC

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X} {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {B : StrongBundle PX P}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))]

/-- The product chart `χ_q × φ_c` of `pr₂*P` over `[0, 1]ⁿ × X` (`cubeProdData`). -/
abbrev cubePC (q : Fin n → unitInterval) (c : StrongBundleChart PX P)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)) :
    StrongBundleChart ((cubePolyfold n).prod PX)
      (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X)) :=
  (cubeProdData q c).toChart q₀

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))] in
/-- The product chart is centred at `(q, y)` when `φ_c(y) = 0`. -/
lemma cubePC_apply_eq_zero (q : Fin n → unitInterval) (c : StrongBundleChart PX P)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)) {y : X}
    (hφ0 : c.φ y = 0) : (cubePC q c q₀).φ (q, y) = 0 :=
  Prod.ext (cChart_self q) hφ0

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))] in
/-- The principal part of a section of `pr₂*P` at the centre of `χ_q × φ_c` is that of its slice
at `q` in `c`. -/
lemma cubePC_principal_zero (q : Fin n → unitInterval) (c : StrongBundleChart PX P)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
    (S' : (Fin n → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)) :
    (cubePC q c q₀).principal S' 0 = c.principal (prodSlice S' q) 0 := by
  change (c (S' ((cChart q).symm 0, c.φ.symm 0)).1.2).2 = (c (S' (q, c.φ.symm 0)).1.2).2
  rw [cChart_symm_zero]

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))] in
/-- **The fibre of the product chart over `0`** is the fibre `K₀` of `c`. -/
lemma mem_K_cubePC_zero_iff (q : Fin n → unitInterval) (c : StrongBundleChart PX P)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
    (h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O) (k : c.F 0) :
    ((0 : (cubePC q c q₀).φ.model.E 0), k) ∈ (cubePC q c q₀).K ↔ (0, k) ∈ c.K := by
  change _ ∈ pullbackRetraction (cubeProdData q c).c.R (cubeProdData q c).RZ
    (cubeProdData q c).g '' ((cubeProdData q c).RZ.U ×ˢ univ) ↔ _
  rw [(cubeProdData q c).image_eq_Kg]
  have hg0 : (cubeProdData q c).g 0 = 0 := by
    change c.φ (((cChart q).prod c.φ).symm 0).2 = 0
    rw [MChart.prod_symm_apply]
    exact c.φ.apply_symm_apply h0O
  have h0R : (0 : (cubePC q c q₀).φ.model.E 0) ∈ (cubeProdData q c).RZ.retract := by
    rw [(cubeProdData q c).RZ_retract]
    exact ⟨zero_mem_cChart_O q, h0O⟩
  change (0 : (cubePC q c q₀).φ.model.E 0) ∈ (cubeProdData q c).RZ.retract ∧
      ((cubeProdData q c).g 0, k) ∈ c.K ↔ _
  rw [hg0]
  exact ⟨fun h => h.2, fun h => ⟨h0R, h⟩⟩

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))] in
/-- `D(id × r)(0) = id × Dr(0)` in the product chart. -/
lemma cubePC_scDeriv_r_zero (q : Fin n → unitInterval) (c : StrongBundleChart PX P)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
    (h0U : (0 : c.φ.model.E 0) ∈ c.U) (v : (Fin n → ℝ) × c.φ.model.E 0) :
    scDeriv (cubePC q c q₀).U (r (cubePC q c q₀).R) (0 : (cubePC q c q₀).φ.model.E 1) v =
      (v.1, scDeriv c.U (r c.R) (0 : c.φ.model.E 1) v.2) := by
  have hO0 := zero_mem_cChart_O q
  have hrelχ := cChart_relOpen q
  have h0' : (0 : (rnSc n |>.prod c.φ.model.E) 1) ∈
      (rnSc n |>.prod c.φ.model.E).lvlSet ((cChart q).model.O ×ˢ c.U) 1 := by
    change (rnSc n |>.prod c.φ.model.E).toBase 1 0 ∈ (cChart q).model.O ×ˢ c.U
    rw [map_zero]
    exact ⟨hO0, h0U⟩
  have h1 := scDeriv_prodMap (F := rnSc n) (F' := c.φ.model.E) hrelχ c.relOpen
    (isScSmooth_id hrelχ.isScDomain)
    (c.isRetraction.baseRetraction c.relOpen).isScSmooth h0'
  have e := congrArg (fun L : (rnSc n |>.prod c.φ.model.E) 0 →L[ℝ]
    (rnSc n |>.prod c.φ.model.E) 0 => L v) h1
  have h2 : scDeriv (E := rnSc n) (F := rnSc n) (cChart q).model.O id (0 : (rnSc n) 1) =
      ContinuousLinearMap.id ℝ (Fin n → ℝ) :=
    IsSc1.scDeriv_eqOn (isSc1With_id _) (hrelχ.isScDomain.uniqueDiffWithinAt 1)
      (by
        change (ScBanach.const (Fin n → ℝ)).toBase 1 (0 : Fin n → ℝ) ∈
          ((cChart q).model.O : Set (Fin n → ℝ))
        rw [ScBanach.const_toBase]; exact hO0)
  refine e.trans (Prod.ext ?_ rfl)
  exact congrArg (fun L : (rnSc n) 0 →L[ℝ] (rnSc n) 0 => L v.1) h2

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))] in
/-- The tangent space of the product chart at `0` is `ℝⁿ × T₀O`. -/
lemma cubePC_mem_tangent_iff (q : Fin n → unitInterval) (c : StrongBundleChart PX P)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
    (h0U : (0 : c.φ.model.E 0) ∈ c.U) (w : (Fin n → ℝ) × c.φ.model.E 0) :
    w ∈ rangeS (scDeriv (cubePC q c q₀).U (r (cubePC q c q₀).R)
      (0 : (cubePC q c q₀).φ.model.E 1)) ↔
      w.2 ∈ rangeS (scDeriv c.U (r c.R) (0 : c.φ.model.E 1)) := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y.2, congrArg Prod.snd ((cubePC_scDeriv_r_zero q c q₀ h0U y).symm.trans hy)⟩
  · rintro ⟨y, hy⟩
    exact ⟨(w.1, y), (cubePC_scDeriv_r_zero q c q₀ h0U (w.1, y)).trans (Prod.ext rfl hy)⟩

/-- **The linearization on the slice direction, in the product chart over `[0, 1]ⁿ`** (the
`[0, 1]ⁿ` form of `linAt_ofProd_slice`): `Lin_G(0)(0, v) = Lin_{G(q, ·)}(0) v`.  The chain rule
for `Ĝ ∘ (id × r)` composed with `ι(u) = (0, u)`, and `(Ĝ ∘ (id × r)) ∘ ι = Ĝ(q, ·) ∘ r`
(`χ_q⁻¹(0) = q`). -/
theorem linAt_cubePC_slice
    {G : (Fin n → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X)}
    (hG : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScSmoothSection G)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (q : Fin n → unitInterval)
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))
    (h0U : (0 : c.φ.model.E 0) ∈ c.U)
    (v : ↥(rangeS (scDeriv (cubePC q c q₀).U (r (cubePC q c q₀).R)
      (0 : (cubePC q c q₀).φ.model.E 1))))
    (hv : (v.1 : (Fin n → ℝ) × c.φ.model.E 0).1 = 0) :
    linAt (cubePC q c q₀).U (cubePC q c q₀).R ((cubePC q c q₀).principal G) 0 v =
      linAt c.U c.R (c.principal (prodSlice G q)) 0
        ⟨(v.1 : (Fin n → ℝ) × c.φ.model.E 0).2, (cubePC_mem_tangent_iff q c q₀ h0U _).1 v.2⟩ := by
  revert hv v
  set pc := cubePC q c q₀ with hpc
  intro v hv
  have hpcc : (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsChart pc :=
    (cubeProdData q c).isChart_toChart B _ hc q₀
  have hH : IsSc1 pc.U (pc.principal G ∘ r pc.R) := hG.isSc1_principal_comp_r hpcc
  set ι := ScBanach.prodInrOp (rnSc n) c.φ.model.E with hι
  have hι1 : IsSc1 (E := c.φ.model.E) (F := pc.φ.model.E) c.U (ι 0) :=
    ((ι.isScSmooth c.relOpen.isScDomain) 1).1
  have hι0 : IsSc0 c.φ.model.E pc.φ.model.E univ (ι 0) := ι.isSc0
  have hmaps : MapsTo (ι 0) c.U pc.U := fun w hw =>
    show ((0 : Fin n → ℝ), w) ∈ (cChart q).model.O ×ˢ c.U from ⟨zero_mem_cChart_O q, hw⟩
  have h0 : (0 : c.φ.model.E 1) ∈ c.φ.model.E.lvlSet c.U 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0U
  have hchain := scDeriv_comp_apply' c.relOpen pc.relOpen hι1 hH hmaps h0
    (v.1 : (Fin n → ℝ) × c.φ.model.E 0).2
  have hlvl : levelMap (E := c.φ.model.E) (F := pc.φ.model.E) (ι 0) 1 (0 : c.φ.model.E 1) =
      (0 : pc.φ.model.E 1) := by
    apply pc.φ.model.E.toBase_injective 1
    rw [IsSc0.toBase_levelMap hι0 (by rw [ScBanach.mem_lvlSet]; exact mem_univ _)]
    simp only [map_zero]
    rfl
  have hDι : scDeriv (E := c.φ.model.E) (F := pc.φ.model.E) c.U (ι 0) 0 = ι 0 :=
    ι.scDeriv_eq c.relOpen.isScDomain h0
  rw [hlvl, hDι] at hchain
  have hHι : (pc.principal G ∘ r pc.R) ∘ ι 0 = c.principal (prodSlice G q) ∘ r c.R := by
    funext w
    change (c (G ((cChart q).symm 0, c.φ.symm (r c.R w))).1.2).2 =
      (c (G (q, c.φ.symm (r c.R w))).1.2).2
    rw [cChart_symm_zero]
  rw [hHι] at hchain
  have hv' : (v.1 : (Fin n → ℝ) × c.φ.model.E 0) = ι 0 (v.1 : (Fin n → ℝ) × c.φ.model.E 0).2 :=
    Prod.ext hv rfl
  change scDeriv pc.U (pc.principal G ∘ r pc.R) 0 (v.1 : (Fin n → ℝ) × c.φ.model.E 0) =
    scDeriv c.U (c.principal (prodSlice G q) ∘ r c.R) 0 (v.1 : (Fin n → ℝ) × c.φ.model.E 0).2
  conv_lhs => rw [hv']
  exact hchain

end CubePC

/-! ### The curve of zeros on the cube -/

section Curve

/-- **sc¹ maps on relatively open subsets of partial quadrants of `ℝⁿ` are differentiable within
them** (the relatively open form of `hasFDerivAt_scDeriv_rn`). -/
lemma hasFDerivWithinAt_scDeriv_rnRel {n : ℕ} {F : ScBanach} {V₀ : Set (Fin n → ℝ)}
    {H : (Fin n → ℝ) → F 0} (hH : IsSc1 (E := rnSc n) V₀ H) {q : Fin n → ℝ} (hq : q ∈ V₀) :
    HasFDerivWithinAt H (scDeriv (E := rnSc n) V₀ H q) V₀ q := by
  have hq1 : (q : (rnSc n) 1) ∈ (rnSc n).lvlSet V₀ 1 := by
    rw [ScBanach.lvlSet_const]; exact hq
  have h := hH.isSc1With_scDeriv.hasFDerivWithinAt q hq1
  rw [ScBanach.lvlSet_const] at h
  have hcomp : H ∘ (rnSc n).toBase 1 = H :=
    funext fun x => congrArg H (ScBanach.const_toBase _ 1 x)
  have hclm : (scDeriv (E := rnSc n) V₀ H q).comp ((rnSc n).toBase 1) =
      scDeriv (E := rnSc n) V₀ H q :=
    ContinuousLinearMap.ext fun x => by
      rw [ContinuousLinearMap.comp_apply, ScBanach.const_toBase]
  rw [hcomp, hclm] at h
  exact h

/-- **The reduced directions** (the boundary form of `fderiv_mem_minimalSubspaceWith_of_centre`):
let `V₀` be relatively open in a partial quadrant `C'` of `ℝⁿ` (presentation `Tχ`), `0 ∈ V₀`, and
`h : V₀ → C` with `h(0) = 0` (presentation `T` of `C`) and derivative `D` at `0` within `V₀`.
For `τ` in the reduced tangent space `E_0` of `C'` at `0` (all its `Tχ`-corner coordinates
vanish), `D τ` lies in the reduced tangent space of `C` at `0`: the line `s ↦ sτ` stays in `C'`,
so each corner coordinate of `h(sτ)` has a local minimum `0` at `s = 0`.  Directions leaving the
boundary of `C'` are not covered. -/
theorem mem_minimalSubspaceWith_of_hasFDerivWithinAt {n n' m : ℕ} {E W W' : ScBanach}
    {C' V₀ : Set (Fin n → ℝ)} (hV₀ : IsRelOpenInQuadrant (rnSc n) C' V₀)
    (h0V : (0 : Fin n → ℝ) ∈ V₀)
    (Tχ : ScIso (rnSc n) ((ScBanach.const (Fin n' → ℝ)).prod W'))
    (hTχ : C' = Tχ 0 ⁻¹' quadrant n' W' 0)
    (T : ScIso E ((ScBanach.const (Fin m → ℝ)).prod W)) {C : Set (E 0)}
    (hT : C = T 0 ⁻¹' quadrant m W 0) {h : (Fin n → ℝ) → E 0} (hC : ∀ v ∈ V₀, h v ∈ C)
    (h00 : h 0 = 0) {D : (Fin n → ℝ) →L[ℝ] E 0} (hD : HasFDerivWithinAt h D V₀ 0)
    {τ : Fin n → ℝ} (hτ : τ ∈ minimalSubspaceWith Tχ 0) : D τ ∈ minimalSubspaceWith T 0 := by
  rw [mem_minimalSubspaceWith] at hτ ⊢
  intro i _
  have hτ0 : ∀ j, (Tχ 0 τ).1 j = 0 := fun j => hτ j (by rw [map_zero]; rfl)
  obtain ⟨U, hU, hUeq⟩ := hV₀.relOpen
  have hline : ∀ s : ℝ, s • τ ∈ C' := by
    intro s
    rw [hTχ]
    intro j
    change 0 ≤ (Tχ 0 (s • τ)).1 j
    rw [map_smul, Prod.smul_fst, Pi.smul_apply, hτ0 j, smul_zero]
  set γ : ℝ → Fin n → ℝ := fun s => s • τ with hγdef
  have hγc : Continuous γ := continuous_id.smul continuous_const
  have h0U : (0 : Fin n → ℝ) ∈ U := by rw [hUeq] at h0V; exact h0V.1
  have hS : {s : ℝ | γ s ∈ V₀} ∈ 𝓝 (0 : ℝ) := by
    have hpre : γ ⁻¹' U ∈ 𝓝 (0 : ℝ) :=
      hγc.continuousAt.preimage_mem_nhds (by simp only [hγdef, zero_smul]; exact hU.mem_nhds h0U)
    filter_upwards [hpre] with s hs
    rw [hUeq]
    exact ⟨hs, hline s⟩
  have hγd : HasDerivWithinAt γ τ {s : ℝ | γ s ∈ V₀} 0 := by
    have := (hasDerivAt_id (0 : ℝ)).smul_const τ
    simp only [one_smul] at this
    exact this.hasDerivWithinAt
  have hD' : HasFDerivWithinAt h D V₀ (γ 0) := by
    simp only [hγdef, zero_smul]; exact hD
  have hhγ : HasDerivAt (h ∘ γ) (D τ) 0 :=
    (hD'.comp_hasDerivWithinAt (0 : ℝ) hγd fun s hs => hs).hasDerivAt hS
  set L : E 0 →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp ((ContinuousLinearMap.fst ℝ (Fin m → ℝ) (W 0)).comp
      (T 0 : E 0 →L[ℝ] (Fin m → ℝ) × W 0)) with hL
  have hLd : HasDerivAt (L ∘ (h ∘ γ)) (L (D τ)) 0 := L.hasFDerivAt.comp_hasDerivAt 0 hhγ
  have hmin : IsLocalMin (L ∘ (h ∘ γ)) 0 := by
    filter_upwards [hS] with s hs
    have hCs : h (γ s) ∈ C := hC _ hs
    rw [hT] at hCs
    have e0 : (L ∘ (h ∘ γ)) 0 = 0 := by
      simp only [Function.comp_apply, hγdef, zero_smul, h00, map_zero]
    rw [e0]
    exact hCs i
  exact hmin.hasDerivAt_eq_zero hLd

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X} {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {B : StrongBundle PX P} {g : X → Y}

/-- **The derivative of a map into the zero set lies in the kernel**, on a relatively open
subset `V₀` of a partial quadrant of `ℝⁿ` (the form of `fderiv_mem_linKer` for parameter domains
with boundary): if `H : V₀ → O` is sc¹ and `ĝ ∘ H = 0` on `V₀`, then `DH(v₀) τ ∈ ker Lin_g(z)`
for every `τ ∈ ℝⁿ`, `z` the level-`1` point over `H(v₀)`. -/
theorem scDeriv_mem_linKer_of_eqOn_zero (hg : B.IsScSmoothSection g) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) {C V₀ : Set (Fin n → ℝ)} (hrel : IsRelOpenInQuadrant (rnSc n) C V₀)
    {H : (Fin n → ℝ) → c.φ.model.E 0} (hH : IsSc1 (E := rnSc n) V₀ H)
    (hHO : ∀ v ∈ V₀, H v ∈ c.φ.model.O) (hzero : ∀ v ∈ V₀, c.principal g (H v) = 0)
    {v₀ : Fin n → ℝ} (hv₀ : v₀ ∈ V₀) (z : c.φ.model.E 1)
    (hz : c.φ.model.E.toBase 1 z = H v₀) (τ : Fin n → ℝ) :
    scDeriv (E := rnSc n) V₀ H v₀ τ ∈ c.linKer g z := by
  have hq₀1 : (v₀ : (rnSc n) 1) ∈ (rnSc n).lvlSet V₀ 1 := by
    rw [ScBanach.lvlSet_const]; exact hv₀
  have hmaps : MapsTo H V₀ c.U := fun q hq =>
    mem_U_of_mem_O c.isRetraction (c.r_image ▸ hHO q hq)
  have hlev : levelMap (E := rnSc n) H 1 v₀ = z := by
    apply levelMap_eq_of_toBase_eq
    rw [hz, ScBanach.const_toBase]
  have hr1 : IsSc1 c.U (r c.R) := (r_isScSmooth c.relOpen c.isRetraction).isSc1
  have hrH : scDeriv (E := rnSc n) V₀ (r c.R ∘ H) v₀ = scDeriv (E := rnSc n) V₀ H v₀ :=
    scDeriv_eq_of_eqOn_relOpen hrel (theorem_1_3_1 hrel c.relOpen hH hr1 hmaps).1 hH
      subset_rfl subset_rfl (fun q hq => r_eq_self c.isRetraction (c.r_image ▸ hHO q hq)) hq₀1
  have hch1 := scDeriv_comp_apply' hrel c.relOpen hH hr1 hmaps hq₀1 τ
  rw [hrH, hlev] at hch1
  have hw : scDeriv (E := rnSc n) V₀ H v₀ τ ∈ rangeS (scDeriv c.U (r c.R) z) := ⟨_, hch1⟩
  refine (c.mem_linKer_iff g z _).2 ⟨hw, ?_⟩
  rw [linAt_apply]
  have hfr : IsSc1 c.U (c.principal g ∘ r c.R) := hg.isSc1_principal_comp_r hc
  have hch2 := scDeriv_comp_apply' hrel c.relOpen hH hfr hmaps hq₀1 τ
  rw [hlev] at hch2
  change scDeriv c.U (c.principal g ∘ r c.R) z (scDeriv (E := rnSc n) V₀ H v₀ τ) = 0
  rw [hch2]
  have hzero' : EqOn ((c.principal g ∘ r c.R) ∘ H) (fun _ => 0) V₀ := fun q hq => by
    simp only [Function.comp_apply]
    rw [r_eq_self c.isRetraction (c.r_image ▸ hHO q hq)]
    exact hzero q hq
  obtain ⟨hcomp, -⟩ := theorem_1_3_1 hrel c.relOpen hH hfr hmaps
  have d1 := hcomp.isSc1With_scDeriv.hasFDerivWithinAt v₀ hq₀1
  have d2 : HasFDerivWithinAt (((c.principal g ∘ r c.R) ∘ H) ∘ (rnSc n).toBase 1)
      ((0 : (rnSc n) 0 →L[ℝ] c.F 0).comp ((rnSc n).toBase 1)) ((rnSc n).lvlSet V₀ 1) v₀ := by
    rw [ContinuousLinearMap.zero_comp]
    exact (hasFDerivWithinAt_const (0 : c.F 0) _ _).congr (fun y hy => hzero' hy) (hzero' hq₀1)
  have := ContinuousLinearMap.ext_of_comp_toBase_one
    ((hrel.isScDomain.uniqueDiffWithinAt 1 v₀ hq₀1).eq d1 d2)
  rw [this]; rfl

/-- **The curve of zeros on the cube** (the `[0, 1]ⁿ` form of `fderiv_mem_linKer`): for an
sc-smooth `Γ : [0, 1]ⁿ → X` along which the sc-smooth section `g` vanishes, a chart `c` around
`Γ(q)` and the level-`1` point `z` over `φ_c(Γ(q))`, there are a relatively open `V₀ ∋ 0` in the
partial quadrant of the centred chart `χ_q` and the derivative `D` at `0` within `V₀` of the
reading `v ↦ φ_c(Γ(χ_q⁻¹(v)))`; every `D τ`, `τ ∈ ℝⁿ`, lies in `ker Lin_g(z)`. -/
theorem exists_hasFDerivWithinAt_cubeCurve (hg : B.IsScSmoothSection g)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) {Γ : (Fin n → unitInterval) → X}
    (hΓ : (cubePolyfold n).IsScSmoothMap PX Γ) (q : Fin n → unitInterval)
    (hq : Γ q ∈ c.φ.source) (h0 : ∀ q', IsZeroAt P g (Γ q')) (z : c.φ.model.E 1)
    (hz : c.φ.model.E.toBase 1 z = c.φ (Γ q)) :
    ∃ V₀ : Set (Fin n → ℝ), IsRelOpenInQuadrant (rnSc n) (cChart q).model.C V₀ ∧
      (0 : Fin n → ℝ) ∈ V₀ ∧ V₀ ⊆ (cChart q).model.O ∧
      (∀ v ∈ V₀, Γ ((cChart q).symm v) ∈ c.φ.source) ∧
      ∃ D : (Fin n → ℝ) →L[ℝ] c.φ.model.E 0,
        HasFDerivWithinAt (fun v => c.φ (Γ ((cChart q).symm v))) D V₀ 0 ∧
        ∀ τ, D τ ∈ c.linKer g z := by
  have hΓc : Continuous Γ := continuousOn_univ.1 hΓ.continuousOn
  set V := (cChart q).source ∩ Γ ⁻¹' c.φ.source with hV
  have hVo : IsOpen V := (cChart q).isOpen_source.inter (c.φ.isOpen_source.preimage hΓc)
  obtain ⟨W, hW, hWeq⟩ := (cChart q).exists_isOpen_image_eq
    (inter_subset_left : V ⊆ (cChart q).source) hVo
  change (cChart q) '' V = (cChart q).model.O ∩ W at hWeq
  have hrel : IsRelOpenInQuadrant (rnSc n) (cChart q).model.C ((cChart q) '' V) := by
    exact (congrArg (fun s => IsRelOpenInQuadrant (rnSc n) (cChart q).model.C s) hWeq).mpr
      ((cChart_relOpen q).inter_isOpen hW)
  have h0V : (0 : Fin n → ℝ) ∈ (cChart q) '' V := ⟨q, ⟨mem_cChart q, hq⟩, cChart_self q⟩
  have hVO : (cChart q) '' V ⊆ (cChart q).model.O := hWeq ▸ inter_subset_left
  have hVsrc : ∀ v ∈ (cChart q) '' V, Γ ((cChart q).symm v) ∈ c.φ.source := by
    rintro _ ⟨x, hx, rfl⟩
    rw [(cChart q).symm_apply_apply hx.1]
    exact hx.2
  have h1 := hΓ.smooth (cChart q) c.φ (isChart_cChart q) c.isChart V hVo
    (fun _ h => ⟨mem_univ _, h.1⟩) (fun _ h => h.2)
  set H : (Fin n → ℝ) → c.φ.model.E 0 := fun v => c.φ (Γ ((cChart q).symm v)) with hHdef
  have hH : IsScSmooth (E := rnSc n) (F := c.φ.model.E) ((cChart q) '' V) H := by
    have := h1.comp_isScSmooth (ScRetraction.id hrel) (image_id _)
    exact this.congr hrel.isScDomain fun v _ => rfl
  have hz' : c.φ.model.E.toBase 1 z = H 0 := by
    rw [hz]
    change c.φ (Γ q) = c.φ (Γ ((cChart q).symm 0))
    rw [cChart_symm_zero]
  refine ⟨(cChart q) '' V, hrel, h0V, hVO, hVsrc, scDeriv (E := rnSc n) ((cChart q) '' V) H 0,
    hasFDerivWithinAt_scDeriv_rnRel hH.isSc1 h0V, fun τ => ?_⟩
  exact scDeriv_mem_linKer_of_eqOn_zero hg hc hrel hH.isSc1
    (fun v hv => c.φ.mapsTo_model _ (hVsrc v hv))
    (fun v hv => (c.isZeroAt_iff hg.1 (hVsrc v hv)).1 (h0 _)) h0V z hz' τ

end Curve

end Polyfold
