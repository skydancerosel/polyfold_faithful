import Polyfold.Chapter15.CubeLiftScPlus
import Polyfold.Chapter15.TransversalExtension
import Polyfold.Chapter15.RegularPerturbations
import Polyfold.Chapter15.LocalIFT
import Polyfold.Chapter6.CubeCharts
import Polyfold.Chapter10.TameBundleCharts
import Polyfold.Chapter3.TameGermTransfer
import Polyfold.Chapter3.FillerLinearization
import Polyfold.Chapter3.SolutionTangentKernel

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), **Corollary 15.3.10 (3)**
(p. 699): the boundary hypothesis of Theorem 15.3.9 for the glued data on the cylinder
`[0, 1] × X`.

# The face condition of the glued multisection

## The text, paraphrased

In the proof of Corollary 15.3.10 (3) the text applies Theorem 15.3.9 on `[0, 1] × X` to the
multisection that is `Λ₀` over `{0} × X` and `Λ₁` over `{1} × X`, for transversal pairs
`(f, Λ₀)`, `(f, Λ₁)` and `d_X ≡ 0`; the boundary hypothesis is taken as evident: at `(t, x)` with
`t ∈ {0, 1}` the reduced tangent space of `[0, 1] × X` is `0 × T_xX`, and in this direction the
linearization of `f̃ − s̃` is that of `f − s̃(t, ·)`, which is onto by transversality.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `surjective_domRestrict_toIntr_subDeriv_of_chart`: the operator `(f − s)'(x)` restricted to
  `T^R_xX` is onto `W_x` if, in a chart `c` with presentation `T`, `D((f̂ − ŝ) ∘ r)(z)` maps
  `T_zO ∩ E_{φ(x)}` onto `K_z` (the reduced form of `surjective_toIntr_subDeriv_iff`).
* `cubeSecSlice S q`: the slice `y ↦ S(q, y)₂` of a section of `W̃`;
  `isScPlusSectionOn_cubeSecSlice` (an sc⁺-section of `W̃` on `Õ` slices to an sc⁺-section of `W`
  on `{y | (q, y) ∈ Õ}`), `isLocalRepOn_cubeSecSlice` (a local representation of a multisection
  `Λ'` of `W̃` that agrees with `Λ̃` over `{q} × X` slices to one of `w ↦ Λ̃(q, w)`).
* The product chart `χ × φ_c` with `χ` the centred chart of `[0, 1]` at `q`, restricted to an open
  `J ∋ q`: `subDeriv_cubeChart_inr`, `D((f̃ − s̃) ∘ r̃)(0, z)(0, v) = D((f̂ − ŝ(q, ·)) ∘ r)(z) v`.
* **`isBoundaryFaceOnto_cubeGlue`**: for `d_X ≡ 0`, `f` sc-Fredholm with tame germ data, and
  `(f, Λ₀)`, `(f, Λ₁)` transversal, the glued data satisfy the boundary hypothesis
  `IsBoundaryFaceOnto (cubeLiftEp f) (cubeGlue Λ₀ Λ₁)`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold EpGroupoid SEP UnitCube

variable {A : SEP.{u}}

/-! ### The reduced form of `surjective_toIntr_subDeriv_iff` -/

/-- **`(f − s)'(x)` onto on `T^R_xX`, from the chart**: if `D((f̂ − ŝ) ∘ r)(z)` maps
`T_zO ∩ E_{φ(x)}` onto `K_z` (`E_{φ(x)}` the reduced directions of the presentation `T`), then
`toIntr c hx (subDeriv c f s z)` restricted to `T^R_xX` is onto `W_x`. -/
theorem surjective_domRestrict_toIntr_subDeriv_of_chart {f : A.Obj → A.W}
    (hf : A.B.IsScSmoothSection f) {s : A.Obj → A.W} {O : Set A.Obj}
    (hs : IsScPlusSectionOn A s O) {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c)
    (hsub : c.φ.source ⊆ O) {x : A.X.PObj.Level 1} (hx : A.X.PObj.levelVal 1 x ∈ c.φ.source)
    (hfs : f (A.X.PObj.levelVal 1 x) = s (A.X.PObj.levelVal 1 x)) {m : ℕ} {V : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin m → ℝ)).prod V))
    (hon : ∀ k, (c.φ.model.E.toBase 1 (levelLift c.φ 1 (A.X.PObj.levelVal 1 x)), k) ∈ c.K →
      ∃ v ∈ rangeS (scDeriv c.U (r c.R) (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))),
        v ∈ minimalSubspaceWith T (c.φ (A.X.PObj.levelVal 1 x)) ∧
        subDeriv c f s (levelLift c.φ 1 (A.X.PObj.levelVal 1 x)) v = k) :
    Surjective ((toIntr c hx (subDeriv c f s (levelLift c.φ 1 (A.X.PObj.levelVal 1 x)))).domRestrict
      (reducedTangentFiber c.isChart hx T)) := by
  set y := A.X.PObj.levelVal 1 x with hy
  set z := levelLift c.φ 1 y with hz
  have ha : c.φ.model.E.toBase 1 z = c.φ y :=
    A.X.PObj.toBase_levelLift c.isChart hx (levelVal_mem x)
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U :=
    mem_U_of_mem_O c.isRetraction (by rw [c.r_image, ha]; exact c.φ.mapsTo_model y hx)
  have hsecs : ∀ w ∈ O, A.P (s w) = w := hs.1
  set g := subSec f s O with hg
  have hgs : IsSection A.P g := isSection_subSec hf.1 s O
  have hgrep : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O (c.φ.model.E.prod c.F)
      (c.φ.model.C ×ˢ univ) c.K (fun z => (z, c.principal g z)) := by
    refine (isScSmoothRetractMap_sectionSubOn hf hs hc hsub).congr fun w hw => ?_
    change (w, c.principal (sectionSubOn f s O) w) = (w, c.principal g w)
    rw [principal_sectionSubOn hf.1 hsecs hsub hw, principal_subSec hf.1 hsecs hsub hw]
  have hg1 : IsSc1 c.U (c.principal g ∘ r c.R) := by
    have := hgrep.comp_isScSmooth (c.isRetraction.baseRetraction c.relOpen) c.base_retract
    exact ((this.snd c.relOpen.isScDomain).congr c.relOpen.isScDomain fun _ _ => rfl).isSc1
  have hD : subDeriv c f s z = scDeriv c.U (c.principal g ∘ r c.R) z := by
    refine scDeriv_eq_of_eqOn_relOpen c.relOpen (isSc1_sub_comp_r hf hs hc hsub) hg1 subset_rfl
      subset_rfl (fun u hu => ?_) hzU
    change c.principal f (r c.R u) - c.principal s (r c.R u) = c.principal g (r c.R u)
    rw [principal_subSec hf.1 hsecs hsub (c.r_mem_O hu)]
  have h0 : IsZeroAt A.P g y := (isZeroAt_subSec_iff hf.1 hsecs (hsub hx)).2 hfs
  have hrange : ∀ α, chartOp c hx (subDeriv c f s z) α ∈ LinearMap.range (c.fiberLin hx) := by
    intro α; rw [hD]; exact chartOp_mem_range hgs hgrep hx h0 α
  intro w
  have hk : (c.φ.model.E.toBase 1 z, c.fiberLin hx w) ∈ c.K := by
    rw [ha, ← c.apply_fiberLin hx w, ← c.image_source]
    exact ⟨_, c.fiberLin_src hx w, rfl⟩
  obtain ⟨v, hv, hvmin, hvk⟩ := hon _ hk
  have hvT : v ∈ tangentFiberModel c.isChart hx := (c.mem_tangentFiberModel_iff_rangeS hx v).2 hv
  set α := (tangentFiberEquiv c.isChart hx).symm ⟨v, hvT⟩ with hα
  have hαv : fiberCoord c.isChart hx α = v := by
    rw [fiberCoord_eq_coe, hα, Equiv.apply_symm_apply]
  have hαR : α ∈ reducedTangentFiber c.isChart hx T := by
    change fiberCoord c.isChart hx α ∈ minimalSubspaceWith T (c.φ y)
    rw [hαv]; exact hvmin
  refine ⟨⟨α, hαR⟩, c.fiberLin_injective hx ?_⟩
  rw [LinearMap.domRestrict_apply, fiberLin_toIntr c hx hrange, chartOp_apply]
  have hαe : (tangentFiberEquiv c.isChart hx α : c.φ.model.E 0) = v := hαv
  rw [hαe]
  exact hvk

/-! ### Slices of sections and multisections of `W̃` at `q ∈ [0, 1]` -/

/-- The slice `y ↦ S(q, y)₂` of a map `S : [0, 1] × X → W̃`, read in `W`. -/
def cubeSecSlice (S : (A.cubeSEP 1).Obj → (A.cubeSEP 1).W) (q : Fin 1 → unitInterval) :
    A.Obj → A.W :=
  fun y => (cubeVal (S (q, y))).2

/-- `w ∈ W_y` seen in the fibre of `W̃` over `(q, y)`. -/
def cubeFibLift (q : Fin 1 → unitInterval) (w : A.W) : (A.cubeSEP 1).W :=
  (⟨((q, A.P w), w), rfl⟩ : pullbackSpace A.P (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj))

theorem cubeVal_cubeFibLift (q : Fin 1 → unitInterval) (w : A.W) :
    cubeVal (cubeFibLift q w) = ((q, A.P w), w) := rfl

theorem P_cubeFibLift (q : Fin 1 → unitInterval) (w : A.W) :
    (A.cubeSEP 1).P (cubeFibLift q w) = (q, A.P w) := rfl

/-- `cubeGlue Λ₀ Λ₁` on the fibre over `(q, y)` is `Λ₁` for `q = 1` and `Λ₀` otherwise. -/
theorem cubeGlue_cubeFibLift (Λ₀ Λ₁ : A.W → ℚ≥0) (q : Fin 1 → unitInterval) (w : A.W) :
    cubeGlue Λ₀ Λ₁ (cubeFibLift q w) = if ((q 0 : ℝ)) = 1 then Λ₁ w else Λ₀ w := rfl

/-- **The slice of an sc⁺-section of `W̃` on `Õ` is an sc⁺-section of `W` on
`{y | (q, y) ∈ Õ}`**: its level-one lift is `P'[1] ∘ G̃ ∘ i_q`, with `P'[1] : W̃[1] → W[1]` the
level-one part of the projection (`isScSmoothMap_one_pullbackProj'`) and `i_q(y) = (q, y)`. -/
theorem isScPlusSectionOn_cubeSecSlice {S : (A.cubeSEP 1).Obj → (A.cubeSEP 1).W}
    {Ot : Set (A.cubeSEP 1).Obj} (hS : IsScPlusSectionOn (A.cubeSEP 1) S Ot) (hOt : IsOpen Ot)
    (q : Fin 1 → unitInterval) :
    IsScPlusSectionOn A (cubeSecSlice S q) {y | (q, y) ∈ Ot} := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := A.B.paracompactSpace_pullback ((cubePolyfold 1).prod A.X.PObj)
    (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj)
  have hπ : ((cubePolyfold 1).prod A.X.PObj).IsScSmoothMap A.X.PObj
      (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj) := (A.X.cubeProj 1).isScSmoothMap_obj
  have hUo : IsOpen {y : A.Obj | (q, y) ∈ Ot} :=
    hOt.preimage (continuous_const.prodMk continuous_id)
  obtain ⟨hsec, G, hG, hGs⟩ := hS
  refine ⟨fun y hy => ?_, ?_⟩
  · have h1 : (cubeVal (S (q, y))).1 = (q, y) := hsec (q, y) hy
    change A.P (cubeVal (S (q, y))).2 = y
    rw [P_cubeVal_snd, h1]
  set one := oneRestrict (A.B.pullback hπ) A.B (pullbackProj' A.P Prod.snd)
    (A.B.mapsTo_oneSet_pullbackProj' hπ) with hone
  have hone_sm : (A.B.pullback hπ).toMPolyfold1.IsScSmoothMap A.B.toMPolyfold1 one :=
    A.B.isScSmoothMap_one_pullbackProj' hπ
  have hincl : A.X.PObj.IsScSmoothMap (A.cubeSEP 1).X.PObj
      (fun y : A.Obj => ((q, y) : (Fin 1 → unitInterval) × A.Obj)) :=
    (A.X.cubeIncl (n := 1) q).isScSmoothMap_obj
  have h1 : A.X.PObj.IsScSmoothOn (A.cubeSEP 1).B.toMPolyfold1
      (G ∘ fun y : A.Obj => ((q, y) : (Fin 1 → unitInterval) × A.Obj)) {y | (q, y) ∈ Ot} :=
    hGs.comp (hincl.mono hUo (subset_univ _)) fun y hy => hy
  refine ⟨one ∘ G ∘ fun y : A.Obj => ((q, y) : (Fin 1 → unitInterval) × A.Obj),
    fun y hy => ?_, MPolyfold.IsScSmoothOn.comp hone_sm h1 (mapsTo_univ _ _)⟩
  change (cubeVal ((A.cubeSEP 1).B.oneVal (G (q, y)))).2 = cubeSecSlice S q y
  rw [hG (q, y) hy]
  rfl

/-- **The slice of a local representation**: if `(s̃ᵢ, σᵢ)` represents `Λ'` on `Õ` and `Λ'` agrees
with `Λ̃` over `{q} × X`, then the slices `s̃ᵢ(q, ·)` with the same weights represent
`w ↦ Λ̃(q, w)` on `{y | (q, y) ∈ Õ}`. -/
theorem isLocalRepOn_cubeSecSlice {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λq : A.W → ℚ≥0}
    {Ot : Set (A.cubeSEP 1).Obj} (hOt : IsOpen Ot) {k : ℕ}
    {s : Fin k → (A.cubeSEP 1).Obj → (A.cubeSEP 1).W} {σ : Fin k → ℚ≥0}
    (hrep : IsLocalRepOn (A.cubeSEP 1) Λ' Ot s σ) (q : Fin 1 → unitInterval)
    (hq : ∀ w : A.W, Λ' (cubeFibLift q w) = Λq w) :
    IsLocalRepOn A Λq {y | (q, y) ∈ Ot} (fun i => cubeSecSlice (s i) q) σ := by
  classical
  refine ⟨hrep.1, fun i => isScPlusSectionOn_cubeSecSlice (hrep.2.1 i) hOt q, hrep.2.2.1,
    fun w hw => ?_⟩
  rw [← hq w, hrep.2.2.2 (cubeFibLift q w) hw]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsi : (cubeVal (s i (q, A.P w))).1 = (q, A.P w) := (hrep.2.1 i).1 (q, A.P w) hw
  have hiff : cubeFibLift q w = s i ((A.cubeSEP 1).P (cubeFibLift q w)) ↔
      w = cubeSecSlice (s i) q (A.P w) := by
    rw [P_cubeFibLift]
    constructor
    · intro h
      have := congrArg (fun v => (cubeVal v).2) h
      exact this
    · intro h
      apply cubeVal_injective
      rw [cubeVal_cubeFibLift]
      exact Prod.ext hsi.symm h
  simp only [hiff]

/-! ### The product chart `χ × φ_c` over `[0, 1] × X` -/

section CubeChart

variable [ParacompactSpace ((Fin 1 → unitInterval) × A.Obj)]
  (q : Fin 1 → unitInterval) {J : Set (Fin 1 → unitInterval)} (hJ : J ⊆ (cChart q).source)
  (hJo : IsOpen J)

/-- The centred chart of `[0, 1]` at `q` (`q ↦ 0`), restricted to an open `J`. -/
abbrev cubeChartOn : MChart (Fin 1 → unitInterval) := (cChart q).restrict hJ hJo

theorem relOpen_cubeChartOn :
    IsRelOpenInQuadrant (cubeChartOn q hJ hJo).model.E (cubeChartOn q hJ hJo).model.C
      (cubeChartOn q hJ hJo).model.O := by
  obtain ⟨W, hW, hWeq⟩ := (cChart q).exists_isOpen_image_eq hJ hJo
  change IsRelOpenInQuadrant (cChart q).model.E (cChart q).model.C ((cChart q) '' J)
  rw [hWeq]
  exact (cChart_relOpen q).inter_isOpen hW

theorem zero_mem_cubeChartOn_O (hqJ : q ∈ J) :
    (0 : (cubeChartOn q hJ hJo).model.E 0) ∈ (cubeChartOn q hJ hJo).model.O :=
  ⟨q, hqJ, cChart_self q⟩

theorem cubeChartOn_symm_zero : (cubeChartOn q hJ hJo).symm 0 = q := by
  have h := (cChart q).symm_apply_apply (mem_cChart q)
  rwa [cChart_self q] at h

/-- **The product chart data `χ × φ_c`** of `W̃` over `[0, 1] × X`, `χ = cubeChartOn q J`, with
the retraction `id × r_c`. -/
abbrev cubeChartData (c : StrongBundleChart A.X.PObj A.P) :
    PullbackChartData A.X.PObj A.P ((cubePolyfold 1).prod A.X.PObj) Prod.snd :=
  PullbackChartData.ofProdChart (MPolyfold.IsChart.restrict _ (isChart_cChart q) hJ hJo)
    (ScRetraction.id (relOpen_cubeChartOn q hJ hJo))
    (by change _root_.id '' (cubeChartOn q hJ hJo).model.O = _; rw [image_id]) c

/-- The strong bundle chart `χ × φ_c` of `W̃` (`q₀` the junk value of its inverse). -/
abbrev cubeChart (c : StrongBundleChart A.X.PObj A.P) (q₀ : (A.cubeSEP 1).W) :
    StrongBundleChart (A.cubeSEP 1).X.PObj (A.cubeSEP 1).P :=
  (cubeChartData q hJ hJo c).toChart q₀

variable {q hJ hJo}

/-- **The linearization in the direction of the slice, in the product chart**:
`D((f̃ − S) ∘ r̃)(ẑ)(0, v) = D((f̂ − Ŝ(q, ·)) ∘ r)(z) v` for `ẑ` over `(0, z)`, for the product
chart `χ × φ_c` with `χ(q) = 0`.  The chain rule for `ι(u) = (0, u)`, and
`((f̃ − S)^ ∘ r̃) ∘ ι = (f̂ − Ŝ(q, ·)) ∘ r` (`χ⁻¹(0) = q`). -/
theorem subDeriv_cubeChart_inr (hqJ : q ∈ J) {f : A.Obj → A.W} (hf : IsSection A.P f)
    (hfs : (A.cubeSEP 1).B.IsScSmoothSection (cubeLiftEp (n := 1) f hf))
    {S : (A.cubeSEP 1).Obj → (A.cubeSEP 1).W} {Ot : Set (A.cubeSEP 1).Obj}
    (hS : IsScPlusSectionOn (A.cubeSEP 1) S Ot) {c : StrongBundleChart A.X.PObj A.P}
    (q₀ : (A.cubeSEP 1).W)
    (hpc : (A.cubeSEP 1).B.IsChart
      (cubeChart q hJ hJo c q₀))
    (hsub : (cubeChart q hJ hJo c q₀).φ.source ⊆ Ot)
    {z : c.φ.model.E 1} (hzU : c.φ.model.E.toBase 1 z ∈ c.U)
    {zt : (cubeChart q hJ hJo c q₀).φ.model.E 1}
    (hzt : (cubeChart q hJ hJo c q₀).φ.model.E.toBase 1 zt =
      ((0 : Fin 1 → ℝ), c.φ.model.E.toBase 1 z)) (v : c.φ.model.E 0) :
    subDeriv (cubeChart q hJ hJo c q₀) (cubeLiftEp (n := 1) f hf) S zt
        ((0 : Fin 1 → ℝ), v) = subDeriv c f (cubeSecSlice S q) z v := by
  have hH : IsSc1 (cubeChart q hJ hJo c q₀).U
      ((fun y => (cubeChart q hJ hJo c q₀).principal (cubeLiftEp (n := 1) f hf) y -
        (cubeChart q hJ hJo c q₀).principal S y) ∘ r (cubeChart q hJ hJo c q₀).R) :=
    isSc1_sub_comp_r hfs hS hpc hsub
  set ι := ScBanach.prodInrOp (rnSc 1) c.φ.model.E with hι
  have hι1 : IsSc1 (E := c.φ.model.E) (F := (cubeChart q hJ hJo c q₀).φ.model.E) c.U (ι 0) :=
    ((ι.isScSmooth c.relOpen.isScDomain) 1).1
  have hι0 : IsSc0 c.φ.model.E (cubeChart q hJ hJo c q₀).φ.model.E univ (ι 0) := ι.isSc0
  have hmaps : MapsTo (ι 0) c.U (cubeChart q hJ hJo c q₀).U := fun w hw =>
    show ((0 : Fin 1 → ℝ), w) ∈ (cubeChartOn q hJ hJo).model.O ×ˢ c.U from
      ⟨zero_mem_cubeChartOn_O q hJ hJo hqJ, hw⟩
  have h0 : z ∈ c.φ.model.E.lvlSet c.U 1 := by rw [ScBanach.mem_lvlSet]; exact hzU
  have hchain := scDeriv_comp_apply' c.relOpen (cubeChart q hJ hJo c q₀).relOpen hι1 hH hmaps h0 v
  have hlvl : levelMap (E := c.φ.model.E) (F := (cubeChart q hJ hJo c q₀).φ.model.E) (ι 0) 1 z =
      zt := by
    apply (cubeChart q hJ hJo c q₀).φ.model.E.toBase_injective 1
    rw [IsSc0.toBase_levelMap hι0 (by rw [ScBanach.mem_lvlSet]; exact mem_univ _), hzt]
    rfl
  have hDι : scDeriv (E := c.φ.model.E) (F := (cubeChart q hJ hJo c q₀).φ.model.E) c.U (ι 0) z =
      ι 0 :=
    ι.scDeriv_eq c.relOpen.isScDomain h0
  rw [hlvl, hDι] at hchain
  have hHι : ((fun y => (cubeChart q hJ hJo c q₀).principal (cubeLiftEp (n := 1) f hf) y -
      (cubeChart q hJ hJo c q₀).principal S y) ∘
      r (cubeChart q hJ hJo c q₀).R) ∘ ι 0 =
      (fun y => c.principal f y - c.principal (cubeSecSlice S q) y) ∘ r c.R := by
    funext w
    change (c (cubeLiftEp (n := 1) f hf ((cubeChartOn q hJ hJo).symm 0,
        c.φ.symm (r c.R w))).1.2).2 -
      (c (S ((cubeChartOn q hJ hJo).symm 0, c.φ.symm (r c.R w))).1.2).2 =
      (c (f (c.φ.symm (r c.R w)))).2 - (c (cubeSecSlice S q (c.φ.symm (r c.R w)))).2
    rw [cubeChartOn_symm_zero]
    rfl
  rw [hHι] at hchain
  exact hchain

end CubeChart

/-! ### The face condition of the glued data -/

/-- **The boundary hypothesis of Theorem 15.3.9 for the glued data of Corollary 15.3.10 (3)**:
for `d_X ≡ 0`, `f` sc-Fredholm with tame germ data and `(f, Λ₀)`, `(f, Λ₁)` transversal, every
sc⁺-multisection `Λ'` of `W̃` agreeing with `cubeGlue Λ₀ Λ₁` over `∂([0, 1] × X) = {0, 1} × X` is in
general position at the boundary points of `supp(Λ̃ ∘ f̃)`.  At `(q, y)`, `q ∈ {0, 1}`, in the
product chart `χ_q × φ_c` (`c` tame, so `T^R_y X = T_y X`), `(0, v)` is a reduced direction and
`(f̃ − s̃ᵢ)'(0, v) = (f − s̃ᵢ(q, ·))'(v)`, and the slices `s̃ᵢ(q, ·)` represent `Λ_q` near `y`. -/
theorem isBoundaryFaceOnto_cubeGlue (hd : ∀ x, A.X.PObj.degIndex x = 0) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ₀ Λ₁ : A.W → ℚ≥0} (h₀ : IsTransversal f Λ₀) (h₁ : IsTransversal f Λ₁) :
    IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁) := by
  classical
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := A.B.paracompactSpace_pullback ((cubePolyfold 1).prod A.X.PObj)
    (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj)
  have hπ : ((cubePolyfold 1).prod A.X.PObj).IsScSmoothMap A.X.PObj
      (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj) := (A.X.cubeProj 1).isScSmoothMap_obj
  have hXP : A.X.PObj.IsTame := A.X.PObj.isTame_of_degIndex_eq_zero hd
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hft' := isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft
  intro Λ' hΛ' hbd xt
  set p := (A.cubeSEP 1).X.PObj.levelVal 1 xt with hp
  set q := p.1 with hq
  set y := p.2 with hy
  intro hxb _ hpos L hL φ hφ hx k V T hT
  have hq01 : (q 0 : ℝ) = 0 ∨ (q 0 : ℝ) = 1 := (mem_boundary_cubeSEP_iff hX hd p).1 hxb
  -- the end multisection `Λ_q`
  set Λq : A.W → ℚ≥0 := fun w => if (q 0 : ℝ) = 1 then Λ₁ w else Λ₀ w with hΛqdef
  have hΛq : IsTransversal f Λq := by
    by_cases h : (q 0 : ℝ) = 1
    · have e : Λq = Λ₁ := funext fun w => if_pos h
      rw [e]; exact h₁
    · have e : Λq = Λ₀ := funext fun w => if_neg h
      rw [e]; exact h₀
  have hbdq : ∀ w : A.W, Λ' (cubeFibLift q w) = Λq w := fun w => by
    rw [hbd (cubeFibLift q w) ((mem_boundary_cubeSEP_iff hX hd (q, A.P w)).2 hq01),
      cubeGlue_cubeFibLift]
  -- a local representation of `Λ'` around `p` and a box `J₀ × O₀` inside its domain
  obtain ⟨R, k', s, σ, hrep⟩ := hΛ'.2 p
  obtain ⟨J₀, O₀, hJ₀, hO₀, hqJ₀, hyO₀, hbox⟩ := isOpen_prod_iff.1 R.isOpen_U q y R.mem_U
  -- a tame chart of `W` around `y`, restricted to `O₀`
  obtain ⟨c₀, hc₀t, hyc₀⟩ := A.B.exists_isTameChart hXP y
  have hOco : IsOpen (O₀ ∩ c₀.φ.source) := hO₀.inter c₀.φ.isOpen_source
  set c := c₀.restrict inter_subset_right hOco with hcdef
  have hc : A.B.IsChart c := hc₀t.isChart.restrict inter_subset_right hOco
  have hyc : y ∈ c.φ.source := ⟨hyO₀, hyc₀⟩
  -- `T^R_y X = T_y X` in the chart `c`
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
  -- the product chart `χ × φ_c` around `p`
  have hJo : IsOpen (J₀ ∩ (cChart q).source) := hJ₀.inter (cChart q).isOpen_source
  have hqJ : q ∈ J₀ ∩ (cChart q).source := ⟨hqJ₀, mem_cChart q⟩
  set pc := cubeChart q inter_subset_right hJo c (cubeLiftEp (n := 1) f hf.1.1.1 p) with hpcdef
  have hpc : (A.cubeSEP 1).B.IsChart pc :=
    PullbackChartData.isChart_toChart A.B hπ _ hc _
  have hpcsub : pc.φ.source ⊆ R.U := fun z hz => hbox ⟨hz.1.1, hz.2.1⟩
  have hpmem : p ∈ pc.φ.source := ⟨hqJ, hyc⟩
  -- the operator `L` is `(f̃ − s̃ᵢ)'(p)` for some branch through `f̃(p)`
  set dt : LocalLinData (A.cubeSEP 1) Λ' xt :=
    ⟨R.U, R.isOpen_U, k', s, σ, hrep, pc, hpc, hpcsub, hpmem⟩
  rw [linearization_eq hft' dt] at hL
  obtain ⟨i, hi, rfl⟩ := (mem_support_linSumIntr_iff hft'.1.1.1 hrep.1
    (fun i => (hrep.2.1 i).1) hpcsub hpmem L).1 hL
  -- the product presentation, and `T^R` read in the product chart
  obtain ⟨nχ, Wχ, Tχ, hTχ⟩ := (cubeChartOn q inter_subset_right hJo).model.isPartialQuadrant
  have hTpc : pc.φ.model.C = (prodPresentation Tχ Tc) 0 ⁻¹' quadrant (nχ + nc) (Wχ.prod Wc) 0 :=
    prod_eq_prodPresentation Tχ Tc hTχ hTc
  rw [reducedTangentFiber_eq hφ hx T pc.isChart hpmem (prodPresentation Tχ Tc) hT hTpc]
  -- transversality of `(f, Λ_q)` at `y`, read in `c`
  have hposq : 0 < Λq (f y) := hpos
  obtain ⟨-, hy1, hon⟩ := hΛq y hposq
  set y₁ : A.X.PObj.Level 1 := A.X.PObj.levelMk 1 y hy1 with hy₁def
  have hy₁ : A.X.PObj.levelVal 1 y₁ = y := rfl
  have hycs : A.X.PObj.levelVal 1 y₁ ∈ c.φ.source := hyc
  have hrepX : IsLocalRepOn A Λq (O₀ ∩ c₀.φ.source) (fun j => cubeSecSlice (s j) q) σ :=
    (isLocalRepOn_cubeSecSlice R.isOpen_U hrep q hbdq).mono hOco
      (fun y' hy' => hbox ⟨hqJ₀, hy'.1⟩)
  set dX : LocalLinData A Λq y₁ :=
    ⟨O₀ ∩ c₀.φ.source, hOco, k', _, σ, hrepX, c, hc, subset_rfl, hycs⟩
  have hfsi : cubeSecSlice (s i) q (A.X.PObj.levelVal 1 y₁) = f (A.X.PObj.levelVal 1 y₁) :=
    congrArg (fun w => (cubeVal w).2) hi
  have hsurjX := (isOntoAtLevel_iff hf dX).1 hon i hfsi
  have hchartX := (surjective_toIntr_subDeriv_iff hf.1.1 (hrepX.2.1 i) hc subset_rfl hycs
    hfsi.symm).1 hsurjX
  -- the chart condition in `χ × φ_c`
  refine surjective_domRestrict_toIntr_subDeriv_of_chart hft'.1.1 (hrep.2.1 i) hpc hpcsub hpmem
    hi.symm (prodPresentation Tχ Tc) fun kk hk => ?_
  set z := levelLift c.φ 1 (A.X.PObj.levelVal 1 y₁) with hzdef
  set zt := levelLift pc.φ 1 p with hztdef
  have haz : c.φ.model.E.toBase 1 z = c.φ y :=
    A.X.PObj.toBase_levelLift c.isChart hycs (levelVal_mem y₁)
  have hyO : c.φ y ∈ c.φ.model.O := c.φ.mapsTo_model y hyc
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U := by
    rw [haz]; exact mem_U_of_mem_O c.isRetraction (by rw [c.r_image]; exact hyO)
  have hazt : pc.φ.model.E.toBase 1 zt = ((0 : Fin 1 → ℝ), c.φ.model.E.toBase 1 z) := by
    rw [(A.cubeSEP 1).X.PObj.toBase_levelLift pc.isChart hpmem (levelVal_mem xt), haz]
    exact Prod.ext (cChart_self q) rfl
  -- `K` of the product chart over `(0, φ_c(y))` is `K` of `c` over `φ_c(y)`
  have hkc : (c.φ.model.E.toBase 1 z, kk) ∈ c.K := by
    rw [hazt] at hk
    change _ ∈ pullbackRetraction (cubeChartData q inter_subset_right hJo c).c.R
      (cubeChartData q inter_subset_right hJo c).RZ (cubeChartData q inter_subset_right hJo c).g ''
      ((cubeChartData q inter_subset_right hJo c).RZ.U ×ˢ univ) at hk
    rw [(cubeChartData q inter_subset_right hJo c).image_eq_Kg] at hk
    have hg : (cubeChartData q inter_subset_right hJo c).g
        ((0 : Fin 1 → ℝ), c.φ.model.E.toBase 1 z) = c.φ.model.E.toBase 1 z := by
      change c.φ (c.φ.symm (c.φ.model.E.toBase 1 z)) = c.φ.model.E.toBase 1 z
      rw [haz]
      exact c.φ.apply_symm_apply hyO
    have h2 : ((cubeChartData q inter_subset_right hJo c).g
        ((0 : Fin 1 → ℝ), c.φ.model.E.toBase 1 z), kk) ∈ c.K := hk.2
    rw [hg] at h2
    exact h2
  obtain ⟨v, ⟨v₀, hv₀⟩, hvk⟩ := hchartX kk hkc
  refine ⟨((0 : Fin 1 → ℝ), v), ⟨((0 : Fin 1 → ℝ), v₀), ?_⟩, ?_, ?_⟩
  · -- `D(id × r)(zt)(0, v₀) = (0, Dr(z) v₀)`
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
    have e := congrArg (fun M : pc.φ.model.E 0 →L[ℝ] pc.φ.model.E 0 =>
      M ((0 : Fin 1 → ℝ), v₀)) h1
    refine e.trans (Prod.ext ?_ ?_)
    · exact ContinuousLinearMap.map_zero _
    · change scDeriv c.U (r c.R) zt.2 v₀ = v
      rw [hzt2]; exact hv₀
  · -- `(0, v)` is a reduced direction
    have hm : ((0 : Fin 1 → ℝ), v) ∈ (minimalSubspaceWith Tχ (pc.φ p).1).prod
        (minimalSubspaceWith Tc (pc.φ p).2) := by
      refine Submodule.mem_prod.2 ⟨zero_mem _, ?_⟩
      change v ∈ minimalSubspaceWith Tc (c.φ y)
      rw [htop]; exact Submodule.mem_top
    exact (SetLike.ext_iff.1 (minimalSubspaceWith_prodPresentation (T := Tχ) (T' := Tc)
      (pc.φ p : ((cubeChartOn q inter_subset_right hJo).model.E.prod c.φ.model.E) 0)) _).2 hm
  · -- `(f̃ − s̃ᵢ)'(0, v) = (f − s̃ᵢ(q, ·))'(v)`
    rw [subDeriv_cubeChart_inr hqJ hf.1.1.1 hft'.1.1 (hrep.2.1 i) _ hpc hpcsub hzU hazt v]
    exact hvk

end SBLocalization

end Polyfold
