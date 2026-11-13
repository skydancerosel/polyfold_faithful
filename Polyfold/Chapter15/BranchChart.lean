import Polyfold.Chapter15.LocalSlice

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.7** (General Position; 2017: Theorem 15.4), p. 696: (15.1) for one branch, read
as Part I's general position of a parametrized section on `W|O`.

# One branch of a linear family as a parametrized section of `W|O`

## The text, paraphrased

For a branch `Σ_j t_j s_{ij}` of the family, the map `(t, y) ↦ f(y) − Σ_j t_j s_{ij}(y)` has, by
(15.1), a surjective linearization at `(0, x)` already on `ℝ^ℓ × T^R_xX`; this is what the
implicit function theorem and the transversality of the projection to `ℝ^ℓ` use.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `negRestrict s`: the section `(−s)|O` of `W|O`; **`paramSlice_branch_eq`**: the slice at `t` of
  the parametrized section `F(t, y) = (f − 0)|O + Σ_j t_j (−s_j)|O` is `(f − Σ_j t_j s_j)|O`
  (`subRestrict f (paramSec s t)`), the branch of `Λ_t`.
* `fiberLin_toIntr_subDeriv`: the chart reading of the intrinsic operator `(f − s)'(x)`.
* **`isParamGP_restrictTo_of_onto`**: (15.1) for the branch, read in a chart `c` of `W` with
  domain in `O` centred at `x`, gives Part I's properties (i)–(ii) (`IsParamGP`) for `F` in the
  transported chart of `W|O`.
* Hence `F` is in general position (Definition 5.3.9) at `(0, x)` on `ℝ^ℓ × O` (Part I's
  `isGeneralPositionGerm_paramSection_of_isParamGP`): `isGeneralPositionGerm_branchParam` in
  `ParametricGeneralPosition`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15

variable {A : SEP.{u}}

section Branch

variable {O : Set A.Obj} (hO : IsOpen O) [Nonempty O] [ParacompactSpace O]
  [ParacompactSpace (pullbackSpace A.P (Subtype.val : O → A.Obj))]

/-- **The section `(−s)|O` of `W|O`** (`s` extended by `0` off `O`, then multiplied by `−1`). -/
def negRestrict (s : A.Obj → A.W) : O → pullbackSpace A.P (Subtype.val : O → A.Obj) :=
  restrictSection A.P O (Polyfold.sectionSmul A.P (fun _ => (-1 : ℝ)) (extendZero O s))
    (isSection_extendZero O s).sectionSmul

theorem isSection_negRestrict (s : A.Obj → A.W) :
    IsSection (pullbackProj A.P (Subtype.val : O → A.Obj)) (negRestrict (O := O) s) :=
  isSection_restrictSection _

include hO in
/-- `(−s)|O` is an sc⁺-section of `W|O` for a local sc⁺-section `s` on `O`. -/
theorem isScPlusSection_negRestrict {s : A.Obj → A.W} (hs : IsScPlusSectionOn A s O) :
    (A.B.restrictOpen hO).IsScPlusSection (negRestrict (O := O) s) :=
  (hs.extendZero.sectionSmul_const hO (isSection_extendZero O s) (-1)).restrictOpen hO
    (isSection_extendZero O s).sectionSmul

/-- The fibre identification `(ι*W)_p ≅ W_p` of the restricted bundle, as a linear map. -/
def pbLin (p : O) :
    pullbackProj A.P (Subtype.val : O → A.Obj) ⁻¹' {p} →ₗ[ℝ] A.P ⁻¹' {(p : A.Obj)} where
  toFun := pullbackFiberEquiv A.P (Subtype.val : O → A.Obj) p
  map_add' := pullbackFiberEquiv_add A.P (Subtype.val : O → A.Obj) p
  map_smul' := pullbackFiberEquiv_smul A.P (Subtype.val : O → A.Obj) p

theorem pbLin_restrictSection {h : A.Obj → A.W} (hh : IsSection A.P h) (p : O) :
    pbLin p ⟨restrictSection A.P O h hh p, isSection_restrictSection hh p⟩ = ⟨h p, hh p⟩ :=
  rfl

theorem pbLin_injective (p : O) : Injective (pbLin (O := O) p) :=
  (pullbackFiberEquiv A.P (Subtype.val : O → A.Obj) p).injective

/-- **The slice of the parametrized branch is the branch of `Λ_t`**: with
`F(t, y) = (f − 0)|O + Σ_j t_j (−s_j)|O`, the slice at `t` is `(f − Σ_j t_j s_j)|O`. -/
theorem paramSlice_branch_eq {f : A.Obj → A.W} (hf : IsSection A.P f) {ℓ : ℕ}
    {s : Fin ℓ → A.Obj → A.W} (hs : ∀ j, IsSection A.P (s j)) (t : Fin ℓ → ℝ) :
    paramSlice (subRestrict (O := O) f (fiberZero A.P) hf) (isSection_restrictSection _)
        (fun j => negRestrict (O := O) (s j)) (fun j => isSection_negRestrict (s j)) t =
      subRestrict (O := O) f (paramSec s t) hf := by
  funext p
  have hlhs := isSection_paramSlice (g := subRestrict (O := O) f (fiberZero A.P) hf)
    (hg := isSection_restrictSection _) (t := fun j => negRestrict (O := O) (s j))
    (ht := fun j => isSection_negRestrict (s j)) t p
  have hrhs : IsSection (pullbackProj A.P (Subtype.val : O → A.Obj))
      (subRestrict (O := O) f (paramSec s t) hf) := isSection_restrictSection _
  suffices h : pbLin p ⟨_, hlhs⟩ = pbLin p ⟨_, hrhs p⟩ from
    congrArg Subtype.val (pbLin_injective p h)
  have hp : (p : A.Obj) ∈ O := p.2
  -- the left side
  have e1 : (⟨paramSlice (subRestrict (O := O) f (fiberZero A.P) hf)
      (isSection_restrictSection _) (fun j => negRestrict (O := O) (s j))
      (fun j => isSection_negRestrict (s j)) t p, hlhs⟩ :
        pullbackProj A.P (Subtype.val : O → A.Obj) ⁻¹' {p}) =
      ⟨subRestrict (O := O) f (fiberZero A.P) hf p, isSection_restrictSection _ p⟩ +
        ∑ j, t j • (⟨negRestrict (O := O) (s j) p, isSection_negRestrict (s j) p⟩ :
          pullbackProj A.P (Subtype.val : O → A.Obj) ⁻¹' {p}) := rfl
  -- values of the pieces in `W_p`
  have hsub : ∀ (h : A.Obj → A.W), (⟨subSec f h O p, isSection_subSec hf h O p⟩ :
      A.P ⁻¹' {(p : A.Obj)}) = ⟨f p, hf p⟩ + (-1 : ℝ) • ⟨extendZero O h p,
        isSection_extendZero O h p⟩ := fun h => by
    apply Subtype.ext
    change subSec f h O p = _
    unfold subSec
    rw [sectionAdd_apply hf (isSection_extendZero O h).sectionSmul]
    congr 2
    exact Subtype.ext (sectionSmul_apply (f := fun _ => (-1 : ℝ)) (isSection_extendZero O h) _)
  have hneg : ∀ j, (⟨Polyfold.sectionSmul A.P (fun _ => (-1 : ℝ)) (extendZero O (s j)) p,
      (isSection_extendZero O (s j)).sectionSmul p⟩ : A.P ⁻¹' {(p : A.Obj)}) =
      (-1 : ℝ) • ⟨s j p, hs j p⟩ := fun j => by
    apply Subtype.ext
    change Polyfold.sectionSmul A.P (fun _ => (-1 : ℝ)) (extendZero O (s j)) p = _
    rw [sectionSmul_apply (isSection_extendZero O (s j))]
    congr 2
    exact Subtype.ext (extendZero_eqOn (fun y _ => hs j y) hp).symm
  have hz0 : (⟨extendZero O (fiberZero A.P) p, isSection_extendZero O _ p⟩ :
      A.P ⁻¹' {(p : A.Obj)}) = 0 :=
    Subtype.ext (extendZero_eqOn (fun y _ => isSection_fiberZero y) hp).symm
  have hpar : (⟨extendZero O (paramSec s t) p, isSection_extendZero O _ p⟩ :
      A.P ⁻¹' {(p : A.Obj)}) = ∑ j, t j • ⟨s j p, hs j p⟩ := by
    rw [← paramFib hs t p]
    exact Subtype.ext (extendZero_eqOn (fun y _ => isSection_paramSec s t y) hp).symm
  rw [e1, map_add, map_sum]
  simp only [map_smul]
  change (⟨subSec f (fiberZero A.P) O p, _⟩ : A.P ⁻¹' {(p : A.Obj)}) +
      ∑ j, t j • (⟨Polyfold.sectionSmul A.P (fun _ => (-1 : ℝ)) (extendZero O (s j)) p, _⟩ :
        A.P ⁻¹' {(p : A.Obj)}) = ⟨subSec f (paramSec s t) O p, _⟩
  rw [hsub, hsub, hz0, hpar]
  simp only [hneg, smul_zero, add_zero, Finset.smul_sum, smul_smul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

end Branch


/-! ### The chart reading of (15.1) -/

/-- **The chart reading of `(f − s)'(x)`**: at a point `x ∈ X₁` with `f(x) = s(x)`, in a chart `c`
with domain in `O`, `Φ_x((f − s)'(x)α) = D((f̂ − ŝ) ∘ r)(z)(Tφ α)`. -/
theorem fiberLin_toIntr_subDeriv {f : A.Obj → A.W} (hf : A.B.IsScSmoothSection f)
    {s : A.Obj → A.W} {O : Set A.Obj} (hs : IsScPlusSectionOn A s O)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) (hsub : c.φ.source ⊆ O)
    {x : A.X.PObj.Level 1} (hx : A.X.PObj.levelVal 1 x ∈ c.φ.source)
    (hfs : f (A.X.PObj.levelVal 1 x) = s (A.X.PObj.levelVal 1 x))
    (α : A.X.PObj.tangentFiber x) :
    c.fiberLin hx (toIntr c hx (subDeriv c f s (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))) α) =
      subDeriv c f s (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))
        (tangentFiberEquiv c.isChart hx α : c.φ.model.E 0) := by
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
  rw [fiberLin_toIntr c hx hrange, chartOp_apply]

/-- The principal part of a section at `φ(x)` is the chart reading of its value at `x`. -/
theorem principal_eq_fiberLin {c : StrongBundleChart A.X.PObj A.P} {y : A.Obj}
    (hy : y ∈ c.φ.source) {s : A.Obj → A.W} (hs : A.P (s y) = y) :
    c.principal s (c.φ y) = c.fiberLin hy ⟨s y, hs⟩ := by
  unfold StrongBundleChart.principal
  rw [c.φ.symm_apply_apply hy]
  rfl

section Branch

variable {O : Set A.Obj} (hO : IsOpen O) [Nonempty O] [ParacompactSpace O]
  [ParacompactSpace (pullbackSpace A.P (Subtype.val : O → A.Obj))]

include hO in
/-- `ĉ(−s)|O = −ŝ` in a transported chart. -/
theorem principal_restrictTo_negRestrict {s : A.Obj → A.W} (hs : ∀ y ∈ O, A.P (s y) = y)
    {c : StrongBundleChart A.X.PObj A.P} (hsub : c.φ.source ⊆ O)
    (q₀ : pullbackSpace A.P (Subtype.val : O → A.Obj)) {w : c.φ.model.E 0}
    (hw : w ∈ c.φ.model.O) :
    (c.restrictTo A.B.continuous hO hsub q₀).principal (negRestrict (O := O) s) w =
      -c.principal s w := by
  unfold negRestrict
  rw [StrongBundleChart.principal_restrictTo hO A.B.continuous hsub q₀ _ hw,
    principal_sectionSmul_const c (isSection_extendZero O s) (-1) hw, neg_one_smul]
  congr 1
  unfold StrongBundleChart.principal
  rw [← extendZero_eqOn hs (hsub (c.φ.symm_mapsTo hw))]

set_option maxHeartbeats 1600000 in
-- the chart reading of (15.1) in the transported chart
include hO in
/-- **(15.1) for one branch gives Part I's properties (i)–(ii)**: let `c` be a chart of `W` with
domain in `O`, centred at a zero `x` of `f`, and suppose that `(v, τ) ↦ f'(x)v + Σ_j τ_j s_j(x)`
maps `T^R_xX × ℝ^ℓ` onto `W_x` (with `f'(x) = (f − 0)'(x)`, the operator of `T(f, Λ₀)(x)`).  Then
in the transported chart of `W|O`, `F(t, y) = (f − 0)|O + Σ_j t_j (−s_j)|O` has the properties
(i) (`F'(0, x)` onto) and (ii) (`ker F'(0, x)` transversal to `ℝ^ℓ ⊕ T^R_xX`) of Part I's proof
of Theorem 5.3.10 (`IsParamGP`). -/
theorem isParamGP_restrictTo_of_onto {f : A.Obj → A.W} (hft : A.B.IsScFredholmSectionTame f)
    {ℓ : ℕ} {s : Fin ℓ → A.Obj → A.W} (hs : ∀ j, IsScPlusSectionOn A (s j) O)
    (hsec : ∀ j, IsSection A.P (s j)) {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c)
    (hsub : c.φ.source ⊆ O) {x : A.X.PObj.Level 1} (hx : A.X.PObj.levelVal 1 x ∈ c.φ.source)
    (hφ0 : c.φ (A.X.PObj.levelVal 1 x) = 0)
    (hx0 : f (A.X.PObj.levelVal 1 x) = fiberZero A.P (A.X.PObj.levelVal 1 x)) {n : ℕ}
    {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hon : ∀ w : A.P ⁻¹' {A.X.PObj.levelVal 1 x}, ∃ v ∈ reducedTangentFiber c.isChart hx T,
      ∃ τ : Fin ℓ → ℝ, toIntr c hx (subDeriv c f (fiberZero A.P)
        (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))) v +
          ∑ j, τ j • (⟨s j (A.X.PObj.levelVal 1 x), hsec j _⟩ :
            A.P ⁻¹' {A.X.PObj.levelVal 1 x}) = w)
    (q₀ : pullbackSpace A.P (Subtype.val : O → A.Obj)) :
    (c.restrictTo A.B.continuous hO hsub q₀).IsParamGP
      (subRestrict (O := O) f (fiberZero A.P) hft.isScSmooth.1)
      (fun j => negRestrict (O := O) (s j)) T := by
  classical
  have hs0 : IsScPlusSectionOn A (fiberZero A.P) O := isScPlusSectionOn_fiberZero hO
  -- the level-`1` point over `φ(x)` is `0`
  have hz0 : levelLift c.φ 1 (A.X.PObj.levelVal 1 x) = 0 := by
    apply c.φ.model.E.toBase_injective 1
    rw [A.X.PObj.toBase_levelLift c.isChart hx (levelVal_mem x), hφ0, map_zero]
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O :=
    hφ0 ▸ c.φ.mapsTo_model (A.X.PObj.levelVal 1 x) hx
  have hzU : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ c.U := by
    rw [map_zero]; exact mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)
  -- the operator of `F` in `x`-direction and the `t`-columns
  have hlin : ∀ u : ↥(rangeS (scDeriv (c.restrictTo A.B.continuous hO hsub q₀).U
        (r (c.restrictTo A.B.continuous hO hsub q₀).R) 0)),
      linAt (c.restrictTo A.B.continuous hO hsub q₀).U (c.restrictTo A.B.continuous hO hsub q₀).R
        ((c.restrictTo A.B.continuous hO hsub q₀).principal
        (subRestrict (O := O) f (fiberZero A.P) hft.isScSmooth.1)) 0 u =
        subDeriv c f (fiberZero A.P) (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))
          u.1 := fun u => by
    have e := scDeriv_restrictTo_subRestrict hO hft hs0 hc hsub q₀ hzU
    rw [hz0]
    exact congrArg (fun L : c.φ.model.E 0 →L[ℝ] c.F 0 => L u.1) e
  have hcol : ∀ j,
      (c.restrictTo A.B.continuous hO hsub q₀).principal (negRestrict (O := O) (s j)) 0 =
      -c.fiberLin hx ⟨s j (A.X.PObj.levelVal 1 x), hsec j (A.X.PObj.levelVal 1 x)⟩ := fun j => by
    have e := principal_eq_fiberLin hx (hsec j (A.X.PObj.levelVal 1 x))
    rw [hφ0] at e
    exact (principal_restrictTo_negRestrict hO (hs j).1 hsub q₀ h0O).trans (by rw [e])
  -- the chart reading of (15.1)
  have hread : ∀ w : A.P ⁻¹' {A.X.PObj.levelVal 1 x},
      ∃ v ∈ reducedTangentFiber c.isChart hx T, ∃ τ : Fin ℓ → ℝ,
      subDeriv c f (fiberZero A.P) (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))
        (tangentFiberEquiv c.isChart hx v : c.φ.model.E 0) +
        ∑ j, τ j • c.fiberLin hx ⟨s j (A.X.PObj.levelVal 1 x),
          hsec j (A.X.PObj.levelVal 1 x)⟩ = c.fiberLin hx w := fun w => by
    obtain ⟨v, hv, τ, he⟩ := hon w
    refine ⟨v, hv, τ, ?_⟩
    have := congrArg (c.fiberLin hx) he
    rw [map_add, map_sum] at this
    simp only [map_smul] at this
    rwa [fiberLin_toIntr_subDeriv hft.isScSmooth hs0 hc hsub hx (hx0.trans rfl)] at this
  have hred : ∀ v ∈ reducedTangentFiber c.isChart hx T,
      (tangentFiberEquiv c.isChart hx v : c.φ.model.E 0) ∈ minimalSubspaceWith T 0 := by
    intro v hv
    have := hv
    rw [reducedTangentFiber, Submodule.mem_comap, fiberCoord_eq_coe, hφ0] at this
    exact this
  have hrng : ∀ v : A.X.PObj.tangentFiber x,
      (tangentFiberEquiv c.isChart hx v : c.φ.model.E 0) ∈ rangeS (scDeriv c.U (r c.R) 0) :=
    fun v => by
      have := (c.mem_tangentFiberModel_iff_rangeS hx _).1 (tangentFiberEquiv c.isChart hx v).2
      rw [hz0] at this
      exact this
  refine ⟨fun k hk => ?_, fun w => ?_⟩
  · -- (i)
    have hk' : (c.φ (A.X.PObj.levelVal 1 x), k) ∈ c.K := by rw [hφ0]; exact hk
    obtain ⟨w, rfl⟩ := c.mem_range_fiberLin hx hk'
    obtain ⟨v, -, τ, he⟩ := hread w
    refine ⟨⟨_, hrng v⟩, -τ, ?_⟩
    rw [hlin]
    refine Eq.trans ?_ he
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (congrArg (fun q : c.F 0 => (-τ) j • q) (hcol j)).trans (neg_smul_neg (τ j) _)
  · -- (ii)
    let w0 : c.φ.model.E 0 := (w : (c.restrictTo A.B.continuous hO hsub q₀).φ.model.E 0)
    have hwT : w0 ∈ tangentFiberModel c.isChart hx :=
      (c.mem_tangentFiberModel_iff_rangeS hx _).2 (by rw [hz0]; exact w.2)
    set α := (tangentFiberEquiv c.isChart hx).symm
      ⟨w0, hwT⟩ with hα
    have hαw : (tangentFiberEquiv c.isChart hx α : c.φ.model.E 0) = w0 := by
      rw [hα, Equiv.apply_symm_apply]
    obtain ⟨v, hv, τ, he⟩ :=
      hread (toIntr c hx (subDeriv c f (fiberZero A.P)
        (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))) α)
    rw [fiberLin_toIntr_subDeriv hft.isScSmooth hs0 hc hsub hx (hx0.trans rfl),
      hαw] at he
    refine ⟨⟨w0 - (tangentFiberEquiv c.isChart hx v : c.φ.model.E 0),
      Submodule.sub_mem (rangeS (scDeriv c.U (r c.R) 0)) w.2 (hrng v)⟩, τ, ?_, ?_⟩
    · rw [hlin]
      have hs1 : ∀ j, τ j • (c.restrictTo A.B.continuous hO hsub q₀).principal
          (negRestrict (O := O) (s j)) 0 =
          -(τ j • c.fiberLin hx ⟨s j (A.X.PObj.levelVal 1 x), hsec j (A.X.PObj.levelVal 1 x)⟩) :=
        fun j => (congrArg (fun q : c.F 0 => τ j • q) (hcol j)).trans (smul_neg _ _)
      rw [Finset.sum_congr rfl fun j _ => hs1 j]
      change subDeriv c f (fiberZero A.P) (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))
        (w0 - (tangentFiberEquiv c.isChart hx v : c.φ.model.E 0)) +
          ∑ j, -(τ j • c.fiberLin hx ⟨s j (A.X.PObj.levelVal 1 x),
            hsec j (A.X.PObj.levelVal 1 x)⟩) = 0
      rw [Finset.sum_neg_distrib, map_sub, ← he]
      abel
    · change w0 - (w0 - (tangentFiberEquiv c.isChart hx v : c.φ.model.E 0)) ∈ _
      rw [sub_sub_cancel]
      exact hred v hv

end Branch

end SBLocalization

end Polyfold
