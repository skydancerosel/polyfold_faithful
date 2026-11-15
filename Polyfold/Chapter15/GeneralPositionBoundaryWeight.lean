import Polyfold.Chapter15.CylinderEndWeights
import Polyfold.Chapter15.BranchKernelTangent
import Polyfold.Chapter15.GeneralPositionLocal
import Polyfold.Chapter15.TameBranched

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Corollary 15.3.10 (3)** (p. 700; 2017: Corollary 15.1), with Remark 9.2.14 and
Definition 15.3.5: in general position the boundary of `Θ = Λ ∘ f` has the weights of `Θ`.

# `∂Θ = Θ` on `∂X` in general position

## The text, paraphrased

In general position (Definition 15.3.5) every `(f − sᵢ)'(y)` with `f(y) = sᵢ(y)` is onto on
`T^R_yX`.  For `y ∈ ∂X` the tangent space `T_yMᵢ = ker (f − sᵢ)'(y)` of the sheet
`Mᵢ = {f = sᵢ}` is then not contained in `T^R_yX`, so `y ∈ ∂Mᵢ` (Remark 9.2.14) and
`∂Θ(y) = ∑_{y ∈ ∂Mᵢ} σᵢ = Θ(y)`.  On the cylinder this is "`Θ̃` restricts to `Θᵢ` on
`{i} × X`" for `∂Θ̃`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* **`exists_branch_mem_submanifoldBoundary`**: `X` tame, `(f, Λ)` in general position at
  `y ∈ ∂X`, `s` a branch through `f(y)` of a local representation of `Λ` on `O`: there is an
  open `V ∋ y` in `O` with `M = {f = s} ∩ V` a submanifold and `y ∈ ∂M`.  The kernel of
  `(f − s)'(y)` is `T_yM` (`exists_branch_tangent_eq_ker`), the operator is onto on `T^R`, and
  `T_zO ⊄ E_z` since `d_X(y) ≥ 1` (`degIndex_eq_quotDim_of_isTame`).
* **`boundaryTheta_eq_of_isInGeneralPositionAt`**: `∂Θ(y) = Θ(y)` at such a point.
* `hasFullBoundaryWeight_of_generalPosition`: `∂Θ = Θ` on `∂X ∩ supp Θ` if `(f, Λ)` is in
  general position at the points of `∂X ∩ supp Θ`.
* **`hasFullBoundaryWeight_cyl`**: for `d_X ≡ 0`, `Λ̃` an sc⁺-multisection on `[0, 1] × X` with
  `Λ̃ = Λⁱ` over `t = i` and the face condition of Theorem 15.3.9 for the glued data
  (`IsBoundaryFaceOnto`), `∂Θ̃ = Θ̃` on `∂([0, 1] × X) ∩ supp Θ̃`.
* **`boundaryTheta_cyl_zero`**, **`boundaryTheta_cyl_one`**: `∂Θ̃(i, x) = Θᵢ(x)`.
* **`bijective_cylEndProj_zero`**, **`bijective_cylEndProj_one`**: the end `i` of
  `|supp ∂Θ̃|` maps bijectively onto `|supp Θᵢ|`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}}

/-! ### One branch -/

set_option maxHeartbeats 1600000 in
-- the chart assembly: kernel, reduced tangent space and the fibre `K_z` in one chart
/-- **A sheet through a boundary point in general position has the point in its boundary**
(Remark 9.2.14 with Definition 15.3.5): `X` tame, the reduced linearization of `(f, Λ)` onto at
`y ∈ ∂X`, `(sᵢ, σᵢ)` a local representation of `Λ` on `O ∋ y` and `sᵢ(y) = f(y)`.  Then there is
an open `V ∋ y` in `O` such that `M = {y' ∈ V | f(y') = sᵢ(y')}` is a submanifold and
`y ∈ ∂M`. -/
theorem exists_branch_mem_submanifoldBoundary (hX : A.X.IsTame) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ : A.W → ℚ≥0} {x : A.X.PObj.Level 1} (hgp : IsReducedOntoAtLevel f Λ x)
    (hb : A.X.PObj.levelVal 1 x ∈ A.X.PObj.boundary) {O : Set A.Obj} (hO : IsOpen O) {k : ℕ}
    {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0} (hrep : IsLocalRepOn A Λ O s σ)
    (hxO : A.X.PObj.levelVal 1 x ∈ O) {i : Fin k}
    (hi : s i (A.X.PObj.levelVal 1 x) = f (A.X.PObj.levelVal 1 x)) :
    ∃ (V : Set A.Obj) (d : ℕ), IsOpen V ∧ A.X.PObj.levelVal 1 x ∈ V ∧ V ⊆ O ∧
      A.X.PObj.IsSubmanifoldOfDim {y ∈ V | f y = s i y} d ∧
      A.X.PObj.levelVal 1 x ∈ A.X.PObj.submanifoldBoundary {y ∈ V | f y = s i y} := by
  classical
  set y := A.X.PObj.levelVal 1 x with hy
  have : Nonempty O := ⟨⟨y, hxO⟩⟩
  have := A.X.PObj.paracompactSpace_subtype O
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : O → A.Obj))
    (A.X.PObj.restrictOpen hO) A.B
  have hs := hrep.2.1 i
  have hG := isGeneralPositionGerm_branch_at hf hft hgp hO hrep hxO hi
  have h0 : IsZeroAt (pullbackProj A.P (Subtype.val : O → A.Obj))
      (subRestrict (O := O) f (s i) hft.isScSmooth.1) ⟨y, hxO⟩ := by
    unfold subRestrict
    rw [isZeroAt_restrictSection_iff]
    exact (isZeroAt_subSec_iff hft.isScSmooth.1 hs.1 hxO).2 hi.symm
  have hgood := hG.isGoodPositionGermTame (isScFredholmSectionTame_subRestrict hO hft hs) h0
  obtain ⟨V, d, hVo, hxV, hVO, hdim, hall⟩ :=
    exists_branch_tangent_eq_ker hO hft hs hxO hi.symm hgood
  refine ⟨V, d, hVo, hxV, hVO, hdim, ?_⟩
  have hyM : y ∈ {y' ∈ V | f y' = s i y'} := ⟨hxV, hi.symm⟩
  rw [MPolyfold.mem_submanifoldBoundary_iff hdim.1]
  refine ⟨hyM, hb, fun hred => ?_⟩
  obtain ⟨hys, -, htan⟩ := hall y hxV hi.symm
  -- a chart of `W` around `y` with domain in `O`
  obtain ⟨c₀, hc₀, hxc₀⟩ := StrongBundle.exists_chart_mem A.B y
  have hso : IsOpen (c₀.φ.source ∩ O) := c₀.φ.isOpen_source.inter hO
  obtain ⟨c, hc, hcsrc⟩ : ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsChart c ∧
      c.φ.source = c₀.φ.source ∩ O :=
    ⟨_, (StrongBundle.isChart_of_mem A.B hc₀).restrict inter_subset_left hso, rfl⟩
  have hsub : c.φ.source ⊆ O := hcsrc ▸ inter_subset_right
  have hxc : y ∈ c.φ.source := hcsrc ▸ ⟨hxc₀, hxO⟩
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  have hy1 : y ∈ A.X.PObj.levelSet 1 := levelVal_mem x
  set z := levelLift c.φ 1 y with hzdef
  have hz : c.φ.model.E.toBase 1 z = c.φ y := A.X.PObj.toBase_levelLift c.isChart hxc hy1
  have hker := htan c hc hsub hxc z hz
  -- `ker ⊆ E_z` if `T_yM ⊆ T^R_yX`
  have hyV := hdim.1.mem_data_V hyM
  have hredc := hred.isReducedChart (hdim.1.data hyM) c.isChart T hT hyV hxc hz
  have himg := chartVec_image_submanifoldTangent c.isChart (hdim.1.data hyM) hyM hyV hxc
  have hkmin : kerSet c f (s i) z ⊆
      (minimalSubspaceWith T (c.φ.model.E.toBase 1 z) : Set (c.φ.model.E 0)) := by
    rw [← hker, himg]
    exact hredc
  -- `T_zO ⊄ E_z` at a boundary point of a tame `X`
  set R := c.isRetraction.baseRetraction c.relOpen with hR
  have hdeg := A.X.PObj.degIndex_eq_quotDim_of_isTame hX c.isChart R c.base_retract T hT hxc hys hz
  have hb1 : 1 ≤ A.X.PObj.degIndex y := hb
  obtain ⟨v, hvT, hvE⟩ : ∃ v ∈ LinearMap.range (scDeriv R.U R z :
      c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0), v ∉ minimalSubspaceWith T (c.φ.model.E.toBase 1 z) := by
    by_contra hcon
    push Not at hcon
    have htop : (reducedTangentSpaceWith R T z).comap
        (LinearMap.range (scDeriv R.U R z : c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0)).subtype = ⊤ :=
      eq_top_iff.2 fun a _ => ⟨a.2, hcon a.1 a.2⟩
    have h0q : quotDim (LinearMap.range (scDeriv R.U R z : c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0))
        (reducedTangentSpaceWith R T z) = 0 := by
      rw [quotDim, htop]
      have : Subsingleton (↥(LinearMap.range (scDeriv R.U R z :
          c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0)) ⧸ (⊤ : Submodule ℝ _)) :=
        ⟨fun a b => by
          obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
          obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
          exact (Submodule.Quotient.eq _).2 Submodule.mem_top⟩
      exact finrank_zero_of_subsingleton
    omega
  have hvT' : v ∈ rangeS (scDeriv c.U (r c.R) z) := hvT
  -- `L v ∈ K_z`, and a reduced preimage
  let p : ChartPoint A.B y := ⟨c, hc, hxc, z, hz⟩
  obtain ⟨h, hh⟩ := subDeriv_mem_K hft.isScSmooth hs p hsub hi.symm v
  have hk' : (c.φ.model.E.toBase 1 z, subDeriv c f (s i) z v) ∈ c.K := by
    refine ⟨(c.φ.model.E.toBase 1 z, h), ⟨p.mem_U, mem_univ _⟩, ?_⟩
    rw [StrongRetr.apply_eq c.isRetraction p.mem_U h]
    exact Prod.ext (StrongRetr.r_eq_self c.isRetraction p.mem_O) hh
  rw [hz] at hk'
  obtain ⟨w, hwR, hwT, hwk⟩ := exists_reduced_preimage_of_isGeneralPositionGerm hO hft hs hc hsub
    hxc hi.symm hG hz T hT hk'
  have hmem : v - w ∈ kerSet c f (s i) z :=
    ⟨Submodule.sub_mem _ hvT' hwT, by rw [map_sub, hwk, sub_self]⟩
  have hvw := hkmin hmem
  have hwE : w ∈ minimalSubspaceWith T (c.φ.model.E.toBase 1 z) := hwR.2
  refine hvE ?_
  have := Submodule.add_mem _ hvw hwE
  rwa [sub_add_cancel] at this

/-! ### All branches: `∂Θ(y) = Θ(y)` -/

set_option maxHeartbeats 800000 in
-- the local branching structure is assembled as in Theorem 15.2.5
/-- **`∂Θ(y) = Θ(y)` at a boundary point of general position** (Definition 9.2.16,
Remark 9.2.14, Definition 15.3.5): `X` tame, `Λ` an sc⁺-multisection, `y ∈ ∂X` with
`Λ(f(y)) > 0` and `(f, Λ)` in general position at `y`. -/
theorem boundaryTheta_eq_of_isInGeneralPositionAt (hX : A.X.IsTame) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) {x : A.Obj}
    (hb : x ∈ A.X.PObj.boundary) (hgp : IsInGeneralPositionAt f Λ x) :
    A.X.boundaryTheta (fun z => (Λ (f z) : ℚ)) x = (Λ (f x) : ℚ) := by
  classical
  obtain ⟨hx1, hred⟩ := hgp
  obtain ⟨O, k, s, σ, hO, hxO, hrep⟩ := hΛ.exists_isLocalRepOn x
  have hsec : IsSection A.P f := hf.1.1.1
  have hfc : Continuous f := continuousOn_univ.1 hft.isScSmooth.2.continuousOn
  have hV : ∀ i, ∃ V : Set A.Obj, IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧
      (s i x = f x → A.X.PObj.IsSmoothSubmanifold {y ∈ V | f y = s i y} ∧
        x ∈ A.X.PObj.submanifoldBoundary {y ∈ V | f y = s i y}) ∧
      (s i x ≠ f x → ∀ y ∈ V, f y ≠ s i y) := by
    intro i
    by_cases h : s i x = f x
    · obtain ⟨V, d, hVo, hxV, hVO, hdim, hbd⟩ :=
        exists_branch_mem_submanifoldBoundary hX hf hft (x := A.X.PObj.levelMk 1 x hx1) hred hb
          hO hrep hxO h
      exact ⟨V, hVo, hxV, hVO, fun _ => ⟨hdim.1, hbd⟩, fun h' => absurd h h'⟩
    · exact ⟨{y ∈ O | f y ≠ s i y}, isOpen_sep_ne hfc hO (hrep.2.1 i).continuousOn,
        ⟨hxO, fun e => h e.symm⟩, sep_subset _ _, fun h' => absurd h' h, fun _ y hy => hy.2⟩
  choose V hVo hxV hVO hVt hVn using hV
  set U : Set A.Obj := O ∩ ⋂ i, V i with hU
  have hUo : IsOpen U := hO.inter (isOpen_iInter_of_finite hVo)
  have hxU : x ∈ U := ⟨hxO, mem_iInter.2 hxV⟩
  have hRV : ∀ i, U ⊆ V i := fun i y hy => mem_iInter.1 hy.2 i
  have hRO : U ⊆ O := fun y hy => hy.1
  have hcount : ∀ z ∈ U, Λ (f z) = ∑ i with f z = s i z, σ i := fun z hz => by
    have h := hrep.2.2.2 (f z) (by rw [hsec z]; exact hRO hz)
    rw [hsec z] at h
    rw [h, Finset.sum_filter]
  have hI : ∀ i, ∀ z ∈ U, f z = s i z → s i x = f x := fun i z hz hfz => by
    by_contra h
    exact hVn i h z (hRV i hz) hfz
  have eM : ∀ i, {z ∈ U | f z = s i z} = {z ∈ V i | f z = s i z} ∩ U := fun i => by
    ext z
    constructor
    · rintro ⟨hz, he⟩; exact ⟨⟨hRV i hz, he⟩, hz⟩
    · rintro ⟨⟨-, he⟩, hz⟩; exact ⟨hz, he⟩
  have hS : ∀ j : ULift.{u} {i : Fin k // s i x = f x},
      A.X.PObj.IsSmoothSubmanifold {z ∈ U | f z = s j.down.1 z} := fun j => by
    rw [eM]; exact (hVt j.down.1 j.down.2).1.inter_isOpen hUo
  have hP : ∀ j : ULift.{u} {i : Fin k // s i x = f x},
      IsProperMap (inclusion (sep_subset U fun z => f z = s j.down.1 z)) := fun j => by
    rw [isProperMap_inclusion_iff]
    have hcs : ContinuousOn (s j.down.1) U := (hrep.2.1 j.down.1).continuousOn.mono hRO
    have h1 : Continuous fun p : U => f p := hfc.comp continuous_subtype_val
    have h2 : Continuous fun p : U => s j.down.1 p :=
      hcs.comp_continuous continuous_subtype_val fun p => p.2
    convert isClosed_eq h1 h2 using 1
    ext p
    simp
  let B : A.X.LocalBranchingStructure (fun z => (Λ (f z) : ℚ)) x :=
    EpGroupoid.LocalBranchingStructure.mk U hUo hxU
      (ULift.{u} {i : Fin k // s i x = f x}) (fun j => {z ∈ U | f z = s j.down.1 z})
      (fun j => sep_subset _ _) hS (fun j => ⟨hxU, j.down.2.symm⟩) hP
      (fun j => (σ j.down.1 : ℚ)) (fun j => by exact_mod_cast hrep.1 j.down.1) (by
        intro z hz
        have e0 : ((Λ (f z) : ℚ≥0) : ℚ) = ∑ i, if f z = s i z then (σ i : ℚ) else 0 := by
          rw [hcount z hz, Finset.sum_filter]
          refine (map_sum NNRat.coeHom _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
          split_ifs <;> rfl
        have e1 : (∑ i, if f z = s i z then (σ i : ℚ) else 0) =
            ∑ i with s i x = f x, (if f z = s i z then (σ i : ℚ) else 0) :=
          (Finset.sum_filter_of_ne fun i _ hne => hI i z hz (by
            by_contra h
            exact hne (if_neg h))).symm
        have e2 : (∑ i with s i x = f x, (if f z = s i z then (σ i : ℚ) else 0)) =
            ∑ a : {i // s i x = f x}, (if f z = s a.1 z then (σ a.1 : ℚ) else 0) :=
          Finset.sum_subtype _ (fun i => by simp) _
        have e3 : (∑ a : {i // s i x = f x}, (if f z = s a.1 z then (σ a.1 : ℚ) else 0)) =
            ∑ j : ULift.{u} {i // s i x = f x},
              (if f z = s j.down.1 z then (σ j.down.1 : ℚ) else 0) :=
          (Fintype.sum_equiv Equiv.ulift _ _ fun _ => rfl).symm
        refine e0.trans (e1.trans (e2.trans (e3.trans ?_)))
        simp only [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs with h1 h2 h2 <;> first | rfl | exact absurd ⟨hz, h1⟩ h2 | exact absurd h2.2 h1)
  refine (EpGroupoid.boundaryTheta_eq_self_iff B hxU).2 fun j _ => ?_
  change x ∈ A.X.PObj.submanifoldBoundary {z ∈ U | f z = s j.down.1 z}
  rw [eM]
  exact (MPolyfold.mem_submanifoldBoundary_inter_isOpen_iff (hVt j.down.1 j.down.2).1 hUo
    hxU).2 (hVt j.down.1 j.down.2).2

/-- **`∂Θ = Θ` on `∂X ∩ supp Θ` in general position on the boundary**: `X` tame, `Λ` an
sc⁺-multisection, `(f, Λ)` in general position at the points of `∂X ∩ supp(Λ ∘ f)`. -/
theorem hasFullBoundaryWeight_of_generalPosition (hX : A.X.IsTame) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (hgp : ∀ y ∈ A.X.PObj.boundary, 0 < Λ (f y) → IsInGeneralPositionAt f Λ y) :
    A.X.HasFullBoundaryWeight (fun z => (Λ (f z) : ℚ)) := fun y hy =>
  boundaryTheta_eq_of_isInGeneralPositionAt hX hf hft hΛ hy.1
    (hgp y hy.1 (by exact_mod_cast hy.2))

/-- The face condition of Theorem 15.3.9 gives general position at the boundary points of the
support, for every sc⁺-multisection that agrees with the boundary data over `∂X`. -/
theorem isInGeneralPositionAt_of_isBoundaryFaceOnto {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ₀ Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (hbd : ∀ w, A.P w ∈ A.X.PObj.boundary → Λ w = Λ₀ w) (honto : IsBoundaryFaceOnto f Λ₀)
    {y : A.Obj} (hy : y ∈ A.X.PObj.boundary) (hpos : 0 < Λ (f y)) :
    IsInGeneralPositionAt f Λ y := by
  have hy1 := mem_levelSet_one_of_pos hf hΛ hpos
  have hPy : A.P (f y) ∈ A.X.PObj.boundary := by rw [hf.1.1.1 y]; exact hy
  refine ⟨hy1, honto Λ hΛ hbd (A.X.PObj.levelMk 1 y hy1) hy (mem_smoothSet_of_pos hft hΛ hpos) ?_⟩
  change 0 < Λ₀ (f y)
  rw [← hbd _ hPy]
  exact hpos

/-! ### The cylinder -/

/-- **`∂Θ̃ = Θ̃` on `∂([0, 1] × X) ∩ supp Θ̃`** (proof of Corollary 15.3.10 (3), p. 700): for
`d_X ≡ 0`, `f` sc-Fredholm with tame germ data, `Λ̃` an sc⁺-multisection on `[0, 1] × X` with
`Λ̃ = Λⁱ` over `t = i`, and the face condition of Theorem 15.3.9 for the glued data. -/
theorem hasFullBoundaryWeight_cyl (hd : ∀ x, A.X.PObj.degIndex x = 0) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ')
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁)) :
    (A.cubeSEP 1).X.HasFullBoundaryWeight
      (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) := by
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
  exact hasFullBoundaryWeight_of_generalPosition hXC hfC hftC hΛ' fun y hy hpos =>
    isInGeneralPositionAt_of_isBoundaryFaceOnto hfC hftC hΛ' hbd honto hy hpos

/-- **`∂Θ̃(0, x) = Θ₀(x)`** (proof of Corollary 15.3.10 (3), p. 700: `Θ̃` restricts to `Θ₀` on
`{0} × X`, on the level of `∂Θ̃`). -/
theorem boundaryTheta_cyl_zero (hd : ∀ x, A.X.PObj.degIndex x = 0) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ')
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁))
    {z : (A.cubeSEP 1).Obj} (hz : (z.1 0 : ℝ) = 0) :
    (A.cubeSEP 1).X.boundaryTheta (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) z =
      (Λ₀ (f z.2) : ℚ) :=
  boundaryTheta_cyl_eq hf.1.1.1 h0 (hasFullBoundaryWeight_cyl hd hf hft hΛ' h0 h1 honto) hz
    ((mem_boundary_cubeSEP_iff (A.X.isTame_of_degIndex_eq_zero hd) hd z).2 (Or.inl hz))

/-- **`∂Θ̃(1, x) = Θ₁(x)`**. -/
theorem boundaryTheta_cyl_one (hd : ∀ x, A.X.PObj.degIndex x = 0) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ')
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁))
    {z : (A.cubeSEP 1).Obj} (hz : (z.1 0 : ℝ) = 1) :
    (A.cubeSEP 1).X.boundaryTheta (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) z =
      (Λ₁ (f z.2) : ℚ) :=
  boundaryTheta_cyl_eq hf.1.1.1 h1 (hasFullBoundaryWeight_cyl hd hf hft hΛ' h0 h1 honto) hz
    ((mem_boundary_cubeSEP_iff (A.X.isTame_of_degIndex_eq_zero hd) hd z).2 (Or.inr hz))

/-- **The end `0` of `|supp ∂Θ̃|` is `|supp Θ₀|`**: `|(0, x)| ↦ |x|` is a continuous bijection
of the end `0` onto `|supp Θ₀|` (`∂Θ̃ = Θ₀` on the end). -/
theorem bijective_cylEndProj_zero (hd : ∀ x, A.X.PObj.degIndex x = 0) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ')
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁)) :
    Bijective (cylEndProj (fun p => cylEndMap_mem_orbitSupp_zero hd hf.1.1.1 h0 h1 p)) :=
  bijective_cylEndProj (i := 0) hf.1.1.1 h0 (hasFullBoundaryWeight_cyl hd hf hft hΛ' h0 h1 honto)
    (fun z hz => (mem_boundary_cubeSEP_iff (A.X.isTame_of_degIndex_eq_zero hd) hd z).2
      (Or.inl hz)) _

/-- **The end `1` of `|supp ∂Θ̃|` is `|supp Θ₁|`**. -/
theorem bijective_cylEndProj_one (hd : ∀ x, A.X.PObj.degIndex x = 0) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ')
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁)) :
    Bijective (cylEndProj (fun p => cylEndMap_mem_orbitSupp_one hd hf.1.1.1 h0 h1 p)) :=
  bijective_cylEndProj (i := 1) hf.1.1.1 h1 (hasFullBoundaryWeight_cyl hd hf hft hΛ' h0 h1 honto)
    (fun z hz => (mem_boundary_cubeSEP_iff (A.X.isTame_of_degIndex_eq_zero hd) hd z).2
      (Or.inr hz)) _

end SBLocalization

end Polyfold
