import Polyfold.Chapter3.NonVacuity
import Polyfold.Chapter3.TameVacuity

/-!
# A non-vacuity witness with boundary: the trivial bundle over a half-space

The second non-vacuity witness for the §3.6 implicit function theorems (after `NonVacuity.lean`),
now over an M-polyfold **with boundary**, so that good position at a boundary point (Definition
3.53 (2), the case `d_X(x) ≥ 1`) is exercised: the base is the half-space
`H = [0, ∞) × ℝᵐ` (the partial quadrant `quadrant 1 ℝᵐ` of `ℝ ⊕ ℝᵐ`, as the M-polyfold of a
relatively open subset of a partial quadrant), the bundle is `H × ℝᵏ → H`, and the section is
`x ↦ (x, φ(x))` for a `C^∞` map `φ : ℝ × ℝᵐ → ℝᵏ`.  If at every zero `x` of `φ` in `H` the
derivative `Dφ(x)` is onto, and at a zero on the boundary `{x₁ = 0}` the kernel `ker Dφ(x)` is
not contained in the boundary hyperplane (`φ|∂H` is also regular there), then the section meets
every hypothesis of Theorem 3.6.11 (preprint 3.57), and its conclusion is the regular value theorem for manifolds
with boundary (`theorem_3_6_11_halfSpace`).  The instance `φ(a, y) = y` on `[0, ∞) × ℝ`, with
solution set the half-line `[0, ∞) × {0}`, is `theorem_3_6_11_halfSpace_example`.

Not in the text (Findings, Chapter 3 item 201).  The charts centred at the points of `H` are the
re-centred charts of `Chapter4/Recentre.lean` (`StrongBundleChart.recentre`): at a boundary point
the partial quadrant stays `H`, at an interior point it becomes all of `ℝ ⊕ ℝᵐ`.

## What is formalized

* `StrongBundleChart.compatible_self`: every strong bundle chart is compatible with itself
  (general).
* `scDeriv_eq_of_hasFDerivAt`: on a relatively open subset of a partial quadrant, the
  sc-derivative at a level-`1` point of an sc¹ map which is differentiable in the classical sense
  is the classical derivative (general).
* `isInGoodPositionIn_halfSpace`: a subspace `N` of `ℝ ⊕ ℝᵐ` not contained in the boundary
  hyperplane `{v₁ = 0}` is in good position to `[0, ∞) ⊕ ℝᵐ` (a complement of `N ∩ {v₁ = 0}` in
  `{v₁ = 0}` is a good complement).
* `HalfSpaceBundle.bundle m k`, `HalfSpaceBundle.graphSection φ`, the germ data in the re-centred
  charts (`isScFredholmGermTame_graphSection_wholeChart`), good position at the regular zeros
  (`isGoodPositionGermTame_graphSection_wholeChart`), `theorem_3_6_11_halfSpace` and the example.

The half-space chart example (`HalfSpaceBundle.chartAt`, `HalfSpaceBundle.C_chartAt`,
`HalfSpaceBundle.r_chartAt`, `HalfSpaceBundle.scDeriv_loc`, …): `Chapter4/NonVacuityHalfSpace.lean`.
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

/-! ### General lemmas -/

section General

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- **A strong bundle chart is compatible with itself**: its transition map is the identity on the
overlap `K` (and on `K[1]`). -/
theorem StrongBundleChart.compatible_self (c : StrongBundleChart PX P) : c.Compatible c := by
  have htr : ∀ p ∈ c.overlap c, c.transition c p = p := by
    rintro _ ⟨y, hy, rfl⟩
    change c.toPartialEquiv (c.toPartialEquiv.symm (c.toPartialEquiv y)) = c.toPartialEquiv y
    rw [c.toPartialEquiv.left_inv hy.1]
  have h0 : IsScSmoothRetractMap (c.φ.model.E.prod c.F) (c.φ.model.C ×ˢ univ) (c.overlap c)
      (c.φ.model.E.prod c.F) (c.φ.model.C ×ˢ univ) (c.overlap c) (c.transition c) :=
    (isScSmoothRetractMap_id _).congr fun p hp => (htr p hp).symm
  have hsf : ∀ p ∈ strongShiftOne (c.overlap c), shiftFiber (c.transition c) p = p := by
    intro p hp
    change ((c.transition c (p.1, c.F.toBase 1 p.2)).1,
      invFun (c.F.toBase 1) (c.transition c (p.1, c.F.toBase 1 p.2)).2) = p
    rw [htr _ hp, leftInverse_invFun (c.F.toBase_injective 1)]
  have h1 : IsScSmoothRetractMap (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ)
      (strongShiftOne (c.overlap c)) (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ)
      (strongShiftOne (c.overlap c)) (shiftFiber (c.transition c)) :=
    (isScSmoothRetractMap_id _).congr fun p hp => (hsf p hp).symm
  have hr : ∀ x ∈ c.overlap c, x.2 ∈ range (c.F.toBase 1) →
      (c.transition c x).2 ∈ range (c.F.toBase 1) := fun x hx h => by rwa [htr x hx]
  exact ⟨h0, h0, h1, h1, hr, hr⟩

end General

section Deriv

variable {E F : ScBanach}

/-- **The sc-derivative is the classical derivative** where the latter exists: on a relatively open
`U` in a partial quadrant, if `f` is sc¹ and `HasFDerivAt f D (ι z)` at a point `z ∈ U₁`, then
`Df(z) = D` (uniqueness of the derivative within `U₁`, `ι : E₁ → E₀` having dense range). -/
theorem scDeriv_eq_of_hasFDerivAt {C U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U)
    {f : E 0 → F 0} (hf : IsSc1 U f) {z : E 1} (hz : z ∈ E.lvlSet U 1) {D : E 0 →L[ℝ] F 0}
    (hD : HasFDerivAt f D (E.toBase 1 z)) : scDeriv U f z = D :=
  ContinuousLinearMap.ext_of_comp_toBase_one (E := E)
    ((hU.isScDomain.uniqueDiffWithinAt 1 z hz).eq
      (hf.isSc1With_scDeriv.hasFDerivWithinAt z hz)
      (hD.comp_hasFDerivWithinAt z (E.toBase 1).hasFDerivAt.hasFDerivWithinAt))

/-- `scDeriv_eq_of_hasFDerivAt` at the point `0`. -/
theorem scDeriv_zero_eq_of_hasFDerivAt {C U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U)
    {f : E 0 → F 0} (hf : IsSc1 U f) (h0 : (0 : E 0) ∈ U) {D : E 0 →L[ℝ] F 0}
    (hD : HasFDerivAt f D 0) : scDeriv U f 0 = D := by
  refine scDeriv_eq_of_hasFDerivAt hU hf (by rw [ScBanach.mem_lvlSet, map_zero]; exact h0) ?_
  rw [map_zero]; exact hD

end Deriv

/-! ### Good position to a half-space -/

section HalfSpace

variable {m : ℕ}

/-- The sc-Banach space `ℝ ⊕ ℝᵐ` (constant structure) with the half-space `[0, ∞) ⊕ ℝᵐ`. -/
abbrev halfSpaceSc (m : ℕ) : ScBanach := halfLineSc (rnSc m)

lemma mem_quadrant_one_iff {p : (halfSpaceSc m) 0} : p ∈ quadrant 1 (rnSc m) 0 ↔ 0 ≤ p.1 0 :=
  Fin.forall_fin_one

/-- **A subspace not contained in the boundary hyperplane is in good position to the half-space**
(Definition 3.1.24 (preprint 3.21)): `N ∩ H` has interior in `N` (it contains `v` with `v₁ > 0`), and a complement
`P` of `N ∩ {v₁ = 0}` inside the hyperplane `{v₁ = 0}` is a complement of `N` with
`x + p ∈ H ↔ x ∈ H` for every `p ∈ P`. -/
theorem isInGoodPositionIn_halfSpace (N : Submodule ℝ ((halfSpaceSc m) 0))
    (hN : ∃ v ∈ N, v.1 0 ≠ 0) : IsInGoodPositionIn (halfSpaceSc m) ⊤ (quadrant 1 (rnSc m) 0) N := by
  obtain ⟨v, hvN, hv0⟩ := hN
  -- the coordinate `ℓ(p) = p₁` and the hyperplane `B = ker ℓ`
  let ℓ : (halfSpaceSc m) 0 →ₗ[ℝ] ℝ := (LinearMap.proj 0).comp (LinearMap.fst ℝ _ _)
  have hℓ : ∀ p, ℓ p = p.1 0 := fun _ => rfl
  let B := LinearMap.ker ℓ
  obtain ⟨P', hP'⟩ := Submodule.exists_isCompl (N.comap B.subtype)
  refine ⟨le_top, ?_, P'.map B.subtype, le_top, ?_, ?_, 1, one_pos, fun x _ p hp _ => ?_⟩
  · -- a point of `N` with `v₁ > 0` is interior to `N ∩ H` in `N`
    let w : (halfSpaceSc m) 0 := if 0 < v.1 0 then v else -v
    have hwN : w ∈ N := by
      by_cases h : 0 < v.1 0
      · simp only [w, if_pos h]; exact hvN
      · simp only [w, if_neg h]; exact N.neg_mem hvN
    have hw0 : 0 < w.1 0 := by
      by_cases h : 0 < v.1 0
      · simp only [w, if_pos h]; exact h
      · simp only [w, if_neg h]
        change 0 < -(v.1 0)
        exact neg_pos.2 (lt_of_le_of_ne (not_lt.1 h) hv0)
    have hopen : IsOpen {x : N | 0 < (x : (halfSpaceSc m) 0).1 0} :=
      isOpen_lt continuous_const ((continuous_apply 0).comp (continuous_fst.comp
        continuous_subtype_val))
    refine ⟨⟨w, hwN⟩, interior_mono (fun x hx => ?_) (by rw [hopen.interior_eq]; exact hw0)⟩
    exact mem_quadrant_one_iff.2 (le_of_lt hx)
  · -- `N ∩ P = 0`
    rw [eq_bot_iff]
    rintro x ⟨hxN, ⟨b, hbP, rfl⟩⟩
    have hb : b ∈ N.comap B.subtype ⊓ P' := ⟨hxN, hbP⟩
    rw [hP'.inf_eq_bot, Submodule.mem_bot] at hb
    rw [Submodule.mem_bot, hb]; rfl
  · -- `N + P = E`: `y = t v + (y − t v)` with `y − t v ∈ B = (N ∩ B) ⊕ P'`
    refine eq_top_iff.2 fun y _ => ?_
    set t := y.1 0 / v.1 0
    have hb : y - t • v ∈ B := by
      rw [LinearMap.mem_ker, map_sub, map_smul, hℓ, hℓ, smul_eq_mul]
      simp only [t]
      rw [div_mul_cancel₀ _ hv0, sub_self]
    obtain ⟨b₁, hb₁, b₂, hb₂, hb12⟩ :=
      Submodule.mem_sup.1 (hP'.sup_eq_top ▸ Submodule.mem_top (x := (⟨y - t • v, hb⟩ : B)))
    have hy : y = (t • v + (b₁ : (halfSpaceSc m) 0)) + (b₂ : (halfSpaceSc m) 0) := by
      have := congrArg Subtype.val hb12
      simp only [Submodule.coe_add] at this
      rw [add_assoc, this]; abel
    rw [hy]
    exact Submodule.add_mem_sup (N.add_mem (N.smul_mem t hvN) hb₁) ⟨b₂, hb₂, rfl⟩
  · -- `p ∈ B` does not change the first coordinate
    obtain ⟨b, -, rfl⟩ := hp
    have hb0 : (b : (halfSpaceSc m) 0).1 0 = 0 := b.2
    rw [mem_quadrant_one_iff, mem_quadrant_one_iff]
    change 0 ≤ x.1 0 ↔ 0 ≤ x.1 0 + (b : (halfSpaceSc m) 0).1 0
    rw [hb0, add_zero]

end HalfSpace

/-! ### The trivial bundle over the half-space -/

namespace HalfSpaceBundle

variable (m k : ℕ)

/-- The half-space `H = [0, ∞) × ℝᵐ ⊆ ℝ ⊕ ℝᵐ`. -/
abbrev H : Set ((halfSpaceSc m) 0) := quadrant 1 (rnSc m) 0

lemma relOpen_H : IsRelOpenInQuadrant (halfSpaceSc m) (H m) (H m) :=
  isRelOpenInQuadrant_quadrant_one (rnSc m)

lemma H_nonempty : (H m).Nonempty := ⟨0, fun _ => le_rfl⟩

/-- **The half-space as an M-polyfold** (one chart, the inclusion). -/
def basePoly : MPolyfold (H m) := (relOpen_H m).toMPolyfold (H_nonempty m)

/-- The chart of `basePoly`: the inclusion `H → ℝ ⊕ ℝᵐ`. -/
abbrev baseChart : MChart (H m) := (LocalModel.ofRelOpen (relOpen_H m)).selfChart (H_nonempty m)

/-- The projection `H × ℝᵏ → H`. -/
def proj : H m × (Fin k → ℝ) → H m := Prod.fst

variable {m k}

@[simp] lemma proj_apply (y : H m × (Fin k → ℝ)) : proj m k y = y.1 := rfl

lemma bijective_toBase_E (j : ℕ) : Bijective ((halfSpaceSc m).toBase j) :=
  bijective_toBase_prod (bijective_toBase_const _) (bijective_toBase_const _) j

lemma mem_smooth (e : (halfSpaceSc m) 0) : e ∈ (halfSpaceSc m).smooth :=
  (halfSpaceSc m).mem_smooth_iff.2 fun j => (bijective_toBase_E j).2 e

lemma baseChart_symm_val {z : (halfSpaceSc m) 0} (hz : z ∈ H m) :
    (((baseChart m).symm z : H m) : (halfSpaceSc m) 0) = z := by
  exact (baseChart m).toPartialEquiv.right_inv hz

/-- The fibre `proj⁻¹(x) ≃ ℝᵏ`. -/
def fibEquiv (x : H m) : proj m k ⁻¹' {x} ≃ (Fin k → ℝ) where
  toFun y := y.1.2
  invFun v := ⟨(x, v), rfl⟩
  left_inv := by
    rintro ⟨⟨a, b⟩, h⟩
    simp only [mem_preimage, proj_apply, mem_singleton_iff] at h
    subst h; rfl
  right_inv _ := rfl

instance (x : H m) : AddCommGroup (proj m k ⁻¹' {x}) := (fibEquiv x).addCommGroup

instance (x : H m) : Module ℝ (proj m k ⁻¹' {x}) := (fibEquiv x).module ℝ

lemma isStrongBundleRetraction_id_H :
    IsStrongBundleRetraction (E := halfSpaceSc m) (F := rnSc k) (H m) id where
  mapsTo := mapsTo_id _
  fst_independent _ _ _ _ := rfl
  fiber_linear _ _ := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  preserves_filtration _ _ _ _ _ hu _ hh := ⟨hu, hh⟩
  isScSmooth_zero := isScSmooth_id ((relOpen_H m).prod_univ (rnSc k)).isScDomain
  isScSmooth_one := by
    refine (isScSmooth_id ((relOpen_H m).prod_univ (rnSc k).shift).isScDomain).congr
      ((relOpen_H m).prod_univ (rnSc k).shift).isScDomain fun p _ => ?_
    change p = (p.1, invFun ((rnSc k).toBase 1) ((rnSc k).toBase 1 p.2))
    rw [leftInverse_invFun ((rnSc k).toBase_injective 1)]
  idem _ _ := rfl

/-- **The strong bundle chart** `H × ℝᵏ → H ◁ ℝᵏ`, `(x, v) ↦ (x, v)`, with the identity strong
bundle retraction. -/
def chart₀ : StrongBundleChart (basePoly m) (proj m k) where
  φ := baseChart m
  isChart := (basePoly m).isChart_of_mem (mem_singleton _)
  F := rnSc k
  U := H m
  R := id
  relOpen := relOpen_H m
  isRetraction := isStrongBundleRetraction_id_H
  base_retract := image_id _
  toPartialEquiv := (baseChart m).toPartialEquiv.prod (PartialEquiv.refl (Fin k → ℝ))
  source_eq := by
    change (univ : Set (H m)) ×ˢ (univ : Set (Fin k → ℝ)) = proj m k ⁻¹' univ
    rw [univ_prod_univ, preimage_univ]
  target_eq := by
    change H m ×ˢ (univ : Set (Fin k → ℝ)) = id '' (H m ×ˢ univ)
    rw [image_id]
  continuousOn_toFun := (baseChart m).continuousOn_toFun.prodMap continuousOn_id
  continuousOn_invFun := (baseChart m).continuousOn_invFun.prodMap continuousOn_id
  covers _ _ := rfl
  fiber_linear x _ := ((fibEquiv x).linearEquiv ℝ).toLinearMap.isLinear

@[simp] lemma chart₀_apply (y : H m × (Fin k → ℝ)) :
    chart₀ y = (((y.1 : H m) : (halfSpaceSc m) 0), y.2) := rfl

variable (m k) in
/-- **The trivial strong bundle** `H × ℝᵏ → H` over the half-space. -/
def bundle : StrongBundle (basePoly m) (proj m k) where
  continuous := continuous_fst
  surjective x := ⟨(x, 0), rfl⟩
  banachable x := ⟨Fin k → ℝ, inferInstance, inferInstance, inferInstance,
    ⟨{ toLinearEquiv := (fibEquiv x).linearEquiv ℝ
       continuous_toFun := continuous_snd.comp continuous_subtype_val
       continuous_invFun :=
        (continuous_const.prodMk continuous_id).subtype_mk fun _ => rfl }⟩⟩
  atlas :=
    { charts := {chart₀}
      compatible := by
        rintro _ h _ h'
        rw [mem_singleton_iff.1 h, mem_singleton_iff.1 h']
        exact chart₀.compatible_self
      cover := fun y => ⟨chart₀, mem_singleton _, mem_univ y, mem_univ _⟩ }

lemma isChart_chart₀ : (bundle m k).IsChart chart₀ :=
  StrongBundle.isChart_of_mem (B := bundle m k) (mem_singleton _)

lemma levelSet_eq_univ (j : ℕ) : (basePoly m).levelSet j = univ :=
  eq_univ_of_forall fun x => ((basePoly m).mem_levelSet_iff
    ((basePoly m).isChart_of_mem (mem_singleton _)) (mem_univ x)).2
      ((bijective_toBase_E (m := m) j).2 _)

lemma smoothSet_eq_univ : (basePoly m).smoothSet = univ :=
  eq_univ_of_forall fun x => mem_iInter.2 fun j => by rw [levelSet_eq_univ]; exact mem_univ x

/-! ### The re-centred charts -/

/-- `C = T⁻¹(quadrant)` for the trivial presentation `T = 1`. -/
lemma hT₀ : (chart₀ (m := m) (k := k)).φ.model.C =
    (ScIso.refl (halfSpaceSc m)) 0 ⁻¹' quadrant 1 (rnSc m) 0 := by
  ext; rfl

/-! ### Conjugation to a basic germ over a partial quadrant of `ℝ ⊕ ℝᵐ` -/

/-- `ℝ ⊕ ℝᵐ` as one finite-dimensional space (the `P` of the basic germs below). -/
abbrev Pm (m : ℕ) : Type := (Fin 1 → ℝ) × (Fin m → ℝ)

/-- **A `C^∞` map `κ` with `κ(0) = 0` on a relatively open `U ∋ 0` of a partial quadrant `C̃` of
`ℝ ⊕ ℝᵐ` is conjugated to a basic germ** (as `isConjugateToBasicGerm_of_contDiff`, with
`P = ℝ ⊕ ℝᵐ`, the partial quadrant `C̃`, `W = 0`, `h(a, w) = (κ(a), w)`, `B = 0`). -/
theorem isConjugateToBasicGerm_halfSpace {Ct U : Set ((halfSpaceSc m) 0)}
    (hCt : IsPartialQuadrant (ScBanach.const (Pm m)) Ct)
    (hU : IsRelOpenInQuadrant (halfSpaceSc m) Ct U) (h0 : (0 : (halfSpaceSc m) 0) ∈ U)
    {κ : Pm m → (Fin k → ℝ)} (hκ : ContDiff ℝ ∞ κ) (hκ0 : κ 0 = 0) :
    IsConjugateToBasicGerm (E := halfSpaceSc m) (F := rnSc k) U κ := by
  obtain ⟨O, hO, hUO⟩ := hU.2
  have hCt' : IsPartialQuadrant (ScBanach.paramProd (Pm m) TrivialBundle.zeroSc) (Ct ×ˢ univ) :=
    hCt.prod_univ TrivialBundle.zeroSc
  have hO' : ∃ O' : Set ((ScBanach.paramProd (Pm m) TrivialBundle.zeroSc) 0), IsOpen O' ∧
      U ×ˢ (univ : Set (Fin 0 → ℝ)) = O' ∩ Ct ×ˢ univ :=
    ⟨O ×ˢ univ, hO.prod isOpen_univ, by rw [hUO, prod_inter_prod, inter_univ]⟩
  have hU' : IsRelOpenInQuadrant (ScBanach.paramProd (Pm m) TrivialBundle.zeroSc) (Ct ×ˢ univ)
      (U ×ˢ (univ : Set (Fin 0 → ℝ))) := ⟨hCt', hO'⟩
  have h0' : (0 : (ScBanach.paramProd (Pm m) TrivialBundle.zeroSc) 0) ∈ U ×ˢ (univ : Set (Fin 0 → ℝ)) :=
    ⟨h0, mem_univ _⟩
  have hbE : ∀ j, Bijective (((halfSpaceSc m).prod (rnSc k)).toBase j) :=
    bijective_toBase_prod bijective_toBase_E (bijective_toBase_const _)
  have hbE1 : ∀ j, Bijective (((halfSpaceSc m).prod (rnSc k).shift).toBase j) :=
    bijective_toBase_prod bijective_toBase_E (bijective_toBase_shift (bijective_toBase_const _))
  have hbP : ∀ j, Bijective ((ScBanach.paramProd (Pm m) TrivialBundle.zeroSc).toBase j) :=
    TrivialBundle.bijective_toBase_param _
  have hbE' : ∀ j, Bijective (((ScBanach.paramProd (Pm m) TrivialBundle.zeroSc).prod
      (ScBanach.paramProd (Fin k → ℝ) TrivialBundle.zeroSc)).toBase j) :=
    bijective_toBase_prod hbP (TrivialBundle.bijective_toBase_param _)
  have hbE'1 : ∀ j, Bijective (((ScBanach.paramProd (Pm m) TrivialBundle.zeroSc).prod
      (ScBanach.paramProd (Fin k → ℝ) TrivialBundle.zeroSc).shift).toBase j) :=
    bijective_toBase_prod hbP (bijective_toBase_shift (TrivialBundle.bijective_toBase_param _))
  have hdom := (hU.prod_univ (rnSc k)).isScDomain
  have hdom1 := (hU.prod_univ (rnSc k).shift).isScDomain
  have hdom' := (hU'.prod_univ (ScBanach.paramProd (Fin k → ℝ) TrivialBundle.zeroSc)).isScDomain
  have hdom'1 := (hU'.prod_univ (ScBanach.paramProd (Fin k → ℝ) TrivialBundle.zeroSc).shift).isScDomain
  have hι : ∀ v : Fin k → ℝ, (rnSc k).toBase 1 v = v := ScBanach.const_toBase _ 1
  have hι' : ∀ q : (ScBanach.paramProd (Fin k → ℝ) TrivialBundle.zeroSc) 1,
      (ScBanach.paramProd (Fin k → ℝ) TrivialBundle.zeroSc).toBase 1 q = q := fun q =>
    Prod.ext rfl (Subsingleton.elim _ _)
  let Ψ : Pm m × (Fin k → ℝ) → (Pm m × (Fin 0 → ℝ)) × ((Fin k → ℝ) × (Fin 0 → ℝ)) :=
    fun p => ((p.1, 0), (p.2, 0))
  let Ψ' : (Pm m × (Fin 0 → ℝ)) × ((Fin k → ℝ) × (Fin 0 → ℝ)) → Pm m × (Fin k → ℝ) :=
    fun q => (q.1.1, q.2.1)
  have hΨ : ContDiff ℝ ∞ Ψ :=
    (contDiff_fst.prodMk contDiff_const).prodMk (contDiff_snd.prodMk contDiff_const)
  have hΨ' : ContDiff ℝ ∞ Ψ' := contDiff_fst.fst.prodMk contDiff_snd.fst
  -- a radius `r` with `a ∈ C̃, |a| < r ⟹ a ∈ U`
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO 0 (by rw [hUO] at h0; exact h0.1)
  refine ⟨Pm m, Fin k → ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, TrivialBundle.zeroSc, Ct, U ×ˢ univ, Ψ, Ψ', ScNbhdGerm.ofSet hO' h0',
    fun p => (κ p.1, p.2), fun _ => 0, hCt, hU', ?_, rfl, fun x hx => hx,
    ?_, Eventually.of_forall fun _ _ => rfl⟩
  · refine ⟨⟨fun p hp => ⟨⟨hp.1, mem_univ _⟩, mem_univ _⟩, fun _ _ _ _ => rfl,
      fun _ _ => ⟨fun _ _ => Prod.ext rfl (Subsingleton.elim _ _),
        fun _ _ => Prod.ext rfl (Subsingleton.elim _ _)⟩,
      fun j l _ _ _ _ _ _ => ⟨(hbP j).2 _, (TrivialBundle.bijective_toBase_param _ l).2 _⟩,
      isScSmooth_of_bijective_toBase hbE hbE' hdom (f := Ψ) hΨ.contDiffOn, ?_⟩,
      ⟨fun q hq => ⟨hq.1.1, mem_univ _⟩, fun _ _ _ _ => rfl,
      fun _ _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩,
      fun j l _ _ _ _ _ _ => ⟨(bijective_toBase_E j).2 _, (bijective_toBase_const _ l).2 _⟩,
      isScSmooth_of_bijective_toBase hbE' hbE hdom' (f := Ψ') hΨ'.contDiffOn, ?_⟩,
      fun _ _ => rfl, fun q _ => Prod.ext (Prod.ext rfl (Subsingleton.elim _ _))
        (Prod.ext rfl (Subsingleton.elim _ _))⟩
    · refine (isScSmooth_of_bijective_toBase hbE1 hbE'1 hdom1 (f := Ψ)
        hΨ.contDiffOn).congr hdom1 fun p _ => ?_
      refine Prod.ext rfl ?_
      change ((p.2, 0) : (ScBanach.paramProd (Fin k → ℝ) TrivialBundle.zeroSc) 1) =
        invFun ((ScBanach.paramProd (Fin k → ℝ) TrivialBundle.zeroSc).toBase 1) ((rnSc k).toBase 1 p.2, 0)
      rw [hι, ← hι' (p.2, 0), leftInverse_invFun
        ((ScBanach.paramProd (Fin k → ℝ) TrivialBundle.zeroSc).toBase_injective 1)]
      exact hι' _
    · refine (isScSmooth_of_bijective_toBase hbE'1 hbE1 hdom'1 (f := Ψ')
        hΨ'.contDiffOn).congr hdom'1 fun p _ => ?_
      refine Prod.ext rfl ?_
      change (p.2.1 : (rnSc k) 1) =
        invFun ((rnSc k).toBase 1) ((ScBanach.paramProd (Fin k → ℝ) TrivialBundle.zeroSc).toBase 1 p.2).1
      rw [hι', ← hι p.2.1, leftInverse_invFun ((rnSc k).toBase_injective 1)]
      exact hι _
  · have hQ := hCt'.isQuadrantLike
    refine ⟨?_, Prod.ext hκ0 rfl, fun x _ => (sub_zero _).symm, ?_⟩
    · exact IsScSmooth.isScSmoothGerm hQ hO' h0'
        (isScSmooth_of_bijective_toBase hbP (TrivialBundle.bijective_toBase_param _) hU'.isScDomain
          ((hκ.comp contDiff_fst).prodMk contDiff_snd).contDiffOn)
    · refine ⟨?_, rfl, fun ε hε j => ⟨r, hr, fun a ha har w w' _ _ => ⟨?_, ?_⟩⟩⟩
      · exact IsScSmooth.isScSmoothGerm hQ hO' h0'
          (isScSmooth_of_bijective_toBase hbP (bijective_toBase_const _) hU'.isScDomain
            contDiffOn_const) 0
      · change (ScBanach.paramProd (Pm m) TrivialBundle.zeroSc).toBase j (a, w) ∈ U ×ˢ univ
        rw [ScBanach.paramProd_toBase]
        refine ⟨?_, mem_univ _⟩
        rw [hUO]
        exact ⟨hball (by rw [mem_ball_zero_iff]; exact har), ha⟩
      · simp only [Subsingleton.elim w w', sub_self, norm_zero, mul_zero, le_refl]

/-! ### The graph section `x ↦ (x, φ(x))` over the half-space -/

variable {φ : Pm m → (Fin k → ℝ)}

/-- The section `x ↦ (x, φ(x))` of `H × ℝᵏ → H`. -/
def graphSection (φ : Pm m → (Fin k → ℝ)) (x : H m) : H m × (Fin k → ℝ) :=
  (x, φ (x : (halfSpaceSc m) 0))

lemma isSection_graphSection : IsSection (proj m k) (graphSection φ) := fun _ => rfl

/-- `(f, x)` is zero iff `φ(x) = 0`. -/
lemma isZeroAt_graphSection_iff {x : H m} :
    IsZeroAt (proj m k) (graphSection φ) x ↔ φ (x : (halfSpaceSc m) 0) = 0 := by
  constructor
  · intro h
    exact congrArg (fun y : proj m k ⁻¹' {x} => fibEquiv x y) (Subtype.ext h :
      (⟨graphSection φ x, rfl⟩ : proj m k ⁻¹' {x}) = 0)
  · intro h
    change (graphSection φ x) = ((0 : proj m k ⁻¹' {x}) : H m × (Fin k → ℝ))
    refine Prod.ext ((0 : proj m k ⁻¹' {x}).2).symm ?_
    rw [graphSection, h]; rfl

/-- **The graph section is sc-smooth** (in the chart `chart₀` it is `u ↦ (u, φ(u))` on `H`). -/
theorem isScSmoothSection_graphSection (hφ : ContDiff ℝ ∞ φ) :
    (bundle m k).IsScSmoothSection (graphSection φ) := by
  refine ⟨isSection_graphSection, MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ
    (continuous_id.prodMk (hφ.continuous.comp continuous_subtype_val)).continuousOn
    fun x _ => ?_⟩
  refine ⟨baseChart m, chart₀.toMChart (bundle m k).continuous, univ,
    (basePoly m).isChart_of_mem (mem_singleton _), (bundle m k).isChart_toMChart (mem_singleton _),
    isOpen_univ, mem_univ x, fun z _ => ⟨mem_univ _, mem_univ _⟩,
    fun z _ => ⟨mem_univ _, mem_univ _⟩, ?_⟩
  have himg : (baseChart m).toPartialEquiv '' univ = H m := by
    rw [image_univ]; exact Subtype.range_coe
  rw [himg]
  have hval : ∀ u ∈ H m, (chart₀ (m := m) (k := k)).toMChart (bundle m k).continuous
      (graphSection φ ((baseChart m).symm u)) = (u, φ u) := fun u hu => by
    change ((((baseChart m).symm u : H m) : (halfSpaceSc m) 0),
      φ (((baseChart m).symm u : H m) : (halfSpaceSc m) 0)) = (u, φ u)
    rw [baseChart_symm_val hu]
  refine (isScSmoothRetractMap_iff_exists (relOpen_H m).isScRetract).2
    ⟨fun u hu => ?_, ScRetraction.id (relOpen_H m), image_id _, ?_⟩
  · change (chart₀ (m := m) (k := k)).toMChart (bundle m k).continuous
      (graphSection φ ((baseChart m).symm u)) ∈ _
    rw [hval u hu]
    exact ⟨(u, φ u), ⟨hu, mem_univ _⟩, rfl⟩
  · refine (isScSmooth_of_bijective_toBase bijective_toBase_E
      (bijective_toBase_prod bijective_toBase_E (bijective_toBase_const _))
      (relOpen_H m).isScDomain (f := fun u : Pm m => (u, φ u))
      (contDiff_id.prodMk hφ).contDiffOn).congr (relOpen_H m).isScDomain fun u hu => ?_
    exact (hval u hu).symm

/-- The principal part `u ↦ φ(u + x₀)` of the graph section in the chart centred at `x₀`. -/
def loc (φ : Pm m → (Fin k → ℝ)) (x₀ : H m) : Pm m → (Fin k → ℝ) :=
  fun u => φ (u + (x₀ : (halfSpaceSc m) 0))

lemma contDiff_loc (hφ : ContDiff ℝ ∞ φ) (x₀ : H m) : ContDiff ℝ ∞ (loc φ x₀) :=
  hφ.comp (contDiff_id.add contDiff_const)

/-- `ℝ ⊕ ℝᵐ` with its constant structure is the direct sum of the constant structures. -/
def constPmIso (m : ℕ) : ScIso (ScBanach.const (Pm m)) (halfSpaceSc m) where
  lvl _ := ContinuousLinearEquiv.refl ℝ (Pm m)
  incl_comm _ _ := rfl

/-! ### The graph section is sc-Fredholm, and Theorem 3.6.11 (preprint 3.57) applies -/

variable (φ) in
/-- `0` is a regular value of `φ` on `H` and of `φ|∂H`: at every zero `x ∈ H`, `Dφ(x)` is onto, and
at a zero on the boundary `ker Dφ(x) ⊄ {v₁ = 0}` (equivalently, `Dφ(x)` restricted to the
boundary hyperplane is onto). -/
def IsRegularOnHalfSpace : Prop :=
  ∀ x : H m, φ (x : Pm m) = 0 → Surjective (fderiv ℝ φ (x : Pm m)) ∧
    ((x : Pm m).1 0 = 0 → ∃ v, fderiv ℝ φ (x : Pm m) v = 0 ∧ v.1 0 ≠ 0)

/-- The linear map `ℝ ⊕ ℝ → ℝ`, `(a, y) ↦ y`. -/
def exampleMap : Pm 1 →L[ℝ] (Fin 1 → ℝ) :=
  ContinuousLinearMap.pi fun _ => (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℝ _ _)

end HalfSpaceBundle

end Polyfold
