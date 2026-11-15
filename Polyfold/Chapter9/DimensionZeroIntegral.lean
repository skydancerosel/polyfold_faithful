import Polyfold.Chapter9.ZeroFormValues
import Polyfold.Chapter9.MathlibManifoldBridge
import Polyfold.Chapter4.StokesFaceCharts
import Polyfold.Chapter9.Boundary

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §9.5:
**Definition 9.5.6 for `n = 0`**, the branched integrals over oriented points, with Theorems 9.5.4
and 9.5.5 in dimension `0`.  Numbers and pages are the 2021 text's.

# Branched integrals of dimension `0`

## The text, paraphrased
(Theorems 9.5.4, 9.5.5, Definition 9.5.6) For an oriented, tame, compact branched ep⁺-subgroupoid
`Θ̂` of dimension `n` and a form `ω` of degree `n`, `∫_Θ̂ ω = μ_ω(S)` and
`∮_Θ̂ ω = μ^eff_ω(S)`, with `μ_ω(K) = (1/♯G_x) ∑ σᵢ ∫_{Kᵢ} ω|(Mᵢ, oᵢ)` on `|U(x)|` (and
`♯G_x^eff` for `μ^eff`).  For `n = 0` the sheets are oriented points and
`∫_{{p}} ω|({p}, o) = ±ω(p)`.

## What is formalized
Points of an M-polyfold (namespace `Polyfold.MPolyfold`):
* `isSubmanifoldOfDim_singleton`: a smooth point `{p}` is a `0`-dimensional submanifold
  (Remark 9.1.1).
* `isInGoodPosition_bot`: `{0}` is in good position to every partial quadrant containing `0`
  (Definition 3.1.24); **`hasTameInducedStructure_singleton`**: the structure induced on a smooth
  point is tame (2021 Definition 2.5.18), also when `p ∈ ∂X`: it has a corner structure of
  dimension `0` (Theorem 4.1.2's chart, `hasCornerStructureOfDim_of_centred`).
* `isOrientedAt_singleton_univ`, `isOrientedAt_singleton_empty`: the two orientations of
  `T_p{p}` are the positive one (the empty frame) and the negative one (no frame);
  `pointOrientation p b` is the orientation `+` (`b = true`) or `−` of `{p}`.

Ep-groupoids (namespaces `Polyfold.EpGroupoid`, `Polyfold.EP`):
* `EpGroupoid.IsTameOfDimZero Θ T`: `Θ̂ = (Θ, T)` is tame of dimension `0` with point sheets.
* **`EP.branchedIntegralDimZero`**, **`EP.branchedIntegralEffDimZero`**: Definition 9.5.6 for
  `n = 0`, with the integration of `0`-forms over oriented points (`EP.zeroFormIntegration`);
  `branchedMeasureDimZero_apply`, `branchedMeasureEffDimZero_apply`: the local formulas.
* Isolated points (`{x}` open): `isolatedRep x` (a natural representation on `U(x) = {x}`, which
  has the property of Definition 7.2.18, `isolatedRep_hasLUC`) and **`isolatedStructure`**, the
  oriented tame structure of dimension `0` with the one sheet `{x}`, weight `Θ(x)`, orientation `o`;
  `isolatedStructure_localMeasureEff`: its local measure of a set containing `x` is
  `(1/♯G_x^eff) Θ(x) (±ω(x))`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module Submodule

noncomputable section

namespace Polyfold

universe u

/-! ### `{0}` is in good position -/

/-- **`{0}` is in good position** (Definition 3.1.24) to every `C ∋ 0`: the trace `{0} ∩ C` is all
of `{0}`, and `E₀` is a good complement. -/
theorem isInGoodPosition_bot {E : ScBanach} {C : Set (E 0)} (h0 : (0 : E 0) ∈ C) :
    IsInGoodPosition E C ⊥ := by
  have hsub : ∀ x : (⊥ : Submodule ℝ (E 0)), x = 0 := fun x => Subsingleton.elim x 0
  have huniv : (Subtype.val ⁻¹' C : Set (⊥ : Submodule ℝ (E 0))) = univ :=
    eq_univ_of_forall fun x => by rw [hsub x]; exact h0
  refine ⟨?_, ⊤, isCompl_bot_top, 1, one_pos, fun x hx p _ hp => ?_⟩
  · rw [huniv, interior_univ]; exact ⟨0, mem_univ _⟩
  · rw [(Submodule.mem_bot ℝ).1 hx, norm_zero, mul_zero] at hp
    rw [norm_le_zero_iff.1 hp, add_zero]

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- The chart image of a point is a point. -/
lemma image_shrink_inter_singleton {p : X} (hA : P.IsSmoothSubmanifold {p}) {φ : MChart X}
    (hpφ : p ∈ φ.source) :
    φ '' ((hA.data (mem_singleton p)).toSubData.shrink φ ∩ {p}) = {φ p} := by
  rw [inter_eq_right.2 (singleton_subset_iff.2 ((hA.data (mem_singleton p)).toSubData.mem_shrink
    φ (mem_singleton p) (hA.mem_data_V (mem_singleton p)) hpφ)), image_singleton]

/-- The chart tangent space of a point is `{0}`. -/
lemma tangentSpace_shrink_singleton_subset {p : X} (hA : P.IsSmoothSubmanifold {p})
    {φ : MChart X} (hφ : P.IsChart φ) (hpφ : p ∈ φ.source) {z : φ.model.E 1}
    (hz : φ.model.E.toBase 1 z = φ p) :
    tangentSpace φ.model.E φ.model.C
      (φ '' ((hA.data (mem_singleton p)).toSubData.shrink φ ∩ {p})) z ⊆ {0} := by
  have hQ := image_shrink_inter_singleton hA hpφ
  obtain ⟨R, hR⟩ := (hA.data (mem_singleton p)).toSubData.isScRetract_image φ hφ
  rw [hQ]
  exact tangentSpace_singleton_subset R (hR.trans hQ) hz

/-- **A smooth point is a `0`-dimensional submanifold** (Remark 9.1.1): `{p}` is a smooth
submanifold (`isSmoothSubmanifold_singleton`) whose chart tangent space is `{0}`. -/
theorem isSubmanifoldOfDim_singleton {p : X} (hp : p ∈ P.smoothSet) :
    P.IsSubmanifoldOfDim {p} 0 := by
  have hA := isSmoothSubmanifold_singleton hp
  refine ⟨hA, fun a ha => ?_⟩
  rw [mem_singleton_iff.1 ha]
  obtain ⟨φ, hφ, hpφ⟩ := P.exists_isChart_mem_source p
  have hp1 : p ∈ P.levelSet 1 := hA.mem_levelSet_one (mem_singleton p)
  have hz : φ.model.E.toBase 1 (levelLift φ 1 p) = φ p := P.toBase_levelLift hφ hpφ hp1
  refine ⟨mem_singleton p, hA.data (mem_singleton p), φ, levelLift φ 1 p,
    hA.mem_data_V (mem_singleton p), hφ, hpφ, hz, ?_⟩
  have hb : span ℝ (tangentSpace φ.model.E φ.model.C
      (φ '' ((hA.data (mem_singleton p)).toSubData.shrink φ ∩ {p})) (levelLift φ 1 p)) = ⊥ :=
    (span_eq_bot).2 fun v hv => tangentSpace_shrink_singleton_subset hA hφ hpφ hz hv
  rw [hb, finrank_bot]

/-- **The structure induced on a smooth point is tame** (2021 Definition 2.5.18), also at points
of `∂X`: in a chart of `X` centred at `p` the tangent space of `{p}` is `{0}`, which is in good
position to the partial quadrant, so Theorem 4.1.2's chart gives a corner structure of
dimension `0` (`hasCornerStructureOfDim_of_centred`), and corner structures are tame. -/
theorem hasTameInducedStructure_singleton {p : X} (hp : p ∈ P.smoothSet) :
    P.HasTameInducedStructure {p} := by
  let := P.paracompactSpace_subtype {p}
  have hA := isSubmanifoldOfDim_singleton hp
  have hcs := hA.hasCornerStructureOfDim_of_centred fun a ha => by
    obtain rfl : p = a := (mem_singleton_iff.1 ha).symm
    obtain ⟨φ, hφ, hpφ⟩ := P.exists_isChart_mem_source p
    obtain ⟨k, Wq, T, hT⟩ := φ.model.isPartialQuadrant
    have he : φ p ∈ φ.model.E.smooth := (mem_smoothSet_iff hφ hpφ).1 hp
    set ψ := φ.recentre T hT (φ p) he
    have hψ : P.IsChart ψ := φ.recentre_isChart T hT (φ p) he hφ
    have hpψ : p ∈ ψ.source := φ.mem_recentre_source T hT (φ p) he hpφ rfl
    have hψ0 : ψ p = 0 := φ.recentre_apply_self T hT (φ p) he rfl
    refine ⟨ψ, hψ, hpψ, hψ0, fun N hN => ?_⟩
    have hz : ψ.model.E.toBase 1 0 = ψ p := by rw [map_zero, hψ0]
    have hbot : N = ⊥ := (Submodule.eq_bot_iff N).2 fun v hv => by
      have hv' : v ∈ (N : Set (ψ.model.E 0)) := hv
      rw [hN] at hv'
      exact tangentSpace_shrink_singleton_subset hA.1 hψ hpψ hz hv'
    rw [hbot]
    refine isInGoodPosition_bot ?_
    rw [← hψ0]
    exact ψ.model.O_subset_C (ψ.mapsTo_model p hpψ)
  exact ⟨hA.1.isSubMPolyfold, hcs.isTame⟩

/-- The tangent frames of dimension `0` form a subsingleton type. -/
lemma eq_univ_or_eq_empty (O : Set (Fin 0 → P.TangentSpace)) : O = univ ∨ O = ∅ := by
  by_cases h : O.Nonempty
  · obtain ⟨v, hv⟩ := h
    refine Or.inl (eq_univ_of_forall fun w => ?_)
    rwa [Subsingleton.elim w v]
  · exact Or.inr (not_nonempty_iff_eq_empty.1 h)

/-- **Both frame sets orient `T_p{p}`** (the orientations `+` and `−` of a point). -/
theorem isOrientedAt_singleton {p : X} (hp : p ∈ P.smoothSet) (O : Set (Fin 0 → P.TangentSpace)) :
    P.IsOrientedAt p ⟨0, P.submanifoldTangent {p} p, O⟩ := by
  obtain ⟨O₁, O₂, hne, hO⟩ := exists_two_orientations_submanifoldTangent
    (isSubmanifoldOfDim_singleton hp) (mem_singleton p)
  have h1 := (hO O₁).2 (Or.inl rfl)
  have h2 := (hO O₂).2 (Or.inr rfl)
  rcases eq_univ_or_eq_empty O with rfl | rfl <;>
    rcases eq_univ_or_eq_empty O₁ with rfl | rfl <;>
    rcases eq_univ_or_eq_empty O₂ with rfl | rfl <;>
    first | exact absurd rfl hne | assumption

/-- **The orientation `+` (`b = true`) or `−` (`b = false`) of a smooth point** `{p}`. -/
def pointOrientation {p : X} (hp : p ∈ P.smoothSet) (b : Bool) : P.SubmanifoldOrientation {p} 0 :=
  SubmanifoldOrientation.ofPoint (if b then univ else ∅) (isOrientedAt_singleton hp _)

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

open MPolyfold

/-- The sign of the orientation `±` of a point: `+1` for `b = true`, `−1` for `b = false`. -/
theorem frameSign_pointOrientation {p : Obj} (hp : p ∈ X.PObj.smoothSet) (b : Bool) (y : Obj) :
    frameSign (X := X) ((pointOrientation hp b).tangent y) = if b then 1 else -1 := by
  classical
  cases b
  · exact if_neg (by simp [pointOrientation, SubmanifoldOrientation.ofPoint,
      SubmanifoldOrientation.tangent])
  · exact if_pos ⟨Fin.elim0, mem_univ _⟩

variable (X) in
/-- **`Θ̂ = (Θ, T)` is tame of dimension `0`** (Definition 9.3.6 for `n = 0`): at every point of
`supp Θ` an oriented tame structure of dimension `0` whose sheets are points describes `T`. -/
def IsTameOfDimZero (Θ : Obj → ℚ) (T : Obj → X.PObj.OrTangent →₀ ℚ) : Prop :=
  ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure 0 Θ x,
    (∀ i, C.M i ∈ pointSheets X) ∧ C.Represents T

variable {Θ : Obj → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ}

/-- With the local unique continuation property the structures have it (Definition 7.2.18). -/
theorem IsTameOfDimZero.hasLUC (h : X.IsTameOfDimZero Θ T) (hLUC : X.IsLUC) :
    ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure 0 Θ x,
      (∀ i, C.M i ∈ pointSheets X) ∧ C.Represents T ∧ C.rep.HasLUC :=
  fun x hx => (h x hx).imp fun C hC =>
    ⟨hC.1, hC.2, X.isLUC_iff_forall_naturalRep.1 hLUC x C.rep⟩

/-! ### Isolated points -/

variable (X) in
/-- **A natural representation on `U(x) = {x}`** for an isolated point `x` (Theorem 7.1.13 with
`V = {x}`). -/
def isolatedRep (x : Obj) (hx : IsOpen ({x} : Set Obj)) : X.NaturalRep x :=
  (X.theorem_7_1_13 x hx rfl).choose

theorem isolatedRep_U {x : Obj} (hx : IsOpen ({x} : Set Obj)) : (X.isolatedRep x hx).U = {x} :=
  Subset.antisymm (X.theorem_7_1_13 x hx rfl).choose_spec
    (singleton_subset_iff.2 (X.isolatedRep x hx).mem_U)

/-- **On `U(x) = {x}` every `ĝ` is the identity**, so the natural representation has the
property of Definition 7.2.18. -/
theorem isolatedRep_hasLUC {x : Obj} (hx : IsOpen ({x} : Set Obj)) :
    (X.isolatedRep x hx).HasLUC := by
  intro g _ _ _ _ _ y hy
  have hU := isolatedRep_U (X := X) hx
  have h1 : (X.isolatedRep x hx).Φ g y ∈ (X.isolatedRep x hx).U :=
    ((X.isolatedRep x hx).isScDiffeoOn_Φ g).mapsTo hy
  rw [hU] at h1 hy
  rw [mem_singleton_iff.1 h1, mem_singleton_iff.1 hy]

/-- **The oriented tame structure of dimension `0` at an isolated smooth point** `x`: the
natural representation on `U(x) = {x}`, the one sheet `{x}` with weight `Θ(x) > 0`, and an
orientation `o` of `{x}`. -/
def isolatedStructure {x : Obj} (hx : IsOpen ({x} : Set Obj)) (hxs : x ∈ X.PObj.smoothSet)
    (hΘ : 0 < Θ x) (o : X.PObj.SubmanifoldOrientation {x} 0) :
    X.OrientedTameStructure 0 Θ x where
  U := (X.isolatedRep x hx).U
  isOpen_U := (X.isolatedRep x hx).isOpen_U
  mem_U := (X.isolatedRep x hx).mem_U
  ι := PUnit
  M _ := {x}
  subset_U _ := by rw [isolatedRep_U hx]
  isSmoothSubmanifold _ := isSmoothSubmanifold_singleton hxs
  mem_M _ := rfl
  isProperMap _ := (continuous_inclusion _).isProperMap
  σ _ := Θ x
  σ_pos _ := hΘ
  eq_sum y hy := by
    rw [isolatedRep_U hx] at hy
    rw [mem_singleton_iff.1 hy]
    simp
  rep := X.isolatedRep x hx
  U_eq := rfl
  hasPropernessProperty := by
    obtain ⟨V, hxV, hV⟩ := X.exists_hasPropernessProperty x
    refine hV.mono (X.isolatedRep x hx).isOpen_U ?_
    rw [isolatedRep_U hx]
    exact singleton_subset_iff.2 hxV
  hasTameInducedStructure _ := hasTameInducedStructure_singleton hxs
  isSubmanifoldOfDim _ := isSubmanifoldOfDim_singleton hxs
  orient _ := o

theorem isolatedStructure_U {x : Obj} (hx : IsOpen ({x} : Set Obj)) (hxs : x ∈ X.PObj.smoothSet)
    (hΘ : 0 < Θ x) (o : X.PObj.SubmanifoldOrientation {x} 0) :
    (isolatedStructure hx hxs hΘ o).U = {x} :=
  isolatedRep_U (X := X) hx

instance {x : Obj} (hx : IsOpen ({x} : Set Obj)) (hxs : x ∈ X.PObj.smoothSet) (hΘ : 0 < Θ x)
    (o : X.PObj.SubmanifoldOrientation {x} 0) : Unique (isolatedStructure hx hxs hΘ o).ι :=
  inferInstanceAs (Unique PUnit)

theorem isolatedStructure_mem_pointSheets {x : Obj} (hx : IsOpen ({x} : Set Obj))
    (hxs : x ∈ X.PObj.smoothSet) (hΘ : 0 < Θ x) (o : X.PObj.SubmanifoldOrientation {x} 0)
    (i : (isolatedStructure hx hxs hΘ o).ι) :
    (isolatedStructure hx hxs hΘ o).M i ∈ pointSheets X :=
  Or.inr ⟨x, hxs, rfl⟩

/-- `C` describes `T(x) = Θ(x) · T_x({x}, o)`. -/
theorem isolatedStructure_represents {x : Obj} (hx : IsOpen ({x} : Set Obj))
    (hxs : x ∈ X.PObj.smoothSet) (hΘ : 0 < Θ x) (o : X.PObj.SubmanifoldOrientation {x} 0)
    (hT : T x = Finsupp.single (o.tangent x) (Θ x)) :
    (isolatedStructure hx hxs hΘ o).Represents T := by
  classical
  intro y hy _
  rw [isolatedStructure_U] at hy
  rw [mem_singleton_iff.1 hy, hT, OrientedBranchingStructure.orientedSum]
  have hf : (Finset.univ.filter fun i : (isolatedStructure hx hxs hΘ o).toOriented.ι =>
      x ∈ (isolatedStructure hx hxs hΘ o).toOriented.M i) = Finset.univ :=
    Finset.filter_true_of_mem fun _ _ => rfl
  rw [hf]
  have : Unique (isolatedStructure hx hxs hΘ o).toOriented.ι := inferInstanceAs (Unique PUnit)
  rw [Fintype.sum_unique]
  rfl

theorem isolatedStructure_hasLUC {x : Obj} (hx : IsOpen ({x} : Set Obj))
    (hxs : x ∈ X.PObj.smoothSet) (hΘ : 0 < Θ x) (o : X.PObj.SubmanifoldOrientation {x} 0) :
    (isolatedStructure hx hxs hΘ o).rep.HasLUC :=
  isolatedRep_hasLUC (X := X) hx

end EpGroupoid

namespace EP

open EpGroupoid

variable (A : EP.{u}) {Θ : A.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}

/-- **Definition 9.5.6 (1) for `n = 0`: `∫_Θ̂ ω = μ_ω(|supp Θ|)`**, the weighted signed count of a
`0`-form `ω` over an oriented, tame, compact `0`-dimensional `Θ̂` (Theorem 9.5.4 with
`∫_{{p}} ω|({p}, o) = ±ω(p)`). -/
def branchedIntegralDimZero (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : A.X.IsTameOfDimZero Θ T) (ω : A.epFormsInfty 0) : ℝ :=
  branchedIntegral A.zeroFormIntegration hΘ hcpt hT hloc ω

/-- **Definition 9.5.6 (2) for `n = 0`: `∮_Θ̂ ω = μ^eff_ω(|supp Θ|)`** (Theorem 9.5.5, weights
`1/♯G_x^eff`), for `X` with the local unique continuation property. -/
def branchedIntegralEffDimZero (hLUC : A.X.IsLUC) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : A.X.IsTameOfDimZero Θ T) (ω : A.epFormsInfty 0) : ℝ :=
  branchedIntegralEff A.zeroFormIntegration hΘ hcpt hT (hloc.hasLUC hLUC) ω

/-- **The local formula** (Theorem 9.5.4 for `n = 0`). -/
theorem branchedMeasureDimZero_apply (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : A.X.IsTameOfDimZero Θ T) (ω : A.epFormsInfty 0) {x : A.Obj}
    (C : A.X.OrientedTameStructure 0 Θ x) (hS : ∀ i, C.M i ∈ pointSheets A.X)
    (hCT : C.Represents T) {K : Set (A.X.orbitSupp Θ)}
    (hK : MeasurableSet[A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X)) Θ] K)
    (hKU : Subtype.val '' K ⊆ A.X.π '' C.U) :
    branchedMeasure A.zeroFormIntegration hΘ hcpt hT hloc ω K =
      C.localMeasure A.zeroFormIntegration ω (Subtype.val '' K) :=
  branchedMeasure_apply A.zeroFormIntegration hΘ hcpt hT hloc ω C hS hCT hK hKU

/-- **The local formula of the effective integral** (Theorem 9.5.5 for `n = 0`). -/
theorem branchedMeasureEffDimZero_apply (hLUC : A.X.IsLUC) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : A.X.IsTameOfDimZero Θ T) (ω : A.epFormsInfty 0) {x : A.Obj}
    (C : A.X.OrientedTameStructure 0 Θ x) (hS : ∀ i, C.M i ∈ pointSheets A.X)
    (hCT : C.Represents T) {K : Set (A.X.orbitSupp Θ)}
    (hK : MeasurableSet[A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X)) Θ] K)
    (hKU : Subtype.val '' K ⊆ A.X.π '' C.U) :
    branchedMeasureEff A.zeroFormIntegration hΘ hcpt hT (hloc.hasLUC hLUC) ω K =
      C.localMeasureEff A.zeroFormIntegration ω (Subtype.val '' K) :=
  branchedMeasureEff_apply A.zeroFormIntegration hΘ hcpt hT (hloc.hasLUC hLUC) ω C hS hCT
    (A.X.isLUC_iff_forall_naturalRep.1 hLUC x C.rep) hK hKU

variable {A}

/-- **The local measure at an isolated point**: for `K ∋ π(x)`,
`μ_ω^{U(x)}(K) = (1/♯G_x) Θ(x) (±ω(x))`, the sign that of `o`. -/
theorem isolatedStructure_localMeasure {x : A.Obj} (hx : IsOpen ({x} : Set A.Obj))
    (hxs : x ∈ A.X.PObj.smoothSet) (hΘ : 0 < Θ x) (o : A.X.PObj.SubmanifoldOrientation {x} 0)
    (ω : A.epFormsInfty 0) {K : Set A.X.OrbitSpace} (hK : A.X.π x ∈ K) :
    (isolatedStructure hx hxs hΘ o).localMeasure A.zeroFormIntegration ω K =
      (Nat.card (A.X.Isotropy x) : ℝ)⁻¹ *
        ((Θ x : ℝ) * (frameSign (o.tangent x) * A.zeroFormEval ω x)) := by
  rw [OrientedTameStructure.localMeasure, OrientedTameStructure.sheetSum, Fintype.sum_unique]
  congr 2
  exact zeroFormIntegration_integ_singleton A ω _ ⟨hK, rfl⟩

/-- **The effective local measure at an isolated point**: for `K ∋ π(x)`,
`μ_ω^{eff,U(x)}(K) = (1/♯G_x^eff) Θ(x) (±ω(x))`. -/
theorem isolatedStructure_localMeasureEff {x : A.Obj} (hx : IsOpen ({x} : Set A.Obj))
    (hxs : x ∈ A.X.PObj.smoothSet) (hΘ : 0 < Θ x) (o : A.X.PObj.SubmanifoldOrientation {x} 0)
    (ω : A.epFormsInfty 0) {K : Set A.X.OrbitSpace} (hK : A.X.π x ∈ K) :
    (isolatedStructure hx hxs hΘ o).localMeasureEff A.zeroFormIntegration ω K =
      (Nat.card (A.X.EffIsotropy x) : ℝ)⁻¹ *
        ((Θ x : ℝ) * (frameSign (o.tangent x) * A.zeroFormEval ω x)) := by
  rw [OrientedTameStructure.localMeasureEff, OrientedTameStructure.sheetSum, Fintype.sum_unique]
  congr 2
  exact zeroFormIntegration_integ_singleton A ω _ ⟨hK, rfl⟩

end EP

end Polyfold
