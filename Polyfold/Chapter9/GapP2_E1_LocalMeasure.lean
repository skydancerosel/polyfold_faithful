import Polyfold.Chapter9.GapP2_E1_SheetIntegration
import Polyfold.Chapter9.MeasureEffective
import Polyfold.Chapter7.Zhou

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5 "Integration and Stokes": the local measures (9.21) (p. 441),
**Lemma 9.5.7** (p. 439; 2017: Lemma 9.17), **Lemma 9.5.9** (p. 442; 2017: Lemma 9.18),
**Lemma 9.5.10** with (9.23) (p. 444, new in the 2021 edition) and **Lemma 9.5.11** (p. 445; 2017:
Lemma 9.19).  Numbers and pages are the 2021 text's.

# The local measures `μ_ω^U`, `μ_ω^{eff,U}` and their three invariance lemmas

## The text, paraphrased

(9.21) For `U = U(x)` with the natural `G_x`-action and an oriented local branching structure
`(Mᵢ, oᵢ)`, `(σᵢ)`, and a measurable `K ⊆ |M_U|` with preimages `Kᵢ ⊆ Mᵢ`,
`μ_ω^U(K) = (1/♯G_x) ∑ σᵢ ∫_{Kᵢ} ω|(Mᵢ, oᵢ)` and `μ_ω^{eff,U}(K)` with `♯G_x^eff`.
(Lemma 9.5.7) They do not depend on the oriented structure on `U`.  (Lemma 9.5.9) For `y ∈ U` and
a small `V = V(y) ⊆ U` with the natural `G_y`-action, `μ_ω^U(K) = μ_ω^V(K)` for `K ⊆ |M_V|`.
(Lemma 9.5.10) The same for the effective measures under the local unique continuation property.
(Lemma 9.5.11) For a morphism `φ : x → x'` whose local sc-diffeomorphism is `φ̂ : U → U'`,
`μ_ω^U(K) = μ_ω^{U'}(K)`, and likewise for the effective measures.

## What is formalized

For a `SheetIntegration` `𝓘` on a class `S` of sheets (`GapP2_E1_SheetIntegration.lean`):

* `OrientedTameStructure n Θ x`: a tame local branching structure at `x` (natural `G_x`-action,
  properness property, tame sheets: `TameBranchingStructure`, Definition 9.3.6) whose sheets are
  `n`-dimensional and oriented; `toOriented`, `Represents T` (it describes the orientation `T̂Θ`,
  (9.9)), `IsMeas` (measurable traces on all sheets).
* `sheetSum 𝓘 ω A = ∑ σᵢ ∫_{A ∩ Mᵢ} ω|(Mᵢ, oᵢ)`, `localMeasure` (`μ_ω^U`), `localMeasureEff`
  (`μ_ω^{eff,U}`): **(9.21)**; linear in `ω`, additive in the set.
* `sheetSum_eq_of_orientedSum_eq` and **`lemma_9_5_7`**.
* `sheetSum_image`: the sums of two structures correspond under an sc-diffeomorphism whose tangent
  maps are those of morphisms; `isMorTangentOn_Φ` (the maps `ϕ_g` of a natural representation are
  such).
* **`lemma_9_5_9`**, **`lemma_9_5_10`** (with (9.23), `card_quotient_stabilizer_mul_card_effIsotropy`),
  **`lemma_9_5_11`**.

## The choices made

* In Lemma 9.5.9 the structure on `V` is any oriented tame structure at `y` describing `T̂Θ`
  (the text takes the restriction `M̃ᵢ = V ∩ Mᵢ`; by Lemma 9.5.7 this makes no difference), and
  "`V` small enough" is the property used in the text's proof: `ϕ_g(V) = V` for `g ∈ H` and
  `ϕ_g(V) ∩ V = ∅` for `g ∉ H` (such `V` exist: `NaturalRep.exists_slice`).
* In Lemma 9.5.11 the local sc-diffeomorphism `φ̂ : U → U'` is an sc-diffeomorphism with
  `φ̂(x) = x'` whose tangent map at every point `w` is `Tψ` for a morphism `ψ : w → φ̂(w)`
  (`IsMorTangentOn`).  The effective statement holds without the local unique continuation
  property and for every such `U`: only `♯G_x^eff = ♯G_{x'}^eff` is used.
* The measurability of `K` is the measurability of the traces of `π⁻¹(K)` on the sheets
  (`IsMeas`); for `K ∈ L(S)` see `GapP2_E1_BranchedIntegral.lean`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

variable (X : EpGroupoid Obj Mor) in
/-- **An oriented tame local branching structure of dimension `n` at `x`** (2021 Definition
9.3.6, p. 425, with the orientations of p. 423): a tame local branching structure
(`TameBranchingStructure`: natural `G_x`-action on `U(x)`, properness property, tame sheets) whose
sheets `Mᵢ` are `n`-dimensional and oriented. -/
structure OrientedTameStructure (n : ℕ) (Θ : Obj → ℚ) (x : Obj) extends
    X.TameBranchingStructure Θ x where
  isSubmanifoldOfDim : ∀ i, X.PObj.IsSubmanifoldOfDim (M i) n
  /-- The orientations `oᵢ`. -/
  orient : ∀ i, X.PObj.SubmanifoldOrientation (M i) n

variable {X : EpGroupoid Obj Mor} {S : Set (Set Obj)} {G : SheetNullSets S} {Ω : Type*}
  [AddCommGroup Ω] [Module ℝ Ω] (𝓘 : X.SheetIntegration G Ω) {n : ℕ} {Θ : Obj → ℚ}

namespace OrientedTameStructure

open scoped Classical

section Basic

variable {x : Obj} (C : X.OrientedTameStructure n Θ x)

/-- The underlying local branching structure with orientations. -/
def toOriented : X.OrientedBranchingStructure Θ x where
  toLocalBranchingStructure := C.toLocalBranchingStructure
  dim := fun _ => n
  isSubmanifoldOfDim := C.isSubmanifoldOfDim
  orient := C.orient

/-- `C` describes the orientation `T̂Θ = T` on `U(x)`: `T(y) = ∑_{y ∈ Mᵢ} σᵢ · T_y(Mᵢ, oᵢ)`
(9.9). -/
def Represents (T : Obj → X.PObj.OrTangent →₀ ℚ) : Prop :=
  ∀ y ∈ C.U, y ∈ X.PObj.smoothSet → T y = C.toOriented.orientedSum y

theorem orientedSum_eq_sum_ite (y : Obj) : C.toOriented.orientedSum y =
    ∑ i, if y ∈ C.M i then Finsupp.single ((C.orient i).tangent y) (C.σ i) else 0 := by
  rw [OrientedBranchingStructure.orientedSum, Finset.sum_filter]
  rfl

variable (G) in
/-- `A` has measurable traces on all sheets of `C`. -/
def IsMeas (A : Set Obj) : Prop := ∀ i, G.IsMeasIn (C.M i) A

/-- **`∑ σᵢ ∫_{A ∩ Mᵢ} ω|(Mᵢ, oᵢ)`**, the sum in (9.20) and (9.21). -/
def sheetSum (ω : Ω) (A : Set Obj) : ℝ :=
  ∑ i, (C.σ i : ℝ) * 𝓘.integ ω (C.M i) (C.orient i).tangent (A ∩ C.M i)

/-- **(9.21), 2021 p. 441: the local measure** `μ_ω^{U(x)}(K) = (1/♯G_x) ∑ σᵢ ∫_{Kᵢ} ω|(Mᵢ, oᵢ)`,
`Kᵢ = Mᵢ ∩ π⁻¹(K)`. -/
def localMeasure (ω : Ω) (K : Set X.OrbitSpace) : ℝ :=
  (Nat.card (X.Isotropy x) : ℝ)⁻¹ * C.sheetSum 𝓘 ω (X.π ⁻¹' K)

/-- **(9.21), 2021 p. 441: the effective local measure**
`μ_ω^{eff,U(x)}(K) = (1/♯G_x^eff) ∑ σᵢ ∫_{Kᵢ} ω|(Mᵢ, oᵢ)`. -/
def localMeasureEff (ω : Ω) (K : Set X.OrbitSpace) : ℝ :=
  (Nat.card (X.EffIsotropy x) : ℝ)⁻¹ * C.sheetSum 𝓘 ω (X.π ⁻¹' K)

theorem sheetSum_congr (ω : Ω) {A A' : Set Obj} (h : ∀ i, A ∩ C.M i = A' ∩ C.M i) :
    C.sheetSum 𝓘 ω A = C.sheetSum 𝓘 ω A' :=
  Finset.sum_congr rfl fun i _ => by rw [h i]

theorem subset_MU (i : C.ι) : C.M i ⊆ C.MU := subset_iUnion C.M i

theorem MU_inter_inter (A : Set Obj) (i : C.ι) : C.MU ∩ A ∩ C.M i = A ∩ C.M i := by
  ext y
  simp only [mem_inter_iff]
  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨C.subset_MU i h.2, h.1⟩, h.2⟩⟩

theorem sheetSum_MU_inter (ω : Ω) (A : Set Obj) :
    C.sheetSum 𝓘 ω (C.MU ∩ A) = C.sheetSum 𝓘 ω A :=
  C.sheetSum_congr 𝓘 ω fun i => C.MU_inter_inter A i

theorem sheetSum_add (ω τ : Ω) (A : Set Obj) :
    C.sheetSum 𝓘 (ω + τ) A = C.sheetSum 𝓘 ω A + C.sheetSum 𝓘 τ A := by
  simp only [sheetSum, 𝓘.integ_add, mul_add, Finset.sum_add_distrib]

theorem sheetSum_smul (c : ℝ) (ω : Ω) (A : Set Obj) :
    C.sheetSum 𝓘 (c • ω) A = c * C.sheetSum 𝓘 ω A := by
  simp only [sheetSum, 𝓘.integ_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sheetSum_empty (hS : ∀ i, C.M i ∈ S) (ω : Ω) : C.sheetSum 𝓘 ω ∅ = 0 :=
  Finset.sum_eq_zero fun i _ => by
    rw [empty_inter, 𝓘.integ_empty ω (hS i) (C.orient i), mul_zero]

/-- Countable additivity of `A ↦ ∑ σᵢ ∫_{A ∩ Mᵢ} ω|(Mᵢ, oᵢ)`. -/
theorem sheetSum_hasSum (hS : ∀ i, C.M i ∈ S) (ω : Ω) (A : ℕ → Set Obj)
    (hA : ∀ k, C.IsMeas G (A k)) (hd : Pairwise (Function.onFun Disjoint A)) :
    HasSum (fun k => C.sheetSum 𝓘 ω (A k)) (C.sheetSum 𝓘 ω (⋃ k, A k)) := by
  unfold sheetSum
  refine hasSum_sum fun i _ => HasSum.mul_left _ ?_
  rw [iUnion_inter]
  exact 𝓘.integ_hasSum ω _ (hS i) (C.orient i) (fun k => A k ∩ C.M i)
    (fun k => inter_subset_right)
    (fun k => (hA k i).inter (SheetNullSets.isMeasIn_self _))
    fun k l hkl => (hd hkl).mono inter_subset_left inter_subset_left

/-- Finite additivity of `A ↦ ∑ σᵢ ∫_{A ∩ Mᵢ} ω|(Mᵢ, oᵢ)`. -/
theorem sheetSum_iUnion_fintype (hS : ∀ i, C.M i ∈ S) (ω : Ω) {T : Type*} [Fintype T]
    (P : T → Set Obj) (hP : ∀ t, C.IsMeas G (P t)) (hd : Pairwise (Function.onFun Disjoint P)) :
    C.sheetSum 𝓘 ω (⋃ t, P t) = ∑ t, C.sheetSum 𝓘 ω (P t) := by
  unfold sheetSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, iUnion_inter]
  congr 1
  have h := 𝓘.integ_biUnion_finset ω (hS i) (C.orient i) Finset.univ (fun t => P t ∩ C.M i)
    (fun t => inter_subset_right)
    (fun t => (hP t i).inter (SheetNullSets.isMeasIn_self _))
    fun s t hst => (hd hst).mono inter_subset_left inter_subset_left
  simpa using h

end Basic

/-! ### Lemma 9.5.7 -/

section Independence

variable {x x' : Obj} (C : X.OrientedTameStructure n Θ x) (C' : X.OrientedTameStructure n Θ x')

include 𝓘 in
/-- Measurability passes from the sheets of `C` to the sheets of `C'`, for subsets of `M_U`. -/
theorem IsMeas.of_subset_MU (hS : ∀ i, C.M i ∈ S) (hS' : ∀ i, C'.M i ∈ S) {A : Set Obj}
    (hA : C.IsMeas G A) (hAM : A ⊆ C.MU) : C'.IsMeas G A := fun j =>
  𝓘.isMeasIn_of_cover hS (hS' j) (inter_subset_left.trans hAM) hA

/-- **(9.20), 2021 p. 440**: two oriented tame structures (at possibly different points) whose
weighted sums of oriented tangent spaces agree at the points of `A ⊆ M_U ∩ M_{U'}` (9.19) have the
same sum `∑ σᵢ ∫_{A ∩ Mᵢ} ω|(Mᵢ, oᵢ)`. -/
theorem sheetSum_eq_of_orientedSum_eq (hS : ∀ i, C.M i ∈ S) (hS' : ∀ i, C'.M i ∈ S) (ω : Ω)
    {A : Set Obj} (hAM : A ⊆ C.MU) (hA : C.IsMeas G A)
    (hsum : ∀ y ∈ A, C.toOriented.orientedSum y = C'.toOriented.orientedSum y) :
    C.sheetSum 𝓘 ω A = C'.sheetSum 𝓘 ω A := by
  have hA' : C'.IsMeas G A := hA.of_subset_MU 𝓘 C C' hS hS' hAM
  refine 𝓘.sum_integ_eq_sum_integ ω C.orient C'.orient hS hS' C.σ C'.σ
    (fun i => (hA i).inter (SheetNullSets.isMeasIn_self _))
    (fun j => (hA' j).inter (SheetNullSets.isMeasIn_self _)) fun y hy => ?_
  have h := hsum y hy
  rw [C.orientedSum_eq_sum_ite, C'.orientedSum_eq_sum_ite] at h
  convert h

theorem sheetSum_eq_of_represents (hΘ : X.IsBranchedEpSubgroupoid Θ)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hS : ∀ i, C.M i ∈ S) (hS' : ∀ i, C'.M i ∈ S)
    (hCT : C.Represents T) (hC'T : C'.Represents T) (ω : Ω) {A : Set Obj}
    (hAM : A ⊆ C.MU ∩ C'.MU) (hA : C.IsMeas G A) :
    C.sheetSum 𝓘 ω A = C'.sheetSum 𝓘 ω A := by
  refine C.sheetSum_eq_of_orientedSum_eq 𝓘 C' hS hS' ω (hAM.trans inter_subset_left) hA
    fun y hy => ?_
  have h1 := (hAM hy).1
  have h2 := (hAM hy).2
  rw [LocalBranchingStructure.MU_eq] at h1 h2
  have hsm := hΘ.support_subset h1.1
  rw [← hCT y h1.2 hsm, ← hC'T y h2.2 hsm]

end Independence

/-- **Lemma 9.5.7 (Independence), 2021 p. 439 (2017: Lemma 9.17)**: two oriented tame local
branching structures `(Mᵢ, oᵢ)`, `(σᵢ)` and `(M'ᵢ', o'ᵢ')`, `(σ'ᵢ')` on the same `U = U(x)` with
the same weighted sums of oriented tangent spaces (9.19) give the same local measures:
`(1/♯G_x) ∑ σᵢ ∫_{Kᵢ} ω|(Mᵢ, oᵢ) = (1/♯G_x) ∑ σ'ᵢ' ∫_{K'ᵢ'} ω|(M'ᵢ', o'ᵢ')`, and likewise with
`♯G_x^eff`.  Here `K` is measurable (its preimage has measurable traces on the sheets). -/
theorem lemma_9_5_7 {x : Obj} (C C' : X.OrientedTameStructure n Θ x) (hS : ∀ i, C.M i ∈ S)
    (hS' : ∀ i, C'.M i ∈ S) (hU : C.U = C'.U)
    (hb : ∀ y ∈ C.U, C.toOriented.orientedSum y = C'.toOriented.orientedSum y) (ω : Ω)
    {K : Set X.OrbitSpace} (hK : C.IsMeas G (X.π ⁻¹' K)) :
    C.localMeasure 𝓘 ω K = C'.localMeasure 𝓘 ω K ∧
      C.localMeasureEff 𝓘 ω K = C'.localMeasureEff 𝓘 ω K := by
  have hMU : C.MU = C'.MU := by
    rw [LocalBranchingStructure.MU_eq, LocalBranchingStructure.MU_eq, hU]
  have hmeas : C.IsMeas G (C.MU ∩ X.π ⁻¹' K) := fun i =>
    (hK i).congr_inter (C.MU_inter_inter _ i).symm
  have h : C.sheetSum 𝓘 ω (X.π ⁻¹' K) = C'.sheetSum 𝓘 ω (X.π ⁻¹' K) := by
    rw [← C.sheetSum_MU_inter, ← C'.sheetSum_MU_inter, ← hMU]
    exact C.sheetSum_eq_of_orientedSum_eq 𝓘 C' hS hS' ω inter_subset_left hmeas fun y hy => by
      have := hy.1
      rw [LocalBranchingStructure.MU_eq] at this
      exact hb y this.2
  exact ⟨by rw [localMeasure, localMeasure, h], by rw [localMeasureEff, localMeasureEff, h]⟩

/-! ### Sc-diffeomorphisms given by morphisms -/

section Image

variable {x x' : Obj} (C : X.OrientedTameStructure n Θ x) (C' : X.OrientedTameStructure n Θ x')
  {f f' : Obj → Obj} {U U' : Set Obj}

include 𝓘 in
/-- The image of a measurable subset of `M_U` under an sc-diffeomorphism given by morphisms is
measurable in the sheets of any structure. -/
theorem IsMeas.image (hS : ∀ i, C.M i ∈ S) (hS' : ∀ i, C'.M i ∈ S)
    (hf : X.PObj.IsScDiffeoOn X.PObj f f' U U') (hmor : X.IsMorTangentOn hf U) {A : Set Obj}
    (hAU : A ⊆ C.MU ∩ U) (hA : C.IsMeas G A) : C'.IsMeas G (f '' A) := by
  have hUo : IsOpen U := hf.isScSmoothOn.isOpen
  have hNS : ∀ i, C.M i ∩ U ∈ S := fun i => 𝓘.inter_mem _ (hS i) U hUo
  have hmor' : ∀ i, X.IsMorTangentOn hf (C.M i ∩ U) := fun i w hw => hmor w hw.2
  have hN'S : ∀ i, f '' (C.M i ∩ U) ∈ S := fun i =>
    𝓘.image_mem _ (hNS i) hf inter_subset_right (hmor' i)
  have hAi : ∀ i, G.IsMeasIn (C.M i ∩ U) (A ∩ C.M i) := fun i =>
    SheetNullSets.IsMeasIn.transfer (hS i) (hNS i)
      (by rw [inter_comm (C.M i) (C.M i ∩ U)]; exact 𝓘.isMeasIn_inter _ (hNS i) _ (hS i))
      (fun y hy => ⟨hy.2, hy.2, (hAU hy.1).2⟩)
      ((hA i).inter (SheetNullSets.isMeasIn_self _))
  have himg : ∀ i, G.IsMeasIn (f '' (C.M i ∩ U)) (f '' A) := fun i => by
    have h := 𝓘.isMeasIn_image _ (hNS i) hf inter_subset_right (hmor' i) (A ∩ C.M i)
      (fun y hy => ⟨hy.2, (hAU hy.1).2⟩) (hAi i)
    refine h.congr_inter ?_
    ext z
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hz⟩
      exact ⟨⟨a, ha.1, rfl⟩, hz⟩
    · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
      have : b = a := by
        rw [← hf.left_inv b hb.2, hab, hf.left_inv a (hAU ha).2]
      exact ⟨⟨a, ⟨ha, this ▸ hb.1⟩, rfl⟩, ⟨b, hb, hab⟩⟩
  intro j
  refine 𝓘.isMeasIn_of_cover hN'S (hS' j) ?_ himg
  rintro _ ⟨⟨a, ha, rfl⟩, -⟩
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hAU ha).1
  exact mem_iUnion.2 ⟨i, a, ⟨hi, (hAU ha).2⟩, rfl⟩

/-- **The change of variables behind Lemmas 9.5.9 and 9.5.11 (2021 pp. 443, 445)**: let `f` be an
sc-diffeomorphism `U → U'` whose tangent maps are the `Tψ` of morphisms `ψ : w → f(w)`, and `C`,
`C'` two oriented tame structures describing the orientation `T̂Θ`.  For a measurable
`A ⊆ M_U ∩ U` with `f(A) ⊆ M_{U'}`, the sum of `C'` over `f(A)` is the sum of `C` over `A`
(`f^*ω = ω`, the naturality of `T̂Θ`, and (9.20)). -/
theorem sheetSum_image (hΘ : X.IsBranchedEpSubgroupoid Θ) {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hT : X.IsOrientation Θ T) (hS : ∀ i, C.M i ∈ S) (hS' : ∀ i, C'.M i ∈ S)
    (hCT : C.Represents T) (hC'T : C'.Represents T)
    (hf : X.PObj.IsScDiffeoOn X.PObj f f' U U') (hmor : X.IsMorTangentOn hf U) (ω : Ω)
    {A : Set Obj} (hAU : A ⊆ C.MU ∩ U) (hA : C.IsMeas G A) (hfA : f '' A ⊆ C'.MU) :
    C'.sheetSum 𝓘 ω (f '' A) = C.sheetSum 𝓘 ω A := by
  have hUo : IsOpen U := hf.isScSmoothOn.isOpen
  have hNS : ∀ i, C.M i ∩ U ∈ S := fun i => 𝓘.inter_mem _ (hS i) U hUo
  have hmor' : ∀ i, X.IsMorTangentOn hf (C.M i ∩ U) := fun i w hw => hmor w hw.2
  have hN'S : ∀ i, f '' (C.M i ∩ U) ∈ S := fun i =>
    𝓘.image_mem _ (hNS i) hf inter_subset_right (hmor' i)
  have hMN : ∀ i, X.PObj.IsSmoothSubmanifold (C.M i ∩ U) := fun i =>
    (C.isSmoothSubmanifold i).inter_isOpen hUo
  -- the moved family
  let o' : ∀ i, X.PObj.SubmanifoldOrientation (f '' (C.M i ∩ U)) n := fun i =>
    ((C.orient i).restrict hUo).mapDiffeo (hMN i) hf inter_subset_right
  have himgset : ∀ i, f '' (A ∩ C.M i) = f '' A ∩ f '' (C.M i ∩ U) := by
    intro i
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha.1, rfl⟩, ⟨a, ⟨ha.2, (hAU ha.1).2⟩, rfl⟩⟩
    · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
      have : b = a := by
        rw [← hf.left_inv b hb.2, hab, hf.left_inv a (hAU ha).2]
      exact ⟨a, ⟨ha, this ▸ hb.1⟩, rfl⟩
  have hAi : ∀ i, G.IsMeasIn (C.M i ∩ U) (A ∩ C.M i) := fun i =>
    SheetNullSets.IsMeasIn.transfer (hS i) (hNS i)
      (by rw [inter_comm (C.M i) (C.M i ∩ U)]; exact 𝓘.isMeasIn_inter _ (hNS i) _ (hS i))
      (fun y hy => ⟨hy.2, hy.2, (hAU hy.1).2⟩)
      ((hA i).inter (SheetNullSets.isMeasIn_self _))
  -- step 1: every integral of `C` is an integral over the moved sheet
  have step1 : ∀ i, 𝓘.integ ω (C.M i) (C.orient i).tangent (A ∩ C.M i) =
      𝓘.integ ω (f '' (C.M i ∩ U)) (o' i).tangent (f '' A ∩ f '' (C.M i ∩ U)) := by
    intro i
    rw [← himgset i]
    have h1 := 𝓘.integ_congr ω _ (hS i) _ (hNS i) (C.orient i) ((C.orient i).restrict hUo)
      (A ∩ C.M i) (fun y hy => ⟨hy.2, hy.2, (hAU hy.1).2⟩)
      ((hA i).inter (SheetNullSets.isMeasIn_self _))
      (fun y hy => ((C.orient i).restrict_tangent hUo (hAU hy.1).2).symm)
    have h2 := 𝓘.integ_image ω _ (hNS i) ((C.orient i).restrict hUo) (hMN i) hf
      inter_subset_right (hmor' i) (A ∩ C.M i) (fun y hy => ⟨hy.2, (hAU hy.1).2⟩) (hAi i)
    rw [h1, ← h2]
  have hA' : C'.IsMeas G (f '' A) := hA.image 𝓘 C C' hS hS' hf hmor hAU
  have hAimg : ∀ i, G.IsMeasIn (f '' (C.M i ∩ U)) (f '' A ∩ f '' (C.M i ∩ U)) := fun i => by
    rw [← himgset i]
    exact 𝓘.isMeasIn_image _ (hNS i) hf inter_subset_right (hmor' i) (A ∩ C.M i)
      (fun y hy => ⟨hy.2, (hAU hy.1).2⟩) (hAi i)
  have hC : C.sheetSum 𝓘 ω A = ∑ i, (C.σ i : ℝ) *
      𝓘.integ ω (f '' (C.M i ∩ U)) (o' i).tangent (f '' A ∩ f '' (C.M i ∩ U)) :=
    Finset.sum_congr rfl fun i _ => by rw [step1 i]
  rw [hC]
  symm
  refine 𝓘.sum_integ_eq_sum_integ ω o' C'.orient hN'S hS' C.σ C'.σ hAimg
    (fun j => (hA' j).inter (SheetNullSets.isMeasIn_self _)) ?_
  rintro _ ⟨a, ha, rfl⟩
  have haM : a ∈ C.MU := (hAU ha).1
  have haU : a ∈ U := (hAU ha).2
  have hfaM : f a ∈ C'.MU := hfA ⟨a, ha, rfl⟩
  rw [LocalBranchingStructure.MU_eq] at haM hfaM
  have hsm : a ∈ X.PObj.smoothSet := hΘ.support_subset haM.1
  have hsm' : f a ∈ X.PObj.smoothSet := hΘ.support_subset hfaM.1
  obtain ⟨ψ, hsrc, htgt, hψ⟩ := hmor a haU
  -- the right-hand side is `T̂Θ(f a)`
  have hR : (∑ l, if f a ∈ C'.M l then
      Finsupp.single ((C'.orient l).tangent (f a)) (C'.σ l) else 0) = T (f a) := by
    rw [hC'T (f a) hfaM.2 hsm', C'.orientedSum_eq_sum_ite]
  -- the left-hand side is `Tf(T̂Θ(a))`
  have hL : (∑ i, if f a ∈ f '' (C.M i ∩ U) then
      Finsupp.single ((o' i).tangent (f a)) (C.σ i) else 0) =
      (T a).mapDomain (MPolyfold.OrTangent.map (MPolyfold.tangentMapOn hf.isScSmoothOn)) := by
    rw [hCT a haM.2 hsm, C.orientedSum_eq_sum_ite, Finsupp.mapDomain_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hai : a ∈ C.M i
    · have hmem : f a ∈ f '' (C.M i ∩ U) := ⟨a, ⟨hai, haU⟩, rfl⟩
      rw [if_pos hmem, if_pos hai, Finsupp.mapDomain_single]
      congr 1
      have h := MPolyfold.SubmanifoldOrientation.mapDiffeo_tangent ((C.orient i).restrict hUo)
        (hMN i) hf inter_subset_right (y := a) ⟨hai, haU⟩
      rw [(C.orient i).restrict_tangent hUo haU] at h
      exact h
    · have hnm : f a ∉ f '' (C.M i ∩ U) := by
        rintro ⟨b, hb, hab⟩
        have : b = a := by rw [← hf.left_inv b hb.2, hab, hf.left_inv a haU]
        exact hai (this ▸ hb.1)
      rw [if_neg hnm, if_neg hai, Finsupp.mapDomain_zero]
  -- naturality of `T̂Θ`
  have hnat := hT.natural ψ (by rw [hsrc]; exact hsm)
  rw [hsrc, htgt, grHatPush] at hnat
  have hmem := (hT.mem a hsm).2
  have hcongr : (T a).mapDomain (MPolyfold.OrTangent.push (X.tangentMor ψ)) =
      (T a).mapDomain (MPolyfold.OrTangent.map (MPolyfold.tangentMapOn hf.isScSmoothOn)) :=
    Finsupp.mapDomain_congr fun g hg => by
      have hor := hmem g hg
      rw [MPolyfold.OrTangent.map_eq_push]
      exact MPolyfold.OrTangent.push_congr (fun α hα => hψ α (hor.1 α hα))
        fun v hv i => hor.mem_carrier hv i
  rw [hL, hR, ← hnat, hcongr]

end Image

/-- **The maps `ϕ_g` of a natural representation have the tangent maps of the morphisms
`Γ(g, w) : w → ϕ_g(w)`** (2021 p. 331; `NaturalRep.tangentMor_Γ`). -/
theorem _root_.Polyfold.EpGroupoid.NaturalRep.isMorTangentOn_Φ {x : Obj} (R : X.NaturalRep x)
    (g : X.Isotropy x) : X.IsMorTangentOn (R.isScDiffeoOn_Φ g) R.U := fun w hw =>
  ⟨R.Γ g w, R.src_Γ g w hw, R.tgt_Γ g w hw, fun α hα => by
    have hαU : α ∈ R.tangentU := by
      change X.PObj.levelVal 1 (X.PObj.tangentProj α) ∈ R.U
      rw [hα]; exact hw
    have h := R.tangentMor_Γ g hαU
    rw [hα] at h
    exact h⟩

/-! ### Lemmas 9.5.9 and 9.5.10 -/

section Restriction

variable {x : Obj} (C : X.OrientedTameStructure n Θ x)

/-- **The computation in the proof of Lemma 9.5.9 (2021 p. 443)**: for `y ∈ U(x)` with
stabilizer `H` and a neighbourhood `V ⊆ U(x)` of `y` with `ϕ_g(V) = V` for `g ∈ H` and
`ϕ_g(V) ∩ V = ∅` for `g ∉ H`, the preimage of `K ⊆ |M_U ∩ V|` in `M_U` is the disjoint union of
the `ϕ_r(K̃)`, `K̃ = M_U ∩ V ∩ π⁻¹(K)`, and every `r` contributes the same sum:
`∑ σᵢ ∫_{Kᵢ} ω|Mᵢ = ♯(G_x/H) · ∑ σᵢ ∫_{K̃ ∩ Mᵢ} ω|Mᵢ`. -/
theorem sheetSum_preimage_eq_card_mul_slice (hΘ : X.IsBranchedEpSubgroupoid Θ)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T) (hS : ∀ i, C.M i ∈ S)
    (hCT : C.Represents T) (a : C.rep.U) {V : Set Obj} (hVU : V ⊆ C.rep.U)
    (hVH : ∀ g ∈ MulAction.stabilizer (X.Isotropy x) a, C.rep.Φ g '' V = V)
    (hVd : ∀ g ∉ MulAction.stabilizer (X.Isotropy x) a, Disjoint (C.rep.Φ g '' V) V)
    (ω : Ω) {K : Set X.OrbitSpace} (hK : K ⊆ X.π '' (C.MU ∩ V))
    (hKtm : C.IsMeas G (C.MU ∩ V ∩ X.π ⁻¹' K)) :
    C.sheetSum 𝓘 ω (X.π ⁻¹' K) =
      (Nat.card (X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a) : ℝ) *
        C.sheetSum 𝓘 ω (C.MU ∩ V ∩ X.π ⁻¹' K) := by
  have hfin : Finite (X.Isotropy x) := NatRepConstruction.finite_isotropy X x
  have : Fintype (X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a) := Fintype.ofFinite _
  have hBU : C.U = C.rep.U := C.U_eq
  have hMUU : C.MU ⊆ C.rep.U := fun z hz => by
    rw [LocalBranchingStructure.MU_eq, hBU] at hz; exact hz.2
  set Kt : Set Obj := C.MU ∩ V ∩ X.π ⁻¹' K with hKt
  have hdec := C.rep.MU_inter_preimage_eq_iUnion_quotient hΘ.isFunctorial
    C.toLocalBranchingStructure hBU a hVH (K := K) hK
  have hdisj := C.rep.pairwise_disjoint_image_Φ_out a hVU hVd (A := Kt)
    (fun z hz => hz.1.2)
  have hKtU : Kt ⊆ C.MU ∩ C.rep.U := fun z hz => ⟨hz.1.1, hMUU hz.1.1⟩
  have himgM : ∀ q : X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a,
      C.rep.Φ (Quotient.out q) '' Kt ⊆ C.MU := fun q => by
    refine Subset.trans ?_ (inter_subset_left (t := X.π ⁻¹' K))
    rw [hdec]
    exact subset_iUnion (fun q => C.rep.Φ (Quotient.out q) '' Kt) q
  have hinv : ∀ q : X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a,
      C.sheetSum 𝓘 ω (C.rep.Φ (Quotient.out q) '' Kt) = C.sheetSum 𝓘 ω Kt := fun q =>
    C.sheetSum_image 𝓘 C hΘ hT hS hS hCT hCT (C.rep.isScDiffeoOn_Φ _)
      (C.rep.isMorTangentOn_Φ _) ω hKtU hKtm (himgM q)
  rw [← C.sheetSum_MU_inter, hdec, C.sheetSum_iUnion_fintype 𝓘 hS ω _
    (fun q => hKtm.image 𝓘 C C hS hS (C.rep.isScDiffeoOn_Φ _) (C.rep.isMorTangentOn_Φ _) hKtU)
    hdisj, Finset.sum_congr rfl fun q _ => hinv q, Finset.sum_const, Finset.card_univ,
    Nat.card_eq_fintype_card, nsmul_eq_mul]

/-- The same with an oriented tame structure `C'` at `y` on `V`:
`∑ σᵢ ∫_{Kᵢ} ω|Mᵢ = ♯(G_x/H) · ∑ σ'ⱼ ∫_{K̃ⱼ} ω|M'ⱼ` for measurable `K ⊆ |M_V|`. -/
theorem sheetSum_preimage_eq_card_mul (hΘ : X.IsBranchedEpSubgroupoid Θ)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T) (hS : ∀ i, C.M i ∈ S)
    (hCT : C.Represents T) (a : C.rep.U) {V : Set Obj} (hVo : IsOpen V) (hVU : V ⊆ C.rep.U)
    (hVH : ∀ g ∈ MulAction.stabilizer (X.Isotropy x) a, C.rep.Φ g '' V = V)
    (hVd : ∀ g ∉ MulAction.stabilizer (X.Isotropy x) a, Disjoint (C.rep.Φ g '' V) V)
    (C' : X.OrientedTameStructure n Θ (a : Obj)) (hC'U : C'.U = V) (hS' : ∀ i, C'.M i ∈ S)
    (hC'T : C'.Represents T) (ω : Ω) {K : Set X.OrbitSpace} (hK : K ⊆ X.π '' C'.MU)
    (hKm : C.IsMeas G (X.π ⁻¹' K)) :
    C.sheetSum 𝓘 ω (X.π ⁻¹' K) =
      (Nat.card (X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a) : ℝ) *
        C'.sheetSum 𝓘 ω (X.π ⁻¹' K) := by
  have hBU : C.U = C.rep.U := C.U_eq
  have hMU' : C'.MU = C.MU ∩ V := by
    rw [LocalBranchingStructure.MU_eq, LocalBranchingStructure.MU_eq, hC'U, hBU, inter_assoc,
      inter_eq_right.2 hVU]
  have hKtm : C.IsMeas G (C.MU ∩ V ∩ X.π ⁻¹' K) := fun i => by
    have h1 : G.IsMeasIn (C.M i) (V ∩ X.π ⁻¹' K) :=
      (SheetNullSets.isMeasIn_of_borel (MeasurableSpace.measurableSet_generateFrom hVo)).inter
        (hKm i)
    refine h1.congr_inter ?_
    rw [inter_assoc C.MU V, C.MU_inter_inter]
  have h2 : C'.sheetSum 𝓘 ω (X.π ⁻¹' K) = C.sheetSum 𝓘 ω (C.MU ∩ V ∩ X.π ⁻¹' K) := by
    rw [← C'.sheetSum_MU_inter, hMU']
    exact (C.sheetSum_eq_of_represents 𝓘 C' hΘ hS hS' hCT hC'T ω
      (fun z hz => ⟨hz.1.1, by rw [hMU']; exact hz.1⟩) hKtm).symm
  rw [C.sheetSum_preimage_eq_card_mul_slice 𝓘 hΘ hT hS hCT a hVU hVH hVd ω
    (by rw [← hMU']; exact hK) hKtm, h2]

theorem inv_mul_mul_eq {a b c : ℕ} (h : a * b = c) (hb : 0 < b) (hc : 0 < c) (s : ℝ) :
    (c : ℝ)⁻¹ * ((a : ℝ) * s) = (b : ℝ)⁻¹ * s := by
  have ha : (a : ℝ) ≠ 0 := by
    rintro h0
    have : a = 0 := by exact_mod_cast h0
    rw [this, zero_mul] at h
    omega
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hcab : (c : ℝ) = a * b := by exact_mod_cast h.symm
  rw [hcab]
  field_simp

/-- **Lemma 9.5.9 (Restrictions in the `G_x`-case), 2021 p. 442 (2017: Lemma 9.18)**: let
`U = U(x)` carry the natural `G_x`-action and an oriented tame local branching structure `C`, let
`y ∈ U` with stabilizer `H ≅ G_y`, and let `V = V(y) ⊆ U` be small (`ϕ_g(V) = V` for `g ∈ H`,
`ϕ_g(V) ∩ V = ∅` for `g ∉ H`) with an oriented tame structure `C'` at `y` on `V`; both describe
`T̂Θ`.  Then `μ_ω^U(K) = μ_ω^V(K)` for every measurable `K ⊆ |M_V|`. -/
theorem lemma_9_5_9 (hΘ : X.IsBranchedEpSubgroupoid Θ) {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hT : X.IsOrientation Θ T) (hS : ∀ i, C.M i ∈ S) (hCT : C.Represents T) (a : C.rep.U)
    {V : Set Obj} (hVo : IsOpen V) (hVU : V ⊆ C.rep.U)
    (hVH : ∀ g ∈ MulAction.stabilizer (X.Isotropy x) a, C.rep.Φ g '' V = V)
    (hVd : ∀ g ∉ MulAction.stabilizer (X.Isotropy x) a, Disjoint (C.rep.Φ g '' V) V)
    (C' : X.OrientedTameStructure n Θ (a : Obj)) (hC'U : C'.U = V) (hS' : ∀ i, C'.M i ∈ S)
    (hC'T : C'.Represents T) (ω : Ω) {K : Set X.OrbitSpace} (hK : K ⊆ X.π '' C'.MU)
    (hKm : C.IsMeas G (X.π ⁻¹' K)) :
    C.localMeasure 𝓘 ω K = C'.localMeasure 𝓘 ω K := by
  have hfin : Finite (X.Isotropy x) := NatRepConstruction.finite_isotropy X x
  have hfin' : Finite (X.Isotropy (a : Obj)) := NatRepConstruction.finite_isotropy X _
  rw [localMeasure, localMeasure, C.sheetSum_preimage_eq_card_mul 𝓘 hΘ hT hS hCT a hVo hVU hVH
    hVd C' hC'U hS' hC'T ω hK hKm]
  exact inv_mul_mul_eq (C.rep.card_quotient_stabilizer_mul_card_isotropy a) Nat.card_pos
    Nat.card_pos _

/-- **Lemma 9.5.10 (Restrictions in the effective case), 2021 p. 444 (new in the 2021
edition)**: in the situation of Lemma 9.5.9, if `U(x)` has the property of Definition 7.2.18
(`NaturalRep.HasLUC`: `ĝ = id` as soon as `ĝ` is the identity on a nonempty open subset), then
`μ_ω^{eff,U}(K) = μ_ω^{eff,V}(K)` for every measurable `K ⊆ |M_V|`; the proof replaces
`♯R = ♯G/♯H` by (9.23), `♯R = ♯G_x^eff/♯H_y^eff`. -/
theorem lemma_9_5_10 (hΘ : X.IsBranchedEpSubgroupoid Θ) {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hT : X.IsOrientation Θ T) (hS : ∀ i, C.M i ∈ S) (hCT : C.Represents T)
    (hL : C.rep.HasLUC) (a : C.rep.U)
    {V : Set Obj} (hVo : IsOpen V) (hVU : V ⊆ C.rep.U)
    (hVH : ∀ g ∈ MulAction.stabilizer (X.Isotropy x) a, C.rep.Φ g '' V = V)
    (hVd : ∀ g ∉ MulAction.stabilizer (X.Isotropy x) a, Disjoint (C.rep.Φ g '' V) V)
    (C' : X.OrientedTameStructure n Θ (a : Obj)) (hC'U : C'.U = V) (hS' : ∀ i, C'.M i ∈ S)
    (hC'T : C'.Represents T) (ω : Ω) {K : Set X.OrbitSpace} (hK : K ⊆ X.π '' C'.MU)
    (hKm : C.IsMeas G (X.π ⁻¹' K)) :
    C.localMeasureEff 𝓘 ω K = C'.localMeasureEff 𝓘 ω K := by
  have hfin : ∀ z : Obj, Finite (X.EffIsotropy z) := fun z =>
    haveI : Finite (X.Isotropy z) := NatRepConstruction.finite_isotropy X z
    Finite.of_equiv _ (X.effIsotropyEquiv z).toEquiv.symm
  have := hfin x
  have := hfin (a : Obj)
  rw [localMeasureEff, localMeasureEff, C.sheetSum_preimage_eq_card_mul 𝓘 hΘ hT hS hCT a hVo hVU
    hVH hVd C' hC'U hS' hC'T ω hK hKm]
  exact inv_mul_mul_eq (C.rep.card_quotient_stabilizer_mul_card_effIsotropy hL a) Nat.card_pos
    Nat.card_pos _

end Restriction

/-! ### Lemma 9.5.11 -/

section Morphism

variable {x x' : Obj} (C : X.OrientedTameStructure n Θ x) (C' : X.OrientedTameStructure n Θ x')
  {f f' : Obj → Obj}

/-- The sums of two structures related by an sc-diffeomorphism `U → U'` given by morphisms
agree on the preimages of every measurable `K`. -/
theorem sheetSum_preimage_eq_of_morDiffeo (hΘ : X.IsBranchedEpSubgroupoid Θ)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T) (hS : ∀ i, C.M i ∈ S)
    (hS' : ∀ i, C'.M i ∈ S) (hCT : C.Represents T) (hC'T : C'.Represents T)
    (hf : X.PObj.IsScDiffeoOn X.PObj f f' C.U C'.U) (hmor : X.IsMorTangentOn hf C.U) (ω : Ω)
    {K : Set X.OrbitSpace} (hKm : C.IsMeas G (X.π ⁻¹' K)) :
    C.sheetSum 𝓘 ω (X.π ⁻¹' K) = C'.sheetSum 𝓘 ω (X.π ⁻¹' K) := by
  have hrel : ∀ w ∈ C.U, Θ (f w) = Θ w ∧ X.π (f w) = X.π w := fun w hw => by
    obtain ⟨ψ, hsrc, htgt, -⟩ := hmor w hw
    have h1 := hΘ.isFunctorial ψ
    rw [hsrc, htgt] at h1
    exact ⟨h1.symm, ((X.π_eq_π_iff).2 ⟨ψ, hsrc, htgt⟩).symm⟩
  set A : Set Obj := C.MU ∩ X.π ⁻¹' K with hA
  have himg : f '' A = C'.MU ∩ X.π ⁻¹' K := by
    ext z
    rw [hA, LocalBranchingStructure.MU_eq, LocalBranchingStructure.MU_eq]
    constructor
    · rintro ⟨w, ⟨⟨hws, hwU⟩, hwK⟩, rfl⟩
      obtain ⟨h1, h2⟩ := hrel w hwU
      refine ⟨⟨?_, hf.mapsTo hwU⟩, ?_⟩
      · change 0 < Θ (f w); rw [h1]; exact hws
      · rw [mem_preimage, h2]; exact hwK
    · rintro ⟨⟨hzs, hzU⟩, hzK⟩
      have hw : f' z ∈ C.U := hf.symm.mapsTo hzU
      have hfz : f (f' z) = z := hf.right_inv z hzU
      obtain ⟨h1, h2⟩ := hrel (f' z) hw
      rw [hfz] at h1 h2
      refine ⟨f' z, ⟨⟨?_, hw⟩, ?_⟩, hfz⟩
      · change 0 < Θ (f' z); rw [← h1]; exact hzs
      · rw [mem_preimage, ← h2]; exact hzK
  have hAm : C.IsMeas G A := fun i =>
    (hKm i).congr_inter (C.MU_inter_inter _ i).symm
  have hAU : A ⊆ C.MU ∩ C.U := fun z hz => by
    have := hz.1
    rw [LocalBranchingStructure.MU_eq] at this
    exact ⟨hz.1, this.2⟩
  rw [← C.sheetSum_MU_inter, ← C'.sheetSum_MU_inter, ← himg]
  exact (C.sheetSum_image 𝓘 C' hΘ hT hS hS' hCT hC'T hf hmor ω hAU hAm
    (by rw [himg]; exact inter_subset_left)).symm

/-- **Lemma 9.5.11 (Morphism Invariance), 2021 p. 445 (2017: Lemma 9.19)**: let `φ̂ : U → U'`
be an sc-diffeomorphism between the domains of two oriented tame structures at `x` and `x'`
describing `T̂Θ`, with `φ̂(x) = x'` and with the tangent maps of morphisms `w → φ̂(w)` (the
natural local sc-diffeomorphism of a morphism `φ : x → x'`).  Then `μ_ω^U(K) = μ_ω^{U'}(K)` and
`μ_ω^{eff,U}(K) = μ_ω^{eff,U'}(K)` for every measurable `K`. -/
theorem lemma_9_5_11 (hΘ : X.IsBranchedEpSubgroupoid Θ)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T) (hS : ∀ i, C.M i ∈ S)
    (hS' : ∀ i, C'.M i ∈ S) (hCT : C.Represents T) (hC'T : C'.Represents T)
    (hf : X.PObj.IsScDiffeoOn X.PObj f f' C.U C'.U) (hmor : X.IsMorTangentOn hf C.U)
    (hfx : f x = x') (ω : Ω) {K : Set X.OrbitSpace} (hKm : C.IsMeas G (X.π ⁻¹' K)) :
    C.localMeasure 𝓘 ω K = C'.localMeasure 𝓘 ω K ∧
      C.localMeasureEff 𝓘 ω K = C'.localMeasureEff 𝓘 ω K := by
  obtain ⟨ψ, hsrc, htgt, -⟩ := hmor x C.mem_U
  rw [hfx] at htgt
  have h := C.sheetSum_preimage_eq_of_morDiffeo 𝓘 C' hΘ hT hS hS' hCT hC'T hf hmor ω hKm
  exact ⟨by rw [localMeasure, localMeasure, h, card_isotropy_eq_of_mor ψ hsrc htgt],
    by rw [localMeasureEff, localMeasureEff, h, card_effIsotropy_eq_of_mor ψ hsrc htgt]⟩

end Morphism

end OrientedTameStructure

end EpGroupoid

end Polyfold
