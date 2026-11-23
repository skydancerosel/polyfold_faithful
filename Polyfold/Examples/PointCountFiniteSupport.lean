import Polyfold.Chapter16.IndexZeroAllAdmissible

/-!
# The weighted signed count over a finite orbit support

Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §9.5, Definition 9.5.6
(p. 439) for `n = 0`, with Theorem 9.5.4: the branched integral of a `0`-form over an oriented
tame compact branched ep⁺-subgroupoid of dimension `0` whose orbit support is finite.

## What is formalized

* `EpGroupoid.signedWeight t`: for `t = ∑ σᵢ · (Lᵢ, oᵢ)` of dimension `0`, the number
  `∑ σᵢ · sign(oᵢ)` (`frameSign`).
* `OrientedTameStructure.sheetSum_point`, `localMeasure_point`: for a structure at `x` with point
  sheets representing `T`, the local measure of a set containing `|x|` is
  `(1/♯G_x) · signedWeight (T x) · ω(x)`.
* `signedMeasure_coe_finset`: a signed measure of a finite set is the sum over its points.
* **`EP.pointBranchedIntegral_eq_sum`**: if the orbit support of `Θ` is `{|x| : x ∈ s}` for a
  finite set `s` of points of the support, injective into the orbit space, then
  `∫_Θ̂ ω = ∑_{x ∈ s} (1/♯G_x) · signedWeight (T x) · ω(x)`.
* `SBLocalization.PointSolution.count_eq_sum`: the same for the count of a point solution set.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- **The signed weight** `∑ σᵢ · sign(oᵢ)` of a formal sum `∑ σᵢ · (Lᵢ, oᵢ)` of oriented
tangent sets (the signs are those of dimension `0`, `frameSign`). -/
def signedWeight (t : X.PObj.OrTangent →₀ ℚ) : ℝ :=
  t.sum fun g q => (q : ℝ) * frameSign (X := X) g

theorem signedWeight_single (g : X.PObj.OrTangent) (q : ℚ) :
    signedWeight (X := X) (Finsupp.single g q) = (q : ℝ) * frameSign (X := X) g := by
  unfold signedWeight
  rw [Finsupp.sum_single_index]
  rw [Rat.cast_zero, zero_mul]

theorem signedWeight_sum {ι : Type*} (s : Finset ι) (t : ι → X.PObj.OrTangent →₀ ℚ) :
    signedWeight (X := X) (∑ i ∈ s, t i) = ∑ i ∈ s, signedWeight (X := X) (t i) := by
  unfold signedWeight
  exact Finsupp.sum_finsetSum_index (fun g => by rw [Rat.cast_zero, zero_mul])
    (fun g a b => by rw [Rat.cast_add, add_mul]) |>.symm

end EpGroupoid

/-- **A signed measure of a finite set is the sum over its points**, when the points are
measurable. -/
theorem signedMeasure_coe_finset {α : Type*} [MeasurableSpace α] (μ : SignedMeasure α)
    (s : Finset α) (h : ∀ p ∈ s, MeasurableSet ({p} : Set α)) :
    μ (↑s : Set α) = ∑ p ∈ s, μ {p} := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs : MeasurableSet (↑s : Set α) := by
      have e : (↑s : Set α) = ⋃ p ∈ s, {p} := by
        ext q
        simp
      rw [e]
      exact Finset.measurableSet_biUnion s fun p hp => h p (Finset.mem_insert_of_mem hp)
    rw [Finset.coe_insert, Set.insert_eq, VectorMeasure.of_union
      (Set.disjoint_singleton_left.2 (by simpa using ha)) (h a (Finset.mem_insert_self a s)) hs,
      Finset.sum_insert ha, ih fun p hp => h p (Finset.mem_insert_of_mem hp)]

namespace EP

open EpGroupoid

variable (A : EP.{u}) {Θ : A.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}

/-- **The sheet sum of a structure with point sheets**: every sheet is `{x}`, and
`∑ σᵢ ∫_{B ∩ Mᵢ} ω|(Mᵢ, oᵢ) = signedWeight (T x) · ω(x)` for `B ∋ x`. -/
theorem sheetSum_point {x : A.Obj} (hx : x ∈ A.X.PObj.smoothSet)
    (C : A.X.OrientedTameStructure 0 Θ x) (hS : ∀ i, C.M i ∈ pointSheets A.X)
    (hCT : C.Represents T) (ω : A.epFormsInfty 0) {B : Set A.Obj} (hB : x ∈ B) :
    C.sheetSum A.zeroFormIntegration ω B = signedWeight (T x) * A.zeroFormEval ω x := by
  classical
  have hM : ∀ i, C.M i = {x} := fun i => by
    rcases hS i with h | ⟨p, -, h⟩
    · exact absurd (C.mem_M i) (by rw [h]; exact notMem_empty x)
    · have hxp : x = p := by
        have := C.mem_M i
        rw [h] at this
        exact this
      rw [h, hxp]
  have hT : T x = ∑ i, Finsupp.single ((C.orient i).tangent x) (C.σ i) := by
    rw [hCT x C.mem_U hx, C.orientedSum_eq_sum_ite]
    exact Finset.sum_congr rfl fun i _ => if_pos (C.mem_M i)
  rw [hT, signedWeight_sum, Finset.sum_mul]
  unfold OrientedTameStructure.sheetSum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [signedWeight_single, A.zeroFormIntegration_integ,
    EpGroupoid.pointInteg_of_mem (by rw [hM i]; exact subsingleton_singleton)
      (⟨⟨hB, C.mem_M i⟩, C.mem_M i⟩ : x ∈ (B ∩ C.M i) ∩ C.M i), mul_assoc]

/-- **The local measure of a structure with point sheets**:
`μ_ω^{U(x)}(K) = (1/♯G_x) · signedWeight (T x) · ω(x)` for `K ∋ |x|`. -/
theorem localMeasure_point {x : A.Obj} (hx : x ∈ A.X.PObj.smoothSet)
    (C : A.X.OrientedTameStructure 0 Θ x) (hS : ∀ i, C.M i ∈ pointSheets A.X)
    (hCT : C.Represents T) (ω : A.epFormsInfty 0) {K : Set A.X.OrbitSpace} (hK : A.X.π x ∈ K) :
    C.localMeasure A.zeroFormIntegration ω K =
      (Nat.card (A.X.Isotropy x) : ℝ)⁻¹ * (signedWeight (T x) * A.zeroFormEval ω x) := by
  unfold OrientedTameStructure.localMeasure
  rw [A.sheetSum_point hx C hS hCT ω (show x ∈ A.X.π ⁻¹' K from hK)]

/-- **Definition 9.5.6 (1), 2021 p. 439, for `n = 0` and a finite orbit support**: let `Θ̂` be an
oriented tame compact branched ep⁺-subgroupoid of dimension `0` whose orbit support is
`{|x| : x ∈ s}` for a finite set `s` of points of `supp Θ` with pairwise different orbits.  Then
`∫_Θ̂ ω = ∑_{x ∈ s} (1/♯G_x) · signedWeight (T x) · ω(x)`. -/
theorem pointBranchedIntegral_eq_sum (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T) (hloc : A.X.IsPointTame Θ T)
    (ω : A.epFormsInfty 0) (s : Finset A.Obj) (hs : ∀ x ∈ s, x ∈ supp Θ)
    (hinj : Set.InjOn A.X.π (↑s : Set A.Obj)) (hcov : A.X.orbitSupp Θ ⊆ A.X.π '' (↑s : Set A.Obj)) :
    A.pointBranchedIntegral hΘ hcpt hT hloc ω =
      ∑ x ∈ s, (Nat.card (A.X.Isotropy x) : ℝ)⁻¹ *
        (signedWeight (T x) * A.zeroFormEval ω x) := by
  classical
  have hborel : ∀ q : A.X.orbitSupp Θ,
      MeasurableSet[borel (A.X.orbitSupp Θ)] ({q} : Set (A.X.orbitSupp Θ)) := fun q => by
    have h : MeasurableSet[borel (A.X.orbitSupp Θ)] ({q}ᶜ : Set (A.X.orbitSupp Θ)) :=
      MeasurableSpace.measurableSet_generateFrom
        (show IsOpen ({q}ᶜ : Set (A.X.orbitSupp Θ)) from isOpen_compl_singleton)
    exact @MeasurableSet.of_compl _ _ (borel _) h
  let m : MeasurableSpace (A.X.orbitSupp Θ) :=
    A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X)) Θ
  let μ : @SignedMeasure (A.X.orbitSupp Θ) m :=
    branchedMeasure A.zeroFormIntegration hΘ hcpt hT hloc ω
  let p : {x // x ∈ s} → A.X.orbitSupp Θ := fun x => ⟨A.X.π x.1, ⟨x.1, hs x.1 x.2, rfl⟩⟩
  have hp : Injective p := fun x y h =>
    Subtype.ext (hinj x.2 y.2 (congrArg Subtype.val h))
  let s' : Finset (A.X.orbitSupp Θ) := s.attach.image p
  have huniv : (univ : Set (A.X.orbitSupp Θ)) = ↑s' := by
    refine (eq_univ_of_forall fun q => ?_).symm
    obtain ⟨x, hx, hq⟩ := hcov q.2
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨⟨x, hx⟩, Finset.mem_attach _ _,
      Subtype.ext hq⟩)
  have hmeas : ∀ q : A.X.orbitSupp Θ, MeasurableSet[m] ({q} : Set (A.X.orbitSupp Θ)) :=
    fun q => borel_le_borelNullSigma _ _ (hborel q)
  have hpt : ∀ x : {x // x ∈ s}, μ {p x} =
      (Nat.card (A.X.Isotropy x.1) : ℝ)⁻¹ *
        (signedWeight (T x.1) * A.zeroFormEval ω x.1) := by
    intro x
    obtain ⟨C, hS, hCT⟩ := hloc x.1 (hs x.1 x.2)
    have himg : Subtype.val '' ({p x} : Set (A.X.orbitSupp Θ)) = {A.X.π x.1} := by
      rw [image_singleton]
    have hKU : Subtype.val '' ({p x} : Set (A.X.orbitSupp Θ)) ⊆ A.X.π '' C.U := by
      rw [himg]
      exact singleton_subset_iff.2 ⟨x.1, C.mem_U, rfl⟩
    have h1 := A.pointBranchedMeasure_apply hΘ hcpt hT hloc ω C hS hCT (hmeas (p x)) hKU
    rw [himg] at h1
    exact h1.trans (A.localMeasure_point (hΘ.support_subset (hs x.1 x.2)) C hS hCT ω rfl)
  change μ univ = _
  rw [huniv, @signedMeasure_coe_finset _ m μ s' fun q _ => hmeas q,
    Finset.sum_image fun x _ y _ h => hp h]
  rw [Finset.sum_congr rfl fun x _ => hpt x]
  exact Finset.sum_attach s fun x => (Nat.card (A.X.Isotropy x) : ℝ)⁻¹ *
    (signedWeight (T x) * A.zeroFormEval ω x)

end EP

namespace SBLocalization

open EpGroupoid

variable {A : SEP.{u}} {f : A.Obj → A.W}

/-- **The count of a point solution set with finite orbit support**: if the orbit support of
`Θ = Λ ∘ f` is `{|x| : x ∈ s}` for a finite set `s` of perturbed solutions with pairwise
different orbits, then `∫_{(Λ ∘ f, T̂)} ω = ∑_{x ∈ s} (1/♯G_x) · signedWeight (T̂ x) · ω(x)`. -/
theorem PointSolution.count_eq_sum (P : PointSolution A f) (ω : A.baseEP.epFormsInfty 0)
    (s : Finset A.Obj) (hs : ∀ x ∈ s, 0 < P.Λ (f x))
    (hinj : Set.InjOn A.X.π (↑s : Set A.Obj))
    (hcov : ∀ y, 0 < P.Λ (f y) → ∃ x ∈ s, A.X.π x = A.X.π y) :
    P.count ω = ∑ x ∈ s, (Nat.card (A.X.Isotropy x) : ℝ)⁻¹ *
      (signedWeight (P.T x) * A.baseEP.zeroFormEval ω x) := by
  refine A.baseEP.pointBranchedIntegral_eq_sum P.isBranched P.isCompact P.isOrientation P.loc ω s
    (fun x hx => ?_) hinj ?_
  · change (0 : ℚ) < _
    exact_mod_cast hs x hx
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : (0 : ℚ) < (P.Λ (f y) : ℚ) := hy
    obtain ⟨x, hx, hxy⟩ := hcov y (by exact_mod_cast hy')
    exact ⟨x, hx, hxy⟩

end SBLocalization

end Polyfold
