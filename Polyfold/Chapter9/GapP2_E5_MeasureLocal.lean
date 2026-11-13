import Polyfold.Chapter9.GapP2_E1_BranchedIntegral
import Polyfold.Chapter9.GapP2_E2Stokes
import Polyfold.Chapter7.OrbitTopology

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, proof of Theorem 9.5.18, pp. 450–451 (gap G.110).  Numbers and pages are
the 2021 text's.

# The second equality of the display on p. 451

For `ω_k = β_k ω` with `supp β_k ⊆ U_k^*` the text writes
`μ_{dω_k}(S) = (1/♯G^{eff}_{x_k}) ∑_{i ∈ I_k} σᵢ ∫_{(Mᵢ,oᵢ)} dω_k`, the integrals over the whole
sheets.  Theorems 9.5.4 and 9.5.5 give the local formula for the measurable subsets of `|U_k|`
only; the step uses that the measure of a form vanishing on the sheets off a closed saturated
`C ⊆ U_k^*` is carried by `|C|`.

## What is formalized

For a linear map `Φ` into the signed measures on `(S, L(S))` with the local formula for a class of
oriented tame structures covering `supp Θ` (Theorems 9.5.4, 9.5.5: `c = 1/♯G_x`, `1/♯G_x^{eff}`):

* `signedMeasure_eq_zero_of_openCover`: a signed measure on a compact space vanishing on the
  measurable subsets of the members of an open cover is `0`.
* `measure_eq_zero_of_integ_eq_zero`: `Φ(ω)(D) = 0` if the integrals of `ω` over the parts of the
  sheets above `D` vanish.
* **`measure_univ_eq_of_integ_eq_zero`**: if the integrals of `ω` over the subsets of the sheets
  disjoint from a closed saturated `C ⊆ U(x)^*` vanish, then
  `Φ(ω)(S) = c(x) ∑ᵢ σᵢ ∫_{Mᵢ} ω|(Mᵢ, oᵢ)`.
* `isClosed_π_image`, `isSaturated_tsupport`: `|C|` is closed for `C` closed and saturated; the
  support of a function constant on the orbits is saturated.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

/-- **A signed measure on a compact space which vanishes on the measurable subsets of the members
of an open cover is zero.** -/
theorem signedMeasure_eq_zero_of_openCover {T : Type*} [TopologicalSpace T] [CompactSpace T]
    {m : MeasurableSpace T} (hm : borel T ≤ m) {J : Type*} (O : J → Set T)
    (hO : ∀ j, IsOpen (O j)) (hcov : ⋃ j, O j = univ) (ν : SignedMeasure T)
    (h : ∀ j K, MeasurableSet K → K ⊆ O j → ν K = 0) : ν = 0 := by
  obtain ⟨Φ, -, huniq⟩ := existsUnique_linearMap_signedMeasure_of_openCover (V := ℝ)
    hm O hO hcov (fun _ => 0) (fun _ _ _ _ _ _ => rfl)
  have h1 := huniq (LinearMap.toSpanSingleton ℝ _ ν) fun j t K hK hKO => by
    change t • ν K = 0
    rw [h j K hK hKO, smul_zero]
  have h2 := huniq 0 fun j t K hK hKO => rfl
  have h3 := congrArg (fun L : ℝ →ₗ[ℝ] SignedMeasure T => L 1) (h1.trans h2.symm)
  simpa using h3

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- `|C|` is closed in `|X|` for `C` closed and saturated (`π` is open). -/
theorem isClosed_π_image {C : Set Obj} (hC : IsClosed C) (hsat : X.IsSaturated C) :
    IsClosed (X.π '' C) := by
  have hcompl : (X.π '' C)ᶜ = X.π '' Cᶜ := by
    ext p
    obtain ⟨y, rfl⟩ := X.surjective_π p
    constructor
    · intro hp
      exact ⟨y, fun hy => hp ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨z, hz, hzy⟩ ⟨c, hc, hcy⟩
      exact hz (hsat ▸ (⟨c, hc, hcy.trans hzy.symm⟩ : z ∈ X.π ⁻¹' (X.π '' C)))
  rw [← isOpen_compl_iff, hcompl]
  exact X.proposition_7_1_8 _ hC.isOpen_compl

/-- **The support of a function constant on the orbits is saturated** (2021 p. 451:
`supp β_k ⊆ U_k^*`). -/
theorem isSaturated_tsupport {β : Obj → ℝ} (hinv : ∀ φ : Mor, β (X.src φ) = β (X.tgt φ)) :
    X.IsSaturated (tsupport β) := by
  have hs : X.π ⁻¹' (X.π '' Function.support β) = Function.support β := by
    refine Subset.antisymm ?_ (subset_preimage_image _ _)
    rintro y ⟨z, hz, hzy⟩
    obtain ⟨φ, hsrc, htgt⟩ := X.π_eq_π_iff.1 hzy
    have := hinv φ
    rw [hsrc, htgt] at this
    exact fun h0 => hz (this.trans h0)
  have hcl : tsupport β = X.π ⁻¹' closure (X.π '' Function.support β) := by
    rw [X.proposition_7_1_8.preimage_closure_eq_closure_preimage X.continuous_π, hs]
    rfl
  change X.π ⁻¹' (X.π '' tsupport β) = tsupport β
  refine Subset.antisymm ?_ (subset_preimage_image _ _)
  rintro y ⟨z, hz, hzy⟩
  rw [hcl] at hz ⊢
  have hz' : X.π z ∈ closure (X.π '' Function.support β) := hz
  rw [hzy] at hz'
  exact hz'

variable {S : Set (Set Obj)} {G : SheetNullSets S} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω]
  (𝓘 : X.SheetIntegration G Ω) {n : ℕ} {Θ : Obj → ℚ}
  (Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp Θ) (X.lebesgueSigma G Θ)) (c : Obj → ℝ)
  (Good : ∀ x, X.OrientedTameStructure n Θ x → Prop)

open OrientedTameStructure

include 𝓘 in
/-- **The measure of a form whose integrals over the parts of the sheets above `D` vanish**: for
`Φ` with the local formula (Theorems 9.5.4, 9.5.5) for the structures of a class covering
`supp Θ`, and a measurable `D ⊆ S`: `Φ(ω)(D) = 0`. -/
theorem measure_eq_zero_of_integ_eq_zero (hcpt : X.IsCompactBranched Θ)
    (hcov : ∀ x ∈ supp Θ, ∃ C, Good x C)
    (hΦ : ∀ (ω : Ω) (x : Obj) (C : X.OrientedTameStructure n Θ x), Good x C →
      ∀ K : Set (X.orbitSupp Θ), MeasurableSet[X.lebesgueSigma G Θ] K →
        Subtype.val '' K ⊆ X.π '' C.U →
        Φ ω K = c x * C.sheetSum 𝓘 ω (X.π ⁻¹' (Subtype.val '' K)))
    (ω : Ω) {D : Set (X.orbitSupp Θ)} (hD : MeasurableSet[X.lebesgueSigma G Θ] D)
    (h0 : ∀ (x : Obj) (C : X.OrientedTameStructure n Θ x), Good x C → ∀ i, ∀ A : Set Obj,
      A ⊆ C.M i ∩ X.π ⁻¹' (Subtype.val '' D) →
      𝓘.integ ω (C.M i) (C.orient i).tangent A = 0) :
    Φ ω D = 0 := by
  let _ : MeasurableSpace (X.orbitSupp Θ) := X.lebesgueSigma G Θ
  have : CompactSpace (X.orbitSupp Θ) := isCompact_iff_compactSpace.1 hcpt
  let J := {j : Σ x, X.OrientedTameStructure n Θ x // Good j.1 j.2}
  let O : J → Set (X.orbitSupp Θ) := fun j => Subtype.val ⁻¹' (X.π '' j.1.2.U)
  have hO : ∀ j, IsOpen (O j) := fun j =>
    (X.proposition_7_1_8 _ j.1.2.isOpen_U).preimage continuous_subtype_val
  have hcovO : ⋃ j, O j = univ := eq_univ_of_forall fun q => by
    obtain ⟨y, hy, hyq⟩ := q.2
    obtain ⟨C, hC⟩ := hcov y hy
    exact mem_iUnion.2 ⟨⟨⟨y, C⟩, hC⟩, y, C.mem_U, hyq⟩
  have hν : (Φ ω).restrict D = 0 :=
    signedMeasure_eq_zero_of_openCover (borel_le_borelNullSigma _) O hO hcovO _
      fun j K hK hKO => by
        rw [VectorMeasure.restrict_apply _ hD hK,
          hΦ ω j.1.1 j.1.2 j.2 (K ∩ D) (hK.inter hD)
            (by rintro _ ⟨q, hq, rfl⟩; exact hKO hq.1), sheetSum]
        rw [Finset.sum_eq_zero fun i _ => ?_, mul_zero]
        rw [h0 j.1.1 j.1.2 j.2 i _ fun y hy =>
          ⟨hy.2, image_mono inter_subset_right hy.1⟩, mul_zero]
  have h := congrArg (fun ν : SignedMeasure (X.orbitSupp Θ) => ν univ) hν
  simpa using h

include 𝓘 in
/-- **The second equality of the display on p. 451**: let `Φ` have the local formula for the
structures of a class covering `supp Θ`, with sheets in `S`, `C` one of them at `x`, and let
`Z ⊆ U(x)^*` be closed and saturated such that the integrals of `ω` over the subsets of the
sheets disjoint from `Z` vanish.  Then
`Φ(ω)(S) = c(x) ∑ᵢ σᵢ ∫_{Mᵢ} ω|(Mᵢ, oᵢ)`. -/
theorem measure_univ_eq_of_integ_eq_zero (hcpt : X.IsCompactBranched Θ)
    (hGS : ∀ x C, Good x C → ∀ i, C.M i ∈ S)
    (hcov : ∀ x ∈ supp Θ, ∃ C, Good x C)
    (hΦ : ∀ (ω : Ω) (x : Obj) (C : X.OrientedTameStructure n Θ x), Good x C →
      ∀ K : Set (X.orbitSupp Θ), MeasurableSet[X.lebesgueSigma G Θ] K →
        Subtype.val '' K ⊆ X.π '' C.U →
        Φ ω K = c x * C.sheetSum 𝓘 ω (X.π ⁻¹' (Subtype.val '' K)))
    (ω : Ω) {x : Obj} (C : X.OrientedTameStructure n Θ x) (hC : Good x C) {Z : Set Obj}
    (hZ : IsClosed Z) (hsat : X.IsSaturated Z) (hZU : Z ⊆ X.π ⁻¹' (X.π '' C.U))
    (h0 : ∀ (x' : Obj) (C' : X.OrientedTameStructure n Θ x'), Good x' C' → ∀ i, ∀ A : Set Obj,
      A ⊆ C'.M i → Disjoint A Z → 𝓘.integ ω (C'.M i) (C'.orient i).tangent A = 0) :
    Φ ω univ = c x * ∑ i, (C.σ i : ℝ) * 𝓘.integ ω (C.M i) (C.orient i).tangent (C.M i) := by
  let _ : MeasurableSpace (X.orbitSupp Θ) := X.lebesgueSigma G Θ
  have hTS : X.HasTameSheetsIn S Θ := fun y hy => by
    obtain ⟨C', hC'⟩ := hcov y hy
    exact ⟨C'.toTameBranchingStructure, hGS y C' hC'⟩
  set D : Set (X.orbitSupp Θ) := Subtype.val ⁻¹' (X.π '' Z) with hDdef
  have hDc : IsClosed D := (isClosed_π_image hZ hsat).preimage continuous_subtype_val
  have hD : MeasurableSet D :=
    borel_le_borelNullSigma _ _ (@MeasurableSet.of_compl _ D (borel _)
      (MeasurableSpace.measurableSet_generateFrom hDc.isOpen_compl))
  -- the part off `|Z|`
  have h2 : Φ ω Dᶜ = 0 :=
    measure_eq_zero_of_integ_eq_zero 𝓘 Φ c Good hcpt hcov hΦ ω hD.compl
      fun x' C' hC' i A hA => h0 x' C' hC' i A (fun y hy => (hA hy).1)
        (Set.disjoint_left.2 fun y hyA hyZ => by
          obtain ⟨q, hq, hqy⟩ := (hA hyA).2
          exact hq (show q.1 ∈ X.π '' Z from hqy ▸ ⟨y, hyZ, rfl⟩))
  -- the part over `|Z|`
  have hDU : Subtype.val '' D ⊆ X.π '' C.U := by
    rintro _ ⟨q, ⟨z, hz, hzq⟩, rfl⟩
    rw [← hzq]
    exact hZU hz
  have h1 : Φ ω D = c x * C.sheetSum 𝓘 ω (X.π ⁻¹' (Subtype.val '' D)) := hΦ ω x C hC D hD hDU
  have hsplit : Φ ω univ = Φ ω D + Φ ω Dᶜ := by
    rw [← VectorMeasure.of_union disjoint_compl_right hD hD.compl, union_compl_self]
  rw [hsplit, h2, add_zero, h1, sheetSum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  set P : Set Obj := X.π ⁻¹' (Subtype.val '' D) with hP
  have hPm : G.IsMeasIn (C.M i) P := C.isMeas_preimage hTS (hGS x C hC) hD i
  have hPc : G.IsMeasIn (C.M i) Pᶜ := MeasurableSet.compl hPm
  have hun : C.M i = (P ∩ C.M i) ∪ (Pᶜ ∩ C.M i) := by
    rw [← union_inter_distrib_right, union_compl_self, univ_inter]
  have hz : 𝓘.integ ω (C.M i) (C.orient i).tangent (Pᶜ ∩ C.M i) = 0 :=
    h0 x C hC i _ inter_subset_right (Set.disjoint_left.2 fun y hy hyZ => hy.1 (by
      have hys : y ∈ supp Θ := C.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp i hy.2
      exact ⟨⟨X.π y, y, hys, rfl⟩, ⟨y, hyZ, rfl⟩, rfl⟩))
  have e : 𝓘.integ ω (C.M i) (C.orient i).tangent (C.M i) =
      𝓘.integ ω (C.M i) (C.orient i).tangent ((P ∩ C.M i) ∪ (Pᶜ ∩ C.M i)) :=
    congrArg (𝓘.integ ω (C.M i) (C.orient i).tangent) hun
  rw [e, 𝓘.integ_union ω (hGS x C hC i) (C.orient i) inter_subset_right inter_subset_right
    (SheetNullSets.isMeasIn_inter_iff.2 hPm) (SheetNullSets.isMeasIn_inter_iff.2 hPc)
    (Set.disjoint_left.2 fun y hy hy' => hy'.1 hy.1), hz, add_zero]

end EpGroupoid

end Polyfold
