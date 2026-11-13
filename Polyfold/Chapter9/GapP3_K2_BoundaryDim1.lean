import Polyfold.Chapter9.GapP3_K2_ZeroForms
import Polyfold.Chapter9.GapP2_E8_BoundaryLocal
import Polyfold.Chapter9.GapP2_E8F_FaceChange
import Polyfold.Chapter9.GapP2_E4_FiniteTheorem

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Theorems 9.5.15 and 9.5.16 for `n = 1`** (p. 449; 2017: Theorems
9.4, 9.5), gap G.109.  Numbers and pages are the 2021 text's.

# The boundary measures of a `1`-dimensional `Θ̂`

For `n = 1` the boundary sheets `∂₁Mᵢ` are `0`-dimensional: near every point of a
`1`-dimensional tame sheet the boundary stratum has at most one point (a corner chart of the
sheet takes values in `[0, ∞)`, and its face `{0}` is one point).  Restricting an oriented tame
structure into such neighbourhoods, its boundary sheets become empty or single smooth points,
which lie in the class `pointSheets` of E1's integration over oriented points.  So the class
condition of E7's Theorems 9.5.15/9.5.16 holds for `n = 1` as soon as every point has an oriented
tame structure describing `T̂Θ` (the reading of "oriented, tame" of gap G.107).

* `MPolyfold.boundaryStratum_inter_subset`: `∂₁(A ∩ V) ⊆ ∂₁A ∩ V` for open `V`.
* **`MPolyfold.exists_isOpen_boundaryStratum_subsingleton`**: a `1`-dimensional tame submanifold
  has, near each of its points, at most one point of its boundary stratum.
* `OrientedTameStructure.exists_restrict_open`: an oriented tame structure restricted into an
  open neighbourhood of `x` (the same `T̂Θ`, the same action).
* **`OrientedTameStructure.exists_boundarySheet_subsingleton`**: a structure of dimension `1`
  restricts to one whose boundary sheets have at most one point;
  `boundarySheet_mem_pointSheets`.
* **`hcov_dim1_of_loc`**, `hcovEff_dim1_of_loc`: E7's class hypothesis for `n = 1`, from the
  existence of oriented tame structures describing `T̂Θ`.
* **`theorem_9_5_15_dim1`, `theorem_9_5_16_dim1`**: Theorems 9.5.15 and 9.5.16 for `n = 1`, for
  the `0`-forms `Ω⁰_{ep,∞}(X)` integrated over the oriented boundary points
  (`EP.zeroFormIntegration`), with no class hypothesis.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

/-! ### At most one boundary point near each point of a `1`-dimensional sheet -/

namespace MPolyfold

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {P : MPolyfold Z}

/-- `∂₁(A ∩ V) ⊆ ∂₁A ∩ V` for an open `V`. -/
theorem boundaryStratum_inter_subset {A V : Set Z} (hV : IsOpen V) :
    P.boundaryStratum (A ∩ V) ⊆ P.boundaryStratum A ∩ V := by
  rintro y ⟨⟨hyA, hyV⟩, h⟩
  exact ⟨⟨hyA, fun c => by rw [← submanifoldTangent_inter_isOpen hV hyV]; exact h c⟩, hyV⟩

/-- **Near each point of a `1`-dimensional tame submanifold `M` there is at most one point of the
boundary stratum `∂₁M`**: in corner coordinates `κ` of `M` (values in `[0, ∞)`), every point of
`∂₁M` in `dom κ` is `κ⁻¹(0)` (E8F's `exists_facePt_of_mem_boundaryStratum`, with the face
parameters in `ℝ⁰`). -/
theorem exists_isOpen_boundaryStratum_subsingleton {M : Set Z} (hM : P.IsSubmanifoldOfDim M (0 + 1))
    (ht : P.HasTameInducedStructure M) {x : Z} (hx : x ∈ M) :
    ∃ W : Set Z, IsOpen W ∧ x ∈ W ∧ (P.boundaryStratum M ∩ W).Subsingleton := by
  let _ := P.paracompactSpace_subtype M
  have hcs := hM.hasCornerStructureOfDim_of_hasTameInducedStructure ht
  set κ := hcs.coords ⟨x, hx⟩ with hκ
  obtain ⟨W, hW, hWκ⟩ := isOpen_induced_iff.1 κ.isOpen_s
  have hmem : ∀ {y : Z} (hyM : y ∈ M), y ∈ W → (⟨y, hyM⟩ : M) ∈ κ.s := fun {y} hyM hyW => by
    rw [← hWκ]; exact hyW
  have hE : ∀ u u' : EuclideanSpace ℝ (Fin 0), u = u' := fun u u' => by
    ext i; exact i.elim0
  refine ⟨W, hW, ?_, ?_⟩
  · have h := hcs.mem_coords ⟨x, hx⟩
    rw [← hκ, ← hWκ] at h
    exact h
  · rintro y ⟨hyb, hyW⟩ y' ⟨hy'b, hy'W⟩
    obtain ⟨l, u, hu, hyu⟩ := exists_facePt_of_mem_boundaryStratum hM.1 ht κ (hmem hyb.1 hyW) hyb
    obtain ⟨l', u', hu', hyu'⟩ :=
      exists_facePt_of_mem_boundaryStratum hM.1 ht κ (hmem hy'b.1 hy'W) hy'b
    have hl : l = l' := Fin.ext (by have := l.isLt; have := l'.isLt; omega)
    subst hl
    rw [hE u u'] at hyu
    exact congrArg Subtype.val (hyu.symm.trans hyu')

end MPolyfold

namespace EpGroupoid

open MPolyfold

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ}

namespace OrientedTameStructure

open scoped Classical in
/-- **An oriented tame structure restricted into an open neighbourhood `W` of `x`**: it describes
the same `T̂Θ`, and the natural action is the restriction of the given one (E8's
`exists_restrict_subset` without a class of sheets). -/
theorem exists_restrict_open {n : ℕ} {x : Obj} (C₀ : X.OrientedTameStructure n Θ x)
    (hC₀ : C₀.Represents T) {W : Set Obj} (hWo : IsOpen W) (hxW : x ∈ W) :
    ∃ C : X.OrientedTameStructure n Θ x, C.Represents T ∧ C.U ⊆ W ∧ C.rep.U ⊆ C₀.rep.U ∧
      C.rep.Φ = C₀.rep.Φ ∧ ∃ V : Set Obj, IsOpen V ∧ ∀ i, ∃ j, C.M i = C₀.M j ∩ V := by
  obtain ⟨R', hR'sub, hR'Φ, -⟩ := exists_naturalRep_shrink X C₀.rep hWo hxW
  have hsubU : R'.U ⊆ C₀.U := fun y hy => C₀.U_eq ▸ (hR'sub hy).2
  let C : X.OrientedTameStructure n Θ x :=
    { toLocalBranchingStructure :=
        C₀.toLocalBranchingStructure.restrict R'.isOpen_U R'.mem_U hsubU
      rep := R'
      U_eq := rfl
      hasPropernessProperty := C₀.hasPropernessProperty.mono R'.isOpen_U hsubU
      hasTameInducedStructure := fun i =>
        FormEval.tameOpen X _ _ (C₀.isSmoothSubmanifold i) (C₀.hasTameInducedStructure i)
          R'.isOpen_U
      isSubmanifoldOfDim := fun i => (C₀.isSubmanifoldOfDim i).inter_isOpen R'.isOpen_U
      orient := fun i => (C₀.orient i).restrict R'.isOpen_U }
  refine ⟨C, fun y hy hys => ?_, fun y hy => (hR'sub hy).1, fun y hy => (hR'sub hy).2, hR'Φ,
    R'.U, R'.isOpen_U, fun i => ⟨i, rfl⟩⟩
  have hyU' : y ∈ R'.U := hy
  rw [hC₀ y (hsubU hy) hys, C₀.orientedSum_eq_sum_ite, C.orientedSum_eq_sum_ite]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hiff : y ∈ C.M i ↔ y ∈ C₀.M i := ⟨fun h => h.1, fun h => ⟨h, hyU'⟩⟩
  have ht : (C.orient i).tangent y = (C₀.orient i).tangent y :=
    (C₀.orient i).restrict_tangent R'.isOpen_U hyU'
  by_cases h : y ∈ C₀.M i
  · rw [if_pos h, if_pos (hiff.2 h), ht]
    rfl
  · rw [if_neg h, if_neg (fun h' => h (hiff.1 h'))]

/-- **An oriented tame structure of dimension `1` restricts to one whose boundary sheets have at
most one point** (the same `T̂Θ`, the same action, `U` inside the given one; the sheets are those
of the given structure cut by one open set). -/
theorem exists_boundarySheet_subsingleton {x : Obj} (C₀ : X.OrientedTameStructure (0 + 1) Θ x)
    (hC₀ : C₀.Represents T) :
    ∃ C : X.OrientedTameStructure (0 + 1) Θ x, C.Represents T ∧
      (∀ i, (C.boundarySheet i).Subsingleton) ∧ C.rep.U ⊆ C₀.rep.U ∧ C.rep.Φ = C₀.rep.Φ ∧
        ∃ V : Set Obj, IsOpen V ∧ ∀ i, ∃ j, C.M i = C₀.M j ∩ V := by
  choose W hW hxW hsub using fun i => exists_isOpen_boundaryStratum_subsingleton
    (C₀.isSubmanifoldOfDim i) (C₀.hasTameInducedStructure i) (C₀.mem_M i)
  obtain ⟨C, hCT, hCW, hU, hΦ, V, hV, hM⟩ := C₀.exists_restrict_open hC₀
    (isOpen_iInter_of_finite hW) (mem_iInter.2 hxW)
  refine ⟨C, hCT, fun i => ?_, hU, hΦ, V, hV, hM⟩
  obtain ⟨j, hj⟩ := hM i
  have h1 : C.boundarySheet i ⊆ X.PObj.boundaryStratum (C₀.M j) ∩ W j := by
    intro y hy
    have hy' : y ∈ X.PObj.boundaryStratum (C₀.M j ∩ V) := by
      rw [← hj]; exact hy
    exact ⟨(boundaryStratum_inter_subset hV hy').1,
      mem_iInter.1 (hCW (C.subset_U i (C.boundarySheet_subset i hy))) j⟩
  exact (hsub j).anti h1

/-- **A nonempty boundary sheet with at most one point is an oriented point** of the class of
E1's `pointIntegration` (the point is smooth: `supp Θ ⊆ X_∞`). -/
theorem boundarySheet_mem_pointSheets {m : ℕ} {x : Obj} (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (C : X.OrientedTameStructure (m + 1) Θ x) (i : C.ι) (hs : (C.boundarySheet i).Subsingleton)
    (hne : (C.boundarySheet i).Nonempty) : C.boundarySheet i ∈ pointSheets X := by
  obtain ⟨p, hp⟩ := hne
  refine Or.inr ⟨p, hΘ.support_subset
    (C.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp i
      (C.boundarySheet_subset i hp)), ?_⟩
  exact Subset.antisymm (fun y hy => hs hy hp) (singleton_subset_iff.2 hp)

end OrientedTameStructure

/-! ### The class hypothesis for `n = 1` -/

/-- **E7's class hypothesis for `n = 1`, from the existence of oriented tame structures**: at
every point of `supp(∂Θ)` there is an oriented tame structure describing `T̂Θ` whose nonempty
boundary sheets are oriented points (`pointSheets`). -/
theorem hcov_dim1_of_loc (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hloc : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (0 + 1) Θ x,
      C.Represents T) :
    ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (0 + 1) Θ x,
      C.Represents T ∧ ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ pointSheets X :=
  fun x hx => by
    obtain ⟨C₀, hC₀⟩ := hloc x hx
    obtain ⟨C, hCT, hs, -⟩ := C₀.exists_boundarySheet_subsingleton hC₀
    exact ⟨C, hCT, fun i hne => C.boundarySheet_mem_pointSheets hΘ i (hs i) hne⟩

/-- The class hypothesis of Theorem 9.5.16 for `n = 1`, from oriented tame structures with LUC
(the restriction keeps the action, hence LUC). -/
theorem hcovEff_dim1_of_loc (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hloc : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (0 + 1) Θ x,
      C.Represents T ∧ C.rep.HasLUC) :
    ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (0 + 1) Θ x,
      C.Represents T ∧ (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ pointSheets X) ∧
        C.rep.HasLUC :=
  fun x hx => by
    obtain ⟨C₀, hC₀, hL⟩ := hloc x hx
    obtain ⟨C, hCT, hs, hU, hΦ, -⟩ := C₀.exists_boundarySheet_subsingleton hC₀
    refine ⟨C, hCT, fun i hne => C.boundarySheet_mem_pointSheets hΘ i (hs i) hne, ?_⟩
    intro g V hV hne hVU hid y hy
    rw [hΦ] at hid ⊢
    exact hL g V hV hne (hVU.trans hU) hid y (hU hy)

/-- The null sets of the oriented points are those of dimension `0`. -/
theorem point_isNull_iff_isHNull_zero (N B : Set Obj) :
    (SheetNullSets.point (pointSheets X)).IsNull N B ↔ X.PObj.IsHNull 0 (B ∩ N) := by
  rw [SheetNullSets.point_isNull_iff, isHNull_zero_iff, Set.disjoint_iff_inter_eq_empty]

end EpGroupoid

/-! ### Theorems 9.5.15 and 9.5.16 for `n = 1` -/

namespace EP

open EpGroupoid

variable (A : EP.{u}) {Θ : A.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}

/-- **Theorem 9.5.15, 2021 p. 449 (2017: Theorem 9.4), for `n = 1`**: let `Θ̂` be oriented, tame
(an oriented tame structure describing `T̂Θ` at every point of `supp Θ`, gap G.107), compact and
`1`-dimensional.  There is exactly one linear map `ω ↦ μ_ω^∂` from `Ω⁰_{ep,∞}(X)` to the signed
measures on `(∂S, L(∂S))` such that `μ_ω^∂(K) = (1/♯G_x) ∑ σᵢ ∫_{Kᵢ} ω|(∂₁Mᵢ, o_{∂Mᵢ})` for every
oriented tame structure at `x ∈ supp(∂Θ)` describing `T̂Θ` whose nonempty boundary sheets are
points, and every measurable `K ⊆ ∂S` in `|U(x)|`; here `∫_{Kᵢ} ω|({p}, o) = ±ω(p)`
(`zeroFormIntegration`).  Such structures exist at every point (`hcov_dim1_of_loc`). -/
theorem theorem_9_5_15_dim1 (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T) :
    ∃! Φ : A.epFormsInfty 0 →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta Θ))
        (A.X.lebesgueSigmaBoundaryH (0 + 1) Θ),
      ∀ (ω : A.epFormsInfty 0) (x : A.Obj) (C : A.X.OrientedTameStructure (0 + 1) Θ x)
        (hCT : C.Represents T), x ∈ supp (A.X.boundaryTheta Θ) →
        (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ pointSheets A.X) →
        ∀ K : Set (A.X.orbitSupp (A.X.boundaryTheta Θ)),
          MeasurableSet[A.X.lebesgueSigmaBoundaryH (0 + 1) Θ] K →
          Subtype.val '' K ⊆ A.X.π '' C.U →
          Φ ω K = (Nat.card (A.X.Isotropy x) : ℝ)⁻¹ *
            (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum A.zeroFormIntegration ω
              (A.X.π ⁻¹' (Subtype.val '' K)) :=
  theorem_9_5_15_hyp A.zeroFormIntegration hΘ hcpt (FormEval.isNDimensional_of_loc hloc) hT
    (fun N B => point_isNull_iff_isHNull_zero N B)
    (hcov_dim1_of_loc hΘ fun x hx => hloc x (A.X.supp_boundaryTheta_subset Θ hx).2)

/-- **Theorem 9.5.16, 2021 p. 449 (2017: Theorem 9.5), for `n = 1`**: as Theorem 9.5.15 for the
structures whose `U(x)` has the local unique continuation property, with `1/♯G_x^eff`. -/
theorem theorem_9_5_16_dim1 (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x,
      C.Represents T ∧ C.rep.HasLUC) :
    ∃! Φ : A.epFormsInfty 0 →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta Θ))
        (A.X.lebesgueSigmaBoundaryH (0 + 1) Θ),
      ∀ (ω : A.epFormsInfty 0) (x : A.Obj) (C : A.X.OrientedTameStructure (0 + 1) Θ x)
        (hCT : C.Represents T), x ∈ supp (A.X.boundaryTheta Θ) →
        (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ pointSheets A.X) →
        C.rep.HasLUC →
        ∀ K : Set (A.X.orbitSupp (A.X.boundaryTheta Θ)),
          MeasurableSet[A.X.lebesgueSigmaBoundaryH (0 + 1) Θ] K →
          Subtype.val '' K ⊆ A.X.π '' C.U →
          Φ ω K = (Nat.card (A.X.EffIsotropy x) : ℝ)⁻¹ *
            (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum A.zeroFormIntegration ω
              (A.X.π ⁻¹' (Subtype.val '' K)) :=
  theorem_9_5_16_hyp A.zeroFormIntegration hΘ hcpt (FormEval.isNDimensional_of_loc hloc) hT
    (fun N B => point_isNull_iff_isHNull_zero N B)
    (hcovEff_dim1_of_loc hΘ fun x hx => hloc x (A.X.supp_boundaryTheta_subset Θ hx).2)

end EP

end Polyfold
