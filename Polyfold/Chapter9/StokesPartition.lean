import Polyfold.Chapter9.StokesSheet

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5: **Theorems 9.5.17 and 9.5.18 (Stokes), pp. 449–451** (2017: Theorems
9.6, 9.7), gap G.110.  Numbers and pages are the 2021 text's.

# Stokes' theorem for the branched integral: the interior side and the partition of unity

## The text, paraphrased

`μ_{dω}(S) = μ^∂_ω(∂S)` for `Θ` tame, oriented, compact, of dimension `n`, `X` with sc-smooth
partitions of unity (and the local unique continuation property for the effective version), `ω`
an sc-differential form of degree `n − 1`.  Proof (p. 450–451): finitely many `U_k = U(x_k)` with
oriented structures cover `S`; with `U_0^*` saturated open such that the `U_k^*` cover `X` and
`|U_k^* ∖ U_0^*|` cover `S`, a subordinate sc-smooth partition of unity `β_0, …, β_ℓ`,
`ω_k = β_k ω`; then `μ_{dω}(S) = ∑ μ_{dω_k}(S) = ∑ c_k ∑ σᵢ ∫_{(Mᵢ,oᵢ)} dω_k
= ∑ c_k ∑ σᵢ ∫_{∂(Mᵢ,oᵢ)} ω_k = ∑ μ^∂_{ω_k}(∂S) = μ^∂_ω(∂S)`.

## What is formalized (for `n = m + 1 ≥ 2`, the integral of `SheetIntegrationConcrete.lean`)

* `EP.exists_stokes_partition`: the finite cover and the partition of unity of the proof, from
  `HasScPartitionsOfUnity` (Definition 7.5.5) and the compactness of `S`; `U_0^* = π⁻¹(|X| ∖ S)`.
* **`EP.stokes_of_partition`**: the first three equalities of the display on p. 451, for every
  such cover and partition: `Φ(dω)(S) = ∑_k c(x_k) ∑ᵢ σᵢ ∫_{∂(Mᵢ,oᵢ)} β_k ω`, for `Φ` with the local
  formula of Theorem 9.5.4 (`c = 1/♯G_x`) or 9.5.5 (`c = 1/♯G_x^{eff}`).
* **`EP.theorem_9_5_17_boundary_sum`**, **`EP.theorem_9_5_18_boundary_sum`**: for the branched
  integral and the effective branched integral of Definition 9.5.6 (`tameBranchedIntegral`,
  `tameBranchedIntegralEff`): `∫_Θ̂ dω`, resp. `∮_Θ̂ dω`, is the sum of the boundary integrals of
  `β_k ω` over the oriented sheets, for a cover and a partition of unity as in the text.
* `EP.exists_boundary_functional`: `ω ↦ Φ(dω)(S)` has the two properties asked of `Φ^∂` below
  (so they are satisfiable, and determine `Φ^∂`).
* **`EP.theorem_9_5_17_of_boundary`**, **`EP.theorem_9_5_18_of_boundary`**: Stokes' theorem
  `∫_Θ̂ dω = Φ^∂(ω)` for every linear `Φ^∂ : Ωᵐ_{ep,∞}(X) → ℝ` with the local formula of
  Theorem 9.5.15 (resp. 9.5.16) for the forms `βω` (`supp β ⊆ U(x)^*`) and `Φ^∂(βω) = 0` when
  `supp β` does not meet `supp Θ`: the last two equalities of the display are these two
  properties of `ω ↦ μ^∂_ω(∂S)`.

## The choices made

* The boundary integral of the right-hand sides is Part I's `ManifoldForm.boundaryIntegral` of the
  restricted form over the faces of the manifold with corners `Mᵢ`
  (`OrientedSheet.boundaryIntegral`, `StokesLocalFormulas.lean`), for the tangent orientation
  `bridgeOrientation oᵢ` of the orientation `oᵢ` of Definition 9.3.3.  The measure `μ^∂_ω` on
  `(∂S, L(∂S))` of Theorems 9.5.15, 9.5.16 (gap G.109) is not constructed; `Φ^∂` stands for
  `ω ↦ μ^∂_ω(∂S)` through the two properties used in the proof.  (2026-11-13) The measure is
  constructed for `n ≥ 2` under a class condition on the boundary sheets in
  `BoundaryMeasure.lean`, and Stokes' theorem with it is `StokesBoundaryMeasure.lean`
  (`theorem_9_5_17_msheets`).
* `n ≥ 2`: for `n = 1` the forms `ω` are functions, and the restriction of `β·ω` to a sheet is
  not read through the evaluation on frames (`EP.epFormsInftyEval` is `0` in degree `0`).
  (2026-11-13) The case `n = 1` is in `StokesSheetAllDegrees.lean`, `StokesPartitionAllDegrees.lean`
  (`theorem_9_5_17_boundary_sum_all`, `theorem_9_5_18_boundary_sum_all`).
* The orientation is described near every point of `supp Θ` by an oriented tame structure
  (`hloc`, agent E3's reading of "oriented, tame").
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module Manifold

noncomputable section

namespace Polyfold

universe u

open MPolyfold EpGroupoid

namespace EP

variable (A : EP.{u}) {m : ℕ} {Θ : A.Obj → ℚ}

/-! ### The cover and the partition of unity -/

/-- **The cover and the partition of unity of the proof of Theorem 9.5.18** (p. 450): for `X` with
sc-smooth partitions of unity, `Θ` compact and a class of structures covering `supp Θ`, there are
finitely many structures `C_k` of the class at points `x_k` and sc-smooth functions
`β_0, β_k`, constant on the orbits, with `supp β_k ⊆ U(x_k)^*`, `supp β_0` disjoint from
`supp Θ` and `β_0 + ∑ β_k = 1`. -/
theorem exists_stokes_partition (hPU : A.X.HasScPartitionsOfUnity)
    (hcpt : A.X.IsCompactBranched Θ) {n : ℕ}
    (Good : ∀ x, A.X.OrientedTameStructure n Θ x → Prop)
    (hcov : ∀ x ∈ supp Θ, ∃ C, Good x C) :
    ∃ (κ : Type u) (_ : Fintype κ) (pt : κ → A.Obj)
      (C : ∀ k, A.X.OrientedTameStructure n Θ (pt k)) (β : Option κ → A.Obj → ℝ),
      (∀ k, Good (pt k) (C k)) ∧ (∀ j, A.X.PObj.IsScSmoothMap realPolyfold (β j)) ∧
      (∀ j, ∀ φ : A.Mor, β j (A.X.src φ) = β j (A.X.tgt φ)) ∧
      (∀ k, tsupport (β (some k)) ⊆ A.X.π ⁻¹' (A.X.π '' (C k).U)) ∧
      Disjoint (tsupport (β none)) (supp Θ) ∧ ∀ y, ∑ j, β j y = 1 := by
  choose C₀ hC₀ using hcov
  obtain ⟨t, ht⟩ := hcpt.elim_finite_subcover
    (fun a : supp Θ => A.X.π '' (C₀ a.1 a.2).U)
    (fun a => A.X.proposition_7_1_8 _ (C₀ a.1 a.2).isOpen_U)
    (fun q ⟨y, hy, hyq⟩ => mem_iUnion.2 ⟨⟨y, hy⟩, y, (C₀ y hy).mem_U, hyq⟩)
  let κ : Type u := {a : supp Θ // a ∈ t}
  let U : Option κ → Set A.Obj := fun j =>
    j.elim (A.X.π ⁻¹' (A.X.orbitSupp Θ)ᶜ) fun k => A.X.π ⁻¹' (A.X.π '' (C₀ k.1.1 k.1.2).U)
  have hUo : ∀ j, IsOpen (U j) := by
    rintro (_ | k)
    · exact hcpt.isClosed.isOpen_compl.preimage A.X.continuous_π
    · exact (A.X.proposition_7_1_8 _ (C₀ k.1.1 k.1.2).isOpen_U).preimage A.X.continuous_π
  have hsatpre : ∀ B : Set A.X.OrbitSpace, A.X.IsSaturated (A.X.π ⁻¹' B) := fun B => by
    change A.X.π ⁻¹' (A.X.π '' (A.X.π ⁻¹' B)) = A.X.π ⁻¹' B
    rw [image_preimage_eq _ A.X.surjective_π]
  have hUsat : ∀ j, A.X.IsSaturated (U j) := by
    rintro (_ | k)
    · exact hsatpre _
    · exact hsatpre _
  have hUcov : ⋃ j, U j = univ := eq_univ_of_forall fun y => by
    by_cases hy : A.X.π y ∈ A.X.orbitSupp Θ
    · obtain ⟨a, ha⟩ := mem_iUnion.1 (ht hy)
      obtain ⟨hat, hya⟩ := mem_iUnion.1 ha
      exact mem_iUnion.2 ⟨some ⟨a, hat⟩, hya⟩
    · exact mem_iUnion.2 ⟨none, hy⟩
  obtain ⟨ρ, hsub, hsm, -, hinv⟩ := hPU (Option κ) U hUo hUsat hUcov
  refine ⟨κ, inferInstance, fun k => k.1.1, fun k => C₀ k.1.1 k.1.2, fun j => ρ j,
    fun k => hC₀ k.1.1 k.1.2, hsm, hinv, fun k => hsub (some k), ?_, fun y => ?_⟩
  · exact Set.disjoint_left.2 fun y hy hyΘ => hsub none hy ⟨y, hyΘ, rfl⟩
  · rw [← finsum_eq_sum_of_fintype]
    exact ρ.sum_eq_one (mem_univ y)

/-! ### The display on p. 451 -/

variable (Φ : A.epFormsInfty (m + 1) →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp Θ)
    (A.X.lebesgueSigma (A.epFormsInftyEval (m + 1)).sheetNull Θ))
  (c : A.Obj → ℝ) (Good : ∀ x, A.X.OrientedTameStructure (m + 1) Θ x → Prop)

/-- **The first three equalities of the display on p. 451** (proof of Theorem 9.5.18): for `Φ`
with the local formula of Theorem 9.5.4 or 9.5.5 (weights `c`), structures `C_k` of the class at
`x_k` and sc-smooth `β_0, β_k`, constant on the orbits, with `supp β_k ⊆ U(x_k)^*`, `supp β_0`
disjoint from `supp Θ`, `β_0 + ∑ β_k = 1`, and `ω ∈ Ωᵐ_{ep,∞}(X)`, `m ≥ 1`:
`Φ(dω)(S) = ∑_k c(x_k) ∑ᵢ σᵢ ∫_{∂(Mᵢ,oᵢ)} β_k ω`. -/
theorem stokes_of_partition (hm : 0 < m) (hcpt : A.X.IsCompactBranched Θ)
    (hGS : ∀ x C, Good x C → ∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets)
    (hcov : ∀ x ∈ supp Θ, ∃ C, Good x C)
    (hΦ : ∀ (η : A.epFormsInfty (m + 1)) (x : A.Obj)
      (C : A.X.OrientedTameStructure (m + 1) Θ x), Good x C →
      ∀ K : Set (A.X.orbitSupp Θ),
        MeasurableSet[A.X.lebesgueSigma (A.epFormsInftyEval (m + 1)).sheetNull Θ] K →
        Subtype.val '' K ⊆ A.X.π '' C.U →
        Φ η K = c x * C.sheetSum ((A.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m))
          η (A.X.π ⁻¹' (Subtype.val '' K)))
    {κ : Type*} [Fintype κ] (pt : κ → A.Obj)
    (C : ∀ k, A.X.OrientedTameStructure (m + 1) Θ (pt k)) (hC : ∀ k, Good (pt k) (C k))
    (β : Option κ → A.Obj → ℝ) (hβ : ∀ j, A.X.PObj.IsScSmoothMap realPolyfold (β j))
    (hinv : ∀ j, ∀ φ : A.Mor, β j (A.X.src φ) = β j (A.X.tgt φ))
    (hsupp : ∀ k, tsupport (β (some k)) ⊆ A.X.π ⁻¹' (A.X.π '' (C k).U))
    (h0 : Disjoint (tsupport (β none)) (supp Θ)) (hsum : ∀ y, ∑ j, β j y = 1)
    (ω : A.epFormsInfty m) :
    Φ (A.epFormsInftyD m ω) univ = ∑ k, c (pt k) * ∑ i, ((C k).σ i : ℝ) *
      ((C k).orientedSheet (A.epFormsInftyEval (m + 1)) (hGS _ _ (hC k)) i).boundaryIntegral
        (A.epFormsInftyToObj m (A.epFormsInftySmul (β (some k)) m (hβ _) (hinv _) ω)) := by
  classical
  have happ : ∀ (s : Finset (Option κ)) (f : Option κ → @SignedMeasure (A.X.orbitSupp Θ)
      (A.X.lebesgueSigma (A.epFormsInftyEval (m + 1)).sheetNull Θ)),
      (∑ j ∈ s, f j) univ = ∑ j ∈ s, f j univ := fun s f => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, FunLike.coe_add, Pi.add_apply, ih]
  have hω := A.sum_epFormsInftySmul m Finset.univ β hβ hinv hsum ω
  have e0 : Φ (A.epFormsInftyD m ω) univ = Φ (A.epFormsInftyD m
      (∑ j, A.epFormsInftySmul (β j) m (hβ j) (hinv j) ω)) univ := by rw [hω]
  have hnone : Φ (A.epFormsInftyD m (A.epFormsInftySmul (β none) m (hβ none) (hinv none) ω))
      univ = 0 := A.stokes_off_support Φ c Good hm hcpt hcov hΦ (hβ none) (hinv none) h0 ω
  have hsome : ∀ k, Φ (A.epFormsInftyD m
      (A.epFormsInftySmul (β (some k)) m (hβ _) (hinv _) ω)) univ =
      c (pt k) * ∑ i, ((C k).σ i : ℝ) *
        ((C k).orientedSheet (A.epFormsInftyEval (m + 1)) (hGS _ _ (hC k)) i).boundaryIntegral
          (A.epFormsInftyToObj m (A.epFormsInftySmul (β (some k)) m (hβ _) (hinv _) ω)) :=
    fun k => A.stokes_one_structure Φ c Good hm hcpt hGS hcov hΦ (C k) (hC k) (hβ _) (hinv _)
      (hsupp k) ω
  have e1 : Φ (A.epFormsInftyD m (∑ j, A.epFormsInftySmul (β j) m (hβ j) (hinv j) ω)) =
      ∑ j, Φ (A.epFormsInftyD m (A.epFormsInftySmul (β j) m (hβ j) (hinv j) ω)) :=
    (congrArg Φ (map_sum (A.epFormsInftyD m) _ _)).trans (map_sum Φ _ _)
  have e2 : Φ (A.epFormsInftyD m ω) univ =
      ∑ j, Φ (A.epFormsInftyD m (A.epFormsInftySmul (β j) m (hβ j) (hinv j) ω)) univ :=
    e0.trans ((congrArg (fun ν : @SignedMeasure (A.X.orbitSupp Θ)
      (A.X.lebesgueSigma (A.epFormsInftyEval (m + 1)).sheetNull Θ) => ν univ) e1).trans
      (happ Finset.univ _))
  refine e2.trans ((Fintype.sum_option _).trans ?_)
  refine (congrArg (· + _) hnone).trans ((zero_add _).trans ?_)
  exact Finset.sum_congr rfl fun k _ => hsome k

/-- **Stokes' theorem from the two properties of the boundary integral used on p. 451**: let `Φ`
have the local formula of Theorem 9.5.4 or 9.5.5 (weights `c`) and `Φ^∂ : Ωᵐ_{ep,∞}(X) → ℝ` be
linear with `Φ^∂(βω) = c(x) ∑ᵢ σᵢ ∫_{∂(Mᵢ,oᵢ)} βω` for the structures of the class and
`supp β ⊆ U(x)^*` (the local formula of Theorem 9.5.15, 9.5.16 on the forms `βω`), and
`Φ^∂(βω) = 0` when `supp β` does not meet `supp Θ`.  Then `Φ(dω)(S) = Φ^∂(ω)`. -/
theorem stokes_of_boundary_functional (hPU : A.X.HasScPartitionsOfUnity) (hm : 0 < m)
    (hcpt : A.X.IsCompactBranched Θ)
    (hGS : ∀ x C, Good x C → ∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets)
    (hcov : ∀ x ∈ supp Θ, ∃ C, Good x C)
    (hΦ : ∀ (η : A.epFormsInfty (m + 1)) (x : A.Obj)
      (C : A.X.OrientedTameStructure (m + 1) Θ x), Good x C →
      ∀ K : Set (A.X.orbitSupp Θ),
        MeasurableSet[A.X.lebesgueSigma (A.epFormsInftyEval (m + 1)).sheetNull Θ] K →
        Subtype.val '' K ⊆ A.X.π '' C.U →
        Φ η K = c x * C.sheetSum ((A.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m))
          η (A.X.π ⁻¹' (Subtype.val '' K)))
    (Φb : A.epFormsInfty m →ₗ[ℝ] ℝ)
    (hΦb : ∀ (x : A.Obj) (C : A.X.OrientedTameStructure (m + 1) Θ x) (hC : Good x C)
      (β : A.Obj → ℝ) (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
      (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)),
      tsupport β ⊆ A.X.π ⁻¹' (A.X.π '' C.U) → ∀ ω : A.epFormsInfty m,
      Φb (A.epFormsInftySmul β m hβ hinv ω) = c x * ∑ i, (C.σ i : ℝ) *
        (C.orientedSheet (A.epFormsInftyEval (m + 1)) (hGS x C hC) i).boundaryIntegral
          (A.epFormsInftyToObj m (A.epFormsInftySmul β m hβ hinv ω)))
    (hΦb₀ : ∀ (β : A.Obj → ℝ) (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
      (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)),
      Disjoint (tsupport β) (supp Θ) → ∀ ω : A.epFormsInfty m,
      Φb (A.epFormsInftySmul β m hβ hinv ω) = 0)
    (ω : A.epFormsInfty m) :
    Φ (A.epFormsInftyD m ω) univ = Φb ω := by
  obtain ⟨κ, _, pt, C, β, hC, hβ, hinv, hsupp, h0, hsum⟩ :=
    A.exists_stokes_partition hPU hcpt Good hcov
  rw [A.stokes_of_partition Φ c Good hm hcpt hGS hcov hΦ pt C hC β hβ hinv hsupp h0 hsum ω]
  have hω := A.sum_epFormsInftySmul m Finset.univ β hβ hinv hsum ω
  have e0 : Φb ω = Φb (∑ j, A.epFormsInftySmul (β j) m (hβ j) (hinv j) ω) := by rw [hω]
  rw [e0, map_sum, Fintype.sum_option, hΦb₀ (β none) (hβ none) (hinv none) h0 ω, zero_add]
  exact Finset.sum_congr rfl fun k _ =>
    (hΦb (pt k) (C k) (hC k) (β (some k)) (hβ _) (hinv _) (hsupp k) ω).symm

/-- **The hypotheses on `Φ^∂` in `stokes_of_boundary_functional` are satisfiable**: the linear
map `ω ↦ Φ(dω)(S)` has the two properties (`stokes_one_structure`, `stokes_off_support`); by
`stokes_of_boundary_functional` it is the only one when `X` has sc-smooth partitions of unity. -/
theorem exists_boundary_functional (hm : 0 < m) (hcpt : A.X.IsCompactBranched Θ)
    (hGS : ∀ x C, Good x C → ∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets)
    (hcov : ∀ x ∈ supp Θ, ∃ C, Good x C)
    (hΦ : ∀ (η : A.epFormsInfty (m + 1)) (x : A.Obj)
      (C : A.X.OrientedTameStructure (m + 1) Θ x), Good x C →
      ∀ K : Set (A.X.orbitSupp Θ),
        MeasurableSet[A.X.lebesgueSigma (A.epFormsInftyEval (m + 1)).sheetNull Θ] K →
        Subtype.val '' K ⊆ A.X.π '' C.U →
        Φ η K = c x * C.sheetSum ((A.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m))
          η (A.X.π ⁻¹' (Subtype.val '' K))) :
    ∃ Φb : A.epFormsInfty m →ₗ[ℝ] ℝ, (∀ ω, Φb ω = Φ (A.epFormsInftyD m ω) univ) ∧
      (∀ (x : A.Obj) (C : A.X.OrientedTameStructure (m + 1) Θ x) (hC : Good x C)
        (β : A.Obj → ℝ) (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
        (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)),
        tsupport β ⊆ A.X.π ⁻¹' (A.X.π '' C.U) → ∀ ω : A.epFormsInfty m,
        Φb (A.epFormsInftySmul β m hβ hinv ω) = c x * ∑ i, (C.σ i : ℝ) *
          (C.orientedSheet (A.epFormsInftyEval (m + 1)) (hGS x C hC) i).boundaryIntegral
            (A.epFormsInftyToObj m (A.epFormsInftySmul β m hβ hinv ω))) ∧
      ∀ (β : A.Obj → ℝ) (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
        (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)),
        Disjoint (tsupport β) (supp Θ) → ∀ ω : A.epFormsInfty m,
        Φb (A.epFormsInftySmul β m hβ hinv ω) = 0 :=
  ⟨{ toFun := fun ω => Φ (A.epFormsInftyD m ω) univ
     map_add' := fun a b => by rw [map_add, map_add]; rfl
     map_smul' := fun r a => by rw [map_smul, map_smul]; rfl }, fun _ => rfl,
    fun _ C hC _ hβ hinv hs ω =>
      A.stokes_one_structure Φ c Good hm hcpt hGS hcov hΦ C hC hβ hinv hs ω,
    fun _ hβ hinv hd ω => A.stokes_off_support Φ c Good hm hcpt hcov hΦ hβ hinv hd ω⟩

/-! ### Theorems 9.5.17 and 9.5.18 for the branched integrals of Definition 9.5.6 -/

variable {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}

/-- **Theorem 9.5.17 (Stokes), 2021 p. 449, with the boundary side as the sum of the display on
p. 451**: `X` with sc-smooth partitions of unity, `Θ` compact, of dimension `m + 1 ≥ 2`, oriented
by `T̂Θ = T` (described near every point of the support by an oriented tame structure),
`ω ∈ Ωᵐ_{ep,∞}(X)`.  There are finitely many oriented tame structures `C_k` at points `x_k`,
describing `T̂Θ`, with sheets in the class, and sc-smooth `β_k` constant on the orbits with
`supp β_k ⊆ U(x_k)^*`, such that `∫_Θ̂ dω = ∑_k (1/♯G_{x_k}) ∑ᵢ σᵢ ∫_{∂(Mᵢ,oᵢ)} β_k ω`. -/
theorem theorem_9_5_17_boundary_sum (hPU : A.X.HasScPartitionsOfUnity) (hm : 0 < m)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T)
    (ω : A.epFormsInfty m) :
    ∃ (κ : Type u) (_ : Fintype κ) (pt : κ → A.Obj)
      (C : ∀ k, A.X.OrientedTameStructure (m + 1) Θ (pt k)) (β : κ → A.Obj → ℝ)
      (hS : ∀ k i, (C k).M i ∈ (A.epFormsInftyEval (m + 1)).sheets)
      (hβ : ∀ k, A.X.PObj.IsScSmoothMap realPolyfold (β k))
      (hinv : ∀ k, ∀ φ : A.Mor, β k (A.X.src φ) = β k (A.X.tgt φ)),
      (∀ k, (C k).Represents T) ∧
      (∀ k, tsupport (β k) ⊆ A.X.π ⁻¹' (A.X.π '' (C k).U)) ∧
      (∀ y ∈ supp Θ, ∑ k, β k y = 1) ∧
      (A.epFormsInftyEval (m + 1)).tameBranchedIntegral (Nat.succ_pos m) hΘ hcpt hT hloc
          (A.epFormsInftyD m ω) =
        ∑ k, (Nat.card (A.X.Isotropy (pt k)) : ℝ)⁻¹ * ∑ i, ((C k).σ i : ℝ) *
          ((C k).orientedSheet (A.epFormsInftyEval (m + 1)) (hS k) i).boundaryIntegral
            (A.epFormsInftyToObj m (A.epFormsInftySmul (β k) m (hβ k) (hinv k) ω)) := by
  set F := A.epFormsInftyEval (m + 1) with hF
  let Good : ∀ x, A.X.OrientedTameStructure (m + 1) Θ x → Prop :=
    fun _ C => (∀ i, C.M i ∈ F.sheets) ∧ C.Represents T
  have hcov : ∀ x ∈ supp Θ, ∃ C, Good x C := F.hcov_of_loc hloc
  obtain ⟨κ, _, pt, C, β, hC, hβ, hinv, hsupp, h0, hsum⟩ :=
    A.exists_stokes_partition hPU hcpt Good hcov
  refine ⟨κ, inferInstance, pt, C, fun k => β (some k), fun k => (hC k).1, fun k => hβ _,
    fun k => hinv _, fun k => (hC k).2, hsupp, fun y hy => ?_, ?_⟩
  · have h := hsum y
    rw [Fintype.sum_option, image_eq_zero_of_notMem_tsupport
      (fun hn => Set.disjoint_left.1 h0 hn hy), zero_add] at h
    exact h
  · exact A.stokes_of_partition
      (branchedMeasure (F.sheetIntegration (Nat.succ_pos m)) hΘ hcpt hT hcov)
      (fun x => (Nat.card (A.X.Isotropy x) : ℝ)⁻¹) Good hm hcpt (fun _ _ h => h.1) hcov
      (fun η x C hC K hK hKU => branchedMeasure_apply (F.sheetIntegration (Nat.succ_pos m)) hΘ
        hcpt hT hcov η C hC.1 hC.2 hK hKU) pt C hC β hβ hinv hsupp h0 hsum ω

/-- **Theorem 9.5.18 (effective Stokes), 2021 p. 450, with the boundary side as the sum of the
display on p. 451**: the same for the effective branched integral `∮_Θ̂ dω`, with the weights
`1/♯G^{eff}_{x_k}`, the structures having the property of Definition 7.2.18 on `U(x_k)`. -/
theorem theorem_9_5_18_boundary_sum (hPU : A.X.HasScPartitionsOfUnity) (hm : 0 < m)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ C.rep.HasLUC)
    (ω : A.epFormsInfty m) :
    ∃ (κ : Type u) (_ : Fintype κ) (pt : κ → A.Obj)
      (C : ∀ k, A.X.OrientedTameStructure (m + 1) Θ (pt k)) (β : κ → A.Obj → ℝ)
      (hS : ∀ k i, (C k).M i ∈ (A.epFormsInftyEval (m + 1)).sheets)
      (hβ : ∀ k, A.X.PObj.IsScSmoothMap realPolyfold (β k))
      (hinv : ∀ k, ∀ φ : A.Mor, β k (A.X.src φ) = β k (A.X.tgt φ)),
      (∀ k, (C k).Represents T ∧ (C k).rep.HasLUC) ∧
      (∀ k, tsupport (β k) ⊆ A.X.π ⁻¹' (A.X.π '' (C k).U)) ∧
      (∀ y ∈ supp Θ, ∑ k, β k y = 1) ∧
      (A.epFormsInftyEval (m + 1)).tameBranchedIntegralEff (Nat.succ_pos m) hΘ hcpt hT hloc
          (A.epFormsInftyD m ω) =
        ∑ k, (Nat.card (A.X.EffIsotropy (pt k)) : ℝ)⁻¹ * ∑ i, ((C k).σ i : ℝ) *
          ((C k).orientedSheet (A.epFormsInftyEval (m + 1)) (hS k) i).boundaryIntegral
            (A.epFormsInftyToObj m (A.epFormsInftySmul (β k) m (hβ k) (hinv k) ω)) := by
  set F := A.epFormsInftyEval (m + 1) with hF
  let Good : ∀ x, A.X.OrientedTameStructure (m + 1) Θ x → Prop :=
    fun _ C => (∀ i, C.M i ∈ F.sheets) ∧ C.Represents T ∧ C.rep.HasLUC
  have hcov : ∀ x ∈ supp Θ, ∃ C, Good x C := F.hcovEff_of_loc hloc
  obtain ⟨κ, _, pt, C, β, hC, hβ, hinv, hsupp, h0, hsum⟩ :=
    A.exists_stokes_partition hPU hcpt Good hcov
  refine ⟨κ, inferInstance, pt, C, fun k => β (some k), fun k => (hC k).1, fun k => hβ _,
    fun k => hinv _, fun k => (hC k).2, hsupp, fun y hy => ?_, ?_⟩
  · have h := hsum y
    rw [Fintype.sum_option, image_eq_zero_of_notMem_tsupport
      (fun hn => Set.disjoint_left.1 h0 hn hy), zero_add] at h
    exact h
  · exact A.stokes_of_partition
      (branchedMeasureEff (F.sheetIntegration (Nat.succ_pos m)) hΘ hcpt hT hcov)
      (fun x => (Nat.card (A.X.EffIsotropy x) : ℝ)⁻¹) Good hm hcpt (fun _ _ h => h.1) hcov
      (fun η x C hC K hK hKU => branchedMeasureEff_apply (F.sheetIntegration (Nat.succ_pos m))
        hΘ hcpt hT hcov η C hC.1 hC.2.1 hC.2.2 hK hKU) pt C hC β hβ hinv hsupp h0 hsum ω

/-- **Theorem 9.5.17 (Stokes), 2021 p. 449, from the boundary functional**: `∫_Θ̂ dω = Φ^∂(ω)`
for every linear `Φ^∂ : Ωᵐ_{ep,∞}(X) → ℝ` with the local formula of Theorem 9.5.15 on the forms
`βω`, `supp β ⊆ U(x)^*` (for the oriented tame structures describing `T̂Θ` with sheets in the
class), and `Φ^∂(βω) = 0` when `supp β` does not meet `supp Θ`. -/
theorem theorem_9_5_17_of_boundary (hPU : A.X.HasScPartitionsOfUnity) (hm : 0 < m)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T)
    (Φb : A.epFormsInfty m →ₗ[ℝ] ℝ)
    (hΦb : ∀ (x : A.Obj) (C : A.X.OrientedTameStructure (m + 1) Θ x)
      (hS : ∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets), C.Represents T →
      ∀ (β : A.Obj → ℝ) (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
      (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)),
      tsupport β ⊆ A.X.π ⁻¹' (A.X.π '' C.U) → ∀ ω : A.epFormsInfty m,
      Φb (A.epFormsInftySmul β m hβ hinv ω) =
        (Nat.card (A.X.Isotropy x) : ℝ)⁻¹ * ∑ i, (C.σ i : ℝ) *
          (C.orientedSheet (A.epFormsInftyEval (m + 1)) hS i).boundaryIntegral
            (A.epFormsInftyToObj m (A.epFormsInftySmul β m hβ hinv ω)))
    (hΦb₀ : ∀ (β : A.Obj → ℝ) (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
      (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)),
      Disjoint (tsupport β) (supp Θ) → ∀ ω : A.epFormsInfty m,
      Φb (A.epFormsInftySmul β m hβ hinv ω) = 0)
    (ω : A.epFormsInfty m) :
    (A.epFormsInftyEval (m + 1)).tameBranchedIntegral (Nat.succ_pos m) hΘ hcpt hT hloc
      (A.epFormsInftyD m ω) = Φb ω := by
  set F := A.epFormsInftyEval (m + 1) with hF
  have hcov := F.hcov_of_loc hloc
  exact A.stokes_of_boundary_functional
    (branchedMeasure (F.sheetIntegration (Nat.succ_pos m)) hΘ hcpt hT hcov)
    (fun x => (Nat.card (A.X.Isotropy x) : ℝ)⁻¹)
    (fun _ C => (∀ i, C.M i ∈ F.sheets) ∧ C.Represents T) hPU hm hcpt (fun _ _ h => h.1) hcov
    (fun η x C hC K hK hKU => branchedMeasure_apply (F.sheetIntegration (Nat.succ_pos m)) hΘ
      hcpt hT hcov η C hC.1 hC.2 hK hKU) Φb
    (fun x C hC β hβ hinv hs ω => hΦb x C hC.1 hC.2 β hβ hinv hs ω) hΦb₀ ω

/-- **Theorem 9.5.18 (effective Stokes), 2021 p. 450, from the boundary functional**:
`∮_Θ̂ dω = Φ^∂(ω)` for every linear `Φ^∂` with the local formula of Theorem 9.5.16 (weights
`1/♯G_x^{eff}`) on the forms `βω`, `supp β ⊆ U(x)^*`, and `Φ^∂(βω) = 0` when `supp β` does not
meet `supp Θ`. -/
theorem theorem_9_5_18_of_boundary (hPU : A.X.HasScPartitionsOfUnity) (hm : 0 < m)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ C.rep.HasLUC)
    (Φb : A.epFormsInfty m →ₗ[ℝ] ℝ)
    (hΦb : ∀ (x : A.Obj) (C : A.X.OrientedTameStructure (m + 1) Θ x)
      (hS : ∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets), C.Represents T → C.rep.HasLUC →
      ∀ (β : A.Obj → ℝ) (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
      (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)),
      tsupport β ⊆ A.X.π ⁻¹' (A.X.π '' C.U) → ∀ ω : A.epFormsInfty m,
      Φb (A.epFormsInftySmul β m hβ hinv ω) =
        (Nat.card (A.X.EffIsotropy x) : ℝ)⁻¹ * ∑ i, (C.σ i : ℝ) *
          (C.orientedSheet (A.epFormsInftyEval (m + 1)) hS i).boundaryIntegral
            (A.epFormsInftyToObj m (A.epFormsInftySmul β m hβ hinv ω)))
    (hΦb₀ : ∀ (β : A.Obj → ℝ) (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
      (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)),
      Disjoint (tsupport β) (supp Θ) → ∀ ω : A.epFormsInfty m,
      Φb (A.epFormsInftySmul β m hβ hinv ω) = 0)
    (ω : A.epFormsInfty m) :
    (A.epFormsInftyEval (m + 1)).tameBranchedIntegralEff (Nat.succ_pos m) hΘ hcpt hT hloc
      (A.epFormsInftyD m ω) = Φb ω := by
  set F := A.epFormsInftyEval (m + 1) with hF
  have hcov := F.hcovEff_of_loc hloc
  exact A.stokes_of_boundary_functional
    (branchedMeasureEff (F.sheetIntegration (Nat.succ_pos m)) hΘ hcpt hT hcov)
    (fun x => (Nat.card (A.X.EffIsotropy x) : ℝ)⁻¹)
    (fun _ C => (∀ i, C.M i ∈ F.sheets) ∧ C.Represents T ∧ C.rep.HasLUC) hPU hm hcpt
    (fun _ _ h => h.1) hcov
    (fun η x C hC K hK hKU => branchedMeasureEff_apply (F.sheetIntegration (Nat.succ_pos m)) hΘ
      hcpt hT hcov η C hC.1 hC.2.1 hC.2.2 hK hKU) Φb
    (fun x C hC β hβ hinv hs ω => hΦb x C hC.1 hC.2.1 hC.2.2 β hβ hinv hs ω) hΦb₀ ω

end EP

end Polyfold
