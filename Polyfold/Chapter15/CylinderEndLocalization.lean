import Polyfold.Chapter15.CylinderCobordism

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703:
**Corollary 15.4.4** (2017: Corollary 15.2), the step "`∂Θ̃ = Θ₁ ⊔ −Θ₀`" of its proof: the
identification of the boundary measure of the cylinder cobordism on each end with `±∫_{Θᵢ}` is
a local statement on `|supp Θᵢ|`.

# The end identities of the cylinder are local

## The text, paraphrased

The cobordism `Θ̃` over `[0, 1] × X` restricts to `Θᵢ` over `{i} × X`, and with the boundary
orientation `∂Θ̃ = Θ₁ ⊔ −Θ₀`.  Both the boundary measure of `Θ̃` (Theorem 9.5.15) and the measure
of `Θᵢ` (Theorem 9.5.4) are given by local formulas near the points of the supports.

## What is formalized

* `signedMeasure_closed_eq_of_local`: for signed measures `μ` on a compact space `S` and `ν` on
  `D`, a closed `E ⊆ D` and a continuous `g : E → S`, if every point of `S` has an open
  neighbourhood `N` with `ν(g⁻¹(K)) = ε · μ(K)` for the Borel sets `K ⊆ N`, then
  `ν(E) = ε · μ(S)`.
* `OrientedRegularPerturbation.measure`: the measure `ω ↦ μ_ω` of Theorem 9.5.4 of an oriented
  regular perturbation, with `integral ω = measure ω univ`.
* `cylEndProj`: the continuous map from the end `i` of `|supp ∂Θ̃|` to `|supp Θᵢ|`.
* `IsLocalEndIdentity`: every point of `|supp Θᵢ|` has an open neighbourhood `N` such that the
  boundary measure of `pr^*ω` on the part of the end `i` over a Borel set `K ⊆ N` is
  `ε · μ^{Θᵢ}_ω(K)`.
* **`isCylinderBoundaryOf_of_local`**: the local end identities with `ε = 1` on the end `1`
  and `ε = −1` on the end `0` give `IsCylinderBoundaryOf`.
* **`isLocalEndIdentity_of_structures`**: the local end identity from oriented tame structures
  `C` of `Θᵢ` at `x` and `C̃` of `Θ̃` at a point over `x` whose local formulas agree up to `ε`
  over a neighbourhood of `|x|`.
* `CylinderLocalEndsStatement`, **`corollary_15_4_4_of_local_ends`**: Corollary 15.4.4 with
  step (c) of its proof in the local form.
* `OrientedRegularPerturbation.measureEff`, `IsLocalEndIdentityEff`,
  **`isCylinderBoundaryEffOf_of_local`**: the same for the effective measures (Theorems 9.5.5,
  9.5.16).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

/-! ### Two signed measures that agree locally -/

/-- For `E` closed, `g : E → S` continuous and `K ⊆ S` Borel, the part `g⁻¹(K)` of `E` is a
Borel set of the ambient space. -/
theorem measurableSet_image_preimage_borel {S D : Type*} [TopologicalSpace S]
    [TopologicalSpace D] {E : Set D} (hE : IsClosed E) {g : E → S} (hg : Continuous g)
    {K : Set S} (hK : MeasurableSet[borel S] K) :
    MeasurableSet[borel D] (Subtype.val '' (g ⁻¹' K)) := by
  let _ : MeasurableSpace D := borel D
  have : BorelSpace D := ⟨rfl⟩
  let _ : MeasurableSpace S := borel S
  have : BorelSpace S := ⟨rfl⟩
  exact hE.measurableSet.subtype_image (hg.measurable hK)

/-- **Two signed measures that agree locally agree globally.**  Let `μ` be a signed measure on a
compact space `S` and `ν` one on `D` (σ-algebras containing the Borel sets), `E ⊆ D` closed and
`g : E → S` continuous.  If every point of `S` has an open neighbourhood `N` such that
`ν(g⁻¹(K)) = ε · μ(K)` for all Borel `K ⊆ N`, then `ν(E) = ε · μ(S)`. -/
theorem signedMeasure_closed_eq_of_local {S D : Type*} [TopologicalSpace S] [CompactSpace S]
    [TopologicalSpace D] {mS : MeasurableSpace S} {mD : MeasurableSpace D}
    (hS : borel S ≤ mS) (hD : borel D ≤ mD) (μ : @SignedMeasure S mS) (ν : @SignedMeasure D mD)
    {E : Set D} (hE : IsClosed E) (g : E → S) (hg : Continuous g) (ε : ℝ)
    (hloc : ∀ s : S, ∃ N : Set S, IsOpen N ∧ s ∈ N ∧ ∀ K : Set S, MeasurableSet[borel S] K →
      K ⊆ N → ν (Subtype.val '' (g ⁻¹' K)) = ε * μ K) :
    ν E = ε * μ univ := by
  classical
  choose N hNo hsN hN using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover N hNo
    (fun s _ => mem_iUnion.2 ⟨s, hsN s⟩)
  have key : ∀ t : Finset S, ∀ K : Set S, MeasurableSet[borel S] K → K ⊆ ⋃ s ∈ t, N s →
      ν (Subtype.val '' (g ⁻¹' K)) = ε * μ K := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro K _ hKt
      have hK0 : K = ∅ := by
        refine eq_empty_iff_forall_notMem.2 fun s hs => ?_
        simpa using hKt hs
      rw [hK0, preimage_empty, image_empty, VectorMeasure.empty, VectorMeasure.empty, mul_zero]
    | insert a t _ ih =>
      intro K hK hKt
      have hNa : MeasurableSet[borel S] (N a) :=
        MeasurableSpace.measurableSet_generateFrom (hNo a)
      have h1 : MeasurableSet[borel S] (K ∩ N a) := @MeasurableSet.inter _ (borel S) _ _ hK hNa
      have h2 : MeasurableSet[borel S] (K \ N a) := @MeasurableSet.diff _ (borel S) _ _ hK hNa
      have hsub : K \ N a ⊆ ⋃ s ∈ t, N s := by
        intro s hs
        obtain ⟨b, hb⟩ := mem_iUnion.1 (hKt hs.1)
        obtain ⟨hbt, hsb⟩ := mem_iUnion.1 hb
        rcases Finset.mem_insert.1 hbt with rfl | hbt'
        · exact absurd hsb hs.2
        · exact mem_iUnion₂.2 ⟨b, hbt', hsb⟩
      have hdis : Disjoint (K ∩ N a) (K \ N a) :=
        Set.disjoint_left.2 fun s h h' => h'.2 h.2
      have hK' : K = K ∩ N a ∪ K \ N a := (inter_union_sdiff K (N a)).symm
      have e1 := hN a _ h1 inter_subset_right
      have e2 := ih _ h2 hsub
      have hμ : μ K = μ (K ∩ N a) + μ (K \ N a) := by
        conv_lhs => rw [hK']
        exact VectorMeasure.of_union hdis (hS _ h1) (hS _ h2)
      have hdis' : Disjoint (Subtype.val '' (g ⁻¹' (K ∩ N a)) : Set D)
          (Subtype.val '' (g ⁻¹' (K \ N a))) := by
        refine Set.disjoint_left.2 ?_
        rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, hqp⟩
        rw [Subtype.ext hqp] at hq
        exact hq.2 hp.2
      have hν : ν (Subtype.val '' (g ⁻¹' K)) =
          ν (Subtype.val '' (g ⁻¹' (K ∩ N a))) + ν (Subtype.val '' (g ⁻¹' (K \ N a))) := by
        conv_lhs => rw [hK', preimage_union, image_union]
        exact VectorMeasure.of_union hdis'
          (hD _ (measurableSet_image_preimage_borel hE hg h1))
          (hD _ (measurableSet_image_preimage_borel hE hg h2))
      rw [hν, hμ, e1, e2, mul_add]
  have := key t univ (@MeasurableSet.univ _ (borel S)) ht
  rwa [preimage_univ, image_univ, Subtype.range_coe] at this

variable {A : SEP.{u}}

/-! ### The measure of an oriented regular perturbation -/

namespace OrientedRegularPerturbation

variable {f : A.Obj → A.W} {m : ℕ}

/-- **The measure `ω ↦ μ_ω` of Theorem 9.5.4** on `(|supp Θ|, L(S))` for the oriented regular
perturbation `P`, `Θ = Λ ∘ f`. -/
def measure (P : OrientedRegularPerturbation A f m) :
    A.baseEP.epFormsInfty (m + 1) →ₗ[ℝ]
      @SignedMeasure (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ)))
        (A.X.lebesgueSigma (A.baseEP.epFormsInftyEval (m + 1)).sheetNull
          (fun z => (P.Λ (f z) : ℚ))) :=
  EpGroupoid.branchedMeasure
    ((A.baseEP.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m)) P.isBranched
    P.isCompact P.isOrientation
    (EpGroupoid.FormEval.hcov_of_tameOpen (EpGroupoid.FormEval.tameOpen A.X) P.loc)

/-- `∫_{(Λ ∘ f, o)} ω = μ_ω(|supp Θ|)` (Definition 9.5.6 (1)). -/
theorem integral_eq_measure_univ (P : OrientedRegularPerturbation A f m)
    (ω : A.baseEP.epFormsInfty (m + 1)) : P.integral ω = P.measure ω univ :=
  rfl

end OrientedRegularPerturbation

/-! ### The ends over `|supp Θᵢ|` -/

/-- **The end `i` of `|supp ∂Θ̃|` over `|supp Θ|`**: the map `|(i, x)| ↦ |x|` with values in
`|supp Θ|`, for `Θ` on `X` whose support contains the points under the end. -/
def cylEndProj {Θ' : (A.cubeSEP 1).Obj → ℚ} {Θ : A.Obj → ℚ} {i : ℝ}
    (hover : ∀ p : cylEnd (X := A.X) Θ' i, cylEndMap p ∈ A.X.orbitSupp Θ)
    (p : cylEnd (X := A.X) Θ' i) : A.X.orbitSupp Θ :=
  ⟨cylEndMap p, hover p⟩

theorem continuous_cylEndProj {Θ' : (A.cubeSEP 1).Obj → ℚ} {Θ : A.Obj → ℚ} {i : ℝ}
    (hover : ∀ p : cylEnd (X := A.X) Θ' i, cylEndMap p ∈ A.X.orbitSupp Θ) :
    Continuous (cylEndProj hover) :=
  (A.X.continuous_cylEndMap Θ' i).subtype_mk _

/-- **The local end identity** on the end `i` with sign `ε`: every point of `|supp Θ|` has an
open neighbourhood `N` such that, for every Borel `K ⊆ N`, the boundary measure of `pr^*ω` on
the part of the end `i` over `K` is `ε · μ^Θ_ω(K)`. -/
def IsLocalEndIdentity {f : A.Obj → A.W} {m : ℕ} (P : OrientedRegularPerturbation A f m)
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    (i ε : ℝ)
    (hover : ∀ p : cylEnd (X := A.X) Θ' i,
      cylEndMap p ∈ A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))) : Prop :=
  ∀ (ω : A.baseEP.epFormsInfty (m + 1)) (s : A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))),
    ∃ N : Set (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))), IsOpen N ∧ s ∈ N ∧
      ∀ K : Set (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))), MeasurableSet[borel _] K → K ⊆ N →
        (A.cubeSEP 1).baseEP.boundaryMeasure (Nat.succ_pos m) hΘ' hcpt' hT' hloc'
            (EP.epFormsInftyPullback (A.X.cubeProj 1) (m + 1) ω)
            (Subtype.val '' (cylEndProj hover ⁻¹' K)) = ε * P.measure ω K

/-- **The end identity from the local end identity**: the boundary measure of `pr^*ω` on the
whole end `i` is `ε · ∫_{Θ} ω`. -/
theorem boundaryMeasure_cylEnd_of_local {f : A.Obj → A.W} {m : ℕ}
    (P : OrientedRegularPerturbation A f m)
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    {i ε : ℝ}
    (hover : ∀ p : cylEnd (X := A.X) Θ' i,
      cylEndMap p ∈ A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ)))
    (h : IsLocalEndIdentity P hΘ' hcpt' hT' hloc' i ε hover)
    (ω : A.baseEP.epFormsInfty (m + 1)) :
    (A.cubeSEP 1).baseEP.boundaryMeasure (Nat.succ_pos m) hΘ' hcpt' hT' hloc'
        (EP.epFormsInftyPullback (A.X.cubeProj 1) (m + 1) ω) (cylEnd (X := A.X) Θ' i) =
      ε * P.integral ω := by
  have : CompactSpace (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))) :=
    isCompact_iff_compactSpace.1 P.isCompact
  rw [P.integral_eq_measure_univ]
  exact signedMeasure_closed_eq_of_local (borel_le_borelNullSigma _)
    ((A.X.cubeProd 1).borel_le_lebesgueSigmaBoundaryH (m + 1 + 1) Θ') _ _
    (A.X.isClosed_cylEnd Θ' i) (cylEndProj hover) (continuous_cylEndProj hover) ε (h ω)

/-- **`∂Θ̃ = Θ₁ ⊔ −Θ₀` from the local end identities** (proof of Corollary 15.4.4, p. 703): if
the ends of `|supp ∂Θ̃|` lie over `|supp Θ₀|` and `|supp Θ₁|` and the local end identities hold
with sign `+1` on the end `1` and `−1` on the end `0`, then `IsCylinderBoundaryOf` holds. -/
theorem isCylinderBoundaryOf_of_local {f : A.Obj → A.W} {m : ℕ}
    (P₀ P₁ : OrientedRegularPerturbation A f m)
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    (hover₀ : ∀ p : cylEnd (X := A.X) Θ' 0,
      cylEndMap p ∈ A.X.orbitSupp (fun z => (P₀.Λ (f z) : ℚ)))
    (hover₁ : ∀ p : cylEnd (X := A.X) Θ' 1,
      cylEndMap p ∈ A.X.orbitSupp (fun z => (P₁.Λ (f z) : ℚ)))
    (h₀ : IsLocalEndIdentity P₀ hΘ' hcpt' hT' hloc' 0 (-1) hover₀)
    (h₁ : IsLocalEndIdentity P₁ hΘ' hcpt' hT' hloc' 1 1 hover₁) :
    IsCylinderBoundaryOf P₀ P₁ hΘ' hcpt' hT' hloc' := by
  intro ω
  refine ⟨?_, ?_⟩
  · rw [boundaryMeasure_cylEnd_of_local P₁ hΘ' hcpt' hT' hloc' hover₁ h₁ ω, one_mul]
  · rw [boundaryMeasure_cylEnd_of_local P₀ hΘ' hcpt' hT' hloc' hover₀ h₀ ω, neg_one_mul]

/-! ### The local end identity from oriented tame structures -/

set_option maxHeartbeats 1600000 in
-- the statement unfolds the cylinder's ep-groupoid in several places
/-- **The local end identity from local structures**: let every `x ∈ supp Θ` have an oriented
tame structure `C` of `Θ` at `x` describing the orientation of `P` (sheets in the class of the
integration), an oriented tame structure `C̃` of `Θ̃` at a point `z ∈ supp ∂Θ̃` describing `T̃`
(nonempty boundary sheets in the class of the integration), and an open neighbourhood `N` of
`|x|` in `|X|` inside `|U(x)|` over which the end `i` lies in `|Ũ(z)|`, such that for all Borel
`K` over `N` the local formula of Theorem 9.5.15 for `C̃`, `pr^*ω` and the part of the end over
`K` is `ε` times the local formula (9.21) of Theorem 9.5.4 for `C`, `ω` and `K`.  Then the local
end identity holds. -/
theorem isLocalEndIdentity_of_structures {f : A.Obj → A.W} {m : ℕ}
    (P : OrientedRegularPerturbation A f m)
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    {i ε : ℝ}
    (hover : ∀ p : cylEnd (X := A.X) Θ' i,
      cylEndMap p ∈ A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ)))
    (h : ∀ x ∈ EpGroupoid.supp (fun z => (P.Λ (f z) : ℚ)),
      ∃ (C : A.X.OrientedTameStructure (m + 1) (fun z => (P.Λ (f z) : ℚ)) x)
        (z : (A.cubeSEP 1).Obj) (C' : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' z)
        (hCT' : C'.Represents T') (N : Set A.X.OrbitSpace),
        (∀ j, C.M j ∈ (A.baseEP.epFormsInftyEval (m + 1)).sheets) ∧ C.Represents P.T ∧
        z ∈ EpGroupoid.supp ((A.cubeSEP 1).X.boundaryTheta Θ') ∧
        (∀ j, (C'.boundarySheet j).Nonempty →
          C'.boundarySheet j ∈ ((A.cubeSEP 1).baseEP.epFormsInftyEval (m + 1)).msheets) ∧
        IsOpen N ∧ A.X.π x ∈ N ∧ N ⊆ A.X.π '' C.U ∧
        (∀ p : cylEnd (X := A.X) Θ' i, cylEndMap p ∈ N →
          p.1.1 ∈ (A.cubeSEP 1).X.π '' C'.U) ∧
        ∀ (ω : A.baseEP.epFormsInfty (m + 1))
          (K : Set (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ)))),
          MeasurableSet[borel _] K → Subtype.val '' K ⊆ N →
          (Nat.card ((A.cubeSEP 1).X.Isotropy z) : ℝ)⁻¹ *
              (C'.boundaryFamily hΘ' hCT').nonemptyPart.sheetSum
                (((A.cubeSEP 1).baseEP.epFormsInftyEval (m + 1)).msheetIntegration
                  (Nat.succ_pos m))
                (EP.epFormsInftyPullback (A.X.cubeProj 1) (m + 1) ω)
                ((A.cubeSEP 1).X.π ⁻¹'
                  (Subtype.val '' (Subtype.val '' (cylEndProj hover ⁻¹' K)))) =
            ε * C.localMeasure
              ((A.baseEP.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m)) ω
              (Subtype.val '' K)) :
    IsLocalEndIdentity P hΘ' hcpt' hT' hloc' i ε hover := by
  intro ω s
  obtain ⟨x, hx, hxs⟩ := s.2
  obtain ⟨C, z, C', hCT', N, hCS, hCT, hz, hS', hNo, hxN, hNU, hNU', hid⟩ := h x hx
  refine ⟨Subtype.val ⁻¹' N, hNo.preimage continuous_subtype_val, by
    change s.1 ∈ N
    rw [← hxs]
    exact hxN, fun K hK hKN => ?_⟩
  have hKN' : Subtype.val '' K ⊆ N := image_subset_iff.2 hKN
  have hm' := measurableSet_image_preimage_borel (A.X.isClosed_cylEnd Θ' i)
    (continuous_cylEndProj hover) hK
  have hKU' : Subtype.val '' (Subtype.val '' (cylEndProj hover ⁻¹' K)) ⊆
      (A.cubeSEP 1).X.π '' C'.U := by
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact hNU' p (hKN' ⟨_, hp, rfl⟩)
  have e1 := (A.cubeSEP 1).baseEP.boundaryMeasure_spec (Nat.succ_pos m) hΘ' hcpt' hT' hloc'
    (EP.epFormsInftyPullback (A.X.cubeProj 1) (m + 1) ω) z C' hCT' hz hS'
    (Subtype.val '' (cylEndProj hover ⁻¹' K))
    ((A.X.cubeProd 1).borel_le_lebesgueSigmaBoundaryH (m + 1 + 1) Θ' _ hm') hKU'
  have e2 : P.measure ω K = C.localMeasure
      ((A.baseEP.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m)) ω
      (Subtype.val '' K) :=
    EpGroupoid.branchedMeasure_apply _ P.isBranched P.isCompact P.isOrientation _ ω C hCS hCT
      (borel_le_borelNullSigma _ _ hK) (hKN'.trans hNU)
  rw [e2, ← hid ω K hK hKN']
  exact e1

/-! ### Corollary 15.4.4 from the local end identities -/

/-- **Step (c) of the proof of Corollary 15.4.4 in local form**: every structurable regular
perturbation `Λ̃` of `f̃` on `[0, 1] × X` that step (b) can produce carries an orientation `T̃`,
described by oriented tame structures of dimension `m + 2`, with the local end identities
(sign `−1` over `Θ₀`, sign `+1` over `Θ₁`). -/
def CylinderLocalEndsStatement {f : A.Obj → A.W} (hf : IsSection A.P f) {m : ℕ}
    (P₀ P₁ : OrientedRegularPerturbation A f m) : Prop :=
  ∀ Λ' : (A.cubeSEP 1).W → ℚ≥0,
    IsRegularPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf)
      (interpAuxNorm A P₀.N P₁.N) (interpSet A P₀.U P₁.U) Λ' →
    (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = P₀.Λ (cubeVal w).2) →
    (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = P₁.Λ (cubeVal w).2) →
    ∀ (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)))
      (hcpt' : (A.cubeSEP 1).X.IsCompactBranched
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ))),
    ∃ (T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ)
      (hT' : (A.cubeSEP 1).X.IsOrientation (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)) T')
      (hloc' : ∀ x ∈ EpGroupoid.supp (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)),
        ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1)
          (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)) x, C.Represents T')
      (hover₀ : ∀ p : cylEnd (X := A.X) (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)) 0,
        cylEndMap p ∈ A.X.orbitSupp (fun z => (P₀.Λ (f z) : ℚ)))
      (hover₁ : ∀ p : cylEnd (X := A.X) (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)) 1,
        cylEndMap p ∈ A.X.orbitSupp (fun z => (P₁.Λ (f z) : ℚ))),
      IsLocalEndIdentity P₀ hΘ' hcpt' hT' hloc' 0 (-1) hover₀ ∧
        IsLocalEndIdentity P₁ hΘ' hcpt' hT' hloc' 1 1 hover₁

/-- The local form of step (c) gives `CylinderOrientationStatement`. -/
theorem cylinderOrientationStatement_of_local_ends {f : A.Obj → A.W} (hf : IsSection A.P f)
    {m : ℕ} {P₀ P₁ : OrientedRegularPerturbation A f m}
    (h : CylinderLocalEndsStatement hf P₀ P₁) : CylinderOrientationStatement hf P₀ P₁ := by
  intro Λ' hreg e0 e1 hΘ' hcpt'
  obtain ⟨T', hT', hloc', hover₀, hover₁, h₀, h₁⟩ := h Λ' hreg e0 e1 hΘ' hcpt'
  exact ⟨T', hT', hloc', isCylinderBoundaryOf_of_local P₀ P₁ hΘ' hcpt' hT' hloc' hover₀ hover₁
    h₀ h₁⟩

/-- **Corollary 15.4.4 (2017: Corollary 15.2), p. 703, from the local end identities**:
`corollary_15_4_4_of_rel` with step (c) in its local form. -/
theorem corollary_15_4_4_of_local_ends
    (hrelC : theorem_15_3_7_relative_statement (A.cubeSEP 1))
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.HasScPartitionsOfUnity) (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hS : A.E.HasCompactSolutionSetEp f) {m : ℕ}
    (Can : OrientedRegularPerturbation A f m → Prop)
    (hglue : ∀ P₀ P₁, Can P₀ → Can P₁ →
      IsBoundaryStructurable (A.cubeSEP 1) (cubeGlue P₀.Λ P₁.Λ) ∧
        IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue P₀.Λ P₁.Λ))
    (hor : ∀ P₀ P₁, Can P₀ → Can P₁ → CylinderLocalEndsStatement hf.1.1.1 P₀ P₁) :
    corollary_15_4_4_statement A f m Can :=
  corollary_15_4_4_of_rel hrelC hd hpara hPU hPUC hf hft hS Can hglue fun P₀ P₁ h₀ h₁ =>
    cylinderOrientationStatement_of_local_ends hf.1.1.1 (hor P₀ P₁ h₀ h₁)

/-! ### The effective version -/

namespace OrientedRegularPerturbation

variable {f : A.Obj → A.W} {m : ℕ}

/-- **The effective measure `ω ↦ μ^eff_ω` of Theorem 9.5.5** of the oriented regular
perturbation `P`, for `X` with the local unique continuation property. -/
def measureEff (hLUC : A.X.IsLUC) (P : OrientedRegularPerturbation A f m) :
    A.baseEP.epFormsInfty (m + 1) →ₗ[ℝ]
      @SignedMeasure (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ)))
        (A.X.lebesgueSigma (A.baseEP.epFormsInftyEval (m + 1)).sheetNull
          (fun z => (P.Λ (f z) : ℚ))) :=
  EpGroupoid.branchedMeasureEff
    ((A.baseEP.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m)) P.isBranched
    P.isCompact P.isOrientation
    (EpGroupoid.FormEval.hcovEff_of_tameOpen (EpGroupoid.FormEval.tameOpen A.X)
      (A.baseEP.hloc_hasLUC hLUC P.loc))

/-- `∮_{(Λ ∘ f, o)} ω = μ^eff_ω(|supp Θ|)` (Definition 9.5.6 (2)). -/
theorem integralEff_eq_measureEff_univ (hLUC : A.X.IsLUC)
    (P : OrientedRegularPerturbation A f m) (ω : A.baseEP.epFormsInfty (m + 1)) :
    P.integralEff hLUC ω = P.measureEff hLUC ω univ :=
  rfl

end OrientedRegularPerturbation

/-- **The local end identity, effective form**: as `IsLocalEndIdentity`, for the effective
boundary measure (Theorem 9.5.16) and the effective measure of `Θ` (Theorem 9.5.5). -/
def IsLocalEndIdentityEff {f : A.Obj → A.W} {m : ℕ} (hLUC : A.X.IsLUC)
    (hLUCC : (A.cubeSEP 1).X.IsLUC) (P : OrientedRegularPerturbation A f m)
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    (i ε : ℝ)
    (hover : ∀ p : cylEnd (X := A.X) Θ' i,
      cylEndMap p ∈ A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))) : Prop :=
  ∀ (ω : A.baseEP.epFormsInfty (m + 1)) (s : A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))),
    ∃ N : Set (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))), IsOpen N ∧ s ∈ N ∧
      ∀ K : Set (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))), MeasurableSet[borel _] K → K ⊆ N →
        (A.cubeSEP 1).baseEP.boundaryMeasureEff (Nat.succ_pos m) hLUCC hΘ' hcpt' hT' hloc'
            (EP.epFormsInftyPullback (A.X.cubeProj 1) (m + 1) ω)
            (Subtype.val '' (cylEndProj hover ⁻¹' K)) = ε * P.measureEff hLUC ω K

/-- **`∂Θ̃ = Θ₁ ⊔ −Θ₀` for the effective measures from the local end identities**:
`IsCylinderBoundaryEffOf` from `IsLocalEndIdentityEff` on the two ends. -/
theorem isCylinderBoundaryEffOf_of_local {f : A.Obj → A.W} {m : ℕ} (hLUC : A.X.IsLUC)
    (hLUCC : (A.cubeSEP 1).X.IsLUC) (P₀ P₁ : OrientedRegularPerturbation A f m)
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    (hover₀ : ∀ p : cylEnd (X := A.X) Θ' 0,
      cylEndMap p ∈ A.X.orbitSupp (fun z => (P₀.Λ (f z) : ℚ)))
    (hover₁ : ∀ p : cylEnd (X := A.X) Θ' 1,
      cylEndMap p ∈ A.X.orbitSupp (fun z => (P₁.Λ (f z) : ℚ)))
    (h₀ : IsLocalEndIdentityEff hLUC hLUCC P₀ hΘ' hcpt' hT' hloc' 0 (-1) hover₀)
    (h₁ : IsLocalEndIdentityEff hLUC hLUCC P₁ hΘ' hcpt' hT' hloc' 1 1 hover₁) :
    IsCylinderBoundaryEffOf hLUC hLUCC P₀ P₁ hΘ' hcpt' hT' hloc' := by
  have hc₀ : CompactSpace (A.X.orbitSupp (fun z => (P₀.Λ (f z) : ℚ))) :=
    isCompact_iff_compactSpace.1 P₀.isCompact
  have hc₁ : CompactSpace (A.X.orbitSupp (fun z => (P₁.Λ (f z) : ℚ))) :=
    isCompact_iff_compactSpace.1 P₁.isCompact
  intro ω
  refine ⟨?_, ?_⟩
  · rw [P₁.integralEff_eq_measureEff_univ, ← one_mul (P₁.measureEff hLUC ω univ)]
    exact signedMeasure_closed_eq_of_local (borel_le_borelNullSigma _)
      ((A.X.cubeProd 1).borel_le_lebesgueSigmaBoundaryH (m + 1 + 1) Θ') _ _
      (A.X.isClosed_cylEnd Θ' 1) (cylEndProj hover₁) (continuous_cylEndProj hover₁) 1 (h₁ ω)
  · rw [P₀.integralEff_eq_measureEff_univ, ← neg_one_mul (P₀.measureEff hLUC ω univ)]
    exact signedMeasure_closed_eq_of_local (borel_le_borelNullSigma _)
      ((A.X.cubeProd 1).borel_le_lebesgueSigmaBoundaryH (m + 1 + 1) Θ') _ _
      (A.X.isClosed_cylEnd Θ' 0) (cylEndProj hover₀) (continuous_cylEndProj hover₀) (-1) (h₀ ω)

end SBLocalization

end Polyfold
