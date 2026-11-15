import Polyfold.Chapter15.CylinderFaceIntegration
import Polyfold.Chapter15.CylinderEndWeights
import Polyfold.Chapter15.CubeLUC

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703:
**Corollary 15.4.4** (2017: Corollary 15.2), the step "`∂Θ̃ = Θ₁ ⊔ −Θ₀`" of its proof, with
Definition 9.3.10 and the local formulas of Theorems 9.5.4 and 9.5.15.

# The local end identity from matching structures

## The text, paraphrased

Near a point `(i, x)` of an end of the cylinder the sheets of `Θ̃` are `M̃ⱼ = {f̃ = s̃ⱼ}`, their
boundaries are the slices `{i} × Mⱼ` with `Mⱼ = {f = s̃ⱼ(i, ·)}` the sheets of `Θᵢ` near `x`, the
weights are the same, and the isotropy groups of `(i, x)` and of `x` are the same.  With the
boundary orientation the slice `{i} × Mⱼ` is `(−1)^{i+1}` times `Mⱼ`.  The local formulas for the
two measures then agree up to this sign.

## What is formalized

* `EpGroupoid.bijective_cubeIsotropyHom`, **`EpGroupoid.card_isotropy_cubeProd`**:
  `♯G_{(q, x)} = ♯G_x` for the ep-groupoid `[0, 1]ⁿ × X`.
* `SBLocalization.AreMatchedAt`: structures `C` of `Θ` at `x` and `C̃` of `Θ̃` at `(i, x)` match
  with sign `ε`: the nonempty boundary sheets of `C̃` are the slices `{i} × M_{e j}` of the
  sheets of `C`, with the same weights, `{i} × U(x) ⊆ Ũ(i, x)`, and the boundary orientation of
  `∂₁M̃ⱼ` is `ε` times the orientation of `M_{e j}` moved to the slice.
* **`isLocalEndIdentity_of_matched`**: if every point of `supp Θ` has matched structures with
  sign `ε` (the one of `Θ` with sheets in the class of the integration and describing the
  orientation of `P`, the one of `Θ̃` describing `T̃`), then the local end identity with sign `ε`
  holds on the end `i`.
* **`isCylinderBoundaryOf_of_matched`**: matched structures with sign `−1` on the end `0` and
  `+1` on the end `1` give `IsCylinderBoundaryOf` (`∂Θ̃ = Θ₁ ⊔ −Θ₀` for the integrals).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

section Isotropy

variable (X : EpGroupoid Obj Mor) (n : ℕ)
  [ParacompactSpace ((Fin n → unitInterval) × Obj)]
  [ParacompactSpace ((Fin n → unitInterval) × Mor)]

/-- The isotropy group of `(q, x)` in `[0, 1]ⁿ × X` is the isotropy group of `x`. -/
theorem bijective_cubeIsotropyHom (z : (Fin n → unitInterval) × Obj) :
    Bijective (X.cubeIsotropyHom n z) := by
  constructor
  · intro g h e
    have e2 : g.val.2 = h.val.2 := congrArg (fun k => k.val) e
    have e1 : g.val.1 = h.val.1 :=
      (congrArg Prod.fst g.src_val).trans (congrArg Prod.fst h.src_val).symm
    exact GroupoidStr.Isotropy.ext (Prod.ext e1 e2)
  · intro k
    refine ⟨⟨(z.1, k.val), ?_, ?_⟩, GroupoidStr.Isotropy.ext rfl⟩
    · rw [cubeProd_src]
      exact Prod.ext rfl k.src_val
    · rw [cubeProd_tgt]
      exact Prod.ext rfl k.tgt_val

/-- **`♯G_{(q, x)} = ♯G_x`** for the ep-groupoid `[0, 1]ⁿ × X`. -/
theorem card_isotropy_cubeProd (z : (Fin n → unitInterval) × Obj) :
    Nat.card ((X.cubeProd n).Isotropy z) = Nat.card (X.Isotropy z.2) :=
  Nat.card_eq_of_bijective _ (X.bijective_cubeIsotropyHom n z)

end Isotropy

end EpGroupoid

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}}

/-- **Structures of `Θ` at `x` and of `Θ̃` at `(i, x)` that match with sign `ε`** (proof of
Corollary 15.4.4, p. 703): through an injection `e` of the index set of the nonempty boundary
sheets of `C̃` into the index set of `C` that misses only empty sheets, the boundary sheet
`∂₁M̃ⱼ` is the slice `{i} × M_{e j}`, the weights agree, `{i} × U(x) ⊆ Ũ(i, x)`, and the boundary
orientation (Definition 9.3.10) of `∂₁M̃ⱼ` is the orientation of `M_{e j}` moved to the slice
(`ε = 1`) or the opposite one (`ε = −1`). -/
def AreMatchedAt {m : ℕ} {Θ : A.Obj → ℚ} {x : A.Obj} (q : Fin 1 → unitInterval)
    (C : A.X.OrientedTameStructure (m + 1) Θ x) {Θ' : (A.cubeSEP 1).Obj → ℚ}
    {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (C' : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' (q, x))
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ') (hCT' : C'.Represents T')
    (hS : ∀ i, C.M i ∈ (A.baseEP.epFormsInftyEval (m + 1)).sheets) (ε : ℝ) : Prop :=
  ∃ e : (C'.boundaryFamily hΘ' hCT').nonemptyPart.ι → C.ι,
    Injective e ∧ (∀ i, i ∉ range e → C.M i = ∅) ∧ (∀ j, C'.σ j.1 = C.σ (e j)) ∧
    (∀ j, C'.boundarySheet j.1 = (cubeFaceIncl A q).obj '' C.M (e j)) ∧
    (∀ y ∈ C.U, (q, y) ∈ C'.U) ∧
    ((ε = 1 ∧ ∀ j, ∀ y ∈ C.M (e j),
        (C'.boundaryOrient j.1).tangent ((cubeFaceIncl A q).obj y) =
          (faceOrient q (C.orient (e j)) (hS (e j)).1.1).tangent ((cubeFaceIncl A q).obj y)) ∨
      (ε = -1 ∧ ∀ j, ∀ y ∈ C.M (e j),
        (C'.boundaryOrient j.1).tangent ((cubeFaceIncl A q).obj y) ≠
          (faceOrient q (C.orient (e j)) (hS (e j)).1.1).tangent ((cubeFaceIncl A q).obj y)))

set_option maxHeartbeats 1600000 in
-- the statement unfolds the cylinder's ep-groupoid in several places
/-- **The local end identity from matched structures** (proof of Corollary 15.4.4, p. 703):
let every `x ∈ supp Θ` have an oriented tame structure `C` of `Θ` at `x` (sheets in the class of
the integration, describing the orientation of `P`) and one `C̃` of `Θ̃` at `(i, x)` describing
`T̃` that match with sign `ε`.  Then the boundary measure of `pr^*ω` on the end `i` is locally
`ε` times the measure of `ω` on `|supp Θ|`. -/
theorem isLocalEndIdentity_of_matched {f : A.Obj → A.W} {m : ℕ}
    (P : OrientedRegularPerturbation A f m)
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    {i : unitInterval} {ε : ℝ}
    (hover : ∀ p : cylEnd (X := A.X) Θ' (i : ℝ),
      cylEndMap p ∈ A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ)))
    (h : ∀ x ∈ EpGroupoid.supp (fun z => (P.Λ (f z) : ℚ)),
      ∃ (C : A.X.OrientedTameStructure (m + 1) (fun z => (P.Λ (f z) : ℚ)) x)
        (C' : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' ((fun _ => i), x))
        (hCT' : C'.Represents T') (hS : ∀ j, C.M j ∈ (A.baseEP.epFormsInftyEval (m + 1)).sheets),
        C.Represents P.T ∧ AreMatchedAt (fun _ => i) C C' hΘ' hCT' hS ε) :
    IsLocalEndIdentity P hΘ' hcpt' hT' hloc' (i : ℝ) ε hover := by
  classical
  set q : Fin 1 → unitInterval := fun _ => i with hq
  refine isLocalEndIdentity_of_structures P hΘ' hcpt' hT' hloc' hover fun x hx => ?_
  obtain ⟨C, C', hCT', hS, hCT, e, he, hrange, hσ, hM, hU, hε⟩ := h x hx
  -- the point `(i, x)` lies in `supp ∂Θ̃`
  have hsupp : ∀ j : (C'.boundaryFamily hΘ' hCT').nonemptyPart.ι, ∀ y ∈ C.M (e j),
      ((q, y) : (A.cubeSEP 1).Obj) ∈ EpGroupoid.supp ((A.cubeSEP 1).X.boundaryTheta Θ') :=
    fun j y hy => C'.boundarySheet_subset_supp_boundaryTheta j.1 (by
      rw [hM j]
      exact ⟨y, hy, rfl⟩)
  have hrg : ∀ j₀ : C.ι, ∀ y ∈ C.M j₀, ∃ j, e j = j₀ := fun j₀ y hy => by
    by_contra hne
    have := hrange j₀ (fun ⟨j, hj⟩ => hne ⟨j, hj⟩)
    rw [this] at hy
    exact hy
  have hz : ((q, x) : (A.cubeSEP 1).Obj) ∈
      EpGroupoid.supp ((A.cubeSEP 1).X.boundaryTheta Θ') := by
    obtain ⟨j₀, hj₀⟩ := (C.toLocalBranchingStructure.mem_supp_iff C.mem_U).1 hx
    obtain ⟨j, rfl⟩ := hrg j₀ x hj₀
    exact hsupp j x hj₀
  have hS' : ∀ j, (C'.boundarySheet j).Nonempty →
      C'.boundarySheet j ∈ ((A.cubeSEP 1).baseEP.epFormsInftyEval (m + 1)).msheets :=
    fun j hj => by
      have := hM ⟨j, hj⟩
      rw [this]
      exact cubeFace_mem_msheets q (hS _)
  have hNo : IsOpen (A.X.π '' C.U) := A.X.proposition_7_1_8 _ C.isOpen_U
  refine ⟨C, (q, x), C', hCT', A.X.π '' C.U, hS, hCT, hz, hS', hNo, ⟨x, C.mem_U, rfl⟩,
    Subset.rfl, ?_, ?_⟩
  · -- the end over `|U(x)|` lies in `|Ũ(i, x)|`
    intro p hp
    obtain ⟨z, -, hzp⟩ := p.1.2
    obtain ⟨y, hyU, hy⟩ := hp
    rw [A.X.cylEndMap_π p z hzp] at hy
    have ht : (z.1 0 : ℝ) = i := by
      have h2 : A.X.cylOrbitTime p.1.1 = i := p.2
      rwa [← hzp, cylOrbitTime_π] at h2
    have hz1 : z.1 = q := funext fun a => by
      have : a = 0 := Subsingleton.elim _ _
      subst this
      exact Subtype.ext ht
    refine ⟨(q, y), hU y hyU, ?_⟩
    rw [← hzp]
    exact ((A.X.cubeProd_π_eq_π_iff 1 (q, y) z).2 ⟨hz1.symm, hy⟩)
  · intro ω K hK hKN
    have hcl : IsClosed (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))) := P.isCompact.isClosed
    have hKb : MeasurableSet[borel A.X.OrbitSpace] (Subtype.val '' K) := by
      let _ : MeasurableSpace A.X.OrbitSpace := borel _
      have : BorelSpace A.X.OrbitSpace := ⟨rfl⟩
      have : BorelSpace (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))) := Subtype.borelSpace _
      exact hcl.measurableSet.subtype_image (by
        rw [BorelSpace.measurable_eq (α := A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ)))]
        exact hK)
    have hA₀ : MeasurableSet[borel A.Obj] (A.X.π ⁻¹' (Subtype.val '' K)) := by
      let _ : MeasurableSpace A.X.OrbitSpace := borel _
      have : BorelSpace A.X.OrbitSpace := ⟨rfl⟩
      let _ : MeasurableSpace A.Obj := borel _
      have : BorelSpace A.Obj := ⟨rfl⟩
      exact A.X.continuous_π.measurable hKb
    have hA : ∀ j₀, (A.cubeSEP 1).X.π ⁻¹'
          (Subtype.val '' (Subtype.val '' (cylEndProj hover ⁻¹' K))) ∩
          (cubeFaceIncl A q).obj '' C.M j₀ =
        (cubeFaceIncl A q).obj '' (A.X.π ⁻¹' (Subtype.val '' K) ∩ C.M j₀) := by
      intro j₀
      ext w
      constructor
      · rintro ⟨hw, y, hy, rfl⟩
        refine ⟨y, ⟨?_, hy⟩, rfl⟩
        obtain ⟨_, ⟨p, hpK, rfl⟩, hpw⟩ := hw
        have := A.X.cylEndMap_π p (q, y) hpw.symm
        exact ⟨cylEndProj hover p, hpK, this⟩
      · rintro ⟨y, ⟨⟨s, hsK, hsy⟩, hy⟩, rfl⟩
        refine ⟨?_, y, hy, rfl⟩
        obtain ⟨j, rfl⟩ := hrg j₀ y hy
        let p : cylEnd (X := A.X) Θ' (i : ℝ) :=
          ⟨⟨(A.X.cubeProd 1).π (q, y), (q, y), hsupp j y hy, rfl⟩, by
            change A.X.cylOrbitTime ((A.X.cubeProd 1).π (q, y)) = i
            rw [cylOrbitTime_π]⟩
        have hp : cylEndProj hover p = s := Subtype.ext (by
          change cylEndMap p = s.1
          rw [A.X.cylEndMap_π p (q, y) rfl]
          exact hsy.symm)
        exact ⟨_, ⟨p, by change cylEndProj hover p ∈ K; rw [hp]; exact hsK, rfl⟩, rfl⟩
    have hAm : ∀ j₀, (A.baseEP.epFormsInftyEval (m + 1)).sheetNull.IsMeasIn (C.M j₀)
        (A.X.π ⁻¹' (Subtype.val '' K) ∩ C.M j₀) := fun j₀ =>
      SheetNullSets.isMeasIn_inter_iff.2 (SheetNullSets.isMeasIn_of_borel hA₀)
    have hε' : (ε = 1 ∧ ∀ j, ∀ y ∈ A.X.π ⁻¹' (Subtype.val '' K) ∩ C.M (e j),
          (C'.boundaryOrient j.1).tangent ((cubeFaceIncl A q).obj y) =
            (faceOrient q (C.orient (e j)) (hS (e j)).1.1).tangent
              ((cubeFaceIncl A q).obj y)) ∨
        (ε = -1 ∧ ∀ j, ∀ y ∈ A.X.π ⁻¹' (Subtype.val '' K) ∩ C.M (e j),
          (C'.boundaryOrient j.1).tangent ((cubeFaceIncl A q).obj y) ≠
            (faceOrient q (C.orient (e j)) (hS (e j)).1.1).tangent
              ((cubeFaceIncl A q).obj y)) :=
      hε.imp (fun h => ⟨h.1, fun j y hy => h.2 j y hy.2⟩)
        (fun h => ⟨h.1, fun j y hy => h.2 j y hy.2⟩)
    have key := sheetSum_boundaryFamily_cubeFace q C C' hΘ' hCT' hS e he hrange hσ hM hA hAm
      hε' ω
    have hcard : Nat.card ((A.cubeSEP 1).X.Isotropy ((q, x) : (A.cubeSEP 1).Obj)) =
        Nat.card (A.X.Isotropy x) := A.X.card_isotropy_cubeProd 1 (q, x)
    rw [key, hcard]
    change _ = ε * ((Nat.card (A.X.Isotropy x) : ℝ)⁻¹ * _)
    ring

/-- **`∂Θ̃ = Θ₁ ⊔ −Θ₀` from matched structures** (proof of Corollary 15.4.4, p. 703): if the
ends of `|supp ∂Θ̃|` lie over `|supp Θ₀|`, `|supp Θ₁|` and every point of `supp Θᵢ` has
structures of `Θᵢ` and of `Θ̃` at `(i, x)` matching with sign `(−1)^{i+1}`, the boundary measure
of `pr^*ω` is `∫_{Θ₁} ω` on the end `1` and `−∫_{Θ₀} ω` on the end `0`. -/
theorem isCylinderBoundaryOf_of_matched {f : A.Obj → A.W} {m : ℕ}
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
    (h₀ : ∀ x ∈ EpGroupoid.supp (fun z => (P₀.Λ (f z) : ℚ)),
      ∃ (C : A.X.OrientedTameStructure (m + 1) (fun z => (P₀.Λ (f z) : ℚ)) x)
        (C' : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' ((fun _ => 0), x))
        (hCT' : C'.Represents T') (hS : ∀ j, C.M j ∈ (A.baseEP.epFormsInftyEval (m + 1)).sheets),
        C.Represents P₀.T ∧ AreMatchedAt (fun _ => 0) C C' hΘ' hCT' hS (-1))
    (h₁ : ∀ x ∈ EpGroupoid.supp (fun z => (P₁.Λ (f z) : ℚ)),
      ∃ (C : A.X.OrientedTameStructure (m + 1) (fun z => (P₁.Λ (f z) : ℚ)) x)
        (C' : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' ((fun _ => 1), x))
        (hCT' : C'.Represents T') (hS : ∀ j, C.M j ∈ (A.baseEP.epFormsInftyEval (m + 1)).sheets),
        C.Represents P₁.T ∧ AreMatchedAt (fun _ => 1) C C' hΘ' hCT' hS 1) :
    IsCylinderBoundaryOf P₀ P₁ hΘ' hcpt' hT' hloc' := by
  have e0 : ((0 : unitInterval) : ℝ) = 0 := rfl
  have e1 : ((1 : unitInterval) : ℝ) = 1 := rfl
  exact isCylinderBoundaryOf_of_local P₀ P₁ hΘ' hcpt' hT' hloc' hover₀ hover₁
    (isLocalEndIdentity_of_matched P₀ hΘ' hcpt' hT' hloc' (i := 0) hover₀ h₀)
    (isLocalEndIdentity_of_matched P₁ hΘ' hcpt' hT' hloc' (i := 1) hover₁ h₁)

end SBLocalization

end Polyfold
