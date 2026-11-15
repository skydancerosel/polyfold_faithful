import Polyfold.Chapter16.IndexZeroInheritedCorrespondence
import Polyfold.Chapter16.IndexZeroIsotropyWitness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.6, p. 739:
**Definition 16.6.5** and **Theorem 16.6.6 for Fredholm index `0`**, with **Remark 10.5.5**
(p. 508) and **Theorem 12.5.7 (2)**.  Numbers and pages are the 2021 text's.

# The model independence of dimension `0` along a diagram which is not the identity

## The example

The strong bundle `ℝ × ℝ → ℝ` over `ℤ/3 × ℝ ⇉ ℝ` (trivial action; every isotropy group is
`ℤ/3`, the fibres are not zero), the section `f(x) = (x, x² − 1)` with the orientation
`z3Orientation` (`z3OrientationRep`), and the diagram `W ←1 W →Inv W` of Remark 10.5.5, with
`Inv (g, x) = (g⁻¹, x)`: `[Inv] ≠ [1]` (already the generalized maps of the bases differ), and
`|[Inv]| = |[1]|`.

## What is formalized (namespace `Polyfold.StrongBundleLocalizationExamples`)

* `pullOr_ofHom_z3InvHom`: `1^* o = Inv^* o` over `W ←1 W →Inv W` (from the uniqueness of the
  corresponding orientation in Theorem 12.5.7 (2), `theorem_12_5_7_two_orbitMap_unique_z3`).
* `z3InvCorrespondence`: the correspondence of `z3OrientationRep` with itself over
  `W ←1 W →Inv W`.
* **`theorem_16_6_6_index_zero_correspondence_z3`**: `[Inv] ≠ [1]`, a morphism which is not a
  unit, non-zero fibres, `Z` with sc-smooth partitions of unity and `∂Z = ∅`, compact solution
  set, and a canonically oriented regular perturbation `P` of dimension `0` with the two points
  `±1` in its support, such that: the perturbation `[Inv]_* Λ` of the other model with its
  canonical orientation gives the same oriented perturbed solution set
  (`isInheritedFromPoint_of_diagram`), the iff `isInheritedFromPoint_iff_of_correspondence`
  applies, and `theorem_16_6_6_index_zero_correspondence` applies, all over `z3InvCorrespondence`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace StrongBundleLocalizationExamples

open SBLocalization StrongBundle EpGroupoid SEP StrongBundleEquivalenceExamples TrivialBundle
  StrongPolyfoldBundle StrongPolyfoldBundleStructure OrientationRep

variable {k : ℕ} {φ : (Fin 1 → ℝ) → (Fin k → ℝ)}

/-- `1^* f = Inv^* f` over `W ←1 W →Inv W`, for the graph section `f` of a `C^∞` map. -/
theorem pullback_ofHom_z3InvHom (hφ : ContDiff ℝ ∞ φ) :
    (SDiagram.ofHom (z3InvHom k)).hΦ.pullback (graphSection φ) =
      (sbe (z3InvHom_mem_equivalences k)).pullback (graphSection φ) := by
  have hF : (z3SEP k).E.IsScFredholmSectionFunctor (graphSection φ) :=
    isScFredholmSectionFunctor_graphSection_z3 hφ
  funext x
  have h1 := (SDiagram.ofHom (z3InvHom k)).hΦ.obj_pullback hF.1.1.1 x
  have h2 := (sbe (z3InvHom_mem_equivalences k)).obj_pullback hF.1.1.1 x
  exact h1.trans h2.symm

/-- **`1^* o = Inv^* o` over `W ←1 W →Inv W`** (Definition 16.6.5 for the diagram of Remark
10.5.5): Theorem 12.5.7 (2) gives exactly one orientation `o'` corresponding to `o` over every
diagram of every generalized isomorphism `𝔄'` with `|𝔄'| = |[1]|` and `𝔄'_* f = f`; the identity
diagram gives `o' = o`, and the diagram of `[Inv]` then gives `Inv^* o = 1^* o`. -/
theorem pullOr_ofHom_z3InvHom (hφ : ContDiff ℝ ∞ φ) :
    (SDiagram.ofHom (z3InvHom k)).hΦ.pullOr
        ((EpStrongBundle.theorem_10_4_5_fred (SDiagram.ofHom (z3InvHom k)).hΦ).2.1
          (isScFredholmSectionFunctor_graphSection_z3 hφ))
        (isScFredholmSectionFunctor_graphSection_z3 hφ) rfl (hasScPlusSectionsThrough_z3SEP k)
        (hasScPlusSectionsThrough_z3SEP k) (z3Orientation hφ) =
      (sbe (z3InvHom_mem_equivalences k)).pullOr
        ((EpStrongBundle.theorem_10_4_5_fred (SDiagram.ofHom (z3InvHom k)).hΦ).2.1
          (isScFredholmSectionFunctor_graphSection_z3 hφ))
        (isScFredholmSectionFunctor_graphSection_z3 hφ) (pullback_ofHom_z3InvHom hφ)
        (hasScPlusSectionsThrough_z3SEP k) (hasScPlusSectionsThrough_z3SEP k)
        (z3Orientation hφ) := by
  have hF := isScFredholmSectionFunctor_graphSection_z3 (k := k) hφ
  obtain ⟨hInv, h₁, -, horb, -, -, o', ⟨-, ho'⟩, -⟩ := theorem_12_5_7_two_orbitMap_unique_z3
    (k := k) hφ
  obtain ⟨-, hId, -, -, -⟩ := remark_10_5_5 k
  have h₂ : graphSection φ = GenSBMap.pushforward hId (graphSection φ) :=
    ((GenSBMap.pushforward_eq hId rfl (SEP.equivalences.id_mem _) hF.1).trans
      (SDiagram.pushforward_id _ hF.1)).symm
  have e : o' = z3Orientation hφ := by
    funext v hv
    exact (Equiv.injective _) (ho' _ hId rfl h₂ (SDiagram.id (z3SEP k)) rfl v hv)
  subst e
  funext v hv
  exact (ho' _ hInv horb h₁ (SDiagram.ofHom (z3InvHom k)) rfl v hv).symm

/-- **The correspondence of `z3OrientationRep` with itself over `W ←1 W →Inv W`**
(Definition 16.6.5, Remark 10.5.5): `|[1, Inv]| = id`, `1^* f = Inv^* f`, `1^* o = Inv^* o`. -/
def z3InvCorrespondence (hφ : ContDiff ℝ ∞ φ) :
    Correspondence (z3OrientationRep hφ) (z3OrientationRep hφ) :=
  Correspondence.ofDiagram (SDiagram.ofHom (z3InvHom k)) (z3InvHom_mem_equivalences k)
    (by
      have h := orbitMap_ofHom_z3InvHom k
      rw [SDiagram.orbitMap_id'] at h
      change ⇑(z3Structure k).Γ ∘ (SDiagram.ofHom (z3InvHom k)).orbitMap = ⇑(z3Structure k).Γ
      rw [h]; rfl) (pullback_ofHom_z3InvHom hφ)
    (hasScPlusSectionsThrough_z3SEP k) (pullOr_ofHom_z3InvHom hφ)

/-- The diagram of `z3InvCorrespondence` is not the identity: `[Inv] ≠ [1]`. -/
theorem z3InvCorrespondence_cls_ne (hφ : ContDiff ℝ ∞ φ) :
    (z3InvCorrespondence hφ).D.cls ≠ (SDiagram.id (z3SEP k)).cls :=
  (remark_10_5_5 k).2.2.2.2

/-- `|ℤ/3 × ℝ ⇉ ℝ|` has no boundary. -/
theorem z3Bundle_boundary_eq_empty : (z3Bundle k).polyfold.boundary = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
  obtain ⟨x, rfl⟩ := (z3Structure k).surjective_γπ z
  have hx := (mem_boundary_iff_obj (c := z3Bundle k) rfl x).1 hz
  have h : (0 : ℕ) < (z3SEP k).X.PObj.degIndex x := hx
  have h0 : (z3SEP k).X.PObj.degIndex x = 0 := MPolyfold.degIndex_rn x
  omega

/-- `|ℤ/3 × ℝ ⇉ ℝ|` admits sc-smooth partitions of unity (Definition 16.1.5 (2)). -/
theorem z3Bundle_admitsScPartitionsOfUnity :
    (z3Bundle k).polyfold.AdmitsScPartitionsOfUnity :=
  ⟨(z3Structure k).toPolyfoldStructure, rfl, (z3SEP k).X.theorem_7_5_7
    EpGroupoid.Examples.hasParacompactOrbitSpace_trivialZ3
    (rnPolyfold_admitsScPartitionsOfUnity 1)⟩

/-- **Theorem 16.6.6 for Fredholm index `0` across two models, over a diagram which is not the
identity** (§16.6, p. 739; Remark 10.5.5): for `f(x) = (x, x² − 1)` over `|ℤ/3 × ℝ ⇉ ℝ|` with
the orientation `z3OrientationRep` and the correspondence `z3InvCorrespondence` over
`W ←1 W →Inv W` (`[Inv] ≠ [1]`): a morphism is not a unit, the fibres are not zero, `Z` admits
sc-smooth partitions of unity, `∂Z = ∅`, `S_f` is compact, and there is a canonically oriented
regular perturbation `P` of dimension `0` with `±1` in its support such that
`isInheritedFromPoint_of_diagram` gives a canonically oriented `P'` with `Λ' = [Inv]_* Λ` and
the same oriented perturbed solution set `θ̂`, `θ̂` is inherited from the orientation, the iff
`isInheritedFromPoint_iff_of_correspondence` holds, and the counts agree as in
`theorem_16_6_6_index_zero_correspondence`. -/
theorem theorem_16_6_6_index_zero_correspondence_z3 :
    (z3InvCorrespondence (k := 1) contDiff_twoPointMap).D.cls ≠ (SDiagram.id (z3SEP 1)).cls ∧
    (∃ σ : (z3SEP 1).Mor, σ ≠ (z3SEP 1).X.unit ((z3SEP 1).X.src σ)) ∧
    (∀ y : (z3SEP 1).Obj, Nontrivial ((z3SEP 1).P ⁻¹' {y})) ∧
    (z3Bundle 1).polyfold.AdmitsScPartitionsOfUnity ∧ (z3Bundle 1).polyfold.boundary = ∅ ∧
    (z3FredholmSection (k := 1) contDiff_twoPointMap).1.HasCompactSolutionSet ∧
    ∃ P : PointPerturbation (z3SEP 1) (graphSection twoPointMap),
      P.IsCanonical (z3OrientationRep (k := 1) contDiff_twoPointMap).hF.2
        (z3OrientationRep (k := 1) contDiff_twoPointMap).hsec
        (z3OrientationRep (k := 1) contDiff_twoPointMap).o ∧
      (fun _ => (1 : ℝ)) ∈ EpGroupoid.supp (fun z => (P.Λ (graphSection twoPointMap z) : ℚ)) ∧
      (fun _ => (-1 : ℝ)) ∈ EpGroupoid.supp (fun z => (P.Λ (graphSection twoPointMap z) : ℚ)) ∧
      (∃ P' : PointPerturbation (z3SEP 1) (graphSection twoPointMap),
        P'.Λ = (z3InvCorrespondence (k := 1) contDiff_twoPointMap).D.pushMult
          (z3InvCorrespondence (k := 1) contDiff_twoPointMap).hΨ P.Λ ∧
        P'.IsCanonical (z3OrientationRep (k := 1) contDiff_twoPointMap).hF.2
          (z3OrientationRep (k := 1) contDiff_twoPointMap).hsec
          (z3OrientationRep (k := 1) contDiff_twoPointMap).o ∧
        toPointOrientedPerturbation (z3OrientationRep (k := 1) contDiff_twoPointMap).a P'
            (z3OrientationRep (k := 1) contDiff_twoPointMap).ha =
          toPointOrientedPerturbation (z3OrientationRep (k := 1) contDiff_twoPointMap).a P
            (z3OrientationRep (k := 1) contDiff_twoPointMap).ha) ∧
      IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o)
        (z3OrientationRep (k := 1) contDiff_twoPointMap)
        (toPointOrientedPerturbation (z3OrientationRep (k := 1) contDiff_twoPointMap).a P
          (z3OrientationRep (k := 1) contDiff_twoPointMap).ha) ∧
      (∀ Q : PointOrientedPerturbation (z3FredholmSection (k := 1) contDiff_twoPointMap).1,
        IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o)
            (z3OrientationRep (k := 1) contDiff_twoPointMap) Q ↔
          IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o)
            (z3OrientationRep (k := 1) contDiff_twoPointMap) Q) ∧
      ∀ (n : _ → ℝ) (U : Set _), (z3Bundle 1).IsAuxNorm n → IsOpen U →
        (z3FredholmSection (k := 1) contDiff_twoPointMap).1.ControlsCompactness n U →
        ∀ Q₀ Q₁ : PointOrientedPerturbation (z3FredholmSection (k := 1) contDiff_twoPointMap).1,
          Q₀.IsAdmissible n U →
          IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o)
            (z3OrientationRep (k := 1) contDiff_twoPointMap) Q₀ →
          Q₁.IsAdmissible n U →
          IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o)
            (z3OrientationRep (k := 1) contDiff_twoPointMap) Q₁ →
          ∀ τ : PolyfoldClass.ScForm (z3Bundle 1).polyfold 0, PolyfoldClass.ScForm.d τ = 0 →
            Q₀.count τ = Q₁.count τ ∧ Q₀.countEff τ = Q₁.countEff τ := by
  set o := z3OrientationRep (k := 1) contDiff_twoPointMap
  set C := z3InvCorrespondence (k := 1) contDiff_twoPointMap
  have H := indexZeroInput_z3OrientationRep
  have hidx : ∀ x ∈ o.a.S.A.X.PObj.smoothSet, o.a.S.A.B.IsIndexAt o.a.F x ((0 : ℕ) : ℤ) :=
    fun x hx => by exact_mod_cast H.index x hx
  have hPU := z3Bundle_admitsScPartitionsOfUnity (k := 1)
  have hbd := z3Bundle_boundary_eq_empty (k := 1)
  obtain ⟨hX, hbump, hbd'⟩ := o.tame_bump_of_boundary_eq_empty hPU hbd
  obtain ⟨hne, hnu, -⟩ := corollary_15_4_4_index_zero_hypotheses_z3
  obtain ⟨P, -, hP, h1, h2⟩ := exists_isCanonical_z3
  have hcs : (z3FredholmSection (k := 1) contDiff_twoPointMap).1.HasCompactSolutionSet :=
    (z3GraphRep contDiff_twoPointMap).hasCompactSolutionSet_iff.2
      hasCompactSolutionSetEp_twoPoint_z3
  refine ⟨z3InvCorrespondence_cls_ne contDiff_twoPointMap, hnu, hne, hPU, hbd, hcs, P, hP, h1, h2,
    isInheritedFromPoint_of_diagram C hX hbump H.tame hidx P hP fun x hx => absurd hx (hbd' x),
    ⟨P, hP, rfl⟩, isInheritedFromPoint_iff_of_correspondence hPU hbd C H.tame hidx hidx,
    fun n U hn hU hcc Q₀ Q₁ h₀ hQ₀ h₁ hQ₁ τ hτ =>
      theorem_16_6_6_index_zero_correspondence hPU n U hbd hcs hn hU hcc C H hidx Q₀ Q₁ h₀ hQ₀
        h₁ hQ₁ τ hτ⟩

end StrongBundleLocalizationExamples

end Polyfold
