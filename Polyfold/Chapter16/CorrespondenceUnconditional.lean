import Polyfold.Chapter16.InvariantUnconditional
import Polyfold.Chapter16.IndexZeroUnconditional
import Polyfold.Chapter16.IndexZeroInheritedCorrespondence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.6, p. 739:
**Definition 16.6.5** and **Theorem 16.6.6** across two models of the orientation, with no
sc-smooth partitions of unity on `Z`.

# The inherited orientation across two models, with bump functions only

The correspondence results of `CanonicalModelTransfer`, `InheritedOrientationGeneralPosition`
and `IndexZeroInheritedCorrespondence` assume `c.polyfold.AdmitsScPartitionsOfUnity`.  There it
enters in two ways: through sc-smooth bump functions in the models (Theorem 12.3.2 (1), used for
the canonical orientation of Theorem 15.4.1), and through Stokes' theorem in the cobordism
argument of Theorem 16.6.6.  Stokes' theorem holds with no partitions of unity
(`StokesUnconditional`), and the cobordisms come from the collar extension
(`InvariantUnconditional`, `IndexZeroUnconditional`).  So here the hypothesis is
`hbump : c.polyfold.AdmitsBumpFunctions` (Definition 16.1.5 (1)), which partitions of unity
imply.

* `OrientationRep.tame_bump_of_boundary_eq_empty_all`;
* `isInheritedFrom_of_correspondence_of_boundary_eq_empty_all`,
  `isInheritedFrom_iff_of_correspondence_all`, `integral_eq_of_correspondence_all`,
  `theorem_16_6_6_correspondence_all`, `theorem_16_6_6_correspondence_generalPosition_all`;
* index `0`: `isInheritedFromPoint_of_correspondence_of_boundary_eq_empty_all`,
  `isInheritedFromPoint_iff_of_correspondence_all`,
  `theorem_16_6_6_index_zero_correspondence_all`,
  `theorem_16_6_6_index_zero_correspondence_generalPosition_all`.
-/

open Set Function Topology

universe u

namespace Polyfold

open EPLocalization EpGroupoid SBLocalization PolyfoldClass

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure SEP

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

variable {s : FredholmSection c}

open OrientationRep

/-- For `∂Z = ∅` and `Z` with sc-smooth bump functions (Definition 16.1.5 (1), 2021 p. 712),
every model is tame (`d_X ≡ 0`) with sc-smooth bump functions and empty boundary:
`OrientationRep.tame_bump_of_boundary_eq_empty` with bump functions in place of partitions of
unity. -/
theorem OrientationRep.tame_bump_of_boundary_eq_empty_all
    (hbump : c.polyfold.AdmitsBumpFunctions) (hbd : c.polyfold.boundary = ∅)
    (o : OrientationRep s) :
    o.a.S.A.X.PObj.IsTame ∧ o.a.S.A.X.PObj.AdmitsBumpFunctions ∧
      ∀ x, x ∉ o.a.S.A.X.PObj.boundary := by
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  exact ⟨o.a.S.A.X.isTame_of_degIndex_eq_zero hd,
    (c.polyfold.definition_16_1_5_one).1 hbump o.a.S.toPolyfoldStructure
      (toPolyfoldStructure_mem o.a.hS),
    fun x hx => (Nat.one_le_iff_ne_zero.1 hx) (hd x)⟩

/-- **`IsInheritedFrom Can o Q → IsInheritedFrom Can o' Q` for `∂Z = ∅`** (2021 §16.6, p. 739),
with sc-smooth bump functions on `Z`: `isInheritedFrom_of_correspondence_of_boundary_eq_empty`
with `hbump` in place of partitions of unity. -/
theorem isInheritedFrom_of_correspondence_of_boundary_eq_empty_all
    (hbump : c.polyfold.AdmitsBumpFunctions) (hbd : c.polyfold.boundary = ∅)
    {o o' : OrientationRep s} (C : Correspondence o o') {m : ℕ}
    (hft : o'.a.S.A.B.IsScFredholmSectionTame o'.a.F)
    (hidx : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((m + 1 : ℕ) : ℤ))
    (hT : C.MiddleCanonical m) {Q : OrientedPerturbation s.1 m} :
    IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o Q →
      IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o' Q := by
  obtain ⟨hX, hb, hbd'⟩ := o'.tame_bump_of_boundary_eq_empty_all hbump hbd
  exact isInheritedFrom_of_correspondence C hX hb hft hidx hT
    fun _ _ x hx => absurd hx (hbd' x)

/-- **2021 §16.6, p. 739: the orientation inherited from `(f, o)` does not depend on the model of
`o`** (`∂Z = ∅`), with sc-smooth bump functions on `Z`: `isInheritedFrom_iff_of_correspondence`
with `hbump` in place of partitions of unity. -/
theorem isInheritedFrom_iff_of_correspondence_all (hbump : c.polyfold.AdmitsBumpFunctions)
    (hbd : c.polyfold.boundary = ∅) {o o' : OrientationRep s} (C : Correspondence o o')
    {m : ℕ} (hft : o.a.S.A.B.IsScFredholmSectionTame o.a.F)
    (hft' : o'.a.S.A.B.IsScFredholmSectionTame o'.a.F)
    (hidx : ∀ x ∈ o.a.S.A.X.PObj.smoothSet, o.a.S.A.B.IsIndexAt o.a.F x ((m + 1 : ℕ) : ℤ))
    (hidx' : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((m + 1 : ℕ) : ℤ))
    (hT : C.MiddleCanonical m) (hT' : C.symm.MiddleCanonical m)
    (Q : OrientedPerturbation s.1 m) :
    IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o Q ↔
      IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o' Q :=
  ⟨isInheritedFrom_of_correspondence_of_boundary_eq_empty_all hbump hbd C hft' hidx' hT,
    isInheritedFrom_of_correspondence_of_boundary_eq_empty_all hbump hbd C.symm hft hidx hT'⟩

/-- **2021 Theorem 16.6.6, p. 739, across two models of the orientation**, with sc-smooth bump
functions on `Z` and no partitions of unity: `integral_eq_of_correspondence` with `hbump` and
`CanonicalInput_all`.  The cobordism argument is `theorem_16_6_6_canonical_all`. -/
theorem integral_eq_of_correspondence_all (hbump : c.polyfold.AdmitsBumpFunctions)
    (n : Y → ℝ) (U : Set Z) {m : ℕ} (hbd : c.polyfold.boundary = ∅)
    (hcs : s.1.HasCompactSolutionSet) (hn : c.IsAuxNorm n) (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {o o' : OrientationRep s} (C : Correspondence o o')
    (H : CanonicalInput_all o (m + 1)) (hft' : o'.a.S.A.B.IsScFredholmSectionTame o'.a.F)
    (hidx' : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((m + 1 : ℕ) : ℤ))
    (hT : C.MiddleCanonical m) (hT' : C.symm.MiddleCanonical m)
    (Q₀ Q₁ : OrientedPerturbation s.1 m) (h₀ : Q₀.IsAdmissible n U)
    (hQ₀ : IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o Q₀)
    (h₁ : Q₁.IsAdmissible n U)
    (hQ₁ : IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o' Q₁)
    (τ : ScForm c.polyfold (m + 1)) (hτ : ScForm.d τ = 0) :
    Q₀.integral τ = Q₁.integral τ ∧ Q₀.integralEff τ = Q₁.integralEff τ := by
  have hQ₁' := (isInheritedFrom_iff_of_correspondence_all hbump hbd C H.tame hft' H.index hidx'
    hT hT' Q₁).2 hQ₁
  exact (theorem_16_6_6_canonical_all hbump s n U m hbd hcs hn hU hcc o).2 Q₀ Q₁ h₀ ⟨H, hQ₀⟩ h₁
    ⟨H, hQ₁'⟩ τ hτ

/-- **2021 Theorem 16.6.6, p. 739, across two models of the orientation**, with sc-smooth bump
functions on `Z` and no partitions of unity: `theorem_16_6_6_correspondence` with `hbump` and
`CanonicalInput_all`. -/
theorem theorem_16_6_6_correspondence_all (hbump : c.polyfold.AdmitsBumpFunctions)
    (n : Y → ℝ) (U : Set Z) {m : ℕ} (hbd : c.polyfold.boundary = ∅)
    (hcs : s.1.HasCompactSolutionSet) (hn : c.IsAuxNorm n) (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {o o' : OrientationRep s} (C : Correspondence o o')
    (H : CanonicalInput_all o (m + 1))
    (hidx' : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((m + 1 : ℕ) : ℤ))
    (Q₀ Q₁ : OrientedPerturbation s.1 m) (h₀ : Q₀.IsAdmissible n U)
    (hQ₀ : IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o Q₀)
    (h₁ : Q₁.IsAdmissible n U)
    (hQ₁ : IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o' Q₁)
    (τ : ScForm c.polyfold (m + 1)) (hτ : ScForm.d τ = 0) :
    Q₀.integral τ = Q₁.integral τ ∧ Q₀.integralEff τ = Q₁.integralEff τ :=
  integral_eq_of_correspondence_all hbump n U hbd hcs hn hU hcc C H
    (C.isScFredholmSectionTame H.tame) hidx' (C.middleCanonical m) (C.symm.middleCanonical m)
    Q₀ Q₁ h₀ hQ₀ h₁ hQ₁ τ hτ

/-- **2021 Theorem 16.6.6 across two models, for perturbations in general position** (p. 739),
with sc-smooth bump functions on `Z` and no partitions of unity. -/
theorem theorem_16_6_6_correspondence_generalPosition_all
    (hbump : c.polyfold.AdmitsBumpFunctions) (n : Y → ℝ) (U : Set Z) {m : ℕ}
    (hbd : c.polyfold.boundary = ∅) (hcs : s.1.HasCompactSolutionSet) (hn : c.IsAuxNorm n)
    (hU : IsOpen U) (hcc : s.1.ControlsCompactness n U) {o o' : OrientationRep s}
    (C : Correspondence o o') (H : CanonicalInput_all o (m + 1))
    (hidx' : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((m + 1 : ℕ) : ℤ))
    (Q₀ Q₁ : OrientedPerturbation s.1 m) (h₀ : Q₀.IsAdmissible n U)
    (hQ₀ : IsInheritedFrom IsCanonicalInGeneralPosition o Q₀) (h₁ : Q₁.IsAdmissible n U)
    (hQ₁ : IsInheritedFrom IsCanonicalInGeneralPosition o' Q₁)
    (τ : ScForm c.polyfold (m + 1)) (hτ : ScForm.d τ = 0) :
    Q₀.integral τ = Q₁.integral τ ∧ Q₀.integralEff τ = Q₁.integralEff τ :=
  theorem_16_6_6_correspondence_all hbump n U hbd hcs hn hU hcc C H hidx' Q₀ Q₁ h₀
    hQ₀.of_generalPosition h₁ hQ₁.of_generalPosition τ hτ

/-! ### Fredholm index `0` -/

/-- **`IsInheritedFromPoint o Q → IsInheritedFromPoint o' Q` for `∂Z = ∅`** (2021 §16.6,
p. 739, index `0`), with sc-smooth bump functions on `Z`:
`isInheritedFromPoint_of_correspondence_of_boundary_eq_empty` with `hbump` in place of
partitions of unity. -/
theorem isInheritedFromPoint_of_correspondence_of_boundary_eq_empty_all
    (hbump : c.polyfold.AdmitsBumpFunctions) (hbd : c.polyfold.boundary = ∅)
    {o o' : OrientationRep s} (C : Correspondence o o')
    (hft : o'.a.S.A.B.IsScFredholmSectionTame o'.a.F)
    (hidx : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((0 : ℕ) : ℤ))
    {Q : PointOrientedPerturbation s.1} :
    IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o Q →
      IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o' Q := by
  rintro ⟨P, hP, rfl⟩
  obtain ⟨hX, hb, hbd'⟩ := o'.tame_bump_of_boundary_eq_empty_all hbump hbd
  obtain ⟨P', -, hC₂, heq⟩ := isInheritedFromPoint_of_diagram C hX hb hft hidx P hP
    fun x hx => absurd hx (hbd' x)
  exact ⟨P', hC₂, heq⟩

/-- **2021 §16.6, p. 739, for Fredholm index `0` and `∂Z = ∅`: the inherited orientation does
not depend on the model**, with sc-smooth bump functions on `Z`:
`isInheritedFromPoint_iff_of_correspondence` with `hbump` in place of partitions of unity. -/
theorem isInheritedFromPoint_iff_of_correspondence_all (hbump : c.polyfold.AdmitsBumpFunctions)
    (hbd : c.polyfold.boundary = ∅) {o o' : OrientationRep s} (C : Correspondence o o')
    (hft : o.a.S.A.B.IsScFredholmSectionTame o.a.F)
    (hidx : ∀ x ∈ o.a.S.A.X.PObj.smoothSet, o.a.S.A.B.IsIndexAt o.a.F x ((0 : ℕ) : ℤ))
    (hidx' : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((0 : ℕ) : ℤ))
    (Q : PointOrientedPerturbation s.1) :
    IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o Q ↔
      IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o' Q :=
  ⟨isInheritedFromPoint_of_correspondence_of_boundary_eq_empty_all hbump hbd C
      (C.isScFredholmSectionTame hft) hidx',
    isInheritedFromPoint_of_correspondence_of_boundary_eq_empty_all hbump hbd C.symm hft hidx⟩

/-- **2021 Theorem 16.6.6, p. 739, for Fredholm index `0`, across two models of the
orientation**, with sc-smooth bump functions on `Z` and no partitions of unity:
`theorem_16_6_6_index_zero_correspondence` with `hbump` and `IndexZeroInput_all`; the compact
solution set is not used for the cobordism (`hasOrientedCobordism_of_indexZeroInput_all`). -/
theorem theorem_16_6_6_index_zero_correspondence_all (hbump : c.polyfold.AdmitsBumpFunctions)
    (n : Y → ℝ) (U : Set Z) (hbd : c.polyfold.boundary = ∅)
    (hcs : s.1.HasCompactSolutionSet) (hn : c.IsAuxNorm n) (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {o o' : OrientationRep s} (C : Correspondence o o')
    (H : IndexZeroInput_all o)
    (hidx' : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((0 : ℕ) : ℤ))
    (Q₀ Q₁ : PointOrientedPerturbation s.1) (h₀ : Q₀.IsAdmissible n U)
    (hQ₀ : IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o Q₀)
    (h₁ : Q₁.IsAdmissible n U)
    (hQ₁ : IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o' Q₁)
    (τ : ScForm c.polyfold 0) (hτ : ScForm.d τ = 0) :
    Q₀.count τ = Q₁.count τ ∧ Q₀.countEff τ = Q₁.countEff τ := by
  have hidx : ∀ x ∈ o.a.S.A.X.PObj.smoothSet, o.a.S.A.B.IsIndexAt o.a.F x ((0 : ℕ) : ℤ) :=
    fun x hx => by exact_mod_cast H.index x hx
  have hQ₁' := (isInheritedFromPoint_iff_of_correspondence_all hbump hbd C H.tame hidx hidx'
    Q₁).2 hQ₁
  have key : theorem_16_6_6_index_zero_polyfold_statement s n U
      (fun o'' Q => o'' = o ∧
        IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o'' Q) := by
    refine theorem_16_6_6_index_zero_polyfold_hyp_all s n U _ ?_
    rintro o'' P₀ P₁ - ⟨rfl, M₀, c₀, rfl⟩ - ⟨-, M₁, c₁, rfl⟩
    obtain ⟨h, he⟩ := hasOrientedCobordism_of_indexZeroInput_all hbump hbd H M₀ M₁ c₀ c₁
    exact ⟨hasCobordism_pointSuborbifold_all h, hasCobordismEff_pointSuborbifold_all he⟩
  exact key hbd hcs hn hU hcc o Q₀ Q₁ h₀ ⟨rfl, hQ₀⟩ h₁ ⟨rfl, hQ₁'⟩ τ hτ

/-- **2021 Theorem 16.6.6 for Fredholm index `0` across two models, for perturbations in general
position** (p. 739), with sc-smooth bump functions on `Z` and no partitions of unity. -/
theorem theorem_16_6_6_index_zero_correspondence_generalPosition_all
    (hbump : c.polyfold.AdmitsBumpFunctions) (n : Y → ℝ) (U : Set Z)
    (hbd : c.polyfold.boundary = ∅) (hcs : s.1.HasCompactSolutionSet) (hn : c.IsAuxNorm n)
    (hU : IsOpen U) (hcc : s.1.ControlsCompactness n U) {o o' : OrientationRep s}
    (C : Correspondence o o') (H : IndexZeroInput_all o)
    (hidx' : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((0 : ℕ) : ℤ))
    (Q₀ Q₁ : PointOrientedPerturbation s.1) (h₀ : Q₀.IsAdmissible n U)
    (hQ₀ : IsInheritedFromPoint IsPointCanonicalInGeneralPosition o Q₀)
    (h₁ : Q₁.IsAdmissible n U)
    (hQ₁ : IsInheritedFromPoint IsPointCanonicalInGeneralPosition o' Q₁)
    (τ : ScForm c.polyfold 0) (hτ : ScForm.d τ = 0) :
    Q₀.count τ = Q₁.count τ ∧ Q₀.countEff τ = Q₁.countEff τ :=
  theorem_16_6_6_index_zero_correspondence_all hbump n U hbd hcs hn hU hcc C H hidx' Q₀ Q₁ h₀
    hQ₀.of_generalPosition h₁ hQ₁.of_generalPosition τ hτ

end StrongPolyfoldBundle

end Polyfold
