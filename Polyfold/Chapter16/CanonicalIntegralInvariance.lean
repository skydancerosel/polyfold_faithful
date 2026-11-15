import Polyfold.Chapter16.ModelPerturbations
import Polyfold.Chapter16.IndexZeroCylinder

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.6, p. 739:
**Theorem 16.6.6** (2017: Theorem 16.8) for the canonical orientations of Definition 15.4.2,
with Definition 16.6.5 (p. 739), Corollary 15.4.4 (p. 703) and Theorem 6.6.17 (p. 275).

# Theorem 16.6.6 for the orientation inherited from `(f, o)`

## The text, paraphrased

(Definition 16.6.5) An orientation of an sc-Fredholm section `f` of `p : Y → Z` is an
orientation `o` of a representative `(W, F)` (Definition 12.5.4: a continuous section of
`O_F → X_∞`, invariant under the morphisms).  (p. 739) For a generic `λ` the perturbed solution
set `θ = λ ∘ f` carries the orientation inherited from `(f, o)` (Theorem 15.4.1, Definition
15.4.2).  (Theorem 16.6.6) For `∂Z = ∅`, `f` oriented with compact solution set and `(n, U)`
controlling compactness, `∫_θ̂ τ` and `∮_θ̂ τ` do not depend on `λ` for closed `τ` and depend
only on `[τ]`.  The proof is Corollary 15.4.4 in the model of `o`: the cylinder `[0, 1] × X`
oriented by `e ∧ o`.

## What is formalized

* **`OrientationRep.isSectionOrientation`**: the orientation `o` of Definition 16.6.5 (continuous
  for any topology on `O_F` with the properties of Theorem 6.6.17) is an orientation of `F` in the
  sense of Definition 6.6.16, for a tame object M-polyfold with bump functions and tame germ data:
  the topology of Theorem 6.6.17 is unique (`eq_orTopology_of`).
* `CanonicalInput o k`: the standing hypotheses in the model of `o`: sc-smooth partitions of
  unity on the object M-polyfold of `[0, 1] × X` (Stokes on the cobordism), tame germ data of
  `F`, and Fredholm index `k` at every smooth point.
* `SBLocalization.cylinderOrientationStatement_of_isCanonical`: the end identities of the
  cylinder (`CylinderOrientationStatement` and its effective form) for any two regular
  perturbations with the canonical orientation of `(f, o)`, from Corollary 15.4.4's pieces
  (Theorem 15.4.1 on the cylinder, the frame convention, the invariance of `e ∧ o`).
* **`cylinderInput_canonical`**: every field of `CylinderInput` for the canonical orientations,
  from `∂Z = ∅`, partitions of unity on `Z` and `CanonicalInput o (m + 1)`.
* **`theorem_16_6_6_canonical`**: Theorem 16.6.6 for the orientation inherited from `(f, o)`,
  for every orientation satisfying the standing hypotheses in its model, with partitions of unity
  on `Z` as the only further hypothesis; `theorem_16_6_6_canonical_of_forall`: the same with the
  standing hypotheses assumed for all orientations.
* Fredholm index `0`: `indexZeroInput_of_canonicalInput` (the field `orient` of
  `IndexZeroInput` is derived), **`theorem_16_6_6_index_zero_canonical_input`**,
  `theorem_16_6_6_index_zero_polyfold_canonical_input` (for every orientation with the standing
  hypotheses in its model), `theorem_16_6_6_index_zero_inherited`,
  `theorem_16_6_6_index_zero_polyfold_inherited` (the standing hypotheses for all orientations).

## Reading

The orientation inherited from `(f, o)` is read in the model carrying `o` (as in
`theorem_16_6_6_of_model`).  The hypotheses beyond the text are sc-smooth partitions of unity on
`Z` and on `[0, 1] × X` of the model (Stokes, Theorems 9.5.17, 9.5.18 as printed; gap G.153).
Tame germ data are the text's hypothesis under the adopted reading of "strong bundle over a tame
M-polyfold"; the index is the text's "degree equal to the index".
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP UnitCube

variable {A : SEP.{u}} {f : A.Obj → A.W}

/-- **The end identities of the cylinder for two canonically oriented perturbations** (proof of
Corollary 15.4.4, 2021 p. 703).  Let `d_X ≡ 0`, `X` with sc-smooth bump functions, `(f, o)` an
oriented sc-Fredholm section functor (Definitions 6.6.16, 12.5.4) with tame germ data and index
`m + 1`, and `P₀`, `P₁` regular perturbations with the canonical orientation of `(f, o)`.  Then
every regular perturbation `Λ̃` of `f̃` on `[0, 1] × X` with `Λ̃ = Λᵢ` over `t = i` carries an
orientation (the canonical one for `(f̃, e ∧ o)`) with `∂Θ̃ = Θ₁ ⊔ −Θ₀` for the measures, and the
same for the effective measures. -/
theorem cylinderOrientationStatement_of_isCanonical (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hbump : A.X.PObj.AdmitsBumpFunctions) (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hf.2 o)
    (hinv : A.E.IsOrInvariant hf hsec o)
    {m : ℕ} (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ))
    (P₀ P₁ : OrientedRegularPerturbation A f m)
    (h₀ : IsCanonicalPerturbation hf.2 hsec o P₀) (h₁ : IsCanonicalPerturbation hf.2 hsec o P₁) :
    CylinderOrientationStatement hf.1.1.1 P₀ P₁ ∧
      ∀ (hLUC : A.X.IsLUC) (hLUCC : (A.cubeSEP 1).X.IsLUC),
        CylinderOrientationEffStatement hf.1.1.1 hLUC hLUCC P₀ P₁ := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hXC : (A.cubeSEP 1).X.IsTame := A.X.isTame_cubeProd 1 hX
  have hbumpC : (A.cubeSEP 1).X.PObj.AdmitsBumpFunctions := admitsBumpFunctions_prod_cube hbump
  have hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough :=
    MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbumpC
  have hftC := isScFredholmSectionTame_cubeLiftEp (n := 1) hft
  have honto := isBoundaryFaceOnto_cubeGlue hd hf hft P₀.isRegular.2.2.2.2 P₁.isRegular.2.2.2.2
  have hinvC := isOrInvariant_cubeOrientation hf hft hsec hsec' o hinv
  have hK₀ : IsKernelCanonical P₀.Λ hf.2 hsec o P₀.T :=
    IsCanonicalFor.isKernelCanonical h₀ (canonContinuous P₀.Λ hX hbump hft hsec o ho)
  have hK₁ : IsKernelCanonical P₁.Λ hf.2 hsec o P₁.T :=
    IsCanonicalFor.isKernelCanonical h₁ (canonContinuous P₁.Λ hX hbump hft hsec o ho)
  have hconv₀ := cylinderKernelFrameConvention_of_isIndexAt hf hft hsec hsec' o hidx hbump
    (fun _ => 0)
  have hconv₁ := cylinderKernelFrameConvention_of_isIndexAt hf hft hsec hsec' o hidx hbump
    (fun _ => 1)
  have hor : CylinderKernelCanonicalStatement hf hft hsec' (cubeOrientation hf hft hsec o)
      P₀ P₁ :=
    cylinderKernelCanonicalStatement_of_isCanonicalFor
      (fun Λ' => canonContinuous Λ' hXC hbumpC hftC hsec' (cubeOrientation hf hft hsec o)
        (isSectionOrientation_cubeOrientation hX hbump hf hft ho))
      (fun Λ' hreg e0 e1 => ⟨_, theorem_15_4_1_cylinder hd hbump hf hft hsec hsec' o ho hinvC
        hidx hreg.2.1.1 hreg.2.2.2.2 e0 e1 honto⟩)
  exact ⟨cylinderOrientationStatement_of_local_ends hf.1.1.1
      (cylinderLocalEndsStatement_of_kernelCanonical hd honto hK₀ hK₁ hconv₀ hconv₁ hor),
    fun hLUC hLUCC => cylinderOrientationEffStatement_of_local_ends hf.1.1.1
      (cylinderLocalEndsEffStatement_of_kernelCanonical hd hLUC hLUCC honto hK₀ hK₁ hconv₀ hconv₁
        hor)⟩

end SBLocalization

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure PolyfoldClass SBLocalization SEP

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-! ### Definition 16.6.5 against Definition 6.6.16 -/

/-- **An orientation in the sense of Definition 16.6.5 is one in the sense of Definition 6.6.16**
(2021 pp. 274–275, 739): for a tame object M-polyfold with sc-smooth bump functions and tame germ
data of `F`, the topology `t` of `O_F` carried by `o` is the topology of Theorem 6.6.17 (unique:
`eq_orTopology_of`), and `x ↦ o_x` is continuous for it, so `o` is an orientation of `F`
(`isSectionOrientation_iff_continuous`). -/
theorem OrientationRep.isSectionOrientation {s : FredholmSection c} (o : OrientationRep s)
    (hX : o.a.S.A.X.PObj.IsTame) (hbump : o.a.S.A.X.PObj.AdmitsBumpFunctions)
    (hft : o.a.S.A.B.IsScFredholmSectionTame o.a.F) :
    haveI := paracompactSpace_rn_prod o.a.S.A.X.PObj
    haveI := paracompactSpace_rn_pullback o.a.S.A.B
    IsSectionOrientation o.a.F o.hF.2 o.o := by
  have := paracompactSpace_rn_prod o.a.S.A.X.PObj
  have := paracompactSpace_rn_pullback o.a.S.A.B
  have := paracompactSpace_rn_rn_prod o.a.S.A.X.PObj
  have := paracompactSpace_rn_rn_pullback o.a.S.A.B
  have ht : o.t = orTopology (orLocalTransport hX hbump hft o.hsec) :=
    eq_orTopology_of hX hbump hft o.hsec o.isOrientationTopology.isLocalHomeomorph
      o.isOrientationTopology.propagation
  have hc := o.isOrientation.1
  rw [ht] at hc
  exact (isSectionOrientation_iff_continuous hX hbump hft o.hsec o.o).2 hc

/-- **The orientation of Definition 16.6.5 is one of Definition 6.6.16 when `∂Z = ∅`**: the
model is then tame (`d_X ≡ 0`), and sc-smooth partitions of unity on `Z` give sc-smooth bump
functions on the model (Theorem 12.3.2 (1)). -/
theorem OrientationRep.isSectionOrientation_of_boundary_eq_empty
    (hPU : c.polyfold.AdmitsScPartitionsOfUnity) (hbd : c.polyfold.boundary = ∅)
    {s : FredholmSection c} (o : OrientationRep s)
    (hft : o.a.S.A.B.IsScFredholmSectionTame o.a.F) :
    haveI := paracompactSpace_rn_prod o.a.S.A.X.PObj
    haveI := paracompactSpace_rn_pullback o.a.S.A.B
    IsSectionOrientation o.a.F o.hF.2 o.o := by
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  have hPUq := (c.polyfold.definition_16_1_5_two).1 hPU o.a.S.toPolyfoldStructure
    (toPolyfoldStructure_mem o.a.hS)
  exact o.isSectionOrientation (o.a.S.A.X.isTame_of_degIndex_eq_zero hd)
    (o.a.S.A.X.theorem_12_3_2_1.1
      (EpGroupoid.admitsBumpFunctionsPointwise_of_hasScPartitionsOfUnity hPUq)) hft

/-! ### The standing hypotheses in the model of an orientation -/

/-- **The standing hypotheses of Theorem 16.6.6 in the model of an orientation `o`**, Fredholm
index `k`: sc-smooth partitions of unity on the object M-polyfold of `[0, 1] × X` (Stokes on the
cobordism), tame germ data of the representative `F`, and index `k` at every smooth point. -/
structure CanonicalInput {s : FredholmSection c} (o : OrientationRep s) (k : ℕ) : Prop where
  pu : (o.a.S.A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity
  tame : o.a.S.A.B.IsScFredholmSectionTame o.a.F
  index : ∀ x ∈ o.a.S.A.X.PObj.smoothSet, o.a.S.A.B.IsIndexAt o.a.F x (k : ℤ)

/-- **The inputs of the cylinder construction for the canonical orientations**: for `∂Z = ∅`, `Z`
with sc-smooth partitions of unity and the standing hypotheses in the model of `o` (index
`m + 1`), every field of `CylinderInput` holds for the predicate "the orientation is the canonical
one for `(F, o)`" (`IsCanonicalPerturbation`): the relative step on the cylinder
(`theorem_15_3_7_relative`), the local unique continuation property of `[0, 1] × X` (from Zhou's
condition, Proposition 7.4.10), the glued data structurable with the face condition, and the end
identities (`cylinderOrientationStatement_of_isCanonical`). -/
theorem cylinderInput_canonical (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c} {m : ℕ} {o : OrientationRep s}
    (H : CanonicalInput o (m + 1)) :
    CylinderInput (m := m) (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o := by
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  have hpara := o.a.S.paracompact
  have hPUq := (c.polyfold.definition_16_1_5_two).1 hPU o.a.S.toPolyfoldStructure
    (toPolyfoldStructure_mem o.a.hS)
  have hbump : o.a.S.A.X.PObj.AdmitsBumpFunctions := o.a.S.A.X.theorem_12_3_2_1.1
    (EpGroupoid.admitsBumpFunctionsPointwise_of_hasScPartitionsOfUnity hPUq)
  have ho := o.isSectionOrientation_of_boundary_eq_empty hPU hbd H.tame
  have hLUC := o.a.S.A.X.proposition_7_4_10_of_isZhou o.a.S.isZhou
  have key := fun P₀ P₁ (h₀ : IsCanonicalPerturbation o.hF.2 o.hsec o.o P₀)
      (h₁ : IsCanonicalPerturbation o.hF.2 o.hsec o.o P₁) =>
    cylinderOrientationStatement_of_isCanonical hd hbump o.hF H.tame o.hsec o.o ho
      o.isOrientation.2 H.index P₀ P₁ h₀ h₁
  exact
    { rel := theorem_15_3_7_relative
      pu := H.pu
      luc := isLUC_cubeSEP hLUC
      tame := H.tame
      glue := fun P₀ P₁ _ _ =>
        ⟨isBoundaryStructurable_cubeGlue hd hpara P₀.isRegular.2.1 P₁.isRegular.2.1,
          isBoundaryFaceOnto_cubeGlue hd o.hF H.tame P₀.isRegular.2.2.2.2 P₁.isRegular.2.2.2.2⟩
      orient := fun P₀ P₁ h₀ h₁ => (key P₀ P₁ h₀ h₁).1
      orientEff := fun P₀ P₁ h₀ h₁ => (key P₀ P₁ h₀ h₁).2 _ _ }

/-! ### Theorem 16.6.6 -/

/-- **2021 Theorem 16.6.6, p. 739 (2017: Theorem 16.8), for the orientation inherited from
`(f, o)`.**  Let `Z` admit sc-smooth partitions of unity.  For `∂Z = ∅`, `f` with compact solution
set and `(n, U)` controlling compactness, and for every orientation `o` of `f` (Definition 16.6.5)
whose model has the standing hypotheses (partitions of unity on `[0, 1] × X`, tame germ data,
Fredholm index `m + 1`): over the admissible perturbed solution sets `θ̂ = λ ∘ f` with the
orientation inherited from `(f, o)` (the canonical orientation of Definition 15.4.2, read in the
model of `o`), `∫_θ̂ τ` and `∮_θ̂ τ` depend only on `[τ]`, and a closed `τ` has the same `∫_θ̂ τ`
and `∮_θ̂ τ` for any two of them.  No cobordism is assumed: it is the cylinder of Corollary
15.4.4. -/
theorem theorem_16_6_6_canonical (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    (s : FredholmSection c) (n : Y → ℝ) (U : Set Z) (m : ℕ) :
    theorem_16_6_6_statement s n U m (fun o Q => CanonicalInput o (m + 1) ∧
      IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o Q) := by
  intro hbd hcs _ _ _ o
  refine ⟨fun P _ _ τ η => ⟨?_, ?_⟩, ?_⟩
  · exact OrientedSuborbifold.integral_add_d hbd hPU _ _ _ τ η
  · exact OrientedSuborbifold.integralEff_add_d hbd hPU _ _ _ τ η
  rintro P₀ P₁ - ⟨H, M₀, c₀, rfl⟩ - ⟨-, M₁, c₁, rfl⟩ τ hτ
  obtain ⟨h, he⟩ := hasOrientedCobordism_of_cylinderInput hbd hcs
    (cylinderInput_canonical hPU hbd H) _ _ c₀ c₁
  exact ⟨CompactOrientedSuborbifold.integral_eq_of_hasCobordism
      (ModelPerturbation.hasCobordism_ofRegular h) τ hτ,
    CompactOrientedSuborbifold.integralEff_eq_of_hasCobordismEff
      (ModelPerturbation.hasCobordismEff_ofRegular he) τ hτ⟩

/-- **2021 Theorem 16.6.6 along `theorem_16_6_6_of_cylinder`**: if `Z` admits sc-smooth
partitions of unity and the standing hypotheses hold in the model of every orientation, Theorem
16.6.6 holds for the orientation inherited from `(f, o)` (`IsInheritedFrom` of the canonical
orientations); `CylinderInput` is filled by `cylinderInput_canonical`. -/
theorem theorem_16_6_6_canonical_of_forall (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    (s : FredholmSection c) (n : Y → ℝ) (U : Set Z) (m : ℕ)
    (H : ∀ o : OrientationRep s, CanonicalInput o (m + 1)) :
    theorem_16_6_6_statement s n U m
      (IsInheritedFrom fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) := by
  intro hbd
  exact theorem_16_6_6_of_cylinder hPU s n U m _ (fun o => cylinderInput_canonical hPU hbd (H o))
    hbd

/-! ### Fredholm index `0` -/

/-- **`IndexZeroInput` from the standing hypotheses**: for `∂Z = ∅` and `Z` with sc-smooth
partitions of unity, the field `orient` (`o` an orientation of `F` in the sense of Definition
6.6.16) follows from Definition 16.6.5 (`OrientationRep.isSectionOrientation`). -/
theorem indexZeroInput_of_canonicalInput (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c} {o : OrientationRep s}
    (H : CanonicalInput o 0) : IndexZeroInput o :=
  ⟨H.pu, H.tame, o.isSectionOrientation_of_boundary_eq_empty hPU hbd H.tame,
    fun x hx => by exact_mod_cast H.index x hx⟩

/-- **2021 Theorem 16.6.6 for Fredholm index `0`, for every orientation with the standing
hypotheses in its model** (p. 739): if `Z` admits sc-smooth partitions of unity, then for
`∂Z = ∅` and `f` with compact solution set, the counts `∫`, `∮` of a closed `0`-form over two
regular perturbations of dimension `0` with the canonical orientation of `(F, o)` agree, for every
orientation `o` whose model has sc-smooth partitions of unity on `[0, 1] × X`, tame germ data and
index `0`. -/
theorem theorem_16_6_6_index_zero_canonical_input (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    (s : FredholmSection c) (n : Y → ℝ) (U : Set Z) :
    theorem_16_6_6_index_zero_statement s n U
      (fun o P => CanonicalInput o 0 ∧ P.IsCanonical o.hF.2 o.hsec o.o) :=
  theorem_16_6_6_index_zero_of_model s n U _ fun hbd hcs _ P₀ P₁ h₀ h₁ =>
    hasOrientedCobordism_of_indexZeroInput hPU hbd hcs
      (indexZeroInput_of_canonicalInput hPU hbd h₀.1) P₀ P₁ h₀.2 h₁.2

/-- **2021 Theorem 16.6.6 for Fredholm index `0`, on the polyfold, for every orientation with the
standing hypotheses in its model** (p. 739): the polyfold form of
`theorem_16_6_6_index_zero_canonical_input`. -/
theorem theorem_16_6_6_index_zero_polyfold_canonical_input
    (hPU : c.polyfold.AdmitsScPartitionsOfUnity) (s : FredholmSection c) (n : Y → ℝ)
    (U : Set Z) :
    theorem_16_6_6_index_zero_polyfold_statement s n U
      (IsInheritedFromPoint fun o P => CanonicalInput o 0 ∧ P.IsCanonical o.hF.2 o.hsec o.o) :=
  theorem_16_6_6_index_zero_polyfold_of_model s n U _ fun hbd hcs _ P₀ P₁ h₀ h₁ =>
    hasOrientedCobordism_of_indexZeroInput hPU hbd hcs
      (indexZeroInput_of_canonicalInput hPU hbd h₀.1) P₀ P₁ h₀.2 h₁.2

/-- **2021 Theorem 16.6.6 for Fredholm index `0`, in the model of the orientation** (p. 739): if
`Z` admits sc-smooth partitions of unity and every orientation has the standing hypotheses in its
model (partitions of unity on `[0, 1] × X`, tame germ data, index `0`), the counts `∫`, `∮` of a
closed `0`-form over two regular perturbations of dimension `0` with the canonical orientation
agree (`theorem_16_6_6_index_zero_canonical` with the field `orient` derived). -/
theorem theorem_16_6_6_index_zero_inherited (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    (s : FredholmSection c) (n : Y → ℝ) (U : Set Z)
    (H : ∀ o : OrientationRep s, CanonicalInput o 0) :
    theorem_16_6_6_index_zero_statement s n U
      (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) := by
  intro hbd
  exact theorem_16_6_6_index_zero_canonical hPU s n U
    (fun o => indexZeroInput_of_canonicalInput hPU hbd (H o)) hbd

/-- **2021 Theorem 16.6.6 for Fredholm index `0`, on the polyfold** (p. 739): under the
hypotheses of `theorem_16_6_6_index_zero_inherited`, a closed `0`-form on `Z` has the same counts
`∫_θ̂ τ`, `∮_θ̂ τ` over any two admissible perturbed solution sets of dimension `0` with the
orientation inherited from `(f, o)`. -/
theorem theorem_16_6_6_index_zero_polyfold_inherited
    (hPU : c.polyfold.AdmitsScPartitionsOfUnity) (s : FredholmSection c) (n : Y → ℝ)
    (U : Set Z) (H : ∀ o : OrientationRep s, CanonicalInput o 0) :
    theorem_16_6_6_index_zero_polyfold_statement s n U
      (IsInheritedFromPoint fun o P => P.IsCanonical o.hF.2 o.hsec o.o) := by
  intro hbd
  exact theorem_16_6_6_index_zero_polyfold_canonical hPU s n U
    (fun o => indexZeroInput_of_canonicalInput hPU hbd (H o)) hbd

end StrongPolyfoldBundle

end Polyfold
