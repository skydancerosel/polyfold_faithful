import Polyfold.Examples.Classical.Structure
import Polyfold.Examples.Classical.DetSign
import Polyfold.Examples.Classical.MorphismCharts
import Polyfold.Examples.OrbifoldSquareSign

/-!
# The classical reduction: the canonical orientation

For a finite group `G` acting linearly on `ℝⁿ`, a fibre action `σ` and an equivariant `C^∞` map
`φ : ℝⁿ → ℝⁿ` (`Setup.lean`, `Structure.lean`), an orientation of the sc-Fredholm section
`|x| ↦ |(x, φ x)|` of `|ℝⁿ × ℝⁿ| → ℝⁿ/G` (Definition 12.5.4, 2021 p. 594; Definition 16.6.5,
2021 p. 739) for which the sign of an isomorphism `(f + S)'(y) = D(φ + ψ)(y)` is the sign of its
determinant.  Invariance under the morphisms uses `det ρ(g) · det σ(g) > 0` for all `g`.
The readings in the translation chart points (`stdPt`, `tEquiv`, `kEquiv`, `orTEquiv`,
`orKEquiv`, `stabT_std_fderiv`) are those of `MorphismCharts.lean`.

## What is formalized (namespace `Polyfold.Examples.Classical`)

* `conjDet_detUnit`, `ray_map_conjDet_unitRay`: the determinant isomorphism of a conjugation
  `S' ∘ A = Γ ∘ S` of isomorphisms maps the unit of `det S = λ(0) ⊗ λ*(0)` to the unit of `det S'`.
* `idSec φ y`: the graph section of `u ↦ (u − y) − φ(u)`, with `(f + S)(u) = u − y` and
  linearization the identity; `IsPosId o y`: `o_y` is positive at it.
* **`isPosOr_iff_det_of_isPosId`**: if `o_y` is positive at the identity, `o_y` is positive at an
  isomorphism `(f + S)'(y) = D(φ + ψ)(y)` iff `det D(φ + ψ)(y) > 0`.
* `isPosId_iff`: for a continuous orientation positivity at the identity at `0` and at `y` agree
  (`isPosOr_iff_of_path` along `t ↦ t • y`).
* `clOrientation σ hφ heq`: the continuous orientation positive at the identity at every point;
  **`isPosOr_clOrientation_iff`**: the sign of `(f + S)'(y)` is the sign of `det D(φ + ψ)(y)`.
* `isOrInvariantAt_zero`, **`isOrInvariant_clOrientation`** (Definition 12.5.4): `(g, 0)` maps
  positivity at an isomorphism `L` to positivity at `μ((g,0),·) ∘ L ∘ T(g,0)⁻¹`, whose
  determinant has the sign of `det σ(g) · det ρ(g) · det L`; invariance is locally constant along
  the morphisms (`eventually_isOrInvariantAt_iff`).
* **`clOrientationRep σ hφ heq hdet`** (Definition 16.6.5), `canonicalGermInput_clOrientationRep`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Classical

/-! ### The determinant isomorphism of a conjugation of isomorphisms -/

section ConjUnit

open TensorProduct

variable {E F E' F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
  [FiniteDimensional ℝ E'] [FiniteDimensional ℝ F']

/-- **The determinant isomorphism of a conjugation of isomorphisms maps the unit to the unit**:
for `S' ∘ A = Γ ∘ S` with `S`, `S'` bijective, `conjDet (1 ⊗ 1*) = 1 ⊗ 1*`. -/
theorem conjDet_detUnit (A : E ≃L[ℝ] E') (Γ : F ≃L[ℝ] F') {S : E →L[ℝ] F} {S' : E' →L[ℝ] F'}
    (h : ∀ v, S' (A v) = Γ (S v)) (hb : Bijective S) (hb' : Bijective S') :
    conjDet A Γ h (detUnit hb) = detUnit hb' := by
  unfold detUnit conjDet
  rw [TensorProduct.congr_tmul, maxPowEquiv_emptyWedge _ _ (finrank_ker_of_injective hb'.1)]
  congr 1
  rw [emptyWedge, maxPowDualEquiv_dualVec_symm _ linearIndependent_empty_type]
  congr 1

/-- The ray of the unit is carried to the ray of the unit. -/
theorem ray_map_conjDet_unitRay (A : E ≃L[ℝ] E') (Γ : F ≃L[ℝ] F') {S : E →L[ℝ] F}
    {S' : E' →L[ℝ] F'} (h : ∀ v, S' (A v) = Γ (S v)) (hb : Bijective S) (hb' : Bijective S') :
    Module.Ray.map (conjDet A Γ h) (unitRay hb) = unitRay hb' := by
  rw [unitRay, Module.Ray.map_apply]
  exact rayOfNeZero_congr (conjDet_detUnit A Γ h hb hb') _ _

end ConjUnit

/-- The matrix of `L` in the bases carried from the standard basis by `eT`, `eK` has the
determinant of `eK ∘ L ∘ eT⁻¹`. -/
theorem det_toMatrix_map {n : ℕ} {T K : Type*} [AddCommGroup T] [Module ℝ T] [AddCommGroup K]
    [Module ℝ K] (eT : T ≃ₗ[ℝ] (Fin n → ℝ)) (eK : K ≃ₗ[ℝ] (Fin n → ℝ)) (L : T →ₗ[ℝ] K) :
    (LinearMap.toMatrix ((Pi.basisFun ℝ (Fin n)).map eT.symm)
        ((Pi.basisFun ℝ (Fin n)).map eK.symm) L).det =
      LinearMap.det ((eK : K →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ L ∘ₗ
        (eT.symm : (Fin n → ℝ) →ₗ[ℝ] T)) := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin n))]
  congr 1

open TrivialBundle EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure StrongBundleEquivalenceExamples
  StrongBundleLocalizationExamples SBLocalization StrongRetr

variable {G : Type} [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  {n : ℕ} [DistribMulAction G (Fin n → ℝ)] [SMulCommClass G ℝ (Fin n → ℝ)]
  (σ : G →* ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) {φ : (Fin n → ℝ) → (Fin n → ℝ)}

/-! ### The identity at `y` -/

/-- `u ↦ (u − y) − φ(u)`. -/
abbrev idFun (φ : (Fin n → ℝ) → (Fin n → ℝ)) (y : Fin n → ℝ) : (Fin n → ℝ) → (Fin n → ℝ) :=
  fun u => (u - y) - φ u

theorem contDiff_idFun (hφ : ContDiff ℝ ∞ φ) (y : Fin n → ℝ) : ContDiff ℝ ∞ (idFun φ y) :=
  (contDiff_id.sub contDiff_const).sub hφ

theorem add_idFun (φ : (Fin n → ℝ) → (Fin n → ℝ)) (y : Fin n → ℝ) :
    φ + idFun φ y = fun u => u - y := by
  funext u
  change φ u + ((u - y) - φ u) = u - y
  abel

/-- `D(φ + idFun φ y) = id` everywhere. -/
theorem fderiv_add_idFun (φ : (Fin n → ℝ) → (Fin n → ℝ)) (y x : Fin n → ℝ) :
    fderiv ℝ (φ + idFun φ y) x = ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
  rw [add_idFun]
  exact ((hasFDerivAt_id x).sub_const y).fderiv

/-- **The graph section of `u ↦ (u − y) − φ(u)`**: `(f + S)(u) = u − y`. -/
abbrev idSec (φ : (Fin n → ℝ) → (Fin n → ℝ)) (y : Fin n → ℝ) :
    (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
  graphSection (idFun φ y)

theorem isScPlusSection_idSec (hφ : ContDiff ℝ ∞ φ) (y : Fin n → ℝ) :
    (AG (G := G) σ).B.IsScPlusSection (idSec φ y) :=
  isScPlusSection_graphSection (contDiff_idFun hφ y)

/-- `(f + S)(y) = 0` for `S = idSec φ y`. -/
theorem isZeroAt_idSec (y : Fin n → ℝ) :
    IsZeroAt (AG (G := G) σ).P (sectionAdd (AG (G := G) σ).P (fSec φ) (idSec φ y)) y := by
  change IsZeroAt (proj n n) (sectionAdd (proj n n) (graphSection φ) (graphSection (idFun φ y))) y
  rw [sectionAdd_graphSection_std, add_idFun]
  refine isZeroAt_graphSection_iff.2 ?_
  exact sub_self y

/-! ### Bijectivity and the reading in the chosen chart point -/

/-- **`(f + S)'(y)` is an isomorphism in every chart point** when `S` is the graph section of
`ψ` and `D(φ + ψ)(y)` is bijective. -/
theorem bijective_stabT_graph (hφ : ContDiff ℝ ∞ φ)
    (hf : (AG (G := G) σ).B.IsScFredholmSection (fSec φ)) {ψ : (Fin n → ℝ) → (Fin n → ℝ)}
    (hψ : ContDiff ℝ ∞ ψ) {y : Fin n → ℝ} {S : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    (hSe : S = graphSection ψ) (hS : (AG (G := G) σ).B.IsScPlusSection S)
    (h0 : IsZeroAt (AG (G := G) σ).P (sectionAdd (AG (G := G) σ).P (fSec φ) S) y)
    (hb : Bijective (fderiv ℝ (φ + ψ) y)) (p : ChartPoint (AG (G := G) σ).B y) :
    Bijective (p.stabT hf hS h0) := by
  subst hSe
  refine ChartPoint.bijective_stabT_of_bijective (p := stdPt σ y) p hf hS h0 ?_
  have e : ⇑((stdPt σ y).stabT hf hS h0) =
      ⇑(kEquiv σ y).symm ∘ ⇑(fderiv ℝ (φ + ψ) y) ∘ ⇑(tEquiv σ y) := by
    funext v
    apply (kEquiv σ y).injective
    rw [stabT_std_fderiv σ hφ hψ hf hS h0 v]
    simp
  rw [e]
  exact (kEquiv σ y).symm.bijective.comp (hb.comp (tEquiv σ y).bijective)

/-- **`(f + S)'(y)` read in the chosen chart point is `D(φ + ψ)(y)`** through `orTEquiv`,
`orKEquiv`. -/
theorem orKEquiv_stabT (hφ : ContDiff ℝ ∞ φ)
    (hf : (AG (G := G) σ).B.IsScFredholmSection (fSec φ)) {ψ : (Fin n → ℝ) → (Fin n → ℝ)}
    (hψ : ContDiff ℝ ∞ ψ) {y : Fin n → ℝ} (hS : (AG (G := G) σ).B.IsScPlusSection (graphSection ψ))
    (h0 : IsZeroAt (AG (G := G) σ).P (sectionAdd (AG (G := G) σ).P (fSec φ) (graphSection ψ)) y)
    (hs : y ∈ (AG (G := G) σ).X.PObj.smoothSet) (v : ↥(orPt (AG (G := G) σ).B y hs).T) :
    orKEquiv σ y hs ((orPt (AG (G := G) σ).B y hs).stabT hf hS h0 v) =
      fderiv ℝ (φ + ψ) y (orTEquiv σ y hs v) := by
  change kEquiv σ y ((orPt (AG (G := G) σ).B y hs).transferK (stdPt σ y)
    ((orPt (AG (G := G) σ).B y hs).stabT hf hS h0 v)) =
      fderiv ℝ (φ + ψ) y (tEquiv σ y ((orPt (AG (G := G) σ).B y hs).transferT (stdPt σ y) v))
  rw [← ChartPoint.stabT_transferT (stdPt σ y) hf hS h0 v]
  exact stabT_std_fderiv σ hφ hψ hf hS h0 _

/-! ### The sign of an isomorphism `(f + S)'(y)` -/

instance finiteDimensional_orT (x : Fin n → ℝ) (hs : x ∈ (AG (G := G) σ).X.PObj.smoothSet) :
    FiniteDimensional ℝ ↥(orPt (AG (G := G) σ).B x hs).T :=
  (orTEquiv σ x hs).toLinearEquiv.symm.finiteDimensional

instance finiteDimensional_orK (x : Fin n → ℝ) (hs : x ∈ (AG (G := G) σ).X.PObj.smoothSet) :
    FiniteDimensional ℝ ↥(orPt (AG (G := G) σ).B x hs).K :=
  (orKEquiv σ x hs).toLinearEquiv.symm.finiteDimensional

/-- The basis of `T_xℝⁿ` in the chosen chart point carried from the standard basis. -/
abbrev orTBasis (x : Fin n → ℝ) (hs : x ∈ (AG (G := G) σ).X.PObj.smoothSet) :
    Basis (Fin n) ℝ ↥(orPt (AG (G := G) σ).B x hs).T :=
  (Pi.basisFun ℝ (Fin n)).map (orTEquiv σ x hs).toLinearEquiv.symm

/-- The basis of `W_x` in the chosen chart point carried from the standard basis. -/
abbrev orKBasis (x : Fin n → ℝ) (hs : x ∈ (AG (G := G) σ).X.PObj.smoothSet) :
    Basis (Fin n) ℝ ↥(orPt (AG (G := G) σ).B x hs).K :=
  (Pi.basisFun ℝ (Fin n)).map (orKEquiv σ x hs).toLinearEquiv.symm

/-- An operator `T_xℝⁿ → W_x` of the chosen chart point read as an endomorphism of `ℝⁿ`. -/
abbrev readLin (x : Fin n → ℝ) (hs : x ∈ (AG (G := G) σ).X.PObj.smoothSet)
    (L : ↥(orPt (AG (G := G) σ).B x hs).T →L[ℝ] ↥(orPt (AG (G := G) σ).B x hs).K) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  ((orKEquiv σ x hs).toLinearEquiv : ↥(orPt (AG (G := G) σ).B x hs).K →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ
    (L : ↥(orPt (AG (G := G) σ).B x hs).T →ₗ[ℝ] ↥(orPt (AG (G := G) σ).B x hs).K) ∘ₗ
      ((orTEquiv σ x hs).toLinearEquiv.symm :
        (Fin n → ℝ) →ₗ[ℝ] ↥(orPt (AG (G := G) σ).B x hs).T)

theorem det_toMatrix_orBasis (x : Fin n → ℝ) (hs : x ∈ (AG (G := G) σ).X.PObj.smoothSet)
    (L : ↥(orPt (AG (G := G) σ).B x hs).T →L[ℝ] ↥(orPt (AG (G := G) σ).B x hs).K) :
    (LinearMap.toMatrix (orTBasis σ x hs) (orKBasis σ x hs)
      (L : ↥(orPt (AG (G := G) σ).B x hs).T →ₗ[ℝ] ↥(orPt (AG (G := G) σ).B x hs).K)).det =
      LinearMap.det (readLin σ x hs L) :=
  det_toMatrix_map _ _ _

/-- `(f + S)'(y)` read as an endomorphism of `ℝⁿ` is `D(φ + ψ)(y)`. -/
theorem readLin_stabT (hφ : ContDiff ℝ ∞ φ)
    (hf : (AG (G := G) σ).B.IsScFredholmSection (fSec φ)) {ψ : (Fin n → ℝ) → (Fin n → ℝ)}
    (hψ : ContDiff ℝ ∞ ψ) {y : Fin n → ℝ} (hS : (AG (G := G) σ).B.IsScPlusSection (graphSection ψ))
    (h0 : IsZeroAt (AG (G := G) σ).P (sectionAdd (AG (G := G) σ).P (fSec φ) (graphSection ψ)) y)
    (hs : y ∈ (AG (G := G) σ).X.PObj.smoothSet) :
    readLin σ y hs ((orPt (AG (G := G) σ).B y hs).stabT hf hS h0) =
      (fderiv ℝ (φ + ψ) y : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) := by
  refine LinearMap.ext fun w => ?_
  change orKEquiv σ y hs ((orPt (AG (G := G) σ).B y hs).stabT hf hS h0
    ((orTEquiv σ y hs).symm w)) = _
  rw [orKEquiv_stabT σ hφ hf hψ hS h0 hs, ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- **The sign of an isomorphism `(f + S)'(y)`** for an orientation `o ∈ Or_y^f` positive at the
identity `(f + idSec φ y)'(y)`: `o` is positive at `(f + S)'(y) = D(φ + ψ)(y)`, `S` the graph
section of `ψ`, iff `det D(φ + ψ)(y) > 0` (`isPos_iff_det_of_isPos`). -/
theorem isPosOr_iff_det_of_isPosId (hφ : ContDiff ℝ ∞ φ)
    (hf : (AG (G := G) σ).B.IsScFredholmSection (fSec φ)) {y : Fin n → ℝ}
    (hs : y ∈ (AG (G := G) σ).X.PObj.smoothSet) (o : Orx (B := (AG (G := G) σ).B) (fSec φ) hf y hs)
    (hpos : IsPosOr hf hs o (idSec φ y) (isScPlusSection_idSec σ hφ y) (isZeroAt_idSec σ y))
    {ψ : (Fin n → ℝ) → (Fin n → ℝ)} (hψ : ContDiff ℝ ∞ ψ)
    (hS : (AG (G := G) σ).B.IsScPlusSection (graphSection ψ))
    (h0 : IsZeroAt (AG (G := G) σ).P (sectionAdd (AG (G := G) σ).P (fSec φ) (graphSection ψ)) y)
    (hb : Bijective (fderiv ℝ (φ + ψ) y)) :
    IsPosOr hf hs o (graphSection ψ) hS h0 ↔
      0 < LinearMap.det (fderiv ℝ (φ + ψ) y : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) := by
  have hb₁ := bijective_stabT_graph σ hφ hf hψ rfl hS h0 hb (orPt (AG (G := G) σ).B y hs)
  refine (isPos_iff_det_of_isPos (orPt (AG (G := G) σ).B y hs) o
    ((orPt (AG (G := G) σ).B y hs).stabT_mem_linSet hf hS h0 hs) hb₁ hpos
    (orTBasis σ y hs) (orKBasis σ y hs)).trans ?_
  rw [det_toMatrix_orBasis, det_toMatrix_orBasis, readLin_stabT σ hφ hf hψ hS h0 hs,
    readLin_stabT σ hφ hf (contDiff_idFun hφ y) (isScPlusSection_idSec σ hφ y)
      (isZeroAt_idSec σ y) hs, fderiv_add_idFun, ContinuousLinearMap.coe_id, LinearMap.det_id,
    one_mul]

/-! ### Positivity at the identity along paths -/

/-- **`o` is positive at the identity at `y`**: at `(f + idSec φ y)'(y)`. -/
def IsPosId (hφ : ContDiff ℝ ∞ φ) {hf : (AG (G := G) σ).B.IsScFredholmSection (fSec φ)}
    (o : ∀ a (hs : a ∈ (AG (G := G) σ).X.PObj.smoothSet),
      Orx (B := (AG (G := G) σ).B) (fSec φ) hf a hs) (y : Fin n → ℝ) : Prop :=
  IsPosOr hf (mem_smoothSet_AG σ y) (o y (mem_smoothSet_AG σ y)) (idSec φ y)
    (isScPlusSection_idSec σ hφ y) (isZeroAt_idSec σ y)

/-- `D(φ + idFun φ y)` is bijective. -/
theorem bijective_fderiv_add_idFun (y x : Fin n → ℝ) :
    Bijective (fderiv ℝ (φ + idFun φ y) x) := by
  rw [fderiv_add_idFun, ContinuousLinearMap.coe_id']
  exact bijective_id

section Path

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × (AG (G := G) σ).Obj)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace (AG (G := G) σ).P
    (Prod.snd : (Fin n → ℝ) × (AG (G := G) σ).Obj → (AG (G := G) σ).Obj))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × (AG (G := G) σ).Obj))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj (AG (G := G) σ).P
      (Prod.snd : (Fin n → ℝ) × (AG (G := G) σ).Obj → (AG (G := G) σ).Obj))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × (AG (G := G) σ).Obj) →
      (Fin n → ℝ) × (AG (G := G) σ).Obj))]

/-- **For a continuous orientation, positivity at the identity at `0` and at `y` agree**: along
`γ(t) = t • y` the sc⁺-section `(t, u) ↦ (u, (u − t • y) − φ(u))` of the pull-back bundle has
`(f + S_t)(γ t) = 0` and `(f + S_t)'(γ t) = id` (`isPosOr_iff_of_path`). -/
theorem isPosId_iff (hφ : ContDiff ℝ ∞ φ)
    {o : ∀ a (hs : a ∈ (AG (G := G) σ).X.PObj.smoothSet),
      Orx (B := (AG (G := G) σ).B) (fSec φ)
        (isScFredholmSectionTame_fSec σ hφ).toIsScFredholmSection a hs}
    (ho : IsContOrOn (orLocalTransport (isTame_AG σ) (admitsBumpFunctions_AG σ)
      (isScFredholmSectionTame_fSec σ hφ) (hasScPlusSectionsThrough_AG σ)) univ o)
    (y : Fin n → ℝ) : IsPosId σ hφ o 0 ↔ IsPosId σ hφ o y := by
  have hft := isScFredholmSectionTame_fSec σ hφ
  let γ : (Fin 1 → ℝ) → (Fin n → ℝ) := fun q => q 0 • y
  have hγd : ContDiff ℝ ∞ γ := (contDiff_apply ℝ ℝ (0 : Fin 1)).smul contDiff_const
  have hγs : (rnPolyfold 1).IsScSmoothMap (rnPolyfold n) γ := isScSmoothMap_rn_rn_of_contDiff hγd
  have hP : (AG (G := G) σ).B.IsScPlusSection (graphSection fun u => u - φ u) :=
    isScPlusSection_graphSection (contDiff_id.sub hφ)
  have hL := isScPlusSection_paramLift hP
  have hg : ContDiff ℝ ∞ fun q : Fin 1 → ℝ => -γ q := hγd.neg
  have hF := OrbifoldSquare.isScPlusSection_famSection (n := n) hg
  have hS := hL.add hF
  set S := sectionAdd (pullbackProj (AG (G := G) σ).P Prod.snd)
    (paramLift (n := 1) (graphSection fun u => u - φ u) hP.1)
    (OrbifoldSquare.famSection n fun q : Fin 1 → ℝ => -γ q) with hSdef
  have hslice : ∀ q, pullbackSlice S q = idSec φ (γ q) := fun q => by
    have hpl : pullbackSlice (paramLift (n := 1) (graphSection fun u => u - φ u) hP.1) q =
        graphSection fun u => u - φ u := rfl
    refine (pullbackSlice_sectionAdd hL.1 hF.1 q).trans ?_
    refine (congrArg₂ (sectionAdd (AG (G := G) σ).P) hpl
      (OrbifoldSquare.pullbackSlice_famSection _ q)).trans ?_
    refine (sectionAdd_graphSection_std _ _).trans ?_
    congr 1
    funext u
    change (u - φ u) + -γ q = (u - γ q) - φ u
    abel
  have hzq : ∀ q, IsZeroAt (AG (G := G) σ).P
      (sectionAdd (AG (G := G) σ).P (fSec φ) (pullbackSlice S q)) (γ q) := fun q => by
    rw [hslice q]
    exact isZeroAt_idSec σ (γ q)
  have hz : ∀ q : Fin 1 → ℝ, IsZeroAt (pullbackProj (AG (G := G) σ).P Prod.snd)
      (sectionAdd (pullbackProj (AG (G := G) σ).P Prod.snd)
        (paramLift (fSec φ) hft.isScSmooth.1) S) (q, γ q) := fun q => by
    refine (isZeroAt_pullback_iff_pullbackSlice (P := (AG (G := G) σ).P)
      ((isSection_pullbackLift _).sectionAdd hS.1) q (γ q)).2 ?_
    rw [pullbackSlice_sectionAdd_paramLift hft.isScSmooth.1 hS.1 q]
    exact hzq q
  have key := isPosOr_iff_of_path (isTame_AG σ) (admitsBumpFunctions_AG σ) hft
    (hasScPlusSectionsThrough_AG σ) ho hγs (fun _ _ => mem_univ _) hS (Eventually.of_forall hz)
    (fun q _ p h0 => bijective_stabT_graph σ hφ _ (contDiff_idFun hφ (γ q)) (hslice q) _ h0
      (bijective_fderiv_add_idFun _ _) p)
    (mem_smoothSet_AG σ _) (mem_smoothSet_AG σ _) (hzq _) (hzq _)
  have e0 : γ (pt1 0) = 0 := zero_smul ℝ y
  have e1 : γ (pt1 1) = y := one_smul ℝ y
  have c0 := isPosOr_congr_pt hft.toIsScFredholmSection o e0 (mem_smoothSet_AG σ _)
    (mem_smoothSet_AG σ _) ((hslice (pt1 0)).trans (by rw [e0])) (hS.pullbackSlice _)
    (isScPlusSection_idSec σ hφ 0) (hzq _) (isZeroAt_idSec σ 0)
  have c1 := isPosOr_congr_pt hft.toIsScFredholmSection o e1 (mem_smoothSet_AG σ _)
    (mem_smoothSet_AG σ _) ((hslice (pt1 1)).trans (by rw [e1])) (hS.pullbackSlice _)
    (isScPlusSection_idSec σ hφ y) (hzq _) (isZeroAt_idSec σ y)
  exact c0.symm.trans (key.trans c1)

end Path

/-! ### The orientation positive at the identity -/

/-- **`f` has a continuous orientation over `ℝⁿ` positive at the identity at `0`**: a continuous
orientation exists (Theorem 6.6.17; paths in `ℝⁿ` with the same end points are homotopic), and of
it and the opposite orientation exactly one is positive at the isomorphism `(f + idSec φ 0)'(0)`. -/
theorem exists_isContOrOn_isPosId (hφ : ContDiff ℝ ∞ φ) :
    haveI := paracompactSpace_rn_prod (AG (G := G) σ).X.PObj
    haveI := paracompactSpace_rn_pullback (AG (G := G) σ).B
    haveI := paracompactSpace_rn_rn_prod (AG (G := G) σ).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (AG (G := G) σ).B
    ∃ o : ∀ a (hs : a ∈ (AG (G := G) σ).X.PObj.smoothSet),
        Orx (B := (AG (G := G) σ).B) (fSec φ)
          (isScFredholmSectionTame_fSec σ hφ).toIsScFredholmSection a hs,
      IsContOrOn (orLocalTransport (isTame_AG σ) (admitsBumpFunctions_AG σ)
        (isScFredholmSectionTame_fSec σ hφ) (hasScPlusSectionsThrough_AG σ)) univ o ∧
      IsPosId σ hφ o 0 := by
  have := paracompactSpace_rn_prod (AG (G := G) σ).X.PObj
  have := paracompactSpace_rn_pullback (AG (G := G) σ).B
  have := paracompactSpace_rn_rn_prod (AG (G := G) σ).X.PObj
  have := paracompactSpace_rn_rn_pullback (AG (G := G) σ).B
  have hft := isScFredholmSectionTame_fSec σ hφ
  have hf := hft.toIsScFredholmSection
  have hsec := hasScPlusSectionsThrough_AG σ
  obtain ⟨o, -, hc⟩ := exists_continuous_orSec_of_hom_eq (isTame_AG σ)
    (admitsBumpFunctions_AG σ) hft hsec (fun {_ _} a b => PathCat.hom_eq_rn (n := n) a b)
  have ho := isContOrOn_univ_of_continuous_orSec
    (fun _ hy => exists_two_orx _ hy hsec) (AG (G := G) σ).X.PObj.hasConnectedSmoothNbhds hc
  have h2 : IsTwoPointed (B := (AG (G := G) σ).B) (fSec φ) hf := fun x hs =>
    exists_two_orx hf hs hsec
  by_cases hp : IsPosId σ hφ o 0
  · exact ⟨o, ho, hp⟩
  · refine ⟨fun y hy => orOther (o y hy), ho.other _ h2, ?_⟩
    have hs := mem_smoothSet_AG σ (0 : Fin n → ℝ)
    have hall : ∀ a : Orx (B := (AG (G := G) σ).B) (fSec φ) hf (0 : Fin n → ℝ) hs,
        a = o _ hs ∨ a = orOther (o _ hs) := fun a => by
      by_cases h : a = o _ hs
      · exact Or.inl h
      · exact Or.inr ((eq_orOther_iff h2 _ _).2 h)
    have hb := bijective_stabT_graph σ hφ hf (contDiff_idFun hφ 0) rfl
      (isScPlusSection_idSec σ hφ 0) (isZeroAt_idSec σ 0) (bijective_fderiv_add_idFun 0 0)
      (orPt (AG (G := G) σ).B (0 : Fin n → ℝ) hs)
    rcases ChartPoint.isPos_or_isPos (ChartPoint.stabT_mem_linSet _ hf
      (isScPlusSection_idSec σ hφ 0) (isZeroAt_idSec σ 0) hs) hb hall with h | h
    · exact absurd h hp
    · exact h

/-- **The canonical orientation of `|x| ↦ |(x, φ x)|`**: the continuous orientation positive at
the identity `(f + idSec φ 0)'(0)`. -/
def clOrientation (hφ : ContDiff ℝ ∞ φ) : ∀ a (hs : a ∈ (AG (G := G) σ).X.PObj.smoothSet),
    Orx (B := (AG (G := G) σ).B) (fSec φ)
      (isScFredholmSectionTame_fSec σ hφ).toIsScFredholmSection a hs :=
  (exists_isContOrOn_isPosId σ hφ).choose

theorem isContOrOn_clOrientation (hφ : ContDiff ℝ ∞ φ) :
    haveI := paracompactSpace_rn_prod (AG (G := G) σ).X.PObj
    haveI := paracompactSpace_rn_pullback (AG (G := G) σ).B
    haveI := paracompactSpace_rn_rn_prod (AG (G := G) σ).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (AG (G := G) σ).B
    IsContOrOn (orLocalTransport (isTame_AG σ) (admitsBumpFunctions_AG σ)
      (isScFredholmSectionTame_fSec σ hφ) (hasScPlusSectionsThrough_AG σ)) univ
      (clOrientation σ hφ) :=
  (exists_isContOrOn_isPosId σ hφ).choose_spec.1

/-- **`clOrientation` is positive at the identity at every point.** -/
theorem isPosId_clOrientation (hφ : ContDiff ℝ ∞ φ) (y : Fin n → ℝ) :
    IsPosId σ hφ (clOrientation σ hφ) y := by
  have := paracompactSpace_rn_prod (AG (G := G) σ).X.PObj
  have := paracompactSpace_rn_pullback (AG (G := G) σ).B
  have := paracompactSpace_rn_rn_prod (AG (G := G) σ).X.PObj
  have := paracompactSpace_rn_rn_pullback (AG (G := G) σ).B
  exact (isPosId_iff σ hφ (isContOrOn_clOrientation σ hφ) y).1
    (exists_isContOrOn_isPosId σ hφ).choose_spec.2

/-- **The sign of `(f + S)'(y)` for the canonical orientation is the sign of the determinant**:
for the graph section `S` of a `C^∞` map `ψ` with `(f + S)(y) = 0` and `D(φ + ψ)(y)` bijective,
`clOrientation` is positive at `(f + S)'(y)` iff `det D(φ + ψ)(y) > 0`. -/
theorem isPosOr_clOrientation_iff (hφ : ContDiff ℝ ∞ φ)
    (hf : (AG (G := G) σ).B.IsScFredholmSection (fSec φ)) {y : Fin n → ℝ}
    (hs : y ∈ (AG (G := G) σ).X.PObj.smoothSet) {ψ : (Fin n → ℝ) → (Fin n → ℝ)}
    (hψ : ContDiff ℝ ∞ ψ) (hS : (AG (G := G) σ).B.IsScPlusSection (graphSection ψ))
    (h0 : IsZeroAt (AG (G := G) σ).P (sectionAdd (AG (G := G) σ).P (fSec φ) (graphSection ψ)) y)
    (hb : Bijective (fderiv ℝ (φ + ψ) y)) :
    IsPosOr hf hs (clOrientation σ hφ y hs) (graphSection ψ) hS h0 ↔
      0 < LinearMap.det (fderiv ℝ (φ + ψ) y : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :=
  isPosOr_iff_det_of_isPosId σ hφ hf hs _ (isPosId_clOrientation σ hφ y) hψ hS h0 hb

/-! ### Invariance under the morphisms -/

omit [Fintype G] in
/-- `det ρ(g) · det ρ(g⁻¹) = 1`. -/
theorem det_rhoL_mul_inv (g : G) :
    LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (rhoL (n := n) g⁻¹ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = 1 := by
  rw [← LinearMap.det_comp]
  have e : (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ
      (rhoL (n := n) g⁻¹ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = LinearMap.id :=
    LinearMap.ext fun x => smul_inv_smul g x
  rw [e, LinearMap.det_id]

/-- `d · (s · (d · a')) > 0` for `d ≠ 0`, `a · a' = 1`, `a · s > 0`. -/
theorem pos_of_det_mul_inv {a a' s d : ℝ} (hd : d ≠ 0) (ha' : a' ≠ 0) (h : a * a' = 1)
    (hs : 0 < a * s) : 0 < d * (s * (d * a')) := by
  have e : d * (s * (d * a')) = (d * d) * ((a * s) * (a' * a')) := by
    linear_combination (-(d * d * s * a')) * h
  rw [e]
  exact mul_pos (mul_self_pos.2 hd) (mul_pos hs (mul_self_pos.2 ha'))

/-- **An isotropy morphism `(g, 0)` fixes an orientation positive at the identity at `0`**, when
`det ρ(g) · det σ(g) > 0`: `(g, 0)_*` is the conjugation by `T(g, 0)` and `μ((g, 0), ·)`
(`orMor_apply`), which carries the unit of `det L` to the unit of `det L'`,
`L' = μ((g, 0), ·) ∘ L ∘ T(g, 0)⁻¹`; read in `ℝⁿ`, `L' = σ(g) ∘ L ∘ ρ(g)⁻¹`, so `det L · det L'`
has the sign of `det σ(g) · det ρ(g)` and `o` is positive at `L'` as well
(`isPos_iff_det_of_isPos`). -/
theorem orMor_zero_eq (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    (g : G) (hgx : (AG (G := G) σ).X.tgt ((g, (0 : Fin n → ℝ)) : (AG (G := G) σ).Mor) =
      (0 : Fin n → ℝ))
    (hs : (0 : Fin n → ℝ) ∈ (AG (G := G) σ).X.PObj.smoothSet)
    (o0 : Orx (B := (AG (G := G) σ).B) (fSec φ) (isScFredholmSectionFunctor_fSec hφ heq).2
      (0 : Fin n → ℝ) hs)
    (hpos : IsPosOr (isScFredholmSectionFunctor_fSec hφ heq).2 hs o0 (idSec φ 0)
      (isScPlusSection_idSec σ hφ 0) (isZeroAt_idSec σ 0)) :
    (AG (G := G) σ).E.orMor (isScFredholmSectionFunctor_fSec hφ heq)
      (hasScPlusSectionsThrough_AG σ) ((g, (0 : Fin n → ℝ)) : (AG (G := G) σ).Mor)
      (x := (0 : Fin n → ℝ)) rfl hgx hs hs o0 = o0 := by
  have hF := isScFredholmSectionFunctor_fSec (σ := σ) hφ heq
  have hsec := hasScPlusSectionsThrough_AG σ
  set p := orPt (AG (G := G) σ).B (0 : Fin n → ℝ) hs with hp
  set L := p.stabT hF.2 (isScPlusSection_idSec σ hφ 0) (isZeroAt_idSec σ 0) with hLdef
  have hL : L ∈ p.linSet (B := (AG (G := G) σ).B) (fSec φ) := p.stabT_mem_linSet hF.2 _ _ hs
  have hb : Bijective L := ChartPoint.IsPos.bijective hpos
  set L' := (AG (G := G) σ).E.linMor ((g, (0 : Fin n → ℝ)) : (AG (G := G) σ).Mor)
    (x := (0 : Fin n → ℝ)) rfl hgx hs hs L with hL'def
  have hL' : L' ∈ p.linSet (B := (AG (G := G) σ).B) (fSec φ) :=
    (AG (G := G) σ).E.lemma_12_5_1_one hF hsec _ (x := (0 : Fin n → ℝ)) rfl hgx hs hs hL
  have h : ∀ v, L' (((AG (G := G) σ).E.morTx ((g, (0 : Fin n → ℝ)) : (AG (G := G) σ).Mor)
        (x := (0 : Fin n → ℝ)) rfl hgx hs hs) v) =
      (((AG (G := G) σ).E.morKx ((g, (0 : Fin n → ℝ)) : (AG (G := G) σ).Mor)
        (x := (0 : Fin n → ℝ)) rfl hgx hs hs) (L v)) := fun v =>
    congrArg (fun w => (((AG (G := G) σ).E.morKx ((g, (0 : Fin n → ℝ)) : (AG (G := G) σ).Mor)
        (x := (0 : Fin n → ℝ)) rfl hgx hs hs) (L w)))
      (((AG (G := G) σ).E.morTx ((g, (0 : Fin n → ℝ)) : (AG (G := G) σ).Mor)
        (x := (0 : Fin n → ℝ)) rfl hgx hs hs).symm_apply_apply v)
  have hb' : Bijective L' := by
    have e : ⇑L' = ⇑((AG (G := G) σ).E.morKx ((g, (0 : Fin n → ℝ)) : (AG (G := G) σ).Mor)
        (x := (0 : Fin n → ℝ)) rfl hgx hs hs) ∘ ⇑L ∘
        ⇑((AG (G := G) σ).E.morTx ((g, (0 : Fin n → ℝ)) : (AG (G := G) σ).Mor)
        (x := (0 : Fin n → ℝ)) rfl hgx hs hs).symm := by
      funext w
      exact EpStrongBundle.linMor_apply _ _ _ _ _ _ _ _
    rw [e]
    exact ((AG (G := G) σ).E.morKx ((g, (0 : Fin n → ℝ)) : (AG (G := G) σ).Mor)
        (x := (0 : Fin n → ℝ)) rfl hgx hs hs).bijective.comp
      (hb.comp ((AG (G := G) σ).E.morTx ((g, (0 : Fin n → ℝ)) : (AG (G := G) σ).Mor)
        (x := (0 : Fin n → ℝ)) rfl hgx hs hs).symm.bijective)
  -- `(g, 0)_* o` at `L'`
  have hu : o0 ⟨L, hL⟩ = unitRay hb := (isPos_iff_eq_unitRay p o0 hL hb).1 hpos
  -- `L'` read in `ℝⁿ`
  have hread : readLin σ 0 hs L' = (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ readLin σ 0 hs L ∘ₗ
      (rhoL (n := n) g⁻¹ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) := by
    refine LinearMap.ext fun w => ?_
    obtain ⟨v, hv⟩ : ∃ v, v = (orTEquiv σ 0 hs).symm (g⁻¹ • w) := ⟨_, rfl⟩
    have hAv : (((AG (G := G) σ).E.morTx ((g, (0 : Fin n → ℝ)) : (AG (G := G) σ).Mor)
          (x := (0 : Fin n → ℝ)) rfl hgx hs hs) v) =
        (orTEquiv σ 0 hs).symm w := by
      apply (orTEquiv σ 0 hs).injective
      rw [ContinuousLinearEquiv.apply_symm_apply]
      have e := morTx_std σ g (x := (0 : Fin n → ℝ)) rfl hgx hs hs v
      change orTEquiv σ 0 hs (((AG (G := G) σ).E.morTx ((g, (0 : Fin n → ℝ)) : (AG (G := G) σ).Mor)
          (x := (0 : Fin n → ℝ)) rfl hgx hs hs) v) =
        g • orTEquiv σ 0 hs v at e
      rw [e, hv, ContinuousLinearEquiv.apply_symm_apply, smul_inv_smul]
    have e := morKx_std σ g (x := (0 : Fin n → ℝ)) rfl hgx hs hs (L v)
    change orKEquiv σ 0 hs (((AG (G := G) σ).E.morKx ((g, (0 : Fin n → ℝ)) : (AG (G := G) σ).Mor)
        (x := (0 : Fin n → ℝ)) rfl hgx hs hs) (L v)) =
      σ g (orKEquiv σ 0 hs (L v)) at e
    change orKEquiv σ 0 hs (L' ((orTEquiv σ 0 hs).symm w)) =
      σ g (orKEquiv σ 0 hs (L ((orTEquiv σ 0 hs).symm (g⁻¹ • w))))
    rw [← hAv, h, e, hv]
  have hpos' : p.IsPos o0 L' := by
    refine (isPos_iff_det_of_isPos p o0 hL' hb' hpos (orTBasis σ 0 hs) (orKBasis σ 0 hs)).2 ?_
    rw [det_toMatrix_orBasis, det_toMatrix_orBasis, hread, LinearMap.det_comp,
      LinearMap.det_comp]
    have hd : LinearMap.det (readLin σ 0 hs L) ≠ 0 := by
      rw [← det_toMatrix_orBasis]
      exact det_toMatrix_ne_zero _ _
        (LinearEquiv.ofBijective (L : ↥p.T →ₗ[ℝ] ↥p.K) hb)
    have h1 := det_rhoL_mul_inv (n := n) g
    have ha' : LinearMap.det (rhoL (n := n) g⁻¹ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ≠ 0 :=
      right_ne_zero_of_mul_eq_one h1
    exact pos_of_det_mul_inv hd ha' h1 (hdet g)
  have h2 : o0 ⟨L', hL'⟩ = unitRay hb' := (isPos_iff_eq_unitRay p o0 hL' hb').1 hpos'
  have : ContractibleSpace (p.linSet (B := (AG (G := G) σ).B) (fSec φ)) :=
    (p.convex_linSet hF.2).contractibleSpace ⟨_, hL⟩
  have hc := LineOrientation.conj_apply (hC := p.isFredholm_of_mem_linSet hF.2)
    (hC' := p.isFredholm_of_mem_linSet hF.2)
    ((AG (G := G) σ).E.morTx ((g, (0 : Fin n → ℝ)) : (AG (G := G) σ).Mor) (x := (0 : Fin n → ℝ))
      rfl hgx hs hs)
    ((AG (G := G) σ).E.morKx ((g, (0 : Fin n → ℝ)) : (AG (G := G) σ).Mor) (x := (0 : Fin n → ℝ))
      rfl hgx hs hs)
    ((AG (G := G) σ).E.morTx_mem hF hsec _ (x := (0 : Fin n → ℝ)) rfl hgx hs hs) o0 hL hL' h
  refine ((AG (G := G) σ).E.orMor_apply hF hsec ((g, (0 : Fin n → ℝ)) : (AG (G := G) σ).Mor)
    (x := (0 : Fin n → ℝ)) rfl hgx hs hs o0).trans ?_
  refine LineOrientation.eq_of_apply_eq ⟨L', hL'⟩ (hc.trans ?_)
  have hm := ray_map_conjDet_unitRay _ _ h hb hb'
  exact (congrArg (Module.Ray.map (conjDet _ _ h)) hu).trans (hm.trans h2.symm)

section Invariance

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × (AG (G := G) σ).Obj)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace (AG (G := G) σ).P
    (Prod.snd : (Fin n → ℝ) × (AG (G := G) σ).Obj → (AG (G := G) σ).Obj))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × (AG (G := G) σ).Obj))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj (AG (G := G) σ).P
      (Prod.snd : (Fin n → ℝ) × (AG (G := G) σ).Obj → (AG (G := G) σ).Obj))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × (AG (G := G) σ).Obj) →
      (Fin n → ℝ) × (AG (G := G) σ).Obj))]

/-- **`clOrientation` is invariant under the morphisms** (Definition 12.5.4), when
`det ρ(g) · det σ(g) > 0` for all `g`: the invariance at `(g, q)` is locally constant in `q`
(`EpStrongBundle.eventually_isOrInvariantAt_iff`, from Theorem 12.5.3), `ℝⁿ` is connected, and
at `(g, 0)` it holds by `orMor_zero_eq`. -/
theorem isOrInvariant_clOrientation (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) :
    (AG (G := G) σ).E.IsOrInvariant (isScFredholmSectionFunctor_fSec hφ heq)
      (hasScPlusSectionsThrough_AG σ) (clOrientation σ hφ) := by
  have hF := isScFredholmSectionFunctor_fSec (σ := σ) hφ heq
  have hsec := hasScPlusSectionsThrough_AG σ
  refine ((AG (G := G) σ).E.isOrInvariant_iff_forall_isOrInvariantAt hF hsec).2 fun m => ?_
  have hloc : ∀ g : G, IsLocallyConstant fun q : Fin n → ℝ =>
      (AG (G := G) σ).E.IsOrInvariantAt hF hsec (clOrientation σ hφ)
        ((g, q) : (AG (G := G) σ).Mor) := fun g =>
    (IsLocallyConstant.iff_eventually_eq _).2 fun q => by
      have h := (AG (G := G) σ).E.eventually_isOrInvariantAt_iff hF hsec (isTame_AG σ)
        (admitsBumpFunctions_AG σ) (isScFredholmSectionTame_fSec σ hφ) (mem_smoothSet_AG σ)
        (isContOrOn_clOrientation σ hφ) ((g, q) : (AG (G := G) σ).Mor)
      have hc : Continuous fun q : Fin n → ℝ => ((g, q) : (AG (G := G) σ).Mor) :=
        continuous_const.prodMk continuous_id
      filter_upwards [hc.continuousAt.eventually h] with q' hq'
      exact propext hq'
  have h0 : ∀ g : G, (AG (G := G) σ).E.IsOrInvariantAt hF hsec (clOrientation σ hφ)
      ((g, (0 : Fin n → ℝ)) : (AG (G := G) σ).Mor) := fun g => by
    refine ((AG (G := G) σ).E.isOrInvariantAt_iff' hF hsec).2 fun {x x'} hx hx' hs₁ hs₂ => ?_
    obtain rfl : (0 : Fin n → ℝ) = x := hx
    obtain rfl : (0 : Fin n → ℝ) = x' := (smul_zero g).symm.trans hx'
    exact orMor_zero_eq σ hφ heq hdet g hx' hs₁ _ (isPosId_clOrientation σ hφ 0)
  obtain ⟨g, q⟩ := m
  have e := (hloc g).apply_eq_of_preconnectedSpace q 0
  exact e ▸ h0 g

end Invariance

/-- **`clOrientation` is an orientation in the sense of Definition 12.5.4**: continuous for
Part I's topology on `O_f` and invariant under the morphisms. -/
theorem definition_12_5_4_clOrientation (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) :
    haveI := paracompactSpace_rn_prod (AG (G := G) σ).X.PObj
    haveI := paracompactSpace_rn_pullback (AG (G := G) σ).B
    haveI := paracompactSpace_rn_rn_prod (AG (G := G) σ).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (AG (G := G) σ).B
    (AG (G := G) σ).E.definition_12_5_4 (isScFredholmSectionFunctor_fSec hφ heq)
      (hasScPlusSectionsThrough_AG σ)
      (orTopology (orLocalTransport (isTame_AG σ) (admitsBumpFunctions_AG σ)
        (isScFredholmSectionTame_fSec σ hφ) (hasScPlusSectionsThrough_AG σ)))
      (clOrientation σ hφ) := by
  have := paracompactSpace_rn_prod (AG (G := G) σ).X.PObj
  have := paracompactSpace_rn_pullback (AG (G := G) σ).B
  have := paracompactSpace_rn_rn_prod (AG (G := G) σ).X.PObj
  have := paracompactSpace_rn_rn_pullback (AG (G := G) σ).B
  refine ⟨?_, isOrInvariant_clOrientation σ hφ heq hdet⟩
  let := orTopology (orLocalTransport (isTame_AG σ) (admitsBumpFunctions_AG σ)
    (isScFredholmSectionTame_fSec σ hφ) (hasScPlusSectionsThrough_AG σ))
  have h := continuousOn_orSec (isContOrOn_clOrientation σ hφ)
  rw [preimage_univ] at h
  exact continuousOn_univ.1 h

/-- Part I's topology on `O_f` is a topology with the properties of Theorem 12.5.3. -/
theorem isOrientationTopology_fSec (hφ : ContDiff ℝ ∞ φ) :
    haveI := paracompactSpace_rn_prod (AG (G := G) σ).X.PObj
    haveI := paracompactSpace_rn_pullback (AG (G := G) σ).B
    haveI := paracompactSpace_rn_rn_prod (AG (G := G) σ).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (AG (G := G) σ).B
    IsOrientationTopology (B := (AG (G := G) σ).B) (fSec φ)
      (isScFredholmSectionTame_fSec σ hφ).toIsScFredholmSection
      (orTopology (orLocalTransport (isTame_AG σ) (admitsBumpFunctions_AG σ)
        (isScFredholmSectionTame_fSec σ hφ) (hasScPlusSectionsThrough_AG σ))) := by
  have := paracompactSpace_rn_prod (AG (G := G) σ).X.PObj
  have := paracompactSpace_rn_pullback (AG (G := G) σ).B
  have := paracompactSpace_rn_rn_prod (AG (G := G) σ).X.PObj
  have := paracompactSpace_rn_rn_pullback (AG (G := G) σ).B
  obtain ⟨t₀, ht₀⟩ := (theorem_6_6_17 (isTame_AG σ) (admitsBumpFunctions_AG σ)
    (isScFredholmSectionTame_fSec σ hφ)).exists
  exact eq_orTopology_of (isTame_AG σ) (admitsBumpFunctions_AG σ)
    (isScFredholmSectionTame_fSec σ hφ) (hasScPlusSectionsThrough_AG σ) ht₀.isLocalHomeomorph
    ht₀.propagation ▸ ht₀

/-- **The canonical orientation of the sc-Fredholm section `|x| ↦ |(x, φ x)|` of
`|ℝⁿ × ℝⁿ| → ℝⁿ/G`** (Definition 16.6.5, 2021 p. 739), for `det ρ(g) · det σ(g) > 0`. -/
def clOrientationRep (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) :
    OrientationRep (clFredholmSection σ hφ heq) where
  a := clRep σ hφ heq
  ha := rfl
  hF := isScFredholmSectionFunctor_fSec hφ heq
  hsec := hasScPlusSectionsThrough_AG σ
  t := haveI := paracompactSpace_rn_prod (AG (G := G) σ).X.PObj
    haveI := paracompactSpace_rn_pullback (AG (G := G) σ).B
    haveI := paracompactSpace_rn_rn_prod (AG (G := G) σ).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (AG (G := G) σ).B
    orTopology (orLocalTransport (isTame_AG σ) (admitsBumpFunctions_AG σ)
      (isScFredholmSectionTame_fSec σ hφ) (hasScPlusSectionsThrough_AG σ))
  isOrientationTopology := isOrientationTopology_fSec σ hφ
  o := clOrientation σ hφ
  isOrientation := definition_12_5_4_clOrientation σ hφ heq hdet

/-- **The standing hypotheses of Theorem 16.6.6 (2021 p. 739) for index `0` hold in the model
of `clOrientationRep`**: tame germ data and Fredholm index `0`. -/
theorem canonicalGermInput_clOrientationRep (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) :
    CanonicalGermInput (clOrientationRep σ hφ heq hdet) 0 :=
  ⟨isScFredholmSectionTame_fSec σ hφ, fun x _ => by exact_mod_cast isIndexAt_fSec σ hφ x⟩

end Polyfold.Examples.Classical
