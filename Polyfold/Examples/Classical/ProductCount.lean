import Polyfold.Examples.Classical.ProductOrientation
import Polyfold.Examples.Classical.ProductPerturbation

/-!
# The classical reduction crossed with the weighted `ℓ²` factor: the count

For Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Theorem 16.6.6,
2021 p. 739, for Fredholm index `0`.  For the section `f(x, e) = ((x, φ x), (e, e))` over
`(ℝⁿ × H)/G` (`ProductSection.lean`), the multisection `λ = tP σ c` with the branches
`((x, σ g c), (e, 0))` (`ProductPerturbation.lean`) and the canonical orientation
`prOrientationRep` (`ProductOrientation.lean`), the count (Definition 9.5.6, 2021 p. 439,
`n = 0`) of the constant form `1` is the classical count `(1/♯G) · ∑_{x ∈ φ⁻¹(c)} sign det Dφ(x)`.

## What is formalized (namespace `Polyfold.Examples.Classical.Product`)

* `prEval τ x`, `prOne σ`, `d_prOne`, `prEval_prOne`: the constant `0`-form `1` on `(ℝⁿ × H)/G`.
* **`signedWeight_prCanonical`**: for a canonical orientation `T̂` of `Λ ∘ f`, at a solution
  `(x, 0)`, `φ x = σ g c`, the signed weight of `T̂(x, 0)` is
  `sign det Dφ(x) · ♯{g | φ x = σ g c} / ♯G`.
* `exists_canonical_tP`: an admissible perturbed solution set with the canonical orientation and
  `Q.t = tP σ c` (Theorem 16.6.6, 2021 p. 739, index `0`, without bump functions).
* **`count_tP_eq_classicalCount`**: for such a `Q`, `Q.count (prOne σ) = classicalCount G φ c`;
  the orbit representatives are `(x, 0)` for orbit representatives `x` of `φ⁻¹(G · c)`, with
  isotropy `♯G_{(x, 0)} = ♯Stab_G(x)` (`card_isotropy`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Classical.Product

open TrivialBundle EpGroupoid EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure WeightedEllTwo SBLocalization StrongRetr PolyfoldClass
  Polyfold.Examples.OrbifoldSquareInf Polyfold.Examples.Classical

variable {G : Type} [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  {n : ℕ} [DistribMulAction G (Fin n → ℝ)] [SMulCommClass G ℝ (Fin n → ℝ)]
  [FaithfulSMul G (Fin n → ℝ)]
  (σ : G →* ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) {φ : (Fin n → ℝ) → (Fin n → ℝ)}

/-! ### The constant form `1` -/

/-- The value of a `0`-form on `(ℝⁿ × H)/G` at `(x, e)`, read in the model `(G ⋉ ℝⁿ) × H`. -/
def prEval (τ : ScForm (prBundle σ).polyfold 0) (x : (AP σ).Obj) : ℝ :=
  (AP σ).baseEP.zeroFormEval
    (ScForm.toStructure (prStructure σ).toPolyfoldStructure (toPolyfoldStructure_mem rfl) τ) x

/-- **The constant `0`-form `1` on `(ℝⁿ × H)/G`.** -/
def prOne : ScForm (prBundle σ).polyfold 0 :=
  ScForm.mk (prStructure σ).toPolyfoldStructure (toPolyfoldStructure_mem rfl)
    ((prStructure σ).toPolyfoldStructure.X.constFormInfty 1)

/-- The constant form `1` is closed. -/
theorem d_prOne : ScForm.d (prOne σ) = 0 := by
  have h : (prStructure σ).toPolyfoldStructure.X.epFormsInftyD 0
      ((prStructure σ).toPolyfoldStructure.X.constFormInfty 1) = 0 :=
    (prStructure σ).toPolyfoldStructure.X.epFormsInftyD_constFormInfty 1
  rw [prOne, ScForm.d_mk, h]
  have h0 := ScForm.mk_toStructure (c := (prBundle σ).polyfold)
    (prStructure σ).toPolyfoldStructure (toPolyfoldStructure_mem rfl)
    (0 : ScForm (prBundle σ).polyfold (0 + 1))
  rw [ScForm.toStructure_zero] at h0
  exact h0

/-- The constant form `1` has the value `1` at the points `(x, 0)`. -/
theorem prEval_prOne (x : Fin n → ℝ) : prEval σ (prOne σ) ((x, h0) : (AP σ).Obj) = 1 := by
  have h := ScForm.toStructure_mk (prStructure σ).toPolyfoldStructure
    (toPolyfoldStructure_mem (c := prBundle σ) rfl)
    ((prStructure σ).toPolyfoldStructure.X.constFormInfty 1)
  have h1 : prEval σ (prOne σ) ((x, h0) : (AP σ).Obj) =
      (prStructure σ).toPolyfoldStructure.X.zeroFormEval
        ((prStructure σ).toPolyfoldStructure.X.constFormInfty 1) ((x, h0) : (AP σ).Obj) :=
    congrArg (fun τ => (prStructure σ).toPolyfoldStructure.X.zeroFormEval τ
      ((x, h0) : (AP σ).Obj)) h
  exact h1.trans ((prStructure σ).toPolyfoldStructure.X.zeroFormEval_constFormInfty 1
    (mem_smoothSet_mk_h0P (σ := σ) x))

/-! ### The signed weight at a perturbed solution -/

/-- **The signed weight of a canonical orientation at a perturbed solution** (Theorem 15.4.1,
2021 pp. 701–702, dimension `0`, with the canonical orientation `prOrientation`): at a solution
`(x, 0)`, `φ x = σ g c`, of a regular value `c`, the signed weight of `T̂(x, 0)` is
`sign det Dφ(x) · ♯{g | φ x = σ g c} / ♯G`. -/
theorem signedWeight_prCanonical (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    {c : Fin n → ℝ} (hc : ∀ x, φ x = c → Surjective (fderiv ℝ φ x))
    {T : (AP σ).Obj → (AP σ).X.PObj.OrTangent →₀ ℚ}
    (h : IsCanonicalFor (ΛP σ c) (prOrientationRep σ hφ heq hdet).hF.2
      (prOrientationRep σ hφ heq hdet).hsec (prOrientationRep σ hφ heq hdet).o 0 T)
    {x : Fin n → ℝ} (hx : ∃ g : G, φ x = σ g c) :
    signedWeight (X := (AP σ).X) (T ((x, h0) : (AP σ).Obj)) =
      (SignType.sign (LinearMap.det (fderiv ℝ φ x : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) : ℝ) *
        ((hitCount (fun g w => σ g w) φ c x : ℝ) / Fintype.card G) := by
  classical
  have hf := (prOrientationRep σ hφ heq hdet).hF.2
  obtain ⟨g₀, hg₀⟩ := hx
  have hsurj := surjective_fderiv_of_eq hφ heq hc hg₀
  have hbφ : Bijective (fderiv ℝ φ x) :=
    ⟨(LinearMap.injective_iff_surjective
      (f := (fderiv ℝ φ x : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))).2 hsurj, hsurj⟩
  have hdne := det_ne_zero_of_bijective hbφ
  have hpos : 0 < ΛP σ c (fP σ φ ((x, h0) : (AP σ).Obj)) :=
    (ΛP_fP_pos_iff σ c ((x, h0) : (Fin n → ℝ) × HObj)).2 ⟨⟨g₀, hg₀⟩, rfl⟩
  have hy : ((x, h0) : (AP σ).Obj) ∈
      EpGroupoid.supp (fun z : (AP σ).Obj => ((ΛP σ c (fP σ φ z) : ℚ≥0) : ℚ)) := by
    change (0 : ℚ) < _
    exact_mod_cast hpos
  have hys := mem_smoothSet_mk_h0P (σ := σ) x
  let S : Fin (Fintype.card G) → (AP σ).Obj → (AP σ).W := fun j =>
    gP σ fun _ => -(σ ((Fintype.equivFin G).symm j) c)
  have hS : ∀ j, (AP σ).B.IsScPlusSection (S j) := fun j =>
    isScPlusSection_gP σ contDiff_const
  have key := IsCanonicalFor.signedWeight_eq_sign h hy hys isOpen_univ (mem_univ _)
    (isLocalRepOn_ΛP σ c) S hS
    (fun j x' _ => congrFun (subSec_branchP σ c ((Fintype.equivFin G).symm j)).symm x')
    (0 < LinearMap.det (fderiv ℝ φ x : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    (fun j hj => by
      have hb : Bijective (fderiv ℝ (φ + fun _ => -(σ ((Fintype.equivFin G).symm j) c)) x) := by
        rw [fderiv_add_const_fun]; exact hbφ
      have e : φ x = σ ((Fintype.equivFin G).symm j) c :=
        (congrArg (fun w : (AP σ).W => w.1.2) hj).symm
      have hx0 : IsZeroAt (AP σ).P (sectionAdd (AP σ).P (fP σ φ) (S j))
          ((x, h0) : (AP σ).Obj) := by
        refine isZeroAt_gP σ hf (hS j) ?_
        change φ x + -(σ ((Fintype.equivFin G).symm j) c) = 0
        rw [e, add_neg_cancel]
      refine ⟨hx0, ⟨orPt (AP σ).B ((x, h0) : (AP σ).Obj) hys,
        bijective_stabT_P σ hφ contDiff_const hf (hS j) hx0 hb _⟩, ?_⟩
      refine (isPosOr_prOrientation_iff σ hφ heq hf hys contDiff_const (hS j) hx0 hb).trans ?_
      rw [fderiv_add_const_fun])
  refine key.trans ?_
  rw [← sign_eq_ite hdne]
  refine congrArg (_ * ·) ?_
  change (((ΛP σ c (fP σ φ ((x, h0) : (Fin n → ℝ) × HObj)) : ℚ≥0) : ℚ) : ℝ) = _
  rw [ΛP_fP_eq, if_pos rfl, hitCount_eq_card]
  push_cast
  rfl

/-! ### The count -/

/-- **The multisection `λ = tP σ c` is admissible and has a canonically oriented perturbed
solution set** (Theorem 16.6.6, 2021 p. 739, index `0`), for a regular value `c` of a proper `φ`
with `gNorm σ c ≤ 1`. -/
theorem exists_canonical_tP (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    (hprop : ∀ K, IsCompact K → IsCompact (φ ⁻¹' K)) {c : Fin n → ℝ}
    (hc : ∀ x, φ x = c → Surjective (fderiv ℝ φ x)) (hc1 : gNorm σ c ≤ 1) :
    ∃ Q : PointOrientedPerturbation (prFredholmSection σ hφ heq).1, Q.t = tP σ c ∧
      Q.IsAdmissible (nP σ) (univ : Set (AP σ).X.OrbitSpace) ∧
      IsCanonicalPointSolutionSet (prOrientationRep σ hφ heq hdet) Q :=
  theorem_16_6_6_index_zero_solutionSet_noBumps (prBundle_boundary_eq_empty σ) (isAuxNorm_nP σ)
    isOpen_univ (controlsCompactness_nP hφ heq hprop)
    (canonicalGermInput_prOrientationRep σ hφ heq hdet) (tP σ c) (isControlledBy_tP hc1)
    (isInGeneralPositionWith_tP hφ heq hc)

/-- The embedding `x ↦ (x, 0)` of `ℝⁿ` into `ℝⁿ × H`. -/
def embH0 : (Fin n → ℝ) ↪ (AP σ).Obj :=
  ⟨fun x => ((x, h0) : (Fin n → ℝ) × HObj), fun _ _ h => congrArg Prod.fst h⟩

set_option maxHeartbeats 1600000 in
-- the model of the orientation is unfolded to `AP σ`
/-- **The count of `λ = tP σ c` is the classical count** (Definition 9.5.6, 2021 p. 439,
`n = 0`): a perturbed solution set `Q` with `Q.t = tP σ c` and the canonical orientation is the
class of a point solution set `(ΛP σ c, T̂)`; over the orbit representatives `(x, 0)`, `x` running
over orbit representatives of `φ⁻¹(G · c)`, its count of the constant form `1` is
`∑_x (♯G_x)⁻¹ · sign det Dφ(x) · ♯{g | φ x = σ g c} / ♯G = (1/♯G) ∑_{φ(x) = c} sign det Dφ(x)`. -/
theorem count_tP_eq_classicalCount (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    (hprop : ∀ K, IsCompact K → IsCompact (φ ⁻¹' K)) {c : Fin n → ℝ}
    (hc : ∀ x, φ x = c → Surjective (fderiv ℝ φ x))
    {Q : PointOrientedPerturbation (prFredholmSection σ hφ heq).1} (ht : Q.t = tP σ c)
    (hcan : IsCanonicalPointSolutionSet (prOrientationRep σ hφ heq hdet) Q) :
    Q.count (prOne σ) = classicalCount G φ c := by
  classical
  obtain ⟨P, hP, rfl⟩ := hcan
  have hΛ : P.Λ = ΛP σ c := by
    have h1 := congrArg ScPlusMultisection.toFun ht
    funext w
    have ca := (ofFunctor (prStructure σ) rfl P.Λ P.isScPlusMultisection).comm w
    have cb := (ofFunctor (prStructure σ) rfl (ΛP σ c) (isScPlusMultisection_ΛP σ c)).comm w
    exact ca.symm.trans ((congrFun h1 _).trans cb)
  have hP' : IsCanonicalFor (ΛP σ c) (prOrientationRep σ hφ heq hdet).hF.2
      (prOrientationRep σ hφ heq hdet).hsec (prOrientationRep σ hφ heq hdet).o 0 P.T :=
    hΛ ▸ hP
  have hfin := finite_preimage_of_regular (hφ.of_le (by simp)) hprop hc
  obtain ⟨s, hs⟩ := exists_isOrbitReps_of_finite heq hfin
  let s' : Finset (AP σ).Obj := s.map (embH0 σ)
  have hpos : ∀ x ∈ s', 0 < P.Λ (fP σ φ x) := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
    rw [hΛ]
    exact (ΛP_fP_pos_iff σ c ((y, h0) : (Fin n → ℝ) × HObj)).2 ⟨hs.1 y hy, rfl⟩
  have hinj : Set.InjOn (AP σ).X.π (↑s' : Set (AP σ).Obj) := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 hx)
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 hy)
    obtain ⟨g, hg, -⟩ := (π_eq_π_iff (G := G) (x := ((a, h0) : (Fin n → ℝ) × HObj))
      (y := ((b, h0) : (Fin n → ℝ) × HObj))).1 hxy
    rw [hs.2.1 a ha b hb ⟨g, hg⟩]
  have hcov : ∀ y, 0 < P.Λ (fP σ φ y) → ∃ x ∈ s', (AP σ).X.π x = (AP σ).X.π y := by
    intro y hy
    rw [hΛ] at hy
    obtain ⟨hy1, hy2⟩ := (ΛP_fP_pos_iff σ c y).1 hy
    obtain ⟨x, hx, g, hg⟩ := hs.2.2 y.1 hy1
    exact ⟨embH0 σ x, Finset.mem_map_of_mem (embH0 σ) hx,
      (π_eq_π_iff (G := G) (x := ((x, h0) : (Fin n → ℝ) × HObj)) (y := y)).2
        ⟨g, hg, hy2.symm⟩⟩
  refine (count_solutionPointSuborbifold (c := prBundle σ) (prOrientationRep σ hφ heq hdet).a P
    (prOne σ)).trans ?_
  refine (P.count_eq_sum _ s' hpos hinj hcov).trans ?_
  refine (Finset.sum_map s (embH0 σ) _).trans ?_
  refine Eq.trans ?_
    (sum_orbitReps_eq_classicalCount (hφ.differentiable (by simp)) heq hdet hfin hs)
  refine Finset.sum_congr rfl fun (x : Fin n → ℝ) hx => ?_
  have h1 : Nat.card ((prOrientationRep σ hφ heq hdet).a.S.A.X.Isotropy (embH0 σ x)) =
      Nat.card (MulAction.stabilizer G x) := card_isotropy G ((x, h0) : (Fin n → ℝ) × HObj)
  have h2 : (prOrientationRep σ hφ heq hdet).a.S.A.baseEP.zeroFormEval
      (ScForm.toStructure (prOrientationRep σ hφ heq hdet).a.S.toPolyfoldStructure
        (toPolyfoldStructure_mem (prOrientationRep σ hφ heq hdet).a.hS) (prOne σ))
        (embH0 σ x) = 1 :=
    prEval_prOne σ x
  have h3 := signedWeight_prCanonical σ hφ heq hdet hc hP' (hs.1 x hx)
  rw [h1, h2, mul_one]
  exact congrArg (_ * ·) h3

end Polyfold.Examples.Classical.Product
