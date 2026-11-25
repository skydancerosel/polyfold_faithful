import Polyfold.Examples.Classical.Orientation
import Polyfold.Examples.Classical.Perturbation
import Polyfold.Examples.Classical.SignedWeight
import Polyfold.Examples.Classical.ClassicalSum

/-!
# The classical reduction: the count of the perturbed solution set

For a finite group `G` acting linearly on `ℝⁿ`, a fibre action `σ` with
`det ρ(g) · det σ(g) > 0`, a proper equivariant `C^∞` map `φ : ℝⁿ → ℝⁿ` and a regular value `c`
with `gNorm σ c ≤ 1`, the count (Definition 9.5.6, 2021 p. 439, `n = 0`) of the perturbed
solution set of the multisection `λ = tG σ c` with the canonical orientation `clOrientationRep`
on the constant form `1` is the classical count `(1/♯G) · ∑_{x ∈ φ⁻¹(c)} sign det Dφ(x)`.

## What is formalized (namespace `Polyfold.Examples.Classical`)

* `clEval τ x`: the value of a `0`-form `τ` on `ℝⁿ/G` at `x ∈ ℝⁿ`, read in the model.
* `clOne σ`: the constant `0`-form `1`; `d_clOne` (closed), `clEval_clOne` (value `1`).
* `subSec_graphSection_const`: `f − s = f + (−s)` for a constant section `s`.
* **`signedWeight_clCanonical`**: for a canonical orientation `T̂` of `Λ ∘ f`, at a solution
  `φ x = σ g c` the signed weight of `T̂(x)` is `sign det Dφ(x) · ♯{g | φ x = σ g c} / ♯G`
  (`IsCanonicalFor.signedWeight_eq_sign`, `isPosOr_clOrientation_iff`).
* `exists_canonical_tG`: an admissible perturbed solution set with the canonical orientation and
  `Q.t = tG σ c` (Theorem 16.6.6, 2021 p. 739, index `0`, without bump functions).
* **`count_tG_eq_classicalCount`**: for such a `Q`, `Q.count (clOne σ) = classicalCount G φ c`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Classical

open TrivialBundle EpGroupoid EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure SBLocalization PolyfoldClass

variable {G : Type} [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  {n : ℕ} [DistribMulAction G (Fin n → ℝ)] [SMulCommClass G ℝ (Fin n → ℝ)]
  [FaithfulSMul G (Fin n → ℝ)]
  (σ : G →* ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) {φ : (Fin n → ℝ) → (Fin n → ℝ)}

/-! ### The constant form `1` -/

/-- The value of a `0`-form on `ℝⁿ/G` at `x ∈ ℝⁿ`, read in the model `G ⋉ ℝⁿ`. -/
def clEval (τ : ScForm (clBundle σ).polyfold 0) (x : Fin n → ℝ) : ℝ :=
  (AG σ).baseEP.zeroFormEval
    (ScForm.toStructure (clStructure σ).toPolyfoldStructure (toPolyfoldStructure_mem rfl) τ) x

/-- **The constant `0`-form `1` on `ℝⁿ/G`.** -/
def clOne : ScForm (clBundle σ).polyfold 0 :=
  ScForm.mk (clStructure σ).toPolyfoldStructure (toPolyfoldStructure_mem rfl)
    ((clStructure σ).toPolyfoldStructure.X.constFormInfty 1)

/-- The constant form `1` is closed. -/
theorem d_clOne : ScForm.d (clOne σ) = 0 := by
  have h : (clStructure σ).toPolyfoldStructure.X.epFormsInftyD 0
      ((clStructure σ).toPolyfoldStructure.X.constFormInfty 1) = 0 :=
    (clStructure σ).toPolyfoldStructure.X.epFormsInftyD_constFormInfty 1
  rw [clOne, ScForm.d_mk, h]
  have h0 := ScForm.mk_toStructure (c := (clBundle σ).polyfold)
    (clStructure σ).toPolyfoldStructure (toPolyfoldStructure_mem rfl)
    (0 : ScForm (clBundle σ).polyfold (0 + 1))
  rw [ScForm.toStructure_zero] at h0
  exact h0

/-- The constant form `1` has the value `1` at every point. -/
theorem clEval_clOne (x : Fin n → ℝ) : clEval σ (clOne σ) x = 1 := by
  have h := ScForm.toStructure_mk (clStructure σ).toPolyfoldStructure
    (toPolyfoldStructure_mem (c := clBundle σ) rfl)
    ((clStructure σ).toPolyfoldStructure.X.constFormInfty 1)
  have h1 : clEval σ (clOne σ) x = (clStructure σ).toPolyfoldStructure.X.zeroFormEval
      ((clStructure σ).toPolyfoldStructure.X.constFormInfty 1) x :=
    congrArg (fun τ => (clStructure σ).toPolyfoldStructure.X.zeroFormEval τ x) h
  exact h1.trans ((clStructure σ).toPolyfoldStructure.X.zeroFormEval_constFormInfty 1
    (mem_smoothSet_AG σ x))

/-! ### The signed weight at a perturbed solution -/

/-- `f − s = f + (−s)` for the constant section `s` through `b`. -/
theorem subSec_graphSection_const (b : Fin n → ℝ) :
    subSec (A := AG σ) (fSec φ) (graphSection fun _ => b) univ =
      sectionAdd (AG σ).P (fSec φ) (graphSection fun _ => -b) := by
  have hsec : IsSection (AG σ).P (graphSection (n := n) (k := n) fun _ => b) :=
    isSection_graphSection
  have he : extendZero (A := AG σ) univ (graphSection fun _ => b) = graphSection fun _ => b :=
    funext fun y => (extendZero_eqOn (A := AG σ) (fun y _ => hsec y) (mem_univ y)).symm
  unfold subSec
  rw [he]
  congr 1
  funext x
  rw [sectionSmul_apply hsec]
  refine Prod.ext (fst_fiber _) ?_
  refine (snd_smul _ _).trans ?_
  change (-1 : ℝ) • b = -b
  rw [neg_one_smul]

/-- `D(φ + const)(x) = Dφ(x)`. -/
theorem fderiv_add_const_fun (φ : (Fin n → ℝ) → (Fin n → ℝ)) (b x : Fin n → ℝ) :
    fderiv ℝ (φ + fun _ => b) x = fderiv ℝ φ x :=
  fderiv_add_const (f := φ) b

/-- A bijective endomorphism of `ℝⁿ` has nonzero determinant. -/
theorem det_ne_zero_of_bijective {L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} (hb : Bijective L) :
    LinearMap.det (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ≠ 0 :=
  (LinearEquiv.ofBijective (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) hb).isUnit_det'.ne_zero

/-- `sign d = if 0 < d then 1 else -1` for `d ≠ 0`. -/
theorem sign_eq_ite {d : ℝ} (hd : d ≠ 0) :
    ((SignType.sign d : SignType) : ℝ) = if 0 < d then 1 else -1 := by
  by_cases h : 0 < d
  · rw [if_pos h, sign_pos h]; rfl
  · rw [if_neg h, sign_neg (lt_of_le_of_ne (not_lt.1 h) hd)]; rfl

/-- `♯{g | φ x = σ g c}` as a `Finset` filter. -/
theorem hitCount_eq_card (c x : Fin n → ℝ) :
    (hitCount (fun g w => σ g w) φ c x : ℝ) =
      ((Finset.univ.filter fun g : G => φ x = σ g c).card : ℝ) := by
  classical
  unfold hitCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **The signed weight of a canonical orientation at a perturbed solution** (Theorem 15.4.1,
2021 pp. 701–702, dimension `0`, with the canonical orientation `clOrientation`): at a solution
`φ x = σ g c` of a regular value `c`, the signed weight of `T̂(x)` is
`sign det Dφ(x) · ♯{g | φ x = σ g c} / ♯G`. -/
theorem signedWeight_clCanonical (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    {c : Fin n → ℝ} (hc : ∀ x, φ x = c → Surjective (fderiv ℝ φ x))
    {T : (AG σ).Obj → (AG σ).X.PObj.OrTangent →₀ ℚ}
    (h : IsCanonicalFor (ΛG σ c) (clOrientationRep σ hφ heq hdet).hF.2
      (clOrientationRep σ hφ heq hdet).hsec (clOrientationRep σ hφ heq hdet).o 0 T)
    {x : Fin n → ℝ} (hx : ∃ g : G, φ x = σ g c) :
    signedWeight (X := (AG σ).X) (T x) =
      (SignType.sign (LinearMap.det (fderiv ℝ φ x : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) : ℝ) *
        ((hitCount (fun g w => σ g w) φ c x : ℝ) / Fintype.card G) := by
  classical
  have hf := (clOrientationRep σ hφ heq hdet).hF.2
  obtain ⟨g₀, hg₀⟩ := hx
  have hsurj := surjective_fderiv_of_eq hφ heq hc hg₀
  have hbφ : Bijective (fderiv ℝ φ x) :=
    ⟨(LinearMap.injective_iff_surjective
      (f := (fderiv ℝ φ x : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))).2 hsurj, hsurj⟩
  have hdne := det_ne_zero_of_bijective hbφ
  have hpos : 0 < ΛG σ c (fSec φ x) := (ΛG_fSec_pos_iff σ c x).2 ⟨g₀, hg₀⟩
  have hy : (x : (AG σ).Obj) ∈
      EpGroupoid.supp (fun z : (AG σ).Obj => ((ΛG σ c (fSec φ z) : ℚ≥0) : ℚ)) := by
    change (0 : ℚ) < _
    exact_mod_cast hpos
  have hys := mem_smoothSet_AG σ x
  let S : Fin (Fintype.card G) → (AG σ).Obj → (AG σ).W := fun j =>
    graphSection fun _ => -(σ ((Fintype.equivFin G).symm j) c)
  have hS : ∀ j, (AG σ).B.IsScPlusSection (S j) := fun j =>
    isScPlusSection_graphSection contDiff_const
  have key := IsCanonicalFor.signedWeight_eq_sign h hy hys isOpen_univ (mem_univ _)
    (isLocalRepOn_ΛG σ c) S hS
    (fun j x' _ => congrFun (subSec_graphSection_const σ (σ ((Fintype.equivFin G).symm j) c)).symm
      x')
    (0 < LinearMap.det (fderiv ℝ φ x : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    (fun j hj => by
      have hb : Bijective (fderiv ℝ (φ + fun _ => -(σ ((Fintype.equivFin G).symm j) c)) x) := by
        rw [fderiv_add_const_fun]; exact hbφ
      have e : φ x = σ ((Fintype.equivFin G).symm j) c := (congrArg Prod.snd hj).symm
      have hx0 : IsZeroAt (AG σ).P (sectionAdd (AG σ).P (fSec φ) (S j)) x := by
        change IsZeroAt (proj n n) (sectionAdd (proj n n) (graphSection φ)
          (graphSection fun _ => -(σ ((Fintype.equivFin G).symm j) c))) x
        rw [sectionAdd_graphSection_std]
        refine isZeroAt_graphSection_iff.2 ?_
        change φ x + -(σ ((Fintype.equivFin G).symm j) c) = 0
        rw [e, add_neg_cancel]
      refine ⟨hx0, ⟨orPt (AG σ).B x hys,
        bijective_stabT_graph σ hφ hf contDiff_const rfl (hS j) hx0 hb _⟩, ?_⟩
      refine (isPosOr_clOrientation_iff σ hφ hf hys contDiff_const (hS j) hx0 hb).trans ?_
      rw [fderiv_add_const_fun])
  refine key.trans ?_
  rw [← sign_eq_ite hdne]
  refine congrArg (_ * ·) ?_
  change (((ΛG σ c (fSec φ x) : ℚ≥0) : ℚ) : ℝ) = _
  rw [ΛG_fSec, hitCount_eq_card]
  push_cast
  rfl

/-! ### The count -/

/-- **The multisection `λ = tG σ c` is admissible and has a canonically oriented perturbed
solution set** (Theorem 16.6.6, 2021 p. 739, index `0`), for a regular value `c` of a proper `φ`
with `gNorm σ c ≤ 1`. -/
theorem exists_canonical_tG (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    (hprop : ∀ K, IsCompact K → IsCompact (φ ⁻¹' K)) {c : Fin n → ℝ}
    (hc : ∀ x, φ x = c → Surjective (fderiv ℝ φ x)) (hc1 : gNorm σ c ≤ 1) :
    ∃ Q : PointOrientedPerturbation (clFredholmSection σ hφ heq).1, Q.t = tG σ c ∧
      Q.IsAdmissible (nG σ) (univ : Set (AG σ).X.OrbitSpace) ∧
      IsCanonicalPointSolutionSet (clOrientationRep σ hφ heq hdet) Q :=
  theorem_16_6_6_index_zero_solutionSet_noBumps (clBundle_boundary_eq_empty σ) (isAuxNorm_nG σ)
    isOpen_univ (controlsCompactness_nG hφ heq hprop)
    (canonicalGermInput_clOrientationRep σ hφ heq hdet) (tG σ c) (isControlledBy_tG hc1)
    (isInGeneralPositionWith_tG hφ heq hc)

set_option maxHeartbeats 1600000 in
-- the model of the orientation is unfolded to `AG σ`
/-- **The count of `λ = tG σ c` is the classical count** (Definition 9.5.6, 2021 p. 439,
`n = 0`): a perturbed solution set `Q` with `Q.t = tG σ c` and the canonical orientation is the
class of a point solution set `(ΛG σ c, T̂)`; over orbit representatives `x` of `φ⁻¹(G · c)` its
count of the constant form `1` is
`∑_x (♯G_x)⁻¹ · sign det Dφ(x) · ♯{g | φ x = σ g c} / ♯G = (1/♯G) ∑_{φ(x) = c} sign det Dφ(x)`. -/
theorem count_tG_eq_classicalCount (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    (hprop : ∀ K, IsCompact K → IsCompact (φ ⁻¹' K)) {c : Fin n → ℝ}
    (hc : ∀ x, φ x = c → Surjective (fderiv ℝ φ x))
    {Q : PointOrientedPerturbation (clFredholmSection σ hφ heq).1} (ht : Q.t = tG σ c)
    (hcan : IsCanonicalPointSolutionSet (clOrientationRep σ hφ heq hdet) Q) :
    Q.count (clOne σ) = classicalCount G φ c := by
  classical
  obtain ⟨P, hP, rfl⟩ := hcan
  have hΛ : P.Λ = ΛG σ c := by
    have h1 := congrArg ScPlusMultisection.toFun ht
    funext w
    have ca := (ofFunctor (clStructure σ) rfl P.Λ P.isScPlusMultisection).comm w
    have cb := (ofFunctor (clStructure σ) rfl (ΛG σ c) (isScPlusMultisection_ΛG σ c)).comm w
    exact ca.symm.trans ((congrFun h1 _).trans cb)
  have hP' : IsCanonicalFor (ΛG σ c) (clOrientationRep σ hφ heq hdet).hF.2
      (clOrientationRep σ hφ heq hdet).hsec (clOrientationRep σ hφ heq hdet).o 0 P.T :=
    hΛ ▸ hP
  have hfin := finite_preimage_of_regular (hφ.of_le (by simp)) hprop hc
  obtain ⟨s, hs⟩ := exists_isOrbitReps_of_finite heq hfin
  let s' : Finset (AG σ).Obj := s
  have hpos : ∀ x ∈ s', 0 < P.Λ (fSec φ x) := fun x hx => by
    rw [hΛ]
    exact (ΛG_fSec_pos_iff σ c x).2 (hs.1 x hx)
  have hinj : Set.InjOn (AG σ).X.π (↑s' : Set (AG σ).Obj) := by
    intro x hx y hy hxy
    exact hs.2.1 x hx y hy ((action_π_eq_π_iff isScSmoothMap_smul).1 hxy)
  have hcov : ∀ y, 0 < P.Λ (fSec φ y) → ∃ x ∈ s', (AG σ).X.π x = (AG σ).X.π y := by
    intro y hy
    rw [hΛ] at hy
    obtain ⟨x, hx, hxy⟩ := hs.2.2 y ((ΛG_fSec_pos_iff σ c y).1 hy)
    exact ⟨x, hx, (action_π_eq_π_iff isScSmoothMap_smul).2 hxy⟩
  refine (count_solutionPointSuborbifold (c := clBundle σ) (clOrientationRep σ hφ heq hdet).a P
    (clOne σ)).trans ?_
  refine (P.count_eq_sum _ s' hpos hinj hcov).trans ?_
  refine Eq.trans ?_
    (sum_orbitReps_eq_classicalCount (hφ.differentiable (by simp)) heq hdet hfin hs)
  refine Finset.sum_congr rfl fun (x : Fin n → ℝ) hx => ?_
  have h1 : Nat.card ((clOrientationRep σ hφ heq hdet).a.S.A.X.Isotropy x) =
      Nat.card (MulAction.stabilizer G x) := card_isotropy G x
  have h2 : (clOrientationRep σ hφ heq hdet).a.S.A.baseEP.zeroFormEval
      (ScForm.toStructure (clOrientationRep σ hφ heq hdet).a.S.toPolyfoldStructure
        (toPolyfoldStructure_mem (clOrientationRep σ hφ heq hdet).a.hS) (clOne σ)) x = 1 :=
    clEval_clOne σ x
  have h3 := signedWeight_clCanonical σ hφ heq hdet hc hP' (hs.1 x hx)
  rw [h1, h2, mul_one]
  exact congrArg (_ * ·) h3

end Polyfold.Examples.Classical
