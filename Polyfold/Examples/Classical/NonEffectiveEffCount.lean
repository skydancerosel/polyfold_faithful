import Polyfold.Examples.Classical.Main

/-!
# The classical reduction without effectiveness: the effective count

Theorem 16.6.6, 2021 p. 739, for Fredholm index `0`, for the section `|x| ↦ |(x, φ x)|` of
`|ℝⁿ × ℝⁿ| → ℝⁿ/G`, `G` acting linearly on `ℝⁿ` with kernel `K` (`baseKernel G n`), not
necessarily faithfully.  The effective count `∮` (Definition 9.5.6 (2), 2021 p. 439, with the
measure of Theorem 9.5.5, weights `1/♯G_x^eff`) of the constant form `1` is `♯K` times the count:
`∮ 1 = (♯K/♯G) · ∑_{x ∈ φ⁻¹(c)} sign det Dφ(x) = (1/♯(G/K)) · ∑_{x ∈ φ⁻¹(c)} sign det Dφ(x)`.

## What is formalized (namespace `Polyfold.Examples.Classical.NonEffective`)

* `pointBranchedIntegralEff_eq_sum`: for an oriented tame compact `Θ̂` of dimension `0` with finite
  orbit support `{|x| : x ∈ s}`,
  `∮_Θ̂ ω = ∑_{x ∈ s} (♯G_x/♯G_x^eff) · (1/♯G_x) · signedWeight (T x) · ω(x)`.
* `countEff_eq_mul`: for a point solution set with finite orbit support, if `♯G_x/♯G_x^eff = r`
  at every point, then `∮ ω = r · ∫ ω`.
* `card_isotropy_div_card_effIsotropy`: in `G ⋉ ℝⁿ`, `♯G_x/♯G_x^eff = ♯K` at every `x`.
* `preimage_eq_empty_of_ne_one`: if `σ` is nontrivial on `K`, a regular value of `φ` has empty
  preimage, so both counts are `0`.
* **`countEff_tG_eq`**, **`countEff_eq_classicalCount`**: every admissible perturbed solution set
  with the canonical orientation has
  `Q.countEff 1 = ♯K · classicalCount G φ c = (♯K/♯G) · ∑_{φ(x) = c} sign det Dφ(x)`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module MeasureTheory

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Classical.NonEffective

open TrivialBundle EpGroupoid EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure SBLocalization PolyfoldClass

/-! ### The effective count over a finite orbit support -/

section General

universe u

variable (A : EP.{u}) {Θ : A.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}

/-- **Definition 9.5.6 (2), 2021 p. 439, for `n = 0` and a finite orbit support**: with the
measure of Theorem 9.5.5,
`∮_Θ̂ η = ∑_{x ∈ s} (♯G_x/♯G_x^eff) · (1/♯G_x) · signedWeight (T x) · η(x)` when the orbit support of `Θ` is `{|x| : x ∈ s}` for a finite set `s` of points of `supp Θ` with
pairwise different orbits. -/
theorem pointBranchedIntegralEff_eq_sum (hLUC : A.X.IsLUC) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T) (hloc : A.X.IsPointTame Θ T)
    (η : A.epFormsInfty 0) (s : Finset A.Obj) (hs : ∀ x ∈ s, x ∈ supp Θ)
    (hinj : Set.InjOn A.X.π (↑s : Set A.Obj)) (hcov : A.X.orbitSupp Θ ⊆ A.X.π '' (↑s : Set A.Obj)) :
    A.pointBranchedIntegralEff hLUC hΘ hcpt hT hloc η =
      ∑ x ∈ s, (Nat.card (A.X.Isotropy x) : ℝ) / (Nat.card (A.X.EffIsotropy x) : ℝ) *
        ((Nat.card (A.X.Isotropy x) : ℝ)⁻¹ * (signedWeight (T x) * A.zeroFormEval η x)) := by
  classical
  have hborel : ∀ q : A.X.orbitSupp Θ,
      MeasurableSet[borel (A.X.orbitSupp Θ)] ({q} : Set (A.X.orbitSupp Θ)) := fun q => by
    have h : MeasurableSet[borel (A.X.orbitSupp Θ)] ({q}ᶜ : Set (A.X.orbitSupp Θ)) :=
      MeasurableSpace.measurableSet_generateFrom
        (show IsOpen ({q}ᶜ : Set (A.X.orbitSupp Θ)) from isOpen_compl_singleton)
    exact @MeasurableSet.of_compl _ _ (borel _) h
  let m : MeasurableSpace (A.X.orbitSupp Θ) :=
    A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X)) Θ
  let μ : @SignedMeasure (A.X.orbitSupp Θ) m :=
    branchedMeasureEff A.zeroFormIntegration hΘ hcpt hT (hloc.hasLUC hLUC) η
  let p : {x // x ∈ s} → A.X.orbitSupp Θ := fun x => ⟨A.X.π x.1, ⟨x.1, hs x.1 x.2, rfl⟩⟩
  have hp : Injective p := fun x y h =>
    Subtype.ext (hinj x.2 y.2 (congrArg Subtype.val h))
  let s' : Finset (A.X.orbitSupp Θ) := s.attach.image p
  have huniv : (univ : Set (A.X.orbitSupp Θ)) = ↑s' := by
    refine (eq_univ_of_forall fun q => ?_).symm
    obtain ⟨x, hx, hq⟩ := hcov q.2
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨⟨x, hx⟩, Finset.mem_attach _ _,
      Subtype.ext hq⟩)
  have hmeas : ∀ q : A.X.orbitSupp Θ, MeasurableSet[m] ({q} : Set (A.X.orbitSupp Θ)) :=
    fun q => borel_le_borelNullSigma _ _ (hborel q)
  have hpt : ∀ x : {x // x ∈ s}, μ {p x} =
      (Nat.card (A.X.Isotropy x.1) : ℝ) / (Nat.card (A.X.EffIsotropy x.1) : ℝ) *
        ((Nat.card (A.X.Isotropy x.1) : ℝ)⁻¹ *
          (signedWeight (T x.1) * A.zeroFormEval η x.1)) := by
    intro x
    obtain ⟨C, hS, hCT⟩ := hloc x.1 (hs x.1 x.2)
    have himg : Subtype.val '' ({p x} : Set (A.X.orbitSupp Θ)) = {A.X.π x.1} := by
      rw [image_singleton]
    have hKU : Subtype.val '' ({p x} : Set (A.X.orbitSupp Θ)) ⊆ A.X.π '' C.U := by
      rw [himg]
      exact singleton_subset_iff.2 ⟨x.1, C.mem_U, rfl⟩
    have h1 := A.pointBranchedMeasureEff_apply hLUC hΘ hcpt hT hloc η C hS hCT (hmeas (p x)) hKU
    rw [himg] at h1
    refine h1.trans ?_
    rw [OrientedTameStructure.localMeasureEff_eq,
      A.localMeasure_point (hΘ.support_subset (hs x.1 x.2)) C hS hCT η (mem_singleton _)]
  change μ univ = _
  rw [huniv, @signedMeasure_coe_finset _ m μ s' fun q _ => hmeas q,
    Finset.sum_image fun x _ y _ h => hp h]
  rw [Finset.sum_congr rfl fun x _ => hpt x]
  exact Finset.sum_attach s fun x =>
    (Nat.card (A.X.Isotropy x) : ℝ) / (Nat.card (A.X.EffIsotropy x) : ℝ) *
      ((Nat.card (A.X.Isotropy x) : ℝ)⁻¹ * (signedWeight (T x) * A.zeroFormEval η x))

variable {A : SEP.{u}} {f : A.Obj → A.W}

/-- **The effective count is a constant multiple of the count**: for a point solution set whose
orbit support is `{|x| : x ∈ s}` for a finite set `s` of perturbed solutions with pairwise
different orbits, if `♯G_x/♯G_x^eff = r` at every point of `s`, then `∮ η = r · ∫ η`. -/
theorem countEff_eq_mul (hLUC : A.X.IsLUC) (P : PointSolution A f) (η : A.baseEP.epFormsInfty 0)
    (s : Finset A.Obj) (hs : ∀ x ∈ s, 0 < P.Λ (f x))
    (hinj : Set.InjOn A.X.π (↑s : Set A.Obj))
    (hcov : ∀ y, 0 < P.Λ (f y) → ∃ x ∈ s, A.X.π x = A.X.π y) (r : ℝ)
    (hr : ∀ x ∈ s, (Nat.card (A.X.Isotropy x) : ℝ) / (Nat.card (A.X.EffIsotropy x) : ℝ) = r) :
    P.countEff hLUC η = r * P.count η := by
  have hs' : ∀ x ∈ s, x ∈ EpGroupoid.supp (fun z => (P.Λ (f z) : ℚ)) := fun x hx => by
    change (0 : ℚ) < _
    exact_mod_cast hs x hx
  have hcov' : A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ)) ⊆ A.X.π '' (↑s : Set A.Obj) := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : (0 : ℚ) < (P.Λ (f y) : ℚ) := hy
    obtain ⟨x, hx, hxy⟩ := hcov y (by exact_mod_cast hy')
    exact ⟨x, hx, hxy⟩
  have e := pointBranchedIntegralEff_eq_sum A.baseEP hLUC P.isBranched P.isCompact
    P.isOrientation P.loc η s hs' hinj hcov'
  change A.baseEP.pointBranchedIntegralEff hLUC P.isBranched P.isCompact P.isOrientation P.loc η =
    _
  rw [e, P.count_eq_sum η s hs hinj hcov, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x hx => by rw [hr x hx]

end General

/-! ### The classical case -/

variable {G : Type} [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  {n : ℕ} [DistribMulAction G (Fin n → ℝ)] [SMulCommClass G ℝ (Fin n → ℝ)]
  (σ : G →* ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) {φ : (Fin n → ℝ) → (Fin n → ℝ)}

variable (G) in
/-- **In `G ⋉ ℝⁿ`, `♯G_x/♯G_x^eff = ♯K`** at every point. -/
theorem card_isotropy_div_card_effIsotropy (x : Fin n → ℝ) :
    (Nat.card ((XG G n).Isotropy x) : ℝ) / (Nat.card ((XG G n).EffIsotropy x) : ℝ) =
      Nat.card (baseKernel G n) := by
  have h := card_effIsotropy G x
  rw [← card_isotropy G x] at h
  have hpos : (Nat.card ((XG G n).EffIsotropy x) : ℝ) ≠ 0 := by
    have : Finite ((XG G n).Isotropy x) :=
      Finite.of_equiv _ (isotropyEquivStabilizer (isScSmoothMap_smul (G := G)) x).symm.toEquiv
    have : Finite ((XG G n).EffIsotropy x) := Finite.of_surjective _ QuotientGroup.mk_surjective
    exact_mod_cast Nat.card_pos.ne'
  rw [div_eq_iff hpos, ← h]
  push_cast
  ring

/-- **A fibre action nontrivial on `K` leaves no solutions at a regular value**: if some `k ∈ K`
has `σ k ≠ 1`, then `φ = σ k ∘ φ`, so the image of every `Dφ(x)` lies in the fixed vectors of
`σ k`, and a regular value `c` has `φ⁻¹(c) = ∅`.  Both counts are then `0`. -/
theorem preimage_eq_empty_of_ne_one (hφ : Differentiable ℝ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) {c : Fin n → ℝ}
    (hc : ∀ x, φ x = c → Surjective (fderiv ℝ φ x)) {k : G} (hk : k ∈ baseKernel G n)
    (hσ : σ k ≠ 1) : φ ⁻¹' {c} = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx => hσ ?_
  have hφk : φ = fun y => σ k (φ y) := funext fun y => by
    conv_lhs => rw [← hk y]
    exact heq k y
  have hD : fderiv ℝ φ x = (σ k).comp (fderiv ℝ φ x) := by
    conv_lhs => rw [hφk]
    exact ((σ k).hasFDerivAt.comp x (hφ x).hasFDerivAt).fderiv
  ext1 w
  obtain ⟨v, rfl⟩ := hc x hx w
  exact (congrArg (fun L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => L v) hD).symm

set_option maxHeartbeats 1600000 in
-- the model of the orientation is unfolded to `AG σ`
/-- **The effective count of `λ = tG σ c` is `♯K` times the classical count** (Definition 9.5.6
(2), 2021 p. 439, `n = 0`): a perturbed solution set `Q` with `Q.t = tG σ c` and the canonical
orientation has `Q.countEff 1 = ♯K · (1/♯G) ∑_{φ(x) = c} sign det Dφ(x)`. -/
theorem countEff_tG_eq (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    (hprop : ∀ K, IsCompact K → IsCompact (φ ⁻¹' K)) {c : Fin n → ℝ}
    (hc : ∀ x, φ x = c → Surjective (fderiv ℝ φ x))
    {Q : PointOrientedPerturbation (clFredholmSection σ hφ heq).1} (ht : Q.t = tG σ c)
    (hcan : IsCanonicalPointSolutionSet (clOrientationRep σ hφ heq hdet) Q) :
    Q.countEff (clOne σ) = (Nat.card (baseKernel G n) : ℝ) * classicalCount G φ c := by
  classical
  rw [← count_tG_eq_classicalCount σ hφ heq hdet hprop hc ht hcan]
  obtain ⟨P, hP, rfl⟩ := hcan
  have hΛ : P.Λ = ΛG σ c := by
    have h1 := congrArg ScPlusMultisection.toFun ht
    funext w
    have ca := (ofFunctor (clStructure σ) rfl P.Λ P.isScPlusMultisection).comm w
    have cb := (ofFunctor (clStructure σ) rfl (ΛG σ c) (isScPlusMultisection_ΛG σ c)).comm w
    exact ca.symm.trans ((congrFun h1 _).trans cb)
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
  refine (countEff_solutionPointSuborbifold (c := clBundle σ) (clOrientationRep σ hφ heq hdet).a
    P (clOne σ)).trans ?_
  refine ((countEff_eq_mul _ P _ s' hpos hinj hcov _
    fun x _ => card_isotropy_div_card_effIsotropy G x)).trans ?_
  exact congrArg (_ * ·) (count_solutionPointSuborbifold (c := clBundle σ)
    (clOrientationRep σ hφ heq hdet).a P (clOne σ)).symm

/-- **Theorem 16.6.6 (2021 p. 739, index `0`) for a proper equivariant map of `ℝⁿ`, for an action
that need not be faithful: the count and the effective count.**  Let `G` act linearly on `ℝⁿ`
with kernel `K`, `σ` be a fibre action with `det ρ(g) · det σ(g) > 0`, `φ` a proper equivariant
`C^∞` map and `c` a regular value of `φ` with `gNorm σ c ≤ 1`.  Then an admissible perturbed
solution set with the canonical orientation exists, and every such `Q` has
`Q.count 1 = (1/♯G) · ∑_{x ∈ φ⁻¹(c)} sign det Dφ(x)` and
`Q.countEff 1 = (♯K/♯G) · ∑_{x ∈ φ⁻¹(c)} sign det Dφ(x)`. -/
theorem count_countEff_eq_classicalCount
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hprop : ∀ K, IsCompact K → IsCompact (φ ⁻¹' K)) {c : Fin n → ℝ}
    (hc : ∀ x, φ x = c → Surjective (fderiv ℝ φ x)) (hc1 : gNorm σ c ≤ 1) :
    (∃ Q : PointOrientedPerturbation (clFredholmSection σ hφ heq).1, Q.t = tG σ c ∧
      Q.IsAdmissible (nG σ) (univ : Set (AG σ).X.OrbitSpace) ∧
      IsCanonicalPointSolutionSet (clOrientationRep σ hφ heq hdet) Q) ∧
    ∀ Q : PointOrientedPerturbation (clFredholmSection σ hφ heq).1,
      Q.IsAdmissible (nG σ) (univ : Set (AG σ).X.OrbitSpace) →
      IsCanonicalPointSolutionSet (clOrientationRep σ hφ heq hdet) Q →
      Q.count (clOne σ) = classicalCount G φ c ∧
        Q.countEff (clOne σ) = (Nat.card (baseKernel G n) : ℝ) * classicalCount G φ c := by
  obtain ⟨-, hex, hall⟩ := count_eq_classicalCount σ hdet hφ heq hprop hc hc1
  obtain ⟨Q₁, ht₁, a₁, c₁⟩ := hex
  refine ⟨⟨Q₁, ht₁, a₁, c₁⟩, fun Q a hcan => ⟨hall Q a hcan, ?_⟩⟩
  exact (theorem_16_6_6_index_zero_count_eq_unconditional (clBundle_boundary_eq_empty σ)
    (isAuxNorm_nG σ) isOpen_univ (controlsCompactness_nG hφ heq hprop)
    (canonicalGermInput_clOrientationRep σ hφ heq hdet) a hcan a₁ c₁ (clOne σ)
    (d_clOne σ)).2.trans (countEff_tG_eq σ hφ heq hdet hprop hc ht₁ c₁)

end Polyfold.Examples.Classical.NonEffective
