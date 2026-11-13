import Polyfold.Chapter14.BoundaryExtensionTheorem
import Polyfold.Chapter3.NonVacuityCorner
import Polyfold.Chapter8.NonVacuityBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 14,
**Theorem 14.1.9** (∂-Extension Theorem, p. 646; 2017: Theorem 14.2): **a witness with
boundary** for the hypotheses of A6's `theorem_14_1_9_charged_a6`.

# The trivial bundle over a half-space as a strong bundle over an ep-groupoid

## Why

The only earlier witness for the standing hypothesis `hB` (a tame strong bundle chart around
every object) was LX's `proposition_14_1_4_hypotheses_rn`, over `ℝⁿ`, where `∂X = ∅`.  There the
∂-Extension Theorem says nothing.  Here the base is the half-space `H = [0, ∞) × ℝᵐ`, whose
boundary `{0} × ℝᵐ` is non-empty, and the fibre is `ℝᵏ` (non-zero for `k ≥ 1`).

## What is formalized (namespace `Polyfold.HalfSpaceBundle`)

* `halfSEP m k`: Part I's trivial strong bundle `H × ℝᵏ → H` (`HalfSpaceBundle.bundle`,
  `Chapter3/NonVacuityCorner`) over the trivial ep-groupoid of `H`, as an object of `SEP`.
* `isTame_halfSEP` (the M-polyfold `H` is the tame quadrant `[0, ∞) ⊕ ℝᵐ`),
  `hasParacompactOrbitSpace_halfSEP`, `admitsScPartitionsOfUnity_halfSEP` (Theorem 5.5.10 with the
  one chart of `H`, whose finite-dimensional model has the approximation property, Proposition
  5.5.11), `hB_halfSEP` (Part I's re-centred charts `chartAt x` are tame strong bundle charts).
* `zero_mem_boundary_halfSEP`: the corner `0` lies in `∂H` (`d_H(0) = 1`, Corollary 2.4.13);
  `mem_boundary_halfSEP_iff`: `∂H = {x | x₁ = 0}`.
* `nontrivial_fibre_halfSEP`: for `k ≥ 1` every fibre is a non-zero vector space.
* **`theorem_14_1_9_charged_hypotheses_halfSEP`**: all hypotheses of
  `theorem_14_1_9_charged_a6` hold on `halfSEP m k`, with `∂X ≠ ∅`, for `Λ` the zero
  multisection over `∂X` (structurable, charging every boundary fibre), an auxiliary norm
  (Theorem 12.2.2), `Ũ = X` and `f ≡ 1`.  **`theorem_14_1_9_halfSEP`**: hence the conclusion.

The non-zero `Λ` with non-empty `dom-supp` is in `HalfSpaceConstSection.lean`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

namespace HalfSpaceBundle

open SBLocalization StrongBundle EpGroupoid

variable (m k : ℕ)

/-- `𝐗 ₛ×_P W` for the half-space bundle over the trivial ep-groupoid of `H` is paracompact. -/
instance instParacompactPullbackW1 :
    ParacompactSpace (pullbackSpace (proj m k) (EpGroupoid.trivial (basePoly m)).src) :=
  (bundle m k).paracompactSpace_pullback (basePoly m) _

/-- **The half-space bundle `H × ℝᵏ → H` over the trivial ep-groupoid of `H`** (Definition 8.3.1).
-/
def epBundleW1 : EpStrongBundle (EpGroupoid.trivial (basePoly m)) (bundle m k) :=
  EpStrongBundle.trivial (bundle m k)

/-- `H × ℝᵏ → H = [0, ∞) × ℝᵐ` as an object of `SEP` (Definition 10.4.11). -/
def halfSEP : SEP.{0} :=
  ⟨_, _, EpGroupoid.trivial (basePoly m), _, proj m k, bundle m k, epBundleW1 m k⟩

theorem halfSEP_PObj : (halfSEP m k).X.PObj = basePoly m := rfl

/-- `H` is a tame M-polyfold: it is the quadrant M-polyfold `[0, ∞) ⊕ ℝᵐ`. -/
theorem isTame_halfSEP : (halfSEP m k).X.IsTame :=
  MPolyfold.quadrantPolyfold_isTame 1 (rnSc m)

/-- The orbit space of the trivial ep-groupoid is `H`, which is paracompact. -/
theorem hasParacompactOrbitSpace_halfSEP : (halfSEP m k).X.HasParacompactOrbitSpace :=
  EpGroupoid.hasParacompactOrbitSpace_trivial (basePoly m)

/-- **`H` admits sc-smooth partitions of unity** (Theorem 5.5.10: its one chart has the
finite-dimensional model `ℝ ⊕ ℝᵐ`, which has the approximation property by Proposition 5.5.11). -/
theorem admitsScPartitionsOfUnity_halfSEP :
    (halfSEP m k).X.PObj.AdmitsScPartitionsOfUnity := by
  change (basePoly m).AdmitsScPartitionsOfUnity
  refine theorem_5_5_10.2 ⟨{baseChart m}, ?_, fun x => ⟨baseChart m, mem_singleton _, mem_univ x⟩,
    ?_⟩
  · rintro _ rfl
    exact (basePoly m).isChart_of_mem (mem_singleton _)
  · rintro _ rfl
    have : FiniteDimensional ℝ ((baseChart m).model.E 0) := by
      change FiniteDimensional ℝ ((Fin 1 → ℝ) × (Fin m → ℝ))
      infer_instance
    exact proposition_5_5_11 _ (admitsContDiffPartitionsOfUnity_of_finiteDimensional _)

/-- **The standing hypothesis `hB`**: every object lies in a tame strong bundle chart (the
re-centred chart `chartAt x` of Part I). -/
theorem hB_halfSEP : ∀ x : (halfSEP m k).Obj, ∃ c : StrongBundleChart (halfSEP m k).X.PObj
    (halfSEP m k).P, (halfSEP m k).B.IsTameChart c ∧ x ∈ c.φ.source := fun x =>
  ⟨chartAt (k := k) x, isTameChart_chartAt x, mem_source_chartAt x⟩

/-- **`∂X ≠ ∅`**: the corner `0` of `H` has degeneracy index `1` (Corollary 2.4.13). -/
theorem zero_mem_boundary_halfSEP :
    (⟨0, fun _ => le_rfl⟩ : (halfSEP m k).Obj) ∈ (halfSEP m k).X.PObj.boundary := by
  change 1 ≤ (MPolyfold.quadrantPolyfold 1 (rnSc m)).degIndex ⟨0, _⟩
  rw [MPolyfold.quadrantPolyfold_degIndex_zero]

/-- **`∂H = {x | x₁ = 0}`** (Corollary 2.4.13: `d_H(x) = d_C(x)` = the number of vanishing
`[0, ∞)`-coordinates). -/
theorem mem_boundary_halfSEP_iff (x : H m) :
    (show (halfSEP m k).Obj from x) ∈ (halfSEP m k).X.PObj.boundary ↔
      (x : (halfSpaceSc m) 0).1 0 = 0 := by
  change 1 ≤ (MPolyfold.quadrantPolyfold 1 (rnSc m)).degIndex x ↔ _
  rw [MPolyfold.quadrantPolyfold, corollary_2_4_13 (MPolyfold.isRelOpenInQuadrant_quadrant 1 _)
    (MPolyfold.quadrant_nonempty 1 _), degIndex_quadrant x.2]
  unfold quadrantDeg
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Finset.card_pos.1 h
    rw [Subsingleton.elim 0 i]
    exact (Finset.mem_filter.1 hi).2
  · intro h
    exact Finset.card_pos.2 ⟨0, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩

/-- **The fibres are non-zero for `k ≥ 1`**: `W_x ≅ ℝᵏ`. -/
theorem nontrivial_fibre_halfSEP [NeZero k] (x : (halfSEP m k).Obj) :
    Nontrivial ((halfSEP m k).P ⁻¹' {x}) :=
  (fibEquiv (m := m) (k := k) x).nontrivial

/-- **The hypotheses of `theorem_14_1_9_charged_a6` hold with `∂X ≠ ∅`** on the half-space bundle
`H × ℝᵏ → H`: `X` tame, `|X|` paracompact, sc-smooth partitions of unity, tame strong bundle charts
(`hB`), a non-empty boundary, the zero multisection over `∂X` structurable and charging every
boundary fibre, an auxiliary norm `N` (Theorem 12.2.2), and `Ũ = X`, `f ≡ 1` with the conditions
of the theorem. -/
theorem theorem_14_1_9_charged_hypotheses_halfSEP :
    let A := halfSEP m k
    A.X.IsTame ∧ A.X.HasParacompactOrbitSpace ∧ A.X.PObj.AdmitsScPartitionsOfUnity ∧
      (∀ x : A.Obj, ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧
        x ∈ c.φ.source) ∧
      A.X.PObj.boundary.Nonempty ∧
      IsBoundaryStructurable A (zeroMultisection A) ∧ ChargesBoundary (zeroMultisection A) ∧
      (∃ N : A.B.One → ℝ, A.E.IsAuxNorm N) ∧
      IsOpen (univ : Set A.Obj) ∧ A.X.IsSaturated univ ∧
      boundaryDomSupp (zeroMultisection A) ⊆ univ ∧
      Continuous (fun _ : A.Obj => (1 : ℝ)) ∧ (∀ _ : A.Obj, (0 : ℝ) ≤ 1) ∧
      tsupport (fun _ : A.Obj => (1 : ℝ)) ⊆ univ ∧
      ∀ N : A.B.One → ℝ, ∀ x ∈ boundaryDomSupp (zeroMultisection A),
        pointwiseNorm N (zeroMultisection A) x < 1 := by
  intro A
  have hX := isTame_halfSEP m k
  have hpara := hasParacompactOrbitSpace_halfSEP m k
  refine ⟨hX, hpara, admitsScPartitionsOfUnity_halfSEP m k, hB_halfSEP m k,
    ⟨_, zero_mem_boundary_halfSEP m k⟩, isBoundaryStructurable_zero hX hpara,
    chargesBoundary_zeroMultisection_a6, EpStrongBundle.theorem_12_2_2 A.E hpara, isOpen_univ,
    GroupoidStr.isSaturated_univ _, subset_univ _, continuous_const, fun _ => zero_le_one,
    subset_univ _, fun _ x hx => ?_⟩
  rw [boundaryDomSupp_zero] at hx
  exact absurd hx (notMem_empty x)

/-- **Theorem 14.1.9 on the half-space bundle** (`∂X ≠ ∅`): `theorem_14_1_9_charged_a6` applies
with all its hypotheses discharged, and gives a structurable `Λ'` on `H × ℝᵏ → H` with
`N(Λ') ≤ 1` which restricts to the zero multisection over `∂H = {0} × ℝᵐ`. -/
theorem theorem_14_1_9_halfSEP :
    ∃ N : (halfSEP m k).B.One → ℝ, (halfSEP m k).E.IsAuxNorm N ∧
      ∃ Λ' : (halfSEP m k).W → ℚ≥0, IsStructurable (halfSEP m k) Λ' ∧
        (∀ x, pointwiseNorm N Λ' x ≤ 1) ∧
        ∀ w, (halfSEP m k).P w ∈ (halfSEP m k).X.PObj.boundary →
          Λ' w = zeroMultisection (halfSEP m k) w := by
  obtain ⟨hX, hpara, hpu, hB, -, hΛ, hch, ⟨N, hN⟩, hUo, hUs, hsub, hf, hf0, htsupp, hlt⟩ :=
    theorem_14_1_9_charged_hypotheses_halfSEP m k
  obtain ⟨Λ', h1, h2, -, h4⟩ := theorem_14_1_9_charged_a6 hX hpara hpu hB _ hΛ hch N hN univ
    hUo hUs hsub _ hf hf0 (fun _ => rfl) htsupp (hlt N)
  exact ⟨N, hN, Λ', h1, h2, h4⟩

end HalfSpaceBundle

end Polyfold
