import GWMemoir.FredholmGerm
import Polyfold.Chapter1.ScFredholmCriterion
import Polyfold.Chapter4.LocalStrongBundle

/-!
# Linear local models: Propositions 4.7, 4.23, 4.25 for an sc-Fredholm operator

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §§4.2–4.5 (pp. 101–122),
Propositions 4.7 (p. 102), 4.8 (p. 104), 4.23 (p. 118), 4.25 (p. 121), as stated in
`GWMemoir.FilledSection`, for a local model whose section is an sc-operator `T : E → F`.

## The memoir, paraphrased

In the coordinates of a good uniformizer the Cauchy–Riemann section is a map `f : O → F` from
an open set of the section space; Proposition 4.7 says it is sc-smooth and regularizing,
Proposition 4.23 that its linearizations are sc-Fredholm of constant index, `C¹` in the
`η`-direction and have a compactness property, Proposition 4.25 that the `η`-derivative varies
little in `η`.  Together they give the sc-Fredholm property (Proposition 4.8, Theorem 1.11).

## What is formalized

For an sc-operator `T : E → F` and an open `U ∋ 0`:

* `scDeriv_scOperator`, `levelDeriv_scOperator`, `derivOpAt_scOperator`: the sc-derivative of
  `T₀` is `T₀` at every point, `T_m` on level `m` (the book's `scDeriv_eq_of_hasFDerivAt`).
* `prop_4_7_scOperator` (`T` regularizing), `prop_4_23_scOperator` (`T` sc-Fredholm; `A = 0`,
  `H = E`), `prop_4_25_scOperator` (no hypothesis), `prop_4_8_scOperator`.
* `exists_tendsto_subseq_of_isFredholm`: for a Fredholm operator between Banach spaces, a
  bounded sequence with convergent image has a convergent subsequence; with the compact
  inclusion `F_{m+1} → F_m` this is bullet (3) of Proposition 4.23 on every level.
* **`isScFredholmGerm2021_scOperator`**: in the local strong bundle `E₀ ◁ F → E₀` of the book
  (`Polyfold.LocalBundle`, 2021 §4.1), the section `x ↦ (x, T₀ x)` is an sc-Fredholm germ at `0`
  (Definition 3.1.11), through `isScFredholmGerm2021_of_prop_4_23`.

The instance at a constant map from the three-pointed sphere is `GWMemoir.LinearModelFredholm`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace GWMemoir

open Polyfold

variable {E F : ScBanach}

/-- An open subset of `E₀` is relatively open in the partial quadrant `C = E₀`. -/
theorem relOpen_of_isOpen {U : Set (E 0)} (hU : IsOpen U) : IsRelOpenInQuadrant E univ U :=
  ⟨isPartialQuadrant_univ _, U, hU, (inter_univ _).symm⟩

section Abstract

variable (T : ScOperator E F) {U : Set (E 0)}

/-- The sc-derivative of an sc-operator is the operator itself, at every point of `U₁`. -/
theorem scDeriv_scOperator (hU : IsOpen U) {z : E 1} (hz : z ∈ E.lvlSet U 1) :
    scDeriv U (T 0) z = T 0 :=
  scDeriv_eq_of_hasFDerivAt (relOpen_of_isOpen hU)
    (T.isScSmooth (relOpen_of_isOpen hU).isScDomain).isSc1 hz (T 0).hasFDerivAt

/-- On level `m` the derivative of an sc-operator is its level map `T_m`. -/
theorem levelDeriv_scOperator (hU : IsOpen U) {m : ℕ} {x : E (m + 1)}
    (hx : x ∈ E.lvlSet U (m + 1)) : levelDeriv (scDeriv U (T 0)) m x = T m := by
  have hD : scDeriv U (T 0) (E.shift.toBase m x) = T 0 :=
    scDeriv_scOperator T hU (E.mem_lvlSet_shift_toBase.2 hx)
  have h : ∃ S : E m →L[ℝ] F m, ∀ v, F.toBase m (S v) =
      scDeriv U (T 0) (E.shift.toBase m x) (E.toBase m v) :=
    ⟨T m, fun v => by rw [hD, T.toBase_comm]⟩
  ext v
  apply F.toBase_injective m
  rw [toBase_levelDeriv h, hD, T.toBase_comm]

/-- The linearization of `T₀` at a smooth point, as an sc-operator, is `T`. -/
theorem derivOpAt_scOperator (hU : IsOpen U) (hf : IsScSmooth U (T 0)) {x : E 1}
    (hx : x ∈ E.lvlSet U 1) (hs : x ∈ E.smoothLvl 1) : derivOpAt hf hx hs = T :=
  ScOperator.ext_base (by rw [derivOpAt_zero, scDeriv_scOperator T hU hx])

/-- **Proposition 4.7** for a regularizing sc-operator. -/
theorem prop_4_7_scOperator (hU : IsOpen U) (hreg : T.IsRegularizing) : Prop_4_7 U (T 0) :=
  ⟨T.isScSmooth (relOpen_of_isOpen hU).isScDomain, fun m _ _ hx => hreg (m + 1) _ hx⟩

/-- A Fredholm operator between Banach spaces: a bounded sequence whose image converges has a
convergent subsequence (open mapping theorem on the closed range, compactness of the bounded
part of the finite-dimensional kernel). -/
theorem exists_tendsto_subseq_of_isFredholm {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y] {S : X →L[ℝ] Y} (hS : S.IsFredholm) {h : ℕ → X}
    (hb : ∃ M, ∀ j, ‖h j‖ ≤ M) {c : Y} (hc : Tendsto (fun j => S (h j)) atTop (𝓝 c)) :
    ∃ (h₀ : X) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (h ∘ φ) atTop (𝓝 h₀) := by
  obtain ⟨M, hM⟩ := hb
  have hcl := hS.isClosed_range
  have : CompleteSpace S.range := hcl.completeSpace_coe
  have := hS.finite_ker
  set S' : X →L[ℝ] S.range := S.codRestrict S.range fun x => LinearMap.mem_range_self _ x
  have hsurj : Surjective S' := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  have hcr : c ∈ S.range :=
    hcl.mem_of_tendsto hc (Eventually.of_forall fun j => LinearMap.mem_range_self _ (h j))
  obtain ⟨C, hC, hpre⟩ := S'.exists_preimage_norm_le hsurj
  obtain ⟨x₀, hx₀⟩ := hcr
  choose g hg hgn using fun j => hpre (⟨S (h j) - c, S.range.sub_mem
    (LinearMap.mem_range_self _ (h j)) ⟨x₀, hx₀⟩⟩ : S.range)
  have hg0 : Tendsto g atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun j => hgn j) ?_
    have : Tendsto (fun j => ‖S (h j) - c‖) atTop (𝓝 0) := by
      have := (hc.sub_const c).norm
      simpa using this
    simpa using this.const_mul C
  -- `k j = h j - x₀ - g j` lies in the kernel and is bounded
  have hk : ∀ j, h j - x₀ - g j ∈ S.ker := fun j => by
    have e := congrArg Subtype.val (hg j)
    change S (g j) = S (h j) - c at e
    have hx₀' : S x₀ = c := hx₀
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, map_sub, e, hx₀']
    abel
  obtain ⟨Mg, hMg⟩ : ∃ Mg, ∀ j, ‖g j‖ ≤ Mg := by
    obtain ⟨Mg, hMg⟩ := hg0.norm.bddAbove_range
    exact ⟨Mg, fun j => hMg ⟨j, rfl⟩⟩
  let k : ℕ → S.ker := fun j => ⟨h j - x₀ - g j, hk j⟩
  have hkb : ∀ j, k j ∈ Metric.closedBall (0 : S.ker) (M + ‖x₀‖ + Mg) := fun j => by
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖h j - x₀ - g j‖ ≤ _
    calc ‖h j - x₀ - g j‖ ≤ ‖h j - x₀‖ + ‖g j‖ := norm_sub_le _ _
      _ ≤ ‖h j‖ + ‖x₀‖ + ‖g j‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ M + ‖x₀‖ + Mg := by gcongr <;> simp_all
  obtain ⟨k₀, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : S.ker) _).tendsto_subseq hkb
  refine ⟨(k₀ : X) + x₀, φ, hφ, ?_⟩
  have e : h ∘ φ = fun j => ((k (φ j) : S.ker) : X) + x₀ + g (φ j) := by
    funext j; simp only [k, Function.comp_apply]; abel
  rw [e]
  have := ((continuous_subtype_val.tendsto _).comp hlim).add_const x₀ |>.add
    (hg0.comp hφ.tendsto_atTop)
  simpa using this

/-- **Proposition 4.23** for an sc-Fredholm operator, with `A = 0` and `H = E`: (1) the
linearization is `T` at every point; (2) `η ↦ T_m(a + η)` is affine; (3) `T_m h_j = y_j + z_j`
with `z_j` bounded in `F_{m+1}` has a convergent subsequence in `F_m` (compact inclusion), so
`h_j` has one (`T_m` Fredholm). -/
theorem prop_4_23_scOperator (hU : IsOpen U) (hT : IsScFredholm T) :
    Prop_4_23 U (T 0) ⊥ ⊤ (T.isScSmooth (relOpen_of_isOpen hU).isScDomain) := by
  refine ⟨⟨fun x hx hs => ?_, fun x hx hs x' hx' hs' => ?_⟩,
    fun m => ⟨1, one_pos, fun a _ _ => ?_⟩, ?_⟩
  · rw [derivOpAt_scOperator T hU]; exact hT
  · rw [derivOpAt_scOperator T hU, derivOpAt_scOperator T hU]
  · have e : (fun η : E.levelSub ⊤ m => levelMap (T 0) m (a + η)) =
        fun η : E.levelSub ⊤ m => T m (a + η) := funext fun η => T.levelMap_eq m _
    rw [e]
    exact ((T m).contDiff.comp (contDiff_const.add (E.levelSub ⊤ m).subtypeL.contDiff)).contDiffOn
  · intro K _ _ _ m p p₀ h y z hp _ _ _ hhb hD hy hz
    obtain ⟨s⟩ := hT
    have hD' : ∀ j, T m (h j) = y j + F.incl m (z j) := fun j => by
      rw [← levelDeriv_scOperator T hU (hp j).2]; exact hD j
    obtain ⟨M, hM⟩ := hz
    obtain ⟨Kc, hKc, hsub⟩ :=
      (F.incl_isCompactOperator m).image_closedBall_subset_compact (f := (F.incl m).toLinearMap) M
    have hmem : ∀ j, F.incl m (z j) ∈ Kc := fun j =>
      hsub ⟨z j, by rw [Metric.mem_closedBall, dist_zero_right]; exact hM j, rfl⟩
    obtain ⟨c, -, φ, hφ, hlim⟩ := hKc.tendsto_subseq hmem
    have hc : Tendsto (fun j => T m ((h ∘ φ) j)) atTop (𝓝 (0 + c)) := by
      simp only [Function.comp_apply, hD']
      exact (hy.comp hφ.tendsto_atTop).add hlim
    obtain ⟨Mh, hMh⟩ := hhb
    obtain ⟨h₀, ψ, hψ, hlim'⟩ :=
      exists_tendsto_subseq_of_isFredholm (s.isFredholm m) ⟨Mh, fun j => hMh (φ j)⟩ hc
    exact ⟨h₀, φ ∘ ψ, hφ.comp hψ, hlim'⟩

/-- **Proposition 4.25** for an sc-operator: the derivative does not depend on the point. -/
theorem prop_4_25_scOperator (hU : IsOpen U) (A H : Submodule ℝ (E 0)) :
    Prop_4_25 U (T 0) A H := by
  intro m lam hlam
  refine ⟨1, one_pos, fun a _ _ ha η _ _ haη h _ => ?_⟩
  rw [levelDeriv_scOperator T hU ha, levelDeriv_scOperator T hU haη, sub_self, norm_zero]
  positivity

/-- **Proposition 4.8** for an sc-Fredholm operator, from Propositions 4.7, 4.23, 4.25 through
`memoir_proposition_4_8_of_4_23`, with `B = ker T` and its sc-complement. -/
theorem prop_4_8_scOperator (hU : IsOpen U) (h0 : (0 : E 0) ∈ U) (hT : IsScFredholm T) :
    Prop_4_8 U (T 0) := by
  obtain ⟨s⟩ := id hT
  have := s.finite_K
  have h01 : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  exact memoir_proposition_4_8_of_4_23 hU h0 (prop_4_7_scOperator T hU hT.isRegularizing)
    (prop_4_23_scOperator T hU hT) (prop_4_25_scOperator T hU ⊥ ⊤) E.isScSplitting_bot_top
    s.splitE bot_le le_top (by rw [scDeriv_scOperator T hU h01, s.ker_eq])

end Abstract

section LocalBundle

/-- The base point `0` of the local model `E₀ ◁ F → E₀`. -/
abbrev lmPt : (univ : Set (E 0)) := ⟨0, mem_univ _⟩

/-- In the chart of `E₀ ◁ F`, the principal part of `x ↦ (x, k(x))` is `k`. -/
theorem principal_chart_sec (k : E 0 → F 0) :
    (LocalBundle.chart (F := F) (relOpen_of_isOpen (E := E) isOpen_univ) (lmPt (E := E))).principal
      (LocalBundle.sec k) = k := by
  funext v
  have h1 : ((LocalBundle.baseChart (relOpen_of_isOpen (E := E) isOpen_univ)
      (lmPt (E := E))).toPartialEquiv.symm v : E 0) = v :=
    (LocalBundle.baseChart _ _).toPartialEquiv.right_inv (mem_univ v)
  change k ((LocalBundle.baseChart (relOpen_of_isOpen (E := E) isOpen_univ)
      (lmPt (E := E))).toPartialEquiv.symm v : E 0) = k v
  rw [h1]

variable (T : ScOperator E F)

/-- **The section `x ↦ (x, T₀ x)` of `E₀ ◁ F → E₀` is an sc-Fredholm germ at `0`** (book
Definition 3.1.11, 2021 p. 96) for an sc-Fredholm `T`, from Propositions 4.7, 4.23 and 4.25
(`isScFredholmGerm2021_of_prop_4_23`); the strong bundle retraction is the identity, so the
principal part fills itself. -/
theorem isScFredholmGerm2021_scOperator (hT : IsScFredholm T) :
    (LocalBundle.bundle F (relOpen_of_isOpen (E := E) isOpen_univ) lmPt).IsScFredholmGerm2021
      (LocalBundle.sec (T 0)) lmPt := by
  have hU := relOpen_of_isOpen (E := E) isOpen_univ
  have hp := principal_chart_sec (F := F) (T 0)
  obtain ⟨s⟩ := id hT
  have := s.finite_K
  have h01 : (0 : E 1) ∈ E.lvlSet univ 1 := mem_univ _
  have hfill : IsFilling2021 (LocalBundle.chart (F := F) hU lmPt).relOpen
      (LocalBundle.chart (F := F) hU lmPt).isRetraction (mem_univ 0)
      ((LocalBundle.chart (F := F) hU lmPt).principal (LocalBundle.sec (T 0))) (T 0) := by
    rw [hp]
    exact isFilling2021_of_R_eq_self _ _ (fun _ => rfl) _ (T.isScSmooth hU.isScDomain)
  have hbot : FiniteDimensional ℝ
      (⊥ : Submodule ℝ ((LocalBundle.chart (F := F) hU lmPt).φ.model.E 0)) := by
    change FiniteDimensional ℝ (⊥ : Submodule ℝ (E 0)); infer_instance
  have hK : FiniteDimensional ℝ
      ↥(show Submodule ℝ ((LocalBundle.chart (F := F) hU lmPt).φ.model.E 0) from s.K) := this
  have hker : LinearMap.ker (scDeriv univ (T 0) 0 : E 0 →ₗ[ℝ] F 0) ≤ s.K := by
    rw [scDeriv_scOperator T isOpen_univ h01, s.ker_eq]
  exact isScFredholmGerm2021_of_prop_4_23 (A := ⊥) (H := ⊤)
    (B' := show Submodule ℝ ((LocalBundle.chart (F := F) hU lmPt).φ.model.E 0) from s.K)
    (X' := s.X)
    (LocalBundle.isChart_chart hU lmPt)
    ((LocalBundle.mem_smoothSet_iff hU lmPt).2 (zero_mem _)) (mem_univ _) rfl (mem_univ _)
    isOpen_univ hfill (prop_4_7_scOperator T isOpen_univ hT.isRegularizing)
    (prop_4_23_scOperator T isOpen_univ hT) (prop_4_25_scOperator T isOpen_univ ⊥ ⊤)
    E.isScSplitting_bot_top s.splitE bot_le le_top hker

end LocalBundle

end GWMemoir
