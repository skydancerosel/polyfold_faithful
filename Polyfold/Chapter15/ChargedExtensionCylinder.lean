import Polyfold.Chapter15.CylinderGlue
import Polyfold.Chapter15.CutoffFunctor
import Polyfold.Chapter14.BoundaryExtensionTheorem
import Polyfold.Chapter15.ChargedExtensionFibres

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, pp. 694–700:
**Theorem 15.3.9** (2017: Theorem 15.5) for boundary data that charge every boundary fibre, and
**Corollary 15.3.10 (3)** (2017: Corollary 15.1 (3)) on the cylinder `[0, 1] × X` from it.

# Theorem 15.3.9 for charged boundary data, and the cylinder

## What is formalized (namespace `Polyfold.SBLocalization`)

* The charged form of Theorem 15.3.9 is `theorem_15_3_9_charged_statement`
  (`ChargedExtensionFibres`: the uncharged statement with tame strong bundle charts and
  `ChargesBoundary Λ` added), proved there from the relative step (`theorem_15_3_9_charged_hyp`);
  with tame strong bundle charts it gives the uncharged statement
  (`theorem_15_3_9_statement_of_charged`).
* `exists_ne_zero_of_isScPlusMultisection`: an sc⁺-multisection charges every fibre;
  **`chargesBoundary_cubeGlue`**: the glued data `cubeGlue Λ⁰ Λ¹` charge `∂([0, 1] × X)`.
* **`corollary_15_3_10_3_charged`**: Corollary 15.3.10 (3) for two structurable regular
  perturbations from the charged statement on the cylinder (`corollary_15_3_10_3_glue_hyp`
  with `h159` replaced by its charged form and tame strong bundle charts on the cylinder).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}}

/-! ### The zero function -/

/-- The pointwise norm of the function `Λ ≡ 0` is `0` (`supp(Λ)(x) = ∅`). -/
theorem pointwiseNorm_zeroFun_w2 (N : A.B.One → ℝ) (x : A.Obj) :
    pointwiseNorm N (fun _ : A.W => (0 : ℚ≥0)) x = 0 := by
  have : suppAt (fun _ : A.W => (0 : ℚ≥0)) x = ∅ :=
    eq_empty_iff_forall_notMem.2 fun w hw => lt_irrefl _ hw.2
  rw [pointwiseNorm, this, image_empty, Real.sSup_empty]

/-! ### The glued data charge `∂([0, 1] × X)` -/

/-- **An sc⁺-multisection charges every fibre**: some `w` over `x` has `Λ(w) ≠ 0` (the weights of
a local representation sum to `1`; the same argument at every point). -/
theorem exists_ne_zero_of_isScPlusMultisection {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (x : A.Obj) : ∃ w, A.P w = x ∧ Λ w ≠ 0 := by
  classical
  obtain ⟨R, k, s, σ, hpos, hsc, hsum, hrep⟩ := hΛ.2 x
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at hsum
    · exact hk
  set i : Fin k := ⟨0, hk⟩
  have hP : A.P (s i x) = x := (hsc i).1 x R.mem_U
  refine ⟨s i x, hP, ?_⟩
  rw [hrep _ (by rw [hP]; exact R.mem_U)]
  refine ne_of_gt (lt_of_lt_of_le (hpos i) ?_)
  have := Finset.single_le_sum (f := fun j => if s i x = s j (A.P (s i x)) then σ j else 0)
    (fun j _ => by positivity) (Finset.mem_univ i)
  simpa [hP] using this

/-- **The glued data charge `∂([0, 1] × X)`**: if `Λ⁰`, `Λ¹` are sc⁺-multisections and
`∂([0, 1] × X)` lies over `t ∈ {0, 1}`, then `cubeGlue Λ⁰ Λ¹` charges every boundary fibre. -/
theorem chargesBoundary_cubeGlue {Λ₀ Λ₁ : A.W → ℚ≥0} (hΛ₀ : IsScPlusMultisection A Λ₀)
    (hΛ₁ : IsScPlusMultisection A Λ₁)
    (hbd : ∀ z ∈ (A.cubeSEP 1).X.PObj.boundary, (z.1 0 : ℝ) = 0 ∨ (z.1 0 : ℝ) = 1) :
    ChargesBoundary (A := A.cubeSEP 1) (cubeGlue Λ₀ Λ₁) := by
  intro z hz
  rcases hbd z hz with h | h
  · obtain ⟨v, hv, hne⟩ := exists_ne_zero_of_isScPlusMultisection hΛ₀ z.2
    refine ⟨⟨(z, v), hv⟩, rfl, ?_⟩
    rw [cubeGlue_of_zero (w := ⟨(z, v), hv⟩) h]
    exact hne
  · obtain ⟨v, hv, hne⟩ := exists_ne_zero_of_isScPlusMultisection hΛ₁ z.2
    refine ⟨⟨(z, v), hv⟩, rfl, ?_⟩
    rw [cubeGlue_of_one (w := ⟨(z, v), hv⟩) h]
    exact hne

/-! ### Corollary 15.3.10 (3) from the charged statement -/

/-- **Corollary 15.3.10 (3), p. 699, for two structurable regular perturbations, from the
charged Theorem 15.3.9 on `[0, 1] × X`**: `corollary_15_3_10_3_glue_hyp` with
`theorem_15_3_9_statement (A.cubeSEP 1)` replaced by the charged form and tame strong bundle
charts on the cylinder (`hBC`); the charge of the glued data is `chargesBoundary_cubeGlue`.
Left open: structurability and the face condition of the glued data and partitions
of unity of the cylinder. -/
theorem corollary_15_3_10_3_charged
    (h159 : theorem_15_3_9_charged_statement (A.cubeSEP 1))
    (hBC : ∀ x : (A.cubeSEP 1).Obj,
      ∃ c : StrongBundleChart (A.cubeSEP 1).X.PObj (A.cubeSEP 1).P,
        (A.cubeSEP 1).B.IsTameChart c ∧ x ∈ c.φ.source)
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hS : A.E.HasCompactSolutionSetEp f) {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    {Λ₀ Λ₁ : A.W → ℚ≥0} (hr₀ : IsRegularPerturbation A f N₀ U₀ Λ₀)
    (hr₁ : IsRegularPerturbation A f N₁ U₁ Λ₁)
    (hbs : IsBoundaryStructurable (A.cubeSEP 1) (cubeGlue Λ₀ Λ₁))
    (hbonto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁)) :
    ∃ Λ' : (A.cubeSEP 1).W → ℚ≥0,
      IsRegularPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1)
        (interpAuxNorm A N₀ N₁) (interpSet A U₀ U₁) Λ' ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2) ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2) ∧
      (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) ∧
      (A.cubeSEP 1).X.IsCompactBranched
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hXC : (A.cubeSEP 1).X.IsTame := A.X.isTame_cubeProd 1 hX
  have hbd : ∀ z ∈ (A.cubeSEP 1).X.PObj.boundary, (z.1 0 : ℝ) = 0 ∨ (z.1 0 : ℝ) = 1 :=
    fun z hz => (mem_boundary_cubeSEP_iff hX hd z).1 hz
  have hN₀ := hr₀.1.1.isAuxNorm
  have hN₁ := hr₁.1.1.isAuxNorm
  have hcc := corollary_15_3_10_2 hf.1.1.1 hr₀.1 hr₁.1
  have hbN : ∀ z ∈ (A.cubeSEP 1).X.PObj.boundary,
      pointwiseNorm (interpAuxNorm A N₀ N₁) (cubeGlue Λ₀ Λ₁) z < 1 := by
    intro z hz
    rcases hbd z hz with h | h
    · exact (pointwiseNorm_cubeGlue_le_zero hN₀ hN₁ hr₀.2.1.1 h).trans_lt (hr₀.2.2.2.1 z.2)
    · exact (pointwiseNorm_cubeGlue_le_one hN₀ hN₁ hr₁.2.1.1 h).trans_lt (hr₁.2.2.2.1 z.2)
  obtain ⟨Λ', hΛ', hbd', hdom', hN', -, htr', hbr, hcpt⟩ :=
    h159 hXC (A.X.hasParacompactOrbitSpace_cubeProd 1 hpara) hPUC hBC _
      (isScFredholmSectionFunctor_cubeLiftEp hf hft) (isScFredholmSectionTame_cubeLiftEp hft)
      (hasCompactSolutionSetEp_cubeLiftEp hf.1.1.1 hS) _ _ hcc (cubeGlue Λ₀ Λ₁) hbs
      (chargesBoundary_cubeGlue hr₀.2.1.1 hr₁.2.1.1 hbd)
      (boundaryDomSupp_cubeGlue_subset hr₀.2.2.1 hr₁.2.2.1 hbd) (fun z hz => (hbN z hz).le)
      (fun _ => 1) continuous_const (fun _ => rfl) (fun _ => ⟨one_pos, le_rfl⟩) hbN hbonto
  have hbdry : ∀ w : (A.cubeSEP 1).W, ((cubeVal w).1.1 0 : ℝ) = 0 ∨ ((cubeVal w).1.1 0 : ℝ) = 1 →
      (A.cubeSEP 1).P w ∈ (A.cubeSEP 1).X.PObj.boundary := fun w hw =>
    (mem_boundary_cubeSEP_iff hX hd _).2 hw
  exact ⟨Λ', ⟨hcc, hΛ', hdom', hN', htr'⟩,
    fun w hw => (hbd' w (hbdry w (Or.inl hw))).trans (cubeGlue_of_zero hw),
    fun w hw => (hbd' w (hbdry w (Or.inr hw))).trans (cubeGlue_of_one hw), hbr, hcpt⟩

end SBLocalization

end Polyfold
