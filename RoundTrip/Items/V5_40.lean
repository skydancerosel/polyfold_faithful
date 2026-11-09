import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_40

/-!
Round trip for V5_40 (Theorem 5.19).  `A` is the conjunction of the types of
`Polyfold.theorem_5_3_12_param` and `Polyfold.StrongBundle.IsGoodPositionGermTame.congr_nhds`, universes
instantiated at `0`.

Neither `A → B` nor `B → A` is proved.

* `A → B` fails, for two reasons:
  1. **The misprint, kept literally by B**: B asks the germ `(f, x)` (not `(f + s, x)`) to be in
     good position at every zero `x` of `f + s`.  A gives `(f + s, x)`.  With `congr_nhds` this
     transfers to `(f, x)` only at the zeros outside `supp(s)` (where `f + s = f` near `x`); at the
     zeros inside `supp(s)` nothing relates `(f, x)` to good position (and the literal claim is
     presumably false: the blind author's example `f ≡ 0` on the Möbius bundle; not refuted here).
  2. **Bump functions**: B assumes `AdmitsBumpFunctionsWeak` (`f ≢ 0`), A `AdmitsBumpFunctions`
     (`f(x) ≠ 0`); the project has only strong ⟹ weak.
  With both removed, i.e. for `BIntendedStrong` (the blind file's `BIntended` with
  `AdmitsBumpFunctions`), the implication is proved (`A_to_BIntendedStrong`): A's generic family
  `s_λ = Σ λᵢ tᵢ` with `λ` outside a null set in a small ball gives arbitrarily small `s`
  (`N(s(x)) ≤ m|λ|`), vanishing on the open complement of `supp(s)`, which contains `∂X`; the corner
  structure comes from `IsManifoldWithCornersLoc` (`hasCornerStructure_iff_finiteDimensional`), the
  empty solution set by hand.  B's tame strong bundle hypothesis is not needed.
* `B → A` fails: B assumes a tame strong bundle (`IsTameStrongBundle`), A assumes no tameness at
  all; and B's "for every `ε` some small `s`" does not give A's generic form (a finite family
  `t₁, …, t_m` with supports disjoint from `∂X` such that `Σ λᵢ tᵢ` works for almost every small
  `λ`), nor the tameness of `S_{f+s}` in A.  A's second conjunct (`congr_nhds`, good position is a
  property of the germ) is a separate lemma that B says nothing about.
-/

/-! **Refresh 2026-11-02** (HEAD after the germ reading of Definition 3.11 and the notions built
on it).
theorem_5_3_12_param and IsGoodPositionGermTame.congr_nhds now denote the germ reading (congr_nhds lives
in Chapter3/Chapter5BridgeG.lean), as do B's IsScFredholmSectionTame and IsGoodPositionGermTame.
The obstacles (B's literal '(f, x)' misprint, weak bump functions, B's tame strong bundle) are
unrelated; A ⇒ BIntendedStrong still checks. Result unchanged.
-/

namespace RoundTrip.V5_40
open Polyfold MeasureTheory

/-- The project's statement, universes `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_5_3_12_param.{0, 0} ∧
  type_of% @Polyfold.StrongBundle.IsGoodPositionGermTame.congr_nhds.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.theorem_5_3_12_param.{0, 0}, @Polyfold.StrongBundle.IsGoodPositionGermTame.congr_nhds.{0, 0}⟩

/-- The blind file's `BIntended` (misprint corrected) with the strong reading of bump functions
(not the item; it isolates the differences). -/
def BIntendedStrong : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (N : Bd.One → ℝ),
    IsTameStrongBundle Bd → PX.AdmitsBumpFunctions →
    Bd.IsScFredholmSectionTame f → IsCompact (solSet P f) → Bd.IsAuxNorm N →
    (∀ x ∈ solSet P f, x ∈ PX.boundary → Bd.IsGoodPositionGermTame f x) →
      ∃ U : Set X, IsOpen U ∧ solSet P f ⊆ U ∧
        (∀ s ∈ Bd.allowableSections N U, IsCompact (solSet P (sectionAdd P f s))) ∧
        ∀ ε : ℝ, 0 < ε → ∃ s ∈ Bd.allowableSections N U,
          (∃ δ < ε, ∀ x, Bd.AuxLe N (s x) δ) ∧
          (∃ W : Set X, IsOpen W ∧ PX.boundary ⊆ W ∧ ∀ x ∈ W, IsZeroAt P s x) ∧
          Bd.IsTransversal (sectionAdd P f s) ∧
          (∀ x ∈ solSet P (sectionAdd P f s), Bd.IsGoodPositionGermTame (sectionAdd P f s) x) ∧
          IsCompactCornerManifold PX (solSet P (sectionAdd P f s))

theorem BIntended_to_BIntendedStrong : BIntended → BIntendedStrong :=
  fun hB _X _ _ _ PX _Y _ _ _ P _ _ Bd f N hT hbump => hB PX P Bd f N hT hbump.weak

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {Bd : StrongBundle PX P}

set_option maxHeartbeats 1600000 in
/-- The size of `s_λ = Σ λᵢ tᵢ`: `N(s_λ(x)) ≤ m |λ|` when `N(tᵢ) ≤ 1`. -/
theorem auxLe_paramSlice_zero {N : Bd.One → ℝ} (hN : Bd.IsAuxNorm N) {m : ℕ}
    {t : Fin m → X → Y} (ht : ∀ i, Bd.IsScPlusSection (t i))
    (htN : ∀ i x (hx : t i x ∈ Bd.oneSet), N (Bd.oneMk (t i x) hx) ≤ 1) (lam : Fin m → ℝ)
    (x : X) :
    Bd.AuxLe N (paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam x)
      ((m : ℝ) * ‖lam‖) := by
  classical
  have hs₀ : Bd.IsScPlusSection (fiberZero P) := StrongBundle.isScPlusSection_fiberZero
  have hsl : Bd.IsScPlusSection (paramSlice (fiberZero P) hs₀.1 t (fun i => (ht i).1) lam) :=
    isScPlusSection_paramSlice hs₀ ht lam
  refine ⟨hsl.mem_oneSet x, ?_⟩
  set w : Fin m → Bd.oneFiber x := fun i => ⟨⟨t i x, (ht i).1 x⟩, (ht i).mem_oneSet x⟩ with hw
  have hu : (⟨⟨paramSlice (fiberZero P) hs₀.1 t (fun i => (ht i).1) lam x, hsl.1 x⟩,
      hsl.mem_oneSet x⟩ : Bd.oneFiber x) = ∑ i, lam i • w i := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    apply Subtype.ext
    change paramSlice (fiberZero P) hs₀.1 t (fun i => (ht i).1) lam x = _
    unfold paramSlice
    have h1 : (⟨fiberZero P x, hs₀.1 x⟩ : P ⁻¹' {x}) = 0 := rfl
    rw [h1, zero_add]
    rfl
  have hli : ∀ i, |lam i| ≤ ‖lam‖ := fun i => by
    have := norm_le_pi_norm lam i
    rwa [Real.norm_eq_abs] at this
  have hwN : ∀ i, N (Bd.toOne (w i)) ≤ 1 := fun i => htN i x ((ht i).mem_oneSet x)
  change N (Bd.toOne (⟨⟨paramSlice (fiberZero P) hs₀.1 t (fun i => (ht i).1) lam x, hsl.1 x⟩,
      hsl.mem_oneSet x⟩ : Bd.oneFiber x)) ≤ _
  rw [hu]
  calc N (Bd.toOne (∑ i, lam i • w i))
      ≤ ∑ i, N (Bd.toOne (lam i • w i)) := hN.toOne_sum_le _ _
    _ = ∑ i, |lam i| * N (Bd.toOne (w i)) :=
        Finset.sum_congr rfl fun i _ => hN.smul (w i) (lam i)
    _ ≤ ∑ _i : Fin m, ‖lam‖ * 1 :=
        Finset.sum_le_sum fun i _ => mul_le_mul (hli i) (hwN i) (hN.nonneg _) (norm_nonneg _)
    _ = (m : ℝ) * ‖lam‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

end Glue

/-- A gives the corrected statement with the strong reading of bump functions. -/
theorem A_to_BIntendedStrong : A → BIntendedStrong := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd f N _hT hbump hf hS hN hbd
  obtain ⟨U, hUo, hSU, hcpt, m, t, ht, -, -, htN, δ, hδ, CV, hCV, hlam⟩ :=
    hA.1 hbump hf hS hN fun x hxb hx0 => hbd x hx0 hxb
  refine ⟨U, hUo, hSU, hcpt, fun ε hε => ?_⟩
  -- a parameter `λ ∉ CV` with `|λ| < δ` and `m|λ| ≤ ε/2`
  set r : ℝ := min δ (ε / (2 * (m + 1))) with hr
  have hrpos : 0 < r := lt_min hδ (by positivity)
  obtain ⟨lam, hlamr, hlamCV⟩ : ∃ lam ∈ Metric.ball (0 : Fin m → ℝ) r, lam ∉ CV := by
    by_contra h
    have h1 : Metric.ball (0 : Fin m → ℝ) r ⊆ CV := fun lam hl => by
      by_contra hc
      exact h ⟨lam, hl, hc⟩
    exact (Metric.measure_ball_pos volume (0 : Fin m → ℝ) hrpos).ne' (measure_mono_null h1 hCV)
  have hlamδ : ‖lam‖ < δ := lt_of_lt_of_le (mem_ball_zero_iff.1 hlamr) (min_le_left _ _)
  have hlamε : (m : ℝ) * ‖lam‖ ≤ ε / 2 := by
    have h1 : ‖lam‖ ≤ ε / (2 * (m + 1)) :=
      (mem_ball_zero_iff.1 hlamr).le.trans (min_le_right _ _)
    calc (m : ℝ) * ‖lam‖ ≤ m * (ε / (2 * (m + 1))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (ε / 2) * (m / (m + 1)) := by field_simp
      _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left
          ((div_le_one (by positivity)).2 (by linarith)) (by positivity)
      _ = ε / 2 := mul_one _
  obtain ⟨halw, hdisj, htr, hgood, hcomp, hman⟩ := hlam lam hlamδ hlamCV
  refine ⟨_, halw, ⟨(m : ℝ) * ‖lam‖, by linarith,
      auxLe_paramSlice_zero hN ht htN lam⟩, ⟨_, isClosed_closure.isOpen_compl,
      fun x hxb hxs => Set.disjoint_left.1 hdisj hxs hxb,
      fun x hx => not_not.1 fun hne => hx (subset_closure hne)⟩, htr,
      fun x hx => hgood x hx, hcomp, ?_⟩
  by_cases hne : (solutionSet P (sectionAdd P f
      (paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam))).Nonempty
  · obtain ⟨hsub, -, hloc⟩ := hman hne
    have := PX.paracompactSpace_subtype (solSet P (sectionAdd P f
      (paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam)))
    exact ⟨hsub, PX.paracompactSpace_subtype _,
      MPolyfold.hasCornerStructure_iff_finiteDimensional.2 hloc⟩
  · have he : ∀ x : X, x ∉ solutionSet P (sectionAdd P f
        (paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam)) :=
      fun x hx => hne ⟨x, hx⟩
    have hsub : PX.IsSubMPolyfold (solSet P (sectionAdd P f
        (paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam))) :=
      fun a ha => (he a ha).elim
    have := PX.paracompactSpace_subtype (solSet P (sectionAdd P f
      (paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam)))
    exact ⟨hsub, PX.paracompactSpace_subtype _,
      MPolyfold.hasCornerStructure_iff.2 fun a => (he a.1 a.2).elim⟩

#rt_check RoundTrip.V5_40.A_to_BIntendedStrong [Polyfold.theorem_5_3_12_param,
  Polyfold.StrongBundle.IsGoodPositionGermTame.congr_nhds]

end RoundTrip.V5_40
