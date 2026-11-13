import Polyfold.Chapter14.P3W4LX_LocalExtension
import Polyfold.Chapter10.StrongBundleEquivalenceExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.1, p. 642:
**Proposition 14.1.4** (Local Extension Result; 2017: Remark 14.2) on `V(x)` itself.

# Extension of face-wise sc⁺ data from `V ∩ ∂X` to the open set `V`

## The text, paraphrased

(Proof of Proposition 14.1.4) Each `sᵢ` on `U(x) = V(x) ∩ ∂X` extends to an sc⁺-section `s̄⁰ᵢ` on
`V(x)` "using an sc-smooth partition of unity argument"; then the `s̄⁰ᵢ` are averaged.

## What is formalized

* `IsScPlusSectionOn.of_locally_p3w4`: sc⁺ on an open set is a local property.
* `exists_scSmooth_cutoff_p3w4`: for a closed `K` inside an open `O` an sc-smooth `χ : X → [0, 1]`
  with `χ = 1` on `K` and `supp χ ⊆ O` (a two-set partition of unity).
* `exists_scPlusSectionOn_extension_of_face`: for `s` face-wise sc⁺ on `V ∩ ∂X` there is an
  sc⁺-section on `V` equal to `s` on `V ∩ ∂X`.  The object M-polyfold is metrizable
  (`MPolyfold.metrizableSpace`); with `f = dist(·, X ∖ V)` the sets `G_n = {f > 1/(n+1)}` exhaust
  `V` with `cl G_n ⊆ G_{n+1}`; cut-offs `χ_n` (`= 1` on `cl G_n`, supported in `G_{n+1}`) give the
  weights `w_n = χ_n − χ_{n−1}`, locally finite on `V` with sum `1`; the extensions `σ_n` of
  `exists_scPlusSection_extension_of_face` agree with `s` on `G_{n+1} ∩ ∂X ⊇ supp w_n ∩ ∂X`; and
  `Σ_n w_n σ_n` is the extension.
* **Proposition 14.1.4**: `proposition_14_1_4_full` (the hypothesis of B1's
  `proposition_14_1_4_hyp` discharged on `V(x)` itself).
* `proposition_14_1_4_hypotheses_rn`: the two standing hypotheses (tame strong bundle charts,
  partitions of unity of the object M-polyfold) hold for `ℝⁿ × ℝᵏ → ℝⁿ` over the trivial
  ep-groupoid of `ℝⁿ`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-- **Sc⁺ on an open set is local.** -/
theorem IsScPlusSectionOn.of_locally_p3w4 {s : A.Obj → A.W} {U : Set A.Obj} (hU : IsOpen U)
    (h : ∀ y ∈ U, ∃ U' : Set A.Obj, IsOpen U' ∧ y ∈ U' ∧ U' ⊆ U ∧ IsScPlusSectionOn A s U') :
    IsScPlusSectionOn A s U := by
  classical
  choose U' hU' hyU' hU'U hs using h
  have hmem : ∀ y (hy : y ∈ U), s y ∈ A.B.oneSet := fun y hy =>
    (hs y hy).mem_oneSet (hyU' y hy)
  have h0 : ∀ y, fiberZero A.P y ∈ A.B.oneSet := fun y =>
    (StrongBundle.isScPlusSection_fiberZero (B := A.B)).mem_oneSet y
  set G : A.Obj → A.B.One := fun y =>
    if hy : s y ∈ A.B.oneSet then A.B.oneMk (s y) hy else A.B.oneMk _ (h0 y) with hGdef
  have hG : ∀ y (hy : y ∈ U), A.B.oneVal (G y) = s y := fun y hy => by
    simp only [hGdef, dif_pos (hmem y hy), oneVal_oneMk]
  refine ⟨fun y hy => (hs y hy).1 y (hyU' y hy), G, hG, ?_⟩
  refine MPolyfold.IsScSmoothOn.of_locally hU fun y hy => ?_
  obtain ⟨-, G', hG', hG's⟩ := hs y hy
  refine ⟨U' y hy, hU' y hy, hyU' y hy, hU'U y hy, hG's.congr fun z hz => ?_⟩
  apply A.B.oneVal_injective
  rw [hG' z hz, hG z (hU'U y hy hz)]

/-- **Sc-smooth cut-offs**: for a closed `K` inside an open `O` there is an sc-smooth
`χ : X → [0, 1]` with `χ = 1` on `K` and `supp χ ⊆ O` (from a partition of unity for the cover
`{O, X ∖ K}`). -/
theorem exists_scSmooth_cutoff_p3w4 (hpu : A.X.PObj.AdmitsScPartitionsOfUnity) {K O : Set A.Obj}
    (hK : IsClosed K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ χ : A.Obj → ℝ, A.X.PObj.IsScSmoothMap realPolyfold χ ∧ (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧
      (∀ y ∈ K, χ y = 1) ∧ tsupport χ ⊆ O := by
  classical
  let U : ULift.{u} Bool → Set A.Obj := fun b => if b.down then O else Kᶜ
  have hUo : ∀ b, IsOpen (U b) := fun b => by
    dsimp only [U]; split_ifs
    · exact hO
    · exact hK.isOpen_compl
  have hUc : ⋃ b, U b = univ := iUnion_eq_univ_iff.2 fun y => by
    by_cases hy : y ∈ K
    · exact ⟨⟨true⟩, by simp only [U]; exact hKO hy⟩
    · exact ⟨⟨false⟩, by simp only [U]; exact hy⟩
  obtain ⟨ρ, hρsub, hρsm⟩ := hpu (ULift.{u} Bool) U hUo hUc
  refine ⟨ρ ⟨true⟩, hρsm _, fun y => ⟨ρ.nonneg _ y, ρ.le_one _ y⟩, fun y hy => ?_,
    hρsub ⟨true⟩⟩
  have h0 : ρ ⟨false⟩ y = 0 := by
    by_contra hne
    exact (hρsub ⟨false⟩ (subset_tsupport _ hne)) hy
  have hsum := ρ.sum_eq_one (mem_univ y)
  have hs : ∀ i, i ≠ (⟨true⟩ : ULift.{u} Bool) → ρ i y = 0 := by
    rintro ⟨_ | _⟩ hi
    · exact h0
    · exact absurd rfl hi
  rwa [finsum_eq_single _ _ hs] at hsum

/-- **The partition of unity step of Proposition 14.1.4 on the open set `V` itself**: let every
object lie in a tame strong bundle chart and let the object M-polyfold admit sc-smooth partitions
of unity.  If `s` is face-wise sc⁺ on `V ∩ ∂X` (`V` open, Definition 14.1.3 (1)), there is an
sc⁺-section `σ` on `V` with `σ = s` on `V ∩ ∂X`. -/
theorem exists_scPlusSectionOn_extension_of_face
    (hB : ∀ x : A.Obj, ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧ x ∈ c.φ.source)
    (hpu : A.X.PObj.AdmitsScPartitionsOfUnity) {s : A.Obj → A.W} {V : Set A.Obj}
    (hV : IsOpen V) (hs : IsFaceScPlusSectionOn A s (V ∩ A.X.PObj.boundary)) :
    ∃ σ : A.Obj → A.W, IsScPlusSectionOn A σ V ∧ ∀ y ∈ V ∩ A.X.PObj.boundary, σ y = s y := by
  classical
  rcases (Vᶜ).eq_empty_or_nonempty with hF | hF
  · have hVu : V = univ := compl_empty_iff.mp hF
    obtain ⟨σ, hσ, hσs⟩ := exists_scPlusSection_extension_of_face hB hpu hV hs
      (G := univ) (by rw [closure_univ, hVu])
    exact ⟨σ, IsScPlusSectionOn.of_isScPlusSection hσ hV,
      fun y hy => hσs y ⟨mem_univ _, hy.2⟩⟩
  have := MPolyfold.metrizableSpace A.X.PObj
  let _ : MetricSpace A.Obj := TopologicalSpace.metrizableSpaceMetric A.Obj
  -- the exhaustion `G n = {dist(·, X ∖ V) > 1/(n+1)}`
  set f : A.Obj → ℝ := fun y => Metric.infDist y Vᶜ with hfdef
  have hfc : Continuous f := Metric.continuous_infDist_pt _
  have hfpos : ∀ y, y ∈ V ↔ 0 < f y := fun y => by
    have h := hV.isClosed_compl.notMem_iff_infDist_pos (x := y) hF
    rwa [notMem_compl_iff] at h
  set G : ℕ → Set A.Obj := fun n => {y | ((n : ℝ) + 1)⁻¹ < f y} with hGdef
  have hGo : ∀ n, IsOpen (G n) := fun n => isOpen_lt continuous_const hfc
  have hGcl : ∀ n, closure (G n) ⊆ {y | ((n : ℝ) + 1)⁻¹ ≤ f y} := fun n =>
    closure_minimal (fun y (hy : y ∈ G n) => show ((n : ℝ) + 1)⁻¹ ≤ f y from le_of_lt hy)
      (isClosed_le continuous_const hfc)
  have hGV : ∀ n, closure (G n) ⊆ V := fun n y hy =>
    (hfpos y).2 (lt_of_lt_of_le (by positivity) (hGcl n hy))
  have hGsucc : ∀ n, closure (G n) ⊆ G (n + 1) := fun n y hy => by
    have h1 := hGcl n hy
    change (((n + 1 : ℕ) : ℝ) + 1)⁻¹ < f y
    refine lt_of_lt_of_le (inv_strictAnti₀ (by positivity) (by push_cast; linarith)) h1
  have hGmono : Monotone G := monotone_nat_of_le_succ fun n =>
    subset_closure.trans (hGsucc n)
  have hVG : ∀ y ∈ V, ∃ n, y ∈ G n := fun y hy => by
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt ((hfpos y).1 hy)
    exact ⟨n, by rw [one_div] at hn; exact hn⟩
  -- the cut-offs and the weights `w n = c (n + 1) − c n`, `c 0 = 0`, `c (n + 1) = χ n`
  choose χ hχs hχ01 hχ1 hχsupp using fun n =>
    exists_scSmooth_cutoff_p3w4 hpu isClosed_closure (hGo (n + 1)) (hGsucc n)
  set c : ℕ → A.Obj → ℝ := fun n y => if n = 0 then 0 else χ (n - 1) y with hcdef
  have hc0 : ∀ y, c 0 y = 0 := fun y => by simp [hcdef]
  have hcs : ∀ n y, c (n + 1) y = χ n y := fun n y => by simp [hcdef]
  set w : ℕ → A.Obj → ℝ := fun n y => c (n + 1) y - c n y with hwdef
  have hcsm : ∀ n, A.X.PObj.IsScSmoothMap realPolyfold (c n) := fun n => by
    rcases n with _ | n
    · have : c 0 = fun _ => (0 : ℝ) := funext hc0
      rw [this]; exact isScSmoothMap_real_const 0
    · have : c (n + 1) = χ n := funext (hcs n)
      rw [this]; exact hχs n
  have hwsm : ∀ n, A.X.PObj.IsScSmoothMap realPolyfold (w n) := fun n =>
    (hcsm (n + 1)).real_sub (hcsm n)
  -- `c n = 1` on `G m` for `n > m`
  have hc1 : ∀ m n, m < n → ∀ y ∈ G m, c n y = 1 := fun m n hmn y hy => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [hcs]
    exact hχ1 k y (subset_closure (hGmono (by omega : m ≤ k) hy))
  have hw0 : ∀ m n, m < n → ∀ y ∈ G m, w n y = 0 := fun m n hmn y hy => by
    simp only [hwdef, hc1 m (n + 1) (by omega) y hy, hc1 m n hmn y hy, sub_self]
  -- `w n = 0` off `G (n + 1)`
  have hwG : ∀ n y, w n y ≠ 0 → y ∈ G (n + 1) := fun n y hne => by
    by_contra hy
    apply hne
    have h1 : c (n + 1) y = 0 := by
      rw [hcs]; exact image_eq_zero_of_notMem_tsupport fun h => hy (hχsupp n h)
    have h2 : c n y = 0 := by
      rcases n with _ | k
      · exact hc0 y
      · rw [hcs]
        exact image_eq_zero_of_notMem_tsupport fun h =>
          hy (subset_closure.trans (hGsucc (k + 1)) (hχsupp k h))
    simp only [hwdef, h1, h2, sub_self]
  -- the extensions `σ n = s` on `G (n + 1) ∩ ∂X`
  choose σ hσ hσs using fun n => exists_scPlusSection_extension_of_face hB hpu hV hs (hGV (n + 1))
  have hsec : ∀ n, IsSection A.P (σ n) := fun n => (hσ n).1
  set τ : A.Obj → A.W := fun y =>
    ((∑ᶠ n, w n y • (⟨σ n y, hsec n y⟩ : A.P ⁻¹' {y}) : A.P ⁻¹' {y}) : A.W) with hτdef
  have hfin : ∀ m, ∀ y ∈ G m, (∑ᶠ n, w n y • (⟨σ n y, hsec n y⟩ : A.P ⁻¹' {y})) =
      ∑ n ∈ Finset.range (m + 1), w n y • (⟨σ n y, hsec n y⟩ : A.P ⁻¹' {y}) :=
    fun m y hy => finsum_eq_sum_of_support_subset _ fun n hn => by
      rw [Finset.coe_range, mem_Iio]
      by_contra hmn
      apply hn
      simp only [hw0 m n (by omega) y hy, zero_smul]
  refine ⟨τ, IsScPlusSectionOn.of_locally_p3w4 hV fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨m, hm⟩ := hVG y hy
    have hsum : A.B.IsScPlusSection
        (sectionSum A.P (Finset.range (m + 1)) fun n => sectionSmul A.P (w n) (σ n)) :=
      StrongBundle.isScPlusSection_sectionSum _ fun n => (hσ n).smul_left (hwsm n)
    refine ⟨G m, hGo m, hm, subset_closure.trans (hGV m),
      (IsScPlusSectionOn.of_isScPlusSection hsum (hGo m)).congr fun z hz => ?_⟩
    rw [sectionSum_apply (fun n => (hsec n).sectionSmul), hτdef]
    dsimp only
    rw [hfin m z hz]
    congr 1
    refine Finset.sum_congr rfl fun n _ => Subtype.ext ?_
    exact sectionSmul_apply (hsec n) z
  · obtain ⟨m, hm⟩ := hVG y hy.1
    have hPs : A.P (s y) = y := (hs.1 y hy).1
    have hterm : ∀ n ∈ Finset.range (m + 1), w n y • (⟨σ n y, hsec n y⟩ : A.P ⁻¹' {y}) =
        w n y • (⟨s y, hPs⟩ : A.P ⁻¹' {y}) := fun n _ => by
      by_cases hwn : w n y = 0
      · rw [hwn, zero_smul, zero_smul]
      · congr 2
        exact hσs n y ⟨hwG n y hwn, hy.2⟩
    have htel : ∑ n ∈ Finset.range (m + 1), w n y = 1 := by
      rw [Finset.sum_range_sub (fun n => c n y) (m + 1), hcs, hc0, sub_zero]
      exact hχ1 m y (subset_closure hm)
    rw [hτdef]
    dsimp only
    rw [hfin m y hm, Finset.sum_congr rfl hterm, ← Finset.sum_smul, htel, one_smul]

/-- **2021 Proposition 14.1.4, p. 642 (2017: Remark 14.2)**, on `V(x)`: let every object lie in a
tame strong bundle chart and let the object M-polyfold admit sc-smooth partitions of unity.  A
symmetric sc⁺-section structure `(sᵢ)` on `U(x) = V(x) ∩ ∂X` (Definition 14.1.3) extends to
sc⁺-sections `s̄ᵢ` on `V(x)` with `s̄ᵢ|U(x) = sᵢ` and `s̄_{g(i)}(g ∗ y) = μ(Γ(g, y), s̄ᵢ(y))` for
all `y ∈ V(x)` (Definition 13.2.5 (1)).  (The hypothesis of `proposition_14_1_4_hyp` is
`exists_scPlusSectionOn_extension_of_face`.) -/
theorem proposition_14_1_4_full
    (hB : ∀ x : A.Obj, ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧ x ∈ c.φ.source)
    (hpu : A.X.PObj.AdmitsScPartitionsOfUnity) {Λ : A.W → ℚ≥0} {x : A.Obj}
    {V : A.X.NatNbhd x} (S : BoundarySymmetricStructure A Λ V) :
    ∃ sb : S.I → A.Obj → A.W, (∀ i, IsScPlusSectionOn A (sb i) V.U) ∧
      (∀ i, ∀ y ∈ V.bdry, sb i y = S.s i y) ∧
      ∀ (g : A.X.Isotropy x) i, ∀ y ∈ V.U,
        sb (g • i) (V.rep.Φ g y) = fibAct (V.rep.Γ g y) (sb i y) := by
  choose s₀ hs₀ hs₀b using fun i =>
    exists_scPlusSectionOn_extension_of_face hB hpu V.isOpen_U (S.isFaceScPlus i)
  exact proposition_14_1_4_hyp S s₀ hs₀ hs₀b

/-- **The standing hypotheses of `proposition_14_1_4_full` and `proposition_14_4_14` are
satisfiable**: for the trivial bundle `ℝⁿ × ℝᵏ → ℝⁿ` over the trivial ep-groupoid of `ℝⁿ`
(`StrongBundleEquivalenceExamples.epSEP`) every object lies in a tame strong bundle chart and the
object M-polyfold admits sc-smooth partitions of unity. -/
theorem proposition_14_1_4_hypotheses_rn (n k : ℕ) :
    (∀ x : (StrongBundleEquivalenceExamples.epSEP n k).Obj,
      ∃ c : StrongBundleChart (StrongBundleEquivalenceExamples.epSEP n k).X.PObj
          (StrongBundleEquivalenceExamples.epSEP n k).P,
        (StrongBundleEquivalenceExamples.epSEP n k).B.IsTameChart c ∧ x ∈ c.φ.source) ∧
      (StrongBundleEquivalenceExamples.epSEP n k).X.PObj.AdmitsScPartitionsOfUnity :=
  ⟨(EpStrongBundle.theorem_12_3_9_hypotheses_rn n k).1.2,
    (EpGroupoid.theorem_7_5_7_hypotheses_rn n).2⟩

end SBLocalization

end Polyfold
