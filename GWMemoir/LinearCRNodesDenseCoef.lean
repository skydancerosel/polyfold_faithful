import GWMemoir.LinearCRNodesDenseGeo

/-!
# Changes of charts between discs and necks for forms

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §1.2 (p. 7), §2.4 (p. 51),
on an atlas satisfying `GlueCharts`: the coefficients that carry the neck blocks of a form into
its disc blocks and back.  The changes of charts are those of `GWMemoir.GlueDataNodes`
(`exists_Dn`, `exists_Dd`); the coefficients carry the Jacobians of these changes.

* `exists_rho_neck'`: the partition `ρ_i = (1 - ∑ χ_j) τ_i` of `exists_rho_neck`, with
  `ρ_i ∘ σ_j = 0` for `s ≥ s₀ + 1`.
* `bNf`, `cFN`: from the neck `j` to the disc `i`, `β · χ_j · τ_a(w) / β(s - s₀)` times
  `ε_i⁻¹ (Dψ e_d)` read through `J₀` (`contDiff_cFN`, `tsupport_cFN_sub`, `bNf_mul`).
* `bDf`, `cDN`: from the disc `i` to the neck `j`, `cut(t) τ_a β(s - s₀) ρ_i(σ) / β(ψ)` times
  `½ (D(chart ∘ σ) ∂_s + J₀ D(chart ∘ σ) ∂_t)` (`contDiff_cDN`, `tsupport_cDN_sub`, `bDf_mul`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-- A smooth function times a function smooth near its support is smooth. -/
lemma contDiff_mul_of_tsupport {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {b : ℝ × ℝ → ℝ} {M : ℝ × ℝ → F} {U : Set (ℝ × ℝ)} (hb : ContDiff ℝ ∞ b) (hU : IsOpen U)
    (hsub : tsupport b ⊆ U) (hM : ContDiffOn ℝ ∞ M U) : ContDiff ℝ ∞ fun p => b p • M p := by
  refine contDiff_of_open_cover hU (isClosed_tsupport b).isOpen_compl (fun p => ?_)
    (hb.contDiffOn.smul hM) fun p hp => by simp [image_eq_zero_of_notMem_tsupport hp]
  by_cases h : p ∈ tsupport b
  · exact Or.inl (hsub h)
  · exact Or.inr h

lemma tsupport_mul_sub {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {b : ℝ × ℝ → ℝ} {M : ℝ × ℝ → F} : tsupport (fun p => b p • M p) ⊆ tsupport b :=
  tsupport_smul_subset_left _ _

section Partition

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} {q : Q} {A : SectionAtlas (E := E) X (fun _ => q)}
  (H : GlueCharts A) (hT : ChartsOnto X)
include H hT

/-- **The partition of unity of `exists_rho_neck`**, with `ρ_i ∘ σ_j = 0` for `s ≥ s₀ + 1`. -/
theorem exists_rho_neck' : ∃ ρ : Fin A.nd → C^∞⟮𝓘(ℝ, E2), X.S; 𝓘(ℝ), ℝ⟯,
    (∀ i, tsupport (ρ i) ⊆ discSet (A.center i) (A.ε i)) ∧
      (∀ y, ∑ i, ρ i y + ∑ j, chiSN (A.hol j) (A.s0 j) y = 1) ∧
      ∀ i j (p : ℝ × ℝ), A.s0 j + 1 ≤ p.1 → ρ i (X.polar (A.hol j) p) = 0 := by
  set S : X.S → ℝ := fun y => ∑ j, chiSN (A.hol j) (A.s0 j) y with hSdef
  have hS : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ) ∞ S :=
    contMDiff_finsetSum fun j _ => (chiSb H j).contMDiff
  have hC : tsupport (fun y => 1 - S y) ⊆ ⋃ i, discSet (A.center i) (A.ε i) :=
    (closure_minimal (support_sub_core H) (isClosed_coreSet hT)).trans (core_sub_discSet hT)
  obtain ⟨τ, hτ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E2) (isClosed_tsupport _)
    (fun i => discSet (A.center i) (A.ε i)) (fun i => isOpen_discSet _ _) hC
  have hm : ∀ i, ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ) ∞ fun y => (1 - S y) * τ i y := fun i =>
    (contMDiff_const.sub hS).mul (τ i).contMDiff
  refine ⟨fun i => ⟨fun y => (1 - S y) * τ i y, hm i⟩, fun i => ?_, fun y => ?_,
    fun i j p hp => ?_⟩
  · exact (tsupport_mul_subset_right (f := fun y => 1 - S y) (g := τ i)).trans (hτ i)
  · change ∑ i, (1 - S y) * τ i y + S y = 1
    by_cases hy : y ∈ tsupport (fun y => 1 - S y)
    · have h := τ.sum_eq_one hy
      rw [finsum_eq_sum_of_fintype] at h
      rw [← Finset.mul_sum, h, mul_one, sub_add_cancel]
    · have h0 : 1 - S y = 0 := image_eq_zero_of_notMem_tsupport (f := fun y => 1 - S y) hy
      simp only [h0, zero_mul, Finset.sum_const_zero, zero_add]
      linarith
  · change (1 - S _) * τ i _ = 0
    have hS1 : S (X.polar (A.hol j) p) = 1 := by
      change ∑ j', chiSN (A.hol j') (A.s0 j') (X.polar (A.hol j) p) = 1
      rw [sum_chiSN_of_mem H (X.polar_mem_source (by rw [H.target j]; trivial)),
        chiSN_polar (H.target j), chiN_one hp]
    rw [hS1, sub_self, zero_mul]

end Partition

/-! ## 1. From the necks to the discs -/

section NeckToDisc

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} {q : Q} (A : SectionAtlas (E := E) X (fun _ => q))

/-- The base coefficient `β · χ_j · τ_a(w) / β(s - s₀)` of the neck blocks in the disc blocks. -/
def bNf (i : Fin A.nd) (j : Fin A.nn) (a : Fin 2) (p : ℝ × ℝ) : ℝ :=
  discCut p * chiSN (A.hol j) (A.s0 j) (X.discPt (A.center i) (A.ε i) p) *
    (tauAng a (wN A i j p) / Real.smoothTransition (lamN (A.s0 j) (wN A i j p)))

/-- The Jacobian factor: `ε_i⁻¹ (δ_{kl} α - J_{kl} β)` with `(α, β) = Dψ(e_d)`. -/
def mNf (J₀ : E →L[ℝ] E) (i : Fin A.nd) (j : Fin A.nn) (a : Fin 2) (d : Fin 2)
    (k l : Fin (Module.finrank ℝ E)) (p : ℝ × ℝ) : ℝ :=
  (A.ε i)⁻¹ * ((if k = l then (fderiv ℝ (fDn A i j a) p (dir2 d)).1 else 0) -
    Jm J₀ k l * (fderiv ℝ (fDn A i j a) p (dir2 d)).2)

/-- The coefficient of the neck block `(j, l)` (piece `a`) in the disc block `(i, d, k)`. -/
def cFN (J₀ : E →L[ℝ] E) (i : Fin A.nd) (j : Fin A.nn) (a : Fin 2) (d : Fin 2)
    (k l : Fin (Module.finrank ℝ E)) (p : ℝ × ℝ) : ℝ :=
  bNf A i j a p • mNf A J₀ i j a d k l p

variable {A} (H : GlueCharts A) (hT : ChartsOnto X)
include H hT

lemma lamN_pos_of_mem' {i : Fin A.nd} {j : Fin A.nn} {p : ℝ × ℝ} (h1 : p ∈ closedDisc)
    (h2 : X.discPt (A.center i) (A.ε i) p ∈ tsupport (chiSN (A.hol j) (A.s0 j))) :
    X.discPt (A.center i) (A.ε i) p ∈ (A.hol j).source ∧ wN A i j p ≠ 0 ∧
      ‖wN A i j p‖ < Real.exp (-2 * Real.pi * A.s0 j) := by
  have hsrc := mem_source_of_tsupport H hT h2
  have hz := tsupport_chiSN_sub (H.smooth_symm j).continuous h2
  exact ⟨hsrc, wN_ne_zero H hT h1 hsrc,
    (norm_le_of_mem_zSet (H.target j) hz).trans_lt (rN_lt _)⟩

omit H hT in
lemma mem_KDn_of_ne' {i : Fin A.nd} {j : Fin A.nn} {a : Fin 2} {p : ℝ × ℝ}
    (h : discCut p * chiSN (A.hol j) (A.s0 j) (X.discPt (A.center i) (A.ε i) p) *
      tauAng a (wN A i j p) ≠ 0) : p ∈ KDn A i j a := by
  obtain ⟨h12, h3⟩ := mul_ne_zero_iff.1 h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h12
  exact ⟨discD_sub_closedDisc (discD_of_discCut_ne h1), subset_tsupport _ h2,
    mem_secT_of_tauW_ne h3⟩

lemma contDiff_bNf (i : Fin A.nd) (j : Fin A.nn) (a : Fin 2) : ContDiff ℝ ∞ (bNf A i j a) := by
  set y := X.discPt (A.center i) (A.ε i)
  set V : Set (ℝ × ℝ) := y ⁻¹' ((A.hol j).source ∩
    A.hol j ⁻¹' {ζ | ζ ≠ 0 ∧ ‖ζ‖ < Real.exp (-2 * Real.pi * A.s0 j)})
  have hVo : IsOpen V := ((A.hol j).isOpen_inter_preimage (isOpen_ne.inter
    (isOpen_lt continuous_norm continuous_const))).preimage (continuous_discPt hT _ _)
  set W : Set (ℝ × ℝ) := (closedDisc ∩ y ⁻¹' tsupport (chiSN (A.hol j) (A.s0 j)))ᶜ
  have hWo : IsOpen W := (isCompact_closedDisc.isClosed.inter
    ((isClosed_tsupport _).preimage (continuous_discPt hT _ _))).isOpen_compl
  refine contDiff_of_open_cover hVo hWo (fun p => ?_) ?_ ?_
  · by_cases hp : p ∈ W
    · exact Or.inr hp
    · left
      rw [mem_compl_iff, not_not] at hp
      obtain ⟨h1, h2, h3⟩ := lamN_pos_of_mem' H hT hp.1 hp.2
      exact ⟨h1, h2, h3⟩
  · intro p hp
    obtain ⟨hsrc, hne, hlt⟩ := hp
    have hw := contDiffAt_wN H hT i j hsrc
    have hpos := lamN_pos hne hlt
    refine ContDiffAt.contDiffWithinAt ?_
    have hden : ContDiffAt ℝ ∞
        (fun p => Real.smoothTransition (lamN (A.s0 j) (wN A i j p))) p :=
      Real.smoothTransition.contDiff.contDiffAt.comp p
        ((contDiffAt_lamN (A.s0 j) (ζ := wN A i j p) hne).comp p hw)
    have htau : ContDiffAt ℝ ∞ (fun p => tauAng a (wN A i j p)) p :=
      (contDiffAt_tauW a (ζ := wN A i j p) hne).comp p hw
    exact (contDiff_discCut.contDiffAt.mul (contDiff_chiSN_discPt H hT i j).contDiffAt).mul
      (htau.div hden (Real.smoothTransition.pos_of_pos hpos).ne')
  · intro p hp
    rw [mem_compl_iff, mem_inter_iff, not_and_or] at hp
    rcases hp with hp | hp
    · simp [bNf, discCut_eq_zero hp]
    · simp [bNf, y, image_eq_zero_of_notMem_tsupport hp]

lemma tsupport_bNf_sub (i : Fin A.nd) (j : Fin A.nn) (a : Fin 2) :
    tsupport (bNf A i j a) ⊆ KDn A i j a := by
  refine closure_minimal (fun p hp => mem_KDn_of_ne' (a := a) ?_)
    (isCompact_KDn H hT i j a).isClosed
  intro h
  apply hp
  rcases mul_eq_zero.1 h with h' | h'
  · simp [bNf, h']
  · simp [bNf, h']

lemma bNf_mul {i : Fin A.nd} {j : Fin A.nn} {a : Fin 2} {D : ChartChange}
    (hDK : D.K = KDn A i j a) (hDψ : ∀ p ∈ D.K, D.ψ p = fDn A i j a p) (p : ℝ × ℝ) :
    bNf A i j a p * Real.smoothTransition (D.ψ p).1 =
      discCut p * chiSN (A.hol j) (A.s0 j) (X.discPt (A.center i) (A.ε i) p) *
        tauAng a (wN A i j p) := by
  by_cases h : discCut p * chiSN (A.hol j) (A.s0 j) (X.discPt (A.center i) (A.ε i) p) *
      tauAng a (wN A i j p) = 0
  · rw [h]
    rcases mul_eq_zero.1 h with h' | h'
    · simp [bNf, h']
    · simp [bNf, h']
  · have hK := mem_KDn_of_ne' h
    obtain ⟨h12, -⟩ := mul_ne_zero_iff.1 h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h12
    obtain ⟨-, hne, hlt⟩ := lamN_pos_of_mem' H hT
      (discD_sub_closedDisc (discD_of_discCut_ne h1)) (subset_tsupport _ h2)
    have hpos := Real.smoothTransition.pos_of_pos (lamN_pos hne hlt)
    rw [hDψ p (hDK ▸ hK), fDn_fst H, bNf, mul_assoc, div_mul_cancel₀ _ hpos.ne']

lemma contDiffOn_mNf (J₀ : E →L[ℝ] E) (i : Fin A.nd) (j : Fin A.nn) (a d : Fin 2)
    (k l : Fin (Module.finrank ℝ E)) : ContDiffOn ℝ ∞ (mNf A J₀ i j a d k l) (UDn A i j a) := by
  intro p hp
  have hF : ContDiffAt ℝ ∞ (fun p => fderiv ℝ (fDn A i j a) p (dir2 d)) p :=
    ((contDiffAt_fDn H hT a hp).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  have h1 : ContDiffAt ℝ ∞ (fun p => (fderiv ℝ (fDn A i j a) p (dir2 d)).1) p :=
    contDiff_fst.contDiffAt.comp p hF
  have h2 : ContDiffAt ℝ ∞ (fun p => (fderiv ℝ (fDn A i j a) p (dir2 d)).2) p :=
    contDiff_snd.contDiffAt.comp p hF
  refine ContDiffAt.contDiffWithinAt ?_
  unfold mNf
  split_ifs
  · exact contDiffAt_const.mul (h1.sub (contDiffAt_const.mul h2))
  · exact contDiffAt_const.mul (contDiffAt_const.sub (contDiffAt_const.mul h2))

lemma contDiff_cFN (J₀ : E →L[ℝ] E) (i : Fin A.nd) (j : Fin A.nn) (a d : Fin 2)
    (k l : Fin (Module.finrank ℝ E)) : ContDiff ℝ ∞ (cFN A J₀ i j a d k l) :=
  contDiff_mul_of_tsupport (contDiff_bNf H hT i j a) (isOpen_UDn H hT i j a)
    ((tsupport_bNf_sub H hT i j a).trans (KDn_sub_UDn H hT i j a))
    (contDiffOn_mNf H hT J₀ i j a d k l)

lemma tsupport_cFN_sub (J₀ : E →L[ℝ] E) (i : Fin A.nd) (j : Fin A.nn) (a d : Fin 2)
    (k l : Fin (Module.finrank ℝ E)) : tsupport (cFN A J₀ i j a d k l) ⊆ KDn A i j a :=
  tsupport_mul_sub.trans (tsupport_bNf_sub H hT i j a)

end NeckToDisc

/-! ## 2. From the discs to the necks -/

section DiscToNeck

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} {q : Q} (A : SectionAtlas (E := E) X (fun _ => q))

/-- The numerator `cut(t) τ_a(t + θ_a) β(s - s₀) ρ(σ(s, t + θ_a))`. -/
def nDf (j : Fin A.nn) (a : Fin 2) (ρ : X.S → ℝ) (y : ℝ × ℝ) : ℝ :=
  cutT y.2 * tauT a (y.2 + thetaN a) * Real.smoothTransition (y.1 - A.s0 j) *
    ρ (polarSh A j 0 (thetaN a) y)

/-- The base coefficient of the disc blocks in the neck blocks. -/
def bDf (j : Fin A.nn) (i : Fin A.nd) (a : Fin 2) (ρ : X.S → ℝ) (y : ℝ × ℝ) : ℝ :=
  nDf A j a ρ y / discCut (fDd A j i a y)

/-- `D(chart_i ∘ σ) w`, the derivative of the polar coordinates read in the disc chart. -/
def jDf (i : Fin A.nd) (j : Fin A.nn) (a : Fin 2) (w y : ℝ × ℝ) : E2 :=
  fderiv ℝ (fun y => extChartAt 𝓘(ℝ, E2) (A.center i) (polarSh A j 0 (thetaN a) y)) y w

/-- The Jacobian factor `½ (δ_{kl} (D ∂_s)_d + J_{kl} (D ∂_t)_d)`. -/
def mDf (J₀ : E →L[ℝ] E) (j : Fin A.nn) (i : Fin A.nd) (a : Fin 2) (d : Fin 2)
    (k l : Fin (Module.finrank ℝ E)) (y : ℝ × ℝ) : ℝ :=
  (1 / 2 : ℝ) * ((if k = l then jDf A i j a (1, 0) y d else 0) +
    Jm J₀ k l * jDf A i j a (0, 1) y d)

/-- The coefficient of the disc block `(i, d, l)` (piece `a`) in the neck block `(j, k)`. -/
def cDN (J₀ : E →L[ℝ] E) (j : Fin A.nn) (i : Fin A.nd) (a : Fin 2) (ρ : X.S → ℝ) (d : Fin 2)
    (k l : Fin (Module.finrank ℝ E)) (y : ℝ × ℝ) : ℝ :=
  bDf A j i a ρ y • mDf A J₀ j i a d k l y

variable {A}

lemma mem_KDd_of_ne' {j : Fin A.nn} {a : Fin 2} {ρ : X.S → ℝ}
    (hρn : ∀ p : ℝ × ℝ, A.s0 j + 1 ≤ p.1 → ρ (X.polar (A.hol j) p) = 0) {y : ℝ × ℝ}
    (h : nDf A j a ρ y ≠ 0) : y ∈ KDd A j a ρ := by
  obtain ⟨h123, h4⟩ := mul_ne_zero_iff.1 h
  obtain ⟨h12, h3⟩ := mul_ne_zero_iff.1 h123
  obtain ⟨h1, -⟩ := mul_ne_zero_iff.1 h12
  refine ⟨⟨⟨?_, ?_⟩, mem_of_cutT_ne h1⟩, subset_tsupport _ h4⟩
  · by_contra hc
    exact h3 (Real.smoothTransition.zero_of_nonpos (by linarith [not_le.1 hc]))
  · by_contra hc
    exact h4 (hρn _ (by simp only [add_zero]; linarith [not_le.1 hc]))

variable (H : GlueCharts A) (hT : ChartsOnto X)
include H hT

lemma contDiff_bDf (j : Fin A.nn) (i : Fin A.nd) (a : Fin 2) (ρ : C^∞⟮𝓘(ℝ, E2), X.S; 𝓘(ℝ), ℝ⟯)
    (hρ : tsupport ρ ⊆ discSet (A.center i) (A.ε i)) : ContDiff ℝ ∞ (bDf A j i a ρ) := by
  set V : Set (ℝ × ℝ) := polarSh A j 0 (thetaN a) ⁻¹' discSet (A.center i) (A.ε i)
  have hVo : IsOpen V := (isOpen_discSet _ _).preimage (continuous_polarSh H j 0 _)
  set W : Set (ℝ × ℝ) := (polarSh A j 0 (thetaN a) ⁻¹' tsupport ρ)ᶜ
  have hWo : IsOpen W := ((isClosed_tsupport _).preimage (continuous_polarSh H j 0 _)).isOpen_compl
  have hN : ContDiff ℝ ∞ (nDf A j a ρ) := by
    have hρc : ContDiff ℝ ∞ fun y => ρ (polarSh A j 0 (thetaN a) y) :=
      contMDiff_iff_contDiff.1 (ρ.contMDiff.comp (contMDiff_polarSh H j 0 _))
    exact (((contDiff_cutT.comp contDiff_snd).mul
      ((contDiff_tauT a).comp (contDiff_snd.add contDiff_const))).mul
      (Real.smoothTransition.contDiff.comp (contDiff_fst.sub contDiff_const))).mul hρc
  refine contDiff_of_open_cover hVo hWo (fun y => ?_) (fun y hy => ?_) (fun y hy => ?_)
  · by_cases h : y ∈ W
    · exact Or.inr h
    · exact Or.inl (hρ (not_not.1 h))
  · have hf := contDiffAt_chart_polarSh H (A.center i) (A.ε i) j 0 (thetaN a) hy.1
    have hpos : 0 < discCut (fDd A j i a y) := discCut_pos hy.2
    exact (hN.contDiffAt.div (contDiff_discCut.contDiffAt.comp y hf) hpos.ne').contDiffWithinAt
  · simp [bDf, nDf, image_eq_zero_of_notMem_tsupport hy]

lemma tsupport_bDf_sub (j : Fin A.nn) (i : Fin A.nd) (a : Fin 2) {ρ : X.S → ℝ}
    (hρn : ∀ p : ℝ × ℝ, A.s0 j + 1 ≤ p.1 → ρ (X.polar (A.hol j) p) = 0) :
    tsupport (bDf A j i a ρ) ⊆ KDd A j a ρ := by
  refine closure_minimal (fun y hy => mem_KDd_of_ne' hρn ?_)
    ((isCompact_KDd H hT j a ρ).isClosed)
  intro h
  exact hy (by simp [bDf, h])

lemma bDf_mul {j : Fin A.nn} {i : Fin A.nd} {a : Fin 2} {ρ : X.S → ℝ}
    (hρ : tsupport ρ ⊆ discSet (A.center i) (A.ε i))
    (hρn : ∀ p : ℝ × ℝ, A.s0 j + 1 ≤ p.1 → ρ (X.polar (A.hol j) p) = 0) {D : ChartChange}
    (hDK : D.K = KDd A j a ρ) (hDψ : ∀ y ∈ D.K, D.ψ y = fDd A j i a y) (y : ℝ × ℝ) :
    bDf A j i a ρ y * discCut (D.ψ y) = nDf A j a ρ y := by
  by_cases h : nDf A j a ρ y = 0
  · simp [bDf, h]
  · have hK := mem_KDd_of_ne' hρn h
    have hpos : 0 < discCut (fDd A j i a y) := discCut_pos (hρ hK.2).2
    rw [hDψ y (hDK ▸ hK), bDf, div_mul_cancel₀ _ hpos.ne']

lemma contDiffOn_mDf (J₀ : E →L[ℝ] E) (j : Fin A.nn) (i : Fin A.nd) (a d : Fin 2)
    (k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (mDf A J₀ j i a d k l) (UDd A j i a) := by
  intro y hy
  have hc : ContDiffAt ℝ ∞
      (fun y => extChartAt 𝓘(ℝ, E2) (A.center i) (polarSh A j 0 (thetaN a) y)) y := by
    have h1 : ContMDiffAt 𝓘(ℝ, E2) 𝓘(ℝ, E2) ∞ (extChartAt 𝓘(ℝ, E2) (A.center i))
        (polarSh A j 0 (thetaN a) y) :=
      contMDiffAt_extChartAt' (by rw [← extChartAt_source 𝓘(ℝ, E2)]; exact hy.2)
    exact contMDiffAt_iff_contDiffAt.1 (h1.comp y (contMDiff_polarSh H j 0 _ y))
  have hF : ∀ w : ℝ × ℝ, ContDiffAt ℝ ∞ (fun y => jDf A i j a w y d) y := fun w =>
    (EuclideanSpace.proj d : E2 →L[ℝ] ℝ).contDiff.contDiffAt.comp y
      ((hc.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const)
  refine ContDiffAt.contDiffWithinAt ?_
  unfold mDf
  split_ifs
  · exact contDiffAt_const.mul ((hF _).add (contDiffAt_const.mul (hF _)))
  · exact contDiffAt_const.mul (contDiffAt_const.add (contDiffAt_const.mul (hF _)))

lemma contDiff_cDN (J₀ : E →L[ℝ] E) (j : Fin A.nn) (i : Fin A.nd) (a : Fin 2)
    (ρ : C^∞⟮𝓘(ℝ, E2), X.S; 𝓘(ℝ), ℝ⟯) (hρ : tsupport ρ ⊆ discSet (A.center i) (A.ε i))
    (hρn : ∀ p : ℝ × ℝ, A.s0 j + 1 ≤ p.1 → ρ (X.polar (A.hol j) p) = 0) (d : Fin 2)
    (k l : Fin (Module.finrank ℝ E)) : ContDiff ℝ ∞ (cDN A J₀ j i a ρ d k l) :=
  contDiff_mul_of_tsupport (contDiff_bDf H hT j i a ρ hρ) (isOpen_UDd H hT j i a)
    ((tsupport_bDf_sub H hT j i a hρn).trans (KDd_sub_UDd H hT a hρ))
    (contDiffOn_mDf H hT J₀ j i a d k l)

lemma tsupport_cDN_sub (J₀ : E →L[ℝ] E) (j : Fin A.nn) (i : Fin A.nd) (a : Fin 2)
    {ρ : X.S → ℝ} (hρn : ∀ p : ℝ × ℝ, A.s0 j + 1 ≤ p.1 → ρ (X.polar (A.hol j) p) = 0)
    (d : Fin 2) (k l : Fin (Module.finrank ℝ E)) :
    tsupport (cDN A J₀ j i a ρ d k l) ⊆ KDd A j a ρ :=
  tsupport_mul_sub.trans (tsupport_bDf_sub H hT j i a hρn)

end DiscToNeck

end GWMemoir
