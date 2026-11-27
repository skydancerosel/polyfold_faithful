import GWMemoir.LinearCRNodesDenseCoef

/-!
# The gluing operator on the fibre blocks with necks

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §1.2 (p. 7), §2.4 (p. 51),
at a constant map, on an atlas satisfying `GlueCharts`: the operator `Φ` of `formsDense_const`
with necks.  For a tuple `v` of blocks it reads the disc blocks as forms `ξ_i` in the discs and
the neck blocks as anti-linear forms `ξ_j` on the necks, glues them with the partition
`∑ ρ_i + ∑ χ_j = 1` and returns the representative of the anti-linear part of the glued form.

* `FormGlueN A`: the partition (`exists_rho_neck'`) and the changes of charts between discs
  (`exists_chartChange`), from the discs to the necks (`exists_Dn`) and back (`exists_Dd`);
  `nonempty_formGlueN`.
* `discOutN`, `neckOutN`, `glueN`, `phiN`: the operator, bounded on the level-`0` fibre blocks.
* `neckToDisc_pt`, `discToNeck_pt`: the two changes of charts, pointwise.
* `GWMemoir.LinearCRNodesDenseRep`: if the disc blocks of `v` agree with the representatives of
  `ξ_i` where the cut-off does not vanish, and the neck blocks with those of anti-linear `ξ_j` for
  `s ≥ s₀ + ½`, then `Φ v` represents `projF J(q) (∑ ρ_i ξ_i + ∑ χ_j ξ_j)` (`isFormRep_phiN`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. The gluing data for forms -/

section Glue

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} {q : Q} (A : SectionAtlas (E := E) X (fun _ => q))

/-- **Gluing data for forms with necks**: the partition `∑ ρ_i + ∑ χ_j = 1` with `ρ_i ∘ σ_j = 0`
for `s ≥ s₀ + 1`, and the changes of charts between discs, from discs to necks and back. -/
structure FormGlueN where
  ρ : Fin A.nd → C^∞⟮𝓘(ℝ, E2), X.S; 𝓘(ℝ), ℝ⟯
  hρ : ∀ i, tsupport (ρ i) ⊆ discSet (A.center i) (A.ε i)
  hsum : ∀ y, ∑ i, ρ i y + ∑ j, chiSN (A.hol j) (A.s0 j) y = 1
  hρn : ∀ i j (p : ℝ × ℝ), A.s0 j + 1 ≤ p.1 → ρ i (X.polar (A.hol j) p) = 0
  D : Fin A.nd → Fin A.nd → ChartChange
  hDK : ∀ i j, (D i j).K = pieceK (ρ j) (A.center i) (A.ε i)
  hDψ : ∀ i j, ∀ p ∈ (D i j).K,
    (D i j).ψ p = dtrans (A.center i) (A.ε i) (A.center j) (A.ε j) p
  Dn : Fin A.nd → Fin A.nn → Fin 2 → ChartChange
  hDnK : ∀ i j a, (Dn i j a).K = KDn A i j a
  hDnψ : ∀ i j a, ∀ p ∈ (Dn i j a).K, (Dn i j a).ψ p = fDn A i j a p
  Dd : Fin A.nn → Fin A.nd → Fin 2 → ChartChange
  hDdK : ∀ j i a, (Dd j i a).K = KDd A j a (ρ i)
  hDdψ : ∀ j i a, ∀ y ∈ (Dd j i a).K, (Dd j i a).ψ y = fDd A j i a y

variable {A}

/-- **Gluing data for forms exist** on an atlas satisfying `GlueCharts`. -/
theorem nonempty_formGlueN (hG : GlueCharts A) (hT : ChartsOnto X) : Nonempty (FormGlueN A) := by
  obtain ⟨ρ, hρ, hsum, hρn⟩ := exists_rho_neck' hG hT
  choose D hDK hDψ using fun i j : Fin A.nd =>
    exists_chartChange hT (ρ := ρ j) (z := A.center i) (A.ε_pos i).ne' (A.ε_pos j).ne' (hρ j)
  choose Dn hDnK hDnψ using fun i j a => exists_Dn hG hT i j a
  choose Dd hDdK hDdψ using fun j i a => exists_Dd hG hT j i a (hρ i)
  exact ⟨⟨ρ, hρ, hsum, hρn, D, hDK, hDψ, Dn, hDnK, hDnψ, Dd, hDdK, hDdψ⟩⟩

end Glue

lemma mult_chiN (s₀ : ℝ) (k : ℕ) : Mult k (chiN s₀) := by
  refine Neck.mult_of_deriv (contDiff_chiN s₀) (C := 1) (fun s => ?_) ?_ k
  · have h0 := Real.smoothTransition.nonneg
      ((Real.exp (-4 * Real.pi * (s₀ + 1 / 2)) - Real.exp (-4 * Real.pi * s)) /
        (Real.exp (-4 * Real.pi * (s₀ + 1 / 2)) - Real.exp (-4 * Real.pi * (s₀ + 1))))
    have h1 := Real.smoothTransition.le_one
      ((Real.exp (-4 * Real.pi * (s₀ + 1 / 2)) - Real.exp (-4 * Real.pi * s)) /
        (Real.exp (-4 * Real.pi * (s₀ + 1 / 2)) - Real.exp (-4 * Real.pi * (s₀ + 1))))
    rw [abs_le]
    exact ⟨by unfold chiN gN; linarith, by unfold chiN gN; linarith⟩
  · refine HasCompactSupport.intro (isCompact_Icc (a := s₀ + 1 / 2) (b := s₀ + 1)) fun s hs => ?_
    rcases not_and_or.1 hs with h | h
    · have e : chiN s₀ =ᶠ[𝓝 s] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds (not_le.1 h)] with y hy using chiN_zero hy.le
      rw [e.deriv_eq, deriv_const]
    · have e : chiN s₀ =ᶠ[𝓝 s] fun _ => 1 := by
        filter_upwards [Ioi_mem_nhds (not_le.1 h)] with y hy using chiN_one hy.le
      rw [e.deriv_eq, deriv_const]

/-! ## 2. The operator -/

section Operator

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} (hT : ChartsOnto X) {q : Q}
  {A : SectionAtlas (E := E) X (fun _ => q)} (hG : GlueCharts A) (F : FormGlueN A)
  (J₀ : E →L[ℝ] E) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

include hT in
lemma FormGlueN.hcG : ∀ o t, ContDiff ℝ ∞ (aG A (fun j => F.ρ j) o t) :=
  fun _ t => contDiff_coef hT (F.ρ t.1) _ _ _ _ (F.hρ t.1) _ _

include hT in
lemma FormGlueN.hsG : ∀ o t, tsupport (aG A (fun j => F.ρ j) o t) ⊆ (F.D o.1 t.1).K :=
  fun o t => by rw [F.hDK]; exact tsupport_coef_sub hT _ _ _ _ _ _ _

include hG hT in
lemma FormGlueN.hsN (i : Fin A.nd) (j : Fin A.nn) (a d : Fin 2)
    (k l : Fin (Module.finrank ℝ E)) : tsupport (cFN A J₀ i j a d k l) ⊆ (F.Dn i j a).K := by
  rw [F.hDnK]; exact tsupport_cFN_sub hG hT J₀ i j a d k l

include hG hT in
lemma FormGlueN.hsD (j : Fin A.nn) (i : Fin A.nd) (a d : Fin 2)
    (k l : Fin (Module.finrank ℝ E)) :
    tsupport (cDN A J₀ j i a (F.ρ i) d k l) ⊆ (F.Dd j i a).K := by
  rw [F.hDdK]; exact tsupport_cDN_sub hG hT J₀ j i a (F.hρn i j) d k l

/-- The disc block `o` of the glued form: the changes of disc charts (`fBlock`) and the neck
blocks carried into the disc. -/
def discOutN (o : Ix A) : (fibreBlocks A δ h0 hmono) 0 →L[ℝ] H 2 (Neck.δ_nonneg δ h0 hmono 0) :=
  fBlock δ h0 hmono (fun o t => F.D o.1 t.1) (aG A (fun j => F.ρ j)) (F.hcG hT) (F.hsG hT)
      (srcG A) 0 o +
    ∑ j, ∑ a, ∑ l, ((F.Dn o.1 j a).op 2 (Neck.δ_nonneg δ h0 hmono 0)
      (contDiff_cFN hG hT J₀ o.1 j a o.2.1 o.2.2 l) (F.hsN hT hG J₀ o.1 j a o.2.1 o.2.2 l)
      (Neck.δ_nonneg δ h0 hmono 0)).comp
        ((Neck.shH (-A.s0 j) (thetaN a)).comp
          ((ContinuousLinearMap.proj (j, l)).comp (ContinuousLinearMap.snd ℝ _ _)))

/-- The neck block `(j, k)` of the projected glued form: `χ_j` times the neck block, and the
disc blocks carried into the neck. -/
def neckOutN (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    (fibreBlocks A δ h0 hmono) 0 →L[ℝ] H 2 (Neck.δ_nonneg δ h0 hmono 0) :=
  (Neck.mulHL (chiN (A.s0 jk.1)) (mult_chiN _ 2)).comp
      ((ContinuousLinearMap.proj jk).comp (ContinuousLinearMap.snd ℝ _ _)) +
    ∑ i, ∑ a, ∑ d, ∑ l, (Neck.shH 0 (thetaN a)).comp
      (((F.Dd jk.1 i a).op 2 (Neck.δ_nonneg δ h0 hmono 0)
        (contDiff_cDN hG hT J₀ jk.1 i a (F.ρ i) (F.hρ i) (F.hρn i jk.1) d jk.2 l)
        (F.hsD hT hG J₀ jk.1 i a d jk.2 l) (Neck.δ_nonneg δ h0 hmono 0)).comp
          ((ContinuousLinearMap.proj (i, d, l)).comp (ContinuousLinearMap.fst ℝ _ _)))

/-- The glued form, read in the blocks. -/
def glueN : (fibreBlocks A δ h0 hmono) 0 →L[ℝ] (fibreBlocks A δ h0 hmono) 0 :=
  (ContinuousLinearMap.pi fun o => discOutN hT hG F J₀ δ h0 hmono o).prod
    (ContinuousLinearMap.pi fun jk => neckOutN hT hG F J₀ δ h0 hmono jk)

/-- The projection on the disc blocks. -/
def projPN : (fibreBlocks A δ h0 hmono) 0 →L[ℝ] (fibreBlocks A δ h0 hmono) 0 :=
  fOp δ h0 hmono (fun _ _ => idCC) (aPI A J₀) (fun _ _ => contDiff_aP hT J₀ _ _ _ _ _ _)
    (fun _ _ => tsupport_aP J₀ _ _ _ _ _ _) (srcP A) 0

/-- **The operator `Φ`**: on the disc blocks `½ (G + P G)`, on the neck blocks `G`. -/
def phiN : (fibreBlocks A δ h0 hmono) 0 →L[ℝ] (fibreBlocks A δ h0 hmono) 0 :=
  ((ContinuousLinearMap.fst ℝ _ _).comp ((1 / 2 : ℝ) • (glueN hT hG F J₀ δ h0 hmono +
      (projPN hT J₀ δ h0 hmono).comp (glueN hT hG F J₀ δ h0 hmono)))).prod
    ((ContinuousLinearMap.snd ℝ _ _).comp (glueN hT hG F J₀ δ h0 hmono))

end Operator

/-! ## 3. The changes of charts, pointwise -/

lemma lamN_ge_half {s₀ : ℝ} {ζ : ℂ} (hζ : ζ ≠ 0) (h : ‖ζ‖ ≤ rN s₀) : 1 / 2 ≤ lamN s₀ ζ := by
  have hπ := Real.pi_pos
  have hl := (Real.log_le_iff_le_exp (norm_pos_iff.2 hζ)).2 h
  unfold lamN
  rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
  linarith

section Pointwise

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} (hT : ChartsOnto X) {q : Q}
  {A : SectionAtlas (E := E) X (fun _ => q)} (hG : GlueCharts A) (F : FormGlueN A)

include hG hT

/-- **The neck blocks carried into the disc `i`**, piece `a`, pointwise: for an anti-linear form
`ξ` on the neck with neck representatives `g`, the result is `β χ_j τ_a · ξ(∂_d)`. -/
theorem neckToDisc_pt (J : AlmostComplexStructure E Q) (i : Fin A.nd) (j : Fin A.nn)
    (a d : Fin 2) (k : Fin (Module.finrank ℝ E)) {ξN : Form E X}
    (hξ : ∀ x : ℝ × ℝ, A.s0 j + 1 / 2 ≤ x.1 →
      ξN (X.polar (A.hol j) x) ∈ X.antiLinearForms J q (X.polar (A.hol j) x))
    {g : Fin (Module.finrank ℝ E) → ℝ × ℝ → ℝ}
    (hg : ∀ l (x : ℝ × ℝ), A.s0 j + 1 / 2 ≤ x.1 → g l x = formNeckRep A j l ξN x)
    (x : ℝ × ℝ) :
    ∑ l, cFN A (J.J q) i j a d k l x *
        g l (Neck.shT (-A.s0 j) (thetaN a) ((F.Dn i j a).ψ x)) =
      discCut x * chiSN (A.hol j) (A.s0 j) (X.discPt (A.center i) (A.ε i) x) *
        tauAng a (wN A i j x) * crd k (formAt (fun _ : X.S => q) (A.center i) ξN
          (X.discPt (A.center i) (A.ε i) x) (EuclideanSpace.single d 1)) := by
  by_cases hK : x ∈ KDn A i j a
  swap
  · have h0 : ∀ l, cFN A (J.J q) i j a d k l x = 0 := fun l =>
      image_eq_zero_of_notMem_tsupport fun h => hK (tsupport_cFN_sub hG hT _ i j a d k l h)
    have h1 : discCut x * chiSN (A.hol j) (A.s0 j) (X.discPt (A.center i) (A.ε i) x) *
        tauAng a (wN A i j x) = 0 := by
      by_contra h; exact hK (mem_KDn_of_ne' h)
    simp [h0, h1]
  have hU := KDn_sub_UDn hG hT i j a hK
  have hw : wN A i j x ≠ 0 :=
    right_ne_zero_of_mul (Complex.slitPlane_ne_zero (show cSgn a * wN A i j x ∈
      Complex.slitPlane from hU.2))
  have hrN : ‖wN A i j x‖ ≤ rN (A.s0 j) :=
    norm_le_of_mem_zSet (hG.target j) (tsupport_chiSN_sub (hG.smooth_symm j).continuous hK.2.1)
  set y := fDn A i j a x with hy
  have hψ : (F.Dn i j a).ψ x = y := F.hDnψ i j a x ((F.hDnK i j a).symm ▸ hK)
  have hy1 : 1 / 2 ≤ y.1 := by rw [hy, fDn_fst hG]; exact lamN_ge_half hw hrN
  set x0 : ℝ × ℝ := (y.1 + A.s0 j, y.2 + -thetaN a) with hx0
  obtain ⟨n, hn⟩ := Neck.rot_int (thetaN a) y.2
  have hx' : Neck.shT (-A.s0 j) (thetaN a) y = (x0.1, x0.2 + n) := by
    simp only [Neck.shT, hn, hx0, sub_neg_eq_add]; ext <;> simp; ring
  have hpol : X.polar (A.hol j) (x0.1, x0.2 + n) = X.polar (A.hol j) x0 :=
    polar_add_int (A.hol j) _ _ n
  have hmf := mfderiv_polar_add_int hG j x0.1 x0.2 n
  have hY : X.polar (A.hol j) x0 = X.discPt (A.center i) (A.ε i) x := polarSh_fDn hG a hU.1 hw
  set F0 := ξN (X.polar (A.hol j) x0)
    (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) x0 (1, 0)) with hF0
  have hgl : ∀ l, g l (Neck.shT (-A.s0 j) (thetaN a) y) =
      Real.smoothTransition y.1 * crd l F0 := by
    intro l
    rw [hx', hg l _ (by simp only [hx0]; linarith), formNeckRep]
    simp only [NodalSurface.formInPolar, tcc_const]
    rw [hpol, hmf]
    congr 2
    simp [hx0]
  have hdt := antiJ_dt hG J j x0 (hξ x0 (by simp only [hx0]; linarith))
  have hfa := formAt_eq_polar hG hT a hU ξN d
  set u := fderiv ℝ (fDn A i j a) x (dir2 d) with hu
  have hu' : u = u.1 • ((1 : ℝ), (0 : ℝ)) + u.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  have hval : crd k (formAt (fun _ : X.S => q) (A.center i) ξN
      (X.discPt (A.center i) (A.ε i) x) (EuclideanSpace.single d 1)) =
      (A.ε i)⁻¹ * (u.1 * crd k F0 - u.2 * ∑ l, Jm (J.J q) k l * crd l F0) := by
    rw [hfa, ← hY, ← hy, ← hx0]
    have hlin : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) x0 u =
        u.1 • mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) x0 ((1 : ℝ), (0 : ℝ)) +
          u.2 • mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) x0 ((0 : ℝ), (1 : ℝ)) := by
      let L : ℝ × ℝ →L[ℝ] E2 := mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) x0
      change L u = u.1 • L (1, 0) + u.2 • L (0, 1)
      conv_lhs => rw [hu']
      rw [L.map_add, L.map_smul, L.map_smul]
    rw [hlin]
    let M : E2 →L[ℝ] E := ξN (X.polar (A.hol j) x0)
    let L : ℝ × ℝ →L[ℝ] E2 := mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) x0
    have h10 : M (L (1, 0)) = F0 := rfl
    have h01 : M (L (0, 1)) = -(J.J q) F0 := hdt
    change crd k ((A.ε i)⁻¹ • M (u.1 • L (1, 0) + u.2 • L (0, 1))) = _
    rw [M.map_add, M.map_smul, M.map_smul, h10, h01]
    simp only [map_smul, map_add, map_neg, smul_eq_mul, crd_J]
    ring
  rw [hval, hψ]
  have hb := bNf_mul hG hT (F.hDnK i j a) (F.hDnψ i j a) x
  rw [hψ] at hb
  have e1 : ∀ l, cFN A (J.J q) i j a d k l x * g l (Neck.shT (-A.s0 j) (thetaN a) y) =
      (bNf A i j a x * Real.smoothTransition y.1) * (mNf A (J.J q) i j a d k l x * crd l F0) := by
    intro l; rw [hgl, cFN, smul_eq_mul]; ring
  rw [Finset.sum_congr rfl fun l _ => e1 l, ← Finset.mul_sum, hb]
  have e2 : ∑ l, mNf A (J.J q) i j a d k l x * crd l F0 =
      (A.ε i)⁻¹ * (u.1 * crd k F0 - u.2 * ∑ l, Jm (J.J q) k l * crd l F0) := by
    simp only [mNf, ← hu]
    have : ∀ l, (A.ε i)⁻¹ * ((if k = l then u.1 else 0) - Jm (J.J q) k l * u.2) * crd l F0 =
        (A.ε i)⁻¹ * ((if k = l then u.1 * crd l F0 else 0) -
          u.2 * (Jm (J.J q) k l * crd l F0)) := fun l => by split_ifs <;> ring
    rw [Finset.sum_congr rfl fun l _ => this l, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_ite_eq, if_pos (Finset.mem_univ _), ← Finset.mul_sum]
  rw [e2]

/-- **The disc blocks carried into the neck `j`**, piece `a`, pointwise: for a form `ξ` on the
disc `i` with disc representatives `f`, the result is
`nDf · ½ (ξ(∂_s σ) + J₀ ξ(∂_t σ))`. -/
theorem discToNeck_pt (J₀ : E →L[ℝ] E) (j : Fin A.nn) (i : Fin A.nd) (a : Fin 2)
    (k : Fin (Module.finrank ℝ E)) (ξs : Form E X)
    {f : Fin 2 → Fin (Module.finrank ℝ E) → ℝ × ℝ → ℝ}
    (hf : ∀ d l p, discCut p ≠ 0 → f d l p = formDiscRep A i d l ξs p) (x : ℝ × ℝ) :
    ∑ d, ∑ l, cDN A J₀ j i a (F.ρ i) d k l (Neck.shT 0 (thetaN a) x) *
        f d l ((F.Dd j i a).ψ (Neck.shT 0 (thetaN a) x)) =
      nDf A j a (F.ρ i) (Neck.shT 0 (thetaN a) x) * ((1 / 2 : ℝ) *
        (crd k (ξs (X.polar (A.hol j) x)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) x (1, 0))) +
          crd k (J₀ (ξs (X.polar (A.hol j) x)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) x (0, 1)))))) := by
  set z := Neck.shT 0 (thetaN a) x with hz
  by_cases hK : z ∈ KDd A j a (F.ρ i)
  swap
  · have h0 : ∀ d l, cDN A J₀ j i a (F.ρ i) d k l z = 0 := fun d l =>
      image_eq_zero_of_notMem_tsupport fun h =>
        hK (tsupport_cDN_sub hG hT J₀ j i a (F.hρn i j) d k l h)
    have h1 : nDf A j a (F.ρ i) z = 0 := by
      by_contra h; exact hK (mem_KDd_of_ne' (F.hρn i j) h)
    simp [h0, h1]
  have hzd := F.hρ i hK.2
  have hsrc : polarSh A j 0 (thetaN a) z ∈ (extChartAt 𝓘(ℝ, E2) (A.center i)).source := hzd.1
  have hψ : (F.Dd j i a).ψ z = fDd A j i a z := F.hDdψ j i a z ((F.hDdK j i a).symm ▸ hK)
  have hdp : discCut (fDd A j i a z) ≠ 0 := (discCut_pos hzd.2).ne'
  have hdisc : X.discPt (A.center i) (A.ε i) (fDd A j i a z) = polarSh A j 0 (thetaN a) z :=
    discPt_fDd hG a hsrc
  have hpol : polarSh A j 0 (thetaN a) z = X.polar (A.hol j) x := polarSh_shT hG j a x
  obtain ⟨n, hn⟩ := Neck.rot_int (thetaN a) x.2
  have hmf : ∀ w, mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (polarSh A j 0 (thetaN a)) z w =
      mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) x w := by
    intro w
    rw [mfderiv_polarSh hG]
    have e : ((z.1 + 0, z.2 + thetaN a) : ℝ × ℝ) = (x.1, x.2 + n) := by
      simp only [hz, Neck.shT, sub_zero, add_zero, hn]; ext <;> simp; ring
    rw [e, mfderiv_polar_add_int hG]
    rfl
  have hpe : ∀ w : ℝ × ℝ, ξs (X.polar (A.hol j) x)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) x w) = ∑ d,
        (fderiv ℝ (fun z => extChartAt 𝓘(ℝ, E2) (A.center i) (polarSh A j 0 (thetaN a) z)) z w) d •
          formAt (fun _ : X.S => q) (A.center i) ξs (X.polar (A.hol j) x)
            (EuclideanSpace.single d 1) := by
    intro w
    have h := polar_eq_formAt (q := q) hG hT i j 0 (thetaN a) hsrc ξs w
    rw [hmf w, hpol] at h
    exact h
  have hb := bDf_mul hG hT (F.hρ i) (F.hρn i j) (F.hDdK j i a) (F.hDdψ j i a) z
  rw [hψ] at hb
  set c := fun d : Fin 2 => fun l : Fin (Module.finrank ℝ E) =>
    crd l (formAt (fun _ : X.S => q) (A.center i) ξs (X.polar (A.hol j) x)
      (EuclideanSpace.single d 1)) with hc
  have hfv : ∀ d l, f d l ((F.Dd j i a).ψ z) = discCut (fDd A j i a z) * c d l := by
    intro d l
    rw [hψ, hf d l _ hdp, formDiscRep, hdisc, hpol]
  have e1 : ∀ d l, cDN A J₀ j i a (F.ρ i) d k l z * f d l ((F.Dd j i a).ψ z) =
      (bDf A j i a (F.ρ i) z * discCut (fDd A j i a z)) *
        (mDf A J₀ j i a d k l z * c d l) := by
    intro d l; rw [hfv, cDN, smul_eq_mul]; ring
  simp only [Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun l _ => e1 d l,
    ← Finset.mul_sum, hb]
  congr 1
  have hs : ∀ w, crd k (ξs (X.polar (A.hol j) x)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) x w)) =
        ∑ d, (jDf A i j a w z) d * c d k := by
    intro w
    rw [hpe w]
    simp only [map_sum, map_smul, smul_eq_mul, hc, jDf]
  have hs' : ∀ w, crd k (J₀ (ξs (X.polar (A.hol j) x)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) x w))) =
        ∑ l, Jm J₀ k l * ∑ d, (jDf A i j a w z) d * c d l := by
    intro w
    rw [crd_J]
    refine Finset.sum_congr rfl fun l _ => ?_
    congr 1
    rw [hpe w]
    simp only [map_sum, map_smul, smul_eq_mul, hc, jDf]
  erw [hs (1, 0), hs' (0, 1)]
  simp only [mDf]
  have e2 : ∀ d, ∑ l, (1 / 2 : ℝ) * ((if k = l then jDf A i j a (1, 0) z d else 0) +
      Jm J₀ k l * jDf A i j a (0, 1) z d) * c d l =
      (1 / 2 : ℝ) * (jDf A i j a (1, 0) z d * c d k +
        ∑ l, Jm J₀ k l * (jDf A i j a (0, 1) z d * c d l)) := by
    intro d
    have : ∀ l, (1 / 2 : ℝ) * ((if k = l then jDf A i j a (1, 0) z d else 0) +
        Jm J₀ k l * jDf A i j a (0, 1) z d) * c d l =
        (1 / 2 : ℝ) * ((if k = l then jDf A i j a (1, 0) z d * c d l else 0) +
          Jm J₀ k l * (jDf A i j a (0, 1) z d * c d l)) := fun l => by split_ifs <;> ring
    rw [Finset.sum_congr rfl fun l _ => this l, ← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  rw [Finset.sum_congr rfl fun d _ => e2 d, ← Finset.mul_sum, Finset.sum_add_distrib]
  congr 2
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => by rw [Finset.mul_sum]

end Pointwise

end GWMemoir
