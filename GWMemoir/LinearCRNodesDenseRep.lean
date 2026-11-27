import GWMemoir.LinearCRNodesDenseOp

/-!
# The gluing operator with necks represents the anti-linear part of the glued form

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §1.2 (p. 7), §2.4 (p. 51),
at a constant map, on an atlas satisfying `GlueCharts`.

* `glueForm F ξs ξN = ∑ ρ_i ξs_i + ∑ χ_j ξN_j`; `IsGlueRep J v ξs ξN`: the disc blocks of `v`
  agree with the representatives of `ξs_i` where the cut-off does not vanish, and the neck blocks
  with those of `ξN_j` for `s ≥ s₀ + ½`, where `ξN_j` is anti-linear.
* **`isFormRep_phiN`**: then `Φ v` represents `projF J(q) (glueForm F ξs ξN)`.
* **`phiN_eq_self`**: when the polar coordinates avoid the nodal points, `Φ` is the identity on the
  representatives of the forms anti-linear off the nodes, hence the fibre (`phiN_eq_self_fibre`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

lemma coeFn_sum3H {k : ℕ} {d : ℝ} {hd : 0 ≤ d} {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂]
    [Fintype ι₃] (f : ι₁ → ι₂ → ι₃ → H k hd) :
    (H.val (∑ a, ∑ b, ∑ c, f a b c) : ℝ × ℝ → ℝ) =ᵐ[cyl]
      fun x => ∑ a, ∑ b, ∑ c, H.val (f a b c) x := by
  have e : (∑ a, ∑ b, ∑ c, f a b c) = ∑ p : ι₁ × ι₂ × ι₃, f p.1 p.2.1 p.2.2 := by
    simp only [Fintype.sum_prod_type]
  filter_upwards [coeFn_sumH Finset.univ fun p : ι₁ × ι₂ × ι₃ => f p.1 p.2.1 p.2.2] with x hx
  rw [e, hx]; simp only [Fintype.sum_prod_type]

lemma coeFn_sum4H {k : ℕ} {d : ℝ} {hd : 0 ≤ d} {ι₁ ι₂ ι₃ ι₄ : Type*} [Fintype ι₁] [Fintype ι₂]
    [Fintype ι₃] [Fintype ι₄] (f : ι₁ → ι₂ → ι₃ → ι₄ → H k hd) :
    (H.val (∑ a, ∑ b, ∑ c, ∑ e, f a b c e) : ℝ × ℝ → ℝ) =ᵐ[cyl]
      fun x => ∑ a, ∑ b, ∑ c, ∑ e, H.val (f a b c e) x := by
  have e : (∑ a, ∑ b, ∑ c, ∑ e, f a b c e) =
      ∑ p : ι₁ × ι₂ × ι₃ × ι₄, f p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    simp only [Fintype.sum_prod_type]
  filter_upwards [coeFn_sumH Finset.univ
    fun p : ι₁ × ι₂ × ι₃ × ι₄ => f p.1 p.2.1 p.2.2.1 p.2.2.2] with x hx
  rw [e, hx]; simp only [Fintype.sum_prod_type]

section Rep

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} (hT : ChartsOnto X) {q : Q}
  {A : SectionAtlas (E := E) X (fun _ => q)} (hG : GlueCharts A) (F : FormGlueN A)
  (J : AlmostComplexStructure E Q) {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}

lemma formDiscRep_fsum {ι : Type*} [Fintype ι] (c : ι → X.S → ℝ) (ξ : ι → Form E X)
    (i : Fin A.nd) (d : Fin 2) (k : Fin (Module.finrank ℝ E)) (x : ℝ × ℝ) :
    formDiscRep A i d k (fun y => ∑ j, c j y • ξ j y) x =
      ∑ j, c j (X.discPt (A.center i) (A.ε i) x) * formDiscRep A i d k (ξ j) x := by
  simp only [formDiscRep, formAt_of_const (fun _ => rfl), ContinuousLinearMap.comp_apply,
    FunLike.coe_sum, Finset.sum_apply, smul_apply, map_sum,
    map_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma neck_val (k : Fin (Module.finrank ℝ E)) (L : E2 →L[ℝ] E) (J₀ : E →L[ℝ] E)
    (jY : E2 →L[ℝ] E2) (ds dt : E2) (hj : jY ds = dt) :
    crd k (((1 / 2 : ℝ) • (L + J₀.comp (L.comp jY))) ds) =
      (1 / 2 : ℝ) * (crd k (L ds) + crd k (J₀ (L dt))) := by
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, hj, map_smul, map_add, smul_eq_mul]

lemma alg_glue {ι : Type*} [Fintype ι] (β c u w : ℝ) (r a b : ι → ℝ) :
    β * ((1 / 2 : ℝ) * (c * u + c * w)) + ∑ i, β * r i * ((1 / 2 : ℝ) * (a i + b i)) =
      β * ((1 / 2 : ℝ) * ((∑ i, r i * a i + c * u) + (∑ i, r i * b i + c * w))) := by
  have e : ∑ i, β * r i * ((1 / 2 : ℝ) * (a i + b i)) =
      β * ((1 / 2 : ℝ) * (∑ i, r i * a i + ∑ i, r i * b i)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]; ring

/-- The glued form `∑ ρ_i ξs_i + ∑ χ_j ξN_j`. -/
def glueForm (ξs : Fin A.nd → Form E X) (ξN : Fin A.nn → Form E X) : Form E X :=
  fun y => ∑ i, F.ρ i y • ξs i y + ∑ j, chiSN (A.hol j) (A.s0 j) y • ξN j y

/-- The blocks of `v` read as forms: the disc blocks agree with the representatives of `ξs_i`
where the cut-off does not vanish, the neck blocks with those of `ξN_j` for `s ≥ s₀ + ½`, where
`ξN_j` is anti-linear. -/
def IsGlueRep (v : (fibreBlocks A δ h0 hmono) 0) (ξs : Fin A.nd → Form E X)
    (ξN : Fin A.nn → Form E X) : Prop :=
  (∀ i d k, ∃ f : ℝ × ℝ → ℝ, (H.val (v.1 (i, d, k)) : ℝ × ℝ → ℝ) =ᵐ[cyl] f ∧
      ∀ p, discCut p ≠ 0 → f p = formDiscRep A i d k (ξs i) p) ∧
    (∀ j k, ∃ g : ℝ × ℝ → ℝ, (H.val (v.2 (j, k)) : ℝ × ℝ → ℝ) =ᵐ[cyl] g ∧
      ∀ x : ℝ × ℝ, A.s0 j + 1 / 2 ≤ x.1 → g x = formNeckRep A j k (ξN j) x) ∧
    ∀ j (x : ℝ × ℝ), A.s0 j + 1 / 2 ≤ x.1 →
      ξN j (X.polar (A.hol j) x) ∈ X.antiLinearForms J q (X.polar (A.hol j) x)

include hT hG

/-- **The disc blocks of the glued tuple** represent the glued form. -/
theorem disc_glueN {v : (fibreBlocks A δ h0 hmono) 0} {ξs : Fin A.nd → Form E X}
    {ξN : Fin A.nn → Form E X} (hv : IsGlueRep J v ξs ξN) (o : Ix A) :
    (H.val ((glueN hT hG F (J.J q) δ h0 hmono v).1 o) : ℝ × ℝ → ℝ) =ᵐ[cyl]
      formDiscRep A o.1 o.2.1 o.2.2 (glueForm F ξs ξN) := by
  obtain ⟨hd, hn, ha⟩ := hv
  choose f hf hf' using hd
  choose g hg hg' using hn
  have h1 : (H.val (fBlock δ h0 hmono (fun o t => F.D o.1 t.1) (aG A (fun j => F.ρ j))
      (F.hcG hT) (F.hsG hT) (srcG A) 0 o v) : ℝ × ℝ → ℝ) =ᵐ[cyl]
        fun x => ∑ i, F.ρ i (X.discPt (A.center o.1) (A.ε o.1) x) *
          formDiscRep A o.1 o.2.1 o.2.2 (ξs i) x := by
    refine G_ae hT (fun _ => rfl) F.hρ F.hDK F.hDψ (F.hcG hT) (F.hsG hT) ξs
      (fun o t => ?_) o
    refine (ChartChange.comp_congr (F.hsG hT o t) (hf t.1 t.2 o.2.2)).trans
      (Eventually.of_forall fun x => ?_)
    change aG A (fun j => F.ρ j) o t x * f t.1 t.2 o.2.2 ((F.D o.1 t.1).ψ x) =
      aG A (fun j => F.ρ j) o t x * formDiscRep A t.1 t.2 o.2.2 (ξs t.1) ((F.D o.1 t.1).ψ x)
    by_cases hx : aG A (fun j => F.ρ j) o t x = 0
    · rw [hx, zero_mul, zero_mul]
    have hxK : x ∈ pieceK (F.ρ t.1) (A.center o.1) (A.ε o.1) :=
      tsupport_coef_sub hT _ _ _ _ _ _ _ (subset_tsupport _ hx)
    have hxD := pieceK_sub (F.hρ t.1) hxK
    rw [F.hDψ o.1 t.1 x ((F.hDK o.1 t.1).symm ▸ hxK),
      hf' _ _ _ _ (discCut_pos (pieceDom_sub hxD).2).ne']
  have h2 : ∀ j a l, (H.val (((F.Dn o.1 j a).op 2 (Neck.δ_nonneg δ h0 hmono 0)
      (contDiff_cFN hG hT (J.J q) o.1 j a o.2.1 o.2.2 l)
      (F.hsN hT hG (J.J q) o.1 j a o.2.1 o.2.2 l) (Neck.δ_nonneg δ h0 hmono 0))
        (Neck.shH (-A.s0 j) (thetaN a) (v.2 (j, l)))) : ℝ × ℝ → ℝ) =ᵐ[cyl]
      fun x => cFN A (J.J q) o.1 j a o.2.1 o.2.2 l x *
        g j l (Neck.shT (-A.s0 j) (thetaN a) ((F.Dn o.1 j a).ψ x)) := by
    intro j a l
    refine (ChartChange.coeFn_op _ _ _ _).trans
      (ChartChange.comp_congr (F.hsN hT hG (J.J q) o.1 j a o.2.1 o.2.2 l)
        (f' := fun y => g j l (Neck.shT (-A.s0 j) (thetaN a) y)) ?_)
    exact (Neck.val_shH _ _ _).trans
      ((Neck.measurePreserving_shT _ _).quasiMeasurePreserving.ae_eq_comp (hg j l))
  have e : (glueN hT hG F (J.J q) δ h0 hmono v).1 o =
      fBlock δ h0 hmono (fun o t => F.D o.1 t.1) (aG A (fun j => F.ρ j))
        (F.hcG hT) (F.hsG hT) (srcG A) 0 o v +
      ∑ j, ∑ a, ∑ l, ((F.Dn o.1 j a).op 2 (Neck.δ_nonneg δ h0 hmono 0)
        (contDiff_cFN hG hT (J.J q) o.1 j a o.2.1 o.2.2 l)
        (F.hsN hT hG (J.J q) o.1 j a o.2.1 o.2.2 l) (Neck.δ_nonneg δ h0 hmono 0))
          (Neck.shH (-A.s0 j) (thetaN a) (v.2 (j, l))) := by
    change discOutN hT hG F (J.J q) δ h0 hmono o v = _
    simp only [discOutN, add_apply, FunLike.coe_sum,
      Finset.sum_apply]
    rfl
  rw [e]
  filter_upwards [val_add_ae _ _, h1, coeFn_sum3H fun j a l =>
      ((F.Dn o.1 j a).op 2 (Neck.δ_nonneg δ h0 hmono 0)
        (contDiff_cFN hG hT (J.J q) o.1 j a o.2.1 o.2.2 l)
        (F.hsN hT hG (J.J q) o.1 j a o.2.1 o.2.2 l) (Neck.δ_nonneg δ h0 hmono 0))
          (Neck.shH (-A.s0 j) (thetaN a) (v.2 (j, l))),
    ae_all_iff.2 fun j => ae_all_iff.2 fun a => ae_all_iff.2 fun l => h2 j a l]
    with x e1 e2 e3 e4
  rw [e1, e2, e3]
  simp only [e4]
  have hN : ∀ j, ∑ a, ∑ l, cFN A (J.J q) o.1 j a o.2.1 o.2.2 l x *
      g j l (Neck.shT (-A.s0 j) (thetaN a) ((F.Dn o.1 j a).ψ x)) =
        chiSN (A.hol j) (A.s0 j) (X.discPt (A.center o.1) (A.ε o.1) x) *
          formDiscRep A o.1 o.2.1 o.2.2 (ξN j) x := by
    intro j
    rw [Finset.sum_congr rfl fun a _ =>
      neckToDisc_pt hT hG F J o.1 j a o.2.1 o.2.2 (ha j) (hg' j) x]
    have : ∀ a : Fin 2, discCut x * chiSN (A.hol j) (A.s0 j)
        (X.discPt (A.center o.1) (A.ε o.1) x) * tauAng a (wN A o.1 j x) *
          crd o.2.2 (formAt (fun _ : X.S => q) (A.center o.1) (ξN j)
            (X.discPt (A.center o.1) (A.ε o.1) x) (EuclideanSpace.single o.2.1 1)) =
        (chiSN (A.hol j) (A.s0 j) (X.discPt (A.center o.1) (A.ε o.1) x) *
          formDiscRep A o.1 o.2.1 o.2.2 (ξN j) x) * tauAng a (wN A o.1 j x) := fun a => by
      simp only [formDiscRep]; ring
    rw [Finset.sum_congr rfl fun a _ => this a, ← Finset.mul_sum, sum_tauW, mul_one]
  rw [Finset.sum_congr rfl fun j _ => hN j]
  rw [show glueForm F ξs ξN = (fun y => ∑ i, F.ρ i y • ξs i y) +
      fun y => ∑ j, chiSN (A.hol j) (A.s0 j) y • ξN j y from rfl, formDiscRep_add,
    Pi.add_apply, formDiscRep_fsum, formDiscRep_fsum]

lemma sum_nDf (j : Fin A.nn) (ρ : X.S → ℝ) (x : ℝ × ℝ) :
    ∑ a, nDf A j a ρ (Neck.shT 0 (thetaN a) x) =
      Real.smoothTransition (x.1 - A.s0 j) * ρ (X.polar (A.hol j) x) := by
  have e : ∀ a, nDf A j a ρ (Neck.shT 0 (thetaN a) x) =
      (Real.smoothTransition (x.1 - A.s0 j) * ρ (X.polar (A.hol j) x)) *
        (cutT (Neck.rot (thetaN a) x.2) * tauT a (Neck.rot (thetaN a) x.2 + thetaN a)) := by
    intro a
    rw [nDf, polarSh_shT hG j a x]
    simp only [Neck.shT, sub_zero]
    ring
  rw [Finset.sum_congr rfl fun a _ => e a, ← Finset.mul_sum, sum_cutT_tauT, mul_one]

/-- `j ∂_s σ = ∂_t σ` in the polar coordinates of a neck chart. -/
lemma j_ds (j : Fin A.nn) (x : ℝ × ℝ) :
    X.j.J (X.polar (A.hol j) x) (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) x (1, 0)) =
      mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) x (0, 1) := by
  have hp : expPolar x ∈ (A.hol j).target := by rw [hG.target j]; trivial
  exact (polar_deriv (A.isHol j) hp ((hG.smooth_symm j _).mdifferentiableAt (by simp))).2.symm

/-- **The neck blocks of the glued tuple** represent the anti-linear part of the glued form. -/
theorem neck_glueN {v : (fibreBlocks A δ h0 hmono) 0} {ξs : Fin A.nd → Form E X}
    {ξN : Fin A.nn → Form E X} (hv : IsGlueRep J v ξs ξN)
    (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    (H.val ((glueN hT hG F (J.J q) δ h0 hmono v).2 jk) : ℝ × ℝ → ℝ) =ᵐ[cyl]
      formNeckRep A jk.1 jk.2 (projF (J.J q) (glueForm F ξs ξN)) := by
  obtain ⟨j, k⟩ := jk
  obtain ⟨hd, hn, ha⟩ := hv
  choose f hf hf' using hd
  choose g hg hg' using hn
  have h1 : (H.val ((Neck.mulHL (chiN (A.s0 j)) (mult_chiN _ 2)) (v.2 (j, k))) :
      ℝ × ℝ → ℝ) =ᵐ[cyl] fun x => chiN (A.s0 j) x.1 * g j k x := by
    filter_upwards [Neck.val_mulHL (chiN (A.s0 j)) (mult_chiN _ 2) (v.2 (j, k)), hg j k]
      with x e1 e2
    rw [← e2]; exact e1
  have h2 : ∀ i a d l, (H.val (Neck.shH 0 (thetaN a) (((F.Dd j i a).op 2
      (Neck.δ_nonneg δ h0 hmono 0)
      (contDiff_cDN hG hT (J.J q) j i a (F.ρ i) (F.hρ i) (F.hρn i j) d k l)
      (F.hsD hT hG (J.J q) j i a d k l) (Neck.δ_nonneg δ h0 hmono 0)) (v.1 (i, d, l)))) :
        ℝ × ℝ → ℝ) =ᵐ[cyl] fun x => cDN A (J.J q) j i a (F.ρ i) d k l
          (Neck.shT 0 (thetaN a) x) * f i d l ((F.Dd j i a).ψ (Neck.shT 0 (thetaN a) x)) := by
    intro i a d l
    exact (Neck.val_shH _ _ _).trans
      ((Neck.measurePreserving_shT _ _).quasiMeasurePreserving.ae_eq_comp
        ((ChartChange.coeFn_op
            (contDiff_cDN hG hT (J.J q) j i a (F.ρ i) (F.hρ i) (F.hρn i j) d k l)
            (F.hsD hT hG (J.J q) j i a d k l) (Neck.δ_nonneg δ h0 hmono 0) (v.1 (i, d, l))).trans
          (ChartChange.comp_congr (F.hsD hT hG (J.J q) j i a d k l) (hf i d l))))
  have e : (glueN hT hG F (J.J q) δ h0 hmono v).2 (j, k) =
      (Neck.mulHL (chiN (A.s0 j)) (mult_chiN _ 2)) (v.2 (j, k)) +
      ∑ i, ∑ a, ∑ d, ∑ l, Neck.shH 0 (thetaN a) (((F.Dd j i a).op 2
        (Neck.δ_nonneg δ h0 hmono 0)
        (contDiff_cDN hG hT (J.J q) j i a (F.ρ i) (F.hρ i) (F.hρn i j) d k l)
        (F.hsD hT hG (J.J q) j i a d k l) (Neck.δ_nonneg δ h0 hmono 0)) (v.1 (i, d, l))) := by
    change neckOutN hT hG F (J.J q) δ h0 hmono (j, k) v = _
    simp only [neckOutN, add_apply, FunLike.coe_sum,
      Finset.sum_apply]
    rfl
  rw [e]
  filter_upwards [val_add_ae _ _, h1, coeFn_sum4H fun i a d l =>
      Neck.shH 0 (thetaN a) (((F.Dd j i a).op 2 (Neck.δ_nonneg δ h0 hmono 0)
        (contDiff_cDN hG hT (J.J q) j i a (F.ρ i) (F.hρ i) (F.hρn i j) d k l)
        (F.hsD hT hG (J.J q) j i a d k l) (Neck.δ_nonneg δ h0 hmono 0)) (v.1 (i, d, l))),
    ae_all_iff.2 fun i => ae_all_iff.2 fun a => ae_all_iff.2 fun d => ae_all_iff.2 fun l =>
      h2 i a d l] with x e1 e2 e3 e4
  rw [e1, e2, e3]
  simp only [e4]
  set Y := X.polar (A.hol j) x with hY
  set ds : E2 := mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) x (1, 0) with hds
  set dt : E2 := mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) x (0, 1) with hdt
  have hD : ∀ i, ∑ a, ∑ d, ∑ l, cDN A (J.J q) j i a (F.ρ i) d k l (Neck.shT 0 (thetaN a) x) *
      f i d l ((F.Dd j i a).ψ (Neck.shT 0 (thetaN a) x)) =
        Real.smoothTransition (x.1 - A.s0 j) * F.ρ i Y *
          ((1 / 2 : ℝ) * (crd k (ξs i Y ds) + crd k (J.J q (ξs i Y dt)))) := by
    intro i
    rw [Finset.sum_congr rfl fun a _ =>
      discToNeck_pt hT hG F (J.J q) j i a k (ξs i) (hf' i) x, ← Finset.sum_mul, sum_nDf hT hG]
  rw [Finset.sum_congr rfl fun i _ => hD i]
  -- the glued form along the neck
  have hΞ : ∀ w, glueForm F ξs ξN Y w =
      ∑ i, F.ρ i Y • ξs i Y w + chiN (A.s0 j) x.1 • ξN j Y w := by
    intro w
    simp only [glueForm, add_apply, FunLike.coe_sum,
      Finset.sum_apply, smul_apply, hY, chiSN_polar_cross hG j, ite_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hR : formNeckRep A j k (projF (J.J q) (glueForm F ξs ξN)) x =
      Real.smoothTransition (x.1 - A.s0 j) * ((1 / 2 : ℝ) *
        ((∑ i, F.ρ i Y * crd k (ξs i Y ds) + chiN (A.s0 j) x.1 * crd k (ξN j Y ds)) +
          (∑ i, F.ρ i Y * crd k (J.J q (ξs i Y dt)) +
            chiN (A.s0 j) x.1 * crd k (J.J q (ξN j Y dt))))) := by
    have h := neck_val k (glueForm F ξs ξN Y) (J.J q) (X.j.J Y) ds dt (j_ds hT hG j x)
    rw [hΞ, hΞ] at h
    simp only [map_add, map_sum, map_smul, smul_eq_mul] at h
    refine Eq.trans ?_ (congrArg (Real.smoothTransition (x.1 - A.s0 j) * ·) h)
    simp only [formNeckRep, NodalSurface.formInPolar, tcc_const]
    rfl
  rw [hR]
  have hN : chiN (A.s0 j) x.1 * g j k x = Real.smoothTransition (x.1 - A.s0 j) *
      ((1 / 2 : ℝ) * (chiN (A.s0 j) x.1 * crd k (ξN j Y ds) +
        chiN (A.s0 j) x.1 * crd k (J.J q (ξN j Y dt)))) := by
    by_cases hx : x.1 ≤ A.s0 j + 1 / 2
    · rw [chiN_zero hx]; ring
    have hx' : A.s0 j + 1 / 2 ≤ x.1 := (not_le.1 hx).le
    have hat := antiJ_dt hG J j x (ha j x hx')
    rw [← hY, ← hds, ← hdt] at hat
    have hJJ : J.J q (J.J q (ξN j Y ds)) = -ξN j Y ds := by
      have := congrArg (fun L : E →L[ℝ] E => L (ξN j Y ds)) (J.sq q)
      simpa using this
    rw [hg' j k x hx', hat, map_neg, hJJ, neg_neg]
    simp only [formNeckRep, NodalSurface.formInPolar, tcc_const]
    rw [← hY, ← hds]
    ring
  rw [hN]
  exact alg_glue _ _ _ _ (fun i => F.ρ i Y) (fun i => crd k (ξs i Y ds))
    (fun i => crd k (J.J q (ξs i Y dt)))

lemma val_half_add {hd : 0 ≤ δ 0} {a b : H 2 hd} {fa fb : ℝ × ℝ → ℝ}
    (ha : (H.val a : ℝ × ℝ → ℝ) =ᵐ[cyl] fa) (hb : (H.val b : ℝ × ℝ → ℝ) =ᵐ[cyl] fb) :
    (H.val ((1 / 2 : ℝ) • (a + b)) : ℝ × ℝ → ℝ) =ᵐ[cyl] (1 / 2 : ℝ) • (fa + fb) := by
  filter_upwards [val_smul_ae (1 / 2 : ℝ) (a + b), val_add_ae a b, ha, hb] with x e1 e2 e3 e4
  rw [e1, e2, e3, e4]; rfl

omit hG in
/-- The projection on the disc blocks represents `J₀ ∘ ξ ∘ j` in the discs. -/
lemma proj_disc {w : (fibreBlocks A δ h0 hmono) 0} {ξ : Form E X}
    (hw : ∀ o : Ix A, (H.val (w.1 o) : ℝ × ℝ → ℝ) =ᵐ[cyl] formDiscRep A o.1 o.2.1 o.2.2 ξ)
    (o : Ix A) :
    (H.val ((projPN hT (J.J q) δ h0 hmono w).1 o) : ℝ × ℝ → ℝ) =ᵐ[cyl]
      formDiscRep A o.1 o.2.1 o.2.2 (twist (J.J q) ξ) := by
  filter_upwards [coeFn_fOp (fun _ _ => idCC) (aPI A (J.J q)) _ _ (srcP A) w o,
    ae_all_iff.2 fun t : Fin 2 × Fin (Module.finrank ℝ E) => hw (o.1, t.1, t.2)] with x h1 h2
  refine h1.trans ?_
  rw [formDiscRep_twist hT (fun _ => rfl) A]
  exact Finset.sum_congr rfl fun t _ => congrArg (aPI A (J.J q) o t x * ·) (h2 t)

/-- **`Φ` represents the anti-linear part of the glued form.** -/
theorem isFormRep_phiN {v : (fibreBlocks A δ h0 hmono) 0} {ξs : Fin A.nd → Form E X}
    {ξN : Fin A.nn → Form E X} (hv : IsGlueRep J v ξs ξN) :
    IsFormRep (projF (J.J q) (glueForm F ξs ξN)) (phiN hT hG F (J.J q) δ h0 hmono v) := by
  refine ⟨fun i d k => ?_, fun j k => neck_glueN hT hG F J hv (j, k)⟩
  have e : fDiscBlock (phiN hT hG F (J.J q) δ h0 hmono v) i d k =
      (1 / 2 : ℝ) • ((glueN hT hG F (J.J q) δ h0 hmono v).1 (i, d, k) +
        (projPN hT (J.J q) δ h0 hmono (glueN hT hG F (J.J q) δ h0 hmono v)).1 (i, d, k)) := rfl
  rw [e, projF, formDiscRep_smul, formDiscRep_add]
  exact val_half_add hT hG (disc_glueN hT hG F J hv (i, d, k))
    (proj_disc hT J (disc_glueN hT hG F J hv) (i, d, k))

end Rep

/-! ## The identity on the fibre -/

section Ident

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} (hT : ChartsOnto X) {q : Q}
  {A : SectionAtlas (E := E) X (fun _ => q)} (hG : GlueCharts A) (F : FormGlueN A)
  (J : AlmostComplexStructure E Q) {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}

lemma isFormRep_congr {ξ η : Form E X}
    (hd : ∀ i d k p, formDiscRep A i d k ξ p = formDiscRep A i d k η p)
    (hn : ∀ j k x, formNeckRep A j k ξ x = formNeckRep A j k η x)
    {v : (fibreBlocks A δ h0 hmono) 0} (h : IsFormRep ξ v) : IsFormRep η v := by
  have e1 : ∀ i d k, formDiscRep A i d k ξ = formDiscRep A i d k η := fun i d k =>
    funext (hd i d k)
  have e2 : ∀ j k, formNeckRep A j k ξ = formNeckRep A j k η := fun j k => funext (hn j k)
  exact ⟨fun i d k => e1 i d k ▸ h.1 i d k, fun j k => e2 j k ▸ h.2 j k⟩

variable (hpn : ∀ j (x : ℝ × ℝ), ∀ p ∈ X.nodes, X.polar (A.hol j) x ∉ p)
include hT hG hpn

/-- **`Φ` is the identity on the representatives of the forms anti-linear off the nodes**, when
the polar coordinates avoid the nodal points. -/
theorem phiN_eq_self {v : (fibreBlocks A δ h0 hmono) 0} (hv : v ∈ formsSub J A δ h0 hmono) :
    phiN hT hG F (J.J q) δ h0 hmono v = v := by
  obtain ⟨ξ, ha, hr⟩ := hv
  have hg : IsGlueRep J v (fun _ => ξ) (fun _ => ξ) :=
    ⟨fun i d k => ⟨_, hr.1 i d k, fun _ _ => rfl⟩, fun j k => ⟨_, hr.2 j k, fun _ _ => rfl⟩,
      fun j x _ => ha _ (hpn j x)⟩
  have hΞ : glueForm F (fun _ => ξ) (fun _ => ξ) = ξ := by
    funext y
    simp only [glueForm]
    rw [← Finset.sum_smul, ← Finset.sum_smul, ← add_smul, F.hsum y, one_smul]
  have h := isFormRep_phiN hT hG F J hg
  rw [hΞ] at h
  refine (isFormRep_congr ?_ ?_ h).unique hr
  · intro i d k p
    by_cases hp : discCut p = 0
    · simp [formDiscRep, hp]
    have hoff := A.disc_avoid i p (discD_of_discCut_ne hp)
    simp only [formDiscRep, formAt_of_const (fun _ => rfl), projF_of_mem (ha _ hoff)]
  · intro j k x
    simp only [formNeckRep, NodalSurface.formInPolar, projF_of_mem (ha _ (hpn j x))]

/-- **`Φ` is the identity on the fibre.** -/
theorem phiN_eq_self_fibre {v : (fibreBlocks A δ h0 hmono) 0}
    (hv : v ∈ fibreSpace J A δ h0 hmono) : phiN hT hG F (J.J q) δ h0 hmono v = v := by
  rw [← SetLike.mem_coe, fibreSpace, Submodule.topologicalClosure_coe] at hv
  exact (show EqOn (phiN hT hG F (J.J q) δ h0 hmono) id (formsSub J A δ h0 hmono : Set _) from
    fun v hv => phiN_eq_self hT hG F J hpn hv).closure
      (phiN hT hG F (J.J q) δ h0 hmono).continuous continuous_id hv

end Ident

end GWMemoir
