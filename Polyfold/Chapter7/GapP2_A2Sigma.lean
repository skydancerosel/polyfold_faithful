import Polyfold.Chapter7.GapP2_A2ZhouGroupoid

set_option maxSynthPendingDepth 3

/-!
# Appendix 7.6.3 (2021, p. 348): `Y ≅ Σ`, and `𝐗^T` on `Σ` as printed

The text identifies the retract `Y = r(F)` of Zhou's retraction with
`Σ = {(s, t) ∈ ℝ² | t = 0 if s ≤ 0}` by `(s, t) ↦ (s, t · β(· + e^{1/s}))` (the image of `(0, 0)`
read as `(0, 0)`), `Y` carrying the topology of `F = F₀`, and computes `𝐗^T` on `{0,1} × Σ`.

* `sigmaHomeo D : Sig ≃ₜ O D`: that map is a homeomorphism.  The inverse is
  `(s, f) ↦ (s, ⟨β(· + e^{1/s}), f⟩)`; both are continuous because `‖β(· + c)‖ = 1` in
  `E₀ = L²(ℝ)` (`norm_w`).
* `nonEffectivePart_sigma`: the preimage of `𝐗^T` in `ℤˣ × Σ` is
  `(ℤˣ × {(s, 0) | s < 0}) ∪ ({1} × {(0, 0)}) ∪ ({1} × {(s, t) | s > 0})`, the text's
  `({0,1} × {(s,0) | s < 0}) ∪ ({0} × {(0,0)}) ∪ ({0} × {(s,t) | s > 0})` with `ℤ/2 = {1, −1}`.
* `closure_nonEffectivePart_sigma`: its closure minus itself is `{(−1, (0, 0))}`, the text's
  `{1} × {(0, 0)}`.
-/

open Set Filter Topology
open scoped InnerProductSpace

namespace Polyfold.EpGroupoid.Examples.ZhouRetract

open Polyfold.ZhouLine Polyfold.GapP1Sobolev

noncomputable section

variable (D : Data)

/-- `Σ = {(s, t) | t = 0 if s ≤ 0}` (2021 Appendix 7.6.3, p. 348). -/
def Sig : Set (ℝ × ℝ) := {p | p.1 ≤ 0 → p.2 = 0}

/-- Level `0` is `L²(ℝ)` isometrically. -/
lemma norm_eq_norm_val (f : Z D 0) : ‖f‖ = ‖H1.val (show H1 0 _ from f)‖ := by
  have hiso := (level0_line (nonneg_of_strictMono D.h0 D.hmono 0) D.h0).1
  have := hiso.dist_eq f 0
  change dist (H1.val f) 0 = dist f 0 at this
  rw [dist_zero_right, dist_zero_right] at this
  exact this.symm

lemma norm_tr0 (c : ℝ) : ‖tr0 D.β c‖ = 1 := by
  have h := inner_tr0_self D.hβ D.hβ2 c
  rw [real_inner_self_eq_norm_sq] at h
  have h0 : 0 ≤ ‖tr0 D.β c‖ := norm_nonneg _
  nlinarith

lemma val_w (t : ℝ) : H1.val (show H1 0 _ from w D t) = tr0 D.β (Real.exp t⁻¹) :=
  val_trH (m := 0) (hδ := nonneg_of_strictMono D.h0 D.hmono 0) _

/-- `‖β(· + e^{1/t})‖ = 1` in `E₀`. -/
lemma norm_w (t : ℝ) : ‖w D t‖ = 1 := by
  rw [norm_eq_norm_val, val_w, norm_tr0]

lemma continuousAt_w {t : ℝ} (ht : t ≠ 0) : ContinuousAt (w D) t :=
  (contDiff_trH (m := 0) (hδ := nonneg_of_strictMono D.h0 D.hmono 0) D.hβ).continuous.continuousAt.comp
    (Real.continuous_exp.continuousAt.comp (continuousAt_inv₀ ht))

lemma continuousAt_tr0 {t : ℝ} (ht : t ≠ 0) :
    ContinuousAt (fun s => tr0 D.β (Real.exp s⁻¹)) t :=
  (hasDerivAt_tr0 D.hβ _).continuousAt.comp
    (Real.continuous_exp.continuousAt.comp (continuousAt_inv₀ ht))

/-- `(s, t) ↦ (s, t · β(· + e^{1/s}))`. -/
def toY (p : Sig) : O D :=
  ⟨(p.1.1, p.1.2 • w D p.1.1), by
    rw [mem_O_iff']
    rcases le_or_gt p.1.1 0 with h | h
    · exact Or.inl ⟨h, by change p.1.2 • w D p.1.1 = 0; rw [p.2 h, zero_smul]⟩
    · exact Or.inr ⟨h, p.1.2, rfl⟩⟩

/-- `(s, f) ↦ (s, ⟨β(· + e^{1/s}), f⟩)`. -/
def toSig (y : O D) : Sig :=
  ⟨(y.1.1, ⟪tr0 D.β (Real.exp y.1.1⁻¹), H1.val (show H1 0 _ from y.1.2)⟫_ℝ), fun h => by
    change ⟪_, H1.val (show H1 0 _ from y.1.2)⟫_ℝ = 0
    rw [snd_eq_zero_of_nonpos D y h]
    exact inner_zero_right _⟩

lemma toSig_toY (p : Sig) : toSig D (toY D p) = p := by
  refine Subtype.ext (Prod.ext rfl ?_)
  change ⟪tr0 D.β (Real.exp p.1.1⁻¹), p.1.2 • H1.val (show H1 0 _ from w D p.1.1)⟫_ℝ = p.1.2
  rw [val_w, inner_smul_right, inner_tr0_self D.hβ D.hβ2, mul_one]

lemma toY_toSig (y : O D) : toY D (toSig D y) = y := by
  refine Subtype.ext (Prod.ext rfl ?_)
  change ⟪tr0 D.β (Real.exp y.1.1⁻¹), H1.val (show H1 0 _ from y.1.2)⟫_ℝ • w D y.1.1 = y.1.2
  rcases le_or_gt y.1.1 0 with h | h
  · rw [snd_eq_zero_of_nonpos D y h]
    change ⟪_, (0 : MeasureTheory.Lp ℝ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ))⟫_ℝ •
      w D y.1.1 = 0
    rw [inner_zero_right, zero_smul]
  · rw [← pi_apply_pos D h]; exact (mem_O_iff D _).1 y.2

lemma continuous_toY : Continuous (toY D) := by
  refine Continuous.subtype_mk ((continuous_fst.comp continuous_subtype_val).prodMk ?_) _
  rw [continuous_iff_continuousAt]
  intro p
  rcases le_or_gt p.1.1 0 with h | h
  · have hp : p.1.2 • w D p.1.1 = 0 := by rw [p.2 h, zero_smul]
    change Tendsto (fun x : Sig => x.1.2 • w D x.1.1) (𝓝 p) (𝓝 (p.1.2 • w D p.1.1))
    rw [hp, tendsto_zero_iff_norm_tendsto_zero]
    have he : (fun q : Sig => ‖q.1.2 • w D q.1.1‖) = fun q => ‖q.1.2‖ := funext fun q => by
      rw [norm_smul, norm_w, mul_one]
    rw [he]
    have := ((continuous_norm.comp (continuous_snd.comp continuous_subtype_val)).tendsto p)
    change Tendsto (fun q : Sig => ‖q.1.2‖) (𝓝 p) (𝓝 ‖p.1.2‖) at this
    rwa [p.2 h, norm_zero] at this
  · have hc : ContinuousAt (fun x : Sig => w D x.1.1) p :=
      (continuousAt_w D h.ne').comp (f := fun x : Sig => x.1.1)
        (continuous_fst.comp continuous_subtype_val).continuousAt
    exact ((continuous_snd.comp continuous_subtype_val).continuousAt).smul hc

lemma continuous_toSig : Continuous (toSig D) := by
  have hval : Continuous fun y : O D => H1.val (show H1 0 _ from y.1.2) :=
    (val1CLM 0 (nonneg_of_strictMono D.h0 D.hmono 0)).continuous.comp
      (continuous_snd.comp continuous_subtype_val)
  refine Continuous.subtype_mk ((continuous_fst.comp continuous_subtype_val).prodMk ?_) _
  rw [continuous_iff_continuousAt]
  intro y
  rcases le_or_gt y.1.1 0 with h | h
  · have hy : y.1.2 = 0 := snd_eq_zero_of_nonpos D y h
    have h0 : ⟪tr0 D.β (Real.exp y.1.1⁻¹), H1.val (show H1 0 _ from y.1.2)⟫_ℝ = 0 := by
      rw [hy]; exact inner_zero_right _
    change Tendsto (fun x : O D => ⟪tr0 D.β (Real.exp x.1.1⁻¹), H1.val (show H1 0 _ from x.1.2)⟫_ℝ)
      (𝓝 y) (𝓝 (⟪tr0 D.β (Real.exp y.1.1⁻¹), H1.val (show H1 0 _ from y.1.2)⟫_ℝ))
    rw [h0]
    refine squeeze_zero_norm (a := fun y' : O D => ‖y'.1.2‖) (fun y' => ?_) ?_
    · refine (norm_inner_le_norm _ _).trans ?_
      rw [norm_tr0, one_mul, ← norm_eq_norm_val]
    · have := ((continuous_norm.comp (continuous_snd.comp continuous_subtype_val)).tendsto y)
      change Tendsto (fun y' : O D => ‖y'.1.2‖) (𝓝 y) (𝓝 ‖y.1.2‖) at this
      rwa [hy, norm_zero] at this
  · have hc : ContinuousAt (fun x : O D => tr0 D.β (Real.exp x.1.1⁻¹)) y :=
      (continuousAt_tr0 D h.ne').comp (f := fun x : O D => x.1.1)
        (continuous_fst.comp continuous_subtype_val).continuousAt
    exact hc.inner hval.continuousAt

/-- **`Σ ≅ Y`** (2021 Appendix 7.6.3, p. 348): `(s, t) ↦ (s, t · β(· + e^{1/s}))` is a
homeomorphism of `Σ` onto the retract `Y`. -/
def sigmaHomeo : Sig ≃ₜ O D where
  toFun := toY D
  invFun := toSig D
  left_inv := toSig_toY D
  right_inv := toY_toSig D
  continuous_toFun := continuous_toY D
  continuous_invFun := continuous_toSig D

lemma sigmaHomeo_apply (p : Sig) : ((sigmaHomeo D p : O D) : E D 0) = (p.1.1, p.1.2 • w D p.1.1) :=
  rfl

/-- The point `(0, 0)` of `Σ`. -/
def σ₀ : Sig := ⟨(0, 0), fun _ => rfl⟩

lemma sigmaHomeo_σ₀ : sigmaHomeo D σ₀ = o₀ D :=
  Subtype.ext (Prod.ext rfl (zero_smul ℝ _))

/-- `ℤ/2 × Σ ≅ ℤ/2 × Y`, the identification of the text. -/
def sigmaHomeo₂ : ℤˣ × Sig ≃ₜ ℤˣ × O D := (Homeomorph.refl ℤˣ).prodCongr (sigmaHomeo D)

/-- **`𝐗^T` on `{0,1} × Σ`, as printed** (2021 Appendix 7.6.3, p. 348):
`({0,1} × {(s, 0) | s < 0}) ∪ ({0} × {(0, 0)}) ∪ ({0} × {(s, t) | s > 0})`, with `ℤ/2 = {1, −1}`
(`0 ↦ 1`, `1 ↦ −1`). -/
theorem nonEffectivePart_sigma :
    sigmaHomeo₂ D ⁻¹' (X D).nonEffectivePart =
      {q | q.2.1.1 < 0 ∧ q.2.1.2 = 0} ∪ {q | q.1 = 1 ∧ q.2.1 = (0, 0)} ∪
        {q | q.1 = 1 ∧ 0 < q.2.1.1} := by
  ext ⟨k, p⟩
  change ((k, sigmaHomeo D p) : ℤˣ × O D) ∈ (X D).nonEffectivePart ↔ _
  rw [nonEffectivePart_eq]
  simp only [mem_union, mem_ofPred_eq]
  change k = 1 ∨ (k = -1 ∧ p.1.1 < 0) ↔
    (p.1.1 < 0 ∧ p.1.2 = 0 ∨ k = 1 ∧ p.1 = (0, 0)) ∨ k = 1 ∧ 0 < p.1.1
  constructor
  · rintro (rfl | ⟨rfl, hp⟩)
    · rcases lt_trichotomy p.1.1 0 with hp | hp | hp
      · exact Or.inl (Or.inl ⟨hp, p.2 hp.le⟩)
      · exact Or.inl (Or.inr ⟨rfl, Prod.ext hp (p.2 hp.le)⟩)
      · exact Or.inr ⟨rfl, hp⟩
    · exact Or.inl (Or.inl ⟨hp, p.2 hp.le⟩)
  · rintro ((⟨hp, -⟩ | ⟨rfl, -⟩) | ⟨rfl, -⟩)
    · rcases Int.units_eq_one_or k with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr ⟨rfl, hp⟩
    · exact Or.inl rfl
    · exact Or.inl rfl

/-- **`cl(𝐗^T) ∖ 𝐗^T = {1} × {(0, 0)}` on `{0,1} × Σ`, as printed** (2021 Appendix 7.6.3,
p. 348): the one point `(−1, (0, 0))`. -/
theorem closure_nonEffectivePart_sigma :
    closure (sigmaHomeo₂ D ⁻¹' (X D).nonEffectivePart) \ sigmaHomeo₂ D ⁻¹' (X D).nonEffectivePart =
      {((-1 : ℤˣ), σ₀)} := by
  rw [← (sigmaHomeo₂ D).preimage_closure, ← preimage_sdiff, closure_nonEffectivePart_diff]
  have hΦ : sigmaHomeo₂ D ((-1 : ℤˣ), σ₀) = ((-1 : ℤˣ), o₀ D) :=
    Prod.ext rfl (sigmaHomeo_σ₀ D)
  ext q
  rw [mem_preimage, mem_singleton_iff, mem_singleton_iff, ← hΦ]
  exact (sigmaHomeo₂ D).injective.eq_iff

/-- **2021 Appendix 7.6.3, p. 348, on `Σ` as printed**: `Y ≅ Σ`; on `ℤ/2 × Σ` the
non-effective part is the text's set and `cl(𝐗^T) ∖ 𝐗^T` is the one point `(−1, (0, 0))`. -/
theorem appendix_7_6_3_sigma :
    sigmaHomeo₂ D ⁻¹' (X D).nonEffectivePart =
      {q | q.2.1.1 < 0 ∧ q.2.1.2 = 0} ∪ {q | q.1 = 1 ∧ q.2.1 = (0, 0)} ∪
        {q | q.1 = 1 ∧ 0 < q.2.1.1} ∧
    closure (sigmaHomeo₂ D ⁻¹' (X D).nonEffectivePart) \ sigmaHomeo₂ D ⁻¹' (X D).nonEffectivePart =
      {((-1 : ℤˣ), σ₀)} :=
  ⟨nonEffectivePart_sigma D, closure_nonEffectivePart_sigma D⟩

end

end Polyfold.EpGroupoid.Examples.ZhouRetract
