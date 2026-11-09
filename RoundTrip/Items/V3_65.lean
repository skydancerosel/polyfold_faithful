import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_65

/-! Round trip for V3_65 (Lemma 3.80: the fixed point set `X_k`).

`A` is the conjunction of the types of `Polyfold.Radii.mapsTo_ball` and
`Polyfold.Radii.exists_fixed` (no universe parameters: `K Y : Type`).  `Polyfold.Radii.τ` (also
listed) is a definition and is vocabulary only.

`A → B`: the blind setting is turned into the project's normalized data: `K = ker L`, the blind
`Y`, `Cp = {(k, y) | k + y ∈ C}`, `Up = domB = {(k, y) | k + y ∈ U}`, and the blind map `Bmap`
(whose `invY = (L|_Y)⁻¹` is identified with the continuous linear inverse of `L|_Y`); this is a
`ContractionData` with `j = 1` (`contractionData`, copied from the proof of `theorem_3_8_22`).  The
radii are built by hand (`exists_radii'`, a copy of `ContractionData.exists_radii` with the
prescribed good-position constant `ε` of `B` and `a ≤ a₀`).  `A` gives the self-map property
`|B(k, y)| ≤ ε|k|` and the existence of the fixed point; uniqueness in `X_k` is the contraction
`Radii.norm_B_sub_le_snd`; `k + y ∈ U` is `Radii.mem_R_of_mem_V₀`; the bound `|B(k, y)| ≤ c(a)|k|`
with the blind `c(a) = (1 + ε) sup |DB|` is not in `A` and is proved here by the mean value
inequality (`norm_B_le_sSup`).

`B → A` is not proved: `A` is uniform over every admissible `Radii` (any `ε`, `a`, `b` with
`εa ≤ b` and `‖DB‖ ≤ ε/(2(1+ε))` on the region) for an abstract convex `Cp ⊆ K × Y` and an abstract
`B` with `B(0) = 0`, `DB(0) = 0`; `B` is about the concrete quadrant in `Fin n → ℝ` and only
asserts that *some* small `a` works. -/

open Set Filter Topology Function Module
open scoped ContDiff NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace RoundTrip.V3_65
open Polyfold

/-- The project's statement (no universe parameters). -/
def A : Prop := (type_of% @Polyfold.Radii.mapsTo_ball) ∧ (type_of% @Polyfold.Radii.exists_fixed)

theorem A_holds : A := ⟨@Polyfold.Radii.mapsTo_ball, @Polyfold.Radii.exists_fixed⟩

/-! ### Abstract glue: radii with a prescribed `ε`, and the bound by `sup ‖DB‖` -/

section Abstract

variable {K Y : Type} [NormedAddCommGroup K] [NormedSpace ℝ K] [FiniteDimensional ℝ K]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {Cp Up : Set (K × Y)} {B : K × Y → Y} {j : ℕ}

/-- `ContractionData.exists_radii` with a prescribed good-position constant `ε` and radii below
`a₀`, `b₀`; also records `b = (1 + ε) a` and the derivative bound on `{‖p‖ < b} ∩ Cp`. -/
theorem exists_radii' (h : ContractionData Cp Up B j) (ε : ℝ) (hε : 0 < ε)
    (hgood : ∀ (k : K) (y : Y), ‖y‖ ≤ ε * ‖k‖ → ((k, 0) ∈ Cp ↔ (k, y) ∈ Cp))
    (a₀ b₀ : ℝ) (ha₀ : 0 < a₀) (hb₀ : 0 < b₀) :
    ∃ S : Radii Cp Up B, S.ε = ε ∧ S.a ≤ a₀ ∧ S.b ≤ b₀ ∧ S.b = (1 + ε) * S.a ∧
      ∀ p : K × Y, ‖p‖ < S.b → p ∈ Cp → p ∈ Up ∧
        ‖fderivWithin ℝ B Up p‖ ≤ ε / (2 * (1 + ε)) := by
  obtain ⟨O, hO, hU⟩ := h.relOpen
  set c₀ : ℝ := ε / (2 * (1 + ε)) with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  have hcont := h.continuousOn_deriv 0 h.zero_mem_U
  rw [ContinuousWithinAt, h.deriv_zero, Metric.tendsto_nhdsWithin_nhds] at hcont
  obtain ⟨δ, hδ, hδ'⟩ := hcont c₀ hc₀pos
  have h0O : (0 : K × Y) ∈ O := by
    have := h.zero_mem_U; rw [hU] at this; exact this.1
  obtain ⟨δ', hδ'pos, hball⟩ := Metric.isOpen_iff.1 hO 0 h0O
  set r : ℝ := min (min δ δ' / 2) (min ((1 + ε) * a₀) b₀) with hr
  have hmin : 0 < min δ δ' := lt_min hδ hδ'pos
  have hrpos : 0 < r := lt_min (by linarith) (lt_min (by positivity) hb₀)
  have hr1 : r ≤ min δ δ' / 2 := min_le_left _ _
  have hrδ : r < δ := by have := min_le_left δ δ'; linarith
  have hrδ' : r < δ' := by have := min_le_right δ δ'; linarith
  have key : ∀ p : K × Y, ‖p‖ ≤ r → p ∈ Cp → p ∈ Up ∧ ‖fderivWithin ℝ B Up p‖ ≤ c₀ := by
    intro p hp hpC
    have hpU : p ∈ Up := by
      rw [hU]
      exact ⟨hball (by rw [Metric.mem_ball, dist_zero_right]; linarith), hpC⟩
    refine ⟨hpU, ?_⟩
    have := hδ' hpU (by rw [dist_zero_right]; linarith)
    rw [dist_zero_right] at this
    exact this.le
  have h1ε : 0 < 1 + ε := by linarith
  have ha_le : r / (1 + ε) ≤ r := div_le_self hrpos.le (by linarith)
  have hnorm : ∀ p : K × Y, ‖p.1‖ ≤ r / (1 + ε) → ‖p.2‖ ≤ r → ‖p‖ ≤ r := fun p h1 h2 => by
    rw [Prod.norm_def]; exact max_le (h1.trans ha_le) h2
  refine ⟨⟨ε, r / (1 + ε), r, hε, by positivity, hrpos, ?_, hgood, fun p h1 h2 hpC =>
      (key p (hnorm p h1 h2) hpC).1, fun p h1 h2 hpC => (key p (hnorm p h1 h2) hpC).2⟩,
    rfl, ?_, ?_, ?_, fun p hp hpC => key p hp.le hpC⟩
  · rw [mul_div_assoc', div_le_iff₀ h1ε]; nlinarith
  · change r / (1 + ε) ≤ a₀
    rw [div_le_iff₀ h1ε]
    have : r ≤ (1 + ε) * a₀ := (min_le_right _ _).trans (min_le_left _ _)
    linarith [this]
  · exact (min_le_right _ _).trans (min_le_right _ _)
  · change r = (1 + ε) * (r / (1 + ε))
    field_simp

/-- The bound `|B(k, y)| ≤ (1 + ε) sup_{Up ∩ B((1+ε)a)} ‖DB‖ · |k|` for `k ∈ V₀`, `|y| ≤ ε|k|`
(the mean value inequality on the convex set `Cp ∩ B((1 + ε)a) ⊆ Up`). -/
lemma norm_B_le_sSup (h : ContractionData Cp Up B j) (S : Radii Cp Up B)
    (hb : S.b = (1 + S.ε) * S.a)
    (hreg : ∀ p : K × Y, ‖p‖ < S.b → p ∈ Cp → p ∈ Up ∧
      ‖fderivWithin ℝ B Up p‖ ≤ S.ε / (2 * (1 + S.ε)))
    {k : K} (hk : k ∈ S.V₀) {y : Y} (hy : ‖y‖ ≤ S.ε * ‖k‖) :
    ‖B (k, y)‖ ≤ (1 + S.ε) * sSup ((fun p => ‖fderivWithin ℝ B Up p‖) ''
      {p | p ∈ Up ∧ ‖p‖ < (1 + S.ε) * S.a}) * ‖k‖ := by
  have hε := S.ε_pos
  have hUC : Up ⊆ Cp := by
    obtain ⟨O, -, hU⟩ := h.relOpen; rw [hU]; exact inter_subset_right
  set T := (fun p => ‖fderivWithin ℝ B Up p‖) '' {p | p ∈ Up ∧ ‖p‖ < (1 + S.ε) * S.a} with hT
  set D : Set (K × Y) := Cp ∩ Metric.ball 0 ((1 + S.ε) * S.a) with hD
  have hDU : D ⊆ Up := fun p hp => by
    have : ‖p‖ < S.b := by
      rw [hb]; have := hp.2; rwa [Metric.mem_ball, dist_zero_right] at this
    exact (hreg p this hp.1).1
  have hbdd : BddAbove T := by
    refine ⟨S.ε / (2 * (1 + S.ε)), ?_⟩
    rintro _ ⟨p, ⟨hpU, hp⟩, rfl⟩
    exact (hreg p (by rw [hb]; exact hp) (hUC hpU)).2
  have hDconv : Convex ℝ D := h.convex.inter (convex_ball 0 _)
  have hbound : ∀ p ∈ D, ‖fderivWithin ℝ B Up p‖ ≤ sSup T := fun p hp => by
    refine le_csSup hbdd ⟨p, ⟨hDU hp, ?_⟩, rfl⟩
    have := hp.2; rwa [Metric.mem_ball, dist_zero_right] at this
  have hderiv : ∀ p ∈ D, HasFDerivWithinAt B (fderivWithin ℝ B Up p) D p := fun p hp =>
    (h.hasFDerivWithinAt (hDU hp)).mono hDU
  have hka := hk.1
  have hkn := norm_nonneg k
  have h0D : (0 : K × Y) ∈ D :=
    ⟨h.zero_mem, by rw [Metric.mem_ball, dist_self]; exact mul_pos (by linarith) S.a_pos⟩
  have hkyC : ((k, y) : K × Y) ∈ Cp := (S.good k y hy).1 hk.2
  have hkyn : ‖((k, y) : K × Y)‖ ≤ (1 + S.ε) * ‖k‖ := by
    rw [Prod.norm_def]
    exact max_le (by nlinarith) (by nlinarith)
  have hkyD : ((k, y) : K × Y) ∈ D := by
    refine ⟨hkyC, ?_⟩
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖((k, y) : K × Y)‖ ≤ (1 + S.ε) * ‖k‖ := hkyn
      _ < (1 + S.ε) * S.a := by
        apply mul_lt_mul_of_pos_left hka; linarith
  have hmvt := hDconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound h0D hkyD
  rw [h.B_zero, sub_zero, sub_zero] at hmvt
  have hT0 : 0 ≤ sSup T := Real.sSup_nonneg fun t ht => by
    obtain ⟨p, -, rfl⟩ := ht; exact norm_nonneg _
  calc ‖B (k, y)‖ ≤ sSup T * ‖((k, y) : K × Y)‖ := hmvt
    _ ≤ sSup T * ((1 + S.ε) * ‖k‖) := mul_le_mul_of_nonneg_left hkyn hT0
    _ = (1 + S.ε) * sSup T * ‖k‖ := by ring

end Abstract

/-! ### Concrete glue: the blind setting is a `ContractionData` -/

section Glue

variable {n q N : ℕ} {L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)} {Y : Submodule ℝ (Fin n → ℝ)}

lemma quadC_convex (n q : ℕ) : Convex ℝ (quadC n q) := by
  intro x hx y hy s t hs ht _ i hi
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg hs (hx i hi)) (mul_nonneg ht (hy i hi))

lemma quadC_interior_nonempty (n q : ℕ) : (interior (quadC n q)).Nonempty := by
  refine ⟨fun _ => 1, mem_interior.2 ⟨Metric.ball (fun _ => 1) 1, fun x hx i _ => ?_,
    Metric.isOpen_ball, Metric.mem_ball_self one_pos⟩⟩
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have := (norm_le_pi_norm (x - fun _ => (1 : ℝ)) i).trans_lt hx
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_lt] at this
  linarith [this.1]

/-- `K × Y ≅ ℝⁿ`, `(k, y) ↦ k + y`. -/
def addE (hKY : IsCompl (kerCLM L) Y) : (kerCLM L × Y) ≃L[ℝ] (Fin n → ℝ) :=
  (Submodule.prodEquivOfIsCompl _ _ hKY).toContinuousLinearEquiv

lemma addE_apply (hKY : IsCompl (kerCLM L) Y) (p : kerCLM L × Y) :
    addE hKY p = (p.1 : Fin n → ℝ) + p.2 := by
  change (Submodule.prodEquivOfIsCompl _ _ hKY).toContinuousLinearEquiv p = _
  rw [LinearEquiv.coe_toContinuousLinearEquiv', Submodule.coe_prodEquivOfIsCompl']

lemma L_ker (k : kerCLM L) : L k = 0 := LinearMap.mem_ker.1 k.2

lemma eq_of_L_eq (hKY : IsCompl (kerCLM L) Y) {y y' : Y} (h : L y = L y') : y = y' := by
  have h1 : L ((y : Fin n → ℝ) - y') = 0 := by rw [map_sub]; exact sub_eq_zero.2 h
  have h2 : ((y : Fin n → ℝ) - y') ∈ kerCLM L := LinearMap.mem_ker.2 h1
  have h3 : ((y : Fin n → ℝ) - y') ∈ Y := Y.sub_mem y.2 y'.2
  have h4 : ((y : Fin n → ℝ) - y') = 0 := by
    have := hKY.disjoint.le_bot ⟨h2, h3⟩
    simpa using this
  exact Subtype.ext (sub_eq_zero.1 h4)

/-- `L|_Y` has a continuous linear right inverse with values in `Y`. -/
lemma exists_rightInv (hKY : IsCompl (kerCLM L) Y) (hsurj : Function.Surjective L) :
    ∃ Li : (Fin N → ℝ) →L[ℝ] Y, ∀ z, L (Li z) = z := by
  have hinj : Function.Injective ((L : (Fin n → ℝ) →ₗ[ℝ] (Fin N → ℝ)) ∘ₗ Y.subtype) :=
    fun y y' hyy' => eq_of_L_eq hKY hyy'
  have hsurjY : Function.Surjective ((L : (Fin n → ℝ) →ₗ[ℝ] (Fin N → ℝ)) ∘ₗ Y.subtype) := by
    intro z
    obtain ⟨x, hx⟩ := hsurj z
    have hx' : x ∈ kerCLM L ⊔ Y := by rw [hKY.sup_eq_top]; trivial
    obtain ⟨k, hk, y, hy, rfl⟩ := Submodule.mem_sup.1 hx'
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [map_add, L_ker ⟨k, hk⟩, zero_add] at hx
    exact hx
  let LY : Y ≃L[ℝ] (Fin N → ℝ) :=
    (LinearEquiv.ofBijective _ ⟨hinj, hsurjY⟩).toContinuousLinearEquiv
  exact ⟨LY.symm, fun z => LY.apply_symm_apply z⟩

/-- `Cp = {(k, y) | k + y ∈ C}`. -/
def Cp (q : ℕ) (L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) (Y : Submodule ℝ (Fin n → ℝ)) :
    Set (kerCLM L × Y) :=
  {p | (p.1 : Fin n → ℝ) + (p.2 : Fin n → ℝ) ∈ quadC n q}

/-- `B(k, y) = y − Li f(k + y)` for a right inverse `Li : ℝᴺ → Y` of `L`. -/
def Bn (L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) (f : (Fin n → ℝ) → (Fin N → ℝ))
    (Li : (Fin N → ℝ) →L[ℝ] Y) (p : kerCLM L × Y) : Y :=
  p.2 - Li (f ((p.1 : Fin n → ℝ) + (p.2 : Fin n → ℝ)))

lemma Bmap_eq (hKY : IsCompl (kerCLM L) Y) (f : (Fin n → ℝ) → (Fin N → ℝ))
    (Li : (Fin N → ℝ) →L[ℝ] Y) (hLi : ∀ z, L (Li z) = z) : Bmap f L Y = Bn L f Li := by
  funext p
  simp only [Bmap, Bn]
  congr 1
  apply eq_of_L_eq hKY
  rw [hLi]
  have hex : ∃ y : Y, L y = f ((p.1 : Fin n → ℝ) + (p.2 : Fin n → ℝ)) := ⟨Li _, hLi _⟩
  simp only [invY, dif_pos hex]
  exact hex.choose_spec

lemma mem_Cp_iff (p : kerCLM L × Y) :
    p ∈ Cp q L Y ↔ (p.1 : Fin n → ℝ) + (p.2 : Fin n → ℝ) ∈ quadC n q := Iff.rfl

/-- The blind setting gives the project's `ContractionData` (as in the proof of
`theorem_3_8_22`). -/
theorem contractionData {j : ℕ} {U : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → (Fin N → ℝ)}
    (hj : 1 ≤ j) (hU : ∃ O : Set (Fin n → ℝ), IsOpen O ∧ U = O ∩ quadC n q)
    (h0 : (0 : Fin n → ℝ) ∈ U) (hf : ContDiffOn ℝ j f U) (hf0 : f 0 = 0)
    (hL : HasFDerivWithinAt f L U 0)
    (hint : (interior (Subtype.val ⁻¹' quadC n q : Set (kerCLM L))).Nonempty)
    (hKY : IsCompl (kerCLM L) Y) (Li : (Fin N → ℝ) →L[ℝ] Y) (hLi : ∀ z, L (Li z) = z)
    {ε : ℝ} (hε : 0 < ε)
    (hgood : ∀ v ∈ kerCLM L, ∀ y ∈ Y, ‖y‖ ≤ ε * ‖v‖ → (v ∈ quadC n q ↔ v + y ∈ quadC n q)) :
    ContractionData (Cp q L Y) (domB L Y U) (Bn L f Li) j := by
  set add := addE hKY with hadd_def
  have hadd : ∀ p : kerCLM L × Y, add p = (p.1 : Fin n → ℝ) + p.2 := addE_apply hKY
  have hadd' : ∀ p : kerCLM L × Y, (add : kerCLM L × Y →L[ℝ] Fin n → ℝ) p = (p.1 : Fin n → ℝ) + p.2 :=
    fun p => hadd p
  have hLiL : ∀ y : Y, Li (L y) = y := fun y => eq_of_L_eq hKY (hLi _)
  have hCp : Cp q L Y = add ⁻¹' quadC n q := by
    ext p; rw [mem_preimage, hadd]; rfl
  have hUp : domB L Y U = add ⁻¹' U := by
    ext p; rw [mem_preimage, hadd]; rfl
  have hB : Bn L f Li = fun p => p.2 - Li (f (add p)) := by
    funext p; simp only [Bn, hadd]
  rw [hCp, hUp, hB]
  obtain ⟨O, hO, hUO⟩ := hU
  have hCpconv : Convex ℝ (add ⁻¹' quadC n q) :=
    (quadC_convex n q).linear_preimage (add : kerCLM L × Y →ₗ[ℝ] Fin n → ℝ)
  have hCpint : (interior (add ⁻¹' quadC n q)).Nonempty := by
    have hpre : (add : kerCLM L × Y → Fin n → ℝ) ⁻¹' interior (quadC n q) =
        interior (add ⁻¹' quadC n q) := by
      simpa using add.toHomeomorph.preimage_interior (quadC n q)
    rw [← hpre]
    exact (quadC_interior_nonempty n q).preimage add.surjective
  have hUpeq : add ⁻¹' U = add ⁻¹' O ∩ add ⁻¹' quadC n q := by rw [hUO, preimage_inter]
  have h0Up : (0 : kerCLM L × Y) ∈ add ⁻¹' U := by
    show add 0 ∈ U; rw [map_zero]; exact h0
  have hUpUD : UniqueDiffWithinAt ℝ (add ⁻¹' U) 0 := by
    rw [hUpeq, inter_comm]
    refine (uniqueDiffWithinAt_convex hCpconv hCpint (subset_closure ?_)).inter
      ((hO.preimage add.continuous).mem_nhds ?_)
    · have := h0Up; rw [hUpeq] at this; exact this.2
    · have := h0Up; rw [hUpeq] at this; exact this.1
  have hBcd : ContDiffOn ℝ j (fun p : kerCLM L × Y => p.2 - Li (f (add p))) (add ⁻¹' U) := by
    have h1 : ContDiffOn ℝ j (f ∘ add) (add ⁻¹' U) :=
      hf.comp (add : kerCLM L × Y →L[ℝ] Fin n → ℝ).contDiff.contDiffOn fun p hp => hp
    exact contDiff_snd.contDiffOn.sub (h1.continuousLinearMap_comp Li)
  have hLf : HasFDerivWithinAt f L U (add 0) := by rw [map_zero]; exact hL
  have hBderiv : HasFDerivWithinAt (fun p : kerCLM L × Y => p.2 - Li (f (add p)))
      (ContinuousLinearMap.snd ℝ (kerCLM L) Y -
        Li.comp (L.comp (add : kerCLM L × Y →L[ℝ] Fin n → ℝ))) (add ⁻¹' U) 0 := by
    refine hasFDerivWithinAt_snd.sub ?_
    exact Li.hasFDerivAt.comp_hasFDerivWithinAt (x := (0 : kerCLM L × Y))
      (hLf.comp (0 : kerCLM L × Y) (add : kerCLM L × Y →L[ℝ] Fin n → ℝ).hasFDerivWithinAt
        fun p hp => hp)
  have hBderiv0 : ContinuousLinearMap.snd ℝ (kerCLM L) Y -
      Li.comp (L.comp (add : kerCLM L × Y →L[ℝ] Fin n → ℝ)) = 0 := by
    refine ContinuousLinearMap.ext fun p => ?_
    simp only [sub_apply, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.comp_apply, zero_apply]
    rw [hadd', map_add, L_ker, zero_add, hLiL, sub_self]
  exact
    { convex := hCpconv
      interior_nonempty := hCpint
      relOpen := ⟨add ⁻¹' O, hO.preimage add.continuous, hUpeq⟩
      zero_mem_U := h0Up
      one_le := hj
      contDiffOn := hBcd
      B_zero := by
        change (0 : kerCLM L × Y).2 - Li (f (add 0)) = 0
        rw [map_zero, hf0, map_zero]; simp
      deriv_zero := by rw [hBderiv.fderivWithin hUpUD, hBderiv0]
      good := ⟨ε, hε, fun k y hy => by
        have := hgood k k.2 y y.2 hy
        rw [mem_preimage, mem_preimage, hadd, hadd]
        simpa using this⟩
      interior_K_nonempty := by
        have : {k : kerCLM L | ((k, 0) : kerCLM L × Y) ∈ add ⁻¹' quadC n q} =
            Subtype.val ⁻¹' quadC n q := by
          ext k
          rw [mem_ofPred_eq, mem_preimage, hadd]
          simp
        rw [this]; exact hint }

lemma good_abstract {ε : ℝ}
    (hgood : ∀ v ∈ kerCLM L, ∀ y ∈ Y, ‖y‖ ≤ ε * ‖v‖ → (v ∈ quadC n q ↔ v + y ∈ quadC n q)) :
    ∀ (k : kerCLM L) (y : Y), ‖y‖ ≤ ε * ‖k‖ → ((k, 0) ∈ Cp q L Y ↔ (k, y) ∈ Cp q L Y) :=
  fun k y hy => by
    rw [mem_Cp_iff, mem_Cp_iff]
    simpa using hgood k k.2 y y.2 hy

lemma mem_V₀_iff {U : Set (Fin n → ℝ)} {B : kerCLM L × Y → Y}
    (S : Radii (Cp q L Y) (domB L Y U) B) (k : kerCLM L) :
    k ∈ S.V₀ ↔ (k : Fin n → ℝ) ∈ quadC n q ∧ ‖k‖ < S.a := by
  change ‖k‖ < S.a ∧ (k : Fin n → ℝ) + ((0 : Y) : Fin n → ℝ) ∈ quadC n q ↔ _
  simp [and_comm]

end Glue

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  intro hA n q N U f L Y ε _ hU h0 hf hf0 hL hsurj hint hKY hε hgood a₀ ha₀
  obtain ⟨Li, hLi⟩ := exists_rightInv hKY hsurj
  have hBeq : Bmap f L Y = Bn L f Li := Bmap_eq hKY f Li hLi
  have h := contractionData (j := 1) le_rfl hU h0 (by exact_mod_cast hf) hf0 hL hint hKY Li hLi
    hε hgood
  obtain ⟨S, hSε, hSa, -, hSb, hSreg⟩ :=
    exists_radii' h ε hε (good_abstract hgood) a₀ a₀ ha₀ ha₀
  refine ⟨S.a, S.a_pos, hSa, fun k hkC hka => ?_⟩
  have hk : k ∈ S.V₀ := (mem_V₀_iff S k).2 ⟨hkC, hka⟩
  rw [hBeq]
  refine ⟨fun y hy => ⟨?_, ?_, ?_⟩, ?_⟩
  · -- `k + y ∈ U`
    exact S.R_sub_U (S.mem_R_of_mem_V₀ hk (by rw [hSε]; exact hy))
  · -- `|B(k, y)| ≤ c(a)|k|`
    have := norm_B_le_sSup h S (by rw [hSε]; exact hSb) (by rw [hSε]; exact hSreg) hk
      (by rw [hSε]; exact hy)
    rw [hSε] at this
    simp only [cConst, hBeq]
    exact this
  · -- `|B(k, y)| ≤ ε|k|` (`mapsTo_ball`)
    have hy' : y ∈ Metric.closedBall (0 : Y) (S.ε * ‖k‖) := by
      rw [Metric.mem_closedBall, dist_zero_right, hSε]; exact hy
    have := hA.1 S h hk hy'
    rw [Metric.mem_closedBall, dist_zero_right, hSε] at this
    exact this
  · -- the unique fixed point (`exists_fixed`; uniqueness by the contraction)
    obtain ⟨t, ht, hfix⟩ := hA.2 S h hk
    refine ⟨t, ⟨by rw [← hSε]; exact ht, hfix⟩, fun t' ⟨ht', hfix'⟩ => ?_⟩
    have := S.norm_B_sub_le_snd h (S.mem_R_of_mem_V₀ hk (by rw [hSε]; exact ht'))
      (S.mem_R_of_mem_V₀ hk ht)
    rw [hfix', hfix] at this
    have h2 : ‖t' - t‖ ≤ 0 := by linarith [norm_nonneg (t' - t)]
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)

#rt_check RoundTrip.V3_65.A_to_B [Polyfold.Radii.mapsTo_ball, Polyfold.Radii.exists_fixed]
#rt_overlap RoundTrip.V3_65.A_to_B [Polyfold.Radii.mapsTo_ball, Polyfold.Radii.exists_fixed]

end RoundTrip.V3_65

end
