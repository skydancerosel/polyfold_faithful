import GWMemoir.LevelsNodesFredholm

/-!
# Filling at a node, `a ≠ 0`: the abstract part

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4.1 (the filled section,
(4.4)–(4.6), pp. 103–104, and (4.18), p. 116), at a constant map `u ≡ q` from two spheres joined
at a node (`twoSpheres`).

* `isScFredholm_scIso_comp`: an sc-isomorphism after an sc-Fredholm operator gives an
  sc-Fredholm operator of the same index, with the same kernel on level `0`.
* `scIndex_crScN`: `D = crScN` has index `dim E`; its kernel is the constant sections
  (`cstScN`, `crScN_cstScN`).
* **`isScFredholm_filled_of`**: for every sc⁺-operator `K` and sc-isomorphism `S` of the fibre,
  `S ∘ (D + K)` is sc-Fredholm of index `dim E`, every level map is Fredholm of that index, and
  the constants lie in its kernel when `K` vanishes on them.  This is the form of target (i) of the
  gluing at `a ≠ 0` (`GWMemoir.GlueFilled`) before the particular `K_a` and `S_a` are inserted.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology NNReal
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. Composition with an sc-isomorphism -/

section ScIsoComp

variable {E F G : ScBanach}

lemma range_scIso_comp (T : ScOperator E F) (S : ScIso F G) (m : ℕ) :
    ((LinearMap.range ((S.toScOperator.comp T) m : E m →ₗ[ℝ] G m) : Set (G m))) =
      (S m) '' (LinearMap.range (T m : E m →ₗ[ℝ] F m) : Set (F m)) := by
  ext y
  simp only [LinearMap.coe_range, ContinuousLinearMap.coe_coe, mem_range, mem_image]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨T m x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

lemma ker_scIso_comp (T : ScOperator E F) (S : ScIso F G) (m : ℕ) (x : E m) :
    (S.toScOperator.comp T) m x = 0 ↔ T m x = 0 := by
  rw [ScOperator.comp_apply, ScIso.toScOperator_apply]
  exact (S m).map_eq_zero_iff

/-- **An sc-isomorphism after an sc-Fredholm operator**: `S ∘ T` is sc-Fredholm and
`ind(S ∘ T) = ind(T)`. -/
theorem isScFredholm_scIso_comp {T : ScOperator E F} (hT : IsScFredholm T) (S : ScIso F G) :
    IsScFredholm (S.toScOperator.comp T) ∧ scIndex (S.toScOperator.comp T) = scIndex T := by
  obtain ⟨hF, hreg⟩ := isScFredholm_iff.1 hT
  have hu := IsFredholm.hasFiniteIndex hF
  have hv := HasFiniteIndex.equiv (S 0).toLinearEquiv
  have hc := hu.comp_and_linIndex hv
  have e0 : ((S.toScOperator.comp T) 0 : E 0 →ₗ[ℝ] G 0) =
      ((S 0).toLinearEquiv : F 0 →ₗ[ℝ] G 0) ∘ₗ (T 0 : E 0 →ₗ[ℝ] F 0) := rfl
  have hF' : ((S.toScOperator.comp T) 0).IsFredholm := by
    refine isFredholm_of_banach _ ?_ ?_ ?_
    · have := hc.1.finite_ker
      change FiniteDimensional ℝ (LinearMap.ker ((S.toScOperator.comp T) 0 : E 0 →ₗ[ℝ] G 0))
      rw [e0]; exact this
    · rw [range_scIso_comp]
      exact (S 0).toHomeomorph.isClosedMap _ hF.isClosed_range
    · have := hc.1.finite_coker
      change (LinearMap.range ((S.toScOperator.comp T) 0 : E 0 →ₗ[ℝ] G 0)).CoFG
      rw [e0]
      exact this
  refine ⟨isScFredholm_of_isRegularizing hF' fun m e he => hreg m e ?_, ?_⟩
  · obtain ⟨y, hy⟩ := he
    refine ⟨(S m).symm y, ?_⟩
    rw [ScIso.symm_toBase_comm, hy]
    exact (S 0).symm_apply_apply _
  · change linIndex ((S.toScOperator.comp T) 0 : E 0 →ₗ[ℝ] G 0) = linIndex (T 0 : E 0 →ₗ[ℝ] F 0)
    rw [e0, hc.2, linIndex_equiv, add_zero]

end ScIsoComp

/-! ## 2. The kernel and the index of `D` -/

section Index

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q}
  {A : SectionAtlas (E := E) twoSpheres (fun _ => q)} (hsm : NeckSmooth A) (G : GlueDataN A)
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)
  (hA : IsStdNeck A) (hδ : ∀ m, δ m < 2 * Real.pi) (hδ0 : 0 < δ 0) (hG : GlueCharts A)

/-- The constant section `η ≡ e`, as a point of level `0` of `H^{3,δ₀}_c` (`secScN`). -/
def cstScN : E →ₗ[ℝ] (secScN J hsm G δ h0 hmono hA hδ hδ0 hG) 0 where
  toFun e := ⟨constBlocksN A δ h0 hmono e, constBlocksN_mem δ h0 hmono e⟩
  map_add' e e' := Subtype.ext (map_add _ e e')
  map_smul' c e := Subtype.ext (map_smul _ c e)

lemma cstScN_eq (e : E) : cstScN J hsm G δ h0 hmono hA hδ hδ0 hG e = cstLvN δ h0 hmono hA hδ 0 e :=
  Subtype.ext (toBase_cstLvN δ h0 hmono hA hδ 0 e).symm

include hsm in
/-- `D` vanishes on the constants. -/
theorem crScN_cstScN (e : E) :
    crScN J hsm G δ h0 hmono hA hδ hδ0 hG 0 (cstScN J hsm G δ h0 hmono hA hδ hδ0 hG e) = 0 := by
  rw [cstScN_eq]
  exact crLvN_cstLvN J hsm G δ h0 hmono hA hδ 0 e

/-- The kernel of `D` on level `0` is a copy of `E`. -/
def kerCrScNEquiv :
    E ≃ₗ[ℝ] LinearMap.ker ((crScN J hsm G δ h0 hmono hA hδ hδ0 hG 0 :
      (secScN J hsm G δ h0 hmono hA hδ hδ0 hG) 0 →ₗ[ℝ] (fibScN J hsm G δ h0 hmono hA hδ hδ0 hG) 0)) :=
  LinearEquiv.ofBijective
    { toFun := fun e => ⟨cstScN J hsm G δ h0 hmono hA hδ hδ0 hG e,
        crScN_cstScN J hsm G δ h0 hmono hA hδ hδ0 hG e⟩
      map_add' := fun e e' => Subtype.ext (map_add _ e e')
      map_smul' := fun c e => Subtype.ext (map_smul _ c e) }
    ⟨fun e e' h => constBlocksN_injective (A := A) (δ := δ) (h0 := h0) (hmono := hmono)
        (congrArg (fun x : LinearMap.ker ((crScN J hsm G δ h0 hmono hA hδ hδ0 hG 0 :
          (secScN J hsm G δ h0 hmono hA hδ hδ0 hG) 0 →ₗ[ℝ]
            (fibScN J hsm G δ h0 hmono hA hδ hδ0 hG) 0)) =>
          x.1.1) h),
      fun x => by
        obtain ⟨e, he⟩ := crLvN_ker J hsm G δ h0 hmono hA hδ 0 x.1 x.2
        exact ⟨e, Subtype.ext ((cstScN_eq J hsm G δ h0 hmono hA hδ hδ0 hG e).trans he.symm)⟩⟩

/-- **The index of `D` is `dim E`**: the kernel is the constants and `D` is onto. -/
theorem scIndex_crScN :
    scIndex (crScN J hsm G δ h0 hmono hA hδ hδ0 hG) = Module.finrank ℝ E := by
  have hs : LinearMap.range ((crScN J hsm G δ h0 hmono hA hδ hδ0 hG 0 :
      (secScN J hsm G δ h0 hmono hA hδ hδ0 hG) 0 →ₗ[ℝ] (fibScN J hsm G δ h0 hmono hA hδ hδ0 hG) 0))
        = ⊤ :=
    LinearMap.range_eq_top.2 (crLvN_zero_surjective J hsm G δ h0 hmono hA hδ hδ0 hG)
  unfold scIndex
  rw [← (kerCrScNEquiv J hsm G δ h0 hmono hA hδ hδ0 hG).finrank_eq, hs]
  have : Subsingleton ((fibScN J hsm G δ h0 hmono hA hδ hδ0 hG) 0 ⧸
      (⊤ : Submodule ℝ ((fibScN J hsm G δ h0 hmono hA hδ hδ0 hG) 0))) :=
    Submodule.Quotient.subsingleton_iff.2 rfl
  have h0' : Module.finrank ℝ ((fibScN J hsm G δ h0 hmono hA hδ hδ0 hG) 0 ⧸
      (⊤ : Submodule ℝ ((fibScN J hsm G δ h0 hmono hA hδ hδ0 hG) 0))) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [h0']
  simp

/-! ## 3. Target (i) for any sc⁺-perturbation and any sc-isomorphism of the fibre -/

/-- **`S ∘ (D + K)` is sc-Fredholm of index `dim E`** for every sc⁺-operator `K` and every
sc-isomorphism `S` of the fibre (Proposition 1.1.11 of the book, 2021 p. 9, and
`isScFredholm_scIso_comp`); every level map is Fredholm of that index; if `K` vanishes on the
constants, they lie in the kernel. -/
theorem isScFredholm_filled_of
    (K : ScPlus (secScN J hsm G δ h0 hmono hA hδ hδ0 hG) (fibScN J hsm G δ h0 hmono hA hδ hδ0 hG))
    (S : ScIso (fibScN J hsm G δ h0 hmono hA hδ hδ0 hG) (fibScN J hsm G δ h0 hmono hA hδ hδ0 hG)) :
    IsScFredholm (S.toScOperator.comp (crScN J hsm G δ h0 hmono hA hδ hδ0 hG + K.toScOperator)) ∧
      scIndex (S.toScOperator.comp (crScN J hsm G δ h0 hmono hA hδ hδ0 hG + K.toScOperator)) =
        Module.finrank ℝ E ∧
      (∀ m, ((S.toScOperator.comp (crScN J hsm G δ h0 hmono hA hδ hδ0 hG + K.toScOperator)) m).IsFredholm
        ∧ fredholmIndex ((S.toScOperator.comp
          (crScN J hsm G δ h0 hmono hA hδ hδ0 hG + K.toScOperator)) m) = Module.finrank ℝ E) ∧
      ((∀ e, K.toScOperator 0 (cstScN J hsm G δ h0 hmono hA hδ hδ0 hG e) = 0) →
        ∀ e, (S.toScOperator.comp (crScN J hsm G δ h0 hmono hA hδ hδ0 hG + K.toScOperator)) 0
          (cstScN J hsm G δ h0 hmono hA hδ hδ0 hG e) = 0) := by
  have h1 := proposition_1_1_11_preprint (crScN_isScFredholm J hsm G δ h0 hmono hA hδ hδ0 hG) K
  have h2 := proposition_1_1_11_index (crScN_isScFredholm J hsm G δ h0 hmono hA hδ hδ0 hG) K
  obtain ⟨h3, h4⟩ := isScFredholm_scIso_comp h1 S
  have hind : scIndex (S.toScOperator.comp (crScN J hsm G δ h0 hmono hA hδ hδ0 hG +
      K.toScOperator)) = Module.finrank ℝ E := by
    rw [h4, h2, scIndex_crScN]
  refine ⟨h3, hind, fun m => ⟨(h3.fredholmIndex_lvl m).1, ?_⟩, fun hK e => ?_⟩
  · rw [(h3.fredholmIndex_lvl m).2, hind]
  · rw [ker_scIso_comp, ScOperator.add_apply, crScN_cstScN, hK e, add_zero]

end Index

/-! ## 4. Tuples carried by the far part of the necks lie in the fibre -/

section Far

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {q : Q} {A : SectionAtlas (E := E) twoSpheres (fun _ => q)}

variable (A) in
/-- **The far part of the necks**: `σ` lies beyond `s₀ + 1` in every neck, and beyond the
polar coordinates `-log|w|/2π` of every point of the compact pieces `KDn` of the closed discs
read in the necks.  So `{s ≥ σ}` in the polar coordinates of a neck misses every closed disc of
the atlas and lies where the neck cut-offs are `1`. -/
def FarBound (σ : ℝ) : Prop :=
  (∀ j, A.s0 j + 1 ≤ σ) ∧
    ∀ i j a, ∀ p ∈ KDn A i j a, -Real.log ‖wN A i j p‖ / (2 * Real.pi) ≤ σ

lemma FarBound.mono {σ σ' : ℝ} (h : FarBound A σ) (hσ : σ ≤ σ') : FarBound A σ' :=
  ⟨fun j => (h.1 j).trans hσ, fun i j a p hp => (h.2 i j a p hp).trans hσ⟩

/-- **Witness**: on an atlas with `GlueCharts` there is such a `σ` (the closed discs avoid the
nodal points, `wN_ne_zero`, and `KDn` is compact). -/
theorem exists_farBound (hG : GlueCharts A) : ∃ σ, FarBound A σ := by
  have hb : ∀ i j a, BddAbove ((fun p => -Real.log ‖wN A i j p‖ / (2 * Real.pi)) ''
      KDn A i j a) := by
    intro i j a
    refine (isCompact_KDn hG twoSpheres_chartsOnto i j a).bddAbove_image ?_
    have hsub : KDn A i j a ⊆
        twoSpheres.discPt (A.center i) (A.ε i) ⁻¹' (A.hol j).source := fun p hp =>
      zSet_sub (hG.target j) (tsupport_chiSN_sub (hG.smooth_symm j).continuous hp.2.1)
    have hw := (continuousOn_wN twoSpheres_chartsOnto i j).mono hsub
    exact ((hw.norm.log fun p hp =>
      norm_ne_zero_iff.2 (wN_ne_zero hG twoSpheres_chartsOnto hp.1 (hsub hp))).neg.div_const _)
  choose B hB using hb
  refine ⟨(∑ i, ∑ j, ∑ a, |B i j a|) + ∑ j, |A.s0 j| + 1, fun j => ?_, fun i j a p hp => ?_⟩
  · have h1 : A.s0 j ≤ ∑ j, |A.s0 j| := (le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |A.s0 j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j))
    have h2 : 0 ≤ ∑ i, ∑ j, ∑ a, |B i j a| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        abs_nonneg _
    linarith
  · have h1 : -Real.log ‖wN A i j p‖ / (2 * Real.pi) ≤ B i j a := hB i j a ⟨p, hp, rfl⟩
    have h2 : B i j a ≤ ∑ i, ∑ j, ∑ a, |B i j a| := by
      refine (le_abs_self _).trans ?_
      refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ∑ a, |B i j a|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ i))
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => ∑ a, |B i j a|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j))
      exact Finset.single_le_sum (f := fun a => |B i j a|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ a)
    have h3 : 0 ≤ ∑ j, |A.s0 j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith

variable (J : AlmostComplexStructure E Q) (hG : GlueCharts A) (F : FormGlueN A)
  {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}

/-- **`Φ` maps every tuple of blocks into the fibre** (`Φ` of the tuples of test functions
represents smooth anti-linear forms, `neckTestForms_of_glueCharts`; these tuples are dense). -/
theorem phiN_mem_fibreSpace (y : (fibreBlocks A δ h0 hmono) 0) :
    phiN twoSpheres_chartsOnto hG F (J.J q) δ h0 hmono y ∈ fibreSpace J A δ h0 hmono := by
  have hsub : phiN twoSpheres_chartsOnto hG F (J.J q) δ h0 hmono '' testTuplesN δ h0 hmono ⊆
      (fibreSpace J A δ h0 hmono : Set _) := by
    rintro _ ⟨w, hw, rfl⟩
    choose φ hφ hwφ using fun o => hw.1 o (mem_univ _)
    choose γ hγ hwγ using fun jk => hw.2 jk (mem_univ _)
    obtain ⟨ξN, h1, h2, -, -⟩ := neckTestForms_of_glueCharts J hG F φ hφ γ hγ
    have hg : IsGlueRep J w (testForm A φ) ξN :=
      ⟨fun i d k => ⟨φ (i, d, k), by rw [hwφ (i, d, k)]; exact MemLp.coeFn_toLp ((hφ _).memLp 2),
          fun p hp => (formDiscRep_testForm twoSpheres_chartsOnto (fun _ => rfl) A φ i d k hp).symm⟩,
        fun j k => ⟨γ (j, k), by rw [hwγ (j, k)]; exact MemLp.coeFn_toLp ((hγ _).memLp 2),
          h1 j k⟩, h2⟩
    exact formsSub_le J A δ h0 hmono ⟨_, fun y _ => projF_mem J q _ y,
      isFormRep_phiN twoSpheres_chartsOnto hG F J hg⟩
  exact closure_minimal hsub (isClosed_fibreSpace J A δ h0 hmono)
    (image_closure_subset_closure_image (phiN twoSpheres_chartsOnto hG F (J.J q) δ h0 hmono).continuous
      ⟨y, dense_testTuplesN δ h0 hmono y, rfl⟩)

/-- A change of charts applied to a shifted function that vanishes on `s ≤ σ` is `0`, if the
chart change lands in `s + s₀ ≤ σ`. -/
lemma op_shH_eq_zero {k : ℕ} {d d' : ℝ} {hd : 0 ≤ d} (D : ChartChange) {c : ℝ × ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) (hcK : tsupport c ⊆ D.K) (hd' : 0 ≤ d') {s₀ θ σ : ℝ}
    (hψ : ∀ p ∈ D.K, (D.ψ p).1 + s₀ ≤ σ) {g : H k hd} (hg : Neck.Van (Iic σ) (H.val g)) :
    D.op k hd hc hcK hd' (Neck.shH (-s₀) θ g) = 0 := by
  apply valCLM_injective
  rw [map_zero]
  apply Lp.ext
  set g' : ℝ × ℝ → ℝ := fun z => if z.1 ≤ σ then 0 else (H.val g : ℝ × ℝ → ℝ) z with hg'
  have e0 : (H.val g : ℝ × ℝ → ℝ) =ᵐ[cyl] g' := by
    filter_upwards [hg] with z hz
    by_cases h : z.1 ≤ σ
    · simp only [hg', if_pos h]; exact hz h
    · simp only [hg', if_neg h]
  have hq := (Neck.measurePreserving_shT (-s₀) θ).quasiMeasurePreserving
  have e1 : (H.val (Neck.shH (-s₀) θ g) : ℝ × ℝ → ℝ) =ᵐ[cyl] fun x => g' (Neck.shT (-s₀) θ x) :=
    (Neck.val_shH (-s₀) θ g).trans (hq.ae_eq_comp e0)
  filter_upwards [ChartChange.coeFn_op hc hcK hd' (Neck.shH (-s₀) θ g), D.comp_congr hcK e1,
    Lp.coeFn_zero ℝ 2 cyl] with x h1 h2 h3
  change (H.val (D.op k hd hc hcK hd' (Neck.shH (-s₀) θ g)) : ℝ × ℝ → ℝ) x = _
  rw [h1, h2, h3]
  by_cases hx : x ∈ D.K
  · have : (Neck.shT (-s₀) θ (D.ψ x)).1 ≤ σ := by
      simp only [Neck.shT, sub_neg_eq_add]; exact hψ x hx
    simp only [hg', if_pos this, mul_zero]; rfl
  · rw [ChartChange.eq_zero_off hcK hx, zero_mul]; rfl

/-- `χ_N g = g` for `g` vanishing on `s ≤ σ`, `σ ≥ s₀ + 1`. -/
lemma mulHL_chiN_eq {k : ℕ} {d : ℝ} {hd : 0 ≤ d} {s₀ σ : ℝ} (hσ : s₀ + 1 ≤ σ) {g : H k hd}
    (hg : Neck.Van (Iic σ) (H.val g)) : Neck.mulHL (chiN s₀) (mult_chiN s₀ k) g = g := by
  apply valCLM_injective
  apply Lp.ext
  filter_upwards [Neck.val_mulHL (chiN s₀) (mult_chiN s₀ k) g, hg] with x h1 h2
  rw [h1]
  by_cases hx : x.1 ≤ σ
  · show chiN s₀ x.1 * (H.val g : ℝ × ℝ → ℝ) x = (H.val g : ℝ × ℝ → ℝ) x
    rw [h2 hx, mul_zero]
  · rw [chiN_one (by linarith [not_le.1 hx]), one_mul]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ Q] in
lemma comp_proj_fst_of_fst_zero {ι X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {y : (ι → X) × Y} (hy : y.1 = 0) (i : ι) (f : X →L[ℝ] Z) :
    (f.comp ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _))) y = 0 :=
  (congrArg (fun z => f (z i)) hy).trans (map_zero f)

lemma fBlock_of_fst_zero {T : Type} [Fintype T] (D : Ix A → T → ChartChange)
    (a : Ix A → T → ℝ × ℝ → ℝ) (hc : ∀ o t, ContDiff ℝ ∞ (a o t))
    (hs : ∀ o t, tsupport (a o t) ⊆ (D o t).K) (src : Ix A → T → Ix A) (n : ℕ) (o : Ix A)
    {y : (fibreBlocks A δ h0 hmono) n} (hy : y.1 = 0) :
    fBlock δ h0 hmono D a hc hs src n o y = 0 := by
  rw [fBlock, ContinuousLinearMap.sum_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  exact comp_proj_fst_of_fst_zero hy _ _

/-- A tuple of blocks **carried by the far part of the necks**: no disc blocks, and neck blocks
vanishing on `s ≤ σ`. -/
def IsFar (σ : ℝ) (y : (fibreBlocks A δ h0 hmono) 0) : Prop :=
  y.1 = 0 ∧ ∀ jk, Neck.Van (Iic σ) (H.val (y.2 jk))

/-- **`Φ` is the identity on the tuples carried by the far part of the necks.** -/
theorem phiN_of_isFar {σ : ℝ} (hσ : FarBound A σ) {y : (fibreBlocks A δ h0 hmono) 0}
    (hy : IsFar σ y) : phiN twoSpheres_chartsOnto hG F (J.J q) δ h0 hmono y = y := by
  have hglue : glueN twoSpheres_chartsOnto hG F (J.J q) δ h0 hmono y = y := by
    refine Prod.ext (funext fun o => ?_) (funext fun jk => ?_)
    · change discOutN twoSpheres_chartsOnto hG F (J.J q) δ h0 hmono o y = y.1 o
      rw [hy.1]
      simp only [discOutN, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.comp_apply]
      rw [fBlock_of_fst_zero _ _ _ _ _ _ _ hy.1, zero_add]
      refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun a _ =>
        Finset.sum_eq_zero fun l _ => ?_
      refine op_shH_eq_zero _ _ _ _ (fun p hp => ?_) (hy.2 (j, l))
      rw [F.hDnK] at hp
      rw [F.hDnψ _ _ _ p (by rw [F.hDnK]; exact hp), fDn_fst hG, lamN]
      have := hσ.2 o.1 j a p hp
      linarith
    · change neckOutN twoSpheres_chartsOnto hG F (J.J q) δ h0 hmono jk y = y.2 jk
      simp only [neckOutN, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply]
      rw [Finset.sum_eq_zero, add_zero]
      · exact mulHL_chiN_eq (hσ.1 jk.1) (hy.2 jk)
      refine fun i _ => Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun d _ =>
        Finset.sum_eq_zero fun l _ => ?_
      rw [ContinuousLinearMap.comp_apply]
      exact (congrArg (Neck.shH 0 (thetaN a)) (comp_proj_fst_of_fst_zero hy.1 _ _)).trans
        (map_zero _)
  have hP : (projPN twoSpheres_chartsOnto (J.J q) δ h0 hmono y).1 = 0 := by
    funext o
    exact fBlock_of_fst_zero _ _ _ _ _ _ _ hy.1
  refine Prod.ext ?_ ?_
  · change ((1 / 2 : ℝ) • (glueN twoSpheres_chartsOnto hG F (J.J q) δ h0 hmono y +
      projPN twoSpheres_chartsOnto (J.J q) δ h0 hmono
        (glueN twoSpheres_chartsOnto hG F (J.J q) δ h0 hmono y))).1 = y.1
    rw [hglue]
    change (1 / 2 : ℝ) • (y.1 + (projPN twoSpheres_chartsOnto (J.J q) δ h0 hmono y).1) = y.1
    rw [hP, hy.1, add_zero, smul_zero]
  · change (glueN twoSpheres_chartsOnto hG F (J.J q) δ h0 hmono y).2 = y.2
    rw [hglue]

/-- **A tuple carried by the far part of the necks lies in the fibre.** -/
theorem mem_fibreSpace_of_isFar (hG : GlueCharts A) {σ : ℝ} (hσ : FarBound A σ) {y : (fibreBlocks A δ h0 hmono) 0}
    (hy : IsFar σ y) : y ∈ fibreSpace J A δ h0 hmono := by
  obtain ⟨F⟩ := nonempty_formGlueN hG twoSpheres_chartsOnto
  rw [← phiN_of_isFar J hG F hσ hy]
  exact phiN_mem_fibreSpace J hG F y

end Far

end GWMemoir
