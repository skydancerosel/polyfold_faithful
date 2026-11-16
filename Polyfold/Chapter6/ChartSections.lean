import Polyfold.Chapter5.Lemma629
import Polyfold.Chapter5.OrientableNbhd
import Polyfold.Chapter5.IndexAlongPathsLocal

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §6.6,
pp. 219–222: **Proposition 6.6.3** (3), (4) and **Lemma 6.6.4** for a strong bundle with a chart
over the whole base, without sc-smooth bump functions.

# Local sc⁺-sections in a chart over the whole base

## The text, paraphrased

In the proof of Proposition 6.6.3 the sc⁺-sections of (3) and (4) are written in a strong bundle
chart, "assuming `X = U`": `s(y, t) = R(y, f(φ(t)))` and `q(y, t) = R(y, e₀)`.  No cut-off
occurs.  Lemma 6.6.4 then takes finitely many sc⁺-sections `s₁, …, s_k` with property (P) along
a path.

## What is formalized

Throughout, `hch : ∃ c ∈ B.atlas.charts, c.φ.source = univ` (a chart of the atlas whose base
domain is all of `X`, the text's "`X = U`") replaces the sc-smooth bump functions of
`OrientableNbhd.lean` and `Lemma629.lean`.

* `exists_isScPlusSection_pullback_of_family_of_chart`: property (3) for every sc-smooth family
  `Φ : ℝⁿ → X` (the section `S(q, y) = −R(y, f(Φ(q)))`, cut-off `1`).
* `proposition_6_6_3_of_chart`: Proposition 6.6.3 in the form of `proposition_6_6_3`.
* `exists_sections_isGeneralPositionGerm_of_isCompact_of_sections`: finitely many sc⁺-sections
  putting `F` in general position along a compact set of zeros, from sc⁺-sections through the
  smooth fibre points (`StrongBundle.HasScPlusSectionsThrough`).
* `lemma_6_6_4_of_chart`: Lemma 6.6.4 in the form of `lemma_6_6_4`.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-! ### Properties (3) and (4) in a chart over the whole base -/

section Sections

variable {n : ℕ} [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- **Property (3) without cut-off**: if a chart `c` of the atlas has base domain `X`, then along
every sc-smooth `Φ : ℝⁿ → X` there is an sc⁺-section `S` of `ℝⁿ × X → Y` with
`(f + S)(q, Φ(q)) = 0` for all `q` (the text's `s(y, t) = R(y, f(φ(t)))`, with the sign of
`sectionAdd`), and `S(q, ·)` depends on `q` only through `Φ(q)`. -/
theorem exists_isScPlusSection_pullback_of_family_of_chart
    (hch : ∃ c ∈ B.atlas.charts, c.φ.source = univ)
    (hf : B.IsScSmoothSection f) {Φ : (Fin n → ℝ) → X} (hΦ : (rnPolyfold n).IsScSmoothMap PX Φ) :
    ∃ S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X),
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S ∧
      (∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.1) S) (q, Φ q)) ∧
      ∀ q ∈ Icc (0 : Fin n → ℝ) 1, ∀ q' ∈ Icc (0 : Fin n → ℝ) 1, Φ q = Φ q' →
        ∀ y, (S (q, y)).1.2 = (S (q', y)).1.2 := by
  obtain ⟨c, hc, hsrc⟩ := hch
  obtain ⟨S, hS, hz, hdep⟩ := exists_isScPlusSection_pullback_of_mapsTo_of_bump hf hΦ 0 hc
    (fun t => hsrc ▸ mem_univ _) (isScSmoothMap_real_const 1) (hsrc ▸ subset_univ _)
  exact ⟨S, hS, Eventually.of_forall fun q => hz q rfl, fun q _ q' _ hqq' y => hdep q q' hqq' y⟩

end Sections

/-! ### Proposition 6.6.3 -/

-- `x ∈ X_∞` is the text's hypothesis; the construction does not use it
set_option linter.unusedVariables false in
/-- **Proposition 6.6.3 for a bundle with a chart over the whole base** (`proposition_6_6_3`
without sc-smooth bump functions): every smooth point `x` has open neighbourhoods `U ⊆ W` in the
domain of one chart `c` of the atlas with (1′) any two sc-smooth paths in `U` with the same end
points are sc-smoothly homotopic in `W` with end points fixed; (2) `{y ∈ cl(U) | f(y) = 0}` is
compact; (3) along every sc-smooth family `Φ : ℝⁿ → X` with `Φ([0, 1]ⁿ) ⊆ W` there is an
sc⁺-section `S` with `(f + S)(q, Φ(q)) = 0` near `[0, 1]ⁿ`, depending on `q ∈ [0, 1]ⁿ` only
through `Φ(q)`; (4) `ℝⁿ × X → Y` has sc⁺-sections through all smooth fibre points.  (1′) and (2)
are proved as in `proposition_6_6_3`; (3) and (4) are the text's local sections in the chart over
the whole base. -/
theorem proposition_6_6_3_of_chart
    (hch : ∃ c ∈ B.atlas.charts, c.φ.source = univ) (hf : B.IsScFredholmSection f) {x : X}
    (hx : x ∈ PX.smoothSet) :
    ∃ (U W : Set X) (c : StrongBundleChart PX P), IsOpen U ∧ IsOpen W ∧ x ∈ U ∧ U ⊆ W ∧
      c ∈ B.atlas.charts ∧ W ⊆ c.φ.source ∧
      (∀ γ₀ γ₁ : (Fin 1 → ℝ) → X, (rnPolyfold 1).IsScSmoothMap PX γ₀ →
        (rnPolyfold 1).IsScSmoothMap PX γ₁ → (∀ t ∈ Icc (0 : ℝ) 1, γ₀ (pt1 t) ∈ U) →
        (∀ t ∈ Icc (0 : ℝ) 1, γ₁ (pt1 t) ∈ U) → γ₀ (pt1 0) = γ₁ (pt1 0) →
        γ₀ (pt1 1) = γ₁ (pt1 1) →
        ∃ Φ, IsScHomotopyRel PX γ₀ γ₁ Φ ∧ ∀ τ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          Φ (pt2 τ t) ∈ W) ∧
      IsCompact {y ∈ closure U | IsZeroAt P f y} ∧
      (∀ (n : ℕ) [ParacompactSpace ((Fin n → ℝ) × X)]
        [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
        (Φ : (Fin n → ℝ) → X), (rnPolyfold n).IsScSmoothMap PX Φ →
        (∀ q ∈ Icc (0 : Fin n → ℝ) 1, Φ q ∈ W) →
        ∃ S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X),
          (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S ∧
          (∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
            (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q, Φ q)) ∧
          ∀ q ∈ Icc (0 : Fin n → ℝ) 1, ∀ q' ∈ Icc (0 : Fin n → ℝ) 1, Φ q = Φ q' →
            ∀ y, (S (q, y)).1.2 = (S (q', y)).1.2) ∧
      ∀ (n : ℕ) [ParacompactSpace ((Fin n → ℝ) × X)]
        [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))],
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).HasScPlusSectionsThrough := by
  classical
  obtain ⟨c, hc, hxc⟩ := StrongBundle.exists_chart_mem B x
  set u₀ := c.φ x with hu₀
  set r := StrongRetr.r c.R with hr
  have hu₀O : u₀ ∈ c.φ.model.O := c.φ.mapsTo_model x hxc
  have hOU : ∀ {u}, u ∈ c.φ.model.O → u ∈ c.U := fun hu =>
    StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ hu)
  have hrO : ∀ {u}, u ∈ c.U → r u ∈ c.φ.model.O := fun hu => c.r_mem_O hu
  have hrfix : ∀ {u}, u ∈ c.φ.model.O → r u = u := fun hu =>
    StrongRetr.r_eq_self c.isRetraction (c.r_image ▸ hu)
  have hCconv : Convex ℝ c.φ.model.C := c.relOpen.isPartialQuadrant.convex
  obtain ⟨O', hO'o, hO'⟩ := c.relOpen.relOpen
  have hUC : c.U ⊆ c.φ.model.C := by rw [hO']; exact inter_subset_right
  -- `B_δ ∩ C ⊆ U` (the domain of the retraction)
  obtain ⟨δ, hδ, hδO'⟩ := Metric.isOpen_iff.1 hO'o u₀ (by
    have := hOU hu₀O
    rw [hO'] at this
    exact this.1)
  have hballU : ∀ {u}, u ∈ Metric.ball u₀ δ → u ∈ c.φ.model.C → u ∈ c.U := fun h1 h2 => by
    rw [hO']; exact ⟨hδO' h1, h2⟩
  -- `r(B_{δ₂} ∩ U) ⊆ B_δ` (continuity of `r` at level `0`)
  have hrcont : ContinuousOn r c.U :=
    (c.isRetraction.baseRetraction c.relOpen).isScSmooth.isSc1.isSc0.continuousOn_base
  obtain ⟨δ₂, hδ₂, hδ₂r⟩ := Metric.mem_nhdsWithin_iff.1
    ((hrcont u₀ (hOU hu₀O)).preimage_mem_nhdsWithin
      (by rw [hrfix hu₀O]; exact Metric.ball_mem_nhds u₀ hδ))
  -- a closed neighbourhood `T` of `x` on which the solution set is compact
  obtain ⟨N, hN, hNcpt⟩ := exists_nhds_isCompact_zeros hf x
  obtain ⟨T, hT, hTc, hTN⟩ := exists_mem_nhds_isClosed_subset hN
  obtain ⟨δ₃, hδ₃, hδ₃T⟩ := Metric.mem_nhdsWithin_iff.1
    ((c.φ.continuousOn_invFun u₀ hu₀O).preimage_mem_nhdsWithin
      (by rw [show c.φ.toPartialEquiv.symm u₀ = x from c.φ.symm_apply_apply hxc]; exact hT))
  set δ' := min δ (min δ₂ δ₃) with hδ'def
  have hδ' : 0 < δ' := lt_min hδ (lt_min hδ₂ hδ₃)
  set W : Set X := c.φ.source ∩ c.φ ⁻¹' Metric.ball u₀ δ with hWdef
  set U : Set X := c.φ.source ∩ c.φ ⁻¹' Metric.ball u₀ δ' with hUdef
  have hWo : IsOpen W :=
    c.φ.continuousOn_toFun.isOpen_inter_preimage c.φ.isOpen_source Metric.isOpen_ball
  have hUo : IsOpen U :=
    c.φ.continuousOn_toFun.isOpen_inter_preimage c.φ.isOpen_source Metric.isOpen_ball
  have hxU : x ∈ U := ⟨hxc, Metric.mem_ball_self hδ'⟩
  have hUW : U ⊆ W := fun y hy => ⟨hy.1, Metric.ball_subset_ball (min_le_left _ _) hy.2⟩
  have hUT : U ⊆ T := fun y hy => by
    have := hδ₃T ⟨Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hy.2,
      c.φ.mapsTo_model y hy.1⟩
    rwa [mem_preimage, show c.φ.toPartialEquiv.symm (c.φ y) = y from
      c.φ.symm_apply_apply hy.1] at this
  refine ⟨U, W, c, hUo, hWo, hxU, hUW, hc, inter_subset_left, ?_, ?_, ?_, ?_⟩
  · -- (1′): the straight-line homotopy in the chart, followed by `r`
    intro γ₀ γ₁ hγ₀ hγ₁ hγ₀U hγ₁U h0 h1
    have hγ₀c : Continuous γ₀ := continuousOn_univ.1 hγ₀.continuousOn
    have hγ₁c : Continuous γ₁ := continuousOn_univ.1 hγ₁.continuousOn
    -- a reparametrization keeping both paths in `U`
    set A : Set (Fin 1 → ℝ) := γ₀ ⁻¹' U ∩ γ₁ ⁻¹' U with hAdef
    have hAo : IsOpen A := (hUo.preimage hγ₀c).inter (hUo.preimage hγ₁c)
    have hpt1 : ∀ p : Fin 1 → ℝ, pt1 (p 0) = p := fun p =>
      funext fun i => by rw [Fin.fin_one_eq_zero i]; rfl
    have hIA : Icc (0 : Fin 1 → ℝ) 1 ⊆ A := fun p hp => by
      have hp0 : p 0 ∈ Icc (0 : ℝ) 1 := ⟨hp.1 0, hp.2 0⟩
      rw [← hpt1 p]
      exact ⟨hγ₀U _ hp0, hγ₁U _ hp0⟩
    obtain ⟨σ, hσ, hσid, hσA⟩ := exists_contDiff_eq_id_near_Icc_mapsTo hAo hIA
    have hσI : ∀ t ∈ Icc (0 : ℝ) 1, σ (pt1 t) = pt1 t := fun t ht =>
      hσid.self_of_nhdsSet _ ⟨fun _ => ht.1, fun _ => ht.2⟩
    -- the homotopy
    set ρ : ℝ → ℝ := Real.smoothTransition with hρdef
    set k : (Fin 2 → ℝ) → Fin 1 → ℝ := fun p => σ (pt1 (p 1)) with hkdef
    have hk : ContDiff ℝ ∞ k := hσ.comp (contDiff_pi.2 fun _ => contDiff_apply ℝ ℝ (1 : Fin 2))
    set v₀ : (Fin 2 → ℝ) → c.φ.model.E 0 := fun p => c.φ (γ₀ (k p)) with hv₀def
    set v₁ : (Fin 2 → ℝ) → c.φ.model.E 0 := fun p => c.φ (γ₁ (k p)) with hv₁def
    set G₀ : (Fin 2 → ℝ) → c.φ.model.E 0 := fun p => (1 - ρ (p 0)) • v₀ p + ρ (p 0) • v₁ p
      with hG₀def
    set Φ : (Fin 2 → ℝ) → X := fun p => c.φ.symm (r (G₀ p)) with hΦdef
    have hkU₀ : ∀ p, γ₀ (k p) ∈ U := fun p => (hσA _).1
    have hkU₁ : ∀ p, γ₁ (k p) ∈ U := fun p => (hσA _).2
    have hvB : ∀ {y}, y ∈ U → c.φ y ∈ Metric.ball u₀ δ' ∩ c.φ.model.C := fun hy =>
      ⟨hy.2, hUC (hOU (c.φ.mapsTo_model _ hy.1))⟩
    have hG₀B : ∀ p, G₀ p ∈ Metric.ball u₀ δ' ∩ c.φ.model.C := fun p =>
      ((convex_ball u₀ δ').inter hCconv) (hvB (hkU₀ p)) (hvB (hkU₁ p))
        (sub_nonneg.2 (Real.smoothTransition.le_one _)) (Real.smoothTransition.nonneg _)
        (sub_add_cancel 1 _)
    have hG₀U : ∀ p, G₀ p ∈ c.U := fun p =>
      hballU (Metric.ball_subset_ball (min_le_left _ _) (hG₀B p).1) (hG₀B p).2
    have hrG₀ : ∀ p, r (G₀ p) ∈ Metric.ball u₀ δ := fun p =>
      hδ₂r ⟨Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) (hG₀B p).1,
        hG₀U p⟩
    have hfix : ∀ y ∈ c.φ.source, c.φ.symm (r (c.φ y)) = y := fun y hy => by
      rw [hrfix (c.φ.mapsTo_model y hy), c.φ.symm_apply_apply hy]
    have hΦapp : ∀ τ t, Φ (pt2 τ t) = c.φ.symm (r ((1 - ρ τ) • c.φ (γ₀ (σ (pt1 t))) +
        ρ τ • c.φ (γ₁ (σ (pt1 t))))) := fun _ _ => rfl
    have hρ₀ : ρ 0 = 0 := Real.smoothTransition.zero
    have hρ₁ : ρ 1 = 1 := Real.smoothTransition.one
    have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    refine ⟨Φ, ⟨?_, fun t ht => ?_, fun t ht => ?_, fun τ _ => ?_, fun τ _ => ?_⟩,
      fun τ _ t _ => ?_⟩
    · -- sc-smoothness, read in the chart
      have hU2 := isScDomain_univ (rnSc 2)
      have hv₀ : IsScSmooth (E := rnSc 2) (F := c.φ.model.E) univ v₀ :=
        isScSmooth_chart_comp (hγ₀.comp (isScSmoothMap_rn_rn_of_contDiff hk)) c.isChart
          fun p => (hkU₀ p).1
      have hv₁ : IsScSmooth (E := rnSc 2) (F := c.φ.model.E) univ v₁ :=
        isScSmooth_chart_comp (hγ₁.comp (isScSmoothMap_rn_rn_of_contDiff hk)) c.isChart
          fun p => (hkU₁ p).1
      have hρ0 : IsScSmooth (E := rnSc 2) (F := ScBanach.const ℝ) univ
          fun p : Fin 2 → ℝ => ρ (p 0) :=
        IsScSmooth.of_contDiffOn_finiteDimensional (V := ℝ) hU2
          ((Real.smoothTransition.contDiff.comp (contDiff_apply ℝ ℝ (0 : Fin 2))).contDiffOn)
      have hρ1 : IsScSmooth (E := rnSc 2) (F := ScBanach.const ℝ) univ
          fun p : Fin 2 → ℝ => 1 - ρ (p 0) :=
        IsScSmooth.of_contDiffOn_finiteDimensional (V := ℝ) hU2 ((contDiff_const.sub
          (Real.smoothTransition.contDiff.comp (contDiff_apply ℝ ℝ (0 : Fin 2)))).contDiffOn)
      have hG₀ : IsScSmooth (E := rnSc 2) (F := c.φ.model.E) univ G₀ :=
        (hρ1.smul hU2 hv₀).add hU2 (hρ0.smul hU2 hv₁)
      have hrG : IsScSmooth (E := rnSc 2) (F := c.φ.model.E) univ fun p => r (G₀ p) :=
        IsScSmooth.comp hU2 c.relOpen.isScDomain
          (c.isRetraction.baseRetraction c.relOpen).isScSmooth hG₀ fun p _ => hG₀U p
      exact isScSmoothMap_rn_chart_symm c.isChart hrG fun p => hrO (hG₀U p)
    · rw [hΦapp, hσI t ht, hρ₀, sub_zero, one_smul, zero_smul, add_zero]
      exact hfix _ (hγ₀U t ht).1
    · rw [hΦapp, hσI t ht, hρ₁, sub_self, zero_smul, one_smul, zero_add]
      exact hfix _ (hγ₁U t ht).1
    · rw [hΦapp, hσI 0 h0I, ← h0, ← add_smul, sub_add_cancel, one_smul]
      exact hfix _ (hγ₀U 0 h0I).1
    · rw [hΦapp, hσI 1 h1I, ← h1, ← add_smul, sub_add_cancel, one_smul]
      exact hfix _ (hγ₀U 1 h1I).1
    · refine ⟨c.φ.symm_mapsTo (hrO (hG₀U _)), ?_⟩
      change c.φ (c.φ.symm (r (G₀ (pt2 τ t)))) ∈ Metric.ball u₀ δ
      rw [c.φ.apply_symm_apply (hrO (hG₀U _))]
      exact hrG₀ _
  · -- (2): `cl(U) ⊆ T ⊆ N`
    exact hNcpt _ isClosed_closure ((closure_minimal hUT hTc).trans hTN)
  · -- (3)
    intro n _ _ Φ hΦ hΦW
    exact exists_isScPlusSection_pullback_of_family_of_chart hch hf.isScSmooth hΦ
  · -- (4)
    intro n _ _
    exact (hch.elim fun _ h => hasScPlusSectionsThrough_pullback_rn_of_chart h.1 h.2)

/-! ### General position along a compact set of zeros -/

section Compact

/-- **Sections putting `F` in general position along a compact set of zeros, from sections
through the fibre points** (`exists_sections_isGeneralPositionGerm_of_isCompact` with
`StrongBundle.HasScPlusSectionsThrough` in place of sc-smooth bump functions): let `X` be tame,
`g` an sc-Fredholm section with tame germ data and `K` a compact set of zeros of `g`.  Then there
are finitely many sc⁺-sections `s₁, …, s_k` and an open `W ⊇ K` such that
`F(λ, y) = g(y) + Σ λᵢ sᵢ(y)` is in general position (Definition 5.3.9) at `(0, y)` for every
zero `y ∈ W` of `g`. -/
theorem exists_sections_isGeneralPositionGerm_of_isCompact_of_sections
    (hX : PX.IsTame)
    (hsec : B.HasScPlusSectionsThrough) {g : X → Y} (hg : B.IsScFredholmSectionTame g)
    {K : Set X} (hK : IsCompact K) (hK0 : ∀ x ∈ K, IsZeroAt P g x) :
    ∃ (k : ℕ) (s : Fin k → X → Y) (hs : ∀ i, B.IsScPlusSection (s i)) (W : Set X),
      IsOpen W ∧ K ⊆ W ∧
      ∀ [ParacompactSpace ((Fin k → ℝ) × X)]
        [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))],
        ∀ y ∈ W, IsZeroAt P g y →
          (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsGeneralPositionGerm
            (paramSection g hg.isScSmooth.1 s fun i => (hs i).1) (0, y) := by
  classical
  have hgF : B.IsScFredholmSection g := hg.toIsScFredholmSection
  -- a tame chart centred at every zero of `g`, with a presentation
  have hch : ∀ y : solutionSet P g, ∃ c : StrongBundleChart PX P,
      B.IsTameChart c ∧ (y : X) ∈ c.φ.source ∧ c.φ y = 0 := fun y => by
    obtain ⟨-, c, hc, hyc, hφ0, -⟩ := hg.germTame y (hgF.mem_smoothSet_of_isZeroAt y.2)
    exact ⟨c, hc, hyc, hφ0⟩
  choose c hc hyc hφ0 using hch
  have hpres : ∀ y : solutionSet P g, ∃ (n : ℕ) (Wq : ScBanach)
      (T : ScIso (c y).φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)),
      (c y).φ.model.C = T 0 ⁻¹' quadrant n Wq 0 := fun y => (c y).φ.model.isPartialQuadrant
  choose n Wq T hT using hpres
  -- at every point of `K`: sections with (i)–(ii), and a neighbourhood where `F_x` is general
  have hfam : ∀ x : K, ∃ (k : ℕ) (s : Fin k → X → Y) (hsp : ∀ i, B.IsScPlusSection (s i)),
      ∃ Ux : Set X, IsOpen Ux ∧ (x : X) ∈ Ux ∧ ∀ y ∈ Ux, IsZeroAt P g y →
        haveI := MPolyfold.paracompactSpace_prod (rnPolyfold k) PX
        haveI := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin k → ℝ) × X → X))
          ((rnPolyfold k).prod PX) B
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsGeneralPositionGerm
          (paramSection g hg.isScSmooth.1 s fun i => (hsp i).1) (0, y) := by
    intro x
    have hx0 : IsZeroAt P g x := hK0 x x.2
    obtain ⟨k, s, hsp, hgpx⟩ := exists_sections_isParamGP_of_sections hsec hg hx0
      (hc ⟨x, hx0⟩) (hyc ⟨x, hx0⟩) (hφ0 ⟨x, hx0⟩) (T ⟨x, hx0⟩) (hT ⟨x, hx0⟩)
    have := MPolyfold.paracompactSpace_prod (rnPolyfold k) PX
    have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin k → ℝ) × X → X))
      ((rnPolyfold k).prod PX) B
    have hFt := theorem_3_1_21_tame hg hsp
    have hz0 : ∀ y, IsZeroAt P g y → IsZeroAt (pullbackProj P Prod.snd)
        (paramSection g hg.isScSmooth.1 s fun i => (hsp i).1) (0, y) := fun y hy =>
      isZeroAt_paramSection_zero hg.isScSmooth.1 (fun i => (hsp i).1) hy
    have h0 := isGeneralPositionGerm_paramSection_of_isParamGP hg hsp hx0 (hc ⟨x, hx0⟩)
      (hyc ⟨x, hx0⟩) (hφ0 ⟨x, hx0⟩) (T ⟨x, hx0⟩) (hT ⟨x, hx0⟩) hgpx
    obtain ⟨W, hWo, h0W, -, hW⟩ :=
      exists_isOpen_isGeneralPositionGerm (prod_rn_isTame hX) hFt (hz0 x hx0) h0
    exact ⟨k, s, hsp, Prod.mk 0 ⁻¹' W, hWo.preimage (continuous_const.prodMk continuous_id),
      h0W, fun y hy hy0 => (hW (0, y) hy (hz0 y hy0)).2.1⟩
  choose k s hsp Ux hUxo hxUx hUx using hfam
  -- a finite subcover of `K`, and the united family `t`
  obtain ⟨T₀, hT₀⟩ := hK.elim_finite_subcover Ux hUxo
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxUx ⟨x, hx⟩⟩)
  let e := Fintype.equivFin (Σ x : T₀, Fin (k x.1))
  set m := Fintype.card (Σ x : T₀, Fin (k x.1)) with hm
  set t : Fin m → X → Y := fun j => s (e.symm j).1.1 (e.symm j).2 with htdef
  have ht : ∀ j, B.IsScPlusSection (t j) := fun j => hsp _ _
  refine ⟨m, t, ht, ⋃ x ∈ T₀, Ux x, isOpen_biUnion fun x _ => hUxo x, hT₀, ?_⟩
  -- `F` is in general position at every `(0, y)`, `y ∈ W` a zero
  intro _ _ y hyW hy
  obtain ⟨x, hxT, hyUx⟩ := mem_iUnion₂.1 hyW
  have := MPolyfold.paracompactSpace_prod (rnPolyfold (k x)) PX
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin (k x) → ℝ) × X → X))
    ((rnPolyfold (k x)).prod PX) B
  have hgx := hUx x y hyUx hy
  have hpx := isParamGP_of_isGeneralPositionGerm hg (hsp x) hy (hc ⟨y, hy⟩) (hyc ⟨y, hy⟩)
    (hφ0 ⟨y, hy⟩) (T ⟨y, hy⟩) (hT ⟨y, hy⟩) hgx
  have hpt := hpx.comp (fun i => e ⟨⟨x, hxT⟩, i⟩) (t := t) (fun i => by
    have := congrArg (fun σ : (Σ x : T₀, Fin (k x.1)) => s σ.1.1 σ.2)
      (e.symm_apply_apply ⟨⟨x, hxT⟩, i⟩)
    exact this.symm)
  exact isGeneralPositionGerm_paramSection_of_isParamGP hg ht hy (hc ⟨y, hy⟩)
    (hyc ⟨y, hy⟩) (hφ0 ⟨y, hy⟩) (T ⟨y, hy⟩) (hT ⟨y, hy⟩) hpt

end Compact

/-! ### Lemma 6.6.4 -/

section Lemma664

variable {n : ℕ} [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- **Lemma 6.6.4 for a bundle with a chart over the whole base** (`lemma_6_6_4` without
sc-smooth bump functions): let `X` be tame, `f` an sc-Fredholm section with tame germ data,
`Φ : ℝⁿ → X` sc-smooth and `S` an sc⁺-section of `π*Y → ℝⁿ × X` with `(f̃ + S)(q, Φ(q)) = 0` for
`q` near `[0, 1]ⁿ`.  Then there are finitely many sc⁺-sections `s₁, …, s_k` of `π*Y` such that
`F(λ, (q, y)) = f(y) + S(q, y) + Σ λᵢ sᵢ(q, y)` is in general position (Definition 5.3.9) at
`(0, (q, Φ(q)))` for all `q` near `[0, 1]ⁿ`.  *Proof*: as for `lemma_6_6_4`, the sc⁺-sections
through the fibre points of `π*Y` coming from the product chart
(`hasScPlusSectionsThrough_pullback_rn_of_chart`). -/
theorem lemma_6_6_4_of_chart (hX : PX.IsTame) (hch : ∃ c ∈ B.atlas.charts, c.φ.source = univ)
    (hf : B.IsScFredholmSectionTame f) {Φ : (Fin n → ℝ) → X}
    (hΦ : (rnPolyfold n).IsScSmoothMap PX Φ)
    {S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S)
    (hz : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q, Φ q)) :
    ∃ (k : ℕ) (s : Fin k → (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
      (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection
        (s i)),
      ∀ [ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
        [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
          (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))],
        ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1),
          ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
            (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
              ((rnPolyfold n).prod PX))).IsGeneralPositionGerm
            (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
              ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (0, (q, Φ q)) := by
  have hΦc : Continuous Φ := continuousOn_univ.1 hΦ.continuousOn
  have hγ : Continuous fun q : Fin n → ℝ => (q, Φ q) := continuous_id.prodMk hΦc
  have hg := theorem_3_1_18_tame hf.param hS
  have hK : IsCompact ((fun q : Fin n → ℝ => (q, Φ q)) '' Icc 0 1) :=
    isCompact_Icc.image hγ
  have hK0 : ∀ x ∈ (fun q : Fin n → ℝ => (q, Φ q)) '' Icc 0 1, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) x := by
    rintro _ ⟨q, hq, rfl⟩
    exact hz.self_of_nhdsSet q hq
  obtain ⟨k, s, hs, W, hWo, hKW, hW⟩ :=
    exists_sections_isGeneralPositionGerm_of_isCompact_of_sections (prod_rn_isTame hX)
      (hch.elim fun _ h => hasScPlusSectionsThrough_pullback_rn_of_chart h.1 h.2) hg hK hK0
  refine ⟨k, s, hs, ?_⟩
  intro _ _
  have hWq : (fun q : Fin n → ℝ => (q, Φ q)) ⁻¹' W ∈ 𝓝ˢ (Icc (0 : Fin n → ℝ) 1) :=
    (hWo.preimage hγ).mem_nhdsSet.2 fun q hq => hKW ⟨q, hq, rfl⟩
  filter_upwards [hz, hWq] with q hq hqW
  exact hW _ hqW hq

end Lemma664

end Polyfold
