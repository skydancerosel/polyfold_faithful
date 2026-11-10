import Polyfold.Chapter5.Book2021
import Polyfold.Chapter6.OrientationConvention2021
import Polyfold.Chapter6.PropagationWellDefined
import Polyfold.Chapter6.SolutionOrientationCharts

/-!
# Admissible sections and the cobordism between them (2021 §5.3, §6.7)

Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021): the perturbation results
that the proof of Theorem 6.7.1 (p. 277; preprint Theorem 6.43) uses.

* Auxiliary norms (Definition 5.1.1, p. 205): `IsAuxNorm.const_mul`, `IsAuxNorm.max`,
  `exists_isAuxNorm_ge` (finitely many norms are dominated by one), `allowableSections_max_subset`,
  `allowableSections_mono`, and `IsAuxNorm.pullback` (the norm `N ∘ π` of a pull-back bundle).
* The neighbourhood `U` of the §6.7 preamble (p. 276) with a margin, `exists_adapted_margin`:
  `cl{x ∈ U | N(f(x)) ≤ C}` compact for every `C > 0` (we use `C = 2`), and `S_{f+s}` compact for
  every `s` allowable for `(N, U)`.
* `theorem_5_3_10_relative_hyp`: Theorem 5.3.10 (p. 220; preprint Theorem 5.18) relative to a
  compact part `K ⊆ W` of the zero set, for a section already in general position off `K`, with the
  perturbation supported in `W`. It re-assembles the mechanism of `theorem_5_3_10_param`
  (the families `F(λ, x) = G(x) + Σ λᵢ sᵢ(x)`, Theorem 4.3.1 and Sard).
* Admissible sections (§6.7 preamble): `exists_admissible`, `exists_admissible_subset`
  (one section admissible for finitely many norms), `exists_admissible_two` (for two pairs
  `(N₀, U₀)`, `(N₁, U₁)`), `exists_cobordism_data`.
* General position of lifts: `isGeneralPositionGerm_paramLift` (`(g, y)` general gives
  `(g̃, (r, y))` general for the lift to `ℝᵐ × X`), the chart criterion
  `isGeneralPositionGerm_of_sup_eq`, and the locality `isGeneralPositionGerm_congr_nhds`.
* `exists_cobordism` (Remark 5.3.8, p. 219, as the proof of Theorem 6.7.1 uses it, p. 278): two
  sections admissible for `(N, U)` are joined by an sc⁺-section `S` of the pull-back to `ℝ¹ × X`,
  equal to `s₀` for `t ≤ 1/8` and to `s₁` for `t ≥ 7/8`, with `f̃ + S` in general position at every
  zero and compact zero sets over compact `t`-intervals.

The text's cobordism lives over `[0, 1] × X`; we use `ℝ¹ × X` with a section stationary near the
ends (reading D2 of the Theorem 6.7.1 plan), so that `[0, 1] × X` never has to be a tame
M-polyfold with the extra boundary.
-/

open Set Filter Topology Function MeasureTheory

noncomputable section

namespace Polyfold

universe u v

/-! ### Auxiliary norms: positive multiples and maxima -/

section AuxNorms

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

namespace StrongBundle

/-- A positive multiple `a·N` of an auxiliary norm is an auxiliary norm (2021 Definition 5.1.1,
p. 205; preprint Definition 5.1). -/
theorem IsAuxNorm.const_mul {N : B.One → ℝ} (hN : B.IsAuxNorm N) {a : ℝ} (ha : 0 < a) :
    B.IsAuxNorm fun w => a * N w where
  continuous := continuous_const.mul hN.continuous
  fiber x :=
    { eq_zero := fun v hv => (hN.fiber x).eq_zero v
        ((mul_eq_zero.1 hv).resolve_left ha.ne')
      smul := fun t v => by rw [(hN.fiber x).smul]; ring
      add_le := fun v w => by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left ((hN.fiber x).add_le v w) ha.le
      complete := fun u hu => by
        obtain ⟨v, hv⟩ := (hN.fiber x).complete u fun ε hε => by
          obtain ⟨n, hn⟩ := hu (a * ε) (mul_pos ha hε)
          exact ⟨n, fun m hm k hk => (mul_lt_mul_iff_of_pos_left ha).1 (hn m hm k hk)⟩
        exact ⟨v, by simpa using hv.const_mul a⟩ }
  tendsto_zeroOne w x hw hNw := hN.tendsto_zeroOne w x hw (by
    simpa [← mul_assoc, inv_mul_cancel₀ ha.ne'] using hNw.const_mul a⁻¹)

/-- The pointwise maximum of two auxiliary norms is an auxiliary norm (2021 Definition 5.1.1,
p. 205); completeness of the fibres from the comparison of Proposition 5.1.3 (p. 206;
preprint Proposition 5.3), `N₁ ≤ f⁻¹·N₀`. -/
theorem IsAuxNorm.max {N₀ N₁ : B.One → ℝ} (h₀ : B.IsAuxNorm N₀) (h₁ : B.IsAuxNorm N₁) :
    B.IsAuxNorm fun w => Max.max (N₀ w) (N₁ w) where
  continuous := h₀.continuous.max h₁.continuous
  fiber x :=
    { eq_zero := fun v hv => (h₀.fiber x).eq_zero v
        (le_antisymm (hv ▸ le_max_left _ _) (h₀.nonneg _))
      smul := fun t v => by
        rw [(h₀.fiber x).smul, (h₁.fiber x).smul, mul_max_of_nonneg _ _ (abs_nonneg t)]
      add_le := fun v w => max_le
        (((h₀.fiber x).add_le v w).trans (add_le_add (le_max_left _ _) (le_max_left _ _)))
        (((h₁.fiber x).add_le v w).trans (add_le_add (le_max_right _ _) (le_max_right _ _)))
      complete := fun u hu => by
        obtain ⟨v, hv⟩ := (h₀.fiber x).complete u fun ε hε => by
          obtain ⟨n, hn⟩ := hu ε hε
          exact ⟨n, fun m hm k hk => (le_max_left _ _).trans_lt (hn m hm k hk)⟩
        obtain ⟨f, -, hfpos, hf⟩ := proposition_5_1_3_compare h₀ h₁
        have h1 : Tendsto (fun k => N₁ (B.toOne (u k - v))) atTop (𝓝 0) := by
          have hb : Tendsto (fun k => (f x)⁻¹ * N₀ (B.toOne (u k - v))) atTop (𝓝 0) := by
            simpa using hv.const_mul (f x)⁻¹
          refine squeeze_zero (fun k => h₁.nonneg _) (fun k => ?_) hb
          have := (hf (B.toOne (u k - v))).2
          rwa [B.proj_oneVal_toOne (u k - v)] at this
        exact ⟨v, by simpa using hv.max h1⟩ }
  tendsto_zeroOne w x hw hNw := h₀.tendsto_zeroOne w x hw
    (squeeze_zero (fun k => h₀.nonneg _) (fun k => le_max_left _ _) hNw)

/-- An sc⁺-section allowable for `max(N₀, N₁)` and `U` is allowable for `N₀` and for `N₁`, and
for every larger open set (the step "an `s₂` admissible for both pairs" of the proof of 2021
Theorem 6.7.1, p. 278). -/
theorem allowableSections_max_subset {N₀ N₁ : B.One → ℝ} {U U₀ U₁ : Set X} (hU₀ : U ⊆ U₀)
    (hU₁ : U ⊆ U₁) :
    B.allowableSections (fun w => Max.max (N₀ w) (N₁ w)) U ⊆
      B.allowableSections N₀ U₀ ∩ B.allowableSections N₁ U₁ := by
  rintro s ⟨hs, hsupp, hsN⟩
  exact ⟨⟨hs, hsupp.trans hU₀, fun x hx => (le_max_left _ _).trans (hsN x hx)⟩,
    ⟨hs, hsupp.trans hU₁, fun x hx => (le_max_right _ _).trans (hsN x hx)⟩⟩

/-- `AuxLe N y r` for the scaled norm `a·N` is `AuxLe N y (r / a)`. -/
lemma auxLe_const_mul_iff {N : B.One → ℝ} {a : ℝ} (ha : 0 < a) {y : Y} {r : ℝ} :
    B.AuxLe (fun w => a * N w) y r ↔ B.AuxLe N y (r / a) := by
  refine ⟨fun ⟨hy, h⟩ => ⟨hy, ?_⟩, fun ⟨hy, h⟩ => ⟨hy, ?_⟩⟩
  · rw [le_div_iff₀ ha, mul_comm]; exact h
  · rw [le_div_iff₀ ha, mul_comm] at h; exact h

/-- **The triangle inequality for `AuxLe`**: `N(f(x)) ≤ N((f + s)(x)) + N(s(x))`. -/
lemma IsAuxNorm.auxLe_of_sectionAdd_le {N : B.One → ℝ} (hN : B.IsAuxNorm N) {f s : X → Y}
    (hf : IsSection P f) (hs : IsSection P s) {x : X} {a b : ℝ}
    (hfs : B.AuxLe N (sectionAdd P f s x) a) (hsx : B.AuxLe N (s x) b) :
    B.AuxLe N (f x) (a + b) := by
  obtain ⟨h1, ha⟩ := hfs
  obtain ⟨h2, hb⟩ := hsx
  have e1 : (⟨sectionAdd P f s x, (hf.sectionAdd hs) x⟩ : P ⁻¹' {x}) =
      ⟨f x, hf x⟩ + ⟨s x, hs x⟩ := Subtype.ext (sectionAdd_apply hf hs x)
  set v : B.oneFiber x := ⟨⟨sectionAdd P f s x, (hf.sectionAdd hs) x⟩, h1⟩ with hv
  set w : B.oneFiber x := ⟨⟨s x, hs x⟩, h2⟩ with hw
  have hfv : f x = (((v - w : B.oneFiber x) : P ⁻¹' {x}) : Y) := by
    change f x = ((((⟨sectionAdd P f s x, (hf.sectionAdd hs) x⟩ : P ⁻¹' {x}) -
      ⟨s x, hs x⟩ : P ⁻¹' {x})) : Y)
    rw [e1, add_sub_cancel_right]
  refine ⟨hfv ▸ (v - w).2, ?_⟩
  have e2 : B.oneMk (f x) (hfv ▸ (v - w).2) = B.toOne (v - w) := B.oneVal_injective (by
    rw [oneVal_oneMk, oneVal_toOne, hfv])
  rw [e2, sub_eq_add_neg]
  refine ((hN.fiber x).add_le _ _).trans (add_le_add ha ?_)
  rw [← neg_one_smul ℝ w, hN.smul, abs_neg, abs_one, one_mul]
  exact hb

/-- **The triangle inequality for `AuxLe`**: `N((f + s)(x)) ≤ N(f(x)) + N(s(x))`. -/
lemma IsAuxNorm.auxLe_sectionAdd {N : B.One → ℝ} (hN : B.IsAuxNorm N) {f s : X → Y}
    (hf : IsSection P f) (hs : IsSection P s) {x : X} {a b : ℝ}
    (hfx : B.AuxLe N (f x) a) (hsx : B.AuxLe N (s x) b) :
    B.AuxLe N (sectionAdd P f s x) (a + b) := by
  obtain ⟨h1, ha⟩ := hfx
  obtain ⟨h2, hb⟩ := hsx
  set v : B.oneFiber x := ⟨⟨f x, hf x⟩, h1⟩ with hv
  set w : B.oneFiber x := ⟨⟨s x, hs x⟩, h2⟩ with hw
  have hfv : sectionAdd P f s x = (((v + w : B.oneFiber x) : P ⁻¹' {x}) : Y) :=
    sectionAdd_apply hf hs x
  refine ⟨hfv ▸ (v + w).2, ?_⟩
  have e2 : B.oneMk (sectionAdd P f s x) (hfv ▸ (v + w).2) = B.toOne (v + w) :=
    B.oneVal_injective (by rw [oneVal_oneMk, oneVal_toOne, hfv])
  rw [e2]
  exact ((hN.fiber x).add_le _ _).trans (add_le_add ha hb)

/-- **`AuxLe` of a multiple**: `N((a·s)(x)) = |a(x)|·N(s(x))`. -/
lemma IsAuxNorm.auxLe_sectionSmul {N : B.One → ℝ} (hN : B.IsAuxNorm N) {s : X → Y}
    (hs : IsSection P s) (a : X → ℝ) {x : X} {b : ℝ} (hsx : B.AuxLe N (s x) b) :
    B.AuxLe N (sectionSmul P a s x) (|a x| * b) := by
  obtain ⟨h2, hb⟩ := hsx
  set w : B.oneFiber x := ⟨⟨s x, hs x⟩, h2⟩ with hw
  have hfv : sectionSmul P a s x = (((a x • w : B.oneFiber x) : P ⁻¹' {x}) : Y) :=
    sectionSmul_apply hs x
  refine ⟨hfv ▸ (a x • w).2, ?_⟩
  have e2 : B.oneMk (sectionSmul P a s x) (hfv ▸ (a x • w).2) = B.toOne (a x • w) :=
    B.oneVal_injective (by rw [oneVal_oneMk, oneVal_toOne, hfv])
  rw [e2, hN.smul]
  exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)

end StrongBundle

end AuxNorms

/-! ### The adapted neighbourhood `U` with a margin -/

section Margin

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **The neighbourhood `U` of the §6.7 preamble (2021 p. 276), with a margin** (reading R-b of
the Theorem 6.7.1 plan): for an sc-Fredholm section with compact solution set, an auxiliary norm
`N` and any open `V ⊇ S_f`, there is an open `S_f ⊆ U ⊆ V` such that the closure of
`{x ∈ U | N(f(x)) ≤ C}` is compact for every `C > 0` (Theorem 5.2.2, p. 210, proper`<∞`), and
`S_{f+s}` is compact for every `s` allowable for `(N, U)` (Remark 5.3.4, p. 214; preprint
Remark 5.12). The text's `U` of Theorem 5.3.10 has the first property for `C = 1`; the margin
`C = 2` is what the cobordism `exists_cobordism` uses. -/
theorem exists_adapted_margin (hf : B.IsScFredholmSection f) (hS : IsCompact (solutionSet P f))
    {N : B.One → ℝ} (hN : B.IsAuxNorm N) {V : Set X} (hV : IsOpen V)
    (hSV : solutionSet P f ⊆ V) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧ U ⊆ V ∧
      (∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U | B.AuxLe N (f x) C})) ∧
      ∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s)) := by
  obtain ⟨-, h⟩ := theorem_5_2_2 hf hS
  obtain ⟨U₀, hU₀o, hSU₀, hK⟩ := h N hN
  have hK' : ∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U₀ ∩ V | B.AuxLe N (f x) C}) :=
    fun C hC => (hK C hC).of_isClosed_subset isClosed_closure
      (closure_mono fun x hx => ⟨hx.1.1, hx.2⟩)
  refine ⟨U₀ ∩ V, hU₀o.inter hV, subset_inter hSU₀ hSV, inter_subset_right, hK', ?_⟩
  rintro s ⟨hs, hssupp, hsN⟩
  have hsU : ∀ x ∉ U₀ ∩ V, IsZeroAt P s x := fun x hx =>
    not_not.1 fun hne => hx (hssupp (subset_closure hne))
  have hsN' : ∀ x, B.AuxLe N (s x) 1 := fun x => ⟨hs.mem_oneSet x, hsN x _⟩
  obtain ⟨-, hcl⟩ := remark_5_3_4 hN hf.isScSmooth.1 (subset_inter hSU₀ hSV) (hK' 1 one_pos)
    hs.1 hsU hsN'
  exact hcl.of_isClosed_subset
    (isClosed_solutionSet (theorem_3_1_18_preprint hf hs).isScSmooth) subset_closure

end Margin

/-! ### General position: locality, and general position of the families `F` -/

section GeneralPositionTools

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {g : X → Y}

open StrongRetr

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
lemma isZeroAt_congr {f f' : X → Y} {x : X} (h : f x = f' x) :
    IsZeroAt P f x ↔ IsZeroAt P f' x := by
  unfold IsZeroAt; rw [h]

/-- **General position is a property of the germ** (2021 Definition 5.3.9, p. 220; preprint
Definition 5.17): if `f = f'` near the zero `y`, both with tame germ data, and `(f, y)` is in
general position, so is `(f', y)` (through the general position of the solution set,
`exists_isGeneralPositionGerm_iff`, which is local). -/
theorem isGeneralPositionGerm_congr_nhds {f f' : X → Y} (hf : B.IsScFredholmSectionTame f)
    (hf' : B.IsScFredholmSectionTame f') {y : X} (hy0 : IsZeroAt P f y) {O : Set X}
    (hO : IsOpen O) (hyO : y ∈ O) (heq : ∀ x ∈ O, f x = f' x)
    (h : B.IsGeneralPositionGerm f y) : B.IsGeneralPositionGerm f' y := by
  have hy0' : IsZeroAt P f' y := (isZeroAt_congr (heq y hyO)).1 hy0
  have hgood := h.isGoodPositionGermTame hf hy0
  have hgood' := hgood.congr_nhds hO hyO heq
  obtain ⟨V, hVo, hyV, -, hA, hiff, -⟩ := exists_isGeneralPositionGerm_iff hf hgood hy0
  obtain ⟨V', hV'o, hyV', -, hA', hiff', -⟩ := exists_isGeneralPositionGerm_iff hf' hgood' hy0'
  refine (hiff' y hyV' hy0').2 ?_
  refine MPolyfold.IsGeneralPositionAt.congr_nhds hA hA' ((hVo.inter hV'o).inter hO)
    ⟨⟨hyV, hyV'⟩, hyO⟩ ?_ ((hiff y hyV hy0).1 h)
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨⟨hx0, -⟩, ⟨hxV, hxV'⟩, hxO⟩
    exact ⟨⟨(isZeroAt_congr (heq x hxO)).1 hx0, hxV'⟩, ⟨hxV, hxV'⟩, hxO⟩
  · rintro ⟨⟨hx0, -⟩, ⟨hxV, hxV'⟩, hxO⟩
    exact ⟨⟨(isZeroAt_congr (heq x hxO)).2 hx0, hxV⟩, ⟨hxV, hxV'⟩, hxO⟩

/-- **A germ in general position has properties (i)–(ii) with no added sections** (the empty
family; the proof of 2021 Theorem 5.3.10, p. 216): in every tame chart `c` centred at the zero
`y`, `Lin_g(0)` is onto and `T₀O = ker Lin_g(0) + E_0` (through the general position of the
solution set, as in `isParamGP_of_isGeneralPositionGerm`). -/
theorem isParamGP_elim0_of_isGeneralPositionGerm (hgFt : B.IsScFredholmSectionTame g) {y : X}
    (hy0 : IsZeroAt P g y) {c : StrongBundleChart PX P} (hc : B.IsTameChart c)
    (hyV : y ∈ c.φ.source) (hφ0 : c.φ y = 0) {n : ℕ} {Wq : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0) (hgp : B.IsGeneralPositionGerm g y) :
    c.IsParamGP g (Fin.elim0 : Fin 0 → X → Y) T := by
  classical
  have hz : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = c.φ y := by rw [map_zero, hφ0]
  have hsurj := hgp.isLinSurjAt.linAt_surjective hgFt.isScSmooth hy0 hc.1 hyV hz
  refine ⟨fun k' hk' => ?_, fun w => ?_⟩
  · have hk : (c.φ y, k') ∈ c.K := by rw [hφ0]; exact hk'
    obtain ⟨v, hvk⟩ := hsurj k' hk
    exact ⟨v, 0, by simpa using hvk⟩
  · have hgood := hgp.isGoodPositionGermTame hgFt hy0
    obtain ⟨V, -, hyV0, -, hAV, hiff, hidV⟩ := exists_isGeneralPositionGerm_iff hgFt hgood hy0
    have hyA : y ∈ solutionSet P g ∩ V := ⟨hy0, hyV0⟩
    have hA := (hiff _ hyV0 hy0).1 hgp
    set d := hAV.data hyA with hd
    obtain ⟨N, M, Bs, hN, hM, hBM, -, hsplit⟩ := hA.isGeneralPositionChart d c.isChart T hT
      (hAV.mem_data_V hyA) hyV hz
    have hyG : y ∈ d.toSubData.shrink c.φ :=
      d.toSubData.mem_shrink _ hyA (hAV.mem_data_V hyA) hyV
    have hT0 := hidV _ hyV0 hy0 _ hc.1 hyV _ (d.toSubData.isOpen_shrink _)
      (d.toSubData.shrink_subset_source _) hyG
      (d.toSubData.isScRetract_image _ c.isChart) 0 hz
    have hNeq : N = c.linKer g 0 := SetLike.coe_injective (hN.trans hT0)
    have hzO : (0 : c.φ.model.E 1) ∈
        c.φ.model.E.lvlSet ((c.isRetraction.baseRetraction c.relOpen).retract) 1 := by
      rw [ScBanach.mem_lvlSet, c.base_retract, hz]
      exact c.φ.mapsTo_model _ hyV
    have hMeq : M = rangeS (scDeriv c.U (r c.R) 0) := by
      apply SetLike.coe_injective
      rw [hM, ← c.base_retract]
      exact tangentSpace_eq_coe_submodule _ hzO
    have h0 := hsplit 0
    rw [ScBanach.levelSub_zero, ScBanach.levelSub_zero, ScBanach.levelSub_zero] at h0
    have hp : (w : c.φ.model.E 0) ∈ M := by rw [hMeq]; exact w.2
    rw [← h0.2] at hp
    obtain ⟨k, hk, b, hb, hkb⟩ := Submodule.mem_sup.1 hp
    rw [hNeq] at hk
    obtain ⟨hkr, hk0⟩ := (c.mem_linKer_iff _ 0 k).1 hk
    have hbmin := (hBM hb).2
    have hb0' : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = 0 := map_zero _
    rw [hb0'] at hbmin
    refine ⟨⟨k, hkr⟩, 0, by simpa using hk0, ?_⟩
    rw [← hkb, add_sub_cancel_left]
    exact hbmin

variable {m : ℕ} [ParacompactSpace ((Fin m → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))]

/-- **A germ in general position stays so in every family** (the text: adding sections keeps
properties (i)–(ii), proof of 2021 Theorem 5.3.10, p. 216): if `(g, y)` is in general position,
then `F(λ, x) = g(x) + Σ λᵢ tᵢ(x)` is in general position at `(0, y)`. -/
theorem isGeneralPositionGerm_paramSection_of_isGeneralPositionGerm
    (hgFt : B.IsScFredholmSectionTame g) {t : Fin m → X → Y}
    (htp : ∀ i, B.IsScPlusSection (t i)) {y : X} (hy0 : IsZeroAt P g y)
    (hgp : B.IsGeneralPositionGerm g y) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGeneralPositionGerm
      (paramSection g hgFt.isScSmooth.1 t fun i => (htp i).1) (0, y) := by
  obtain ⟨-, c, hc, hyc, hφ0, -⟩ :=
    hgFt.germTame y (hgFt.toIsScFredholmSection.mem_smoothSet_of_isZeroAt hy0)
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  have h0 := isParamGP_elim0_of_isGeneralPositionGerm hgFt hy0 hc hyc hφ0 T hT hgp
  have h1 : c.IsParamGP g t T := h0.comp Fin.elim0 (fun i => i.elim0)
  exact isGeneralPositionGerm_paramSection_of_isParamGP hgFt htp hy0 hc hyc hφ0 T hT h1

end GeneralPositionTools

/-! ### A chart criterion for general position -/

section ChartCriterion

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

open StrongRetr

set_option maxHeartbeats 3200000 in
-- the same assembly as `isGeneralPositionGerm_paramSection_of_isParamGP`
/-- **A chart criterion for general position** (2021 Definition 5.3.9, p. 220; preprint
Definition 5.17), the second half of the proof of `isGeneralPositionGerm_paramSection_of_isParamGP`
for any section: if in a tame chart `c` centred at the zero `y` the linearization `Lin_f(0)` is
onto and `ker Lin_f(0) + T^R_0 = T_0O` (at level `0`), then `(f, y)` is in general position. -/
theorem isGeneralPositionGerm_of_sup_eq {f : X → Y} (hf : B.IsScFredholmSectionTame f) {y : X}
    (hy0 : IsZeroAt P f y) {c : StrongBundleChart PX P} (hc : B.IsTameChart c)
    (hyV : y ∈ c.φ.source) (hφ0 : c.φ y = 0) {n : ℕ} {Wq : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (hsurj : ∀ k, (c.φ y, k) ∈ c.K → ∃ x, linAt c.U c.R (c.principal f) 0 x = k)
    (hsup : c.linKer f 0 ⊔
        reducedTangentSpaceWith (c.isRetraction.baseRetraction c.relOpen) T 0 =
      LinearMap.range (scDeriv (c.isRetraction.baseRetraction c.relOpen).U
        (c.isRetraction.baseRetraction c.relOpen) 0 :
          c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0)) :
    B.IsGeneralPositionGerm f y := by
  classical
  have hc'B : B.IsChart c := hc.1
  have hc'T : B.IsTameChart c := hc
  have hyV' : y ∈ c.φ.source := hyV
  have hc'0 : c.φ y = 0 := hφ0
  have hsurj' := hsurj
  have hz' : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = c.φ y := by rw [map_zero, hφ0]
  set R' := c.isRetraction.baseRetraction c.relOpen with hR'
  have hzR : (0 : c.φ.model.E 1) ∈ c.φ.model.E.lvlSet R'.retract 1 := by
    rw [ScBanach.mem_lvlSet, c.base_retract, hz']; exact c.φ.mapsTo_model _ hyV'
  have hzs : (0 : c.φ.model.E 1) ∈ c.φ.model.E.smoothLvl 1 := by
    change c.φ.model.E.toBase 1 0 ∈ c.φ.model.E.smooth
    rw [map_zero]; exact c.φ.model.E.smooth.zero_mem
  obtain ⟨B'', hB''T, hKB, hKBM⟩ := exists_compl_le_of_sup_eq le_rfl (c.linKer_le _ 0)
    le_rfl inf_le_left hsup
  have hR'T : R'.IsTameWith T := hc'T.2 _ _ T hT
  have hker := isInGoodPositionIn_of_scComplement_le_reduced T hR'T
    hzR hzs hB''T hKB hKBM
  have hpt : c.φ y = c.φ.model.E.toBase 1 0 := by
    rw [hc'0]; exact (map_zero _).symm
  have hker' : IsInGoodPositionIn c.φ.model.E
      (rangeS (scDeriv c.U
        (r c.R) 0))
      (partialQuadrantAtWith T
        (c.φ y))
      ((LinearMap.ker (linAt c.U
        c.R
        (c.principal
          f) 0 :
        ↥(rangeS (scDeriv c.U
          (r c.R) 0)) →ₗ[ℝ]
          c.F 0)).map
        (rangeS (scDeriv c.U
          (r c.R) 0)).subtype) := by
    rw [hpt]; exact hker
  have hFs : y ∈ PX.smoothSet :=
    hf.mem_smoothSet_of_isZeroAt hy0
  have hgood := (StrongBundle.isGoodPositionGerm_of_linAt_surj hf.isScSmooth
    (hf.germ _ hFs) hy0 hc'B hyV' hz' T hT hsurj' hker').toTame
    hf.isScSmooth
    (hf.germTame _ hFs) hy0
  -- `ker F'(0, y) = T_{(0, y)}S̃`: finite-dimensional and smooth
  obtain ⟨V, hVo, h0V, -, hAV, -, hidV⟩ := exists_isGeneralPositionGerm_iff hf hgood hy0
  have hyA : y ∈ solutionSet P f ∩ V := ⟨hy0, h0V⟩
  set d := hAV.data hyA with hd
  have hyG : y ∈ d.toSubData.shrink c.φ :=
    d.toSubData.mem_shrink c.φ hyA (hAV.mem_data_V hyA) hyV'
  have hT0 := hidV _ h0V hy0 c hc'B hyV' _ (d.toSubData.isOpen_shrink c.φ)
    (d.toSubData.shrink_subset_source c.φ) hyG
    (d.toSubData.isScRetract_image c.φ c.isChart) 0 hz'
  obtain ⟨t', ht', ht'p⟩ := d.isScPlusRetract_image c.isChart
    (PX.levelMk 1 _ (d.mem_levelSet_one hyA (hAV.mem_data_V hyA)))
  have hy0t' : (0 : c.φ.model.E 1) ∈ c.φ.model.E.lvlSet t'.retract 1 := by
    rw [ScBanach.mem_lvlSet, ht', hz']; exact ⟨_, ⟨hyG, hyA⟩, rfl⟩
  have hKeq : LinearMap.range
      (scDeriv t'.U t' 0 : c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) =
      c.linKer f 0 := by
    apply SetLike.coe_injective
    rw [← tangentSpace_eq_coe_submodule t' hy0t', ht', hT0]
  have hy0t'' : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ t'.retract := hy0t'
  have hfin : FiniteDimensional ℝ
      (c.linKer f 0) := by
    rw [← hKeq]
    exact lemma_4_1_7_ii ht'p hy0t''
  have hsm : c.linKer f 0 ≤
      c.φ.model.E.smooth := by
    have : FiniteDimensional ℝ
        (LinearMap.range
          (scDeriv t'.U t' 0 : c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0)) := by
      rw [hKeq]; exact hfin
    rw [← hKeq]
    exact (c.φ.model.E.proposition_1_1_7_iff _).1
      (t'.isScSplitting_range_scDeriv hy0t' hzs).1
  -- Definition 5.3.9 (preprint 5.17)
  refine ⟨c, hc'T, hyV', 0, hz', hsurj', fun {n₂ Wq₂} T₂ hT₂ => ?_⟩
  have hR'T₂ : R'.IsTameWith T₂ := hc'T.2 _ _ T₂ hT₂
  obtain ⟨-, hTRsc, -⟩ := proposition_2_5_6_partialCone hT₂ hR'T₂ hzR hzs
  have hred : reducedTangentSpaceWith R' T₂ 0 =
      reducedTangentSpaceWith R' T 0 := by
    unfold reducedTangentSpaceWith
    rw [minimalSubspaceWith_eq T₂ hT₂ T hT (by
      rw [map_zero, ← hc'0]
      exact c.φ.model.O_subset_C (c.φ.mapsTo_model _ hyV'))]
  have hM : LinearMap.range
      (scDeriv R'.U R' 0 : c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) =
      c.linKer f 0 ⊔
        reducedTangentSpaceWith R' T₂ 0 := by rw [hred, hsup]
  obtain ⟨Bc, hBcT, hBcsc, hsplit⟩ := exists_scComplement_le hsm hTRsc hM
  exact ⟨Bc, hBcT, hBcsc, hsplit⟩


end ChartCriterion

/-! ### General position of `f̃(t, x) = g(x)` on `ℝᵐ × X` -/

section ParamLift

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {g : X → Y} {m : ℕ}

open StrongRetr

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- `F(λ, x) = g(x) + Σ λᵢ·0` is the lift `g̃(λ, x) = g(x)`. -/
lemma paramLift_eq_paramSection_zero (hg : IsSection P g) :
    paramLift (n := m) g hg =
      paramSection g hg (fun _ : Fin m => fiberZero P) fun _ => isSection_fiberZero := by
  funext z
  apply Subtype.ext
  change ((z, g z.2) : ((Fin m → ℝ) × X) × Y) =
    (z, (((⟨g z.2, hg z.2⟩ : P ⁻¹' {z.2}) +
      fiberComb (fun _ : Fin m => fiberZero P) (fun _ => isSection_fiberZero) z :
        P ⁻¹' {z.2}) : Y))
  have h0 : fiberComb (fun _ : Fin m => fiberZero P) (fun _ => isSection_fiberZero) z = 0 := by
    unfold fiberComb
    exact Finset.sum_eq_zero fun i _ => smul_zero (z.1 i)
  rw [h0, add_zero]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- The slices of `g + Σ λᵢ·0` are `g`. -/
lemma paramSlice_zeroFamily (hg : IsSection P g) (lam : Fin m → ℝ) :
    paramSlice g hg (fun _ : Fin m => fiberZero P) (fun _ => isSection_fiberZero) lam = g := by
  funext y
  change ((((⟨g y, hg y⟩ : P ⁻¹' {y}) +
    fiberComb (fun _ : Fin m => fiberZero P) (fun _ => isSection_fiberZero) (lam, y)) :
      P ⁻¹' {y}) : Y) = g y
  have h0 : fiberComb (fun _ : Fin m => fiberZero P) (fun _ => isSection_fiberZero)
      (lam, y) = 0 := by
    unfold fiberComb
    exact Finset.sum_eq_zero fun i _ => smul_zero (lam i)
  rw [h0, add_zero]

variable [ParacompactSpace ((Fin m → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))]

set_option maxHeartbeats 1600000 in
-- the product chart `(r ↦ r − r₀) × c` centred at `(r₀, y)`
/-- **General position of the lift** (2021 Definition 5.3.9, p. 220, for the section
`g̃(t, x) = g(x)` of the pull-back to `ℝᵐ × X`): if `(g, y)` is in general position, then
`(g̃, (r₀, y))` is in general position for every `r₀`. *Proof*: in the product chart
`(r ↦ r − r₀) × c` centred at `(r₀, y)`, `Lin_{g̃}(0)(a, u) = Lin_g(0)u`, so the surjectivity and
`ker + T^R = T` pass from `c` (`isParamGP_elim0_of_isGeneralPositionGerm`) to the product chart,
and the chart criterion `isGeneralPositionGerm_of_sup_eq` concludes. -/
theorem isGeneralPositionGerm_paramLift (hgFt : B.IsScFredholmSectionTame g) {y : X}
    (hy0 : IsZeroAt P g y) (hgp : B.IsGeneralPositionGerm g y) (r₀ : Fin m → ℝ) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGeneralPositionGerm
      (paramLift g hgFt.isScSmooth.1) (r₀, y) := by
  classical
  have hgF := hgFt.toIsScFredholmSection
  have h0s : ∀ _ : Fin m, B.IsScPlusSection (fiberZero P) := fun _ =>
    StrongBundle.isScPlusSection_fiberZero
  rw [paramLift_eq_paramSection_zero hgFt.isScSmooth.1]
  have hFt := theorem_3_1_21_tame hgFt h0s
  set F := paramSection g hgFt.isScSmooth.1 (fun _ : Fin m => fiberZero P)
    (fun i => (h0s i).1) with hF
  have hz0 : IsZeroAt (pullbackProj P Prod.snd) F (r₀, y) := by
    rw [hF, isZeroAt_paramSection_iff]
    change IsZeroAt P (paramSlice g _ (fun _ : Fin m => fiberZero P)
      (fun _ => isSection_fiberZero) r₀) y
    rw [paramSlice_zeroFamily]; exact hy0
  obtain ⟨-, c, hc, hyV, hφ0, -⟩ := hgFt.germTame y (hgF.mem_smoothSet_of_isZeroAt hy0)
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  have hP := isParamGP_elim0_of_isGeneralPositionGerm hgFt hy0 hc hyV hφ0 T hT hgp
  set q₀ := F (r₀, y) with hq₀
  set c' := (PullbackChartData.ofProd c r₀).toChart q₀ with hc'
  have hc'B : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsChart c' :=
    (PullbackChartData.ofProd c r₀).isChart_toChart B _ hc.1 q₀
  have hc'T : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsTameChart c' :=
    ⟨hc'B, PullbackChartData.ofProd_isTame c r₀ q₀ hc.2⟩
  have hyV' : (r₀, y) ∈ c'.φ.source := ⟨mem_univ _, hyV⟩
  have hc'0 : c'.φ (r₀, y) = 0 := ofProd_apply_eq_zero c r₀ q₀ hφ0
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model y hyV
  have h0U : (0 : c.φ.model.E 0) ∈ c.U := mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)
  have hT' : c'.φ.model.C = (prodPresentation (rnPres m) T) 0 ⁻¹'
      quadrant (0 + n) ((ScBanach.const (Fin m → ℝ)).prod Wq) 0 :=
    prod_eq_prodPresentation (rnPres m) T (rnPres_eq (m := m)) hT
  have hmin : minimalSubspaceWith (prodPresentation (rnPres m) T)
      (0 : ((rnSc m).prod c.φ.model.E) 0) =
      (⊤ : Submodule ℝ (Fin m → ℝ)).prod (minimalSubspaceWith T 0) := by
    rw [minimalSubspaceWith_prodPresentation]
    simp only [Prod.fst_zero, Prod.snd_zero, minimalSubspaceWith_rnPres]
  have htan : ∀ w : (Fin m → ℝ) × c.φ.model.E 0,
      w ∈ rangeS (scDeriv c'.U (r c'.R) 0) ↔ w.2 ∈ rangeS (scDeriv c.U (r c.R) 0) := fun w =>
    PullbackChartData.ofProd_mem_tangent_iff c r₀ q₀ 0 (u := 0) (by rw [map_zero]; exact h0U) w
  -- the linearization in the product chart
  have hz0' : ∀ u ∈ c.φ.model.O, c.principal (fiberZero P) u = 0 := fun u hu =>
    c.snd_fiberZero (c.φ.symm_mapsTo hu)
  have hlin : ∀ (w : (Fin m → ℝ) × c.φ.model.E 0) (hw : w ∈ rangeS (scDeriv c'.U (r c'.R) 0)),
      linAt c'.U c'.R (c'.principal F) 0 ⟨w, hw⟩ =
        linAt c.U c.R (c.principal g) 0 ⟨w.2, (htan w).1 hw⟩ := by
    intro w hw
    rw [hF, linAt_paramSection hgF h0s hc.1 h0O r₀ q₀ hw]
    have hgs := hgFt.isScSmooth.isSc1_principal_comp_r hc.1
    have heq : EqOn (c.principal g ∘ r c.R) ((fun u => c.principal g u +
        ∑ i, r₀ i • c.principal (fiberZero P) u) ∘ r c.R) c.U := fun u hu => by
      simp only [Function.comp_apply, hz0' _ (c.r_mem_O hu), smul_zero, Finset.sum_const_zero,
        add_zero]
    have h0lvl : (0 : c.φ.model.E 1) ∈ c.φ.model.E.lvlSet c.U 1 := by
      rw [ScBanach.mem_lvlSet, map_zero]; exact h0U
    rw [linAt_congr c.relOpen (hgs.congr heq) hgs (fun u hu => by
      obtain ⟨u', hu', rfl⟩ := hu
      simp only [hz0' _ (c.r_mem_O hu'), smul_zero, Finset.sum_const_zero, add_zero]) h0lvl]
    simp only [hz0' 0 h0O, smul_zero, Finset.sum_const_zero, add_zero]
    rfl
  -- (i): surjectivity
  have hsurj : ∀ k, (c'.φ (r₀, y), k) ∈ c'.K →
      ∃ x, linAt c'.U c'.R (c'.principal F) 0 x = k := by
    intro k hk
    rw [hc'0] at hk
    obtain ⟨u, a, hua⟩ := hP.1 k ((mem_K_ofProd_zero_iff c r₀ q₀ h0O k).1 hk)
    have hw : ((0 : Fin m → ℝ), (u : c.φ.model.E 0)) ∈ rangeS (scDeriv c'.U (r c'.R) 0) :=
      (htan _).2 u.2
    refine ⟨⟨_, hw⟩, ?_⟩
    rw [hlin _ hw]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hua
    exact hua
  -- (ii): `ker + T^R = T`
  set R' := c'.isRetraction.baseRetraction c'.relOpen with hR'
  have hsup : c'.linKer F 0 ⊔ reducedTangentSpaceWith R' (prodPresentation (rnPres m) T) 0 =
      LinearMap.range (scDeriv R'.U R' 0 : c'.φ.model.E 0 →ₗ[ℝ] c'.φ.model.E 0) := by
    refine le_antisymm (sup_le (c'.linKer_le _ 0) inf_le_left) fun v hv => ?_
    have hv2 : v.2 ∈ rangeS (scDeriv c.U (r c.R) 0) :=
      PullbackChartData.ofProd_mem_tangent c r₀ q₀ h0U hv
    obtain ⟨u, a, hua, hwu⟩ := hP.2 ⟨v.2, hv2⟩
    have hk : ((0 : Fin m → ℝ), (u : c.φ.model.E 0)) ∈ rangeS (scDeriv c'.U (r c'.R) 0) :=
      (htan _).2 u.2
    have hkK : ((0 : Fin m → ℝ), (u : c.φ.model.E 0)) ∈ c'.linKer F 0 := by
      refine (c'.mem_linKer_iff _ 0 _).2 ⟨hk, ?_⟩
      rw [hlin _ hk]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hua
      exact hua
    let k : c'.φ.model.E 0 := ((0 : Fin m → ℝ), (u : c.φ.model.E 0))
    have hrest : v - k ∈ reducedTangentSpaceWith R' (prodPresentation (rnPres m) T) 0 := by
      refine ⟨Submodule.sub_mem _ hv hk, ?_⟩
      have hb0' : c'.φ.model.E.toBase 1 (0 : c'.φ.model.E 1) = 0 := map_zero _
      rw [hb0']
      change v - k ∈ minimalSubspaceWith (prodPresentation (rnPres m) T)
        (0 : ((rnSc m).prod c.φ.model.E) 0)
      rw [hmin]
      exact ⟨Submodule.mem_top, hwu⟩
    have : v = k + (v - k) := by abel
    rw [this]
    exact Submodule.add_mem_sup hkK hrest
  exact isGeneralPositionGerm_of_sup_eq hFt hz0 hc'T hyV' hc'0 (prodPresentation (rnPres m) T)
    hT' hsurj hsup

end ParamLift

/-! ### Theorem 5.3.10 relative to a compact part -/

section Relative

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

open StrongRetr

/-- A Lebesgue null set misses every ball. -/
lemma exists_norm_lt_not_mem_of_null {m : ℕ} {CV : Set (Fin m → ℝ)} (hCV : volume CV = 0)
    {δ : ℝ} (hδ : 0 < δ) : ∃ lam : Fin m → ℝ, ‖lam‖ < δ ∧ lam ∉ CV := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hsub : Metric.ball (0 : Fin m → ℝ) δ ⊆ CV := fun lam hlam =>
    h lam (mem_ball_zero_iff.1 hlam)
  exact (Metric.measure_ball_pos volume (0 : Fin m → ℝ) hδ).ne' (measure_mono_null hsub hCV)

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- `G + Σ λᵢ tᵢ`, read as `G` plus the perturbation `0 + Σ λᵢ tᵢ`. -/
lemma sectionAdd_paramSlice_fiberZero {m : ℕ} {G : X → Y} (hG : IsSection P G)
    {t : Fin m → X → Y} (ht : ∀ i, IsSection P (t i)) (lam : Fin m → ℝ) :
    sectionAdd P G (paramSlice (fiberZero P) isSection_fiberZero t ht lam) =
      paramSlice G hG t ht lam := by
  rw [sectionAdd_paramSlice hG isSection_fiberZero ht lam]
  have key : ∀ (g' : X → Y) (hg' : IsSection P g'), g' = G →
      paramSlice g' hg' t ht lam = paramSlice G hG t ht lam := by
    rintro _ _ rfl; rfl
  exact key _ _ (sectionAdd_fiberZero hG)

/-- **Sections putting `F` in general position near a compact set of zeros, supported in a given
open set and bounded by an auxiliary norm** (the construction of the proof of 2021 Theorem 5.3.10,
p. 216, over a compact `K` of zeros, as in `exists_sections_isGeneralPositionGerm_of_isCompact`):
for `K ⊆ W` compact, there are sc⁺-sections `s₁, …, s_k` supported in `W` with `N(sᵢ) ≤ 1` and an
open `W' ⊇ K` such that `F(λ, y) = g(y) + Σ λᵢ sᵢ(y)` is in general position at `(0, y)` for
every zero `y ∈ W'` of `g`. -/
theorem exists_sections_isGeneralPositionGerm_near (hbump : PX.AdmitsBumpFunctions)
    {g : X → Y} (hg : B.IsScFredholmSectionTame g) {N : B.One → ℝ} (hN : B.IsAuxNorm N)
    {W : Set X} (hW : IsOpen W) {K : Set X} (hK : IsCompact K) (hKW : K ⊆ W)
    (hK0 : ∀ x ∈ K, IsZeroAt P g x) (hX : PX.IsTame) :
    ∃ (k : ℕ) (s : Fin k → X → Y) (hs : ∀ i, B.IsScPlusSection (s i)),
      (∀ i, sectionSupport P (s i) ⊆ W) ∧
      (∀ i x (hx : s i x ∈ B.oneSet), N (B.oneMk (s i x) hx) ≤ 1) ∧
      ∃ W' : Set X, IsOpen W' ∧ K ⊆ W' ∧
      ∀ [ParacompactSpace ((Fin k → ℝ) × X)]
        [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))],
        ∀ y ∈ W', IsZeroAt P g y →
          (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsGeneralPositionGerm
            (paramSection g hg.isScSmooth.1 s fun i => (hs i).1) (0, y) := by
  classical
  have hgF : B.IsScFredholmSection g := hg.toIsScFredholmSection
  have hch : ∀ y : solutionSet P g, ∃ c : StrongBundleChart PX P,
      B.IsTameChart c ∧ (y : X) ∈ c.φ.source ∧ c.φ y = 0 := fun y => by
    obtain ⟨-, c, hc, hyc, hφ0, -⟩ := hg.germTame y (hgF.mem_smoothSet_of_isZeroAt y.2)
    exact ⟨c, hc, hyc, hφ0⟩
  choose c hc hyc hφ0 using hch
  have hpres : ∀ y : solutionSet P g, ∃ (n : ℕ) (Wq : ScBanach)
      (T : ScIso (c y).φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)),
      (c y).φ.model.C = T 0 ⁻¹' quadrant n Wq 0 := fun y => (c y).φ.model.isPartialQuadrant
  choose n Wq T hT using hpres
  have hfam : ∀ x : K, ∃ (k : ℕ) (s : Fin k → X → Y) (hsp : ∀ i, B.IsScPlusSection (s i)),
      (∀ i, sectionSupport P (s i) ⊆ W) ∧
      (∀ i y (hy : s i y ∈ B.oneSet), N (B.oneMk (s i y) hy) ≤ 1) ∧
      ∃ Ux : Set X, IsOpen Ux ∧ (x : X) ∈ Ux ∧ ∀ y ∈ Ux, IsZeroAt P g y →
        haveI := MPolyfold.paracompactSpace_prod (rnPolyfold k) PX
        haveI := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin k → ℝ) × X → X))
          ((rnPolyfold k).prod PX) B
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsGeneralPositionGerm
          (paramSection g hg.isScSmooth.1 s fun i => (hsp i).1) (0, y) := by
    intro x
    have hx0 : IsZeroAt P g x := hK0 x x.2
    obtain ⟨k, s, hsp, hsupp, hsN, hgpx⟩ := exists_sections_isParamGP hbump hN hg hx0
      (hc ⟨x, hx0⟩) (hyc ⟨x, hx0⟩) (hφ0 ⟨x, hx0⟩) (T ⟨x, hx0⟩) (hT ⟨x, hx0⟩) hW (hKW x.2)
    have := MPolyfold.paracompactSpace_prod (rnPolyfold k) PX
    have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin k → ℝ) × X → X))
      ((rnPolyfold k).prod PX) B
    have hFt := theorem_3_1_21_tame hg hsp
    have hz0 : ∀ y, IsZeroAt P g y → IsZeroAt (pullbackProj P Prod.snd)
        (paramSection g hg.isScSmooth.1 s fun i => (hsp i).1) (0, y) := fun y hy =>
      isZeroAt_paramSection_zero hg.isScSmooth.1 (fun i => (hsp i).1) hy
    have h0 := isGeneralPositionGerm_paramSection_of_isParamGP hg hsp hx0 (hc ⟨x, hx0⟩)
      (hyc ⟨x, hx0⟩) (hφ0 ⟨x, hx0⟩) (T ⟨x, hx0⟩) (hT ⟨x, hx0⟩) hgpx
    obtain ⟨W₁, hW₁o, h0W₁, -, hW₁⟩ :=
      exists_isOpen_isGeneralPositionGerm (prod_rn_isTame hX) hFt (hz0 x hx0) h0
    exact ⟨k, s, hsp, hsupp, hsN, Prod.mk 0 ⁻¹' W₁,
      hW₁o.preimage (continuous_const.prodMk continuous_id), h0W₁,
      fun y hy hy0 => (hW₁ (0, y) hy (hz0 y hy0)).2.1⟩
  choose k s hsp hsupp hsN Ux hUxo hxUx hUx using hfam
  obtain ⟨T₀, hT₀⟩ := hK.elim_finite_subcover Ux hUxo
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxUx ⟨x, hx⟩⟩)
  let e := Fintype.equivFin (Σ x : T₀, Fin (k x.1))
  set m := Fintype.card (Σ x : T₀, Fin (k x.1)) with hm
  set t : Fin m → X → Y := fun j => s (e.symm j).1.1 (e.symm j).2 with htdef
  have ht : ∀ j, B.IsScPlusSection (t j) := fun j => hsp _ _
  refine ⟨m, t, ht, fun j => hsupp _ _, fun j x hx => hsN _ _ x hx,
    ⋃ x ∈ T₀, Ux x, isOpen_biUnion fun x _ => hUxo x, hT₀, ?_⟩
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

set_option maxHeartbeats 6400000 in
-- the assembly of `theorem_5_3_10_of_family`, relative to `W`
/-- **The perturbation step of 2021 Theorem 5.3.10 (p. 216), relative to an open `W`** (the
mechanism of `theorem_5_3_10_of_family`, with `s₀ = 0` and only the zeros in `W` controlled): let
`G` have tame germ data, `N` an auxiliary norm, `W` open with `cl{x ∈ W | N(G(x)) ≤ 1}` compact,
and `t₁, …, t_m` sc⁺-sections with `N(tᵢ) ≤ 1` such that
`F(λ, x) = G(x) + Σ λᵢ tᵢ(x)` is in general position at `(0, y)` for every zero `y` of `G`.
Then there are `δ > 0` and a Lebesgue null set `CV` such that for `|λ| < δ`, `λ ∉ CV`:
`N(Σ λᵢ tᵢ) ≤ 1`, and `(G + Σ λᵢ tᵢ, x)` is in general position at every zero `x ∈ W`. -/
theorem exists_null_isGeneralPositionGerm_paramSlice (hX : PX.IsTame) {G : X → Y}
    (hG : B.IsScFredholmSectionTame G) {N : B.One → ℝ} (hN : B.IsAuxNorm N) {W : Set X}
    (hW : IsOpen W) (hcpt : IsCompact (closure {x ∈ W | B.AuxLe N (G x) 1}))
    {m : ℕ} (t : Fin m → X → Y) (ht : ∀ i, B.IsScPlusSection (t i))
    (htN : ∀ i x (hx : t i x ∈ B.oneSet), N (B.oneMk (t i x) hx) ≤ 1)
    (hgp0 : ∀ y, IsZeroAt P G y →
      haveI := MPolyfold.paracompactSpace_prod (rnPolyfold m) PX
      haveI := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin m → ℝ) × X → X))
        ((rnPolyfold m).prod PX) B
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGeneralPositionGerm
        (paramSection G hG.isScSmooth.1 t fun i => (ht i).1) (0, y)) :
    ∃ δ > 0, ∃ CV : Set (Fin m → ℝ), volume CV = 0 ∧
      ∀ lam : Fin m → ℝ, ‖lam‖ < δ → lam ∉ CV →
        (∀ x, B.AuxLe N (paramSlice (fiberZero P) isSection_fiberZero t
          (fun i => (ht i).1) lam x) 1) ∧
        ∀ x ∈ W, IsZeroAt P (paramSlice G hG.isScSmooth.1 t (fun i => (ht i).1) lam) x →
          B.IsGeneralPositionGerm (paramSlice G hG.isScSmooth.1 t (fun i => (ht i).1) lam) x := by
  classical
  have hGs : IsSection P G := hG.isScSmooth.1
  have := MPolyfold.paracompactSpace_prod (rnPolyfold m) PX
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin m → ℝ) × X → X))
    ((rnPolyfold m).prod PX) B
  have hFt := theorem_3_1_21_tame hG ht
  have hXm : ((rnPolyfold m).prod PX).IsTame := prod_rn_isTame hX
  set F := paramSection G hGs t fun i => (ht i).1 with hF
  set Kc := closure {x ∈ W | B.AuxLe N (G x) 1} with hKc
  have hz0 : ∀ y, IsZeroAt P G y → IsZeroAt (pullbackProj P Prod.snd) F (0, y) := fun y hy =>
    isZeroAt_paramSection_zero hGs (fun i => (ht i).1) hy
  -- the open set `Wu ⊇ {0} × S_G` of zeros of `F` in good and general position
  have hloc : ∀ y : solutionSet P G, ∃ Wy : Set ((Fin m → ℝ) × X), IsOpen Wy ∧
      ((0 : Fin m → ℝ), (y : X)) ∈ Wy ∧
      ((rnPolyfold m).prod PX).IsSmoothSubmanifold
        (solutionSet (pullbackProj P Prod.snd) F ∩ Wy) ∧
      ∀ z ∈ Wy, IsZeroAt (pullbackProj P Prod.snd) F z →
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGoodPositionGermTame
          F z ∧
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGeneralPositionGerm
          F z ∧
        ((rnPolyfold m).prod PX).IsGeneralPositionAt
          (solutionSet (pullbackProj P Prod.snd) F ∩ Wy) z :=
    fun y => exists_isOpen_isGeneralPositionGerm hXm hFt (hz0 y y.2) (hgp0 y y.2)
  choose Wy hWyo hyWy hWyA hWy using hloc
  set Wu := ⋃ y, Wy y with hWudef
  have hWuo : IsOpen Wu := isOpen_iUnion hWyo
  have h0W : ∀ y, IsZeroAt P G y → ((0 : Fin m → ℝ), y) ∈ Wu := fun y hy =>
    mem_iUnion.2 ⟨⟨y, hy⟩, hyWy ⟨y, hy⟩⟩
  have hWgood : ∀ z ∈ Wu, IsZeroAt (pullbackProj P Prod.snd) F z →
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGoodPositionGermTame
        F z := fun z hz hz0 => by
    obtain ⟨y, hzy⟩ := mem_iUnion.1 hz
    exact (hWy y z hzy hz0).1
  -- the perturbations `p_λ = Σ λᵢ tᵢ`, with `N(p_λ) ≤ 1` for `|λ| ≤ δ₁ = 1/(m + 1)`
  have hslice : ∀ lam : Fin m → ℝ,
      sectionAdd P G (paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam) =
        paramSlice G hGs t (fun i => (ht i).1) lam := fun lam =>
    sectionAdd_paramSlice_fiberZero hGs (fun i => (ht i).1) lam
  set δ₁ : ℝ := 1 / (m + 1) with hδ₁
  have hδ₁pos : 0 < δ₁ := by positivity
  have hallow : ∀ lam : Fin m → ℝ, ‖lam‖ ≤ δ₁ →
      ∀ x, B.AuxLe N (paramSlice (fiberZero P) isSection_fiberZero t
        (fun i => (ht i).1) lam x) 1 := fun lam hlam x =>
    auxLe_paramSlice hN StrongBundle.isScPlusSection_fiberZero ht (ε := 1)
      (fun x hx => by rw [hN.fiberZero_eq x hx]; norm_num) htN (by
        calc (m : ℝ) * ‖lam‖ ≤ m * δ₁ := mul_le_mul_of_nonneg_left hlam (by positivity)
          _ = m / (m + 1) := by rw [hδ₁]; ring
          _ ≤ 1 := (div_le_one (by positivity)).2 (by linarith)) x
  -- the zeros of `F` over `W` with `|λ| ≤ δ₁` lie over `Kc`
  have hzKc : ∀ z : (Fin m → ℝ) × X, ‖z.1‖ ≤ δ₁ → z.2 ∈ W →
      IsZeroAt (pullbackProj P Prod.snd) F z → z.2 ∈ Kc := by
    intro z hz1 hzW hz0'
    have hx' : IsZeroAt P (paramSlice G hGs t (fun i => (ht i).1) z.1) z.2 :=
      (isZeroAt_paramSection_iff z).1 hz0'
    rw [← hslice z.1] at hx'
    exact subset_closure ⟨hzW, hN.auxLe_of_sectionAdd hGs (isSection_paramSlice z.1) hx'
      (hallow z.1 hz1 z.2)⟩
  -- the compact set `Z` of zeros of `F` over `Kc` with `|λ| ≤ δ₁`
  have hFsm := hFt.isScSmooth
  set Z : Set ((Fin m → ℝ) × X) := {z | ‖z.1‖ ≤ δ₁ ∧ z.2 ∈ Kc ∧
    IsZeroAt (pullbackProj P Prod.snd) F z} with hZdef
  have hZclosed : IsClosed Z :=
    (isClosed_le (continuous_norm.comp continuous_fst) continuous_const).inter
      ((isClosed_closure.preimage continuous_snd).inter (isClosed_solutionSet hFsm))
  have hZsub : Z ⊆ Metric.closedBall (0 : Fin m → ℝ) δ₁ ×ˢ Kc := fun z hz =>
    ⟨mem_closedBall_zero_iff.2 hz.1, hz.2.1⟩
  have hZ : IsCompact Z :=
    ((isCompact_closedBall _ _).prod hcpt).of_isClosed_subset hZclosed hZsub
  obtain ⟨δ₀, hδ₀, hδ₀W⟩ := exists_pos_forall_mem_of_isCompact hZ hWuo fun z hz hz1 => by
    have hz2 : IsZeroAt P G z.2 := by
      have := (isZeroAt_paramSection_iff z).1 hz.2.2
      rw [hz1, paramSlice_zero] at this; exact this
    have hz' : z = (0, z.2) := Prod.ext hz1 rfl
    rw [hz']; exact h0W z.2 hz2
  set δ : ℝ := min δ₀ δ₁ with hδ
  have hδpos : 0 < δ := lt_min hδ₀ hδ₁pos
  -- the submanifold `A = S̃ ∩ Wu ∩ {|λ| < δ} ∩ (ℝᵐ × W)`
  set Wδ : Set ((Fin m → ℝ) × X) := Wu ∩ {z | ‖z.1‖ < δ} ∩ {z | z.2 ∈ W} with hWδ
  have hWδo : IsOpen Wδ := (hWuo.inter (isOpen_lt (continuous_norm.comp continuous_fst)
    continuous_const)).inter (hW.preimage continuous_snd)
  set A := solutionSet (pullbackProj P Prod.snd) F ∩ Wδ with hAdef
  have hA : ((rnPolyfold m).prod PX).IsSmoothSubmanifold A :=
    StrongBundle.isSmoothSubmanifold_solutionSet_inter hFt.isScSmooth.1 hWδo
      fun z hz hz0' => hWgood z hz.1.1 hz0'
  have hAZ : A ⊆ Z := fun z hz =>
    ⟨(le_of_lt hz.2.1.2).trans (min_le_right _ _),
      hzKc z ((le_of_lt hz.2.1.2).trans (min_le_right _ _)) hz.2.2 hz.1, hz.1⟩
  have hcl : IsCompact (closure A) :=
    hZ.of_isClosed_subset isClosed_closure (closure_minimal hAZ hZclosed)
  have hgpA : ∀ z ∈ A, ((rnPolyfold m).prod PX).IsGeneralPositionAt A z := by
    intro z hz
    obtain ⟨y, hzy⟩ := mem_iUnion.1 hz.2.1.1
    refine MPolyfold.IsGeneralPositionAt.congr_nhds (hWyA y) hA ((hWyo y).inter hWδo)
      ⟨hzy, hz.2⟩ ?_ (hWy y z hzy hz.1).2.2
    ext w
    simp only [hAdef, mem_inter_iff]
    tauto
  -- Theorem 4.3.1 (preprint 4.23)
  obtain ⟨Sig, -, hSig0, hSig⟩ := theorem_4_3_1_of_subset hX hA hcl hgpA univ
  -- the Sard step on the compact `Z₀ = Z ∩ {|λ| ≤ δ/2}`
  set Z₀ : Set ((Fin m → ℝ) × X) := {z | ‖z.1‖ ≤ δ / 2 ∧ z.2 ∈ Kc ∧
    IsZeroAt (pullbackProj P Prod.snd) F z} with hZ₀def
  have hZ₀Z : Z₀ ⊆ Z := fun z hz =>
    ⟨hz.1.trans (by linarith [min_le_right δ₀ δ₁]), hz.2⟩
  have hZ₀closed : IsClosed Z₀ :=
    (isClosed_le (continuous_norm.comp continuous_fst) continuous_const).inter
      ((isClosed_closure.preimage continuous_snd).inter (isClosed_solutionSet hFsm))
  have hZ₀ : IsCompact Z₀ := hZ.of_isClosed_subset hZ₀closed hZ₀Z
  have hZ₀W : ∀ z ∈ Z₀, z ∈ Wu := fun z hz =>
    hδ₀W z (hZ₀Z hz) (by linarith [min_le_left δ₀ δ₁, hz.1])
  have hlocS : ∀ z : Z₀, ∃ W' : Set ((Fin m → ℝ) × X), IsOpen W' ∧
      (z : (Fin m → ℝ) × X) ∈ W' ∧ ∃ CV : Set (Fin m → ℝ), volume CV = 0 ∧
        ∀ z' ∈ W', IsZeroAt (pullbackProj P Prod.snd) F z' → z'.1 ∉ CV →
          B.IsLinSurjAt (paramSlice G hGs t (fun i => (ht i).1) z'.1) z'.2 := fun z =>
    exists_null_isLinSurjAt_paramSlice_near hG ht z.2.2.2 (hWgood z (hZ₀W z z.2) z.2.2.2)
  choose W' hW'o hzW' CV hCV hW'tr using hlocS
  obtain ⟨T', hT'⟩ := hZ₀.elim_finite_subcover W' hW'o
    (fun z hz => mem_iUnion.2 ⟨⟨z, hz⟩, hzW' ⟨z, hz⟩⟩)
  refine ⟨δ / 2, by positivity, (univ \ Sig) ∪ ⋃ z ∈ T', CV z, ?_, fun lam hlam hlamCV => ?_⟩
  · exact measure_union_null hSig0
      ((measure_biUnion_null_iff T'.countable_toSet).2 fun z _ => hCV z)
  have hlamSig : lam ∈ Sig := by
    by_contra h; exact hlamCV (Or.inl ⟨mem_univ _, h⟩)
  have hlam₁ : ‖lam‖ ≤ δ₁ := by linarith [min_le_right δ₀ δ₁]
  refine ⟨hallow lam hlam₁, ?_⟩
  set h := paramSlice G hGs t (fun i => (ht i).1) lam with hhdef
  have hhF : B.IsScFredholmSectionTame h := by
    rw [hhdef, ← hslice lam]
    exact theorem_3_1_18_tame hG (isScPlusSection_paramSlice StrongBundle.isScPlusSection_fiberZero
      ht lam)
  -- transversality at the zeros over `W`
  have htrans : ∀ y ∈ W, IsZeroAt P h y → B.IsLinSurjAt h y := by
    intro y hyW hy
    have hzF : IsZeroAt (pullbackProj P Prod.snd) F (lam, y) :=
      (isZeroAt_paramSection_iff (lam, y)).2 hy
    have hzZ₀ : (lam, y) ∈ Z₀ := ⟨hlam.le, hzKc (lam, y) hlam₁ hyW hzF, hzF⟩
    obtain ⟨z, hzT', hzW'⟩ := mem_iUnion₂.1 (hT' hzZ₀)
    have hlamCV' : lam ∉ CV z := fun h' => hlamCV (Or.inr (mem_iUnion₂.2 ⟨z, hzT', h'⟩))
    exact hW'tr z (lam, y) hzW' hzF hlamCV'
  -- the fibre of `A` over `λ` is `S_h ∩ W`
  have hfib : solutionSet P h ∩ W = fibreSet A lam := by
    ext x
    constructor
    · rintro ⟨hx, hxW⟩
      have hzF : IsZeroAt (pullbackProj P Prod.snd) F (lam, x) :=
        (isZeroAt_paramSection_iff (lam, x)).2 hx
      have hlt : ‖lam‖ < δ := by linarith
      exact ⟨hzF, ⟨⟨hδ₀W (lam, x) ⟨hlam₁, hzKc (lam, x) hlam₁ hxW hzF, hzF⟩
        (lt_of_lt_of_le hlt (min_le_left _ _)), hlt⟩, hxW⟩⟩
    · intro hx
      exact ⟨(isZeroAt_paramSection_iff (lam, x)).1 hx.1, hx.2.2⟩
  obtain ⟨-, hFL⟩ := hSig lam hlamSig
  have hSm : PX.IsSmoothSubmanifold (solutionSet P h ∩ W) := by
    intro x hx
    rw [hfib] at hx ⊢
    obtain ⟨-, ⟨V, hV, hxV, s, hs, himg⟩, -, -⟩ := hFL x hx
    exact ⟨V, hV, hxV, s, hs, himg⟩
  have hgpS : ∀ y ∈ solutionSet P h ∩ W, PX.IsGeneralPositionAt (solutionSet P h ∩ W) y := by
    intro y hy
    rw [hfib] at hy ⊢
    exact (hFL y hy).2.2.1
  -- general position of the section at every zero over `W`
  intro y hyW hy0
  have hgood := isGoodPositionGermTame_of_isGeneralPositionAt hhF hy0 (htrans y hyW hy0) hSm
    inter_subset_left (hgpS y ⟨hy0, hyW⟩)
  obtain ⟨V', hV'o, hyV', -, hA', hiff', -⟩ := exists_isGeneralPositionGerm_iff hhF hgood hy0
  refine (hiff' y hyV' hy0).2 ?_
  refine MPolyfold.IsGeneralPositionAt.congr_nhds hSm hA' (hV'o.inter hW) ⟨hyV', hyW⟩ ?_
    (hgpS y ⟨hy0, hyW⟩)
  ext w; simp only [mem_inter_iff]; tauto

omit [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- The zero section has empty support. -/
lemma sectionSupport_fiberZero : sectionSupport P (fiberZero P : X → Y) = ∅ := by
  unfold sectionSupport
  simp

/-- **2021 Theorem 5.3.10 (p. 220; preprint Theorem 5.18) relative to a compact part** (an
auxiliary-hypothesis form for the cobordism of the proof of Theorem 6.7.1, p. 278, Remark 5.3.8):
let `X` be tame with sc-smooth bump functions, `G` an sc-Fredholm section with tame germ data, `N`
an auxiliary norm, `K ⊆ W` with `K` compact and `W` open, such that `(G, x)` is in general
position at every zero `x ∉ K` and `cl{x ∈ W | N(G(x)) ≤ 1}` is compact. Then for every `ε > 0`
there is an sc⁺-section `p` supported in `W` with `N(p) ≤ ε` such that `(G + p, x)` is in general
position at every zero. The text's theorem is the case `K = S_G` compact and `W = U`; here `S_G`
need not be compact. *Proof*: sections making `F(λ, x) = G(x) + Σ λᵢ sᵢ(x)` general at `(0, y)`
near the compact `K ∩ S_G` (`exists_sections_isGeneralPositionGerm_near`), and at the other zeros
since `G` is already general there
(`isGeneralPositionGerm_paramSection_of_isGeneralPositionGerm`); the Sard and Theorem 4.3.1 step
over `W` (`exists_null_isGeneralPositionGerm_paramSlice`) for the norm `N/η`, `η = min(ε, 1)`;
off `W` the perturbation vanishes near the zero and the general position is that of `G`
(`isGeneralPositionGerm_congr_nhds`). -/
theorem theorem_5_3_10_relative_hyp (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    {G : X → Y} (hG : B.IsScFredholmSectionTame G) {N : B.One → ℝ} (hN : B.IsAuxNorm N)
    {W K : Set X} (hW : IsOpen W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hgpK : ∀ x, IsZeroAt P G x → x ∉ K → B.IsGeneralPositionGerm G x)
    (hcpt : IsCompact (closure {x ∈ W | B.AuxLe N (G x) 1})) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : X → Y, B.IsScPlusSection p ∧ sectionSupport P p ⊆ W ∧ (∀ x, B.AuxLe N (p x) ε) ∧
      ∀ x, IsZeroAt P (sectionAdd P G p) x → B.IsGeneralPositionGerm (sectionAdd P G p) x := by
  classical
  have hGs : IsSection P G := hG.isScSmooth.1
  set η : ℝ := min ε 1 with hη
  have hηpos : 0 < η := lt_min hε one_pos
  have hNη : B.IsAuxNorm fun w => η⁻¹ * N w := hN.const_mul (inv_pos.2 hηpos)
  -- the compact set `cl{x ∈ W | N(G(x))/η ≤ 1}`
  have hcptη : IsCompact (closure {x ∈ W | B.AuxLe (fun w => η⁻¹ * N w) (G x) 1}) := by
    refine hcpt.of_isClosed_subset isClosed_closure (closure_mono fun x hx => ⟨hx.1, ?_⟩)
    have := (StrongBundle.auxLe_const_mul_iff (inv_pos.2 hηpos)).1 hx.2
    refine this.mono ?_
    rw [div_inv_eq_mul, one_mul]; exact min_le_right _ _
  -- the sections near the compact `K ∩ S_G`
  have hK₀ : IsCompact (K ∩ solutionSet P G) :=
    hK.inter_right (isClosed_solutionSet hG.isScSmooth)
  obtain ⟨k, s, hs, hssupp, hsN, W', hW'o, hKW', hgpW'⟩ :=
    exists_sections_isGeneralPositionGerm_near hbump hG hNη hW hK₀
      (inter_subset_left.trans hKW) (fun x hx => hx.2) hX
  have := MPolyfold.paracompactSpace_prod (rnPolyfold k) PX
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin k → ℝ) × X → X))
    ((rnPolyfold k).prod PX) B
  have hgpAll : ∀ y, IsZeroAt P G y →
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsGeneralPositionGerm
        (paramSection G hGs s fun i => (hs i).1) (0, y) := by
    intro y hy
    by_cases hyW' : y ∈ W'
    · exact hgpW' y hyW' hy
    · have hyK : y ∉ K := fun h => hyW' (hKW' ⟨h, hy⟩)
      exact isGeneralPositionGerm_paramSection_of_isGeneralPositionGerm hG hs hy (hgpK y hy hyK)
  obtain ⟨δ, hδ, CV, hCV, hmain⟩ :=
    exists_null_isGeneralPositionGerm_paramSlice hX hG hNη hW hcptη s hs hsN hgpAll
  obtain ⟨lam, hlam, hlamCV⟩ := exists_norm_lt_not_mem_of_null hCV hδ
  obtain ⟨hbound, hgpW⟩ := hmain lam hlam hlamCV
  set p := paramSlice (fiberZero P) isSection_fiberZero s (fun i => (hs i).1) lam with hpdef
  have hp : B.IsScPlusSection p :=
    isScPlusSection_paramSlice StrongBundle.isScPlusSection_fiberZero hs lam
  have hpsupp : sectionSupport P p ⊆ W := by
    refine (sectionSupport_paramSlice_subset isSection_fiberZero _ lam).trans ?_
    rw [sectionSupport_fiberZero, empty_union]
    exact iUnion_subset hssupp
  have hslice : sectionAdd P G p = paramSlice G hGs s (fun i => (hs i).1) lam :=
    sectionAdd_paramSlice_fiberZero hGs (fun i => (hs i).1) lam
  refine ⟨p, hp, hpsupp, fun x => ?_, fun x hx0 => ?_⟩
  · have := (StrongBundle.auxLe_const_mul_iff (inv_pos.2 hηpos)).1 (hbound x)
    refine this.mono ?_
    rw [div_inv_eq_mul, one_mul]; exact min_le_left _ _
  by_cases hxW : x ∈ W
  · rw [hslice] at hx0 ⊢
    exact hgpW x hxW hx0
  -- off `W`, `G + p = G` near `x`
  have hpz : ∀ y ∈ (sectionSupport P p)ᶜ, sectionAdd P G p y = G y := fun y hy => by
    have hy0 : p y = fiberZero P y := not_not.1 fun hne => hy (subset_closure hne)
    rw [sectionAdd_apply hGs hp.1]
    have : (⟨p y, hp.1 y⟩ : P ⁻¹' {y}) = 0 := Subtype.ext hy0
    rw [this, add_zero]
  have hxs : x ∈ (sectionSupport P p)ᶜ := fun h => hxW (hpsupp h)
  have hGx : IsZeroAt P G x := (isZeroAt_congr (hpz x hxs)).1 hx0
  exact isGeneralPositionGerm_congr_nhds hG (theorem_3_1_18_tame hG hp) hGx
    isClosed_closure.isOpen_compl hxs (fun y hy => (hpz y hy).symm)
    (hgpK x hGx fun h => hxW (hKW h))

end Relative

/-! ### The pulled-back auxiliary norm -/

section PullbackNorm

universe w

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {π : Z → X} (hπ : PZ.IsScSmoothMap PX π) [ParacompactSpace (pullbackSpace P π)]

namespace StrongBundle

/-- `Y[1]` of the pull-back is the pull-back of `Y[1]`: `q ∈ (π*Y)_{0,1}` iff its `Y`-component
lies in `Y_{0,1}` (the pulled-back charts keep the fibre component). -/
theorem pullback_mem_oneSet_iff (q : pullbackSpace P π) :
    q ∈ (B.pullback hπ).oneSet ↔ q.1.2 ∈ B.oneSet := by
  obtain ⟨Φ, hΦ, hq⟩ := (B.pullback hπ).atlas.cover q
  obtain ⟨d, q₀, hd, rfl⟩ := hΦ
  rw [(B.pullback hπ).mem_oneSet_iff ⟨d, q₀, hd, rfl⟩ hq, B.mem_oneSet_iff hd (d.mem_c_source hq)]
  exact Iff.rfl

/-- The map `(π*Y)[1] → Y[1]`, `((z, y)) ↦ y`. -/
def pullbackOneMap (w : (B.pullback hπ).One) : B.One :=
  B.oneMk ((B.pullback hπ).oneVal w).1.2
    ((pullback_mem_oneSet_iff hπ _).1 ((B.pullback hπ).oneVal_mem w))

lemma oneVal_pullbackOneMap (w : (B.pullback hπ).One) :
    B.oneVal (pullbackOneMap hπ w) = ((B.pullback hπ).oneVal w).1.2 := rfl

/-- The map `(π*Y)[1] → Y[1]` is continuous: in a pulled-back chart `Φ_π = ψ × pr_F Φ`,
`Φ[1](y) = (g(ψ(z)), Φ_π[1](z, y)₂)` with `g = φ ∘ π ∘ ψ⁻¹` continuous on `O_ψ`. -/
theorem continuous_pullbackOneMap : Continuous (pullbackOneMap (B := B) hπ) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro s ⟨c, hc, W, hW, rfl⟩
  rw [isOpen_iff_forall_mem_open]
  intro w₀ hw₀
  set q := (B.pullback hπ).oneVal w₀ with hq
  have hqc : q.1.2 ∈ c.toPartialEquiv.source := hw₀.1
  have hπz : π q.1.1 ∈ c.φ.source := by
    rw [c.source_eq, mem_preimage, show P q.1.2 = π q.1.1 from q.2] at hqc; exact hqc
  obtain ⟨d, hdc, hzd⟩ := exists_pullbackChartData hπ c hπz
  subst hdc
  have hΦ : d.toChart q ∈ (B.pullback hπ).atlas.charts := ⟨d, q, hc, rfl⟩
  set Φ1 := (B.pullback hπ).oneChart hΦ w₀ with hΦ1
  set G₂ : (d.ψ.model.E.prod d.c.F.shift) 0 → (d.c.φ.model.E.prod d.c.F.shift) 0 :=
    fun a => (d.g a.1, a.2) with hG₂
  have hgc : ContinuousOn d.g d.ψ.model.O := d.smooth.continuousOn d.ψ.model.isScRetract
  have hG₂c : ContinuousOn G₂ (d.ψ.model.O ×ˢ univ) :=
    (hgc.comp continuousOn_fst fun a ha => ha.1).prodMk continuousOn_snd
  have hmaps : MapsTo Φ1 Φ1.source (d.ψ.model.O ×ˢ univ) := fun w' hw' =>
    ⟨d.ψ.mapsTo_model _ hw', mem_univ _⟩
  have hcont : ContinuousOn (G₂ ∘ Φ1) Φ1.source :=
    hG₂c.comp Φ1.continuousOn_toFun hmaps
  have heq : ∀ w' ∈ Φ1.source, (G₂ ∘ Φ1) w' =
      d.c.liftOne ((B.pullback hπ).oneVal w').1.2 := fun w' hw' => by
    change ((d.g (d.ψ ((B.pullback hπ).oneVal w').1.1)),
      Function.invFun (d.c.F.toBase 1) (d.c ((B.pullback hπ).oneVal w').1.2).2) = _
    rw [d.g_apply hw']
    rfl
  refine ⟨Φ1.source ∩ (G₂ ∘ Φ1) ⁻¹' W, ?_, ?_, ?_⟩
  · rintro w' ⟨hw's, hw'W⟩
    refine ⟨d.mem_c_source hw's, ?_⟩
    change d.c.liftOne ((B.pullback hπ).oneVal w').1.2 ∈ W
    rw [← heq w' hw's]; exact hw'W
  · exact hcont.isOpen_inter_preimage Φ1.isOpen_source hW
  · have hw₀s : w₀ ∈ Φ1.source := hzd
    refine ⟨hw₀s, ?_⟩
    change (G₂ ∘ Φ1) w₀ ∈ W
    rw [heq w₀ hw₀s]; exact hw₀.2

variable (B) in
/-- **The pulled-back auxiliary norm** `π*N(z, y) = N(y)` on `(π*Y)[1]`. -/
def pullbackAuxNorm (N : B.One → ℝ) (w : (B.pullback hπ).One) : ℝ := N (pullbackOneMap hπ w)

/-- `AuxLe` for the pulled-back norm is `AuxLe` of the `Y`-component. -/
theorem auxLe_pullbackAuxNorm_iff {N : B.One → ℝ} {q : pullbackSpace P π} {r : ℝ} :
    (B.pullback hπ).AuxLe (B.pullbackAuxNorm hπ N) q r ↔ B.AuxLe N q.1.2 r :=
  ⟨fun ⟨hq, h⟩ => ⟨(pullback_mem_oneSet_iff hπ q).1 hq, h⟩,
    fun ⟨hq, h⟩ => ⟨(pullback_mem_oneSet_iff hπ q).2 hq, h⟩⟩

/-- The fibre `(π*Y)_{0,1}` over `z` is `Y_{0,1}` over `π(z)` (a linear bijection). -/
def pullbackOneFiberMap (z : Z) :
    (B.pullback hπ).oneFiber z →ₗ[ℝ] B.oneFiber (π z) where
  toFun v := ⟨pullbackFiberEquiv P π z v, (pullback_mem_oneSet_iff hπ _).1 v.2⟩
  map_add' v w := Subtype.ext (pullbackFiberEquiv_add P π z v w)
  map_smul' a v := Subtype.ext (pullbackFiberEquiv_smul P π z a v)

lemma pullbackOneMap_toOne {z : Z} (v : (B.pullback hπ).oneFiber z) :
    pullbackOneMap hπ ((B.pullback hπ).toOne v) = B.toOne (pullbackOneFiberMap hπ z v) := rfl

lemma pullbackOneFiberMap_injective (z : Z) :
    Injective (pullbackOneFiberMap (B := B) hπ z) := fun _ _ h =>
  Subtype.ext ((pullbackFiberEquiv P π z).injective (congrArg Subtype.val h))

lemma pullbackOneFiberMap_surjective (z : Z) :
    Surjective (pullbackOneFiberMap (B := B) hπ z) := fun v₀ =>
  ⟨⟨(pullbackFiberEquiv P π z).symm v₀, (pullback_mem_oneSet_iff hπ _).2 v₀.2⟩,
    Subtype.ext ((pullbackFiberEquiv P π z).apply_symm_apply _)⟩

/-- **The pulled-back auxiliary norm is an auxiliary norm** of `π*P` (2021 Definition 5.1.1,
p. 205, for the pull-back of Proposition 2.6.8, p. 75; preprint Proposition 2.54). -/
theorem IsAuxNorm.pullback {N : B.One → ℝ} (hN : B.IsAuxNorm N) :
    (B.pullback hπ).IsAuxNorm (B.pullbackAuxNorm hπ N) where
  continuous := hN.continuous.comp (continuous_pullbackOneMap hπ)
  fiber z :=
    { eq_zero := fun v hv => pullbackOneFiberMap_injective hπ z (by
        rw [map_zero]
        exact (hN.fiber (π z)).eq_zero _ hv)
      smul := fun t v => by
        change N (pullbackOneMap hπ ((B.pullback hπ).toOne (t • v))) =
          |t| * N (pullbackOneMap hπ ((B.pullback hπ).toOne v))
        rw [pullbackOneMap_toOne, pullbackOneMap_toOne, map_smul, hN.smul]
      add_le := fun v w => by
        change N (pullbackOneMap hπ ((B.pullback hπ).toOne (v + w))) ≤
          N (pullbackOneMap hπ ((B.pullback hπ).toOne v)) +
            N (pullbackOneMap hπ ((B.pullback hπ).toOne w))
        rw [pullbackOneMap_toOne, pullbackOneMap_toOne, pullbackOneMap_toOne, map_add]
        exact (hN.fiber (π z)).add_le _ _
      complete := fun u hu => by
        have hu' : ∀ m k, B.pullbackAuxNorm hπ N ((B.pullback hπ).toOne (u m - u k)) =
            N (B.toOne (pullbackOneFiberMap hπ z (u m) - pullbackOneFiberMap hπ z (u k))) :=
          fun m k => by
            change N (pullbackOneMap hπ ((B.pullback hπ).toOne (u m - u k))) = _
            rw [pullbackOneMap_toOne, map_sub]
        obtain ⟨v₀, hv₀⟩ := (hN.fiber (π z)).complete (fun k => pullbackOneFiberMap hπ z (u k))
          fun ε hε => by
            obtain ⟨n, hn⟩ := hu ε hε
            exact ⟨n, fun m hm k hk => by rw [← hu']; exact hn m hm k hk⟩
        obtain ⟨v, rfl⟩ := pullbackOneFiberMap_surjective hπ z v₀
        refine ⟨v, hv₀.congr fun k => ?_⟩
        change _ = N (pullbackOneMap hπ ((B.pullback hπ).toOne (u k - v)))
        rw [pullbackOneMap_toOne, map_sub] }
  tendsto_zeroOne w z hw hNw := by
    have hπc : Continuous π := continuousOn_univ.1 hπ.continuousOn
    have hB := hN.tendsto_zeroOne (fun k => pullbackOneMap hπ (w k)) (π z)
      (by
        have : Tendsto (fun k => π (pullbackProj P π ((B.pullback hπ).oneVal (w k)))) atTop
            (𝓝 (π z)) := (hπc.tendsto z).comp hw
        refine this.congr fun k => ?_
        change π (((B.pullback hπ).oneVal (w k)).1.1) = P (((B.pullback hπ).oneVal (w k)).1.2)
        exact (((B.pullback hπ).oneVal (w k)).2).symm) hNw
    have h0 : pullbackOneMap hπ ((B.pullback hπ).zeroOne z) = B.zeroOne (π z) := by
      apply B.oneVal_injective
      rw [oneVal_pullbackOneMap, oneVal_zeroOne]
      rfl
    rw [← h0] at hB
    refine (TopologicalSpace.tendsto_nhds_generateFrom_iff).2 ?_
    rintro s ⟨Φ, hΦ, W, hW, rfl⟩ ⟨h0s, h0W⟩
    obtain ⟨d, q₀, hd, rfl⟩ := hΦ
    set q0 := (B.pullback hπ).oneVal ((B.pullback hπ).zeroOne z) with hq0
    have hzψ : q0.1.1 ∈ d.ψ.source := h0s
    have hq0z : q0.1.1 = z := rfl
    -- the two components of `Φ[1]` converge
    have h1 : Tendsto (fun k => ((B.pullback hπ).oneVal (w k)).1.1) atTop (𝓝 q0.1.1) := hw
    have hψ : Tendsto (fun k => d.ψ ((B.pullback hπ).oneVal (w k)).1.1) atTop
        (𝓝 (d.ψ q0.1.1)) :=
      ((d.ψ.continuousOn_toFun.continuousAt (d.ψ.isOpen_source.mem_nhds hzψ)).tendsto).comp h1
    have hcs : B.oneVal (pullbackOneMap hπ ((B.pullback hπ).zeroOne z)) ∈
        d.c.toPartialEquiv.source := d.mem_c_source hzψ
    set Φ1 := B.oneChart hd (pullbackOneMap hπ ((B.pullback hπ).zeroOne z)) with hΦ1
    have hc1 : Tendsto (fun k => Φ1 (pullbackOneMap hπ (w k))) atTop
        (𝓝 (Φ1 (pullbackOneMap hπ ((B.pullback hπ).zeroOne z)))) :=
      ((Φ1.continuousOn_toFun.continuousAt (Φ1.isOpen_source.mem_nhds hcs)).tendsto).comp hB
    have hpair := hψ.prodMk_nhds (hc1.snd_nhds)
    have hev := hpair (hW.mem_nhds h0W)
    have hevs : ∀ᶠ k in atTop, ((B.pullback hπ).oneVal (w k)).1.1 ∈ d.ψ.source :=
      h1 (d.ψ.isOpen_source.mem_nhds hzψ)
    filter_upwards [hev, hevs] with k hk hks
    exact ⟨hks, hk⟩

end StrongBundle

end PullbackNorm


/-! ### Sections admissible for finitely many auxiliary norms -/

section Admissible

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

namespace StrongBundle

/-- Allowable sections for `(N, U)` are allowable for `(N', U')` when `N' ≤ N` and `U ⊆ U'`. -/
theorem allowableSections_mono {N N' : B.One → ℝ} {U U' : Set X} (hN : ∀ w, N' w ≤ N w)
    (hU : U ⊆ U') : B.allowableSections N U ⊆ B.allowableSections N' U' := by
  rintro s ⟨hs, hsupp, hsN⟩
  exact ⟨hs, hsupp.trans hU, fun x hx => (hN _).trans (hsN x hx)⟩

/-- **Finitely many auxiliary norms are dominated by one** (their maximum; for the empty family
an auxiliary norm from Proposition 5.1.3, 2021 p. 206; preprint Proposition 5.3). -/
theorem exists_isAuxNorm_ge {ι : Type*} (I : Finset ι) {N : ι → B.One → ℝ}
    (hN : ∀ i ∈ I, B.IsAuxNorm (N i)) :
    ∃ M : B.One → ℝ, B.IsAuxNorm M ∧ ∀ i ∈ I, ∀ w, N i w ≤ M w := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    obtain ⟨M, hM⟩ := proposition_5_1_3_exists (B := B)
    exact ⟨M, hM, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a I _ ih =>
    obtain ⟨M, hM, hMN⟩ := ih fun i hi => hN i (Finset.mem_insert_of_mem hi)
    refine ⟨fun w => Max.max (N a w) (M w), (hN a (Finset.mem_insert_self a I)).max hM,
      fun i hi w => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact le_max_left _ _
    · exact (hMN i hi w).trans (le_max_right _ _)

end StrongBundle

/-- **Sections admissible for finitely many auxiliary norms at once** (2021 §6.7 preamble, p. 276,
with the density statement of Theorem 5.3.10, p. 220; preprint Theorem 5.18): let `X` be tame
with sc-smooth bump functions and `f` an sc-Fredholm section (tame germ data) with compact
solution set. For finitely many auxiliary norms `Nᵢ` and every open `V ⊇ S_f` there is an
sc⁺-section `s`, allowable for every `(Nᵢ, V)`, with `(f + s, x)` in general position at every
zero. *Proof*: `theorem_5_3_10_relative_hyp` with `K = S_f`, `W = U` the neighbourhood of
`exists_adapted_margin` for a norm `M ≥ Nᵢ` (`exists_isAuxNorm_ge`) inside `V`. This is the step
"an `s₂` admissible for both pairs" of the proof of Theorem 6.7.1 (p. 278). -/
theorem exists_admissible_subset (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) {f : X → Y}
    (hf : B.IsScFredholmSectionTame f) (hS : IsCompact (solutionSet P f)) {ι : Type*}
    (I : Finset ι) {N : ι → B.One → ℝ} (hN : ∀ i ∈ I, B.IsAuxNorm (N i)) {V : Set X}
    (hV : IsOpen V) (hSV : solutionSet P f ⊆ V) :
    ∃ s : X → Y, (∀ i ∈ I, s ∈ B.allowableSections (N i) V) ∧
      ∀ x, IsZeroAt P (sectionAdd P f s) x → B.IsGeneralPositionGerm (sectionAdd P f s) x := by
  obtain ⟨M, hM, hMN⟩ := StrongBundle.exists_isAuxNorm_ge I hN
  obtain ⟨U, hUo, hSU, hUV, hcpt, -⟩ :=
    exists_adapted_margin hf.toIsScFredholmSection hS hM hV hSV
  obtain ⟨p, hp, hpsupp, hpN, hgp⟩ := theorem_5_3_10_relative_hyp hX hbump hf hM hUo hS hSU
    (fun x hx hxS => absurd hx hxS) (hcpt 1 one_pos) one_pos
  refine ⟨p, fun i hi => ⟨hp, hpsupp.trans hUV, fun x hx => ?_⟩, hgp⟩
  obtain ⟨_, h⟩ := hpN x
  exact (hMN i hi _).trans h

/-- **An admissible section** (2021 §6.7 preamble, p. 276; Theorem 5.3.10, p. 220): for an
auxiliary norm `N` and an open `V ⊇ S_f` there is `s ∈ allowableSections N V` with `(f + s, x)` in
general position at every zero. -/
theorem exists_admissible (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) {f : X → Y}
    (hf : B.IsScFredholmSectionTame f) (hS : IsCompact (solutionSet P f)) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N) {V : Set X} (hV : IsOpen V) (hSV : solutionSet P f ⊆ V) :
    ∃ s ∈ B.allowableSections N V,
      ∀ x, IsZeroAt P (sectionAdd P f s) x → B.IsGeneralPositionGerm (sectionAdd P f s) x := by
  obtain ⟨s, hs, hgp⟩ := exists_admissible_subset hX hbump hf hS ({()} : Finset Unit)
    (N := fun _ => N) (fun _ _ => hN) hV hSV
  exact ⟨s, hs () (Finset.mem_singleton_self _), hgp⟩

/-- **One section admissible for two pairs** `(N₀, U₀)` and `(N₁, U₁)` (the comparison of
different auxiliary norms in the proof of 2021 Theorem 6.7.1, p. 278): `exists_admissible_subset`
for `{N₀, N₁}` and `V = U₀ ∩ U₁`. -/
theorem exists_admissible_two (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) {f : X → Y}
    (hf : B.IsScFredholmSectionTame f) (hS : IsCompact (solutionSet P f)) {N₀ N₁ : B.One → ℝ}
    (hN₀ : B.IsAuxNorm N₀) (hN₁ : B.IsAuxNorm N₁) {U₀ U₁ : Set X} (hU₀ : IsOpen U₀)
    (hU₁ : IsOpen U₁) (hSU₀ : solutionSet P f ⊆ U₀) (hSU₁ : solutionSet P f ⊆ U₁) :
    ∃ s : X → Y, s ∈ B.allowableSections N₀ U₀ ∧ s ∈ B.allowableSections N₁ U₁ ∧
      ∀ x, IsZeroAt P (sectionAdd P f s) x → B.IsGeneralPositionGerm (sectionAdd P f s) x := by
  obtain ⟨s, hs, hgp⟩ := exists_admissible_subset hX hbump hf hS (Finset.univ : Finset Bool)
    (N := fun b => if b then N₁ else N₀) (fun b _ => by cases b <;> simpa) (hU₀.inter hU₁)
    (subset_inter hSU₀ hSU₁)
  exact ⟨s, StrongBundle.allowableSections_mono (fun _ => le_rfl) inter_subset_left
      (by simpa using hs false (Finset.mem_univ _)),
    StrongBundle.allowableSections_mono (fun _ => le_rfl) inter_subset_right
      (by simpa using hs true (Finset.mem_univ _)), hgp⟩

/-- **The hypotheses of `exists_cobordism` are satisfiable** (2021 §6.7 preamble, p. 276): for an
sc-Fredholm section with compact solution set and every auxiliary norm `N` there is an open
`U ⊇ S_f` with `cl{x ∈ U | N(f(x)) ≤ 2}` compact and an sc⁺-section admissible for `(N, U)`. -/
theorem exists_cobordism_data (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) {f : X → Y}
    (hf : B.IsScFredholmSectionTame f) (hS : IsCompact (solutionSet P f)) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      IsCompact (closure {x ∈ U | B.AuxLe N (f x) 2}) ∧
      ∃ s ∈ B.allowableSections N U,
        ∀ x, IsZeroAt P (sectionAdd P f s) x → B.IsGeneralPositionGerm (sectionAdd P f s) x := by
  obtain ⟨U, hUo, hSU, -, hcpt, -⟩ :=
    exists_adapted_margin hf.toIsScFredholmSection hS hN isOpen_univ (subset_univ _)
  exact ⟨U, hUo, hSU, hcpt 2 two_pos, exists_admissible hX hbump hf hS hN hUo hSU⟩

end Admissible


/-! ### The cut-off of the cobordism -/

section Cutoff

open scoped ContDiff

/-- The cut-off `χ(t) = κ((t − 3/16)·8/5)` of the cobordism (`κ = Real.smoothTransition`): `0` for
`t ≤ 3/16` and `1` for `t ≥ 13/16`. -/
def cylCut (t : ℝ) : ℝ := Real.smoothTransition ((t - 3 / 16) * (8 / 5))

lemma contDiff_cylCut : ContDiff ℝ ∞ cylCut :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).mul contDiff_const)

lemma cylCut_nonneg (t : ℝ) : 0 ≤ cylCut t := Real.smoothTransition.nonneg _

lemma cylCut_le_one (t : ℝ) : cylCut t ≤ 1 := Real.smoothTransition.le_one _

lemma cylCut_of_le {t : ℝ} (ht : t ≤ 3 / 16) : cylCut t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by nlinarith)

lemma cylCut_of_ge {t : ℝ} (ht : 13 / 16 ≤ t) : cylCut t = 1 :=
  Real.smoothTransition.one_of_one_le (by nlinarith)

end Cutoff

/-! ### Sections over `ℝ¹ × X`: slices, zeros and bounds -/

section CylinderSections

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- If `f + s` and `s` vanish at `x`, so does `f`. -/
lemma isZeroAt_left_of_isZeroAt_sectionAdd {f s : X → Y} (hf : IsSection P f) (hs : IsSection P s)
    {x : X} (h : IsZeroAt P (sectionAdd P f s) x) (hsx : IsZeroAt P s x) : IsZeroAt P f x := by
  have e : (⟨s x, hs x⟩ : P ⁻¹' {x}) = 0 := Subtype.ext hsx
  have h' : ((⟨f x, hf x⟩ : P ⁻¹' {x}) + ⟨s x, hs x⟩ : P ⁻¹' {x}) = 0 :=
    Subtype.ext ((sectionAdd_apply hf hs x).symm.trans h)
  rw [e, add_zero] at h'
  exact congrArg Subtype.val h'

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- `(f + s)(x)` depends on `s` only through `s(x)`. -/
lemma sectionAdd_congr_right {f s s' : X → Y} (hf : IsSection P f) (hs : IsSection P s)
    (hs' : IsSection P s') {x : X} (h : s x = s' x) :
    sectionAdd P f s x = sectionAdd P f s' x := by
  rw [sectionAdd_apply hf hs, sectionAdd_apply hf hs']
  have e : (⟨s x, hs x⟩ : P ⁻¹' {x}) = ⟨s' x, hs' x⟩ := Subtype.ext h
  rw [e]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- The fibre value of `a·s₀ + b·s₁`. -/
lemma sectionAdd_sectionSmul_apply {s₀ s₁ : X → Y} (h₀ : IsSection P s₀) (h₁ : IsSection P s₁)
    (a b : X → ℝ) (x : X) :
    sectionAdd P (sectionSmul P a s₀) (sectionSmul P b s₁) x =
      ((a x • (⟨s₀ x, h₀ x⟩ : P ⁻¹' {x}) + b x • ⟨s₁ x, h₁ x⟩ : P ⁻¹' {x}) : Y) := by
  rw [sectionAdd_apply (IsSection.sectionSmul (f := a) h₀) (IsSection.sectionSmul (f := b) h₁)]
  have e₀ : (⟨sectionSmul P a s₀ x, IsSection.sectionSmul h₀ x⟩ : P ⁻¹' {x}) =
      a x • ⟨s₀ x, h₀ x⟩ := Subtype.ext (sectionSmul_apply h₀ x)
  have e₁ : (⟨sectionSmul P b s₁ x, IsSection.sectionSmul h₁ x⟩ : P ⁻¹' {x}) =
      b x • ⟨s₁ x, h₁ x⟩ := Subtype.ext (sectionSmul_apply h₁ x)
  rw [e₀, e₁]

/-- **The interpolation `ŝ(t, x) = (1 − χ(t))·s₀(x) + χ(t)·s₁(x)`** of two sections over `ℝ¹ × X`
(`χ = cylCut`). -/
def cylInterp (s₀ s₁ : X → Y) (h₀ : IsSection P s₀) (h₁ : IsSection P s₁) :
    (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X) :=
  sectionAdd (pullbackProj P Prod.snd)
    (sectionSmul (pullbackProj P Prod.snd) (fun z => 1 - cylCut (z.1 0)) (constLift s₀ h₀))
    (sectionSmul (pullbackProj P Prod.snd) (fun z => cylCut (z.1 0)) (constLift s₁ h₁))

variable {s₀ s₁ : X → Y} (h₀ : IsSection P s₀) (h₁ : IsSection P s₁)

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
lemma isSection_cylInterp : IsSection (pullbackProj P Prod.snd) (cylInterp s₀ s₁ h₀ h₁) :=
  ((isSection_constLift s₀ h₀).sectionSmul).sectionAdd (isSection_constLift s₁ h₁).sectionSmul

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- The slices of `ŝ`: `ŝ(t, ·) = (1 − χ(t))·s₀ + χ(t)·s₁`. -/
lemma pullbackSlice_cylInterp (t : Fin 1 → ℝ) :
    pullbackSlice (cylInterp s₀ s₁ h₀ h₁) t =
      sectionAdd P (sectionSmul P (fun _ => 1 - cylCut (t 0)) s₀)
        (sectionSmul P (fun _ => cylCut (t 0)) s₁) := by
  rw [cylInterp, pullbackSlice_sectionAdd (isSection_constLift s₀ h₀).sectionSmul
      (isSection_constLift s₁ h₁).sectionSmul,
    pullbackSlice_sectionSmul (isSection_constLift s₀ h₀),
    pullbackSlice_sectionSmul (isSection_constLift s₁ h₁), pullbackSlice_constLift,
    pullbackSlice_constLift]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
lemma pullbackSlice_cylInterp_apply (t : Fin 1 → ℝ) (x : X) :
    pullbackSlice (cylInterp s₀ s₁ h₀ h₁) t x =
      (((1 - cylCut (t 0)) • (⟨s₀ x, h₀ x⟩ : P ⁻¹' {x}) + cylCut (t 0) • ⟨s₁ x, h₁ x⟩ :
        P ⁻¹' {x}) : Y) := by
  rw [pullbackSlice_cylInterp, sectionAdd_sectionSmul_apply h₀ h₁]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- `ŝ(t, ·) = s₀` for `t ≤ 3/16`. -/
lemma pullbackSlice_cylInterp_of_le {t : Fin 1 → ℝ} (ht : t 0 ≤ 3 / 16) :
    pullbackSlice (cylInterp s₀ s₁ h₀ h₁) t = s₀ := by
  funext x
  rw [pullbackSlice_cylInterp_apply, cylCut_of_le ht]
  simp

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- `ŝ(t, ·) = s₁` for `t ≥ 13/16`. -/
lemma pullbackSlice_cylInterp_of_ge {t : Fin 1 → ℝ} (ht : 13 / 16 ≤ t 0) :
    pullbackSlice (cylInterp s₀ s₁ h₀ h₁) t = s₁ := by
  funext x
  rw [pullbackSlice_cylInterp_apply, cylCut_of_ge ht]
  simp

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- `ŝ(t, x) = 0` where `s₀(x) = s₁(x) = 0`. -/
lemma isZeroAt_pullbackSlice_cylInterp {x : X} (hx₀ : IsZeroAt P s₀ x) (hx₁ : IsZeroAt P s₁ x)
    (t : Fin 1 → ℝ) : IsZeroAt P (pullbackSlice (cylInterp s₀ s₁ h₀ h₁) t) x := by
  have e₀ : (⟨s₀ x, h₀ x⟩ : P ⁻¹' {x}) = 0 := Subtype.ext hx₀
  have e₁ : (⟨s₁ x, h₁ x⟩ : P ⁻¹' {x}) = 0 := Subtype.ext hx₁
  unfold IsZeroAt
  rw [pullbackSlice_cylInterp_apply, e₀, e₁, smul_zero, smul_zero, add_zero]
  rfl

/-- `N(ŝ(t, x)) ≤ 1` when `N(s₀(x)), N(s₁(x)) ≤ 1` (a convex combination). -/
lemma auxLe_pullbackSlice_cylInterp {N : B.One → ℝ} (hN : B.IsAuxNorm N) {x : X}
    (hx₀ : B.AuxLe N (s₀ x) 1) (hx₁ : B.AuxLe N (s₁ x) 1) (t : Fin 1 → ℝ) :
    B.AuxLe N (pullbackSlice (cylInterp s₀ s₁ h₀ h₁) t x) 1 := by
  rw [pullbackSlice_cylInterp]
  refine (hN.auxLe_sectionAdd h₀.sectionSmul h₁.sectionSmul (hN.auxLe_sectionSmul h₀ _ hx₀)
    (hN.auxLe_sectionSmul h₁ _ hx₁)).mono (le_of_eq ?_)
  show |1 - cylCut (t 0)| * 1 + |cylCut (t 0)| * 1 = 1
  rw [abs_of_nonneg (sub_nonneg.2 (cylCut_le_one _)), abs_of_nonneg (cylCut_nonneg _)]
  ring

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- A section of `π*P` over `ℝ¹ × X` equals the lift `g̃` at `z` when its slice at `z.1` takes the
value `g(z.2)`. -/
lemma eq_paramLift_of_pullbackSlice {T : (Fin 1 → ℝ) × X → pullbackSpace P Prod.snd}
    (hT : IsSection (pullbackProj P Prod.snd) T) {g : X → Y} (hg : IsSection P g)
    {z : (Fin 1 → ℝ) × X} (h : pullbackSlice T z.1 z.2 = g z.2) : T z = paramLift g hg z :=
  Subtype.ext (Prod.ext (hT z) h)

variable {f : X → Y} (hf : IsSection P f)

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- A zero of `f̃ + T` lies over `U` when `T` vanishes over the complement of `U` and `S_f ⊆ U`. -/
lemma mem_of_isZeroAt_paramLift_add {T : (Fin 1 → ℝ) × X → pullbackSpace P Prod.snd}
    (hT : IsSection (pullbackProj P Prod.snd) T) {U : Set X} (hSU : solutionSet P f ⊆ U)
    (hTU : ∀ z : (Fin 1 → ℝ) × X, z.2 ∉ U → IsZeroAt P (pullbackSlice T z.1) z.2)
    {z : (Fin 1 → ℝ) × X}
    (hz : IsZeroAt (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
      (paramLift f hf) T) z) : z.2 ∈ U := by
  by_contra hzU
  have hL : IsSection (pullbackProj P Prod.snd) (paramLift (n := 1) f hf) :=
    isSection_pullbackLift _
  have h1 := (isZeroAt_pullback_iff_pullbackSlice (hL.sectionAdd hT) z.1 z.2).1 hz
  rw [pullbackSlice_sectionAdd_paramLift hf hT] at h1
  exact hzU (hSU (isZeroAt_left_of_isZeroAt_sectionAdd hf (hT.pullbackSlice z.1) h1 (hTU z hzU)))

/-- `N(f(x)) ≤ a + b` when `N((f̃ + T)(t, x)) ≤ a` and `N(T(t, x)) ≤ b`. -/
lemma auxLe_of_auxLe_paramLift_add {N : B.One → ℝ} (hN : B.IsAuxNorm N)
    {T : (Fin 1 → ℝ) × X → pullbackSpace P Prod.snd} (hT : IsSection (pullbackProj P Prod.snd) T)
    {z : (Fin 1 → ℝ) × X} {a b : ℝ}
    (h : B.AuxLe N (pullbackSlice (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf) T)
      z.1 z.2) a)
    (hb : B.AuxLe N (pullbackSlice T z.1 z.2) b) : B.AuxLe N (f z.2) (a + b) := by
  rw [pullbackSlice_sectionAdd_paramLift hf hT] at h
  exact hN.auxLe_of_sectionAdd_le hf (hT.pullbackSlice z.1) h hb

end CylinderSections


/-! ### The cobordism between two admissible sections -/

section Cobordism

open scoped ContDiff

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]

omit [T2Space X] [ParacompactSpace X] [ParacompactSpace ((Fin 1 → ℝ) × X)] in
lemma continuous_fst_apply_zero : Continuous fun z : (Fin 1 → ℝ) × X => z.1 0 :=
  (continuous_apply 0).comp continuous_fst

lemma mem_Icc_of_apply_zero {r : Fin 1 → ℝ} {a b : ℝ} (h : r 0 ∈ Icc a b) :
    r ∈ Icc (fun _ : Fin 1 => a) (fun _ => b) :=
  ⟨fun i => by rw [Fin.fin_one_eq_zero i]; exact h.1,
    fun i => by rw [Fin.fin_one_eq_zero i]; exact h.2⟩

/-- A function of `t` alone is sc-smooth on `ℝ¹ × X`. -/
lemma isScSmoothMap_of_contDiff_fst {g : (Fin 1 → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) :
    ((rnPolyfold 1).prod PX).IsScSmoothMap realPolyfold fun z => g z.1 :=
  (isScSmoothMap_rn_real_of_contDiff hg).comp (MPolyfold.isScSmoothMap_fst (rnPolyfold 1) PX)

/-- `ŝ = (1 − χ)·s̃₀ + χ·s̃₁` is an sc⁺-section of `π*P` for sc⁺-sections `s₀, s₁`
(`IsScPlusSection.smul_left`, `IsScPlusSection.add`, `isScPlusSection_constLift`). -/
theorem isScPlusSection_cylInterp {s₀ s₁ : X → Y} (h₀ : B.IsScPlusSection s₀)
    (h₁ : B.IsScPlusSection s₁) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection
      (cylInterp s₀ s₁ h₀.1 h₁.1) :=
  ((isScPlusSection_constLift h₀).smul_left (isScSmoothMap_of_contDiff_fst
      (g := fun r => 1 - cylCut (r 0))
      (contDiff_const.sub (contDiff_cylCut.comp (contDiff_apply ℝ ℝ 0))))).add
    ((isScPlusSection_constLift h₁).smul_left (isScSmoothMap_of_contDiff_fst
      (g := fun r => cylCut (r 0)) (contDiff_cylCut.comp (contDiff_apply ℝ ℝ 0))))

variable {f : X → Y}

/-- **Compact slabs**: if `T` vanishes over `X ∖ U`, `N(T) ≤ 2`, `S_f ⊆ U` and
`cl{x ∈ U | N(f(x)) ≤ 2}` is compact, then the zeros of `f̃ + T` over `t ∈ [a, b]` form a compact
set (they lie in `[a, b] × cl{x ∈ U | N(f(x)) ≤ 2}`). -/
theorem isCompact_slab_paramLift_add (hf : B.IsScFredholmSectionTame f) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N) {U : Set X} (hSU : solutionSet P f ⊆ U)
    (hcpt : IsCompact (closure {x ∈ U | B.AuxLe N (f x) 2}))
    {T : (Fin 1 → ℝ) × X → pullbackSpace P Prod.snd}
    (hT : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection T)
    (hTU : ∀ z : (Fin 1 → ℝ) × X, z.2 ∉ U → IsZeroAt P (pullbackSlice T z.1) z.2)
    (hTN : ∀ z : (Fin 1 → ℝ) × X, B.AuxLe N (pullbackSlice T z.1 z.2) 2) (a b : ℝ) :
    IsCompact {z ∈ solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) T) |
        z.1 0 ∈ Icc a b} := by
  have hfs : IsSection P f := hf.isScSmooth.1
  have hH := theorem_3_1_18_tame hf.param hT
  have hL : IsSection (pullbackProj P Prod.snd) (paramLift (n := 1) f hfs) :=
    isSection_pullbackLift _
  have hcl : IsClosed {z ∈ solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs) T) | z.1 0 ∈ Icc a b} :=
    (isClosed_solutionSet hH.isScSmooth).inter
      ((isClosed_Icc (a := a) (b := b)).preimage (continuous_fst_apply_zero (X := X)))
  refine ((isCompact_Icc (a := fun _ : Fin 1 => a) (b := fun _ => b)).prod hcpt).of_isClosed_subset
    hcl ?_
  rintro z ⟨hz, ht⟩
  refine ⟨mem_Icc_of_apply_zero ht,
    subset_closure ⟨mem_of_isZeroAt_paramLift_add hfs hT.1 hSU hTU hz, ?_⟩⟩
  have h0 : B.AuxLe N (pullbackSlice (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs) T)
      z.1 z.2) 0 :=
    (hN.auxLe_fiberZero z.2 le_rfl).congr
      ((isZeroAt_pullback_iff_pullbackSlice (hL.sectionAdd hT.1) z.1 z.2).1 hz).symm
  simpa using auxLe_of_auxLe_paramLift_add hfs hN hT.1 h0 (hTN z)

/-- **General position where the perturbation is `t`-constant**: if the slices of `T` near the
zero `z` (on an open `O ∋ z`) are those of an sc⁺-section `s` with `(f + s, x)` in general position
at every zero, then `(f̃ + T, z)` is in general position (`f̃ + T = (f + s)~` on `O`,
`isGeneralPositionGerm_paramLift`, `isGeneralPositionGerm_congr_nhds`). -/
theorem isGeneralPositionGerm_paramLift_add_of_eq (hf : B.IsScFredholmSectionTame f)
    {T : (Fin 1 → ℝ) × X → pullbackSpace P Prod.snd}
    (hT : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection T)
    {s : X → Y} (hs : B.IsScPlusSection s) {O : Set ((Fin 1 → ℝ) × X)} (hO : IsOpen O)
    (hTO : ∀ w ∈ O, pullbackSlice T w.1 w.2 = s w.2)
    (hgp : ∀ x, IsZeroAt P (sectionAdd P f s) x → B.IsGeneralPositionGerm (sectionAdd P f s) x)
    {z : (Fin 1 → ℝ) × X} (hzO : z ∈ O)
    (hz : IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) T) z) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsGeneralPositionGerm
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) T) z := by
  have hfs : IsSection P f := hf.isScSmooth.1
  have hg := theorem_3_1_18_tame hf hs
  have hL : IsSection (pullbackProj P Prod.snd) (paramLift (n := 1) f hfs) :=
    isSection_pullbackLift _
  have heq : ∀ w ∈ O, paramLift (sectionAdd P f s) hg.isScSmooth.1 w =
      sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs) T w := by
    intro w hw
    refine (eq_paramLift_of_pullbackSlice (hL.sectionAdd hT.1) _ ?_).symm
    rw [pullbackSlice_sectionAdd_paramLift hfs hT.1]
    exact sectionAdd_congr_right hfs (hT.1.pullbackSlice w.1) hs.1 (hTO w hw)
  have hzL : IsZeroAt (pullbackProj P Prod.snd)
      (paramLift (n := 1) (sectionAdd P f s) hg.isScSmooth.1) z :=
    (isZeroAt_congr (heq z hzO)).2 hz
  have hz' : IsZeroAt P (sectionAdd P f s) z.2 :=
    (isZeroAt_pullback_iff_pullbackSlice (isSection_pullbackLift _) z.1 z.2).1 hzL
  exact isGeneralPositionGerm_congr_nhds hg.param (theorem_3_1_18_tame hf.param hT) hzL hO hzO
    heq (isGeneralPositionGerm_paramLift hg hz' (hgp z.2 hz') z.1)


/-- **The cobordism between two admissible sections** (2021 Remark 5.3.8, p. 219, and the proof of
Theorem 6.7.1, p. 278; preprint Remark 5.16 and Theorem 6.43), in the form used for Theorem 6.7.1:
let `X` be tame with sc-smooth bump functions, `f` an sc-Fredholm section (tame germ data), `N` an
auxiliary norm and `U ⊇ S_f` open with `cl{x ∈ U | N(f(x)) ≤ 2}` compact (the margin of
`exists_adapted_margin`). For `s₀, s₁ ∈ allowableSections N U` with `f + sᵢ` in general position
at every zero there is an sc⁺-section `S` of the pull-back to `ℝ¹ × X` with `S(t, ·) = s₀` for
`t ≤ 1/8`, `S(t, ·) = s₁` for `t ≥ 7/8`, `S = 0` over `X ∖ U`, `N(S) ≤ 2`, `f̃ + S` in general
position at every zero, and the zeros of `f̃ + S` over every `[a, b]` compact. The text's
cobordism is a section of the bundle over `[0, 1] × X`; here it lives on `ℝ¹ × X` and is
stationary near the ends (reading D2 of the plan). *Proof*: `S = ŝ + p`, `ŝ = (1 − χ)s̃₀ + χs̃₁`,
`p` from `theorem_5_3_10_relative_hyp` for `G = f̃ + ŝ`, the pulled-back norm, `W = (1/8, 7/8) × U`
and `K` the zeros over `[3/16, 13/16]`; off `K` the section `G` is `(f + sᵢ)~` near its zeros. -/
theorem exists_cobordism (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) {N : B.One → ℝ} (hN : B.IsAuxNorm N) {U : Set X}
    (hU : IsOpen U) (hSU : solutionSet P f ⊆ U)
    (hcpt : IsCompact (closure {x ∈ U | B.AuxLe N (f x) 2})) {s₀ s₁ : X → Y}
    (hs₀ : s₀ ∈ B.allowableSections N U) (hs₁ : s₁ ∈ B.allowableSections N U)
    (hgp₀ : ∀ x, IsZeroAt P (sectionAdd P f s₀) x →
      B.IsGeneralPositionGerm (sectionAdd P f s₀) x)
    (hgp₁ : ∀ x, IsZeroAt P (sectionAdd P f s₁) x →
      B.IsGeneralPositionGerm (sectionAdd P f s₁) x) :
    ∃ S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X),
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S ∧
      (∀ t : Fin 1 → ℝ, t 0 ≤ 1 / 8 → pullbackSlice S t = s₀) ∧
      (∀ t : Fin 1 → ℝ, 7 / 8 ≤ t 0 → pullbackSlice S t = s₁) ∧
      (∀ z : (Fin 1 → ℝ) × X, z.2 ∉ U → IsZeroAt P (pullbackSlice S z.1) z.2) ∧
      (∀ z : (Fin 1 → ℝ) × X, B.AuxLe N (pullbackSlice S z.1 z.2) 2) ∧
      (∀ z, IsZeroAt (pullbackProj P Prod.snd)
          (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) z →
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsGeneralPositionGerm
          (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) z) ∧
      ∀ a b : ℝ, IsCompact {z ∈ solutionSet (pullbackProj P Prod.snd)
          (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) |
        z.1 0 ∈ Icc a b} := by
  classical
  have hfs : IsSection P f := hf.isScSmooth.1
  obtain ⟨hs₀p, hs₀U, hs₀N⟩ := hs₀
  obtain ⟨hs₁p, hs₁U, hs₁N⟩ := hs₁
  have hs₀N' : ∀ x, B.AuxLe N (s₀ x) 1 := fun x => ⟨hs₀p.mem_oneSet x, hs₀N x _⟩
  have hs₁N' : ∀ x, B.AuxLe N (s₁ x) 1 := fun x => ⟨hs₁p.mem_oneSet x, hs₁N x _⟩
  have hL : IsSection (pullbackProj P Prod.snd) (paramLift (n := 1) f hfs) :=
    isSection_pullbackLift _
  -- the interpolation `ŝ` and `G = f̃ + ŝ`
  set ŝ := cylInterp s₀ s₁ hs₀p.1 hs₁p.1 with hŝdef
  have hŝ := isScPlusSection_cylInterp (B := B) hs₀p hs₁p
  have hŝU : ∀ z : (Fin 1 → ℝ) × X, z.2 ∉ U → IsZeroAt P (pullbackSlice ŝ z.1) z.2 :=
    fun z hz => isZeroAt_pullbackSlice_cylInterp hs₀p.1 hs₁p.1
      (StrongBundle.isZeroAt_of_not_mem_of_support_subset hs₀U hz)
      (StrongBundle.isZeroAt_of_not_mem_of_support_subset hs₁U hz) z.1
  have hŝN : ∀ z : (Fin 1 → ℝ) × X, B.AuxLe N (pullbackSlice ŝ z.1 z.2) 1 := fun z =>
    auxLe_pullbackSlice_cylInterp hs₀p.1 hs₁p.1 hN (hs₀N' z.2) (hs₁N' z.2) z.1
  have hGt := theorem_3_1_18_tame (hf.param (n := 1)) hŝ
  have hN₁ := hN.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)
  -- `W = (1/8, 7/8) × U` and the compact `K` of the zeros over `[3/16, 13/16]`
  set W : Set ((Fin 1 → ℝ) × X) := {z | z.1 0 ∈ Ioo (1 / 8 : ℝ) (7 / 8) ∧ z.2 ∈ U} with hWdef
  have hWo : IsOpen W :=
    (isOpen_Ioo.preimage continuous_fst_apply_zero).inter (hU.preimage continuous_snd)
  set K := {z ∈ solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs) ŝ) |
    z.1 0 ∈ Icc (3 / 16 : ℝ) (13 / 16)} with hKdef
  have hK : IsCompact K := isCompact_slab_paramLift_add hf hN hSU hcpt hŝ hŝU
    (fun z => (hŝN z).mono one_le_two) _ _
  have hKW : K ⊆ W := fun z hz =>
    ⟨⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩,
      mem_of_isZeroAt_paramLift_add hfs hŝ.1 hSU hŝU hz.1⟩
  -- off `K`, `G` is `(f + sᵢ)~` near its zeros
  have hgpK : ∀ z, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs) ŝ) z → z ∉ K →
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsGeneralPositionGerm
        (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs) ŝ) z := by
    intro z hz hzK
    have ht : z.1 0 < 3 / 16 ∨ 13 / 16 < z.1 0 := by
      by_contra h
      simp only [not_or, not_lt] at h
      exact hzK ⟨hz, h⟩
    rcases ht with ht | ht
    · exact isGeneralPositionGerm_paramLift_add_of_eq hf hŝ hs₀p
        (isOpen_lt continuous_fst_apply_zero continuous_const)
        (fun w hw => congrFun (pullbackSlice_cylInterp_of_le hs₀p.1 hs₁p.1
          (le_of_lt (hw : w.1 0 < 3 / 16))) w.2) hgp₀ ht hz
    · exact isGeneralPositionGerm_paramLift_add_of_eq hf hŝ hs₁p
        (isOpen_lt continuous_const continuous_fst_apply_zero)
        (fun w hw => congrFun (pullbackSlice_cylInterp_of_ge hs₀p.1 hs₁p.1
          (le_of_lt (hw : 13 / 16 < w.1 0))) w.2) hgp₁ ht hz
  -- the compact `cl{z ∈ W | N(G(z)) ≤ 1}`
  have hcpt₁ : IsCompact (closure {z ∈ W |
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).AuxLe
        (B.pullbackAuxNorm (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX) N)
        (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs) ŝ z) 1}) := by
    refine ((isCompact_Icc (a := fun _ : Fin 1 => (1 / 8 : ℝ)) (b := fun _ => 7 / 8)).prod
      hcpt).of_isClosed_subset isClosed_closure (closure_minimal ?_
        (isClosed_Icc.prod isClosed_closure))
    rintro z ⟨hzW, hzN⟩
    refine ⟨mem_Icc_of_apply_zero ⟨hzW.1.1.le, hzW.1.2.le⟩, subset_closure ⟨hzW.2, ?_⟩⟩
    have h1 := (StrongBundle.auxLe_pullbackAuxNorm_iff _).1 hzN
    have := auxLe_of_auxLe_paramLift_add hfs hN hŝ.1 h1 (hŝN z)
    exact this.mono (by norm_num)
  -- the perturbation `p`
  obtain ⟨p, hp, hpW, hpN, hgpp⟩ := theorem_5_3_10_relative_hyp (prod_rn_isTame hX)
    (MPolyfold.admitsBumpFunctions_prod_rn hbump) hGt hN₁ hWo hK hKW hgpK hcpt₁ one_pos
  have hpZ : ∀ z ∉ W, IsZeroAt P (pullbackSlice p z.1) z.2 := fun z hz =>
    (isZeroAt_pullback_iff_pullbackSlice hp.1 z.1 z.2).1
      (StrongBundle.isZeroAt_of_not_mem_of_support_subset hpW hz)
  have hpN' : ∀ z : (Fin 1 → ℝ) × X, B.AuxLe N (pullbackSlice p z.1 z.2) 1 := fun z =>
    (StrongBundle.auxLe_pullbackAuxNorm_iff _).1 (hpN z)
  have hslice : ∀ t, pullbackSlice (sectionAdd (pullbackProj P Prod.snd) ŝ p) t =
      sectionAdd P (pullbackSlice ŝ t) (pullbackSlice p t) := fun t =>
    pullbackSlice_sectionAdd hŝ.1 hp.1 t
  have hp0 : ∀ t : Fin 1 → ℝ, t 0 ∉ Ioo (1 / 8 : ℝ) (7 / 8) → pullbackSlice p t = fiberZero P :=
    fun t ht => funext fun x => hpZ (t, x) fun h => ht h.1
  have hS := hŝ.add hp
  refine ⟨sectionAdd (pullbackProj P Prod.snd) ŝ p, hS, fun t ht => ?_, fun t ht => ?_,
    fun z hz => ?_, fun z => ?_, fun z hz => ?_, fun a b => ?_⟩
  · rw [hslice, hp0 t fun h => by linarith [h.1],
      pullbackSlice_cylInterp_of_le hs₀p.1 hs₁p.1 (by linarith), sectionAdd_fiberZero hs₀p.1]
  · rw [hslice, hp0 t fun h => by linarith [h.2],
      pullbackSlice_cylInterp_of_ge hs₀p.1 hs₁p.1 (by linarith), sectionAdd_fiberZero hs₁p.1]
  · have h1 := hŝU z hz
    have h2 := hpZ z fun h => hz h.2
    unfold IsZeroAt at h1 h2 ⊢
    rw [hslice, sectionAdd_apply (hŝ.1.pullbackSlice z.1) (hp.1.pullbackSlice z.1)]
    have e₁ : (⟨pullbackSlice ŝ z.1 z.2, hŝ.1.pullbackSlice z.1 z.2⟩ : P ⁻¹' {z.2}) = 0 :=
      Subtype.ext h1
    have e₂ : (⟨pullbackSlice p z.1 z.2, hp.1.pullbackSlice z.1 z.2⟩ : P ⁻¹' {z.2}) = 0 :=
      Subtype.ext h2
    rw [e₁, e₂, add_zero]
    rfl
  · rw [hslice]
    exact (hN.auxLe_sectionAdd (hŝ.1.pullbackSlice z.1) (hp.1.pullbackSlice z.1) (hŝN z)
      (hpN' z)).mono (by norm_num)
  · rw [← sectionAdd_assoc hL hŝ.1 hp.1] at hz ⊢
    exact hgpp z hz
  · have hSU' : ∀ z : (Fin 1 → ℝ) × X, z.2 ∉ U →
        IsZeroAt P (pullbackSlice (sectionAdd (pullbackProj P Prod.snd) ŝ p) z.1) z.2 := by
      intro z hz
      have h1 := hŝU z hz
      have h2 := hpZ z fun h => hz h.2
      unfold IsZeroAt at h1 h2 ⊢
      rw [hslice, sectionAdd_apply (hŝ.1.pullbackSlice z.1) (hp.1.pullbackSlice z.1)]
      have e₁ : (⟨pullbackSlice ŝ z.1 z.2, hŝ.1.pullbackSlice z.1 z.2⟩ : P ⁻¹' {z.2}) = 0 :=
        Subtype.ext h1
      have e₂ : (⟨pullbackSlice p z.1 z.2, hp.1.pullbackSlice z.1 z.2⟩ : P ⁻¹' {z.2}) = 0 :=
        Subtype.ext h2
      rw [e₁, e₂, add_zero]
      rfl
    refine isCompact_slab_paramLift_add hf hN hSU hcpt hS hSU' (fun z => ?_) a b
    rw [hslice]
    exact (hN.auxLe_sectionAdd (hŝ.1.pullbackSlice z.1) (hp.1.pullbackSlice z.1) (hŝN z)
      (hpN' z)).mono (by norm_num)

end Cobordism

end Polyfold
