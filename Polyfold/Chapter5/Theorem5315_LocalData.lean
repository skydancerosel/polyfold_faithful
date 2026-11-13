import Polyfold.Chapter5.Theorem5315_LocalTangent

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §5.3, the local data of
**Theorem 5.3.15** (p. 223; preprint: Theorem 5.22) from the implicit function theorem
(Theorem 3.6.8, p. 136) and Definition 5.3.13 (3), third step.  Gap G.48.

# The three local statements (A1)–(A3)

## The text, paraphrased

(Proof of Theorem 5.3.15, pp. 223–227) After the first perturbation `(f, x)` is in general
position at every zero.  Near `∂S` the function `t|S` has no critical points.  At an interior
critical point `x` the sections `sᵢ` are chosen with `sᵢ(x) = −f'(x) b(eᵢ)`, where `dt(x) b = τ`
(Lemma 5.3.16), and the solution sets of the families `f + Σ λᵢ sᵢ` are manifolds on which `λ`
is a submersion.

## What is formalized

* `StrongBundle.exists_isSmoothParam_solutionSet`: a zero in general position has a smooth
  parametrization of the solution set by a set `Ω ⊆ ℝⁿ` with unique derivatives, which is a
  neighbourhood of the parameter point when `d_X = 0` there (Theorem 3.6.8 through
  `TangentGermChart.exists_isSmoothParam`).
* `StrongBundle.isRegularPointOn_of_extremum` (**(A3)**): a zero `x` in general position at
  which `t` has a minimum or maximum on `X`, with `dt(x) ≠ 0`, is a regular point of `t|S_f`.
  The degeneracy index of `x` is arbitrary: `dt(x)` vanishes on the reduced tangent space
  because the reduced directions are two-sided (`scDeriv_eq_zero_of_extremum`), and
  `T_xX = ker f'(x) + T^R_xX`.
* `StrongBundle.hasFamilyParam` (**(A1)**): for a zero `y` with `d_X(y) = 0` in general
  position and sc⁺-sections `σ₁, …, σ_k`, the solution set of `(μ, y) ↦ f(y) + Σ μ_j σ_j(y)` has
  a smooth parametrization by an open set around `(0, y)` on which `μ` is a submersion
  (`f'(y)` is onto, so every `δμ` is the first component of a kernel vector of `F'(0, y)`).
* `StrongBundle.exists_hasRegularFamilyParam` (**(A2)**): at such a zero with `dt(y) ≠ 0`
  there is an sc⁺-section `σ`, as small as wanted, with `d(t ∘ pr₂)(0, y) ≠ 0` on the solution
  set of `f + μσ`: `σ(y) = −c f'(y) w₁` for a smooth tangent vector `w₁` with `dt(y) w₁ ≠ 0`
  (smooth vectors are dense; `f'(y)` is an sc-operator at the smooth point `y`; Lemma 5.3.3).
* `StrongBundle.hasMorseLocalData`: the three together, for a generalized compact homotopy.

## What the text leaves implicit, and the choices made

* (A3) at a corner point (`d_X(x) ≥ 2`): no hypothesis on the degeneracy index is needed.  Only
  `0 ≤ t ≤ 1` and `t(x) ∈ {0, 1}` are used, not the structure of the ends `Xᵢ`.
* (A2): the text's vector `b(eᵢ)` lies in an algebraic complement `Z` of `ker dt(x)`; for the
  section through `−f'(x) b` to exist the value has to be a smooth point of the fibre.  Here the
  tangent vector is chosen smooth.
-/

open Set Function Module Topology Filter
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

/-! ### The parametrization at a zero in general position -/

section Param

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- A smooth parametrization whose domain is a neighbourhood of `u₀` restricts to one with an
open domain. -/
lemma MPolyfold.IsSmoothParam.exists_isOpen_of_mem_nhds {A : Set X} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {Ω : Set E} {p : E → X}
    {q : X → E} {G : Set X} (h : PX.IsSmoothParam A Ω p q G) {u₀ : E} (hu₀ : Ω ∈ 𝓝 u₀) :
    ∃ (Ω' : Set E) (G' : Set X), PX.IsSmoothParam A Ω' p q G' ∧ IsOpen Ω' ∧ u₀ ∈ Ω' ∧
      Ω' ⊆ Ω := by
  have hmem : ∀ u ∈ Ω, (u ∈ p ⁻¹' (q ⁻¹' interior Ω) ↔ u ∈ interior Ω) := fun u hu => by
    rw [mem_preimage, mem_preimage, h.left_inv u hu]
  have heq : Ω ∩ p ⁻¹' (q ⁻¹' interior Ω) = interior Ω := by
    ext u
    exact ⟨fun hu => (hmem u hu.1).1 hu.2, fun hu =>
      ⟨interior_subset hu, (hmem u (interior_subset hu)).2 hu⟩⟩
  refine ⟨Ω ∩ p ⁻¹' (q ⁻¹' interior Ω), G ∩ q ⁻¹' interior Ω,
    h.restrict (_root_.isOpen_interior.preimage h.continuous_q) rfl, ?_, ?_, inter_subset_left⟩
  · rw [heq]; exact _root_.isOpen_interior
  · rw [heq]; exact mem_interior_iff_mem_nhds.2 hu₀

variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

/-- **A smooth parametrization of the solution set around a zero in general position** (2021
Theorem 3.6.8, p. 136): by a set `Ω ⊆ ℝⁿ` with unique derivatives; `Ω` is a neighbourhood of
the parameter point if the degeneracy index of the zero is `0`. -/
theorem StrongBundle.exists_isSmoothParam_solutionSet (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) {y : X} (hy0 : IsZeroAt P f y)
    (hgp : B.IsGeneralPositionGerm f y) :
    ∃ (n : ℕ) (Ω : Set (Fin n → ℝ)) (p : (Fin n → ℝ) → X) (q : X → Fin n → ℝ) (G : Set X)
      (u₀ : Fin n → ℝ), PX.IsSmoothParam (solutionSet P f) Ω p q G ∧ UniqueDiffOn ℝ Ω ∧
        u₀ ∈ Ω ∧ p u₀ = y ∧ (PX.degIndex y = 0 → Ω ∈ 𝓝 u₀) := by
  have hgood := hgp.isGoodPositionGermTame hf hy0
  obtain ⟨Vx, d, -, -, -, D, hreg, -, -⟩ := theorem_3_6_8_index hf hgood hy0
  obtain ⟨Ω, q, G, OE, hpar, hOE, hΩ, h0, hp0⟩ := D.exists_isSmoothParam hbump hreg
  have hfr : finrank ℝ (Fin d → ℝ) = finrank ℝ D.N := by rw [D.finrank_eq]; simp
  set e : (Fin d → ℝ) ≃L[ℝ] D.N := ContinuousLinearEquiv.ofFinrankEq hfr with he
  have hUD : UniqueDiffOn ℝ Ω := by
    rw [hΩ]
    have h1 : UniqueDiffOn ℝ D.V := fun v hv =>
      D.V_isRelOpenInQuadrant.isScDomain.uniqueDiffWithinAt 0 v hv
    exact h1.inter hOE
  have hmem : e.symm 0 ∈ e ⁻¹' Ω := by simpa using h0
  refine ⟨d, e ⁻¹' Ω, _, _, G, e.symm 0, hpar.comp_equiv e, e.uniqueDiffOn_preimage_iff.2 hUD,
    hmem, by simpa using hp0, fun hdeg => ?_⟩
  obtain ⟨R, hR, hRt⟩ := D.tame
  obtain ⟨n, W, T, hT⟩ := D.φ.model.isPartialQuadrant
  have h1 := PX.degIndex_eq_chartDegIndex_of_isTameWith D.isChart R hR hT (hRt n W T hT)
    D.mem_source
  have h0C : (0 : D.φ.model.E 0) ∈ D.φ.model.C := D.V_subset D.zero_mem_V
  have hd0 : degIndex D.φ.model.E D.φ.model.C 0 = 0 := by
    rw [hdeg] at h1
    unfold MPolyfold.chartDegIndex at h1
    rw [D.φ_zero] at h1
    exact h1.symm
  have hint : (0 : D.φ.model.E 0) ∈ interior D.φ.model.C :=
    (degIndex_eq_zero_iff D.φ.model.isPartialQuadrant h0C).1 hd0
  have hVn : D.V ∈ 𝓝 (0 : D.N) := by
    obtain ⟨O', hO', hV⟩ := D.V_relOpen
    have h0O' : (0 : D.N) ∈ O' := (hV ▸ D.zero_mem_V : (0 : D.N) ∈ O' ∩ _).1
    rw [hV]
    exact inter_mem (hO'.mem_nhds h0O')
      (mem_of_superset ((isOpen_interior.preimage continuous_subtype_val).mem_nhds hint)
        (preimage_mono interior_subset))
  have hΩn : Ω ∈ 𝓝 (0 : D.N) := by
    rw [hΩ]; exact inter_mem hVn (hOE.mem_nhds (hΩ ▸ h0 : (0 : D.N) ∈ D.V ∩ OE).2)
  exact e.continuous.continuousAt.preimage_mem_nhds (by rw [e.apply_symm_apply]; exact hΩn)

/-! ### (A3): boundary zeros are regular points -/

/-- **(A3): a zero in general position at an extremum of `t` is a regular point of `t|S_f`**
(the proof of 2021 Theorem 5.3.15, p. 223: "`d(t|S)` has no critical points near `∂S`").  Let
`x` be a zero of `f` in general position, `t` an sc-smooth function with `dt(x)` onto and with
a minimum or a maximum at `x`.  Then `d(t|S_f)(x) ≠ 0`.  *Proof*: in a tame chart centred at
`x`, `T_0O = ker f'(x) + T^R_0O` (general position), and `dt(x)` vanishes on `T^R_0O ⊆ E_0`
(`scDeriv_eq_zero_of_extremum`); so `dt(x)` does not vanish on `ker f'(x)`, which is tangent to
the parametrization.  No condition on the degeneracy index of `x`. -/
theorem StrongBundle.isRegularPointOn_of_extremum (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) {x : X} (hx0 : IsZeroAt P f x)
    (hgp : B.IsGeneralPositionGerm f x) {t : X → ℝ} (ht : PX.IsScSmoothMap realPolyfold t)
    (hsurj : PX.HasSurjDerivAt t x) (hext : (∀ y, t x ≤ t y) ∨ (∀ y, t y ≤ t x)) :
    PX.IsRegularPointOn (solutionSet P f) t x := by
  obtain ⟨n, Ω, p, q, G, u₀, hpar, hUD, hu₀, hpu, -⟩ :=
    StrongBundle.exists_isSmoothParam_solutionSet hbump hf hx0 hgp
  refine ⟨n, Ω, p, q, G, u₀, hpar, hUD, hu₀, hpu, fun h0 => ?_⟩
  obtain ⟨-, c, hc, hxc, hφ0, -⟩ :=
    hf.germTame x (hf.toIsScFredholmSection.mem_smoothSet_of_isZeroAt hx0)
  obtain ⟨n', Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  have hGP := isParamGP_elim0_of_isGeneralPositionGerm hf hx0 hc hxc hφ0 T hT hgp
  have hz : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = c.φ x := by rw [map_zero, hφ0]
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model x hxc
  have h0U : (0 : c.φ.model.E 0) ∈ c.U := mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)
  -- `dt(x) ≠ 0` on `T_0O`
  obtain ⟨φ', hφ', hx', R', hR', z', hz', hs⟩ := hsurj
  obtain ⟨v', hv'⟩ := hs 1
  obtain ⟨w, ⟨w₀, hw₀⟩, hw⟩ := MPolyfold.exists_scDeriv_eq_chart_change c.isChart hφ' hxc hx'
    (c.isRetraction.baseRetraction c.relOpen) c.base_retract R' hR' hz hz'
    (scDeriv R'.U R' z' v')
  have hw1 : scDeriv (F := ScBanach.const ℝ) c.U ((t ∘ c.φ.symm) ∘ r c.R) 0 w = 1 :=
    (hw t ht).trans hv'
  -- `w = u + e`, `u ∈ ker Lin(0)`, `e ∈ E_0`
  have hwr : w ∈ rangeS (scDeriv c.U (r c.R) 0) := ⟨w₀, hw₀⟩
  obtain ⟨u, a, hua, hmin⟩ := hGP.2 ⟨w, hwr⟩
  have hu0 : linAt c.U c.R (c.principal f) 0 u = 0 := by simpa using hua
  have huK : (u : c.φ.model.E 0) ∈ c.linKer f 0 := (c.mem_linKer_iff f 0 _).2 ⟨u.2, hu0⟩
  obtain ⟨v, hv⟩ := StrongBundle.exists_fderivWithin_eq_scDeriv_of_mem_linKer hf hx0 hgp hpar
    hu₀ hpu hc.1 hxc hz huK
  have hvt := hv t ht
  rw [h0, zero_apply] at hvt
  -- `dt(x)` vanishes on `E_0`
  have hτ : IsSc1 (F := ScBanach.const ℝ) c.U ((t ∘ c.φ.symm) ∘ r c.R) :=
    ((ht.real_chart c.isChart).comp_isScSmooth (c.isRetraction.baseRetraction c.relOpen)
      c.base_retract).isSc1
  have hτ0 : ((t ∘ c.φ.symm) ∘ r c.R) (c.φ.model.E.toBase 1 (0 : c.φ.model.E 1)) = t x := by
    rw [map_zero]
    change t (c.φ.symm (r c.R 0)) = t x
    rw [r_eq_self c.isRetraction (c.r_image ▸ h0O), ← hφ0, c.φ.symm_apply_apply hxc]
  have hext' : (∀ u' ∈ c.U, ((t ∘ c.φ.symm) ∘ r c.R) (c.φ.model.E.toBase 1 (0 : c.φ.model.E 1))
        ≤ ((t ∘ c.φ.symm) ∘ r c.R) u') ∨
      (∀ u' ∈ c.U, ((t ∘ c.φ.symm) ∘ r c.R) u' ≤
        ((t ∘ c.φ.symm) ∘ r c.R) (c.φ.model.E.toBase 1 (0 : c.φ.model.E 1))) := by
    rw [hτ0]
    rcases hext with h | h
    · exact Or.inl fun u' _ => h _
    · exact Or.inr fun u' _ => h _
  have h0U1 : (0 : c.φ.model.E 1) ∈ c.φ.model.E.lvlSet c.U 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0U
  have he := scDeriv_eq_zero_of_extremum T hT c.relOpen hτ h0U1 hext'
    (e := w - (u : c.φ.model.E 0)) (by rw [map_zero]; exact hmin)
  have hsplit : w = (u : c.φ.model.E 0) + (w - (u : c.φ.model.E 0)) := by abel
  rw [hsplit, map_add, ← hvt, he, add_zero] at hw1
  exact zero_ne_one hw1

end Param

/-! ### Small tools -/

section Tools

/-- An sc-operator maps smooth points to smooth points. -/
lemma IsScOperator.apply_mem_smooth {E F : ScBanach} {L : E 0 →L[ℝ] F 0} (hL : IsScOperator L)
    {v : E 0} (hv : v ∈ E.smooth) : L v ∈ F.smooth := by
  refine F.mem_smooth_iff.2 fun m => ?_
  obtain ⟨Lm, hLm⟩ := hL m
  obtain ⟨y, hy⟩ := E.mem_smooth_iff.1 hv m
  exact ⟨Lm y, by rw [hLm, hy]⟩

/-- The degeneracy index of a point of the partial quadrant `E` in `E` is `0`. -/
private lemma degIndex_univ_aux (E : ScBanach) (y : E 0) : degIndex E univ y = 0 := by
  let T : ScIso E ((ScBanach.const (Fin 0 → ℝ)).prod E) :=
    { lvl := fun m => (ContinuousLinearEquiv.uniqueProd ℝ (E m) (Fin 0 → ℝ)).symm
      incl_comm := fun m x => Prod.ext (funext fun i => i.elim0) rfl }
  have hT : (univ : Set (E 0)) = T 0 ⁻¹' quadrant 0 E 0 := by ext; simp [quadrant]
  rw [degIndex_eq T hT (mem_univ y), degIndexWith, quadrantDeg]
  simp

/-- The points of `ℝᵐ` have degeneracy index `0`. -/
private lemma degIndex_rn_aux {m : ℕ} (x : Fin m → ℝ) : (rnPolyfold m).degIndex x = 0 :=
  Nat.le_zero.1 (((rnPolyfold m).degIndex_le (isChart_rnChart 0) (mem_univ x)).trans
    (le_of_eq (degIndex_univ_aux _ _)))

end Tools

/-! ### The families `f + Σ μ_j σ_j`: (A1) and (A2) -/

section Family

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y} {m : ℕ} [ParacompactSpace ((Fin m → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))]

open StrongRetr

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))] in
/-- In the product chart `(a, u)`, the derivative of the coordinate `μ_j` is `(δa, δu) ↦ δa_j`. -/
lemma scDeriv_pc0_fst_apply (c : StrongBundleChart PX P)
    (q₀ : pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X)) (h0U : (0 : c.φ.model.E 0) ∈ c.U)
    (j : Fin m) (w : (Fin m → ℝ) × c.φ.model.E 0) :
    scDeriv (F := ScBanach.const ℝ) (pc0 c q₀).U
      (((fun z : (Fin m → ℝ) × X => z.1 j) ∘ (pc0 c q₀).φ.symm) ∘ r (pc0 c q₀).R)
      (0 : (pc0 c q₀).φ.model.E 1) w = w.1 j := by
  have hg : ((rnPolyfold m).prod PX).IsScSmoothMap realPolyfold
      (fun z : (Fin m → ℝ) × X => z.1 j) :=
    (isScSmoothMap_rn_real_of_contDiff
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j).contDiff).comp
      (MPolyfold.isScSmoothMap_fst (rnPolyfold m) PX)
  have h1 : IsSc1 (F := ScBanach.const ℝ) (pc0 c q₀).U
      (((fun z : (Fin m → ℝ) × X => z.1 j) ∘ (pc0 c q₀).φ.symm) ∘ r (pc0 c q₀).R) :=
    ((hg.real_chart (pc0 c q₀).isChart).comp_isScSmooth
      ((pc0 c q₀).isRetraction.baseRetraction (pc0 c q₀).relOpen) (pc0 c q₀).base_retract).isSc1
  have hz0 : (0 : (pc0 c q₀).φ.model.E 1) ∈ (pc0 c q₀).φ.model.E.lvlSet (pc0 c q₀).U 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact ⟨mem_univ _, h0U⟩
  set L : (pc0 c q₀).φ.model.E 0 →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j).comp
      (ContinuousLinearMap.fst ℝ (Fin m → ℝ) (c.φ.model.E 0)) with hL
  have hfun : ((fun z : (Fin m → ℝ) × X => z.1 j) ∘ (pc0 c q₀).φ.symm) ∘ r (pc0 c q₀).R =
      fun w => L w := by
    funext w
    change (w.1 + 0) j = w.1 j
    rw [add_zero]
  have hd : HasFDerivWithinAt
      ((((fun z : (Fin m → ℝ) × X => z.1 j) ∘ (pc0 c q₀).φ.symm) ∘ r (pc0 c q₀).R) ∘
        (pc0 c q₀).φ.model.E.toBase 1) (L.comp ((pc0 c q₀).φ.model.E.toBase 1))
      ((pc0 c q₀).φ.model.E.lvlSet (pc0 c q₀).U 1) 0 := by
    rw [hfun]
    exact (L.comp ((pc0 c q₀).φ.model.E.toBase 1)).hasFDerivWithinAt
  rw [scDeriv_eq_of_hasFDerivWithinAt (F := ScBanach.const ℝ) (pc0 c q₀).relOpen h1 hz0 hd]
  rfl

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))] in
/-- In the product chart `(a, u)`, the derivative of a function of the second variable is its
derivative in the chart `c`. -/
lemma scDeriv_pc0_snd_apply (c : StrongBundleChart PX P)
    (q₀ : pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X)) (h0U : (0 : c.φ.model.E 0) ∈ c.U)
    {t : X → ℝ} (ht : PX.IsScSmoothMap realPolyfold t) (w : (Fin m → ℝ) × c.φ.model.E 0) :
    scDeriv (F := ScBanach.const ℝ) (pc0 c q₀).U
      (((fun z : (Fin m → ℝ) × X => t z.2) ∘ (pc0 c q₀).φ.symm) ∘ r (pc0 c q₀).R)
      (0 : (pc0 c q₀).φ.model.E 1) w =
      scDeriv (F := ScBanach.const ℝ) c.U ((t ∘ c.φ.symm) ∘ r c.R) 0 w.2 := by
  have hg : ((rnPolyfold m).prod PX).IsScSmoothMap realPolyfold
      (fun z : (Fin m → ℝ) × X => t z.2) :=
    ht.comp (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)
  have h1 : IsSc1 (F := ScBanach.const ℝ) (pc0 c q₀).U
      (((fun z : (Fin m → ℝ) × X => t z.2) ∘ (pc0 c q₀).φ.symm) ∘ r (pc0 c q₀).R) :=
    ((hg.real_chart (pc0 c q₀).isChart).comp_isScSmooth
      ((pc0 c q₀).isRetraction.baseRetraction (pc0 c q₀).relOpen) (pc0 c q₀).base_retract).isSc1
  have hτ : IsSc1 (F := ScBanach.const ℝ) c.U ((t ∘ c.φ.symm) ∘ r c.R) :=
    ((ht.real_chart c.isChart).comp_isScSmooth (c.isRetraction.baseRetraction c.relOpen)
      c.base_retract).isSc1
  have hz0 : (0 : (pc0 c q₀).φ.model.E 1) ∈ (pc0 c q₀).φ.model.E.lvlSet (pc0 c q₀).U 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact ⟨mem_univ _, h0U⟩
  have h0U1 : (0 : c.φ.model.E 1) ∈ c.φ.model.E.lvlSet c.U 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0U
  set Lc : c.φ.model.E 0 →L[ℝ] ℝ :=
    scDeriv (F := ScBanach.const ℝ) c.U ((t ∘ c.φ.symm) ∘ r c.R) 0 with hLc
  set snd₁ : (pc0 c q₀).φ.model.E 1 →L[ℝ] c.φ.model.E 1 :=
    ContinuousLinearMap.snd ℝ (Fin m → ℝ) (c.φ.model.E 1) with hsnd₁
  set L : (pc0 c q₀).φ.model.E 0 →L[ℝ] ℝ :=
    Lc.comp (ContinuousLinearMap.snd ℝ (Fin m → ℝ) (c.φ.model.E 0)) with hL
  have hmaps : MapsTo snd₁ ((pc0 c q₀).φ.model.E.lvlSet (pc0 c q₀).U 1)
      (c.φ.model.E.lvlSet c.U 1) := fun y hy => by
    have h2 : (pc0 c q₀).φ.model.E.toBase 1 y ∈ (univ : Set (Fin m → ℝ)) ×ˢ c.U := hy
    have h3 := ScBanach.prod_toBase (rnSc m) c.φ.model.E 1 y
    change c.φ.model.E.toBase 1 y.2 ∈ c.U
    have h4 := h2.2
    rw [show ((pc0 c q₀).φ.model.E.toBase 1 y).2 = c.φ.model.E.toBase 1 y.2 from
      congrArg Prod.snd h3] at h4
    exact h4
  have hd0 : HasFDerivWithinAt (((t ∘ c.φ.symm) ∘ r c.R) ∘ c.φ.model.E.toBase 1)
      (Lc.comp (c.φ.model.E.toBase 1)) (c.φ.model.E.lvlSet c.U 1)
      (snd₁ (0 : (pc0 c q₀).φ.model.E 1)) := hτ.isSc1With_scDeriv.hasFDerivWithinAt 0 h0U1
  have key := hd0.comp (0 : (pc0 c q₀).φ.model.E 1) snd₁.hasFDerivWithinAt hmaps
  have hd : HasFDerivWithinAt
      ((((fun z : (Fin m → ℝ) × X => t z.2) ∘ (pc0 c q₀).φ.symm) ∘ r (pc0 c q₀).R) ∘
        (pc0 c q₀).φ.model.E.toBase 1) (L.comp ((pc0 c q₀).φ.model.E.toBase 1))
      ((pc0 c q₀).φ.model.E.lvlSet (pc0 c q₀).U 1) 0 := by
    have hLeq : L.comp ((pc0 c q₀).φ.model.E.toBase 1) =
        (Lc.comp (c.φ.model.E.toBase 1)).comp snd₁ := by
      refine ContinuousLinearMap.ext fun y => ?_
      change Lc ((pc0 c q₀).φ.model.E.toBase 1 y).2 = Lc (c.φ.model.E.toBase 1 y.2)
      rw [show ((pc0 c q₀).φ.model.E.toBase 1 y).2 = c.φ.model.E.toBase 1 y.2 from
        congrArg Prod.snd (ScBanach.prod_toBase (rnSc m) c.φ.model.E 1 y)]
    rw [hLeq]
    refine key.congr (fun y _ => ?_) ?_
    · change t (c.φ.symm (r c.R ((pc0 c q₀).φ.model.E.toBase 1 y).2)) =
        t (c.φ.symm (r c.R (c.φ.model.E.toBase 1 y.2)))
      rw [show ((pc0 c q₀).φ.model.E.toBase 1 y).2 = c.φ.model.E.toBase 1 y.2 from
        congrArg Prod.snd (ScBanach.prod_toBase (rnSc m) c.φ.model.E 1 y)]
    · change t (c.φ.symm (r c.R ((pc0 c q₀).φ.model.E.toBase 1 0).2)) =
        t (c.φ.symm (r c.R (c.φ.model.E.toBase 1 (0 : (pc0 c q₀).φ.model.E 1).2)))
      rw [show ((pc0 c q₀).φ.model.E.toBase 1 0).2 =
          c.φ.model.E.toBase 1 (0 : (pc0 c q₀).φ.model.E 1).2 from
        congrArg Prod.snd (ScBanach.prod_toBase (rnSc m) c.φ.model.E 1 0)]
  rw [scDeriv_eq_of_hasFDerivWithinAt (F := ScBanach.const ℝ) (pc0 c q₀).relOpen h1 hz0 hd]
  rfl

/-- **The parametrization of the solution set of a family, with its tangent vectors.**  Let
`y` be a zero of `f` in general position with `d_X(y) = 0`, and `σ₁, …, σ_m` sc⁺-sections.  The
solution set of `F(μ, y) = f(y) + Σ μ_j σ_j(y)` has a smooth parametrization `p` by an open
subset of some `ℝⁿ` with `p(v₀) = (0, y)`, and in the product chart of every tame chart `c`
centred at `y` every kernel vector `w ∈ ker F'(0, y)` is `d(g ∘ p)(v₀) v = D(g ∘ χ⁻¹ ∘ r)(0) w`
for some `v`, for all sc-smooth `g` on `ℝᵐ × X`. -/
theorem StrongBundle.exists_isSmoothParam_famZero (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) {σ : Fin m → X → Y}
    (hσ : ∀ j, B.IsScPlusSection (σ j)) {y : X} (hy0 : IsZeroAt P f y)
    (hgp : B.IsGeneralPositionGerm f y) (hdeg : PX.degIndex y = 0) :
    ∃ (n : ℕ) (Ω : Set (Fin n → ℝ)) (p : (Fin n → ℝ) → (Fin m → ℝ) × X)
      (q : (Fin m → ℝ) × X → Fin n → ℝ) (G : Set ((Fin m → ℝ) × X)) (v₀ : Fin n → ℝ),
      ((rnPolyfold m).prod PX).IsSmoothParam
        (famZero f hf.isScSmooth.1 σ fun j => (hσ j).1) Ω p q G ∧ IsOpen Ω ∧ v₀ ∈ Ω ∧
      p v₀ = (0, y) ∧
      ∀ (c : StrongBundleChart PX P), B.IsTameChart c → y ∈ c.φ.source → c.φ y = 0 →
        ∀ (q₀ : pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X)),
        ∀ w ∈ (pc0 c q₀).linKer (paramSection f hf.isScSmooth.1 σ fun j => (hσ j).1) 0,
          ∃ v : Fin n → ℝ, ∀ g : (Fin m → ℝ) × X → ℝ,
            ((rnPolyfold m).prod PX).IsScSmoothMap realPolyfold g →
            fderiv ℝ (g ∘ p) v₀ v =
              scDeriv (F := ScBanach.const ℝ) (pc0 c q₀).U
                ((g ∘ (pc0 c q₀).φ.symm) ∘ r (pc0 c q₀).R) 0 w := by
  have hFt := theorem_3_1_21_tame hf hσ
  have hz0 : IsZeroAt (pullbackProj P Prod.snd)
      (paramSection f hf.isScSmooth.1 σ fun j => (hσ j).1) (0, y) :=
    isZeroAt_paramSection_zero hf.isScSmooth.1 (fun j => (hσ j).1) hy0
  have hgpF := isGeneralPositionGerm_paramSection_of_isGeneralPositionGerm hf hσ hy0 hgp
  have hdegZ : ((rnPolyfold m).prod PX).degIndex ((0 : Fin m → ℝ), y) = 0 :=
    Nat.le_zero.1 ((MPolyfold.degIndex_prod_le (rnPolyfold m) PX 0 y).trans
      (by rw [degIndex_rn_aux, hdeg]))
  obtain ⟨n, Ω, p, q, G, u₀, hpar, -, hu₀, hpu, hnh⟩ :=
    StrongBundle.exists_isSmoothParam_solutionSet (MPolyfold.admitsBumpFunctions_prod_rn hbump)
      hFt hz0 hgpF
  obtain ⟨Ω', G', hpar', hΩ'o, hu₀', -⟩ := hpar.exists_isOpen_of_mem_nhds (hnh hdegZ)
  have hsol : solutionSet (pullbackProj P Prod.snd)
      (paramSection f hf.isScSmooth.1 σ fun j => (hσ j).1) =
      famZero f hf.isScSmooth.1 σ fun j => (hσ j).1 := by
    ext z
    exact isZeroAt_paramSection_iff z
  have hparF : ((rnPolyfold m).prod PX).IsSmoothParam
      (famZero f hf.isScSmooth.1 σ fun j => (hσ j).1) Ω' p q G' := by
    rw [← hsol]; exact hpar'
  refine ⟨n, Ω', p, q, G', u₀, hparF, hΩ'o, hu₀', hpu, fun c hc hyc hφ0 q₀ w hw => ?_⟩
  have hχ : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsChart (pc0 c q₀) :=
    (PullbackChartData.ofProd c 0).isChart_toChart B _ hc.1 q₀
  have hyV' : ((0 : Fin m → ℝ), y) ∈ (pc0 c q₀).φ.source := ⟨mem_univ _, hyc⟩
  have hz' : (pc0 c q₀).φ.model.E.toBase 1 (0 : (pc0 c q₀).φ.model.E 1) =
      (pc0 c q₀).φ (0, y) := by
    rw [map_zero, ofProd_apply_eq_zero c 0 q₀ hφ0]
  obtain ⟨v, hv⟩ := StrongBundle.exists_fderivWithin_eq_scDeriv_of_mem_linKer hFt hz0 hgpF hpar'
    hu₀' hpu hχ hyV' hz' hw
  exact ⟨v, fun g hg => by rw [← fderivWithin_of_isOpen hΩ'o hu₀']; exact hv g hg⟩

/-- **(A1): `μ` is a submersion on the solution set of the family** (2021 Theorem 3.6.8 for
`F(μ, y) = f(y) + Σ μ_j σ_j(y)`): at a zero `y` of `f` in general position with `d_X(y) = 0`,
the solution set of `F` has a smooth parametrization by an open set around `(0, y)` on which
the projection `μ` to `ℝᵐ` is a submersion at `(0, y)`.  *Proof*: `f'(y)` is onto, so for every
`δμ` there is `u` with `f'(y) u + Σ δμ_j σ_j(y) = 0`, i.e. `(δμ, u) ∈ ker F'(0, y)`. -/
theorem StrongBundle.hasFamilyParam (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) {σ : Fin m → X → Y}
    (hσ : ∀ j, B.IsScPlusSection (σ j)) {y : X} (hy0 : IsZeroAt P f y)
    (hgp : B.IsGeneralPositionGerm f y) (hdeg : PX.degIndex y = 0) :
    HasFamilyParam PX (famZero f hf.isScSmooth.1 σ fun j => (hσ j).1) y := by
  classical
  obtain ⟨n, Ω, p, q, G, v₀, hpar, hΩ, hv₀, hpv₀, hker⟩ :=
    StrongBundle.exists_isSmoothParam_famZero hbump hf hσ hy0 hgp hdeg
  refine ⟨n, Ω, p, q, G, v₀, hpar, hΩ, hv₀, hpv₀, fun δ => ?_⟩
  obtain ⟨-, c, hc, hyc, hφ0, -⟩ :=
    hf.germTame y (hf.toIsScFredholmSection.mem_smoothSet_of_isZeroAt hy0)
  obtain ⟨n', Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  have hGP := isParamGP_elim0_of_isGeneralPositionGerm hf hy0 hc hyc hφ0 T hT hgp
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model y hyc
  have h0r : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := c.r_image ▸ h0O
  have h0U : (0 : c.φ.model.E 0) ∈ c.U := mem_U_of_mem_O c.isRetraction h0r
  set q₀ := paramSection f hf.isScSmooth.1 σ (fun j => (hσ j).1) (0, y) with hq₀
  have hK : ((0 : c.φ.model.E 0), -∑ j, δ j • c.principal (σ j) 0) ∈ c.K := by
    refine (mem_rangeS_ρCLM_iff c.isRetraction h0r h0U).1 ?_
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
    exact (mem_rangeS_ρCLM_iff c.isRetraction h0r h0U).2 (c.principal_mem_K (hσ j).1 h0O)
  obtain ⟨u, a, hua⟩ := hGP.1 _ hK
  have hua' : linAt c.U c.R (c.principal f) 0 u + ∑ j, δ j • c.principal (σ j) 0 = 0 := by
    have h1 : linAt c.U c.R (c.principal f) 0 u = -∑ j, δ j • c.principal (σ j) 0 := by
      simpa using hua
    rw [h1]; exact neg_add_cancel _
  have hk : ((δ, (u : c.φ.model.E 0)) : (Fin m → ℝ) × c.φ.model.E 0) ∈
      rangeS (scDeriv (pc0 c q₀).U (r (pc0 c q₀).R) 0) := ofProd_mem_rangeS c q₀ h0U u.2
  have hkK : ((δ, (u : c.φ.model.E 0)) : (Fin m → ℝ) × c.φ.model.E 0) ∈
      (pc0 c q₀).linKer (paramSection f hf.isScSmooth.1 σ fun j => (hσ j).1) 0 := by
    refine ((pc0 c q₀).mem_linKer_iff _ 0 _).2 ⟨hk, ?_⟩
    rw [linAt_paramSection_zero hf.toIsScFredholmSection hσ hc.1 h0O q₀ hk]
    exact hua'
  obtain ⟨v, hv⟩ := hker c hc hyc hφ0 q₀ _ hkK
  refine ⟨v, ?_⟩
  have hμ : ∀ ℓ : (Fin m → ℝ) →L[ℝ] ℝ,
      ((rnPolyfold m).prod PX).IsScSmoothMap realPolyfold fun z => ℓ (Prod.fst z) := fun ℓ =>
    (isScSmoothMap_rn_real_of_contDiff ℓ.contDiff).comp
      (MPolyfold.isScSmoothMap_fst (rnPolyfold m) PX)
  have hd : DifferentiableAt ℝ (fun v => (p v).1) v₀ :=
    ((hpar.contDiffOn_comp (ψ := Prod.fst) hμ).contDiffAt (hΩ.mem_nhds hv₀)).differentiableAt
      (by simp)
  funext j
  have h1 : fderiv ℝ ((fun z : (Fin m → ℝ) × X => z.1 j) ∘ p) v₀ =
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j).comp
        (fderiv ℝ (fun v => (p v).1) v₀) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j).hasFDerivAt.comp v₀
      hd.hasFDerivAt).fderiv
  have h2 := hv (fun z : (Fin m → ℝ) × X => z.1 j)
    (hμ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j))
  rw [scDeriv_pc0_fst_apply c q₀ h0U j, h1] at h2
  exact h2

end Family

/-! ### (A2): a section making `(0, x)` a regular point of `t` on the family -/

section Regular

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y} [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]

open StrongRetr

/-- **(A2): a small sc⁺-section `σ` for which `(0, x)` is not a critical point of `t` on the
solution set of `f + μσ`** (the proof of 2021 Theorem 5.3.15, p. 224, with Lemmas 5.3.16 and
5.3.3).  Let `x` be a zero of `f` in general position with `d_X(x) = 0` and `dt(x)` onto.  For
every open `W ∋ x` and `η > 0` there is an sc⁺-section `σ` with `supp σ ⊆ W`, `N(σ) ≤ η`, such
that the solution set of `(μ, y) ↦ f(y) + μσ(y)` has a smooth parametrization by an open set
around `(0, x)` with `d(t ∘ pr₂) ≠ 0` there.  *Proof*: in a tame chart centred at `x` take a
smooth `w₁ ∈ T_0O` with `dt(x) w₁ ≠ 0` (smooth vectors are dense, `Dr(0)` is an sc-operator);
`k = f'(x) w₁` is a smooth point of the fibre, Lemma 5.3.3 gives a section through it, and
`(−1/θ, w₁)` is a kernel vector of the family with the rescaled section `σ = θ s`. -/
theorem StrongBundle.exists_hasRegularFamilyParam (hbump : PX.AdmitsBumpFunctions)
    {N : B.One → ℝ} (hN : B.IsAuxNorm N) (hf : B.IsScFredholmSectionTame f) {x : X}
    (hx0 : IsZeroAt P f x) (hgp : B.IsGeneralPositionGerm f x) (hdeg : PX.degIndex x = 0)
    {t : X → ℝ} (ht : PX.IsScSmoothMap realPolyfold t) (hsurj : PX.HasSurjDerivAt t x)
    {W : Set X} (hW : IsOpen W) (hxW : x ∈ W) {η : ℝ} (hη : 0 < η) :
    ∃ (σ : X → Y) (hσ : B.IsScPlusSection σ), sectionSupport P σ ⊆ W ∧
      (∀ x', B.AuxLe N (σ x') η) ∧
      HasRegularFamilyParam PX
        (famZero f hf.isScSmooth.1 (fun _ : Fin 1 => σ) fun _ => hσ.1) t x := by
  classical
  have hxs : x ∈ PX.smoothSet := hf.toIsScFredholmSection.mem_smoothSet_of_isZeroAt hx0
  obtain ⟨-, c, hc, hxc, hφ0, -⟩ := hf.germTame x hxs
  have hz : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = c.φ x := by rw [map_zero, hφ0]
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model x hxc
  have h0r : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := c.r_image ▸ h0O
  have h0U : (0 : c.φ.model.E 0) ∈ c.U := mem_U_of_mem_O c.isRetraction h0r
  have h0U1 : (0 : c.φ.model.E 1) ∈ c.φ.model.E.lvlSet c.U 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0U
  have hzs : (0 : c.φ.model.E 1) ∈ c.φ.model.E.smoothLvl 1 := by
    change c.φ.model.E.toBase 1 0 ∈ c.φ.model.E.smooth
    rw [map_zero]; exact c.φ.model.E.smooth.zero_mem
  set Lτ : c.φ.model.E 0 →L[ℝ] ℝ :=
    scDeriv (F := ScBanach.const ℝ) c.U ((t ∘ c.φ.symm) ∘ r c.R) 0 with hLτ
  set Dr : c.φ.model.E 0 →L[ℝ] c.φ.model.E 0 := scDeriv c.U (r c.R) 0 with hDr
  -- `dt(x) ≠ 0` on `T_0O`
  obtain ⟨φ', hφ', hx', R', hR', z', hz', hs⟩ := hsurj
  obtain ⟨v', hv'⟩ := hs 1
  obtain ⟨w, ⟨w₀, hw₀⟩, hw⟩ := MPolyfold.exists_scDeriv_eq_chart_change c.isChart hφ' hxc hx'
    (c.isRetraction.baseRetraction c.relOpen) c.base_retract R' hR' hz hz'
    (scDeriv R'.U R' z' v')
  have hw1 : Lτ w = 1 := (hw t ht).trans hv'
  -- a smooth tangent vector with `dt(x) w₁ ≠ 0`
  have hex : ∃ v₁ ∈ c.φ.model.E.smooth, Lτ (Dr v₁) ≠ 0 := by
    by_contra hne
    have hall : ∀ v ∈ c.φ.model.E.smooth, Lτ (Dr v) = 0 := fun v hv =>
      by_contra fun h => hne ⟨v, hv, h⟩
    have hd : Dense (c.φ.model.E.smooth : Set (c.φ.model.E 0)) := c.φ.model.E.dense_smooth 0
    have hcl : IsClosed {v : c.φ.model.E 0 | (Lτ.comp Dr) v = 0} :=
      isClosed_eq (Lτ.comp Dr).continuous continuous_const
    have h1 : Lτ (Dr w₀) = 0 := hcl.closure_subset_iff.2 (fun v hv => hall v hv) (hd w₀)
    have h2 : Dr w₀ = w := hw₀
    rw [h2, hw1] at h1
    exact one_ne_zero h1
  obtain ⟨v₁, hv₁s, hv₁⟩ := hex
  set w₁ : c.φ.model.E 0 := Dr v₁ with hw₁
  have hw₁r : w₁ ∈ rangeS (scDeriv c.U (r c.R) 0) := ⟨v₁, rfl⟩
  have hDrop : IsScOperator Dr :=
    (c.isRetraction.baseRetraction c.relOpen).isScOperator_scDeriv h0U1 hzs
  have hw₁s : w₁ ∈ c.φ.model.E.smooth := hDrop.apply_mem_smooth hv₁s
  have hfr : IsSc1 c.U (c.principal f ∘ r c.R) := hf.isScSmooth.isSc1_principal_comp_r hc.1
  have hLop : IsScOperator (scDeriv c.U (c.principal f ∘ r c.R) 0) :=
    hfr.isSc1With_scDeriv.scOperator_deriv h0U1 hzs
  set k : c.F 0 := linAt c.U c.R (c.principal f) 0 ⟨w₁, hw₁r⟩ with hk
  have hks : k ∈ c.F.smooth := hLop.apply_mem_smooth hw₁s
  have hzO : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ r c.R '' c.U := by
    rw [map_zero]; exact h0r
  have hkρ := rho_scDeriv_comp_r c.relOpen c.isRetraction hfr
    (fun x hx => c.principal_mem_K hf.isScSmooth.1 (c.r_image ▸ hx)) hzO
    (by rw [hz]; exact (c.isZeroAt_iff hf.isScSmooth.1 hxc).1 hx0) w₁
  have hkK : ((0 : c.φ.model.E 0), k) ∈ c.K := by
    have h1 := (mem_rangeS_ρCLM_iff c.isRetraction hzO (mem_U_of_mem_O c.isRetraction hzO)).1
      ⟨_, hkρ⟩
    rw [map_zero] at h1
    exact h1
  -- the section through `k`
  set e : Y := c.toPartialEquiv.symm (0, k) with he
  have hφsymm0 : c.φ.symm 0 = x := by rw [← hφ0]; exact c.φ.symm_apply_apply hxc
  have hPe : P e = x := by
    change P (c.toPartialEquiv.symm (0, k)) = x
    rw [c.proj_symm hkK]; exact hφsymm0
  have hesm : e ∈ B.toMPolyfold0.smoothSet :=
    mem_smoothSet_toMPolyfold0_of_chart hc.1 hkK c.φ.model.E.smooth.zero_mem hks
  obtain ⟨he1, s, hs, hsx, hssupp, hsN⟩ := lemma_5_3_3 hbump hN hxs hesm hPe one_pos hW hxW
  set M : ℝ := N (B.oneMk e he1) + 1 with hM
  have hMpos : 0 < M := by
    have := hN.nonneg (B.oneMk e he1)
    simp only [hM]; linarith
  set θ : ℝ := η / M with hθ
  have hθpos : 0 < θ := div_pos hη hMpos
  set σ : X → Y := sectionSmul P (fun _ => θ) s with hσdef
  have hσ : B.IsScPlusSection σ := hs.smul_left (isScSmoothMap_real_const _)
  refine ⟨σ, hσ, (sectionSupport_sectionSmul_const_subset hs.1 _).trans hssupp,
    fun x' => ⟨hσ.mem_oneSet x', ?_⟩, ?_⟩
  · rw [hN.oneMk_sectionSmul_const hs θ x' (hσ.mem_oneSet x'), abs_of_pos hθpos]
    calc θ * N (B.oneMk (s x') (hs.mem_oneSet x')) ≤ θ * M :=
          mul_le_mul_of_nonneg_left (hsN x' (hs.mem_oneSet x')).le hθpos.le
      _ = η := div_mul_cancel₀ η hMpos.ne'
  · obtain ⟨n, Ω, p, q, G, v₀, hpar, hΩ, hv₀, hpv₀, hker⟩ :=
      StrongBundle.exists_isSmoothParam_famZero (m := 1) hbump hf (σ := fun _ => σ)
        (fun _ => hσ) hx0 hgp hdeg
    refine ⟨n, Ω, p, q, G, v₀, hpar, hΩ, hv₀, hpv₀, fun h0 => ?_⟩
    set q₀ := paramSection f hf.isScSmooth.1 (fun _ : Fin 1 => σ) (fun _ => hσ.1) (0, x)
      with hq₀
    have hprin : c.principal σ 0 = θ • k := by
      change c.principal (sectionSmul P (fun _ => θ) s) 0 = _
      rw [principal_sectionSmul_const c hs.1 _ h0O]
      unfold StrongBundleChart.principal
      rw [hφsymm0, hsx]
      change θ • (c (c.toPartialEquiv.symm (0, k))).2 = _
      rw [c.apply_symm hkK]
    have hk' : (((fun _ : Fin 1 => -θ⁻¹), w₁) : (Fin 1 → ℝ) × c.φ.model.E 0) ∈
        rangeS (scDeriv (pc0 c q₀).U (r (pc0 c q₀).R) 0) := ofProd_mem_rangeS c q₀ h0U hw₁r
    have hkK' : (((fun _ : Fin 1 => -θ⁻¹), w₁) : (Fin 1 → ℝ) × c.φ.model.E 0) ∈
        (pc0 c q₀).linKer
          (paramSection f hf.isScSmooth.1 (fun _ : Fin 1 => σ) fun _ => hσ.1) 0 := by
      refine ((pc0 c q₀).mem_linKer_iff _ 0 _).2 ⟨hk', ?_⟩
      rw [linAt_paramSection_zero hf.toIsScFredholmSection (fun _ : Fin 1 => hσ) hc.1 h0O q₀
        hk']
      rw [Fin.sum_univ_one, hprin, smul_smul, neg_mul, inv_mul_cancel₀ hθpos.ne', neg_one_smul]
      exact add_neg_cancel k
    obtain ⟨v, hv⟩ := hker c hc hxc hφ0 q₀ _ hkK'
    have h2 := hv (fun z : (Fin 1 → ℝ) × X => t z.2)
      (ht.comp (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX))
    rw [scDeriv_pc0_snd_apply c q₀ h0U ht] at h2
    have h3 : fderiv ℝ ((fun z : (Fin 1 → ℝ) × X => t z.2) ∘ p) v₀ = 0 := h0
    rw [h3, zero_apply] at h2
    exact hv₁ h2.symm

end Regular

/-! ### The three local statements together -/

section Together

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- **The local data (A1)–(A3) hold** for every sc-Fredholm section `g` (tame germ data) in
general position at all its zeros, when `X` admits sc-smooth bump functions, `t : X → [0, 1]` is
sc-smooth with `dt(x)` onto at the smooth points (2021 Definition 5.3.13 (3)), and
`t(∂X) ⊆ {0, 1}`.  The boundary zeros may be corner points of any index. -/
theorem StrongBundle.hasMorseLocalData (hbump : PX.AdmitsBumpFunctions) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N) {t : X → ℝ} (ht : PX.IsScSmoothMap realPolyfold t)
    (hsurj : ∀ x ∈ PX.smoothSet, PX.HasSurjDerivAt t x) (hIcc : ∀ x, t x ∈ Icc (0 : ℝ) 1)
    (hbd : PX.boundary ⊆ t ⁻¹' {0} ∪ t ⁻¹' {1}) {g : X → Y}
    (hg : B.IsScFredholmSectionTame g)
    (hgp : ∀ x, IsZeroAt P g x → B.IsGeneralPositionGerm g x) :
    B.HasMorseLocalData N t g hg := by
  have hsm : ∀ x, IsZeroAt P g x → x ∈ PX.smoothSet := fun x hx =>
    hg.toIsScFredholmSection.mem_smoothSet_of_isZeroAt hx
  have hdeg : ∀ x, x ∉ PX.boundary → PX.degIndex x = 0 := fun x hx =>
    Nat.lt_one_iff.1 (not_le.1 (show ¬ 1 ≤ PX.degIndex x from hx))
  refine ⟨fun k σ hσ y hy0 hyb => ?_, fun x hx0 hxb W hW hxW η hη => ?_, fun x hxb hx0 => ?_⟩
  · have := MPolyfold.paracompactSpace_prod (rnPolyfold k) PX
    have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin k → ℝ) × X → X))
      ((rnPolyfold k).prod PX) B
    exact StrongBundle.hasFamilyParam hbump hg hσ hy0 (hgp y hy0) (hdeg y hyb)
  · have := MPolyfold.paracompactSpace_prod (rnPolyfold 1) PX
    have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin 1 → ℝ) × X → X))
      ((rnPolyfold 1).prod PX) B
    exact StrongBundle.exists_hasRegularFamilyParam hbump hN hg hx0 (hgp x hx0) (hdeg x hxb) ht
      (hsurj x (hsm x hx0)) hW hxW hη
  · refine StrongBundle.isRegularPointOn_of_extremum hbump hg hx0 (hgp x hx0) ht
      (hsurj x (hsm x hx0)) ?_
    rcases hbd hxb with h | h
    · have h0 : t x = 0 := h
      exact Or.inl fun y => h0 ▸ (hIcc y).1
    · have h1 : t x = 1 := h
      exact Or.inr fun y => h1 ▸ (hIcc y).2

end Together

end Polyfold
