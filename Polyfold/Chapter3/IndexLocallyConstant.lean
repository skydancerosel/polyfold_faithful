import Polyfold.Chapter3.LinearizationChartsSc
import Polyfold.Chapter3.BasicGermLinearizationLevel
import Polyfold.Chapter5.GeneralPosition

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6 and §6
(Theorem 3.54 and the proof of Proposition 6.2, p. 201): **the Fredholm index of the linearization
is locally constant along the zero set of an sc-Fredholm section**, without good position or
surjectivity at the base point (round-trip item V3.98 (b)).  Findings, Chapter 3, items 240–244.

# The index along the zero set

## The text, paraphrased

(Theorem 3.54, proof, and Proposition 6.2) Along the solution set of an sc-Fredholm section the
Fredholm index of `f'(y) : T_yX → Y_y` is locally constant; the text's device for Proposition 6.2
adds finitely many sc⁺-sections with parameters `λ`, applies the implicit function theorem to the
extended section `F(λ, y) = f(y) + Σ λᵢ sᵢ(y)`, and reads off the index from the tangent spaces
of its solution manifold.  (Round-trip item V3.98 (b)) Every zero `x₀` of an sc-Fredholm section
has an open neighbourhood `V` such that `ind(f, y) = ind(f, x₀)` for every zero `y ∈ V`, the index
being the sc-Fredholm index of `f'(y)` in every strong bundle chart around `y`.

## What is formalized

* `Polyfold.StrongBundle.IsLinOfIndex B f y i`: "`f'(y)` is Fredholm of index `i`" in every
  strong bundle chart around `y` (the form `IsSurjLinOfIndex` without the surjectivity; the
  `IndexAt` of the round-trip statement V3.98 on level `0`).
  `StrongBundle.isLinOfIndex_of_conjugationData_wholeChart` (the index is `dim Pn − dim Q` for every germ
  datum at `y`, by `linAt_index_of_conjugationData_wholeChart`), `StrongBundle.IsSurjLinOfIndex.isLinOfIndex`.
* `Polyfold.linIndex_snd`, `Polyfold.fredholmIndex_eq_of_param` (linear algebra): for
  `M(a, u) = L u + E a` on `ℝᵏ × T` with `L` and `M` Fredholm, `ind M = ind L + k`.
* `Polyfold.StrongBundle.isLinOfIndex_of_paramSection_isLinOfIndex_wholeChart`: if the parametrized section
  `F(λ, y) = f(y) + Σ λᵢ sᵢ(y)` of Theorem 3.18 has index `d` at `(0, y)`, then `f` has index
  `d − k` at the zero `y` — the linearization of `F` at `(0, y)` in the product chart is
  `(δa, δu) ↦ Lin_f(0) δu + Σ δaᵢ ŝᵢ(0)` (`linAt_paramSection_zero_wholeChart`).
* **The index is locally constant along the zero set** (round-trip item V3.98 (b), with the
  hypotheses of Chapter 5): `Polyfold.index_locally_constant_of_admitsBumpFunctions_wholeChart` (level `0`,
  `IsLinOfIndex` at every zero near `x₀` with one index `i`) and
  `Polyfold.theorem_3_54_index_locally_constant_general_wholeChart` (the sc form: at every zero `y` near
  `x₀`, in every strong bundle chart around `y`, `Lin(z) : T_zO → K_z` is sc-Fredholm of index `i`
  on every level).  Hypotheses: `X` admits sc-smooth bump functions (Definition 5.9) and `f` is an
  sc-Fredholm section with tame germ data (Definition 3.51); no good position, no surjectivity.
  The auxiliary norm the construction uses exists by Proposition 5.3 (`proposition_5_3_exists`).

## What the text leaves implicit, and the choices made (the findings)

* **The proof is the text's device for Proposition 6.2, with the ingredients of Chapter 5.**
  At the zero `x₀`, finitely many sc⁺-sections `s₁, …, s_k` put the parametrized section `F` into
  general position at `(0, x₀)` (`exists_sections_isParamGP`,
  `isGeneralPositionGerm_paramSection_of_isParamGP`: the spanning sections of Lemma 5.11 for the
  surjectivity, and the tilting sections for the kernel condition at the corner — the two points
  of Findings items 105 (a) and 107 which the text's proof of Proposition 6.2 does not address);
  general position gives good position in a tame chart (Lemma 5.26), so Theorem 3.54 (1) and the
  dimension count (`theorem_3_54_index_locally_constant_wholeChart`) make the index of `F` constant along
  its solution set near `(0, x₀)`; at `(0, y)` with `f(y) = 0` the index of `F` is `k + ind f'(y)`.
* **The neighbourhood does not depend on the sections**: the `Λ₀`-dependence of Findings item
  106 concerns the surjectivity of `f'(y)` (which needs all smooth vectors in the range); for the
  index one family of sections at `x₀` suffices.  Tameness enters through the kernel condition of
  good position at the corner (`IsScFredholmSectionTameWholeChart`, `IsTameChart` with a presentation of the
  partial quadrant); bump functions through Lemma 5.11.
* **Without bump functions the question is open** (see the Findings): in the chart at `x₀` with
  the filler `g`, at a zero `z` near `0`, `Dg(z)` is Fredholm of index `n − N` (push-forward and
  Proposition 3.10 at `ψ(z)`), `Lin(z)` is Fredholm (the germ at `y`), and the upper triangular
  matrix `Dg(z) = [[Lin(z), B], [0, C(z)]]` gives `ind Dg(z) = ind Lin(z) + ind C(z)` with
  `C(z) = (1 − ρ(z))Dg(z)|_{ker Dr(z)} : ker Dr(z) → ker ρ(z)` Fredholm; the claim is
  `ind C(z) = 0`, which condition (3) of Definition 3.4 gives at `z = 0` only, and `z ↦ C(z)` is
  not norm continuous.
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

universe u v

/-! ### Linear algebra: the index of `(a, u) ↦ L u + E a` on `ℝᵏ × T` -/

section LinearAlgebra

variable {T K : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K] {k : ℕ}

omit [CompleteSpace T] in
/-- The projection `pr₂ : ℝᵏ × T → T` has finite index `k` (kernel `ℝᵏ × 0`, onto). -/
theorem linIndex_snd :
    HasFiniteIndex (LinearMap.snd ℝ (Fin k → ℝ) T) ∧
      linIndex (LinearMap.snd ℝ (Fin k → ℝ) T) = k := by
  have hker : LinearMap.ker (LinearMap.snd ℝ (Fin k → ℝ) T) =
      LinearMap.range (LinearMap.inl ℝ (Fin k → ℝ) T) := LinearMap.ker_snd ℝ (Fin k → ℝ) T
  have hrange : LinearMap.range (LinearMap.snd ℝ (Fin k → ℝ) T) = ⊤ := Submodule.range_snd
  have hfin : FiniteDimensional ℝ (LinearMap.ker (LinearMap.snd ℝ (Fin k → ℝ) T)) := by
    rw [hker]; exact LinearMap.finiteDimensional_range _
  have hsub : Subsingleton (T ⧸ LinearMap.range (LinearMap.snd ℝ (Fin k → ℝ) T)) := by
    rw [hrange]
    refine ⟨fun a b => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    exact (Submodule.Quotient.eq _).2 Submodule.mem_top
  have h0 : finrank ℝ (T ⧸ LinearMap.range (LinearMap.snd ℝ (Fin k → ℝ) T)) = 0 :=
    finrank_zero_of_subsingleton
  refine ⟨⟨hfin, inferInstance⟩, ?_⟩
  unfold linIndex
  rw [h0, hker, LinearMap.finrank_range_of_inj LinearMap.inl_injective, Module.finrank_fin_fun]
  simp

/-- **The index of `M(a, u) = L u + E a`** on `ℝᵏ × T`: if `L : T → K` and `M` are Fredholm, then
`ind M = ind L + k` (`E ∘ pr₁` has finite rank, so `ind M = ind (L ∘ pr₂) = ind L + ind pr₂`). -/
theorem fredholmIndex_eq_of_param {L : T →L[ℝ] K} (hL : L.IsFredholm) (E : (Fin k → ℝ) →L[ℝ] K)
    {M : (Fin k → ℝ) × T →L[ℝ] K}
    (hM : M = L.comp (ContinuousLinearMap.snd ℝ (Fin k → ℝ) T) +
      E.comp (ContinuousLinearMap.fst ℝ (Fin k → ℝ) T)) (hMF : M.IsFredholm) :
    fredholmIndex M = fredholmIndex L + k := by
  have hE : IsCompactOperator ((-E).comp (ContinuousLinearMap.fst ℝ (Fin k → ℝ) T)) :=
    (isCompactOperator_of_finiteDimensional_domain (-E)).comp_clm _
  have hsum : L.comp (ContinuousLinearMap.snd ℝ (Fin k → ℝ) T) =
      M + (-E).comp (ContinuousLinearMap.fst ℝ (Fin k → ℝ) T) := by
    rw [hM]; ext x <;> simp
  have hLs : (L.comp (ContinuousLinearMap.snd ℝ (Fin k → ℝ) T)).IsFredholm := by
    rw [hsum]; exact isFredholm_add_isCompactOperator hMF hE
  have hind : fredholmIndex (L.comp (ContinuousLinearMap.snd ℝ (Fin k → ℝ) T)) =
      fredholmIndex M := by
    rw [hsum, fredholmIndex_add_isCompactOperator hMF hE]
  rw [← hind]
  obtain ⟨hs, hsind⟩ := linIndex_snd (T := T) (k := k)
  have hcoe : ((L.comp (ContinuousLinearMap.snd ℝ (Fin k → ℝ) T) : (Fin k → ℝ) × T →L[ℝ] K) :
      (Fin k → ℝ) × T →ₗ[ℝ] K) = (L : T →ₗ[ℝ] K) ∘ₗ LinearMap.snd ℝ (Fin k → ℝ) T := rfl
  change linIndex _ = linIndex (L : T →ₗ[ℝ] K) + k
  rw [hcoe, linIndex_comp hs (Polyfold.IsFredholm.hasFiniteIndex hL), hsind]
  ring

end LinearAlgebra

/-! ### "`f'(y)` is Fredholm of index `i`" in every chart -/

section Bundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

variable (B) in
/-- **"`f'(y)` is Fredholm of index `i`"**, chart-intrinsically (the `IndexAt` of round-trip item
V3.98 on level `0`; `IsSurjLinOfIndex` without the surjectivity): in every strong bundle chart `c`
of `P` around `y`, at the level-`1` point `z` over `φ(y)`, the linearization
`Lin(z) : T_zO → K_z` (`linAt`) is Fredholm of index `i`. -/
def StrongBundle.IsLinOfIndex (f : X → Y) (y : X) (i : ℤ) : Prop :=
  ∀ c : StrongBundleChart PX P, B.IsChart c → y ∈ c.φ.source →
    ∀ (z : c.φ.model.E 1) (_ : c.φ.model.E.toBase 1 z = c.φ y)
      (hzU : c.φ.model.E.toBase 1 z ∈ c.U)
      (L : ↥(rangeS (scDeriv c.U (r c.R) z)) →L[ℝ] ↥(rangeS (ρCLM c.isRetraction hzU))),
      (∀ x, (L x : c.F 0) = linAt c.U c.R (c.principal f) z x) →
      L.IsFredholm ∧ fredholmIndex L = i

/-- `IsSurjLinOfIndex f y d` gives `IsLinOfIndex f y d`. -/
theorem StrongBundle.IsSurjLinOfIndex.isLinOfIndex {y : X} {d : ℕ}
    (h : B.IsSurjLinOfIndex f y d) : B.IsLinOfIndex f y d := fun c hc hyV z hz hzU L hL =>
  ⟨(h c hc hyV z hz hzU L hL).2.1, (h c hc hyV z hz hzU L hL).2.2.1⟩

/-- **The index of `f'(y)` is `dim Pn − dim Q` for every germ datum at `y`** (Proposition 3.52
with the index, carried to every chart by `linAt_index_of_conjugationData_wholeChart`). -/
theorem StrongBundle.isLinOfIndex_of_conjugationData_wholeChart (hf : B.IsScSmoothSection f) {y : X}
    (hy0 : IsZeroAt P f y) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hyV : y ∈ c.φ.source) (hφ0 : c.φ y = 0) (h0 : (0 : c.φ.model.E 0) ∈ c.U)
    {g : c.φ.model.E 0 → c.F 0} {s : c.φ.model.E 0 → c.F 1}
    (hfill : IsFilledVersion c.relOpen c.isRetraction h0 (c.principal f) g)
    (hs : IsScSmooth (F := c.F.shift) c.U s) (hs0 : c.F.toBase 1 (s 0) = g 0)
    (dc : ConjugationData c.U fun u => g u - c.F.toBase 1 (s u)) :
    B.IsLinOfIndex f y (finrank ℝ dc.Pn - finrank ℝ dc.Q) := fun _ hc' hyV' _ hz' hzU' L' hL' =>
  ⟨(StrongBundle.linAt_index_of_conjugationData_wholeChart hf hy0 hc hyV hφ0 h0 hfill hs hs0 dc hc' hyV' hz'
      hzU' L' hL').1,
    (StrongBundle.linAt_index_of_conjugationData_wholeChart hf hy0 hc hyV hφ0 h0 hfill hs hs0 dc hc' hyV' hz'
      hzU' L' hL').2.1⟩

set_option maxHeartbeats 400000 in
-- the product chart `(r ↦ r) × φ₁` and its tangent space are unfolded through `PullbackChartData`
/-- **The index of `f` at a zero from the index of the parametrized section** (the step of the
proof of Proposition 6.2 "the index of `F'(0, y)` is `k + ind f'(y)`"): let `f` be an sc-Fredholm
section, `s₁, …, s_k` sc⁺-sections, `y` a zero of `f`, and suppose the parametrized section
`F(λ, y) = f(y) + Σ λᵢ sᵢ(y)` of Theorem 3.18 is Fredholm of index `d` at its zero `(0, y)`
(`IsLinOfIndex`, in every chart of `π*P`).  Then `f'(y)` is Fredholm of index `d − k` in every
chart.  Proof: in the product chart over the chart `c₁` of the germ datum at `y`,
`Lin_F(0)(δa, δu) = Lin_f(0) δu + Σ δaᵢ ŝᵢ(0)` on `T₀(ℝᵏ × O₁) = ℝᵏ × T₀O₁` with values in
`K_{F,0} = K₁` (`linAt_paramSection_zero_wholeChart`, `ofProd_scDeriv_r`, `mem_K_ofProd_zero_iff`), so
`d = ind Lin_F(0) = ind Lin_f(0) + k` (`fredholmIndex_eq_of_param`), and the index of `f'(y)` in
every chart is that in `c₁` (`isLinOfIndex_of_conjugationData_wholeChart`). -/
theorem StrongBundle.isLinOfIndex_of_paramSection_isLinOfIndex_wholeChart {k : ℕ}
    [ParacompactSpace ((Fin k → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))]
    (hf : B.IsScFredholmSectionWholeChart f) {s : Fin k → X → Y} (hs : ∀ i, B.IsScPlusSection (s i))
    {y : X} (hy0 : IsZeroAt P f y) {d : ℤ}
    (hF : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsLinOfIndex
      (paramSection f hf.isScSmooth.1 s fun i => (hs i).1) (0, y) d) :
    B.IsLinOfIndex f y (d - k) := by
  classical
  set F := paramSection f hf.isScSmooth.1 s (fun i => (hs i).1) with hFdef
  have hFF : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsScFredholmSectionWholeChart F :=
    theorem_3_18_wholeChart hf hs
  have hFs : IsSection (pullbackProj P Prod.snd) F := hFF.isScSmooth.1
  have hz0 : IsZeroAt (pullbackProj P Prod.snd) F (0, y) := by
    rw [hFdef, isZeroAt_paramSection_iff]
    change IsZeroAt P (paramSlice f hf.isScSmooth.1 s (fun i => (hs i).1) 0) y
    rw [paramSlice_zero]; exact hy0
  -- the chart of the germ datum at `y`
  have hys : y ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hy0
  obtain ⟨-, c₁, hc₁, hyV₁, hφ₁, h0₁, g₁, s₁, hfill₁, hs₁, hs0₁, hconj₁⟩ := hf.germ y hys
  obtain ⟨d₁⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj₁
  have hidx₁ := StrongBundle.isLinOfIndex_of_conjugationData_wholeChart hf.isScSmooth hy0 hc₁ hyV₁ hφ₁ h0₁
    hfill₁ hs₁ hs0₁ d₁
  suffices hsuff : (finrank ℝ d₁.Pn - finrank ℝ d₁.Q : ℤ) = d - k by rw [← hsuff]; exact hidx₁
  -- `L₁ = Lin_f(0) : T₀O₁ → K₁` in `c₁`
  have h0O₁ : (0 : c₁.φ.model.E 0) ∈ c₁.φ.model.O := by
    rw [← hφ₁]; exact c₁.φ.mapsTo_model y hyV₁
  have h0O₁' : (0 : c₁.φ.model.E 0) ∈ r c₁.R '' c₁.U := c₁.r_image ▸ h0O₁
  have hz₁ : c₁.φ.model.E.toBase 1 (0 : c₁.φ.model.E 1) = c₁.φ y := by rw [map_zero, hφ₁]
  have hzU₁ : c₁.φ.model.E.toBase 1 (0 : c₁.φ.model.E 1) ∈ c₁.U := by rw [map_zero]; exact h0₁
  have hzO₁ : c₁.φ.model.E.toBase 1 (0 : c₁.φ.model.E 1) ∈ r c₁.R '' c₁.U := by
    rw [map_zero]; exact h0O₁'
  have hfr₁ : IsSc1 c₁.U (c₁.principal f ∘ r c₁.R) := hf.isScSmooth.isSc1_principal_comp_r hc₁
  have hfK₁ : ∀ x ∈ r c₁.R '' c₁.U, (x, c₁.principal f x) ∈ c₁.R '' (c₁.U ×ˢ univ) :=
    fun x hx => c₁.principal_mem_K hf.isScSmooth.1 (c₁.r_image ▸ hx)
  have hfz₁ : c₁.principal f (c₁.φ.model.E.toBase 1 (0 : c₁.φ.model.E 1)) = 0 := by
    rw [hz₁]; exact (c₁.isZeroAt_iff hf.isScSmooth.1 hyV₁).1 hy0
  have hmem₁ : ∀ x : ↥(rangeS (scDeriv c₁.U (r c₁.R) (0 : c₁.φ.model.E 1))),
      linAt c₁.U c₁.R (c₁.principal f) 0 x ∈ rangeS (ρCLM c₁.isRetraction hzU₁) := fun x =>
    ⟨_, rho_scDeriv_comp_r c₁.relOpen c₁.isRetraction hfr₁ hfK₁ hzO₁ hfz₁ x⟩
  set L₁ := (linAt c₁.U c₁.R (c₁.principal f) 0).codRestrict _ hmem₁ with hL₁
  obtain ⟨hL₁F, hL₁ind⟩ := hidx₁ c₁ hc₁ hyV₁ 0 hz₁ hzU₁ L₁ fun _ => rfl
  -- the product chart `(r ↦ r) × φ₁` at `(0, y)` and `L_F = Lin_F(0)`
  set q₀ := F (0, y) with hq₀
  set pc := (PullbackChartData.ofProd c₁ 0).toChart q₀ with hpc
  have hpcc : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsChart pc :=
    (PullbackChartData.ofProd c₁ 0).isChart_toChart B _ hc₁ q₀
  have hzV : (0, y) ∈ pc.φ.source := ⟨mem_univ _, hyV₁⟩
  have hpc0 : pc.φ (0, y) = 0 := ofProd_apply_eq_zero c₁ 0 q₀ hφ₁
  have hzF : pc.φ.model.E.toBase 1 (0 : pc.φ.model.E 1) = pc.φ (0, y) := by
    rw [map_zero, hpc0]
  have hzUF : pc.φ.model.E.toBase 1 (0 : pc.φ.model.E 1) ∈ pc.U := by
    rw [map_zero]; exact ⟨mem_univ _, h0₁⟩
  have hzOF : pc.φ.model.E.toBase 1 (0 : pc.φ.model.E 1) ∈ r pc.R '' pc.U := by
    rw [pc.r_image, hzF]; exact pc.φ.mapsTo_model (0, y) hzV
  have hfrF : IsSc1 pc.U (pc.principal F ∘ r pc.R) := hFF.isScSmooth.isSc1_principal_comp_r hpcc
  have hfKF : ∀ x ∈ r pc.R '' pc.U, (x, pc.principal F x) ∈ pc.R '' (pc.U ×ˢ univ) :=
    fun x hx => pc.principal_mem_K hFs (pc.r_image ▸ hx)
  have hfzF : pc.principal F (pc.φ.model.E.toBase 1 (0 : pc.φ.model.E 1)) = 0 := by
    rw [hzF]; exact (pc.isZeroAt_iff hFs hzV).1 hz0
  have hmemF : ∀ x : ↥(rangeS (scDeriv pc.U (r pc.R) (0 : pc.φ.model.E 1))),
      linAt pc.U pc.R (pc.principal F) 0 x ∈ rangeS (ρCLM pc.isRetraction hzUF) := fun x =>
    ⟨_, rho_scDeriv_comp_r pc.relOpen pc.isRetraction hfrF hfKF hzOF hfzF x⟩
  set LF := (linAt pc.U pc.R (pc.principal F) 0).codRestrict _ hmemF with hLF
  obtain ⟨hLFF, hLFind⟩ := hF pc hpcc hzV 0 hzF hzUF LF fun _ => rfl
  -- the fibres `K_{F,0}` and `K₁` agree
  have hKeq : ∀ k' : pc.F 0, k' ∈ rangeS (ρCLM pc.isRetraction hzUF) ↔
      k' ∈ rangeS (ρCLM c₁.isRetraction hzU₁) := by
    intro k'
    refine (mem_rangeS_ρCLM_iff pc.isRetraction hzOF hzUF).trans ?_
    refine Iff.trans ?_ (mem_rangeS_ρCLM_iff c₁.isRetraction hzO₁ hzU₁).symm
    rw [map_zero, map_zero]
    exact mem_K_ofProd_zero_iff c₁ 0 q₀ h0O₁ k'
  -- `T₀(ℝᵏ × O₁) = ℝᵏ × T₀O₁`
  have hTmem : ∀ (a : Fin k → ℝ) (u : ↥(rangeS (scDeriv c₁.U (r c₁.R) (0 : c₁.φ.model.E 1)))),
      ((a, (u : c₁.φ.model.E 0)) : (Fin k → ℝ) × c₁.φ.model.E 0) ∈
        rangeS (scDeriv pc.U (r pc.R) (0 : pc.φ.model.E 1)) := by
    intro a u
    obtain ⟨u₀, hu₀⟩ := u.2
    exact ⟨(a, u₀), (PullbackChartData.ofProd_scDeriv_r c₁ 0 q₀ h0₁ (a, u₀)).trans
      (Prod.ext rfl hu₀)⟩
  -- completeness of the four spaces
  obtain ⟨-, hT₁, hK₁, -, -, -, -⟩ := StrongBundle.linAt_isScFredholm_wholeChart hf hy0 hc₁ hyV₁ hz₁ hzU₁
  obtain ⟨-, hTF, hKF, -, -, -, -⟩ := StrongBundle.linAt_isScFredholm_wholeChart hFF hz0 hpcc hzV hzF hzUF
  have : CompleteSpace ↥(rangeS (scDeriv c₁.U (r c₁.R) (0 : c₁.φ.model.E 1))) :=
    hT₁.isClosed.completeSpace_coe
  have : CompleteSpace ↥(rangeS (ρCLM c₁.isRetraction hzU₁)) := hK₁.isClosed.completeSpace_coe
  have : CompleteSpace ↥(rangeS (scDeriv pc.U (r pc.R) (0 : pc.φ.model.E 1))) :=
    hTF.isClosed.completeSpace_coe
  have : CompleteSpace ↥(rangeS (ρCLM pc.isRetraction hzUF)) := hKF.isClosed.completeSpace_coe
  -- the isomorphisms `ℝᵏ × T₀O₁ ≃ T₀(ℝᵏ × O₁)` and `K₁ ≃ K_{F,0}`
  set eT : ((Fin k → ℝ) × ↥(rangeS (scDeriv c₁.U (r c₁.R) (0 : c₁.φ.model.E 1)))) ≃L[ℝ]
      ↥(rangeS (scDeriv pc.U (r pc.R) (0 : pc.φ.model.E 1))) :=
    ContinuousLinearEquiv.equivOfInverse
      (((ContinuousLinearMap.id ℝ (Fin k → ℝ)).prodMap
        (rangeS (scDeriv c₁.U (r c₁.R) (0 : c₁.φ.model.E 1))).subtypeL).codRestrict _
          fun p => hTmem p.1 p.2)
      (((ContinuousLinearMap.fst ℝ (Fin k → ℝ) (c₁.φ.model.E 0)).comp
          (rangeS (scDeriv pc.U (r pc.R) (0 : pc.φ.model.E 1))).subtypeL).prod
        (((ContinuousLinearMap.snd ℝ (Fin k → ℝ) (c₁.φ.model.E 0)).comp
          (rangeS (scDeriv pc.U (r pc.R) (0 : pc.φ.model.E 1))).subtypeL).codRestrict _
            fun w => PullbackChartData.ofProd_mem_tangent c₁ 0 q₀ h0₁ w.2))
      (fun p => Prod.ext rfl (Subtype.ext rfl)) (fun w => Subtype.ext (Prod.ext rfl rfl))
    with heT
  set eK : ↥(rangeS (ρCLM c₁.isRetraction hzU₁)) ≃L[ℝ] ↥(rangeS (ρCLM pc.isRetraction hzUF)) :=
    restrictEquiv _ _ (ContinuousLinearMap.id ℝ (c₁.F 0)) (ContinuousLinearMap.id ℝ (c₁.F 0))
      (fun x hx => (hKeq x).2 hx) (fun x hx => (hKeq x).1 hx) (fun _ _ => rfl) (fun _ _ => rfl)
    with heK
  -- the finite-rank part `a ↦ Σ aᵢ ŝᵢ(0)`
  have hsmem : ∀ i, c₁.principal (s i) 0 ∈ rangeS (ρCLM c₁.isRetraction hzU₁) := fun i => by
    rw [mem_rangeS_ρCLM_iff c₁.isRetraction hzO₁ hzU₁, map_zero]
    exact c₁.principal_mem_K (hs i).1 h0O₁
  set Ef : (Fin k → ℝ) →L[ℝ] ↥(rangeS (ρCLM c₁.isRetraction hzU₁)) :=
    ∑ i, (ContinuousLinearMap.proj i).smulRight
      (⟨c₁.principal (s i) 0, hsmem i⟩ : ↥(rangeS (ρCLM c₁.isRetraction hzU₁))) with hEf
  set M := L₁.comp (ContinuousLinearMap.snd ℝ (Fin k → ℝ) _) +
    Ef.comp (ContinuousLinearMap.fst ℝ (Fin k → ℝ) _) with hM
  -- the conjugation `L_F ∘ eT = eK ∘ M`
  have hconj : ∀ p, LF (eT p) = eK (M p) := by
    intro p
    apply Subtype.ext
    change linAt pc.U pc.R (pc.principal F) 0 (eT p) = ((M p : _) : c₁.F 0)
    rw [linAt_paramSection_zero_wholeChart hf hs hc₁ h0O₁ q₀ (eT p).2]
    change linAt c₁.U c₁.R (c₁.principal f) 0 ⟨p.2.1, _⟩ + ∑ i, p.1 i • c₁.principal (s i) 0 =
      (L₁ p.2 : c₁.F 0) + (Ef p.1 : c₁.F 0)
    rw [hEf]
    simp only [FunLike.coe_sum, Finset.sum_apply, Submodule.coe_sum,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, Submodule.coe_smul]
    rfl
  obtain ⟨hiff, hind⟩ := isFredholm_iff_of_conj hconj
  have hMF : M.IsFredholm := hiff.2 hLFF
  have hMind : fredholmIndex M = fredholmIndex L₁ + k := fredholmIndex_eq_of_param hL₁F Ef hM hMF
  have h1 := hind hMF
  rw [hLFind] at h1
  rw [← hL₁ind]
  omega

/-! ### The index is locally constant along the zero set -/

/-- **The Fredholm index of the linearization is locally constant along the zero set** (round-trip
item V3.98 (b); Theorem 3.54 and the proof of Proposition 6.2 along the solution set, without good
position or surjectivity at `x₀`): let `X` admit sc-smooth bump functions (Definition 5.9) and `f`
be an sc-Fredholm section with tame germ data (Definition 3.51), `f(x₀) = 0`.  Then there are an
open `V ∋ x₀` and `i ∈ ℤ` such that at every zero `y ∈ V` (in particular at `x₀`) `f'(y)` is
Fredholm of index `i` in every strong bundle chart (`IsLinOfIndex`).  Proof: the text's device for
Proposition 6.2 — finitely many sc⁺-sections put the parametrized section `F` of Theorem 3.18 into
general position at `(0, x₀)` (`exists_sections_isParamGP`,
`isGeneralPositionGerm_paramSection_of_isParamGP`, Lemma 5.26), the index of `F` is constant along
its solution set near `(0, x₀)` (`theorem_3_54_index_locally_constant_wholeChart`), and at `(0, y)` it is
`k + ind f'(y)` (`isLinOfIndex_of_paramSection_isLinOfIndex_wholeChart`). -/
theorem index_locally_constant_of_admitsBumpFunctions_wholeChart (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTameWholeChart f) {x₀ : X} (hx₀ : IsZeroAt P f x₀) :
    ∃ (V : Set X) (i : ℤ), IsOpen V ∧ x₀ ∈ V ∧ ∀ y ∈ V, IsZeroAt P f y → B.IsLinOfIndex f y i := by
  classical
  obtain ⟨N, hN⟩ := proposition_5_3_exists (B := B)
  have hfF := hf.toIsScFredholmSectionWholeChart
  have hxs : x₀ ∈ PX.smoothSet := hfF.mem_smoothSet_of_isZeroAt hx₀
  obtain ⟨-, c, hc, hxV, hφ0, -⟩ := hf.germTame x₀ hxs
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  -- the Chapter 5 lemmas take the germ reading of Definition 3.51 (phase 2); the whole-chart
  -- reading implies it
  obtain ⟨k, s, hsp, -, -, hgp⟩ := exists_sections_isParamGP hbump hN hf.isScFredholmSectionTame
    hx₀ hc hxV hφ0 T hT isOpen_univ (mem_univ _)
  have := MPolyfold.paracompactSpace_prod (rnPolyfold k) PX
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin k → ℝ) × X → X))
    ((rnPolyfold k).prod PX) B
  have hFt := theorem_3_18_tame_wholeChart hf hsp
  set F := paramSection f hf.isScSmooth.1 s (fun i => (hsp i).1) with hFdef
  have hz0 : ∀ y, IsZeroAt P f y → IsZeroAt (pullbackProj P Prod.snd) F (0, y) := fun y hy => by
    rw [hFdef, isZeroAt_paramSection_iff]
    change IsZeroAt P (paramSlice f hf.isScSmooth.1 s (fun i => (hsp i).1) 0) y
    rw [paramSlice_zero]; exact hy
  have hgen := isGeneralPositionGerm_paramSection_of_isParamGP hf.isScFredholmSectionTame hsp hx₀
    hc hxV hφ0 T hT hgp
  have hgood := hgen.isGoodPositionGermTame hFt.isScFredholmSectionTame (hz0 x₀ hx₀)
  obtain ⟨Vx, d, hVo, hxVx, hall⟩ :=
    theorem_3_54_index_locally_constant hFt.isScFredholmSectionTame hgood (hz0 x₀ hx₀)
  refine ⟨Prod.mk (0 : Fin k → ℝ) ⁻¹' Vx, (d : ℤ) - k,
    hVo.preimage (continuous_const.prodMk continuous_id), hxVx, fun y hy hy0 => ?_⟩
  exact StrongBundle.isLinOfIndex_of_paramSection_isLinOfIndex_wholeChart hfF hsp hy0
    (hall (0, y) hy (hz0 y hy0)).isLinOfIndex

/-- **The index is locally constant along the zero set, sc form** (round-trip item V3.98 (b):
the sc-Fredholm index of `f'(y)` in every chart; `theorem_3_54_index_locally_constant_sc_wholeChart` without
the good position at `x₀`): with the hypotheses of `index_locally_constant_of_admitsBumpFunctions_wholeChart`,
there are an open `V ∋ x₀` and `i ∈ ℤ` such that at every zero `y ∈ V`, in **every** strong bundle
chart `c` of `P` around `y`, at the level-`1` point `z` over `φ(y)`, the linearization
`Lin(z) : T_zO → K_z` (`ScOperator.restrict`, level-`0` map `linAt`) is an sc-Fredholm operator,
Fredholm of index `i` on every level.  (`linAt_isScFredholm_wholeChart` gives the sc-Fredholm property and
the equality of the indices on all levels; the level-`0` index is `i` by
`index_locally_constant_of_admitsBumpFunctions_wholeChart`.) -/
theorem theorem_3_54_index_locally_constant_general_wholeChart (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTameWholeChart f) {x₀ : X} (hx₀ : IsZeroAt P f x₀) :
    ∃ (V : Set X) (i : ℤ), IsOpen V ∧ x₀ ∈ V ∧
      ∀ y ∈ V, IsZeroAt P f y → ∀ (c : StrongBundleChart PX P) (_ : B.IsChart c)
        (_ : y ∈ c.φ.source) (z : c.φ.model.E 1) (_ : c.φ.model.E.toBase 1 z = c.φ y)
        (hzU : c.φ.model.E.toBase 1 z ∈ c.U),
        ∃ (hD : IsScOperator (scDeriv c.U (c.principal f ∘ r c.R) z))
          (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (r c.R) z)))
          (hK : c.F.IsScSubspace (rangeS (ρCLM c.isRetraction hzU)))
          (hTK : ∀ x ∈ rangeS (scDeriv c.U (r c.R) z),
            hD.toScOperator 0 x ∈ rangeS (ρCLM c.isRetraction hzU)),
          (∀ x : (c.φ.model.E.ofSubspace hT) 0,
            ((hD.toScOperator.restrict hT hK hTK 0 x).1 : c.F 0) =
              linAt c.U c.R (c.principal f) z ⟨x.1, x.2⟩) ∧
          IsScFredholm (hD.toScOperator.restrict hT hK hTK) ∧
          ∀ m, ((hD.toScOperator.restrict hT hK hTK) m).IsFredholm ∧
            fredholmIndex ((hD.toScOperator.restrict hT hK hTK) m) = i := by
  obtain ⟨V, i, hVo, hxV, hall⟩ := index_locally_constant_of_admitsBumpFunctions_wholeChart hbump hf hx₀
  refine ⟨V, i, hVo, hxV, fun y hy hy0 c hc hyV z hz hzU => ?_⟩
  obtain ⟨hD, hT, hK, hTK, happ, hsc, hlvl⟩ :=
    StrongBundle.linAt_isScFredholm_wholeChart hf.toIsScFredholmSectionWholeChart hy0 hc hyV hz hzU
  have hmem : ∀ x : ↥(rangeS (scDeriv c.U (r c.R) z)),
      linAt c.U c.R (c.principal f) z x ∈ rangeS (ρCLM c.isRetraction hzU) := fun x => by
    have := hTK x x.2
    rwa [hD.toScOperator_zero] at this
  obtain ⟨hLF, hLind⟩ := hall y hy hy0 c hc hyV z hz hzU
    ((linAt c.U c.R (c.principal f) z).codRestrict _ hmem) fun _ => rfl
  obtain ⟨-, hind0⟩ := hD.toScOperator.isFredholm_restrict_zero hT hK hTK
    (L := (linAt c.U c.R (c.principal f) z).codRestrict _ hmem)
    (fun x => by rw [hD.toScOperator_zero]; rfl) hLF
  refine ⟨hD, hT, hK, hTK, happ, hsc, fun m => ⟨(hlvl m).1, ?_⟩⟩
  rw [(hlvl m).2.1, hind0, hLind]

end Bundle

end Polyfold
