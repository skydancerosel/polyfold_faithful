import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_56

/-!
Round trip for V5_56 (Theorem 5.37, "(ii) ⇒ (i)", the steps of the proof).  `A` is the
conjunction of the types of `Polyfold.MChart.exists_small_nhds`,
`Polyfold.LocalModel.HasApproxProperty.exists_approx`, `Polyfold.exists_isScSmoothMap_urysohn`
and `Polyfold.admitsScPartitionsOfUnity_of_approx`, universes instantiated at `0`.

B is the text's construction as one existence claim (for an atlas `A ≃ PX.atlas` of local models
with the approximation property and any open cover `(U_i)`: a locally finite refinement `(W_λ)`
indexed by a new set `Λ` with `τ : Λ → I`, `cl(W_λ) ⊆ U_{τ(λ)} ∩ dom φ_λ`, a closed shrinking
`(Q_λ)`, Urysohn functions `f_λ`, sc-smooth `g_λ` with `|f_λ ∘ φ_λ⁻¹ − g_λ| < 1/2`, and
`γ_λ = ĝ_λ / Σ ĝ` an sc-smooth partition of unity subordinate to `(W_λ)`), together with the
conclusion (i).

`A → B` (uses `A`): the conclusion (i) is the fourth conjunct (with the atlas glue
`exists_atlas_iff` of V5_57).  The construction is built from the first two conjuncts, which are
exactly the tools the text's steps need: `exists_small_nhds` (applied inside an open `U'` with
`cl(U') ⊆ U_i`) gives chart neighbourhoods `N_x` with `cl(N_x) ⊆ U_{τ(x)} ∩ dom φ_x` and
`cl(φ_x(N_x)) ⊆ O_x` (the hypothesis the text does not arrange), Mathlib gives the locally finite
refinement `W_x ⊆ N_x` and a bump covering `f_x` (`Q_x = {f_x = 1}`), `exists_approx` with
`ε = 1/4` gives `ĝ_x`, and `g_x = ĝ_x ∘ φ_x⁻¹`.  Then `Σ ĝ ≥ 3/4 > 0` and `ĝ_λ / Σ ĝ` is
sc-smooth (locally `ĝ_λ · σ(Σ ĝ)` with `σ` smooth, `σ(t) = 1/t` for `t ≥ c`).  So the text's
quotient construction works once the refinement is allowed a new index set (B allows it).

`B → A`: conjuncts 3 and 4 follow from B's conclusion (i) (Urysohn functions from a partition of
unity subordinate to `{X ∖ s, X ∖ t}`).  Conjuncts 1 and 2 are auxiliary chart lemmas of the
project's proof (no approximation property in 1; one chart in 2) on which B says nothing; they are
re-proved here by the project's short arguments (copied, they do not use the banned theorems).
-/

namespace RoundTrip.V5_56
open Polyfold Set Filter Topology Function
open scoped ContDiff

/-- The project's statement, universe `0`. -/
def A : Prop :=
  (type_of% @Polyfold.MChart.exists_small_nhds.{0}) ∧
  (type_of% @Polyfold.LocalModel.HasApproxProperty.exists_approx.{0}) ∧
  (type_of% @Polyfold.exists_isScSmoothMap_urysohn.{0}) ∧
  (type_of% @Polyfold.admitsScPartitionsOfUnity_of_approx.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MChart.exists_small_nhds.{0}, @Polyfold.LocalModel.HasApproxProperty.exists_approx.{0},
    @Polyfold.exists_isScSmoothMap_urysohn.{0}, @Polyfold.admitsScPartitionsOfUnity_of_approx.{0}⟩

/-- A covering set of charts of the structure is the same as an atlas equivalent to `PX.atlas`
(from V5_57). -/
theorem exists_atlas_iff {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) (Q : MChart X → Prop) :
    (∃ S : Set (MChart X), (∀ φ ∈ S, PX.IsChart φ) ∧ (∀ x, ∃ φ ∈ S, x ∈ φ.source) ∧
      ∀ φ ∈ S, Q φ) ↔
    ∃ A : MAtlas X, A.Equiv PX.atlas ∧ ∀ φ ∈ A.charts, Q φ := by
  constructor
  · rintro ⟨S, hS, hcov, hQ⟩
    refine ⟨⟨S, fun φ hφ ψ hψ => MPolyfold.IsChart.compatible PX (hS φ hφ) (hS ψ hψ), hcov⟩,
      (MAtlas.equiv_iff _ _).2 fun φ hφ ψ hψ => hS φ hφ ψ hψ, hQ⟩
  · rintro ⟨A, hA, hQ⟩
    exact ⟨A.charts, fun φ hφ ψ hψ => (MAtlas.equiv_iff _ _).1 hA φ hφ ψ hψ, A.cover, hQ⟩

/-- A `C^∞` function equal to `1/t` for `t ≥ c > 0`: `1/q` with
`q(t) = t + τ(2(c − t)/c)(c − t) ≥ c/2`. -/
theorem exists_smooth_inv {c : ℝ} (hc : 0 < c) :
    ∃ σ : ℝ → ℝ, ContDiff ℝ ∞ σ ∧ ∀ t, c ≤ t → σ t = t⁻¹ := by
  have hs : ContDiff ℝ ∞ fun t : ℝ => Real.smoothTransition (2 * (c - t) / c) :=
    (Real.smoothTransition.contDiff (n := ⊤)).comp
      ((contDiff_const.mul (contDiff_const.sub contDiff_id)).div_const c)
  have hq : ContDiff ℝ ∞ fun t : ℝ => t + Real.smoothTransition (2 * (c - t) / c) * (c - t) :=
    contDiff_id.add (hs.mul (contDiff_const.sub contDiff_id))
  have hqpos : ∀ t : ℝ, 0 < t + Real.smoothTransition (2 * (c - t) / c) * (c - t) := by
    intro t
    have h0 := Real.smoothTransition.nonneg (2 * (c - t) / c)
    have h1 := Real.smoothTransition.le_one (2 * (c - t) / c)
    by_cases ht : c / 2 ≤ t
    · nlinarith
    · have h2 : 1 ≤ 2 * (c - t) / c := by rw [le_div_iff₀ hc]; linarith
      rw [Real.smoothTransition.one_of_one_le h2]
      linarith
  refine ⟨fun t => (t + Real.smoothTransition (2 * (c - t) / c) * (c - t))⁻¹,
    hq.inv fun t => (hqpos t).ne', fun t ht => ?_⟩
  have h3 : 2 * (c - t) / c ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hc.le
  simp only [Real.smoothTransition.zero_of_nonpos h3, zero_mul, add_zero]

/-! ### A → B -/

theorem A_to_B : A → B := by
  rintro ⟨hsmall, happrox, -, hpou⟩
  intro X _ _ _ PX At hAt happ
  have hS : ∀ φ ∈ At.charts, PX.IsChart φ := fun φ hφ ψ hψ =>
    (MAtlas.equiv_iff _ _).1 hAt φ hφ ψ hψ
  refine ⟨fun I U hUo hUcov => ?_, hpou hS At.cover happ⟩
  classical
  -- a chart and a member of the cover at each point
  choose φ hφA hxφ using At.cover
  have hi : ∀ x, ∃ i, x ∈ U i := fun x => mem_iUnion.1 (hUcov.symm ▸ mem_univ x)
  choose τ hxτ using hi
  -- an open `U'_x ∋ x` with `cl(U'_x) ⊆ U_{τ(x)}`
  have hU' : ∀ x, ∃ U' : Set X, IsOpen U' ∧ x ∈ U' ∧ closure U' ⊆ U (τ x) := by
    intro x
    obtain ⟨t, ht, htc, htsub⟩ :=
      exists_mem_nhds_isClosed_subset ((hUo (τ x)).mem_nhds (hxτ x))
    exact ⟨interior t, isOpen_interior, mem_interior_iff_mem_nhds.2 ht,
      (closure_minimal interior_subset htc).trans htsub⟩
  choose U' hU'o hxU' hU'cl using hU'
  -- small chart neighbourhoods (conjunct 1 of `A`)
  have hN : ∀ x, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ N ⊆ U' x ∩ (φ x).source ∧
      closure N ⊆ (φ x).source ∧ closure ((φ x) '' N) ⊆ (φ x).model.O :=
    fun x => hsmall (φ x) (hxφ x) (hU'o x) (hxU' x)
  choose N hNo hxN hNsub hNcl hNO using hN
  -- the locally finite refinement and the bump covering
  obtain ⟨W, hWo, hWcov, hWlf, hWN⟩ :=
    precise_refinement N hNo (iUnion_eq_univ_iff.2 fun x => ⟨x, hxN x⟩)
  obtain ⟨f, hf⟩ := BumpCovering.exists_isSubordinate isClosed_univ W hWo (by rw [hWcov])
  have hWφ : ∀ x, W x ⊆ (φ x).source := fun x => (hWN x).trans ((hNsub x).trans inter_subset_right)
  -- the approximations (conjunct 2 of `A`, `ε = 1/4`)
  have hG : ∀ x, ∃ G : X → ℝ, PX.IsScSmoothMap realPolyfold G ∧ (∀ y, G y ∈ Icc (0 : ℝ) 1) ∧
      tsupport G ⊆ W x ∧ ∀ y, |f x y - G y| ≤ 1 / 4 :=
    fun x => happrox (hS _ (hφA x)) (happ _ (hφA x)) (hWo x) (hWφ x)
      ((closure_mono (hWN x)).trans (hNcl x)) ((closure_mono (image_mono (hWN x))).trans (hNO x))
      (f x).continuous (fun y => ⟨f.nonneg x y, f.le_one x y⟩) (hf x) (by norm_num)
  choose G hGsc hG01 hGsupp hGf using hG
  have hGlf : LocallyFinite fun x => support (G x) :=
    hWlf.subset fun x => subset_closure.trans (hGsupp x)
  -- `ĝ_λ` is `G λ`
  have hext : ∀ l y, extByZero (φ l) (fun z => G l ((φ l).toPartialEquiv.symm z)) y = G l y := by
    intro l y
    unfold extByZero
    by_cases hy : y ∈ (φ l).source
    · rw [indicator_of_mem hy]
      change G l ((φ l).symm ((φ l) y)) = G l y
      rw [(φ l).symm_apply_apply hy]
    · rw [indicator_of_notMem hy]
      exact (image_eq_zero_of_notMem_tsupport fun h => hy (hWφ l (hGsupp l h))).symm
  -- `Σ ĝ ≥ 3/4`
  set Sm : X → ℝ := fun y => ∑ᶠ m, G m y with hSm
  have hSpos : ∀ y, 0 < Sm y := by
    intro y
    set i := f.ind y (mem_univ y)
    have h1 : f i y = 1 := f.ind_apply y (mem_univ y)
    have h2 := hGf i y
    rw [h1] at h2
    have h3 : 3 / 4 ≤ G i y := by linarith [(abs_le.1 h2).2]
    exact lt_of_lt_of_le (by linarith) (h3.trans
      (single_le_finsum i (hGlf.point_finite y) fun j => (hG01 j y).1))
  have hSsc : PX.IsScSmoothMap realPolyfold Sm := isScSmoothMap_real_finsum hGsc hGlf
  have hScont : Continuous Sm := continuousOn_univ.1 hSsc.continuousOn
  have hdivsupp : ∀ l, tsupport (fun y => G l y / Sm y) ⊆ W l := fun l =>
    (closure_mono (show support (fun y => G l y / Sm y) ⊆ support (G l) from fun y hy =>
      mem_support.2 fun h0 => (mem_support.1 hy) (by simp only [h0, zero_div]))).trans (hGsupp l)
  refine ⟨X, τ, φ, W, fun x => {y | f x y = 1}, fun x => ⇑(f x),
    fun l z => G l ((φ l).toPartialEquiv.symm z), hφA, hWo, hWlf,
    fun l => subset_inter ((closure_mono ((hWN l).trans ((hNsub l).trans
      inter_subset_left))).trans (hU'cl l)) ((closure_mono (hWN l)).trans (hNcl l)),
    fun l => ⟨isClosed_eq (f l).continuous continuous_const, fun y (hy : f l y = 1) =>
      hf l (subset_tsupport _ (by rw [mem_support, hy]; exact one_ne_zero))⟩,
    eq_univ_of_forall fun y => mem_iUnion.2 ⟨f.ind y (mem_univ y), f.ind_apply y (mem_univ y)⟩,
    fun l => ⟨(f l).continuous, fun y => ⟨f.nonneg l y, f.le_one l y⟩, fun y hy => hy, hf l⟩,
    fun l => ⟨(hGsc l).real_chart (hS _ (hφA l)), fun y _ => hG01 l _, ?_, fun y _ =>
      (hGf l _).trans_lt (by norm_num)⟩, ?_⟩
  · -- the support of `g_λ` lies in `φ_λ(W_λ)`
    rintro z ⟨hz, hzO⟩
    have hcw : ContinuousWithinAt (φ l).symm
        ((φ l).model.O ∩ support fun z => G l ((φ l).toPartialEquiv.symm z)) z :=
      ((φ l).continuousOn_invFun z hzO).mono inter_subset_left
    have h1 := hcw.mem_closure_image hz
    have h2 : (φ l).symm '' ((φ l).model.O ∩ support fun z => G l ((φ l).toPartialEquiv.symm z))
        ⊆ support (G l) := by
      rintro _ ⟨z', hz', rfl⟩; exact hz'.2
    have h3 : (φ l).symm z ∈ W l := hGsupp l (closure_mono h2 h1)
    exact ⟨(φ l).symm z, h3, (φ l).apply_symm_apply hzO⟩
  · simp only [hext]
    refine ⟨hSpos, ⟨fun l => ?_, fun l y => div_nonneg (hG01 l y).1 (hSpos y).le,
      hWlf.subset hdivsupp, fun y => ?_⟩, hdivsupp⟩
    · -- `ĝ_λ / Σ ĝ` is sc-smooth: locally `ĝ_λ · σ(Σ ĝ)`
      refine isScSmoothMap_real_of_eventuallyEq fun y => ?_
      obtain ⟨σ, hσ, hσinv⟩ := exists_smooth_inv (half_pos (hSpos y))
      refine ⟨fun z => G l z * (σ ∘ Sm) z, (hGsc l).real_mul (hSsc.comp_contDiff hσ), ?_⟩
      filter_upwards [hScont.continuousAt.eventually (lt_mem_nhds (half_lt_self (hSpos y)))]
        with z hz
      simp only [Function.comp_apply, hσinv _ hz.le, div_eq_mul_inv]
      rfl
    · simp_rw [div_eq_mul_inv]
      rw [← finsum_mul]
      exact mul_inv_cancel₀ (hSpos y).ne'

/-! ### B → A -/

section Reproved

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- Conjunct 1 re-proved (the project's argument; B says nothing on charts alone). -/
lemma exists_small_nhds' (φ : MChart X) {x : X} (hx : x ∈ φ.source) {U : Set X}
    (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ N ⊆ U ∩ φ.source ∧ closure N ⊆ φ.source ∧
      closure (φ '' N) ⊆ φ.model.O := by
  set z := φ x with hz
  have hzO : z ∈ φ.model.O := φ.mapsTo_model x hx
  obtain ⟨R₀, hR₀⟩ := φ.model.isScRetract
  obtain ⟨W', hW'o, hW'eq⟩ := R₀.relOpen.relOpen
  have hzW' : z ∈ W' := by
    have : z ∈ R₀.U := R₀.retract_subset (hR₀ ▸ hzO)
    rw [hW'eq] at this; exact this.1
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hW'o z hzW'
  have hclos := closure_inter_ball_subset R₀ hR₀ hW'eq hball
  obtain ⟨t, ht, htc, htsub⟩ :=
    exists_mem_nhds_isClosed_subset ((hU.inter φ.isOpen_source).mem_nhds ⟨hxU, hx⟩)
  refine ⟨interior t ∩ (φ.source ∩ φ ⁻¹' Metric.ball z (r / 2)),
    isOpen_interior.inter (φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source
      Metric.isOpen_ball),
    ⟨mem_interior_iff_mem_nhds.2 ht, hx, Metric.mem_ball_self (by positivity)⟩,
    fun y hy => htsub (interior_subset hy.1), ?_, ?_⟩
  · exact (closure_mono (inter_subset_left.trans interior_subset)).trans
      (htc.closure_subset.trans (htsub.trans inter_subset_right))
  · refine (closure_mono ?_).trans hclos
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨φ.mapsTo_model y hy.2.1, hy.2.2⟩

/-- Conjunct 2 re-proved (the project's argument; B says nothing on a single chart). -/
theorem exists_approx' {PX : MPolyfold X} {φ : MChart X} (hφ : PX.IsChart φ)
    (happ : φ.model.HasApproxProperty) {N : Set X} (hNo : IsOpen N) (hNφ : N ⊆ φ.source)
    (hcl : closure N ⊆ φ.source) (hclO : closure (φ '' N) ⊆ φ.model.O) {f : X → ℝ}
    (hf : Continuous f) (hf01 : ∀ y, f y ∈ Icc (0 : ℝ) 1) (hfsupp : tsupport f ⊆ N) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : X → ℝ, PX.IsScSmoothMap realPolyfold g ∧ (∀ y, g y ∈ Icc (0 : ℝ) 1) ∧
      tsupport g ⊆ N ∧ ∀ y, |f y - g y| ≤ ε := by
  obtain ⟨W, hWo, hWeq⟩ := φ.exists_isOpen_image_eq hNφ hNo
  have hWcl : closure (φ.model.O ∩ W) ⊆ φ.model.O := hWeq ▸ hclO
  have hfc : ContinuousOn (f ∘ φ.symm) φ.model.O := hf.comp_continuousOn φ.continuousOn_invFun
  have hfsupp' : closure (φ.model.O ∩ support (f ∘ φ.symm)) ∩ φ.model.O ⊆ W := by
    rintro z ⟨hz, hzO⟩
    have hcw : ContinuousWithinAt φ.symm (φ.model.O ∩ support (f ∘ φ.symm)) z :=
      (φ.continuousOn_invFun z hzO).mono inter_subset_left
    have h1 := hcw.mem_closure_image hz
    have h2 : φ.symm '' (φ.model.O ∩ support (f ∘ φ.symm)) ⊆ support f := by
      rintro _ ⟨z', hz', rfl⟩; exact hz'.2
    have h3 : φ.symm z ∈ N := hfsupp (closure_mono h2 h1)
    have h4 : φ (φ.symm z) ∈ φ '' N := mem_image_of_mem _ h3
    rw [φ.apply_symm_apply hzO, hWeq] at h4
    exact h4.2
  obtain ⟨g₀, hg₀, hg₀01, hg₀supp, hg₀f⟩ := happ W hWo hWcl (f ∘ φ.symm) hfc
    (fun z _ => hf01 _) hfsupp' ε hε
  set K := closure (φ.model.O ∩ support g₀) with hK
  have hKO : φ.model.O ∩ support g₀ ⊆ φ.model.O ∩ W := fun z hz =>
    ⟨hz.1, hg₀supp ⟨subset_closure hz, hz.1⟩⟩
  have hKN : K ⊆ φ '' N := by
    intro z hz
    have hzO : z ∈ φ.model.O := hWcl (closure_mono hKO hz)
    rw [hWeq]
    exact ⟨hzO, hg₀supp ⟨hz, hzO⟩⟩
  obtain ⟨hBc, hBN⟩ := φ.isClosed_inter_preimage hcl isClosed_closure hKN
  set g : X → ℝ := φ.source.indicator (g₀ ∘ φ) with hgdef
  have hgsupp : support g ⊆ φ.source ∩ φ ⁻¹' K := by
    intro y hy
    have hyφ : y ∈ φ.source := by
      by_contra h; exact hy (indicator_of_notMem h _)
    have hgy : g₀ (φ y) ≠ 0 := by
      have := mem_support.1 hy; rwa [hgdef, indicator_of_mem hyφ] at this
    exact ⟨hyφ, subset_closure ⟨φ.mapsTo_model y hyφ, hgy⟩⟩
  have htsupp : tsupport g ⊆ N := (closure_minimal hgsupp hBc).trans hBN
  refine ⟨g, ?_, fun y => ?_, htsupp, fun y => ?_⟩
  · refine isScSmoothMap_real_of_chart hφ (htsupp.trans hNφ) (hg₀.congr fun z hz => ?_)
    simp only [Function.comp_apply, hgdef, indicator_of_mem (φ.symm_mapsTo hz),
      φ.apply_symm_apply hz]
  · by_cases hy : y ∈ φ.source
    · rw [hgdef, indicator_of_mem hy]; exact hg₀01 _ (φ.mapsTo_model y hy)
    · rw [hgdef, indicator_of_notMem hy]; exact ⟨le_rfl, zero_le_one⟩
  · by_cases hy : y ∈ φ.source
    · have := hg₀f (φ y) (φ.mapsTo_model y hy)
      simp only [Function.comp_apply, φ.symm_apply_apply hy] at this
      rwa [hgdef, indicator_of_mem hy]
    · have hfy : f y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy (hNφ (hfsupp h))
      rw [hgdef, indicator_of_notMem hy, hfy, sub_zero, abs_zero]
      exact hε.le

end Reproved

theorem B_to_A : B → A := by
  intro hB
  -- (i) for an atlas of local models with the approximation property, from B
  have hpou : ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
      {PX : MPolyfold X} {S : Set (MChart X)}, (∀ φ ∈ S, PX.IsChart φ) →
      (∀ x, ∃ φ ∈ S, x ∈ φ.source) → (∀ φ ∈ S, φ.model.HasApproxProperty) →
      PX.AdmitsScPartitionsOfUnity := by
    intro X _ _ _ PX S hS hcov happ
    obtain ⟨At, hAt, hAapp⟩ := (exists_atlas_iff PX _).1 ⟨S, hS, hcov, happ⟩
    exact (hB X PX At hAt hAapp).2
  refine ⟨@exists_small_nhds', @exists_approx', ?_, @hpou⟩
  -- Urysohn functions from a partition of unity subordinate to `{X ∖ s, X ∖ t}`
  intro X _ _ _ PX S hS hcov happ s t hs ht hst
  let V : Bool → Set X := fun b => if b then tᶜ else sᶜ
  have hVo : ∀ b, IsOpen (V b) := by
    rintro (_ | _)
    · exact hs.isOpen_compl
    · exact ht.isOpen_compl
  have hVcov : ⋃ b, V b = univ := by
    refine eq_univ_of_forall fun y => mem_iUnion.2 ?_
    by_cases hy : y ∈ s
    · exact ⟨true, fun hyt => hst.ne_of_mem hy hyt rfl⟩
    · exact ⟨false, hy⟩
  obtain ⟨ρ, hρsub, hρsc⟩ := hpou hS hcov happ Bool V hVo hVcov
  refine ⟨ρ false, hρsc false, fun y hy => ?_, fun y hy => ?_, fun y =>
    ⟨ρ.nonneg false y, ρ.le_one false y⟩⟩
  · exact image_eq_zero_of_notMem_tsupport fun h => hρsub false h hy
  · have h0 : ρ true y = 0 := image_eq_zero_of_notMem_tsupport fun h => hρsub true h hy
    have h1 := ρ.sum_eq_one (mem_univ y)
    rw [finsum_eq_sum_of_fintype, Fintype.sum_bool, h0, zero_add] at h1
    exact h1

#rt_check RoundTrip.V5_56.A_to_B [Polyfold.MChart.exists_small_nhds,
  Polyfold.LocalModel.HasApproxProperty.exists_approx, Polyfold.exists_isScSmoothMap_urysohn,
  Polyfold.admitsScPartitionsOfUnity_of_approx]
#rt_check RoundTrip.V5_56.B_to_A [Polyfold.MChart.exists_small_nhds,
  Polyfold.LocalModel.HasApproxProperty.exists_approx, Polyfold.exists_isScSmoothMap_urysohn,
  Polyfold.admitsScPartitionsOfUnity_of_approx]
#rt_overlap RoundTrip.V5_56.B_to_A [Polyfold.MChart.exists_small_nhds,
  Polyfold.LocalModel.HasApproxProperty.exists_approx, Polyfold.exists_isScSmoothMap_urysohn,
  Polyfold.admitsScPartitionsOfUnity_of_approx]

end RoundTrip.V5_56
