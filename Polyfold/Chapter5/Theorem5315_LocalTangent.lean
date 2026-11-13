import Polyfold.Chapter5.Theorem5315_LocalParam
import Polyfold.Chapter5.Theorem5315_LocalInvariance

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §5.3, the local data of
**Theorem 5.3.15** (p. 223; preprint: Theorem 5.22), second step.  Gap G.48.

# The tangent vectors of a smooth parametrization of a solution set

## The text, paraphrased

(Theorem 3.6.8 (4), p. 136, and the proof of Theorem 5.3.15, pp. 224–227) The solution set `S` of
a section in general position is a manifold with `T_xS = ker f'(x)`; the derivative of `t|S` at
`x` is the restriction of `dt(x)` to `ker f'(x)`.

## What is formalized

* `scDeriv_eq_of_hasFDerivWithinAt`: the chosen derivative of an sc¹ map at a level-`1` point is
  any bounded operator which is its derivative on level `1`.
* `MPolyfold.IsSmoothParam.exists_fderivWithin_eq_scDeriv` (**tangent vectors of a
  parametrization**): let `p : Ω → A ∩ G` be a smooth parametrization (`IsSmoothParam`) and `Q` a
  retract inside `φ(A)` for a chart `φ` around `p(u₀)`.  Every `w ∈ T_zQ` (`z` over `φ(p(u₀))`)
  is the image of a vector `v` of the parameter space: `d(g ∘ p)(u₀) v = D(g ∘ φ⁻¹ ∘ r)(z) w` for
  every sc-smooth function `g` on `X`.
* `StrongBundle.exists_retract_range_eq_linKer`: at a zero in general position, in every strong
  bundle chart, the solution set contains a retract through the point whose tangent space is the
  kernel of the linearization (a form of `exists_tangentSpace_eq_linKer`).
* `StrongBundle.exists_fderivWithin_eq_scDeriv_of_mem_linKer`: the two together: every kernel
  vector `w ∈ ker f'(y)` (in a chart) is `v`-tangent to a smooth parametrization of `S_f`.

## What the text leaves implicit, and the choices made

* A smooth parametrization has a left inverse `q` with sc-smooth components.  The vector is
  `v = D(q ∘ φ⁻¹ ∘ s)(z) w`, `s` a retraction onto `Q`; the identity is the chain rule for
  `g ∘ φ⁻¹ ∘ s = (g ∘ p) ∘ (q ∘ φ⁻¹ ∘ s)` near `z`, and
  `D(g ∘ φ⁻¹ ∘ s)(z) = D(g ∘ φ⁻¹ ∘ r)(z)` on `T_zQ` (`scDeriv_comp_apply_eq_of_retract_subset`).
-/

open Set Function Module Topology Filter
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

/-! ### The derivative at a level-`1` point -/

section DerivTools

variable {E F : ScBanach}

/-- The chosen derivative of an sc¹ map at a level-`1` point `z` is any bounded operator `L` on
`E₀` such that `L ∘ ι` is the derivative of `f ∘ ι` at `z` on level `1`. -/
lemma scDeriv_eq_of_hasFDerivWithinAt {C U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U)
    {f : E 0 → F 0} (hf : IsSc1 U f) {z : E 1} (hz : z ∈ E.lvlSet U 1) {L : E 0 →L[ℝ] F 0}
    (hL : HasFDerivWithinAt (f ∘ E.toBase 1) (L.comp (E.toBase 1)) (E.lvlSet U 1) z) :
    scDeriv U f z = L := by
  apply ContinuousLinearMap.ext_of_comp_toBase_one (E := E)
  exact (hU.isScDomain.uniqueDiffWithinAt 1 z hz).eq
    (hf.isSc1With_scDeriv.hasFDerivWithinAt z hz) hL

end DerivTools

/-! ### Tangent vectors of a smooth parametrization -/

section Tangent

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {A : Set X} {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
  {Ω : Set N} {p : N → X} {q : X → N} {G : Set X}

/-- **The tangent vectors of a smooth parametrization.**  Let `p : Ω → A ∩ G` be a smooth
parametrization, `φ` a chart of `X` around `p(u₀)` with a retraction `R` onto its model, and `S`
a retraction whose retract lies in `φ(A)` and contains `φ(p(u₀))`.  Then every tangent vector
`w` of the retract of `S` at the level-`1` point `z` over `φ(p(u₀))` comes from a vector `v` of
the parameter space: `d(g ∘ p)(u₀) v = D(g ∘ φ⁻¹ ∘ R)(z) w` for every sc-smooth `g : X → ℝ`. -/
theorem MPolyfold.IsSmoothParam.exists_fderivWithin_eq_scDeriv
    (h : PX.IsSmoothParam A Ω p q G) {u₀ : N} (hu₀ : u₀ ∈ Ω) {φ : MChart X} (hφ : PX.IsChart φ)
    (hpφ : p u₀ ∈ φ.source) (R : ScRetraction φ.model.E φ.model.C) (hR : R.retract = φ.model.O)
    (S : ScRetraction φ.model.E φ.model.C) (hS : S.retract ⊆ φ '' (A ∩ φ.source))
    {z : φ.model.E 1} (hz : φ.model.E.toBase 1 z = φ (p u₀)) (hzS : φ (p u₀) ∈ S.retract)
    {w : φ.model.E 0} (hw : w ∈ range (scDeriv S.U S z)) :
    ∃ v : N, ∀ g : X → ℝ, PX.IsScSmoothMap realPolyfold g →
      fderivWithin ℝ (g ∘ p) Ω u₀ v =
        scDeriv (F := ScBanach.const ℝ) R.U ((g ∘ φ.symm) ∘ R) z w := by
  classical
  have hSO : S.retract ⊆ φ.model.O := hS.trans (φ.image_subset_model inter_subset_right)
  have hSR : S.retract ⊆ R.retract := hR ▸ hSO
  have hzS' : φ.model.E.toBase 1 z ∈ S.retract := hz ▸ hzS
  have hzU : z ∈ φ.model.E.lvlSet S.U 1 := S.retract_subset hzS'
  have hmaps : MapsTo S S.U R.U := fun x hx => R.retract_subset (hSR (S.apply_mem_retract hx))
  -- sc-smooth functions read on `S`
  have hgS : ∀ g : X → ℝ, PX.IsScSmoothMap realPolyfold g →
      IsSc1 (F := ScBanach.const ℝ) S.U ((g ∘ φ.symm) ∘ S) ∧
        scDeriv (F := ScBanach.const ℝ) S.U ((g ∘ φ.symm) ∘ S) z w =
          scDeriv (F := ScBanach.const ℝ) R.U ((g ∘ φ.symm) ∘ R) z w := by
    intro g hg
    have hgR : IsSc1 (F := ScBanach.const ℝ) R.U ((g ∘ φ.symm) ∘ R) :=
      ((hg.real_chart hφ).comp_isScSmooth R hR).isSc1
    have hcomp : IsSc1 (F := ScBanach.const ℝ) S.U (((g ∘ φ.symm) ∘ R) ∘ S) :=
      (theorem_1_3_1 S.relOpen R.relOpen S.isSc1 hgR hmaps).1
    have heq : EqOn (((g ∘ φ.symm) ∘ R) ∘ S) ((g ∘ φ.symm) ∘ S) S.U := fun x hx => by
      simp only [Function.comp_apply,
        R.apply_eq_self_of_mem_retract (hSR (S.apply_mem_retract hx))]
    exact ⟨(hcomp.isSc1With_scDeriv.congr heq).isSc1,
      scDeriv_comp_apply_eq_of_retract_subset S R hSR hgR (fun _ _ => rfl) hzS' hw⟩
  -- the coordinates of `κ = q ∘ φ⁻¹ ∘ S`
  set b := Module.finBasis ℝ N with hb
  set gi : Fin (finrank ℝ N) → X → ℝ := fun i y =>
    (LinearMap.toContinuousLinearMap (b.coord i)) (q y) with hgi
  have hgis : ∀ i, PX.IsScSmoothMap realPolyfold (gi i) := fun i =>
    h.smooth_q (LinearMap.toContinuousLinearMap (b.coord i))
  set Di : Fin (finrank ℝ N) → φ.model.E 0 →L[ℝ] ℝ := fun i =>
    scDeriv (F := ScBanach.const ℝ) S.U ((gi i ∘ φ.symm) ∘ S) z with hDi
  set κ : φ.model.E 0 → N := fun x => q (φ.symm (S x)) with hκ
  set M : φ.model.E 0 →L[ℝ] N := ∑ i, (Di i).smulRight (b i) with hM
  have hκsum : κ ∘ φ.model.E.toBase 1 =
      fun y => ∑ i, ((gi i ∘ φ.symm) ∘ S) (φ.model.E.toBase 1 y) • b i := by
    funext y
    exact (b.sum_repr (q (φ.symm (S (φ.model.E.toBase 1 y))))).symm
  have hκd : HasFDerivWithinAt (κ ∘ φ.model.E.toBase 1) (M.comp (φ.model.E.toBase 1))
      (φ.model.E.lvlSet S.U 1) z := by
    rw [hκsum]
    have hsum := HasFDerivWithinAt.fun_sum (u := Finset.univ) fun i _ =>
      (((hgS (gi i) (hgis i)).1.isSc1With_scDeriv.hasFDerivWithinAt z hzU).smul_const (b i))
    refine hsum.congr_fderiv ?_
    ext y
    simp [hM, hDi]
  have hκz : (κ ∘ φ.model.E.toBase 1) z = u₀ := by
    change q (φ.symm (S (φ.model.E.toBase 1 z))) = u₀
    rw [S.apply_eq_self_of_mem_retract hzS', hz, φ.symm_apply_apply hpφ, h.left_inv u₀ hu₀]
  -- near `z`, `φ⁻¹ ∘ S` stays in `G`
  set Fm : φ.model.E 1 → X := fun y => φ.symm (S (φ.model.E.toBase 1 y)) with hFm
  have hFc : ContinuousOn Fm (φ.model.E.lvlSet S.U 1) := by
    have h1 : ContinuousOn S S.U := S.isSc1.isSc0.continuousOn_base
    have h2 : ContinuousOn (fun x => φ.symm (S x)) S.U :=
      φ.continuousOn_invFun.comp h1 fun x hx => hSO (S.apply_mem_retract hx)
    exact h2.comp (φ.model.E.toBase 1).continuous.continuousOn fun y hy => hy
  have hFz : Fm z = p u₀ := by
    change φ.symm (S (φ.model.E.toBase 1 z)) = p u₀
    rw [S.apply_eq_self_of_mem_retract hzS', hz, φ.symm_apply_apply hpφ]
  have hnhds : φ.model.E.lvlSet S.U 1 ∩ Fm ⁻¹' G ∈ 𝓝[φ.model.E.lvlSet S.U 1] z :=
    inter_mem self_mem_nhdsWithin
      ((hFc z hzU).preimage_mem_nhdsWithin (h.isOpen_G.mem_nhds (hFz ▸ h.mem_G hu₀)))
  have hFA : ∀ y ∈ φ.model.E.lvlSet S.U 1, Fm y ∈ A := fun y hy => by
    obtain ⟨a, ha, hay⟩ := hS (S.apply_mem_retract hy)
    change φ.symm (S (φ.model.E.toBase 1 y)) ∈ A
    rw [← hay, φ.symm_apply_apply ha.2]; exact ha.1
  refine ⟨∑ i, Di i w • b i, fun g hg => ?_⟩
  obtain ⟨hg1, hgeq⟩ := hgS g hg
  rw [← hgeq]
  have hgp : HasFDerivWithinAt (g ∘ p) (fderivWithin ℝ (g ∘ p) Ω u₀) Ω
      ((κ ∘ φ.model.E.toBase 1) z) := by
    rw [hκz]
    exact (((h.smooth_p g hg).differentiableOn (by simp)) u₀ hu₀).hasFDerivWithinAt
  have hmapsΩ : MapsTo (κ ∘ φ.model.E.toBase 1) (φ.model.E.lvlSet S.U 1 ∩ Fm ⁻¹' G) Ω := fun y hy =>
    (h.p_q (hFA y hy.1) hy.2).1
  have hcomp := hgp.comp z (hκd.mono inter_subset_left) hmapsΩ
  have hcongr : HasFDerivWithinAt (((g ∘ φ.symm) ∘ S) ∘ φ.model.E.toBase 1)
      ((fderivWithin ℝ (g ∘ p) Ω u₀).comp (M.comp (φ.model.E.toBase 1)))
      (φ.model.E.lvlSet S.U 1 ∩ Fm ⁻¹' G) z := by
    refine hcomp.congr (fun y hy => ?_) ?_
    · change g (φ.symm (S (φ.model.E.toBase 1 y))) = g (p (q (φ.symm (S (φ.model.E.toBase 1 y)))))
      rw [(h.p_q (hFA y hy.1) hy.2).2]
    · change g (φ.symm (S (φ.model.E.toBase 1 z))) = g (p (q (φ.symm (S (φ.model.E.toBase 1 z)))))
      rw [(h.p_q (hFA z hzU) (by rw [hFz]; exact h.mem_G hu₀)).2]
  have hfull := hcongr.mono_of_mem_nhdsWithin hnhds
  have hD := scDeriv_eq_of_hasFDerivWithinAt (F := ScBanach.const ℝ) S.relOpen hg1 hzU
    (L := (fderivWithin ℝ (g ∘ p) Ω u₀).comp M) hfull
  rw [hD]
  simp [hM]

end Tangent

/-! ### The kernel of the linearization as the tangent space of a retract -/

section Kernel

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

/-- **`ker f'(y)` is the tangent space of a retract inside the solution set** (2021 Theorem
3.6.8 (4), p. 136, in a chart): at a zero `y` in general position, in every strong bundle chart
`c` around `y`, there is a retraction `S` whose retract lies in `φ(S_f)`, contains `φ(y)`, and
has `T_zS = ker Lin(z)` at the level-`1` point `z` over `φ(y)`
(`exists_isGeneralPositionGerm_iff`). -/
theorem StrongBundle.exists_retract_range_eq_linKer (hf : B.IsScFredholmSectionTame f) {y : X}
    (hy0 : IsZeroAt P f y) (hgp : B.IsGeneralPositionGerm f y) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) (hyc : y ∈ c.φ.source) {z : c.φ.model.E 1}
    (hz : c.φ.model.E.toBase 1 z = c.φ y) :
    ∃ S : ScRetraction c.φ.model.E c.φ.model.C,
      S.retract ⊆ c.φ '' (solutionSet P f ∩ c.φ.source) ∧ c.φ y ∈ S.retract ∧
        range (scDeriv S.U S z) = (c.linKer f z : Set (c.φ.model.E 0)) := by
  have hgood := hgp.isGoodPositionGermTame hf hy0
  obtain ⟨V, -, h0V, -, hAV, -, hidV⟩ := exists_isGeneralPositionGerm_iff hf hgood hy0
  have hyA : y ∈ solutionSet P f ∩ V := ⟨hy0, h0V⟩
  set d := hAV.data hyA with hd
  have hyG : y ∈ d.toSubData.shrink c.φ :=
    d.toSubData.mem_shrink c.φ hyA (hAV.mem_data_V hyA) hyc
  have hT0 := hidV _ h0V hy0 c hc hyc _ (d.toSubData.isOpen_shrink c.φ)
    (d.toSubData.shrink_subset_source c.φ) hyG
    (d.toSubData.isScRetract_image c.φ c.isChart) z hz
  obtain ⟨S, hS⟩ := d.toSubData.isScRetract_image c.φ c.isChart
  have hyS : c.φ y ∈ S.retract := by rw [hS]; exact ⟨y, ⟨hyG, hyA⟩, rfl⟩
  have hzS : z ∈ c.φ.model.E.lvlSet S.retract 1 := by
    rw [ScBanach.mem_lvlSet, hz]; exact hyS
  refine ⟨S, ?_, hyS, ?_⟩
  · rw [hS]
    rintro _ ⟨a, ⟨haG, haA⟩, rfl⟩
    exact ⟨a, ⟨haA.1, d.toSubData.shrink_subset_source c.φ haG⟩, rfl⟩
  · rw [← tangentSpace_eq_range S hzS, hS, hT0]

variable {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
  {Ω : Set N} {p : N → X} {q : X → N} {G : Set X}

/-- **The kernel vectors are tangent to every smooth parametrization of the solution set.**
Let `p : Ω → S_f ∩ G` be a smooth parametrization around the zero `y = p(u₀)` in general
position.  In every strong bundle chart `c` around `y`, every `w ∈ ker Lin(z)` comes from a
vector `v` of the parameter space: `d(g ∘ p)(u₀) v = D(g ∘ φ⁻¹ ∘ r)(z) w` for every sc-smooth
function `g` on `X`. -/
theorem StrongBundle.exists_fderivWithin_eq_scDeriv_of_mem_linKer
    (hf : B.IsScFredholmSectionTame f) {y : X} (hy0 : IsZeroAt P f y)
    (hgp : B.IsGeneralPositionGerm f y) (h : PX.IsSmoothParam (solutionSet P f) Ω p q G)
    {u₀ : N} (hu₀ : u₀ ∈ Ω) (hpu : p u₀ = y) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hyc : y ∈ c.φ.source) {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    {w : c.φ.model.E 0} (hw : w ∈ c.linKer f z) :
    ∃ v : N, ∀ g : X → ℝ, PX.IsScSmoothMap realPolyfold g →
      fderivWithin ℝ (g ∘ p) Ω u₀ v =
        scDeriv (F := ScBanach.const ℝ) c.U ((g ∘ c.φ.symm) ∘ r c.R) z w := by
  obtain ⟨S, hS, hyS, hrange⟩ := StrongBundle.exists_retract_range_eq_linKer hf hy0 hgp hc hyc hz
  subst hpu
  exact h.exists_fderivWithin_eq_scDeriv hu₀ c.isChart hyc
    (c.isRetraction.baseRetraction c.relOpen) c.base_retract S hS hz hyS (hrange ▸ hw)

end Kernel

/-! ### A function with an extremum: the derivative vanishes on the reduced directions -/

section Extremum

variable {E : ScBanach} {n : ℕ} {W : ScBanach}

/-- The level-`1` vectors of `E_x` are dense in `E_x` (for a presentation `T : E ≅ ℝⁿ ⊕ W` of a
partial quadrant, `E_x = {v | (Tv)ᵢ = 0 whenever (Tx)ᵢ = 0}`). -/
lemma mem_closure_levelOne_minimalSubspaceWith
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (x : E 0) {e : E 0}
    (he : e ∈ minimalSubspaceWith T x) :
    e ∈ closure (E.toBase 1 '' {e₁ : E 1 | E.toBase 1 e₁ ∈ minimalSubspaceWith T x}) := by
  set a : Fin n → ℝ := (T 0 e).1 with ha
  set w : W 0 := (T 0 e).2 with hw
  set Fm : W 0 → E 0 := fun w' => (T 0).symm ((a, w') : ((ScBanach.const (Fin n → ℝ)).prod W) 0)
    with hFm
  have hFc : Continuous Fm :=
    (T 0).symm.continuous.comp (Continuous.prodMk continuous_const continuous_id)
  have hFw : Fm w = e := (T 0).symm_apply_apply e
  have hdense : DenseRange (W.toBase 1) := W.denseRange_incl 0
  have h1 : e ∈ closure (Fm '' range (W.toBase 1)) :=
    image_closure_subset_closure_image hFc ⟨w, hdense w, hFw⟩
  refine closure_mono ?_ h1
  rintro _ ⟨_, ⟨w₁, rfl⟩, rfl⟩
  have hb : E.toBase 1 ((T 1).symm ((a, w₁) : ((ScBanach.const (Fin n → ℝ)).prod W) 1)) =
      Fm (W.toBase 1 w₁) := by
    rw [T.symm_toBase_comm 1, ScBanach.prod_toBase, ScBanach.const_toBase]
  refine ⟨(T 1).symm ((a, w₁) : ((ScBanach.const (Fin n → ℝ)).prod W) 1), ?_, hb⟩
  change E.toBase 1 _ ∈ minimalSubspaceWith T x
  rw [hb, mem_minimalSubspaceWith]
  intro i hi
  have h2 := (mem_minimalSubspaceWith T).1 he i hi
  change (T 0 ((T 0).symm ((a, W.toBase 1 w₁) : ((ScBanach.const (Fin n → ℝ)).prod W) 0))).1 i = 0
  rw [(T 0).apply_symm_apply]
  exact h2

/-- **The derivative of a function with an extremum vanishes on the reduced directions.**  Let
`U` be relatively open in the partial quadrant `C = T⁻¹([0, ∞)ⁿ ⊕ W)`, `τ : U → ℝ` sc¹, and
`z ∈ U₁` a point where `τ` has a minimum or a maximum on `U`.  Then `Dτ(z)` vanishes on
`E_z = {e | (Te)ᵢ = 0 whenever (Tz)ᵢ = 0}`: in these directions one can move both ways inside
`C` (on level `1`; then by density).  This holds at corner points of every index. -/
theorem scDeriv_eq_zero_of_extremum (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    {C U : Set (E 0)} (hT : C = T 0 ⁻¹' quadrant n W 0) (hU : IsRelOpenInQuadrant E C U)
    {τ : E 0 → ℝ} (hτ : IsSc1 (F := ScBanach.const ℝ) U τ) {z : E 1} (hz : z ∈ E.lvlSet U 1)
    (hext : (∀ u ∈ U, τ (E.toBase 1 z) ≤ τ u) ∨ (∀ u ∈ U, τ u ≤ τ (E.toBase 1 z)))
    {e : E 0} (he : e ∈ minimalSubspaceWith T (E.toBase 1 z)) :
    scDeriv (F := ScBanach.const ℝ) U τ z e = 0 := by
  set L : E 0 →L[ℝ] ℝ := scDeriv (F := ScBanach.const ℝ) U τ z with hL
  have hlevel : ∀ e₁ : E 1, E.toBase 1 e₁ ∈ minimalSubspaceWith T (E.toBase 1 z) →
      L (E.toBase 1 e₁) = 0 := by
    intro e₁ he₁
    obtain ⟨O, hO, hUO⟩ := hU.relOpen
    have hzU : E.toBase 1 z ∈ U := hz
    set γ : ℝ → E 1 := fun s => z + s • e₁ with hγ
    have hγ0 : γ 0 = z := by simp [hγ]
    have hγd : HasDerivAt γ e₁ 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const e₁).const_add z
      simpa [hγ] using this
    have hbase : ∀ s : ℝ, E.toBase 1 (γ s) = E.toBase 1 z + s • E.toBase 1 e₁ := fun s => by
      simp [hγ]
    -- the line stays in `U` near `0`
    have hevO : ∀ᶠ s in 𝓝 (0 : ℝ), E.toBase 1 (γ s) ∈ O := by
      have hc : ContinuousAt (fun s : ℝ => E.toBase 1 (γ s)) 0 :=
        (E.toBase 1).continuous.continuousAt.comp hγd.continuousAt
      refine hc.eventually (hO.mem_nhds ?_)
      change E.toBase 1 (γ 0) ∈ O
      rw [hγ0]
      exact (hUO ▸ hzU : E.toBase 1 z ∈ O ∩ C).1
    have hzC : E.toBase 1 z ∈ C := (hUO ▸ hzU : E.toBase 1 z ∈ O ∩ C).2
    have hevC : ∀ᶠ s in 𝓝 (0 : ℝ), E.toBase 1 (γ s) ∈ C := by
      have hcoord : ∀ i, ∀ᶠ s in 𝓝 (0 : ℝ), 0 ≤ (T 0 (E.toBase 1 (γ s))).1 i := by
        intro i
        have hval : ∀ s : ℝ, (T 0 (E.toBase 1 (γ s))).1 i =
            (T 0 (E.toBase 1 z)).1 i + s * (T 0 (E.toBase 1 e₁)).1 i := fun s => by
          rw [hbase, map_add, map_smul]; rfl
        by_cases hi : (T 0 (E.toBase 1 z)).1 i = 0
        · refine Eventually.of_forall fun s => ?_
          rw [hval, hi, (mem_minimalSubspaceWith T).1 he₁ i hi]; simp
        · have hpos : 0 < (T 0 (E.toBase 1 z)).1 i :=
            lt_of_le_of_ne ((hT ▸ hzC : E.toBase 1 z ∈ T 0 ⁻¹' quadrant n W 0) i) (Ne.symm hi)
          have hc : ContinuousAt (fun s : ℝ =>
              (T 0 (E.toBase 1 z)).1 i + s * (T 0 (E.toBase 1 e₁)).1 i) 0 := by fun_prop
          have := hc.eventually (lt_mem_nhds (by simpa using hpos))
          filter_upwards [this] with s hs
          rw [hval]; exact hs.le
      filter_upwards [eventually_all.2 hcoord] with s hs
      rw [hT]; exact hs
    have hev : ∀ᶠ s in 𝓝 (0 : ℝ), γ s ∈ E.lvlSet U 1 := by
      filter_upwards [hevO, hevC] with s h1 h2
      change E.toBase 1 (γ s) ∈ U
      rw [hUO]; exact ⟨h1, h2⟩
    have hF : HasFDerivWithinAt (τ ∘ E.toBase 1) (L.comp (E.toBase 1)) (E.lvlSet U 1) (γ 0) := by
      rw [hγ0]; exact hτ.isSc1With_scDeriv.hasFDerivWithinAt z hz
    have hd : HasDerivAt ((τ ∘ E.toBase 1) ∘ γ) (L (E.toBase 1 e₁)) 0 :=
      (hF.comp_hasDerivWithinAt (0 : ℝ) hγd.hasDerivWithinAt
        (s := {s | γ s ∈ E.lvlSet U 1}) fun s hs => hs).hasDerivAt hev
    have hextr : IsLocalExtr ((τ ∘ E.toBase 1) ∘ γ) 0 := by
      rcases hext with hmin | hmax
      · left
        filter_upwards [hev] with s hs
        change τ (E.toBase 1 (γ 0)) ≤ τ (E.toBase 1 (γ s))
        rw [hγ0]; exact hmin _ hs
      · right
        filter_upwards [hev] with s hs
        change τ (E.toBase 1 (γ s)) ≤ τ (E.toBase 1 (γ 0))
        rw [hγ0]; exact hmax _ hs
    exact hextr.hasDerivAt_eq_zero hd
  have hclosed : IsClosed {v : E 0 | L v = 0} := isClosed_eq L.continuous continuous_const
  have hsub : E.toBase 1 '' {e₁ : E 1 | E.toBase 1 e₁ ∈ minimalSubspaceWith T (E.toBase 1 z)} ⊆
      {v : E 0 | L v = 0} := by
    rintro _ ⟨e₁, he₁, rfl⟩
    exact hlevel e₁ he₁
  exact closure_minimal hsub hclosed (mem_closure_levelOne_minimalSubspaceWith T _ he)

end Extremum

/-! ### The derivative of a function in two charts -/

section ChartChange

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- **The derivative of a function in two charts.**  Let `φ`, `φ'` be charts around `x` with
retractions `R`, `R'` onto their models and level-`1` points `z`, `z'` over `φ(x)`, `φ'(x)`.
For every `v` there is a tangent vector `w ∈ T_zO` with
`D(g ∘ φ⁻¹ ∘ R)(z) w = D(g ∘ φ'⁻¹ ∘ R')(z') v` for every sc-smooth `g : X → ℝ` (`w` is the image
of `v` under the derivative of the transition map). -/
theorem MPolyfold.exists_scDeriv_eq_chart_change {φ φ' : MChart X} (hφ : PX.IsChart φ)
    (hφ' : PX.IsChart φ') {x : X} (hx : x ∈ φ.source) (hx' : x ∈ φ'.source)
    (R : ScRetraction φ.model.E φ.model.C) (hR : R.retract = φ.model.O)
    (R' : ScRetraction φ'.model.E φ'.model.C) (hR' : R'.retract = φ'.model.O)
    {z : φ.model.E 1} (hz : φ.model.E.toBase 1 z = φ x) {z' : φ'.model.E 1}
    (hz' : φ'.model.E.toBase 1 z' = φ' x) (v : φ'.model.E 0) :
    ∃ w ∈ range (scDeriv R.U R z), ∀ g : X → ℝ, PX.IsScSmoothMap realPolyfold g →
      scDeriv (F := ScBanach.const ℝ) R.U ((g ∘ φ.symm) ∘ R) z w =
        scDeriv (F := ScBanach.const ℝ) R'.U ((g ∘ φ'.symm) ∘ R') z' v := by
  have hbase : φ'.Compatible φ := MPolyfold.IsChart.compatible PX hφ' hφ
  obtain ⟨W', hW'o, hW'⟩ := φ'.exists_isOpen_image_eq (s := φ'.source ∩ φ.source)
    inter_subset_left (φ'.isOpen_source.inter φ.isOpen_source)
  set S := R'.restrict hW'o with hSdef
  have hSret : S.retract = φ'.overlap φ := by rw [R'.restrict_retract, hR']; exact hW'.symm
  set τ := φ'.transition φ with hτ
  have hτS : IsSc1 S.U (τ ∘ S) := (hbase.1.comp_isScSmooth S hSret).isSc1
  have hzR : φ.model.E.toBase 1 z ∈ R.retract := by rw [hz, hR]; exact φ.mapsTo_model x hx
  have hzU : z ∈ φ.model.E.lvlSet R.U 1 := R.retract_subset hzR
  have hz'S : φ'.model.E.toBase 1 z' ∈ S.retract := by
    rw [hSret, hz']; exact φ'.mem_overlap φ hx' hx
  have hz'U : z' ∈ φ'.model.E.lvlSet S.U 1 := S.retract_subset hz'S
  have hmaps : MapsTo (τ ∘ S) S.U R.U := fun u hu => by
    have h1 : S u ∈ φ'.overlap φ := hSret ▸ S.apply_mem_retract hu
    have h2 := φ'.transition_mapsTo φ h1
    exact R.retract_subset (hR ▸ φ.overlap_subset φ' h2)
  have hlev : levelMap (τ ∘ S) 1 z' = z := by
    apply levelMap_eq_of_toBase_eq
    change φ.model.E.toBase 1 z = φ'.transition φ (S (φ'.model.E.toBase 1 z'))
    rw [S.apply_eq_self_of_mem_retract hz'S, hz', φ'.transition_apply φ hx', hz]
  set w₁ := scDeriv S.U (τ ∘ S) z' v with hw₁
  refine ⟨scDeriv R.U R z w₁, ⟨w₁, rfl⟩, fun g hg => ?_⟩
  have hgR : IsSc1 (F := ScBanach.const ℝ) R.U ((g ∘ φ.symm) ∘ R) :=
    ((hg.real_chart hφ).comp_isScSmooth R hR).isSc1
  have hgR' : IsSc1 (F := ScBanach.const ℝ) R'.U ((g ∘ φ'.symm) ∘ R') :=
    ((hg.real_chart hφ').comp_isScSmooth R' hR').isSc1
  -- `D(g_R)(z) ∘ DR(z) = D(g_R)(z)`
  have h1 : scDeriv (F := ScBanach.const ℝ) R.U ((g ∘ φ.symm) ∘ R) z (scDeriv R.U R z w₁) =
      scDeriv (F := ScBanach.const ℝ) R.U ((g ∘ φ.symm) ∘ R) z w₁ := by
    have hch := scDeriv_comp_apply' R.relOpen R.relOpen R.isSc1 hgR R.mapsTo hzU w₁
    have hlevR : levelMap R 1 z = z :=
      levelMap_eq_of_toBase_eq (R.apply_eq_self_of_mem_retract hzR).symm
    rw [hlevR] at hch
    rw [hch]
    have hcomp : IsSc1 (F := ScBanach.const ℝ) R.U (((g ∘ φ.symm) ∘ R) ∘ R) :=
      (theorem_1_3_1 R.relOpen R.relOpen R.isSc1 hgR R.mapsTo).1
    exact congrArg (fun A : φ.model.E 0 →L[ℝ] ℝ => A w₁)
      (scDeriv_eq_of_eqOn_relOpen R.relOpen hcomp hgR subset_rfl subset_rfl
        (fun u hu => by simp only [Function.comp_apply, R.idem u hu]) hzU)
  rw [h1]
  -- the chain rule through the transition
  have hch := scDeriv_comp_apply' S.relOpen R.relOpen hτS hgR hmaps hz'U v
  rw [hlev] at hch
  rw [hch]
  have hcomp : IsSc1 (F := ScBanach.const ℝ) S.U (((g ∘ φ.symm) ∘ R) ∘ (τ ∘ S)) :=
    (theorem_1_3_1 S.relOpen R.relOpen hτS hgR hmaps).1
  have heq : EqOn (((g ∘ φ.symm) ∘ R) ∘ (τ ∘ S)) ((g ∘ φ'.symm) ∘ R') S.U := fun u hu => by
    have h1 : S u ∈ φ'.overlap φ := hSret ▸ S.apply_mem_retract hu
    obtain ⟨a, ha, hau⟩ := h1
    have h2 : τ (S u) = φ a := by rw [← hau]; exact φ'.transition_apply φ ha.1
    have h3 : R (φ a) = φ a :=
      R.apply_eq_self_of_mem_retract (hR ▸ φ.mapsTo_model a ha.2)
    change g (φ.symm (R (τ (S u)))) = g (φ'.symm (R' u))
    rw [h2, h3, φ.symm_apply_apply ha.2]
    change g a = g (φ'.symm (S u))
    rw [← hau, φ'.symm_apply_apply ha.1]
  exact congrArg (fun A : φ'.model.E 0 →L[ℝ] ℝ => A v)
    (scDeriv_eq_of_eqOn_relOpen S.relOpen hcomp hgR' subset_rfl inter_subset_left heq hz'U)

end ChartChange

end Polyfold
