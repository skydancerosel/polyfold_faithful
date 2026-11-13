import Polyfold.Chapter6.GapP1_SmoothL1
import Polyfold.Chapter6.GapP1_SmoothL2
import Polyfold.Chapter6.SolutionManifoldFamily2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, **Lemma 6.6.5**
(p. 265; preprint Lemma 6.30, p. 222): **`L` is a smooth vector bundle**.  Gap G.62, rows V6.34,
V6.42.

# Smooth frames of the kernels along an sc-smooth family of zeros

## The text, paraphrased

(Lemma 6.6.5) Along the family `t ↦ (t, φ(t), 0)` the kernels `L_t = ker F_t'(φ(t), 0)`,
the tangent spaces of the fibres `S_t` of the solution set, form a smooth vector bundle `L` over
`[0, 1]`.

## What is formalized

* `isScSmooth_chart_comp_of_isOpen`: an sc-smooth map `Γ : ℝⁿ → X`, read in a chart `φ`, is
  an sc-smooth map `q ↦ φ(Γ(q))` on every open set of `ℝⁿ` that `Γ` maps into the chart domain.
* **`exists_local_smooth_frame_linKer`** (the smooth form of `exists_local_frame_linKer`): for an
  sc-Fredholm section with tame germ data, a chart `c` and an sc-smooth family `Γ : ℝⁿ → X` of
  zeros in good position, read at the level-`1` points `z_q` over `φ(Γ(q))`, the kernels
  `ker Lin(z_q)` have, near every point, a `C^∞` frame `q ↦ e_i(q) ∈ E₀` consisting of smooth
  points, and `C^∞` into every level `E_m`.  The frame is `e_i(q) = DS(z_q) b_i` for an
  sc-retraction `S` onto the solution set (Theorem 3.6.8) and a basis `b` of one kernel:
  `b_i ∈ E_∞` (`apply_mem_smooth_of_finiteDimensional`), so `q ↦ (z_q, b_i)` is sc-smooth into `TE`
  (`isScSmooth_tangentLift`), and the tangent map `TS` is sc-smooth; an sc-smooth map from `ℝⁿ`
  is `C^∞` (`IsScSmooth.contDiffOn_const`).
* **`lemma_6_6_5_smoothBundle`** (**`L` is a smooth vector bundle**): in the setting of
  `exists_isStabKernels` (`Φ([0, 1]ⁿ)` in the domain of a chart `c`, `f + S = 0` along `Φ` and
  property (P) near `[0, 1]ⁿ`), there are an open connected `V ⊇ [0, 1]ⁿ` and a smooth family of
  subspaces over the manifold `V` (`SmoothSubspaceFamily`) whose fibre at `q` is
  `L_q = ker F'(0, (q, z_q)) ∩ {dq = 0}` in the product chart `χ` (the slice kernel of the text, by
  `linKer_inf_ker_sliceProj_eq_map`).  It is a Mathlib `C^∞` vector bundle over `V`
  (`ContMDiffVectorBundle ∞`, `SmoothSubspaceFamily.contMDiffVectorBundle`).
-/

open Set Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {g : X → Y}

/-- An open subset of `ℝⁿ` is an sc-domain of the constant structure. -/
theorem isScDomain_rn_of_isOpen {n : ℕ} {V : Set (Fin n → ℝ)} (hV : IsOpen V) :
    IsScDomain (rnSc n) V :=
  (⟨isPartialQuadrant_univ _, V, hV, (inter_univ _).symm⟩ :
    IsRelOpenInQuadrant (rnSc n) univ V).isScDomain

/-- **An sc-smooth map from `ℝⁿ` read in a chart is sc-smooth**: for an sc-smooth `Γ : ℝⁿ → X`, a
chart `φ` and an open `V` with `Γ(V) ⊆ dom φ`, `q ↦ φ(Γ(q))` is sc-smooth on `V`. -/
theorem isScSmooth_chart_comp_of_isOpen {n : ℕ} {Γ : (Fin n → ℝ) → X}
    (hΓ : (rnPolyfold n).IsScSmoothMap PX Γ) {φ : MChart X} (hφ : PX.IsChart φ)
    {V : Set (Fin n → ℝ)} (hV : IsOpen V) (hVφ : ∀ q ∈ V, Γ q ∈ φ.source) :
    IsScSmooth (E := rnSc n) (F := φ.model.E) V fun q => φ (Γ q) := by
  have hrel : IsRelOpenInQuadrant (rnSc n) univ V :=
    ⟨isPartialQuadrant_univ _, V, hV, (inter_univ _).symm⟩
  have h1 := hΓ.smooth (rnChart n 0) φ (isChart_rnChart 0) hφ V hV
    (fun _ _ => ⟨mem_univ _, mem_univ _⟩) hVφ
  have himg : (rnChart n 0 : (Fin n → ℝ) → (Fin n → ℝ)) '' V = V := by
    have : (rnChart n 0 : (Fin n → ℝ) → (Fin n → ℝ)) = id :=
      funext fun q => by rw [rnChart_apply, sub_zero]; rfl
    rw [this]; exact image_id V
  have := h1.comp_isScSmooth (ScRetraction.id hrel) (by rw [himg]; exact image_id _)
  refine this.congr hrel.isScDomain fun q _ => ?_
  change φ (Γ ((rnChart n 0).symm q)) = φ (Γ q)
  rw [rnChart_symm_apply, add_zero]

open StrongRetr in
/-- **Lemma 6.6.5, near one point, with smooth frames**: for an sc-Fredholm section with tame
germ data, a chart `c`, an sc-smooth `Γ : ℝⁿ → X` mapping an open `V` into the chart domain, with
`g(Γ(q)) = 0` and `(g, Γ(q))` in good position for `q ∈ V`, and level-`1` points `z_q` over
`φ(Γ(q))`: near every `q₀ ∈ V` the kernels `ker Lin(z_q)` have one dimension `d` and a `C^∞` frame
`e : ℝⁿ → E₀` of smooth points, which is also `C^∞` into every level `E_m`. -/
theorem exists_local_smooth_frame_linKer {n : ℕ} (hg : B.IsScFredholmSectionTame g)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) {Γ : (Fin n → ℝ) → X}
    (hΓ : (rnPolyfold n).IsScSmoothMap PX Γ) {V : Set (Fin n → ℝ)} (hV : IsOpen V)
    (hVc : ∀ q ∈ V, Γ q ∈ c.φ.source) (hy0 : ∀ q ∈ V, IsZeroAt P g (Γ q))
    (hgp : ∀ q ∈ V, B.IsGoodPositionGermTame g (Γ q)) (z : (Fin n → ℝ) → c.φ.model.E 1)
    (hzy : ∀ q ∈ V, c.φ.model.E.toBase 1 (z q) = c.φ (Γ q)) {q₀ : Fin n → ℝ} (hq₀ : q₀ ∈ V) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ q₀ ∈ U ∧ U ⊆ V ∧ ∃ d : ℕ,
      (∀ q ∈ U, FiniteDimensional ℝ (c.linKer g (z q)) ∧
        Module.finrank ℝ (c.linKer g (z q)) = d) ∧
      ∃ e : Fin d → (Fin n → ℝ) → c.φ.model.E 0, (∀ i, ContDiffOn ℝ ∞ (e i) U) ∧
        (∀ i m, ∃ em : (Fin n → ℝ) → c.φ.model.E m, ContDiffOn ℝ ∞ em U ∧
          ∀ q ∈ U, c.φ.model.E.toBase m (em q) = e i q) ∧
        ∀ q ∈ U, (∀ i, e i q ∈ c.linKer g (z q) ∧ e i q ∈ c.φ.model.E.smooth) ∧
          LinearIndependent ℝ fun i => e i q := by
  classical
  have hΓc : Continuous Γ := continuousOn_univ.1 hΓ.continuousOn
  obtain ⟨Vx, d, hVxo, hVx₀, hind⟩ :=
    theorem_3_6_8_index_locally_constant hg (hgp q₀ hq₀) (hy0 q₀ hq₀)
  obtain ⟨V', hV'o, hV'₀, hall, hid⟩ := exists_tangentSpace_eq_linKer hg (hgp q₀ hq₀) (hy0 q₀ hq₀)
  have hA : PX.IsSmoothSubmanifold (solutionSet P g ∩ V') :=
    StrongBundle.isSmoothSubmanifold_solutionSet_inter hg.isScSmooth.1 hV'o hall
  have hyA : Γ q₀ ∈ solutionSet P g ∩ V' := ⟨hy0 q₀ hq₀, hV'₀⟩
  set G := (hA.data hyA).toSubData.shrink c.φ with hGdef
  have hGo : IsOpen G := (hA.data hyA).toSubData.isOpen_shrink c.φ
  have hGc : G ⊆ c.φ.source := (hA.data hyA).toSubData.shrink_subset_source c.φ
  have hG₀ : Γ q₀ ∈ G :=
    (hA.data hyA).toSubData.mem_shrink c.φ hyA (hA.mem_data_V hyA) (hVc q₀ hq₀)
  have hQ : IsScRetract c.φ.model.E c.φ.model.C (c.φ '' (G ∩ (solutionSet P g ∩ V'))) :=
    (hA.data hyA).toSubData.isScRetract_image c.φ c.isChart
  obtain ⟨S, hS⟩ := id hQ
  set U₀ := V ∩ Γ ⁻¹' (G ∩ V' ∩ Vx) with hU₀def
  have hU₀o : IsOpen U₀ := hV.inter (((hGo.inter hV'o).inter hVxo).preimage hΓc)
  have hq₀U₀ : q₀ ∈ U₀ := ⟨hq₀, ⟨hG₀, hV'₀⟩, hVx₀⟩
  have hU₀V : U₀ ⊆ V := inter_subset_left
  have hU₀d : IsScDomain (rnSc n) U₀ := isScDomain_rn_of_isOpen hU₀o
  -- the chart reading `H(q) = φ(Γ(q))` and its level-`1` lift
  set H : (Fin n → ℝ) → c.φ.model.E 0 := fun q => c.φ (Γ q) with hHdef
  have hH : IsScSmooth (E := rnSc n) U₀ H :=
    isScSmooth_chart_comp_of_isOpen hΓ c.isChart hU₀o fun q hq => hVc q hq.1
  have hH0 := hH.isSc1.isSc0
  set zl : (Fin n → ℝ) → c.φ.model.E 1 := fun q => levelMap (E := rnSc n) H 1 q with hzldef
  have hzl : ∀ q ∈ U₀, zl q = z q := fun q hq => c.φ.model.E.toBase_injective 1 (by
    rw [hzy q (hU₀V hq)]; exact hH0.toBase_levelMap_const 1 hq)
  have hHS : ∀ q ∈ U₀, H q ∈ S.retract := fun q hq => by
    rw [hS]; exact ⟨Γ q, ⟨hq.2.1.1, hy0 q hq.1, hq.2.1.2⟩, rfl⟩
  have hzS : ∀ q ∈ U₀, z q ∈ c.φ.model.E.lvlSet S.retract 1 := fun q hq => by
    rw [ScBanach.mem_lvlSet, hzy q (hU₀V hq)]; exact hHS q hq
  have hrange : ∀ q ∈ U₀,
      (c.linKer g (z q) : Set (c.φ.model.E 0)) = range (scDeriv S.U S (z q)) := fun q hq => by
    rw [← hid (Γ q) hq.2.1.2 (hy0 q hq.1) c hc (hVc q hq.1) G hGo hGc hq.2.1.1 hQ (z q)
      (hzy q hq.1), ← hS]
    exact tangentSpace_eq_range S (hzS q hq)
  have hdim : ∀ q ∈ U₀, FiniteDimensional ℝ (c.linKer g (z q)) ∧
      Module.finrank ℝ (c.linKer g (z q)) = d := fun q hq =>
    (hind (Γ q) hq.2.2 (hy0 q hq.1)).finrank_linKer hg.isScSmooth (hy0 q hq.1) hc (hVc q hq.1)
      (z q) (hzy q hq.1)
  have := (hdim q₀ hq₀U₀).1
  let b : Module.Basis (Fin d) ℝ (c.linKer g (z q₀)) :=
    Module.finBasisOfFinrankEq ℝ _ (hdim q₀ hq₀U₀).2
  -- the basis vectors are smooth points
  have hrangeS : LinearMap.range (scDeriv S.U S (z q₀) :
      c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) = c.linKer g (z q₀) :=
    SetLike.coe_injective ((LinearMap.coe_range _).trans (hrange q₀ hq₀U₀).symm)
  have : FiniteDimensional ℝ (LinearMap.range (scDeriv S.U S (z q₀) :
      c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0)) := hrangeS ▸ inferInstance
  have hlift : ∀ q ∈ U₀, ∀ m, ∃ y ∈ c.φ.model.E.lvlSet S.U (m + 1),
      c.φ.model.E.shift.toBase m y = z q := fun q hq m =>
    ⟨levelMap (E := rnSc n) H (m + 1) q, by
      rw [ScBanach.mem_lvlSet, hH0.toBase_levelMap_const (m + 1) hq]
      exact S.retract_subset (hHS q hq),
      (hH0.shift_toBase_levelMap_const m hq).trans (hzl q hq)⟩
  have hbS : ∀ i, ((b i : c.linKer g (z q₀)) : c.φ.model.E 0) ∈ c.φ.model.E.smooth := fun i => by
    have hbi : ((b i : c.linKer g (z q₀)) : c.φ.model.E 0) ∈ range (scDeriv S.U S (z q₀)) := by
      rw [← hrange q₀ hq₀U₀]; exact (b i).2
    obtain ⟨w, hw⟩ := hbi
    rw [← hw]
    exact S.isSc1.isSc1With_scDeriv.apply_mem_smooth_of_finiteDimensional (hlift q₀ hq₀U₀) w
  -- the frame `e_i(q) = DS(z_q) b_i`
  set e : Fin d → (Fin n → ℝ) → c.φ.model.E 0 := fun i q => scDeriv S.U S (zl q) (b i)
    with hedef
  have he₀ : ∀ i, e i q₀ = b i := fun i => by
    have hbi : ((b i : c.linKer g (z q₀)) : c.φ.model.E 0) ∈ range (scDeriv S.U S (z q₀)) := by
      rw [← hrange q₀ hq₀U₀]; exact (b i).2
    obtain ⟨w, hw⟩ := hbi
    simp only [hedef, hzl q₀ hq₀U₀]
    rw [← hw]
    exact congrArg (fun T : c.φ.model.E 0 →L[ℝ] c.φ.model.E 0 => T w)
      (S.scDeriv_comp_self (hzS q₀ hq₀U₀))
  have hTS : ∀ i, IsScSmooth (E := rnSc n) (F := c.φ.model.E.tangent) U₀
      (tangentMap S.U S ∘ fun q : Fin n → ℝ => ((levelMap (E := rnSc n) H 1 q,
        ((b i : c.linKer g (z q₀)) : c.φ.model.E 0)) : c.φ.model.E.tangent 0)) := fun i => by
    have hγ := isScSmooth_tangentLift hU₀d hH (hbS i)
    have hmaps : MapsTo (fun q : Fin n → ℝ => ((levelMap (E := rnSc n) H 1 q,
        ((b i : c.linKer g (z q₀)) : c.φ.model.E 0)) : c.φ.model.E.tangent 0)) U₀
        (c.φ.model.E.tangentSet S.U) := fun q hq => by
      rw [ScBanach.mem_tangentSet, ScBanach.mem_lvlSet]
      change c.φ.model.E.toBase 1 (zl q) ∈ S.U
      rw [hzl q hq]
      exact S.retract_subset (hzS q hq)
    exact IsScSmooth.comp hU₀d S.isScDomain.tangentSet (isScSmooth_iff.1 S.isScSmooth).2 hγ hmaps
  have hsmooth : ∀ i, ContDiffOn ℝ ∞ (e i) U₀ := fun i =>
    (contDiff_snd.comp_contDiffOn ((hTS i).contDiffOn_const hU₀d)).congr fun q _ => rfl
  -- on every level `m`: the second component of the level-`m` map of `TS ∘ (z, bᵢ)`
  have hlevels : ∀ i m, ∃ em : (Fin n → ℝ) → c.φ.model.E m, ContDiffOn ℝ ∞ em U₀ ∧
      ∀ q ∈ U₀, c.φ.model.E.toBase m (em q) = e i q := fun i m => by
    refine ⟨fun q => (levelMap (E := rnSc n) (F := c.φ.model.E.tangent) (tangentMap S.U S ∘
      fun q : Fin n → ℝ => ((levelMap (E := rnSc n) H 1 q,
        ((b i : c.linKer g (z q₀)) : c.φ.model.E 0)) : c.φ.model.E.tangent 0)) m q).2,
      contDiff_snd.comp_contDiffOn ((hTS i).contDiffOn_levelMap_const hU₀d m), fun q hq => ?_⟩
    have h := congrArg Prod.snd ((hTS i).isSc1.isSc0.toBase_levelMap_const m hq)
    rw [ScBanach.tangent_toBase] at h
    exact h
  have hli₀ : LinearIndependent ℝ (fun i => e i q₀) := by
    have : (fun i => e i q₀) = (c.linKer g (z q₀)).subtype ∘ b := funext fun i => he₀ i
    rw [this]; exact b.linearIndependent.map' _ (Submodule.ker_subtype _)
  have hev : ∀ᶠ q in 𝓝 q₀, LinearIndependent ℝ (fun i => e i q) := by
    have hca : ContinuousAt (fun q i => e i q) q₀ :=
      continuousAt_pi.2 fun i => (hsmooth i).continuousOn.continuousAt (hU₀o.mem_nhds hq₀U₀)
    exact hca.tendsto.eventually hli₀.eventually
  obtain ⟨U₁, hU₁, hU₁o, hq₀U₁⟩ := eventually_nhds_iff.1 hev
  refine ⟨U₀ ∩ U₁, hU₀o.inter hU₁o, ⟨hq₀U₀, hq₀U₁⟩, inter_subset_left.trans hU₀V, d,
    fun q hq => hdim q hq.1, e, fun i => (hsmooth i).mono inter_subset_left, fun i m => ?_,
    fun q hq => ⟨fun i => ⟨?_, ?_⟩, hU₁ q hq.2⟩⟩
  · obtain ⟨em, hem, hemb⟩ := hlevels i m
    exact ⟨em, hem.mono inter_subset_left, fun q hq => hemb q hq.1⟩
  · have : e i q ∈ (c.linKer g (z q) : Set (c.φ.model.E 0)) := by
      rw [hrange q hq.1]
      exact ⟨((b i : c.linKer g (z q₀)) : c.φ.model.E 0), by
        change _ = scDeriv S.U S (zl q) (b i); rw [hzl q hq.1]⟩
    exact this
  · change scDeriv S.U S (zl q) (b i) ∈ _
    rw [hzl q hq.1]
    have : FiniteDimensional ℝ (LinearMap.range (scDeriv S.U S (z q) :
        c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0)) := by
      have h := (hdim q hq.1).1
      have hr : LinearMap.range (scDeriv S.U S (z q) : c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) =
          c.linKer g (z q) :=
        SetLike.coe_injective ((LinearMap.coe_range _).trans (hrange q hq.1).symm)
      exact hr ▸ h
    exact S.isSc1.isSc1With_scDeriv.apply_mem_smooth_of_finiteDimensional (hlift q hq.1) _

section Stab

open StrongRetr StrongBundle

variable {f : X → Y} {n k : ℕ}
  [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  [ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]

/-- **2021 Lemma 6.6.5, p. 265: `L` is a smooth vector bundle** (preprint Lemma 6.30).  In the
setting of `exists_isStabKernels` and `lemma_6_6_5_submersion` (`Φ([0, 1]ⁿ)` in the domain of a
chart `c`, `f + S = 0` along `Φ` and `F` in general position at `(0, (q, Φ(q)))` near `[0, 1]ⁿ`,
the conclusion of `lemma_6_6_4`), read in the product chart `χ` at the level-`1` points
`z_q` over `φ(Φ(q))`: there are an open connected `V ⊇ [0, 1]ⁿ` and a smooth family of subspaces
over the manifold `V` whose fibre at `q` is `L_q = ker F'(0, (q, z_q)) ∩ {dq = 0}`; it is a Mathlib
`C^∞` vector bundle over `V`. -/
theorem lemma_6_6_5_smoothBundle (hf : B.IsScFredholmSectionTame f)
    {Φ : (Fin n → ℝ) → X} (hΦ : (rnPolyfold n).IsScSmoothMap PX Φ)
    {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hΦc : ∀ q ∈ Icc (0 : Fin n → ℝ) 1, Φ q ∈ c.φ.source)
    {S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S)
    (hz : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q, Φ q))
    {s : Fin k → (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection (s i))
    (hP : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1),
      ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
        (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
          ((rnPolyfold n).prod PX))).IsGeneralPositionGerm
        (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
          ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (0, (q, Φ q)))
    (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
    (q₁ : pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))
    (z : (Fin n → ℝ) → c.φ.model.E 1)
    (hzy : ∀ q, Φ q ∈ c.φ.source → c.φ.model.E.toBase 1 (z q) = c.φ (Φ q)) :
    ∃ V : TopologicalSpace.Opens (Fin n → ℝ), Icc (0 : Fin n → ℝ) 1 ⊆ V ∧
      IsConnected (V : Set (Fin n → ℝ)) ∧
      ∃ Λ : SmoothSubspaceFamily 𝓘(ℝ, Fin n → ℝ) V
          (((PullbackChartData.ofProd ((PullbackChartData.ofProd c 0).toChart q₀) 0).toChart
            q₁).φ.model.E 0),
        (∀ q : V, Λ.L q =
          ((PullbackChartData.ofProd ((PullbackChartData.ofProd c 0).toChart q₀) 0).toChart
            q₁).linKer
            (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
              ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1)
            ((0, ((q : Fin n → ℝ), z q)) : ((PullbackChartData.ofProd
              ((PullbackChartData.ofProd c 0).toChart q₀) 0).toChart q₁).φ.model.E 1) ⊓
          LinearMap.ker (sliceProj k n (c.φ.model.E 0)).toLinearMap) ∧
        ContMDiffVectorBundle ∞ (Fin Λ.n → ℝ) Λ.Fiber 𝓘(ℝ, Fin n → ℝ) := by
  classical
  have hΦcont : Continuous Φ := continuousOn_univ.1 hΦ.continuousOn
  obtain ⟨hgt, hzero⟩ := isScFredholmSectionTame_stab (Φ := Φ) hf hS hs
  set cZ := (PullbackChartData.ofProd c 0).toChart q₀
  set χ := (PullbackChartData.ofProd cZ 0).toChart q₁
  have hcZc : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsChart cZ :=
    (PullbackChartData.ofProd c 0).isChart_toChart B _ hc q₀
  have hχc : ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold k) ((rnPolyfold n).prod PX))).IsChart χ :=
    (PullbackChartData.ofProd cZ 0).isChart_toChart _ _ hcZc q₁
  -- an open set `O ⊇ [0, 1]ⁿ` on which everything holds
  have hsrcN : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1), Φ q ∈ c.φ.source :=
    ((c.φ.isOpen_source.preimage hΦcont).mem_nhdsSet).2 hΦc
  obtain ⟨O, hOo, hIccO, hOp⟩ := mem_nhdsSet_iff_exists.1 (hsrcN.and (hz.and hP))
  -- `V`: the connected component of `O` containing `[0, 1]ⁿ`
  have h0 : (0 : Fin n → ℝ) ∈ Icc (0 : Fin n → ℝ) 1 := left_mem_Icc.2 zero_le_one
  set V := connectedComponentIn O (0 : Fin n → ℝ) with hVdef
  have hVo : IsOpen V := hOo.connectedComponentIn
  have hVO : V ⊆ O := connectedComponentIn_subset O 0
  have hIccV : Icc (0 : Fin n → ℝ) 1 ⊆ V :=
    (convex_Icc (0 : Fin n → ℝ) 1).isPreconnected.subset_connectedComponentIn h0 hIccO
  have hVconn : IsConnected V := isConnected_connectedComponentIn_iff.2 (hIccO h0)
  -- the family of zeros `Γ(q) = (0, (q, Φ(q)))` and its chart reading
  set Γ : (Fin n → ℝ) → (Fin k → ℝ) × ((Fin n → ℝ) × X) := fun q => (0, (q, Φ q)) with hΓdef
  have hΓ : (rnPolyfold n).IsScSmoothMap ((rnPolyfold k).prod ((rnPolyfold n).prod PX)) Γ :=
    MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_rn_rn_of_contDiff contDiff_const)
      (MPolyfold.IsScSmoothOn.prodMk MPolyfold.isScSmoothMap_id hΦ)
  set zz : (Fin n → ℝ) → χ.φ.model.E 1 := fun q => ((0, (q, z q)) : χ.φ.model.E 1) with hzzdef
  have hsrc : ∀ q ∈ O, Γ q ∈ χ.φ.source := fun q hq => ⟨mem_univ _, mem_univ _, (hOp hq).1⟩
  have hzz : ∀ q ∈ O, χ.φ.model.E.toBase 1 (zz q) = χ.φ (Γ q) := by
    intro q hq
    change ((rnSc k).prod ((rnSc n).prod c.φ.model.E)).toBase 1 (0, (q, z q)) =
      ((0 : Fin k → ℝ) - 0, ((q : Fin n → ℝ) - 0, c.φ (Φ q)))
    rw [ScBanach.prod_toBase, ScBanach.prod_toBase, ScBanach.const_toBase, ScBanach.const_toBase,
      hzy q (hOp hq).1, sub_zero, sub_zero]
  have hF0 : ∀ q ∈ O, IsZeroAt
      (pullbackProj (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X)) Prod.snd)
      (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
        ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (Γ q) :=
    fun q hq => hzero q (hOp hq).2.1
  have hgp : ∀ q ∈ O, ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
        ((rnPolyfold n).prod PX))).IsGoodPositionGermTame
      (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
        ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (Γ q) :=
    fun q hq => (hOp hq).2.2.isGoodPositionGermTame hgt (hF0 q hq)
  -- local smooth frames of the kernels `ker F'(0, (q, z_q))`
  have hloc := fun q (hq : q ∈ V) => exists_local_smooth_frame_linKer hgt hχc hΓ hVo
    (fun q hq => hsrc q (hVO hq)) (fun q hq => hF0 q (hVO hq)) (fun q hq => hgp q (hVO hq))
    zz (fun q hq => hzz q (hVO hq)) hq
  -- the dimension is constant on the connected set `V`
  have : PreconnectedSpace V := isPreconnected_iff_preconnectedSpace.1 hVconn.isPreconnected
  have hfd : ∀ q ∈ V, FiniteDimensional ℝ (χ.linKer _ (zz q)) := fun q hq => by
    obtain ⟨U, -, hqU, -, d, hd, -⟩ := hloc q hq
    exact (hd q hqU).1
  have hlc : IsLocallyConstant fun q : V => Module.finrank ℝ (χ.linKer
      (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
        ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (zz q)) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro q
    obtain ⟨U, hUo, hqU, -, d, hd, -⟩ := hloc q q.2
    filter_upwards [(hUo.preimage continuous_subtype_val).mem_nhds hqU] with q' hq'
    rw [(hd q' hq').2, (hd q hqU).2]
  set q₂ : V := ⟨0, hIccV h0⟩
  -- the smooth family of the kernels over the manifold `V`
  let Λ₀ : SmoothSubspaceFamily 𝓘(ℝ, Fin n → ℝ) (TopologicalSpace.Opens.mk V hVo)
      (χ.φ.model.E 0) :=
    { L := fun q => χ.linKer _ (zz q)
      n := Module.finrank ℝ (χ.linKer
        (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
          ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (zz q₂))
      finiteDimensional := fun q => hfd q q.2
      finrank_eq := fun q => hlc.apply_eq_of_preconnectedSpace q q₂
      exists_frame := fun b₀ => by
        obtain ⟨U, hUo, hb₀U, -, d, hd, e, he, -, hmem⟩ := hloc b₀ b₀.2
        obtain rfl : d = Module.finrank ℝ (χ.linKer _ (zz q₂)) :=
          (hd b₀ hb₀U).2.symm.trans (hlc.apply_eq_of_preconnectedSpace b₀ q₂)
        refine ⟨Subtype.val ⁻¹' U, hUo.preimage continuous_subtype_val, hb₀U,
          fun i q => e i q, fun i => ?_, fun q hq => ⟨fun i => ((hmem q hq).1 i).1, (hmem q hq).2⟩⟩
        exact (contMDiffOn_iff_contDiffOn.2 (he i)).comp contMDiff_subtype_val.contMDiffOn
          fun q hq => hq }
  -- the `ℝⁿ`-directions: `dπ = sliceProj` maps every kernel onto `ℝⁿ`
  have hℓ : ∀ q, (Λ₀.L q).map (sliceProj k n (c.φ.model.E 0)).toLinearMap = ⊤ := by
    intro q
    refine eq_top_iff.2 fun σ _ => ?_
    have hqO : (q : Fin n → ℝ) ∈ O := hVO q.2
    have hev : ∀ᶠ q' in 𝓝 (q : Fin n → ℝ), IsZeroAt
        (pullbackProj (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X)) Prod.snd)
        (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
          ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (Γ q') :=
      Filter.eventually_of_mem (hOo.mem_nhds hqO) hF0
    obtain ⟨hd, hmem⟩ := fderiv_mem_linKer hgt.isScSmooth hχc hΓ (hsrc q hqO) hev _
      (hzz q hqO) σ
    refine ⟨fderiv ℝ (fun q' => χ.φ (Γ q')) (q : Fin n → ℝ) σ, hmem, ?_⟩
    have hd' : HasFDerivAt (fun q' : Fin n → ℝ => (((0 : Fin k → ℝ) - 0, (q' - 0, c.φ (Φ q'))) :
        (Fin k → ℝ) × ((Fin n → ℝ) × c.φ.model.E 0)))
        (fderiv ℝ (fun q' => χ.φ (Γ q')) (q : Fin n → ℝ) :
          (Fin n → ℝ) →L[ℝ] (Fin k → ℝ) × ((Fin n → ℝ) × c.φ.model.E 0)) (q : Fin n → ℝ) :=
      hd.hasFDerivAt
    have := hd'.snd.fst.unique ((hasFDerivAt_id (q : Fin n → ℝ)).sub_const 0)
    exact congrArg (fun L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => L σ) this
  exact ⟨⟨V, hVo⟩, hIccV, hVconn, Λ₀.infKer (sliceProj k n (c.φ.model.E 0)) hℓ,
    fun q => rfl, inferInstance⟩

end Stab

end Polyfold
