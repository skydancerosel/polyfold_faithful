import Polyfold.Chapter5.GeneralPosition
import Polyfold.Chapter6.SubspaceBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5,
pp. 222–223: the analytic content of **Lemma 6.6.5 (preprint 6.30)** (near the points `(t, φ(t), 0)` the solution
set is a manifold, and the kernels `L_t` form a vector bundle) *(book 2017: Lemma 6.13; see
`BookConcordance.md`)*.

# The kernels of the linearizations along a family of zeros

## The text, paraphrased

(Lemma 6.6.5 (preprint 6.30)) Near `(t, φ(t), 0)` the solution set `S` of `F` is a smooth manifold with boundary
with corners (the implicit function theorem for the boundary case, using (P)); the fibres
`L_t = (Tπ)⁻¹(0)` over the zero section of `T[0, 1]` of the projection `π : S → [0, 1]` form a
smooth vector bundle `L → [0, 1]`, with `L_t = ker F_t'(φ(t), 0)`.

## What is formalized

* `exists_subspaceFamily_linKer`: for an sc-Fredholm section with tame germ data, a chart `c` and
  a continuous family `y_q` of zeros in good position, read in `c` at continuously varying
  level-`1` points `z_q`, the kernels `ker Lin(z_q) ⊆ E₀` form a continuous family of subspaces
  (`SubspaceFamily`).  This is where the implicit function theorem enters: near a zero in good
  position the kernel is the tangent space of the solution set (`exists_tangentSpace_eq_linKer`,
  Theorem 3.6.8 (preprint 3.54)), the range of the derivative of an sc-retraction onto it, whose derivative is
  jointly continuous.  The local statement is `exists_local_frame_linKer`; the dimension is the
  index (`IsSurjLinOfIndex.finrank_linKer`, Theorem 3.6.8 (preprint 3.54)), locally constant along the family.
* `fderiv_mem_linKer`: the derivative of an sc-smooth family of zeros `Γ : ℝⁿ → X`, read in a
  chart, lies in the kernel of the linearization (so the parameter directions of the family span
  the quotient by the slice kernels, `L_t = T S ∩ {dt = 0}`).

## Reading

The bundle `L` is read as a continuous family of subspaces of the model space of one chart; the
smooth structure is not needed for the continuation of orientations.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {g : X → Y}

open StrongRetr in
/-- **The kernel has the dimension of the index**: if `f'(y)` is onto of index `d` in every chart
(`IsSurjLinOfIndex`), then in every chart `c` around the zero `y`, at every level-`1` point `z`
over `φ(y)`, the kernel `ker Lin(z) ⊆ E₀` is finite-dimensional of dimension `d` (the dimension
count in the proof of `exists_tangentSpace_eq_linKer`). -/
theorem StrongBundle.IsSurjLinOfIndex.finrank_linKer {f : X → Y} (hf : B.IsScSmoothSection f)
    {y : X} {d : ℕ} (h : B.IsSurjLinOfIndex f y d) (hy0 : IsZeroAt P f y)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hyc : y ∈ c.φ.source)
    (z : c.φ.model.E 1) (hz : c.φ.model.E.toBase 1 z = c.φ y) :
    FiniteDimensional ℝ (c.linKer f z) ∧ Module.finrank ℝ (c.linKer f z) = d := by
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by
    rw [hz, c.r_image]; exact c.φ.mapsTo_model y hyc
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U := mem_U_of_mem_O c.isRetraction hzO
  have hmem : ∀ x : ↥(rangeS (scDeriv c.U (r c.R) z)),
      linAt c.U c.R (c.principal f) z x ∈ rangeS (ρCLM c.isRetraction hzU) := fun x =>
    ⟨_, rho_scDeriv_comp_r c.relOpen c.isRetraction (hf.isSc1_principal_comp_r hc)
      (fun x hx => c.principal_mem_K hf.1 (c.r_image ▸ hx)) hzO
      (by rw [hz]; exact (c.isZeroAt_iff hf.1 hyc).1 hy0) x⟩
  set Lc := (linAt c.U c.R (c.principal f) z).codRestrict _ hmem with hLcdef
  obtain ⟨-, hFred, -, hker⟩ := h c hc hyc z hz hzU Lc fun _ => rfl
  have hkerEq : LinearMap.ker (Lc : ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ]
      ↥(rangeS (ρCLM c.isRetraction hzU))) =
      LinearMap.ker (linAt c.U c.R (c.principal f) z :
        ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ] c.F 0) := by
    ext x
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hLcdef]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hfin : FiniteDimensional ℝ (LinearMap.ker (linAt c.U c.R (c.principal f) z :
      ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ] c.F 0)) := by
    rw [← hkerEq]; exact hFred.finite_ker
  refine ⟨?_, ?_⟩
  · unfold StrongBundleChart.linKer; infer_instance
  · unfold StrongBundleChart.linKer
    rw [← hker, hkerEq]
    exact (Submodule.equivMapOfInjective _ Subtype.val_injective _).finrank_eq.symm

/-- **Lemma 6.6.5 (preprint 6.30), near one point**: under the hypotheses of `exists_subspaceFamily_linKer`, near
every `q₀` the kernels `ker Lin(z_q)` have one dimension `d` and a continuous frame.  The frame is
`e_i(q) = DS(z_q) b_i` for a basis `b` of `ker Lin(z_{q₀})` and an sc-retraction `S` onto the
retract `φ(G ∩ S_f)` of the solution set, whose tangent space at `z_q` is `ker Lin(z_q)`
(`exists_tangentSpace_eq_linKer`); `(z, v) ↦ DS(z) v` is continuous on `S.U₁ × E₀`, and
independence is open. -/
theorem exists_local_frame_linKer {Q : Type*} [TopologicalSpace Q]
    (hg : B.IsScFredholmSectionTame g) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) (y : Q → X) (hy : Continuous y) (hyc : ∀ q, y q ∈ c.φ.source)
    (hy0 : ∀ q, IsZeroAt P g (y q)) (hgp : ∀ q, B.IsGoodPositionGermTame g (y q))
    (z : Q → c.φ.model.E 1) (hz : Continuous z)
    (hzy : ∀ q, c.φ.model.E.toBase 1 (z q) = c.φ (y q)) (q₀ : Q) :
    ∃ U : Set Q, IsOpen U ∧ q₀ ∈ U ∧ ∃ d : ℕ,
      (∀ q ∈ U, FiniteDimensional ℝ (c.linKer g (z q)) ∧
        Module.finrank ℝ (c.linKer g (z q)) = d) ∧
      ∃ e : Fin d → Q → c.φ.model.E 0, (∀ i, ContinuousOn (e i) U) ∧
        ∀ q ∈ U, (∀ i, e i q ∈ c.linKer g (z q)) ∧ LinearIndependent ℝ fun i => e i q := by
  classical
  obtain ⟨Vx, d, hVxo, hVx₀, hind⟩ :=
    theorem_3_6_8_index_locally_constant hg (hgp q₀) (hy0 q₀)
  obtain ⟨V, hVo, hV₀, hall, hid⟩ := exists_tangentSpace_eq_linKer hg (hgp q₀) (hy0 q₀)
  have hA : PX.IsSmoothSubmanifold (solutionSet P g ∩ V) :=
    StrongBundle.isSmoothSubmanifold_solutionSet_inter hg.isScSmooth.1 hVo hall
  have hyA : y q₀ ∈ solutionSet P g ∩ V := ⟨hy0 q₀, hV₀⟩
  set G := (hA.data hyA).toSubData.shrink c.φ with hGdef
  have hGo : IsOpen G := (hA.data hyA).toSubData.isOpen_shrink c.φ
  have hGc : G ⊆ c.φ.source := (hA.data hyA).toSubData.shrink_subset_source c.φ
  have hG₀ : y q₀ ∈ G :=
    (hA.data hyA).toSubData.mem_shrink c.φ hyA (hA.mem_data_V hyA) (hyc q₀)
  have hQ : IsScRetract c.φ.model.E c.φ.model.C (c.φ '' (G ∩ (solutionSet P g ∩ V))) :=
    (hA.data hyA).toSubData.isScRetract_image c.φ c.isChart
  obtain ⟨S, hS⟩ := id hQ
  set U₀ := y ⁻¹' (G ∩ V ∩ Vx) with hU₀def
  have hU₀o : IsOpen U₀ := ((hGo.inter hVo).inter hVxo).preimage hy
  have hq₀U₀ : q₀ ∈ U₀ := ⟨⟨hG₀, hV₀⟩, hVx₀⟩
  have hzS : ∀ q ∈ U₀, z q ∈ c.φ.model.E.lvlSet S.retract 1 := fun q hq => by
    rw [ScBanach.mem_lvlSet, hS, hzy]; exact ⟨y q, ⟨hq.1.1, hy0 q, hq.1.2⟩, rfl⟩
  have hrange : ∀ q ∈ U₀,
      (c.linKer g (z q) : Set (c.φ.model.E 0)) = range (scDeriv S.U S (z q)) := fun q hq => by
    rw [← hid (y q) hq.1.2 (hy0 q) c hc (hyc q) G hGo hGc hq.1.1 hQ (z q) (hzy q), ← hS]
    exact tangentSpace_eq_range S (hzS q hq)
  have hdim : ∀ q ∈ U₀, FiniteDimensional ℝ (c.linKer g (z q)) ∧
      Module.finrank ℝ (c.linKer g (z q)) = d := fun q hq =>
    (hind (y q) hq.2 (hy0 q)).finrank_linKer hg.isScSmooth (hy0 q) hc (hyc q) (z q) (hzy q)
  have := (hdim q₀ hq₀U₀).1
  let b : Module.Basis (Fin d) ℝ (c.linKer g (z q₀)) :=
    Module.finBasisOfFinrankEq ℝ _ (hdim q₀ hq₀U₀).2
  set e : Fin d → Q → c.φ.model.E 0 := fun i q => scDeriv S.U S (z q) (b i) with hedef
  have he₀ : ∀ i, e i q₀ = b i := fun i => by
    have hbi : ((b i : c.linKer g (z q₀)) : c.φ.model.E 0) ∈ range (scDeriv S.U S (z q₀)) := by
      rw [← hrange q₀ hq₀U₀]; exact (b i).2
    obtain ⟨w, hw⟩ := hbi
    simp only [hedef]
    rw [← hw]
    exact congrArg (fun T : c.φ.model.E 0 →L[ℝ] c.φ.model.E 0 => T w)
      (S.scDeriv_comp_self (hzS q₀ hq₀U₀))
  have hcont : ∀ i, ContinuousOn (e i) U₀ := fun i => by
    have h1 := S.isSc1.isSc1With_scDeriv.continuousOn_deriv
    refine h1.comp (hz.prodMk continuous_const).continuousOn fun q hq => ?_
    exact S.lvlSet_retract_subset 1 (hzS q hq)
  have hli₀ : LinearIndependent ℝ (fun i => e i q₀) := by
    have : (fun i => e i q₀) = (c.linKer g (z q₀)).subtype ∘ b := funext fun i => he₀ i
    rw [this]; exact b.linearIndependent.map' _ (Submodule.ker_subtype _)
  have hev : ∀ᶠ q in 𝓝 q₀, LinearIndependent ℝ (fun i => e i q) := by
    have hca : ContinuousAt (fun q i => e i q) q₀ :=
      continuousAt_pi.2 fun i => (hcont i).continuousAt (hU₀o.mem_nhds hq₀U₀)
    exact hca.tendsto.eventually hli₀.eventually
  obtain ⟨U₁, hU₁, hU₁o, hq₀U₁⟩ := eventually_nhds_iff.1 hev
  refine ⟨U₀ ∩ U₁, hU₀o.inter hU₁o, ⟨hq₀U₀, hq₀U₁⟩, d, fun q hq => hdim q hq.1, e,
    fun i => (hcont i).mono inter_subset_left, fun q hq => ⟨fun i => ?_, hU₁ q hq.2⟩⟩
  have : e i q ∈ (c.linKer g (z q) : Set (c.φ.model.E 0)) := by
    rw [hrange q hq.1]; exact ⟨_, rfl⟩
  exact this

/-- **Lemma 6.6.5 (preprint 6.30), the kernels**: let `g` be an sc-Fredholm section with tame germ data, `c` a
chart, `y : Q → X` a continuous family of zeros of `g` in the domain of `c`, in good position,
and `z : Q → E₁` continuous with `z_q` over `φ(y_q)`.  Then the kernels `ker Lin(z_q) ⊆ E₀` form a
continuous family of subspaces. -/
theorem exists_subspaceFamily_linKer {Q : Type*} [TopologicalSpace Q] [PreconnectedSpace Q]
    [Nonempty Q] (hg : B.IsScFredholmSectionTame g) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) (y : Q → X) (hy : Continuous y) (hyc : ∀ q, y q ∈ c.φ.source)
    (hy0 : ∀ q, IsZeroAt P g (y q)) (hgp : ∀ q, B.IsGoodPositionGermTame g (y q))
    (z : Q → c.φ.model.E 1) (hz : Continuous z)
    (hzy : ∀ q, c.φ.model.E.toBase 1 (z q) = c.φ (y q)) :
    ∃ Λ : SubspaceFamily Q (c.φ.model.E 0), ∀ q, Λ.L q = c.linKer g (z q) := by
  have hloc := exists_local_frame_linKer hg hc y hy hyc hy0 hgp z hz hzy
  have hfd : ∀ q, FiniteDimensional ℝ (c.linKer g (z q)) := fun q => by
    obtain ⟨U, -, hqU, d, hd, -⟩ := hloc q
    exact (hd q hqU).1
  have hlc : IsLocallyConstant (fun q => Module.finrank ℝ (c.linKer g (z q))) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro q
    obtain ⟨U, hUo, hqU, d, hd, -⟩ := hloc q
    filter_upwards [hUo.mem_nhds hqU] with q' hq'
    rw [(hd q' hq').2, (hd q hqU).2]
  obtain ⟨q₁⟩ := ‹Nonempty Q›
  refine ⟨{ L := fun q => c.linKer g (z q)
            n := Module.finrank ℝ (c.linKer g (z q₁))
            finiteDimensional := hfd
            finrank_eq := fun q => hlc.apply_eq_of_preconnectedSpace q q₁
            exists_frame := fun b₀ => ?_ }, fun q => rfl⟩
  obtain ⟨U, hUo, hb₀U, d, hd, e, hec, he⟩ := hloc b₀
  obtain rfl : d = Module.finrank ℝ (c.linKer g (z q₁)) :=
    (hd b₀ hb₀U).2.symm.trans (hlc.apply_eq_of_preconnectedSpace b₀ q₁)
  exact ⟨U, hUo, hb₀U, e, hec, he⟩

/-- **sc¹ maps on open subsets of `ℝⁿ` are differentiable**: for the constant sc-structure on
`ℝⁿ`, an sc¹ map on an open set `V₀` has, at every point of `V₀`, the Fréchet derivative
`scDeriv` (the remark after Definition 1.1.15 (preprint 1.14)). -/
lemma hasFDerivAt_scDeriv_rn {n : ℕ} {F : ScBanach} {V₀ : Set (Fin n → ℝ)} (hV₀ : IsOpen V₀)
    {H : (Fin n → ℝ) → F 0} (hH : IsSc1 (E := rnSc n) V₀ H) {q : Fin n → ℝ} (hq : q ∈ V₀) :
    HasFDerivAt H (scDeriv (E := rnSc n) V₀ H q) q := by
  have hq1 : (q : (rnSc n) 1) ∈ (rnSc n).lvlSet V₀ 1 := by
    rw [ScBanach.lvlSet_const]; exact hq
  have h := hH.isSc1With_scDeriv.hasFDerivWithinAt q hq1
  rw [ScBanach.lvlSet_const] at h
  have hcomp : H ∘ (rnSc n).toBase 1 = H :=
    funext fun x => congrArg H (ScBanach.const_toBase _ 1 x)
  have hclm : (scDeriv (E := rnSc n) V₀ H q).comp ((rnSc n).toBase 1) =
      scDeriv (E := rnSc n) V₀ H q :=
    ContinuousLinearMap.ext fun x => by
      rw [ContinuousLinearMap.comp_apply, ScBanach.const_toBase]
  rw [hcomp, hclm] at h
  exact h.hasFDerivAt (hV₀.mem_nhds hq)

open StrongRetr in
/-- **The derivative of a family of zeros lies in the kernel**: for an sc-smooth `Γ : ℝⁿ → X`
with `g(Γ(q)) = 0` near `q₀` and a chart `c` around `Γ(q₀)`, the derivative of `φ ∘ Γ` at `q₀`
(a vector of `E₀`) lies in `ker Lin(z)` at the level-`1` point `z` over `φ(Γ(q₀))`. -/
theorem fderiv_mem_linKer {n : ℕ} (hg : B.IsScSmoothSection g) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) {Γ : (Fin n → ℝ) → X} (hΓ : (rnPolyfold n).IsScSmoothMap PX Γ)
    {q₀ : Fin n → ℝ} (hq₀ : Γ q₀ ∈ c.φ.source) (h0 : ∀ᶠ q in 𝓝 q₀, IsZeroAt P g (Γ q))
    (z : c.φ.model.E 1) (hz : c.φ.model.E.toBase 1 z = c.φ (Γ q₀)) (v : Fin n → ℝ) :
    DifferentiableAt ℝ (fun q => c.φ (Γ q)) q₀ ∧
      fderiv ℝ (fun q => c.φ (Γ q)) q₀ v ∈ c.linKer g z := by
  have hΓc : Continuous Γ := continuousOn_univ.1 hΓ.continuousOn
  obtain ⟨W, hW0, hWo, hq₀W⟩ := eventually_nhds_iff.1 h0
  set V₀ := W ∩ Γ ⁻¹' c.φ.source with hV₀def
  have hV₀o : IsOpen V₀ := hWo.inter (c.φ.isOpen_source.preimage hΓc)
  have hq₀V₀ : q₀ ∈ V₀ := ⟨hq₀W, hq₀⟩
  have hrel : IsRelOpenInQuadrant (rnSc n) univ V₀ :=
    ⟨isPartialQuadrant_univ _, V₀, hV₀o, (inter_univ _).symm⟩
  -- the map `H = φ ∘ Γ` is sc-smooth on `V₀`
  set H : (Fin n → ℝ) → c.φ.model.E 0 := fun q => c.φ (Γ q) with hHdef
  have h1 := hΓ.smooth (rnChart n 0) c.φ (isChart_rnChart 0) c.isChart V₀ hV₀o
    (fun _ _ => ⟨mem_univ _, mem_univ _⟩) (fun _ hq => hq.2)
  have himg : (rnChart n 0 : (Fin n → ℝ) → (Fin n → ℝ)) '' V₀ = V₀ := by
    have : (rnChart n 0 : (Fin n → ℝ) → (Fin n → ℝ)) = id :=
      funext fun q => by rw [rnChart_apply, sub_zero]; rfl
    rw [this]; exact image_id V₀
  have hH : IsScSmooth (E := rnSc n) (F := c.φ.model.E) V₀ H := by
    have := h1.comp_isScSmooth (ScRetraction.id hrel) (by rw [himg]; exact image_id _)
    refine this.congr hrel.isScDomain fun q _ => ?_
    change c.φ (Γ ((rnChart n 0).symm q)) = c.φ (Γ q)
    rw [rnChart_symm_apply, add_zero]
  have hH1 : IsSc1 (E := rnSc n) V₀ H := hH.isSc1
  have hdiff := hasFDerivAt_scDeriv_rn hV₀o hH1 hq₀V₀
  refine ⟨hdiff.differentiableAt, ?_⟩
  rw [hdiff.fderiv]
  -- the chain rule through `r` and through `ĝ ∘ r`
  have hq₀1 : (q₀ : (rnSc n) 1) ∈ (rnSc n).lvlSet V₀ 1 := by
    rw [ScBanach.lvlSet_const]; exact hq₀V₀
  have hHO : ∀ q ∈ V₀, H q ∈ c.φ.model.O := fun q hq => c.φ.mapsTo_model _ hq.2
  have hmaps : MapsTo H V₀ c.U := fun q hq =>
    mem_U_of_mem_O c.isRetraction (c.r_image ▸ hHO q hq)
  have hlev : levelMap (E := rnSc n) H 1 q₀ = z := by
    apply levelMap_eq_of_toBase_eq
    rw [hz, ScBanach.const_toBase]
  have hr1 : IsSc1 c.U (r c.R) := (r_isScSmooth c.relOpen c.isRetraction).isSc1
  have hrH : scDeriv (E := rnSc n) V₀ (r c.R ∘ H) q₀ = scDeriv (E := rnSc n) V₀ H q₀ :=
    scDeriv_eq_of_eqOn_relOpen hrel (theorem_1_3_1 hrel c.relOpen hH1 hr1 hmaps).1 hH1
      subset_rfl subset_rfl (fun q hq => r_eq_self c.isRetraction (c.r_image ▸ hHO q hq)) hq₀1
  have hch1 := scDeriv_comp_apply' hrel c.relOpen hH1 hr1 hmaps hq₀1 v
  rw [hrH, hlev] at hch1
  have hw : scDeriv (E := rnSc n) V₀ H q₀ v ∈ rangeS (scDeriv c.U (r c.R) z) :=
    ⟨_, hch1⟩
  refine (c.mem_linKer_iff g z _).2 ⟨hw, ?_⟩
  rw [linAt_apply]
  have hfr : IsSc1 c.U (c.principal g ∘ r c.R) := hg.isSc1_principal_comp_r hc
  have hch2 := scDeriv_comp_apply' hrel c.relOpen hH1 hfr hmaps hq₀1 v
  rw [hlev] at hch2
  change scDeriv c.U (c.principal g ∘ r c.R) z (scDeriv (E := rnSc n) V₀ H q₀ v) = 0
  rw [hch2]
  have hzero : EqOn ((c.principal g ∘ r c.R) ∘ H) (fun _ => 0) V₀ := fun q hq => by
    simp only [Function.comp_apply]
    rw [r_eq_self c.isRetraction (c.r_image ▸ hHO q hq)]
    exact (c.isZeroAt_iff hg.1 hq.2).1 (hW0 q hq.1)
  obtain ⟨hcomp, -⟩ := theorem_1_3_1 hrel c.relOpen hH1 hfr hmaps
  have d1 := hcomp.isSc1With_scDeriv.hasFDerivWithinAt q₀ hq₀1
  have d2 : HasFDerivWithinAt (((c.principal g ∘ r c.R) ∘ H) ∘ (rnSc n).toBase 1)
      ((0 : (rnSc n) 0 →L[ℝ] c.F 0).comp ((rnSc n).toBase 1)) ((rnSc n).lvlSet V₀ 1) q₀ := by
    rw [ContinuousLinearMap.zero_comp]
    exact (hasFDerivWithinAt_const (0 : c.F 0) _ _).congr (fun y hy => hzero hy) (hzero hq₀1)
  have := ContinuousLinearMap.ext_of_comp_toBase_one
    ((hrel.isScDomain.uniqueDiffWithinAt 1 q₀ hq₀1).eq d1 d2)
  rw [this]; rfl

end Polyfold
