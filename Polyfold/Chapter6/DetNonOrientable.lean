import Polyfold.Chapter6.StabilizationContinuity
import Polyfold.Chapter6.ChartTransfer

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), the end of §6.5 (p. 262;
preprint p. 219): the remark that **the line bundle `DET(E, F)` is non-orientable**.  Gap G.60.

# `DET(E, F)` is not orientable

## The text, paraphrased

After Lemma 6.5.9 the text remarks that `DET(E, F)`, the determinant line bundle over the space
`F(E, F)` of all Fredholm operators `E → F` (norm topology, with the topology `𝒯` of
Proposition 6.5.8), is known to be non-orientable, and that it is orientable over certain subsets
(Proposition 6.6.1).  No hypothesis on `E`, `F` is stated and no proof or reference is given.

## What is formalized

* `isEmpty_lineOrientation_of_loop`: a line bundle with a continuous nowhere-vanishing section
  along a map `p` from a preconnected space that takes the values `v` and `−v` in one fibre has no
  orientation.
* `kerDetVec`, `kerDetMk`: for a surjective Fredholm `S` and a basis `v` of `ker S`, the element
  `(v₁ ∧ … ∧ vₙ) ⊗ 1*` of `det(S)`; `LocalDetChart.coord_kerDetVec`: its coordinate in a chart
  with `P = 1` is the determinant of the projections of the `vᵢ` to the kernel at the centre;
  `continuous_kerDetMk`: for norm-continuous `A_x` and continuous `v_x` it is a continuous section
  of `DET(E, F)` along `x ↦ A_x`.
* `isEmpty_lineOrientation_det_of_kernel_loop`: **the criterion.**  If `A_x` (x in a preconnected
  space) are surjective Fredholm operators, norm-continuous in `x`, with continuous bases `v_x`
  of the kernels of odd dimension `n`, and `A_{x₁} = A_{x₀}`, `v_{x₁} = −v_{x₀}`, then
  `DET(E, F)` has no orientation.
* `isEmpty_lineOrientation_det_of_complexStructure`: if `E` and `F` carry bounded `J` with
  `J² = −1` and there is a surjective `T : E → F` with kernel of odd finite dimension, then
  `DET(E, F)` has no orientation.  The loop is `A_θ = R'_θ T R_{−θ}`, `θ ∈ [0, π]`, with
  `R_θ = cos θ + sin θ J`; its kernels `R_θ(ker T)` form a Möbius band.
* `isEmpty_lineOrientation_det_prod`: for a Banach space `H` with a surjective `S : H → H` whose
  kernel has odd finite dimension (for instance `H ≅ ℝ × H`), `DET(H × H, H × H)` has no
  orientation.  (`DetNonOrientableHilbert.lean`: `H = ℓ²`.)
* `exists_two_lineOrientation_det_of_finiteDimensional`: for finite-dimensional `E`, `F` the
  bundle `DET(E, F)` over `F(E, F) = L(E, F)` has exactly two orientations, so it is orientable.

## Reading

The remark does not hold as we read it for all `E`, `F`: for finite-dimensional `E`, `F` every
operator is Fredholm, the base is convex, and `DET(E, F)` is orientable (Proposition 6.6.1;
`exists_two_lineOrientation_det_of_finiteDimensional`).  It holds whenever `E`, `F` have complex
structures and a surjective Fredholm operator with odd-dimensional kernel; this covers
`E = F = H × H` for every Banach space `H ≅ ℝ × H`, in particular `ℓ² × ℓ²`.  The transport of
`DET` along isomorphisms of `E`, `F` (to pass to every space isomorphic to such a product) is not
formalized here, and no statement is made for the infinite-dimensional Banach spaces without
these structures.  Infinite dimension enters through the surjective operator
`S : H → H` with a kernel: on a finite-dimensional `H` the same loop has a Möbius band of
cokernels as well, and the two cancel in `det`.
-/

open Module TensorProduct Bundle Topology Set

noncomputable section

namespace Polyfold

/-! ### A line bundle with a section that changes sign around a loop -/

section Loop

variable {B : Type*} [TopologicalSpace B] {L : B → Type*} [∀ b, AddCommMonoid (L b)]
  [∀ b, Module ℝ (L b)] [TopologicalSpace (TotalSpace ℝ L)] [∀ b, TopologicalSpace (L b)]
  [FiberBundle ℝ L] [VectorBundle ℝ ℝ L]

omit [TopologicalSpace B] [TopologicalSpace (TotalSpace ℝ L)] [∀ b, TopologicalSpace (L b)]
  [FiberBundle ℝ L] [VectorBundle ℝ ℝ L] in
/-- A nonzero vector and its negative `(−1) • v` have different rays. -/
theorem rayOfNeZero_ne_neg_one_smul {b : B} {v : L b} (hv : v ≠ 0)
    (hv' : (-1 : ℝ) • v ≠ 0) : rayOfNeZero ℝ v hv ≠ rayOfNeZero ℝ ((-1 : ℝ) • v) hv' := by
  rw [Ne, ray_eq_iff]
  intro h
  obtain ⟨r₁, r₂, h₁, h₂, h⟩ := h.exists_pos hv hv'
  have h0 : (r₁ + r₂) • v = 0 := by
    have h3 : r₂ • (-1 : ℝ) • v + r₂ • v = 0 := by
      rw [smul_smul, ← add_smul]
      simp
    rw [add_smul, h]
    exact h3
  rcases smul_eq_zero.1 h0 with h4 | h4
  · linarith
  · exact hv h4

omit [TopologicalSpace B] [TopologicalSpace (TotalSpace ℝ L)] [∀ b, TopologicalSpace (L b)]
  [FiberBundle ℝ L] [VectorBundle ℝ ℝ L] in
/-- "`o` is the ray of `z`" depends only on the point `z` of the total space. -/
theorem ray_eq_congr (o : ∀ b, Module.Ray ℝ (L b)) {z z' : TotalSpace ℝ L} (h : z = z')
    (hz : z.2 ≠ 0) (hz' : z'.2 ≠ 0) :
    o z.1 = rayOfNeZero ℝ z.2 hz ↔ o z'.1 = rayOfNeZero ℝ z'.2 hz' := by
  subst h
  rfl

/-- Along a continuous nowhere-vanishing section `p`, whether an orientation is the ray of the
section does not change locally. -/
theorem LineOrientation.eventually_eq_ray_iff (o : LineOrientation L) {X : Type*}
    [TopologicalSpace X] {p : X → TotalSpace ℝ L} (hp : Continuous p) (hne : ∀ x, (p x).2 ≠ 0)
    (x₀ : X) :
    ∀ᶠ x in 𝓝 x₀, (o (p x).1 = rayOfNeZero ℝ (p x).2 (hne x) ↔
      o (p x₀).1 = rayOfNeZero ℝ (p x₀).2 (hne x₀)) := by
  set e := trivializationAt ℝ L (p x₀).1 with he
  have hb₀ : (p x₀).1 ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt ℝ L _
  have hproj : Continuous fun x => (p x).1 := (FiberBundle.continuous_proj ℝ L).comp hp
  have hg : ContinuousAt (fun x => (e (p x)).2) x₀ :=
    continuous_snd.continuousAt.comp ((e.continuousOn.continuousAt
      (e.open_source.mem_nhds (e.mem_source.2 hb₀))).comp hp.continuousAt)
  filter_upwards [hproj.continuousAt.eventually (o.2.eventually_posRay_iff e hb₀),
    hproj.continuousAt.eventually (e.open_baseSet.mem_nhds hb₀),
    eventually_pos_iff_of_tendsto hg (coord_ne_zero e hb₀ (hne x₀))] with x h1 hb h3
  rw [eq_iff_posRay_iff e hb, eq_iff_posRay_iff e hb₀, posRay_ray_iff e hb,
    posRay_ray_iff e hb₀]
  exact iff_congr h1 h3

/-- **A section that changes sign around a loop.**  If a continuous map `p` from a preconnected
space into the total space of a line bundle `L` vanishes nowhere and takes the values `v` and
`−v` in one fibre, then `L` has no orientation. -/
theorem isEmpty_lineOrientation_of_loop {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {p : X → TotalSpace ℝ L} (hp : Continuous p) (hne : ∀ x, (p x).2 ≠ 0) (x₀ x₁ : X)
    (h : p x₁ = ⟨(p x₀).1, (-1 : ℝ) • (p x₀).2⟩) : IsEmpty (LineOrientation L) := by
  classical
  refine ⟨fun o => ?_⟩
  have hloc : IsLocallyConstant fun x => decide (o (p x).1 = rayOfNeZero ℝ (p x).2 (hne x)) :=
    (IsLocallyConstant.iff_eventually_eq _).2 fun x =>
      (o.eventually_eq_ray_iff hp hne x).mono fun y hy => decide_eq_decide.2 hy
  have h01 := hloc.apply_eq_of_preconnectedSpace x₁ x₀
  have h01' := decide_eq_decide.1 h01
  have hv' : (-1 : ℝ) • (p x₀).2 ≠ 0 := by
    have := hne x₁
    rw [h] at this
    exact this
  have h1 := ray_eq_congr (fun b => o b) h (hne x₁) hv'
  have h2 : o (p x₀).1 = rayOfNeZero ℝ ((-1 : ℝ) • (p x₀).2) hv' ↔
      o (p x₀).1 = rayOfNeZero ℝ (p x₀).2 (hne x₀) := h1.symm.trans h01'
  have hne' := rayOfNeZero_ne_neg_one_smul (hne x₀) hv'
  -- a fibre has exactly two rays: `o` is one of them
  set e := trivializationAt ℝ L (p x₀).1
  have hb₀ : (p x₀).1 ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt ℝ L _
  by_cases hc : o (p x₀).1 = rayOfNeZero ℝ (p x₀).2 (hne x₀)
  · exact hne' (hc.symm.trans (h2.2 hc))
  · have hc' : ¬ o (p x₀).1 = rayOfNeZero ℝ ((-1 : ℝ) • (p x₀).2) hv' := fun h' => hc (h2.1 h')
    rw [eq_iff_posRay_iff e hb₀] at hc hc'
    rw [Ne, eq_iff_posRay_iff e hb₀] at hne'
    tauto

end Loop

/-! ### Sections of `DET(E, F)` over surjective operators, from bases of the kernels -/

section Det

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **`(v₁ ∧ … ∧ vₙ) ⊗ 1* ∈ det(S)`** for a surjective `S` and `n = dim ker S` vectors `vᵢ` of
`ker S` (`1` is the empty wedge of the cokernel `{0}`). -/
def kerDetVec (S : E →L[ℝ] F) (hs : Function.Surjective S) {n : ℕ} (v : Fin n → E)
    (hv : ∀ i, S (v i) = 0) (hn : n = finrank ℝ (LinearMap.ker (S : E →ₗ[ℝ] F))) :
    fredholmDet S :=
  wedge (fun i => (⟨v i, hv i⟩ : LinearMap.ker (S : E →ₗ[ℝ] F))) hn ⊗ₜ
    dualVec (wedge (Fin.elim0 : Fin 0 → F ⧸ LinearMap.range (S : E →ₗ[ℝ] F))
      (finrank_coker_of_surjective hs).symm)

omit [CompleteSpace E] [CompleteSpace F] in
/-- `kerDetVec` of a basis of the kernel is not zero. -/
theorem kerDetVec_ne_zero {S : E →L[ℝ] F} (hF : S.IsFredholm) (hs : Function.Surjective S)
    {n : ℕ} {v : Fin n → E} (hv : ∀ i, S (v i) = 0)
    (hn : n = finrank ℝ (LinearMap.ker (S : E →ₗ[ℝ] F))) (hli : LinearIndependent ℝ v) :
    kerDetVec S hs v hv hn ≠ 0 := by
  have := hF.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) := hF.finite_coker
  have ha : LinearIndependent ℝ fun i => (⟨v i, hv i⟩ : LinearMap.ker (S : E →ₗ[ℝ] F)) :=
    LinearIndependent.of_comp (LinearMap.ker (S : E →ₗ[ℝ] F)).subtype hli
  exact tmul_ne_zero_of_ne_zero ((wedge_ne_zero_iff hn).2 ha)
    (dualVec_ne_zero finrank_maxPow
      ((wedge_ne_zero_iff (finrank_coker_of_surjective hs).symm).2 linearIndependent_empty_type))

omit [CompleteSpace E] [CompleteSpace F] in
/-- `kerDetVec` of the negated family, for an odd number of vectors, is the negative. -/
theorem kerDetVec_neg {S : E →L[ℝ] F} (hs : Function.Surjective S) {n : ℕ} (hodd : Odd n)
    {v : Fin n → E} (hv : ∀ i, S (v i) = 0) (hv' : ∀ i, S (-v i) = 0)
    (hn : n = finrank ℝ (LinearMap.ker (S : E →ₗ[ℝ] F))) :
    kerDetVec S hs (fun i => -v i) hv' hn = (-1 : ℝ) • kerDetVec S hs v hv hn := by
  have hw : wedge (fun i => (⟨-v i, hv' i⟩ : LinearMap.ker (S : E →ₗ[ℝ] F))) hn =
      (-1 : ℝ) • wedge (fun i => (⟨v i, hv i⟩ : LinearMap.ker (S : E →ₗ[ℝ] F))) hn := by
    have h1 : (fun i => (⟨-v i, hv' i⟩ : LinearMap.ker (S : E →ₗ[ℝ] F))) =
        fun i => (-1 : ℝ) • (⟨v i, hv i⟩ : LinearMap.ker (S : E →ₗ[ℝ] F)) :=
      funext fun i => Subtype.ext (by simp)
    rw [h1]
    apply Subtype.ext
    simp only [coe_wedge, SetLike.val_smul]
    have h2 := (ExteriorAlgebra.ιMulti ℝ n
      (M := LinearMap.ker (S : E →ₗ[ℝ] F))).toMultilinearMap.map_smul_univ
        (fun _ => (-1 : ℝ)) (fun i => ⟨v i, hv i⟩)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hodd.neg_one_pow] at h2
    exact h2
  rw [kerDetVec, kerDetVec, hw, TensorProduct.smul_tmul']

/-- **The coordinate of `(v₁ ∧ … ∧ vₙ) ⊗ 1*` in a chart with `P = 1`**: the determinant, in the
basis of `ker T` of the chart, of the projections of the `vᵢ` to `ker T` along `Y`. -/
theorem LocalDetChart.coord_kerDetVec (c : LocalDetChart E F)
    (hcP : c.P = ContinuousLinearMap.id ℝ F) {S : E →L[ℝ] F} (hF : S.IsFredholm)
    (hs : Function.Surjective S) (hS : ‖S - c.T‖ < c.ε) {n : ℕ} {v : Fin n → E}
    (hv : ∀ i, S (v i) = 0) (hn : n = finrank ℝ (LinearMap.ker (S : E →ₗ[ℝ] F)))
    (hli : LinearIndependent ℝ v) (h1 : finrank ℝ c.K = n) :
    c.coord ⟨S, hF⟩ (kerDetVec S hs v hv hn) =
      ((Module.finBasis ℝ c.K).reindex (finCongr h1)).det (fun i => c.kerProj (v i)) := by
  classical
  have := hF.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) := hF.finite_coker
  set a : Fin n → LinearMap.ker (S : E →ₗ[ℝ] F) := fun i => ⟨v i, hv i⟩ with ha_def
  have ha : LinearIndependent ℝ a :=
    LinearIndependent.of_comp (LinearMap.ker (S : E →ₗ[ℝ] F)).subtype hli
  have hPS := c.isGoodLeftProj_of_lt S hS
  have hb : LinearIndependent ℝ (Fin.append (projSeqJ S c.P ∘ a)
      (Fin.elim0 : Fin 0 → LinearMap.ker ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F))) := by
    rw [Fin.append_elim0]
    exact (ha.map' _ (LinearMap.ker_eq_bot.2 (proposition_6_4_10 hPS).1)).comp _
      (Fin.cast_injective _)
  have htop : LinearMap.range ((c.P : F →L[ℝ] F) : F →ₗ[ℝ] F) = ⊤ := by
    rw [hcP]
    exact LinearMap.range_eq_top.2 fun y => ⟨y, rfl⟩
  have : Subsingleton (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) :=
    Submodule.Quotient.subsingleton_iff.2 htop
  have h2 : finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) = 0 + 0 :=
    Module.finrank_zero_of_subsingleton
  have hj : n + 0 = finrank ℝ (LinearMap.ker ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
    h1.symm.trans (c.kerEquiv S hS).finrank_eq
  have hc0 := c.coord_wedge_tmul hF hS ha hn
    (d := (Fin.elim0 : Fin 0 → F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)))
    linearIndependent_empty_type (finrank_coker_of_surjective hs).symm hb hj
    (cc := Fin.elim0) (fun i => i.elim0) h1 h2
  have hf : (fun i => c.kerProj (Fin.append (projSeqJ S c.P ∘ a)
      (Fin.elim0 : Fin 0 → LinearMap.ker ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)) i).1) =
      fun i => c.kerProj (v i) := by
    funext i
    rw [Fin.append_elim0]
    rfl
  have : IsEmpty (Fin (0 + 0)) := ⟨fun i => Fin.elim0 i⟩
  have h3 : ∀ (b : Basis (Fin (0 + 0)) ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)))
      (w : Fin (0 + 0) → F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)), b.det w = 1 := fun b w => by
    rw [Basis.det_isEmpty, AlternatingMap.constOfIsEmpty_apply, Function.const_apply]
  rw [hf, h3, inv_one, mul_one] at hc0
  exact hc0

/-- The point `(S, (v₁ ∧ … ∧ vₙ) ⊗ 1*)` of `DET(E, F)`. -/
def kerDetMk (S : E →L[ℝ] F) (hF : S.IsFredholm) (hs : Function.Surjective S) {n : ℕ}
    (v : Fin n → E) (hv : ∀ i, S (v i) = 0)
    (hn : n = finrank ℝ (LinearMap.ker (S : E →ₗ[ℝ] F))) :
    TotalSpace ℝ (DetFiber (E := E) (F := F)) :=
  ⟨⟨S, hF⟩, kerDetVec S hs v hv hn⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- `kerDetMk` depends only on the operator and the vectors. -/
theorem kerDetMk_congr {S S' : E →L[ℝ] F} (hSS' : S = S') {hF : S.IsFredholm}
    {hF' : S'.IsFredholm} {hs : Function.Surjective S} {hs' : Function.Surjective S'} {n : ℕ}
    {v v' : Fin n → E} (hvv' : v = v') {hv : ∀ i, S (v i) = 0} {hv' : ∀ i, S' (v' i) = 0}
    {hn : n = finrank ℝ (LinearMap.ker (S : E →ₗ[ℝ] F))}
    {hn' : n = finrank ℝ (LinearMap.ker (S' : E →ₗ[ℝ] F))} :
    kerDetMk S hF hs v hv hn = kerDetMk S' hF' hs' v' hv' hn' := by
  subst hSS' hvv'
  rfl

/-- **Continuous bases of the kernels give a continuous section of `DET(E, F)`**: for surjective
Fredholm operators `A_x`, norm-continuous in `x`, and bases `v_x` of `ker A_x` continuous in `x`,
`x ↦ (A_x, (v_x)₁ ∧ … ∧ (v_x)ₙ ⊗ 1*)` is continuous into `DET(E, F)`. -/
theorem continuous_kerDetMk {X : Type*} [TopologicalSpace X] {A : X → E →L[ℝ] F}
    (hA : Continuous A) (hF : ∀ x, (A x).IsFredholm) (hs : ∀ x, Function.Surjective (A x))
    {n : ℕ} {v : X → Fin n → E} (hvc : Continuous v) (hv : ∀ x i, A x (v x i) = 0)
    (hn : ∀ x, n = finrank ℝ (LinearMap.ker (A x : E →ₗ[ℝ] F)))
    (hli : ∀ x, LinearIndependent ℝ (v x)) :
    Continuous fun x => kerDetMk (A x) (hF x) (hs x) (v x) (hv x) (hn x) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨c, hcT, hcP⟩ :=
    exists_localDetChart_of_proj (hF x₀) (isGoodLeftProj_id_of_surjective (hs x₀))
  obtain ⟨e, -, heb, he⟩ := (proposition_6_5_8 (E := E) (F := F)).2 c
  have hK : c.K = LinearMap.ker (A x₀ : E →ₗ[ℝ] F) := by
    change LinearMap.ker ((c.P ∘L c.T : E →L[ℝ] F) : E →ₗ[ℝ] F) = _
    rw [hcP, ContinuousLinearMap.id_comp, hcT]
  have h1 : finrank ℝ c.K = n := by rw [hK]; exact (hn x₀).symm
  have hx₀ : ‖A x₀ - c.T‖ < c.ε := by
    rw [hcT, sub_self, norm_zero]
    exact c.ε_pos
  have hproj : Continuous fun x => (⟨A x, hF x⟩ : FredholmOp E F) := hA.subtype_mk _
  have hU : ∀ᶠ x in 𝓝 x₀, ‖A x - c.T‖ < c.ε :=
    (hA.continuousAt (x := x₀)).eventually
      ((isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).mem_nhds hx₀)
  refine e.continuousAt_of_comp_left hproj.continuousAt (heb ▸ hx₀) ?_
  have hdet : Continuous fun x =>
      ((Module.finBasis ℝ c.K).reindex (finCongr h1)).det (fun i => c.kerProj (v x i)) :=
    (continuous_basis_det _).comp
      (continuous_pi fun i => c.kerProj.continuous.comp ((continuous_apply i).comp hvc))
  have hcomp : ContinuousAt (fun x => ((⟨A x, hF x⟩ : FredholmOp E F),
      ((Module.finBasis ℝ c.K).reindex (finCongr h1)).det (fun i => c.kerProj (v x i)))) x₀ :=
    (hproj.prodMk hdet).continuousAt
  refine hcomp.congr (hU.mono fun x hx => ?_)
  change _ = e (kerDetMk (A x) (hF x) (hs x) (v x) (hv x) (hn x))
  rw [he, LocalDetChart.pretriv_apply]
  exact Prod.ext rfl (c.coord_kerDetVec hcP (hF x) (hs x) hx (hv x) (hn x) (hli x) h1).symm

/-- **The criterion for non-orientability.**  Let `A_x`, `x` in a preconnected space, be
surjective Fredholm operators `E → F`, norm-continuous in `x`, and `v_x` bases of `ker A_x`,
continuous in `x`, of odd length `n`.  If `A_{x₁} = A_{x₀}` and `v_{x₁} = −v_{x₀}` for two
parameters, then `DET(E, F)` has no orientation. -/
theorem isEmpty_lineOrientation_det_of_kernel_loop {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {A : X → E →L[ℝ] F} (hA : Continuous A)
    (hF : ∀ x, (A x).IsFredholm) (hs : ∀ x, Function.Surjective (A x)) {n : ℕ} (hodd : Odd n)
    {v : X → Fin n → E} (hvc : Continuous v) (hv : ∀ x i, A x (v x i) = 0)
    (hn : ∀ x, n = finrank ℝ (LinearMap.ker (A x : E →ₗ[ℝ] F)))
    (hli : ∀ x, LinearIndependent ℝ (v x)) (x₀ x₁ : X) (hA01 : A x₁ = A x₀)
    (hv01 : ∀ i, v x₁ i = -v x₀ i) :
    IsEmpty (LineOrientation (DetFiber (E := E) (F := F))) := by
  refine isEmpty_lineOrientation_of_loop (continuous_kerDetMk hA hF hs hvc hv hn hli)
    (fun x => kerDetVec_ne_zero (hF x) (hs x) (hv x) (hn x) (hli x)) x₀ x₁ ?_
  have hv' : ∀ i, A x₀ (-v x₀ i) = 0 := fun i => by rw [map_neg, hv x₀ i, neg_zero]
  refine (kerDetMk_congr hA01 (funext hv01) (hF' := hF x₀) (hs' := hs x₀) (hv' := hv')
    (hn' := hn x₀)).trans ?_
  exact congrArg (TotalSpace.mk (⟨A x₀, hF x₀⟩ : FredholmOp E F))
    (kerDetVec_neg (hs x₀) hodd (hv x₀) hv' (hn x₀))

end Det

/-! ### The loop `R'_θ T R_{−θ}` of a complex structure -/

section Rotation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `R_θ = cos θ + sin θ J`, the rotation by `θ` of a complex structure `J`. -/
def rotJ (J : E →L[ℝ] E) (θ : ℝ) : E →L[ℝ] E :=
  Real.cos θ • ContinuousLinearMap.id ℝ E + Real.sin θ • J

theorem rotJ_apply (J : E →L[ℝ] E) (θ : ℝ) (x : E) :
    rotJ J θ x = Real.cos θ • x + Real.sin θ • J x := rfl

/-- `θ ↦ R_θ` is norm-continuous. -/
theorem continuous_rotJ (J : E →L[ℝ] E) : Continuous (rotJ J) :=
  (Real.continuous_cos.smul continuous_const).add (Real.continuous_sin.smul continuous_const)

/-- `R_θ R_{−θ} = 1` for `J² = −1`. -/
theorem rotJ_rotJ_neg {J : E →L[ℝ] E} (hJ : ∀ x, J (J x) = -x) (θ : ℝ) (x : E) :
    rotJ J θ (rotJ J (-θ) x) = x := by
  simp only [rotJ_apply, Real.cos_neg, Real.sin_neg, map_add, map_smul, hJ]
  calc _ = (Real.cos θ ^ 2 + Real.sin θ ^ 2) • x := by module
    _ = x := by rw [Real.cos_sq_add_sin_sq, one_smul]

/-- `R_{−θ} R_θ = 1` for `J² = −1`. -/
theorem rotJ_neg_rotJ {J : E →L[ℝ] E} (hJ : ∀ x, J (J x) = -x) (θ : ℝ) (x : E) :
    rotJ J (-θ) (rotJ J θ x) = x := by
  have h := rotJ_rotJ_neg hJ (-θ) x
  rwa [neg_neg] at h

theorem rotJ_zero_apply (J : E →L[ℝ] E) (x : E) : rotJ J 0 x = x := by
  simp [rotJ_apply]

theorem rotJ_pi_apply (J : E →L[ℝ] E) (x : E) : rotJ J Real.pi x = -x := by
  simp [rotJ_apply]

theorem rotJ_neg_pi_apply (J : E →L[ℝ] E) (x : E) : rotJ J (-Real.pi) x = -x := by
  simp [rotJ_apply]

/-- `R_θ` as an isomorphism, for `J² = −1`. -/
def rotJEquiv {J : E →L[ℝ] E} (hJ : ∀ x, J (J x) = -x) (θ : ℝ) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse (rotJ J θ) (rotJ J (-θ)) (rotJ_neg_rotJ hJ θ)
    (rotJ_rotJ_neg hJ θ)

@[simp] theorem rotJEquiv_apply {J : E →L[ℝ] E} (hJ : ∀ x, J (J x) = -x) (θ : ℝ) (x : E) :
    rotJEquiv hJ θ x = rotJ J θ x := rfl

end Rotation

section Complex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A surjective operator between Banach spaces with finite-dimensional kernel is Fredholm. -/
theorem isFredholm_of_surjective_of_finite_ker {S : E →L[ℝ] F} (hs : Function.Surjective S)
    (hk : FiniteDimensional ℝ (LinearMap.ker (S : E →ₗ[ℝ] F))) : S.IsFredholm := by
  have hr : S.range = ⊤ := LinearMap.range_eq_top.2 hs
  refine isFredholm_of_banach _ hk ?_ ?_
  · rw [hr]
    exact isClosed_univ
  · rw [hr]
    exact Submodule.CoFG.top

/-- **(2021, p. 262) `DET(E, F)` is not orientable** when `E` and `F` carry complex structures
(bounded `J` with `J² = −1`) and there is a surjective operator `T : E → F` whose kernel has odd
finite dimension.  The loop is `A_θ = R'_θ T R_{−θ}`, `θ ∈ [0, π]`, with kernels `R_θ(ker T)`:
`A_π = (−1) T (−1) = T = A_0`, while the basis `R_θ k` of the kernels returns to `−k`. -/
theorem isEmpty_lineOrientation_det_of_complexStructure {J : E →L[ℝ] E}
    (hJ : ∀ x, J (J x) = -x) {J' : F →L[ℝ] F} (hJ' : ∀ y, J' (J' y) = -y) {T : E →L[ℝ] F}
    (hT : Function.Surjective T) [FiniteDimensional ℝ (LinearMap.ker (T : E →ₗ[ℝ] F))]
    (hodd : Odd (finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)))) :
    IsEmpty (LineOrientation (DetFiber (E := E) (F := F))) := by
  set k := Module.finBasis ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)) with hk
  let A : ℝ → E →L[ℝ] F := fun θ => rotJ J' θ ∘L T ∘L rotJ J (-θ)
  have hAapp : ∀ θ x, A θ x = rotJ J' θ (T (rotJ J (-θ) x)) := fun _ _ => rfl
  have hAc : Continuous A :=
    (continuous_rotJ J').clm_comp (continuous_const.clm_comp ((continuous_rotJ J).comp
      continuous_neg))
  let v : ℝ → Fin (finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F))) → E :=
    fun θ i => rotJ J θ (k i : E)
  have hvc : Continuous v :=
    continuous_pi fun i => (continuous_rotJ J).clm_apply continuous_const
  have hconj : ∀ θ x, A θ (rotJEquiv hJ θ x) = rotJEquiv hJ' θ (T x) := fun θ x => by
    rw [hAapp, rotJEquiv_apply, rotJ_neg_rotJ hJ, rotJEquiv_apply]
  have hv : ∀ θ i, A θ (v θ i) = 0 := fun θ i => by
    have h := hconj θ (k i : E)
    rw [show T (k i : E) = 0 from (k i).2, map_zero] at h
    exact h
  have hs : ∀ θ, Function.Surjective (A θ) := fun θ y => by
    obtain ⟨x, hx⟩ := hT (rotJ J' (-θ) y)
    exact ⟨rotJ J θ x, by rw [hAapp, rotJ_neg_rotJ hJ, hx, rotJ_rotJ_neg hJ']⟩
  have hF : ∀ θ, (A θ).IsFredholm := fun θ =>
    isFredholm_of_surjective_of_finite_ker (hs θ)
      (conjKerEquiv (rotJEquiv hJ θ) (rotJEquiv hJ' θ) (hconj θ)).finiteDimensional
  have hn : ∀ θ, finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)) =
      finrank ℝ (LinearMap.ker (A θ : E →ₗ[ℝ] F)) := fun θ =>
    (conjKerEquiv (rotJEquiv hJ θ) (rotJEquiv hJ' θ) (hconj θ)).finrank_eq
  have hli : ∀ θ, LinearIndependent ℝ (v θ) := fun θ => by
    have h1 : LinearIndependent ℝ fun i => (k i : E) :=
      k.linearIndependent.map' (LinearMap.ker (T : E →ₗ[ℝ] F)).subtype (Submodule.ker_subtype _)
    exact h1.map' ((rotJEquiv hJ θ).toLinearEquiv : E →ₗ[ℝ] E) (LinearEquiv.ker _)
  refine isEmpty_lineOrientation_det_of_kernel_loop hAc hF hs hodd hvc hv hn hli 0 Real.pi
    ?_ fun i => ?_
  · ext x
    rw [hAapp, hAapp, rotJ_pi_apply, rotJ_neg_pi_apply, map_neg, neg_neg, neg_zero,
      rotJ_zero_apply, rotJ_zero_apply]
  · change rotJ J Real.pi (k i : E) = -rotJ J 0 (k i : E)
    rw [rotJ_pi_apply, rotJ_zero_apply]

/-- For finite-dimensional `E`, `F`, every operator is Fredholm. -/
theorem isFredholm_of_finiteDimensional [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (T : E →L[ℝ] F) : T.IsFredholm :=
  isFredholm_of_banach T inferInstance (Submodule.closed_of_finiteDimensional _) inferInstance

/-- **For finite-dimensional `E`, `F` the bundle `DET(E, F)` is orientable**: every operator is
Fredholm, so the base `F(E, F) = L(E, F)` is convex, and `DET(E, F)` has exactly two orientations
(Proposition 6.6.1).  So the remark that `DET(E, F)` is non-orientable (2021, p. 262) does not
hold as we read it for these `E`, `F`. -/
theorem exists_two_lineOrientation_det_of_finiteDimensional [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] :
    ∃ o₁ o₂ : LineOrientation (DetFiber (E := E) (F := F)), o₁ ≠ o₂ ∧
      ∀ o : LineOrientation (DetFiber (E := E) (F := F)), o = o₁ ∨ o = o₂ := by
  have hall : ∀ T : E →L[ℝ] F, T.IsFredholm := isFredholm_of_finiteDimensional
  have hconv : Convex ℝ {T : E →L[ℝ] F | T.IsFredholm} := by
    rw [eq_univ_of_forall hall]
    exact convex_univ
  have hne : ({T : E →L[ℝ] F | T.IsFredholm}).Nonempty := ⟨0, hall 0⟩
  have : Nonempty (FredholmOp E F) := ⟨⟨0, hall 0⟩⟩
  have : ContractibleSpace (FredholmOp E F) := hconv.contractibleSpace hne
  have : LocallyPathConnectedSpace (FredholmOp E F) := hconv.locallyPathConnectedSpace
  exact exists_two_lineOrientation

/-- For finite-dimensional `E`, `F`, `DET(E, F)` has an orientation. -/
theorem nonempty_lineOrientation_det_of_finiteDimensional [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] : Nonempty (LineOrientation (DetFiber (E := E) (F := F))) :=
  let ⟨o, _⟩ := exists_two_lineOrientation_det_of_finiteDimensional (E := E) (F := F)
  ⟨o⟩

end Complex

/-! ### `E = F = H × H` -/

section Prod

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- The complex structure `(x, y) ↦ (−y, x)` of `H × H`. -/
def prodJ (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] : H × H →L[ℝ] H × H :=
  (-ContinuousLinearMap.snd ℝ H H).prod (ContinuousLinearMap.fst ℝ H H)

omit [CompleteSpace H] in
theorem prodJ_prodJ (z : H × H) : prodJ H (prodJ H z) = -z := by
  obtain ⟨x, y⟩ := z
  simp [prodJ]

/-- `ker(S × 1) ≅ ker S`. -/
def kerProdMapIdEquiv (S : H →L[ℝ] H) :
    LinearMap.ker ((S.prodMap (ContinuousLinearMap.id ℝ H) : H × H →L[ℝ] H × H) :
      H × H →ₗ[ℝ] H × H) ≃ₗ[ℝ] LinearMap.ker (S : H →ₗ[ℝ] H) where
  toFun z := ⟨(z : H × H).1, congrArg Prod.fst (z.2 : S.prodMap (ContinuousLinearMap.id ℝ H) z = 0)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := ⟨((x : H), 0), Prod.ext (x.2 : S x = 0) rfl⟩
  left_inv z := Subtype.ext (Prod.ext rfl
    (congrArg Prod.snd (z.2 : S.prodMap (ContinuousLinearMap.id ℝ H) z = 0)).symm)
  right_inv _ := rfl

/-- **(2021, p. 262) `DET(H × H, H × H)` is not orientable** for a Banach space `H` with a
surjective operator `S : H → H` whose kernel has odd finite dimension (for instance, `H`
isomorphic to `ℝ × H`).  The loop is the conjugation of `S × 1` by the rotations of `H × H`. -/
theorem isEmpty_lineOrientation_det_prod {S : H →L[ℝ] H} (hS : Function.Surjective S)
    [FiniteDimensional ℝ (LinearMap.ker (S : H →ₗ[ℝ] H))]
    (hodd : Odd (finrank ℝ (LinearMap.ker (S : H →ₗ[ℝ] H)))) :
    IsEmpty (LineOrientation (DetFiber (E := H × H) (F := H × H))) := by
  have hT : Function.Surjective (S.prodMap (ContinuousLinearMap.id ℝ H)) := fun y => by
    obtain ⟨x, hx⟩ := hS y.1
    exact ⟨(x, y.2), Prod.ext hx rfl⟩
  have : FiniteDimensional ℝ (LinearMap.ker
      ((S.prodMap (ContinuousLinearMap.id ℝ H) : H × H →L[ℝ] H × H) : H × H →ₗ[ℝ] H × H)) :=
    (kerProdMapIdEquiv S).symm.finiteDimensional
  refine isEmpty_lineOrientation_det_of_complexStructure (J := prodJ H) prodJ_prodJ
    (J' := prodJ H) prodJ_prodJ hT ?_
  rw [(kerProdMapIdEquiv S).finrank_eq]
  exact hodd

/-- **`DET(H × H, H × H)` is not orientable when `H ≅ ℝ × H`.** -/
theorem isEmpty_lineOrientation_det_prod_of_equiv (e : H ≃L[ℝ] ℝ × H) :
    IsEmpty (LineOrientation (DetFiber (E := H × H) (F := H × H))) := by
  let S : H →L[ℝ] H := ContinuousLinearMap.snd ℝ ℝ H ∘L (e : H →L[ℝ] ℝ × H)
  have hS : Function.Surjective S := fun y => ⟨e.symm (0, y), by simp [S]⟩
  let φ : LinearMap.ker (S : H →ₗ[ℝ] H) ≃ₗ[ℝ] ℝ :=
    { toFun := fun x => (e (x : H)).1
      map_add' := fun x y => by simp
      map_smul' := fun a x => by simp
      invFun := fun t => ⟨e.symm (t, 0), by simp [S]⟩
      left_inv := fun x => Subtype.ext (by
        have h2 : (e (x : H)).2 = 0 := x.2
        have : ((e (x : H)).1, (0 : H)) = e (x : H) := Prod.ext rfl h2.symm
        simp [this])
      right_inv := fun t => by simp }
  have : FiniteDimensional ℝ (LinearMap.ker (S : H →ₗ[ℝ] H)) := φ.symm.finiteDimensional
  refine isEmpty_lineOrientation_det_prod hS ?_
  rw [φ.finrank_eq, Module.finrank_self]
  exact odd_one

end Prod

end Polyfold
