import Polyfold.Chapter4.UntamedBundleTheorem
import Polyfold.Chapter6.OrientationMainClean
import Polyfold.Chapter5.SobolevRemarkAbstract

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §6.2 and §6.6:
**Definition 6.2.1** and **Proposition 6.2.2** (p. 201), **Theorem 6.6.11** (p. 272), read with the
2021 sc-Fredholm notion of **Definitions 3.1.16 = 3.6.4** (pp. 96, 135), whose germ data
(Definition 3.6.3 with the filling of Definitions 3.1.4/3.6.1) need not sit in a tame chart.

# The index of the untamed example jumps, and there is no local propagation at `x₀`

## The text, paraphrased

(Definition 6.2.1) At a smooth point `x` the linearizations `(f − s)'(x) : T_xX → Y_x`, `s` an
sc⁺-section with `s(x) = f(x)`, are sc-Fredholm of one index `ind(f, x)`.  (Proposition 6.2.2) The
index is locally constant on `X_∞`.  (Theorem 6.6.11) Every smooth point has an open neighbourhood
in which the orientations of `DET(f, ·)` are propagated along sc-smooth paths, by a push-forward
which depends only on the end points; the push-forward along a path `φ` is the continuation in the
determinant of the bundle of the stabilized kernels
`ker((f − s(·, t))'(φ(t)) ⊕ (λ ↦ Σ λᵢ sᵢ(φ(t), t)))`, a vector bundle over `[0, 1]`.

## What is formalized

In general, for an sc-Fredholm section `f` (germ data in any compatible chart):

* `finrank_ker_coprod_eq_fredholmIndex_add`: for `T` Fredholm and `T ⊕ φ : E × ℝᵏ → F` onto,
  `dim ker(T ⊕ φ) = ind T + k`.
* `IsStabKernels.rank_eq_index_add`: the rank of a family of stabilized kernels along `y` is
  `ind(f, y(q)) + k` at every parameter `q`.
* `isIndexAt_eq_of_isPush`: **if there is a push-forward datum along `γ`, then
  `ind(f, γ(0)) = ind(f, γ(1))`**; `HasLocalPropagation.isIndexAt_eq`: in a set with the local
  propagation property the index is the same at the two ends of every sc-smooth path.

For the strong bundle `bundle : K → O` over the tame M-polyfold without boundary `O ≅ ℝ` and its
section `sec` (`Chapter3/UntamedBundle.lean`; parameter `t`, the point `x₀` is `t = 0`, the fibre
is `0` for `t ≤ 0` and a line for `0 < t < 1`):

* `isScFredholmSection_sec`, `hasScPlusSectionsThrough_bundle`, `admitsBumpFunctions_polyO`.
* `finrank_T_base`, `finrank_K_base_of_nonpos`, `finrank_K_base_of_pos`: in the chart `chart0`,
  `dim T_zO = 1`, and `dim K_z = 0` for `t ≤ 0`, `dim K_z = 1` for `0 < t < 1`.
* `isIndexAt_sec_of_nonpos`, `isIndexAt_sec_of_pos`: **`ind(sec, x) = 1` for `t(x) ≤ 0` and
  `ind(sec, x) = 0` for `0 < t(x) < 1`** (`StrongBundle.IsIndexAt`, in every chart).
* `not_index_locally_constant_sec`: no neighbourhood of `x₀` carries one index: the conclusion of
  Proposition 6.2.2 does not hold at `x₀` for `(bundle, sec)`.
* `scPathO`, `isScSmoothMap_scPathO`: the sc-smooth path `s ↦ t = ε (2 σ(s) − 1)` through `x₀`
  (`σ` the smooth transition function).
* `not_hasLocalPropagation_sec`: **for every chart `c` of the structure and every open `U ∋ x₀`,
  `U` does not have the local propagation property** (`HasLocalPropagation`);
  `not_isPropagationNbhd_sec`: no open set containing `x₀` is a propagation neighbourhood;
  `not_theorem_6_6_11_conclusion`: the conclusion of `theorem_6_6_11` does not hold at `x₀`.
* `theorem_6_6_11_untamed_not`: **the statement of `theorem_6_6_11` with `IsScFredholmSection`
  (2021 Definitions 3.1.16 = 3.6.4) in place of `IsScFredholmSectionTame` does not hold as we
  read it**; `proposition_6_2_2_untamed_not`: the same for the local constancy of the index.

## What this says about the text

The example meets the printed hypotheses: `O` is a tame M-polyfold without boundary, with
sc-smooth bump functions; `K → O` is a tame strong bundle; `sec` is an sc-Fredholm section in the
sense of 2021 Definitions 3.1.16 = 3.6.4; every point is smooth.  The germ of `sec` at `x₀` has no
germ data in a tame chart (`not_isScFredholmGermTame_sec_zero`).  With germ data in tame charts the
statements are `isIndexAt_const_of_path` and `theorem_6_6_11`.  The solution set of `sec` is
`{t ≤ 0}`, on which the index is `1`; the jump is seen at the smooth points `t > 0`, which are not
zeros of `sec`, through Definition 6.2.1.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

universe u v

/-! ### Finite-dimensional linear algebra -/

section LinearAlgebra

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- For `T` Fredholm and `T ⊕ φ : E × ℝᵏ → F` onto, `dim ker(T ⊕ φ) = ind T + k`. -/
theorem finrank_ker_coprod_eq_fredholmIndex_add {T : E →L[ℝ] F} {k : ℕ}
    {φ : (Fin k → ℝ) →L[ℝ] F} (hT : T.IsFredholm) (hφ : Surjective (T.coprod φ)) :
    (finrank ℝ (LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F)) : ℤ) = fredholmIndex T + k := by
  have := hT.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have := finiteDimensional_ker_coprod (T := T) (φ := φ)
  have h1 := LinearMap.finrank_le_finrank_of_injective (stabJ_injective (T := T) (φ := φ))
  have e1 := stab_card_eq hT hφ rfl (Nat.add_sub_cancel' h1)
  unfold fredholmIndex linIndex
  omega

/-- The index of an operator between finite-dimensional spaces is `dim E − dim F`. -/
theorem fredholmIndex_of_finiteDimensional [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (L : E →L[ℝ] F) : fredholmIndex L = (finrank ℝ E : ℤ) - finrank ℝ F := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (L : E →ₗ[ℝ] F)
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range (L : E →ₗ[ℝ] F))
  unfold fredholmIndex linIndex
  omega

end LinearAlgebra

/-! ### A push-forward datum keeps the index -/

section General

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **The rank of the stabilized kernels is `ind(f, y(q)) + k`** (Definition 6.2.1 and
pp. 221–223): at the parameter `q`, `T_q ⊕ φ_q` is onto and `Λ_q ≅ ker(T_q ⊕ φ_q)`, with
`T_q = (f + S_q)'(y(q)) ∈ Lin(f, y(q))`. -/
theorem IsStabKernels.rank_eq_index_add {Q : Type*} [TopologicalSpace Q]
    {c : StrongBundleChart PX P} {hc : B.IsChart c} {y : Q → X} {hy : ∀ q, y q ∈ c.φ.source}
    {S : Q → X → Y} {k : ℕ} {s : Fin k → Q → X → Y}
    {Λ : SubspaceFamily Q (c.φ.model.E 0 × (Fin k → ℝ))}
    (hΛ : IsStabKernels f c hc y hy S s Λ) (hf : B.IsScFredholmSection f) (q : Q)
    (hxs : y q ∈ PX.smoothSet) {i : ℤ} (hi : B.IsIndexAt f (y q) i) : (Λ.n : ℤ) = i + k := by
  obtain ⟨z, hz⟩ := hΛ.exists_lift q
  have hT := (chartPt c hc (hy q) z hz).stabT_mem_linSet hf (hΛ.isScPlusSection q) (hΛ.zero q) hxs
  obtain ⟨hsurj, hL⟩ := hΛ.spec q rfl (hy q) z hz
    ((chartPt c hc (hy q) z hz).stabT hf (hΛ.isScPlusSection q) (hΛ.zero q)) (fun _ => rfl)
    ((chartPt c hc (hy q) z hz).stabPhi (fun i => s i q) (fun i => hΛ.isSection i q))
    (fun μ => ChartPoint.coe_stabPhi _ _ _ μ)
  obtain ⟨hF, hidx⟩ := (chartPt c hc (hy q) z hz).fredholmIndex_of_mem_linSet hf hi hT
  have e := (kerEquivMap (chartPt c hc (hy q) z hz).T.subtypeL Subtype.val_injective hL).finrank_eq
  rw [Λ.finrank_eq q] at e
  rw [← hidx, ← finrank_ker_coprod_eq_fredholmIndex_add hF hsurj, e]

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- **A push-forward datum along `γ` forces `ind(f, γ(0)) = ind(f, γ(1))`**: the stabilized
kernels along `γ` form a family of subspaces of one rank over `[0, 1]`, and the rank at `t` is
`ind(f, γ(t)) + k` (`IsStabKernels.rank_eq_index_add`). -/
theorem isIndexAt_eq_of_isPush {hf : B.IsScFredholmSection f} {c : StrongBundleChart PX P}
    {hc : B.IsChart c} {γ : (Fin 1 → ℝ) → X} {hγ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ c.φ.source}
    {x₀ x₁ : X} {h₀ : γ (pt1 0) = x₀} {h₁ : γ (pt1 1) = x₁} {hx₀ : x₀ ∈ c.φ.source}
    {hx₁ : x₁ ∈ c.φ.source} {hs₀ : x₀ ∈ PX.smoothSet} {hs₁ : x₁ ∈ PX.smoothSet}
    {e : (chartPtOf c hc hx₀ hs₀).Or f hf ≃ (chartPtOf c hc hx₁ hs₁).Or f hf}
    (he : IsPush f hf c hc γ hγ h₀ h₁ hx₀ hx₁ hs₀ hs₁ e) {i j : ℤ} (hi : B.IsIndexAt f x₀ i)
    (hj : B.IsIndexAt f x₁ j) : i = j := by
  obtain ⟨S, -, -, k, s, -, Λ, hΛ, -⟩ := he
  subst h₀ h₁
  have e0 := hΛ.rank_eq_index_add hf ⟨pt1 0, pt1_mem_Icc (left_mem_Icc.2 zero_le_one)⟩ hs₀ hi
  have e1 := hΛ.rank_eq_index_add hf ⟨pt1 1, pt1_mem_Icc (right_mem_Icc.2 zero_le_one)⟩ hs₁ hj
  omega

/-- **In a set with the local propagation property the index is the same at the two ends of
every sc-smooth path** (with smooth end points). -/
theorem HasLocalPropagation.isIndexAt_eq {hf : B.IsScFredholmSection f}
    {c : StrongBundleChart PX P} {hc : B.IsChart c} {U : Set X}
    (hU : HasLocalPropagation f hf c hc U) {γ : (Fin 1 → ℝ) → X}
    (hγs : (rnPolyfold 1).IsScSmoothMap PX γ) (hγ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ U)
    (hs₀ : γ (pt1 0) ∈ PX.smoothSet) (hs₁ : γ (pt1 1) ∈ PX.smoothSet) {i j : ℤ}
    (hi : B.IsIndexAt f (γ (pt1 0)) i) (hj : B.IsIndexAt f (γ (pt1 1)) j) : i = j := by
  obtain ⟨e, he⟩ := hU.exists_isPush γ hγs hγ rfl rfl
    (hU.subset (hγ _ (pt1_mem_Icc (left_mem_Icc.2 zero_le_one))))
    (hU.subset (hγ _ (pt1_mem_Icc (right_mem_Icc.2 zero_le_one)))) hs₀ hs₁
  exact isIndexAt_eq_of_isPush he hi hj

end General

/-! ### The untamed example: the section, sections through points, bump functions -/

namespace UntamedCorner

open ScOneExample Jump StrongRetr

/-- `sec` is an sc-Fredholm section (2021 Definitions 3.1.16 = 3.6.4). -/
theorem isScFredholmSection_sec : bundle.IsScFredholmSection sec :=
  StrongBundle.isScFredholmSection2021_iff.1 isScFredholmSection2021_sec

/-- Every point of `O` is smooth. -/
lemma mem_smoothSet_polyO (x : Ob) : x ∈ polyO.smoothSet := smoothSet_polyO ▸ mem_univ x

/-- `K → O` has sc⁺-sections through every smooth fibre point (the chart `chart0` is over all of
`O`). -/
theorem hasScPlusSectionsThrough_bundle : bundle.HasScPlusSectionsThrough :=
  StrongBundle.hasScPlusSectionsThrough_of_chart (c := chart0) (mem_singleton _) rfl

/-- **`O` admits sc-smooth bump functions** (it has a chart onto an open subset of `ℝ¹`). -/
theorem admitsBumpFunctions_polyO : polyO.AdmitsBumpFunctions :=
  MPolyfold.admitsBumpFunctions_of_hasContDiffBump fun x =>
    ⟨chartT, isChart_chartT, mem_univ x, fun v : Fin 1 → ℝ => Real.smoothTransition (1 - v 0 ^ 2),
      Real.smoothTransition.contDiff.comp
        (contDiff_const.sub ((contDiff_apply ℝ ℝ (0 : Fin 1)).pow 2)),
      fun h => by
        have h1 : Real.smoothTransition (1 - (0 : Fin 1 → ℝ) 0 ^ 2) = 0 := congrFun h 0
        rw [Pi.zero_apply, zero_pow two_ne_zero, sub_zero, Real.smoothTransition.one] at h1
        exact one_ne_zero h1,
      (Metric.isBounded_closedBall (x := (0 : Fin 1 → ℝ)) (r := 1)).subset fun v hv => by
        have hpos : 0 < 1 - v 0 ^ 2 := by
          by_contra hle
          exact hv (Real.smoothTransition.zero_of_nonpos (not_lt.1 hle))
        rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
        intro i
        rw [Subsingleton.elim i 0, Real.norm_eq_abs]
        exact (abs_le_one_iff_mul_self_le_one.2 (by nlinarith)) ⟩

/-! ### The chart point of `chart0` at a point of `O` -/

/-- The chart point of `chart0` at `x`. -/
def basePt (x : Ob) : ChartPoint bundle x :=
  chartPtOf chart0 isChart_chart0 (mem_univ x) (mem_smoothSet_polyO x)

/-- `Dr(z) = r` at every level-`1` point of `U` (`r` is linear). -/
lemma scDeriv_r_eq {z : E 1} (hz : E.toBase 1 z ∈ U) : scDeriv U (r R) z = rOp 0 :=
  scDeriv_eq_of_hasFDerivAt (z := z) relOpen_U
    ((isStrongBundleRetraction_R.baseRetraction relOpen_U).isScSmooth.isSc1)
    (show z ∈ E.lvlSet U 1 from hz) (rOp 0).hasFDerivAt

lemma toBase_z_basePt (x : Ob) : E.toBase 1 (basePt x).z = (x : E 0) := (basePt x).toBase_z

/-- `T_zO` in `chart0` is the line `{((0, s), 0)}`. -/
lemma mem_T_basePt {x : Ob} {p : E 0} :
    p ∈ (basePt x).T ↔ ∃ s : ℝ, (((0, s), 0) : E 0) = p := by
  have key : scDeriv U (r R) (basePt x).z = rOp 0 := scDeriv_r_eq (basePt x).mem_U
  change (∃ q : E 0, scDeriv U (r R) (basePt x).z q = p) ↔ _
  rw [key]
  exact ⟨fun ⟨q, hq⟩ => ⟨q.1.2, hq⟩, fun ⟨s, hs⟩ => ⟨((0, s), 0), hs⟩⟩

/-- **`dim T_zO = 1`** in `chart0`. -/
theorem finrank_T_base (x : Ob) : finrank ℝ ↥(basePt x).T = 1 := by
  refine finrank_eq_one_iff'.2 ⟨⟨(((0, 1), 0) : E 0), mem_T_basePt.2 ⟨1, rfl⟩⟩, fun h => ?_,
    fun w => ?_⟩
  · have h1 : ((((0 : ℝ), (1 : ℝ)), (0 : X 0)) : E 0) = 0 := congrArg Subtype.val h
    exact one_ne_zero (α := ℝ) (congrArg (fun p : E 0 => p.1.2) h1)
  · obtain ⟨s, hs⟩ := mem_T_basePt.1 w.2
    refine ⟨s, Subtype.ext ?_⟩
    change s • ((((0 : ℝ), (1 : ℝ)), (0 : X 0)) : E 0) = (w.1 : E 0)
    rw [← hs]
    exact Prod.ext (Prod.ext (mul_zero s) (mul_one s)) (smul_zero s)

/-- `K_z` in `chart0`: the vectors `(0, π_t k)`. -/
lemma mem_K_basePt {x : Ob} {h : F 0} :
    h ∈ (basePt x).K ↔ ∃ k : F 0, ((0, proj (tco x) k.2) : F 0) = h := by
  have e : (E.toBase 1 (basePt x).z).1.2 = tco x :=
    congrArg (fun p : E 0 => p.1.2) (toBase_z_basePt x)
  have key : ∀ k : F 0, ρCLM isStrongBundleRetraction_R (basePt x).mem_U k =
      ((0, proj (tco x) k.2) : F 0) := fun k => by
    change ((0, proj (E.toBase 1 (basePt x).z).1.2 k.2) : F 0) = _
    rw [e]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, (key k).symm.trans hk⟩, fun ⟨k, hk⟩ => ⟨k, (key k).trans hk⟩⟩

lemma eq_zero_of_mem_K_basePt {x : Ob} (hx : tco x ≤ 0) {h : F 0} (hh : h ∈ (basePt x).K) :
    h = 0 := by
  obtain ⟨k, rfl⟩ := mem_K_basePt.1 hh
  rw [proj_of_nonpos hx]
  rfl

lemma subsingleton_K_basePt {x : Ob} (hx : tco x ≤ 0) : Subsingleton ↥(basePt x).K :=
  ⟨fun a b => Subtype.ext
    ((eq_zero_of_mem_K_basePt hx a.2).trans (eq_zero_of_mem_K_basePt hx b.2).symm)⟩

/-- **`dim K_z = 0` for `t ≤ 0`** in `chart0`. -/
theorem finrank_K_base_of_nonpos {x : Ob} (hx : tco x ≤ 0) : finrank ℝ ↥(basePt x).K = 0 :=
  have := subsingleton_K_basePt hx
  finrank_zero_of_subsingleton

/-- **`dim K_z = 1` for `0 < t < 1`** in `chart0`: `K_z` is spanned by `(0, π_t v)`. -/
theorem finrank_K_base_of_pos {x : Ob} (hx : 0 < tco x) : finrank ℝ ↥(basePt x).K = 1 := by
  have ht : tco x ∈ Ioo (0 : ℝ) 1 := ⟨hx, (mem_O.1 x.2).2.1⟩
  refine finrank_eq_one_iff'.2 ⟨⟨((0, proj (tco x) v) : F 0), mem_K_basePt.2 ⟨(0, v), rfl⟩⟩,
    fun h => qf_ne_zero ht ?_, fun w => ?_⟩
  · have h1 : ((0, proj (tco x) v) : F 0) = 0 := congrArg Subtype.val h
    have h2 : proj (tco x) v = 0 := congrArg Prod.snd h1
    change nu (proj (tco x) v) = 0
    rw [h2, map_zero]
  · obtain ⟨k, hk⟩ := mem_K_basePt.1 w.2
    have h1 := frame1.fr_co (tco x) ht (proj (tco x) k.2) (proj_proj ht.2 _)
    change proj (tco x) ((frame1.co (tco x) (proj (tco x) k.2) 0) • v) = _ at h1
    rw [map_smul] at h1
    refine ⟨frame1.co (tco x) (proj (tco x) k.2) 0, Subtype.ext ?_⟩
    change frame1.co (tco x) (proj (tco x) k.2) 0 • ((0, proj (tco x) v) : F 0) = (w.1 : F 0)
    rw [← hk]
    exact Prod.ext (mul_zero _) h1

/-! ### The index -/

/-- The index of `(sec, x)` is `dim T_zO − dim K_z` in `chart0`, when both are finite. -/
theorem isIndexAt_sec_basePt (x : Ob) [FiniteDimensional ℝ ↥(basePt x).T]
    [FiniteDimensional ℝ ↥(basePt x).K] :
    bundle.IsIndexAt sec x ((finrank ℝ ↥(basePt x).T : ℤ) - finrank ℝ ↥(basePt x).K) := by
  obtain ⟨L, hL⟩ := (basePt x).linSet_nonempty isScFredholmSection_sec (mem_smoothSet_polyO x)
    hasScPlusSectionsThrough_bundle
  have h := ((basePt x).isFredholm_isIndexAt_of_mem_linSet isScFredholmSection_sec hL).2
  rwa [fredholmIndex_of_finiteDimensional] at h

/-- **`ind(sec, x) = 1` for `t(x) ≤ 0`** (the fibre is `0`). -/
theorem isIndexAt_sec_of_nonpos {x : Ob} (hx : tco x ≤ 0) : bundle.IsIndexAt sec x 1 := by
  have : FiniteDimensional ℝ ↥(basePt x).T :=
    Module.finite_of_finrank_pos (by rw [finrank_T_base]; exact one_pos)
  have := subsingleton_K_basePt hx
  have h := isIndexAt_sec_basePt x
  rwa [finrank_T_base, finrank_K_base_of_nonpos hx, Nat.cast_one, Nat.cast_zero, sub_zero] at h

/-- **`ind(sec, x) = 0` for `0 < t(x) < 1`** (the fibre is a line). -/
theorem isIndexAt_sec_of_pos {x : Ob} (hx : 0 < tco x) : bundle.IsIndexAt sec x 0 := by
  have : FiniteDimensional ℝ ↥(basePt x).T :=
    Module.finite_of_finrank_pos (by rw [finrank_T_base]; exact one_pos)
  have : FiniteDimensional ℝ ↥(basePt x).K :=
    Module.finite_of_finrank_pos (by rw [finrank_K_base_of_pos hx]; exact one_pos)
  have h := isIndexAt_sec_basePt x
  rwa [finrank_T_base, finrank_K_base_of_pos hx, Nat.cast_one, sub_self] at h

/-- The index of `(sec, x)`: `1` for `t(x) ≤ 0`, `0` for `t(x) > 0`. -/
theorem isIndexAt_sec_iff {x : Ob} {i : ℤ} :
    bundle.IsIndexAt sec x i ↔ i = if tco x ≤ 0 then 1 else 0 := by
  by_cases hx : tco x ≤ 0
  · rw [if_pos hx]
    exact ⟨fun h => h.unique isScFredholmSection_sec (isIndexAt_sec_of_nonpos hx),
      fun h => h ▸ isIndexAt_sec_of_nonpos hx⟩
  · rw [if_neg hx]
    exact ⟨fun h => h.unique isScFredholmSection_sec (isIndexAt_sec_of_pos (not_le.1 hx)),
      fun h => h ▸ isIndexAt_sec_of_pos (not_le.1 hx)⟩

/-- **The index is not locally constant at `x₀`**: no open neighbourhood of `x₀` carries one index
(the conclusion of Proposition 6.2.2 in its local form). -/
theorem not_index_locally_constant_sec :
    ¬ ∃ (V : Set Ob) (i : ℤ), IsOpen V ∧ x0 ∈ V ∧ ∀ y ∈ V, bundle.IsIndexAt sec y i := by
  rintro ⟨V, i, hV, h0, hall⟩
  have hc : Continuous fun s : ℝ => ptO (min s (1 / 2))
      (lt_of_le_of_lt (min_le_right _ _) (by norm_num)) :=
    ((continuous_const.prodMk (continuous_id.min continuous_const)).prodMk
      continuous_const).subtype_mk _
  have h00 : ptO (min 0 (1 / 2)) (lt_of_le_of_lt (min_le_right _ _) (by norm_num)) = x0 :=
    tco_injective (min_eq_left (by norm_num))
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (hV.preimage hc) 0
    (by rw [mem_preimage, h00]; exact h0)
  have hm : min (δ / 2) (1 / 2) ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (lt_min (by linarith) (by norm_num))]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have h1 := hall _ (hball hm)
  have h2 : (0 : ℝ) < tco (ptO (min (min (δ / 2) (1 / 2)) (1 / 2))
      (lt_of_le_of_lt (min_le_right _ _) (by norm_num))) :=
    lt_min (lt_min (by linarith) (by norm_num)) (by norm_num)
  have e1 := h1.unique isScFredholmSection_sec (isIndexAt_sec_of_pos h2)
  have e2 := (hall x0 h0).unique isScFredholmSection_sec
    (isIndexAt_sec_of_nonpos (x := x0) le_rfl)
  omega

/-! ### An sc-smooth path through `x₀` -/

lemma tco_chartT_symm {q : Fin 1 → ℝ} (hq : q 0 < 1) : tco (chartT.symm q) = q 0 := by
  change tco (if h : q 0 < 1 then (⟨sigmaOp 0 q, mem_O.2 ⟨rfl, h, rfl⟩⟩ : Ob)
    else ⟨0, zero_mem_O⟩) = _
  rw [dif_pos hq]
  rfl

/-- The coordinate `t = ε (2 σ(s) − 1)` of the path, `σ` the smooth transition function. -/
def pathCo (ε : ℝ) (p : Fin 1 → ℝ) : Fin 1 → ℝ :=
  fun _ => ε * (2 * Real.smoothTransition (p 0) - 1)

/-- **The path `s ↦ t = ε (2 σ(s) − 1)` in `O`**, from `t = −ε` through `x₀` to `t = ε`. -/
def scPathO (ε : ℝ) (p : Fin 1 → ℝ) : Ob := chartT.symm (pathCo ε p)

lemma abs_pathCo_le {ε : ℝ} (hε : 0 ≤ ε) (p : Fin 1 → ℝ) : |pathCo ε p 0| ≤ ε := by
  have h0 := Real.smoothTransition.nonneg (p 0)
  have h1 := Real.smoothTransition.le_one (p 0)
  change |ε * (2 * Real.smoothTransition (p 0) - 1)| ≤ ε
  rw [abs_mul, abs_of_nonneg hε]
  exact mul_le_of_le_one_right hε (abs_le.2 ⟨by linarith, by linarith⟩)

lemma tco_scPathO {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1) (p : Fin 1 → ℝ) :
    tco (scPathO ε p) = ε * (2 * Real.smoothTransition (p 0) - 1) :=
  tco_chartT_symm (lt_of_le_of_lt ((le_abs_self _).trans (abs_pathCo_le h0 p)) h1)

/-- The path is sc-smooth. -/
theorem isScSmoothMap_scPathO {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1) :
    (rnPolyfold 1).IsScSmoothMap polyO (scPathO ε) := by
  have hG : IsScSmooth (E := rnSc 1) (F := rnSc 1) univ (pathCo ε) :=
    IsScSmooth.of_contDiffOn_finiteDimensional (V := Fin 1 → ℝ) (isScDomain_univ _)
      (contDiff_pi.2 fun _ => contDiff_const.mul (((contDiff_const.mul
        (Real.smoothTransition.contDiff.comp (contDiff_apply ℝ ℝ (0 : Fin 1)))).sub
          contDiff_const))).contDiffOn
  exact isScSmoothMap_rn_chart_symm isChart_chartT (G := pathCo ε) hG fun a =>
    show pathCo ε a 0 < 1 from lt_of_le_of_lt ((le_abs_self _).trans (abs_pathCo_le h0 a)) h1

/-- Every neighbourhood of `x₀` contains the points with `|t| ≤ ε` for some `0 < ε < 1`. -/
lemma exists_eps_of_mem_open {U : Set Ob} (hU : IsOpen U) (h0 : x0 ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ x : Ob, |tco x| ≤ ε → x ∈ U := by
  have hc : Continuous fun s : ℝ => ptO (min s (1 / 2))
      (lt_of_le_of_lt (min_le_right _ _) (by norm_num)) :=
    ((continuous_const.prodMk (continuous_id.min continuous_const)).prodMk
      continuous_const).subtype_mk _
  have h00 : ptO (min 0 (1 / 2)) (lt_of_le_of_lt (min_le_right _ _) (by norm_num)) = x0 :=
    tco_injective (min_eq_left (by norm_num))
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (hU.preimage hc) 0
    (by rw [mem_preimage, h00]; exact h0)
  refine ⟨min (δ / 2) (1 / 2), lt_min (by linarith) (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), fun x hx => ?_⟩
  have hx1 : |tco x| ≤ δ / 2 := hx.trans (min_le_left _ _)
  have hx2 : tco x ≤ 1 / 2 := (le_abs_self _).trans (hx.trans (min_le_right _ _))
  have hm : tco x ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    linarith
  have hxe : ptO (min (tco x) (1 / 2)) (lt_of_le_of_lt (min_le_right _ _) (by norm_num)) = x :=
    tco_injective (min_eq_left hx2)
  have := hball hm
  rwa [mem_preimage, hxe] at this

/-! ### No local propagation at `x₀` -/

/-- **No neighbourhood of `x₀` has the local propagation property, in any chart**: along the path
`scPathO ε` in `U` from `t = −ε` to `t = ε` a push-forward datum would be a family of subspaces
over `[0, 1]` of rank `1 + k` at `0` and of rank `k` at `1`. -/
theorem not_hasLocalPropagation_sec (c : StrongBundleChart polyO kproj) (hc : bundle.IsChart c)
    {U : Set Ob} (hU : IsOpen U) (h0 : x0 ∈ U) :
    haveI := paracompactSpace_rn_prod polyO
    haveI := paracompactSpace_rn_pullback bundle
    ¬ HasLocalPropagation sec isScFredholmSection_sec c hc U := by
  have := paracompactSpace_rn_prod polyO
  have := paracompactSpace_rn_pullback bundle
  intro h
  obtain ⟨ε, hε0, hε1, hεU⟩ := exists_eps_of_mem_open hU h0
  have hγ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, scPathO ε q ∈ U := fun q _ =>
    hεU _ (by rw [tco_scPathO hε0.le hε1]; exact abs_pathCo_le hε0.le q)
  have e0 : tco (scPathO ε (pt1 0)) ≤ 0 := by
    rw [tco_scPathO hε0.le hε1, pt1_apply, Real.smoothTransition.zero]
    linarith
  have e1 : 0 < tco (scPathO ε (pt1 1)) := by
    rw [tco_scPathO hε0.le hε1, pt1_apply, Real.smoothTransition.one]
    linarith
  have := h.isIndexAt_eq (isScSmoothMap_scPathO hε0.le hε1) hγ (mem_smoothSet_polyO _)
    (mem_smoothSet_polyO _) (isIndexAt_sec_of_nonpos e0) (isIndexAt_sec_of_pos e1)
  exact one_ne_zero this

/-- **No open set containing `x₀` is a propagation neighbourhood** (`IsPropagationNbhd`, the good
sets of Theorems 6.6.13 and 6.6.17). -/
theorem not_isPropagationNbhd_sec :
    haveI := paracompactSpace_rn_prod polyO
    haveI := paracompactSpace_rn_pullback bundle
    ¬ ∃ U : Set Ob, IsPropagationNbhd sec isScFredholmSection_sec U ∧ x0 ∈ U := by
  rintro ⟨U, ⟨c, hc, hUo, hLP⟩, h0⟩
  exact not_hasLocalPropagation_sec c hc hUo h0 hLP

/-- **The conclusion of `theorem_6_6_11` (2021 Theorem 6.6.11) does not hold at `x₀` for
`(bundle, sec)`.** -/
theorem not_theorem_6_6_11_conclusion :
    haveI := paracompactSpace_rn_prod polyO
    haveI := paracompactSpace_rn_pullback bundle
    ¬ ∃ (c : StrongBundleChart polyO kproj) (hc : bundle.IsChart c) (U : Set Ob), IsOpen U ∧
      x0 ∈ U ∧ HasLocalPropagation sec isScFredholmSection_sec c hc U := by
  rintro ⟨c, hc, U, hUo, h0, hLP⟩
  exact not_hasLocalPropagation_sec c hc hUo h0 hLP

/-- **The untamed example and the hypotheses of §6.2 and §6.6**: `O` is a tame M-polyfold without
boundary which admits sc-smooth bump functions, `K → O` is a tame strong bundle with sc⁺-sections
through every smooth fibre point, every point of `O` is smooth, `sec` is an sc-Fredholm section in
the sense of 2021 Definitions 3.1.16 = 3.6.4 (equivalently `IsScFredholmSection`), with germ data
in tame charts at every point other than `x₀`, and not at `x₀`. -/
theorem untamed_example_hypotheses :
    polyO.IsTame ∧ polyO.IsWithoutBoundary ∧ polyO.AdmitsBumpFunctions ∧ bundle.IsTameBundle ∧
    bundle.HasScPlusSectionsThrough ∧ polyO.smoothSet = univ ∧
    bundle.IsScFredholmSection2021 sec ∧ bundle.IsScFredholmSection sec ∧
    (∀ x, x ≠ x0 → bundle.IsScFredholmGermTame sec x) ∧
    ¬ bundle.IsScFredholmGermTame sec x0 ∧ ¬ bundle.IsScFredholmSectionTame sec :=
  ⟨isTame_polyO, isWithoutBoundary_polyO, admitsBumpFunctions_polyO, isTameBundle_bundle,
    hasScPlusSectionsThrough_bundle, smoothSet_polyO, isScFredholmSection2021_sec,
    isScFredholmSection_sec, fun _ hx => isScFredholmGermTame_sec_of_ne hx,
    not_isScFredholmGermTame_sec_zero,
    fun h => not_isScFredholmGermTame_sec_zero (h.germTame x0 (mem_smoothSet_polyO x0))⟩

/-- **2021 Theorem 6.6.11, p. 272, read with the 2021 sc-Fredholm notion, does not hold as we read
it**: the statement of `theorem_6_6_11` with `IsScFredholmSection2021` (Definitions
3.1.16 = 3.6.4, no tameness of the chart of the germ data) in place of `IsScFredholmSectionTame`,
for a tame strong bundle (`IsTameBundle`) over an M-polyfold with bump functions.  The
counterexample is `(bundle, sec, x₀)`.  With germ data in tame charts the statement is
`theorem_6_6_11`. -/
theorem theorem_6_6_11_untamed_not :
    ¬ ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      (Y : Type) [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle PX P)
      (f : X → Y) (x : X), B.IsTameBundle → PX.AdmitsBumpFunctions →
      ∀ hf : B.IsScFredholmSection2021 f, x ∈ PX.smoothSet →
      haveI := paracompactSpace_rn_prod PX
      haveI := paracompactSpace_rn_pullback B
      ∃ (c : StrongBundleChart PX P) (hc : B.IsChart c) (U : Set X), IsOpen U ∧ x ∈ U ∧
        HasLocalPropagation f (StrongBundle.isScFredholmSection2021_iff.1 hf) c hc U := fun h =>
  not_theorem_6_6_11_conclusion (h Ob polyO Kt kproj bundle sec x0 isTameBundle_bundle
    admitsBumpFunctions_polyO isScFredholmSection2021_sec (mem_smoothSet_polyO x0))

/-- **2021 Proposition 6.2.2, p. 201, read with the 2021 sc-Fredholm notion, does not hold as we
read it**: the statement of `proposition_6_2_2_local'` with `IsScFredholmSection2021` in place of
`IsScFredholmSectionTame`, for a tame strong bundle over an M-polyfold with bump functions.  The
counterexample is `(bundle, sec)` and the path `scPathO (1/2)`, from `t = −1/2` (index `1`) to
`t = 1/2` (index `0`). -/
theorem proposition_6_2_2_untamed_not :
    ¬ ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      (Y : Type) [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle PX P)
      (f : X → Y), B.IsTameBundle → PX.AdmitsBumpFunctions → B.IsScFredholmSection2021 f →
      ∀ φ : (Fin 1 → ℝ) → X, (rnPolyfold 1).IsScSmoothMap PX φ → ∀ i j : ℤ,
        B.IsIndexAtLocal f (φ 0) i → B.IsIndexAtLocal f (φ 1) j → i = j := fun h => by
  have h0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have h1 : (1 / 2 : ℝ) < 1 := by norm_num
  have e0 : tco (scPathO (1 / 2) (0 : Fin 1 → ℝ)) ≤ 0 := by
    rw [tco_scPathO h0 h1, Pi.zero_apply, Real.smoothTransition.zero]
    norm_num
  have e1 : 0 < tco (scPathO (1 / 2) (1 : Fin 1 → ℝ)) := by
    rw [tco_scPathO h0 h1, Pi.one_apply, Real.smoothTransition.one]
    norm_num
  have := h Ob polyO Kt kproj bundle sec isTameBundle_bundle admitsBumpFunctions_polyO
    isScFredholmSection2021_sec (scPathO (1 / 2)) (isScSmoothMap_scPathO h0 h1) 1 0
    ((isIndexAt_sec_of_nonpos e0).isIndexAtLocal isScFredholmSection_sec)
    ((isIndexAt_sec_of_pos e1).isIndexAtLocal isScFredholmSection_sec)
  exact one_ne_zero this

end UntamedCorner

end Polyfold
