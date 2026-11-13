import Polyfold.Chapter14.P3W3B1_BoundaryStructured
import Polyfold.Chapter14.P3W3B2_Cover
import Polyfold.Chapter13.P3D_Structurable
import Polyfold.Chapter13.P3A_AtomicConstruction
import Polyfold.Chapter13.P3W3Q_AtomicSum
import Polyfold.Chapter7.PartitionsOfUnity

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), the end of the proof of
the **∂-Extension Theorem 14.1.9**, pp. 646 and 677–678 (2017: Theorem 14.2): the size control
`N(Λ') ≤ f` by an sc-smooth cut-off functor `σ`.

# The size control of Theorem 14.1.9

## The text, paraphrased

After §§14.3–14.5 the text has a structurable sc⁺-multisection functor `Λ''` on `X` with
`Λ''|(W|∂X) = Λ` and `dom-supp(Λ'') ⊆ Ũ`.  Since `N(Λ)(x) < f(x)` on `dom-supp(Λ)` and the
pointwise norm is continuous, there is a saturated open neighbourhood `G` of `∂X` on which
`N(Λ'') < f` (where `Λ''` is nontrivial); an sc-smooth functor `σ : X → [0, 1]` with `σ = 1` on
`∂X` and `σ = 0` off `G` gives `Λ' = σ ⊙ Λ''` (Lemma 13.3.14), with `N(Λ') ≤ f`,
`dom-supp(Λ') ⊆ Ũ` and `Λ'|∂X = Λ`.

## What is formalized

* `theorem_14_1_9_extension_statement A`: the output of §§14.3–14.5 (Proposition 14.5.4, the
  commensurable sum and Theorem 14.5.5, applied to the local extensions of Proposition 14.4.14)
  as a Lean `Prop`: for every structurable `Λ` over `∂X` and saturated open `Ũ ⊇ dom-supp(Λ)`
  there is a structurable `Λ''` on `X` with `dom-supp(Λ'') ⊆ Ũ` and `Λ''|∂X = Λ`.
* **`theorem_14_1_9_hyp`**: `theorem_14_1_9_extension_statement A → theorem_14_1_9_statement A`
  (B1's statement of Theorem 14.1.9), i.e. the size control is proved.
* `theorem_14_1_9_extension_statement_of_boundary_eq_empty`: the hypothesis holds when
  `∂X = ∅` (with `Λ'' = 0`), a satisfiability witness.
* Tools: `isOpen_pointwiseNorm_lt` (`{N(Λ) < f}` is open, from the local representations and
  the continuity of `N`), `pointwiseNorm_tgt` (`N(Λ)` is a functor), `pointwiseNorm_smulFun_le`
  (`N(β ⊙ Λ) ≤ |β| N(Λ)`), `isSaturated_closure_gl`, `domSupp_zeroMultisection_gl`.

## Reading

* The text (p. 677) uses `h(|x|) = N(Λ)(x) < f(x)` for `x ∈ ∂X`; the hypothesis of Theorem
  14.1.9 gives it on `dom-supp(Λ)`.  We read it there.  At points of `∂X` outside
  `dom-supp(Λ)` with `f = 0` the argument needs `Λ''` to be trivial near them; we obtain this by
  asking the extension to have `dom-supp(Λ'') ⊆ {f > 0}` (a saturated open set containing
  `dom-supp(Λ)` and contained in `Ũ`), which the extension statement allows.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-! ### Saturation -/

/-- `∂X` is saturated (isomorphic objects have the same degeneracy index). -/
theorem isSaturated_boundary_gl : A.X.IsSaturated A.X.PObj.boundary := by
  refine Subset.antisymm (fun y hy => ?_) (subset_preimage_image _ _)
  obtain ⟨b, hb, hby⟩ := hy
  obtain ⟨φ, hs, ht⟩ := A.X.π_eq_π_iff.1 hby
  show 1 ≤ A.X.PObj.degIndex y
  rw [← ht, ← A.X.degIndex_tgt, A.X.degIndex_src, hs]
  exact hb

/-- The closure of a saturated set is saturated (saturations of open sets are open,
Proposition 7.1.8). -/
theorem isSaturated_closure_gl {S : Set A.Obj} (hS : A.X.IsSaturated S) :
    A.X.IsSaturated (closure S) := by
  refine A.X.isSaturated_iff.2 fun φ hφ => ?_
  by_contra hn
  rw [mem_closure_iff] at hn
  push Not at hn
  obtain ⟨V, hVo, hyV, hVS⟩ := hn
  have hx : A.X.src φ ∈ A.X.saturation V :=
    ⟨A.X.tgt φ, hyV, (A.X.π_eq_π_iff.2 ⟨φ, rfl, rfl⟩).symm⟩
  obtain ⟨z, hzV, hzS⟩ := mem_closure_iff.1 hφ _ (A.X.isOpen_saturation hVo) hx
  obtain ⟨v, hv, hvz⟩ := hzV
  have hvS : v ∈ S := by
    rw [← hS]
    exact ⟨z, hzS, hvz.symm⟩
  have : v ∈ V ∩ S := ⟨hv, hvS⟩
  rw [hVS] at this
  exact this

theorem isSaturated_union_gl {S T : Set A.Obj} (hS : A.X.IsSaturated S)
    (hT : A.X.IsSaturated T) : A.X.IsSaturated (S ∪ T) :=
  A.X.isSaturated_iff.2 fun φ h => h.elim (fun h => Or.inl (A.X.isSaturated_iff.1 hS φ h))
    fun h => Or.inr (A.X.isSaturated_iff.1 hT φ h)

/-! ### The pointwise norm -/

/-- `N(Λ)(s(φ)) ≤ N(Λ)(t(φ))` for a functor `Λ` and an auxiliary norm of `(P, μ)`. -/
theorem pointwiseNorm_src_le_tgt {N : A.B.One → ℝ} (hN : A.E.IsAuxNorm N) {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) (φ : A.Mor) :
    pointwiseNorm N Λ (A.X.src φ) ≤ pointwiseNorm N Λ (A.X.tgt φ) := by
  obtain ⟨w, ⟨hw, hpos⟩, hwN⟩ := (hΛ.isGreatest_pointwiseNorm N (A.X.src φ)).1
  rw [← hwN]
  have hw1 := hΛ.suppAt_subset_oneSet _ ⟨hw, hpos⟩
  rw [← normW_μ hN hw hw1]
  refine (hΛ.isGreatest_pointwiseNorm N (A.X.tgt φ)).2 (mem_image_of_mem _ ⟨A.E.P_μ _, ?_⟩)
  rw [hΛ.1 ⟨(φ, w), hw⟩]
  exact hpos

/-- **`N(Λ)` is a functor** (Definition 13.2.3 with Definition 8.3.5 (3)). -/
theorem pointwiseNorm_tgt {N : A.B.One → ℝ} (hN : A.E.IsAuxNorm N) {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) (φ : A.Mor) :
    pointwiseNorm N Λ (A.X.tgt φ) = pointwiseNorm N Λ (A.X.src φ) := by
  refine le_antisymm ?_ (pointwiseNorm_src_le_tgt hN hΛ φ)
  have := pointwiseNorm_src_le_tgt hN hΛ (A.X.inv φ)
  rwa [A.X.src_inv, A.X.tgt_inv] at this

theorem pointwiseNorm_nonneg {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N) (Λ : A.W → ℚ≥0)
    (x : A.Obj) : 0 ≤ pointwiseNorm N Λ x :=
  Real.sSup_nonneg fun _ ⟨w, _, hw⟩ => hw ▸ normW_nonneg hN w

/-- On the domain of an sc⁺-section, `y ↦ N(s(y))` is continuous. -/
theorem IsScPlusSectionOn.continuousOn_normW {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N)
    {s : A.Obj → A.W} {O : Set A.Obj} (hs : IsScPlusSectionOn A s O) :
    ContinuousOn (fun y => normW N (s y)) O := by
  obtain ⟨-, G, hGs, hG⟩ := hs
  refine (hN.continuous.comp_continuousOn hG.continuousOn).congr fun y hy => ?_
  have hm : s y ∈ A.B.oneSet := by rw [← hGs y hy]; exact A.B.oneVal_mem _
  change normW N (s y) = N (G y)
  rw [normW_of_mem N hm]
  congr 1
  exact A.B.oneVal_injective (by rw [A.B.oneVal_oneMk, hGs y hy])

/-- **`{x | N(Λ)(x) < f(x)}` is open** for an sc⁺-multisection `Λ` and continuous `f`: on the
domain `O` of a local representation `(sᵢ, σᵢ)`, `N(Λ)(y) = maxᵢ N(sᵢ(y))`. -/
theorem isOpen_pointwiseNorm_lt {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N) {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) {f : A.Obj → ℝ} (hf : Continuous f) :
    IsOpen {x | pointwiseNorm N Λ x < f x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨O, k, s, σ, hO, hxO, h⟩ := hΛ.exists_isLocalRepOn x
  have key : ∀ y ∈ O, pointwiseNorm N Λ y < f y ↔ ∀ i, normW N (s i y) < f y := by
    intro y hy
    constructor
    · intro hlt i
      refine lt_of_le_of_lt ((hΛ.isGreatest_pointwiseNorm N y).2 (mem_image_of_mem _ ?_)) hlt
      rw [h.suppAt_eq hy]
      exact ⟨i, rfl⟩
    · intro hall
      obtain ⟨w, hw, hwN⟩ := (hΛ.isGreatest_pointwiseNorm N y).1
      rw [h.suppAt_eq hy] at hw
      obtain ⟨i, rfl⟩ := hw
      rw [← hwN]
      exact hall i
  have hopen : ∀ i, IsOpen (O ∩ (fun y => normW N (s i y) - f y) ⁻¹' Iio 0) := fun i =>
    (((h.2.1 i).continuousOn_normW hN).sub hf.continuousOn).isOpen_inter_preimage hO isOpen_Iio
  refine Filter.mem_of_superset (Filter.inter_mem (hO.mem_nhds hxO)
    ((Filter.iInter_mem).2 fun i => (hopen i).mem_nhds ⟨hxO, ?_⟩)) ?_
  · have := (key x hxO).1 hx i
    show normW N (s i x) - f x < 0
    linarith
  · rintro y ⟨hyO, hy⟩
    rw [mem_iInter] at hy
    refine (key y hyO).2 fun i => ?_
    have := (hy i).2
    simp only [mem_preimage, mem_Iio] at this
    show normW N (s i y) < f y
    linarith

/-- **`N(w) ≤ |a| N(Λ)(P(w))`** for `w` in the support of `aΛ` (Definition 13.2.10). -/
theorem normW_le_of_multisectionSmul_pos {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) {a : ℝ} {w : A.W}
    (hw : 0 < multisectionSmul a Λ w) : normW N w ≤ |a| * pointwiseNorm N Λ (A.P w) := by
  have hP0 := pointwiseNorm_nonneg hN Λ (A.P w)
  unfold multisectionSmul smulAt at hw
  split_ifs at hw with h0 hu
  · have e : w = fiberZero A.P (A.P w) := congrArg Subtype.val hu
    have h0' : normW N w = 0 := by rw [e, normW_fiberZero hN]
    rw [h0']
    exact mul_nonneg (abs_nonneg _) hP0
  · exact absurd hw (lt_irrefl 0)
  · set u : A.P ⁻¹' {A.P w} := a⁻¹ • toFib w with hu
    have hus : (u : A.W) ∈ suppAt Λ (A.P w) := ⟨u.2, hw⟩
    have hu1 := hΛ.suppAt_subset_oneSet _ hus
    let vv : A.B.oneFiber (A.P w) := ⟨u, hu1⟩
    have hwv : w = (((a • vv : A.B.oneFiber (A.P w)) : A.P ⁻¹' {A.P w}) : A.W) := by
      have e : ((a • vv : A.B.oneFiber (A.P w)) : A.P ⁻¹' {A.P w}) = a • u := rfl
      rw [e, hu, smul_inv_smul₀ h0]
      rfl
    have hmem : w ∈ A.B.oneSet := by rw [hwv]; exact (a • vv).2
    rw [normW_of_mem N hmem]
    have e : A.B.oneMk w hmem = A.B.toOne (a • vv) :=
      A.B.oneVal_injective (by rw [A.B.oneVal_oneMk, A.B.oneVal_toOne, ← hwv])
    rw [e, (hN.fiber (A.P w)).smul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg a)
    have e' : N (A.B.toOne vv) = normW N u := by
      rw [normW_of_mem N hu1]
      congr 1
    rw [e']
    exact (hΛ.isGreatest_pointwiseNorm N _).2 (mem_image_of_mem _ hus)

/-- **`N(β ⊙ Λ)(x) ≤ |β(x)| N(Λ)(x)`** (Lemma 13.2.11 with Definition 13.2.3). -/
theorem pointwiseNorm_smulFun_le {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N) {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) {β : A.Obj → ℝ}
    (hΛ' : IsScPlusMultisection A (multisectionSmulFun β Λ)) (x : A.Obj) :
    pointwiseNorm N (multisectionSmulFun β Λ) x ≤ |β x| * pointwiseNorm N Λ x := by
  refine csSup_le ((hΛ'.suppAt_nonempty x).image _) ?_
  rintro _ ⟨w, ⟨hw, hpos⟩, rfl⟩
  have := normW_le_of_multisectionSmul_pos hN hΛ (a := β (A.P w)) hpos
  rwa [hw] at this

/-- `β ⊙ Λ = Λ` over the points where `β = 1`. -/
theorem multisectionSmulFun_of_eq_one {β : A.Obj → ℝ} {Λ : A.W → ℚ≥0} {w : A.W}
    (h : β (A.P w) = 1) : multisectionSmulFun β Λ w = Λ w := by
  unfold multisectionSmulFun multisectionSmul smulAt
  rw [h, if_neg one_ne_zero, inv_one, one_smul]
  rfl

theorem domSupp_zeroMultisection_gl : domSupp (zeroMultisection A) = ∅ := by
  classical
  rw [domSupp, closure_empty_iff, eq_empty_iff_forall_notMem]
  rintro x ⟨w, rfl, hw, hpos⟩
  rw [zeroMultisection, if_neg hw] at hpos
  exact lt_irrefl _ hpos

/-! ### Theorem 14.1.9 -/

/-- **The output of §§14.3–14.5** (2021 pp. 646–680; 2017: §14.3–§14.5), as a statement: for
tame `X` with paracompact orbit space admitting sc-smooth partitions of unity, every
structurable `Λ : W|∂X → ℚ⁺` (Definition 14.1.7) and every saturated open `Ũ ⊇ dom-supp(Λ)`,
there is a structurable sc⁺-multisection functor `Λ''` on `X` (Definition 13.3.6) with
`dom-supp(Λ'') ⊆ Ũ` and `Λ''|(W|∂X) = Λ`.  In the text this is the commensurable sum
`Σ_a Λ̃_a` of Proposition 14.5.4 (the transported local extensions of Proposition 14.4.14),
structurable by Theorem 14.5.5; not proved here. -/
def theorem_14_1_9_extension_statement (A : SEP.{u}) : Prop :=
  A.X.IsTame → A.X.HasParacompactOrbitSpace → A.X.PObj.AdmitsScPartitionsOfUnity →
  ∀ Λ : A.W → ℚ≥0, IsBoundaryStructurable A Λ →
  ∀ Ũ : Set A.Obj, IsOpen Ũ → A.X.IsSaturated Ũ → boundaryDomSupp Λ ⊆ Ũ →
  ∃ Λ'' : A.W → ℚ≥0, IsStructurable A Λ'' ∧ domSupp Λ'' ⊆ Ũ ∧
    ∀ w, A.P w ∈ A.X.PObj.boundary → Λ'' w = Λ w

/-- **The hypothesis of `theorem_14_1_9_hyp` is satisfiable**: it holds when `∂X = ∅`
(take `Λ'' = 0`, structurable by `isStructurable_zeroMultisection`). -/
theorem theorem_14_1_9_extension_statement_of_boundary_eq_empty
    (hb : A.X.PObj.boundary = ∅) : theorem_14_1_9_extension_statement A := by
  intro _ hpara _ Λ _ Ũ _ _ _
  refine ⟨zeroMultisection A, isStructurable_zeroMultisection hpara, ?_, fun w hw => ?_⟩
  · rw [domSupp_zeroMultisection_gl]; exact empty_subset _
  · rw [hb] at hw; exact absurd hw (notMem_empty _)

/-- **2021 Theorem 14.1.9 (∂-Extension Theorem), p. 646 (2017: Theorem 14.2)**, from the
extension of §§14.3–14.5 (`theorem_14_1_9_extension_statement`): the size control.
Take the extension `Λ''` with `dom-supp(Λ'') ⊆ {f > 0}`; `G = {N(Λ'') < f} ∪ (X ∖ dom-supp(Λ''))`
is a saturated open neighbourhood of `∂X`; the invariant sc-smooth Urysohn function `σ` of
Theorem 7.5.7 with `σ = 1` on `∂X` and `σ = 0` off `G` gives `Λ' = σ ⊙ Λ''`
(Lemma 13.3.14). -/
theorem theorem_14_1_9_hyp (hext : theorem_14_1_9_extension_statement A) :
    theorem_14_1_9_statement A := by
  intro hX hpara hpu Λ hΛ N hN Ũ hUo hUsat hsub f hf hf0 hfinv htsupp hlt
  have hN1 : A.B.IsAuxNorm N := hN.isAuxNorm
  -- the extension with `dom-supp(Λ'') ⊆ {f > 0}`
  set U' : Set A.Obj := {x | 0 < f x} with hU'
  have hU'o : IsOpen U' := isOpen_lt continuous_const hf
  have hU'sat : A.X.IsSaturated U' := A.X.isSaturated_iff.2 fun φ h => by
    show 0 < f _
    rw [hfinv]
    exact h
  have hsub' : boundaryDomSupp Λ ⊆ U' := fun x hx =>
    lt_of_le_of_lt (pointwiseNorm_nonneg hN1 Λ x) (hlt x hx)
  have hU'Ũ : U' ⊆ Ũ := fun x hx => htsupp (subset_tsupport f (ne_of_gt hx))
  obtain ⟨Λ'', hΛ'', hdom, hres⟩ := hext hX hpara hpu Λ hΛ U' hU'o hU'sat hsub'
  set h : A.Obj → ℝ := pointwiseNorm N Λ'' with hh
  have hh0 : ∀ x, 0 ≤ h x := pointwiseNorm_nonneg hN1 Λ''
  set K := domSupp Λ'' with hK
  have hKeq : K = closure {x | 0 < h x} := hΛ''.1.domSupp_eq_closure_pointwiseNorm hN1
  have hhK : ∀ x, x ∉ K → h x = 0 := fun x hx =>
    le_antisymm (not_lt.1 fun hpos => hx (by rw [hKeq]; exact subset_closure hpos)) (hh0 x)
  have hhinv : ∀ φ, h (A.X.tgt φ) = h (A.X.src φ) := pointwiseNorm_tgt hN hΛ''.1
  -- `G`
  set G : Set A.Obj := {x | h x < f x} ∪ Kᶜ with hG
  have hGo : IsOpen G :=
    (isOpen_pointwiseNorm_lt hN1 hΛ''.1 hf).union
      (by rw [hK, domSupp]; exact isClosed_closure.isOpen_compl)
  have hGsat : A.X.IsSaturated G := by
    refine isSaturated_union_gl (A.X.isSaturated_iff.2 fun φ hφ => ?_) (A.X.isSaturated_compl ?_)
    · show h _ < f _
      rw [hhinv, hfinv]
      exact hφ
    · rw [hKeq]
      exact isSaturated_closure_gl (A.X.isSaturated_iff.2 fun φ hφ => by
        show 0 < h _
        rw [hhinv]
        exact hφ)
  have hbG : A.X.PObj.boundary ⊆ G := by
    intro x hx
    by_cases hxK : x ∈ K
    swap
    · exact Or.inr hxK
    left
    show h x < f x
    have hfx : 0 < f x := hdom hxK
    have hsupp : suppAt Λ'' x = suppAt Λ x := by
      ext w
      constructor
      · rintro ⟨hw, hpos⟩
        refine ⟨hw, ?_⟩
        rw [← hres w (by rw [hw]; exact hx)]
        exact hpos
      · rintro ⟨hw, hpos⟩
        refine ⟨hw, ?_⟩
        rw [hres w (by rw [hw]; exact hx)]
        exact hpos
    by_cases hxb : x ∈ boundaryDomSupp Λ
    · have := hlt x hxb
      rw [hh, pointwiseNorm, hsupp]
      exact this
    · have hle : h x ≤ 0 := by
        refine csSup_le ((hΛ''.1.suppAt_nonempty x).image _) ?_
        rintro _ ⟨w, hws, rfl⟩
        have hw0 : w = fiberZero A.P x := by
          by_contra hne
          rw [hsupp] at hws
          exact hxb (subset_closure ⟨hx, w, hws.1, hws.1 ▸ hne, hws.2⟩)
        rw [hw0, normW_fiberZero hN1]
      linarith
  -- the cut-off `σ`
  have hbcl : IsClosed (A.X.π '' A.X.PObj.boundary) :=
    A.X.isClosed_π_image_of_isSaturated isSaturated_boundary_gl A.X.PObj.isClosed_boundary
  have hGcl : IsClosed (A.X.π '' Gᶜ) :=
    A.X.isClosed_π_image_of_isSaturated (A.X.isSaturated_compl hGsat) hGo.isClosed_compl
  have hdisj : Disjoint (A.X.π '' Gᶜ) (A.X.π '' A.X.PObj.boundary) := by
    rw [disjoint_iff_forall_ne]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, hab⟩ e
    have : a ∈ A.X.PObj.boundary := by
      rw [← isSaturated_boundary_gl]
      exact ⟨b, hb, hab.trans e.symm⟩
    exact ha (hbG this)
  obtain ⟨F, hFs, hF0, hF1, hFI⟩ := A.X.exists_isScSmoothMap_orbit_urysohn hpara hpu hGcl hbcl hdisj
  set σ : A.Obj → ℝ := F ∘ A.X.π with hσ
  have hσinv : ∀ φ : A.Mor, σ (A.X.tgt φ) = σ (A.X.src φ) := fun φ => by
    simp only [hσ, comp_apply]
    rw [A.X.π_eq_π_iff.2 ⟨φ, rfl, rfl⟩]
  have hσ01 : ∀ x, σ x ∈ Icc (0 : ℝ) 1 := fun x => hFI _
  have hσG : ∀ x, x ∉ G → σ x = 0 := fun x hx => hF0 (mem_image_of_mem _ hx)
  have hσb : ∀ x ∈ A.X.PObj.boundary, σ x = 1 := fun x hx => hF1 (mem_image_of_mem _ hx)
  have hΛ' := lemma_13_3_14_fun hΛ'' hσinv hFs
  have hbound : ∀ x, pointwiseNorm N (multisectionSmulFun σ Λ'') x ≤ σ x * h x := fun x => by
    have := pointwiseNorm_smulFun_le hN1 hΛ''.1 hΛ'.1 x
    rwa [abs_of_nonneg (hσ01 x).1] at this
  refine ⟨multisectionSmulFun σ Λ'', hΛ', fun x => ?_, ?_, fun w hw => ?_⟩
  · refine (hbound x).trans ?_
    by_cases hxG : x ∈ G
    · rcases hxG with hlt' | hxK
      · have : σ x * h x ≤ h x := mul_le_of_le_one_left (hh0 x) (hσ01 x).2
        exact this.trans (le_of_lt hlt')
      · rw [hhK x hxK, mul_zero]; exact hf0 x
    · rw [hσG x hxG, zero_mul]; exact hf0 x
  · rw [hΛ'.1.domSupp_eq_closure_pointwiseNorm hN1]
    refine (closure_mono fun x hx => ?_).trans (hKeq ▸ hdom.trans hU'Ũ)
    change 0 < h x
    have := lt_of_lt_of_le hx (hbound x)
    by_contra hn
    rw [le_antisymm (not_lt.1 hn) (hh0 x), mul_zero] at this
    exact lt_irrefl _ this
  · rw [multisectionSmulFun_of_eq_one (hσb _ hw)]
    exact hres w hw

end SBLocalization

end Polyfold
