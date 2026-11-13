import Polyfold.Chapter15.LocalIFT

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 15,
§15.2 (pp. 688–689): Definition 15.2.1, Theorem 15.2.2 (interior local perturbation) and
Remark 15.2.3.

# Transversality and the interior local solution sets

## The text, paraphrased

(Definition 15.2.1) For a strong bundle `(P : W → X, μ)` over an ep-groupoid, an sc-Fredholm
section functor `f` and an sc⁺-multisection `Λ`: `(f, Λ)` is transversal at `x` with
`Λ(f(x)) > 0` if `T(f,Λ)(x)` is a nonzero combination of surjective operators, i.e. for a local
sc⁺-section structure `(sᵢ)` of `Λ` all the `(f − sᵢ)'(x)` with `f(x) = sᵢ(x)` are onto; it is
transversal if it is so at every point of `supp(Λ ∘ f)`.

(Theorem 15.2.2) If `d_X(x) = 0`, `Λ(f(x)) > 0` and `(f, Λ)` is transversal at `x`, there is an
open neighbourhood `U(x)` with the natural `G_x`-action on which: (1) `d_X ≡ 0`; (2) `T(f,Λ)` is
onto at the points of `M_{U(x)} = {Λ ∘ f > 0}`; (3) there are submanifolds `Mᵢ` and weights
`σᵢ > 0` with (a) `Mᵢ` smooth, (b) properly embedded, (c) `M_{U(x)} = ⋃ Mᵢ`,
(d) `Λ(f(y)) = ∑_{i : y ∈ Mᵢ} σᵢ`, (e) `T(f,Λ)(y) = ∑_{i : f(y) = sᵢ(y)} σᵢ (f − sᵢ)'(y)`.

(Remark 15.2.3) Hence `z ↦ Λ(f(z))` is a branched ep⁺-subgroupoid of `U(x)`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `IsOntoAtLevel`, `IsOntoAt`, `IsTransversalAt`, `IsTransversal` (**Definition 15.2.1**), with
  `isOntoAtLevel_iff` (the reading "all `(f − sᵢ)'(x)` with `f(x) = sᵢ(x)` are onto" in any local
  section structure) and `linearization_ne_zero` ("nonzero combination" is automatic).
* `mem_smoothSet_of_pos`: `supp(Λ ∘ f) ⊆ X_∞`.
* **`theorem_15_2_2_hyp`** (Theorem 15.2.2), with `Mᵢ = {y ∈ U(x) | f(y) = sᵢ(y)}`.
* **`remark_15_2_3_hyp`**: a local branching structure (Definition 9.1.2) of `z ↦ Λ(f(z))` at
  every interior point of the support where `(f, Λ)` is transversal, and
  `remark_15_2_3_isBranchedEpSubgroupoid_hyp`: under transversality, `d_X = 0` on the support and
  paracompactness of `|supp(Λ ∘ f)|`, `Λ ∘ f` is a branched ep⁺-subgroupoid of `X`.

The added hypothesis (suffix `_hyp`) is that `f` has germ data in tame charts
(`IsScFredholmSectionTame`, Part I rows V3.85, V3.103): the theorem rests on Theorem 3.6.8, which
with the 2021 untamed sc-Fredholm notion does not hold as we read it
(`theorem_3_6_8_untamed_not`).  Satisfiability of all the hypotheses together:
`theorem_15_2_2_hyp_witness` and `remark_15_2_3_isBranchedEpSubgroupoid_hyp_witness`
(`InteriorPerturbationWitness`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15

variable {A : SEP.{u}}

/-! ### The support of the formal sum -/

open Classical in
/-- **The operators of the formal sum**: an operator `L` occurs (with positive weight) in
`∑_{i : f(x) = sᵢ(x)} σᵢ · (f − sᵢ)'(x)` iff it is `(f − sᵢ)'(x)` for some `i` with
`f(x) = sᵢ(x)`. -/
theorem mem_support_linSumIntr_iff {f : A.Obj → A.W} (hf : IsSection A.P f) {O : Set A.Obj}
    {k : ℕ} {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0} (hσ : ∀ i, 0 < σ i)
    (hsec : ∀ i, ∀ y ∈ O, A.P (s i y) = y) {c : StrongBundleChart A.X.PObj A.P}
    (hsub : c.φ.source ⊆ O) {x : A.X.PObj.Level 1} (hx : A.X.PObj.levelVal 1 x ∈ c.φ.source)
    (L : A.X.PObj.tangentFiber x →ₗ[ℝ] A.P ⁻¹' {A.X.PObj.levelVal 1 x}) :
    L ∈ (linSumIntr c hx f s σ).support ↔ ∃ i, s i (A.X.PObj.levelVal 1 x) =
      f (A.X.PObj.levelVal 1 x) ∧
        toIntr c hx (subDeriv c f (s i) (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))) = L := by
  have ha : c.φ.model.E.toBase 1 (levelLift c.φ 1 (A.X.PObj.levelVal 1 x)) =
      c.φ (A.X.PObj.levelVal 1 x) :=
    A.X.PObj.toBase_levelLift c.isChart hx (levelVal_mem x)
  rw [Finsupp.mem_support_iff, linSumIntr, linSumModelMap_apply, ha]
  have key : ∀ i, (if c.principal (s i) (c.φ (A.X.PObj.levelVal 1 x)) =
      c.principal f (c.φ (A.X.PObj.levelVal 1 x)) ∧
      toIntr c hx (subDeriv c f (s i) (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))) = L
      then σ i else 0) = if s i (A.X.PObj.levelVal 1 x) = f (A.X.PObj.levelVal 1 x) ∧
        toIntr c hx (subDeriv c f (s i) (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))) = L
      then σ i else 0 :=
    fun i => by rw [principal_eq_iff hf (hsec i) hsub hx]
  refine (iff_of_eq (congrArg (· ≠ 0) (Finset.sum_congr rfl fun i _ => key i))).trans ?_
  rw [Ne, Finset.sum_eq_zero_iff]
  simp only [Finset.mem_univ, true_implies, not_forall]
  constructor
  · rintro ⟨i, hi⟩
    by_cases h : s i (A.X.PObj.levelVal 1 x) = f (A.X.PObj.levelVal 1 x) ∧
        toIntr c hx (subDeriv c f (s i) (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))) = L
    · exact ⟨i, h⟩
    · exact absurd (if_neg h) hi
  · rintro ⟨i, h⟩
    exact ⟨i, by rw [if_pos h]; exact (hσ i).ne'⟩

/-! ### Definition 15.2.1 -/

/-- **`T(f,Λ)(x)` is onto** (Definition 15.2.1, 2021 p. 688, closing sentence; 2017 Definition
15.2), at `x ∈ X₁`: every operator occurring in `T(f,Λ)(x)` with positive weight is onto `W_x`. -/
def IsOntoAtLevel (f : A.Obj → A.W) (Λ : A.W → ℚ≥0) (x : A.X.PObj.Level 1) : Prop :=
  ∀ L ∈ (linearization f Λ x).support, Surjective L

/-- **`T(f,Λ)(x)` is onto at `x ∈ X`** (Definition 15.2.1): `x ∈ X₁` (where `T(f,Λ)(x)` is
defined) and `IsOntoAtLevel`. -/
def IsOntoAt (f : A.Obj → A.W) (Λ : A.W → ℚ≥0) (x : A.Obj) : Prop :=
  ∃ hx : x ∈ A.X.PObj.levelSet 1, IsOntoAtLevel f Λ (A.X.PObj.levelMk 1 x hx)

/-- **Definition 15.2.1 (2) (2017: Definition 15.2 (2)), p. 688**: `(f, Λ)` is transversal at
`x` if `Λ(f(x)) > 0` and `T(f,Λ)(x)` is a combination of surjective operators (it is then nonzero,
`linearization_ne_zero`). -/
def IsTransversalAt (f : A.Obj → A.W) (Λ : A.W → ℚ≥0) (x : A.Obj) : Prop :=
  0 < Λ (f x) ∧ IsOntoAt f Λ x

/-- **Definition 15.2.1 (1) (2017: Definition 15.2 (1)), p. 688**: `(f, Λ)` is transversal if it
is transversal at every point of `supp(Λ ∘ f)`. -/
def IsTransversal (f : A.Obj → A.W) (Λ : A.W → ℚ≥0) : Prop :=
  ∀ x, 0 < Λ (f x) → IsTransversalAt f Λ x

/-- **Definition 15.2.1 (1), the text's reading**: `T(f,Λ)(x)` is onto iff, for a (any) local
sc⁺-section structure `(sᵢ, σᵢ)` of `Λ` around `x`, every `(f − sᵢ)'(x)` with `f(x) = sᵢ(x)` is
onto. -/
theorem isOntoAtLevel_iff {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    {Λ : A.W → ℚ≥0} {x : A.X.PObj.Level 1} (d : LocalLinData A Λ x) :
    IsOntoAtLevel f Λ x ↔ ∀ i, d.s i (A.X.PObj.levelVal 1 x) = f (A.X.PObj.levelVal 1 x) →
      Surjective (toIntr d.c d.mem
        (subDeriv d.c f (d.s i) (levelLift d.c.φ 1 (A.X.PObj.levelVal 1 x)))) := by
  have hiff := mem_support_linSumIntr_iff hf.1.1.1 d.rep.1 (fun i => (d.rep.2.1 i).1) d.sub
    d.mem
  rw [IsOntoAtLevel, linearization_eq hf d, LocalLinData.sum]
  constructor
  · intro h i hi
    exact h _ ((hiff _).2 ⟨i, hi, rfl⟩)
  · intro h L hL
    obtain ⟨i, hi, rfl⟩ := (hiff L).1 hL
    exact h i hi

/-- **Definition 15.2.1, "nonzero combination"**: where `Λ(f(x)) > 0`, `T(f,Λ)(x) ≠ 0`. -/
theorem linearization_ne_zero {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) {x : A.X.PObj.Level 1}
    (hpos : 0 < Λ (f (A.X.PObj.levelVal 1 x))) : linearization f Λ x ≠ 0 := by
  classical
  obtain ⟨d⟩ := nonempty_localLinData hΛ x
  set y := A.X.PObj.levelVal 1 x
  have hsec : IsSection A.P f := hf.1.1.1
  have hcount := d.rep.2.2.2 (f y) (by rw [hsec y]; exact d.sub d.mem)
  rw [hsec y] at hcount
  obtain ⟨i, hi⟩ : ∃ i, d.s i y = f y := by
    by_contra hno
    rw [Finset.sum_eq_zero fun i _ => if_neg (fun h => not_exists.1 hno i h.symm)] at hcount
    exact hpos.ne' hcount
  have hmem := (mem_support_linSumIntr_iff hsec d.rep.1 (fun i => (d.rep.2.1 i).1) d.sub d.mem
    _).2 ⟨i, hi, rfl⟩
  rw [linearization_eq hf d]
  intro h0
  rw [LocalLinData.sum] at h0
  rw [h0] at hmem
  simp at hmem

/-! ### Continuity and smoothness of the solution points -/

/-- An sc⁺-section on `O` is continuous on `O`. -/
theorem IsScPlusSectionOn.continuousOn {s : A.Obj → A.W} {O : Set A.Obj}
    (hs : IsScPlusSectionOn A s O) : ContinuousOn s O := by
  obtain ⟨-, G, hGs, hG⟩ := hs
  exact (A.B.continuous_oneVal.comp_continuousOn hG.continuousOn).congr fun y hy => (hGs y hy).symm

/-- `{y ∈ O | f(y) ≠ s(y)}` is open. -/
theorem isOpen_sep_ne {f s : A.Obj → A.W} (hf : Continuous f) {O : Set A.Obj} (hO : IsOpen O)
    (hs : ContinuousOn s O) : IsOpen {y ∈ O | f y ≠ s y} := by
  have h := (hf.continuousOn.prodMk hs).isOpen_inter_preimage hO isClosed_diagonal.isOpen_compl
  exact h

/-- A point of `O` with `f(y) = s(y)` is smooth (`f` with tame germ data, `s` sc⁺ on `O`): it is a
zero of the sc-Fredholm section `(f − s)|O` of `W|O` (Part I, Theorem 3.1.18). -/
theorem mem_smoothSet_of_eq {f : A.Obj → A.W} (hft : A.B.IsScFredholmSectionTame f)
    {s : A.Obj → A.W} {O : Set A.Obj} (hO : IsOpen O) (hs : IsScPlusSectionOn A s O) {y : A.Obj}
    (hy : y ∈ O) (hfs : f y = s y) : y ∈ A.X.PObj.smoothSet := by
  have : Nonempty O := ⟨⟨y, hy⟩⟩
  have := A.X.PObj.paracompactSpace_subtype O
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : O → A.Obj))
    (A.X.PObj.restrictOpen hO) A.B
  have hf := hft.isScSmooth.1
  have hgO := isScFredholmSectionTame_subRestrict hO hft hs
  have h0 : IsZeroAt (pullbackProj A.P (Subtype.val : O → A.Obj)) (subRestrict (O := O) f s hf)
      ⟨y, hy⟩ := by
    unfold subRestrict
    rw [isZeroAt_restrictSection_iff]
    exact (isZeroAt_subSec_iff hf hs.1 hy).2 hfs
  exact (MPolyfold.mem_smoothSet_restrictOpen_iff hO _).1
    (hgO.toIsScFredholmSection.mem_smoothSet_of_isZeroAt h0)

/-- **`supp(Λ ∘ f) ⊆ X_∞`** (`f` with tame germ data). -/
theorem mem_smoothSet_of_pos {f : A.Obj → A.W} (hft : A.B.IsScFredholmSectionTame f)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) {y : A.Obj} (hpos : 0 < Λ (f y)) :
    y ∈ A.X.PObj.smoothSet := by
  classical
  obtain ⟨R, k, s, σ, hrep⟩ := hΛ.2 y
  have hsec : IsSection A.P f := hft.isScSmooth.1
  have h := hrep.2.2.2 (f y) (by rw [hsec y]; exact R.mem_U)
  rw [hsec y] at h
  obtain ⟨i, hi⟩ : ∃ i, f y = s i y := by
    by_contra hno
    rw [Finset.sum_eq_zero fun i _ => if_neg (not_exists.1 hno i)] at h
    exact hpos.ne' h
  exact mem_smoothSet_of_eq hft R.isOpen_U (hrep.2.1 i) R.mem_U hi

/-! ### One branch -/

/-- **One branch of the proof of Theorem 15.2.2**: for an sc⁺-section `s` on `O ⊇ dom(c)` and an
interior point `x ∈ X₁` of the chart domain: an open `V ∋ x` in the chart domain with
`{y ∈ V | f(y) = s(y)}` a submanifold, `(f − s)'(y)` onto in the chart at its points, and, if
`s(x) ≠ f(x)`, no such points at all. -/
theorem exists_branch_interior {f : A.Obj → A.W} (hft : A.B.IsScFredholmSectionTame f)
    {s : A.Obj → A.W} {O : Set A.Obj} (hO : IsOpen O) (hs : IsScPlusSectionOn A s O)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) (hsub : c.φ.source ⊆ O) {x : A.Obj}
    (hx : x ∈ c.φ.source) (hx1 : x ∈ A.X.PObj.levelSet 1) (hd : A.X.PObj.degIndex x = 0)
    (hon : s x = f x → ChartOnto c (subDeriv c f s (levelLift c.φ 1 x)) (levelLift c.φ 1 x)) :
    ∃ V : Set A.Obj, IsOpen V ∧ x ∈ V ∧ V ⊆ c.φ.source ∧
      A.X.PObj.IsSmoothSubmanifold {y ∈ V | f y = s y} ∧
      (∀ y ∈ V, f y = s y → y ∈ A.X.PObj.smoothSet ∧
        ∀ z : c.φ.model.E 1, c.φ.model.E.toBase 1 z = c.φ y → ChartOnto c (subDeriv c f s z) z) ∧
      ∀ y ∈ V, f y = s y → s x = f x := by
  by_cases h : s x = f x
  · obtain ⟨V, hVo, hxV, hVc, hS, hall⟩ := exists_solutionSet_interior hft hO hs hc hsub hx h.symm
      hd (A.X.PObj.toBase_levelLift c.isChart hx hx1) (hon h)
    exact ⟨V, hVo, hxV, hVc, hS, hall, fun _ _ _ => h⟩
  · have hfc : Continuous f := continuousOn_univ.1 hft.isScSmooth.2.continuousOn
    refine ⟨{y ∈ c.φ.source | f y ≠ s y},
      isOpen_sep_ne hfc c.φ.isOpen_source (hs.continuousOn.mono hsub), ⟨hx, fun e => h e.symm⟩,
      sep_subset _ _, fun a ha => absurd ha.2 ha.1.2, fun y hy hfs => absurd hfs hy.2,
      fun y hy hfs => absurd hfs hy.2⟩

/-! ### Theorem 15.2.2 -/

open Classical in
/-- **Theorem 15.2.2 (2017: Theorem 15.2), p. 688 (interior local perturbation)**, with the
added hypothesis that `f` has germ data in tame charts (`hft`, needed for Part I's Theorem
3.6.8).  If `d_X(x) = 0` and `(f, Λ)` is transversal at `x`, there are a natural representation
`U(x)` of `G_x`, a local sc⁺-section structure `(sᵢ, σᵢ)` of `Λ` on `O ⊇ U(x)` and a strong bundle
chart `c` with `U(x) ⊆ dom(c) ⊆ O` such that, with `Mᵢ = {y ∈ U(x) | f(y) = sᵢ(y)}`:
(1) `d_X ≡ 0` on `U(x)`; (2) `T(f,Λ)` is onto at every `y ∈ U(x)` with `Λ(f(y)) > 0`;
(a) every `Mᵢ` is a smooth finite-dimensional submanifold (Definition 4.2.1); (b) properly embedded
in `U(x)`; (c) `{y ∈ U(x) | Λ(f(y)) > 0} = ⋃ᵢ Mᵢ`; (d) `Λ(f(y)) = ∑_{i : y ∈ Mᵢ} σᵢ` on `U(x)`;
(e) `T(f,Λ)(y) = ∑_{i : f(y) = sᵢ(y)} σᵢ (f − sᵢ)'(y)` (read in `c`) on `dom(c) ∩ X₁`.
Moreover only branches through `f(x)` meet `f` in `U(x)` (the text's `I`). -/
theorem theorem_15_2_2_hyp {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    {x : A.Obj} (hd : A.X.PObj.degIndex x = 0) (htr : IsTransversalAt f Λ x) :
    ∃ (R : A.X.NaturalRep x) (O : Set A.Obj) (k : ℕ) (s : Fin k → A.Obj → A.W)
      (σ : Fin k → ℚ≥0) (c : StrongBundleChart A.X.PObj A.P),
      IsOpen O ∧ IsLocalRepOn A Λ O s σ ∧ A.B.IsChart c ∧ R.U ⊆ c.φ.source ∧ c.φ.source ⊆ O ∧
      (∀ y ∈ R.U, A.X.PObj.degIndex y = 0) ∧
      (∀ y ∈ R.U, 0 < Λ (f y) → IsOntoAt f Λ y) ∧
      (∀ i, A.X.PObj.IsSmoothSubmanifold {y ∈ R.U | f y = s i y}) ∧
      (∀ i, IsProperMap (inclusion (sep_subset R.U fun y => f y = s i y))) ∧
      {y ∈ R.U | 0 < Λ (f y)} = ⋃ i, {y ∈ R.U | f y = s i y} ∧
      (∀ y ∈ R.U, Λ (f y) = ∑ i with f y = s i y, σ i) ∧
      (∀ (y : A.X.PObj.Level 1) (hy : A.X.PObj.levelVal 1 y ∈ c.φ.source),
        linearization f Λ y = linSumIntr c hy f s σ) ∧
      ∀ i, ∀ y ∈ R.U, f y = s i y → s i x = f x := by
  obtain ⟨-, hx1, hon⟩ := htr
  obtain ⟨R₀, k, s, σ, hrep⟩ := hΛ.2 x
  obtain ⟨c₀, hc₀, hxc₀⟩ := StrongBundle.exists_chart_mem A.B x
  have hso : IsOpen (c₀.φ.source ∩ R₀.U) := c₀.φ.isOpen_source.inter R₀.isOpen_U
  obtain ⟨c, hc, hcsrc⟩ : ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsChart c ∧
      c.φ.source = c₀.φ.source ∩ R₀.U :=
    ⟨_, (StrongBundle.isChart_of_mem A.B hc₀).restrict inter_subset_left hso, rfl⟩
  have hsub : c.φ.source ⊆ R₀.U := hcsrc ▸ inter_subset_right
  have hxc : x ∈ c.φ.source := hcsrc ▸ ⟨hxc₀, R₀.mem_U⟩
  have hsec : IsSection A.P f := hf.1.1.1
  have hfc : Continuous f := continuousOn_univ.1 hft.isScSmooth.2.continuousOn
  let d : LocalLinData A Λ (A.X.PObj.levelMk 1 x hx1) :=
    ⟨R₀.U, R₀.isOpen_U, k, s, σ, hrep, c, hc, hsub, hxc⟩
  have hon' := (isOntoAtLevel_iff hf d).1 hon
  have hch : ∀ i, s i x = f x →
      ChartOnto c (subDeriv c f (s i) (levelLift c.φ 1 x)) (levelLift c.φ 1 x) := fun i hi =>
    (surjective_toIntr_subDeriv_iff hft.isScSmooth (hrep.2.1 i) hc hsub
      (x := A.X.PObj.levelMk 1 x hx1) hxc hi.symm).1 (hon' i hi)
  have hV := fun i => exists_branch_interior hft R₀.isOpen_U (hrep.2.1 i) hc hsub hxc hx1 hd (hch i)
  choose V hVo hxV hVc hVS hVall hVx using hV
  have hU'o : IsOpen (c.φ.source ∩ (⋂ i, V i) ∩ {y | A.X.PObj.degIndex y = 0}) :=
    (c.φ.isOpen_source.inter (isOpen_iInter_of_finite hVo)).inter A.X.PObj.isOpen_interior
  have hxU' : x ∈ c.φ.source ∩ (⋂ i, V i) ∩ {y | A.X.PObj.degIndex y = 0} :=
    ⟨⟨hxc, mem_iInter.2 hxV⟩, hd⟩
  obtain ⟨R, hRU, -, -⟩ := A.X.exists_naturalRep_shrink R₀ hU'o hxU'
  have hRc : R.U ⊆ c.φ.source := fun y hy => (hRU hy).1.1.1
  have hRV : ∀ i, R.U ⊆ V i := fun i y hy => mem_iInter.1 (hRU hy).1.1.2 i
  have hcount : ∀ y ∈ R.U, Λ (f y) = ∑ i with f y = s i y, σ i := fun y hy => by
    have h := hrep.2.2.2 (f y) (by rw [hsec y]; exact hsub (hRc hy))
    rw [hsec y] at h
    rw [h, Finset.sum_filter]
  have hposiff : ∀ y ∈ R.U, 0 < Λ (f y) ↔ ∃ i, f y = s i y := fun y hy => by
    rw [hcount y hy]
    constructor
    · intro h
      by_contra hno
      rw [Finset.sum_eq_zero fun i hi => absurd (Finset.mem_filter.1 hi).2 (not_exists.1 hno i)]
        at h
      exact lt_irrefl _ h
    · rintro ⟨i, hi⟩
      exact lt_of_lt_of_le (hrep.1 i) (Finset.single_le_sum (fun _ _ => zero_le)
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩))
  refine ⟨R, R₀.U, k, s, σ, c, R₀.isOpen_U, hrep, hc, hRc, hsub, fun y hy => (hRU hy).1.2,
    ?_, ?_, ?_, ?_, hcount, ?_, fun i y hy hi => hVx i y (hRV i hy) hi⟩
  · -- (2)
    intro y hy hpos
    obtain ⟨i, hi⟩ := (hposiff y hy).1 hpos
    have hy1 : y ∈ A.X.PObj.levelSet 1 :=
      smoothSet_subset_levelSet 1 (hVall i y (hRV i hy) hi).1
    let dy : LocalLinData A Λ (A.X.PObj.levelMk 1 y hy1) :=
      ⟨R₀.U, R₀.isOpen_U, k, s, σ, hrep, c, hc, hsub, hRc hy⟩
    refine ⟨hy1, (isOntoAtLevel_iff hf dy).2 fun j hj => ?_⟩
    exact (surjective_toIntr_subDeriv_iff hft.isScSmooth (hrep.2.1 j) hc hsub
      (x := A.X.PObj.levelMk 1 y hy1) (hRc hy) hj.symm).2
      ((hVall j y (hRV j hy) hj.symm).2 _ (A.X.PObj.toBase_levelLift c.isChart (hRc hy) hy1))
  · -- (a)
    intro i
    have e : {y ∈ R.U | f y = s i y} = {y ∈ V i | f y = s i y} ∩ R.U := by
      ext y
      constructor
      · rintro ⟨hy, he⟩
        exact ⟨⟨hRV i hy, he⟩, hy⟩
      · rintro ⟨⟨-, he⟩, hy⟩
        exact ⟨hy, he⟩
    rw [e]
    exact (hVS i).inter_isOpen R.isOpen_U
  · -- (b)
    intro i
    rw [isProperMap_inclusion_iff]
    have hcs : ContinuousOn (s i) R.U := (hrep.2.1 i).continuousOn.mono (hRc.trans hsub)
    have h1 : Continuous fun p : R.U => f p := hfc.comp continuous_subtype_val
    have h2 : Continuous fun p : R.U => s i p :=
      hcs.comp_continuous continuous_subtype_val fun p => p.2
    convert isClosed_eq h1 h2 using 1
    ext p
    simp
  · -- (c)
    ext y
    simp only [mem_iUnion]
    constructor
    · rintro ⟨hy, hp⟩
      obtain ⟨i, hi⟩ := (hposiff y hy).1 hp
      exact ⟨i, hy, hi⟩
    · rintro ⟨i, hy, hi⟩
      exact ⟨hy, (hposiff y hy).2 ⟨i, hi⟩⟩
  · -- (e)
    intro y hy
    exact linearization_eq hf ⟨R₀.U, R₀.isOpen_U, k, s, σ, hrep, c, hc, hsub, hy⟩

/-! ### Remark 15.2.3 -/

/-- **Remark 15.2.3 (2017: Remark 15.2), p. 689, local part**, with the added tame-germ
hypothesis of `theorem_15_2_2_hyp`: at a point `y` of `supp(Λ ∘ f)` with `d_X(y) = 0` where
`(f, Λ)` is transversal, `z ↦ Λ(f(z))` has a local branching structure (Definition 9.1.2 (2)–(4)):
the submanifolds `Mᵢ = {z ∈ U(y) | f(z) = sᵢ(z)}` of the branches through `f(y)`, with the
weights `σᵢ`. -/
theorem remark_15_2_3_hyp {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    {y : A.Obj} (hd : A.X.PObj.degIndex y = 0) (htr : IsTransversalAt f Λ y) :
    Nonempty (A.X.LocalBranchingStructure (fun z => (Λ (f z) : ℚ)) y) := by
  classical
  obtain ⟨R, O, k, s, σ, c, -, hrep, -, -, -, -, -, hS, hP, -, hcount, -, hI⟩ :=
    theorem_15_2_2_hyp hf hft hΛ hd htr
  refine ⟨EpGroupoid.LocalBranchingStructure.mk R.U R.isOpen_U R.mem_U
    (ULift.{u} {i : Fin k // s i y = f y}) (fun j => {z ∈ R.U | f z = s j.down.1 z})
    (fun j => sep_subset _ _) (fun j => hS j.down.1) (fun j => ⟨R.mem_U, j.down.2.symm⟩)
    (fun j => hP j.down.1) (fun j => (σ j.down.1 : ℚ))
    (fun j => by exact_mod_cast hrep.1 j.down.1) ?_⟩
  intro z hz
  have e0 : ((Λ (f z) : ℚ≥0) : ℚ) = ∑ i, if f z = s i z then (σ i : ℚ) else 0 := by
    rw [hcount z hz, Finset.sum_filter]
    refine (map_sum NNRat.coeHom _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
    split_ifs <;> rfl
  have e1 : (∑ i, if f z = s i z then (σ i : ℚ) else 0) =
      ∑ i with s i y = f y, (if f z = s i z then (σ i : ℚ) else 0) :=
    (Finset.sum_filter_of_ne fun i _ hne => hI i z hz (by
      by_contra h
      exact hne (if_neg h))).symm
  have e2 : (∑ i with s i y = f y, (if f z = s i z then (σ i : ℚ) else 0)) =
      ∑ a : {i // s i y = f y}, (if f z = s a.1 z then (σ a.1 : ℚ) else 0) :=
    Finset.sum_subtype _ (fun i => by simp) _
  have e3 : (∑ a : {i // s i y = f y}, (if f z = s a.1 z then (σ a.1 : ℚ) else 0)) =
      ∑ j : ULift.{u} {i // s i y = f y},
        (if f z = s j.down.1 z then (σ j.down.1 : ℚ) else 0) :=
    (Fintype.sum_equiv Equiv.ulift _ _ fun _ => rfl).symm
  refine e0.trans (e1.trans (e2.trans (e3.trans ?_)))
  simp only [Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd ⟨hz, h1⟩ h2 | exact absurd h2.2 h1

/-- **Remark 15.2.3, global form**, with the added tame-germ hypothesis: if `(f, Λ)` is
transversal (Definition 15.2.1 (1)), `d_X = 0` on `supp(Λ ∘ f)` and `|supp(Λ ∘ f)|` is
paracompact (Definition 9.1.2 (1), new in 2021), then `Λ ∘ f` is a branched ep⁺-subgroupoid of
`X` (Definition 9.1.2): functoriality from `f` and `Λ` being functors, `supp ⊆ X_∞` from
`mem_smoothSet_of_pos`, the local branching from `remark_15_2_3_hyp`. -/
theorem remark_15_2_3_isBranchedEpSubgroupoid_hyp {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) (htr : IsTransversal f Λ)
    (hd : ∀ y, 0 < Λ (f y) → A.X.PObj.degIndex y = 0)
    (hpar : ParacompactSpace (A.X.orbitSupp fun z => (Λ (f z) : ℚ))) :
    A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) where
  nonneg z := NNRat.coe_nonneg _
  isFunctorial φ := by
    obtain ⟨hsm, hfun⟩ := hf.1
    change ((Λ (f (A.X.src φ)) : ℚ≥0) : ℚ) = Λ (f (A.X.tgt φ))
    rw [hfun φ, hΛ.1]
    rfl
  support_subset z hz := mem_smoothSet_of_pos hft hΛ (by exact_mod_cast hz)
  paracompactSpace_orbitSupp := hpar
  localBranching z hz := by
    have hpos : 0 < Λ (f z) := by exact_mod_cast hz
    exact remark_15_2_3_hyp hf hft hΛ (hd z hpos) (htr z hpos)

end SBLocalization

end Polyfold
