import Polyfold.Chapter15.P3L_Transversality

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 15,
§15.2 (pp. 689–690): Definition 15.2.4 and Theorem 15.2.5 (boundary local perturbation).

# Good position at a boundary point and the local solution sets

## The text, paraphrased

(Definition 15.2.4) For `x ∈ ∂X` with `Λ(f(x)) > 0`, `(f, Λ)` is in good position at `x` if
(1) `X` is tame near `x`, (2) `(f, Λ)` is transversal at `x`, (3) the kernels of the surjective
operators `Lᵢ` of `T(f,Λ)(x) = ∑ σᵢ Lᵢ` are in good position to the partial quadrant `C_xX`
(Definition 3.1.24): "a version of Definition 3.6.6".

(Theorem 15.2.5) Then there are a neighbourhood `U(x)` with the natural `G_x`-action, tame
submanifolds `Mᵢ` and weights `σᵢ > 0` with (1) `Mᵢ` properly embedded, (2) `T(f,Λ)(y)` onto
with kernels in good position at the points of `M_{U(x)} = ⋃ Mᵢ`, (3)
`Λ(f(y)) = ∑_{i : y ∈ Mᵢ} σᵢ`.  The proof follows that of Theorem 15.2.2 with Theorem 3.6.8.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `IsBranchGoodPosition f s hO x hxO`: Part I's Definition 3.6.6 in a tame chart
  (`IsGoodPositionGermTame`) for the section `(f − s)|O` of the restriction `W|O` at `x`.
* **`IsGoodPositionAt f Λ x`** (Definition 15.2.4): `Λ(f(x)) > 0`, `T(f,Λ)(x)` onto, and a local
  sc⁺-section structure `(sᵢ, σᵢ)` of `Λ` on an open `O ∋ x` with every branch through `f(x)` in
  good position at `x` in the sense of `IsBranchGoodPosition`.
* **`theorem_15_2_5_hyp`** (Theorem 15.2.5), with `Mᵢ = {y ∈ U(x) | f(y) = sᵢ(y)}` and the
  conclusions (1)–(3), (2) as `IsGoodPositionAt f Λ y` for the same local structure.

## Reading

* Definition 15.2.4 (1)+(3) for the branch `i` is read as Part I's good position of `f − sᵢ`
  near `x` (the text: "a version of Definition 3.6.6"): germ data in a tame chart of `W|O`
  (this gives (1), tameness near `x`) whose linearization at `x` is onto with kernel in good
  position to the partial quadrant (Definition 3.1.24).  Good position is asked for one local
  section structure; the text does not say whether it depends on the structure chosen.
* The added hypothesis (suffix `_hyp`) is as in `theorem_15_2_2_hyp`: `f` has germ data in tame
  charts (`IsScFredholmSectionTame`), the reading under which Theorem 3.6.8 holds.
* The `Mᵢ` are smooth finite-dimensional submanifolds in the sense of Definition 4.2.1
  (`IsSmoothSubmanifold`, which allows boundary and corners); that they are tame and that
  `Λ ∘ f` is a tame branched ep⁺-subgroupoid (Definition 9.3.6) is not formalized.
* The point need not lie on the boundary: the statement holds at every point where `(f, Λ)` is
  in good position.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15

variable {A : SEP.{u}}

/-! ### Definition 15.2.4 -/

/-- **Part I's good position (Definition 3.6.6) of the branch `f − s` at `x`**, for an
sc⁺-section `s` on the open set `O ∋ x`: the section `(f − s)|O` of `W|O` is in good position at
`x` in a tame chart (`IsGoodPositionGermTame`). -/
def IsBranchGoodPosition (f s : A.Obj → A.W) {O : Set A.Obj} (hO : IsOpen O) (x : A.Obj)
    (hxO : x ∈ O) : Prop :=
  haveI : Nonempty O := ⟨⟨x, hxO⟩⟩
  haveI := A.X.PObj.paracompactSpace_subtype O
  haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : O → A.Obj))
    (A.X.PObj.restrictOpen hO) A.B
  ∃ hf : IsSection A.P f,
    (A.B.restrictOpen hO).IsGoodPositionGermTame (subRestrict (O := O) f s hf) ⟨x, hxO⟩

/-- **Definition 15.2.4 (2017: Definition 15.5), p. 689**: `(f, Λ)` is in good position at `x`
if `Λ(f(x)) > 0`, (2) `T(f,Λ)(x)` is onto, and (1), (3) there is a local sc⁺-section structure
`(sᵢ, σᵢ)` of `Λ` on an open `O ∋ x` such that every branch `f − sᵢ` with `f(x) = sᵢ(x)` is in
good position at `x` (Part I's Definition 3.6.6 in a tame chart of `W|O`: tameness near `x`, and
the linearization onto with kernel in good position to the partial quadrant). -/
def IsGoodPositionAt (f : A.Obj → A.W) (Λ : A.W → ℚ≥0) (x : A.Obj) : Prop :=
  0 < Λ (f x) ∧ IsOntoAt f Λ x ∧
    ∃ (O : Set A.Obj) (hO : IsOpen O) (hxO : x ∈ O) (k : ℕ) (s : Fin k → A.Obj → A.W)
      (σ : Fin k → ℚ≥0), IsLocalRepOn A Λ O s σ ∧
        ∀ i, s i x = f x → IsBranchGoodPosition f (s i) hO x hxO

/-! ### One branch -/

/-- **One branch of the proof of Theorem 15.2.5**: as `exists_branch_interior`, at a point where
the branch is in good position, with good position at the solution points. -/
theorem exists_branch_goodPosition {f : A.Obj → A.W} (hft : A.B.IsScFredholmSectionTame f)
    {s : A.Obj → A.W} {O : Set A.Obj} (hO : IsOpen O) (hs : IsScPlusSectionOn A s O)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) (hsub : c.φ.source ⊆ O) {x : A.Obj}
    (hx : x ∈ c.φ.source) (hgp : s x = f x → IsBranchGoodPosition f s hO x (hsub hx)) :
    ∃ V : Set A.Obj, IsOpen V ∧ x ∈ V ∧ V ⊆ c.φ.source ∧
      A.X.PObj.IsSmoothSubmanifold {y ∈ V | f y = s y} ∧
      (∀ y ∈ V, f y = s y → y ∈ A.X.PObj.smoothSet ∧
        (∀ hyO : y ∈ O, IsBranchGoodPosition f s hO y hyO) ∧
        ∀ z : c.φ.model.E 1, c.φ.model.E.toBase 1 z = c.φ y → ChartOnto c (subDeriv c f s z) z) ∧
      ∀ y ∈ V, f y = s y → s x = f x := by
  by_cases h : s x = f x
  · have : Nonempty O := ⟨⟨x, hsub hx⟩⟩
    have := A.X.PObj.paracompactSpace_subtype O
    have := paracompactSpace_pullbackSpace (f := (Subtype.val : O → A.Obj))
      (A.X.PObj.restrictOpen hO) A.B
    obtain ⟨_, hg⟩ := hgp h
    obtain ⟨V, hVo, hxV, hVc, hS, hall⟩ :=
      exists_solutionSet_of_isGoodPosition hft hO hs hc hsub hx h.symm hg
    refine ⟨V, hVo, hxV, hVc, hS, fun y hy hfy => ?_, fun _ _ _ => h⟩
    obtain ⟨h1, h2, h3⟩ := hall y hy hfy
    exact ⟨h1, fun hyO => ⟨hft.isScSmooth.1, h2 hyO⟩, h3⟩
  · have hfc : Continuous f := continuousOn_univ.1 hft.isScSmooth.2.continuousOn
    refine ⟨{y ∈ c.φ.source | f y ≠ s y},
      isOpen_sep_ne hfc c.φ.isOpen_source (hs.continuousOn.mono hsub), ⟨hx, fun e => h e.symm⟩,
      sep_subset _ _, fun a ha => absurd ha.2 ha.1.2, fun y hy hfs => absurd hfs hy.2,
      fun y hy hfs => absurd hfs hy.2⟩

/-! ### Theorem 15.2.5 -/

open Classical in
/-- **Theorem 15.2.5 (2017: Theorem 15.6), p. 690 (boundary local perturbation)**, with the
added hypothesis that `f` has germ data in tame charts (`hft`, as in `theorem_15_2_2_hyp`).  If
`(f, Λ)` is in good position at `x` (Definition 15.2.4), there are a natural representation
`U(x)` of `G_x`, a local sc⁺-section structure `(sᵢ, σᵢ)` of `Λ` on `O ⊇ U(x)` and a strong bundle
chart `c` with `U(x) ⊆ dom(c) ⊆ O` such that, with `Mᵢ = {y ∈ U(x) | f(y) = sᵢ(y)}`: every `Mᵢ` is
a smooth finite-dimensional submanifold (Definition 4.2.1), (1) properly embedded in `U(x)`;
`{y ∈ U(x) | Λ(f(y)) > 0} = ⋃ᵢ Mᵢ`; (2) `(f, Λ)` is in good position at every point of it (so
`T(f,Λ)(y)` is onto, with the branches in good position); (3) `Λ(f(y)) = ∑_{i : y ∈ Mᵢ} σᵢ` on
`U(x)`; and `T(f,Λ)(y) = ∑_{i : f(y) = sᵢ(y)} σᵢ (f − sᵢ)'(y)` (read in `c`). -/
theorem theorem_15_2_5_hyp {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    {x : A.Obj} (hgp : IsGoodPositionAt f Λ x) :
    ∃ (R : A.X.NaturalRep x) (O : Set A.Obj) (k : ℕ) (s : Fin k → A.Obj → A.W)
      (σ : Fin k → ℚ≥0) (c : StrongBundleChart A.X.PObj A.P),
      IsOpen O ∧ IsLocalRepOn A Λ O s σ ∧ A.B.IsChart c ∧ R.U ⊆ c.φ.source ∧ c.φ.source ⊆ O ∧
      (∀ i, A.X.PObj.IsSmoothSubmanifold {y ∈ R.U | f y = s i y}) ∧
      (∀ i, IsProperMap (inclusion (sep_subset R.U fun y => f y = s i y))) ∧
      {y ∈ R.U | 0 < Λ (f y)} = ⋃ i, {y ∈ R.U | f y = s i y} ∧
      (∀ y ∈ R.U, 0 < Λ (f y) → IsGoodPositionAt f Λ y) ∧
      (∀ y ∈ R.U, Λ (f y) = ∑ i with f y = s i y, σ i) ∧
      (∀ (y : A.X.PObj.Level 1) (hy : A.X.PObj.levelVal 1 y ∈ c.φ.source),
        linearization f Λ y = linSumIntr c hy f s σ) ∧
      ∀ i, ∀ y ∈ R.U, f y = s i y → s i x = f x := by
  obtain ⟨-, -, O, hO, hxO, k, s, σ, hrep, hbr⟩ := hgp
  obtain ⟨R₀, -⟩ := hΛ.2 x
  obtain ⟨c₀, hc₀, hxc₀⟩ := StrongBundle.exists_chart_mem A.B x
  have hso : IsOpen (c₀.φ.source ∩ O) := c₀.φ.isOpen_source.inter hO
  obtain ⟨c, hc, hcsrc⟩ : ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsChart c ∧
      c.φ.source = c₀.φ.source ∩ O :=
    ⟨_, (StrongBundle.isChart_of_mem A.B hc₀).restrict inter_subset_left hso, rfl⟩
  have hsub : c.φ.source ⊆ O := hcsrc ▸ inter_subset_right
  have hxc : x ∈ c.φ.source := hcsrc ▸ ⟨hxc₀, hxO⟩
  have hsec : IsSection A.P f := hf.1.1.1
  have hfc : Continuous f := continuousOn_univ.1 hft.isScSmooth.2.continuousOn
  have hV := fun i => exists_branch_goodPosition hft hO (hrep.2.1 i) hc hsub hxc (hbr i)
  choose V hVo hxV hVc hVS hVall hVx using hV
  have hU'o : IsOpen (c.φ.source ∩ ⋂ i, V i) :=
    c.φ.isOpen_source.inter (isOpen_iInter_of_finite hVo)
  have hxU' : x ∈ c.φ.source ∩ ⋂ i, V i := ⟨hxc, mem_iInter.2 hxV⟩
  obtain ⟨R, hRU, -, -⟩ := A.X.exists_naturalRep_shrink R₀ hU'o hxU'
  have hRc : R.U ⊆ c.φ.source := fun y hy => (hRU hy).1.1
  have hRV : ∀ i, R.U ⊆ V i := fun i y hy => mem_iInter.1 (hRU hy).1.2 i
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
  refine ⟨R, O, k, s, σ, c, hO, hrep, hc, hRc, hsub, ?_, ?_, ?_, ?_, hcount, ?_,
    fun i y hy hi => hVx i y (hRV i hy) hi⟩
  · -- the `Mᵢ` are submanifolds
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
  · -- (1)
    intro i
    rw [isProperMap_inclusion_iff]
    have hcs : ContinuousOn (s i) R.U := (hrep.2.1 i).continuousOn.mono (hRc.trans hsub)
    have h1 : Continuous fun p : R.U => f p := hfc.comp continuous_subtype_val
    have h2 : Continuous fun p : R.U => s i p :=
      hcs.comp_continuous continuous_subtype_val fun p => p.2
    convert isClosed_eq h1 h2 using 1
    ext p
    simp
  · -- `M_{U(x)} = ⋃ Mᵢ`
    ext y
    simp only [mem_iUnion]
    constructor
    · rintro ⟨hy, hp⟩
      obtain ⟨i, hi⟩ := (hposiff y hy).1 hp
      exact ⟨i, hy, hi⟩
    · rintro ⟨i, hy, hi⟩
      exact ⟨hy, (hposiff y hy).2 ⟨i, hi⟩⟩
  · -- (2)
    intro y hy hpos
    obtain ⟨i, hi⟩ := (hposiff y hy).1 hpos
    have hy1 : y ∈ A.X.PObj.levelSet 1 :=
      smoothSet_subset_levelSet 1 (hVall i y (hRV i hy) hi).1
    let dy : LocalLinData A Λ (A.X.PObj.levelMk 1 y hy1) :=
      ⟨O, hO, k, s, σ, hrep, c, hc, hsub, hRc hy⟩
    refine ⟨hpos, ⟨hy1, (isOntoAtLevel_iff hf dy).2 fun j hj => ?_⟩,
      O, hO, hsub (hRc hy), k, s, σ, hrep, fun j hj => (hVall j y (hRV j hy) hj.symm).2.1 _⟩
    exact (surjective_toIntr_subDeriv_iff hft.isScSmooth (hrep.2.1 j) hc hsub
      (x := A.X.PObj.levelMk 1 y hy1) (hRc hy) hj.symm).2
      ((hVall j y (hRV j hy) hj.symm).2.2 _ (A.X.PObj.toBase_levelLift c.isChart (hRc hy) hy1))
  · -- `T(f,Λ)` on `dom(c)`
    intro y hy
    exact linearization_eq hf ⟨O, hO, k, s, σ, hrep, c, hc, hsub, hy⟩

end SBLocalization

end Polyfold
