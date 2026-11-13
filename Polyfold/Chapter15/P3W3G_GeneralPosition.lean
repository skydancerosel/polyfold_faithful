import Polyfold.Chapter15.P3W3G_GoodPosition
import Polyfold.Chapter13.P3D_Structurable
import Polyfold.Chapter13.P3A_AtomicConstruction

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, pp. 693–694:
**Remark 15.3.6**, last sentence (2017: Remark 15.6), and **Theorem 15.3.7** (General Position;
2017: Theorem 15.4): the statement, and the "in particular" sentence.

# `Λ ∘ f` in general position is a branched ep⁺-subgroupoid; Theorem 15.3.7

## The text, paraphrased

(Remark 15.3.6, last sentence) In general position `Λ ∘ f : X → ℚ⁺` is a tame branched
ep⁺-subgroupoid.

(Theorem 15.3.7) Over a tame ep-groupoid admitting sc-smooth bump functions, let `f` be an
sc-Fredholm section functor with compact `|S_f|`, `N` an auxiliary norm and `U ⊇ S_f` saturated
with `(N, U)` controlling compactness.  For every continuous functor `h : X → (0, 1]` there is an
sc⁺-multisection functor `Λ` with (1) `N(Λ)(x) < h(x)`, (2) `dom-supp(Λ) ⊆ U`, (3) `T(f,Λ)`
onto on `supp(Λ ∘ f)`, (4) the kernels in general position to `∂X`.  In particular `Λ ∘ f` is a
compact tame branched ep⁺-subgroupoid, and `Λ` can be taken structurable.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `remark_15_3_6_localBranching_hyp`: at every point of `supp(Λ ∘ f)` a local branching
  structure (Definition 9.1.2 (2)–(4)) of `z ↦ Λ(f(z))`, from L's Theorem 15.2.5 and
  `remark_15_3_6_goodPosition_hyp`; **`remark_15_3_6_isBranchedEpSubgroupoid_hyp`**: with
  `|supp(Λ ∘ f)|` paracompact (Definition 9.1.2 (1), new in 2021), `Λ ∘ f` is a branched
  ep⁺-subgroupoid (Definition 9.1.2).  Unlike L's interior form, no `d_X = 0` is needed.
* Compactness of `|supp(Λ ∘ f)|`: `isClosed_supp_comp` (`supp(Λ ∘ f)` is closed in `X`),
  `isClosed_orbitSupp_comp` (its orbit space is closed in `|X|`),
  `supp_comp_subset_controlled` (with `N(Λ) ≤ 1` and `dom-supp(Λ) ⊆ U` it lies in
  `{x ∈ U | N(f(x)) ≤ 1}`), **`isCompact_orbitSupp_comp`** (so `|supp(Λ ∘ f)|` is compact when
  `(N, U)` controls compactness).
* **`theorem_15_3_7_statement`**: Theorem 15.3.7 as a Lean proposition (not proved here), with
  (3) as `IsTransversal f Λ` (Definition 15.2.1) and (4) as `IsInGeneralPosition A f Λ`
  (Definition 15.3.5; the proof's first sentence: (4) is the surjectivity of the reduced
  linearization), and `Λ` structurable (Definition 13.3.6, D's `IsStructurable`).
* **`theorem_15_3_7_in_particular_hyp`**: the "in particular" sentence: every `Λ` with the
  conclusions (1)–(4) makes `Λ ∘ f` a compact branched ep⁺-subgroupoid
  (`IsBranchedEpSubgroupoid` and `IsCompactBranched`, Definitions 9.1.2, 9.1.6 (2)).
* `theorem_15_3_7_of_isInGeneralPosition_zero`: the case where `(f, Λ₀)` is already in general
  position (`Λ₀` the trivial multisection): then `Λ₀` has all the conclusions (paracompact
  `|X|` for "structurable", D's `isStructurable_zeroMultisection`).

## Reading

* As in §15.2, `f` carries germ data in tame charts (`IsScFredholmSectionTame`), the inherited
  Part I hypothesis of Theorem 3.6.8 (the proof of the theorem goes through Theorem 15.2.5).
* "Tame" in "tame branched ep⁺-subgroupoid" (Definition 9.3.6) is not formalized in §15.2
  either; the branched structure is Definition 9.1.2 with Definition 4.2.1 submanifolds.
* `U` is taken open and saturated (D15.3.1 as formalized, `ControlsCompactness`); the text says
  "a saturated subset".
* `h` is a continuous functor: continuous on objects and constant along morphisms.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid

variable {A : SEP.{u}}

/-! ### Remark 15.3.6, last sentence -/

/-- **Remark 15.3.6, last sentence, local part**, with the inherited tame-germ hypothesis: at a
point `y ∈ supp(Λ ∘ f)` where `(f, Λ)` is in general position, `z ↦ Λ(f(z))` has a local
branching structure (Definition 9.1.2 (2)–(4)): the submanifolds `Mᵢ = {z ∈ U(y) | f(z) = sᵢ(z)}`
of the branches through `f(y)` (Theorem 15.2.5 at the point of good position), with the weights
`σᵢ`. -/
theorem remark_15_3_6_localBranching_hyp {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (hgp : IsInGeneralPosition A f Λ) {y : A.Obj} (hpos : 0 < Λ (f y)) :
    Nonempty (A.X.LocalBranchingStructure (fun z => (Λ (f z) : ℚ)) y) := by
  classical
  obtain ⟨R, O, k, s, σ, c, -, hrep, -, -, -, hS, hP, -, -, hcount, -, hI⟩ :=
    theorem_15_2_5_hyp hf hft hΛ (remark_15_3_6_goodPosition_hyp hf hft hΛ hgp hpos).1
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

/-- `Λ ∘ f` is a functor for a section functor `f` and a functor `Λ`. -/
theorem isFunctorial_comp {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) :
    A.X.IsFunctorial (fun z => (Λ (f z) : ℚ)) := by
  intro φ
  obtain ⟨_, hfun⟩ := hf.1
  change ((Λ (f (A.X.src φ)) : ℚ≥0) : ℚ) = Λ (f (A.X.tgt φ))
  rw [hfun φ, hΛ.1]
  rfl

/-- **Remark 15.3.6 (2017: Remark 15.6), p. 693, last sentence**, with the inherited tame-germ
hypothesis: if `(f, Λ)` is in general position (Definition 15.3.5) and `|supp(Λ ∘ f)|` is
paracompact (Definition 9.1.2 (1), new in 2021, not addressed by the remark), then `Λ ∘ f` is a
branched ep⁺-subgroupoid of `X` (Definition 9.1.2), with local branching structures at boundary
points as well (no `d_X = 0` is needed). -/
theorem remark_15_3_6_isBranchedEpSubgroupoid_hyp {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) (hgp : IsInGeneralPosition A f Λ)
    (hpar : ParacompactSpace (A.X.orbitSupp fun z => (Λ (f z) : ℚ))) :
    A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) where
  nonneg z := NNRat.coe_nonneg _
  isFunctorial := isFunctorial_comp hf hΛ
  support_subset z hz := mem_smoothSet_of_pos hft hΛ (by exact_mod_cast hz)
  paracompactSpace_orbitSupp := hpar
  localBranching z hz :=
    remark_15_3_6_localBranching_hyp hf hft hΛ hgp (by exact_mod_cast hz)

/-! ### Compactness of `|supp(Λ ∘ f)|` -/

/-- Near a point of a local section structure, `Λ(f(y)) > 0` iff `f(y) = sᵢ(y)` for some `i`. -/
theorem pos_iff_exists_eq {f : A.Obj → A.W} (hf : IsSection A.P f) {Λ : A.W → ℚ≥0}
    {O : Set A.Obj} {k : ℕ} {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0}
    (hrep : IsLocalRepOn A Λ O s σ) {y : A.Obj} (hy : y ∈ O) :
    0 < Λ (f y) ↔ ∃ i, f y = s i y := by
  classical
  rw [hrep.apply_of_proj hy (hf y)]
  constructor
  · intro h
    by_contra hno
    rw [Finset.sum_eq_zero fun i _ => if_neg (not_exists.1 hno i)] at h
    exact lt_irrefl _ h
  · rintro ⟨i, hi⟩
    refine lt_of_lt_of_le (hrep.1 i) ?_
    have := Finset.single_le_sum (f := fun j => if f y = s j y then σ j else 0)
      (fun j _ => zero_le) (Finset.mem_univ i)
    simpa [hi] using this

/-- **`supp(Λ ∘ f)` is closed in `X`**: near every point it is the finite union of the closed
sets `{f = sᵢ}` of a local section structure. -/
theorem isClosed_supp_comp {f : A.Obj → A.W} (hf : IsSection A.P f) (hfc : Continuous f)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) : IsClosed {y | 0 < Λ (f y)} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨O, k, s, σ, hO, hxO, hrep⟩ := hΛ.exists_isLocalRepOn x
  refine ⟨O ∩ ⋂ i, {y ∈ O | f y ≠ s i y}, fun y hy hpos => ?_,
    hO.inter (isOpen_iInter_of_finite fun i =>
      isOpen_sep_ne hfc hO (hrep.2.1 i).continuousOn), ⟨hxO, mem_iInter.2 fun i => ⟨hxO, ?_⟩⟩⟩
  · obtain ⟨i, hi⟩ := (pos_iff_exists_eq hf hrep hy.1).1 hpos
    exact (mem_iInter.1 hy.2 i).2 hi
  · intro he
    exact hx ((pos_iff_exists_eq hf hrep hxO).2 ⟨i, he⟩)

/-- **`|supp(Λ ∘ f)|` is closed in `|X|`**: `supp(Λ ∘ f)` is closed and saturated, and the orbit
map is open (Proposition 7.1.8). -/
theorem isClosed_orbitSupp_comp {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hfc : Continuous f) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) :
    IsClosed (A.X.orbitSupp fun z => (Λ (f z) : ℚ)) := by
  have hpre := A.X.preimage_π_orbitSupp (isFunctorial_comp hf hΛ)
  have hcl : IsClosed (EpGroupoid.supp fun z => (Λ (f z) : ℚ)) := by
    have : (EpGroupoid.supp fun z => (Λ (f z) : ℚ)) = {y | 0 < Λ (f y)} := by
      ext y; simp [EpGroupoid.supp]
    rw [this]; exact isClosed_supp_comp hf.1.1.1 hfc hΛ
  rw [← isOpen_compl_iff]
  have e : (A.X.orbitSupp fun z => (Λ (f z) : ℚ))ᶜ =
      A.X.π '' (EpGroupoid.supp fun z => (Λ (f z) : ℚ))ᶜ := by
    rw [← hpre, ← preimage_compl, image_preimage_eq _ A.X.surjective_π]
  rw [e]
  exact A.X.proposition_7_1_8 _ hcl.isOpen_compl

/-- **`supp(Λ ∘ f)` lies in the controlled set**: if `N(Λ) ≤ 1` and `dom-supp(Λ) ⊆ U ⊇ S_f`,
every `x` with `Λ(f(x)) > 0` lies in `U` and has `N(f(x)) ≤ 1`. -/
theorem supp_comp_subset_controlled {f : A.Obj → A.W} (hf : IsSection A.P f) {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) {N : A.B.One → ℝ} {U : Set A.Obj}
    (hSU : solutionSet A.P f ⊆ U) (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1) (hdom : domSupp Λ ⊆ U) :
    {x | 0 < Λ (f x)} ⊆ {x ∈ U | A.B.AuxLe N (f x) 1} := by
  intro x hx
  have hmem : f x ∈ suppAt Λ x := ⟨hf x, hx⟩
  refine ⟨?_, hΛ.suppAt_subset_oneSet x hmem, ?_⟩
  · by_cases h0 : f x = fiberZero A.P x
    · exact hSU h0
    · exact hdom (subset_closure ⟨f x, hf x, h0, hx⟩)
  · have hle := (hΛ.isGreatest_pointwiseNorm N x).2 ⟨f x, hmem, rfl⟩
    rw [normW_of_mem N (hΛ.suppAt_subset_oneSet x hmem)] at hle
    exact hle.trans (hN1 x)

/-- **`|supp(Λ ∘ f)|` is compact** (the "compact" of Theorem 15.3.7): if `(N, U)` controls the
compactness of `f`, `N(Λ) ≤ 1` and `dom-supp(Λ) ⊆ U`. -/
theorem isCompact_orbitSupp_comp {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hfc : Continuous f) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) {N : A.B.One → ℝ}
    {U : Set A.Obj} (hcc : ControlsCompactness A f N U) (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1)
    (hdom : domSupp Λ ⊆ U) : IsCompact (A.X.orbitSupp fun z => (Λ (f z) : ℚ)) := by
  refine hcc.2.2.2.2.of_isClosed_subset (isClosed_orbitSupp_comp hf hfc hΛ) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx' : 0 < Λ (f x) := by exact_mod_cast hx
  exact subset_closure ⟨x, supp_comp_subset_controlled hf.1.1.1 hΛ hcc.2.2.2.1 hN1 hdom hx', rfl⟩

/-! ### Theorem 15.3.7 -/

variable (A) in
/-- **Theorem 15.3.7 (General Position; 2017: Theorem 15.4), pp. 693–694**, as a proposition (the
statement, for wave 4 to prove).  `X` tame with sc-smooth bump functions, `f` an sc-Fredholm section
functor with germ data in tame charts (the inherited Part I hypothesis, as in §15.2) and compact
`|S_f|`, `(N, U)` controlling compactness, `h : X → (0, 1]` a continuous functor.  Then there is a
structurable sc⁺-multisection functor `Λ` (Definition 13.3.6) with (1) `N(Λ)(x) < h(x)`,
(2) `dom-supp(Λ) ⊆ U`, (3) `T(f,Λ)` onto on `supp(Λ ∘ f)` (`IsTransversal`, Definition 15.2.1),
(4) the kernels in general position to `∂X`, i.e. the reduced linearization onto
(`IsInGeneralPosition`, Definition 15.3.5; the proof's first sentence). -/
def theorem_15_3_7_statement : Prop :=
  A.X.IsTame → A.X.AdmitsBumpFunctionsPointwise →
    ∀ f : A.Obj → A.W, A.E.IsScFredholmSectionFunctor f → A.B.IsScFredholmSectionTame f →
      A.E.HasCompactSolutionSetEp f →
      ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
      ∀ h : A.Obj → ℝ, Continuous h → (∀ φ, h (A.X.src φ) = h (A.X.tgt φ)) →
        (∀ x, 0 < h x ∧ h x ≤ 1) →
        ∃ Λ : A.W → ℚ≥0, IsStructurable A Λ ∧ (∀ x, pointwiseNorm N Λ x < h x) ∧
          domSupp Λ ⊆ U ∧ IsTransversal f Λ ∧ IsInGeneralPosition A f Λ

/-- **Theorem 15.3.7, "In particular" (p. 694)**, with the inherited tame-germ hypothesis: if `Λ`
is an sc⁺-multisection with the conclusions (1), (2), (4) of the theorem for `h ≤ 1` (so
`N(Λ) ≤ 1`), and `(N, U)` controls compactness, then `Λ ∘ f` is a **compact** branched
ep⁺-subgroupoid (Definitions 9.1.2, 9.1.6 (2)): `|supp(Λ ∘ f)|` is compact
(`isCompact_orbitSupp_comp`), hence paracompact, and the local branching structures come from
Remark 15.3.6. -/
theorem theorem_15_3_7_in_particular_hyp {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {N : A.B.One → ℝ} {U : Set A.Obj} (hcc : ControlsCompactness A f N U) {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1)
    (hdom : domSupp Λ ⊆ U) (hgp : IsInGeneralPosition A f Λ) :
    A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ)) := by
  have hfc : Continuous f := continuousOn_univ.1 hft.isScSmooth.2.continuousOn
  have hK := isCompact_orbitSupp_comp hf hfc hΛ hcc hN1 hdom
  have : CompactSpace (A.X.orbitSupp fun z => (Λ (f z) : ℚ)) := isCompact_iff_compactSpace.1 hK
  exact ⟨remark_15_3_6_isBranchedEpSubgroupoid_hyp hf hft hΛ hgp inferInstance, hK⟩

/-- `N(Λ₀) = 0` for the trivial multisection and an auxiliary norm. -/
theorem pointwiseNorm_zeroMultisection {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N) (x : A.Obj) :
    pointwiseNorm N (zeroMultisection A) x = 0 := by
  classical
  have hs : suppAt (zeroMultisection A) x = {fiberZero A.P x} := by
    ext w
    simp only [suppAt, mem_ofPred_eq, mem_singleton_iff, zeroMultisection]
    constructor
    · rintro ⟨hw, hpos⟩
      by_contra hne
      rw [if_neg (by rw [hw]; exact hne)] at hpos
      exact lt_irrefl _ hpos
    · rintro rfl
      exact ⟨proj_fiberZero A.P x, by rw [proj_fiberZero A.P x, if_pos rfl]; exact one_pos⟩
  rw [pointwiseNorm, hs, image_singleton, csSup_singleton, normW_fiberZero hN]

/-- `dom-supp(Λ₀) = ∅` for the trivial multisection. -/
theorem domSupp_zeroMultisection : domSupp (zeroMultisection A) = ∅ := by
  classical
  rw [domSupp]
  convert closure_empty
  ext x
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists, not_and]
  intro w hw hne hpos
  unfold zeroMultisection at hpos
  rw [if_neg (by rw [hw]; exact hne)] at hpos
  exact lt_irrefl _ hpos

/-- **Theorem 15.3.7 when `f` is already in general position**: if `(f, Λ₀)` is in general
position for the trivial multisection `Λ₀` (and `|X|` is paracompact, for "structurable"), then
`Λ₀` has all the conclusions of the theorem, for every `h > 0` and every `U`. -/
theorem theorem_15_3_7_of_isInGeneralPosition_zero (hpara : A.X.HasParacompactOrbitSpace)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f) {N : A.B.One → ℝ}
    (hN : A.B.IsAuxNorm N) (U : Set A.Obj) {h : A.Obj → ℝ} (hh : ∀ x, 0 < h x)
    (hgp : IsInGeneralPosition A f (zeroMultisection A)) :
    IsStructurable A (zeroMultisection A) ∧ (∀ x, pointwiseNorm N (zeroMultisection A) x < h x) ∧
      domSupp (zeroMultisection A) ⊆ U ∧ IsTransversal f (zeroMultisection A) ∧
      IsInGeneralPosition A f (zeroMultisection A) := by
  refine ⟨isStructurable_zeroMultisection hpara, fun x => ?_, ?_, fun x hx => ⟨hx, ?_⟩, hgp⟩
  · rw [pointwiseNorm_zeroMultisection hN]; exact hh x
  · rw [domSupp_zeroMultisection]; exact empty_subset _
  · have hx1 := mem_levelSet_one_of_pos hf (isScPlusMultisection_zeroMultisection A) hx
    refine ⟨hx1, fun L hL => hgp.surjective ?_ hL⟩
    rw [A.X.PObj.levelVal_levelMk]; exact hx

/-- On the trivial ep-groupoid of `ℝⁿ` with the bundle `ℝⁿ × ℝ⁰ → ℝⁿ` every pair `(f, Λ)` is in
general position (the fibres are `0`, so every operator onto them is surjective). -/
theorem isInGeneralPosition_epSEP_zero (n : ℕ)
    (f : (StrongBundleEquivalenceExamples.epSEP n 0).Obj →
      (StrongBundleEquivalenceExamples.epSEP n 0).W)
    (Λ : (StrongBundleEquivalenceExamples.epSEP n 0).W → ℚ≥0) :
    IsInGeneralPosition (StrongBundleEquivalenceExamples.epSEP n 0) f Λ := by
  refine fun x _ L _ φ hφ hx k V T _ w => ⟨0, Subtype.ext (Prod.ext ?_ (funext fun i => i.elim0))⟩
  have h1 := ((L.domRestrict (reducedTangentFiber hφ hx T)) 0).2
  have h2 := w.2
  exact (h1.trans h2.symm)

/-- **The statement of Theorem 15.3.7 holds on the trivial example** `ℝⁿ × ℝ⁰ → ℝⁿ` (the trivial
ep-groupoid of `ℝⁿ`, which is tame, admits bump functions and has paracompact orbit space): the
trivial multisection has all the conclusions.  So `theorem_15_3_7_statement` is not vacuous
in its hypotheses' consequences, and holds in at least one instance. -/
theorem theorem_15_3_7_statement_epSEP_zero (n : ℕ) :
    theorem_15_3_7_statement (StrongBundleEquivalenceExamples.epSEP n 0) := by
  intro _ _ f hf _ _ N U hcc h _ _ hh
  exact ⟨zeroMultisection _, theorem_15_3_7_of_isInGeneralPosition_zero
    (EpGroupoid.admitsBumpFunctionsPointwise_trivial_rn n).2 hf hcc.1.isAuxNorm U
    (fun x => (hh x).1) (isInGeneralPosition_epSEP_zero n f _)⟩

end SBLocalization

end Polyfold
