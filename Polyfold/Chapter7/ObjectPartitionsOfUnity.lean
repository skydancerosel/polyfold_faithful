import Polyfold.Chapter7.PartitionsOfUnity

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §7.5:
**Definition 7.5.5** (p. 342) and **Theorem 7.5.7** (p. 342), the converse direction.

# Partitions of unity of an ep-groupoid give partitions of unity of its object M-polyfold

Theorem 7.5.7 says: if `|X|` is paracompact and the object M-polyfold `X` admits sc-smooth
partitions of unity (Definition 5.5.1), then `X` admits sc-smooth partitions of unity as an
ep-groupoid (Definition 7.5.5: saturated covers, invariant partitions).  Here the converse is
proved, with no hypothesis on `|X|`: an ep-groupoid with sc-smooth partitions of unity
(Definition 7.5.5) has an object M-polyfold admitting sc-smooth partitions of unity
(Definition 5.5.1).  So for an ep-groupoid with paracompact orbit space the two notions agree
(`hasScPartitionsOfUnity_iff`); Definition 16.1.5 (2) of a polyfold admitting sc-smooth
partitions of unity is then the condition on the object M-polyfolds of its models that
Theorem 14.1.9 (p. 646) asks for.

## The argument

* **Local Urysohn functions** (`exists_local_urysohn`).  Take `x`, a natural representation of
  `G_x` on `U(x)` and an invariant open `V ∋ x` with `cl V ⊆ U(x)` and `cl V` proper
  (`exists_invariant_nhds_of_isOpen`).  Let `C ⊆ W ⊆ V`, `C` closed, `W` open.  For `y ∈ C` the
  finitely many points `g ∗ y` (`g ∈ G_x`) split into those in `W` and those outside `W`; disjoint
  open `O ⊇` the first and `O' ⊇` the second give `P = O ∩ W` and `Q = O' ∖ C`, and an open
  `B(y) ∋ y` with `g ∗ B(y) ⊆ P` or `⊆ Q` for every `g`.  Since the morphisms between points of
  `U(x)` are the `Γ(g, ·)`, `π⁻¹(π(B(y))) ∩ U(x) ⊆ P ∪ Q`.  An sc-smooth partition of unity
  `(β)` of the ep-groupoid subordinate to the saturated cover `{π⁻¹(π(B(y)))}_{y ∈ C}` together
  with `X ∖ π⁻¹(π(C))` (closed by properness) gives `Σ_y 1_P(y) β_y`: each summand is sc-smooth
  (it agrees with `β_y` on `P(y)` and vanishes off the closed `supp β_y ∩ cl P(y) ⊆ P(y)`), it is
  supported in `W` and equals `1` on `C`.
* **Global Urysohn functions** (`exists_isScSmoothMap_urysohn_of_hasScPartitionsOfUnity`): the
  object space is paracompact and Hausdorff; a locally finite refinement of the sets `V(x)` (cut
  away from one of the two closed sets), a shrinking, the local Urysohn functions and
  `τ(Σ g_x)` with `τ` the smooth transition.
* **Partitions of unity** (`admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity`): Mathlib's
  `BumpCovering.exists_isSubordinate_of_prop` and `ρ_i = f_i ∏_{j < i} (1 − f_j)`, as in
  Theorem 5.5.10 (`admitsScPartitionsOfUnity_of_approx`).

Only the subordination and the sc-smoothness of the partition of Definition 7.5.5 are used, not
its invariance (2) or the saturated neighbourhoods of (1).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- A preimage under `π` is saturated. -/
theorem isSaturated_preimage_π (S : Set X.OrbitSpace) : X.IsSaturated (X.π ⁻¹' S) := by
  change X.π ⁻¹' (X.π '' (X.π ⁻¹' S)) = X.π ⁻¹' S
  rw [image_preimage_eq _ X.surjective_π]

/-- The saturation of an open set is open (`π` is open, Proposition 7.1.8). -/
theorem isOpen_saturation_of_isOpen {B : Set Obj} (hB : IsOpen B) :
    IsOpen (X.saturation B) :=
  (X.proposition_7_1_8 B hB).preimage X.continuous_π

/-- **The splitting step**: for `y ∈ U(x)` and `C ⊆ W`, `C` closed and `W` open, there are an
open `B ∋ y` and disjoint open `P ⊆ W`, `Q ⊆ X ∖ C` with `π⁻¹(π(B)) ∩ U(x) ⊆ P ∪ Q`. -/
theorem exists_split {x : Obj} (R : X.NaturalRep x) {C W : Set Obj} (hC : IsClosed C)
    (hW : IsOpen W) (hCW : C ⊆ W) {y : Obj} (hy : y ∈ R.U) :
    ∃ B P Q : Set Obj, IsOpen B ∧ y ∈ B ∧ IsOpen P ∧ IsOpen Q ∧ Disjoint P Q ∧ P ⊆ W ∧
      Disjoint Q C ∧ X.saturation B ∩ R.U ⊆ P ∪ Q := by
  classical
  set a : X.Isotropy x → Obj := fun g => R.Φ g y with ha
  have hdisj : Disjoint (a '' {g | a g ∈ W}) (a '' {g | a g ∉ W}) := by
    rw [disjoint_iff_forall_ne]
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩ e
    exact hh (by rw [← e]; exact hg)
  obtain ⟨O, O', hO, hO', hsO, hsO', hOO'⟩ :=
    SeparatedNhds.of_isCompact_isCompact ((Set.toFinite _).image a).isCompact
      ((Set.toFinite _).image a).isCompact hdisj
  set T : X.Isotropy x → Set Obj := fun g => if a g ∈ W then O ∩ W else O' ∩ Cᶜ with hT
  have hTo : ∀ g, IsOpen (T g) := fun g => by
    simp only [hT]
    split_ifs
    · exact hO.inter hW
    · exact hO'.inter hC.isOpen_compl
  refine ⟨⋂ g, R.U ∩ R.Φ g ⁻¹' T g, O ∩ W, O' ∩ Cᶜ,
    isOpen_iInter_of_finite fun g =>
      (R.continuousOn_Φ g).isOpen_inter_preimage R.isOpen_U (hTo g),
    mem_iInter.2 fun g => ⟨hy, ?_⟩, hO.inter hW, hO'.inter hC.isOpen_compl,
    hOO'.mono inter_subset_left inter_subset_left, inter_subset_right,
    disjoint_left.2 fun z hz hzC => hz.2 hzC, ?_⟩
  · change a g ∈ T g
    simp only [hT]
    split_ifs with h
    · exact ⟨hsO ⟨g, h, rfl⟩, h⟩
    · exact ⟨hsO' ⟨g, h, rfl⟩, fun hc => h (hCW hc)⟩
  · rintro z ⟨hzs, hz⟩
    obtain ⟨b, hb, hbz⟩ := hzs
    have hbU : b ∈ R.U := (mem_iInter.1 hb 1).1
    obtain ⟨g, hg⟩ := (R.π_eq_π_iff_exists_smul (y := ⟨b, hbU⟩) (z := ⟨z, hz⟩)).1 hbz
    have hg' : R.Φ g b = z := congrArg Subtype.val hg
    have hmem := (mem_iInter.1 hb g).2
    rw [mem_preimage, hg'] at hmem
    simp only [hT] at hmem
    split_ifs at hmem
    · exact Or.inl hmem
    · exact Or.inr hmem

/-- **Local sc-smooth Urysohn functions**: in an ep-groupoid with sc-smooth partitions of unity
(Definition 7.5.5) every object `x` has an open neighbourhood `N` such that for `C ⊆ W ⊆ N`, `C`
closed and `W` open, there is an sc-smooth `g ≥ 0` with `supp g ⊆ W` and `g = 1` on `C`. -/
theorem exists_local_urysohn (hPU : X.HasScPartitionsOfUnity) (x : Obj) :
    ∃ N : Set Obj, IsOpen N ∧ x ∈ N ∧ ∀ C W : Set Obj, IsClosed C → IsOpen W → C ⊆ W → W ⊆ N →
      ∃ g : Obj → ℝ, X.PObj.IsScSmoothMap realPolyfold g ∧ (∀ z, 0 ≤ g z) ∧
        tsupport g ⊆ W ∧ ∀ z ∈ C, g z = 1 := by
  classical
  obtain ⟨R, V, hVo, hxV, -, hVcl, -, hVprop⟩ :=
    X.exists_invariant_nhds_of_isOpen x isOpen_univ (mem_univ x)
  refine ⟨V, hVo, hxV, fun C W hC hW hCW hWV => ?_⟩
  have hCU : ∀ y ∈ C, y ∈ R.U := fun y hy => hVcl (subset_closure (hWV (hCW hy)))
  choose B P Q hBo hyB hPo hQo hPQ hPW hQC hsat using
    fun (y : C) => exists_split (X := X) R hC hW hCW (hCU y y.2)
  -- the saturated cover `{π⁻¹(π(B(y)))}_{y ∈ C} ∪ {X ∖ π⁻¹(π(C))}`
  have hCprop : X.IsProperSubset C :=
    hVprop.of_subset ((hCW.trans hWV).trans subset_closure) hC
  let U' : Option C → Set Obj := fun i =>
    i.elim (X.π ⁻¹' (X.π '' C)ᶜ) fun y => X.saturation (B y)
  have hU'o : ∀ i, IsOpen (U' i) := by
    rintro (_ | y)
    · exact (X.isClosed_saturation_of_isProperSubset hCprop).isOpen_compl
    · exact isOpen_saturation_of_isOpen (hBo y)
  have hU's : ∀ i, X.IsSaturated (U' i) := by
    rintro (_ | y)
    · exact isSaturated_preimage_π _
    · exact isSaturated_preimage_π _
  have hU'c : ⋃ i, U' i = univ := by
    refine eq_univ_of_forall fun z => mem_iUnion.2 ?_
    by_cases hz : z ∈ X.saturation C
    · obtain ⟨c, hc, hcz⟩ := hz
      exact ⟨some ⟨c, hc⟩, ⟨c, hyB ⟨c, hc⟩, hcz⟩⟩
    · exact ⟨none, hz⟩
  obtain ⟨β, hβsub, hβsc, -, -⟩ := hPU (Option C) U' hU'o hU's hU'c
  have hβsome : ∀ y : C, tsupport (β (some y)) ⊆ X.saturation (B y) := fun y => hβsub (some y)
  -- `supp β_y ∩ cl P(y) ⊆ P(y)`
  have hK : ∀ y : C, tsupport (β (some y)) ∩ closure (P y) ⊆ P y := by
    rintro y z ⟨hz1, hz2⟩
    have hzU : z ∈ R.U := hVcl (closure_mono ((hPW y).trans hWV) hz2)
    rcases hsat y ⟨hβsome y hz1, hzU⟩ with h | h
    · exact h
    · exact absurd hz2 (disjoint_left.1 ((hPQ y).symm.closure_right (hQo y)) h)
  -- the summands `1_{P(y)} β_y`
  let f : Option C → Obj → ℝ := fun i => i.elim (fun _ => 0) fun y => (P y).indicator (β (some y))
  have hfsc : ∀ i, X.PObj.IsScSmoothMap realPolyfold (f i) := by
    rintro (_ | y)
    · exact isScSmoothMap_real_const 0
    · refine isScSmoothMap_real_of_eventuallyEq fun z => ?_
      by_cases hz : z ∈ P y
      · exact ⟨β (some y), hβsc (some y),
          eventually_nhds_iff.2 ⟨P y, fun w hw => indicator_of_mem hw _, hPo y, hz⟩⟩
      · refine ⟨fun _ => 0, isScSmoothMap_real_const 0, ?_⟩
        have hKc : IsClosed (tsupport (β (some y)) ∩ closure (P y)) :=
          (isClosed_tsupport _).inter isClosed_closure
        refine eventually_nhds_iff.2 ⟨_, fun w hw => ?_, hKc.isOpen_compl,
          fun h => hz (hK y h)⟩
        change (P y).indicator (β (some y)) w = 0
        by_cases hwP : w ∈ P y
        · rw [indicator_of_mem hwP]
          exact image_eq_zero_of_notMem_tsupport fun h => hw ⟨h, subset_closure hwP⟩
        · exact indicator_of_notMem hwP _
  have hfsupp : ∀ i, support (f i) ⊆ support (β i) := by
    rintro (_ | y) z hz
    · exact (hz rfl).elim
    · change (P y).indicator (β (some y)) z ≠ 0 at hz
      by_cases hzP : z ∈ P y
      · rwa [indicator_of_mem hzP] at hz
      · exact (hz (indicator_of_notMem hzP _)).elim
  have hlf : LocallyFinite fun i => support (f i) := β.locallyFinite.subset hfsupp
  have hfnn : ∀ i z, 0 ≤ f i z := by
    rintro (_ | y) z
    · exact le_rfl
    · exact indicator_nonneg (fun w _ => β.nonneg _ w) z
  have hftsupp : ∀ i, tsupport (f i) ⊆ W := by
    rintro (_ | y)
    · change tsupport (fun _ : Obj => (0 : ℝ)) ⊆ W
      rw [show (fun _ : Obj => (0 : ℝ)) = 0 from rfl, tsupport_zero]
      exact empty_subset _
    · intro z hz
      refine hPW y (hK y ⟨closure_mono (hfsupp (some y)) hz, closure_mono ?_ hz⟩)
      intro w hw
      by_contra hwP
      exact hw (indicator_of_notMem hwP _)
  -- `g = Σ_i f_i`
  refine ⟨fun z => ∑ᶠ i, f i z, isScSmoothMap_real_finsum hfsc hlf,
    fun z => finsum_nonneg fun i => hfnn i z, ?_, fun z hz => ?_⟩
  · have hsub : support (fun z => ∑ᶠ i, f i z) ⊆ ⋃ i, support (f i) := by
      intro z hz
      by_contra h
      simp only [mem_iUnion, not_exists, mem_support, not_not] at h
      exact hz (finsum_eq_zero_of_forall_eq_zero h)
    refine (closure_mono hsub).trans ?_
    rw [hlf.closure_iUnion]
    exact iUnion_subset hftsupp
  · have heq : ∀ i, f i z = β i z := by
      rintro (_ | y)
      · exact (image_eq_zero_of_notMem_tsupport fun h =>
          hβsub none h (X.subset_saturation C hz)).symm
      · change (P y).indicator (β (some y)) z = β (some y) z
        by_cases hb : β (some y) z = 0
        · rw [hb]
          exact indicator_apply_eq_zero.2 fun _ => hb
        · rcases hsat y ⟨hβsome y (subset_tsupport _ hb), hCU z hz⟩ with h | h
          · exact indicator_of_mem h _
          · exact absurd hz (disjoint_left.1 (hQC y) h)
    show ∑ᶠ i, f i z = 1
    rw [finsum_congr heq]
    exact β.sum_eq_one (mem_univ z)

/-- **Sc-smooth Urysohn functions on the object space**: in an ep-groupoid with sc-smooth
partitions of unity (Definition 7.5.5), for disjoint closed `s, t` there is an sc-smooth
`F : X → [0, 1]` with `F = 0` on `s` and `F = 1` on `t`. -/
theorem exists_isScSmoothMap_urysohn_of_hasScPartitionsOfUnity (hPU : X.HasScPartitionsOfUnity)
    {s t : Set Obj} (hs : IsClosed s) (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ F : Obj → ℝ, X.PObj.IsScSmoothMap realPolyfold F ∧ EqOn F 0 s ∧ EqOn F 1 t ∧
      ∀ x, F x ∈ Icc (0 : ℝ) 1 := by
  classical
  choose N hNo hxN hN using exists_local_urysohn hPU
  let N' : Obj → Set Obj := fun x => if x ∈ t then N x ∩ sᶜ else tᶜ
  have hN't : ∀ x ∈ t, N' x = N x ∩ sᶜ := fun x hx => if_pos hx
  have hN'nt : ∀ x ∉ t, N' x = tᶜ := fun x hx => if_neg hx
  have hN'o : ∀ x, IsOpen (N' x) := fun x => by
    by_cases hx : x ∈ t
    · rw [hN't x hx]; exact (hNo x).inter hs.isOpen_compl
    · rw [hN'nt x hx]; exact ht.isOpen_compl
  have hN'c : ⋃ x, N' x = univ := eq_univ_of_forall fun x => mem_iUnion.2 ⟨x, by
    by_cases hx : x ∈ t
    · rw [hN't x hx]; exact ⟨hxN x, fun hxs => disjoint_left.1 hst hxs hx⟩
    · rw [hN'nt x hx]; exact hx⟩
  obtain ⟨W, hWo, hWc, hWlf, hWN⟩ := precise_refinement N' hN'o hN'c
  obtain ⟨V, hVc, -, hVW⟩ := exists_subset_iUnion_closure_subset isClosed_univ hWo
    (fun x _ => hWlf.point_finite x) (by rw [hWc])
  have hg : ∀ x, ∃ g : Obj → ℝ, X.PObj.IsScSmoothMap realPolyfold g ∧ (∀ z, 0 ≤ g z) ∧
      tsupport g ⊆ W x ∧ (x ∈ t → ∀ z ∈ closure (V x), g z = 1) ∧ (x ∉ t → ∀ z, g z = 0) := by
    intro x
    by_cases hxt : x ∈ t
    · have hWx : W x ⊆ N x := fun z hz => by
        have h := hWN x hz
        rw [hN't x hxt] at h
        exact h.1
      obtain ⟨g, h1, h2, h3, h4⟩ :=
        hN x (closure (V x)) (W x) isClosed_closure (hWo x) (hVW x) hWx
      exact ⟨g, h1, h2, h3, fun _ => h4, fun h => absurd hxt h⟩
    · refine ⟨fun _ => 0, isScSmoothMap_real_const 0, fun _ => le_rfl, ?_,
        fun h => absurd h hxt, fun _ _ => rfl⟩
      rw [show (fun _ : Obj => (0 : ℝ)) = 0 from rfl, tsupport_zero]
      exact empty_subset _
  choose g hgsc hg0 hgW hg1 hgz using hg
  have hglf : LocallyFinite fun x => support (g x) :=
    hWlf.subset fun x => subset_closure.trans (hgW x)
  have hGsc : X.PObj.IsScSmoothMap realPolyfold fun z => ∑ᶠ x, g x z :=
    isScSmoothMap_real_finsum hgsc hglf
  have hGs : ∀ z ∈ s, ∑ᶠ x, g x z = 0 := by
    intro z hz
    refine finsum_eq_zero_of_forall_eq_zero fun x => ?_
    by_cases hxt : x ∈ t
    · refine image_eq_zero_of_notMem_tsupport fun h => ?_
      have h' := hWN x (hgW x h)
      rw [hN't x hxt] at h'
      exact h'.2 hz
    · exact hgz x hxt z
  have hGt : ∀ z ∈ t, 1 ≤ ∑ᶠ x, g x z := by
    intro z hz
    obtain ⟨x, hx⟩ := mem_iUnion.1 (hVc (mem_univ z))
    have hxt : x ∈ t := by
      by_contra hxt
      have h' := hWN x (hVW x (subset_closure hx))
      rw [hN'nt x hxt] at h'
      exact h' hz
    rw [← hg1 x hxt z (subset_closure hx)]
    exact single_le_finsum x (hglf.point_finite z) fun j => hg0 j z
  refine ⟨Real.smoothTransition ∘ fun z => ∑ᶠ x, g x z,
    hGsc.comp_contDiff (Real.smoothTransition.contDiff (n := ⊤)), fun z hz => ?_,
    fun z hz => ?_, fun z => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩⟩
  · simp only [Function.comp_apply, Pi.zero_apply, hGs z hz]
    exact Real.smoothTransition.zero_of_nonpos le_rfl
  · simp only [Function.comp_apply, Pi.one_apply]
    exact Real.smoothTransition.one_of_one_le (hGt z hz)

/-- **Definition 7.5.5 ⇒ Definition 5.5.1 for the object M-polyfold** (the converse of Theorem
7.5.7, p. 342): if the ep-groupoid `X` admits sc-smooth partitions of unity (every saturated
open cover has a subordinate invariant sc-smooth partition of unity), then its object
M-polyfold admits sc-smooth partitions of unity for every open cover.  No hypothesis on `|X|`
is needed. -/
theorem admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity (hPU : X.HasScPartitionsOfUnity) :
    X.PObj.AdmitsScPartitionsOfUnity := by
  classical
  intro ι V hVo hVcov
  obtain ⟨b, hbp, hb⟩ := BumpCovering.exists_isSubordinate_of_prop
    (fun g : Obj → ℝ => X.PObj.IsScSmoothMap realPolyfold g) (fun s t hs ht hst => by
      obtain ⟨F, hF, hF0, hF1, hF01⟩ :=
        exists_isScSmoothMap_urysohn_of_hasScPartitionsOfUnity hPU hs ht hst
      exact ⟨⟨F, continuousOn_univ.1 hF.continuousOn⟩, hF, hF0, hF1, hF01⟩)
    isClosed_univ V hVo (by rw [hVcov])
  refine ⟨b.toPartitionOfUnity, hb.toPartitionOfUnity, fun i => ?_⟩
  refine isScSmoothMap_real_of_eventuallyEq fun x => ?_
  obtain ⟨T, hT⟩ := b.exists_finset_toPartitionOfUnity_eventuallyEq i x
  refine ⟨_, ?_, hT⟩
  have h1 : (⇑(b i) * ⇑(∏ j ∈ T with WellOrderingRel j i, (1 - b j))) =
      fun y => b i y * ∏ j ∈ T with WellOrderingRel j i, (1 - b j y) := by
    funext y
    simp [ContinuousMap.coe_prod, Finset.prod_apply]
  rw [h1]
  exact (hbp i).real_mul (isScSmoothMap_real_finsetProd _ fun j _ =>
    (isScSmoothMap_real_const 1).real_sub (hbp j))

/-- **Definition 7.5.5 and Definition 5.5.1 agree** for an ep-groupoid with paracompact orbit
space: `X` admits sc-smooth partitions of unity as an ep-groupoid iff its object M-polyfold does
(Theorem 7.5.7, p. 342, and its converse `admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity`). -/
theorem hasScPartitionsOfUnity_iff (hpara : X.HasParacompactOrbitSpace) :
    X.HasScPartitionsOfUnity ↔ X.PObj.AdmitsScPartitionsOfUnity :=
  ⟨admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity, X.theorem_7_5_7 hpara⟩

end EpGroupoid

end Polyfold
