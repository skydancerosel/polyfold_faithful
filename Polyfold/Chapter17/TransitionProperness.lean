import Polyfold.Chapter17.PolyfoldConstruction

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.1 (pp. 749–752): **Lemma 17.1.10**, **Proposition 17.1.11** and **Definition 17.1.12** (the
properness property of a polyfold `C`).  Numbers and pages are the 2021 text's.

# Properness of the transition M-polyfolds

## The text, paraphrased

(Lemma 17.1.10, p. 749) For `Ψ ∈ F(α)`, `Ψ' ∈ F(α')`, `q ∈ O`, `q' ∈ O'`, let
`Σ = {(q, φⁱ, pⁱ) | i ∈ I}` be the finite set of elements of `M(Ψ, Ψ')` over `q`.  Every sequence
`(q_k, φ_k, q'_k)` in `M(Ψ, Ψ')` with `q_k → q` and `q'_k → q'` has a subsequence converging to some
`(q, φⁱ, pⁱ)` with `pⁱ = q'`.  The proof: `|Ψ(q)| = |Ψ'(q')|`, sheets `U(γᵢ)` of `s` over a common
`U(q)`, every element over `q_k` is `Ψ'(g'_k, q'_k) ∘ φ_k`, and the sc-smoothness of `m` together
with Lemma 17.1.9.  (Proposition 17.1.11, p. 750) For `Ψ ∈ F(α)` every `q ∈ O` has an open
neighbourhood `U(q)` such that for every `Ψ' ∈ F(α')`, `t : s⁻¹(cl_O(U(q))) → O'` is proper.  The
proof: choose `U(q)` with `cl_{|C|}(|Ψ(U(q))|) ⊂ |Ψ(O)|`; for a sequence with `a_k ∈ cl U(q)`,
`a'_k ∈ K'`, pass to `a'_k → a'`, find `a` with `|Ψ(a)| = |Ψ'(a')|`, then `a_k → g ∗ a` along a
subsequence, and apply Lemma 17.1.10.  (Definition 17.1.12, p. 751) The properness property of `C`
names this fact.

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* `exists_mor_of_tendsto`: the limits satisfy `|Ψ(q)| = |Ψ'(q')|`.
* `eq_sheet_of_src_mem`: near `q` every element of `M(Ψ, Ψ')` over a point lies on one of `♯G'`
  pairwise disjoint sheets of `s` through the elements over `q`.
* **Lemma 17.1.10** (`lemma_17_1_10`).
* `GroupoidStr.exists_subseq_tendsto_smul`: convergence in `G\O` lifts, along a subsequence, to
  convergence to `g ∗ a` in `O`.
* **Proposition 17.1.11** (`proposition_17_1_11`) and **Definition 17.1.12**
  (`HasPropernessProperty`, `definition_17_1_12`: every polyfold structure has it).

## Readings

* Lemma 17.1.10 is proved from (a) of Definition 17.1.8 alone, by counting: over every point
  `x ∈ O` the elements of `M(Ψ, Ψ')` are either none or exactly `♯G'` (p. 749, `fiberEquiv`), so
  near `q` the `♯G'` pairwise disjoint sheets through the elements over `q` contain all elements
  over nearby points.  The text's route through `m` and Lemma 17.1.9 uses the continuity of
  `Ψ̂'`, which Definition 17.1.8 does not give (`not_lemma_17_1_9`).
* "Proper" is Mathlib's `IsProperMap` of `t` restricted to `s⁻¹(cl_O U(q))`, the form of
  Definition 7.1.3 (3) (`EpGroupoid.exists_isProperMap`); the neighbourhood `U(q)` is chosen
  before `Ψ'`, as printed.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

/-- **Convergence in `G\O` lifts along a subsequence**: if `|x_k| → |a|` in `|G ⋉ O|` for a finite
group acting by homeomorphisms on a first countable `O`, then `x_{φ(j)} → g ∗ a` for some `g` and
some subsequence (the step (17.5) of the proof of Proposition 17.1.11). -/
theorem GroupoidStr.exists_subseq_tendsto_smul {G O : Type u} [Group G] [Finite G]
    [TopologicalSpace O] [FirstCountableTopology O] [MulAction G O]
    (hc : ∀ g : G, Continuous fun y : O => g • y) {x : ℕ → O} {a : O}
    (h : Tendsto (fun k => (GroupoidStr.translation G O).π (x k)) atTop
      (𝓝 ((GroupoidStr.translation G O).π a))) :
    ∃ g : G, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 (g • a)) := by
  obtain ⟨B, hB⟩ := (𝓝 a).exists_antitone_basis
  -- eventually some translate of `x k` lies in `B n`
  have hev : ∀ n, ∀ᶠ k in atTop, ∃ g : G, g • x k ∈ B n := by
    intro n
    have hO : IsOpen ((GroupoidStr.translation G O).π '' interior (B n)) :=
      GroupoidStr.isOpenMap_π_translation hc _ isOpen_interior
    have hmem : (GroupoidStr.translation G O).π a ∈
        (GroupoidStr.translation G O).π '' interior (B n) :=
      ⟨a, mem_interior_iff_mem_nhds.2 (hB.mem n), rfl⟩
    filter_upwards [h (hO.mem_nhds hmem)] with k hk
    obtain ⟨w, hw, hwk⟩ := hk
    obtain ⟨φ, h1, h2⟩ := (GroupoidStr.π_eq_π_iff _).1 hwk.symm
    refine ⟨φ.1, ?_⟩
    change φ.2 = x k at h1
    change φ.1 • φ.2 = w at h2
    rw [← h1, h2]
    exact interior_subset hw
  -- one translate works for every `n` infinitely often
  have hg : ∃ g : G, ∀ n, ∃ᶠ k in atTop, g • x k ∈ B n := by
    by_contra hne
    simp only [not_exists, not_forall, Filter.not_frequently] at hne
    choose n hn using hne
    obtain ⟨N, hN⟩ := (Set.finite_range n).bddAbove
    have hall : ∀ᶠ k in atTop, ∀ g : G, g • x k ∉ B N := Filter.eventually_all.2 fun g =>
      (hn g).mono fun k hk hkN => hk (hB.antitone (hN ⟨g, rfl⟩) hkN)
    obtain ⟨k, ⟨g, hgk⟩, hk⟩ := ((hev N).and hall).exists
    exact hk g hgk
  obtain ⟨g, hg⟩ := hg
  obtain ⟨φ, hφ, hφB⟩ := Filter.extraction_forall_of_frequently hg
  refine ⟨g⁻¹, φ, hφ, ?_⟩
  have h1 : Tendsto (fun n => g • x (φ n)) atTop (𝓝 a) := hB.tendsto hφB
  have h2 := ((hc g⁻¹).tendsto a).comp h1
  refine h2.congr fun n => ?_
  simp only [Function.comp_apply, inv_smul_smul]

namespace GCT

namespace PolyfoldConstruction

variable {C : GCT.{u}} (S : C.PolyfoldConstruction)

/-- The limits `q, q'` of the sources and targets of a sequence in `M(Ψ, Ψ')` satisfy
`|Ψ(q)| = |Ψ'(q')|`, so `M(Ψ, Ψ')` has an element `(q, φ, q')` (proof of Lemma 17.1.10). -/
theorem exists_mor_of_tendsto {Ψ Ψ' : S.Unif} {q : Ψ.1.O} {q' : Ψ'.1.O} {x : ℕ → S.Tr Ψ Ψ'}
    (hq : Tendsto (fun k => (x k).src) atTop (𝓝 q))
    (hq' : Tendsto (fun k => (x k).tgt) atTop (𝓝 q')) :
    ∃ a₀ : S.Tr Ψ Ψ', a₀.src = q ∧ a₀.tgt = q' := by
  have h1 := (Ψ.1.continuous_π_obj.tendsto q).comp hq
  have h2 := (Ψ'.1.continuous_π_obj.tendsto q').comp hq'
  have heq : (fun q : Ψ.1.O => C.toGroupoidStr.π (Ψ.1.obj q)) ∘ (fun k => (x k).src) =
      (fun q' : Ψ'.1.O => C.toGroupoidStr.π (Ψ'.1.obj q')) ∘ (fun k => (x k).tgt) :=
    funext fun k => (GroupoidStr.π_eq_π_iff _).2 ⟨(x k).mor, (x k).src_mor, (x k).tgt_mor⟩
  rw [heq] at h1
  obtain ⟨φ, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 (tendsto_nhds_unique h1 h2)
  exact ⟨⟨q, φ, q', hs, ht⟩, rfl, rfl⟩

/-- **The sheets over a neighbourhood of `q`** (proof of Lemma 17.1.10): given `a₀` over `q`,
there are maps `σ_{g'}` (`g' ∈ G'`), sc-smooth inverses of `s` on pairwise disjoint sheets, all
continuous at `q` with `s(σ_{g'}(x)) = x`, and an open `N ∋ q` such that every element of
`M(Ψ, Ψ')` over a point of `N` is one of the `σ_{g'}(x)`. -/
theorem eq_sheet_of_src_mem {Ψ Ψ' : S.Unif} (a₀ : S.Tr Ψ Ψ') :
    ∃ (σ : Ψ'.1.G → Ψ.1.O → S.Tr Ψ Ψ') (N : Set Ψ.1.O), IsOpen N ∧ a₀.src ∈ N ∧
      (∀ g, ContinuousAt (σ g) a₀.src) ∧ (∀ g, ∀ x ∈ N, (σ g x).src = x) ∧
      ∀ b : S.Tr Ψ Ψ', b.src ∈ N → ∃ g, b = σ g b.src := by
  classical
  set e := Ψ.1.toUniformizer.fiberEquiv a₀
  set γ : Ψ'.1.G → S.Tr Ψ Ψ' := fun g => (e g).1
  have hγ : ∀ g, (γ g).src = a₀.src := fun g => (e g).2
  have hγinj : Injective γ := fun g h hgh => e.injective (Subtype.ext hgh)
  choose W V σ hmem hd using fun g => S.isLocalScDiffeo_trSrc Ψ Ψ' (γ g)
  obtain ⟨U', hU', hdisj⟩ := (Set.finite_range γ).t2_separation
  set W' := fun g => W g ∩ U' (γ g)
  have hW' : ∀ g, IsOpen (W' g) := fun g => (hd g).isOpen_source.inter (hU' (γ g)).2
  have hd' := fun g => (hd g).restrict (hW' g) inter_subset_left
  set V' := fun g => V g ∩ σ g ⁻¹' W' g
  have hV' : ∀ g, IsOpen (V' g) := fun g => (hd' g).isOpen_target
  have hqV' : ∀ g, a₀.src ∈ V' g := fun g => by
    have := (hd' g).mapsTo ⟨hmem g, (hU' (γ g)).1⟩
    rwa [hγ g] at this
  refine ⟨σ, ⋂ g, V' g, isOpen_iInter_of_finite hV', mem_iInter.2 hqV', fun g => ?_,
    fun g x hx => (hd' g).right_inv x (mem_iInter.1 hx g), ?_⟩
  · exact ((hd' g).isScSmoothOn_inv.continuousOn.continuousAt ((hV' g).mem_nhds (hqV' g)))
  · intro b hb
    set x := b.src
    have hx : ∀ g, x ∈ V' g := mem_iInter.1 hb
    -- the `σ_g(x)` are pairwise distinct elements over `x`
    have hinj : Injective fun g => σ g x := by
      intro g h hgh
      by_contra hne
      have h1 : σ g x ∈ U' (γ g) := ((hd' g).mapsTo_inv (hx g)).2
      have h2 : σ h x ∈ U' (γ h) := ((hd' h).mapsTo_inv (hx h)).2
      have hgh' : σ g x = σ h x := hgh
      rw [← hgh'] at h2
      exact Set.disjoint_left.1 (hdisj (mem_range_self g) (mem_range_self h) (hγinj.ne hne)) h1
        h2
    have hsub : range (fun g => σ g x) ⊆ {a : Ψ.1.Trans Ψ'.1 | a.src = x} := by
      rintro _ ⟨g, rfl⟩
      exact (hd' g).right_inv x (hx g)
    have hfin := Ψ.1.toUniformizer.finite_fiber (Ψ' := Ψ'.1.toUniformizer) x
    have hle := Ψ.1.toUniformizer.ncard_fiber_le (Ψ' := Ψ'.1.toUniformizer) x
    have hcard : (range fun g => σ g x).ncard = Nat.card Ψ'.1.G := by
      rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj]
    have heq := Set.eq_of_subset_of_ncard_le hsub (hle.trans hcard.ge) hfin
    obtain ⟨g, hg⟩ := (Set.ext_iff.1 heq b).2 rfl
    exact ⟨g, hg.symm⟩

/-- **2021 Lemma 17.1.10, p. 749**: a sequence `(q_k, φ_k, q'_k)` in `M(Ψ, Ψ')` with `q_k → q` and
`q'_k → q'` has a subsequence converging in `M(Ψ, Ψ')` to an element `(q, φⁱ, pⁱ)` of `M(Ψ, Ψ')`
over `q` with `pⁱ = q'`. -/
theorem lemma_17_1_10 {Ψ Ψ' : S.Unif} {q : Ψ.1.O} {q' : Ψ'.1.O} {x : ℕ → S.Tr Ψ Ψ'}
    (hq : Tendsto (fun k => (x k).src) atTop (𝓝 q))
    (hq' : Tendsto (fun k => (x k).tgt) atTop (𝓝 q')) :
    ∃ a : S.Tr Ψ Ψ', a.src = q ∧ a.tgt = q' ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) := by
  obtain ⟨a₀, ha₀, -⟩ := S.exists_mor_of_tendsto hq hq'
  subst ha₀
  obtain ⟨σ, N, hN, hqN, hσc, hσs, hσ⟩ := S.eq_sheet_of_src_mem a₀
  have hev : ∀ᶠ k in atTop, ∃ g, x k = σ g (x k).src :=
    (hq.eventually_mem (hN.mem_nhds hqN)).mono fun k hk => hσ (x k) hk
  have hg : ∃ g, ∃ᶠ k in atTop, x k = σ g (x k).src := by
    by_contra hne
    simp only [not_exists, Filter.not_frequently] at hne
    obtain ⟨k, ⟨g, hgk⟩, hk⟩ := (hev.and (Filter.eventually_all.2 hne)).exists
    exact hk g hgk
  obtain ⟨g, hg⟩ := hg
  obtain ⟨φ, hφ, hφg⟩ := Filter.extraction_of_frequently_atTop hg
  have hlim : Tendsto (x ∘ φ) atTop (𝓝 (σ g a₀.src)) := by
    have := (hσc g).tendsto.comp (hq.comp hφ.tendsto_atTop)
    refine this.congr fun j => ?_
    exact (hφg j).symm
  refine ⟨σ g a₀.src, hσs g _ hqN, ?_, φ, hφ, hlim⟩
  exact tendsto_nhds_unique (((S.continuous_trTgt Ψ Ψ').tendsto _).comp hlim)
    (hq'.comp hφ.tendsto_atTop)

/-- **2021 Definition 17.1.12, p. 751**: the **properness property** of `C` with the polyfold
structure `(F, M)`: for every uniformizer `Ψ` of `F`, every `q ∈ O` has an open neighbourhood
`U(q)` such that for every uniformizer `Ψ'` of `F` the map `t : s⁻¹(cl_O(U(q))) → O'` of
`M(Ψ, Ψ')` is proper. -/
def HasPropernessProperty : Prop :=
  ∀ (Ψ : S.Unif) (q : Ψ.1.O), ∃ U : Set Ψ.1.O, IsOpen U ∧ q ∈ U ∧ ∀ Ψ' : S.Unif,
    IsProperMap (((fun a : S.Tr Ψ Ψ' => a.src) ⁻¹' closure U).domRestrict
      fun a : S.Tr Ψ Ψ' => a.tgt)

/-- **2021 Proposition 17.1.11, p. 750**: for every uniformizer `Ψ` of `F` and every `q ∈ O` there
is an open neighbourhood `U(q)` such that for every uniformizer `Ψ'` of `F`,
`t : s⁻¹(cl_O(U(q))) → O'` is proper. -/
theorem proposition_17_1_11 : S.HasPropernessProperty := by
  intro Ψ q
  set πΨ := fun q : Ψ.1.O => C.toGroupoidStr.π (Ψ.1.obj q)
  -- `U(q)` with `cl |Ψ(U(q))| ⊆ |Ψ(O)|`
  obtain ⟨T, hT, hTc, hTsub⟩ := exists_mem_nhds_isClosed_subset
    (Ψ.1.isOpen_footprint.mem_nhds (Ψ.1.π_obj_mem_footprint q))
  set U := πΨ ⁻¹' interior T
  have hU : IsOpen U := isOpen_interior.preimage Ψ.1.continuous_π_obj
  have hqU : q ∈ U := mem_interior_iff_mem_nhds.2 hT
  have hclU : πΨ '' closure U ⊆ T := by
    rintro _ ⟨a, ha, rfl⟩
    have : closure U ⊆ πΨ ⁻¹' T :=
      closure_minimal (fun y (hy : πΨ y ∈ interior T) => (interior_subset hy : πΨ y ∈ T))
        (hTc.preimage Ψ.1.continuous_π_obj)
    exact this ha
  refine ⟨U, hU, hqU, fun Ψ' => ?_⟩
  set A := (fun a : S.Tr Ψ Ψ' => a.src) ⁻¹' closure U
  have := Ψ'.1.P.metrizableSpace
  refine isProperMap_iff_isCompact_preimage.2 ⟨(S.continuous_trTgt Ψ Ψ').comp
    continuous_subtype_val, fun K hK => ?_⟩
  -- the preimage is compact iff its image in `M(Ψ, Ψ')` is
  refine (Topology.IsInducing.subtypeVal.isCompact_iff).2 ?_
  have himg : Subtype.val '' (A.domRestrict (fun a : S.Tr Ψ Ψ' => a.tgt) ⁻¹' K) =
      {a : S.Tr Ψ Ψ' | a.src ∈ closure U ∧ a.tgt ∈ K} := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.2, hb⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨a, h1⟩, h2, rfl⟩
  rw [himg]
  refine IsSeqCompact.isCompact fun x hx => ?_
  have := Ψ'.1.P.metrizableSpace
  -- `a'_k → a' ∈ K`
  obtain ⟨a', ha'K, φ₁, hφ₁, ha'⟩ := hK.isSeqCompact fun k => (hx k).2
  -- `|Ψ'(a'_k)| → |Ψ'(a')| ∈ cl |Ψ(U)| ⊆ |Ψ(O)|`
  have hlim1 : Tendsto (fun k => πΨ (x (φ₁ k)).src) atTop
      (𝓝 (C.toGroupoidStr.π (Ψ'.1.obj a'))) := by
    have := (Ψ'.1.continuous_π_obj.tendsto a').comp ha'
    refine this.congr fun k => ?_
    exact ((GroupoidStr.π_eq_π_iff _).2 ⟨(x (φ₁ k)).mor, (x (φ₁ k)).src_mor,
      (x (φ₁ k)).tgt_mor⟩).symm
  have hmemT : C.toGroupoidStr.π (Ψ'.1.obj a') ∈ T :=
    hTc.mem_of_tendsto hlim1 (Eventually.of_forall fun k => hclU ⟨_, (hx (φ₁ k)).1, rfl⟩)
  obtain ⟨a, ha⟩ := Ψ.1.mem_footprint_iff.1 (hTsub hmemT)
  -- `|a_k| → |a|` in `G\O`, hence `a_k → g ∗ a` along a subsequence
  have hlim2 : Tendsto (fun k => (GroupoidStr.translation Ψ.1.G Ψ.1.O).π (x (φ₁ k)).src) atTop
      (𝓝 ((GroupoidStr.translation Ψ.1.G Ψ.1.O).π a)) := by
    refine Ψ.1.isOpenEmbedding_orbitMap.isInducing.tendsto_nhds_iff.2 ?_
    change Tendsto (fun k => πΨ (x (φ₁ k)).src) atTop (𝓝 (C.toGroupoidStr.π (Ψ.1.obj a)))
    rw [ha]
    exact hlim1
  have := Ψ.1.P.metrizableSpace
  obtain ⟨g, φ₂, hφ₂, hg⟩ := GroupoidStr.exists_subseq_tendsto_smul
    (EpGroupoid.Examples.action_continuous_smul Ψ.1.smooth_smul) hlim2
  -- Lemma 17.1.10
  obtain ⟨b, hbs, hbt, φ₃, hφ₃, hb⟩ := S.lemma_17_1_10 (x := x ∘ φ₁ ∘ φ₂) hg
    (ha'.comp hφ₂.tendsto_atTop)
  refine ⟨b, ⟨?_, ?_⟩, φ₁ ∘ φ₂ ∘ φ₃, hφ₁.comp (hφ₂.comp hφ₃), hb⟩
  · rw [hbs]
    exact isClosed_closure.mem_of_tendsto hg (Eventually.of_forall fun k => (hx _).1)
  · rw [hbt]
    exact ha'K

/-- **2021 Definition 17.1.12, p. 751**: every polyfold `C` has the properness property
(the fact named by the definition is Proposition 17.1.11). -/
theorem definition_17_1_12 : S.HasPropernessProperty := S.proposition_17_1_11

end PolyfoldConstruction

end GCT

end Polyfold
