import Mathlib

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Appendix 2.7.2,
Lemma 2.7.3 (p. 72, quoting Michael [80], Lemma 1) and Proposition 2.7.4 (p. 74)
(preprint Lemma 2.56 and Proposition 2.57).

# Closed locally finite refinements (Michael)

## The text, paraphrased

(Lemma 2.7.3) A regular Hausdorff space is paracompact iff every open cover has a locally finite
refinement by closed sets.  (Proposition 2.7.4) A regular Hausdorff space covered by a locally
finite family of closed paracompact subspaces is paracompact.

## What is formalized

"Paracompact" is Mathlib's `ParacompactSpace` (every open cover has a locally finite open
refinement), "regular Hausdorff" is `T3Space`.

* `paracompactSpace_of_closed_refinement`: the converse direction of Lemma 2.7.3, for every
  topological space (no separation is used).
* `exists_closed_refinement`: the direct direction, for regular spaces.
* `lemma_2_7_3`: the equivalence for `T3Space`.
* `proposition_2_7_4`: as printed.

## Notes on the proofs

* Direct direction: the text takes the closures of a locally finite open refinement `(V_j)`; we
  first shrink the cover by regularity (`x ∈ W_x`, `cl W_x ⊆ U_{i(x)}`) and refine `(W_x)`, so
  that `cl V_j` lies in a member of the cover.
* Converse direction: the text's sets `B(x)`, `A'_j`; local finiteness of `(A'_j)` at `x` is
  proved with a neighbourhood of `x` meeting finitely many `C_k` (each `C_k ⊆ B(x_k)` meets only
  the `A_j` with `x_k ∈ A_j`).
* Proposition 2.7.4: the refinement is indexed by pairs `(i, b)` (`b` indexing a closed refinement
  in `Y_i`) instead of the text's unions `C_j = ⋃_i C^i_j`.
-/

open Set Filter Topology

universe u

namespace Polyfold

namespace GapP1Michael

variable {X : Type u} [TopologicalSpace X]

/-- **Lemma 2.7.3, converse direction** (any topological space): if every open cover has a
locally finite refinement by closed sets, the space is paracompact. -/
theorem paracompactSpace_of_closed_refinement
    (h : ∀ (α : Type u) (s : α → Set X), (∀ a, IsOpen (s a)) → ⋃ a, s a = univ →
      ∃ (β : Type u) (t : β → Set X), (∀ b, IsClosed (t b)) ∧ ⋃ b, t b = univ ∧
        LocallyFinite t ∧ ∀ b, ∃ a, t b ⊆ s a) :
    ParacompactSpace X := by
  classical
  refine ⟨fun α u huo huc => ?_⟩
  -- a closed locally finite refinement `A` of `u`, with `A b ⊆ u (i b)`
  obtain ⟨β, A, hAc, hAcov, hAlf, hAr⟩ := h α u huo huc
  choose i hi using hAr
  -- `B x`: an open neighbourhood of `x` meeting only the `A b ∋ x`, inside `u (i b)` for
  -- every `b` with `x ∈ A b`
  let B : X → Set X := fun x =>
    (⋃ b, if x ∈ A b then ∅ else A b)ᶜ ∩ ⋂ b ∈ {b | x ∈ A b}, u (i b)
  have hBo : ∀ x, IsOpen (B x) := fun x => by
    refine IsOpen.inter ?_ ((hAlf.point_finite x).isOpen_biInter fun b _ => huo _)
    refine isOpen_compl_iff.2 ?_
    refine (hAlf.subset fun b => ?_).isClosed_iUnion fun b => ?_
    · split_ifs; exacts [empty_subset _, subset_rfl]
    · split_ifs; exacts [isClosed_empty, hAc b]
  have hxB : ∀ x, x ∈ B x := fun x => by
    refine ⟨?_, mem_iInter₂.2 fun b hb => hi b hb⟩
    simp only [mem_compl_iff, mem_iUnion, not_exists]
    intro b
    split_ifs with hb
    · exact notMem_empty x
    · exact hb
  have hBA : ∀ x b, (B x ∩ A b).Nonempty → x ∈ A b := by
    rintro x b ⟨z, hzB, hzA⟩
    by_contra hb
    exact hzB.1 (mem_iUnion.2 ⟨b, by simpa [hb] using hzA⟩)
  have hBu : ∀ x b, x ∈ A b → B x ⊆ u (i b) := fun x b hb z hz =>
    mem_iInter₂.1 hz.2 b hb
  -- a closed locally finite refinement `C` of `B`
  obtain ⟨κ, C, hCc, hCcov, hClf, hCr⟩ :=
    h X B hBo (eq_univ_of_forall fun x => mem_iUnion.2 ⟨x, hxB x⟩)
  choose xk hxk using hCr
  -- the open sets `A' b`
  let A' : β → Set X := fun b => (⋃ k, if Disjoint (A b) (C k) then C k else ∅)ᶜ
  have hA'o : ∀ b, IsOpen (A' b) := fun b => by
    refine isOpen_compl_iff.2 ?_
    refine (hClf.subset fun k => ?_).isClosed_iUnion fun k => ?_
    · split_ifs; exacts [subset_rfl, empty_subset _]
    · split_ifs; exacts [hCc k, isClosed_empty]
  have hAA' : ∀ b, A b ⊆ A' b := fun b z hz => by
    simp only [A', mem_compl_iff, mem_iUnion, not_exists]
    intro k
    split_ifs with hk
    · exact fun hzk => (Set.disjoint_left.1 hk) hz hzk
    · exact notMem_empty z
  -- every point of `A' b` lies in some `C k` meeting `A b`
  have hA'C : ∀ b z, z ∈ A' b → ∃ k, z ∈ C k ∧ ¬ Disjoint (A b) (C k) := by
    intro b z hz
    obtain ⟨k, hk⟩ := mem_iUnion.1 (hCcov ▸ mem_univ z : z ∈ ⋃ k, C k)
    refine ⟨k, hk, fun hd => hz (mem_iUnion.2 ⟨k, ?_⟩)⟩
    simpa [hd] using hk
  have hmeet : ∀ b k, ¬ Disjoint (A b) (C k) → xk k ∈ A b := by
    intro b k hd
    obtain ⟨z, hzA, hzC⟩ := Set.not_disjoint_iff.1 hd
    exact hBA (xk k) b ⟨z, hxk k hzC, hzA⟩
  refine ⟨β, A', hA'o, ?_, ?_, fun b => ⟨i b, ?_⟩⟩
  · exact eq_univ_of_forall fun z => by
      obtain ⟨b, hb⟩ := mem_iUnion.1 (hAcov ▸ mem_univ z : z ∈ ⋃ b, A b)
      exact mem_iUnion.2 ⟨b, hAA' b hb⟩
  · intro x
    obtain ⟨t, ht, htf⟩ := hClf x
    refine ⟨t, ht, (htf.biUnion fun k _ => hAlf.point_finite (xk k)).subset ?_⟩
    rintro b ⟨z, hzA', hzt⟩
    obtain ⟨k, hzk, hd⟩ := hA'C b z hzA'
    exact mem_iUnion₂.2 ⟨k, ⟨z, hzk, hzt⟩, hmeet b k hd⟩
  · intro z hz
    obtain ⟨k, hzk, hd⟩ := hA'C b z hz
    exact hBu (xk k) b (hmeet b k hd) (hxk k hzk)

/-- **Lemma 2.7.3, direct direction**: in a paracompact regular space every open cover has a
locally finite refinement by closed sets. -/
theorem exists_closed_refinement [RegularSpace X] [ParacompactSpace X] (α : Type u)
    (s : α → Set X) (hso : ∀ a, IsOpen (s a)) (hsc : ⋃ a, s a = univ) :
    ∃ (β : Type u) (t : β → Set X), (∀ b, IsClosed (t b)) ∧ ⋃ b, t b = univ ∧
      LocallyFinite t ∧ ∀ b, ∃ a, t b ⊆ s a := by
  -- shrink: `x ∈ W x`, `closure (W x) ⊆ s (a x)`
  have hx : ∀ x : X, ∃ a, x ∈ s a := fun x => mem_iUnion.1 (hsc ▸ mem_univ x)
  choose a ha using hx
  have hW : ∀ x : X, ∃ t ∈ 𝓝 x, IsClosed t ∧ t ⊆ s (a x) := fun x =>
    exists_mem_nhds_isClosed_subset ((hso _).mem_nhds (ha x))
  choose t ht htc hts using hW
  obtain ⟨v, hvo, hvc, hvlf, hvW⟩ := precise_refinement (fun x => interior (t x))
    (fun _ => isOpen_interior)
    (eq_univ_of_forall fun x => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (ht x)⟩)
  refine ⟨X, fun x => closure (v x), fun _ => isClosed_closure, ?_, hvlf.closure,
    fun x => ⟨a x, ?_⟩⟩
  · exact eq_univ_of_forall fun z => by
      obtain ⟨x, hx⟩ := mem_iUnion.1 (hvc ▸ mem_univ z : z ∈ ⋃ x, v x)
      exact mem_iUnion.2 ⟨x, subset_closure hx⟩
  · exact (closure_mono ((hvW x).trans interior_subset)).trans
      ((htc x).closure_subset.trans (hts x))

/-- **Lemma 2.7.3 (2021 p. 72; preprint 2.56)**: a regular Hausdorff space is paracompact iff
every open cover has a locally finite refinement consisting of closed sets. -/
theorem lemma_2_7_3 [T3Space X] :
    ParacompactSpace X ↔
      ∀ (α : Type u) (s : α → Set X), (∀ a, IsOpen (s a)) → ⋃ a, s a = univ →
        ∃ (β : Type u) (t : β → Set X), (∀ b, IsClosed (t b)) ∧ ⋃ b, t b = univ ∧
          LocallyFinite t ∧ ∀ b, ∃ a, t b ⊆ s a :=
  ⟨fun _ => exists_closed_refinement, paracompactSpace_of_closed_refinement⟩

/-- **Proposition 2.7.4 (2021 p. 74; preprint 2.57)**: a regular Hausdorff space `Y` with a
locally finite cover `(Y_i)` by closed paracompact subspaces is paracompact. -/
theorem proposition_2_7_4 {Y : Type u} [TopologicalSpace Y] [T3Space Y] {ι : Type u}
    (Yf : ι → Set Y) (hclosed : ∀ i, IsClosed (Yf i)) (hlf : LocallyFinite Yf)
    (hcov : ⋃ i, Yf i = univ) (hpara : ∀ i, ParacompactSpace (Yf i)) : ParacompactSpace Y := by
  classical
  refine paracompactSpace_of_closed_refinement fun α s hso hsc => ?_
  -- closed locally finite refinements in each `Y_i`
  have hloc : ∀ i, ∃ (β : Type u) (t : β → Set (Yf i)), (∀ b, IsClosed (t b)) ∧
      ⋃ b, t b = univ ∧ LocallyFinite t ∧ ∀ b, ∃ a, t b ⊆ Subtype.val ⁻¹' s a := fun i =>
    exists_closed_refinement α (fun a => Subtype.val ⁻¹' s a)
      (fun a => (hso a).preimage continuous_subtype_val)
      (by rw [← preimage_iUnion, hsc, preimage_univ])
  choose β t htc htcov htlf htr using hloc
  let D : (Σ i, β i) → Set Y := fun p => Subtype.val '' t p.1 p.2
  refine ⟨Σ i, β i, D, fun p => (hclosed p.1).isClosedMap_subtype_val _ (htc p.1 p.2), ?_, ?_,
    fun p => ?_⟩
  · refine eq_univ_of_forall fun y => ?_
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov ▸ mem_univ y : y ∈ ⋃ i, Yf i)
    obtain ⟨b, hb⟩ := mem_iUnion.1 (htcov i ▸ mem_univ _ : (⟨y, hi⟩ : Yf i) ∈ ⋃ b, t i b)
    exact mem_iUnion.2 ⟨⟨i, b⟩, ⟨y, hi⟩, hb, rfl⟩
  · intro x
    obtain ⟨V, hV, hVf⟩ := hlf x
    -- for each `i`, a neighbourhood `W i` of `x` meeting finitely many `t i b`
    have hWi : ∀ i, ∃ W ∈ 𝓝 x, {b | ∃ z : Yf i, z ∈ t i b ∧ (z : Y) ∈ W}.Finite := by
      intro i
      by_cases hxi : x ∈ Yf i
      · obtain ⟨s', hs', hs'f⟩ := htlf i ⟨x, hxi⟩
        obtain ⟨W, hW, hWs⟩ := (mem_nhds_subtype _ _ _).1 hs'
        refine ⟨W, hW, hs'f.subset ?_⟩
        rintro b ⟨z, hz, hzW⟩
        exact ⟨z, hz, hWs hzW⟩
      · refine ⟨(Yf i)ᶜ, (hclosed i).isOpen_compl.mem_nhds hxi, ?_⟩
        convert finite_empty
        ext b
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists, not_and]
        intro z _ hz
        exact hz z.2
    choose W hW hWf using hWi
    refine ⟨V ∩ ⋂ i ∈ {i | (Yf i ∩ V).Nonempty}, W i,
      inter_mem hV ((biInter_mem hVf).2 fun i _ => hW i), ?_⟩
    refine (hVf.biUnion fun i _ => (hWf i).image (Sigma.mk i)).subset ?_
    rintro ⟨i, b⟩ ⟨y, ⟨z, hz, rfl⟩, hyV, hyW⟩
    have hi : (Yf i ∩ V).Nonempty := ⟨z, z.2, hyV⟩
    exact mem_iUnion₂.2 ⟨i, hi, b, ⟨z, hz, mem_iInter₂.1 hyW i hi⟩, rfl⟩
  · obtain ⟨a, ha⟩ := htr p.1 p.2
    refine ⟨a, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact ha hz

end GapP1Michael

end Polyfold
