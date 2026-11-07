import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.TFAE

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017 book), Part I, §2.6.2, p. 51:
**Lemma 2.7** [preprint 2.56] (Michael) and **Proposition 2.17** [preprint 2.57]; infrastructure
for Part II, Chapter 7: Corollary 7.2 (p. 247), Proposition 7.12 (pp. 249–250), Proposition 7.14 (2)
(p. 252), and Chapter 8, Theorem 8.4 (p. 268).

# Michael's lemma; locally finite unions of closed paracompact subspaces

## The text, paraphrased

(Lemma 2.7, quoting [55], Lemma 1 = E. Michael, *A note on paracompact spaces*, Proc. Amer. Math.
Soc. 4 (1953), 831–838) A regular Hausdorff space is paracompact if and only if every open cover has
a locally finite refinement by closed sets.  (pp. 51, 249) Paracompact means: every open cover has
a locally finite open refinement (p. 51 says "subcovering"; we read "refinement", as on p. 249);
Hausdorff is not part of it.  (Proposition 2.17) A regular Hausdorff
space `Y` which is the union of a locally finite family `(Y_i)` of closed paracompact subspaces is
paracompact.  *Proof*: closed locally finite refinements `(C^i_j)_j` of the traces `(Y_i ∩ U_j)_j`
(Lemma 2.7 in `Y_i`), `C_j := ⋃_i C^i_j`, and Lemma 2.7 in `Y`.

How Part II uses them.  Corollary 7.2: the union `⋃_{i ≤ k} cl U(zᵢ)` of finitely many closed
paracompact (metrizable) subsets of the regular `|X|` is paracompact.  Proposition 7.12: Lemma 2.7
gives a locally finite closed refinement `(A_x)` of `(|U(x)|)`, and `|X¹|` is paracompact as the
locally finite union of the closed paracompact `A_x ∩ |X¹|` (Proposition 2.17).  Proposition 7.14
(2): Lemma 2.7 in the closed `A ⊆ |X|` gives a locally finite closed cover `A_i ⊆ π(Q_{zᵢ})`.
Theorem 8.4: `|TX|` is paracompact by Proposition 2.17.

## What is formalized

Michael's Lemma 1, all four conditions, for a regular space `X` (covers indexed by types in the
universe of `X`, as in Mathlib's `ParacompactSpace`):
(a) `ParacompactSpace X`; (b) every open cover has a σ-locally finite open refinement;
(c) every open cover has a locally finite refinement by arbitrary sets; (d) every open cover has
a locally finite refinement by closed sets.

* `Polyfold.paracompactSpace_of_closed_refinement`: (d) ⇒ (a), **with no separation axiom**
  (Michael's argument: `V_b := (⋃ {B_c : B_c ∩ A_b = ∅})ᶜ ∩ U_{f(b)}` for a closed locally finite
  refinement `(A_b)` and a closed locally finite refinement `(B_c)` of a cover by open sets each
  meeting finitely many `A_b`).
* `Polyfold.closed_refinement_of_refinement`: (c) ⇒ (d) in a regular space (closures of a
  refinement of a cover by open sets with closures in the cover).
* `Polyfold.refinement_of_sigma_refinement`: (b) ⇒ (c), no separation axiom
  (`t_{n,b} ∖ ⋃_{k<n} ⋃_b' t_{k,b'}`).
* `Polyfold.paracompactSpace_of_refinement`, `Polyfold.paracompactSpace_of_sigma_refinement`:
  (c) ⇒ (a) and (b) ⇒ (a) in a regular space (the latter is the usual "Michael's theorem").
* `Polyfold.exists_closed_precise_refinement` (and `…_set` for a cover of a closed subset): in a
  regular paracompact space every open cover `(u_i)` has a closed locally finite refinement `(v_i)`
  with the same index and `v_i ⊆ u_i` ((a) ⇒ (d), via Mathlib's shrinking lemma).
* `Polyfold.lemma_2_56` (**Lemma 2.7**, the "iff") and `Polyfold.michael_tfae` (Michael's Lemma 1).
* `Polyfold.proposition_2_57` (**Proposition 2.17**) and its subspace forms
  `Polyfold.paracompactSpace_iUnion` (a locally finite family of closed paracompact subsets has a
  paracompact union), `Polyfold.paracompactSpace_iUnion_of_finite`,
  `Polyfold.paracompactSpace_biUnion_of_finite`, `Polyfold.paracompactSpace_union` (the form
  Corollary 7.2 needs), and `Polyfold.paracompactSpace_of_isClosed_subset` (a closed subset of a
  paracompact subspace).
* Tools: `Polyfold.locallyFinite_image_val` (a locally finite family in a closed subspace is
  locally finite in the space), `Polyfold.homeomorphPreimageVal` (`t ↓∩ s ≃ₜ s` for `s ⊆ t`).

## What the text leaves implicit, and the choices made

* **Hausdorff is never used.**  The text's Lemma 2.7 and Proposition 2.17 assume "regular
  Hausdorff"; here only `RegularSpace` (no `T1`), and (d) ⇒ (a) holds in every topological space.
  Regularity enters only through (c) ⇒ (d) and (a) ⇒ (d), and in Proposition 2.17 through the
  subspaces `Y_i`, which are regular because `Y` is.
* "Refinement" is Mathlib's: each set lies in some set of the cover, and the sets cover `X`.
* The plan (`PLAN.md`, II.6, 7) replaces the proof of Proposition 7.12 by
  `Polyfold.metrizableSpace_of_pullback` and Proposition 7.14 (2) by shrinking; the results here
  give the text's routes as well (`exists_closed_precise_refinement_set` is the step of 7.14 (2)).
-/

open Set Filter Topology Function
open scoped Set.Notation

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X]

/-! ### Tools -/

/-- A locally finite family of subsets of a closed subspace `s` is locally finite in `X`. -/
theorem locallyFinite_image_val {s : Set X} (hs : IsClosed s) {α : Type v} {f : α → Set s}
    (hf : LocallyFinite f) : LocallyFinite fun a => ((↑) : s → X) '' f a := by
  intro x
  by_cases hx : x ∈ s
  · obtain ⟨t, ht, htf⟩ := hf ⟨x, hx⟩
    obtain ⟨w, hw, hwt⟩ := (mem_nhds_subtype s ⟨x, hx⟩ t).1 ht
    refine ⟨w, hw, htf.subset ?_⟩
    rintro a ⟨_, ⟨y, hy, rfl⟩, hyw⟩
    exact ⟨y, hy, hwt hyw⟩
  · refine ⟨sᶜ, hs.isOpen_compl.mem_nhds hx, (finite_empty : (∅ : Set α).Finite).subset ?_⟩
    rintro a ⟨_, ⟨y, -, rfl⟩, hy⟩
    exact hy y.2

/-- For `s ⊆ t`, the subspace `t ↓∩ s` of `t` is homeomorphic to the subspace `s` of `X`. -/
def homeomorphPreimageVal {s t : Set X} (h : s ⊆ t) : (t ↓∩ s) ≃ₜ s where
  toFun z := ⟨z.1.1, z.2⟩
  invFun y := ⟨⟨y.1, h y.2⟩, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-! ### Michael's Lemma 1 -/

/-- **Michael's lemma, (d) ⇒ (a)** (Michael 1953, Lemma 1; the "if" of Lemma 2.7 [2.56]): if every
open cover of `X` has a locally finite refinement by closed sets, then `X` is paracompact.  No
separation axiom is needed. -/
theorem paracompactSpace_of_closed_refinement
    (h : ∀ (α : Type u) (s : α → Set X), (∀ a, IsOpen (s a)) → ⋃ a, s a = univ →
      ∃ (β : Type u) (t : β → Set X), (∀ b, IsClosed (t b)) ∧ ⋃ b, t b = univ ∧
        LocallyFinite t ∧ ∀ b, ∃ a, t b ⊆ s a) :
    ParacompactSpace X where
  locallyFinite_refinement α s ho hu := by
    obtain ⟨β, A, -, hAu, hAf, hAs⟩ := h α s ho hu
    choose f hf using hAs
    choose W hWn hWf using hAf
    obtain ⟨γ, B, hBc, hBu, hBf, hBW⟩ := h X (fun x => interior (W x))
      (fun _ => isOpen_interior)
      (iUnion_eq_univ_iff.2 fun x => ⟨x, mem_interior_iff_mem_nhds.2 (hWn x)⟩)
    -- every `B c` meets only finitely many `A b`
    have hBA : ∀ c, {b | (A b ∩ B c).Nonempty}.Finite := fun c => by
      obtain ⟨x, hx⟩ := hBW c
      exact (hWf x).subset fun b ⟨y, hyA, hyB⟩ => ⟨y, hyA, interior_subset (hx hyB)⟩
    -- `A' b`: the complement of the union of the `B c` disjoint from `A b`; an open set `⊇ A b`
    set A' : β → Set X := fun b => (⋃ c : {c // Disjoint (B c) (A b)}, B c)ᶜ with hA'
    have hA'o : ∀ b, IsOpen (A' b) := fun b =>
      ((hBf.comp_injective Subtype.val_injective).isClosed_iUnion fun c => hBc c.1).isOpen_compl
    have hAA' : ∀ b, A b ⊆ A' b := fun b x hx hx' => by
      obtain ⟨c, hc⟩ := mem_iUnion.1 hx'
      exact Set.disjoint_left.1 c.2 hc hx
    refine ⟨β, fun b => A' b ∩ s (f b), fun b => (hA'o b).inter (ho _), ?_, ?_,
      fun b => ⟨f b, inter_subset_right⟩⟩
    · refine eq_univ_of_subset (iUnion_mono fun b => ?_) hAu
      exact subset_inter (hAA' b) (hf b)
    · intro x
      obtain ⟨N, hN, hNf⟩ := hBf x
      refine ⟨N, hN, (hNf.biUnion fun c _ => hBA c).subset ?_⟩
      rintro b ⟨y, ⟨hyA', -⟩, hyN⟩
      obtain ⟨c, hc⟩ := iUnion_eq_univ_iff.1 hBu y
      refine mem_iUnion₂.2 ⟨c, ⟨y, hc, hyN⟩, ?_⟩
      by_contra hne
      exact hyA' (mem_iUnion.2 ⟨⟨c, Set.disjoint_left.2 fun z hzB hzA => hne ⟨z, hzA, hzB⟩⟩, hc⟩)

/-- **Michael's lemma, (c) ⇒ (d)**: in a regular space, if every open cover has a locally finite
refinement by arbitrary sets, then every open cover has a locally finite refinement by closed
sets. -/
theorem closed_refinement_of_refinement [RegularSpace X]
    (h : ∀ (α : Type u) (s : α → Set X), (∀ a, IsOpen (s a)) → ⋃ a, s a = univ →
      ∃ (β : Type u) (t : β → Set X), ⋃ b, t b = univ ∧ LocallyFinite t ∧ ∀ b, ∃ a, t b ⊆ s a)
    (α : Type u) (s : α → Set X) (ho : ∀ a, IsOpen (s a)) (hu : ⋃ a, s a = univ) :
    ∃ (β : Type u) (t : β → Set X), (∀ b, IsClosed (t b)) ∧ ⋃ b, t b = univ ∧
      LocallyFinite t ∧ ∀ b, ∃ a, t b ⊆ s a := by
  choose i hi using iUnion_eq_univ_iff.1 hu
  choose w hwn hwc hws using fun x => exists_mem_nhds_isClosed_subset ((ho (i x)).mem_nhds (hi x))
  obtain ⟨β, t, htu, htf, htw⟩ := h X (fun x => interior (w x)) (fun _ => isOpen_interior)
    (iUnion_eq_univ_iff.2 fun x => ⟨x, mem_interior_iff_mem_nhds.2 (hwn x)⟩)
  refine ⟨β, fun b => closure (t b), fun _ => isClosed_closure,
    eq_univ_of_subset (iUnion_mono fun _ => subset_closure) htu, htf.closure, fun b => ?_⟩
  obtain ⟨x, hx⟩ := htw b
  exact ⟨i x, (closure_mono hx).trans <| (closure_minimal interior_subset (hwc x)).trans (hws x)⟩

/-- **Michael's lemma, (b) ⇒ (c)**: if every open cover has a σ-locally finite open refinement
(`t n b`, each family `t n` locally finite), then every open cover has a locally finite
refinement.  No separation axiom is needed. -/
theorem refinement_of_sigma_refinement
    (h : ∀ (α : Type u) (s : α → Set X), (∀ a, IsOpen (s a)) → ⋃ a, s a = univ →
      ∃ (β : ℕ → Type u) (t : ∀ n, β n → Set X), (∀ n b, IsOpen (t n b)) ∧
        ⋃ n, ⋃ b, t n b = univ ∧ (∀ n, LocallyFinite (t n)) ∧ ∀ n b, ∃ a, t n b ⊆ s a)
    (α : Type u) (s : α → Set X) (ho : ∀ a, IsOpen (s a)) (hu : ⋃ a, s a = univ) :
    ∃ (β : Type u) (t : β → Set X), ⋃ b, t b = univ ∧ LocallyFinite t ∧ ∀ b, ∃ a, t b ⊆ s a := by
  obtain ⟨β, t, hto, htu, htf, hts⟩ := h α s ho hu
  refine ⟨Σ n, β n, fun p => t p.1 p.2 \ ⋃ k < p.1, ⋃ b, t k b, ?_, ?_,
    fun p => (hts p.1 p.2).imp fun _ ha => sdiff_subset.trans ha⟩
  · classical
    refine eq_univ_iff_forall.2 fun x => ?_
    have hex : ∃ n, x ∈ ⋃ b, t n b := mem_iUnion.1 (htu.symm ▸ mem_univ x)
    obtain ⟨b, hb⟩ := mem_iUnion.1 (Nat.find_spec hex)
    refine mem_iUnion.2 ⟨⟨Nat.find hex, b⟩, hb, fun hx' => ?_⟩
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 hx'
    exact Nat.find_min hex hk hxk
  · intro x
    obtain ⟨n, b₀, hb₀⟩ : ∃ n b, x ∈ t n b := by
      simpa only [mem_iUnion] using (htu.symm ▸ mem_univ x : x ∈ ⋃ n, ⋃ b, t n b)
    choose N hN hNf using fun k => htf k x
    refine ⟨t n b₀ ∩ ⋂ k ∈ Iic n, N k,
      inter_mem ((hto n b₀).mem_nhds hb₀) ((biInter_mem (finite_Iic n)).2 fun k _ => hN k),
      ((finite_Iic n).biUnion fun k _ => (hNf k).image (Sigma.mk k)).subset ?_⟩
    rintro ⟨m, b⟩ ⟨y, ⟨hyt, hyT⟩, hy0, hyN⟩
    have hmn : m ≤ n := by
      by_contra hmn
      exact hyT (mem_iUnion₂.2 ⟨n, not_le.1 hmn, mem_iUnion.2 ⟨b₀, hy0⟩⟩)
    exact mem_iUnion₂.2 ⟨m, hmn, b, ⟨y, hyt, mem_iInter₂.1 hyN m hmn⟩, rfl⟩

/-- **Michael's lemma, (c) ⇒ (a)**: a regular space in which every open cover has a locally finite
refinement (by arbitrary sets) is paracompact. -/
theorem paracompactSpace_of_refinement [RegularSpace X]
    (h : ∀ (α : Type u) (s : α → Set X), (∀ a, IsOpen (s a)) → ⋃ a, s a = univ →
      ∃ (β : Type u) (t : β → Set X), ⋃ b, t b = univ ∧ LocallyFinite t ∧ ∀ b, ∃ a, t b ⊆ s a) :
    ParacompactSpace X :=
  paracompactSpace_of_closed_refinement (closed_refinement_of_refinement h)

/-- **Michael's theorem, (b) ⇒ (a)**: a regular space in which every open cover has a σ-locally
finite open refinement is paracompact. -/
theorem paracompactSpace_of_sigma_refinement [RegularSpace X]
    (h : ∀ (α : Type u) (s : α → Set X), (∀ a, IsOpen (s a)) → ⋃ a, s a = univ →
      ∃ (β : ℕ → Type u) (t : ∀ n, β n → Set X), (∀ n b, IsOpen (t n b)) ∧
        ⋃ n, ⋃ b, t n b = univ ∧ (∀ n, LocallyFinite (t n)) ∧ ∀ n b, ∃ a, t n b ⊆ s a) :
    ParacompactSpace X :=
  paracompactSpace_of_refinement (refinement_of_sigma_refinement h)

/-- **Michael's lemma, (a) ⇒ (d)**, precise form: in a regular paracompact space every open cover
`u` has a locally finite refinement `v` by closed sets with the same index and `v i ⊆ u i`. -/
theorem exists_closed_precise_refinement [RegularSpace X] [ParacompactSpace X] {ι : Type v}
    (u : ι → Set X) (uo : ∀ i, IsOpen (u i)) (uc : ⋃ i, u i = univ) :
    ∃ v : ι → Set X, (∀ i, IsClosed (v i)) ∧ ⋃ i, v i = univ ∧ LocallyFinite v ∧
      ∀ i, v i ⊆ u i := by
  obtain ⟨w, wo, wc, wf, wu⟩ := precise_refinement u uo uc
  obtain ⟨v, vc, -, vw⟩ := exists_iUnion_eq_closure_subset wo (fun x => wf.point_finite x) wc
  exact ⟨fun i => closure (v i), fun _ => isClosed_closure,
    eq_univ_of_subset (iUnion_mono fun _ => subset_closure) vc, wf.subset vw,
    fun i => (vw i).trans (wu i)⟩

/-- The version of `exists_closed_precise_refinement` for an open cover `u` of a closed subset
`s`: a locally finite family of closed sets `v i ⊆ s ∩ u i` covering `s`. -/
theorem exists_closed_precise_refinement_set [RegularSpace X] [ParacompactSpace X] {ι : Type v}
    {s : Set X} (hs : IsClosed s) (u : ι → Set X) (uo : ∀ i, IsOpen (u i))
    (us : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, (∀ i, IsClosed (v i)) ∧ s ⊆ ⋃ i, v i ∧ LocallyFinite v ∧
      ∀ i, v i ⊆ s ∩ u i := by
  have uc : ⋃ o, Option.elim' sᶜ u o = univ := by
    rw [iUnion_option, Option.elim'_none, ← compl_subset_iff_union]
    simpa only [Option.elim'_some, compl_compl] using us
  obtain ⟨v, vc, vu, vf, vs⟩ :=
    exists_closed_precise_refinement _ (Option.forall.2 ⟨hs.isOpen_compl, uo⟩) uc
  refine ⟨fun i => v (some i) ∩ s, fun i => (vc _).inter hs, fun x hx => ?_,
    (vf.comp_injective (Option.some_injective _)).subset fun _ => inter_subset_left,
    fun i => subset_inter inter_subset_right (inter_subset_left.trans (vs (some i)))⟩
  obtain ⟨o, ho⟩ := iUnion_eq_univ_iff.1 vu x
  cases o with
  | none => exact absurd hx (vs none ho)
  | some i => exact mem_iUnion.2 ⟨i, ho, hx⟩

/-- **Lemma 2.7** [2.56] (Michael 1953, Lemma 1): a regular space is paracompact if and only if
every open cover has a locally finite refinement by closed sets.  The text assumes "regular
Hausdorff"; Hausdorff is not used. -/
theorem lemma_2_56 [RegularSpace X] :
    ParacompactSpace X ↔
      ∀ (α : Type u) (s : α → Set X), (∀ a, IsOpen (s a)) → ⋃ a, s a = univ →
        ∃ (β : Type u) (t : β → Set X), (∀ b, IsClosed (t b)) ∧ ⋃ b, t b = univ ∧
          LocallyFinite t ∧ ∀ b, ∃ a, t b ⊆ s a := by
  refine ⟨fun _ α s ho hu => ?_, paracompactSpace_of_closed_refinement⟩
  obtain ⟨v, vc, vu, vf, vs⟩ := exists_closed_precise_refinement s ho hu
  exact ⟨α, v, vc, vu, vf, fun a => ⟨a, vs a⟩⟩

/-- **Michael's Lemma 1** (Michael 1953): for a regular space the following are equivalent:
(a) paracompact; (b) every open cover has a σ-locally finite open refinement; (c) every open cover
has a locally finite refinement; (d) every open cover has a locally finite closed refinement. -/
theorem michael_tfae [RegularSpace X] :
    List.TFAE [ParacompactSpace X,
      ∀ (α : Type u) (s : α → Set X), (∀ a, IsOpen (s a)) → ⋃ a, s a = univ →
        ∃ (β : ℕ → Type u) (t : ∀ n, β n → Set X), (∀ n b, IsOpen (t n b)) ∧
          ⋃ n, ⋃ b, t n b = univ ∧ (∀ n, LocallyFinite (t n)) ∧ ∀ n b, ∃ a, t n b ⊆ s a,
      ∀ (α : Type u) (s : α → Set X), (∀ a, IsOpen (s a)) → ⋃ a, s a = univ →
        ∃ (β : Type u) (t : β → Set X), ⋃ b, t b = univ ∧ LocallyFinite t ∧
          ∀ b, ∃ a, t b ⊆ s a,
      ∀ (α : Type u) (s : α → Set X), (∀ a, IsOpen (s a)) → ⋃ a, s a = univ →
        ∃ (β : Type u) (t : β → Set X), (∀ b, IsClosed (t b)) ∧ ⋃ b, t b = univ ∧
          LocallyFinite t ∧ ∀ b, ∃ a, t b ⊆ s a] := by
  tfae_have 1 → 2 := fun _ α s ho hu => by
    obtain ⟨β, t, hto, htu, htf, hts⟩ := ParacompactSpace.locallyFinite_refinement α s ho hu
    exact ⟨fun _ => β, fun _ => t, fun _ => hto, by rw [iUnion_const, htu], fun _ => htf,
      fun _ => hts⟩
  tfae_have 2 → 3 := refinement_of_sigma_refinement
  tfae_have 3 → 4 := closed_refinement_of_refinement
  tfae_have 4 → 1 := paracompactSpace_of_closed_refinement
  tfae_finish

/-! ### Locally finite unions of closed paracompact subspaces -/

/-- **Proposition 2.17** [2.57]: a regular space which is the union of a locally finite family of
closed paracompact subspaces is paracompact.  The text assumes "regular Hausdorff"; Hausdorff is
not used. -/
theorem proposition_2_57 [RegularSpace X] {ι : Type v} (Y : ι → Set X)
    (hYc : ∀ i, IsClosed (Y i)) (hYf : LocallyFinite Y) (hYu : ⋃ i, Y i = univ)
    [∀ i, ParacompactSpace (Y i)] : ParacompactSpace X := by
  refine paracompactSpace_of_closed_refinement fun α U hUo hUu => ?_
  -- in each `Y i`, a closed locally finite precise refinement `C i` of the traces of `U`
  have key : ∀ i, ∃ C : α → Set (Y i), (∀ j, IsClosed (C j)) ∧ ⋃ j, C j = univ ∧
      LocallyFinite C ∧ ∀ j, C j ⊆ ((↑) : Y i → X) ⁻¹' U j := fun i =>
    exists_closed_precise_refinement (fun j => ((↑) : Y i → X) ⁻¹' U j)
      (fun j => (hUo j).preimage continuous_subtype_val)
      (by rw [← preimage_iUnion, hUu, preimage_univ])
  choose C hCc hCu hCf hCU using key
  refine ⟨α, fun j => ⋃ i, ((↑) : Y i → X) '' C i j, fun j => ?_, ?_, fun x => ?_,
    fun j => ⟨j, iUnion_subset fun i => (image_mono (hCU i j)).trans (image_preimage_subset _ _)⟩⟩
  · refine (hYf.subset fun i => ?_).isClosed_iUnion fun i =>
      (hYc i).isClosedMap_subtype_val _ (hCc i j)
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  · refine eq_univ_iff_forall.2 fun x => ?_
    obtain ⟨i, hi⟩ := iUnion_eq_univ_iff.1 hYu x
    obtain ⟨j, hj⟩ := iUnion_eq_univ_iff.1 (hCu i) ⟨x, hi⟩
    exact mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨i, ⟨x, hi⟩, hj, rfl⟩⟩
  · obtain ⟨N, hN, hNf⟩ := hYf x
    choose M hM hMf using fun i => locallyFinite_image_val (hYc i) (hCf i) x
    refine ⟨N ∩ ⋂ i ∈ {i | (Y i ∩ N).Nonempty}, M i,
      inter_mem hN ((biInter_mem hNf).2 fun i _ => hM i), (hNf.biUnion fun i _ => hMf i).subset ?_⟩
    rintro j ⟨y, hy, hyN, hyM⟩
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.1 hy
    have hi : (Y i ∩ N).Nonempty := ⟨z, z.2, hyN⟩
    exact mem_iUnion₂.2 ⟨i, hi, (z : X), ⟨z, hz, rfl⟩, mem_iInter₂.1 hyM i hi⟩

/-- **Proposition 2.17**, subspace form: in a regular space, the union of a locally finite family
of closed subsets, each paracompact, is paracompact. -/
theorem paracompactSpace_iUnion [RegularSpace X] {ι : Type v} {s : ι → Set X}
    (hc : ∀ i, IsClosed (s i)) (hf : LocallyFinite s) [∀ i, ParacompactSpace (s i)] :
    ParacompactSpace (⋃ i, s i) := by
  have : ∀ i, ParacompactSpace ((⋃ i, s i) ↓∩ s i) := fun i =>
    (homeomorphPreimageVal (subset_iUnion s i)).paracompactSpace_iff.2 inferInstance
  refine proposition_2_57 (fun i => (⋃ i, s i) ↓∩ s i)
    (fun i => (hc i).preimage continuous_subtype_val)
    (hf.preimage_continuous continuous_subtype_val) (eq_univ_iff_forall.2 fun x => ?_)
  obtain ⟨i, hi⟩ := mem_iUnion.1 x.2
  exact mem_iUnion.2 ⟨i, hi⟩

/-- In a regular space, the union of finitely many closed paracompact subsets is paracompact. -/
theorem paracompactSpace_iUnion_of_finite [RegularSpace X] {ι : Type v} [Finite ι]
    {s : ι → Set X} (hc : ∀ i, IsClosed (s i)) [∀ i, ParacompactSpace (s i)] :
    ParacompactSpace (⋃ i, s i) :=
  paracompactSpace_iUnion hc (locallyFinite_of_finite s)

/-- In a regular space, `⋃ i ∈ S, s i` is paracompact for a finite `S` and closed paracompact
`s i`, `i ∈ S` (Corollary 7.2's `⋃ cl U(zᵢ)`). -/
theorem paracompactSpace_biUnion_of_finite [RegularSpace X] {ι : Type v} {S : Set ι}
    (hS : S.Finite) {s : ι → Set X} (hc : ∀ i ∈ S, IsClosed (s i))
    (hp : ∀ i ∈ S, ParacompactSpace (s i)) : ParacompactSpace (⋃ i ∈ S, s i) := by
  have : Finite S := hS.to_subtype
  have : ∀ i : S, ParacompactSpace (s i) := fun i => hp i i.2
  rw [biUnion_eq_iUnion]
  exact paracompactSpace_iUnion_of_finite (s := fun i : S => s i) fun i => hc i i.2

/-- In a regular space, the union of two closed paracompact subsets is paracompact. -/
theorem paracompactSpace_union [RegularSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsClosed t)
    [ParacompactSpace s] [ParacompactSpace t] : ParacompactSpace (s ∪ t : Set X) := by
  have : ∀ b : Bool, ParacompactSpace (cond b s t : Set X) := fun b => by
    cases b <;> assumption
  rw [union_eq_iUnion]
  exact paracompactSpace_iUnion_of_finite fun b => by cases b <;> assumption

/-- A closed subset `s` of `X` contained in a paracompact subspace `t` is paracompact. -/
theorem paracompactSpace_of_isClosed_subset {s t : Set X} (hs : IsClosed s) (hst : s ⊆ t)
    [ParacompactSpace t] : ParacompactSpace s :=
  (IsClosedEmbedding.inclusion hst (hs.preimage continuous_subtype_val)).paracompactSpace

end Polyfold
