import Polyfold.Chapter7.OrbitTopology

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II, §7.4
and Appendix 7.5.2: **Theorem 7.3** (p. 250), **Remark 7.2** (p. 251), **Theorem 7.4** (p. 251)
= **Theorem 7.6** (p. 255), **Lemma 7.10** (p. 255), the proof of Theorem 7.4 (pp. 255–256) and
**Corollary 7.3** (p. 256).  There is no 2014 preprint of Part II; numbers and pages are the 2017
text's.  Definition 7.16 (pp. 250–251) is in `EpGroupoid.lean` (`HasScPartitionsOfUnity`).
Part I items carry their 2017 numbers with the preprint number of the Lean name in brackets.

# Partitions of unity on ep-groupoids

## The text, paraphrased

(Theorem 7.3) If `|X|` is paracompact, every open cover `(O_λ)` of `|X|` has a subordinate
partition of unity `(σ_λ)` (some `σ_λ ≡ 0`); every cover `(U_λ)` of `X` by saturated open sets has
a subordinate continuous partition of unity `(β_λ)` whose functions take equal values on
isomorphic objects.  *Proof*: `β_λ = σ_λ ∘ π` for `σ` subordinate to `O_λ = π(U_λ)`; its support
lies in `π⁻¹(O_λ) = U_λ`, and `π⁻¹(V)` meets finitely many supports if `V` meets finitely many
supports of the `σ_λ`.  (Remark 7.2) Apart from sc-Hilbert spaces the existence of sc-smooth
partitions of unity is "a zoo", as for classically smooth ones on Banach spaces.  (Theorem 7.4 =
Theorem 7.6) If `|X|` is paracompact and the object M-polyfold admits sc-smooth partitions of
unity, every cover of `X` by saturated open sets has a subordinate sc-smooth partition of unity of
the ep-groupoid (Definition 7.16).  (Lemma 7.10) Let `|X|` be paracompact, `X` admit sc-smooth
partitions of unity, `U(x) ⊆ cl U(x) ⊆ V(x)` open neighbourhoods of `x`, `V(x)` with the natural
`G_x`-action and `U(x)` invariant.  A continuous `β : X → [0, 1]` supported in `U(x)` and
invariant under `G_x` on `V(x)` lies below an sc-smooth `f : X → [0, ∞)` supported in `V(x)` and
invariant under `G_x` on `V(x)`.  *Proof*: open `W(z)`, `z ∈ V(x)`, with numbers `a_z` (`cl W(z) ⊆
U(x)` and `β < a_z` on `W(z)` for `z ∈ U(x)`; `W(z) ⊆ V(x)`, `β|W(z) = 0`, `a_z = 0` otherwise); an
sc-smooth partition of unity `(σ_z)` of `V(x)` subordinate to them; `γ = Σ σ_z a_z ≥ β` is
supported in `cl U(x)`; `f(y) = |G_x|⁻¹ Σ_g γ(g ∗ y)`.  (Proof of Theorem 7.4) For every `x` an
open `V(x)` with (1) an open `W(x)` with the natural `G_x`-action, `V(x) ⊆ cl V(x) ⊆ W(x)`, `V(x)`
invariant; (2) `t : s⁻¹(cl V(x)) → X` proper; (3) `V(x) ⊆ U_λ` for some `λ`; (4) `(π⁻¹(|V(x)|) ∖
V(x)) ∩ W(x) = ∅`.  A locally finite refinement `(V'_i)` of `(|V(x)|)`, `V'_i ⊆ |V(x_i)|`, open
`V''_i ⊆ cl V''_i ⊆ V'_i` covering `|X|`, `U''_i = V(x_i) ∩ π⁻¹(V''_i)`, a partition of unity
`(β_i)` subordinate to `(V''_i)`; Lemma 7.10 gives `f_i ≥ (β_i ∘ π)|V(x_i)` supported in
`V(x_i)`; averaging, extending to the saturation and by `0` gives `h_i`; `h = Σ h_i > 0` is
locally finite and `(h_i/h)` is the partition of unity.  (Corollary 7.3) If `|X|` is paracompact
and the object M-polyfold has an atlas whose local models have Hilbert spaces `E₀`, Theorem 7.4
applies: such an `X` admits sc-smooth partitions of unity (Appendix 5.5, Proposition 5.6 [5.35],
Theorem 5.12 [5.37], Corollary 5.2 [5.44]).

## What is formalized (namespace `Polyfold.EpGroupoid`)

* **Theorem 7.3**: `theorem_7_3` (both statements); the pull-back `orbitPullback σ = σ ∘ π` of a
  partition of unity of `|X|`, with `orbitPullback_apply`, `orbitPullback_src`,
  `tsupport_orbitPullback_subset`, `orbitPullback_isSubordinate`,
  `exists_isSaturated_nhds_finite_orbitPullback`.
* **Remark 7.2**: no formal content; not formalized.
* **Lemma 7.10**: `lemma_7_10`.
* **The proof of Theorem 7.4**: properties (1)–(3), `exists_invariant_nhds_of_isOpen`; property
  (4), `mem_of_π_mem_image_of_invariant` and `saturation_diff_inter_eq_empty`; the extension
  `orbitExtension R f` of a `G_x`-invariant function on `W(x)` to `|X|`, with
  `orbitExtension_π`, `orbitExtension_nonneg`, `support_orbitExtension_subset`,
  `isScSmoothMap_orbitExtension`; the invariant sc-smooth Urysohn lemma
  `exists_isScSmoothMap_orbit_urysohn`.
* **Theorem 7.4**: `theorem_7_4`; **Theorem 7.6**: `theorem_7_6` (= `theorem_7_4`).
* **Corollary 7.3**: `corollary_7_3`.
* **Satisfiability** (PLAN II.5, 3): `theorem_7_4_hypotheses_rn`,
  `hasScPartitionsOfUnity_trivial_rn_of_theorem_7_4`, `corollary_7_3_hypotheses_rn`.

## Reading

* **Theorem 7.3.**  Index types are arbitrary (`ι : Type v`); "subordinate" is Mathlib's
  `PartitionOfUnity.IsSubordinate` (`tsupport σ_λ ⊆ O_λ`); "(some of the `σ_λ ≡ 0`)" has no
  content beyond the index set being `Λ`.  "Due to paracompactness … a partition of unity" is
  `PartitionOfUnity.exists_isSubordinate`, which needs `|X|` normal: paracompact (Definition 7.15,
  `HasParacompactOrbitSpace`) and Hausdorff (Lemma 7.6, `lemma_7_6`).  The second statement has
  the conclusions of Definition 7.16 except sc-smoothness: the text's neighbourhood `π⁻¹(V)` is a
  saturated open neighbourhood meeting finitely many supports, and "takes the same values on
  isomorphic objects" is `β_λ(s φ) = β_λ(t φ)`.  "The support of `β_λ` lies in `π⁻¹(O_λ) = U_λ`"
  is `tsupport (σ_λ ∘ π) ⊆ π⁻¹(tsupport σ_λ) ⊆ π⁻¹(π(U_λ)) = U_λ`.
* **Lemma 7.10.**  "`V(x)` admits the natural `G_x`-action" is a natural representation `R` with
  `V(x) = R.U` (PLAN II.5, 6); "`U(x)` invariant" is `MapsTo (R.Φ g) U U` for all `g`; `β` is a
  continuous `Obj → ℝ` with values in `[0, 1]`, "support in `U(x)`" is `tsupport β ⊆ U`, the
  invariance is `β(Φ(g)(y)) = β(y)` on `R.U`; `f ≥ 0`.  The conclusion adds `tsupport f ⊆ cl U(x)`,
  which the proof gives ("`γ` … with support in `cl_X(U(x))`", kept by averaging over the invariant
  `U(x)`) and which Theorem 7.4 needs (below).  The hypothesis "`U(x)` is a neighbourhood of `x`" is
  not used by the proof and is omitted (a stronger statement): the proof of Theorem 7.4 applies the
  lemma to `U''_i`, which need not contain `x_i`.  The paracompactness of `|X|` and the continuity
  of `β` are kept as in the text (`_hpara`, `_hβ`) but not used: the two-set cover below needs
  neither.  **The partition of unity "of `V(x)`" is taken for a cover of `X`** (PLAN II.6, 4): the
  hypothesis is that `X`, not the open subset `V(x)`, admits sc-smooth partitions of unity, so the
  text's cover `(W(z))_{z ∈ V(x)}` of `V(x)` is completed by `X ∖ cl U(x)` (where `β = 0`, `a = 0`).
  We coarsen this cover of `X` to two sets: `U(x)` with `a = 1` (as `β ≤ 1`; the text's `cl W(z) ⊆
  U(x)` and `β < a_z` are not needed) and `X ∖ supp β ⊇ X ∖ cl U(x)` with `a = 0`, so that `γ` is
  the function of the partition attached to `U(x)`.  The average `f(y) = |G_x|⁻¹ Σ_g γ(g ∗ y)` is
  read on `V(x)` and extended by `0`: each `γ ∘ Φ(g)`, extended by `0`, is supported in `cl U(x) ⊆
  V(x)` and hence sc-smooth on `X`; `β ≤ f` uses the invariance of `β`, the invariance of `f` the
  reindexing `g ↦ g h`.
* **Proof of Theorem 7.4, properties (1)–(4).**  (1)–(3) are `exists_invariant_nhds_of_isOpen`:
  `W(x) = R.U` from Theorem 7.1 inside `U_λ ∩ V₀`, `V₀` with the properness property
  (Definition 7.3 (3), `HasPropernessProperty.mono`), and `V(x) = ⋂_g Φ(g)⁻¹(N)` for an open
  `N ∋ x` with `cl N ⊆ W(x)`.  **(4) follows from (1)** and is not a further choice: the
  morphisms between points of `W(x)` are the `Γ(g, ·)` (Theorem 7.1 (3)), so a point of `W(x)`
  isomorphic to a point of the invariant `V(x)` lies in `V(x)` (`mem_of_π_mem_image_of_invariant`,
  `saturation_diff_inter_eq_empty`).
* **The four points of PLAN II.6, 4, checked; all four stand.**
  (a) Lemma 7.10 is applied with `W(x_i)` in the role of `V(x)` and `U''_i` in the role of
  `U(x)`: its hypothesis `cl U ⊆ V`, with the natural action on `V`, holds for `W(x_i)` by (1).
  The text's "approximate `(β_i ∘ π)|V(x_i)` using Lemma 7.10" reads as `V(x_i)` in the role of
  `V(x)` (possible misprint).
  (b) The continuity of the cut-off `(β_i ∘ π)|V(x_i)`, extended by `0`, uses (4): a point of
  `cl V(x_i) ∩ π⁻¹(supp β_i)` lies in `W(x_i)` and is isomorphic to a point of `V(x_i)` (as
  `supp β_i ⊆ V'_i ⊆ |V(x_i)|`), hence lies in `V(x_i)` by (4); so the cut-off is supported in
  `U''_i ⊆ V(x_i)`.
  (c) "The sum of all `h_i` is locally finite" needs `supp f_i ⊆ π⁻¹(cl V'_i)`, which the text
  does not state: Lemma 7.10 as stated gives only `supp f_i ⊆ W(x_i)`, and the saturations of the
  `W(x_i)` need not be locally finite.  The bound `supp f_i ⊆ cl U''_i` of the lemma's proof gives
  it, `(cl V'_i)` being locally finite.  (With the text's `V''_i`, `cl V''_i ⊆ V'_i ⊆ |V(x_i)|`
  and (4) also give the text's `supp f_i ⊆ V(x_i)`.)
  (d) The sc-smoothness of `h_i` uses that saturations of proper sets are closed: `h_i` vanishes
  off the saturation of `supp f_i`, which is closed because `supp f_i ⊆ cl V(x_i)` is proper by
  (2) (`isClosed_saturation_of_isProperSubset`, the argument of Proposition 7.14 (1)).  Near a
  point `y ≅ z` of that saturation `h_i = f_i ∘ s ∘ (t|U(φ))⁻¹`, `φ : z → y` (Definition 7.4).
* "We average using the `G_{x_i}`-action": `f_i` is already invariant (Lemma 7.10), no second
  average is taken.  "Extend to the saturation": `orbitExtension`, `F(|y|) = f(y)` for `y ∈ W(x)`,
  well defined since points of `W(x)` in one orbit differ by the natural action
  (`NaturalRep.π_eq_π_iff_exists_smul`, Theorem 7.1 (3)).
* **The normalization.**  The text's `(h_i/h)` and the passage from the index set `I` of the
  refinement back to `Λ` (which the text leaves implicit) are replaced by Mathlib's
  `BumpCovering.exists_isSubordinate_of_prop` on `|X|` for the predicate "`g ∘ π` is sc-smooth",
  as in Part I's Theorem 5.12 [5.37] (`admitsScPartitionsOfUnity_of_approx`).  Its Urysohn input,
  `exists_isScSmoothMap_orbit_urysohn`, is the text's construction for closed disjoint `s, t ⊆ |X|`:
  the points `x ∈ π⁻¹(t)` with `W(x) ⊆ π⁻¹(|X| ∖ s)`, a refinement `(V'_x)` of `(|V(x)|)` covering
  `t`, a subordinate bump covering `(β_x)` of `t` (whose `tsupport β_x ⊆ V'_x` takes the place of
  `V''_x`), `G = Σ h_x` (`= 0` on `s`, `≥ 1` on `t`) and `F = τ ∘ G` with `τ` Mathlib's
  `Real.smoothTransition`.  The partition `ρ_λ = b_λ ∏_{μ<λ}(1 − b_μ)` of `|X|` is locally a finite
  product of functions `g` with `g ∘ π` sc-smooth, and `ρ ∘ π` (Theorem 7.3's pull-back) is the
  partition of unity of Definition 7.16.
* **Corollary 7.3.**  "An atlas consisting of charts whose local models have Hilbert spaces `E₀`"
  is existential, one chart per point, as Part I's `MPolyfold.admitsScPartitionsOfUnity_of_hilbert`;
  "Hilbert" is read as there (`‖v‖² = b(v, v)` for a continuous bilinear `b`).  "Every compatible
  chart has a Hilbert `E₀`" would be unsatisfiable (PLAN II.5, 2).  Theorem 5.14 [5.43]
  (Godefroy–Troyanski–Whitfield–Zizler) is an explicit hypothesis,
  `GodefroyTroyanskiWhitfieldZizlerStatement`, as in Part I.  The text's references Proposition
  5.6 [5.35], Theorem 5.12 [5.37] and Corollary 5.2 [5.44] are the ingredients of that theorem.
* **Hypotheses.**  No hypothesis "for all charts" is added.  The hypotheses of Theorems 7.4 and
  7.6, of Lemma 7.10 and of Corollary 7.3 are satisfiable: the trivial ep-groupoid on `ℝⁿ` has
  paracompact orbit space (`hasParacompactOrbitSpace_trivial`) and `ℝⁿ` admits sc-smooth
  partitions of unity (`rnPolyfold_admitsScPartitionsOfUnity`); the Hilbert atlas and Theorem 5.14
  [5.43] hold for `ℝ¹` (`rnPolyfold_one_hilbert_hypothesis`).  Lemma 7.10's invariance hypotheses
  ("for every `g`") hold for every `G_x`-invariant `β`, e.g. `β = 0`.
* No possible misprint was found on pp. 250–256 other than (a).
-/

open Set Function Filter Topology
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

/-! ### Sc-smooth functions: locality and extension by zero -/

section ScFunctions

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {P : MPolyfold Z}

/-- A function which is sc-smooth on an open neighbourhood of every point is sc-smooth. -/
private theorem isScSmoothMap_real_of_isScSmoothOn_nhds {f : Z → ℝ}
    (h : ∀ y, ∃ N : Set Z, y ∈ N ∧ P.IsScSmoothOn realPolyfold f N) :
    P.IsScSmoothMap realPolyfold f := by
  refine isScSmoothMap_real_of_local fun y => ?_
  obtain ⟨N, hyN, hN⟩ := h y
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y
  have hVo : IsOpen (N ∩ φ.source) := hN.isOpen.inter φ.isOpen_source
  exact ⟨φ, N ∩ φ.source, hφ, hVo, ⟨hyN, hyφ⟩, inter_subset_right,
    hN.smooth φ realChart hφ isChart_realChart _ hVo subset_rfl (mapsTo_univ _ _)⟩

/-- **Extension by zero**: a function sc-smooth on an open set containing its support is
sc-smooth. -/
private theorem isScSmoothMap_real_of_tsupport_subset {f : Z → ℝ} {N : Set Z}
    (hf : P.IsScSmoothOn realPolyfold f N) (hN : tsupport f ⊆ N) :
    P.IsScSmoothMap realPolyfold f := by
  refine isScSmoothMap_real_of_isScSmoothOn_nhds fun y => ?_
  by_cases hy : y ∈ N
  · exact ⟨N, hy, hf⟩
  · refine ⟨(tsupport f)ᶜ, fun h => hy (hN h), ?_⟩
    refine ((isScSmoothMap_real_const (PX := P) 0).mono (isClosed_tsupport f).isOpen_compl
      (subset_univ _)).congr fun z hz => ?_
    exact (image_eq_zero_of_notMem_tsupport hz).symm

end ScFunctions

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### Theorem 7.3 -/

section Theorem73

variable {ι : Type v}

/-- **The pull-back `σ ∘ π`** of a partition of unity `σ` of `|X|` (the proof of Theorem 7.3). -/
def orbitPullback (σ : PartitionOfUnity ι X.OrbitSpace) : PartitionOfUnity ι Obj where
  toFun i := (σ i).comp ⟨X.π, X.continuous_π⟩
  locallyFinite' := σ.locallyFinite.preimage_continuous X.continuous_π
  nonneg' i y := σ.nonneg i (X.π y)
  sum_eq_one' y _ := σ.sum_eq_one (mem_univ (X.π y))
  sum_le_one' y := σ.sum_le_one (X.π y)

theorem orbitPullback_apply (σ : PartitionOfUnity ι X.OrbitSpace) (i : ι) (y : Obj) :
    X.orbitPullback σ i y = σ i (X.π y) := rfl

/-- The functions `σ_λ ∘ π` take the same values on isomorphic objects. -/
theorem orbitPullback_src (σ : PartitionOfUnity ι X.OrbitSpace) (i : ι) (φ : Mor) :
    X.orbitPullback σ i (X.src φ) = X.orbitPullback σ i (X.tgt φ) := by
  simp only [orbitPullback_apply, X.π_src_eq_π_tgt φ]

/-- `supp(σ_λ ∘ π) ⊆ π⁻¹(supp σ_λ)`. -/
theorem tsupport_orbitPullback_subset (σ : PartitionOfUnity ι X.OrbitSpace) (i : ι) :
    tsupport (X.orbitPullback σ i) ⊆ X.π ⁻¹' tsupport (σ i) :=
  tsupport_comp_subset_preimage (σ i) X.continuous_π

/-- If `σ` is subordinate to `(π(U_λ))` with saturated `U_λ`, then `σ ∘ π` is subordinate to
`(U_λ)`: `supp(σ_λ ∘ π) ⊆ π⁻¹(π(U_λ)) = U_λ`. -/
theorem orbitPullback_isSubordinate {σ : PartitionOfUnity ι X.OrbitSpace} {U : ι → Set Obj}
    (hσ : σ.IsSubordinate fun i => X.π '' U i) (hU : ∀ i, X.IsSaturated (U i)) :
    (X.orbitPullback σ).IsSubordinate U := fun i =>
  ((X.tsupport_orbitPullback_subset σ i).trans (preimage_mono (hσ i))).trans (hU i).subset

/-- Every object has a saturated open neighbourhood `π⁻¹(V)` meeting only finitely many
`supp(σ_λ ∘ π)` (Definition 7.16 (1)). -/
theorem exists_isSaturated_nhds_finite_orbitPullback (σ : PartitionOfUnity ι X.OrbitSpace)
    (x : Obj) : ∃ W : Set Obj, IsOpen W ∧ X.IsSaturated W ∧ x ∈ W ∧
      {i | (W ∩ tsupport (X.orbitPullback σ i)).Nonempty}.Finite := by
  obtain ⟨t, ht, hfin⟩ := σ.locallyFinite (X.π x)
  have hWo : IsOpen (X.π ⁻¹' interior t) := isOpen_interior.preimage X.continuous_π
  refine ⟨X.π ⁻¹' interior t, hWo, ?_, mem_interior_iff_mem_nhds.2 ht, hfin.subset fun i hi => ?_⟩
  · change X.π ⁻¹' (X.π '' (X.π ⁻¹' interior t)) = X.π ⁻¹' interior t
    rw [image_preimage_eq _ X.surjective_π]
  · have hi' : (tsupport (X.orbitPullback σ i) ∩ X.π ⁻¹' interior t).Nonempty := by
      rw [inter_comm]
      exact hi
    obtain ⟨y, hy, hyt⟩ := (closure_inter_open_nonempty_iff hWo).1 hi'
    exact ⟨X.π y, hy, interior_subset hyt⟩

/-- The images `π(U_λ)` of a cover of `X` cover `|X|`. -/
private theorem iUnion_image_π_eq_univ {U : ι → Set Obj} (hU : ⋃ i, U i = univ) :
    ⋃ i, X.π '' U i = univ := by
  rw [← image_iUnion, hU, image_univ_of_surjective X.surjective_π]

/-- **Theorem 7.3 (continuous partitions of unity)**: if `|X|` is paracompact, (1) every open
cover `(O_λ)` of `|X|` has a subordinate partition of unity `(σ_λ)`, and (2) every cover `(U_λ)`
of `X` by saturated open sets has a subordinate continuous partition of unity `(β_λ)`, every
object having a saturated open neighbourhood meeting only finitely many supports, with
`β_λ(y) = β_λ(z)` for isomorphic `y, z` (namely `β_λ = σ_λ ∘ π`). -/
theorem theorem_7_3 (h : X.HasParacompactOrbitSpace) :
    (∀ (ι : Type v) (O : ι → Set X.OrbitSpace), (∀ i, IsOpen (O i)) → ⋃ i, O i = univ →
      ∃ σ : PartitionOfUnity ι X.OrbitSpace, σ.IsSubordinate O) ∧
    ∀ (ι : Type v) (U : ι → Set Obj), (∀ i, IsOpen (U i)) → (∀ i, X.IsSaturated (U i)) →
      ⋃ i, U i = univ → ∃ β : PartitionOfUnity ι Obj, β.IsSubordinate U ∧
        (∀ x, ∃ W : Set Obj, IsOpen W ∧ X.IsSaturated W ∧ x ∈ W ∧
          {i | (W ∩ tsupport (β i)).Nonempty}.Finite) ∧
        ∀ i φ, β i (X.src φ) = β i (X.tgt φ) := by
  have : ParacompactSpace X.OrbitSpace := h
  have h1 : ∀ (ι : Type v) (O : ι → Set X.OrbitSpace), (∀ i, IsOpen (O i)) → ⋃ i, O i = univ →
      ∃ σ : PartitionOfUnity ι X.OrbitSpace, σ.IsSubordinate O := fun ι O hO hcov =>
    PartitionOfUnity.exists_isSubordinate isClosed_univ O hO hcov.symm.subset
  refine ⟨h1, fun ι U hUo hUs hcov => ?_⟩
  obtain ⟨σ, hσ⟩ := h1 ι (fun i => X.π '' U i) (fun i => X.proposition_7_1 _ (hUo i))
    (X.iUnion_image_π_eq_univ hcov)
  exact ⟨X.orbitPullback σ, X.orbitPullback_isSubordinate hσ hUs,
    X.exists_isSaturated_nhds_finite_orbitPullback σ, X.orbitPullback_src σ⟩

end Theorem73

/-! ### The neighbourhoods `V(x) ⊆ W(x)` of the proof of Theorem 7.4 -/

section Neighbourhoods

variable {X}

/-- `|Φ(g)(y)| = |y|` for `y ∈ U(x)`. -/
private theorem π_Φ_eq {x : Obj} (R : X.NaturalRep x) (g : X.Isotropy x) {y : Obj}
    (hy : y ∈ R.U) : X.π (R.Φ g y) = X.π y := by
  rw [← R.tgt_Γ g y hy, ← X.π_src_eq_π_tgt, R.src_Γ g y hy]

variable (X) in
/-- **Properties (1)–(3) of the proof of Theorem 7.4**: for every open `W ∋ x` there are a natural
representation `R` of `G_x` on `W(x) = R.U ⊆ W` and an open `V(x) ∋ x`, invariant under the natural
action, with `cl V(x) ⊆ W(x)` and `t : s⁻¹(cl V(x)) → X` proper.  ((3) is `W ⊆ U_λ`.) -/
theorem exists_invariant_nhds_of_isOpen (x : Obj) {W : Set Obj} (hW : IsOpen W) (hx : x ∈ W) :
    ∃ (R : X.NaturalRep x) (V : Set Obj), IsOpen V ∧ x ∈ V ∧ (∀ g, MapsTo (R.Φ g) V V) ∧
      closure V ⊆ R.U ∧ R.U ⊆ W ∧ X.IsProperSubset (closure V) := by
  obtain ⟨V₀, hxV₀, hV₀⟩ := X.exists_hasPropernessProperty x
  obtain ⟨R, hRU⟩ := theorem_7_1 X x (hW.inter hV₀.1) ⟨hx, hxV₀⟩
  obtain ⟨t, ht, htc, htU⟩ := exists_mem_nhds_isClosed_subset (R.isOpen_U.mem_nhds R.mem_U)
  -- `V(x) = ⋂_g Φ(g)⁻¹(int t)`
  let V := ⋂ g, R.U ∩ R.Φ g ⁻¹' interior t
  have hVo : IsOpen V := isOpen_iInter_of_finite fun g =>
    (R.continuousOn_Φ g).isOpen_inter_preimage R.isOpen_U isOpen_interior
  have hxV : x ∈ V := mem_iInter.2 fun g =>
    ⟨R.mem_U, by rw [mem_preimage, R.Φ_self]; exact mem_interior_iff_mem_nhds.2 ht⟩
  have hVU : V ⊆ R.U := fun y hy => (mem_iInter.1 hy 1).1
  have hVt : V ⊆ t := fun y hy => by
    have h1 := (mem_iInter.1 hy 1).2
    rw [mem_preimage, R.Φ_one y (hVU hy)] at h1
    exact interior_subset h1
  have hVinv : ∀ g, MapsTo (R.Φ g) V V := fun g y hy => mem_iInter.2 fun h =>
    ⟨R.mapsTo_Φ g (hVU hy), by
      rw [mem_preimage, ← R.Φ_mul h g y (hVU hy)]
      exact (mem_iInter.1 hy (h * g)).2⟩
  refine ⟨R, V, hVo, hxV, hVinv, (closure_minimal hVt htc).trans htU, fun y hy => (hRU hy).1, ?_⟩
  exact hV₀.isProperSubset.of_subset (closure_mono fun y hy => (hRU (hVU hy)).2) isClosed_closure

/-- **Property (4) of the proof of Theorem 7.4 follows from (1)**: a point of `W(x) = R.U`
isomorphic to a point of an invariant `V ⊆ W(x)` lies in `V` (the morphisms between points of
`W(x)` are the `Γ(g, ·)`, Theorem 7.1 (3)). -/
theorem mem_of_π_mem_image_of_invariant {x : Obj} (R : X.NaturalRep x) {V : Set Obj}
    (hVU : V ⊆ R.U) (hinv : ∀ g, MapsTo (R.Φ g) V V) {y : Obj} (hy : y ∈ R.U)
    (hyV : X.π y ∈ X.π '' V) : y ∈ V := by
  obtain ⟨z, hz, hzy⟩ := hyV
  obtain ⟨g, hg⟩ := (R.π_eq_π_iff_exists_smul (y := ⟨z, hVU hz⟩) (z := ⟨y, hy⟩)).1 hzy
  have hg' : R.Φ g z = y := congrArg Subtype.val hg
  rw [← hg']
  exact hinv g hz

/-- **Property (4)**, as written: `(π⁻¹(|V(x)|) ∖ V(x)) ∩ W(x) = ∅`. -/
theorem saturation_diff_inter_eq_empty {x : Obj} (R : X.NaturalRep x) {V : Set Obj}
    (hVU : V ⊆ R.U) (hinv : ∀ g, MapsTo (R.Φ g) V V) : (X.saturation V \ V) ∩ R.U = ∅ :=
  eq_empty_of_forall_notMem fun _ hy =>
    hy.1.2 (mem_of_π_mem_image_of_invariant R hVU hinv hy.2 hy.1.1)

end Neighbourhoods

/-! ### The extension of an invariant function on `W(x)` to the saturation -/

section Extension

variable {X}

open scoped Classical in
/-- **The extension to the saturation** (proof of Theorem 7.4): for `f` invariant under the
natural action on `W(x) = R.U`, `F(|y|) = f(y)` for `y ∈ W(x)` (`orbitExtension_π`), and `F = 0`
off `|W(x)|`. -/
def orbitExtension {x : Obj} (R : X.NaturalRep x) (f : Obj → ℝ) (q : X.OrbitSpace) : ℝ :=
  if h : ∃ z ∈ R.U, X.π z = q then f h.choose else 0

/-- `F(|y|) = f(y)` for `y ∈ W(x)`: well defined since points of `W(x)` in one orbit differ by
the natural action. -/
theorem orbitExtension_π {x : Obj} (R : X.NaturalRep x) {f : Obj → ℝ}
    (hf : ∀ g, ∀ y ∈ R.U, f (R.Φ g y) = f y) {y : Obj} (hy : y ∈ R.U) :
    X.orbitExtension R f (X.π y) = f y := by
  have h : ∃ z ∈ R.U, X.π z = X.π y := ⟨y, hy, rfl⟩
  rw [orbitExtension, dif_pos h]
  obtain ⟨hz, hzy⟩ := h.choose_spec
  obtain ⟨g, hg⟩ := (R.π_eq_π_iff_exists_smul (y := ⟨_, hz⟩) (z := ⟨y, hy⟩)).1 hzy
  have hg' : R.Φ g h.choose = y := congrArg Subtype.val hg
  exact (hf g _ hz).symm.trans (congrArg f hg')

theorem orbitExtension_nonneg {x : Obj} (R : X.NaturalRep x) {f : Obj → ℝ} (hf : ∀ y, 0 ≤ f y)
    (q : X.OrbitSpace) : 0 ≤ X.orbitExtension R f q := by
  rw [orbitExtension]
  split_ifs
  · exact hf _
  · exact le_rfl

theorem support_orbitExtension_subset {x : Obj} (R : X.NaturalRep x) (f : Obj → ℝ) :
    support (X.orbitExtension R f) ⊆ X.π '' (R.U ∩ support f) := by
  intro q hq
  rw [mem_support, orbitExtension] at hq
  split_ifs at hq with h
  · exact ⟨h.choose, ⟨h.choose_spec.1, hq⟩, h.choose_spec.2⟩
  · exact absurd rfl hq

/-- **The extension is sc-smooth** (proof of Theorem 7.4) if `f` is sc-smooth, invariant on `W(x)`,
supported in `W(x)` and `supp f` is proper: off the saturation of `supp f`, closed by properness
(Proposition 7.14 (1)), `F ∘ π = 0`; near `y ≅ z ∈ supp f`, `F ∘ π = f ∘ s ∘ (t|U(φ))⁻¹`. -/
theorem isScSmoothMap_orbitExtension {x : Obj} (R : X.NaturalRep x) {f : Obj → ℝ}
    (hf : X.PObj.IsScSmoothMap realPolyfold f) (hinv : ∀ g, ∀ y ∈ R.U, f (R.Φ g y) = f y)
    (hsupp : tsupport f ⊆ R.U) (hprop : X.IsProperSubset (tsupport f)) :
    X.PObj.IsScSmoothMap realPolyfold (X.orbitExtension R f ∘ X.π) := by
  refine isScSmoothMap_real_of_isScSmoothOn_nhds fun y => ?_
  by_cases hy : y ∈ X.saturation (tsupport f)
  · -- `φ : z → y`, `z ∈ supp f`, and a sheet `t : W₂ → V₂` through `φ`
    obtain ⟨z, hz, hzy⟩ := hy
    obtain ⟨φ, hφs, hφt⟩ := (X.π_eq_π_iff).1 hzy
    obtain ⟨W₂, V₂, τ, hφW, hd⟩ := X.isLocalScDiffeo_tgt φ
    have hcont : ContinuousOn (X.src ∘ τ) V₂ :=
      X.continuous_src.comp_continuousOn hd.isScSmoothOn_inv.continuousOn
    have hNo : IsOpen (V₂ ∩ (X.src ∘ τ) ⁻¹' R.U) :=
      hcont.isOpen_inter_preimage hd.isScSmoothOn_inv.isOpen R.isOpen_U
    refine ⟨V₂ ∩ (X.src ∘ τ) ⁻¹' R.U, ⟨?_, ?_⟩, ?_⟩
    · rw [← hφt]
      exact hd.mapsTo hφW
    · change X.src (τ y) ∈ R.U
      rw [← hφt, hd.left_inv φ hφW, hφs]
      exact hsupp hz
    · refine (MPolyfold.IsScSmoothOn.comp (hf.comp X.isScSmoothMap_src)
        (hd.isScSmoothOn_inv.mono hNo inter_subset_left) (mapsTo_univ _ _)).congr
          fun y' hy' => ?_
      have hy'' : X.src (τ y') ∈ R.U := hy'.2
      simp only [Function.comp_apply]
      rw [← X.orbitExtension_π R hinv hy'', X.π_src_eq_π_tgt, hd.right_inv y' hy'.1]
  · -- off the closed saturation of `supp f`, `F ∘ π = 0`
    have hcl := X.isClosed_saturation_of_isProperSubset hprop
    refine ⟨(X.saturation (tsupport f))ᶜ, hy, ((isScSmoothMap_real_const (PX := X.PObj) 0).mono
      hcl.isOpen_compl (subset_univ _)).congr fun y' hy' => ?_⟩
    have h0 : X.orbitExtension R f (X.π y') = 0 := by
      by_contra hne
      obtain ⟨w, hw, hwy⟩ := X.support_orbitExtension_subset R f hne
      exact hy' ⟨w, subset_tsupport f hw.2, hwy⟩
    exact h0.symm

end Extension

/-! ### Lemma 7.10 -/

section Lemma710

variable {X}

/-- **Lemma 7.10**: let `X` admit sc-smooth partitions of unity, `V(x) = R.U` carry the natural
`G_x`-action, and `U(x)` be open and invariant with `cl U(x) ⊆ V(x)`.  A continuous
`β : X → [0, 1]` supported in `U(x)` and invariant under `G_x` on `V(x)` lies below an sc-smooth
`f : X → [0, ∞)` supported in `cl U(x) ⊆ V(x)` and invariant under `G_x` on `V(x)`.  (The text's
"`U(x)` a neighbourhood of `x`" is omitted; the paracompactness of `|X|` and the continuity of `β`
are kept but not used; the support bound `cl U(x)` is the proof's.) -/
theorem lemma_7_10 (_hpara : X.HasParacompactOrbitSpace) (hpu : X.PObj.AdmitsScPartitionsOfUnity)
    {x : Obj} (R : X.NaturalRep x) {U : Set Obj} (hUo : IsOpen U) (hUcl : closure U ⊆ R.U)
    (hUinv : ∀ g, MapsTo (R.Φ g) U U) {β : Obj → ℝ} (_hβ : Continuous β)
    (hβ01 : ∀ y, β y ∈ Icc (0 : ℝ) 1) (hβU : tsupport β ⊆ U)
    (hβinv : ∀ g, ∀ y ∈ R.U, β (R.Φ g y) = β y) :
    ∃ f : Obj → ℝ, X.PObj.IsScSmoothMap realPolyfold f ∧ (∀ y, 0 ≤ f y) ∧
      tsupport f ⊆ closure U ∧ tsupport f ⊆ R.U ∧ (∀ g, ∀ y ∈ R.U, f (R.Φ g y) = f y) ∧
      ∀ y, β y ≤ f y := by
  classical
  -- `γ ≥ β`, sc-smooth and supported in `U(x)`: the function attached to `U(x)` of an sc-smooth
  -- partition of unity of `X` subordinate to `{U(x), X ∖ supp β}`
  obtain ⟨γ, hγ, hγ0, hγU, hβγ⟩ : ∃ γ : Obj → ℝ, X.PObj.IsScSmoothMap realPolyfold γ ∧
      (∀ y, 0 ≤ γ y) ∧ tsupport γ ⊆ U ∧ ∀ y, β y ≤ γ y := by
    let C : ULift.{u} Bool → Set Obj := fun i => if i.down then U else (tsupport β)ᶜ
    have hCo : ∀ i, IsOpen (C i) := by
      rintro ⟨_ | _⟩
      · exact (isClosed_tsupport β).isOpen_compl
      · exact hUo
    have hCcov : ⋃ i, C i = univ := by
      refine eq_univ_of_forall fun y => mem_iUnion.2 ?_
      by_cases hy : y ∈ tsupport β
      · exact ⟨⟨true⟩, hβU hy⟩
      · exact ⟨⟨false⟩, hy⟩
    obtain ⟨ρ, hρsub, hρsc⟩ := hpu _ C hCo hCcov
    refine ⟨ρ ⟨true⟩, hρsc _, fun y => ρ.nonneg _ y, hρsub ⟨true⟩, fun y => ?_⟩
    by_cases hy : y ∈ tsupport β
    · have h0 : ρ ⟨false⟩ y = 0 := image_eq_zero_of_notMem_tsupport fun h => hρsub ⟨false⟩ h hy
      have h1 : ∑ᶠ i, ρ i y = ρ ⟨true⟩ y := finsum_eq_single (fun i => ρ i y) ⟨true⟩ fun i hi => by
        obtain ⟨_ | _⟩ := i
        · exact h0
        · exact absurd rfl hi
      rw [← h1, ρ.sum_eq_one (mem_univ y)]
      exact (hβ01 y).2
    · rw [image_eq_zero_of_notMem_tsupport hy]
      exact ρ.nonneg _ y
  -- the average `f = |G_x|⁻¹ Σ_g γ ∘ Φ(g)` on `V(x)`, `0` off `V(x)`
  have := Fintype.ofFinite (X.Isotropy x)
  let γg : X.Isotropy x → Obj → ℝ := fun g => R.U.indicator fun y => γ (R.Φ g y)
  have hγg_eq : ∀ g, ∀ y ∈ R.U, γg g y = γ (R.Φ g y) := fun g y hy => indicator_of_mem hy _
  have hγg_zero : ∀ g y, y ∉ R.U → γg g y = 0 := fun g y hy => indicator_of_notMem hy _
  have hγg_nonneg : ∀ g y, 0 ≤ γg g y := fun g y => indicator_nonneg (fun z _ => hγ0 _) y
  have hγg_supp : ∀ g, support (γg g) ⊆ U := by
    intro g y hy
    by_cases hyR : y ∈ R.U
    · rw [mem_support, hγg_eq g y hyR] at hy
      have h0 : R.Φ g y ∈ support γ := hy
      have h1 := hUinv g⁻¹ (hγU (subset_tsupport γ h0))
      rwa [R.Φ_inv_Φ g hyR] at h1
    · exact absurd (hγg_zero g y hyR) hy
  have hγg_sc : ∀ g, X.PObj.IsScSmoothMap realPolyfold (γg g) := fun g =>
    isScSmoothMap_real_of_tsupport_subset
      ((MPolyfold.IsScSmoothOn.comp hγ (R.isScDiffeoOn_Φ g).isScSmoothOn
        (mapsTo_univ _ _)).congr fun y hy => (hγg_eq g y hy).symm)
      ((closure_mono (hγg_supp g)).trans hUcl)
  have hcard : (0 : ℝ) < Fintype.card (X.Isotropy x) := Nat.cast_pos.2 Fintype.card_pos
  have hc0 : (0 : ℝ) ≤ (Fintype.card (X.Isotropy x) : ℝ)⁻¹ := inv_nonneg.2 hcard.le
  have hf0 : ∀ y, 0 ≤ (Fintype.card (X.Isotropy x) : ℝ)⁻¹ * ∑ g, γg g y := fun y =>
    mul_nonneg hc0 (Finset.sum_nonneg fun g _ => hγg_nonneg g y)
  have hfsupp : support (fun y => (Fintype.card (X.Isotropy x) : ℝ)⁻¹ * ∑ g, γg g y) ⊆ U := by
    refine support_subset_iff'.2 fun y hy => ?_
    rw [Finset.sum_eq_zero fun g _ => notMem_support.1 fun h => hy (hγg_supp g h), mul_zero]
  refine ⟨fun y => (Fintype.card (X.Isotropy x) : ℝ)⁻¹ * ∑ g, γg g y,
    (isScSmoothMap_real_const _).real_mul (isScSmoothMap_real_finsetSum Finset.univ
      fun g _ => hγg_sc g), hf0, closure_mono hfsupp, (closure_mono hfsupp).trans hUcl,
    fun h y hy => ?_, fun y => ?_⟩
  · -- invariance: reindex `g ↦ g h`
    have hΦy := R.mapsTo_Φ h hy
    have hsum : ∑ g, γg g (R.Φ h y) = ∑ g, γg g y := by
      calc ∑ g, γg g (R.Φ h y) = ∑ g, γg (g * h) y := Finset.sum_congr rfl fun g _ => by
            rw [hγg_eq g _ hΦy, hγg_eq (g * h) y hy, R.Φ_mul g h y hy]
        _ = ∑ g, γg g y := Equiv.sum_comp (Equiv.mulRight h) fun g => γg g y
    simp only [hsum]
  · -- `β ≤ f`, by the invariance of `β`
    by_cases hy : y ∈ R.U
    · have hle : ∑ _g : X.Isotropy x, β y ≤ ∑ g, γg g y := Finset.sum_le_sum fun g _ => by
        rw [hγg_eq g y hy, ← hβinv g y hy]
        exact hβγ _
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hle
      calc β y = (Fintype.card (X.Isotropy x) : ℝ)⁻¹ * (Fintype.card (X.Isotropy x) * β y) := by
            rw [← mul_assoc, inv_mul_cancel₀ hcard.ne', one_mul]
        _ ≤ (Fintype.card (X.Isotropy x) : ℝ)⁻¹ * ∑ g, γg g y :=
            mul_le_mul_of_nonneg_left hle hc0
    · have hβ0 : β y = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => hy (hUcl (subset_closure (hβU h)))
      rw [hβ0]
      exact hf0 y

end Lemma710

/-! ### The invariant sc-smooth Urysohn lemma and Theorem 7.4 -/

section Theorem74

/-- **The invariant sc-smooth Urysohn lemma** (the construction of the proof of Theorem 7.4): if
`|X|` is paracompact and `X` admits sc-smooth partitions of unity, then for disjoint closed
`s, t ⊆ |X|` there is a continuous `F : |X| → [0, 1]` with `F ∘ π` sc-smooth, `F = 0` on `s` and
`F = 1` on `t`.  (The points `x ∈ π⁻¹(t)` with `V(x) ⊆ W(x) ⊆ π⁻¹(|X| ∖ s)`, a locally finite
refinement `V'_x` of `(|V(x)|)`, a subordinate bump covering `(β_x)` of `t`, Lemma 7.10 for the
cut-offs `(β_x ∘ π)|V(x)` on `U''_x = V(x) ∩ π⁻¹(V'_x)`, the extensions `h_x` to the saturations,
`G = Σ h_x` and `F = τ ∘ G`.) -/
theorem exists_isScSmoothMap_orbit_urysohn (hpara : X.HasParacompactOrbitSpace)
    (hpu : X.PObj.AdmitsScPartitionsOfUnity) {s t : Set X.OrbitSpace} (hs : IsClosed s)
    (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ F : C(X.OrbitSpace, ℝ), X.PObj.IsScSmoothMap realPolyfold (F ∘ X.π) ∧ EqOn F 0 s ∧
      EqOn F 1 t ∧ ∀ q, F q ∈ Icc (0 : ℝ) 1 := by
  have : ParacompactSpace X.OrbitSpace := hpara
  -- (1)–(3) at the points of `π⁻¹(t)`, with `W(x) ⊆ π⁻¹(|X| ∖ s)`
  let T := {x : Obj // X.π x ∈ t}
  have hW : ∀ x : T, x.1 ∈ X.π ⁻¹' sᶜ := fun x => disjoint_right.1 hst x.2
  choose R V hVo hxV hVinv hVcl hRW hVprop using fun x : T =>
    X.exists_invariant_nhds_of_isOpen x.1 (hs.isOpen_compl.preimage X.continuous_π) (hW x)
  have hVR : ∀ x, V x ⊆ (R x).U := fun x => subset_closure.trans (hVcl x)
  -- a locally finite refinement `(V'_x)` of `(|V(x)|)` and a subordinate bump covering of `t`
  have hcov : t ⊆ ⋃ x : T, X.π '' V x := fun q hq => by
    obtain ⟨y, rfl⟩ := X.surjective_π q
    exact mem_iUnion.2 ⟨⟨y, hq⟩, mem_image_of_mem _ (hxV ⟨y, hq⟩)⟩
  obtain ⟨v, hvo, htv, hvlf, hvV⟩ := precise_refinement_set ht (fun x : T => X.π '' V x)
    (fun x => X.proposition_7_1 _ (hVo x)) hcov
  obtain ⟨b, hb⟩ := BumpCovering.exists_isSubordinate ht v hvo htv
  -- the cut-offs `c_x = (β_x ∘ π)|V(x)`, supported in `U''_x = V(x) ∩ π⁻¹(V'_x)` by (4)
  let U'' : T → Set Obj := fun x => V x ∩ X.π ⁻¹' v x
  let c : T → Obj → ℝ := fun x => (V x).indicator fun y => b x (X.π y)
  have hc_eq : ∀ x, ∀ y ∈ V x, c x y = b x (X.π y) := fun x y hy => indicator_of_mem hy _
  have hc_zero : ∀ x y, y ∉ V x → c x y = 0 := fun x y hy => indicator_of_notMem hy _
  have hc_tsupp : ∀ x, tsupport (c x) ⊆ U'' x := by
    intro x y hy
    have h1 : tsupport (c x) ⊆ closure (V x) ∩ X.π ⁻¹' tsupport (b x) := by
      refine closure_minimal (fun z hz => ?_)
        (isClosed_closure.inter ((isClosed_tsupport _).preimage X.continuous_π))
      have hzV : z ∈ V x := by
        by_contra h
        exact hz (hc_zero x z h)
      rw [mem_support, hc_eq x z hzV] at hz
      have hz' : X.π z ∈ support (b x) := hz
      exact ⟨subset_closure hzV, subset_tsupport _ hz'⟩
    obtain ⟨hyV, hyb⟩ := h1 hy
    have hyv : X.π y ∈ v x := hb x hyb
    exact ⟨mem_of_π_mem_image_of_invariant (R x) (hVR x) (hVinv x) (hVcl x hyV) (hvV x hyv),
      hyv⟩
  have hc_cont : ∀ x, Continuous (c x) := fun x =>
    ContinuousOn.continuous_of_tsupport_subset
      (((b x).continuous.comp X.continuous_π).continuousOn.congr fun y hy => hc_eq x y hy)
      (hVo x) ((hc_tsupp x).trans inter_subset_left)
  have hc01 : ∀ x y, c x y ∈ Icc (0 : ℝ) 1 := by
    intro x y
    by_cases hy : y ∈ V x
    · rw [hc_eq x y hy]
      exact ⟨b.nonneg x _, b.le_one x _⟩
    · rw [hc_zero x y hy]
      exact ⟨le_rfl, zero_le_one⟩
  have hc_inv : ∀ x g, ∀ y ∈ (R x).U, c x ((R x).Φ g y) = c x y := by
    intro x g y hy
    by_cases hyV : y ∈ V x
    · rw [hc_eq x _ (hVinv x g hyV), hc_eq x y hyV, π_Φ_eq (R x) g hy]
    · have hΦ : (R x).Φ g y ∉ V x := fun h => hyV (by
        have h' := hVinv x g⁻¹ h
        rwa [(R x).Φ_inv_Φ g hy] at h')
      rw [hc_zero x _ hΦ, hc_zero x y hyV]
  -- Lemma 7.10 with `(U, V) = (U''_x, W(x))`
  have hU''o : ∀ x, IsOpen (U'' x) := fun x => (hVo x).inter ((hvo x).preimage X.continuous_π)
  have hU''cl : ∀ x, closure (U'' x) ⊆ (R x).U := fun x =>
    (closure_mono inter_subset_left).trans (hVcl x)
  have hU''inv : ∀ x g, MapsTo ((R x).Φ g) (U'' x) (U'' x) := fun x g y hy =>
    ⟨hVinv x g hy.1, by
      change X.π ((R x).Φ g y) ∈ v x
      rw [π_Φ_eq (R x) g (hVR x hy.1)]
      exact hy.2⟩
  choose f hfsc hf0 hfcl hfR hfinv hcf using fun x : T =>
    lemma_7_10 hpara hpu (R x) (hU''o x) (hU''cl x) (hU''inv x) (hc_cont x) (hc01 x) (hc_tsupp x)
      (hc_inv x)
  -- the extensions `h_x = F_x ∘ π` to the saturations, locally finite
  let F : T → X.OrbitSpace → ℝ := fun x => X.orbitExtension (R x) (f x)
  have hFsc : ∀ x, X.PObj.IsScSmoothMap realPolyfold (F x ∘ X.π) := fun x =>
    isScSmoothMap_orbitExtension (R x) (hfsc x) (hfinv x) (hfR x)
      ((hVprop x).of_subset ((hfcl x).trans (closure_mono inter_subset_left))
        (isClosed_tsupport _))
  have hFsupp : ∀ x, support (F x ∘ X.π) ⊆ X.π ⁻¹' closure (v x) := by
    intro x y hy
    have hy' : X.π y ∈ support (X.orbitExtension (R x) (f x)) := hy
    obtain ⟨z, ⟨-, hz⟩, hzy⟩ := support_orbitExtension_subset (R x) (f x) hy'
    have hz' : z ∈ closure (U'' x) := hfcl x (subset_tsupport _ hz)
    have hzv : X.π z ∈ closure (v x) :=
      X.continuous_π.closure_preimage_subset (v x) (closure_mono inter_subset_right hz')
    rw [mem_preimage, ← hzy]
    exact hzv
  have hFlf : LocallyFinite fun x => support (F x ∘ X.π) :=
    (hvlf.closure.preimage_continuous X.continuous_π).subset hFsupp
  have hF0 : ∀ x q, 0 ≤ F x q := fun x q => orbitExtension_nonneg (R x) (hf0 x) q
  -- `G = Σ_x F_x`: `G ∘ π` is sc-smooth, `G = 0` on `s`, `G ≥ 1` on `t`
  let G : X.OrbitSpace → ℝ := fun q => ∑ᶠ x, F x q
  have hGsc : X.PObj.IsScSmoothMap realPolyfold (G ∘ X.π) := isScSmoothMap_real_finsum hFsc hFlf
  have hG0 : ∀ q ∈ s, G q = 0 := by
    intro q hq
    refine finsum_eq_zero_of_forall_eq_zero fun x => ?_
    by_contra hne
    have hne' : q ∈ support (X.orbitExtension (R x) (f x)) := hne
    obtain ⟨z, ⟨hzR, -⟩, hzq⟩ := support_orbitExtension_subset (R x) (f x) hne'
    exact hRW x hzR (by rw [hzq]; exact hq)
  have hG1 : ∀ q ∈ t, 1 ≤ G q := by
    intro q hq
    obtain ⟨i₀, h1⟩ : ∃ i₀, b i₀ q = 1 := ⟨b.ind q hq, b.ind_apply q hq⟩
    have hqs : q ∈ support (b i₀) := by
      rw [mem_support, h1]
      exact one_ne_zero
    obtain ⟨z, hzV, rfl⟩ := hvV _ (hb _ (subset_tsupport _ hqs))
    have h3 : 1 ≤ F i₀ (X.π z) := by
      change 1 ≤ X.orbitExtension (R i₀) (f i₀) (X.π z)
      rw [orbitExtension_π (R _) (hfinv _) (hVR _ hzV)]
      calc (1 : ℝ) = b i₀ (X.π z) := h1.symm
        _ = c i₀ z := (hc_eq _ z hzV).symm
        _ ≤ f i₀ z := hcf _ z
    exact h3.trans (single_le_finsum i₀ (hFlf.point_finite z) fun x => hF0 x (X.π z))
  -- `F = τ ∘ G`
  have hσ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff (n := ⊤)
  have hFbar : X.PObj.IsScSmoothMap realPolyfold ((Real.smoothTransition ∘ G) ∘ X.π) :=
    hGsc.comp_contDiff hσ
  have hcont : Continuous (Real.smoothTransition ∘ G) :=
    X.proposition_7_1_isOpenQuotientMap.isQuotientMap.continuous_iff.2
      (continuousOn_univ.1 hFbar.continuousOn)
  refine ⟨⟨Real.smoothTransition ∘ G, hcont⟩, hFbar, fun q hq => ?_, fun q hq => ?_,
    fun q => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩⟩
  · change Real.smoothTransition (G q) = 0
    rw [hG0 q hq]
    exact Real.smoothTransition.zero_of_nonpos le_rfl
  · exact Real.smoothTransition.one_of_one_le (hG1 q hq)

/-- **Theorem 7.4**: if `|X|` is paracompact and the object M-polyfold `X` admits sc-smooth
partitions of unity, then for every cover of `X` by saturated open sets there is a subordinate
sc-smooth partition of unity of the ep-groupoid (Definition 7.16). -/
theorem theorem_7_4 (hpara : X.HasParacompactOrbitSpace)
    (hpu : X.PObj.AdmitsScPartitionsOfUnity) : X.HasScPartitionsOfUnity := by
  classical
  intro ι U hUo hUs hUcov
  have : ParacompactSpace X.OrbitSpace := hpara
  -- a bump covering `(b_λ)` of `|X|` subordinate to `(π(U_λ))` with `b_λ ∘ π` sc-smooth
  obtain ⟨b, hbp, hb⟩ := BumpCovering.exists_isSubordinate_of_prop
    (fun g : X.OrbitSpace → ℝ => X.PObj.IsScSmoothMap realPolyfold (g ∘ X.π))
    (fun s t hs ht hst => X.exists_isScSmoothMap_orbit_urysohn hpara hpu hs ht hst)
    isClosed_univ (fun i => X.π '' U i) (fun i => X.proposition_7_1 _ (hUo i))
    (X.iUnion_image_π_eq_univ hUcov).symm.subset
  have hbp' : ∀ j, X.PObj.IsScSmoothMap realPolyfold (b j ∘ X.π) := hbp
  -- `β_λ = ρ_λ ∘ π`, `ρ_λ = b_λ ∏_{μ < λ} (1 − b_μ)`
  refine ⟨X.orbitPullback b.toPartitionOfUnity,
    X.orbitPullback_isSubordinate hb.toPartitionOfUnity hUs, fun i => ?_,
    X.exists_isSaturated_nhds_finite_orbitPullback _, X.orbitPullback_src _⟩
  refine isScSmoothMap_real_of_eventuallyEq fun y => ?_
  obtain ⟨T, hT⟩ := b.exists_finset_toPartitionOfUnity_eventuallyEq i (X.π y)
  refine ⟨fun z => b i (X.π z) * ∏ j ∈ T with WellOrderingRel j i, (1 - b j (X.π z)),
    (hbp' i).real_mul (isScSmoothMap_real_finsetProd _ fun j _ =>
      (isScSmoothMap_real_const 1).real_sub (hbp' j)), ?_⟩
  filter_upwards [hT.comp_tendsto (X.continuous_π.tendsto y)] with z hz
  rw [orbitPullback_apply]
  simp only [Function.comp_apply] at hz
  rw [hz]
  simp [ContinuousMap.coe_prod, Finset.prod_apply]

/-- **Theorem 7.6** (p. 255) is Theorem 7.4, restated in Appendix 7.5.2 with its proof. -/
theorem theorem_7_6 (hpara : X.HasParacompactOrbitSpace)
    (hpu : X.PObj.AdmitsScPartitionsOfUnity) : X.HasScPartitionsOfUnity :=
  X.theorem_7_4 hpara hpu

/-- **Corollary 7.3**: if `|X|` is paracompact and the object M-polyfold has an atlas (one chart
around every point) whose local models have Hilbert spaces `E₀` (`‖v‖² = b(v, v)`), then every
cover of `X` by saturated open sets has a subordinate sc-smooth partition of unity of the
ep-groupoid — **under the explicit hypothesis that Theorem 5.14 [5.43] holds** for these `E₀`
(`GodefroyTroyanskiWhitfieldZizlerStatement`, cited and not formalized, as in Part I). -/
theorem corollary_7_3 (hpara : X.HasParacompactOrbitSpace)
    (h : ∀ x, ∃ φ : MChart Obj, X.PObj.IsChart φ ∧ x ∈ φ.source ∧
      (∃ b : φ.model.E 0 →L[ℝ] φ.model.E 0 →L[ℝ] ℝ, ∀ v, ‖v‖ ^ 2 = b v v) ∧
      GodefroyTroyanskiWhitfieldZizlerStatement (φ.model.E 0) ⊤) :
    X.HasScPartitionsOfUnity :=
  X.theorem_7_4 hpara (MPolyfold.admitsScPartitionsOfUnity_of_hilbert h)

end Theorem74

/-! ### Satisfiability of the hypotheses (PLAN II.5, 3) -/

section Satisfiability

/-- **The hypotheses of Theorems 7.4 and 7.6 (and Lemma 7.10's) are satisfiable**: the trivial
ep-groupoid on `ℝⁿ` has paracompact orbit space and its object M-polyfold `ℝⁿ` admits sc-smooth
partitions of unity. -/
theorem theorem_7_4_hypotheses_rn (n : ℕ) :
    (trivial (rnPolyfold n)).HasParacompactOrbitSpace ∧
      (trivial (rnPolyfold n)).PObj.AdmitsScPartitionsOfUnity :=
  ⟨hasParacompactOrbitSpace_trivial _, rnPolyfold_admitsScPartitionsOfUnity n⟩

/-- Theorem 7.4 applies to the trivial ep-groupoid on `ℝⁿ`. -/
theorem hasScPartitionsOfUnity_trivial_rn_of_theorem_7_4 (n : ℕ) :
    (trivial (rnPolyfold n)).HasScPartitionsOfUnity :=
  (trivial (rnPolyfold n)).theorem_7_4 (theorem_7_4_hypotheses_rn n).1
    (theorem_7_4_hypotheses_rn n).2

/-- **The hypotheses of Corollary 7.3 are satisfiable**: the trivial ep-groupoid on `ℝ¹`, with the
chart `id` (a Hilbert `E₀`) and Theorem 5.14 [5.43] for `ℝ¹` (finite-dimensional). -/
theorem corollary_7_3_hypotheses_rn :
    (trivial (rnPolyfold 1)).HasParacompactOrbitSpace ∧
      ∀ x, ∃ φ : MChart (Fin 1 → ℝ), (trivial (rnPolyfold 1)).PObj.IsChart φ ∧ x ∈ φ.source ∧
        (∃ b : φ.model.E 0 →L[ℝ] φ.model.E 0 →L[ℝ] ℝ, ∀ v, ‖v‖ ^ 2 = b v v) ∧
        GodefroyTroyanskiWhitfieldZizlerStatement (φ.model.E 0) ⊤ :=
  ⟨hasParacompactOrbitSpace_trivial _, rnPolyfold_one_hilbert_hypothesis⟩

end Satisfiability

end EpGroupoid

end Polyfold
