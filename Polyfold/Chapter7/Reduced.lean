import Polyfold.Chapter7.Effective

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II, §7.2,
pp. 241–244: **Definition 7.2.7 (2017: 7.12)** made precise (p. 241: the equivalence relation `∼`, the quotient
`𝐗^R` and its topology, the structure maps on `𝐗^R`), **Proposition 7.2.10 (2017: 7.9)** (p. 313 (2017 p. 242), proof
pp. 242–243), the reduced ep-groupoid `X_R` (p. 243), **Proposition 7.10** (p. 244), the isotropy
`G_x/T_x` of `X_R` and **Definition 7.2.15 (2017: 7.13)** (p. 319 (2017 p. 244)).  There is no 2014 preprint of Part II;
numbers and pages are the 2017 text's.  Part I items carry their 2017 numbers, with the preprint
number of the Lean name in brackets: Definition 2.3.2 (2017: 2.6) [2.11] (`MChart`), Definition 2.3.3 (2017: 2.7) [2.12]
(`MAtlas`), Definition 2.3.4 (2017: 2.8) [2.13] (`MPolyfold`), Definition 2.3.8 (2017: 2.9) [2.14] (`MPolyfold.IsScSmoothOn`).

# Reduced ep-groupoids

## The text, paraphrased

(Definition 7.2.7 (2017: 7.12)) `𝐗^T = {φ ∈ T_x | x ∈ X}`; `φ ∼ φ'` if (1) `s(φ) = s(φ') = x` and (2)
`φ = φ' ∘ g` for some `g ∈ T_x`; "the subset `𝐗^R` of reduced morphisms" is the set of the classes
`[φ]`.  (Proposition 7.2.10 (2017: 7.9)) `𝐗^R` has a natural M-polyfold structure.  Proof: `𝐗^R` carries the
quotient topology.  For a sheet `s : U(φ₀) → U(s(φ₀))` the map `π' : U(φ₀) → 𝐗^R` is continuous
and injective (`[ψ] = [ψ']` gives `s ψ = s ψ'`).  Its image `U([φ₀])` is open: for `ψ ∼ φ ∈
U(φ₀)`, `φ = ψ ∘ g` with `g ∈ T_{s ψ}`, and `U(s ψ)` with `ker Φ = T_{s ψ}`, the map
`δ(ψ') = ψ' ∘ Γ(g, s ψ')` is continuous with `δ(ψ) = φ`, so it maps some `U'(ψ)` into `U(φ₀)`,
and `Γ(g, s ψ') ∈ T_{s ψ'}` gives `ψ' ∼ δ(ψ')`.  The same argument shows that `Ψ_{φ₀} : U(φ₀) →
U([φ₀])` is open, hence a homeomorphism.  (p. 243) For overlapping `U([φ₀])`, `U([ψ₀])` the
transition `Ψ_{ψ₀}⁻¹ ∘ Ψ_{φ₀}` is, near `φ` with `ψ = φ ∘ g`, the sc-smooth `δ(φ') = φ' ∘
Γ(g, s φ')`.  (p. 243) `X_R` has objects `X` and morphisms `𝐗^R`, `s([φ]) = s(φ)`, `t([φ]) =
t(φ)`, both surjective; `s(Ψ_φ(φ')) = s(φ')` and `t(Ψ_φ(φ')) = t(φ')` reduce the smoothness of
the structure maps to that of `X`; "the properness can be proved similarly".  (Proposition 7.10)
`X_R` is an ep-groupoid, and it is effective: `[1_x] = T_x`; for `τ = [g]` with `g ∉ T_x` and an
open `V(τ)`, take `U(x)` with `ker Φ = T_x` so small that `U([g]) ⊆ V(τ)`; then `Φ(g)(a) ≠ a` for
some `a`, and `[Γ(g, a)] ∈ V(τ)` has `s ≠ t`.  The isotropy group of `x` in `X_R` is `G_x/T_x`.
(Definition 7.2.15 (2017: 7.13)) `G_x^eff = G_x/T_x` is the effective isotropy group.

## What is formalized (namespace `Polyfold.EpGroupoid`)

* **`𝐗^T` intrinsically**: `mem_nonEffectivePart_iff`, `nonEffectivePart_eq_interior`
  (`𝐗^T = int{s = t}`), `isOpen_nonEffectivePart`; closure under `u`, `ι`, `m` and conjugation:
  `unit_mem_nonEffectivePart`, `inv_mem_nonEffectivePart`, `comp_mem_nonEffectivePart`,
  `conj_mem_nonEffectivePart`; `val_mem_nonEffectivePart_iff` (`g ∈ T_x ↔ g ∈ 𝐗^T`).
* **Definition 7.2.7 (2017: 7.12), made precise**: `reducedRel_iff` (`φ ∼ φ'` iff `φ = φ' ∘ k`, `k ∈ 𝐗^T`),
  `reducedRel_refl`, `ReducedRel.symm`, `ReducedRel.trans`, `reducedSetoid`,
  `reducedMor_eq_quotient`; the left form `reducedRel_comp_left`, `ReducedRel.exists_comp_left`;
  `ReducedRel.src_eq`, `.tgt_eq`, `.inv`, `.comp_left`, `.comp_right`.  The quotient topology
  (an instance), `reducedπ`, `reducedπ_eq_iff`, `surjective_reducedπ`, `isQuotientMap_reducedπ`,
  `continuous_reducedπ` and **`isOpenMap_reducedπ`**.  The structure maps descend:
  `reducedSrc`, `reducedTgt`, `reducedUnit`, `reducedInv`, `reducedComp` (`reducedSrc_π`, …,
  `reducedComp_π`, continuity), `surjective_reducedSrc`, `surjective_reducedTgt` and the groupoid
  `reducedGroupoidStr`.  **Small sheets**: on every sheet `s : W → V` of `s` the projection is a
  homeomorphism onto an open set: `injOn_reducedπ`, `isOpenEmbedding_domRestrict_reducedπ`, and
  `isOpenEmbedding_domRestrict_reducedπ_image_Γ` for the sheets `Γ(g, U)` of Theorem 7.1.13 (2017: 7.1).
* **Proposition 7.2.10 (2017: 7.9)**: the charts `reducedChart ψ hS hψW` (`Ψ_φ`, for a chart `ψ` of `𝐗` with
  domain in a sheet `s : W → V`), `overlap_reducedChart`, `reducedChart_compatible` (the
  transitions are sc-smooth), `reducedCharts`, `exists_chart_sheet` and the atlas
  `reducedAtlas`, all without hypotheses; under `[T2Space X.ReducedMor]`
  `[ParacompactSpace X.ReducedMor]`: `reducedPolyfold`, `isChart_reducedChart`,
  `isScDiffeoOn_reducedπ` (`π : W → π(W)`, inverse `σ ∘ s`), `isLocalScDiffeo_reducedπ`,
  `isScSmoothMap_reducedπ`, and `proposition_7_2_10`.
* **Proposition 7.10**: `isScDiffeoOn_reducedSrc`, `isScDiffeoOn_reducedTgt`; the conditions of
  Definition 7.1.3 (2017: 7.3): `isLocalScDiffeo_reducedSrc`, `isLocalScDiffeo_reducedTgt`,
  `isScSmoothMap_reducedUnit`, `isScSmoothMap_reducedInv`, `exists_isProperMap_reduced`,
  `isScSmoothCompSheet_reduced`; `reducedEpGroupoid` (`X_R`), `reductionFunctor` (`X → X_R`, an
  `EpFunctor`), `isEffective_reducedEpGroupoid`, and `proposition_7_10_2017`.  **The isotropy**
  (p. 244): `reducedIsotropyHom`, `surjective_reducedIsotropyHom`, `ker_reducedIsotropyHom`
  (`[1_x] = T_x`), `quotientTrivialSubgroupEquiv` (`G_x/T_x ≅ G̃_x`); **Definition 7.2.15 (2017: 7.13)**:
  `effIsotropyEquivReduced` (`EffIsotropy x ≅ G̃_x`).
* **Satisfiability** (PLAN II.5, 7): for effective `X`, `reducedRel_iff_eq_of_isEffective`,
  `reducedHomeomorph` (`𝐗 ≃ₜ 𝐗^R`), `t2Space_reducedMor_of_isEffective`,
  `paracompactSpace_reducedMor_of_isEffective`, `t3Space_reducedMor_of_isEffective`,
  `reductionInv` and `reductionIso` (`X ≅ X_R` in `EP`); for the trivial ep-groupoid of every
  M-polyfold `t2Space_reducedMor_trivial`, `paracompactSpace_reducedMor_trivial`; and
  `paracompactSpace_reducedMor_of_t3` (`𝐗^R` regular, `𝐗` second countable).

## Reading

* **`∼` is an equivalence relation** because `T_x` is a subgroup (`trivialSubgroup`,
  `Effective.lean`).  To avoid dependent types it is used in the form `φ = φ' ∘ k` with `k` in
  `𝐗^T = int{φ | s φ = t φ}` (`mem_trivialSet_iff_eventually`, `Effective.lean`).  Transitivity
  only needs the subgroup; the descent of `ι` and `m` also needs `φ T_x φ⁻¹ = T_y`
  (`isotropyConj_mem_trivialSet`, `Effective.lean`), which the text does not state: it gives the
  left form, `φ ∼ ψ` iff `φ = k ∘ ψ` with `k ∈ T_{t ψ}`.
* **The openness of `U([φ₀])`** is the openness of `π` (`isOpenMap_reducedπ`).  The text's
  `δ(ψ') = ψ' ∘ Γ(g, s(ψ'))` composes on the right with a section of `s`; the text asserts that it
  is continuous, which holds by condition (4) of Definition 7.1.3 (2017: 7.3) applied to inverses.  We use the
  left form instead: `δ(ψ') = Γ(g, t ψ') ∘ ψ'`, sc-smooth by (4) in the sheet form
  (`NaturalRep.isScSmoothOn_comp_Γ_tgt`), with `g ∈ T_{t ψ}` and `ker Φ = T_{t ψ}`
  (`exists_naturalRep_trivialSet_iff`); "`Γ(g, s(ψ'))` belongs to `T_{s(ψ')}`" is
  `NaturalRep.mem_trivialSet_of_val_eq_Γ`.  "`Ψ_{φ₀}` is open" is then the openness of `π`
  restricted to the open `U(φ₀)`.
* **"The charts `Ψ_φ`."**  The text's `Ψ_{φ₀} : U(φ₀) → U([φ₀])` are homeomorphisms from open
  subsets of `𝐗`; composed with charts `ψ` of `𝐗` they give charts in the sense of Definition 2.3.2 (2017: 2.6)
  [2.11]: `reducedChart ψ`, `[φ'] ↦ ψ(σ(s[φ']))` on `π(dom ψ)`, where `σ = (s|W)⁻¹` for a sheet
  `W ⊇ dom ψ`.  The atlas consists of all of them (`reducedCharts`); it is a set, not a
  hypothesis.  "Small" sheets are not needed: on every sheet of `s` the projection is injective.
* **The transitions.**  On the overlap, the text's `δ` equals `σ₂ ∘ s` with `σ₂ = (s|U(ψ₀))⁻¹`:
  an element of `U(ψ₀)` equivalent to `φ'` has the source `s(φ')`.  So the transition is
  `ψ₂ ∘ σ₂ ∘ s ∘ ψ₁⁻¹` (`reducedChart_compatible`), sc-smooth since `σ₂ ∘ s` is; what needs the
  argument of the text is that the overlap `ψ₁(dom ψ₁ ∩ π⁻¹π(dom ψ₂))` is open, i.e. that `π` is
  open.
* **Hausdorff and paracompact** (PLAN P7, II.6, 2).  An M-polyfold is a Hausdorff paracompact
  space (Definition 2.3.4 (2017: 2.8) [2.13]).  The proof of Proposition 7.2.10 (2017: 7.9) gives the charts and the sc-smooth
  transitions but, as we read it, neither property, and `𝐗^R` need not be Hausdorff (the splicing
  example of PLAN II.6, 2, on a dimension-jumping retract: `Examples.exists_not_t2Space_reducedMor`,
  `ReducedNotHausdorff.lean`; the 2021 text assumes `T_R` Hausdorff, and paracompactness is the
  instance `paracompactSpace_reducedMor` of `ReducedCriterion.lean`).  So
  `reducedPolyfold`, and with it `reducedEpGroupoid`, take `[T2Space X.ReducedMor]` and
  `[ParacompactSpace X.ReducedMor]` as hypotheses.  The relation, the topology, the openness of
  `π`, the structure maps, the charts and their compatibility need neither.
* **Proposition 7.10, the conditions of Definition 7.1.3 (2017: 7.3).**  (1): for a sheet `𝐔` of Definition 7.1.4 (2017: 7.4),
  `s, t : π(𝐔) → X` are `s_X ∘ (π|𝐔)⁻¹`, `t_X ∘ (π|𝐔)⁻¹` (the text's `s(Ψ_φ(φ')) = s_X(φ')`).
  (2): `u = π ∘ u_X`, and `ι = π ∘ ι_X ∘ (π|W)⁻¹` on `π(W)`.  (3), "proved similarly": for the same
  `V(x)`, `t ∘ π = t_X` on `s⁻¹(cl V(x))` with `π` a continuous surjection onto
  `s⁻¹(cl V(x)) ⊆ 𝐗^R` (Mathlib's `isProperMap_of_comp_of_surj`).  (4), "reduced by our local
  charts", is proved in the sheet form (`isScSmoothComp_iff_sheet`): for an sc-diffeomorphism
  `s : W' → V'` of `𝐗^R` with inverse `σ'`, `κ = σ₂ ∘ s ∘ σ'` is the inverse of `s` on an open
  set of `𝐗` (a step the text leaves implicit) and `m(σ'(t ψ), ψ) = π(m(κ(t ψ), ψ))` on `π(W₁)`.
  The composition of a non-composable pair of `𝐗^R` is a junk value (`[φ]`), as in `GroupoidStr`.
* **Effectiveness.**  The text's argument (a point `a` with `Φ(g)(a) ≠ a`) is replaced by the
  intrinsic form of `T_x`: if `s = t` near `[g]` in `𝐗^R`, then `s = t` near `g` in `𝐗` (`π` is
  continuous), so `g ∈ T_x` and `[g] = [1_x]`.  "`[1_x] = T_x`" is `ker_reducedIsotropyHom`.
* **The isotropy `G_x/T_x`** (p. 244) is `quotientTrivialSubgroupEquiv`; with `effIsotropyEquiv`
  (`Effective.lean`) Definition 7.2.15 (2017: 7.13)'s `G_x^eff` is the isotropy group of `X_R`.
* **Possible misprints.**  Definition 7.2.7 (2017: 7.12) calls `𝐗^R` "the subset of reduced morphisms"; it is a
  quotient of `𝐗` (the next sentence calls it "the collection of all equivalence classes").  In
  the extracted text of pp. 242–243: "`ψ' = (s|U(ψ))⁻¹(s(ψ))`" for `(s|U(ψ))⁻¹(s(ψ'))`;
  "`U(φ) ⊂ Ψ_{φ₀}(U([φ₀]) ∩ U([ψ₀]))`" for `Ψ_{φ₀}⁻¹(…)`; "such that `T_x` agrees with the
  kernel of the `G_{s(φ)}`-action" for `T_{s(φ)}`; "which show that the source and target maps
  are smoothness of the natural maps can be reduced …" (a garbled sentence); "For and object"
  (Definition 7.2.15 (2017: 7.13)).
* **Hypotheses** (PLAN II.5, 7).  `[T2Space X.ReducedMor] [ParacompactSpace X.ReducedMor]` are
  satisfiable: for effective `X`, `π` is a homeomorphism (`reducedHomeomorph`), so both hold
  (`t2Space_reducedMor_of_isEffective`, `paracompactSpace_reducedMor_of_isEffective`), and
  `X_R ≅ X` (`reductionIso`); this covers the trivial ep-groupoid of every M-polyfold
  (`t2Space_reducedMor_trivial`, `paracompactSpace_reducedMor_trivial`).  Paracompactness also
  follows from regularity of `𝐗^R` and second countability of `𝐗`
  (`paracompactSpace_reducedMor_of_t3`; for effective `X` the space `𝐗^R` is regular,
  `t3Space_reducedMor_of_isEffective`).  Hausdorff alone with `𝐗` second countable is not shown
  to suffice: a locally metrizable, second countable Hausdorff space need not be regular (the
  `K`-topology on `ℝ`), and we found no argument for regularity of `𝐗^R`.  The sheet form of (4)
  quantifies over all sheets; it is equivalent to the literal (4) (`isScSmoothComp_iff_sheet`).
  No other hypothesis is added.
-/

open Set Function Topology Filter

noncomputable section

namespace Polyfold

namespace EpGroupoid

universe u

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### `𝐗^T` intrinsically -/

/-- **`𝐗^T` intrinsically**: `k ∈ 𝐗^T` iff `s = t` on a neighbourhood of `k` in `𝐗`. -/
theorem mem_nonEffectivePart_iff {k : Mor} :
    k ∈ X.nonEffectivePart ↔ ∀ᶠ ψ in 𝓝 k, X.src ψ = X.tgt ψ := by
  constructor
  · rintro ⟨x, g, hg, rfl⟩
    exact X.mem_trivialSet_iff_eventually.1 hg
  · intro h
    have hk : X.src k = X.tgt k := h.self_of_nhds
    exact ⟨X.src k, ⟨k, rfl, hk.symm⟩, X.mem_trivialSet_iff_eventually.2 h, rfl⟩

/-- `𝐗^T = int {φ | s φ = t φ}`. -/
theorem nonEffectivePart_eq_interior :
    X.nonEffectivePart = interior {ψ | X.src ψ = X.tgt ψ} := by
  ext k
  rw [mem_nonEffectivePart_iff, mem_interior_iff_mem_nhds]
  rfl

theorem isOpen_nonEffectivePart : IsOpen X.nonEffectivePart := by
  rw [nonEffectivePart_eq_interior]
  exact isOpen_interior

theorem unit_mem_nonEffectivePart (x : Obj) : X.unit x ∈ X.nonEffectivePart :=
  ⟨x, 1, (X.trivialSubgroup x).one_mem, rfl⟩

variable {X}

theorem src_eq_tgt_of_mem_nonEffectivePart {k : Mor} (hk : k ∈ X.nonEffectivePart) :
    X.src k = X.tgt k :=
  (X.mem_nonEffectivePart_iff.1 hk).self_of_nhds

/-- For `g ∈ G_x`: `g ∈ T_x` iff `g ∈ 𝐗^T`. -/
theorem val_mem_nonEffectivePart_iff {x : Obj} {g : X.Isotropy x} :
    g.val ∈ X.nonEffectivePart ↔ g ∈ X.trivialSet x := by
  rw [mem_nonEffectivePart_iff, X.mem_trivialSet_iff_eventually]

theorem inv_mem_nonEffectivePart {k : Mor} (hk : k ∈ X.nonEffectivePart) :
    X.inv k ∈ X.nonEffectivePart := by
  obtain ⟨x, g, hg, rfl⟩ := hk
  exact ⟨x, g⁻¹, (X.trivialSubgroup x).inv_mem hg, rfl⟩

theorem comp_mem_nonEffectivePart {k k' : Mor} (hk : k ∈ X.nonEffectivePart)
    (hk' : k' ∈ X.nonEffectivePart) (h : X.src k = X.tgt k') :
    X.comp k k' ∈ X.nonEffectivePart := by
  obtain ⟨x, g, hg, rfl⟩ := hk
  obtain ⟨x', g', hg', rfl⟩ := hk'
  obtain rfl : x = x' := g.src_val.symm.trans (h.trans g'.tgt_val)
  exact ⟨x, g * g', (X.trivialSubgroup x).mul_mem hg hg', rfl⟩

/-- `φ⁻¹ ∘ k ∘ φ ∈ 𝐗^T` for `k ∈ 𝐗^T` with `s k = t φ` (`φ⁻¹ T_y φ = T_x`, `Effective.lean`). -/
theorem conj_mem_nonEffectivePart {k φ : Mor} (hk : k ∈ X.nonEffectivePart)
    (h : X.src k = X.tgt φ) : X.comp (X.inv φ) (X.comp k φ) ∈ X.nonEffectivePart := by
  obtain ⟨y, g, hg, rfl⟩ := hk
  have hy : X.src (X.inv φ) = y := (X.src_inv φ).trans (h.symm.trans g.src_val)
  have h' := X.isotropyConj_mem_trivialSet (X.inv φ) hy (X.tgt_inv φ) hg
  refine ⟨_, _, h', ?_⟩
  rw [GroupoidStr.isotropyConj_val, GroupoidStr.inv_inv,
    X.comp_assoc _ _ _ (by rw [hy, g.tgt_val]) h]

/-! ### Definition 7.2.7 (2017: 7.12): `∼` is an equivalence relation -/

/-- **`φ ∼ φ'` without dependent types**: `φ = φ' ∘ k` for some `k ∈ 𝐗^T` with `s φ' = t k`. -/
theorem reducedRel_iff {φ φ' : Mor} : X.ReducedRel φ φ' ↔
    ∃ k ∈ X.nonEffectivePart, X.src φ' = X.tgt k ∧ φ = X.comp φ' k := by
  constructor
  · rintro ⟨hs, g, hg, he⟩
    exact ⟨g.val, ⟨_, g, hg, rfl⟩, by rw [g.tgt_val, hs], he⟩
  · rintro ⟨k, hk, hc, rfl⟩
    have hkk := src_eq_tgt_of_mem_nonEffectivePart hk
    have hs : X.src (X.comp φ' k) = X.src k := X.src_comp _ _ hc
    refine ⟨hs.trans (hkk.trans hc.symm), ⟨k, hs.symm, hkk.symm.trans hs.symm⟩, ?_, rfl⟩
    exact val_mem_nonEffectivePart_iff.1 hk

theorem ReducedRel.src_eq {φ φ' : Mor} (h : X.ReducedRel φ φ') : X.src φ = X.src φ' := h.1

theorem ReducedRel.tgt_eq {φ φ' : Mor} (h : X.ReducedRel φ φ') : X.tgt φ = X.tgt φ' := by
  obtain ⟨k, -, hc, rfl⟩ := reducedRel_iff.1 h
  exact X.tgt_comp _ _ hc

variable (X) in
theorem reducedRel_refl (φ : Mor) : X.ReducedRel φ φ :=
  reducedRel_iff.2 ⟨X.unit (X.src φ), X.unit_mem_nonEffectivePart _, (X.tgt_unit _).symm,
    (X.comp_unit φ).symm⟩

theorem ReducedRel.symm {φ φ' : Mor} (h : X.ReducedRel φ φ') : X.ReducedRel φ' φ := by
  obtain ⟨k, hk, hc, rfl⟩ := reducedRel_iff.1 h
  refine reducedRel_iff.2 ⟨X.inv k, inv_mem_nonEffectivePart hk, ?_, ?_⟩
  · rw [X.src_comp _ _ hc, X.tgt_inv]
  · exact (GroupoidStr.comp_inv_cancel_right hc).symm

theorem ReducedRel.trans {φ φ' φ'' : Mor} (h : X.ReducedRel φ φ') (h' : X.ReducedRel φ' φ'') :
    X.ReducedRel φ φ'' := by
  obtain ⟨k, hk, hc, rfl⟩ := reducedRel_iff.1 h
  obtain ⟨k', hk', hc', rfl⟩ := reducedRel_iff.1 h'
  have hkk' : X.src k' = X.tgt k := (X.src_comp _ _ hc').symm.trans hc
  refine reducedRel_iff.2 ⟨X.comp k' k, comp_mem_nonEffectivePart hk' hk hkk', ?_, ?_⟩
  · rw [X.tgt_comp _ _ hkk']
    exact hc'
  · exact X.comp_assoc _ _ _ hc' hkk'

/-- **The left form of `∼`**: `k ∘ φ ∼ φ` for `k ∈ 𝐗^T` with `s k = t φ`. -/
theorem reducedRel_comp_left {k φ : Mor} (hk : k ∈ X.nonEffectivePart) (h : X.src k = X.tgt φ) :
    X.ReducedRel (X.comp k φ) φ := by
  have hc : X.src (X.inv φ) = X.tgt (X.comp k φ) := by
    rw [X.src_inv, X.tgt_comp _ _ h, ← h, src_eq_tgt_of_mem_nonEffectivePart hk]
  refine reducedRel_iff.2 ⟨_, conj_mem_nonEffectivePart hk h, ?_, ?_⟩
  · rw [X.tgt_comp _ _ hc, X.tgt_inv]
  · rw [← X.comp_assoc _ _ _ (X.tgt_inv φ).symm hc, X.comp_inv,
      GroupoidStr.unit_comp_of_eq (by rw [X.tgt_comp _ _ h, ← h,
        src_eq_tgt_of_mem_nonEffectivePart hk])]

/-- **The left form of `∼`**, conversely: `φ ∼ φ'` gives `φ = k ∘ φ'` with `k ∈ 𝐗^T`,
`s k = t φ'` (`k = φ' g φ'⁻¹`). -/
theorem ReducedRel.exists_comp_left {φ φ' : Mor} (h : X.ReducedRel φ φ') :
    ∃ k ∈ X.nonEffectivePart, X.src k = X.tgt φ' ∧ φ = X.comp k φ' := by
  obtain ⟨k, hk, hc, rfl⟩ := reducedRel_iff.1 h
  have hkk := src_eq_tgt_of_mem_nonEffectivePart hk
  have h1 : X.src k = X.tgt (X.inv φ') := by rw [X.tgt_inv, hkk, hc]
  have h2 : X.src φ' = X.tgt (X.comp k (X.inv φ')) := by rw [X.tgt_comp _ _ h1]; exact hc
  have hmem := conj_mem_nonEffectivePart hk h1
  rw [GroupoidStr.inv_inv] at hmem
  refine ⟨_, hmem, ?_, ?_⟩
  · rw [X.src_comp _ _ h2, X.src_comp _ _ h1, X.src_inv]
  · rw [X.comp_assoc _ _ _ h2 (by rw [X.src_comp _ _ h1, X.src_inv]),
      X.comp_assoc _ _ _ h1 (X.src_inv φ'), X.inv_comp,
      GroupoidStr.comp_unit_of_eq (hkk.trans hc.symm)]

theorem ReducedRel.inv {φ φ' : Mor} (h : X.ReducedRel φ φ') :
    X.ReducedRel (X.inv φ) (X.inv φ') := by
  obtain ⟨k, hk, hc, rfl⟩ := reducedRel_iff.1 h
  rw [GroupoidStr.inv_comp_rev hc]
  exact reducedRel_comp_left (inv_mem_nonEffectivePart hk) (by rw [X.src_inv, X.tgt_inv, hc])

theorem ReducedRel.comp_right {φ ψ ψ' : Mor} (h : X.ReducedRel ψ ψ') (hc : X.src φ = X.tgt ψ) :
    X.ReducedRel (X.comp φ ψ) (X.comp φ ψ') := by
  obtain ⟨k, hk, hk', rfl⟩ := reducedRel_iff.1 h
  have hc' : X.src φ = X.tgt ψ' := hc.trans (X.tgt_comp _ _ hk')
  refine reducedRel_iff.2 ⟨k, hk, ?_, (X.comp_assoc _ _ _ hc' hk').symm⟩
  rw [X.src_comp _ _ hc']
  exact hk'

theorem ReducedRel.comp_left {φ φ' ψ : Mor} (h : X.ReducedRel φ φ') (hc : X.src φ = X.tgt ψ) :
    X.ReducedRel (X.comp φ ψ) (X.comp φ' ψ) := by
  obtain ⟨k, hk, hk', rfl⟩ := h.exists_comp_left
  have hc' : X.src φ' = X.tgt ψ := (X.src_comp _ _ hk').symm.trans hc
  rw [X.comp_assoc _ _ _ hk' hc']
  exact reducedRel_comp_left hk (by rw [X.tgt_comp _ _ hc']; exact hk')

/-! ### The quotient `𝐗^R` and its topology -/

variable (X)

/-- **Definition 7.2.7 (2017: 7.12), made precise**: `∼` is an equivalence relation (`T_x` being a subgroup). -/
def reducedSetoid : Setoid Mor where
  r := X.ReducedRel
  iseqv := ⟨X.reducedRel_refl, ReducedRel.symm, ReducedRel.trans⟩

/-- `𝐗^R` is the quotient of `𝐗` by the equivalence relation `∼`. -/
theorem reducedMor_eq_quotient : X.ReducedMor = Quotient X.reducedSetoid := rfl

/-- **`𝐗^R` carries the quotient topology** (p. 242). -/
instance : TopologicalSpace X.ReducedMor := inferInstanceAs (TopologicalSpace (Quot X.ReducedRel))

/-- The projection `π : 𝐗 → 𝐗^R`, `φ ↦ [φ]`. -/
def reducedπ : Mor → X.ReducedMor := Quot.mk _

theorem reducedπ_eq_iff {φ φ' : Mor} : X.reducedπ φ = X.reducedπ φ' ↔ X.ReducedRel φ φ' :=
  Quotient.eq (r := X.reducedSetoid)

theorem surjective_reducedπ : Surjective X.reducedπ := Quot.mk_surjective

theorem isQuotientMap_reducedπ : IsQuotientMap X.reducedπ := isQuotientMap_quot_mk

theorem continuous_reducedπ : Continuous X.reducedπ := continuous_quot_mk

/-- **The projection `π : 𝐗 → 𝐗^R` is open** (the proof of Proposition 7.2.10 (2017: 7.9), p. 313 (2017 p. 242)).  For
`φ = k ∘ ψ`, `k ∈ T_{t ψ}`, the map `ψ' ↦ Γ(g, t ψ') ∘ ψ'` (`g = k`) is continuous and
`Γ(g, t ψ') ∘ ψ' ∼ ψ'`. -/
theorem isOpenMap_reducedπ : IsOpenMap X.reducedπ := by
  intro O hO
  rw [← X.isQuotientMap_reducedπ.isOpen_preimage]
  refine isOpen_iff_mem_nhds.2 fun ψ hψ => ?_
  obtain ⟨φ, hφO, he⟩ := hψ
  obtain ⟨k, hk, hks, rfl⟩ := (X.reducedπ_eq_iff.1 he).exists_comp_left
  -- `k ∈ T_y`, `y = t ψ`, and a natural representation at `y` with `ker Φ = T_y`
  have hkk := src_eq_tgt_of_mem_nonEffectivePart hk
  let g : X.Isotropy (X.src k) := ⟨k, rfl, hkk.symm⟩
  obtain ⟨R, -, hR⟩ := X.exists_naturalRep_trivialSet_iff (X.src k) isOpen_univ (mem_univ _)
  have hg : ∀ z ∈ R.U, R.Φ g z = z := (hR g).1 (val_mem_nonEffectivePart_iff.1 hk)
  -- `δ(ψ') = Γ(g, t ψ') ∘ ψ'` is continuous, `δ(ψ) = k ∘ ψ`
  have hF := (R.isScSmoothOn_comp_Γ_tgt g).continuousOn
  have hψU : ψ ∈ X.tgt ⁻¹' R.U := by rw [mem_preimage, ← hks]; exact R.mem_U
  have hFψ : X.comp (R.Γ g (X.tgt ψ)) ψ = X.comp k ψ := by rw [← hks, R.Γ_self]
  have hN : X.tgt ⁻¹' R.U ∩ (fun ψ' => X.comp (R.Γ g (X.tgt ψ')) ψ') ⁻¹' O ∈ 𝓝 ψ :=
    (hF.isOpen_inter_preimage (R.isOpen_U.preimage X.continuous_tgt) hO).mem_nhds
      ⟨hψU, by rw [mem_preimage, hFψ]; exact hφO⟩
  filter_upwards [hN] with ψ' hψ'
  -- `Γ(g, t ψ') ∈ T_{t ψ'}`, so `δ(ψ') ∼ ψ'`
  have hT : R.Γ g (X.tgt ψ') ∈ X.nonEffectivePart := by
    let h' : X.Isotropy (X.tgt ψ') :=
      ⟨R.Γ g (X.tgt ψ'), R.src_Γ g _ hψ'.1, (R.tgt_Γ g _ hψ'.1).trans (hg _ hψ'.1)⟩
    exact val_mem_nonEffectivePart_iff.2 (R.mem_trivialSet_of_val_eq_Γ hg hψ'.1 (h := h') rfl)
  exact ⟨_, hψ'.2, X.reducedπ_eq_iff.2 (reducedRel_comp_left hT (R.src_Γ g _ hψ'.1))⟩

/-! ### The structure maps descend to `𝐗^R` -/

/-- `s([φ]) = s(φ)` (p. 243). -/
def reducedSrc : X.ReducedMor → Obj := Quot.lift X.src fun _ _ h => ReducedRel.src_eq h

/-- `t([φ]) = t(φ)` (p. 243). -/
def reducedTgt : X.ReducedMor → Obj := Quot.lift X.tgt fun _ _ h => ReducedRel.tgt_eq h

/-- `u(x) = [1_x]`. -/
def reducedUnit (x : Obj) : X.ReducedMor := X.reducedπ (X.unit x)

/-- `ι([φ]) = [φ⁻¹]`. -/
def reducedInv : X.ReducedMor → X.ReducedMor :=
  Quot.lift (fun φ => X.reducedπ (X.inv φ)) fun _ _ h => X.reducedπ_eq_iff.2 (ReducedRel.inv h)

open scoped Classical in
/-- `m([φ], [ψ]) = [φ ∘ ψ]` for `s φ = t ψ` (and `[φ]` otherwise, a junk value). -/
def reducedComp : X.ReducedMor → X.ReducedMor → X.ReducedMor :=
  Quot.lift₂ (fun φ ψ => if X.src φ = X.tgt ψ then X.reducedπ (X.comp φ ψ) else X.reducedπ φ)
    (fun φ ψ ψ' h => by
      by_cases hc : X.src φ = X.tgt ψ
      · rw [if_pos hc, if_pos (hc.trans (ReducedRel.tgt_eq h))]
        exact X.reducedπ_eq_iff.2 (ReducedRel.comp_right h hc)
      · rw [if_neg hc, if_neg fun hc' => hc (hc'.trans (ReducedRel.tgt_eq h).symm)])
    (fun φ φ' ψ h => by
      by_cases hc : X.src φ = X.tgt ψ
      · rw [if_pos hc, if_pos ((ReducedRel.src_eq h).symm.trans hc)]
        exact X.reducedπ_eq_iff.2 (ReducedRel.comp_left h hc)
      · rw [if_neg hc, if_neg fun hc' => hc ((ReducedRel.src_eq h).trans hc')]
        exact X.reducedπ_eq_iff.2 h)

@[simp]
theorem reducedSrc_π (φ : Mor) : X.reducedSrc (X.reducedπ φ) = X.src φ := rfl

@[simp]
theorem reducedTgt_π (φ : Mor) : X.reducedTgt (X.reducedπ φ) = X.tgt φ := rfl

@[simp]
theorem reducedInv_π (φ : Mor) : X.reducedInv (X.reducedπ φ) = X.reducedπ (X.inv φ) := rfl

open scoped Classical in
theorem reducedComp_π {φ ψ : Mor} (h : X.src φ = X.tgt ψ) :
    X.reducedComp (X.reducedπ φ) (X.reducedπ ψ) = X.reducedπ (X.comp φ ψ) := by
  change (if X.src φ = X.tgt ψ then _ else _) = _
  rw [if_pos h]

theorem continuous_reducedSrc : Continuous X.reducedSrc := continuous_quot_lift _ X.continuous_src

theorem continuous_reducedTgt : Continuous X.reducedTgt := continuous_quot_lift _ X.continuous_tgt

theorem continuous_reducedInv : Continuous X.reducedInv :=
  continuous_quot_lift _ (X.continuous_reducedπ.comp X.continuous_inv)

/-- `s : 𝐗^R → X` is surjective (p. 243). -/
theorem surjective_reducedSrc : Surjective X.reducedSrc := fun x => ⟨X.reducedUnit x, X.src_unit x⟩

/-- `t : 𝐗^R → X` is surjective (p. 243). -/
theorem surjective_reducedTgt : Surjective X.reducedTgt := fun x => ⟨X.reducedUnit x, X.tgt_unit x⟩

/-- **The groupoid `(X, 𝐗^R)`** (p. 243): the structure maps of `X` descend. -/
def reducedGroupoidStr : GroupoidStr Obj X.ReducedMor where
  src := X.reducedSrc
  tgt := X.reducedTgt
  comp := X.reducedComp
  unit := X.reducedUnit
  inv := X.reducedInv
  src_comp a b h := by
    obtain ⟨φ, rfl⟩ := X.surjective_reducedπ a
    obtain ⟨ψ, rfl⟩ := X.surjective_reducedπ b
    rw [reducedSrc_π, reducedTgt_π] at h
    rw [X.reducedComp_π h, reducedSrc_π, reducedSrc_π, X.src_comp _ _ h]
  tgt_comp a b h := by
    obtain ⟨φ, rfl⟩ := X.surjective_reducedπ a
    obtain ⟨ψ, rfl⟩ := X.surjective_reducedπ b
    rw [reducedSrc_π, reducedTgt_π] at h
    rw [X.reducedComp_π h, reducedTgt_π, reducedTgt_π, X.tgt_comp _ _ h]
  comp_assoc a b c h h' := by
    obtain ⟨φ, rfl⟩ := X.surjective_reducedπ a
    obtain ⟨ψ, rfl⟩ := X.surjective_reducedπ b
    obtain ⟨χ, rfl⟩ := X.surjective_reducedπ c
    rw [reducedSrc_π, reducedTgt_π] at h h'
    rw [X.reducedComp_π h, X.reducedComp_π (by rw [X.src_comp _ _ h]; exact h'),
      X.reducedComp_π h', X.reducedComp_π (by rw [X.tgt_comp _ _ h']; exact h),
      X.comp_assoc _ _ _ h h']
  src_unit x := X.src_unit x
  tgt_unit x := X.tgt_unit x
  comp_unit a := by
    obtain ⟨φ, rfl⟩ := X.surjective_reducedπ a
    rw [reducedSrc_π, reducedUnit, X.reducedComp_π (X.tgt_unit _).symm, X.comp_unit]
  unit_comp a := by
    obtain ⟨φ, rfl⟩ := X.surjective_reducedπ a
    rw [reducedTgt_π, reducedUnit, X.reducedComp_π (X.src_unit _), X.unit_comp]
  src_inv a := by
    obtain ⟨φ, rfl⟩ := X.surjective_reducedπ a
    exact X.src_inv φ
  tgt_inv a := by
    obtain ⟨φ, rfl⟩ := X.surjective_reducedπ a
    exact X.tgt_inv φ
  comp_inv a := by
    obtain ⟨φ, rfl⟩ := X.surjective_reducedπ a
    rw [reducedInv_π, X.reducedComp_π (X.tgt_inv φ).symm, X.comp_inv, reducedTgt_π, reducedUnit]
  inv_comp a := by
    obtain ⟨φ, rfl⟩ := X.surjective_reducedπ a
    rw [reducedInv_π, X.reducedComp_π (X.src_inv φ), X.inv_comp, reducedSrc_π, reducedUnit]

/-- **(3) of Definition 7.1.3 (2017: 7.3) descends** ("the properness can be proved similarly", p. 244): for
`V(x)` of Definition 7.1.3 (2017: 7.3) (3) for `X`, `t : s⁻¹(cl V(x)) → X` is proper on `𝐗^R`, since `π` is a
continuous surjection of `s⁻¹(cl V(x)) ⊆ 𝐗` onto `s⁻¹(cl V(x)) ⊆ 𝐗^R` and `t ∘ π = t_X`. -/
theorem exists_isProperMap_reduced (x : Obj) : ∃ V : Set Obj, IsOpen V ∧ x ∈ V ∧
    IsProperMap ((X.reducedSrc ⁻¹' closure V).domRestrict X.reducedTgt) := by
  obtain ⟨V, hVo, hxV, hV⟩ := X.exists_isProperMap x
  refine ⟨V, hVo, hxV, ?_⟩
  let f : X.src ⁻¹' closure V → X.reducedSrc ⁻¹' closure V := fun φ => ⟨X.reducedπ φ.1, φ.2⟩
  refine isProperMap_of_comp_of_surj (f := f)
    ((X.continuous_reducedπ.comp continuous_subtype_val).subtype_mk _)
    (X.continuous_reducedTgt.comp continuous_subtype_val) hV ?_
  rintro ⟨q, hq⟩
  obtain ⟨φ, rfl⟩ := X.surjective_reducedπ q
  exact ⟨⟨φ, hq⟩, rfl⟩

/-! ### Small sheets -/

variable {X} {σ : Obj → Mor} {W : Set Mor} {V : Set Obj}

/-- On a sheet `s : W → V` of `s`, `π` is injective (p. 242). -/
theorem injOn_reducedπ (hS : X.PMor.IsScDiffeoOn X.PObj X.src σ W V) : InjOn X.reducedπ W :=
  fun φ hφ φ' hφ' he => by
    rw [← hS.left_inv φ hφ, ← hS.left_inv φ' hφ', ReducedRel.src_eq (X.reducedπ_eq_iff.1 he)]

/-- **`π` is a homeomorphism on every sheet of `s`** onto an open subset of `𝐗^R` (p. 242). -/
theorem isOpenEmbedding_domRestrict_reducedπ (hS : X.PMor.IsScDiffeoOn X.PObj X.src σ W V) :
    IsOpenEmbedding (W.domRestrict X.reducedπ) :=
  .of_continuous_injective_isOpenMap (X.continuous_reducedπ.comp continuous_subtype_val)
    (injOn_iff_injective.1 (injOn_reducedπ hS))
    (X.isOpenMap_reducedπ.domRestrict hS.isScSmoothOn.isOpen)

/-- The same for the sheets `𝐔(g) = Γ(g, U)` of a natural representation (Theorem 7.1.13 (2017: 7.1)). -/
theorem isOpenEmbedding_domRestrict_reducedπ_image_Γ {x : Obj} (R : X.NaturalRep x)
    (g : X.Isotropy x) : IsOpenEmbedding ((R.Γ g '' R.U).domRestrict X.reducedπ) :=
  isOpenEmbedding_domRestrict_reducedπ (R.isScDiffeoOn_src_image g)

theorem sheet_inv_π (hS : X.PMor.IsScDiffeoOn X.PObj X.src σ W V) {φ : Mor} (hφ : φ ∈ W) :
    σ (X.reducedSrc (X.reducedπ φ)) = φ :=
  hS.left_inv φ hφ

theorem π_sheet_inv (hS : X.PMor.IsScDiffeoOn X.PObj X.src σ W V) {q : X.ReducedMor}
    (hq : q ∈ X.reducedπ '' W) : X.reducedπ (σ (X.reducedSrc q)) = q := by
  obtain ⟨φ, hφ, rfl⟩ := hq
  rw [sheet_inv_π hS hφ]

theorem sheet_inv_mem (hS : X.PMor.IsScDiffeoOn X.PObj X.src σ W V) {q : X.ReducedMor}
    (hq : q ∈ X.reducedπ '' W) : σ (X.reducedSrc q) ∈ W := by
  obtain ⟨φ, hφ, rfl⟩ := hq
  rw [sheet_inv_π hS hφ]
  exact hφ

theorem mapsTo_reducedSrc_image (hS : X.PMor.IsScDiffeoOn X.PObj X.src σ W V) :
    MapsTo X.reducedSrc (X.reducedπ '' W) V := by
  rintro _ ⟨φ, hφ, rfl⟩
  exact hS.mapsTo hφ

theorem continuousOn_sheet_inv (hS : X.PMor.IsScDiffeoOn X.PObj X.src σ W V) :
    ContinuousOn (fun q => σ (X.reducedSrc q)) (X.reducedπ '' W) :=
  hS.isScSmoothOn_inv.continuousOn.comp X.continuous_reducedSrc.continuousOn
    (mapsTo_reducedSrc_image hS)

/-! ### Proposition 7.2.10 (2017: 7.9): the charts `Ψ_φ` and the atlas -/

variable (X) in
/-- **The chart `Ψ_φ`** of `𝐗^R` (p. 242) from a chart `ψ` of `𝐗` with domain in a sheet
`s : W → V` (inverse `σ`): `[φ'] ↦ ψ(σ(s[φ']))` on `π(dom ψ)`, with inverse `z ↦ [ψ⁻¹(z)]`. -/
def reducedChart (ψ : MChart Mor) (hS : X.PMor.IsScDiffeoOn X.PObj X.src σ W V)
    (hψW : ψ.source ⊆ W) : MChart X.ReducedMor where
  model := ψ.model
  toPartialEquiv :=
    { toFun := fun q => ψ (σ (X.reducedSrc q))
      invFun := fun z => X.reducedπ (ψ.symm z)
      source := X.reducedπ '' ψ.source
      target := ψ.model.O
      map_source' := by
        rintro _ ⟨φ, hφ, rfl⟩
        change ψ (σ (X.src φ)) ∈ ψ.model.O
        rw [hS.left_inv φ (hψW hφ)]
        exact ψ.mapsTo_model φ hφ
      map_target' := fun z hz => ⟨ψ.symm z, ψ.symm_mapsTo hz, rfl⟩
      left_inv' := by
        rintro _ ⟨φ, hφ, rfl⟩
        change X.reducedπ (ψ.symm (ψ (σ (X.src φ)))) = X.reducedπ φ
        rw [hS.left_inv φ (hψW hφ), ψ.symm_apply_apply hφ]
      right_inv' := fun z hz => by
        change ψ (σ (X.src (ψ.symm z))) = z
        rw [hS.left_inv _ (hψW (ψ.symm_mapsTo hz)), ψ.apply_symm_apply hz] }
  isOpen_source := X.isOpenMap_reducedπ _ ψ.isOpen_source
  target_eq := rfl
  continuousOn_toFun := by
    refine ψ.continuousOn_toFun.comp ((continuousOn_sheet_inv hS).mono (image_mono hψW)) ?_
    rintro _ ⟨φ, hφ, rfl⟩
    change σ (X.src φ) ∈ ψ.source
    rw [hS.left_inv φ (hψW hφ)]
    exact hφ
  continuousOn_invFun := X.continuous_reducedπ.comp_continuousOn ψ.continuousOn_invFun

@[simp]
theorem reducedChart_source (ψ : MChart Mor) (hS : X.PMor.IsScDiffeoOn X.PObj X.src σ W V)
    (hψW : ψ.source ⊆ W) : (X.reducedChart ψ hS hψW).source = X.reducedπ '' ψ.source :=
  rfl

theorem reducedChart_π (ψ : MChart Mor) (hS : X.PMor.IsScDiffeoOn X.PObj X.src σ W V)
    (hψW : ψ.source ⊆ W) {φ : Mor} (hφ : φ ∈ W) :
    X.reducedChart ψ hS hψW (X.reducedπ φ) = ψ φ := by
  change ψ (σ (X.src φ)) = ψ φ
  rw [hS.left_inv φ hφ]

theorem reducedChart_symm (ψ : MChart Mor) (hS : X.PMor.IsScDiffeoOn X.PObj X.src σ W V)
    (hψW : ψ.source ⊆ W) (z : ψ.model.E 0) :
    (X.reducedChart ψ hS hψW).symm z = X.reducedπ (ψ.symm z) :=
  rfl

section Compatible

variable {σ₁ σ₂ : Obj → Mor} {W₁ W₂ : Set Mor} {V₁ V₂ : Set Obj}

/-- The overlap `Ψ₁(dom Ψ₁ ∩ dom Ψ₂) = ψ₁(dom ψ₁ ∩ π⁻¹(π(dom ψ₂)))`. -/
theorem overlap_reducedChart {ψ₁ ψ₂ : MChart Mor}
    (hS₁ : X.PMor.IsScDiffeoOn X.PObj X.src σ₁ W₁ V₁) (h₁ : ψ₁.source ⊆ W₁)
    (hS₂ : X.PMor.IsScDiffeoOn X.PObj X.src σ₂ W₂ V₂) (h₂ : ψ₂.source ⊆ W₂) :
    (X.reducedChart ψ₁ hS₁ h₁).overlap (X.reducedChart ψ₂ hS₂ h₂) =
      ψ₁ '' (ψ₁.source ∩ X.reducedπ ⁻¹' (X.reducedπ '' ψ₂.source)) := by
  ext z
  constructor
  · rintro ⟨_, ⟨⟨φ, hφ, rfl⟩, hq₂⟩, rfl⟩
    exact ⟨φ, ⟨hφ, hq₂⟩, (X.reducedChart_π ψ₁ hS₁ h₁ (h₁ hφ)).symm⟩
  · rintro ⟨φ, ⟨hφ, hq₂⟩, rfl⟩
    exact ⟨X.reducedπ φ, ⟨⟨φ, hφ, rfl⟩, hq₂⟩, X.reducedChart_π ψ₁ hS₁ h₁ (h₁ hφ)⟩

/-- **The transition `Ψ₂ ∘ Ψ₁⁻¹` is sc-smooth** (p. 243): on the overlap it is
`ψ₂ ∘ (σ₂ ∘ s) ∘ ψ₁⁻¹`, `σ₂ ∘ s` is sc-smooth, and the overlap is open since `π` is open. -/
private theorem reducedChart_transition {ψ₁ ψ₂ : MChart Mor} (hψ₁ : X.PMor.IsChart ψ₁)
    (hψ₂ : X.PMor.IsChart ψ₂)
    (hS₁ : X.PMor.IsScDiffeoOn X.PObj X.src σ₁ W₁ V₁) (h₁ : ψ₁.source ⊆ W₁)
    (hS₂ : X.PMor.IsScDiffeoOn X.PObj X.src σ₂ W₂ V₂) (h₂ : ψ₂.source ⊆ W₂) :
    IsScSmoothRetractMap ψ₁.model.E ψ₁.model.C
      ((X.reducedChart ψ₁ hS₁ h₁).overlap (X.reducedChart ψ₂ hS₂ h₂)) ψ₂.model.E ψ₂.model.C
      ((X.reducedChart ψ₂ hS₂ h₂).overlap (X.reducedChart ψ₁ hS₁ h₁))
      ((X.reducedChart ψ₁ hS₁ h₁).transition (X.reducedChart ψ₂ hS₂ h₂)) := by
  have hD : IsOpen (ψ₁.source ∩ X.reducedπ ⁻¹' (X.reducedπ '' ψ₂.source)) :=
    ψ₁.isOpen_source.inter ((X.isOpenMap_reducedπ _ ψ₂.isOpen_source).preimage
      X.continuous_reducedπ)
  have hf : X.PMor.IsScSmoothOn X.PMor (fun φ => σ₂ (X.src φ)) (X.src ⁻¹' V₂) :=
    MPolyfold.IsScSmoothOn.comp hS₂.isScSmoothOn_inv
      (X.isScSmoothMap_src.mono (hS₂.isScSmoothOn_inv.isOpen.preimage X.continuous_src)
        (subset_univ _)) fun _ hφ => hφ
  have hsub : ψ₁.source ∩ X.reducedπ ⁻¹' (X.reducedπ '' ψ₂.source) ⊆
      X.src ⁻¹' V₂ ∩ ψ₁.source := fun φ hφ => by
    obtain ⟨φ', hφ', he⟩ := hφ.2
    refine ⟨?_, hφ.1⟩
    rw [mem_preimage, ← ReducedRel.src_eq (X.reducedπ_eq_iff.1 he)]
    exact hS₂.mapsTo (h₂ hφ')
  have hmaps : MapsTo (fun φ => σ₂ (X.src φ))
      (ψ₁.source ∩ X.reducedπ ⁻¹' (X.reducedπ '' ψ₂.source)) ψ₂.source := fun φ hφ => by
    obtain ⟨φ', hφ', he⟩ := hφ.2
    change σ₂ (X.src φ) ∈ ψ₂.source
    rw [← ReducedRel.src_eq (X.reducedπ_eq_iff.1 he), hS₂.left_inv _ (h₂ hφ')]
    exact hφ'
  have key := hf.smooth ψ₁ ψ₂ hψ₁ hψ₂ _ hD hsub hmaps
  have hmt := (X.reducedChart ψ₁ hS₁ h₁).transition_mapsTo (X.reducedChart ψ₂ hS₂ h₂)
  rw [X.overlap_reducedChart hS₁ h₁ hS₂ h₂] at hmt ⊢
  exact key.mono_target hmt

/-- **The charts `Ψ_φ` are sc-smoothly compatible** (Proposition 7.2.10 (2017: 7.9), p. 243). -/
theorem reducedChart_compatible {ψ₁ ψ₂ : MChart Mor} (hψ₁ : X.PMor.IsChart ψ₁)
    (hψ₂ : X.PMor.IsChart ψ₂)
    (hS₁ : X.PMor.IsScDiffeoOn X.PObj X.src σ₁ W₁ V₁) (h₁ : ψ₁.source ⊆ W₁)
    (hS₂ : X.PMor.IsScDiffeoOn X.PObj X.src σ₂ W₂ V₂) (h₂ : ψ₂.source ⊆ W₂) :
    (X.reducedChart ψ₁ hS₁ h₁).Compatible (X.reducedChart ψ₂ hS₂ h₂) :=
  ⟨reducedChart_transition hψ₁ hψ₂ hS₁ h₁ hS₂ h₂, reducedChart_transition hψ₂ hψ₁ hS₂ h₂ hS₁ h₁⟩

end Compatible

variable (X)

/-- The charts `Ψ_φ` of `𝐗^R`: all `reducedChart ψ` for charts `ψ` of `𝐗` with domain in a sheet
of `s`. -/
def reducedCharts : Set (MChart X.ReducedMor) :=
  {χ | ∃ (ψ : MChart Mor) (σ : Obj → Mor) (W : Set Mor) (V : Set Obj)
    (hS : X.PMor.IsScDiffeoOn X.PObj X.src σ W V) (hψW : ψ.source ⊆ W),
    X.PMor.IsChart ψ ∧ χ = X.reducedChart ψ hS hψW}

/-- Every point of `𝐗` lies in the domain of a chart of `𝐗` inside a sheet of `s`. -/
theorem exists_chart_sheet (φ : Mor) : ∃ (ψ : MChart Mor) (σ : Obj → Mor) (W : Set Mor)
    (V : Set Obj) (_ : X.PMor.IsScDiffeoOn X.PObj X.src σ W V) (_ : ψ.source ⊆ W),
    X.PMor.IsChart ψ ∧ φ ∈ ψ.source := by
  obtain ⟨W, V, σ, hφW, hS⟩ := X.isLocalScDiffeo_src φ
  obtain ⟨ψ, hψ, hφψ⟩ := X.PMor.exists_isChart_mem_source φ
  have ho : IsOpen (ψ.source ∩ W) := ψ.isOpen_source.inter hS.isScSmoothOn.isOpen
  exact ⟨ψ.restrict inter_subset_left ho, σ, W, V, hS, inter_subset_right,
    MPolyfold.IsChart.restrict _ hψ _ _, hφψ, hφW⟩

/-- **Proposition 7.2.10 (2017: 7.9), the atlas**: the charts `Ψ_φ` form an sc-smooth atlas of `𝐗^R`
(Definition 2.3.3 (2017: 2.7) [2.12]). -/
def reducedAtlas : MAtlas X.ReducedMor where
  charts := X.reducedCharts
  compatible := by
    rintro _ ⟨ψ₁, σ₁, W₁, V₁, hS₁, h₁, hψ₁, rfl⟩ _ ⟨ψ₂, σ₂, W₂, V₂, hS₂, h₂, hψ₂, rfl⟩
    exact reducedChart_compatible hψ₁ hψ₂ hS₁ h₁ hS₂ h₂
  cover q := by
    obtain ⟨φ, rfl⟩ := X.surjective_reducedπ q
    obtain ⟨ψ, σ, W, V, hS, hψW, hψ, hφ⟩ := X.exists_chart_sheet φ
    exact ⟨X.reducedChart ψ hS hψW, ⟨ψ, σ, W, V, hS, hψW, hψ, rfl⟩, φ, hφ, rfl⟩

/-! ### Proposition 7.2.10 (2017: 7.9): the M-polyfold `𝐗^R` -/

/-- Sc-smoothness on an open set is local (as the private helper of `EpGroupoid.lean`). -/
private theorem isScSmoothOn_of_local' {A : Type*} [TopologicalSpace A] [T2Space A]
    [ParacompactSpace A] {PA : MPolyfold A} {B : Type*} [TopologicalSpace B] [T2Space B]
    [ParacompactSpace B] {PB : MPolyfold B} {f : A → B} {U : Set A} (hU : IsOpen U)
    (h : ∀ x ∈ U, ∃ W : Set A, x ∈ W ∧ PA.IsScSmoothOn PB f W) : PA.IsScSmoothOn PB f U := by
  have hcont : ContinuousOn f U := fun x hx => by
    obtain ⟨W, hxW, hW⟩ := h x hx
    exact (hW.continuousOn.continuousAt (hW.isOpen.mem_nhds hxW)).continuousWithinAt
  refine MPolyfold.IsScSmoothOn.of_exists_charts hU hcont fun x hx => ?_
  obtain ⟨W, hxW, hW⟩ := h x hx
  obtain ⟨φ, hφ, hxφ⟩ := PA.exists_isChart_mem_source x
  obtain ⟨ψ, hψ, hfx⟩ := PB.exists_isChart_mem_source (f x)
  have hVo : IsOpen ((W ∩ U ∩ φ.source) ∩ f ⁻¹' ψ.source) :=
    (hW.continuousOn.mono fun y hy => hy.1.1).isOpen_inter_preimage
      ((hW.isOpen.inter hU).inter φ.isOpen_source) ψ.isOpen_source
  exact ⟨φ, ψ, _, hφ, hψ, hVo, ⟨⟨⟨hxW, hx⟩, hxφ⟩, hfx⟩, fun y hy => ⟨hy.1.1.2, hy.1.2⟩,
    fun y hy => hy.2, hW.smooth φ ψ hφ hψ _ hVo (fun y hy => ⟨hy.1.1.1, hy.1.2⟩) fun y hy => hy.2⟩

section ReducedPolyfold

variable [T2Space X.ReducedMor] [ParacompactSpace X.ReducedMor]

/-- **Proposition 7.2.10 (2017: 7.9)**: the M-polyfold `𝐗^R` (Definition 2.3.4 (2017: 2.8) [2.13]), given by the atlas of the
charts `Ψ_φ`; that `𝐗^R` is Hausdorff and paracompact is a hypothesis (PLAN P7). -/
def reducedPolyfold : MPolyfold X.ReducedMor := ⟨X.reducedAtlas⟩

variable {X}

theorem isChart_reducedChart {ψ : MChart Mor} (hψ : X.PMor.IsChart ψ)
    (hS : X.PMor.IsScDiffeoOn X.PObj X.src σ W V) (hψW : ψ.source ⊆ W) :
    X.reducedPolyfold.IsChart (X.reducedChart ψ hS hψW) :=
  X.reducedPolyfold.isChart_of_mem ⟨ψ, σ, W, V, hS, hψW, hψ, rfl⟩

/-- **`π : W → π(W)` is an sc-diffeomorphism** on every sheet `s : W → V`, with inverse `σ ∘ s`
(the maps `Ψ_φ` of p. 242 in the language of M-polyfolds). -/
theorem isScDiffeoOn_reducedπ (hS : X.PMor.IsScDiffeoOn X.PObj X.src σ W V) :
    X.PMor.IsScDiffeoOn X.reducedPolyfold X.reducedπ (fun q => σ (X.reducedSrc q)) W
      (X.reducedπ '' W) where
  isScSmoothOn := by
    refine MPolyfold.IsScSmoothOn.of_exists_charts hS.isScSmoothOn.isOpen
      X.continuous_reducedπ.continuousOn fun φ hφ => ?_
    obtain ⟨ψ, hψ, hφψ⟩ := X.PMor.exists_isChart_mem_source φ
    have ho : IsOpen (ψ.source ∩ W) := ψ.isOpen_source.inter hS.isScSmoothOn.isOpen
    let ψ' := ψ.restrict inter_subset_left ho
    have hψ' : X.PMor.IsChart ψ' := MPolyfold.IsChart.restrict _ hψ _ _
    refine ⟨ψ', X.reducedChart ψ' hS inter_subset_right, ψ'.source, hψ',
      isChart_reducedChart hψ' hS inter_subset_right, ho, ⟨hφψ, hφ⟩, fun x hx => ⟨hx.2, hx⟩,
      fun x hx => ⟨x, hx, rfl⟩, ?_⟩
    rw [ψ'.image_source]
    refine (isScSmoothRetractMap_id _).congr fun z hz => ?_
    change z = ψ' (σ (X.src (ψ'.symm z)))
    rw [hS.left_inv _ (inter_subset_right (ψ'.symm_mapsTo hz)), ψ'.apply_symm_apply hz]
  isScSmoothOn_inv := by
    refine MPolyfold.IsScSmoothOn.of_exists_charts
      (X.isOpenMap_reducedπ _ hS.isScSmoothOn.isOpen) (continuousOn_sheet_inv hS) fun q hq => ?_
    obtain ⟨φ, hφ, rfl⟩ := hq
    obtain ⟨ψ, hψ, hφψ⟩ := X.PMor.exists_isChart_mem_source φ
    have ho : IsOpen (ψ.source ∩ W) := ψ.isOpen_source.inter hS.isScSmoothOn.isOpen
    let ψ' := ψ.restrict inter_subset_left ho
    have hψ' : X.PMor.IsChart ψ' := MPolyfold.IsChart.restrict _ hψ _ _
    refine ⟨X.reducedChart ψ' hS inter_subset_right, ψ', X.reducedπ '' ψ'.source,
      isChart_reducedChart hψ' hS inter_subset_right, hψ',
      X.isOpenMap_reducedπ _ ψ'.isOpen_source, ⟨φ, ⟨hφψ, hφ⟩, rfl⟩,
      fun x hx => ⟨image_mono inter_subset_right hx, hx⟩, ?_, ?_⟩
    · rintro _ ⟨φ', hφ', rfl⟩
      change σ (X.src φ') ∈ ψ'.source
      rw [hS.left_inv φ' hφ'.2]
      exact hφ'
    · rw [← X.reducedChart_source ψ' hS inter_subset_right, MChart.image_source]
      refine (isScSmoothRetractMap_id _).congr fun z hz => ?_
      change z = ψ' (σ (X.src (ψ'.symm z)))
      rw [hS.left_inv _ (inter_subset_right (ψ'.symm_mapsTo hz)), ψ'.apply_symm_apply hz]
  mapsTo _ hφ := ⟨_, hφ, rfl⟩
  mapsTo_inv _ hq := sheet_inv_mem hS hq
  left_inv _ hφ := sheet_inv_π hS hφ
  right_inv _ hq := π_sheet_inv hS hq

variable (X)

/-- `π : 𝐗 → 𝐗^R` is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_reducedπ : X.PMor.IsLocalScDiffeo X.reducedPolyfold X.reducedπ :=
  fun φ => by
    obtain ⟨W, V, σ, hφ, hS⟩ := X.isLocalScDiffeo_src φ
    exact ⟨W, _, _, hφ, isScDiffeoOn_reducedπ hS⟩

theorem isScSmoothMap_reducedπ : X.PMor.IsScSmoothMap X.reducedPolyfold X.reducedπ :=
  X.isLocalScDiffeo_reducedπ.isScSmoothMap

/-! ### Proposition 7.10: the reduced ep-groupoid `X_R = (X, 𝐗^R)` -/

variable {X}

/-- On a sheet `s : W → V`, `s : π(W) → V` is an sc-diffeomorphism with inverse `π ∘ σ`
(p. 243, `s(Ψ_φ(φ')) = s_X(φ')`). -/
theorem isScDiffeoOn_reducedSrc (hS : X.PMor.IsScDiffeoOn X.PObj X.src σ W V) :
    X.reducedPolyfold.IsScDiffeoOn X.PObj X.reducedSrc (fun y => X.reducedπ (σ y))
      (X.reducedπ '' W) V where
  isScSmoothOn := by
    have hπ := isScDiffeoOn_reducedπ hS
    refine (MPolyfold.IsScSmoothOn.comp hS.isScSmoothOn hπ.isScSmoothOn_inv
      hπ.mapsTo_inv).congr fun q hq => ?_
    exact hS.right_inv _ (mapsTo_reducedSrc_image hS hq)
  isScSmoothOn_inv := MPolyfold.IsScSmoothOn.comp (isScDiffeoOn_reducedπ hS).isScSmoothOn
    hS.isScSmoothOn_inv hS.mapsTo_inv
  mapsTo := mapsTo_reducedSrc_image hS
  mapsTo_inv _ hy := ⟨_, hS.mapsTo_inv hy, rfl⟩
  left_inv _ hq := π_sheet_inv hS hq
  right_inv y hy := hS.right_inv y hy

/-- On a sheet `S` (Definition 7.1.4 (2017: 7.4)), `t : π(𝐔) → U(y)` is an sc-diffeomorphism with inverse
`π ∘ (t|𝐔)⁻¹` (p. 243, `t(Ψ_φ(φ')) = t_X(φ')`). -/
theorem isScDiffeoOn_reducedTgt (S : X.Sheet) :
    X.reducedPolyfold.IsScDiffeoOn X.PObj X.reducedTgt (fun y => X.reducedπ (S.tgtInv y))
      (X.reducedπ '' S.carrier) S.tgtSet where
  isScSmoothOn := by
    have hπ := isScDiffeoOn_reducedπ S.isScDiffeoOn_src
    refine (MPolyfold.IsScSmoothOn.comp S.isScDiffeoOn_tgt.isScSmoothOn hπ.isScSmoothOn_inv
      hπ.mapsTo_inv).congr ?_
    rintro _ ⟨φ, hφ, rfl⟩
    change X.tgt (S.srcInv (X.src φ)) = X.tgt φ
    rw [S.isScDiffeoOn_src.left_inv φ hφ]
  isScSmoothOn_inv := MPolyfold.IsScSmoothOn.comp
    (isScDiffeoOn_reducedπ S.isScDiffeoOn_src).isScSmoothOn S.isScDiffeoOn_tgt.isScSmoothOn_inv
    S.isScDiffeoOn_tgt.mapsTo_inv
  mapsTo := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact S.isScDiffeoOn_tgt.mapsTo hφ
  mapsTo_inv _ hy := ⟨_, S.isScDiffeoOn_tgt.mapsTo_inv hy, rfl⟩
  left_inv := by
    rintro _ ⟨φ, hφ, rfl⟩
    change X.reducedπ (S.tgtInv (X.tgt φ)) = X.reducedπ φ
    rw [S.isScDiffeoOn_tgt.left_inv φ hφ]
  right_inv y hy := S.isScDiffeoOn_tgt.right_inv y hy

variable (X)

/-- **(1)** `s : 𝐗^R → X` is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_reducedSrc : X.reducedPolyfold.IsLocalScDiffeo X.PObj X.reducedSrc :=
  fun q => by
    obtain ⟨φ, rfl⟩ := X.surjective_reducedπ q
    obtain ⟨W, V, σ, hφ, hS⟩ := X.isLocalScDiffeo_src φ
    exact ⟨X.reducedπ '' W, V, _, ⟨φ, hφ, rfl⟩, isScDiffeoOn_reducedSrc hS⟩

/-- **(1)** `t : 𝐗^R → X` is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_reducedTgt : X.reducedPolyfold.IsLocalScDiffeo X.PObj X.reducedTgt :=
  fun q => by
    obtain ⟨φ, rfl⟩ := X.surjective_reducedπ q
    exact ⟨X.reducedπ '' (X.sheetAt φ).carrier, _, _, ⟨φ, X.mem_sheetAt φ, rfl⟩,
      isScDiffeoOn_reducedTgt (X.sheetAt φ)⟩

/-- **(2)** `u` is sc-smooth: `u = π ∘ u_X`. -/
theorem isScSmoothMap_reducedUnit : X.PObj.IsScSmoothMap X.reducedPolyfold X.reducedUnit :=
  X.isScSmoothMap_reducedπ.comp X.isScSmoothMap_unit

/-- **(2)** `ι` is sc-smooth: on `π(W)`, `ι = π ∘ ι_X ∘ σ ∘ s`. -/
theorem isScSmoothMap_reducedInv :
    X.reducedPolyfold.IsScSmoothMap X.reducedPolyfold X.reducedInv :=
  isScSmoothOn_of_local' isOpen_univ fun q _ => by
    obtain ⟨φ, rfl⟩ := X.surjective_reducedπ q
    obtain ⟨W, V, σ, hφ, hS⟩ := X.isLocalScDiffeo_src φ
    have hπ := isScDiffeoOn_reducedπ hS
    refine ⟨X.reducedπ '' W, ⟨φ, hφ, rfl⟩, (MPolyfold.IsScSmoothOn.comp
      (X.isScSmoothMap_reducedπ.comp X.isScSmoothMap_inv) hπ.isScSmoothOn_inv
      (mapsTo_univ _ _)).congr fun q' hq' => ?_⟩
    conv_rhs => rw [← π_sheet_inv hS hq']
    rfl

/-- **(4)** in the sheet form: for an sc-diffeomorphism `s : W' → V'` of `𝐗^R` with inverse `σ'`,
`ψ ↦ σ'(t ψ) ∘ ψ` is sc-smooth on `t⁻¹(V')`.  Near `[ψ₀]` it is `π ∘ G ∘ σ₁ ∘ s` with
`G(ψ) = κ(t ψ) ∘ ψ` for the sheet inverse `κ = σ₂ ∘ s ∘ σ'` of `s` in `𝐗`, sc-smooth by (4)
for `X`. -/
theorem isScSmoothCompSheet_reduced :
    IsScSmoothCompSheet X.PObj X.reducedPolyfold X.reducedSrc X.reducedTgt X.reducedComp := by
  intro σ' W' V' hd
  refine isScSmoothOn_of_local'
    (hd.isScSmoothOn_inv.isOpen.preimage X.continuous_reducedTgt) fun q₀ hq₀ => ?_
  obtain ⟨ψ₀, rfl⟩ := X.surjective_reducedπ q₀
  obtain ⟨φ₀, hφ₀⟩ := X.surjective_reducedπ (σ' (X.tgt ψ₀))
  have h₁ := (X.sheetAt ψ₀).isScDiffeoOn_src
  have h₂ := (X.sheetAt φ₀).isScDiffeoOn_src
  have hπ₁ := isScDiffeoOn_reducedπ h₁
  have hπ₂ := isScDiffeoOn_reducedπ h₂
  -- `V'' = V' ∩ σ'⁻¹(π(W₂))` and the section `κ = σ₂ ∘ s ∘ σ'` of `s` over `V''`
  set V'' := V' ∩ σ' ⁻¹' (X.reducedπ '' (X.sheetAt φ₀).carrier) with hV''
  have hV''o : IsOpen V'' := hd.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage
    hd.isScSmoothOn_inv.isOpen (X.isOpenMap_reducedπ _ h₂.isScSmoothOn.isOpen)
  set κ : Obj → Mor := fun y => (X.sheetAt φ₀).srcInv (X.reducedSrc (σ' y)) with hκ
  have hκsm : X.PObj.IsScSmoothOn X.PMor κ V'' := MPolyfold.IsScSmoothOn.comp (f := σ')
    hπ₂.isScSmoothOn_inv (hd.isScSmoothOn_inv.mono hV''o inter_subset_left) fun y hy => hy.2
  have hκπ : ∀ y ∈ V'', X.reducedπ (κ y) = σ' y := fun y hy => π_sheet_inv h₂ hy.2
  have hκs : ∀ y ∈ V'', X.src (κ y) = y := fun y hy => by
    rw [← reducedSrc_π, hκπ y hy]
    exact hd.right_inv y hy.1
  -- `κ` is the inverse of `s : W'' → V''`, `W'' = W₂ ∩ π⁻¹(W') ∩ s⁻¹(V'')`
  have hW''o : IsOpen ((X.sheetAt φ₀).carrier ∩ X.reducedπ ⁻¹' W' ∩ X.src ⁻¹' V'') :=
    (h₂.isScSmoothOn.isOpen.inter (hd.isScSmoothOn.isOpen.preimage X.continuous_reducedπ)).inter
      (hV''o.preimage X.continuous_src)
  have hdiff : X.PMor.IsScDiffeoOn X.PObj X.src κ
      ((X.sheetAt φ₀).carrier ∩ X.reducedπ ⁻¹' W' ∩ X.src ⁻¹' V'') V'' :=
    { isScSmoothOn := X.isScSmoothMap_src.mono hW''o (subset_univ _)
      isScSmoothOn_inv := hκsm
      mapsTo := fun _ hφ => hφ.2
      mapsTo_inv := fun y hy => ⟨⟨sheet_inv_mem h₂ hy.2, by
          rw [mem_preimage, hκπ y hy]; exact hd.mapsTo_inv hy.1⟩, by
        rw [mem_preimage, hκs y hy]; exact hy⟩
      left_inv := fun φ hφ => by
        change (X.sheetAt φ₀).srcInv (X.reducedSrc (σ' (X.reducedSrc (X.reducedπ φ)))) = φ
        rw [hd.left_inv _ hφ.1.2, reducedSrc_π]
        exact h₂.left_inv φ hφ.1.1
      right_inv := hκs }
  have hG := X.isScSmoothCompSheet κ _ V'' hdiff
  -- the neighbourhood `N = π(W₁) ∩ t⁻¹(V'')` of `[ψ₀]`
  have hNo : IsOpen (X.reducedπ '' (X.sheetAt ψ₀).carrier ∩ X.reducedTgt ⁻¹' V'') :=
    (X.isOpenMap_reducedπ _ h₁.isScSmoothOn.isOpen).inter
      (hV''o.preimage X.continuous_reducedTgt)
  refine ⟨X.reducedπ '' (X.sheetAt ψ₀).carrier ∩ X.reducedTgt ⁻¹' V'',
    ⟨⟨ψ₀, X.mem_sheetAt ψ₀, rfl⟩, hq₀, ?_⟩, ?_⟩
  · rw [mem_preimage, reducedTgt_π, ← hφ₀]
    exact ⟨φ₀, X.mem_sheetAt φ₀, rfl⟩
  have hmaps : MapsTo (fun q => (X.sheetAt ψ₀).srcInv (X.reducedSrc q))
      (X.reducedπ '' (X.sheetAt ψ₀).carrier ∩ X.reducedTgt ⁻¹' V'') (X.tgt ⁻¹' V'') := by
    rintro _ ⟨⟨ψ, hψ, rfl⟩, hV⟩
    change X.tgt ((X.sheetAt ψ₀).srcInv (X.src ψ)) ∈ V''
    rw [h₁.left_inv ψ hψ]
    exact hV
  refine (MPolyfold.IsScSmoothOn.comp X.isScSmoothMap_reducedπ
    (MPolyfold.IsScSmoothOn.comp hG (hπ₁.isScSmoothOn_inv.mono hNo inter_subset_left) hmaps)
    (mapsTo_univ _ _)).congr ?_
  rintro _ ⟨⟨ψ, hψ, rfl⟩, hV⟩
  change X.reducedπ (X.comp (κ (X.tgt ((X.sheetAt ψ₀).srcInv (X.src ψ))))
    ((X.sheetAt ψ₀).srcInv (X.src ψ))) = X.reducedComp (σ' (X.tgt ψ)) (X.reducedπ ψ)
  rw [h₁.left_inv ψ hψ, ← hκπ (X.tgt ψ) hV, X.reducedComp_π (hκs (X.tgt ψ) hV)]

/-- **Proposition 7.10, the structure**: the reduced ep-groupoid `X_R = (X, 𝐗^R)`, with the
structure maps of `X` descended to `𝐗^R` (p. 243). -/
def reducedEpGroupoid : EpGroupoid Obj X.ReducedMor where
  toGroupoidStr := X.reducedGroupoidStr
  PObj := X.PObj
  PMor := X.reducedPolyfold
  isLocalScDiffeo_src := X.isLocalScDiffeo_reducedSrc
  isLocalScDiffeo_tgt := X.isLocalScDiffeo_reducedTgt
  isScSmoothMap_unit := X.isScSmoothMap_reducedUnit
  isScSmoothMap_inv := X.isScSmoothMap_reducedInv
  exists_isProperMap := X.exists_isProperMap_reduced
  isScSmoothComp := (isScSmoothComp_iff_sheet _ _).2 X.isScSmoothCompSheet_reduced

/-- **The reduction functor** `X → X_R`: the identity on objects and `π` on morphisms, a
morphism of `EP` (Definition 7.1.7 (2017: 7.7)). -/
def reductionFunctor : EpFunctor X X.reducedEpGroupoid where
  obj := id
  mor := X.reducedπ
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ h := (X.reducedComp_π h).symm
  mor_unit _ := rfl
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_id
  isScSmoothMap_mor := X.isScSmoothMap_reducedπ

/-- **Proposition 7.10**: `X_R` is effective (p. 244).  If `s = t` near `[g]` in `𝐗^R`, then
`s = t` near `g` in `𝐗`, so `g ∈ T_x` and `[g] = [1_x]`. -/
theorem isEffective_reducedEpGroupoid : X.reducedEpGroupoid.IsEffective := by
  intro x τ hτ O hO hτO
  by_contra hne
  push Not at hne
  apply hτ
  obtain ⟨g, hg⟩ := X.surjective_reducedπ τ.val
  have hgt : X.tgt g = x := by
    rw [← reducedTgt_π, hg]
    exact τ.tgt_val
  have hT : g ∈ X.nonEffectivePart := X.mem_nonEffectivePart_iff.2 (by
    filter_upwards [(hO.preimage X.continuous_reducedπ).mem_nhds
      (show g ∈ X.reducedπ ⁻¹' O by rw [mem_preimage, hg]; exact hτO)] with ψ hψ
    exact hne _ hψ)
  refine GroupoidStr.Isotropy.ext ?_
  change τ.val = X.reducedπ (X.unit x)
  rw [← hg, X.reducedπ_eq_iff]
  exact reducedRel_iff.2 ⟨g, hT, by rw [X.src_unit, hgt],
    (GroupoidStr.unit_comp_of_eq hgt).symm⟩

end ReducedPolyfold

/-! ### The isotropy of `X_R`: `G_x/T_x` (p. 244) and Definition 7.2.15 (2017: 7.13) -/

/-- `G_x → G̃_x`, `g ↦ [g]`, onto the isotropy group of `x` in `(X, 𝐗^R)`. -/
def reducedIsotropyHom (x : Obj) : X.Isotropy x →* X.reducedGroupoidStr.Isotropy x where
  toFun g := ⟨X.reducedπ g.val, g.src_val, g.tgt_val⟩
  map_one' := rfl
  map_mul' g h :=
    GroupoidStr.Isotropy.ext (X.reducedComp_π (g.src_val.trans h.tgt_val.symm)).symm

theorem surjective_reducedIsotropyHom (x : Obj) : Surjective (X.reducedIsotropyHom x) := by
  intro τ
  obtain ⟨φ, hφ⟩ := X.surjective_reducedπ τ.val
  have hs : X.src φ = x := by rw [← reducedSrc_π, hφ]; exact τ.src_val
  have ht : X.tgt φ = x := by rw [← reducedTgt_π, hφ]; exact τ.tgt_val
  exact ⟨⟨φ, hs, ht⟩, GroupoidStr.Isotropy.ext hφ⟩

/-- **`[1_x] = T_x`** (p. 244): the kernel of `g ↦ [g]` is `T_x`. -/
theorem ker_reducedIsotropyHom (x : Obj) :
    (X.reducedIsotropyHom x).ker = X.trivialSubgroup x := by
  ext g
  rw [MonoidHom.mem_ker, mem_trivialSubgroup, ← val_mem_nonEffectivePart_iff]
  constructor
  · intro h
    have h' : X.reducedπ g.val = X.reducedπ (X.unit x) := congrArg GroupoidStr.Isotropy.val h
    obtain ⟨k, hk, hc, he⟩ := reducedRel_iff.1 (X.reducedπ_eq_iff.1 h')
    rw [he, GroupoidStr.unit_comp_of_eq (hc.symm.trans (X.src_unit x))]
    exact hk
  · intro h
    refine GroupoidStr.Isotropy.ext ?_
    change X.reducedπ g.val = X.reducedπ (X.unit x)
    exact X.reducedπ_eq_iff.2 (reducedRel_iff.2 ⟨g.val, h, by rw [X.src_unit, g.tgt_val],
      (GroupoidStr.unit_comp_of_eq g.tgt_val).symm⟩)

/-- **The isotropy group of `x` in `(X, 𝐗^R)` is `G_x/T_x`** (p. 244). -/
def quotientTrivialSubgroupEquiv (x : Obj) :
    X.Isotropy x ⧸ X.trivialSubgroup x ≃* X.reducedGroupoidStr.Isotropy x :=
  (QuotientGroup.quotientMulEquivOfEq (X.ker_reducedIsotropyHom x).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (X.surjective_reducedIsotropyHom x))

theorem quotientTrivialSubgroupEquiv_mk (x : Obj) (g : X.Isotropy x) :
    (X.quotientTrivialSubgroupEquiv x (QuotientGroup.mk g)).val = X.reducedπ g.val :=
  rfl

/-- **Definition 7.2.15 (2017: 7.13)**: the effective isotropy group `G_x^eff = G_x/T_x` is the isotropy group
of `x` in `(X, 𝐗^R)`. -/
def effIsotropyEquivReduced (x : Obj) : X.EffIsotropy x ≃* X.reducedGroupoidStr.Isotropy x :=
  (X.effIsotropyEquiv x).trans (X.quotientTrivialSubgroupEquiv x)

/-! ### Propositions 7.9 and 7.10 -/

section Statements

variable [T2Space X.ReducedMor] [ParacompactSpace X.ReducedMor]

/-- **Proposition 7.2.10 (2017: 7.9)** (p. 313 (2017 p. 242)): `𝐗^R` has a natural M-polyfold structure (`reducedPolyfold`;
Hausdorff and paracompact are hypotheses, PLAN P7).  Its atlas is the set of the charts `Ψ_φ`
from sheets of `s` (pairwise sc-smoothly compatible, `reducedChart_compatible`), all of them
charts of the structure; on every sheet `s : W → V` (inverse `σ`), `π(W)` is open and
`π : W → π(W)` is an sc-diffeomorphism with inverse `σ ∘ s`; `π : 𝐗 → 𝐗^R` is a local
sc-diffeomorphism. -/
theorem proposition_7_2_10 :
    X.reducedPolyfold.atlas.charts = X.reducedCharts ∧
    (∀ χ ∈ X.reducedCharts, X.reducedPolyfold.IsChart χ) ∧
    (∀ (σ : Obj → Mor) (W : Set Mor) (V : Set Obj), X.PMor.IsScDiffeoOn X.PObj X.src σ W V →
      IsOpen (X.reducedπ '' W) ∧ X.PMor.IsScDiffeoOn X.reducedPolyfold X.reducedπ
        (fun q => σ (X.reducedSrc q)) W (X.reducedπ '' W)) ∧
    X.PMor.IsLocalScDiffeo X.reducedPolyfold X.reducedπ :=
  ⟨rfl, fun _ hχ => X.reducedPolyfold.isChart_of_mem hχ,
    fun _ _ _ hS => ⟨X.isOpenMap_reducedπ _ hS.isScSmoothOn.isOpen, isScDiffeoOn_reducedπ hS⟩,
    X.isLocalScDiffeo_reducedπ⟩

/-- **Proposition 7.10** (p. 244): the reduced ep-groupoid `X_R = (X, 𝐗^R)`
(`reducedEpGroupoid`: the groupoid `reducedGroupoidStr`, the object M-polyfold of `X`, the
morphism M-polyfold `reducedPolyfold`) is effective, its isotropy group at `x` is `G_x/T_x`, and
`π` is a functor `X → X_R` in `EP` (`reductionFunctor`). -/
theorem proposition_7_10_2017 :
    X.reducedEpGroupoid.toGroupoidStr = X.reducedGroupoidStr ∧
    X.reducedEpGroupoid.PObj = X.PObj ∧ X.reducedEpGroupoid.PMor = X.reducedPolyfold ∧
    X.reducedEpGroupoid.IsEffective ∧
    (∀ x, Nonempty (X.Isotropy x ⧸ X.trivialSubgroup x ≃* X.reducedEpGroupoid.Isotropy x)) ∧
    Nonempty (EpFunctor X X.reducedEpGroupoid) :=
  ⟨rfl, rfl, rfl, X.isEffective_reducedEpGroupoid, fun x => ⟨X.quotientTrivialSubgroupEquiv x⟩,
    ⟨X.reductionFunctor⟩⟩

end Statements

/-! ### Satisfiability: effective ep-groupoids (PLAN II.5, 7) -/

section Effective

variable {X}

/-- For effective `X`, `∼` is equality. -/
theorem reducedRel_iff_eq_of_isEffective (hX : X.IsEffective) {φ φ' : Mor} :
    X.ReducedRel φ φ' ↔ φ = φ' := by
  refine ⟨fun h => ?_, fun h => h ▸ X.reducedRel_refl φ⟩
  obtain ⟨k, hk, hc, rfl⟩ := reducedRel_iff.1 h
  obtain ⟨x, g, hg, rfl⟩ := hk
  obtain rfl : g = 1 :=
    (Subgroup.eq_bot_iff_forall _).1 (X.isEffective_iff_trivialSubgroup_eq_bot.1 hX x) g hg
  exact GroupoidStr.comp_unit_of_eq (hc.trans (X.tgt_unit x))

theorem injective_reducedπ_of_isEffective (hX : X.IsEffective) : Injective X.reducedπ :=
  fun _ _ h => (reducedRel_iff_eq_of_isEffective hX).1 (X.reducedπ_eq_iff.1 h)

/-- **For effective `X`, `π : 𝐗 → 𝐗^R` is a homeomorphism.** -/
def reducedHomeomorph (hX : X.IsEffective) : Mor ≃ₜ X.ReducedMor :=
  (Equiv.ofBijective X.reducedπ ⟨injective_reducedπ_of_isEffective hX,
    X.surjective_reducedπ⟩).toHomeomorphOfContinuousOpen X.continuous_reducedπ
    X.isOpenMap_reducedπ

@[simp]
theorem reducedHomeomorph_apply (hX : X.IsEffective) (φ : Mor) :
    reducedHomeomorph hX φ = X.reducedπ φ :=
  rfl

theorem reducedHomeomorph_symm_π (hX : X.IsEffective) (φ : Mor) :
    (reducedHomeomorph hX).symm (X.reducedπ φ) = φ :=
  (reducedHomeomorph hX).symm_apply_apply φ

theorem π_reducedHomeomorph_symm (hX : X.IsEffective) (q : X.ReducedMor) :
    X.reducedπ ((reducedHomeomorph hX).symm q) = q :=
  (reducedHomeomorph hX).apply_symm_apply q

/-- **The hypotheses hold for effective `X`**: `𝐗^R` is Hausdorff. -/
theorem t2Space_reducedMor_of_isEffective (hX : X.IsEffective) : T2Space X.ReducedMor :=
  (reducedHomeomorph hX).symm.isEmbedding.t2Space

/-- **The hypotheses hold for effective `X`**: `𝐗^R` is paracompact. -/
theorem paracompactSpace_reducedMor_of_isEffective (hX : X.IsEffective) :
    ParacompactSpace X.ReducedMor :=
  (reducedHomeomorph hX).symm.isClosedEmbedding.paracompactSpace

/-- For effective `X`, `𝐗^R` is regular (`𝐗` is metrizable, Theorem 2.3.10 (2017: 2.2) [2.16]). -/
theorem t3Space_reducedMor_of_isEffective (hX : X.IsEffective) : T3Space X.ReducedMor := by
  have := X.PMor.metrizableSpace
  exact (reducedHomeomorph hX).symm.isEmbedding.t3Space

variable [T2Space X.ReducedMor] [ParacompactSpace X.ReducedMor]

/-- For effective `X`, the inverse `π⁻¹ : X_R → X` of the reduction functor. -/
def reductionInv (hX : X.IsEffective) : EpFunctor X.reducedEpGroupoid X where
  obj := id
  mor := (reducedHomeomorph hX).symm
  src_mor q := by
    conv_rhs => rw [← π_reducedHomeomorph_symm hX q]
    rfl
  tgt_mor q := by
    conv_rhs => rw [← π_reducedHomeomorph_symm hX q]
    rfl
  mor_comp a b h := by
    obtain ⟨φ, rfl⟩ := X.surjective_reducedπ a
    obtain ⟨ψ, rfl⟩ := X.surjective_reducedπ b
    change X.reducedSrc (X.reducedπ φ) = X.reducedTgt (X.reducedπ ψ) at h
    rw [reducedSrc_π, reducedTgt_π] at h
    change (reducedHomeomorph hX).symm (X.reducedComp (X.reducedπ φ) (X.reducedπ ψ)) = _
    rw [X.reducedComp_π h, reducedHomeomorph_symm_π, reducedHomeomorph_symm_π,
      reducedHomeomorph_symm_π]
  mor_unit x := reducedHomeomorph_symm_π hX (X.unit x)
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_id
  isScSmoothMap_mor := isScSmoothOn_of_local' isOpen_univ fun q _ => by
    obtain ⟨φ, rfl⟩ := X.surjective_reducedπ q
    obtain ⟨W, V, σ, hφ, hS⟩ := X.isLocalScDiffeo_src φ
    refine ⟨X.reducedπ '' W, ⟨φ, hφ, rfl⟩,
      (isScDiffeoOn_reducedπ hS).isScSmoothOn_inv.congr ?_⟩
    rintro _ ⟨φ', hφ', rfl⟩
    change σ (X.src φ') = (reducedHomeomorph hX).symm (X.reducedπ φ')
    rw [reducedHomeomorph_symm_π, hS.left_inv φ' hφ']

/-- **For effective `X`, `X ≅ X_R`** in the category `EP` (Definition 7.1.7 (2017: 7.7)): the reduction functor
is an isomorphism. -/
def reductionIso (hX : X.IsEffective) :
    (⟨Obj, Mor, X⟩ : EP.{u}) ≅ ⟨Obj, X.ReducedMor, X.reducedEpGroupoid⟩ where
  hom := X.reductionFunctor
  inv := reductionInv hX
  hom_inv_id := EpFunctor.ext rfl (funext fun φ => reducedHomeomorph_symm_π hX φ)
  inv_hom_id := EpFunctor.ext rfl (funext fun q => π_reducedHomeomorph_symm hX q)

end Effective

/-- **Satisfiability** (PLAN II.5, 7): the trivial ep-groupoid of every M-polyfold is effective
(`isEffective_trivial`), so its `𝐗^R` is Hausdorff. -/
theorem t2Space_reducedMor_trivial {Z : Type u} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] (P : MPolyfold Z) : T2Space (trivial P).ReducedMor :=
  t2Space_reducedMor_of_isEffective (isEffective_trivial P)

/-- **Satisfiability** (PLAN II.5, 7): the `𝐗^R` of the trivial ep-groupoid is paracompact. -/
theorem paracompactSpace_reducedMor_trivial {Z : Type u} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] (P : MPolyfold Z) : ParacompactSpace (trivial P).ReducedMor :=
  paracompactSpace_reducedMor_of_isEffective (isEffective_trivial P)

/-- **Paracompactness from regularity**: if `𝐗^R` is regular (`T3`) and `𝐗` is second countable,
then `𝐗^R` is second countable (an open quotient), hence metrizable (Urysohn) and paracompact. -/
theorem paracompactSpace_reducedMor_of_t3 [T3Space X.ReducedMor] [SecondCountableTopology Mor] :
    ParacompactSpace X.ReducedMor := by
  have : SecondCountableTopology X.ReducedMor :=
    X.isQuotientMap_reducedπ.secondCountableTopology X.isOpenMap_reducedπ
  have := TopologicalSpace.metrizableSpace_of_t3_secondCountable X.ReducedMor
  exact paracompactSpace_of_metrizableSpace _

end EpGroupoid

end Polyfold
