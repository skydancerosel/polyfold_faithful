import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_24

/-! Round trip for V11_24 (2021 Theorem 11.3.8, pp. 541–542: boundaries `∂Θ` under generalized
isomorphisms, (11.11)).

The item lists eight theorems; `A` is the conjunction of their types, universes at `0` (the two
M-polyfold lemmas have two universe parameters, both set to `0`):
1. `MPolyfold.IsTangentReducedAt.image_of_isScDiffeoOn`,
2. `MPolyfold.isTangentReducedAt_image_iff_of_isScDiffeoOn`,
3. `MPolyfold.mem_submanifoldBoundary_image_iff_of_isScDiffeoOn` (`f(a) ∈ ∂f(M)` iff `a ∈ ∂M`,
   the project's reading of "`d_M(x)` is being preserved"),
4. `EpGroupoid.boundaryTheta_apply_of_isScDiffeoOn` (`∂Θ'(f x) = ∂Θ(x)` for a local
   sc-diffeomorphism `f` with `Θ' ∘ f = Θ`),
5. `EpFunctor.boundaryTheta_pushforwardTheta`, 6. `EpFunctor.boundaryTheta_pullbackTheta`
   ((11.11) for an equivalence),
7. `EPLoc.theorem_11_3_8_push`, 8. `EPLoc.theorem_11_3_8_pull` ((11.11) for a generalized
   isomorphism, `f_*`, `f^*` on the chosen representative).
Every one of 4–8 assumes `HasIndependentTangentSums Θ` (Theorem 9.2.1's independence of the
local branching structure), which the project carries as a hypothesis throughout Chapters 9–11.

`B = BoundaryB ∧ DegPreservedB`: (11.11) on every representative `d` of a generalized isomorphism
for every branched ep⁺-subgroupoid (no independence hypothesis), and `d_{g(M)}(g z) = d_M(z)` for
sub-M-polyfolds `M` and the local sc-diffeomorphisms `g = ψ̂ ∘ F`.

* `A → B` fails, for two reasons.  (i) `BoundaryB` has no `HasIndependentTangentSums`
  hypothesis.  `boundaryTheta` is read off `tangentValue`, a *chosen* local branching structure
  (`Nonempty.some`), and without the independence the chosen structures at `y` and at the moved
  point are unrelated, so `A`'s theorems cannot be applied; the independence is Theorem 9.2.1,
  which the project proves only in special cases (`hasIndependentTangentSums_of_isOfDim`,
  `..._rn`, `..._of_proposition_9_1_12` with Proposition 9.1.12 stated, not proved).
  `A_to_BoundaryB_ind` proves `BoundaryB` from `A` once the independence is added for `Θ`, `Θ'`.
  (ii) `DegPreservedB` asks for equality of the degeneracy indices `d_M` of sub-M-polyfolds;
  `A` has only `d_M ≥ 1 ↔ d_{f(M)} ≥ 1` (item 3), and only for smooth submanifolds.  The equality
  is Proposition 2.24 for the induced structures (an sc-diffeomorphism restricts to one between
  the sub-M-polyfolds), true but not in the project as a lemma.
* `B → A` is proved.  7, 8 come from `BoundaryB` with `d = rep f` (`homMk_rep`), 5, 6 from
  `BoundaryB` applied to the diagram `X ←id X →F Y` (a generalized isomorphism by
  `theorem_10_3_10`; for 6 the identity push-forward is removed by
  `pushforwardTheta_pullbackTheta`), all without using the independence hypothesis that `A`
  grants.  1–4 are local statements about sc-diffeomorphisms between open subsets of two
  M-polyfolds, not consequences of `B` (`DegPreservedB` concerns only the maps `ψ̂ ∘ F` of
  equivalences and sub-M-polyfolds, and does not give the tangent-reduced statements 1, 2); they
  are re-proved outright below by the project's proofs, copied, from non-item lemmas. -/

namespace RoundTrip.V11_24
open Polyfold Polyfold.EPLocalization Set Function

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.IsTangentReducedAt.image_of_isScDiffeoOn.{0, 0}) ∧
  (type_of% @Polyfold.MPolyfold.isTangentReducedAt_image_iff_of_isScDiffeoOn.{0, 0}) ∧
  (type_of% @Polyfold.MPolyfold.mem_submanifoldBoundary_image_iff_of_isScDiffeoOn.{0, 0}) ∧
  (type_of% @Polyfold.EpGroupoid.boundaryTheta_apply_of_isScDiffeoOn.{0}) ∧
  (type_of% @Polyfold.EpFunctor.boundaryTheta_pushforwardTheta.{0}) ∧
  (type_of% @Polyfold.EpFunctor.boundaryTheta_pullbackTheta.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.theorem_11_3_8_push.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.theorem_11_3_8_pull.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.IsTangentReducedAt.image_of_isScDiffeoOn.{0, 0},
    @Polyfold.MPolyfold.isTangentReducedAt_image_iff_of_isScDiffeoOn.{0, 0},
    @Polyfold.MPolyfold.mem_submanifoldBoundary_image_iff_of_isScDiffeoOn.{0, 0},
    @Polyfold.EpGroupoid.boundaryTheta_apply_of_isScDiffeoOn.{0},
    @Polyfold.EpFunctor.boundaryTheta_pushforwardTheta.{0},
    @Polyfold.EpFunctor.boundaryTheta_pullbackTheta.{0},
    @Polyfold.EPLocalization.EPLoc.theorem_11_3_8_push.{0},
    @Polyfold.EPLocalization.EPLoc.theorem_11_3_8_pull.{0}⟩

/-! ### `A → B` with Theorem 9.2.1's independence added -/

/-- `BoundaryB` with `HasIndependentTangentSums` added for `Θ` and `Θ'` (the hypothesis every
theorem of `A` carries). -/
def BoundaryB_ind : Prop :=
  ∀ (X Y : EP.{0}) (f : EPLoc.of X ⟶ EPLoc.of Y), EPLoc.IsGeneralizedIso f →
    ∀ d : Diagram X Y, EPLoc.homMk d = f →
      (∀ Θ : X.Obj → ℚ, X.X.IsBranchedEpSubgroupoid Θ → X.X.HasIndependentTangentSums Θ →
        d.pushTheta (X.X.boundaryTheta Θ) = Y.X.boundaryTheta (d.pushTheta Θ)) ∧
      (∀ Θ' : Y.Obj → ℚ, Y.X.IsBranchedEpSubgroupoid Θ' → Y.X.HasIndependentTangentSums Θ' →
        d.pullTheta (Y.X.boundaryTheta Θ') = X.X.boundaryTheta (d.pullTheta Θ'))

theorem A_to_BoundaryB_ind : A → BoundaryB_ind := by
  rintro ⟨-, -, -, -, -, -, hpush, hpull⟩ X Y f hf d hd
  subst hd
  have hΦ : d.Φ.IsEquivalence := (EPLoc.theorem_10_3_10 d).1.1 hf
  refine ⟨fun Θ hΘ hind => ?_, fun Θ' hΘ' hind' => ?_⟩
  · rw [← EPLoc.pushTheta_homMk d hΦ (X.X.isFunctorial_boundaryTheta hΘ hind), hpush hf hΘ hind,
      EPLoc.pushTheta_homMk d hΦ hΘ.isFunctorial]
  · rw [← EPLoc.pullTheta_homMk d (Y.X.isFunctorial_boundaryTheta hΘ' hind'), hpull hf hΘ' hind',
      EPLoc.pullTheta_homMk d hΘ'.isFunctorial]

/-! ### `B → A`: items 1–4 re-proved outright (the project's proofs, copied) -/

section Copies

open MPolyfold

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

theorem tangentReduced_image' {f : X → Y} {g : Y → X} {U : Set X}
    {U' : Set Y} (hf : P.IsScDiffeoOn Q f g U U') {A : Set X}
    (hfA : Q.IsSmoothSubmanifold (f '' A)) (hAU : A ⊆ U) {a : X}
    (h : P.IsTangentReducedAt A a) : Q.IsTangentReducedAt (f '' A) (f a) := by
  obtain ⟨haA, d, -, -, -, -, -, haV, -⟩ := id h
  have hfaA : f a ∈ f '' A := ⟨a, haA, rfl⟩
  obtain ⟨ψ, hψ, hfaψ⟩ := Q.exists_isChart_mem_source (f a)
  obtain ⟨n, W, T, hT⟩ := ψ.model.isPartialQuadrant
  set χ := transportChart hf ψ with hχdef
  have hχ : P.IsChart χ := transportChart_isChart hf hψ
  have haχ : a ∈ χ.source := ⟨hAU haA, hfaψ⟩
  have hfa1 : f a ∈ Q.levelSet 1 := hfA.mem_levelSet_one hfaA
  have hz : ψ.model.E.toBase 1 (levelLift ψ 1 (f a)) = ψ (f a) :=
    Q.toBase_levelLift hψ hfaψ hfa1
  have hred := h.isReducedChart d hχ T hT haV haχ hz
  set G := f '' d.toSubData.shrink χ with hGdef
  have hWU : d.toSubData.shrink χ ⊆ U := fun x hx => (d.toSubData.shrink_subset_source χ hx).1
  have hinj : InjOn f U := fun x hx x' hx' hxx' => by
    rw [← hf.left_inv x hx, ← hf.left_inv x' hx', hxx']
  have himg : χ '' (d.toSubData.shrink χ ∩ A) = ψ '' (G ∩ f '' A) := by
    change (ψ ∘ f) '' _ = _
    rw [image_comp, hinj.image_inter hWU hAU]
  have hred' : IsReducedTangentAt ψ.model.E ψ.model.C (ψ '' (G ∩ f '' A)) T
      (levelLift ψ 1 (f a)) := by
    rw [← himg]; exact hred
  set d' := hfA.data hfaA
  have hfaV' : f a ∈ d'.V := hfA.mem_data_V hfaA
  have hG : IsOpen G := hf.isOpen_image_of_subset (d.toSubData.isOpen_shrink χ) hWU
  have hGψ : G ⊆ ψ.source := by
    rintro _ ⟨x, hx, rfl⟩; exact (d.toSubData.shrink_subset_source χ hx).2
  have hQ : IsScRetract ψ.model.E ψ.model.C (ψ '' (G ∩ f '' A)) := by
    rw [← himg]; exact d.toSubData.isScRetract_image χ hχ
  have hzs : levelLift ψ 1 (f a) ∈ ψ.model.E.smoothLvl 1 := by
    change ψ.model.E.toBase 1 _ ∈ (ψ.model.E.smooth : Set (ψ.model.E 0))
    rw [hz]; exact d'.apply_mem_smooth hψ hfaA hfaV' hfaψ
  have hres := isReducedTangentAt_chart_change hψ hψ hG (d'.toSubData.isOpen_shrink ψ) hGψ
    (d'.toSubData.shrink_subset_source ψ) hQ (d'.toSubData.isScRetract_image ψ hψ) hfaA
    ⟨a, d.toSubData.mem_shrink χ haA haV haχ, rfl⟩ (d'.toSubData.mem_shrink ψ hfaA hfaV' hfaψ)
    hz hz hzs T hT T hT hred'
  exact ⟨hfaA, d', ψ, n, W, T, _, hfaV', hψ, hfaψ, hT, hz, hres⟩

theorem tangentReduced_image_iff' {f : X → Y} {g : Y → X} {U : Set X}
    {U' : Set Y} (hf : P.IsScDiffeoOn Q f g U U') {A : Set X} (hA : P.IsSmoothSubmanifold A)
    (hAU : A ⊆ U) {a : X} (ha : a ∈ A) :
    Q.IsTangentReducedAt (f '' A) (f a) ↔ P.IsTangentReducedAt A a := by
  have hfA := hA.image_of_isScDiffeoOn hf hAU
  refine ⟨fun h => ?_, fun h => tangentReduced_image' hf hfA hAU h⟩
  have hgf : g '' (f '' A) = A := by
    rw [image_image]
    exact (image_congr fun y hy => hf.left_inv y (hAU hy)).trans (image_id' A)
  have hfAU' : f '' A ⊆ U' := image_subset_iff.2 fun y hy => hf.mapsTo (hAU hy)
  have := tangentReduced_image' hf.symm (hgf.symm ▸ hA) hfAU' h
  rwa [hgf, hf.left_inv a (hAU ha)] at this

/-- **`∂M` is carried by sc-diffeomorphisms between different M-polyfolds**: `f(a) ∈ ∂(f(A))` iff
`a ∈ ∂A` (the step "`d_M(x)` is being preserved" of the proof of Theorem 11.3.8). -/
theorem mem_boundary_image_iff' {f : X → Y} {g : Y → X} {U : Set X}
    {U' : Set Y} (hf : P.IsScDiffeoOn Q f g U U') {A : Set X} (hA : P.IsSmoothSubmanifold A)
    (hAU : A ⊆ U) {a : X} (haU : a ∈ U) :
    f a ∈ Q.submanifoldBoundary (f '' A) ↔ a ∈ P.submanifoldBoundary A := by
  have hfA := hA.image_of_isScDiffeoOn hf hAU
  have hinj : InjOn f U := fun x hx x' hx' hxx' => by
    rw [← hf.left_inv x hx, ← hf.left_inv x' hx', hxx']
  have hmem : f a ∈ f '' A ↔ a ∈ A := hinj.mem_image_iff hAU haU
  rw [mem_submanifoldBoundary_iff hA, mem_submanifoldBoundary_iff hfA, hmem,
    ← hf.mem_boundary_iff haU]
  constructor
  · rintro ⟨ha, hb, hT⟩
    exact ⟨ha, hb, fun h => hT ((tangentReduced_image_iff' hf hA hAU ha).2 h)⟩
  · rintro ⟨ha, hb, hT⟩
    exact ⟨ha, hb, fun h => hT ((tangentReduced_image_iff' hf hA hAU ha).1 h)⟩


end Copies

section Copies4

open MPolyfold EpGroupoid

variable {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}
  {Θ : Obj → ℚ} {Θ' : Obj' → ℚ} {f : Obj → Obj'} {g : Obj' → Obj} {W : Set Obj} {W' : Set Obj'}

theorem boundaryTheta_apply'
    (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W') (hΘ : ∀ u ∈ W, Θ' (f u) = Θ u)
    (hΘb : X.IsBranchedEpSubgroupoid Θ) (hind : X.HasIndependentTangentSums Θ)
    (hind' : Y.HasIndependentTangentSums Θ') {x : Obj} (hxW : x ∈ W) :
    Y.boundaryTheta Θ' (f x) = X.boundaryTheta Θ x := by
  classical
  by_cases hx : x ∈ supp Θ
  · obtain ⟨B⟩ := hΘb.localBranching _ hx
    set B' := B.mapDiffeo hf hxW rfl hΘ
    rw [Y.boundaryTheta_eq hind' B' B'.mem_U, X.boundaryTheta_eq hind B B.mem_U, Finset.sum_filter,
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hA := (B.isSmoothSubmanifold i).inter_isOpen hf.isScSmoothOn.isOpen
    have hiff : f x ∈ Y.PObj.submanifoldBoundary (B'.M i) ↔
        x ∈ X.PObj.submanifoldBoundary (B.M i) :=
      (mem_boundary_image_iff' hf hA inter_subset_right hxW).trans
        (mem_submanifoldBoundary_inter_isOpen_iff (B.isSmoothSubmanifold i)
          hf.isScSmoothOn.isOpen hxW)
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hiff.1 h1) h2
    · exact absurd (hiff.2 h2) h1
    · rfl
  · have hy : f x ∉ supp Θ' := by change ¬ 0 < Θ' _; rw [hΘ _ hxW]; exact hx
    rw [EpGroupoid.boundaryTheta_eq_zero_of_not_mem_supp hy,
      EpGroupoid.boundaryTheta_eq_zero_of_not_mem_supp hx]

end Copies4

/-! ### `B → A` -/

theorem B_to_A : B → A := by
  rintro ⟨hB, -⟩
  -- (11.11) for an equivalence `F`, from `B` on the diagram `X ←id X →F Y`
  have heqv : ∀ {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj]
      [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
      [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
      [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
      {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {F : EpFunctor X Y},
      F.IsEquivalence →
        let d : Diagram (EP.mk Obj Mor X) (EP.mk Obj' Mor' Y) :=
          ⟨EP.mk Obj Mor X, EpFunctor.id X, EpFunctor.IsEquivalence.id X, F⟩
        (∀ Θ : Obj → ℚ, X.IsBranchedEpSubgroupoid Θ →
          d.pushTheta (X.boundaryTheta Θ) = Y.boundaryTheta (d.pushTheta Θ)) ∧
        (∀ Θ' : Obj' → ℚ, Y.IsBranchedEpSubgroupoid Θ' →
          d.pullTheta (Y.boundaryTheta Θ') = X.boundaryTheta (d.pullTheta Θ')) := by
    intro Obj Mor Obj' Mor' _ _ _ _ _ _ _ _ _ _ _ _ X Y F hF d
    exact hB (EP.mk Obj Mor X) (EP.mk Obj' Mor' Y) (EPLoc.homMk d)
      ((EPLoc.theorem_10_3_10 d).1.2 hF) d rfl
  refine ⟨@tangentReduced_image', @tangentReduced_image_iff', @mem_boundary_image_iff',
    @boundaryTheta_apply', ?_, ?_, ?_, ?_⟩
  · intro Obj Mor Obj' Mor' _ _ _ _ _ _ _ _ _ _ _ _ X Y F hF Θ hΘ _
    exact (heqv hF).1 Θ hΘ
  · intro Obj Mor Obj' Mor' _ _ _ _ _ _ _ _ _ _ _ _ X Y F hF Θ' hΘ' hind'
    have h := (heqv hF).2 Θ' hΘ'
    have hid : ∀ Ψ : Obj → ℚ, X.IsFunctorial Ψ → (EpFunctor.id X).pushforwardTheta Ψ = Ψ :=
      fun Ψ hΨ => EpFunctor.pushforwardTheta_pullbackTheta
        (EpFunctor.IsEquivalence.id X).essSurj hΨ
    change (EpFunctor.id X).pushforwardTheta (F.pullbackTheta (Y.boundaryTheta Θ')) =
      X.boundaryTheta ((EpFunctor.id X).pushforwardTheta (F.pullbackTheta Θ')) at h
    rwa [hid _ (F.isFunctorial_pullbackTheta (Y.isFunctorial_boundaryTheta hΘ' hind')),
      hid _ (F.isFunctorial_pullbackTheta hΘ'.isFunctorial)] at h
  · intro X Y f hf Θ hΘ _
    exact (hB X Y f hf (EPLoc.rep f) (EPLoc.homMk_rep f)).1 Θ hΘ
  · intro X Y f hf Θ' hΘ' _
    exact (hB X Y f hf (EPLoc.rep f) (EPLoc.homMk_rep f)).2 Θ' hΘ'

#rt_check RoundTrip.V11_24.A_to_BoundaryB_ind [Polyfold.MPolyfold.IsTangentReducedAt.image_of_isScDiffeoOn,
  Polyfold.MPolyfold.isTangentReducedAt_image_iff_of_isScDiffeoOn,
  Polyfold.MPolyfold.mem_submanifoldBoundary_image_iff_of_isScDiffeoOn,
  Polyfold.EpGroupoid.boundaryTheta_apply_of_isScDiffeoOn,
  Polyfold.EpFunctor.boundaryTheta_pushforwardTheta,
  Polyfold.EpFunctor.boundaryTheta_pullbackTheta,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_8_push,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_8_pull]
#rt_check RoundTrip.V11_24.B_to_A [Polyfold.MPolyfold.IsTangentReducedAt.image_of_isScDiffeoOn,
  Polyfold.MPolyfold.isTangentReducedAt_image_iff_of_isScDiffeoOn,
  Polyfold.MPolyfold.mem_submanifoldBoundary_image_iff_of_isScDiffeoOn,
  Polyfold.EpGroupoid.boundaryTheta_apply_of_isScDiffeoOn,
  Polyfold.EpFunctor.boundaryTheta_pushforwardTheta,
  Polyfold.EpFunctor.boundaryTheta_pullbackTheta,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_8_push,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_8_pull]
#rt_overlap RoundTrip.V11_24.B_to_A [Polyfold.MPolyfold.IsTangentReducedAt.image_of_isScDiffeoOn,
  Polyfold.MPolyfold.isTangentReducedAt_image_iff_of_isScDiffeoOn,
  Polyfold.MPolyfold.mem_submanifoldBoundary_image_iff_of_isScDiffeoOn,
  Polyfold.EpGroupoid.boundaryTheta_apply_of_isScDiffeoOn,
  Polyfold.EpFunctor.boundaryTheta_pushforwardTheta,
  Polyfold.EpFunctor.boundaryTheta_pullbackTheta,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_8_push,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_8_pull]

end RoundTrip.V11_24
