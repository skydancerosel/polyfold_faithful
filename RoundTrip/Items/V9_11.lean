import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_11

/-! Round trip for V9_11 (§9.2, p. 409; 2017 pp. 297–298: the category `Gr(X)`).

`A` is the conjunction of the types of the six listed theorems, universes at `0`
(`tangentMor_unit_of_eq`, `tangentMor_injOn`, `tangentMor_eq_tangentMapOn_hat`, `grPush_mem`,
`grPush_comp`, `grPush_unit`); `Gr`, `grPush`, `GrObj`, `SmoothCat`, `grProj` are vocabulary.

`B` says the project's `Gr x`, `GrObj` (with its category instance) and `grProj` are the text's
objects, with `B`'s `GrB x`: finitely supported `ℚ`-weights (any sign) on sets `L ⊆ T_xX` that
are finite-dimensional linear subspaces in some chart.  The project's `Gr x` (documented choice,
gap G.7) has **nonnegative** weights on **arbitrary** subsets `L` of vectors over `x`.

* `B` is false (`not_B`): in the trivial ep-groupoid of `ℝ⁰` the formal sum `1 · ∅` lies in
  `Gr x` but not in `GrB x` (a chart image of `∅` is empty, a submodule is not).  (Also
  `(-1) · L` for a genuine subspace `L` lies in `GrB x` but not in `Gr x`.)  Hence `A → B` is
  false (`not_A_to_B`) and `B → A` holds only ex falso.
* What does hold (`B_rest`, proved outright): the four conjuncts of `B` that do not mention
  `GrB` (objects determined by `pt`, `sum`; morphisms `o ⟶ o'` are exactly the `φ` with
  `s φ = o.pt`, `t φ = o'.pt`, `o'.sum = φ_* o.sum`; `π` faithful on morphisms; `π(x, a) = x`),
  and `GrB ∩ {weights ≥ 0} ⊆ Gr` (`nonneg_mem_GrB_to_mem_Gr`).  So the only difference is the
  generators (and sign) of `Gr(x)`. -/

namespace RoundTrip.V9_11
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.tangentMor_unit_of_eq.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tangentMor_injOn.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tangentMor_eq_tangentMapOn_hat.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.grPush_mem.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.grPush_comp.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.grPush_unit.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.tangentMor_unit_of_eq.{0}, @Polyfold.EpGroupoid.tangentMor_injOn.{0},
    @Polyfold.EpGroupoid.tangentMor_eq_tangentMapOn_hat.{0}, @Polyfold.EpGroupoid.grPush_mem.{0},
    @Polyfold.EpGroupoid.grPush_comp.{0}, @Polyfold.EpGroupoid.grPush_unit.{0}⟩

/-! ### `B` is false -/

/-- The empty set of tangent vectors is not a finite-dimensional subspace in any chart. -/
theorem not_isFinDimSubspaceB_empty {Z : Type} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] (P : MPolyfold Z) (y : Z) : ¬ IsFinDimSubspaceB P y ∅ := by
  rintro ⟨-, φ, hφ, -, S, -, hS⟩
  have h0 : (0 : φ.model.E.lvl 0) ∈ (S : Set (φ.model.E.lvl 0)) := S.zero_mem
  rw [← hS, chartImgB, Set.image_empty] at h0
  exact h0

theorem not_B : ¬ B := by
  intro hB
  let X := EpGroupoid.trivial (rnPolyfold 0)
  have hsm : (fun _ => 0 : Fin 0 → ℝ) ∈ X.PObj.smoothSet := by
    change _ ∈ (rnPolyfold 0).smoothSet
    rw [TrivialBundle.rnPolyfold_smoothSet]; exact Set.mem_univ _
  have h := (((hB _ _ X).1 _ hsm (Finsupp.single ∅ 1)).1 ⟨fun L => by
    rw [Finsupp.single_apply]; split_ifs <;> norm_num, fun L _ _ hα => ?_⟩)
  · refine not_isFinDimSubspaceB_empty X.PObj _ (h ∅ ?_)
    exact Finsupp.mem_support_iff.2 (by rw [Finsupp.single_apply, if_pos rfl]; norm_num)
  · have hL : L = ∅ := by
      by_contra hne
      have : (Finsupp.single (∅ : Set X.PObj.TangentSpace) (1 : ℚ)) L ≠ 0 :=
        Finsupp.mem_support_iff.1 ‹_›
      rw [Finsupp.single_apply, if_neg (Ne.symm hne)] at this
      exact this rfl
    subst hL; exact hα.elim

theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

theorem B_to_A : B → A := fun h => absurd h not_B

/-! ### What holds: the conjuncts of `B` not mentioning `GrB` -/

/-- The four conjuncts of `B` that do not involve `GrB`. -/
def B_rest : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    (∀ o o' : X.GrObj, o.pt = o'.pt → o.sum = o'.sum → o = o') ∧
    (∀ (o o' : X.GrObj) (φ : Mor),
      (∃ f : o ⟶ o', EpGroupoid.SmoothCat.mor (X.grProj.map f) = φ) ↔
        (X.src φ = o.pt ∧ X.tgt φ = o'.pt ∧ o'.sum = pushB X φ o.sum)) ∧
    (∀ (o o' : X.GrObj) (f g : o ⟶ o'),
      EpGroupoid.SmoothCat.mor (X.grProj.map f) = EpGroupoid.SmoothCat.mor (X.grProj.map g) →
        f = g) ∧
    (∀ o : X.GrObj, EpGroupoid.SmoothCat.pt (X.grProj.obj o) = o.pt)

theorem B_rest_holds : B_rest := by
  intro Obj Mor _ _ _ _ _ _ X
  refine ⟨fun o o' h1 h2 => ?_, fun o o' φ => ⟨?_, ?_⟩, fun o o' f g h => Subtype.ext h,
    fun o => rfl⟩
  · cases o; cases o'; subst h1 h2; rfl
  · rintro ⟨f, rfl⟩
    exact ⟨f.2.1, f.2.2.1, f.2.2.2.symm⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨φ, h1, h2, h3.symm⟩, rfl⟩

/-- `GrB x` with nonnegative weights is contained in the project's `Gr x`. -/
theorem nonneg_mem_GrB_to_mem_Gr {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (x : Obj) (a : Set X.PObj.TangentSpace →₀ ℚ)
    (ha : a ∈ GrB X x) (hnn : ∀ L, 0 ≤ a L) : a ∈ X.Gr x :=
  ⟨hnn, fun L hL _ hα => (ha L hL).1 hα⟩

#rt_check_soft RoundTrip.V9_11.not_B [Polyfold.EpGroupoid.tangentMor_unit_of_eq,
  Polyfold.EpGroupoid.tangentMor_injOn, Polyfold.EpGroupoid.tangentMor_eq_tangentMapOn_hat,
  Polyfold.EpGroupoid.grPush_mem, Polyfold.EpGroupoid.grPush_comp,
  Polyfold.EpGroupoid.grPush_unit]
#rt_check_soft RoundTrip.V9_11.B_to_A [Polyfold.EpGroupoid.tangentMor_unit_of_eq,
  Polyfold.EpGroupoid.tangentMor_injOn, Polyfold.EpGroupoid.tangentMor_eq_tangentMapOn_hat,
  Polyfold.EpGroupoid.grPush_mem, Polyfold.EpGroupoid.grPush_comp,
  Polyfold.EpGroupoid.grPush_unit]
#rt_check_soft RoundTrip.V9_11.B_rest_holds [Polyfold.EpGroupoid.tangentMor_unit_of_eq,
  Polyfold.EpGroupoid.tangentMor_injOn, Polyfold.EpGroupoid.tangentMor_eq_tangentMapOn_hat,
  Polyfold.EpGroupoid.grPush_mem, Polyfold.EpGroupoid.grPush_comp,
  Polyfold.EpGroupoid.grPush_unit]
#rt_overlap RoundTrip.V9_11.B_to_A [Polyfold.EpGroupoid.tangentMor_unit_of_eq,
  Polyfold.EpGroupoid.tangentMor_injOn, Polyfold.EpGroupoid.tangentMor_eq_tangentMapOn_hat,
  Polyfold.EpGroupoid.grPush_mem, Polyfold.EpGroupoid.grPush_comp,
  Polyfold.EpGroupoid.grPush_unit]

end RoundTrip.V9_11
