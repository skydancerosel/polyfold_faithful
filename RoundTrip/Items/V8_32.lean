import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_32

/-! Round trip for V8_32 (Definition 8.9 of the 2017 text, 2021: Definition 8.5.5: `Diff_sc`,
covering functors and geometric lifts).

`A` is the conjunction of the types of the four listed theorems, universes instantiated at `0`
(`B` lives in `Type`): `ScDiffeo.ext` (a morphism of `Diff_sc` is determined by its map),
`IsCoveringFunctor.existsUnique_lift`, `isCoveringFunctor_of_isEmpty`,
`CoveringExamples.isCoveringFunctor_id`.  The other listed names (`MPolyfoldCat`, `ScDiffeo`,
`ScDiffeo.id`, `ScDiffeo.comp`, `coveringMap`, `IsCoveringFunctor`, `GeometricLift`,
`IsCoveringFunctor.lift`) are definitions, the vocabulary compared by `B`.

* `B` is a characterization of the project's definitions, and it holds (`B_holds`, outright):
  (i) a morphism of the project's `Diff_sc` is a map with a two-sided inverse, both sc-smooth on
  the whole spaces, i.e. `B`'s `IsScDiffeoB` (the project's `IsScDiffeoOn … univ univ` unfolds to
  that), every such map is one, identities and composition are those of maps (`rfl`); (ii) the
  project's `IsCoveringFunctor` (bijectivity into `G × D`) is `B`'s `IsCoveringB` (bijectivity into
  `Σ y c, f(y) ⟶ c`), through the bijection `⟨y, c, g⟩ ↦ (g, y)` (`SingleObj G` has one object);
  (iii) `GeometricLift f` is exactly a triple `(L_D, L_C, τ : L_D ⟶ f ⋙ L_C)`.
  So `A → B` holds without using `A` (the theorems of `A` are not needed for the definitions).
* `B → A`: `A`'s four theorems are stated for arbitrary groupoids `D` and groups `G` (no
  finiteness), while `B`'s clauses (ii), (iii) assume `[Fintype D]`, `[Fintype (a ⟶ b)]`,
  `[Fintype G]`; and `B` says nothing about `ScDiffeo.ext`.  They are re-proved outright from the
  definitions (vacuous for the audit). -/

namespace RoundTrip.V8_32
open Polyfold CategoryTheory Set Function

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.ScDiffeo.ext.{0}) ∧
  (type_of% @Polyfold.IsCoveringFunctor.existsUnique_lift) ∧
  (type_of% @Polyfold.isCoveringFunctor_of_isEmpty) ∧
  (type_of% @Polyfold.CoveringExamples.isCoveringFunctor_id)

theorem A_holds : A :=
  ⟨@Polyfold.ScDiffeo.ext.{0}, @Polyfold.IsCoveringFunctor.existsUnique_lift,
    @Polyfold.isCoveringFunctor_of_isEmpty, @Polyfold.CoveringExamples.isCoveringFunctor_id⟩

/-- (ii): the project's covering functors are `B`'s. -/
theorem isCoveringFunctor_iff {D : Type} [Groupoid D] {G : Type} [Group G]
    (f : D ⥤ SingleObj G) : IsCoveringFunctor f ↔ IsCoveringB f := by
  let e : (Σ (y : D) (c : SingleObj G), (f.obj y ⟶ c)) → G × D := fun p => ((p.2.2 : G), p.1)
  have he : Bijective e := by
    constructor
    · rintro ⟨y, c, g⟩ ⟨y', c', g'⟩ h
      have h1 : (g : G) = (g' : G) := congrArg Prod.fst h
      have h2 : y = y' := congrArg Prod.snd h
      subst h2
      cases c
      cases c'
      change g = g' at h1
      subst h1
      rfl
    · rintro ⟨g, y⟩
      exact ⟨⟨y, SingleObj.star G, g⟩, rfl⟩
  have hcomp : coveringMap f =
      e ∘ (fun ψ : (Σ (a : D) (b : D), (a ⟶ b)) =>
        (⟨ψ.1, f.obj ψ.2.1, f.map ψ.2.2⟩ : Σ (y : D) (c : SingleObj G), (f.obj y ⟶ c))) := rfl
  unfold IsCoveringFunctor IsCoveringB
  rw [hcomp]
  exact he.of_comp_iff' _

/-- `B` holds outright: the project's definitions are the text's. -/
theorem B_holds : B := by
  refine ⟨fun A B => ⟨fun m => ?_, fun f hf => ?_⟩, fun A => rfl, fun A B C m n => rfl, ?_⟩
  · exact ⟨m.invFun, m.isScDiffeoOn.isScSmoothOn, m.isScDiffeoOn.isScSmoothOn_inv,
      fun a => m.isScDiffeoOn.left_inv a (mem_univ a),
      fun b => m.isScDiffeoOn.right_inv b (mem_univ b)⟩
  · obtain ⟨g, h1, h2, h3, h4⟩ := hf
    exact ⟨(⟨f, g, ⟨h1, h2, mapsTo_univ _ _, mapsTo_univ _ _, fun a _ => h3 a,
      fun b _ => h4 b⟩⟩ : ScDiffeo A B), rfl⟩
  · intro D _ _ _ G _ _ f
    exact ⟨isCoveringFunctor_iff f, fun _ LD LC τ => ⟨⟨LD, LC, τ⟩, rfl, rfl, HEq.rfl⟩⟩

theorem A_to_B : A → B := fun _ => B_holds

/-- `B → A`, outright (the conjuncts of `A` are general facts `B` cannot supply). -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A B f g h
    have hinv : f.invFun = g.invFun := funext fun b => by
      have h1 := f.isScDiffeoOn.right_inv b (mem_univ b)
      have h2 := g.isScDiffeoOn.left_inv (f.invFun b) (mem_univ _)
      rw [← h] at h2
      rw [h1] at h2
      exact h2.symm
    cases f; cases g
    cases h; cases hinv
    rfl
  · intro D _ G _ f hf g y
    obtain ⟨⟨a, b, ψ⟩, h⟩ := hf.2 (g, y)
    have h' : ((f.map ψ : G), a) = (g, y) := h
    obtain ⟨hg, rfl⟩ := Prod.mk_inj.1 h'
    refine ⟨⟨b, ψ⟩, hg, ?_⟩
    rintro ⟨b', ψ'⟩ hψ'
    have h' : coveringMap f ⟨a, b', ψ'⟩ = coveringMap f ⟨a, b, ψ⟩ :=
      Prod.ext (hψ'.trans hg.symm) rfl
    exact eq_of_heq (Sigma.mk.inj_iff.1 (hf.1 h')).2
  · intro D _ _ G _ f
    exact ⟨fun a => isEmptyElim a.1, fun p => isEmptyElim p.2⟩
  · intro G _
    constructor
    · rintro ⟨a, b, g⟩ ⟨a', b', g'⟩ h
      simp only [coveringMap, Functor.id_map, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      cases a; cases b; cases a'; cases b'
      cases h1
      rfl
    · rintro ⟨g, a⟩
      exact ⟨⟨a, SingleObj.star G, g⟩, rfl⟩

#rt_check_soft RoundTrip.V8_32.A_to_B [Polyfold.ScDiffeo.ext,
  Polyfold.IsCoveringFunctor.existsUnique_lift, Polyfold.isCoveringFunctor_of_isEmpty,
  Polyfold.CoveringExamples.isCoveringFunctor_id]
#rt_check_soft RoundTrip.V8_32.B_to_A [Polyfold.ScDiffeo.ext,
  Polyfold.IsCoveringFunctor.existsUnique_lift, Polyfold.isCoveringFunctor_of_isEmpty,
  Polyfold.CoveringExamples.isCoveringFunctor_id]
#rt_overlap RoundTrip.V8_32.B_to_A [Polyfold.ScDiffeo.ext,
  Polyfold.IsCoveringFunctor.existsUnique_lift, Polyfold.isCoveringFunctor_of_isEmpty,
  Polyfold.CoveringExamples.isCoveringFunctor_id]
#rt_overlap RoundTrip.V8_32.A_to_B [Polyfold.ScDiffeo.ext,
  Polyfold.IsCoveringFunctor.existsUnique_lift, Polyfold.isCoveringFunctor_of_isEmpty,
  Polyfold.CoveringExamples.isCoveringFunctor_id]

end RoundTrip.V8_32
