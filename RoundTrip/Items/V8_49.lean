import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_49

/-!
Round trip for V8_49 (2021, the remark after Definition 8.5.5 and Example 8.5.6, p. 388).

The item lists the definitions `Example856D`, `example856Functor` (vocabulary) and the theorems
`IsCoveringFunctor.injective_map_end` (for a covering functor `f : D → SingleObj G`, `f : G_d → G`
is injective) and `example_8_5_6` (the functor of Example 8.5.6 is a covering functor, the
`G_d` are trivial, `ℤˣ` is not, and `f : G_d → ℤˣ` is injective and not surjective for both
objects `d`).  `A` is the conjunction of their types (no universe parameters: everything is in
`Type`).

`B` states injectivity for covering functors into an *arbitrary* groupoid `C` (its own
`IsCoveringB`), and the example with its own copy `DB`, `fB` of the groupoid and the functor.

* `isCoveringB_iff`: for `C = SingleObj G` the blind `IsCoveringB f` is the project's
  `IsCoveringFunctor f` (`(a, c, g) ↦ (g, a)` is a bijection
  `Σ a (c : SingleObj G), f a ⟶ c ≃ G × D`).  The copies `DB`, `fB` are definitionally the
  project's `Example856D`, `example856Functor` (both `Bool`, `Hom = Unit`, the same `if`).
* `A ⇒ B`: the example part comes from `A` (covering property through `isCoveringB_iff`,
  non-surjectivity at `a`); the injectivity for an arbitrary groupoid `C` is **not** a
  consequence of `A`'s, which is only for one-object `C = SingleObj G`; it is re-proved here
  (three lines: the covering map is injective on `⟨d, d, g⟩`).
* `B ⇒ A`: `injective_map_end` is B's injectivity for `C = SingleObj G`; in the example, the
  covering property, injectivity and non-surjectivity at `a` come from `B`; the trivial facts
  (`G_d` subsingleton, `ℤˣ` nontrivial) and non-surjectivity at `b` (which `B` does not state)
  are proved directly.
-/

namespace RoundTrip.V8_49
open Polyfold CategoryTheory Function

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.IsCoveringFunctor.injective_map_end) ∧
  (type_of% @Polyfold.example_8_5_6)

theorem A_holds : A :=
  ⟨@Polyfold.IsCoveringFunctor.injective_map_end, @Polyfold.example_8_5_6⟩

/-- The bijection `Σ a (c : SingleObj G), f a ⟶ c → G × D`, `(a, c, g) ↦ (g, a)`. -/
def tgtEquivFun {D : Type} [Groupoid.{0} D] {G : Type} [Group G] (f : D ⥤ SingleObj G) :
    (Σ (a : D) (c : SingleObj G), f.obj a ⟶ c) → G × D :=
  fun p => ((p.2.2 : G), p.1)

theorem bijective_tgtEquivFun {D : Type} [Groupoid.{0} D] {G : Type} [Group G]
    (f : D ⥤ SingleObj G) : Bijective (tgtEquivFun f) := by
  constructor
  · rintro ⟨a, c, g⟩ ⟨a', c', g'⟩ h
    obtain ⟨h1, h2⟩ := Prod.mk_inj.1 h
    change a = a' at h2
    subst h2
    have hc : c = c' := Subsingleton.elim (α := Unit) c c'
    subst hc
    change g = g' at h1
    subst h1
    rfl
  · rintro ⟨g, a⟩
    exact ⟨⟨a, SingleObj.star G, g⟩, rfl⟩

/-- For `C = SingleObj G`, the blind covering functors are the project's. -/
theorem isCoveringB_iff {D : Type} [Groupoid.{0} D] {G : Type} [Group G] (f : D ⥤ SingleObj G) :
    IsCoveringB f ↔ IsCoveringFunctor f := by
  unfold IsCoveringB IsCoveringFunctor
  have h : coveringMap f = tgtEquivFun f ∘
      (fun p : (Σ (a : D) (b : D), a ⟶ b) =>
        (⟨p.1, f.obj p.2.1, f.map p.2.2⟩ : Σ (a : D) (c : SingleObj G), f.obj a ⟶ c)) := rfl
  rw [h, (bijective_tgtEquivFun f).of_comp_iff']

theorem A_to_B : A → B := by
  intro hA
  refine ⟨?_, ?_, ?_⟩
  · -- not in `A` (only for `C = SingleObj G`): re-proved
    intro D C _ _ f hf d g g' h
    have h' : (⟨d, f.obj d, f.map g⟩ : Σ (a : D) (c : C), f.obj a ⟶ c) =
        ⟨d, f.obj d, f.map g'⟩ := congrArg (fun x => (⟨d, f.obj d, x⟩ : Σ (a : D) (c : C),
          f.obj a ⟶ c)) h
    have h1 := Sigma.mk.inj_iff.1 (hf.1 (a₁ := ⟨d, d, g⟩) (a₂ := ⟨d, d, g'⟩) h')
    have h2 := Sigma.mk.inj_iff.1 (eq_of_heq h1.2)
    exact eq_of_heq h2.2
  · exact (isCoveringB_iff fB).2 hA.2.1
  · exact hA.2.2.2.2.2 false

theorem B_to_A : B → A := by
  intro hB
  have hcov : IsCoveringFunctor example856Functor := (isCoveringB_iff fB).1 hB.2.1
  refine ⟨?_, hcov, fun d => ⟨fun _ _ => rfl⟩, ⟨⟨1, -1, by decide⟩⟩,
    fun d => hB.1 _ _ example856Functor ((isCoveringB_iff _).2 hcov) d, ?_⟩
  · intro D _ G _ f hf d
    exact hB.1 D (SingleObj G) f ((isCoveringB_iff f).2 hf) d
  · intro d
    cases d
    · exact hB.2.2
    · -- `B` states non-surjectivity only at `a`
      intro h
      obtain ⟨ψ, hψ⟩ := h (-1)
      change (if (true : Example856D) = true then 1 else -1 : ℤˣ) = -1 at hψ
      rw [if_pos rfl] at hψ
      exact absurd hψ (by decide)

#rt_check RoundTrip.V8_49.A_to_B [Polyfold.IsCoveringFunctor.injective_map_end,
  Polyfold.example_8_5_6]
#rt_check RoundTrip.V8_49.B_to_A [Polyfold.IsCoveringFunctor.injective_map_end,
  Polyfold.example_8_5_6]
#rt_overlap RoundTrip.V8_49.B_to_A [Polyfold.IsCoveringFunctor.injective_map_end,
  Polyfold.example_8_5_6]

end RoundTrip.V8_49
