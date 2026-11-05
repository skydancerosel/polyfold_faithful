import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_11

/-! Round trip for V1_11 (Definition 1.12: sc⁰ maps).

`A` is the conjunction of the types of the theorems in the item's declaration list:
`IsSc0.levelMap_mapsTo`, `IsSc0.continuousOn_base`, `IsSc0.congr`, `IsSc0.comp`, `isSc0_id`,
`ScOperator.isSc0` (the definitions `levelMap`, `IsSc0` are vocabulary).  None has universe
parameters (`ScBanach` lives in `Type`).

`B` says that for maps `f : U → U'` between tuples the project's `IsSc0 E F U f` is the text's
sc⁰.  The project's `IsSc0` has target `F` (`f(U_m) ⊆ F_m`, the induced `levelMap f m` continuous
on `U_m`); the text's has target `U'` (`f(U_m) ⊆ U'_m`).  With `f(U) ⊆ U'` they agree: the extra
`U'_m`-clause is `A`'s `IsSc0.levelMap_mapsTo`, and the blind "some `f_m` over `f` on `U_m`" is
`levelMap f m` on `U_m` by injectivity of `F_m → F₀`.

`B → A` is vacuous: `A`'s conjuncts are general facts about `IsSc0` for arbitrary `U` (not only
relatively open subsets of partial quadrants), which a characterization of the definition on
tuples cannot supply; they are re-proved outright. -/

namespace RoundTrip.V1_11
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.IsSc0.levelMap_mapsTo) ∧ (type_of% @Polyfold.IsSc0.continuousOn_base) ∧
    (type_of% @Polyfold.IsSc0.congr) ∧ (type_of% @Polyfold.IsSc0.comp) ∧
    (type_of% @Polyfold.isSc0_id) ∧ (type_of% @Polyfold.ScOperator.isSc0)

theorem A_holds : A :=
  ⟨@Polyfold.IsSc0.levelMap_mapsTo, @Polyfold.IsSc0.continuousOn_base, @Polyfold.IsSc0.congr,
    @Polyfold.IsSc0.comp, @Polyfold.isSc0_id, @Polyfold.ScOperator.isSc0⟩

/-- The text's sc⁰ always gives the project's (no hypothesis on `U`, `U'`, `f` needed). -/
theorem isSc0_of_text {E F : ScBanach} {U : Set (E.lvl 0)} {U' : Set (F.lvl 0)}
    {f : E.lvl 0 → F.lvl 0} (h : IsSc0Text E F U U' f) : IsSc0 E F U f := by
  refine ⟨fun m x hx => ?_, fun m => ?_⟩
  · obtain ⟨fm, -, hfm, -⟩ := h m
    exact ⟨fm x, hfm x hx⟩
  · obtain ⟨fm, -, hfm, hc⟩ := h m
    exact hc.congr fun x hx => levelMap_eq_of_toBase_eq (hfm x hx)

theorem A_to_B : A → B := by
  intro hA E F C U C' U' f _ _ hfU
  constructor
  · intro hf m
    exact ⟨levelMap f m, hA.1 hf hfU m, fun x hx => hf.toBase_levelMap hx, hf.continuousOn m⟩
  · exact isSc0_of_text

/-- `B → A`, vacuous: every conjunct of `A` is re-proved outright (see the module docstring). -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- levelMap_mapsTo
    intro E F U V f hf hfV m x hx
    rw [ScBanach.mem_lvlSet, hf.toBase_levelMap hx]
    exact hfV hx
  · -- continuousOn_base
    intro E F U f hf
    have := hf.continuousOn 0
    simpa [funext (levelMap_zero f)] using this
  · -- congr
    intro E F U f hf f' h
    exact ⟨fun m x hx => by rw [← h hx]; exact hf.mem_range m x hx,
      fun m => (hf.continuousOn m).congr fun x hx => (IsSc0.levelMap_congr h hx).symm⟩
  · -- comp
    intro E F G U V f g hg hf hfV
    have hmaps : ∀ m, MapsTo (levelMap f m) (E.lvlSet U m) (F.lvlSet V m) := fun m x hx => by
      rw [ScBanach.mem_lvlSet, hf.toBase_levelMap hx]
      exact hfV hx
    have hcomp : ∀ m, ∀ x ∈ E.lvlSet U m,
        levelMap (g ∘ f) m x = levelMap g m (levelMap f m x) := fun m x hx => by
      apply levelMap_eq_of_toBase_eq
      rw [hg.toBase_levelMap (hmaps m hx), hf.toBase_levelMap hx]
      rfl
    refine ⟨fun m x hx => ?_, fun m => ?_⟩
    · change g (f (E.toBase m x)) ∈ _
      rw [← hf.toBase_levelMap hx]
      exact hg.mem_range m _ (hmaps m hx)
    · exact ((hg.continuousOn m).comp (hf.continuousOn m) (hmaps m)).congr
        fun x hx => hcomp m x hx
  · -- isSc0_id
    intro E U
    exact ⟨fun _ x _ => ⟨x, rfl⟩, fun _ => (continuousOn_id).congr fun _ _ =>
      levelMap_eq_of_toBase_eq (f := (id : E.lvl 0 → E.lvl 0)) rfl⟩
  · -- ScOperator.isSc0
    intro E F T
    exact ⟨fun m x _ => ⟨T m x, T.toBase_comm m x⟩, fun m => (T m).continuous.continuousOn.congr
      fun x _ => levelMap_eq_of_toBase_eq (T.toBase_comm m x)⟩

#rt_check RoundTrip.V1_11.A_to_B [Polyfold.IsSc0.levelMap_mapsTo, Polyfold.IsSc0.continuousOn_base,
  Polyfold.IsSc0.congr, Polyfold.IsSc0.comp, Polyfold.isSc0_id, Polyfold.ScOperator.isSc0]
#rt_check RoundTrip.V1_11.B_to_A [Polyfold.IsSc0.levelMap_mapsTo, Polyfold.IsSc0.continuousOn_base,
  Polyfold.IsSc0.congr, Polyfold.IsSc0.comp, Polyfold.isSc0_id, Polyfold.ScOperator.isSc0]
#rt_overlap RoundTrip.V1_11.B_to_A [Polyfold.IsSc0.levelMap_mapsTo,
  Polyfold.IsSc0.continuousOn_base, Polyfold.IsSc0.congr, Polyfold.IsSc0.comp, Polyfold.isSc0_id,
  Polyfold.ScOperator.isSc0]

end RoundTrip.V1_11
