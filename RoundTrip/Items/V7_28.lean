import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_28

/-! Round trip for V7_28 (Definition 7.9: local uniformizers; "there exists a local uniformizer
around every object"; "a local uniformizer is injective on objects as well as on morphisms").

`A` is the conjunction of the types of the listed theorems, at universe `0` (B lives in `Type`):
`EpGroupoid.exists_localUniformizer` (inside every open `V ∋ x`),
`LocalUniformizer.injective_obj`, `LocalUniformizer.injective_mor`,
`NaturalRep.isOpenEmbedding_functor_obj`, `NaturalRep.isOpenEmbedding_functor_mor`.
`EpGroupoid.LocalUniformizer` and `NaturalRep.toLocalUniformizer` are definitions (vocabulary).

**B is false** (`not_B`, two independent counterexamples).  B's conjunct (D) claims that the
text's notion (B's `IsLocalUniformizerB`) is *equivalent* to the data of a project
`X.LocalUniformizer x`.  The direction text ⇒ project fails for two independent reasons, both
already flagged as doubts by B's author:
* the project's `LocalUniformizer` contains a `NaturalRep`, whose `U` must be **connected**
  (`NaturalRep.isConnected_U`); B's natural action does not ask this.  Counterexample
  `not_B_connected`: the trivial ep-groupoid of the two-point discrete M-polyfold `Bool`,
  `U = univ` (disconnected), `Φ = Γ = id`, `Ψ = id` satisfies `IsLocalUniformizerB`, but no
  project local uniformizer has `U = univ`.
* the project's `LocalUniformizer` asks `Ψ_x` to be **the inclusion on objects**
  (`LocalUniformizer.obj_eq`); B (reading "embedding" as injective on objects) allows any
  injective `Ψ_x`.  Counterexample `not_B_obj`: the trivial ep-groupoid of `ℝ¹`, `U = univ`
  (connected), `Ψ_x = −id` on objects and morphisms, which satisfies `IsLocalUniformizerB`, but
  `Ψ.obj y = y` would force `1 = −1`.
Both are instances of one lemma (`isLocalUniformizerB_trivial`): in the trivial ep-groupoid of any
M-polyfold `Z`, every self-homeomorphism `e` of `Z` is a local uniformizer on `U = Z` in B's sense.
Since A holds, `A → B` is false; `B → A` holds only ex falso.

The remaining conjuncts of B ((E) existence, (I) injectivity, (O) `π(U)` open) are not refuted;
the differences are definitional (connectedness of `U`, `Ψ_x = inclusion`), and under the
project's definition the text's "injective on objects and morphisms" becomes A's
`injective_obj`/`injective_mor`, while A's `isOpenEmbedding_functor_*` (topological embedding
on objects and morphisms) and the "`U(x) ⊆ V`" strengthening of existence are extra to B. -/

namespace RoundTrip.V7_28
open Polyfold Set

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.exists_localUniformizer.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.LocalUniformizer.injective_obj.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.LocalUniformizer.injective_mor.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_functor_obj.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_functor_mor.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.exists_localUniformizer.{0},
    @Polyfold.EpGroupoid.LocalUniformizer.injective_obj.{0},
    @Polyfold.EpGroupoid.LocalUniformizer.injective_mor.{0},
    @Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_functor_obj.{0},
    @Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_functor_mor.{0}⟩

section Trivial

variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z)
  (x : Z) (e : Z ≃ₜ Z)

/-- The homeomorphism `|Z|_{G_x ⋉ Z} → π(Z)`, `[y] ↦ |e y|`, for the trivial ep-groupoid. -/
noncomputable def τ :
    Quot (orbRel (EpGroupoid.trivial P) x univ fun _ => id) ≃ₜ
      ↥((EpGroupoid.trivial P).π '' univ) where
  toFun := Quot.lift (fun y => ⟨(EpGroupoid.trivial P).π (e y), mem_image_of_mem _ (mem_univ _)⟩)
    (by
      rintro a b ⟨g, hg⟩
      exact Subtype.ext (congrArg (fun z => (EpGroupoid.trivial P).π (e z)) hg))
  invFun w := Quot.mk _ ⟨e.symm (EpGroupoid.trivialOrbitHomeomorph P w.1), mem_univ _⟩
  left_inv q := by
    induction q using Quot.ind with
    | mk y => exact congrArg (Quot.mk _) (Subtype.ext (e.symm_apply_apply y.1))
  right_inv w := by
    refine Subtype.ext ?_
    change (EpGroupoid.trivial P).π (e (e.symm (EpGroupoid.trivialOrbitHomeomorph P w.1))) = w.1
    rw [e.apply_symm_apply]
    exact (EpGroupoid.trivialOrbitHomeomorph P).symm_apply_apply w.1
  continuous_toFun := continuous_quot_lift _
    (Continuous.subtype_mk ((EpGroupoid.trivial P).continuous_π.comp
      (e.continuous.comp continuous_subtype_val)) _)
  continuous_invFun := continuous_quot_mk.comp (Continuous.subtype_mk
    (e.symm.continuous.comp ((EpGroupoid.trivialOrbitHomeomorph P).continuous.comp
      continuous_subtype_val)) _)

/-- **In the trivial ep-groupoid of `Z`, every self-homeomorphism `e` of `Z` is a local
uniformizer in B's sense**, on `U = Z` with `Φ = Γ = id` and `Ψ_x = e` on objects and
morphisms. -/
theorem isLocalUniformizerB_trivial :
    IsLocalUniformizerB (EpGroupoid.trivial P) x univ (fun _ => id) (fun _ => id) e
      (fun _ y => e y) := by
  refine ⟨?_, ⟨fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ => rfl, fun _ _ => rfl⟩, ?_,
    e.injective.injOn, τ P x e, fun _ => rfl⟩
  · exact
      { isOpen := isOpen_univ
        mem := mem_univ _
        diffeo := fun _ => ⟨id, MPolyfold.isScDiffeoOn_id isOpen_univ⟩
        hom := fun _ _ _ _ => rfl
        smooth := fun _ => MPolyfold.isScSmoothMap_id
        Γ_x := fun g => g.src_val.symm
        src_tgt := fun _ _ _ => ⟨rfl, rfl⟩
        unique := fun _ _ _ => ⟨1, rfl, fun g _ => Subsingleton.elim g 1⟩ }
  · intro y _ z _
    refine ⟨fun g hg => ⟨rfl, congrArg e hg⟩, fun g _ h _ _ => Subsingleton.elim g h,
      fun φ hφ => ⟨1, ?_, hφ.1.symm⟩⟩
    exact e.injective (hφ.1.symm.trans hφ.2)

end Trivial

/-- **Counterexample 1 (connectedness)**: in the trivial ep-groupoid of the discrete two-point
M-polyfold `Bool`, the identity on the disconnected `U = Bool` is a local uniformizer in B's
sense, but the project's `NaturalRep` (hence `LocalUniformizer`) needs `U` connected. -/
theorem not_B_connected : ¬ B := by
  intro hB
  obtain ⟨hD, -, -, -⟩ := hB Bool Bool (EpGroupoid.trivial (discretePolyfold Bool))
  obtain ⟨L, hU, -⟩ := (hD true univ _ _ _ _).1
    (isLocalUniformizerB_trivial (discretePolyfold Bool) true (Homeomorph.refl Bool))
  have hc := L.rep.isConnected_U
  rw [hU] at hc
  exact Bool.noConfusion (hc.isPreconnected.subsingleton (mem_univ true) (mem_univ false))

/-- **Counterexample 2 (`Ψ_x` the inclusion on objects)**: in the trivial ep-groupoid of `ℝ¹`,
`Ψ_x = −id` on the connected `U = ℝ¹` is a local uniformizer in B's sense, but the project asks
`Ψ.obj y = y`. -/
theorem not_B_obj : ¬ B := by
  intro hB
  obtain ⟨hD, -, -, -⟩ := hB (Fin 1 → ℝ) (Fin 1 → ℝ) (EpGroupoid.trivial (rnPolyfold 1))
  obtain ⟨L, hU, -, hobj, -⟩ := (hD 0 univ _ _ _ _).1
    (isLocalUniformizerB_trivial (rnPolyfold 1) 0 (Homeomorph.neg (Fin 1 → ℝ)))
  have h1 : (1 : Fin 1 → ℝ) ∈ L.rep.U := by rw [hU]; exact mem_univ _
  have h := (L.obj_eq ⟨1, h1⟩).symm.trans (hobj ⟨1, h1⟩)
  have h0 := congrFun h 0
  simp at h0
  norm_num at h0

theorem not_B : ¬ B := not_B_connected

/-- `B → A` only ex falso (B is false). -/
theorem B_to_A : B → A := fun h => (not_B h).elim

/-- `¬ (A → B)`: A holds and B does not. -/
theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

#rt_check RoundTrip.V7_28.not_B_connected [Polyfold.EpGroupoid.exists_localUniformizer,
  Polyfold.EpGroupoid.LocalUniformizer.injective_obj,
  Polyfold.EpGroupoid.LocalUniformizer.injective_mor,
  Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_functor_obj,
  Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_functor_mor]
#rt_check RoundTrip.V7_28.not_B_obj [Polyfold.EpGroupoid.exists_localUniformizer,
  Polyfold.EpGroupoid.LocalUniformizer.injective_obj,
  Polyfold.EpGroupoid.LocalUniformizer.injective_mor,
  Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_functor_obj,
  Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_functor_mor]
#rt_check RoundTrip.V7_28.B_to_A [Polyfold.EpGroupoid.exists_localUniformizer,
  Polyfold.EpGroupoid.LocalUniformizer.injective_obj,
  Polyfold.EpGroupoid.LocalUniformizer.injective_mor,
  Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_functor_obj,
  Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_functor_mor]
#rt_overlap RoundTrip.V7_28.B_to_A [Polyfold.EpGroupoid.exists_localUniformizer,
  Polyfold.EpGroupoid.LocalUniformizer.injective_obj,
  Polyfold.EpGroupoid.LocalUniformizer.injective_mor,
  Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_functor_obj,
  Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_functor_mor]

end RoundTrip.V7_28
