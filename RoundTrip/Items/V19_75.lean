import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V19_75

set_option maxSynthPendingDepth 3

/-! Round trip for V19_75 (2021 Proposition 19.7.13, p. 913: the topology of `M(Ψ̂, Ψ̂')`).

The item lists `fibHomeomorph` (a definition: vocabulary) and the theorems
`proposition_19_7_13` (main conjunct) and `metrizableSpace_MHat`; `A` is the conjunction of their
types at universe `0`.

* `A_to_B`: the topology is the project's `topologicalSpaceMHat` (induced by `toFib`); the
  homeomorphism, uniqueness (`IsHomeomorph` from a homeomorphism with underlying map `toFib`),
  regularity, Hausdorffness and local metrizability come from `proposition_19_7_13`.
* `B_to_A`: `B`'s topology `t` makes `toFib` a homeomorphism, hence an inducing map, so
  `t = induced toFib = topologicalSpaceMHat`; after this the clauses of `proposition_19_7_13`
  are `B`'s, and global metrizability (not in `B`) follows from the embedding `toFib` into the
  metrizable `Fib` (`metrizableSpace_fib`, Lemma 19.7.12, not an item theorem). -/

namespace RoundTrip.V19_75
open Polyfold GroupoidalCategory

def A : Prop :=
  (type_of% @Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_13.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.CoveringBasicConstruction.metrizableSpace_MHat.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_13.{0},
    @Polyfold.GroupoidalCategory.CoveringBasicConstruction.metrizableSpace_MHat.{0}⟩

theorem main_A_to_B :
    (type_of% @Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_13.{0}) →
      B := by
  intro h A B P hP Bh x y
  obtain ⟨⟨e, he⟩, huniq, hreg, ht2, hloc, -⟩ := h Bh hP x y
  refine ⟨Bh.topologicalSpaceMHat x y, ⟨e, he⟩, fun t' ⟨e', he'⟩ => ?_, hreg, ht2, hloc⟩
  let := t'
  have hfun : (e' : MT Bh x y → Bh.Fib x y) = Bh.toFib x y := funext he'
  exact huniq t' (hfun ▸ e'.isHomeomorph)

theorem A_to_B : A → B := fun h => main_A_to_B h.1

/-- From `B`: the topology on `M(Ψ̂, Ψ̂')` is the project's. -/
theorem B_topology (hB : B) {A B : GroupoidalCategory.{0}}
    {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr} (hP : IsFiniteToOneCovering P)
    (Bh : CoveringBasicConstruction P) (x y : Bh.hatU.Unif) :
    ∃ t : TopologicalSpace (MT Bh x y), t = Bh.topologicalSpaceMHat x y ∧
      IsCanonHomeo Bh x y t ∧
      (∀ t' : TopologicalSpace (MT Bh x y), IsCanonHomeo Bh x y t' → t' = t) ∧
      @RegularSpace (MT Bh x y) t ∧ @T2Space (MT Bh x y) t ∧
      ∀ h : MT Bh x y, ∃ W : Set (MT Bh x y), @IsOpen _ t W ∧ h ∈ W ∧
        @TopologicalSpace.MetrizableSpace W (@instTopologicalSpaceSubtype _ _ t) := by
  obtain ⟨t, ⟨e, he⟩, huniq, hreg, ht2, hloc⟩ := hB A B P hP Bh x y
  refine ⟨t, ?_, ⟨e, he⟩, huniq, hreg, ht2, hloc⟩
  let := t
  have hfun : (e : MT Bh x y → Bh.Fib x y) = Bh.toFib x y := funext he
  have := e.isInducing.eq_induced
  rw [hfun] at this
  exact this

theorem main_B_to_A : B →
    (type_of% @Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_13.{0}) := by
  intro hB A B P Bh hP x y
  obtain ⟨t, ht, ⟨e, he⟩, huniq, hreg, ht2, hloc⟩ := B_topology hB hP Bh x y
  have hemb : @Topology.IsEmbedding (Bh.MHat x y) _ t _ (Bh.toFib x y) := by
    let := t
    have h1 := e.isEmbedding
    have h2 : (fun h => e h) = Bh.toFib x y := funext he
    exact h2 ▸ h1
  subst ht
  refine ⟨⟨e, he⟩, fun t' ht' => huniq t' ⟨@IsHomeomorph.homeomorph _ _ t' _ _ ht', fun _ => rfl⟩,
    hreg, ht2, hloc, hemb.metrizableSpace⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨main_B_to_A hB, fun Bh hP x y => ((main_B_to_A hB) Bh hP x y).2.2.2.2.2⟩

#rt_check RoundTrip.V19_75.A_to_B [Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_13,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.metrizableSpace_MHat]
#rt_check RoundTrip.V19_75.B_to_A [Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_13,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.metrizableSpace_MHat]
#rt_check RoundTrip.V19_75.main_A_to_B [Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_13,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.metrizableSpace_MHat]
#rt_check RoundTrip.V19_75.main_B_to_A [Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_13,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.metrizableSpace_MHat]
#rt_overlap RoundTrip.V19_75.B_to_A [Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_13,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.metrizableSpace_MHat]

end RoundTrip.V19_75
