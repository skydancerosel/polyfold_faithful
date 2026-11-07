import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_35

/-! Round trip for V6_35 (the bundle `L` of kernels along a path, its determinant line bundle
`λ(L)`, and the continuation of orientations over `[0, 1]` and `[0, 1]²`).

A is the conjunction of the four theorems of the row (`Frame.coordChange_continuousOn`,
`transport_eq`, `transport_injective`, `transport_comp`), universes at `0`; the other listed
declarations (`SubspaceFamily`, `det`, `Frame.pretriv`, `comp`, `LineOrientation.comp`,
`transport`) are definitions, and B uses the same `SubspaceFamily`, `det` and `LineOrientation`.

* `A_to_B` is proved.  Uniqueness of the continued orientation comes from A (`transport_comp`
  along a path from `q₀` to `q`, over the path-connected bases `I` and `I × I`).  Existence is
  NOT stated by A: it is hidden in the definition of `transport` (a `choose` of
  `exists_lineOrientation_apply_eq`); it is taken from that non-item project lemma
  (simply connected and locally path-connected base: `I` and `I × I` are contractible).
* `B_to_A` is proved.  `transport_eq` follows from B's uniqueness over `I` (the orientation chosen
  in `transport` and `o` agree at `0`), `transport_injective` from B's existence and uniqueness
  over `I`, and `transport_comp` from `transport_eq` for the restricted family `Λ.comp γ`.  The
  first conjunct (`Frame.coordChange_continuousOn`, continuity of the coordinate changes of the
  line bundle) is not addressed by B and is re-proved outright from the non-item lemmas
  `coordChange_continuousAt`, `coord_ne_zero`, `wedgeAt_ne_zero`.  B's second half (over
  `I × I`) is not needed for A. -/

namespace RoundTrip.V6_35
open Polyfold unitInterval

/-- The project's statement (the four theorems of the row), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.SubspaceFamily.Frame.coordChange_continuousOn.{0, 0} ∧
  type_of% @Polyfold.SubspaceFamily.transport_eq.{0} ∧
  type_of% @Polyfold.SubspaceFamily.transport_injective.{0} ∧
  type_of% @Polyfold.SubspaceFamily.transport_comp.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.SubspaceFamily.Frame.coordChange_continuousOn.{0, 0},
    @Polyfold.SubspaceFamily.transport_eq.{0},
    @Polyfold.SubspaceFamily.transport_injective.{0},
    @Polyfold.SubspaceFamily.transport_comp.{0, 0}⟩

/-! ### `A ⇒ B` -/

/-- Uniqueness from A's `transport_comp`: over a path-connected base two orientations of `λ(L)`
that agree at `q₀` agree everywhere (continue both along a path from `q₀`). -/
theorem uniq_of_A (hA : A) {Q : Type} [TopologicalSpace Q] [PathConnectedSpace Q]
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (Λ : SubspaceFamily Q W) (q₀ : Q)
    (o o' : LineOrientation Λ.det) (h : o.1 q₀ = o'.1 q₀) : o = o' := by
  refine LineOrientation.ext fun q => ?_
  let γ : Path q₀ q := PathConnectedSpace.somePath q₀ q
  have h1 := hA.2.2.2 Λ o γ.toContinuousMap
  have h2 := hA.2.2.2 Λ o' γ.toContinuousMap
  have e0 : ∀ x : Q, x = q₀ → o x = o' x := by rintro x rfl; exact h
  have hs : γ.toContinuousMap 0 = q₀ := γ.source
  have ht : γ.toContinuousMap 1 = q := γ.target
  have h0 : o (γ.toContinuousMap 0) = o' (γ.toContinuousMap 0) := e0 _ hs
  have h3 : o (γ.toContinuousMap 1) = o' (γ.toContinuousMap 1) := by
    rw [← h1, ← h2]
    exact congrArg (Λ.comp γ.toContinuousMap).transport h0
  have e1 : ∀ x : Q, x = q → o x = o' x → o q = o' q := by rintro x rfl hx; exact hx
  exact e1 _ ht h3

/-- Existence (the non-item project lemma `exists_lineOrientation_apply_eq`) and uniqueness
(from A) over a contractible, locally path-connected base. -/
theorem cont_of_A (hA : A) (Q : Type) [TopologicalSpace Q] [ContractibleSpace Q]
    [LocallyPathConnectedSpace Q] : ContinuationOver Q := by
  intro W _ _ Λ q₀ r
  obtain ⟨o, ho⟩ := exists_lineOrientation_apply_eq (L := Λ.det) q₀ r
  exact ⟨o, ho, fun o' ho' => uniq_of_A hA Λ q₀ o' o (ho'.trans ho.symm)⟩

instance : ContractibleSpace I :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace (Set.nonempty_Icc.2 zero_le_one)

instance : LocallyPathConnectedSpace I := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace

theorem A_to_B : A → B := fun hA =>
  ⟨cont_of_A hA I, cont_of_A hA (I × I)⟩

/-! ### `B ⇒ A` -/

section BtoA
variable (hB : B)
include hB

/-- `transport_eq` from B's uniqueness over `[0, 1]`. -/
theorem transport_eq_of_B {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (Λ : SubspaceFamily I W) (o : LineOrientation Λ.det) : Λ.transport (o 0) = o 1 := by
  have hex := exists_lineOrientation_apply_eq (L := Λ.det) (0 : I) (o 0)
  have hc : hex.choose = o := (hB.1 W Λ 0 (o 0)).unique hex.choose_spec rfl
  exact congrArg (fun o' : LineOrientation Λ.det => o'.1 1) hc

/-- `transport_injective` from B's existence and uniqueness over `[0, 1]`. -/
theorem transport_injective_of_B {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (Λ : SubspaceFamily I W) : Function.Injective Λ.transport := by
  intro r r' h
  obtain ⟨o, ho, -⟩ := hB.1 W Λ 0 r
  obtain ⟨o', ho', -⟩ := hB.1 W Λ 0 r'
  subst ho ho'
  rw [transport_eq_of_B hB, transport_eq_of_B hB] at h
  have : o = o' := (hB.1 W Λ 1 (o 1)).unique rfl h.symm
  rw [this]

end BtoA

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun ε ε' => ⟨fun _ hb => (ε.coordChange_continuousAt ε' hb).continuousWithinAt,
      fun _ hb => ε'.coord_ne_zero hb.2 (ε.wedgeAt_ne_zero hb.1)⟩,
    fun Λ o => transport_eq_of_B hB Λ o,
    fun Λ => transport_injective_of_B hB Λ,
    fun Λ o γ => transport_eq_of_B hB (Λ.comp γ) (o.comp γ)⟩

#rt_check_soft RoundTrip.V6_35.A_to_B [Polyfold.SubspaceFamily.Frame.coordChange_continuousOn,
  Polyfold.SubspaceFamily.transport_eq, Polyfold.SubspaceFamily.transport_injective,
  Polyfold.SubspaceFamily.transport_comp]
#rt_check_soft RoundTrip.V6_35.B_to_A [Polyfold.SubspaceFamily.Frame.coordChange_continuousOn,
  Polyfold.SubspaceFamily.transport_eq, Polyfold.SubspaceFamily.transport_injective,
  Polyfold.SubspaceFamily.transport_comp]
#rt_overlap RoundTrip.V6_35.B_to_A [Polyfold.SubspaceFamily.Frame.coordChange_continuousOn,
  Polyfold.SubspaceFamily.transport_eq, Polyfold.SubspaceFamily.transport_injective,
  Polyfold.SubspaceFamily.transport_comp]

end RoundTrip.V6_35
