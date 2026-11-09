import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_47

/-! Round trip for V8_47 (2021 Proposition 8.4.1, p. 380: `|X|`, `|W[0]|`, `|W[1]|` paracompact
together).

`A` is the conjunction of the types of the five listed theorems, universes at `0`:
`EpStrongBundle.μ_fiberZero`, `continuous_zeroOrbitMap`, `leftInverse_zeroOrbitMap`,
`isEmbedding_zeroOrbitMap` (the zero section `|0| : |X| → |W|` is an embedding) and
`proposition_8_4_1_2021_two_imp_one` (`|W[0]|` paracompact ⇒ `|X|` paracompact, for the
ep-groupoid `E.toEpGroupoid`, under the instance `ParacompactSpace (𝐗 ₛ×_P W)`).  The listed
`zeroOrbitMap` is a definition (vocabulary).

* `B → A` (proved): `proposition_8_4_1_2021_two_imp_one` is `B`'s (2) ⇒ (1)
  (`E.toEpGroupoid.OrbitSpace` is literally `E.toGroupoidStr.OrbitSpace` with the quotient
  topology of `W`).  The other four conjuncts are lemmas about the zero section, not consequences
  of `B`; re-proved outright (copies of short proofs from non-item lemmas).
* `A → B` (not proved): `A` contains only the implication (2) ⇒ (1).  The instance
  `ParacompactSpace (𝐗 ₛ×_P W)` it needs is a theorem (`StrongBundle.paracompactSpace_pullback`),
  so `A` does give `B`'s (2) ⇒ (1); but (1) ⇒ (2) and everything about `|W[1]|`
  (`E.OneOrbitSpace`) are absent from the project: they would need the paracompactness of the
  orbit space of `(W, 𝐖)` (resp. of `W[1]`) from that of `|X|`, real mathematics not formalized. -/

namespace RoundTrip.V8_47
open Polyfold Function

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpStrongBundle.μ_fiberZero.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.continuous_zeroOrbitMap.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.leftInverse_zeroOrbitMap.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.isEmbedding_zeroOrbitMap.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.proposition_8_4_1_2021_two_imp_one.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.μ_fiberZero.{0},
    @Polyfold.EpStrongBundle.continuous_zeroOrbitMap.{0},
    @Polyfold.EpStrongBundle.leftInverse_zeroOrbitMap.{0},
    @Polyfold.EpStrongBundle.isEmbedding_zeroOrbitMap.{0},
    @Polyfold.EpStrongBundle.proposition_8_4_1_2021_two_imp_one.{0}⟩

/-! ### Outright re-proofs of the zero-section lemmas (not consequences of `B`) -/

section Outright
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

theorem μ_fiberZero' (E : EpStrongBundle X B) (φ : Mor) :
    E.μ ⟨(φ, fiberZero P (X.src φ)), isSection_fiberZero (X.src φ)⟩ = fiberZero P (X.tgt φ) := by
  have h0 := congrArg Subtype.val ((E.fiberMor φ).map_zero)
  rw [EpStrongBundle.fiberMor_apply] at h0
  exact h0

variable [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B)

/-- The compatibility of `x ↦ |0_x|` with `≈`, proved here (with `μ_fiberZero'`) so that the
continuity proof below does not pick up `zeroOrbitMap`'s own proof field. -/
theorem zeroOrbit_compat (a b : Obj) (hab : X.orbitSetoid.r a b) :
    E.toEpGroupoid.π (fiberZero P a) = E.toEpGroupoid.π (fiberZero P b) := by
  obtain ⟨φ, rfl, rfl⟩ := hab
  exact E.toEpGroupoid.π_eq_π_iff.2
    ⟨⟨(φ, fiberZero P (X.src φ)), isSection_fiberZero (X.src φ)⟩, rfl, μ_fiberZero' E φ⟩

theorem continuous_zeroOrbitMap' : Continuous E.zeroOrbitMap :=
  continuous_quot_lift (f := fun x => E.toEpGroupoid.π (fiberZero P x)) (zeroOrbit_compat E)
    (E.toEpGroupoid.continuous_π.comp
      (continuousOn_univ.1 (B.isScSmoothSection_fiberZero).2.continuousOn))

theorem leftInverse_zeroOrbitMap' : LeftInverse E.projFunctor.orbitMap E.zeroOrbitMap := by
  intro z
  induction z using Quotient.ind with
  | _ x => exact congrArg X.π (isSection_fiberZero (P := P) x)

theorem isEmbedding_zeroOrbitMap' : Topology.IsEmbedding E.zeroOrbitMap :=
  (leftInverse_zeroOrbitMap' E).isEmbedding E.continuous_orbitMap_projFunctor
    (continuous_zeroOrbitMap' E)

end Outright

/-! ### `B → A` -/

theorem B_to_A : B → A := by
  intro hB
  refine ⟨@μ_fiberZero', @continuous_zeroOrbitMap', @leftInverse_zeroOrbitMap',
    @isEmbedding_zeroOrbitMap', ?_⟩
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ Bd _ E h
  exact ((hB Obj Mor X W P Bd E).out 1 0).1 h

/-! ### `A → B`: not proved

`A` has only (2) ⇒ (1) (usable here: its instance hypothesis is
`StrongBundle.paracompactSpace_pullback`); (1) ⇒ (2) and the equivalence with (3) (`|W[1]|`)
are not in the project. -/

-- `#rt_check` fails only because `zeroOrbitMap` (in `A`'s statement) proves its `Quotient.lift`
-- compatibility with `μ_fiberZero`; the soft check confirms that this is the only route.
#rt_check_soft RoundTrip.V8_47.B_to_A [Polyfold.EpStrongBundle.μ_fiberZero,
  Polyfold.EpStrongBundle.continuous_zeroOrbitMap, Polyfold.EpStrongBundle.leftInverse_zeroOrbitMap,
  Polyfold.EpStrongBundle.isEmbedding_zeroOrbitMap,
  Polyfold.EpStrongBundle.proposition_8_4_1_2021_two_imp_one]
#rt_overlap RoundTrip.V8_47.B_to_A [Polyfold.EpStrongBundle.μ_fiberZero,
  Polyfold.EpStrongBundle.continuous_zeroOrbitMap, Polyfold.EpStrongBundle.leftInverse_zeroOrbitMap,
  Polyfold.EpStrongBundle.isEmbedding_zeroOrbitMap,
  Polyfold.EpStrongBundle.proposition_8_4_1_2021_two_imp_one]

end RoundTrip.V8_47
