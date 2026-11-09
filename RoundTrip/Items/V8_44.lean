import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_44

/-! Round trip for V8_44 (2021 Proposition 8.1.16, p. 369: the Zhou condition for `TX`).

`A` is the conjunction of the types of the six listed theorems, universes at `0`:
`MPolyfold.levelVal_tangentProj_mem_smoothSet`, `EpGroupoid.mem_nonEffectivePart_tangent`,
`EpGroupoid.proposition_8_1_16` (`X.IsZhou → X.TangentZhouReflect → TX.IsZhou`),
`EpGroupoid.tangentMor_trivial`, `EpGroupoid.tangentZhouReflect_trivial` and
`EpGroupoid.Examples.proposition_8_1_16_point` (no universe parameters).  The listed
`EpGroupoid.TangentZhouReflect` is a definition (vocabulary).

* `B → A` (proved): `proposition_8_1_16` is `B` with its extra hypothesis
  `TangentZhouReflect` dropped; the point example is `B` at `pointEpGroupoid` (with the non-item
  `isZhou_trivial`).  The other four conjuncts are lemmas/witnesses, not consequences of `B`;
  they are re-proved outright (copies of short proofs from non-item lemmas).
* `A → B` (not proved): `A`'s theorem needs `TangentZhouReflect X` — the step
  "`T(g, h) = id` on `T_b(TX)` ⇒ `Tg = id` on `T_{p(b)}X`" of the text's proof (differentiate
  (8.16), use that `Tτ_X` is onto).  `B` supplies only `X.IsZhou`.  `TangentZhouReflect` is
  satisfiable (trivial ep-groupoids) and believed to hold always, but proving it needs the second
  tangent bundle calculus (`Tτ_X : T(TX) → TX` onto, the chain rule for `T(Ts)`, `T(Tt)`), which
  the project does not formalize. -/

namespace RoundTrip.V8_44
open Polyfold Set Function Topology Filter

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.levelVal_tangentProj_mem_smoothSet.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.mem_nonEffectivePart_tangent.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.proposition_8_1_16.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tangentMor_trivial.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tangentZhouReflect_trivial.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.Examples.proposition_8_1_16_point)

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.levelVal_tangentProj_mem_smoothSet.{0},
    @Polyfold.EpGroupoid.mem_nonEffectivePart_tangent.{0},
    @Polyfold.EpGroupoid.proposition_8_1_16.{0},
    @Polyfold.EpGroupoid.tangentMor_trivial.{0},
    @Polyfold.EpGroupoid.tangentZhouReflect_trivial.{0},
    @Polyfold.EpGroupoid.Examples.proposition_8_1_16_point⟩

/-! ### Outright re-proofs of the lemma/witness conjuncts (not consequences of `B`) -/

section Outright

theorem levelVal_mem_smoothSet' {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) {b : P.TangentSpace} (hb : b ∈ P.tangentPolyfold.smoothSet) :
    P.levelVal 1 (P.tangentProj b) ∈ P.smoothSet := by
  refine (MPolyfold.mem_shift_smoothSet_iff (P.tangentProj b)).1 (mem_iInter.2 fun m => ?_)
  exact P.tangentProj_isScSmooth.mapsTo_levelSet m (mem_iInter.1 hb m)

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

theorem mem_nonEffectivePart_tangent' (X : EpGroupoid Obj Mor) {v : X.PMor.TangentSpace}
    (h : X.tBase v ∈ X.nonEffectivePart) : v ∈ X.tangentEpGroupoid.nonEffectivePart := by
  rw [X.tangentEpGroupoid.mem_nonEffectivePart_iff]
  obtain ⟨N, hNs, hNo, hvN⟩ := mem_nhds_iff.1 (X.mem_nonEffectivePart_iff.1 h)
  have hs := X.isScSmoothMap_src.mono hNo (subset_univ N)
  have ht := X.isScSmoothMap_tgt.mono hNo (subset_univ N)
  filter_upwards [(MPolyfold.isOpen_tangentPreimage hNo).mem_nhds hvN] with ψ hψ
  change MPolyfold.tangentMap X.isScSmoothMap_src ψ = MPolyfold.tangentMap X.isScSmoothMap_tgt ψ
  rw [← MPolyfold.tangentMapOn_eq_tangentMap X.isScSmoothMap_src hs hψ,
    ← MPolyfold.tangentMapOn_eq_tangentMap X.isScSmoothMap_tgt ht hψ]
  exact MPolyfold.tangentMapOn_congr hs ht hNo subset_rfl subset_rfl (fun φ hφ => hNs hφ) hψ

open scoped Classical in
theorem tangentMor_trivial' {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (P : MPolyfold Z) (φ : Z) (v : P.TangentSpace) : (EpGroupoid.trivial P).tangentMor φ v = v := by
  unfold EpGroupoid.tangentMor
  exact dite_eq_right_iff.2 fun hv => hv.choose_spec.2

end Outright

/-! ### `B → A` -/

theorem B_to_A : B → A :=
  fun hB => ⟨@levelVal_mem_smoothSet', @mem_nonEffectivePart_tangent',
    fun X hZ _ => hB _ _ X hZ, @tangentMor_trivial',
    fun P _ _ _ v _ => tangentMor_trivial' P _ v,
    hB Unit Unit EpGroupoid.Examples.pointEpGroupoid (EpGroupoid.isZhou_trivial _)⟩

/-! ### `A → B`: not proved

`A`'s `proposition_8_1_16` concludes `TX.IsZhou` only under `TangentZhouReflect X`, which `B`
does not provide; deriving it from `X.IsZhou` (or outright) is the unformalized second-tangent
step of the text's proof. -/

#rt_check RoundTrip.V8_44.B_to_A [Polyfold.MPolyfold.levelVal_tangentProj_mem_smoothSet,
  Polyfold.EpGroupoid.mem_nonEffectivePart_tangent, Polyfold.EpGroupoid.proposition_8_1_16,
  Polyfold.EpGroupoid.tangentMor_trivial, Polyfold.EpGroupoid.tangentZhouReflect_trivial,
  Polyfold.EpGroupoid.Examples.proposition_8_1_16_point]
#rt_overlap RoundTrip.V8_44.B_to_A [Polyfold.MPolyfold.levelVal_tangentProj_mem_smoothSet,
  Polyfold.EpGroupoid.mem_nonEffectivePart_tangent, Polyfold.EpGroupoid.proposition_8_1_16,
  Polyfold.EpGroupoid.tangentMor_trivial, Polyfold.EpGroupoid.tangentZhouReflect_trivial,
  Polyfold.EpGroupoid.Examples.proposition_8_1_16_point]

end RoundTrip.V8_44
