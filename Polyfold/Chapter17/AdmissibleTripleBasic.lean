import Polyfold.Chapter17.PolyfoldLevels

/-!
# Basic facts on admissible triples (2021 §17.1, pp. 768, 789)

For an admissible triple `T` of a morphism `a ∈ M(Ψ, Ψ')` (the open set `W(h)` around `a` on which
`s` is an sc-diffeomorphism onto `W(ō)`), the elementary facts about the local inverse `T.srcInv` of
`s` used by the tangent construction (§17.2) and the tame boundary category (§17.4).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

universe u

namespace Polyfold

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction}

namespace AdmissibleTriple

variable {Ψ Ψ' : S.Unif} {a : S.Tr Ψ Ψ'} (T : S.AdmissibleTriple a)

theorem isOpen_srcSet : IsOpen T.srcSet := T.isScDiffeoOn_src.isOpen_target

theorem isOpen_carrier : IsOpen T.carrier := T.isScDiffeoOn_src.isOpen_source

theorem src_mem : a.src ∈ T.srcSet := T.isScDiffeoOn_src.mapsTo T.mem_carrier

theorem srcInv_eq {b : S.Tr Ψ Ψ'} (hb : b ∈ T.carrier) : T.srcInv b.src = b :=
  T.isScDiffeoOn_src.left_inv b hb

theorem src_srcInv {p : Ψ.1.O} (hp : p ∈ T.srcSet) : (T.srcInv p).src = p :=
  T.isScDiffeoOn_src.right_inv p hp

theorem srcInv_mem {p : Ψ.1.O} (hp : p ∈ T.srcSet) : T.srcInv p ∈ T.carrier :=
  T.isScDiffeoOn_src.mapsTo_inv hp

end AdmissibleTriple

end GCT.PolyfoldConstruction

end Polyfold
