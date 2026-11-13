import Polyfold.Chapter16.P3W4PB_Multisections
import Polyfold.Chapter13.P3W4FN_Pushforward

/-!
# Definition 16.5.4: structurability is invariant under generalized isomorphisms

HWZ 2021, §16.5, Definition 16.5.4, p. 734 (2017: Definition 16.37): a polyfold multisection is
structurable "if one, and therefore all, representatives are". The step "therefore all" is the
Prop `StructurablePullback` (`P3W4PB_Multisections`). It follows from Theorems 13.4.1 and 13.4.3
for generalized strong bundle isomorphisms (`GenSBMap.isStructurable_pullMult`,
`P3W4FN_Pushforward`).

Part III wave 4 (agent FN; copied from FN's scratch check by the integrator, 2026-11-13).
-/

open Polyfold

namespace Polyfold

/-- `StructurablePullback` holds: pull-backs of structurable sc⁺-multisections along generalized
strong bundle isomorphisms are structurable (Theorems 13.4.1 and 13.4.3). -/
theorem fnStructurablePullback : Polyfold.StructurablePullback := fun _ _ _ hF _ h =>
  SBLocalization.GenSBMap.isStructurable_pullMult hF h

namespace StrongPolyfoldBundle.ScPlusMultisection

universe u

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- **2021 Definition 16.5.4, p. 734 (2017: Definition 16.37)**, "one, and therefore all":
`definition_16_5_4_hyp` with `StructurablePullback` discharged by `fnStructurablePullback`. -/
theorem definition_16_5_4 (s : ScPlusMultisection c) :
    s.IsStructurable ↔
      ∀ a : MultisectionRep c, ⟦a⟧ = s → SBLocalization.IsStructurable a.S.A a.Λ :=
  definition_16_5_4_hyp fnStructurablePullback s

end StrongPolyfoldBundle.ScPlusMultisection

end Polyfold
