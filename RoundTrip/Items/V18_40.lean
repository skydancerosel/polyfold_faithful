import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V18_40

/-! Round trip for V18_40 (2021, the construction on p. 854 and Proposition 18.4.3, p. 855;
2017: Proposition 18.1).

The item lists `exists_atomicData`, `proposition_18_4_3`, `proposition_18_4_3_formula` and the
example `ReflectionBundle.proposition_18_4_3_witness`; `A` is the conjunction of their types, the
first three at universe `0`.  The main conjunct is `proposition_18_4_3`.

Neither direction is proved.  The two statements are about different objects:

* `A` (`proposition_18_4_3`) is an **existence** statement in a model: for a covering family
  `c` of strong bundle uniformizers, a smooth `w ∈ W_x` over a smooth point `x` of `X_Ψ` and
  `e ≅ Γ̄(w)`, there is SOME `Λ : E → ℚ⁺` which is an sc⁺-multisection functor, `Λ(e) > 0`,
  `Γ̄^*Λ` atomic in the model of `c`, structurable.  The `Λ` is built in the model from a natural
  representation of `G_x` (`exists_atomicData`, Theorem 13.5.4 (1)); `proposition_18_4_3_formula`
  records its values in that model.
* `B` speaks of the **explicit function** `lam Ψ̄ s β` of p. 854 built in one strong bundle
  uniformizer `Ψ̄ ∈ F̄(α)` from a given local sc⁺-section `s` and ANY sc-smooth bump
  `β : O → [0, 1]` with `β(q₀) = 1` and support in a suitable `W ∋ q₀`, and asserts: independence
  of the choice of `(q, φ)`, sc⁺-multisection functor, `Λ(e) > 0`, atomic in the model of EVERY
  family `c ⊔ {Ψ̄}`, structurable.

`A → B` needs these properties for `lam`, which `A` (an existence statement about another
function) does not give: it is the whole proof of the proposition in a uniformizer (the
natural representation `G ⋉ O` inside every model `c ⊔ {Ψ̄}`, the sections `s_g`, atomicity).
`B → A` needs, from the model data `(c, w)`, a strong bundle uniformizer `Ψ̄ ∋ α` with a local
sc⁺-section through `e`, an sc-smooth bump `β` on `O` with small support (from
`S.AdmitsModelBumpFunctions`, which is stated in a model), `Q.HasStrongBundleUniformizers`
(a hypothesis of `B` that `A` does not have), and atomicity in the model of `c` itself rather
than of `c ⊔ {Ψ̄}`; and `B` says nothing about `AtomicData` (`exists_atomicData`,
`proposition_18_4_3_formula`).  Both directions are believed to hold mathematically
(re-proving substantial parts of §13.5 and §17), and are not attempted. -/

namespace RoundTrip.V18_40
open Polyfold

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.exists_atomicData.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3.{0}) ∧
  (type_of%
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3_formula.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.proposition_18_4_3_witness)

theorem A_holds : A :=
  ⟨@Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.exists_atomicData.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3_formula.{0},
    @Polyfold.GCT.VectorBundle.ReflectionBundle.proposition_18_4_3_witness⟩


end RoundTrip.V18_40
