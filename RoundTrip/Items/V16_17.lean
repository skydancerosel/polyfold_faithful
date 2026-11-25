import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V16_17

set_option maxSynthPendingDepth 3

/-! Round trip for V16_17 (2021 Lemma 16.2.2, p. 718; 2017: Lemma 16.4: the topology of
`T(Z, c)`).

The item lists the instance `PolyfoldClass.tangentSpaceTopology` (the topology of `|TX₀|`,
`(X₀, α₀) = c.out`, vocabulary) and the theorem `PolyfoldClass.lemma_16_2_2`; `A` is its type at
universe `0` (`Z : Type`, so `T(Z, c) : Type 1`).  `A`: (i) every `Tα` is a homeomorphism for
the instance topology; (ii) a topology for which **one** `Tα` is a homeomorphism is the instance
topology; (iii) the instance topology is metrizable.  `B`: there is exactly one topology `τ` for
which **every** `Tα` is a homeomorphism, and every such `τ` is metrizable.
* `A_to_B`: `τ :=` the instance, by (i); uniqueness by (ii) applied to `c.out`; metrizability:
  such a `τ` is the instance (ii), then (iii).
* `B_to_A`: the instance topology makes every `Tα` a homeomorphism
  (`PolyfoldClass.isHomeomorph_tangentMap`, a non-item project lemma: `Tα = |T𝔣|` for a generalized
  isomorphism `𝔣`) — `B` says a unique such topology exists but does not name it, so this link is
  needed and is not from `B`.  (ii): if `t` makes one `Tα` a homeomorphism, then it makes every
  `Tβ` one, since `Tβ = Tα ∘ |Th|` with `|Th|` a homeomorphism (`tangentMap_comp`,
  `isGeneralizedIso_tangentHom`, `isHomeomorph_orbitMap_of_isGeneralizedIso`, `ScForm.exists_iso`,
  non-item lemmas), and `B`'s uniqueness gives `t =` the instance.  (iii) from `B`'s metrizability
  applied to the instance. -/

namespace RoundTrip.V16_17
open Polyfold EPLocalization EPLocalization.EPLoc

/-- The project's statement (universe `0`). -/
def A : Prop := type_of% @Polyfold.PolyfoldClass.lemma_16_2_2.{0}

theorem A_holds : A := @Polyfold.PolyfoldClass.lemma_16_2_2.{0}

theorem A_to_B : A → B := by
  intro hA Z _ c
  obtain ⟨h1, h2, h3⟩ := hA c
  have hall : ∀ τ : TopologicalSpace c.TangentSpace, AllTαHomeo c τ →
      τ = PolyfoldClass.tangentSpaceTopology c :=
    fun τ hτ => h2 τ ⟨c.out, Quotient.out_eq c, hτ c.out (Quotient.out_eq c)⟩
  refine ⟨⟨PolyfoldClass.tangentSpaceTopology c, h1, hall⟩, fun τ hτ => ?_⟩
  rw [hall τ hτ]
  exact h3

/-- A topology for which one `Tα` is a homeomorphism makes every `Tβ` one. -/
theorem allTαHomeo_of_one {Z : Type} [TopologicalSpace Z] (c : PolyfoldClass Z)
    (t : TopologicalSpace c.TangentSpace) (q : PolyfoldStructure Z) (hq : ⟦q⟧ = c)
    (ht : @IsHomeomorph _ _ _ t (PolyfoldClass.tangentMap q hq)) : AllTαHomeo c t := by
  intro p hp
  obtain ⟨h, hh, hβ⟩ := PolyfoldClass.ScForm.exists_iso hp hq
  have e := PolyfoldClass.tangentMap_comp hp hq hh hβ
  rw [← e]
  exact @IsHomeomorph.comp _ _ _ _ _ t _ _ ht
    (isHomeomorph_orbitMap_of_isGeneralizedIso (isGeneralizedIso_tangentHom hh))

theorem B_to_A : B → A := by
  intro hB Z _ c
  obtain ⟨⟨τ, hτ, huniq⟩, hmet⟩ := hB Z c
  have hinst : AllTαHomeo c (PolyfoldClass.tangentSpaceTopology c) :=
    fun q hq => PolyfoldClass.isHomeomorph_tangentMap q hq
  have hτ' : PolyfoldClass.tangentSpaceTopology c = τ := huniq _ hinst
  refine ⟨hinst, fun t ⟨q, hq, ht⟩ => ?_, hmet _ hinst⟩
  rw [hτ']
  exact huniq t (allTαHomeo_of_one c t q hq ht)

#rt_check RoundTrip.V16_17.A_to_B [Polyfold.PolyfoldClass.lemma_16_2_2]
#rt_check RoundTrip.V16_17.B_to_A [Polyfold.PolyfoldClass.lemma_16_2_2]
#rt_overlap RoundTrip.V16_17.B_to_A [Polyfold.PolyfoldClass.lemma_16_2_2]

end RoundTrip.V16_17
