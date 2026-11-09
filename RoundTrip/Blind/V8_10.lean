import Polyfold
/-! Blind formalization of V8_10 (the text's Part II, §8.1, Lemma 8.1.8 (2017: 8.7), pp. 362–364;
2017 pp. 262–263).

Text: if `(X, 𝐗)` is an ep-groupoid, then `(TX, T𝐗)` has the properness property.  (Proof: for
`x ∈ X₁` and `V(x)` with `t : s⁻¹(cl_X(V(x))) → X` proper (8.10), `t_T : s_T⁻¹(cl_{TX}(TV)) → TX`
is proper (8.11), by a sequence argument using that `Ts : T𝐔(φ) → TU(x)` is an
sc-diffeomorphism.)

Choices:
- Setting: `Obj Mor : Type` (universe 0), Hausdorff paracompact, `X : EpGroupoid Obj Mor` (the
  text's ep-groupoid: `RoundTrip/Blind/V7_3.lean`); tangent spaces (Part I's `TangentSpace`,
  whose topology is the one of the M-polyfold `tangentPolyfold`; tangent maps `tangentMap`) in
  `Type 1`.
- "the properness property" is Definition 7.3 (3) for `(TX, T𝐗)` with `s_T = Ts`, `t_T = Tt`
  (8.3): every `a ∈ TX` has an open neighbourhood `V(a)` with `t_T : s_T⁻¹(cl_{TX}(V(a))) → TX`
  proper; "proper" = continuous with compact preimages of compact sets (`IsProperB`, as in
  `RoundTrip/Blind/V7_3.lean`), the domain with the subspace topology of `T𝐗`.  `s`, `t`
  sc-smooth is asserted (∃ of the proofs).
- Not formalized (proof only): the specific neighbourhoods `V(a) = TV(x)` and (8.11).
- Nothing looks false to me.
-/
namespace RoundTrip.V8_10
open Polyfold

universe u

/-- A proper map: continuous, with compact preimages of compact sets. -/
def IsProperB {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α → β) : Prop :=
  Continuous f ∧ ∀ K : Set β, IsCompact K → IsCompact (f ⁻¹' K)

/-- Lemma 8.1.8: `(TX, T𝐗)` has the properness property of Definition 7.3 (3). -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    ∃ (hs : X.PMor.IsScSmoothMap X.PObj X.src) (ht : X.PMor.IsScSmoothMap X.PObj X.tgt),
      ∀ a : X.PObj.TangentSpace, ∃ V : Set X.PObj.TangentSpace, IsOpen V ∧ a ∈ V ∧
        IsProperB ((MPolyfold.tangentMap hs ⁻¹' closure V).domRestrict (MPolyfold.tangentMap ht))

end RoundTrip.V8_10
