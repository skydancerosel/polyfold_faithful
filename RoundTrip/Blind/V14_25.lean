import Polyfold
/-! Blind formalization of V14_25 (the Springer 2021 book, Part II, §14.4, Proposition 14.4.6,
p. 661; 2017: Proposition 14.5).

Text: for `a ∈ A` and `z ∈ V̂_a`: (1) if `i ∼_{z₀} i'` then `i ∼_z i'` for all `z ∈ V̂_a` near
`z₀`; (2) if `z_k ∈ V_a = V̂_a ∩ ∂X`, `i ∼_{z_k} i'` and `z_k → z₀ ∈ cl_X(V_a)`, then
`s^{0a}_i = s^{0a}_{i'}` on an open `Q(z₀) ⊆ U(a)`.

Choices:
- Setting: universe 0; the strong bundle over the ep-groupoid is `A : SEP.{0}`.  The objects of
  §14.4 are those built in §14.3 (proof of Theorem 14.1.9) from a structured sc⁺-multisection
  over `∂X`: I take the project's `ZConcrete E Q` (its docstring: the data of Proposition 14.3.8
  for a structured tuple `T` over `∂X`, the (P5) neighbourhoods `P`, the correspondence extension
  `E`, the (P6) neighbourhoods `Q`: the set `A ⊆ ∂X`, `Ũ(a)`, the open invariant `V̂_a` with
  `(|V̂_a|)` locally finite, the extended correspondences `τ̂_{a,a'}`), arbitrary.  From it,
  `S = C.toZData` (the index set `A = S.A`, `Ũ(a) = (S.nbhd a).U`, `V̂_a = S.V a`, `I_a = S.I a`,
  `τ̂ = S.τ`) and `D = C.toZSections` (the boundary sections `s^{0a}_i = D.s a i`, the sections
  `sˣᵢ` of `T` at `x = a`).  These are project constructions; I could not state §14.4 without
  its data.
- The standing hypotheses of §§14.2–14.5 (those of Theorem 14.1.9 on `X`): tame, paracompact
  orbit space, sc-smooth partitions of unity (ep-groupoid notion), added since the text
  presupposes them.
- `i ∼_z i'` (Definition 14.4.4): the project's `ZSetup.ZRel S a z i i'` (a z-loop for `a` and a
  z-arc along it from `i` to `i'`).
- (1): for `a ∈ A`, `z₀ ∈ V̂_a`, `i, i' ∈ I_a` with `i ∼_{z₀} i'`, there is an open `O ∋ z₀` with
  `i ∼_z i'` for all `z ∈ O ∩ V̂_a` ("for all `z ∈ V̂_a` near `z₀`").
- (2): `V_a = V̂_a ∩ ∂X`; a sequence `z_k ∈ V_a` with `i ∼_{z_k} i'` (fixed `i, i'`),
  `z_k → z₀` in `X` and `z₀ ∈ cl_X(V_a)` (kept as printed, though it follows); `U(a) = Ũ(a) ∩ ∂X`.
  "on an open `Q(z₀) ⊆ U(a)`": an open neighbourhood of `z₀` in `U(a)`, i.e. `Q ∩ U(a)` for an
  open `Q ∋ z₀` of `X`; the sections agree at every point of `Q ∩ U(a)`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V14_25
open Polyfold Polyfold.SBLocalization Filter Topology

/-- Proposition 14.4.6: local constancy of `∼_z`, and agreement of the boundary sections at
limits. -/
def B : Prop :=
  ∀ (A : SEP.{0}) (T : BoundaryStructuredTuple A) (P : P5Nbhds T) (E : CorrExtension T P)
    (Q : P.P6Nbhds) (C : ZConcrete E Q),
    A.X.IsTame → A.X.HasParacompactOrbitSpace → A.X.HasScPartitionsOfUnity →
    -- (1)
    (∀ a ∈ C.toZData.A, ∀ z₀ ∈ C.toZData.V a, ∀ i i' : C.toZData.I a,
      C.toZData.ZRel a z₀ i i' →
      ∃ O : Set A.Obj, IsOpen O ∧ z₀ ∈ O ∧
        ∀ z ∈ O ∩ C.toZData.V a, C.toZData.ZRel a z i i') ∧
    -- (2)
    (∀ a ∈ C.toZData.A, ∀ i i' : C.toZData.I a, ∀ (zs : ℕ → A.Obj) (z₀ : A.Obj),
      (∀ k, zs k ∈ C.toZData.V a ∩ A.X.PObj.boundary) →
      (∀ k, C.toZData.ZRel a (zs k) i i') →
      Tendsto zs atTop (𝓝 z₀) →
      z₀ ∈ closure (C.toZData.V a ∩ A.X.PObj.boundary) →
      ∃ O : Set A.Obj, IsOpen O ∧ z₀ ∈ O ∧
        ∀ y ∈ O ∩ ((C.toZData.nbhd a).U ∩ A.X.PObj.boundary),
          C.toZSections.s a i y = C.toZSections.s a i' y)

end RoundTrip.V14_25
