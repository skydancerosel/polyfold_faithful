import Polyfold
/-! Blind formalization of V11_4 (the text's Part II, §11.1, Example 11.1.4, p. 523 of the
Springer 2021 book; 2017: Example 11.1, p. 377).

Text: `[0, ∞)²` with only identities is face structured; with `ℤ/2` exchanging the coordinates it
is weakly face structured and not face structured.

Choices:
- `[0, ∞)²`: the project's quadrant `quadrant 2 W₀ 0 = [0, ∞)² ⊕ W₀` in `ℝ² ⊕ W₀` with
  `W₀ = ScBanach.const (Fin 0 → ℝ)` the zero sc-Banach space (so it is `[0, ∞)² × {0}`), with its
  M-polyfold structure `MPolyfold.quadrantPolyfold 2 W₀` (the identity chart of the partial
  quadrant; trusted as the standard structure).  Topology: the subspace topology (`#synth`ed).
- "with only identities" (`IsIdOnlyB`): an ep-groupoid `E` with objects and morphisms
  `[0, ∞)²`, object M-polyfold the quadrant, `s = t = u = id` (every morphism is an identity;
  `comp`, `inv` are then forced).
- "with `ℤ/2` exchanging the coordinates" (`IsSwapB`): the translation groupoid `ℤ/2 ⋉ [0, ∞)²`,
  `ℤ/2` as `ℤˣ = {1, -1}` (discrete), morphisms `(g, x) : x → g·x`, `-1` acting by
  `(a₁, a₂) ↦ (a₂, a₁)` (`swapB`); B fixes the object M-polyfold and `s, t, u, inv, comp` of the
  translation groupoid.  The morphism M-polyfold is left free (the claims depend only on the
  object M-polyfold and on `s`, `t`).
- B asserts, for each of the two groupoids, that one exists (the text presupposes that both are
  ep-groupoids; the project's `EpGroupoid.trivial` and `Examples.swapEpGroupoid W₀` are
  candidates) and that every ep-groupoid with the described structure has the claimed property.
- "face structured", "weakly face structured": Definition 11.1.3 as rendered in my
  `RoundTrip/Blind/V11_3.lean` (copied: `FaceStructuredB` = tame and every `z ∈ |X|` in exactly
  `d_{|X|}(z)` faces of `|X|`; `WeaklyFSB` = the tame object M-polyfold is face structured).
- Nothing looks false to me.
-/
namespace RoundTrip.V11_4
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `|x| ∈ |X|`, the orbit of `x`. -/
abbrev piB (X : EpGroupoid Obj Mor) (x : Obj) : X.OrbitSpace := Quotient.mk _ x

/-- `d_{|X|}(z) = d_X(x)` for a representative `x` of `z`. -/
noncomputable def degOrbB (X : EpGroupoid Obj Mor) (z : X.OrbitSpace) : ℕ :=
  X.PObj.degIndex z.out

/-- A face of `|X|`: the closure of a connected component of `{z | d_{|X|}(z) = 1}`. -/
def IsOrbitFaceB (X : EpGroupoid Obj Mor) (θ : Set X.OrbitSpace) : Prop :=
  ∃ s : {z : X.OrbitSpace // degOrbB X z = 1},
    θ = closure (Subtype.val '' connectedComponent s)

/-- `X` is face structured: tame, and every `z ∈ |X|` lies in exactly `d_{|X|}(z)` faces. -/
def FaceStructuredB (X : EpGroupoid Obj Mor) : Prop :=
  X.PObj.IsTame ∧
    ∀ z : X.OrbitSpace, {θ | IsOrbitFaceB X θ ∧ z ∈ θ}.encard = (degOrbB X z : ℕ∞)

/-- A face of an M-polyfold: the closure of a connected component of `{x | d(x) = 1}`. -/
def IsFaceMB (P : MPolyfold Obj) (F : Set Obj) : Prop :=
  ∃ s : {y : Obj // P.degIndex y = 1}, F = closure (Subtype.val '' connectedComponent s)

/-- A face-structured M-polyfold: every `x` lies in exactly `d(x)` faces. -/
def IsFaceStructuredMB (P : MPolyfold Obj) : Prop :=
  ∀ x : Obj, {F : Set Obj | IsFaceMB P F ∧ x ∈ F}.encard = (P.degIndex x : ℕ∞)

/-- `X` is weakly face structured: the (tame) object M-polyfold is face structured. -/
def WeaklyFSB (X : EpGroupoid Obj Mor) : Prop :=
  X.PObj.IsTame ∧ IsFaceStructuredMB X.PObj

end

/-- The zero sc-Banach space. -/
noncomputable abbrev W₀ : ScBanach := ScBanach.const (Fin 0 → ℝ)

/-- `[0, ∞)² = [0, ∞)² ⊕ {0}`. -/
abbrev QB : Type := ↑(quadrant 2 W₀ 0)

/-- The exchange of the two coordinates of `[0, ∞)²`. -/
noncomputable def swapB (p : QB) : QB :=
  ⟨((p.1.1 ∘ Equiv.swap (0 : Fin 2) 1 : Fin 2 → ℝ), p.1.2), fun _ => p.2 _⟩

/-- The action of `ℤ/2 = ℤˣ`: `1` acts trivially, `-1` exchanges the coordinates. -/
noncomputable def actB (g : ℤˣ) (p : QB) : QB := if g = 1 then p else swapB p

/-- `E` is `[0, ∞)²` with only identities. -/
def IsIdOnlyB (E : EpGroupoid QB QB) : Prop :=
  E.PObj = MPolyfold.quadrantPolyfold 2 W₀ ∧ ∀ p : QB, E.src p = p ∧ E.tgt p = p ∧ E.unit p = p

/-- `E` is the translation groupoid `ℤ/2 ⋉ [0, ∞)²` of the coordinate exchange. -/
def IsSwapB (E : EpGroupoid QB (ℤˣ × QB)) : Prop :=
  E.PObj = MPolyfold.quadrantPolyfold 2 W₀ ∧
  (∀ (g : ℤˣ) (p : QB), E.src (g, p) = p ∧ E.tgt (g, p) = actB g p) ∧
  (∀ p : QB, E.unit p = (1, p)) ∧
  (∀ (g : ℤˣ) (p : QB), E.inv (g, p) = (g⁻¹, actB g p)) ∧
  (∀ (g h : ℤˣ) (p : QB), E.comp (h, actB g p) (g, p) = (h * g, p))

/-- Example 11.1.4: `[0, ∞)²` with only identities is face structured; `ℤ/2 ⋉ [0, ∞)²` (coordinate
exchange) is weakly face structured but not face structured. -/
def B : Prop :=
  (∃ E : EpGroupoid QB QB, IsIdOnlyB E) ∧
  (∀ E : EpGroupoid QB QB, IsIdOnlyB E → FaceStructuredB E) ∧
  (∃ E : EpGroupoid QB (ℤˣ × QB), IsSwapB E) ∧
  (∀ E : EpGroupoid QB (ℤˣ × QB), IsSwapB E → WeaklyFSB E ∧ ¬ FaceStructuredB E)

end RoundTrip.V11_4
