import Polyfold
/-! Blind formalization of V7_10 (the text's Part II, §7.1, the remark after Definition 7.7,
pp. 228–229 of the 2017 book).

Text: it suffices to require that the functor `f` is sc-smooth between the object spaces
`X → Y`: sc-smoothness of `f : 𝐗 → 𝐘` follows from the properties of `s`.  Given `φ ∈ 𝐗` and
`f(φ) = ψ` there are open neighbourhoods `𝐔(φ)`, `𝐔(ψ)`, `U(s(φ))`, `U(s(ψ))` with
`f(U(s(φ))) ⊂ U(s(ψ))` and `f(𝐔(φ)) ⊂ 𝐔(ψ)`, and `s : 𝐔(φ) → U(s(φ))`, `s : 𝐔(ψ) → U(s(ψ))`
sc-diffeomorphisms; hence the claim, from `f(γ) = (s|𝐔(ψ))⁻¹(f(s(γ)))` for `γ ∈ 𝐔(φ)`.

Choices:
- Setting: ep-groupoids `X : EpGroupoid Obj Mor`, `Y : EpGroupoid Obj' Mor'`, spaces in `Type`
  (universe 0), Hausdorff paracompact (`RoundTrip/Blind/V7_3.lean`).
- "the functor `f`": a pair `(f₀, f₁)` with `IsFunctorB` (commuting with `s`, `t`, composition on
  composable pairs, units; as in `RoundTrip/Blind/V7_9.lean`), with NO topological condition on
  `f₁` (the text requires nothing else).  "sc-smooth" is the project's `MPolyfold.IsScSmoothMap`.
- B is the conjunction of (main) `f₀` sc-smooth ⇒ `f₁` sc-smooth, and (local) the text's
  supporting claim: for every `φ` there are open `𝐔(φ) ∋ φ`, `𝐔(ψ) ∋ ψ = f₁(φ)`, `U(s φ)`,
  `U(s ψ)` with `s : 𝐔(φ) → U(s φ)` and `s : 𝐔(ψ) → U(s ψ)` sc-diffeomorphisms (the project's
  `IsScDiffeoOn`, inverses `σ`, `σ'`; then `s φ ∈ U(s φ)`, `s ψ ∈ U(s ψ)`), `f₀(U(s φ)) ⊆ U(s ψ)`,
  `f₁(𝐔(φ)) ⊆ 𝐔(ψ)`, and `f₁(γ) = σ'(f₀(s γ))` on `𝐔(φ)`.
- DOES NOT HOLD AS I READ IT (formalized literally anyway): the inclusion `f(𝐔(φ)) ⊂ 𝐔(ψ)` needs
  continuity of `f` on `𝐗`, which a functor sc-smooth on objects need not have.  Example:
  `X = Y = ℤ/2 ⋉ ℝ` with the trivial action (objects `ℝ`, morphisms `ℤ/2 × ℝ`, `s = t =` the
  projection; an ep-groupoid), `f₀ = id`, `f₁(g, x) = (g, x)` for `x ≤ 0` and `(0, x)` for
  `x > 0` (on each isotropy group `ℤ/2` either the identity or the trivial homomorphism).  This is
  a functor, `f₀` is sc-smooth, but `f₁` is not continuous at `(1, 0)`, so both conjuncts fail.
  With `f₁` continuous the text's argument goes through.
-/
namespace RoundTrip.V7_10
open Polyfold

/-- `(f₀, f₁)` is a functor between the groupoids `G` and `H`. -/
def IsFunctorB {Obj Mor Obj' Mor' : Type} (G : GroupoidStr Obj Mor) (H : GroupoidStr Obj' Mor')
    (f₀ : Obj → Obj') (f₁ : Mor → Mor') : Prop :=
  (∀ φ : Mor, H.src (f₁ φ) = f₀ (G.src φ)) ∧
  (∀ φ : Mor, H.tgt (f₁ φ) = f₀ (G.tgt φ)) ∧
  (∀ φ ψ : Mor, G.src φ = G.tgt ψ → f₁ (G.comp φ ψ) = H.comp (f₁ φ) (f₁ ψ)) ∧
  (∀ x : Obj, f₁ (G.unit x) = H.unit (f₀ x))

/-- The remark after Definition 7.7: a functor between ep-groupoids that is sc-smooth on objects
is sc-smooth on morphisms, via `f(γ) = (s|𝐔(ψ))⁻¹(f(s(γ)))` near every `φ` (literal). -/
def B : Prop :=
  ∀ (Obj Mor Obj' Mor' : Type)
    [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (f₀ : Obj → Obj') (f₁ : Mor → Mor'),
    IsFunctorB X.toGroupoidStr Y.toGroupoidStr f₀ f₁ → X.PObj.IsScSmoothMap Y.PObj f₀ →
      -- (main) `f` is sc-smooth on the morphism spaces
      X.PMor.IsScSmoothMap Y.PMor f₁ ∧
      -- (local) the neighbourhoods and the formula of the text
      (∀ φ : Mor, ∃ (Uφ : Set Mor) (Uψ : Set Mor') (Usφ : Set Obj) (Usψ : Set Obj')
          (σ : Obj → Mor) (σ' : Obj' → Mor'),
        IsOpen Uφ ∧ IsOpen Uψ ∧ IsOpen Usφ ∧ IsOpen Usψ ∧ φ ∈ Uφ ∧ f₁ φ ∈ Uψ ∧
        X.PMor.IsScDiffeoOn X.PObj X.src σ Uφ Usφ ∧
        Y.PMor.IsScDiffeoOn Y.PObj Y.src σ' Uψ Usψ ∧
        Set.MapsTo f₀ Usφ Usψ ∧ Set.MapsTo f₁ Uφ Uψ ∧
        ∀ γ ∈ Uφ, f₁ γ = σ' (f₀ (X.src γ)))

end RoundTrip.V7_10
