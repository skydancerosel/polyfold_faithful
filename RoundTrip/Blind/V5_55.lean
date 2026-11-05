import Polyfold
/-! Blind formalization of V5_55 (the text's §5.4.2, proof of Theorem 5.37, "(i) ⇒ (ii)",
pp. 195–196).

Text: for an atlas of charts `φ : U → O`, "the sc-smooth function `f ∘ φ`" extended by `0` is
supported in `W = φ⁻¹(V)` "satisfying `cl_X(W) ⊆ U`", and is approximated by `Σ β_x g(x)`.

Choices:
- Setting: `X : Type` (universe 0, as asked), Hausdorff paracompact, `PX : MPolyfold X`, as in
  `RoundTrip/Blind/V5_57.lean`.  Hypothesis (i): `PX.AdmitsScPartitionsOfUnity` (Definition 5.28,
  checked with `#print`; see `RoundTrip/Blind/V5_47.lean`).
- "an atlas of charts `φ : U → O`": every atlas `A` of the structure (`A.Equiv PX.atlas`) and every
  chart `φ ∈ A`, `U = dom φ`, `(O, C, E)` its local model.  The data of the proof are those of
  Definition 5.36 for `(O, C, E)`: `V = O ∩ W'` open in `O` with `cl_C(V) = cl_E(V) ∩ C ⊆ O`, `f`
  continuous on `O` with values in `[0, 1]` and `supp_O(f) = cl_E(O ∩ {f ≠ 0}) ∩ O ⊆ V`.
- `W = φ⁻¹(V) = U ∩ φ⁻¹(V)` (`chartPre`); `cl_X(W)` the closure in `X`.  "`f ∘ φ` extended by `0`":
  `ĝ = f ∘ φ` on `U`, `0` off `U` (`extByZero`); "supported in `W`": `cl_X{ĝ ≠ 0} ⊆ W`.
- "approximated by `Σ β_x g(x)`" (`IsApproximatedB`), for every `ε > 0`: an sc-smooth partition of
  unity `(β_x)_{x ∈ X}` indexed by the points of `X` (sc-smooth `X → ℝ` in the project's sense
  `PX.IsScSmoothMap realPolyfold`, `≥ 0`, locally finite supports, sum `1`; its subordinate cover
  is not quoted, so not fixed) such that `h = Σ_x β_x ĝ(x)` is sc-smooth, `[0, 1]`-valued,
  supported in `W` and `|h − ĝ| ≤ ε` on `X` — the properties needed to transport `h` back to `O`.
- B also contains the conclusion of the direction: every such `φ` has a local model with the
  sc-smooth approximation property (the project's `HasApproxProperty`, Definition 5.36, checked
  with `#print`; see `RoundTrip/Blind/V5_54.lean`).
- "the sc-smooth function `f ∘ φ`": formalized LITERALLY as `f ∘ φ` sc-smooth on `U`
  (`PX.IsScSmoothOn realPolyfold (f ∘ φ) U`).  I believe this is a MISPRINT for "continuous": `f`
  is only continuous, so `f ∘ φ` is not sc-smooth in general.  B is therefore FALSE as written.
- "`cl_X(W) ⊆ U`": formalized LITERALLY as a claim.  I believe it is FALSE in general: `X = ℝ`
  with the atlas `{id, φ}`, `φ : U = (0, 1) → O = ℝ` a smooth diffeomorphism, local model
  `(ℝ, ℝ, ℝ)`; `X` admits smooth partitions of unity; `V = O` satisfies `cl_C(V) = ℝ ⊆ O`, but
  `W = U` and `cl_X(W) = [0, 1] ⊄ U`.  (With `f ≡ 1` then `ĝ` is not even continuous and cannot
  be uniformly approximated by continuous `h` within `ε < 1/2`.)
- `BRepaired` (not the item): "sc-smooth" replaced by "continuous" (of `ĝ` on `X`) and
  `cl_X(W) ⊆ U` taken as an extra HYPOTHESIS; the conclusion `HasApproxProperty` kept.
-/
namespace RoundTrip.V5_55
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- An sc-smooth partition of unity `(β_λ)_{λ ∈ Λ}` on `X`: sc-smooth, non-negative, locally
finite supports, summing to `1`. -/
def IsScPOUB (PX : MPolyfold X) {Λ : Type} (β : Λ → X → ℝ) : Prop :=
  (∀ l, PX.IsScSmoothMap realPolyfold (β l)) ∧ (∀ l x, 0 ≤ β l x) ∧
  LocallyFinite (fun l => tsupport (β l)) ∧ ∀ x, ∑ᶠ l, β l x = 1

/-- `W = φ⁻¹(V)`, inside the domain `U` of `φ`. -/
def chartPre (φ : MChart X) (V : Set (φ.model.E.lvl 0)) : Set X :=
  φ.toPartialEquiv.source ∩ φ.toPartialEquiv ⁻¹' V

/-- `f ∘ φ` on the domain `U` of `φ`, extended by `0` to `X`. -/
noncomputable def extByZero (φ : MChart X) (f : φ.model.E.lvl 0 → ℝ) : X → ℝ :=
  Set.indicator φ.toPartialEquiv.source (fun x => f (φ.toPartialEquiv x))

/-- `ĝ` is approximated within `ε` by `h = Σ_x β_x ĝ(x)` for an sc-smooth partition of unity
`(β_x)_{x ∈ X}`, `h` sc-smooth, `[0, 1]`-valued and supported in `W`. -/
def IsApproximatedB (PX : MPolyfold X) (W : Set X) (g : X → ℝ) (ε : ℝ) : Prop :=
  ∃ β : X → X → ℝ, IsScPOUB PX β ∧
    PX.IsScSmoothMap realPolyfold (fun y => ∑ᶠ x, β x y * g x) ∧
    (∀ y, ∑ᶠ x, β x y * g x ∈ Set.Icc (0 : ℝ) 1) ∧
    tsupport (fun y => ∑ᶠ x, β x y * g x) ⊆ W ∧
    ∀ y, |(∑ᶠ x, β x y * g x) - g y| ≤ ε

end

/-- Theorem 5.37, (i) ⇒ (ii), as argued in the text: for a chart `φ : U → O` of an atlas and data
`V`, `f` of Definition 5.36, `cl_X(φ⁻¹(V)) ⊆ U`, the sc-smooth `f ∘ φ` extended by `0` is supported
in `φ⁻¹(V)` and is approximated by `Σ β_x g(x)`; and `(O, C, E)` has the approximation property. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X),
    PX.AdmitsScPartitionsOfUnity →
    ∀ A : MAtlas X, A.Equiv PX.atlas → ∀ φ ∈ A.charts,
      (∀ V : Set (φ.model.E.lvl 0), V ⊆ φ.model.O → (∃ W', IsOpen W' ∧ V = φ.model.O ∩ W') →
        closure V ∩ φ.model.C ⊆ φ.model.O →
        ∀ f : φ.model.E.lvl 0 → ℝ, ContinuousOn f φ.model.O →
          (∀ y ∈ φ.model.O, f y ∈ Set.Icc (0 : ℝ) 1) →
          closure (φ.model.O ∩ Function.support f) ∩ φ.model.O ⊆ V →
            closure (chartPre φ V) ⊆ φ.toPartialEquiv.source ∧
            PX.IsScSmoothOn realPolyfold (fun x => f (φ.toPartialEquiv x))
              φ.toPartialEquiv.source ∧
            tsupport (extByZero φ f) ⊆ chartPre φ V ∧
            ∀ ε : ℝ, 0 < ε → IsApproximatedB PX (chartPre φ V) (extByZero φ f) ε) ∧
      φ.model.HasApproxProperty

/-- Not the item: "sc-smooth" read as "continuous", and `cl_X(φ⁻¹(V)) ⊆ U` assumed. -/
def BRepaired : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X),
    PX.AdmitsScPartitionsOfUnity →
    ∀ A : MAtlas X, A.Equiv PX.atlas → ∀ φ ∈ A.charts,
      (∀ V : Set (φ.model.E.lvl 0), V ⊆ φ.model.O → (∃ W', IsOpen W' ∧ V = φ.model.O ∩ W') →
        closure V ∩ φ.model.C ⊆ φ.model.O →
        ∀ f : φ.model.E.lvl 0 → ℝ, ContinuousOn f φ.model.O →
          (∀ y ∈ φ.model.O, f y ∈ Set.Icc (0 : ℝ) 1) →
          closure (φ.model.O ∩ Function.support f) ∩ φ.model.O ⊆ V →
          closure (chartPre φ V) ⊆ φ.toPartialEquiv.source →
            Continuous (extByZero φ f) ∧
            tsupport (extByZero φ f) ⊆ chartPre φ V ∧
            ∀ ε : ℝ, 0 < ε → IsApproximatedB PX (chartPre φ V) (extByZero φ f) ε) ∧
      φ.model.HasApproxProperty

end RoundTrip.V5_55
