import Polyfold
/-! Blind formalization of V5_56 (the text's §5.4.2, proof of Theorem 5.37, "(ii) ⇒ (i)",
pp. 196–197).

Text: a refinement `(W_λ)` "with the same index set" and `cl_X(W_λ) ⊆ U_{τ(λ)}`, `f_λ = 1` on
`Q_λ`, `g_λ` with `|f_λ ∘ φ⁻¹ − g_λ| < 1/2`, `γ_λ = ĝ_λ / Σ ĝ`.

Choices:
- Setting: `X : Type` (universe 0, as asked), Hausdorff paracompact, `PX : MPolyfold X`, as in
  `RoundTrip/Blind/V5_57.lean`.  Hypothesis (ii): an atlas `A` of the structure
  (`A.Equiv PX.atlas`) all of whose charts have local models with the sc-smooth approximation
  property (the project's `HasApproxProperty`, Definition 5.36, checked with `#print`; see
  `RoundTrip/Blind/V5_54.lean`).
- The quoted fragments are the steps of the construction, for a given open cover
  `(U_i)_{i ∈ I}` of `X` (`I : Type`).  I formalize them as ONE existence claim, the objects of the
  proof together with every property the text attaches to them:
  * an index set `Λ`, `τ : Λ → I`, and for `λ ∈ Λ` a chart `φ_λ ∈ A` (the chart in which `g_λ`
    lives), an open locally finite family `(W_λ)` with `cl_X(W_λ) ⊆ U_{τ(λ)} ∩ dom φ_λ` (the
    text's `cl_X(W_λ) ⊆ U_{τ(λ)}`; `W_λ` must lie in a chart domain for `f_λ ∘ φ⁻¹` to make
    sense), and closed `Q_λ ⊆ W_λ` covering `X`.  "With the same index set": all families
    `W, Q, f, g, γ` are indexed by the one set `Λ` (the cover itself is indexed by `I`, via `τ`);
  * continuous `f_λ : X → [0, 1]`, `f_λ = 1` on `Q_λ`, `supp(f_λ) ⊆ W_λ`;
  * sc-smooth `g_λ : O_λ → [0, 1]` (the project's `IsScSmoothRetractMap … realSc univ univ`,
    checked) with `supp_O(g_λ) ⊆ φ_λ(W_λ)` (as the approximation property delivers) and
    `|f_λ(φ_λ⁻¹(y)) − g_λ(y)| < 1/2` for `y ∈ O_λ`;
  * `ĝ_λ = g_λ ∘ φ_λ` extended by `0` off `dom φ_λ` (`extByZero`), `Σ_μ ĝ_μ > 0` everywhere, and
    `γ_λ = ĝ_λ / Σ_μ ĝ_μ` an sc-smooth partition of unity (sc-smooth `X → ℝ` in the project's sense
    `PX.IsScSmoothMap realPolyfold`, `≥ 0`, locally finite supports, sum `1`) with
    `supp(γ_λ) ⊆ W_λ ⊆ U_{τ(λ)}`.
  B also contains the conclusion of the direction, (i): `PX.AdmitsScPartitionsOfUnity`
  (Definition 5.28, checked; see `RoundTrip/Blind/V5_47.lean`).
- Not quoted, so not imposed: `cl_C(φ_λ(W_λ)) ⊆ O_λ`, which the approximation property needs for
  `V = φ_λ(W_λ)`; it is not implied by `cl_X(W_λ) ⊆ dom φ_λ` in infinite dimensions, but the
  existence claim can choose `W_λ` small enough.  I believe B is true.
-/
namespace RoundTrip.V5_56
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- An sc-smooth partition of unity `(β_λ)_{λ ∈ Λ}` on `X`: sc-smooth, non-negative, locally
finite supports, summing to `1`. -/
def IsScPOUB (PX : MPolyfold X) {Λ : Type} (β : Λ → X → ℝ) : Prop :=
  (∀ l, PX.IsScSmoothMap realPolyfold (β l)) ∧ (∀ l x, 0 ≤ β l x) ∧
  LocallyFinite (fun l => tsupport (β l)) ∧ ∀ x, ∑ᶠ l, β l x = 1

/-- `g ∘ φ` on the domain of `φ`, extended by `0` to `X`. -/
noncomputable def extByZero (φ : MChart X) (g : φ.model.E.lvl 0 → ℝ) : X → ℝ :=
  Set.indicator φ.toPartialEquiv.source (fun x => g (φ.toPartialEquiv x))

end

/-- Theorem 5.37, (ii) ⇒ (i), as argued in the text: for every open cover `(U_i)` there are a
locally finite refinement `(W_λ)` with `cl_X(W_λ) ⊆ U_{τ(λ)}` in chart domains, a closed shrinking
`(Q_λ)`, Urysohn functions `f_λ = 1` on `Q_λ`, sc-smooth `g_λ` within `1/2` of `f_λ ∘ φ⁻¹`, and
`γ_λ = ĝ_λ / Σ ĝ` is an sc-smooth partition of unity subordinate to `(W_λ)`; hence (i). -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    (A : MAtlas X), A.Equiv PX.atlas → (∀ φ ∈ A.charts, φ.model.HasApproxProperty) →
    (∀ (I : Type) (U : I → Set X), (∀ i, IsOpen (U i)) → (⋃ i, U i) = Set.univ →
      ∃ (Λ : Type) (τ : Λ → I) (φ : Λ → MChart X) (W Q : Λ → Set X) (f : Λ → X → ℝ)
        (g : (l : Λ) → (φ l).model.E.lvl 0 → ℝ),
        (∀ l, φ l ∈ A.charts) ∧
        -- the refinement `(W_λ)` and the closed shrinking `(Q_λ)`
        (∀ l, IsOpen (W l)) ∧ LocallyFinite W ∧
        (∀ l, closure (W l) ⊆ U (τ l) ∩ (φ l).toPartialEquiv.source) ∧
        (∀ l, IsClosed (Q l) ∧ Q l ⊆ W l) ∧ (⋃ l, Q l) = Set.univ ∧
        -- `f_λ = 1` on `Q_λ`
        (∀ l, Continuous (f l) ∧ (∀ x, f l x ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ x ∈ Q l, f l x = 1) ∧
          tsupport (f l) ⊆ W l) ∧
        -- `g_λ` with `|f_λ ∘ φ⁻¹ − g_λ| < 1/2`
        (∀ l, IsScSmoothRetractMap (φ l).model.E (φ l).model.C (φ l).model.O realSc
            Set.univ Set.univ (g l) ∧
          (∀ y ∈ (φ l).model.O, g l y ∈ Set.Icc (0 : ℝ) 1) ∧
          closure ((φ l).model.O ∩ Function.support (g l)) ∩ (φ l).model.O ⊆
            (φ l).toPartialEquiv '' W l ∧
          ∀ y ∈ (φ l).model.O, |f l ((φ l).toPartialEquiv.symm y) - g l y| < 1 / 2) ∧
        -- `γ_λ = ĝ_λ / Σ ĝ`
        (∀ x, 0 < ∑ᶠ m, extByZero (φ m) (g m) x) ∧
        IsScPOUB PX (fun l x => extByZero (φ l) (g l) x / ∑ᶠ m, extByZero (φ m) (g m) x) ∧
        (∀ l, tsupport (fun x => extByZero (φ l) (g l) x / ∑ᶠ m, extByZero (φ m) (g m) x) ⊆
          W l)) ∧
    PX.AdmitsScPartitionsOfUnity

end RoundTrip.V5_56
