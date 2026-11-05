import Polyfold
/-! Blind formalization of V3_2 (the text's §3.1, Definition 3.2, pp. 62–63). Choices:
- This item is a definition (sc⁰-, sc¹-, scᵏ- and sc-smooth germs); the text asserts no further
  property.  Setting: `E F : ScBanach` (levels in `Type`, forced by `ScBanach`), `C ⊆ E₀` a
  partial quadrant (`IsPartialQuadrant`), and the germ of neighbourhoods `O(C, 0)` given by its
  levels `U m ⊆ E_m` (Definition 3.1, see my `RoundTrip/Blind/V3_1.lean`).  A germ `f` is a total
  map `f : E₀ → F₀`; only its values on `U₀` matter.  My definitions do not mention `C` (only the
  levels `U_m` enter); B quantifies over germs `G : ScNbhdGerm E C` of a partial quadrant.
- sc⁰ (`IsSc0GermB`): for every `m` there is `f_m : E_m → F_m` lifting `f` on `U_m`
  (`ι(f_m x) = f(ι x)`, i.e. `f(U_m) ⊆ F_m`) and continuous on `U_m` (level topologies).  The
  case `m = 0` is "`f : U₀ → F` continuous".
- sc¹ with the derivative family `D x = Df(x) : E₀ → F₀` (`x ∈ E₁`; only `x ∈ U₁` matter)
  (`IsSc1GermWithB`): sc⁰; for `x ∈ U₁`, `|f(x + h) − f(x) − Df(x)h|₀ / |h|₁ → 0` as `h → 0` in
  `E₁` with `x + h ∈ U₁` (Mathlib `Tendsto` along `𝓝[{h | x + h ∈ U₁}] 0`; at `h = 0` the quotient
  is `0/0 = 0`, harmless); and `Tf(x, h) = (f(x), Df(x)h)` is an sc⁰-germ on
  `TO(C, 0) = (U_{m+1} ⊕ E_m)_m`, as a map `TE₀ = E₁ × E₀ → TF₀ = F₁ × F₀` (`TfB`; its first
  component is the level-1 lift of `f(x)`, `liftB`, a junk `0` if there is none — never used on
  `TO(C, 0)` once `f` is sc⁰).  sc¹ (`IsSc1GermB`): some `D` works.
- scᵏ "inductively" (`IsSckGermB`): sc⁰ for `k = 0`; for `k + 1`: sc¹ with some `D` such that
  `Tf` is scᵏ on `TO(C, 0)` (`TE = E¹ ⊕ E` is `TEB E = E.shift.prod E`).  Existential `D`: for a
  partial quadrant `Df(x)`, `x ∈ U₁`, is unique (`U₁` is relatively open in the partial quadrant
  `C₁`, and `E₁` is dense in `E₀`), so this is "the" `Tf`.  sc-smooth: scᵏ for every `k`.
- B: the project's `IsSc0Germ`, `IsSc1GermWith`, `IsSc1Germ`, `IsSckGerm`, `IsScSmoothGerm`
  (on `G : ScNbhdGerm E C`) are equivalent to mine on the levels `G.U`.
- Nothing looks false to me.
-/
namespace RoundTrip.V3_2
open Polyfold Filter Topology

/-- `TE = E¹ ⊕ E`. -/
noncomputable abbrev TEB (E : ScBanach) : ScBanach := E.shift.prod E

/-- The tangent germ `TO(C, 0)`: `(TO)_m = U_{m+1} ⊕ E_m`. -/
def TUB {E : ScBanach} (U : ∀ m, Set (E.lvl m)) : ∀ m, Set ((TEB E).lvl m) :=
  fun m => {p | p.1 ∈ U (m + 1)}

/-- The level-`m` point over `y ∈ F₀` (junk `0` if `y ∉ F_m`). -/
noncomputable def liftB (F : ScBanach) (m : ℕ) (y : F.lvl 0) : F.lvl m := by
  classical
  exact if h : ∃ z : F.lvl m, F.toBase m z = y then h.choose else 0

/-- **Definition 3.2**: `f` is an sc⁰-germ on the germ with levels `U`: `f(U_m) ⊆ F_m` and
`f : U_m → F_m` is continuous, for every `m`. -/
def IsSc0GermB (E F : ScBanach) (U : ∀ m, Set (E.lvl m)) (f : E.lvl 0 → F.lvl 0) : Prop :=
  ∀ m : ℕ, ∃ fm : E.lvl m → F.lvl m,
    (∀ x ∈ U m, F.toBase m (fm x) = f (E.toBase m x)) ∧ ContinuousOn fm (U m)

/-- The tangent map `Tf(x, h) = (f(x), Df(x)h)`, `TE₀ = E₁ × E₀ → TF₀ = F₁ × F₀`. -/
noncomputable def TfB {E F : ScBanach} (f : E.lvl 0 → F.lvl 0)
    (D : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0) (p : (TEB E).lvl 0) : (TEB F).lvl 0 :=
  (liftB F 1 (f (E.toBase 1 p.1)), D p.1 p.2)

/-- **Definition 3.2**: `f` is an sc¹-germ with derivatives `Df(x) = D x` (`x ∈ U₁`). -/
def IsSc1GermWithB (E F : ScBanach) (U : ∀ m, Set (E.lvl m)) (f : E.lvl 0 → F.lvl 0)
    (D : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0) : Prop :=
  IsSc0GermB E F U f ∧
  (∀ x ∈ U 1, Tendsto
      (fun h : E.lvl 1 =>
        ‖f (E.toBase 1 (x + h)) - f (E.toBase 1 x) - D x (E.toBase 1 h)‖ / ‖h‖)
      (𝓝[{h | x + h ∈ U 1}] 0) (𝓝 0)) ∧
  IsSc0GermB (TEB E) (TEB F) (TUB U) (TfB f D)

/-- **Definition 3.2**: `f` is an sc¹-germ. -/
def IsSc1GermB (E F : ScBanach) (U : ∀ m, Set (E.lvl m)) (f : E.lvl 0 → F.lvl 0) : Prop :=
  ∃ D : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0, IsSc1GermWithB E F U f D

/-- **Definition 3.2**: `f` is an scᵏ-germ (inductively: sc¹ with `Tf` an sc^{k-1}-germ on
`TO(C, 0)`). -/
def IsSckGermB : ℕ → (E F : ScBanach) → (∀ m, Set (E.lvl m)) → (E.lvl 0 → F.lvl 0) → Prop
  | 0, E, F, U, f => IsSc0GermB E F U f
  | k + 1, E, F, U, f => ∃ D : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0,
      IsSc1GermWithB E F U f D ∧ IsSckGermB k (TEB E) (TEB F) (TUB U) (TfB f D)

/-- **Definition 3.2**: `f` is an sc-smooth germ: scᵏ for every `k`. -/
def IsScSmoothGermB (E F : ScBanach) (U : ∀ m, Set (E.lvl m)) (f : E.lvl 0 → F.lvl 0) : Prop :=
  ∀ k : ℕ, IsSckGermB k E F U f

/-- Definition 3.2: on a germ of neighbourhoods of a partial quadrant, the project's sc⁰-, sc¹-,
scᵏ- and sc-smooth germs are the text's. -/
def B : Prop :=
  ∀ (E F : ScBanach) (C : Set (E.lvl 0)), IsPartialQuadrant E C →
    ∀ (G : ScNbhdGerm E C) (f : E.lvl 0 → F.lvl 0),
      (IsSc0Germ G f ↔ IsSc0GermB E F G.U f) ∧
      (∀ D : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0,
        IsSc1GermWith G f D ↔ IsSc1GermWithB E F G.U f D) ∧
      (IsSc1Germ G f ↔ IsSc1GermB E F G.U f) ∧
      (∀ k : ℕ, IsSckGerm k G f ↔ IsSckGermB k E F G.U f) ∧
      (IsScSmoothGerm G f ↔ IsScSmoothGermB E F G.U f)

end RoundTrip.V3_2
