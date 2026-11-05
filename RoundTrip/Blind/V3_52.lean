import Polyfold
/-! Blind formalization of V3_52 (the text's §3.7, Lemma 3.59, p. 117). Choices:
- Setting ("the setting of Theorem 3.58"), reused from the blind file V3_89 (Theorem 3.58, whose
  hypotheses I take over unchanged): arbitrary sc-Banach spaces `E`, `F`; `C ⊆ E₀` a partial
  quadrant and `U` a relatively open neighbourhood of `0` in `C`; `f : U → F` sc-smooth
  (`IsScSmooth`); `Df(x)` for `x ∈ U₁` is the derivative family `scDeriv U f` (unique, `f` being
  sc¹), on level `m` at points of level `m + 1` it is `levelDeriv`.  Hypotheses:
  (1) `ConstIndexFredholm`: `Df(x)` is an sc-Fredholm operator of one index `i` at every smooth
      point `x ∈ U`;
  (2) an sc-splitting `E = B ⊕ X` with `B` finite-dimensional, `C = (B ∩ C) ⊕ X`
      (`b + x ∈ C ⟺ b ∈ C`, presupposed by the text's points `(b, x)`), `ker Df(0) ⊆ B`, and the
      compactness property `CompactnessProp` (my reading, as in V3_89: there is `r > 0` such that
      for every `m`, if `b_j → b` in `B ∩ U`, `|b| < r`, `(η_j) ⊆ X_m` is bounded and
      `Df(b_j)η_j = y_j + z_j` with `y_j → 0` in `F_m` and `(z_j)` bounded in `F_{m+1}`, then
      `(η_j)` has a convergent subsequence in `E_m`.  Doubt: the text may say "`(y_j)` converges"
      instead of "`y_j → 0`".);
  (3) `UniformD2Estimate`: `|[Df(b) − Df(b + x)]h|_m ≤ ε|h|_m` for `b ∈ B ∩ U`, `x ∈ X_{m+1}` small
      on level `m`, `h ∈ X_m`.
  No universe choices arise.
- "`Y = Df(0)X`": the image of `X` under `Df(0) : E₀ → F₀` (`imgY`, a subspace of `F₀`).
- "`P_Y` the projection along a finite-dimensional complement `A`": `A` finite-dimensional with
  `F = A ⊕ Y` an sc-splitting (`F.IsScSplitting A Y`; the complement of the finite-codimensional
  sc-subspace `Y` is taken to be an sc-complement, i.e. smooth).  The claim is made for *every*
  such `A` (the text fixes one, arbitrary).  For `h ∈ X` (level `0`), `P_Y Df(b)h = 0` iff
  `Df(b)h ∈ A`, so "`P_Y ∘ Df(b) : X → Y` has trivial kernel" is: `Df(b)h ∈ A`, `h ∈ X` imply
  `h = 0` (kernel on level `0`; the kernels on higher levels are contained in it).
- "`O` a relatively open neighbourhood of `0` in `B ∩ C`": `O = O' ∩ (B ∩ C)` with `O'` open in
  `E₀`, `0 ∈ O`; also `O ⊆ U` (presupposed: `Df(b)` is defined for `b ∈ U`).  Points of `B` are
  smooth (`B` is a finite-dimensional sc-subspace), and `Df(b)` is evaluated at a lift `b₁ ∈ E₁`
  of `b`; the claim is stated for every such lift.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_52
open Polyfold Filter

/-- The kernel `ker L ⊆ E₀` of a bounded operator `L : E₀ → F₀`. -/
def kerOf {E F : ScBanach} (L : E.lvl 0 →L[ℝ] F.lvl 0) : Submodule ℝ (E.lvl 0) :=
  LinearMap.ker (L : E.lvl 0 →ₗ[ℝ] F.lvl 0)

/-- `Y = Df(0)X ⊆ F₀`. -/
noncomputable def imgY (E F : ScBanach) (U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0)
    (X : Submodule ℝ (E.lvl 0)) : Submodule ℝ (F.lvl 0) :=
  X.map (scDeriv U f 0 : E.lvl 0 →ₗ[ℝ] F.lvl 0)

/-- Condition (1): at every smooth point `x ∈ U` the linearization `Df(x)` is an sc-Fredholm
operator `E → F`, of one and the same index `i`. -/
def ConstIndexFredholm (E F : ScBanach) (U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0) : Prop :=
  ∃ i : ℤ, ∀ x₁ : E.lvl 1, E.toBase 1 x₁ ∈ U → E.toBase 1 x₁ ∈ E.smooth →
    ∃ T : ScOperator E F, T.lvl 0 = scDeriv U f x₁ ∧ IsScFredholm T ∧ scIndex T = i

/-- Condition (2), the compactness property, for the splitting `E = B ⊕ X`. -/
def CompactnessProp (E F : ScBanach) (U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0)
    (Bs X : Submodule ℝ (E.lvl 0)) : Prop :=
  ∃ r > 0, ∀ (m : ℕ) (b : ℕ → E.lvl (m + 1)) (b₀ : E.lvl (m + 1)) (η : ℕ → E.lvl m)
      (y : ℕ → F.lvl m) (z : ℕ → F.lvl (m + 1)),
    (∀ j, E.toBase (m + 1) (b j) ∈ Bs ∧ E.toBase (m + 1) (b j) ∈ U) →
    E.toBase (m + 1) b₀ ∈ Bs → E.toBase (m + 1) b₀ ∈ U → ‖E.toBase (m + 1) b₀‖ < r →
    Tendsto (fun j => E.toBase (m + 1) (b j)) atTop (nhds (E.toBase (m + 1) b₀)) →
    (∀ j, E.toBase m (η j) ∈ X) → (∃ M : ℝ, ∀ j, ‖η j‖ ≤ M) →
    (∀ j, levelDeriv (scDeriv U f) m (b j) (η j) = y j + F.incl m (z j)) →
    Tendsto y atTop (nhds 0) → (∃ M : ℝ, ∀ j, ‖z j‖ ≤ M) →
    ∃ (η₀ : E.lvl m) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (η ∘ φ) atTop (nhds η₀)

/-- Condition (3): `|[D₂f(b, 0) − D₂f(b, x)]h|_m ≤ ε|h|_m` uniformly for `b ∈ B ∩ U` small, `x ∈ X`
small on level `m + 1` (measured on level `m`), `h ∈ X_m`. -/
def UniformD2Estimate (E F : ScBanach) (U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0)
    (Bs X : Submodule ℝ (E.lvl 0)) : Prop :=
  ∀ (m : ℕ), ∀ ε > 0, ∃ r > 0, ∀ (b x : E.lvl (m + 1)),
    E.toBase (m + 1) b ∈ Bs → E.toBase (m + 1) b ∈ U → ‖E.toBase (m + 1) b‖ < r →
    E.toBase (m + 1) x ∈ X → ‖E.incl m x‖ < r → E.toBase (m + 1) (b + x) ∈ U →
    ∀ h : E.lvl m, E.toBase m h ∈ X →
      ‖levelDeriv (scDeriv U f) m b h - levelDeriv (scDeriv U f) m (b + x) h‖ ≤ ε * ‖h‖

/-- The setting of Theorem 3.58 (hypotheses (1)–(3) with the splitting `E = B ⊕ X`). -/
def Setting358 (E F : ScBanach) (C U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0)
    (Bs X : Submodule ℝ (E.lvl 0)) : Prop :=
  IsRelOpenInQuadrant E C U ∧ 0 ∈ U ∧ IsScSmooth U f ∧
    ConstIndexFredholm E F U f ∧
    E.IsScSplitting Bs X ∧ FiniteDimensional ℝ Bs ∧
    (∀ b ∈ Bs, ∀ x ∈ X, (b + x ∈ C ↔ b ∈ C)) ∧
    kerOf (scDeriv U f 0) ≤ Bs ∧
    CompactnessProp E F U f Bs X ∧
    UniformD2Estimate E F U f Bs X

/-- Lemma 3.59: in the setting of Theorem 3.58, for a finite-dimensional sc-complement `A` of
`Y = Df(0)X`, there is a relatively open neighbourhood `O ⊆ U` of `0` in `B ∩ C` such that
`P_Y ∘ Df(b) : X → Y` is injective for every `b ∈ O`. -/
def B : Prop :=
  ∀ (E F : ScBanach) (C U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0)
    (Bs X : Submodule ℝ (E.lvl 0)),
    Setting358 E F C U f Bs X →
    ∀ A : Submodule ℝ (F.lvl 0), FiniteDimensional ℝ A → F.IsScSplitting A (imgY E F U f X) →
      ∃ O : Set (E.lvl 0),
        (∃ O' : Set (E.lvl 0), IsOpen O' ∧ O = O' ∩ ((Bs : Set (E.lvl 0)) ∩ C)) ∧
        0 ∈ O ∧ O ⊆ U ∧
        ∀ b₁ : E.lvl 1, E.toBase 1 b₁ ∈ O →
          ∀ h ∈ X, scDeriv U f b₁ h ∈ A → h = 0

end RoundTrip.V3_52
