import Polyfold
/-! Blind formalization of V3_53 (the text's §3.7, Lemma 3.60, p. 118). Choices:
- Setting ("the setting of Theorem 3.58"), exactly as in my V3_52 (Lemma 3.59), reused from the
  blind file V3_89: sc-Banach spaces `E`, `F`, a partial quadrant `C ⊆ E₀`, a relatively open
  neighbourhood `U` of `0` in `C`, `f : U → F` sc-smooth with derivative family `scDeriv U f`
  (level operators `levelDeriv`), and hypotheses (1) `ConstIndexFredholm`, (2) the sc-splitting
  `E = B ⊕ X` (`B` finite-dimensional, `C = (B ∩ C) ⊕ X`, `ker Df(0) ⊆ B`) with the compactness
  property `CompactnessProp` (my reading, see V3_52/V3_89; doubt: "`y_j → 0`" versus "`(y_j)`
  converges"), (3) `UniformD2Estimate` (`Setting358`).  `Y = Df(0)X` (`imgY`), `A` a
  finite-dimensional sc-complement of `Y` (`F.IsScSplitting A Y`), for every such `A`.
  No universe choices arise.
- "`O` (Lemma 3.59)": the neighbourhood is the one *provided by* Lemma 3.59, so `B` is: there is
  a relatively open neighbourhood `O ⊆ U` of `0` in `B ∩ C` on which `P_Y ∘ Df(b)|_X` is injective
  (Lemma 3.59's conclusion, as in V3_52) such that for every `Õ` as below the estimate holds.
  (Reading it for *every* `O` with Lemma 3.59's property would be stronger and is not what the
  text says: its `O` is a particular small one.)
- "`Õ ∋ 0` relatively open in `C ∩ B` with compact closure in `O`": `Õ = O'' ∩ (C ∩ B)` with
  `O''` open in `E₀`, `0 ∈ Õ`, `closure Õ` (in `E₀`) compact and contained in `O`.
- "for every `m` there is `c_m > 0` with `|P_Y ∘ Df(b)h|_m ≥ c_m|h|_m` for `b ∈ Õ`, `h ∈ X_m`":
  `Df(b)` on level `m` is `levelDeriv (scDeriv U f) m b'` at a lift `b' ∈ E_{m+1}` of `b` (every
  lift; points of `B` are smooth); `P_Y` on level `m` is the projection `F_m = A ⊕ Y_m → Y_m`,
  expressed without naming it: `P_Y(Df(b)h)` is the unique `y ∈ Y_m` with `Df(b)h − y ∈ A`, so the
  estimate is stated for every such `y`.  Norms are the level-`m` norms.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_53
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

/-- Lemma 3.60 (with the `O` of Lemma 3.59): in the setting of Theorem 3.58, for every
finite-dimensional sc-complement `A` of `Y = Df(0)X`, there is a relatively open neighbourhood
`O ⊆ U` of `0` in `B ∩ C` on which `P_Y ∘ Df(b)|_X` is injective, such that for every relatively
open `Õ ∋ 0` in `C ∩ B` with compact closure in `O` and every level `m` there is `c_m > 0` with
`|P_Y ∘ Df(b)h|_m ≥ c_m|h|_m` for `b ∈ Õ`, `h ∈ X_m`. -/
def B : Prop :=
  ∀ (E F : ScBanach) (C U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0)
    (Bs X : Submodule ℝ (E.lvl 0)),
    Setting358 E F C U f Bs X →
    ∀ A : Submodule ℝ (F.lvl 0), FiniteDimensional ℝ A → F.IsScSplitting A (imgY E F U f X) →
      ∃ O : Set (E.lvl 0),
        (∃ O' : Set (E.lvl 0), IsOpen O' ∧ O = O' ∩ ((Bs : Set (E.lvl 0)) ∩ C)) ∧
        0 ∈ O ∧ O ⊆ U ∧
        (∀ b₁ : E.lvl 1, E.toBase 1 b₁ ∈ O →
          ∀ h ∈ X, scDeriv U f b₁ h ∈ A → h = 0) ∧
        ∀ Ot : Set (E.lvl 0),
          (∃ O'' : Set (E.lvl 0), IsOpen O'' ∧ Ot = O'' ∩ (C ∩ (Bs : Set (E.lvl 0)))) →
          0 ∈ Ot → IsCompact (closure Ot) → closure Ot ⊆ O →
          ∀ m : ℕ, ∃ c > 0, ∀ b' : E.lvl (m + 1), E.toBase (m + 1) b' ∈ Ot →
            ∀ h : E.lvl m, E.toBase m h ∈ X →
              ∀ y : F.lvl m, F.toBase m y ∈ imgY E F U f X →
                F.toBase m (levelDeriv (scDeriv U f) m b' h - y) ∈ A →
                  c * ‖h‖ ≤ ‖y‖

end RoundTrip.V3_53
