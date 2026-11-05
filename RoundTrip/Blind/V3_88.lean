import Polyfold
/-! Blind formalization of V3_88 (the text's §3.7, proof of Theorem 3.58, pp. 118–120). Choices:
- Setting: the coordinates in which the proof works, `E = B ⊕ X`, `F = A ⊕ Y`, written with the
  project's `ScBanach.paramProd`: `B`, `A` finite-dimensional real normed spaces (types `Bf`, `Af`
  with the constant sc-structure; the text's `B ⊇ ker Df(0)` and the finite-dimensional
  complement `A` of `Y`), `X`, `Y` arbitrary sc-Banach spaces, `E = Bf ⊕ X`, `F = Af ⊕ Y`, points
  `(b, x)`, `(c, y)`.  The partial quadrant is `C = C̃ ⊕ X` with `C̃ ⊆ B` a partial quadrant (the
  text's `C = (B ∩ C) ⊕ X`), `U` a relatively open neighbourhood of `0` in `C`, `f : U → F`
  sc-smooth (`IsScSmooth`).  `Df(p)` (`p ∈ U₁`) is the derivative family `scDeriv U f`.  The
  types are in `Type` (as `paramProd` requires); no universe choices arise.
- Hypotheses: the setting of Theorem 3.58 (the claim is part of its proof), with the conditions
  copied from my earlier blind file V3_89 (Theorem 3.58), applied to `E = Bf ⊕ X`, `F = Af ⊕ Y`,
  `B = Bf ⊕ 0` (`Bs`), `X = 0 ⊕ X` (`Xs`): (1) `ConstIndexFredholm` (sc-Fredholm of one index at
  every smooth point), (2) `ker Df(0) ⊆ B` and the compactness property `CompactnessProp` (my
  reading, see V3_89; doubt there: "`y_j → 0`" versus "`(y_j)` converges"), (3)
  `UniformD2Estimate`.  The other parts of (2) (`E = B ⊕ X` an sc-splitting, `B`
  finite-dimensional, `C = (B ∩ C) ⊕ X`) hold automatically in these coordinates.  "`Y = Df(0)X`"
  (which makes `F = A ⊕ Y`): `Df(0)` maps `0 ⊕ X` onto `0 ⊕ Y` (`Xs.map Df(0) = Ys`).
  Conditions (1) and (2) are not used in this second half (they produce the family `L`); they are
  kept as the setting of the text's claim.
- "with `L(b) = P_Y ∘ Df(b)|_X` sc-isomorphisms with uniform lower bounds (Lemmas 3.59–3.61)",
  the given family: a relatively open neighbourhood `O` of `0` in `C̃` with `(b, 0) ∈ U` for
  `b ∈ O`, and `L : B → ScIso X Y` (Definition 1.3; values off `O` are junk) with
  `L(b)h = P_Y(Df(b, 0)(0, h))` on level `0` (`P_Y(c, y) = y` the projection along `A`; the levels
  of an sc-isomorphism are determined by level `0`), and `|L(b)h|_m ≥ c_m|h|_m` for `b ∈ O`,
  `h ∈ X_m`, with `c_m > 0` for every `m`.  The sc-smoothness of `(b, k) ↦ L(b)⁻¹k` (Lemma 3.61) is
  a consequence of these and of the sc-smoothness of `f`, so it is not assumed.
- Conclusion: `Φ((b, x), (c, y)) = ((b, x), (c, L(b)⁻¹y))`, `U ◁ (A ⊕ Y) → U ◁ (A ⊕ X)`, with inverse
  `Φ'((b, x), (c, x')) = ((b, x), (c, L(b)x'))`, is a strong bundle isomorphism
  (`IsStrongBundleIso`, Definition 3.11's notion) over a relatively open neighbourhood `U₀ ⊆ U` of
  `0` in `C` on which `b ∈ O`; and the push-forward `Φ_*(f − f(0))`, which (as `Φ` covers the
  identity) is `(b, x) ↦ (c, L(b)⁻¹y)` for `(c, y) = f(b, x) − f(0)` (`pushed`), is a basic germ
  (`IsBasicGerm`, Definition 3.7: sc-smooth germ vanishing at `0` whose `X`-part is `x − B(b, x)`
  with `B` an sc⁰-contraction germ) on some germ of neighbourhoods `G` with `G₀ ⊆ U₀`.
  "the contraction estimate coming from condition (3)" describes the proof, not the claim.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_88
open Polyfold Filter

/-- The kernel `ker L ⊆ E₀` of a bounded operator `L : E₀ → F₀`. -/
def kerOf {E F : ScBanach} (L : E.lvl 0 →L[ℝ] F.lvl 0) : Submodule ℝ (E.lvl 0) :=
  LinearMap.ker (L : E.lvl 0 →ₗ[ℝ] F.lvl 0)

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

/-- `B = Bf ⊕ 0 ⊆ Bf ⊕ X`. -/
def Bsub (Bf : Type) [NormedAddCommGroup Bf] [NormedSpace ℝ Bf] [FiniteDimensional ℝ Bf]
    (X : ScBanach) : Submodule ℝ ((ScBanach.paramProd Bf X).lvl 0) :=
  LinearMap.range (LinearMap.inl ℝ Bf (X.lvl 0))

/-- `X = 0 ⊕ X ⊆ Bf ⊕ X`. -/
def Xsub (Bf : Type) [NormedAddCommGroup Bf] [NormedSpace ℝ Bf] [FiniteDimensional ℝ Bf]
    (X : ScBanach) : Submodule ℝ ((ScBanach.paramProd Bf X).lvl 0) :=
  LinearMap.range (LinearMap.inr ℝ Bf (X.lvl 0))

/-- The push-forward `Φ_*(f − f(0))(b, x) = (c, L(b)⁻¹y)`, `(c, y) = f(b, x) − f(0)`. -/
def pushed {Bf Af : Type} [NormedAddCommGroup Bf] [NormedSpace ℝ Bf] [FiniteDimensional ℝ Bf]
    [NormedAddCommGroup Af] [NormedSpace ℝ Af] [FiniteDimensional ℝ Af] {X Y : ScBanach}
    (L : Bf → ScIso X Y)
    (f : (ScBanach.paramProd Bf X).lvl 0 → (ScBanach.paramProd Af Y).lvl 0) :
    Bf × X.lvl 0 → Af × X.lvl 0 :=
  fun u =>
    let v : Af × Y.lvl 0 := f u - f 0
    (v.1, (L u.1).symm.lvl 0 v.2)

/-- Second half of the proof of Theorem 3.58: in the setting of Theorem 3.58 (coordinates
`E = B ⊕ X`, `F = A ⊕ Y`, `Y = Df(0)X`), given the sc-isomorphisms `L(b) = P_Y ∘ Df(b)|_X` with
uniform lower bounds, `Φ((b, x), (c, y)) = ((b, x), (c, L(b)⁻¹y))` is a strong bundle isomorphism
near `0` and `Φ_*(f − f(0))` is a basic germ. -/
def B : Prop :=
  ∀ (Bf Af : Type) [NormedAddCommGroup Bf] [NormedSpace ℝ Bf] [FiniteDimensional ℝ Bf]
    [NormedAddCommGroup Af] [NormedSpace ℝ Af] [FiniteDimensional ℝ Af] (X Y : ScBanach)
    (Ct : Set Bf) (U : Set ((ScBanach.paramProd Bf X).lvl 0))
    (f : (ScBanach.paramProd Bf X).lvl 0 → (ScBanach.paramProd Af Y).lvl 0),
    IsPartialQuadrant (ScBanach.const Bf) Ct →
    IsRelOpenInQuadrant (ScBanach.paramProd Bf X) (Ct ×ˢ Set.univ) U → 0 ∈ U →
    IsScSmooth U f →
    -- the setting of Theorem 3.58
    ConstIndexFredholm (ScBanach.paramProd Bf X) (ScBanach.paramProd Af Y) U f →
    kerOf (scDeriv U f 0) ≤ Bsub Bf X →
    CompactnessProp (ScBanach.paramProd Bf X) (ScBanach.paramProd Af Y) U f (Bsub Bf X)
      (Xsub Bf X) →
    UniformD2Estimate (ScBanach.paramProd Bf X) (ScBanach.paramProd Af Y) U f (Bsub Bf X)
      (Xsub Bf X) →
    -- `Y = Df(0)X`
    (Xsub Bf X).map (scDeriv U f 0 : (ScBanach.paramProd Bf X).lvl 0 →ₗ[ℝ]
        (ScBanach.paramProd Af Y).lvl 0) = LinearMap.range (LinearMap.inr ℝ Af (Y.lvl 0)) →
    -- the family `L(b) = P_Y ∘ Df(b)|_X` of sc-isomorphisms with uniform lower bounds
    ∀ (O : Set Bf) (L : Bf → ScIso X Y),
      (∃ O' : Set Bf, IsOpen O' ∧ O = O' ∩ Ct) → (0 : Bf) ∈ O →
      (∀ b ∈ O, ((b, 0) : Bf × X.lvl 0) ∈ U) →
      (∀ b ∈ O, ∀ h : X.lvl 0,
        (L b).lvl 0 h =
          (scDeriv U f ((b, 0) : Bf × X.lvl 1) ((0, h) : Bf × X.lvl 0) : Af × Y.lvl 0).2) →
      (∀ m : ℕ, ∃ c > 0, ∀ b ∈ O, ∀ h : X.lvl m, c * ‖h‖ ≤ ‖(L b).lvl m h‖) →
      ∃ U₀ : Set ((ScBanach.paramProd Bf X).lvl 0),
        IsRelOpenInQuadrant (ScBanach.paramProd Bf X) (Ct ×ˢ Set.univ) U₀ ∧ 0 ∈ U₀ ∧ U₀ ⊆ U ∧
        (∀ u ∈ U₀, (u : Bf × X.lvl 0).1 ∈ O) ∧
        IsStrongBundleIso (F := ScBanach.paramProd Af Y) (F' := ScBanach.paramProd Af X) U₀ U₀
          (fun p => (p.1, ((p.2 : Af × Y.lvl 0).1,
            (L (p.1 : Bf × X.lvl 0).1).symm.lvl 0 (p.2 : Af × Y.lvl 0).2)))
          (fun p => (p.1, ((p.2 : Af × X.lvl 0).1,
            (L (p.1 : Bf × X.lvl 0).1).lvl 0 (p.2 : Af × X.lvl 0).2))) ∧
        ∃ (G : ScNbhdGerm (ScBanach.paramProd Bf X) (Ct ×ˢ Set.univ))
          (Bc : Bf × X.lvl 0 → X.lvl 0),
          (∀ u ∈ G.U 0, u ∈ U₀) ∧ IsBasicGerm Ct G (pushed L f) Bc

end RoundTrip.V3_88
