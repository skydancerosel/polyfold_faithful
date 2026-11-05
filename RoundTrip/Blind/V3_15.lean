import Polyfold
/-! Blind formalization of V3_15 (the text's §3.1, Corollary 3.13, p. 70). Choices:
- Setting: the hypotheses of Theorem 3.12 (as in the blind file V3_14): `X Y : Type` (universe 0),
  `PX : MPolyfold X`, `P : Y → X` with the fibrewise linear structure as instances,
  `Bd : StrongBundle PX P` a *tame* strong bundle (`IsTameStrongBundle`: tame base and an
  equivalent strong bundle atlas of charts with tame base retraction — a property of the given
  structure), `f` an sc-smooth section (`StrongBundle.IsScSmoothSection`, Definition 2.52),
  `(f, x₀)` an sc-Fredholm germ and `f(x₀) = 0` (`IsZeroAt`).
- "sc-Fredholm germ": the text's Definition 3.11 as written in my blind file V3_13
  (`IsScFredholmGermB`, copied below with its prelude): germ data in a strong bundle chart with
  tame base retraction, filled version, sc⁺-germ `s`, conjugation to a basic germ, all at the germ
  level.
- The quote's limit point `x` is read as the point `x₀` of the sc-Fredholm germ (Theorem 3.12's
  hypotheses only concern `x₀`; for an arbitrary limit point the claim would be false, e.g. if `f`
  vanishes identically far from `x₀`).  Recorded as the one interpretive choice.
- "`x_k → x` in `X₀`": convergence in the topology of `X` (`X₀ = X`).  "`x_k ∈ X_m` for `k` large":
  `x_k ∈ PX.levelSet m` for `k ≥ K`.  "`x_k → x` in `X_m`": a sequence `y` in the level set
  `X_m = PX.levelSet m` (topologized by the level topology `PX.levelTopology m`, the topology of
  `X_m`, not the subspace topology from `X`) agreeing with `x_k` for `k ≥ K`, converging there to
  the point `x₀` of `X_m` (junk values of `y` for `k < K` do not matter for convergence).
- Nothing in the statement looks false to me (with `x = x₀`).
-/
namespace RoundTrip.V3_15
open Polyfold Filter Topology

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- A **tame strong bundle**: tame base, and an equivalent strong bundle atlas of charts whose base
retractions are tame. -/
def IsTameStrongBundle (Bd : StrongBundle PX P) : Prop :=
  PX.IsTame ∧ ∃ A : StrongBundleAtlas PX P, A.Equiv Bd.atlas ∧
    ∀ c ∈ A.charts, (IsStrongBundleRetraction.baseRetraction c.relOpen c.isRetraction).IsTame

end

/-- **Definitions 3.4/3.6**: `g` is a filling (filled version) of the principal part `f̂` of a
section of `K = R(U ◁ F) → O`, `O = r(U)`, all near `0`. -/
def IsFillingB {E F : ScBanach} (C U : Set (E.lvl 0))
    (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0) (fhat g : E.lvl 0 → F.lvl 0) : Prop :=
  -- `g` is an sc-smooth section germ of `U ◁ F → U`, and condition (3)
  (∃ G : ScNbhdGerm E C, (∀ x ∈ G.U 0, x ∈ U) ∧ IsScSmoothGerm G g ∧
    ∃ Dk : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0,
      IsSc1GermWith G (fun y => g y - (R ((R (y, 0)).1, g y)).2) Dk ∧
    ∃ Dr : E.lvl 1 → E.lvl 0 →L[ℝ] E.lvl 0, IsSc1With U (fun u => (R (u, 0)).1) Dr ∧
      Set.BijOn (Dk 0) {v | Dr 0 v = 0} {h | (R (0, h)).2 = 0} ∧
      ∃ c : ℝ, ∀ v, Dr 0 v = 0 → ‖v‖ ≤ c * ‖Dk 0 v‖) ∧
  -- (1) `f̂ = g` on `O` near `0`
  (∀ᶠ x in 𝓝 (0 : E.lvl 0), x ∈ (fun u => (R (u, 0)).1) '' U → fhat x = g x) ∧
  -- (2) `g(y) = ρ(r(y))g(y)`, `y ∈ U` near `0`, forces `y ∈ O`
  (∀ᶠ y in 𝓝 (0 : E.lvl 0), y ∈ U → g y = (R ((R (y, 0)).1, g y)).2 →
    y ∈ (fun u => (R (u, 0)).1) '' U)

/-- A local sc⁺-section `s : U → F¹` of `U ◁ F → U` near `0`: an sc-smooth germ into `F¹`. -/
def IsScPlusGermB {E F : ScBanach} (C U : Set (E.lvl 0)) (s : E.lvl 0 → F.lvl 1) : Prop :=
  ∃ G : ScNbhdGerm E C, (∀ x ∈ G.U 0, x ∈ U) ∧ IsScSmoothGerm (F := F.shift) G s

/-- The quadrant `[0,∞)ᵏ ⊕ ℝⁿ⁻ᵏ ⊆ ℝⁿ`. -/
def stdQuad (n k : ℕ) : Set (Fin n → ℝ) := {a | ∀ i : Fin n, (i : ℕ) < k → 0 ≤ a i}

/-- **Definition 3.11, conjugation**: the section `u ↦ (u, k(u))` of `U ◁ F → U` is conjugated near
`0` to a basic germ by a strong bundle isomorphism `Ψ` covering an sc-diffeomorphism `ψ`,
`ψ(0) = 0`: `Ψ ∘ k ∘ ψ⁻¹` is a basic germ `O([0,∞)ᵏ ⊕ ℝⁿ⁻ᵏ ⊕ W, 0) → ℝᴺ ⊕ W`. -/
def ConjBasicB {E F : ScBanach} (C U : Set (E.lvl 0)) (k : E.lvl 0 → F.lvl 0) : Prop :=
  ∃ U₀ : Set (E.lvl 0), IsRelOpenInQuadrant E C U₀ ∧ (0 : E.lvl 0) ∈ U₀ ∧ U₀ ⊆ U ∧
  ∃ (n kq N : ℕ) (_ : kq ≤ n) (W : ScBanach)
    (U' : Set ((ScBanach.paramProd (Fin n → ℝ) W).lvl 0)),
    IsRelOpenInQuadrant (ScBanach.paramProd (Fin n → ℝ) W) (stdQuad n kq ×ˢ Set.univ) U' ∧
    ∃ (Ψ : E.lvl 0 × F.lvl 0 →
          (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 × (ScBanach.paramProd (Fin N → ℝ) W).lvl 0)
      (Ψ' : (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 × (ScBanach.paramProd (Fin N → ℝ) W).lvl 0 →
          E.lvl 0 × F.lvl 0),
      IsStrongBundleIso U₀ U' Ψ Ψ' ∧ (Ψ (0, 0)).1 = 0 ∧
      ∃ (G : ScNbhdGerm (ScBanach.paramProd (Fin n → ℝ) W) (stdQuad n kq ×ˢ Set.univ))
        (Bc : (Fin n → ℝ) × W.lvl 0 → W.lvl 0),
        (∀ x ∈ G.U 0, x ∈ U') ∧
        IsBasicGerm (stdQuad n kq) G
          (fun u' => (Ψ ((Ψ' (u', 0)).1, k (Ψ' (u', 0)).1)).2) Bc

/-- **Definition 3.11**: `(f, x₀)` is an sc-Fredholm germ: at the smooth point `x₀`, in a (tame)
strong bundle chart with `φ(x₀) = 0`, the principal part has a filled version `g`, and there is a
local sc⁺-section `s` with `s(0) = g(0)` such that `g − s` is conjugated to a basic germ. -/
def IsScFredholmGermB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {PX : MPolyfold X} {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X) : Prop :=
  x₀ ∈ PX.smoothSet ∧
  ∃ c : StrongBundleChart PX P, Bd.IsChart c ∧
    (IsStrongBundleRetraction.baseRetraction c.relOpen c.isRetraction).IsTame ∧
    x₀ ∈ c.φ.source ∧ c.φ.toPartialEquiv x₀ = 0 ∧
    ∃ (g : c.φ.model.E.lvl 0 → c.F.lvl 0) (s : c.φ.model.E.lvl 0 → c.F.lvl 1),
      IsFillingB c.φ.model.C c.U c.R (c.principal f) g ∧
      IsScPlusGermB c.φ.model.C c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
      ConjBasicB c.φ.model.C c.U (fun u => g u - c.F.toBase 1 (s u))

/-- Corollary 3.13: zeros `x_k` of `f` converging to `x₀` in `X₀` eventually lie in every `X_m`
and converge to `x₀` in `X_m`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X),
    IsTameStrongBundle Bd → Bd.IsScSmoothSection f → IsScFredholmGermB Bd f x₀ →
    IsZeroAt P f x₀ →
      ∀ xs : ℕ → X, (∀ k, IsZeroAt P f (xs k)) → Tendsto xs atTop (𝓝 x₀) →
        ∀ m : ℕ, ∃ K : ℕ, (∀ k ≥ K, xs k ∈ PX.levelSet m) ∧
          ∃ (y : ℕ → PX.levelSet m) (yLim : PX.levelSet m), (yLim : X) = x₀ ∧
            (∀ k ≥ K, (y k : X) = xs k) ∧
            @Tendsto ℕ (PX.levelSet m) y atTop (@nhds _ (PX.levelTopology m) yLim)

end RoundTrip.V3_15
