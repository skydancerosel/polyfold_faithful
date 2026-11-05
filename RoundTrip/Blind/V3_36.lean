import Polyfold
/-! Blind formalization of V3_36 (the text's §3.5, Corollary 3.41, p. 98). `B` is the conjunction
of (1) and (2) (for one `U'`).  Choices:
- Setting (as in the blind V3_35/V3_38/V3_42): `ℝⁿ = Fin n → ℝ`, `ℝᴺ = Fin N → ℝ` (constant
  sc-structures), `C̃ ⊆ ℝⁿ` a partial quadrant, `W` an arbitrary sc-Banach space;
  `E = ℝⁿ ⊕ W` (`ScBanach.paramProd (Fin n → ℝ) W`) with the partial quadrant `C = C̃ × W`,
  `F = ℝᴺ ⊕ W`.  No universe choices arise.
- "`h` basic": `IsBasicGerm C̃ G h B` (Definition 3.7) on a germ of neighbourhoods `G` for some
  contraction map `B`.  "`s` an sc⁺-map, `s(0) = 0`": an sc-smooth germ into `F¹`
  (`IsScSmoothGerm` with target `F.shift`) on the same `G`, `s(0) = 0`.  `f = h + s` (with
  `F₁ → F₀`); its domain `U` is `G₀ = G.U 0`, its level-`m` domain is `G.U m`.
- "`Df(0)` surjective": `Df(0) = D 0` for *any* derivative family `D` of the sc¹-germ `f`
  (`IsSc1GermWith G f D`; unique at level-1 points of the quadrant), `D 0 : E₀ → F₀` onto.  The
  same `D` gives `Df(a, w)` below.
- "`U' ⊆ U` relatively open on level 0": `U' = O ∩ C` with `O` open in `E₀`, `U' ⊆ U`; I add
  `0 ∈ U'` (the statement is local at `0`; without it `U' = ∅` would do).
- "(1) solutions in `U'` are on level 1": every `x ∈ U'` with `f(x) = 0` is the image of some
  `x₁ ∈ E₁`; I read "on level 1" as "in the level-1 part `U₁ = G.U 1` of the domain of `f`" (needed
  for `Df(x₁)` to be meaningful; in the text `f` is sc-smooth on `U`, so `U₁ = U ∩ E₁`).
- "(2) at such solutions `Df(a, w) : E → F` is a surjective Fredholm operator of index `n − N`":
  the bounded operator `D x₁ : E₀ → F₀` is onto and Fredholm in the classical sense (finite-dim
  kernel, closed range, finite-dim cokernel; `IsFredholmOp`, defined here) with index
  `dim ker − dim coker = n − N` (`fredIdx`, as an integer).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_36
open Polyfold

/-- A bounded operator is Fredholm: finite-dimensional kernel, closed range, finite-dimensional
cokernel. -/
def IsFredholmOp {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (L : X →L[ℝ] Y) : Prop :=
  FiniteDimensional ℝ (LinearMap.ker (L : X →ₗ[ℝ] Y)) ∧
    IsClosed (LinearMap.range (L : X →ₗ[ℝ] Y) : Set Y) ∧
    FiniteDimensional ℝ (Y ⧸ LinearMap.range (L : X →ₗ[ℝ] Y))

/-- The Fredholm index `dim ker L − dim (Y / range L)`. -/
noncomputable def fredIdx {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (L : X →L[ℝ] Y) : ℤ :=
  (Module.finrank ℝ (LinearMap.ker (L : X →ₗ[ℝ] Y)) : ℤ) -
    (Module.finrank ℝ (Y ⧸ LinearMap.range (L : X →ₗ[ℝ] Y)) : ℤ)

/-- Corollary 3.41: for `f = h + s` (basic germ plus sc⁺-germ vanishing at `0`) with `Df(0)` onto,
there is a relatively open neighbourhood `U' ⊆ U` of `0` in `C` whose zeros of `f` lie on level 1
(in `U₁`), and at each of them `Df(a, w) : E₀ → F₀` is a surjective Fredholm operator of index
`n − N`. -/
def B : Prop :=
  ∀ (n N : ℕ) (W : ScBanach) (Ct : Set (Fin n → ℝ))
    (G : ScNbhdGerm (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ))
    (h : (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 → (ScBanach.paramProd (Fin N → ℝ) W).lvl 0)
    (Bh : (Fin n → ℝ) × W.lvl 0 → W.lvl 0)
    (s : (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 →
      (ScBanach.paramProd (Fin N → ℝ) W).shift.lvl 0),
    IsPartialQuadrant (ScBanach.const (Fin n → ℝ)) Ct →
    IsBasicGerm Ct G h Bh →
    IsScSmoothGerm (F := (ScBanach.paramProd (Fin N → ℝ) W).shift) G s → s 0 = 0 →
    let f : (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 → (ScBanach.paramProd (Fin N → ℝ) W).lvl 0 :=
      fun x => h x + (ScBanach.paramProd (Fin N → ℝ) W).toBase 1 (s x)
    ∀ D : (ScBanach.paramProd (Fin n → ℝ) W).lvl 1 →
        (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 →L[ℝ] (ScBanach.paramProd (Fin N → ℝ) W).lvl 0,
      IsSc1GermWith G f D → Function.Surjective (D 0) →
      ∃ U' : Set ((ScBanach.paramProd (Fin n → ℝ) W).lvl 0),
        (∃ O : Set ((ScBanach.paramProd (Fin n → ℝ) W).lvl 0),
          IsOpen O ∧ U' = O ∩ (Ct ×ˢ Set.univ)) ∧ 0 ∈ U' ∧ U' ⊆ G.U 0 ∧
        ∀ x ∈ U', f x = 0 →
          ∃ x₁ ∈ G.U 1, (ScBanach.paramProd (Fin n → ℝ) W).toBase 1 x₁ = x ∧
            Function.Surjective (D x₁) ∧ IsFredholmOp (D x₁) ∧
            fredIdx (D x₁) = (n : ℤ) - N

end RoundTrip.V3_36
