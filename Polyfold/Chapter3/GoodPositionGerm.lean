import Polyfold.Chapter3.FredholmGermLinearization
import Polyfold.Chapter3.GermPushforward
import Polyfold.Chapter3.GoodPosition
import Polyfold.Chapter2.TameRetracts

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6,
**Definition 3.6.6 (preprint 3.53)** (good position of an sc-Fredholm germ) in the chart of Definition 3.1.11 (preprint 3.11), and
the linear part of the proof of **Theorem 3.6.8 (preprint 3.54)**: if the germ is in good position then `Dg(0)` is
surjective and `ker Dg(0)` is in good position to the partial quadrant `C` in `E`, and the same
holds for the push-forward `Ψ_*(g) = h + t` under the conjugating strong bundle isomorphism, which
are the hypotheses of Theorem 3.5.11 (preprint 3.47) (local germ solvability).

# Good position of an sc-Fredholm germ

## The text, paraphrased

(Definition 3.6.6 (preprint 3.53)) An sc-Fredholm germ `(f, x)` of a tame strong bundle with `f(x) = 0` is in good
position if (1) `f'(x) : T_xX → Y_x` is surjective and (2) if `d_X(x) ≥ 1`, `ker f'(x) ⊆ T_xX` is in
good position to the partial cone `C_xX` in the tangent space `T_xX`.

(Proof of Theorem 3.6.8 (preprint 3.54), the linear part) "From the postulated surjectivity of `f'(x)` we deduce
that `Tf̃(0) : T₀O → K₀` is surjective.  Hence, by Proposition 3.5, `Dg(0)` is surjective.  Since
`ker f'(x)` is in good position to `C_xX` and `Tϕ(x)(C_xX) = C₀O = T₀O ∩ C`, the kernel
`ker Tf̃(0)` is in good position to `C₀O`.  The retract `O` is tame, hence `T₀O` has the
sc-complement `ker Dr(0)` in `E` (Proposition 2.35), `E = T₀O ⊕ ker Dr(0)`, and `ker Dr(0) ⊆ E_x`
at `x = 0`.  If `Z ⊆ T₀O` is a good complement of `ker Tf̃(0)` in `T₀O`, then `Z ⊕ ker Dr(0)` is a
good complement of `ker Tf̃(0)` in `E`.  Since `ker Tf̃(0) ⊕ {0} = ker Dg(0)` by the properties of
the filler, `ker Dg(0)` is in good position to `C` in `E`."

## What is formalized

* `Polyfold.IsInGoodPositionIn E T C N`: Definition 3.1.24 (preprint 3.21) inside a subspace `T ⊆ E₀` (`N ⊆ T`,
  `N ∩ C` has nonempty interior in `N`, and `N` has a good complement `P ⊆ T` in `T`); for `T = E₀`
  it is `IsInGoodPosition` (`isInGoodPositionIn_top_iff`).
* `Polyfold.IsInGoodPositionIn.isInGoodPosition`: **the transport lemma** of the proof of
  Theorem 3.6.8 (preprint 3.54): if `π` is a bounded idempotent with `(1 − π)E ⊆ E₀ = {v | (Tv)_i = 0 ∀ i}` (the
  minimal subspace at `0`), then good position inside `T = πE` implies good position in `E`, with
  the good complement `P ⊕ (1 − π)E` and the constant `ε/(‖π‖ + 1)`.
* `Polyfold.IsFillerOf.ker_deriv_le_range`: `ker Dg(0) ⊆ T₀O = Dr(0)E` (the text's
  `ker Tf̃(0) ⊕ {0} = ker Dg(0)`), and `IsFillerOf.map_ker_fillerRestrict`: the kernel of
  `Tf̃(0) = Dg(0)|_{T₀O}` is `ker Dg(0)`.
* `Polyfold.IsGoodPositionAt hU hR h0 g`: **Definition 3.6.6 (preprint 3.53) in the chart**: `Tf̃(0) : T₀O → K₀` is
  onto and `ker Dg(0) (= ker Tf̃(0))` is in good position to `C₀O = T₀O ∩ C` inside `T₀O`.
  `IsGoodPositionAt.surjective_fillerRestrict` identifies (1) with the surjectivity of
  `fillerRestrict`.
* `Polyfold.theorem_3_6_8_linear_wholeChart`: **the linear part of Theorem 3.6.8 (preprint 3.54)**: for a filled version `g`
  at a zero with the germ in good position, and `(1 − Dr(0))E ⊆ E₀` (Proposition 2.5.3 (preprint 2.35) for the tame
  retraction `r`), `Dg(0)` is surjective and `ker Dg(0)` is in good position to `C` in `E`;
  `theorem_3_6_8_linear_of_isTameWith_wholeChart` derives the hypothesis on `(1 − Dr(0))E` from a tame
  `ScRetraction` with the same domain and map (Proposition 2.5.3 (preprint 2.35)).
* `Polyfold.scDeriv_mem_iff_of_inverse`: the text's "`C' = Tψ(0)C`" for an sc-diffeomorphism
  `ψ : U → U'` between relatively open subsets of partial quadrants with `ψ(0) = 0` (the one-sided
  sign argument of Lemma 2.4.9 (preprint 2.29) for `ψ` and `ψ⁻¹`).
* `Polyfold.pushforward Ψ Ψ' g` (`Ψ_*(g)(u') = (Ψ(ψ⁻¹(u'), g(ψ⁻¹(u'))))₂`, the text's `h + t`),
  `IsStrongBundleIso.pushforward_linearization_wholeChart` (`D(Ψ_*g)(0) = Γ(0) ∘ Dg(0) ∘ Dψ(0)⁻¹`),
  `IsStrongBundleIso.pushforward_surjective_wholeChart`, `IsStrongBundleIso.pushforward_ker_isInGoodPosition_wholeChart`
  (`N' = ker D(h + t)(0) = Dψ(0)(ker Dg(0))` is in good position to `C'`, by Lemma 3.5.9 (preprint 3.45)).
* `Polyfold.StrongBundle.IsGoodPositionGermWholeChart f x₀`: Definition 3.6.6 (preprint 3.53) for a section of a strong
  bundle (the data of Definition 3.1.11 (preprint 3.11) with the germ in good position in the chart), and
  `theorem_3_6_8_pushforward_section_wholeChart`, the bundle form of `theorem_3_6_8_pushforward_wholeChart`.
* `Polyfold.theorem_3_6_8_pushforward_wholeChart`: **the step of Theorem 3.6.8 (preprint 3.54) before Theorem 3.5.11 (preprint 3.47)**: under the
  hypotheses of Proposition 3.6.5 (preprint 3.52) with the germ in good position and `(1 − Dr(0))E ⊆ E₀`, for any
  conjugating isomorphism `Ψ` with `ψ(0) = 0` the push-forward `Ψ_*(g)` is sc-smooth, vanishes at
  `0`, and `D(Ψ_*g)(0)` is a surjective Fredholm operator whose kernel is in good position to `C'`.
  The next steps of Theorem 3.6.8 (preprint 3.54) are in `GlobalIFT.lean`: Theorem 3.5.11 (preprint 3.47) (`LocalSolvability.lean`)
  applied to `h + t` gives the graph description (3) of the solution set
  (`Polyfold.theorem_3_6_8_graph_wholeChart`), and Theorem 3.2.3 (preprint 3.27) (`TangentGerm.lean`) the manifold structure
  from the tangent germ property (`theorem_3_6_11_of_tangentGerm`, `theorem_3_6_10_of_tangentGerm`).
  The good position at the nearby zeros (Corollary 3.5.3 (preprint 3.41) in `SolutionLinearization.lean`, Lemma
  3.55 in `GoodPositionOpen.lean`, transported to charts centred at those zeros) is not assembled
  (Findings, Chapter 3, item 87).

## What the text leaves implicit, and the choices made (the findings)

* **Condition (2) of Definition 3.6.6 (preprint 3.53) is stated unconditionally.**  If `d_X(x) = 0` the partial
  cone is the whole tangent space and (2) holds for every finite-dimensional subspace; the case
  distinction of the text is therefore not needed.
* **The projection onto `T₀O` along `ker Dr(0)` is `Dr(0)`.**  The estimate `|z| ≤ ε|n|` for the
  `Z`-component `z` of `p = z + k ∈ Z ⊕ ker Dr(0)` with `|p| ≤ ε'|n|` is where the splitting must
  be topological: `z = Dr(0)p`, so `ε' = ε/(‖Dr(0)‖ + 1)` works.  The text does not mention this
  constant.
* **`ker Dr(0) ⊆ E_x` is used only through the coordinates**: `n + z + k ∈ C ↔ n + z ∈ C` because
  the `ℝⁿ`-coordinates of `k` vanish.
* **`ker Dg(0) ⊆ T₀O`** follows from property (3) of the filler ((1 − ρ(0))Dg(0) injective on
  `ker Dr(0)`) and `ρ(0)Dg(0)Dr(0) = Dg(0)Dr(0)`; the text's "by the properties of the filler".
* **Tameness enters only through `(1 − Dr(0))E ⊆ E₀`** (Proposition 2.5.3 (preprint 2.35)); the theorem is stated
  with this inclusion as hypothesis and derived for a tame `ScRetraction`.
* **"`C' = Tψ(0)C`"** is not part of the data of a conjugation (`IsConjugateToBasicGerm`); it is a
  theorem (`scDeriv_mem_iff_of_inverse`), proved by the sign argument of Lemma 2.4.9 (preprint 2.29) applied to `ψ`
  and `ψ⁻¹`, since `C_0 = C` at the corner `0` (`partialQuadrantAtWith_zero`).
* **The push-forward is linearized by the chain rule** `D(κ ∘ ψ⁻¹)(0) = Dκ(0)Dψ⁻¹(0)` with
  `κ(u) = (Ψ(u, g(u)))₂` and `Dκ(0) = Γ(0)Dg(0)` (`g(0) = 0`, `Ψ` linear on the fibres); the text
  writes `Ψ_*(g) = h + t` and uses Propositions 3.1.10 and 1.1.11 (preprint 3.10 and 1.10) for `D(h + t)(0)`; here the Fredholm
  property of `D(Ψ_*g)(0)` is transported from `Dg(0)` (Proposition 3.6.5 (preprint 3.52)) through the isomorphisms.
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

variable {E F : ScBanach}

/-! ### Good position inside a subspace -/

section GoodPositionIn

variable {C : Set (E 0)}

/-- **Definition 3.1.24 (preprint 3.21) inside a subspace `T ⊆ E₀`**: `N ⊆ T`, the interior of `N ∩ C` in `N` is
nonempty, and `N` has a good complement `P ⊆ T` in `T` (`T = N ⊕ P` with the constant `ε`).  For
`T = E₀` this is `IsInGoodPosition`; for `T = T₀O` and `C` the partial quadrant it is good position
to the partial cone `C₀O = T₀O ∩ C` in `T₀O` (Definition 3.6.6 (preprint 3.53) (2)). -/
structure IsInGoodPositionIn (E : ScBanach) (T : Submodule ℝ (E 0)) (C : Set (E 0))
    (N : Submodule ℝ (E 0)) : Prop where
  le : N ≤ T
  interior_nonempty : (interior (Subtype.val ⁻¹' C : Set N)).Nonempty
  exists_goodComplement : ∃ P : Submodule ℝ (E 0), P ≤ T ∧ N ⊓ P = ⊥ ∧ N ⊔ P = T ∧
    ∃ ε > 0, ∀ x ∈ N, ∀ p ∈ P, ‖p‖ ≤ ε * ‖x‖ → (x ∈ C ↔ x + p ∈ C)

/-- Good position inside `E₀` is good position. -/
theorem isInGoodPositionIn_top_iff {N : Submodule ℝ (E 0)} :
    IsInGoodPositionIn E ⊤ C N ↔ IsInGoodPosition E C N := by
  constructor
  · rintro ⟨-, hint, P, -, h1, h2, ε, hε, hgood⟩
    exact ⟨hint, P, ⟨IsCompl.of_eq h1 h2, ε, hε, hgood⟩⟩
  · rintro ⟨hint, P, ⟨hc, ε, hε, hgood⟩⟩
    exact ⟨le_top, hint, P, le_top, hc.inf_eq_bot, hc.sup_eq_top, ε, hε, hgood⟩

variable {n : ℕ} {W : ScBanach}

/-- **The transport lemma of the proof of Theorem 3.6.8 (preprint 3.54).**  Let `π : E₀ → E₀` be a bounded
idempotent with `(1 − π)E₀ ⊆ E₀ = {v | (Tv)_i = 0 for all i}` (the minimal subspace at `0`,
Proposition 2.5.3 (preprint 2.35) for `π = Dr(0)`), and `C = T⁻¹([0,∞)ⁿ ⊕ W)`.  If `N` is in good position to `C`
inside `T = πE₀` then `N` is in good position to `C` in `E₀`: a good complement is `P ⊕ (1 − π)E₀`
with the constant `ε/(‖π‖ + 1)`. -/
theorem IsInGoodPositionIn.isInGoodPosition (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hC : C = T 0 ⁻¹' quadrant n W 0) (π : E 0 →L[ℝ] E 0) (hπ : ∀ x, π (π x) = π x)
    (hK : LinearMap.range (ContinuousLinearMap.id ℝ (E 0) - π : E 0 →ₗ[ℝ] E 0) ≤
      minimalSubspaceWith T 0)
    {N : Submodule ℝ (E 0)} (hN : IsInGoodPositionIn E (rangeS π) C N) : IsInGoodPosition E C N := by
  obtain ⟨hNT, hint, P, hPT, hNP, hNPT, ε, hε, hgood⟩ := hN
  set K : Submodule ℝ (E 0) := LinearMap.range (ContinuousLinearMap.id ℝ (E 0) - π : E 0 →ₗ[ℝ] E 0)
    with hKdef
  have hπT : ∀ x ∈ rangeS π, π x = x := by
    rintro _ ⟨y, rfl⟩
    exact hπ y
  have hπK : ∀ k ∈ K, π k = 0 := by
    rintro _ ⟨y, rfl⟩
    change π (y - π y) = 0
    rw [map_sub, hπ, sub_self]
  have hKcoord : ∀ k ∈ K, ∀ i, (T 0 k).1 i = 0 := fun k hk i =>
    (mem_minimalSubspaceWith T).1 (hK hk) i (by rw [map_zero]; rfl)
  have hmemC : ∀ (x : E 0), ∀ k ∈ K, (x + k ∈ C ↔ x ∈ C) := by
    intro x k hk
    rw [hC, mem_preimage, mem_preimage]
    change (∀ i, 0 ≤ (T 0 (x + k)).1 i) ↔ ∀ i, 0 ≤ (T 0 x).1 i
    refine forall_congr' fun i => ?_
    rw [map_add, Prod.fst_add, Pi.add_apply, hKcoord k hk i, add_zero]
  refine ⟨hint, P ⊔ K, ⟨IsCompl.of_eq ?_ ?_, ?_⟩⟩
  · -- `N ⊓ (P ⊔ K) = ⊥`
    rw [eq_bot_iff]
    rintro x ⟨hxN, hxPK⟩
    obtain ⟨p, hp, k, hk, rfl⟩ := Submodule.mem_sup.1 hxPK
    have h1 : π (p + k) = p + k := hπT _ (hNT hxN)
    rw [map_add, hπT p (hPT hp), hπK k hk, add_zero] at h1
    have hk0 : k = 0 := by
      have := congrArg (fun z => z - p) h1
      simpa using this.symm
    rw [hk0, add_zero] at hxN ⊢
    have : p ∈ N ⊓ P := ⟨hxN, hp⟩
    rwa [hNP] at this
  · -- `N ⊔ (P ⊔ K) = ⊤`
    rw [eq_top_iff]
    intro x _
    rw [← sup_assoc, hNPT]
    exact Submodule.mem_sup.2 ⟨π x, ⟨x, rfl⟩, x - π x, ⟨x, rfl⟩, by abel⟩
  · -- the constant
    refine ⟨ε / (‖π‖ + 1), by positivity, ?_⟩
    intro x hx q hq hle
    obtain ⟨p, hp, k, hk, rfl⟩ := Submodule.mem_sup.1 hq
    have hpq : π (p + k) = p := by rw [map_add, hπT p (hPT hp), hπK k hk, add_zero]
    have hpn : ‖p‖ ≤ ε * ‖x‖ := by
      calc ‖p‖ = ‖π (p + k)‖ := by rw [hpq]
        _ ≤ ‖π‖ * ‖p + k‖ := π.le_opNorm _
        _ ≤ ‖π‖ * (ε / (‖π‖ + 1) * ‖x‖) := by gcongr
        _ = ε * ‖x‖ * (‖π‖ / (‖π‖ + 1)) := by ring
        _ ≤ ε * ‖x‖ * 1 := by
          gcongr
          rw [div_le_one (by positivity)]; linarith
        _ = ε * ‖x‖ := mul_one _
    rw [← add_assoc, hmemC (x + p) k hk]
    exact hgood x hx p hp hpn

end GoodPositionIn

/-! ### The kernel of the linearization lies in `T₀O` -/

section Kernel

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open StrongRetr

namespace IsFillerOf

variable {hU : IsRelOpenInQuadrant E C U} {hR : IsStrongBundleRetraction U R} {h0 : (0 : E 0) ∈ U}
  {fb g : E 0 → F 0} (hfg : IsFillerOf hU hR h0 fb g)

include hfg in
/-- `ker Dg(0) ⊆ T₀O = Dr(0)E` (the text's `ker Tf̃(0) ⊕ {0} = ker Dg(0)`): by property (3) of the
filler, `(1 − ρ(0))Dg(0)` is injective on `ker Dr(0)`, and `(1 − ρ(0))Dg(0)Dr(0) = 0`. -/
theorem ker_deriv_le_range (hg : IsScSmooth U g) (hg0 : g 0 = 0) (h0O : (0 : E 0) ∈ r R '' U)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) :
    LinearMap.ker (scDeriv U g 0 : E 0 →ₗ[ℝ] F 0) ≤ rangeS (scDeriv U (r R) 0) := by
  intro x hx
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx
  obtain ⟨Φ, hΦ⟩ := hfg.exists_kerEquiv hg hg0 h0O
  have hk : scDeriv U (r R) 0 (x - scDeriv U (r R) 0 x) = 0 := by
    rw [map_sub, scDeriv_r_idem hU hR h0O, sub_self]
  have hΦk : ((Φ ⟨x - scDeriv U (r R) 0 x, hk⟩ :
      ↥(LinearMap.ker ((ρCLM hR h0 : F 0 →L[ℝ] F 0) : F 0 →ₗ[ℝ] F 0))) : F 0) = 0 := by
    rw [hΦ ⟨x - scDeriv U (r R) 0 x, hk⟩]
    change scDeriv U g 0 (x - scDeriv U (r R) 0 x) -
      ρCLM hR h0 (scDeriv U g 0 (x - scDeriv U (r R) 0 x)) = 0
    rw [map_sub, hx, zero_sub, map_neg, hfg.ρ_deriv_comp_r hg hg0 h0O hfK x, sub_self]
  have hk0 : (⟨x - scDeriv U (r R) 0 x, hk⟩ :
      ↥(LinearMap.ker ((scDeriv U (r R) 0 : E 0 →L[ℝ] E 0) : E 0 →ₗ[ℝ] E 0))) = 0 :=
    Φ.map_eq_zero_iff.1 (Subtype.ext (by rw [hΦk]; rfl))
  have hxk : x - scDeriv U (r R) 0 x = 0 := congrArg Subtype.val hk0
  exact ⟨x, by rw [sub_eq_zero] at hxk; exact hxk.symm⟩

include hfg in
/-- The kernel of `Tf̃(0) = Dg(0)|_{T₀O}`, as a subspace of `E₀`, is `ker Dg(0)`. -/
theorem map_ker_fillerRestrict (hg : IsScSmooth U g) (hg0 : g 0 = 0) (h0O : (0 : E 0) ∈ r R '' U)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ))
    (h1 : ∀ x, ρCLM hR h0 (scDeriv U g 0 (scDeriv U (r R) 0 x)) =
      scDeriv U g 0 (scDeriv U (r R) 0 x)) :
    (LinearMap.ker (fillerRestrictₗ (scDeriv U (r R) 0) (ρCLM hR h0) (scDeriv U g 0) h1)).map
        (rangeS (scDeriv U (r R) 0)).subtype =
      LinearMap.ker (scDeriv U g 0 : E 0 →ₗ[ℝ] F 0) := by
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, hyk, rfl⟩
    have hyk' : fillerRestrictₗ (scDeriv U (r R) 0) (ρCLM hR h0) (scDeriv U g 0) h1 ⟨y, hy⟩ = 0 :=
      hyk
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    exact congrArg Subtype.val hyk'
  · intro hx
    refine ⟨⟨x, hfg.ker_deriv_le_range hg hg0 h0O hfK hx⟩, ?_, rfl⟩
    show fillerRestrictₗ (scDeriv U (r R) 0) (ρCLM hR h0) (scDeriv U g 0) h1 ⟨x, _⟩ = 0
    exact Subtype.ext (by rw [fillerRestrictₗ_apply]; exact hx)

end IsFillerOf

end Kernel

/-! ### Definition 3.6.6 (preprint 3.53) in the chart -/

section Def353

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open StrongRetr

/-- **Definition 3.6.6 (preprint 3.53) in the chart of Definition 3.1.11 (preprint 3.11)**: for the filled version `g` of the
principal part at the zero `0`, the sc-Fredholm germ is **in good position** if (1)
`Tf̃(0) = Dg(0)|_{T₀O} : T₀O → K₀` is onto, and (2) `ker Tf̃(0) = ker Dg(0)` is in good position to
the partial cone `C₀O = T₀O ∩ C` inside `T₀O = Dr(0)E` (`IsInGoodPositionIn`).  (2) is stated
without the text's case distinction `d_X(x) ≥ 1`: at an interior point it holds trivially. -/
structure IsGoodPositionAt (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E 0) ∈ U) (g : E 0 → F 0) : Prop where
  surj : ∀ y ∈ rangeS (ρCLM hR h0), ∃ x ∈ rangeS (scDeriv U (r R) 0), scDeriv U g 0 x = y
  kernel : IsInGoodPositionIn E (rangeS (scDeriv U (r R) 0)) C
    (LinearMap.ker (scDeriv U g 0 : E 0 →ₗ[ℝ] F 0))

/-- Condition (1) of Definition 3.6.6 (preprint 3.53) is the surjectivity of `fillerRestrict`. -/
theorem IsGoodPositionAt.surjective_fillerRestrict {hU : IsRelOpenInQuadrant E C U}
    {hR : IsStrongBundleRetraction U R} {h0 : (0 : E 0) ∈ U} {g : E 0 → F 0}
    (hgp : IsGoodPositionAt hU hR h0 g)
    (h1 : ∀ x, ρCLM hR h0 (scDeriv U g 0 (scDeriv U (r R) 0 x)) =
      scDeriv U g 0 (scDeriv U (r R) 0 x)) :
    Surjective (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (scDeriv U g 0) h1) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, hxy⟩ := hgp.surj y hy
  exact ⟨⟨x, hx⟩, Subtype.ext (by rw [fillerRestrict_apply]; exact hxy)⟩

variable {n : ℕ} {W : ScBanach}

/-- **Theorem 3.6.8 (preprint 3.54), the linear part**: let `g` be a filled version of the principal part `f̂` of a
section at a zero (`f̂(0) = 0`), with the germ in good position (Definition 3.6.6 (preprint 3.53)), and assume
`(1 − Dr(0))E ⊆ E₀` (Proposition 2.5.3 (preprint 2.35) for the tame retraction `r`; `E₀` the minimal subspace at
`0`).  Then `Dg(0) : E → F` is surjective and `ker Dg(0)` is in good position to `C` in `E`. -/
theorem theorem_3_6_8_linear_wholeChart (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U) {fb g : E 0 → F 0}
    (hfill : IsFilledVersion hU hR h0 fb g) (hfb0 : fb 0 = 0)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ))
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hC : C = T 0 ⁻¹' quadrant n W 0)
    (hK : LinearMap.range (ContinuousLinearMap.id ℝ (E 0) - scDeriv U (r R) 0 : E 0 →ₗ[ℝ] E 0) ≤
      minimalSubspaceWith T 0)
    (hgp : IsGoodPositionAt hU hR h0 g) :
    Surjective (scDeriv U g 0) ∧
      IsInGoodPosition E C (LinearMap.ker (scDeriv U g 0 : E 0 →ₗ[ℝ] F 0)) := by
  have hg : IsScSmooth U g := hfill.isScSmooth
  have hg0 : g 0 = 0 := by rw [← hfill.filler.eq_on.self_of_nhds h0O, hfb0]
  obtain ⟨h1, hsurj, -, -⟩ := hfill.filler.proposition_3_1_5 hg hg0 h0O hfK
  refine ⟨hsurj.1 (hgp.surjective_fillerRestrict h1), ?_⟩
  exact hgp.kernel.isInGoodPosition T hC (scDeriv U (r R) 0) (scDeriv_r_idem hU hR h0O) hK

/-- **Theorem 3.6.8 (preprint 3.54), the linear part, for a tame retraction**: the hypothesis `(1 − Dr(0))E ⊆ E₀` of
`theorem_3_6_8_linear_wholeChart` is Proposition 2.5.3 (preprint 2.35) for a tame sc-retraction `Rr` with `Rr.U = U` and
`Rr = r` (the base retraction of the strong bundle retraction `R`). -/
theorem theorem_3_6_8_linear_of_isTameWith_wholeChart (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    {fb g : E 0 → F 0} (hfill : IsFilledVersion hU hR h0 fb g) (hfb0 : fb 0 = 0)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ))
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hC : C = T 0 ⁻¹' quadrant n W 0)
    (Rr : ScRetraction E C) (hRrU : Rr.U = U) (hRr : ⇑Rr = r R) (hRt : Rr.IsTameWith T)
    (hgp : IsGoodPositionAt hU hR h0 g) :
    Surjective (scDeriv U g 0) ∧
      IsInGoodPosition E C (LinearMap.ker (scDeriv U g 0 : E 0 →ₗ[ℝ] F 0)) := by
  refine theorem_3_6_8_linear_wholeChart hU hR h0 h0O hfill hfb0 hfK T hC ?_ hgp
  have h01 : (0 : E 1) ∈ E.lvlSet Rr.retract 1 := by
    rw [ScBanach.mem_lvlSet, map_zero, ScRetraction.retract, hRrU, hRr]
    exact h0O
  have hs : (0 : E 1) ∈ E.smoothLvl 1 := by
    change E.toBase 1 0 ∈ (E.smooth : Set (E 0))
    rw [map_zero]; exact E.smooth.zero_mem
  have h235 := (proposition_2_5_3 hC hRt h01 hs).1
  rw [map_zero] at h235
  have heq : scDeriv Rr.U Rr 0 = scDeriv U (r R) 0 := by rw [hRrU, hRr]
  rwa [heq] at h235

end Def353

/-! ### Transfer to the conjugated germ (`Ψ_*(g) = h + t`) -/

section Transfer

variable {E' F' : ScBanach} {C U : Set (E 0)} {C' U' : Set (E' 0)}

/-- At `0` the partial quadrant `C_0` is `C` itself. -/
lemma partialQuadrantAtWith_zero {n : ℕ} {W : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) :
    partialQuadrantAtWith T 0 = T 0 ⁻¹' quadrant n W 0 := by
  ext v
  constructor
  · intro h i
    exact h i (by rw [map_zero]; rfl)
  · intro h i _
    exact h i

/-- **`C' = Tψ(0)C`** (proof of Theorem 3.6.8 (preprint 3.54)): for an sc-diffeomorphism `ψ : U → U'` between
relatively open subsets of the partial quadrants `C`, `C'` with `ψ(0) = 0`, `x ∈ C ↔ Dψ(0)x ∈ C'`
(the one-sided sign argument `IsSc1With.mapsTo_partialQuadrant` for `ψ` and for `ψ⁻¹`). -/
theorem scDeriv_mem_iff_of_inverse (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsRelOpenInQuadrant E' C' U') {ψ : E 0 → E' 0} {ψ' : E' 0 → E 0}
    (hψ : IsScSmooth U ψ) (hψ' : IsScSmooth U' ψ') (hψU : MapsTo ψ U U') (hψ'U : MapsTo ψ' U' U)
    (hψψ' : ∀ u ∈ U, ψ' (ψ u) = u) (h0 : (0 : E 0) ∈ U) (hψ0 : ψ 0 = 0) (x : E 0) :
    x ∈ C ↔ scDeriv U ψ 0 x ∈ C' := by
  obtain ⟨n, W, T, hT⟩ := hU.isPartialQuadrant
  obtain ⟨n', W', T', hT'⟩ := hU'.isPartialQuadrant
  have hU'C : U' ⊆ C' := by obtain ⟨O, -, rfl⟩ := hU'.relOpen; exact inter_subset_right
  have hUC : U ⊆ C := by obtain ⟨O, -, rfl⟩ := hU.relOpen; exact inter_subset_right
  have h0' : (0 : E' 0) ∈ U' := hψ0 ▸ hψU h0
  have hψ'0 : ψ' 0 = 0 := by rw [← hψ0, hψψ' 0 h0]
  have h01 : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have h01' : (0 : E' 1) ∈ E'.lvlSet U' 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0'
  have hfwd := hψ.isSc1.isSc1With_scDeriv.mapsTo_partialQuadrant T hT T' hT' hU
    (fun u hu => hU'C (hψU hu)) h01
  have hbwd := hψ'.isSc1.isSc1With_scDeriv.mapsTo_partialQuadrant T' hT' T hT hU'
    (fun u hu => hUC (hψ'U hu)) h01'
  rw [map_zero, hψ0, partialQuadrantAtWith_zero, partialQuadrantAtWith_zero, ← hT, ← hT'] at hfwd
  rw [map_zero, hψ'0, partialQuadrantAtWith_zero, partialQuadrantAtWith_zero, ← hT, ← hT'] at hbwd
  refine ⟨fun hx => hfwd hx, fun hx => ?_⟩
  have hlev : levelMap ψ 1 (0 : E 1) = 0 :=
    levelMap_eq_of_toBase_eq (by rw [map_zero, map_zero, hψ0])
  have hinv := scDeriv_comp_eq_self hU hU' hψ.isSc1 hψ'.isSc1 hψU hψψ' h01 x
  rw [hlev] at hinv
  have := hbwd hx
  rwa [hinv] at this

variable {Ψ : E 0 × F 0 → E' 0 × F' 0} {Ψ' : E' 0 × F' 0 → E 0 × F 0}

/-- **The linearization of the push-forward**: `Ψ_*(g)` is sc-smooth with `Ψ_*(g)(0) = 0`, and
`D(Ψ_*g)(0) = Γ(0) ∘ Dg(0) ∘ Dψ(0)⁻¹` with the isomorphisms `Γ(0) : F → F'` (the fibre map of `Ψ`
over `0`) and `Dψ(0) : E → E'`, which carries `C` onto `C'`. -/
theorem IsStrongBundleIso.pushforward_linearization_wholeChart (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsRelOpenInQuadrant E' C' U') (hΨ : IsStrongBundleIso U U' Ψ Ψ') (h0 : (0 : E 0) ∈ U)
    (hψ0 : IsStrongBundleMap.base Ψ 0 = 0) {g : E 0 → F 0} (hg : IsScSmooth U g) (hg0 : g 0 = 0) :
    IsScSmooth U' (pushforward Ψ Ψ' g) ∧ pushforward Ψ Ψ' g 0 = 0 ∧
      ∃ (Γ : F 0 ≃L[ℝ] F' 0) (S : E 0 ≃L[ℝ] E' 0), (∀ x, x ∈ C ↔ S x ∈ C') ∧
        scDeriv U' (pushforward Ψ Ψ' g) 0 =
          (Γ : F 0 →L[ℝ] F' 0).comp ((scDeriv U g 0).comp (S.symm : E' 0 →L[ℝ] E 0)) := by
  have h01 : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have h0U' : (0 : E' 0) ∈ U' := hψ0 ▸ hΨ.toFun.base_mem h0
  have h01' : (0 : E' 1) ∈ E'.lvlSet U' 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0U'
  set ψ := IsStrongBundleMap.base Ψ with hψdef
  set ψ' := IsStrongBundleMap.base Ψ' with hψ'def
  have hψψ' : ∀ u ∈ U, ψ' (ψ u) = u := fun u hu => hΨ.base_base hu
  have hψ'ψ : ∀ u' ∈ U', ψ (ψ' u') = u' := fun u' hu' => hΨ.base_base' hu'
  have hψ'0 : ψ' 0 = 0 := hΨ.base_zero' h0 hψ0
  have hψsm : IsScSmooth U ψ := hΨ.toFun.base_isScSmooth hU
  have hψ'sm : IsScSmooth U' ψ' := hΨ.invFun.base_isScSmooth hU'
  have hψU' : MapsTo ψ U U' := fun u hu => hΨ.toFun.base_mem hu
  have hψ'U : MapsTo ψ' U' U := fun u hu => hΨ.invFun.base_mem hu
  -- the map `κ(u) = (Ψ(u, g(u)))₂` on `U`
  have hUF := (hU.prod_univ F).isScDomain
  have hpairsm : IsScSmooth U (scPair (_root_.id : E 0 → E 0) g) :=
    (isScSmooth_id hU.isScDomain).scPair hU.isScDomain hg
  have hκsm : IsScSmooth U fun u => (Ψ (u, g u)).2 :=
    (IsScSmooth.comp hU.isScDomain hUF (hΨ.toFun.isScSmooth_zero.snd hUF) hpairsm
      fun u hu => ⟨hu, mem_univ _⟩).congr hU.isScDomain fun _ _ => rfl
  have hpush : pushforward Ψ Ψ' g = (fun u => (Ψ (u, g u)).2) ∘ ψ' := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hpush]
    exact IsScSmooth.comp hU'.isScDomain hU.isScDomain hκsm hψ'sm hψ'U
  · show (Ψ (ψ' 0, g (ψ' 0))).2 = 0
    rw [hψ'0, hg0]
    exact hΨ.toFun.snd_zero h0
  -- the isomorphisms
  set Γ := hΨ.toFun.fiberCLM h0 with hΓ
  set Γ' := hΨ.invFun.fiberCLM h0U' with hΓ'
  have hΓΓ' : ∀ y, Γ (Γ' y) = y := fun y => by
    simp only [hΓ, hΓ']
    have h1 : Ψ' (0, y) = (ψ' 0, (Ψ' (0, y)).2) := hΨ.invFun.apply_eq h0U' y
    rw [hψ'0] at h1
    have h2 := congrArg Prod.snd (hΨ.right_inv (0, y) ⟨h0U', mem_univ _⟩)
    rw [h1] at h2
    exact h2
  have hΓ'Γ : ∀ y, Γ' (Γ y) = y := fun y => by
    simp only [hΓ, hΓ']
    have h1 : Ψ (0, y) = (ψ 0, (Ψ (0, y)).2) := hΨ.toFun.apply_eq h0 y
    rw [hψ0] at h1
    have h2 := congrArg Prod.snd (hΨ.left_inv (0, y) ⟨h0, mem_univ _⟩)
    rw [h1] at h2
    exact h2
  have hlevψ : levelMap ψ 1 (0 : E 1) = 0 :=
    levelMap_eq_of_toBase_eq (by rw [map_zero, map_zero, hψ0])
  have hlevψ' : levelMap ψ' 1 (0 : E' 1) = 0 :=
    levelMap_eq_of_toBase_eq (by rw [map_zero, map_zero, hψ'0])
  have hψψ'D : ∀ x, scDeriv U' ψ' 0 (scDeriv U ψ 0 x) = x := fun x => by
    have := scDeriv_comp_eq_self hU hU' hψsm.isSc1 hψ'sm.isSc1 hψU' hψψ' h01 x
    rwa [hlevψ] at this
  have hψ'ψD : ∀ x, scDeriv U ψ 0 (scDeriv U' ψ' 0 x) = x := fun x => by
    have := scDeriv_comp_eq_self hU' hU hψ'sm.isSc1 hψsm.isSc1 hψ'U hψ'ψ h01' x
    rwa [hlevψ'] at this
  refine ⟨ContinuousLinearEquiv.equivOfInverse Γ Γ' hΓ'Γ hΓΓ',
    ContinuousLinearEquiv.equivOfInverse (scDeriv U ψ 0) (scDeriv U' ψ' 0) hψψ'D hψ'ψD,
    fun x => scDeriv_mem_iff_of_inverse hU hU' hψsm hψ'sm hψU' hψ'U hψψ' h0 hψ0 x, ?_⟩
  -- the chain rule
  ext x
  have hchain := scDeriv_comp_apply' hU' hU hψ'sm.isSc1 hκsm.isSc1 hψ'U h01' x
  rw [hlevψ', hΨ.toFun.scDeriv_fiber_comp hU h0 hg hg0] at hchain
  rw [hpush, ← hchain]
  rfl

/-- `D(Ψ_*g)(0)` is surjective if `Dg(0)` is (the text's "`D(h + t)(0)` is surjective"). -/
theorem IsStrongBundleIso.pushforward_surjective_wholeChart (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsRelOpenInQuadrant E' C' U') (hΨ : IsStrongBundleIso U U' Ψ Ψ') (h0 : (0 : E 0) ∈ U)
    (hψ0 : IsStrongBundleMap.base Ψ 0 = 0) {g : E 0 → F 0} (hg : IsScSmooth U g) (hg0 : g 0 = 0)
    (hsurj : Surjective (scDeriv U g 0)) : Surjective (scDeriv U' (pushforward Ψ Ψ' g) 0) := by
  obtain ⟨-, -, Γ, S, -, hD⟩ := hΨ.pushforward_linearization_wholeChart hU hU' h0 hψ0 hg hg0
  rw [hD]
  simp only [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe]
  exact Γ.surjective.comp (hsurj.comp S.symm.surjective)

/-- **`N' = ker D(h + t)(0)` is in good position to `C' = Tψ(0)C`** (proof of Theorem 3.6.8 (preprint 3.54)): the
kernel of `D(Ψ_*g)(0)` is `Dψ(0)(ker Dg(0))`, and good position is carried by `Dψ(0)` (Lemma
3.45). -/
theorem IsStrongBundleIso.pushforward_ker_isInGoodPosition_wholeChart (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsRelOpenInQuadrant E' C' U') (hΨ : IsStrongBundleIso U U' Ψ Ψ') (h0 : (0 : E 0) ∈ U)
    (hψ0 : IsStrongBundleMap.base Ψ 0 = 0) {g : E 0 → F 0} (hg : IsScSmooth U g) (hg0 : g 0 = 0)
    [FiniteDimensional ℝ (LinearMap.ker (scDeriv U g 0 : E 0 →ₗ[ℝ] F 0))]
    (hker : IsInGoodPosition E C (LinearMap.ker (scDeriv U g 0 : E 0 →ₗ[ℝ] F 0))) :
    IsInGoodPosition E' C'
      (LinearMap.ker (scDeriv U' (pushforward Ψ Ψ' g) 0 : E' 0 →ₗ[ℝ] F' 0)) := by
  obtain ⟨-, -, Γ, S, hS, hD⟩ := hΨ.pushforward_linearization_wholeChart hU hU' h0 hψ0 hg hg0
  have hmap := hker.map S hS
  convert hmap using 1
  ext y
  rw [LinearMap.mem_ker, Submodule.mem_map, ContinuousLinearMap.coe_coe, hD]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.map_eq_zero_iff, LinearMap.mem_ker]
  constructor
  · intro h
    exact ⟨S.symm y, h, S.apply_symm_apply y⟩
  · rintro ⟨x, hx, rfl⟩
    have : S.symm ((S : E 0 →ₗ[ℝ] E' 0) x) = x := S.symm_apply_apply x
    rw [this]
    exact hx

end Transfer

/-! ### Theorem 3.6.8 (preprint 3.54): the hypotheses of Theorem 3.5.11 (preprint 3.47) for the push-forward -/

section Thm354

variable {E' F' : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0} {C' U' : Set (E' 0)}
  {Ψ : E 0 × F 0 → E' 0 × F' 0} {Ψ' : E' 0 × F' 0 → E 0 × F 0}

open StrongRetr

variable {n : ℕ} {W : ScBanach}

/-- **Theorem 3.6.8 (preprint 3.54), the step before Theorem 3.5.11 (preprint 3.47)**: under the hypotheses of Proposition 3.6.5 (preprint 3.52)
(`g` a filled version of `f̂` at the zero `0`, `s` a local sc⁺-section with `s(0) = g(0)` and
`g − s` conjugated to a basic germ), with the germ in good position (Definition 3.6.6 (preprint 3.53)) and
`(1 − Dr(0))E ⊆ E₀` (Proposition 2.5.3 (preprint 2.35) for the tame retraction), the push-forward
`Ψ_*(g) = h + t` under **any** strong bundle isomorphism `Ψ : U ◁ F → U' ◁ F'` with `ψ(0) = 0` is
sc-smooth with `Ψ_*(g)(0) = 0`, `D(Ψ_*g)(0) : E' → F'` is a surjective Fredholm operator and its
kernel `N'` is in good position to `C'` in `E'`.  These are the hypotheses of Theorem 3.5.11 (preprint 3.47) (local
germ solvability) for `h + t`. -/
theorem theorem_3_6_8_pushforward_wholeChart (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    {fb g : E 0 → F 0} (hfill : IsFilledVersion hU hR h0 fb g) (hfb0 : fb 0 = 0)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) {s : E 0 → F 1}
    (hs : IsScSmooth (F := F.shift) U s) (hs0 : F.toBase 1 (s 0) = g 0)
    (hconj : IsConjugateToBasicGerm U fun u => g u - F.toBase 1 (s u))
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hC : C = T 0 ⁻¹' quadrant n W 0)
    (hK : LinearMap.range (ContinuousLinearMap.id ℝ (E 0) - scDeriv U (r R) 0 : E 0 →ₗ[ℝ] E 0) ≤
      minimalSubspaceWith T 0)
    (hgp : IsGoodPositionAt hU hR h0 g) (hU' : IsRelOpenInQuadrant E' C' U')
    (hΨ : IsStrongBundleIso U U' Ψ Ψ') (hψ0 : IsStrongBundleMap.base Ψ 0 = 0) :
    IsScSmooth U' (pushforward Ψ Ψ' g) ∧ pushforward Ψ Ψ' g 0 = 0 ∧
      Surjective (scDeriv U' (pushforward Ψ Ψ' g) 0) ∧
      IsFredholm (scDeriv U' (pushforward Ψ Ψ' g) 0) ∧
      IsInGoodPosition E' C'
        (LinearMap.ker (scDeriv U' (pushforward Ψ Ψ' g) 0 : E' 0 →ₗ[ℝ] F' 0)) := by
  have hg : IsScSmooth U g := hfill.isScSmooth
  have hg0 : g 0 = 0 := by rw [← hfill.filler.eq_on.self_of_nhds h0O, hfb0]
  obtain ⟨hsurj, hker⟩ := theorem_3_6_8_linear_wholeChart hU hR h0 h0O hfill hfb0 hfK T hC hK hgp
  obtain ⟨-, -, -, hDgF, -, -, -⟩ := proposition_3_6_5_local_wholeChart hU hR h0 h0O hfill hfb0 hfK hs hs0 hconj
  haveI : FiniteDimensional ℝ (LinearMap.ker (scDeriv U g 0 : E 0 →ₗ[ℝ] F 0)) := hDgF.finite_ker
  obtain ⟨hsm, hz, Γ, S, -, hD⟩ := hΨ.pushforward_linearization_wholeChart hU hU' h0 hψ0 hg hg0
  refine ⟨hsm, hz, hΨ.pushforward_surjective_wholeChart hU hU' h0 hψ0 hg hg0 hsurj, ?_,
    hΨ.pushforward_ker_isInGoodPosition_wholeChart hU hU' h0 hψ0 hg hg0 hker⟩
  rw [hD]
  exact (isFredholm_equiv_comp_equiv hDgF S.symm Γ).1

end Thm354

/-! ### Definition 3.6.6 (preprint 3.53) for sections of strong bundles -/

section Bundle

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

variable (B) in
/-- **Definition 3.6.6 (preprint 3.53)** for a section `f` of the strong bundle `P : Y → X`: `(f, x₀)` is an
**sc-Fredholm germ in good position**: the data of Definition 3.1.11 (preprint 3.11) (a strong bundle chart centred at
`x₀`, a filled version `g` of `f̂`, a local sc⁺-section `s` with `s(0) = g(0)` and `g − s`
conjugated to a basic germ) such that the germ is in good position in the chart (`IsGoodPositionAt`:
`Tf̃(0) : T₀O → K₀` onto, `ker Tf̃(0)` in good position to `C₀O` in `T₀O`). This is the project's
original whole-chart reading, stricter than the text (Findings, Chapter 3, items 220–221, 260–266);
the text's germ reading is `IsGoodPositionGerm` (`GoodPositionGermG.lean`, phase 2, items 270–330). -/
def StrongBundle.IsGoodPositionGermWholeChart (f : X → Y) (x₀ : X) : Prop :=
  x₀ ∈ PX.smoothSet ∧
  ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1),
    IsFilledVersion c.relOpen c.isRetraction h0 (c.principal f) g ∧
    IsScSmooth (F := c.F.shift) c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
    IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u)) ∧
    IsGoodPositionAt c.relOpen c.isRetraction h0 g

/-- A germ in good position is an sc-Fredholm germ. -/
theorem StrongBundle.IsGoodPositionGermWholeChart.isScFredholmGerm {x₀ : X}
    (h : B.IsGoodPositionGermWholeChart f x₀) : B.IsScFredholmGermWholeChart f x₀ := by
  obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, -⟩ := h
  exact ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩

/-- **Theorem 3.6.8 (preprint 3.54), the step before Theorem 3.5.11 (preprint 3.47), for a section**: let `f` be a section of the
strong bundle `P : Y → X` with `f(x₀) = 0` and `(f, x₀)` an sc-Fredholm germ in good position.
Then in the chart of Definition 3.6.6 (preprint 3.53) (centred at `x₀`, with filled version `g` of `f̂`), for every
presentation `T` of the partial quadrant `C` with `(1 − Dr(0))E ⊆ E₀` (Proposition 2.5.3 (preprint 2.35) for a tame
retraction) and every strong bundle isomorphism `Ψ : U ◁ F → U' ◁ F'` with `ψ(0) = 0`, the
push-forward `Ψ_*(g)` is sc-smooth, vanishes at `0`, and `D(Ψ_*g)(0)` is a surjective Fredholm
operator whose kernel is in good position to `C'`; moreover `Dg(0)` is surjective and `ker Dg(0)`
is in good position to `C` in `E`. -/
theorem theorem_3_6_8_pushforward_section_wholeChart (hf : IsSection P f) {x₀ : X}
    (hg : B.IsGoodPositionGermWholeChart f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0)
      (_ : IsFilledVersion c.relOpen c.isRetraction h0 (c.principal f) g),
      ∀ {n : ℕ} {W : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)),
        c.φ.model.C = T 0 ⁻¹' quadrant n W 0 →
        LinearMap.range (ContinuousLinearMap.id ℝ (c.φ.model.E 0) - scDeriv c.U (r c.R) 0 :
          c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) ≤ minimalSubspaceWith T 0 →
        (Surjective (scDeriv c.U g 0) ∧
          IsInGoodPosition c.φ.model.E c.φ.model.C
            (LinearMap.ker (scDeriv c.U g 0 : c.φ.model.E 0 →ₗ[ℝ] c.F 0))) ∧
        ∀ {E' F' : ScBanach} {C' U' : Set (E' 0)}
          {Ψ : c.φ.model.E 0 × c.F 0 → E' 0 × F' 0} {Ψ' : E' 0 × F' 0 → c.φ.model.E 0 × c.F 0},
          IsRelOpenInQuadrant E' C' U' → IsStrongBundleIso c.U U' Ψ Ψ' →
          IsStrongBundleMap.base Ψ 0 = 0 →
          IsScSmooth U' (pushforward Ψ Ψ' g) ∧ pushforward Ψ Ψ' g 0 = 0 ∧
            Surjective (scDeriv U' (pushforward Ψ Ψ' g) 0) ∧
            IsFredholm (scDeriv U' (pushforward Ψ Ψ' g) 0) ∧
            IsInGoodPosition E' C'
              (LinearMap.ker (scDeriv U' (pushforward Ψ Ψ' g) 0 : E' 0 →ₗ[ℝ] F' 0)) := by
  obtain ⟨-, c, hc, hxV, hφ0, h0U, g, s, hfill, hs, hs0, hconj, hgp⟩ := hg
  have h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := by
    rw [c.r_image, ← hφ0]; exact c.φ.mapsTo_model x₀ hxV
  have hfb0 : c.principal f 0 = 0 := by
    have := (c.isZeroAt_iff hf hxV).1 hx₀
    rwa [hφ0] at this
  have hfK : ∀ x ∈ r c.R '' c.U, (x, c.principal f x) ∈ c.R '' (c.U ×ˢ univ) := by
    intro x hx
    rw [c.r_image] at hx
    rw [← c.apply_section hf hx]
    change c (f (c.φ.symm x)) ∈ c.K
    rw [← c.image_source]
    exact ⟨_, c.mem_source_of_proj (by rw [hf]; exact c.φ.symm_mapsTo hx), rfl⟩
  refine ⟨c, hc, hxV, hφ0, h0U, g, hfill, fun T hC hK => ⟨?_, ?_⟩⟩
  · exact theorem_3_6_8_linear_wholeChart c.relOpen c.isRetraction h0U h0O hfill hfb0 hfK T hC hK hgp
  · intro E' F' C' U' Ψ Ψ' hU' hΨ hψ0
    exact theorem_3_6_8_pushforward_wholeChart c.relOpen c.isRetraction h0U h0O hfill hfb0 hfK hs hs0 hconj T
      hC hK hgp hU' hΨ hψ0

end Bundle

end Polyfold
