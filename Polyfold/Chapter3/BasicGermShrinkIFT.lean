import Polyfold.Chapter3.BasicGermShrink
import Polyfold.Chapter3.SolutionLinearization

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.5,
**Corollary 3.5.3 (preprint 3.41) for the basic germ shrunk to `G″`**, and the data of Theorem 3.4.2 (preprint 3.38) on `G″`: the
nearby solutions `x₁` that Corollary 3.5.3 (preprint 3.41) produces for the conjugated basic germ are mapped by the
inverse base map `ψ'` into the germ `G_g ∩ G_s` on which the filling `g` and the sc⁺-section `s`
of Definition 3.1.11 (preprint 3.11) are sc-smooth.

# Corollary 3.5.3 (preprint 3.41) on the germ `G″`

## The text, paraphrased

(Corollary 3.5.3 (preprint 3.41)) For `h + s` with `h` a basic germ and `s` an sc⁺-germ, `s(0) = 0`, and
`D(h + s)(0)` surjective, the zeros `x` of `h + s` near `0` lie on level `1` and `D(h + s)(x)` is
a surjective Fredholm operator of index `n − N`.  (Proofs of Proposition 3.6.5 (preprint 3.52) and Theorem 3.6.8 (preprint 3.54))
The text applies this to the push-forward `Ψ_*(g) = h + t` and then differentiates `g` at the
points `ψ'(x)`.

## What is formalized

* `Polyfold.ConjugationData.corollary_3_5_3_of_subset_shrinkGerm`: for conjugation data `d`, a germ
  `G'` on the `E`-side, data `𝒮` of Theorem 3.4.2 (preprint 3.38) whose germ lies in
  `G″ = d.shrinkGerm G'` and a basic germ `f` on `𝒮.G`: the conclusion of Corollary 3.5.3 (preprint 3.41)
  (`StabilityData.corollary_3_5_3`) **together with `ψ'₁(x₁) ∈ G'₁` and `ι ψ'₁(x₁) = ψ'(x)`** for
  every nearby zero `x = ι x₁`.  With `G' = G_g ∩ G_s` this is the statement that the filling
  and the sc⁺-section are sc¹ at the point `ψ'₁(x₁)` where the text differentiates them.
* `Polyfold.ConjugationData.corollary_3_5_3_shrink`: the same for the conjugated basic germ
  `d.h` itself, on any germ inside `G″`.
* `Polyfold.ConjugationData.exists_stabilityData_shrinkGerm`: the data of Theorem 3.4.2 (preprint 3.38) on `G″`
  for an sc⁺-germ on `G″` (the push-forward of the sc⁺-section), with `d.h` basic on its germ.

## What the text leaves implicit, and the choices made (the findings)

* The text does not relate the germ of the conjugated basic germ to the germs of `g` and `s`.
  On the shrunk germ `G″` (`BasicGermShrink.lean`) every point produced by Corollary 3.5.3 (preprint 3.41) lies in
  `G″₁` and is therefore admissible; the radius of Corollary 3.5.3 (preprint 3.41) is the one of the data on
  `G″`, which is where the shrinking enters (through the contraction radii and the lifts of
  Theorem 3.5.1 (preprint 3.40) inside `G″₁`).
* The push-forward `t` of the sc⁺-section is an sc-smooth germ on `G″` when `s` is one on `G_s`
  (germ composition with the whole-chart `Ψ[1]` and `ψ'`); that composition is not proved here
  (germ calculus, `GermCalculus.lean`), so `exists_stabilityData_shrinkGerm` takes it as a
  hypothesis.
-/

open Set Filter Topology Function ContinuousLinearMap

noncomputable section

namespace Polyfold

variable {E F : ScBanach} {C U : Set (E 0)} {k : E 0 → F 0}

namespace ConjugationData

variable (d : ConjugationData U k) (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E 0) ∈ U)
  (G' : ScNbhdGerm E C)

/-- **Corollary 3.5.3 (preprint 3.41) on a germ inside `G″`, with the G″ property**: let `d` be conjugation data of
`k`, `G'` a germ of neighbourhoods of `0` in `C`, `𝒮` data of Theorem 3.4.2 (preprint 3.38) (an sc⁺-germ `s` with
`s(0) = 0`) whose germ lies in `G″ = d.shrinkGerm G'`, `f` a basic germ on `𝒮.G` with
`D(f + s)(0)` surjective.  Then there is `r > 0` such that every zero `x ∈ 𝒮.G₀` of `f + s` with
`|x|₀ < r` is `x = ι x₁` with `x₁ ∈ 𝒮.G₁`, `D(f + s)(x₁)` surjective Fredholm of index `n − N`
(Corollary 3.5.3 (preprint 3.41)), **and `ψ'₁(x₁) ∈ G'₁` with `ι ψ'₁(x₁) = ψ'(x)`**. -/
theorem corollary_3_5_3_of_subset_shrinkGerm (𝒮 : StabilityData d.Ct d.W)
    (h𝒮 : ∀ m, 𝒮.G.U m ⊆ (d.shrinkGerm hU h0 G').U m) {Q : Type} [NormedAddCommGroup Q]
    [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] {f : d.Pn × d.W 0 → Q × d.W 0}
    {B : d.Pn × d.W 0 → d.W 0} (hf : IsBasicGerm d.Ct 𝒮.G f B) (hsurj : Surjective (𝒮.Dfs f)) :
    ∃ r > 0, ∀ x ∈ 𝒮.G.U 0, ‖x‖ < r → 𝒮.fsum f x = 0 →
      ∃ x₁ : (ScBanach.paramProd d.Pn d.W) 1, (ScBanach.paramProd d.Pn d.W).toBase 1 x₁ = x ∧
        x₁ ∈ 𝒮.G.U 1 ∧ IsFredholm (𝒮.Dfs' f x₁) ∧
        fredholmIndex (𝒮.Dfs' f x₁) = Module.finrank ℝ d.Pn - Module.finrank ℝ Q ∧
        Surjective (𝒮.Dfs' f x₁) ∧
        levelMap (IsStrongBundleMap.base d.Ψ') 1 x₁ ∈ G'.U 1 ∧
        E.toBase 1 (levelMap (IsStrongBundleMap.base d.Ψ') 1 x₁) =
          IsStrongBundleMap.base d.Ψ' x := by
  obtain ⟨r, hr, hr'⟩ := 𝒮.corollary_3_5_3 d.quadrant hf hsurj
  refine ⟨r, hr, fun x hx hxr hx0 => ?_⟩
  obtain ⟨x₁, hx₁, hx₁G, hF, hind, hsurj'⟩ := hr' x hx hxr hx0
  refine ⟨x₁, hx₁, hx₁G, hF, hind, hsurj', d.levelMap_mem_of_subset_shrinkGerm hU h0 G' h𝒮 hx₁G,
    ?_⟩
  rw [d.toBase_levelMap_of_mem_shrinkGerm hU h0 G' (h𝒮 1 hx₁G), hx₁]

/-- **Corollary 3.5.3 (preprint 3.41) for the conjugated basic germ on a germ inside `G″`**: as
`corollary_3_5_3_of_subset_shrinkGerm` for `f = h` the basic germ of `d` (a basic germ on every
germ inside `G″`, `basic_shrinkGerm`, `IsBasicGerm.mono`). -/
theorem corollary_3_5_3_shrink (𝒮 : StabilityData d.Ct d.W)
    (h𝒮 : ∀ m, 𝒮.G.U m ⊆ (d.shrinkGerm hU h0 G').U m) (hsurj : Surjective (𝒮.Dfs d.h)) :
    ∃ r > 0, ∀ x ∈ 𝒮.G.U 0, ‖x‖ < r → 𝒮.fsum d.h x = 0 →
      ∃ x₁ : (ScBanach.paramProd d.Pn d.W) 1, (ScBanach.paramProd d.Pn d.W).toBase 1 x₁ = x ∧
        x₁ ∈ 𝒮.G.U 1 ∧ IsFredholm (𝒮.Dfs' d.h x₁) ∧
        fredholmIndex (𝒮.Dfs' d.h x₁) = Module.finrank ℝ d.Pn - Module.finrank ℝ d.Q ∧
        Surjective (𝒮.Dfs' d.h x₁) ∧
        levelMap (IsStrongBundleMap.base d.Ψ') 1 x₁ ∈ G'.U 1 ∧
        E.toBase 1 (levelMap (IsStrongBundleMap.base d.Ψ') 1 x₁) =
          IsStrongBundleMap.base d.Ψ' x :=
  d.corollary_3_5_3_of_subset_shrinkGerm hU h0 G' 𝒮 h𝒮
    ((d.basic_shrinkGerm hU h0 G').mono d.quadrant.isQuadrantLike h𝒮) hsurj

/-- **The data of Theorem 3.4.2 (preprint 3.38) on `G″`**: for an sc-smooth sc⁺-germ `t` on `G″` with `t(0) = 0`
(the `W`-part of the push-forward of the sc⁺-section), data `𝒮` of Theorem 3.4.2 (preprint 3.38) with germ `G″`
and `𝒮.s = t`, on which `h` is a basic germ. -/
theorem exists_stabilityData_shrinkGerm {t : d.Pn × d.W 0 → d.W 1}
    (ht : IsScSmoothGerm (E := ScBanach.paramProd d.Pn d.W) (F := d.W.shift)
      (d.shrinkGerm hU h0 G') t) (ht0 : t 0 = 0) :
    ∃ 𝒮 : StabilityData d.Ct d.W, 𝒮.G = d.shrinkGerm hU h0 G' ∧ 𝒮.s = t ∧
      IsBasicGerm d.Ct 𝒮.G d.h d.Bc := by
  obtain ⟨𝒮, h𝒮G, h𝒮s⟩ := StabilityData.exists_of_scPlus ht ht0
  exact ⟨𝒮, h𝒮G, h𝒮s, h𝒮G ▸ d.basic_shrinkGerm hU h0 G'⟩

end ConjugationData

end Polyfold
