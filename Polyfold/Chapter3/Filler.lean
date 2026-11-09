import Polyfold.Chapter2.Tame
import Polyfold.Chapter3.Germ

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1,
Definition 3.1.4 (preprint 3.4) (filling), Lemmas 3.1.19 and 3.1.20 (preprint 3.16 and 3.17) (the local lemmas behind Theorem 3.1.18 (preprint 3.15)), **for the
principal parts of the sections**.

# Fillers and sc⁺-perturbations (local lemmas for Theorem 3.1.18 (preprint 3.15))

## The text, paraphrased

(Definition 3.1.4 (preprint 3.4)) Let `K = R(U ◁ F)` be a tame strong local bundle, `R(u, h) = (r(u), ρ(u)h)`,
`r(0) = 0`, `O = r(U)`.  An sc-smooth section germ `(f, 0)` of `K → O` has a **filling** if there
is an sc-smooth section germ `(g, 0)` of `U ◁ F → U` with (1) `f(x) = g(x)` for `x ∈ O` near `0`;
(2) if `g(y) = ρ(r(y))g(y)` for `y ∈ U` near `0` then `y ∈ O`; (3) the linearization of
`y ↦ [1 − ρ(r(y))]g(y)` at `0`, restricted to `ker Dr(0)`, is a topological linear isomorphism
`ker Dr(0) → ker ρ(0)`.  (Lemma 3.1.19 (preprint 3.16)) An sc⁺-section `s : O → K` extends to the sc⁺-section
`s̃(u) = s(r(u))` of `U ◁ F → U` with `s̃ = s` on `O` and `R(r(u), s̃(u)) = s(r(u))`.
(Lemma 3.1.20 (preprint 3.17)) If `f` has the filler `g` and `s : O → K` is sc⁺, then `f + s` has the filler
`g + s̃`.  (Theorem 3.1.18 (preprint 3.15)) For a tame strong bundle `P : Y → X`, `f ∈ Fred(P)` and `s ∈ Γ⁺(P)`
give `f + s ∈ Fred(P)`.

## What is formalized

* `Polyfold.StrongRetr.r`, `StrongRetr.ρ` (`r(u) = (R(u, 0))₁`, `ρ(u)h = (R(u, h))₂`) and the
  identities `R(u, h) = (r(u), ρ(u)h)`, `r ∘ r = r`, `ρ(r(u)) ∘ ρ(u) = ρ(u)`, `ρ(u) ∘ ρ(u) = ρ(u)`
  on `O`, from Definition 2.6.1 (preprint 2.47); `StrongRetr.ρCLM` (`ρ(u)` as a bounded operator).
* `Polyfold.IsFillerOf` (**Definition 3.1.4 (preprint 3.4), conditions (1)–(3)** for the principal parts
  `f, g : E₀ → F₀`, with the map `y ↦ [1 − ρ(r(y))]g(y)` required sc¹ so that its linearization
  exists; (3) as a continuous linear equivalence `ker Dr(0) ≃L ker ρ(0)` given by that
  linearization).
* `Polyfold.lemma_3_1_19` (**Lemma 3.1.19 (preprint 3.16) (1), (2)**: `s̃ = s ∘ r` agrees with `s` on `O` and
  `ρ(r(u)) s̃(u) = s̃(u)`), `Polyfold.lemma_3_1_20` (**Lemma 3.1.20 (preprint 3.17)**: conditions (1)–(3) pass from
  `(f, g)` to `(f + s, g + s̃)`).

## What the text leaves implicit, and the choices made (the findings)

* **Only the principal parts here.**  The regularity statements — `g` an sc-smooth section of
  `U ◁ F → U`, `s̃` an sc⁺-section (Lemma 3.1.19 (preprint 3.16)), hence `g + s̃` sc-smooth — are not part of
  `IsFillerOf`; they are the composition `s ∘ r` and the sum of sections, i.e. the pairing and
  sum rules of the sc-calculus for maps on sets.  So `lemma_3_1_20` in this file is the version
  "the three filler conditions are stable under adding an sc⁺-section", which is exactly what
  the text's proof checks.  The regularity is supplied where Lemma 3.1.20 (preprint 3.17) is used, in
  `StrongBundleSections.lean`: the sum rule on sets is `Polyfold.IsScSmooth.add`, and
  `Polyfold.StrongBundle.IsScFredholmGermWholeChart.sectionAdd` proves `s̃ = ŝ₁ ∘ r` sc-smooth into `F¹`
  and `g + s̃` sc-smooth on `U` before applying `lemma_3_1_20`; so at the level of Theorem 3.1.18 (preprint 3.15)
  nothing of the text's Lemmas 3.1.19–3.1.20 (preprint 3.16–3.17) is missing.
* **Theorem 3.1.18 (preprint 3.15) and Definition 3.1.16 (preprint 3.14)** (sections of strong bundles over M-polyfolds) are
  formalized in `StrongBundleSections.lean` (`Polyfold.theorem_3_1_18_wholeChart`,
  `Polyfold.StrongBundle.IsScFredholmSectionWholeChart`, with Definitions 3.1.3, 3.1.6, 3.1.11 (preprint 3.3, 3.6, 3.11) as
  `StrongBundle.IsScSmoothSectionGerm`, `IsFilledVersion`, `StrongBundle.IsScFredholmGermWholeChart`).
  Their local content is Lemma 3.1.20 (preprint 3.17) together with the identity `(g + s̃) − (s̃ + t₀) = g − t₀`.
* **Condition (3) presupposes the linearization** of `y ↦ [1 − ρ(r(y))]g(y)` at `0`, i.e. that
  this map is sc¹ (it is, for `g` and `R` sc-smooth, by the chain rule); `IsFillerOf` carries this
  as a field (`isSc1`), and Lemma 3.1.20 (preprint 3.17) transports it by the equality of the two maps on `U`
  (`IsSc1.congr`, and the uniqueness of derivatives on `U₁`, `IsSc1.scDeriv_eqOn`).
* Condition (2) of Lemma 3.1.19 (preprint 3.16), `R(r(u), s̃(u)) = s(r(u))`, is "`R` fixes the points of
  `K = R(U ◁ F)`" (`R ∘ R = R`); the text's computation `R(r(u), s(r(u))) = R(s(r(u))) = s(r(u))`
  uses `s(x) ∈ K` for `x ∈ O` (an sc⁺-section is a section), which is the hypothesis `hsK`.
* `ρ(u)` is linear by Definition 2.6.1 (preprint 2.47) and continuous because `R` is sc⁰ on level `0`; the text
  calls it "a bounded linear operator" without comment.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

/-! ### The base and fibre parts of a strong bundle retraction -/

namespace StrongRetr

/-- The base retraction `r(u) = (R(u, 0))₁` of a strong bundle retraction (Definition 2.6.1 (preprint 2.47)). -/
def r (R : E 0 × F 0 → E 0 × F 0) : E 0 → E 0 := IsStrongBundleMap.base R

/-- The fibre part `ρ(u)h = (R(u, h))₂`. -/
def ρ (R : E 0 × F 0 → E 0 × F 0) (u : E 0) (h : F 0) : F 0 := (R (u, h)).2

variable (hR : IsStrongBundleRetraction U R)
include hR

lemma apply_eq {u : E 0} (hu : u ∈ U) (h : F 0) : R (u, h) = (r R u, ρ R u h) := by
  refine Prod.ext ?_ rfl
  exact hR.fst_independent u hu h 0

lemma r_mem {u : E 0} (hu : u ∈ U) : r R u ∈ U := (hR.mapsTo ⟨hu, mem_univ _⟩).1

/-- `r ∘ r = r` on `U`. -/
lemma r_r {u : E 0} (hu : u ∈ U) : r R (r R u) = r R u := by
  have := congrArg Prod.fst (hR.idem (u, 0) ⟨hu, mem_univ _⟩)
  rw [apply_eq hR hu, apply_eq hR (r_mem hR hu)] at this
  exact this

/-- `ρ(r(u)) ∘ ρ(u) = ρ(u)` on `U`. -/
lemma ρ_r_ρ {u : E 0} (hu : u ∈ U) (h : F 0) : ρ R (r R u) (ρ R u h) = ρ R u h := by
  have := congrArg Prod.snd (hR.idem (u, h) ⟨hu, mem_univ _⟩)
  rw [apply_eq hR hu, apply_eq hR (r_mem hR hu)] at this
  exact this

/-- The retract `O = r(U)`; `r = id` on `O`. -/
lemma r_eq_self {x : E 0} (hx : x ∈ r R '' U) : r R x = x := by
  obtain ⟨u, hu, rfl⟩ := hx
  exact r_r hR hu

lemma mem_U_of_mem_O {x : E 0} (hx : x ∈ r R '' U) : x ∈ U := by
  obtain ⟨u, hu, rfl⟩ := hx
  exact r_mem hR hu

/-- `ρ(x)` is a projection for `x ∈ O`. -/
lemma ρ_ρ {x : E 0} (hx : x ∈ r R '' U) (h : F 0) : ρ R x (ρ R x h) = ρ R x h := by
  have := ρ_r_ρ hR (mem_U_of_mem_O hR hx) h
  rwa [r_eq_self hR hx] at this

/-- The points of `K = R(U ◁ F)` are fixed by `R`. -/
lemma apply_eq_self_of_mem_K {p : E 0 × F 0} (hp : p ∈ R '' (U ×ˢ univ)) : R p = p := by
  obtain ⟨q, hq, rfl⟩ := hp
  exact hR.idem q hq

/-- `ρ(x) h = h` for `(x, h) ∈ K`. -/
lemma ρ_eq_self_of_mem_K {x : E 0} {h : F 0} (hx : x ∈ U) (hp : (x, h) ∈ R '' (U ×ˢ univ)) :
    ρ R x h = h := by
  have := congrArg Prod.snd (apply_eq_self_of_mem_K hR hp)
  rwa [apply_eq hR hx] at this

lemma ρ_isLinear {u : E 0} (hu : u ∈ U) : IsLinearMap ℝ (ρ R u) := hR.fiber_linear u hu

lemma ρ_continuous {u : E 0} (hu : u ∈ U) : Continuous (ρ R u) := by
  have hc : ContinuousOn R (U ×ˢ univ) := hR.isScSmooth_zero.isSc1.isSc0.continuousOn_base
  have : Continuous fun h : F 0 => R (u, h) :=
    hc.comp_continuous (f := fun h : F 0 => ((u, h) : E 0 × F 0)) (by fun_prop)
      fun h => ⟨hu, mem_univ _⟩
  exact continuous_snd.comp this

/-- `ρ(u) : F₀ → F₀` as a bounded linear operator, `u ∈ U`. -/
def ρCLM {u : E 0} (hu : u ∈ U) : F 0 →L[ℝ] F 0 where
  toFun := ρ R u
  map_add' := (ρ_isLinear hR hu).map_add
  map_smul' := (ρ_isLinear hR hu).map_smul
  cont := ρ_continuous hR hu

@[simp] lemma ρCLM_apply {u : E 0} (hu : u ∈ U) (h : F 0) : ρCLM hR hu h = ρ R u h := rfl

end StrongRetr

open StrongRetr

/-! ### Definition 3.1.4 (preprint 3.4): fillers -/

/-- **Definition 3.1.4 (preprint 3.4) (filling), conditions (1)–(3) for the principal parts**: `g : U → F` fills
`f : O → K` (`O = r(U)`, `K = R(U ◁ F)`) if (1) `f = g` on `O` near `0`; (2) a point `y ∈ U` near
`0` with `g(y) = ρ(r(y))g(y)` lies in `O`; (3) the map `y ↦ [1 − ρ(r(y))]g(y)` is sc¹ on `U` and
its linearization at `0`, restricted to `ker Dr(0)`, is a topological linear isomorphism onto
`ker ρ(0)`.  The sc-smoothness of `g` as a section is not included (see the module docstring). -/
structure IsFillerOf (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E 0) ∈ U) (f g : E 0 → F 0) : Prop where
  eq_on : ∀ᶠ x in 𝓝 (0 : E 0), x ∈ r R '' U → f x = g x
  mem_of_fixed : ∀ᶠ y in 𝓝 (0 : E 0), y ∈ U → g y = ρ R (r R y) (g y) → y ∈ r R '' U
  isSc1 : IsSc1 U fun y => g y - ρ R (r R y) (g y)
  linearization : ∃ Φ : LinearMap.ker ((scDeriv U (r R) (0 : E 1) : E 0 →L[ℝ] E 0) : E 0 →ₗ[ℝ] E 0)
      ≃L[ℝ] LinearMap.ker ((ρCLM hR h0 : F 0 →L[ℝ] F 0) : F 0 →ₗ[ℝ] F 0),
    ∀ v : LinearMap.ker ((scDeriv U (r R) (0 : E 1) : E 0 →L[ℝ] E 0) : E 0 →ₗ[ℝ] E 0),
      ((Φ v : LinearMap.ker ((ρCLM hR h0 : F 0 →L[ℝ] F 0) : F 0 →ₗ[ℝ] F 0)) : F 0) =
        scDeriv U (fun y => g y - ρ R (r R y) (g y)) (0 : E 1) (v : E 0)

/-! ### Lemma 3.1.19 (preprint 3.16): the extension `s̃ = s ∘ r` -/

/-- **Lemma 3.1.19 (preprint 3.16) (1), (2)**: for a section `s` of `K → O` (principal part `s : E₀ → F₀` with
`(x, s(x)) ∈ K` for `x ∈ O`), the extension `s̃ = s ∘ r` satisfies `s̃ = s` on `O` and
`ρ(r(u)) s̃(u) = s̃(u)` for `u ∈ U` (the text's `R(r(u), s̃(u)) = s(r(u))`). -/
theorem lemma_3_1_19 (hR : IsStrongBundleRetraction U R) {s : E 0 → F 0}
    (hsK : ∀ x ∈ r R '' U, (x, s x) ∈ R '' (U ×ˢ univ)) :
    (∀ x ∈ r R '' U, s (r R x) = s x) ∧
      ∀ u ∈ U, ρ R (r R u) (s (r R u)) = s (r R u) ∧
        R (r R u, s (r R u)) = (r R u, s (r R u)) := by
  refine ⟨fun x hx => by rw [r_eq_self hR hx], fun u hu => ?_⟩
  have hK := hsK (r R u) ⟨u, hu, rfl⟩
  exact ⟨ρ_eq_self_of_mem_K hR (r_mem hR hu) hK, apply_eq_self_of_mem_K hR hK⟩

/-! ### Lemma 3.1.20 (preprint 3.17): fillers are stable under sc⁺-sections -/

/-- **Lemma 3.1.20 (preprint 3.17)** (conditions (1)–(3)): if `g` fills `f` and `s` is a section of `K → O`
(`(x, s(x)) ∈ K` on `O`), then `g + s ∘ r` fills `f + s`: (1) and (2) from Lemma 3.1.19 (preprint 3.16), and (3)
because `[1 − ρ(r(y))](g(y) + s(r(y))) = [1 − ρ(r(y))]g(y)` on `U`, so the two maps have the same
linearization at `0`. -/
theorem lemma_3_1_20 (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E 0) ∈ U) {f g s : E 0 → F 0} (hfg : IsFillerOf hU hR h0 f g)
    (hsK : ∀ x ∈ r R '' U, (x, s x) ∈ R '' (U ×ˢ univ)) :
    IsFillerOf hU hR h0 (fun x => f x + s x) (fun y => g y + s (r R y)) := by
  obtain ⟨h1, h2⟩ := lemma_3_1_19 hR hsK
  -- the two maps `[1 − ρ(r(y))]g(y)` agree on `U`
  have heq : EqOn (fun y => g y - ρ R (r R y) (g y))
      (fun y => (g y + s (r R y)) - ρ R (r R y) (g y + s (r R y))) U := by
    intro y hy
    simp only
    rw [(ρ_isLinear hR (r_mem hR hy)).map_add, (h2 y hy).1]
    abel
  refine ⟨?_, ?_, hfg.isSc1.congr heq, ?_⟩
  · filter_upwards [hfg.eq_on] with x hx hxO
    rw [hx hxO, h1 x hxO]
  · filter_upwards [hfg.mem_of_fixed] with y hy hyU hfix
    refine hy hyU ?_
    rw [(ρ_isLinear hR (r_mem hR hyU)).map_add, (h2 y hyU).1] at hfix
    exact add_right_cancel hfix
  · obtain ⟨Φ, hΦ⟩ := hfg.linearization
    refine ⟨Φ, fun v => ?_⟩
    rw [hΦ v]
    -- the chosen derivatives agree at `0 ∈ U₁`
    have hsc : IsSc1With U (fun y => (g y + s (r R y)) - ρ R (r R y) (g y + s (r R y)))
        (scDeriv U fun y => g y - ρ R (r R y) (g y)) :=
      hfg.isSc1.isSc1With_scDeriv.congr heq
    have h0' : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
    rw [IsSc1.scDeriv_eqOn hsc (hU.isScDomain.uniqueDiffWithinAt 1) h0']

end Polyfold
