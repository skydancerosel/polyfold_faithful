import Polyfold.Chapter3.BasicClassComposition
import Polyfold.Chapter3.SectionCompactnessG
import Polyfold.Chapter3.Chapter5BridgeG
import Polyfold.Chapter3.GermCalculus
import Polyfold.Chapter3.GermLevels
import Polyfold.Chapter5.AuxNorm

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §5.2
(compactness results) and Appendix 5.4.1: **Definition 5.4, Theorem 5.5** (with its proof in the
appendix), **Theorems 5.6, 5.7, Corollary 5.8** (the compact solution set on every level; the
sc-Fredholm property of `f¹` in a chart, in part) and **Remark 5.12**
*(book 2017: Definition 5.5, Theorems 5.1–5.3, Corollary 5.1, Remark 5.3; see
`BookConcordance.md`)*.

# Compactness of the solution set of an sc-Fredholm section

## The text, paraphrased

(Definition 5.4) An sc-smooth section `f` of `P : Y → X` has a *compact solution set* if
`f⁻¹(0)` is compact in `X₀`; it is *weakly proper* if moreover for every auxiliary norm `N` there
is an open `U ⊇ f⁻¹(0)` such that `{f = s}` is compact for every sc⁺-section `s` with support in
`U` and `N(s(y)) ≤ 1`; it is *proper* if for every `N` there is an open `U ⊇ f⁻¹(0)` with
`cl_{X₀}{x ∈ U | N(f(x)) ≤ 1}` compact (`N(f(x)) = ∞` off `Y_{0,1}`).  "Obviously proper implies
weakly proper, which implies compactness."  (Theorem 5.5) For an sc-Fredholm section over a tame
`X`, a compact solution set implies proper, so the three notions agree.  The proof (appendix): at a
zero, "without loss of generality" `f = h + t` in local coordinates, `h` a basic germ, `t` an
sc⁺-germ with `t(0) = 0`; it suffices to find `U ∋ 0` with `cl{(a, w) ∈ U | |(h + t)(a, w)|₁ ≤ c}`
compact; with `P ∘ h(a, w) = w − B(a, w)`, `z = w − B(a, w)` has `|z|₁ ≤ 3c` and `|z|₀ < τ'/2`, so
`w = δ(a, z)` for the parametrized fixed point `δ` of `w ↦ B(a, w) + z`; by the compactness of
`E₁ → E₀`, `(a_n, z_n)` has a convergent subsequence in `E₀`, hence so has `w_n = δ(a_n, z_n)`.
(Theorem 5.6) For an sc-Fredholm `f` and a solution `x` there are nested open `x ∈ U(i + 1) ⊆ U(i)`
with `cl_{X₀}({y ∈ U(i) | f(y) = 0})` a compact subset of `X_i`.  (Theorem 5.7) If `S = f⁻¹(0)` is
compact in `X₀`, it is compact in `X_∞`: `S ⊆ X_∞` (regularizing), `X_∞` is metrizable, and a
sequence in `S` converging in `X₀` converges on every level "by Theorem 5.6".  (Corollary 5.8)
`f^i` is an sc-Fredholm section of `P^i : Y^i → X^i` with compact solution set ("it is a priori
clear that `f^i` is sc-Fredholm").  (Remark 5.12) A section `s` in the completion of the allowable
sc⁺-sections `Γ^{+,1}_U` (support in `U`, `N(s) ≤ 1`, for the distance `sup N(s − s')`) still has a
compact solution set of `f + s = 0`, if `U` is adapted to `N` as in the properness result.

## What is formalized

* `Polyfold.theorem_5_6` (**Theorem 5.6**): `theorem_3_12` at a zero of an sc-Fredholm section
  (a zero is a smooth point, and `(f, x)` is an sc-Fredholm germ there).
* `Polyfold.theorem_5_7` (**Theorem 5.7**): `S ⊆ X_∞`, and the set of points of `X_∞`
  (`MPolyfold.SmoothLevel`, with the topology induced by `X_∞ → ∏ X_m`) lying in `S` is compact;
  `MPolyfold.tendsto_smoothLevel_iff` (convergence in `X_∞` is convergence on every level).
* `Polyfold.isCompact_solutionSet_level` (**Corollary 5.8, the compact solution set**, for every
  `i`): the zeros of `f` in `X_i` form a compact subset of `X_i` (the underlying space of the
  M-polyfold `X^i`).
* **Corollary 5.8 in a chart** (`i = 1`): `Polyfold.IsBasicGerm.shift` (the level shift `f¹` of a
  basic germ is a basic germ, on the shifted germ `ScNbhdGerm.shiftParam`, with
  `IsSc0ContractionGerm.shift`), `Polyfold.IsConjugateToBasicGerm.shift` (if `k : U → F` is
  conjugated to a basic germ `h` by `Ψ`, then `k¹ : U¹ → F¹` is conjugated to `h¹` by the index
  raise `Ψ¹ = strongShift Ψ`, `IsStrongBundleIso.shift` of `BasicClassComposition.lean`), its germ
  form `Polyfold.IsConjugateToBasicGerm.shift_germ` (`k` an sc⁰-germ only), and
  `Polyfold.corollary_5_8_chart` (the compact solution set in `X₁`, and at every smooth point the
  data of Definition 3.11 in the text's germ reading — filling germ `g`, sc⁺-germ `s` — with
  `(g − s)¹` conjugated to a basic germ and `s¹` an sc⁺-germ on the shifted germ).
* **Definition 5.4**: (1) is `IsCompact (solutionSet P f)`; `StrongBundle.AuxLe` (`N(y) ≤ r`,
  with `N = ∞` off `Y_{0,1}`), (2) `StrongBundle.IsWeaklyProper`, (3) `StrongBundle.IsProper`;
  `StrongBundle.IsProper.isWeaklyProper` ("proper implies weakly proper", for a continuous `f`),
  `StrongBundle.IsWeaklyProper.isCompact_solutionSet`.
* **Theorem 5.5**: `Polyfold.theorem_5_5` (compact solution set ⇒ proper) and
  `Polyfold.theorem_5_5_iff` (proper ⟺ weakly proper ⟺ compact solution set for sc-Fredholm
  sections), from
  - `IsSc0ContractionGerm.exists_isCompact_bdd`, `IsBasicGerm.exists_isCompact_bdd` (**the local
    form**, the appendix's (82)–(90)): an open `O ∋ 0`, independent of the bound `c`, such that the
    points of `U₀ ∩ O` where the basic germ has level-`1` norm `≤ c` lie in a compact set, the image
    of `{a ∈ C̃, |a| ≤ ρ} × K_c` under `(a, z) ↦ (a, δ(a, z))`;
  - `IsStrongBundleMap.exists_fiber_bound_one` (**uniform `(0, 1)` fibre bounds** of a strong
    bundle map near a point, from the continuity of `Ψ[1]` and fibre linearity);
  - `exists_nbhd_isCompact_closure_bdd` (**the local step on the M-polyfold**: for an sc-Fredholm
    germ `(f, x₀)`, in its chart `Φ`, an open `V ∋ x₀` such that for every `C` the closure of
    `{x ∈ V | Φ(f(x))₂ ∈ F₁, |Φ(f(x))₂|₁ ≤ C}` is compact);
  - Lemma 5.2's lower bound `|Φ[1](w)₂|₁ ≤ A·N(w)` in the chart of the germ
    (`StrongBundle.IsAuxNorm.exists_norm_liftOne_le`, `AuxNorm.lean`) and a finite subcover.
* **Remark 5.12**: `Polyfold.remark_5_12` (a section `s` vanishing off `U` with `N(s) ≤ 1` has its
  solution set of `f + s = 0` inside `{x ∈ U | N(f(x)) ≤ 1}`, so with compact closure);
  `StrongBundle.IsAuxNorm.auxLe_of_sectionAdd` (`f(x) + s(x) = 0` gives `N(f(x)) = N(s(x))`).
  The remark as stated (the solution set is compact for every `s` in the completion of
  `Γ^{+,1}_U`, including its closedness) is `Polyfold.remark_5_12_completion` in
  `SolutionSetClosed.lean`.

## What the text leaves implicit, and the choices made (the findings)

* **Tameness is not used** (Theorems 5.5–5.7; the appendix restates Theorem 5.5 without it).
* **Theorem 5.7 uses Corollary 3.13, not Theorem 5.6.**  The step "`x_k → x` in `X₀` implies
  `x_k → x` on every level" is Corollary 3.13 at an arbitrary limit point
  (`corollary_3_13_section`), which needs the germ property at the limit; the limit of zeros is a
  zero (`StrongBundle.IsScSmoothSection.isZeroAt_of_tendsto`) and a smooth point (regularizing).
  Theorem 5.6 alone gives the compactness of `cl({f = 0} ∩ U(i))` in `X_i`, not the convergence
  of a given sequence.  The topology of `X_∞` is not defined in the text; here it is the initial
  topology of the inclusions `X_∞ → X_m` (`MPolyfold.smoothLevel_topology_eq`), metrizable by
  `MPolyfold.metrizableSpace_smoothLevel` (Theorem 2.16).
* **Theorem 5.5: the uniform `(0, 1)` fibre bound of `Ψ`** is used silently when `f` is replaced
  by `h + t` "without loss of generality": the bound `N(f(x)) ≤ 1` becomes `|g(u)|₁ ≤ A` in the
  chart (Lemma 5.2), then `|g(u) − s(u)|₁ ≤ A + |s(0)|₁ + 1` near `0`, then
  `|h(ψ(u))|₁ = |Ψ[1](u, g(u) − s(u))₂|₁ ≤ M(A + |s(0)|₁ + 1)`.  Subtracting the sc⁺-part before
  the conjugation makes the text's `t`, (83) and (85) unnecessary, and the neighbourhood
  independent of the bound.
* **Theorem 5.5: back from local coordinates.**  The set `{(a, w) ∈ U | |(h + t)(a, w)|₁ ≤ c}`
  lives in the domain `U` of the filled version, which is larger than the retract `O ≅ V ⊆ X`; the
  closure of the image of `{x | N(f(x)) ≤ 1}` must stay in `O` to be pulled back to `X`.  It does,
  because `O` is the fixed point set of the retraction `r` in `U`; the compact set on the side of
  the basic germ is cut down to a closed ball inside `U'` first.  The text's "it suffices to find
  in local coordinates" and its last sentence ("since the solution set is compact, the proof is
  complete": a finite cover of `f⁻¹(0)` by such neighbourhoods) leave both steps implicit.
* **Appendix typos** (lines 7769–7891): `z' = h(a, w)` for `(h + t)(a, w)`; `ℝⁿ ⊕ Y₁` for
  `ℝᴺ ⊕ W₁`; "in view of (2) and (3)" for (84) and (86); `Σ` with `a ∈ ℝⁿ` for `a ∈ C̃` (`B` is only
  defined on `C̃ ⊕ W`, and `C̃` must be closed for the compactness, as in Theorem 3.40); (86) has a
  dangling clause; `B(τ')` is a ball "in `Y₀`" for `W₀`.
* **Definition 5.4.**  The convention `N(f(x)) = ∞` off `Y_{0,1}` is `AuxLe`; the support of `s`
  is the closure of `{s ≠ 0}`.  "Proper implies weakly proper" needs `{f = s}` closed (`f` and `s`
  continuous, `Y` Hausdorff) and the observation that a solution of `f = s` outside `U` would be a
  zero of `f`.
* **Corollary 5.8: "it is a priori clear that `f^i` is sc-Fredholm".**  The text never defines
  `Y^i → X^i` (only `Y[i]` for `i = 0, 1`).  The shifted strong bundle `P¹ : Y¹ → X¹`
  (`Y¹ = Y_{1,1}`, charts `Φ¹`) and the full corollary for `i = 1, 2` are in
  `Chapter5/StrongBundleShift.lean` and `Chapter5/Corollary58.lean` (`Polyfold.corollary_5_8`,
  `corollary_5_8_two`; Findings, Chapter 5, items 140–146).  This file gives the chart step: the
  conjugation to a basic germ shifts (`IsConjugateToBasicGerm.shift_germ`, with
  `IsBasicGerm.shift`), and so does the sc⁺-germ (`IsSckGerm.shift`); the filler condition (3) on
  level `1` does not follow from condition (3) on level `0` alone (an sc-operator can be bijective
  on level `0` and not onto on level `1`) and is proved in `Corollary58.lean` for sc-Fredholm germs
  (`IsFillingGerm.germ_shift`).
* **Remark 5.12.**  The completion of `Γ^{+,1}_U` is not constructed: what the remark uses of a
  limit `s` is that it vanishes outside `U` and has `N(s) ≤ 1` (both pass to uniform limits); then
  `{f + s = 0} ⊆ {x ∈ U | N(f(x)) ≤ 1}` (outside `U`, `f + s = f`; on `{f + s = 0}`,
  `N(f) = N(s)`), so the solution set has compact closure.  It is compact when it is closed, a
  point the text does not discuss; for the uniform `N`-limits of allowable sections the closedness
  is proved in `SolutionSetClosed.lean`
  (`StrongBundle.IsInAllowableCompletion.isClosed_solutionSet_sectionAdd`, a chart argument with
  Lemma 5.2), which gives the remark as stated (`remark_5_12_completion`).  The remark's
  "adapted ... in the sense that `N(f(x)) ≤ 1` for `x ∈ U`, has the properties stipulated in the
  properness result" is garbled; it is read as "`cl{x ∈ U | N(f(x)) ≤ 1}` is compact".
-/

open Set Filter Topology Function Metric

noncomputable section

namespace Polyfold

universe u v

section Bundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-! ### Theorem 5.6: local compactness -/

/-- **Theorem 5.6 (local compactness)**: let `f` be an sc-Fredholm section of the strong bundle
`P : Y → X` and `x` a solution of `f(x) = 0`.  Then there are open neighbourhoods
`x ∈ U(i + 1) ⊆ U(i)` of `x` in `X = X₀` such that for every `i` the closure in `X₀` of
`{y ∈ U(i) | f(y) = 0}` is a compact subset of `X_i`: it is the image of a compact subset of
`X_i` (with its level topology) under the inclusion `X_i → X`.  This is `theorem_3_12` at the
zero `x`, which is a smooth point (`f` is regularizing) where `(f, x)` is an sc-Fredholm germ. -/
theorem theorem_5_6 (hf : B.IsScFredholmSection f) {x : X} (hx : IsZeroAt P f x) :
    ∃ U : ℕ → Set X, (∀ i, IsOpen (U i)) ∧ (∀ i, x ∈ U i) ∧ (∀ i, U (i + 1) ⊆ U i) ∧
      ∀ i, ∃ K : Set (PX.Level i), IsCompact K ∧
        PX.levelVal i '' K = closure {y ∈ U i | IsZeroAt P f y} :=
  theorem_3_12 hf.isScSmooth.1 (hf.germ x (hf.mem_smoothSet_of_isZeroAt hx)) hx

/-! ### Theorem 5.7: the solution set is compact in `X_∞` -/

/-- The point of `X_∞` given by a smooth point of `X`. -/
def _root_.Polyfold.MPolyfold.smoothMk (PX : MPolyfold X) (x : X) (hx : x ∈ PX.smoothSet) :
    PX.SmoothLevel :=
  (⟨x, hx⟩ : PX.smoothSet)

/-- The inclusion `X_∞ → X`. -/
def _root_.Polyfold.MPolyfold.smoothVal (PX : MPolyfold X) (x : PX.SmoothLevel) : X :=
  (x : PX.smoothSet).1

lemma _root_.Polyfold.MPolyfold.smoothVal_mem (PX : MPolyfold X) (x : PX.SmoothLevel) :
    PX.smoothVal x ∈ PX.smoothSet :=
  (x : PX.smoothSet).2

@[simp] lemma _root_.Polyfold.MPolyfold.smoothVal_smoothMk (PX : MPolyfold X) (x : X)
    (hx : x ∈ PX.smoothSet) : PX.smoothVal (PX.smoothMk x hx) = x := rfl

lemma _root_.Polyfold.MPolyfold.levelVal_smoothIncl (PX : MPolyfold X) (x : PX.SmoothLevel)
    (m : ℕ) : PX.levelVal m (PX.smoothIncl x m) = PX.smoothVal x := rfl

/-- The inclusion `X_∞ → X_m` is continuous. -/
lemma _root_.Polyfold.MPolyfold.continuous_smoothIncl (PX : MPolyfold X) (m : ℕ) :
    Continuous fun x : PX.SmoothLevel => PX.smoothIncl x m := by
  change Continuous ((fun g : ∀ k, PX.Level k => g m) ∘ PX.smoothIncl)
  exact (continuous_apply m).comp continuous_induced_dom

/-- The inclusion `X_∞ → X` is continuous. -/
lemma _root_.Polyfold.MPolyfold.continuous_smoothVal (PX : MPolyfold X) :
    Continuous PX.smoothVal :=
  (PX.continuous_levelVal 0).comp (PX.continuous_smoothIncl 0)

/-- **Convergence in `X_∞` is convergence on every level** (the topology of `X_∞` is induced by
`X_∞ → ∏_m X_m`). -/
lemma _root_.Polyfold.MPolyfold.tendsto_smoothLevel_iff (PX : MPolyfold X) {u : ℕ → PX.SmoothLevel}
    {x : PX.SmoothLevel} :
    Tendsto u atTop (𝓝 x) ↔ ∀ m, Tendsto (fun n => PX.smoothIncl (u n) m) atTop
      (𝓝 (PX.smoothIncl x m)) := by
  rw [(Topology.IsInducing.induced PX.smoothIncl).tendsto_nhds_iff, tendsto_pi_nhds]
  rfl

/-- **Theorem 5.7**: let `f` be an sc-Fredholm section of the strong bundle `P : Y → X` whose
solution set `S = {x ∈ X | f(x) = 0}` is compact in `X = X₀`.  Then `S ⊆ X_∞`, and `S` is a compact
subset of `X_∞`: the set of points of `X_∞` lying in `S` is compact for the topology of `X_∞`
(the initial topology of the inclusions `X_∞ → X_m`).  The text assumes `X` tame; tameness is not
used.  The convergence on every level is Corollary 3.13 (`corollary_3_13_section`), which the text
cites as Theorem 5.6. -/
theorem theorem_5_7 (hf : B.IsScFredholmSection f) (hS : IsCompact (solutionSet P f)) :
    solutionSet P f ⊆ PX.smoothSet ∧
      IsCompact {x : PX.SmoothLevel | PX.smoothVal x ∈ solutionSet P f} := by
  have hreg : solutionSet P f ⊆ PX.smoothSet := fun x hx => hf.mem_smoothSet_of_isZeroAt hx
  refine ⟨hreg, ?_⟩
  have := PX.metrizableSpace_smoothLevel
  have := PX.metrizableSpace
  refine IsSeqCompact.isCompact fun u hu => ?_
  -- a subsequence converging in `X₀`
  obtain ⟨x₀, hx₀S, φ, hφ, hlim⟩ := hS.tendsto_subseq (x := fun n => PX.smoothVal (u n)) hu
  have hx₀s : x₀ ∈ PX.smoothSet := hreg hx₀S
  refine ⟨PX.smoothMk x₀ hx₀s, hx₀S, φ, hφ, ?_⟩
  -- convergence on every level (Corollary 3.13)
  refine PX.tendsto_smoothLevel_iff.2 fun m => ?_
  obtain ⟨-, -, y₀, hy₀, y, hy, hylim⟩ := corollary_3_13_section hf
    (x := fun n => PX.smoothVal (u (φ n))) (fun n => hu (φ n)) hlim m
  have e₀ : y₀ = PX.smoothIncl (PX.smoothMk x₀ hx₀s) m := MPolyfold.level_ext (by
    rw [hy₀, PX.levelVal_smoothIncl, PX.smoothVal_smoothMk])
  rw [← e₀]
  refine hylim.congr' ?_
  filter_upwards [hy] with n hn
  exact MPolyfold.level_ext (by rw [hn, PX.levelVal_smoothIncl]; rfl)

/-- **Corollary 5.8, the compact solution set** (for every `i`): if the solution set of the
sc-Fredholm section `f` is compact in `X₀`, then the solutions in `X_i` form a compact subset of
`X_i` (the underlying space of the M-polyfold `X^i`, with the level topology): the image of the
compact subset of `X_∞` of Theorem 5.7 under the continuous inclusion `X_∞ → X_i`. -/
theorem isCompact_solutionSet_level (hf : B.IsScFredholmSection f)
    (hS : IsCompact (solutionSet P f)) (i : ℕ) :
    IsCompact {x : PX.Level i | PX.levelVal i x ∈ solutionSet P f} := by
  obtain ⟨hreg, hK⟩ := theorem_5_7 hf hS
  convert hK.image (PX.continuous_smoothIncl i) using 1
  ext x
  constructor
  · intro hx
    refine ⟨PX.smoothMk (PX.levelVal i x) (hreg hx), hx, MPolyfold.level_ext ?_⟩
    rw [PX.levelVal_smoothIncl, PX.smoothVal_smoothMk]
  · rintro ⟨y, hy, rfl⟩
    exact hy

end Bundle

/-! ### Corollary 5.8 in a chart: the level shift of the conjugation to a basic germ -/

section Shift

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] {W : ScBanach}
  {Ct : Set P}

/-- The shifted germ `O(C̃ ⊕ W, 0)¹` as a germ in `P ⊕ W¹` around `0 ∈ C̃ ⊕ W¹` (its level-`m` set
is `U_{m+1}`). -/
def ScNbhdGerm.shiftParam (G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)) :
    ScNbhdGerm (ScBanach.paramProd P W.shift) (Ct ×ˢ univ) where
  U m := G.U (m + 1)
  nested m x hx := G.nested (m + 1) x hx
  zero_mem m := G.zero_mem (m + 1)
  relOpen m := by
    obtain ⟨O, hO, h⟩ := G.relOpen (m + 1)
    refine ⟨O, hO, ?_⟩
    rw [h, ScBanach.paramProd_lvlSet, ScBanach.paramProd_lvlSet]

@[simp] lemma ScNbhdGerm.shiftParam_U (G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ))
    (m : ℕ) : G.shiftParam.U m = G.U (m + 1) := rfl

variable {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)} {B : P × W 0 → W 0}

/-- **The level shift of an sc⁰-contraction germ** (Definition 3.28 on level `1`): `B¹ = B_1` on the
shifted germ is an sc⁰-contraction germ (the estimates of level `m + 1` are those of level `m` of
`B¹`). -/
theorem IsSc0ContractionGerm.shift (h : IsSc0ContractionGerm Ct G B) :
    IsSc0ContractionGerm (W := W.shift) Ct G.shiftParam (levelB B 1) where
  isSc0 := h.isSc0.shift.of_U_eq fun _ => rfl
  B_zero := h.levelB_zero_eq 1
  contraction ε hε m := by
    obtain ⟨r, hr, hr'⟩ := h.contraction ε hε (m + 1)
    refine ⟨r, hr, fun a ha har w w' hw hw' => ?_⟩
    obtain ⟨hU, hc⟩ := hr' a ha har w w' hw hw'
    refine ⟨hU, ?_⟩
    have hU' : ((a, w') : P × W (m + 1)) ∈ G.U (m + 1) := (hr' a ha har w' w hw' hw).1
    have e1 := h.isSc0.levelMap_shift (x := ((a, w) : (ScBanach.paramProd P W) (m + 1))) hU
    have e2 := h.isSc0.levelMap_shift (x := ((a, w') : (ScBanach.paramProd P W) (m + 1))) hU'
    change ‖levelMap (E := (ScBanach.paramProd P W).shift) (F := W.shift) (levelB B 1) m (a, w) -
      levelMap (E := (ScBanach.paramProd P W).shift) (F := W.shift) (levelB B 1) m (a, w')‖ ≤ _
    rw [e1, e2]
    exact hc

/-- **The level shift of a basic germ is a basic germ** (used silently in Corollary 5.8, "it is a
priori clear that `f^i` is sc-Fredholm"): if `f : O(C̃ ⊕ W, 0) → Q ⊕ W` is a basic germ with
`P ∘ f(a, w) = w − B(a, w)`, then `f¹ = f_1 : O(C̃ ⊕ W¹, 0) → Q ⊕ W¹` is a basic germ with
`P ∘ f¹(a, w) = w − B¹(a, w)`.  `C̃` quadrant-like (a partial quadrant) is needed for the
sc-smoothness of the shifted germ (Proposition 1.17 for germs). -/
theorem IsBasicGerm.shift {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [FiniteDimensional ℝ Q] {f : P × W 0 → Q × W 0} (hf : IsBasicGerm Ct G f B)
    (hCt : IsQuadrantLike (ScBanach.const P) Ct) :
    IsBasicGerm (W := W.shift) Ct G.shiftParam
      (levelMap (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) f 1) (levelB B 1) where
  isScSmooth k := (IsSckGerm.shift (hCt.paramProd W) (hf.isScSmooth k)).of_U_eq
    (hCt.paramProd W).shift fun _ => rfl
  contraction := hf.contraction.shift
  f_zero := by
    have h0 : (0 : (ScBanach.paramProd P W) 1) ∈ G.U 1 := G.zero_mem 1
    apply (ScBanach.paramProd Q W).toBase_injective 1
    rw [(hf.isScSmooth 0).toBase_levelMap h0, map_zero, map_zero]
    exact hf.f_zero
  snd_eq x hx := by
    have hx' : x ∈ G.U 1 := hx
    apply W.toBase_injective 1
    have h1 := (hf.isScSmooth 0).toBase_levelMap hx'
    have h2 := hf.contraction.isSc0.toBase_levelMap hx'
    have h3 := hf.snd_eq _ (G.toBase_mem hx')
    have h4 := congrArg Prod.snd h1
    rw [ScBanach.paramProd_toBase] at h4
    dsimp only at h4
    change W.toBase 1
      (levelMap (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) f 1 x).2 = _
    rw [h4, h3, map_sub]
    change _ = W.toBase 1 x.2 - W.toBase 1 (levelMap (E := ScBanach.paramProd P W) (F := W) B 1 x)
    rw [h2, ScBanach.paramProd_toBase]

end Shift

section ShiftBundle

variable {E F : ScBanach}

/-- **The level shift of the conjugation to a basic germ** (Definition 3.11 on level `1`): if the
principal part `k : U → F` (sc⁰ on `U`, `0 ∈ U`) is conjugated to the basic germ `h` by the strong
bundle isomorphism `Ψ`, then `k¹ : U¹ → F¹` is conjugated to the basic germ `h¹` by `Ψ¹`. -/
theorem IsConjugateToBasicGerm.shift {U C : Set (E 0)} (hU : IsRelOpenInQuadrant E C U)
    (h0U : (0 : E 0) ∈ U) {k : E 0 → F 0} (hk : IsSc0 E F U k) (h : IsConjugateToBasicGerm U k) :
    IsConjugateToBasicGerm (E := E.shift) (F := F.shift) (E.lvlSet U 1) (levelMap k 1) := by
  obtain ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, U', Ψ, Ψ', G, hb, Bc, hCt, hU', hΨ, hψ0, hG, hh,
    hev⟩ := h
  have hΨ1 := hΨ.shift hU hU'
  have hU'C : U' ⊆ Ct ×ˢ univ := by
    obtain ⟨Uo, -, rfl⟩ := hU'.relOpen; exact inter_subset_right
  set Ψ₁ := strongShift Ψ with hΨ₁
  set ψ₁ := IsStrongBundleMap.base (E := E.shift) (F := F.shift)
    (E' := (ScBanach.paramProd Pn W).shift) (F' := (ScBanach.paramProd Q W).shift) Ψ₁ with hψ₁
  have h0U1 : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0U
  have hψ₁0 : ψ₁ 0 = 0 := by
    apply (ScBanach.paramProd Pn W).toBase_injective 1
    rw [hΨ.toFun.toBase_base_strongShift (u := 0) (by rw [map_zero]; exact h0U), map_zero, map_zero,
      hψ0]
  refine ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W.shift, Ct, (ScBanach.paramProd Pn W).lvlSet U' 1, Ψ₁,
    strongShift Ψ',
    G.shiftParam, levelMap (E := ScBanach.paramProd Pn W) (F := ScBanach.paramProd Q W) hb 1,
    levelB Bc 1, hCt, ?_, hΨ1, hψ₁0, ?_, hh.shift hCt.isQuadrantLike, ?_⟩
  · have := hU'.shift
    rwa [ScBanach.paramProd_lvlSet] at this
  · intro x hx
    exact hG (G.toBase_mem (show x ∈ G.U 1 from hx))
  · -- the conjugation identity on level `1`
    -- (i) the level-`0` identity at `ι₁ u`
    have h1 : ∀ᶠ u in 𝓝 (0 : E 1), E.toBase 1 u ∈ U →
        (Ψ (E.toBase 1 u, k (E.toBase 1 u))).2 = hb (IsStrongBundleMap.base Ψ (E.toBase 1 u)) := by
      have hc : Tendsto (E.toBase 1) (𝓝 0) (𝓝 0) := by
        have := (E.toBase 1).continuous.tendsto 0
        rwa [map_zero] at this
      exact hc.eventually hev
    -- (ii) `ψ₁ u ∈ G.U 1` near `0`
    have h2 : ∀ᶠ u in 𝓝 (0 : E 1), u ∈ E.lvlSet U 1 → ψ₁ u ∈ G.U 1 := by
      have hψc : ContinuousOn ψ₁ (E.lvlSet U 1) :=
        (hΨ1.toFun.base_isScSmooth hU.shift).isSc1.isSc0.continuousOn_base
      obtain ⟨Og, hOg, hGeq⟩ := G.relOpen 1
      have hmem : Og ∈ 𝓝 (ψ₁ 0) := by
        rw [hψ₁0]
        have : (0 : (ScBanach.paramProd Pn W) 1) ∈ G.U 1 := G.zero_mem 1
        rw [hGeq] at this
        exact hOg.mem_nhds this.1
      have : ψ₁ ⁻¹' Og ∈ 𝓝[E.lvlSet U 1] 0 := hψc 0 h0U1 hmem
      rw [mem_nhdsWithin_iff_eventually] at this
      refine this.mono fun u hu huU => ?_
      rw [hGeq]
      refine ⟨hu huU, ?_⟩
      have := (hΨ1.toFun.mapsTo (show (u, (0 : F 1)) ∈ E.lvlSet U 1 ×ˢ univ from
        ⟨huU, mem_univ _⟩)).1
      exact hU'C this
    filter_upwards [h1, h2] with u hu1 hu2 huU
    have huU' : E.toBase 1 u ∈ U := huU
    have hGu := hu2 huU
    apply (ScBanach.paramProd Q W).toBase_injective 1
    rw [hΨ.toFun.toBase_strongShift_snd huU', hk.toBase_levelMap huU,
      hu1 huU', (hh.isScSmooth 0).toBase_levelMap hGu, hΨ.toFun.toBase_base_strongShift huU']

/-- **The level shift of the conjugation to a basic germ, germ form** (Definition 3.11 on level
`1`, germ reading): as `IsConjugateToBasicGerm.shift`, with `k` only an sc⁰-germ on a germ `Gk`
(`0 ∈ U`): `k¹ : U¹ → F¹` is conjugated to the basic germ `h¹` by `Ψ¹`.  Used by
`corollary_5_8_chart` for `k = g − s` with `g` the filling germ and `s` the sc⁺-germ. -/
theorem IsConjugateToBasicGerm.shift_germ {U C : Set (E 0)} (hU : IsRelOpenInQuadrant E C U)
    (h0U : (0 : E 0) ∈ U) {k : E 0 → F 0} {Gk : ScNbhdGerm E C} (hk : IsSc0Germ Gk k)
    (h : IsConjugateToBasicGerm U k) :
    IsConjugateToBasicGerm (E := E.shift) (F := F.shift) (E.lvlSet U 1) (levelMap k 1) := by
  obtain ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, U', Ψ, Ψ', G, hb, Bc, hCt, hU', hΨ, hψ0, hG, hh,
    hev⟩ := h
  have hΨ1 := hΨ.shift hU hU'
  have hU'C : U' ⊆ Ct ×ˢ univ := by
    obtain ⟨Uo, -, rfl⟩ := hU'.relOpen; exact inter_subset_right
  set Ψ₁ := strongShift Ψ with hΨ₁
  set ψ₁ := IsStrongBundleMap.base (E := E.shift) (F := F.shift)
    (E' := (ScBanach.paramProd Pn W).shift) (F' := (ScBanach.paramProd Q W).shift) Ψ₁ with hψ₁
  have h0U1 : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0U
  have hψ₁0 : ψ₁ 0 = 0 := by
    apply (ScBanach.paramProd Pn W).toBase_injective 1
    rw [hΨ.toFun.toBase_base_strongShift (u := 0) (by rw [map_zero]; exact h0U), map_zero, map_zero,
      hψ0]
  refine ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W.shift, Ct, (ScBanach.paramProd Pn W).lvlSet U' 1, Ψ₁,
    strongShift Ψ',
    G.shiftParam, levelMap (E := ScBanach.paramProd Pn W) (F := ScBanach.paramProd Q W) hb 1,
    levelB Bc 1, hCt, ?_, hΨ1, hψ₁0, ?_, hh.shift hCt.isQuadrantLike, ?_⟩
  · have := hU'.shift
    rwa [ScBanach.paramProd_lvlSet] at this
  · intro x hx
    exact hG (G.toBase_mem (show x ∈ G.U 1 from hx))
  · -- the conjugation identity on level `1`
    -- (i) the level-`0` identity at `ι₁ u`
    have h1 : ∀ᶠ u in 𝓝 (0 : E 1), E.toBase 1 u ∈ U →
        (Ψ (E.toBase 1 u, k (E.toBase 1 u))).2 = hb (IsStrongBundleMap.base Ψ (E.toBase 1 u)) := by
      have hc : Tendsto (E.toBase 1) (𝓝 0) (𝓝 0) := by
        have := (E.toBase 1).continuous.tendsto 0
        rwa [map_zero] at this
      exact hc.eventually hev
    -- (ii) `ψ₁ u ∈ G.U 1` near `0`
    have h2 : ∀ᶠ u in 𝓝 (0 : E 1), u ∈ E.lvlSet U 1 → ψ₁ u ∈ G.U 1 := by
      have hψc : ContinuousOn ψ₁ (E.lvlSet U 1) :=
        (hΨ1.toFun.base_isScSmooth hU.shift).isSc1.isSc0.continuousOn_base
      obtain ⟨Og, hOg, hGeq⟩ := G.relOpen 1
      have hmem : Og ∈ 𝓝 (ψ₁ 0) := by
        rw [hψ₁0]
        have : (0 : (ScBanach.paramProd Pn W) 1) ∈ G.U 1 := G.zero_mem 1
        rw [hGeq] at this
        exact hOg.mem_nhds this.1
      have : ψ₁ ⁻¹' Og ∈ 𝓝[E.lvlSet U 1] 0 := hψc 0 h0U1 hmem
      rw [mem_nhdsWithin_iff_eventually] at this
      refine this.mono fun u hu huU => ?_
      rw [hGeq]
      refine ⟨hu huU, ?_⟩
      have := (hΨ1.toFun.mapsTo (show (u, (0 : F 1)) ∈ E.lvlSet U 1 ×ˢ univ from
        ⟨huU, mem_univ _⟩)).1
      exact hU'C this
    -- (iii) `u ∈ Gk.U 1` near `0`
    have h3 : ∀ᶠ u in 𝓝 (0 : E 1), u ∈ E.lvlSet U 1 → u ∈ Gk.U 1 := by
      obtain ⟨Ok, hOk, hGkeq⟩ := Gk.relOpen 1
      have h0Ok : (0 : E 1) ∈ Ok := by
        have := Gk.zero_mem 1; rw [hGkeq] at this; exact this.1
      filter_upwards [hOk.mem_nhds h0Ok] with u hu huU
      rw [hGkeq]
      obtain ⟨Uo, -, hUeq⟩ := hU.relOpen
      have huU' : E.toBase 1 u ∈ U := huU
      rw [hUeq] at huU'
      exact ⟨hu, huU'.2⟩
    filter_upwards [h1, h2, h3] with u hu1 hu2 hu3 huU
    have huU' : E.toBase 1 u ∈ U := huU
    have hGu := hu2 huU
    apply (ScBanach.paramProd Q W).toBase_injective 1
    rw [hΨ.toFun.toBase_strongShift_snd huU', hk.toBase_levelMap (hu3 huU),
      hu1 huU', (hh.isScSmooth 0).toBase_levelMap hGu, hΨ.toFun.toBase_base_strongShift huU']

/-- **Corollary 5.8 for `i = 1`, in a chart** (what is formalized of "`f¹` is sc-Fredholm with
compact solution set"): if the sc-Fredholm section `f` has a compact solution set, then (a) the
solutions in `X₁` form a compact subset of `X₁`; (b) at every smooth point `x`, in the chart `Φ` of
the sc-Fredholm germ `(f, x)` with filling germ `g` and sc⁺-germ `s` (germ reading of Definition
3.11), the level-`1` germ `(g − s)¹ : U¹ → F¹` is conjugated to a basic germ by the index raise of
the conjugating strong bundle isomorphism (`IsConjugateToBasicGerm.shift_germ`), and
`s¹ : U¹ → (F¹)¹` is an sc⁺-germ (on the shifted germ `G_s¹`).  The filling conditions of
Definition 3.4 for `g¹` and the shifted strong bundle `Y¹ → X¹` itself are not formalized (see the
module docstring). -/
theorem corollary_5_8_chart {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {PX : MPolyfold X} {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    {B : StrongBundle PX P} {f : X → Y} (hf : B.IsScFredholmSection f)
    (hS : IsCompact (solutionSet P f)) :
    IsCompact {x : PX.Level 1 | PX.levelVal 1 x ∈ solutionSet P f} ∧
      ∀ x ∈ PX.smoothSet, ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x ∈ c.φ.source)
        (_ : c.φ x = 0) (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0)
        (s : c.φ.model.E 0 → c.F 1),
        IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g ∧
        IsScPlusGerm c.φ.model.C c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
        IsScPlusGerm (E := c.φ.model.E.shift) (F := c.F.shift)
          (c.φ.model.E.lvlSet c.φ.model.C 1) (c.φ.model.E.lvlSet c.U 1)
          (levelMap (E := c.φ.model.E) (F := c.F.shift) s 1) ∧
        IsConjugateToBasicGerm (E := c.φ.model.E.shift) (F := c.F.shift)
          (c.φ.model.E.lvlSet c.U 1) (levelMap (fun u => g u - c.F.toBase 1 (s u)) 1) := by
  refine ⟨isCompact_solutionSet_level hf hS 1, fun x hx => ?_⟩
  obtain ⟨-, c, hc, hxV, h0, h0U, g, s, hfill, hsP, hs0, hconj⟩ := hf.germ x hx
  obtain ⟨Gs, hGsU, hs⟩ := id hsP
  obtain ⟨Gg, hGgU, hg, -⟩ := hfill.germ
  have hQ := c.isQuadrantLike
  -- `g − s` is an sc⁰-germ on `G_g ∩ G_s`
  have hk : IsSc0Germ (Gg.inter Gs) (fun u => g u - c.F.toBase 1 (s u)) :=
    (hg.sub_inter hQ (hs.operator_comp hQ c.F.shiftIncl)) 0
  refine ⟨c, hc, hxV, h0, h0U, g, s, hfill, hsP, hs0, ⟨Gs.shift, ?_, fun k => (hs k).shift hQ⟩,
    hconj.shift_germ c.relOpen h0U hk⟩
  intro u hu
  exact hGsU (Gs.toBase_mem hu)

end ShiftBundle

/-! ### Theorem 5.5, the local form: a basic germ with a bounded level-`1` value -/

section LocalBound

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] {W : ScBanach}
  {Ct : Set P}

namespace IsSc0ContractionGerm

variable {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)} {B : P × W 0 → W 0}
  (h : IsSc0ContractionGerm Ct G B)
include h

/-- The level-`0` fixed point `δ(a, z)` is the only solution of `w = B(a, w) − z` in the ball. -/
lemma eq_delta_zero {p : P × W 0} (hp : p ∈ h.Sigma 0) {w : W 0} (hw : w ∈ h.cBall 0)
    (hfix : B (p.1, w) - p.2 = w) : w = h.delta 0 p :=
  (h.exists_delta 0).choose_spec.2.2 p hp w hw (by simpa [gmap] using hfix)

/-- **The local form of Theorem 5.5** (the appendix's (82)–(90)): there is an open neighbourhood
`O` of `0` in `E₀`, independent of `c`, such that for every `c` the points `(a, w) ∈ U₀ ∩ O` with
`w − B(a, w) ∈ W₁` and `|w − B(a, w)|₁ ≤ c` lie in a compact subset of `E₀`: the image of the
compact set `{(a, z) | a ∈ C̃, |a|₀ ≤ ρ, z ∈ K_c, |z|₀ ≤ r/8}` (`K_c ⊇ ι(B̄₁(c))` compact, by the
compactness of `W₁ → W₀`) under the continuous `(a, z) ↦ (a, δ(a, z))`, `δ` the parametrized
fixed point of `w ↦ B(a, w) − z`.  Only the level-`0` contraction is used, and `C̃` closed. -/
theorem exists_isCompact_bdd (hCt : IsClosed Ct) :
    ∃ O : Set (P × W 0), IsOpen O ∧ (0 : P × W 0) ∈ O ∧ ∀ c : ℝ, ∃ K : Set (P × W 0),
      IsCompact K ∧ {x ∈ G.U 0 ∩ O | ∃ z : W 1, W.toBase 1 z = x.2 - B x ∧ ‖z‖ ≤ c} ⊆ K := by
  have hr := h.crad_pos 0
  have hρ0 := h.cprad_pos 0
  -- `B(a, w) − w` is small near `0`
  have hc : ContinuousWithinAt (fun x : P × W 0 => B x - x.2) (G.U 0) 0 :=
    (h.isSc0.continuousOn_base 0 (G.zero_mem 0)).sub continuous_snd.continuousWithinAt
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨ρ₁, hρ₁, hρ₁'⟩ := hc (h.crad 0 / 8) (by positivity)
  set ρ := min ρ₁ (min (h.cprad 0 / 2) (h.crad 0 / 2)) with hρdef
  have hρpos : 0 < ρ := lt_min hρ₁ (lt_min (by positivity) (by positivity))
  have hρ₁le : ρ ≤ ρ₁ := min_le_left _ _
  have hρc : ρ ≤ h.cprad 0 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hρr : ρ ≤ h.crad 0 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hB00 : B 0 - (0 : P × W 0).2 = 0 := by
    rw [show (0 : P × W 0) = (0, 0) from rfl, h.B_zero, sub_zero]
  refine ⟨Metric.ball 0 ρ, Metric.isOpen_ball, Metric.mem_ball_self hρpos, fun c => ?_⟩
  obtain ⟨Kc, hKc, hKc'⟩ := (W.toBase_succ_isCompactOperator 0).image_closedBall_subset_compact
    (f := (W.toBase (0 + 1) : W (0 + 1) →ₗ[ℝ] W 0)) c
  set L : Set (P × W 0) :=
    (Ct ∩ Metric.closedBall 0 ρ) ×ˢ (Kc ∩ Metric.closedBall 0 (h.crad 0 / 8)) with hLdef
  have hL : IsCompact L :=
    ((isCompact_closedBall (0 : P) ρ).inter_left hCt).prod (hKc.inter_right isClosed_closedBall)
  have hLS : L ⊆ h.Sigma 0 := fun p hp => by
    refine ⟨hp.1.1, ?_, ?_⟩
    · have := hp.1.2
      rw [Metric.mem_closedBall, dist_zero_right] at this
      linarith
    · have := hp.2.2
      rwa [Metric.mem_closedBall, dist_zero_right] at this
  refine ⟨(fun p => (p.1, h.delta 0 p)) '' L, hL.image_of_continuousOn ?_, ?_⟩
  · exact (continuousOn_fst.prodMk (h.delta_continuousOn 0)).mono hLS
  rintro x ⟨⟨hxU, hxO⟩, z, hz, hzc⟩
  rw [Metric.mem_ball, dist_zero_right] at hxO
  have hxC : x.1 ∈ Ct := by
    have := G.U_subset 0 hxU
    rw [ScBanach.lvlSet_zero] at this
    exact this.1
  have hx1 : ‖x.1‖ < ρ := (norm_fst_le x).trans_lt hxO
  have hx2 : ‖x.2‖ < ρ := (norm_snd_le x).trans_lt hxO
  have hBx : ‖B x - x.2‖ < h.crad 0 / 8 := by
    have := hρ₁' hxU (by rw [dist_zero_right]; exact hxO.trans_le hρ₁le)
    rwa [dist_eq_norm, hB00, sub_zero] at this
  set p : P × W 0 := (x.1, B x - x.2) with hpdef
  have hpL : p ∈ L := by
    refine ⟨⟨hxC, by rw [Metric.mem_closedBall, dist_zero_right]; exact hx1.le⟩, ?_,
      by rw [Metric.mem_closedBall, dist_zero_right]; exact hBx.le⟩
    refine hKc' ⟨-z, by rw [Metric.mem_closedBall, dist_zero_right, norm_neg]; exact hzc, ?_⟩
    change W.toBase 1 (-z) = B x - x.2
    rw [map_neg, hz, neg_sub]
  have hw : x.2 ∈ h.cBall 0 := by
    rw [cBall, Metric.mem_closedBall, dist_zero_right]; linarith
  have hfix : B (p.1, x.2) - p.2 = x.2 := by
    simp only [hpdef, Prod.mk.eta]; abel
  refine ⟨p, hpL, ?_⟩
  change (p.1, h.delta 0 p) = x
  rw [← h.eq_delta_zero (hLS hpL) hw hfix]

end IsSc0ContractionGerm

/-- **The local form of Theorem 5.5 for a basic germ** `f` (Definition 3.7): there is an open
neighbourhood `O` of `0` such that for every `c` the points `x ∈ U₀ ∩ O` with `f(x) ∈ ℝᴺ ⊕ W₁`,
`|f(x)|₁ ≤ c`, lie in a compact subset of `E₀` (the `W`-component of `f(x)` is `w − B(a, w)`). -/
theorem IsBasicGerm.exists_isCompact_bdd {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [FiniteDimensional ℝ Q] {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)}
    {f : P × W 0 → Q × W 0} {B : P × W 0 → W 0} (hf : IsBasicGerm Ct G f B) (hCt : IsClosed Ct) :
    ∃ O : Set (P × W 0), IsOpen O ∧ (0 : P × W 0) ∈ O ∧ ∀ c : ℝ, ∃ K : Set (P × W 0),
      IsCompact K ∧ {x ∈ G.U 0 ∩ O | ∃ z : (ScBanach.paramProd Q W) 1,
        (ScBanach.paramProd Q W).toBase 1 z = f x ∧ ‖z‖ ≤ c} ⊆ K := by
  obtain ⟨O, hO, h0O, hK⟩ := hf.contraction.exists_isCompact_bdd hCt
  refine ⟨O, hO, h0O, fun c => ?_⟩
  obtain ⟨K, hKc, hKsub⟩ := hK c
  refine ⟨K, hKc, fun x hx => hKsub ⟨hx.1, ?_⟩⟩
  obtain ⟨z, hz, hzc⟩ := hx.2
  refine ⟨z.2, ?_, (norm_snd_le z).trans hzc⟩
  have := congrArg Prod.snd hz
  rw [ScBanach.paramProd_toBase] at this
  rw [← hf.snd_eq x hx.1.1]
  exact this

end LocalBound

/-! ### Uniform `(0, 1)` fibre bounds of strong bundle maps -/

section FiberBound

variable {E F E' F' : ScBanach} {U : Set (E 0)} {U' : Set (E' 0)} {Ψ : E 0 × F 0 → E' 0 × F' 0}

/-- `(Ψ[1](u, 0))₂ = 0`. -/
lemma IsStrongBundleMap.shiftFiber_snd_zero (hΨ : IsStrongBundleMap U U' Ψ) {u : E 0} (hu : u ∈ U) :
    (shiftFiber Ψ (u, 0)).2 = 0 := by
  apply F'.toBase_injective 1
  rw [hΨ.toBase_shiftFiber_snd (p := (u, 0)) hu, map_zero, map_zero]
  exact hΨ.snd_zero hu

/-- The fibre maps of `Ψ[1]` are linear: `(Ψ[1](u, a • k))₂ = a • (Ψ[1](u, k))₂`. -/
lemma IsStrongBundleMap.shiftFiber_snd_smul (hΨ : IsStrongBundleMap U U' Ψ) {u : E 0} (hu : u ∈ U)
    (a : ℝ) (k : F 1) : (shiftFiber Ψ (u, a • k)).2 = a • (shiftFiber Ψ (u, k)).2 := by
  apply F'.toBase_injective 1
  rw [hΨ.toBase_shiftFiber_snd (p := (u, a • k)) hu, map_smul, map_smul,
    hΨ.toBase_shiftFiber_snd (p := (u, k)) hu]
  exact (hΨ.fiber_linear u hu).map_smul a _

/-- **Uniform `(0, 1)` fibre bounds of a strong bundle map near a point** (used silently in the
proof of Theorem 5.5): there are `δ > 0` and `M ≥ 0` with `|(Ψ[1](u, k))₂|₁ ≤ M |k|₁` for
`u ∈ U`, `|u − u₀|₀ < δ`, `k ∈ F₁` — from the continuity of `Ψ[1]` at `(u₀, 0)` (Definition 2.47)
and the linearity of the fibre maps. -/
theorem IsStrongBundleMap.exists_fiber_bound_one (hΨ : IsStrongBundleMap U U' Ψ) {u₀ : E 0}
    (hu₀ : u₀ ∈ U) :
    ∃ δ > 0, ∃ M : ℝ, 0 ≤ M ∧ ∀ u ∈ U, dist u u₀ < δ → ∀ k : F 1,
      ‖(shiftFiber Ψ (u, k)).2‖ ≤ M * ‖k‖ := by
  have hc : ContinuousOn (shiftFiber Ψ) (U ×ˢ univ) :=
    hΨ.isScSmooth_one.isSc1.isSc0.continuousOn_base
  have hc0 := hc (u₀, 0) ⟨hu₀, mem_univ _⟩
  rw [Metric.continuousWithinAt_iff] at hc0
  obtain ⟨δ, hδ, hδ'⟩ := hc0 1 one_pos
  refine ⟨δ, hδ, 2 / δ, by positivity, fun u hu hud k => ?_⟩
  rcases eq_or_ne k 0 with rfl | hk
  · rw [hΨ.shiftFiber_snd_zero hu, norm_zero, norm_zero, mul_zero]
  have hkpos : 0 < ‖k‖ := norm_pos_iff.2 hk
  set a : ℝ := δ / 2 / ‖k‖ with ha
  have hapos : 0 < a := by positivity
  have hak : ‖a • k‖ = δ / 2 := by
    rw [norm_smul, Real.norm_of_nonneg hapos.le, ha]; field_simp
  have h1 := hδ' (x := ((u, a • k) : (E.prod F.shift) 0)) ⟨hu, mem_univ _⟩ (by
    rw [Prod.dist_eq, dist_zero_right, hak]
    exact max_lt hud (by linarith))
  have h2 : ‖(shiftFiber Ψ (u, a • k)).2‖ < 1 := by
    have := (norm_snd_le (shiftFiber Ψ (u, a • k) - shiftFiber Ψ (u₀, 0))).trans_lt
      (by rwa [dist_eq_norm] at h1)
    rwa [Prod.snd_sub, hΨ.shiftFiber_snd_zero hu₀, sub_zero] at this
  rw [hΨ.shiftFiber_snd_smul hu, norm_smul, Real.norm_of_nonneg hapos.le] at h2
  have h3 : ‖(shiftFiber Ψ (u, k)).2‖ < 1 / a := by
    rw [lt_div_iff₀ hapos]; linarith
  calc ‖(shiftFiber Ψ (u, k)).2‖ ≤ 1 / a := h3.le
    _ = 2 / δ * ‖k‖ := by rw [ha]; field_simp

end FiberBound

/-! ### The local step of Theorem 5.5 on the M-polyfold -/

section Bundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **The local step of Theorem 5.5** (the appendix's proof, at one point): let `(f, x₀)` be an
sc-Fredholm germ (Definition 3.11).  In the strong bundle chart `Φ` of the germ there is an open
neighbourhood `V` of `x₀`, independent of `C`, such that for every `C` the closure in `X` of
`{x ∈ V | Φ(f(x))₂ ∈ F₁, |Φ(f(x))₂|₁ ≤ C}` is compact.  The proof: `f̂ = g` on `O` near `0`
(the filler), `|g − t₀|₁ ≤ C + |t₀(0)|₁ + 1` near `0` (`t₀` the sc⁺-section, continuous into
`F₁`), `|h(ψ(u))|₁ = |Ψ[1](u, g(u) − t₀(u))₂|₁ ≤ M(C + |t₀(0)|₁ + 1)` (uniform `(0, 1)` fibre bound
of `Ψ`), the local form `IsBasicGerm.exists_isCompact_bdd` on the side of the basic germ, and the
transport back through `ψ⁻¹` and `φ⁻¹`; the closure of the image in `U` lies in `O` because `O` is
the fixed point set of the retraction `r`.  `x₀` need not be a zero of `f`. -/
theorem exists_nbhd_isCompact_closure_bdd {x₀ : X}
    (hg : B.IsScFredholmGerm f x₀) :
    ∃ c : StrongBundleChart PX P, B.IsChart c ∧ x₀ ∈ c.φ.source ∧ ∃ V : Set X, IsOpen V ∧
      x₀ ∈ V ∧ V ⊆ c.φ.source ∧ ∀ C : ℝ,
        IsCompact (closure {x ∈ V | ∃ k : c.F 1, c.F.toBase 1 k = (c (f x)).2 ∧ ‖k‖ ≤ C}) := by
  obtain ⟨-, c, hc, hxV, h0, h0U, g, t₀, hfill, ⟨Gs, -, ht₀⟩, -, hconj⟩ := hg
  obtain ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, U', Ψ, Ψ', G, h, Bc, hCt, hU', hΨ, hψ0, hG, hh,
    hev⟩ := hconj
  set ψ := IsStrongBundleMap.base Ψ with hψdef
  set ψ' := IsStrongBundleMap.base Ψ' with hψ'def
  have hψψ' : ∀ u ∈ c.U, ψ' (ψ u) = u := fun u hu => hΨ.base_base hu
  set fb := c.principal f with hfbdef
  have hU := c.relOpen
  have hOU : c.φ.model.O ⊆ c.U := fun z hz => by
    rw [← c.r_image] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    exact StrongRetr.r_mem c.isRetraction hv
  have hC'closed : IsClosed (Ct ×ˢ (univ : Set (W 0))) := hU'.isPartialQuadrant.isClosed
  have hU'C : U' ⊆ Ct ×ˢ univ := by
    obtain ⟨Uo, -, rfl⟩ := hU'.relOpen; exact inter_subset_right
  have h0U' : (0 : (ScBanach.paramProd Pn W) 0) ∈ U' := hψ0 ▸ hΨ.toFun.base_mem h0U
  have hψ'cont : ContinuousOn ψ' U' :=
    (hΨ.invFun.base_isScSmooth hU').isSc1.isSc0.continuousOn_base
  have hψcont : ContinuousOn ψ c.U := (hΨ.toFun.base_isScSmooth hU).isSc1.isSc0.continuousOn_base
  -- `N₁`: the filler identity (1) and the conjugation identity
  have hN₀ : ∀ᶠ u in 𝓝 (0 : c.φ.model.E 0), (u ∈ c.φ.model.O → fb u = g u) ∧
      (u ∈ c.U → (Ψ (u, g u - c.F.toBase 1 (t₀ u))).2 = h (ψ u)) := by
    have h1 := hfill.eq_on
    rw [c.r_image] at h1
    exact h1.and hev
  obtain ⟨N₁, hN₁sub, hN₁open, h0N₁⟩ := _root_.mem_nhds_iff.1 hN₀
  -- `t₀` is bounded in `F₁` near `0`
  have ht₀c : ContinuousOn t₀ (Gs.U 0) := (ht₀ 0).continuousOn_base
  have ht₀c0 := ht₀c 0 (Gs.zero_mem 0)
  obtain ⟨Os, hOs, hGsEq⟩ := Gs.relOpen 0
  have h0Os : (0 : c.φ.model.E 0) ∈ Os := by
    have := Gs.zero_mem 0; rw [hGsEq] at this; exact this.1
  rw [Metric.continuousWithinAt_iff] at ht₀c0
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := ht₀c0 1 one_pos
  -- the uniform `(0, 1)` fibre bound of `Ψ` near `0`
  obtain ⟨δ₃, hδ₃, M, hM0, hM⟩ := hΨ.toFun.exists_fiber_bound_one h0U
  set N : Set (c.φ.model.E 0) := N₁ ∩ (Metric.ball 0 δ₂ ∩ Os) ∩ Metric.ball 0 δ₃ with hNdef
  have hNopen : IsOpen N := (hN₁open.inter (Metric.isOpen_ball.inter hOs)).inter Metric.isOpen_ball
  have h0N : (0 : c.φ.model.E 0) ∈ N :=
    ⟨⟨h0N₁, Metric.mem_ball_self hδ₂, h0Os⟩, Metric.mem_ball_self hδ₃⟩
  -- the side of the basic germ
  obtain ⟨O', hO'open, h0O', hK⟩ := hh.exists_isCompact_bdd hCt.isClosed
  obtain ⟨Og, hOg, hGeq⟩ := G.relOpen 0
  have hGmem : ∀ u', u' ∈ G.U 0 ↔ u' ∈ Og ∧ u' ∈ Ct ×ˢ univ := fun u' => by
    rw [hGeq]; rfl
  -- a closed ball (intersected with `C'`) inside `U'`
  obtain ⟨Uo, hUo, hU'eq⟩ := hU'.relOpen
  obtain ⟨ρ', hρ', hball⟩ := Metric.isOpen_iff.1 hUo 0 (hU'eq ▸ h0U' |>.1)
  set r₀ := ρ' / 2 with hr₀
  have hr₀pos : 0 < r₀ := by positivity
  have hcl_mem : ∀ u' ∈ Metric.closedBall (0 : (ScBanach.paramProd Pn W) 0) r₀ ∩ Ct ×ˢ univ,
      u' ∈ U' := fun u' hu' =>
    hU'eq ▸ ⟨hball ((Metric.closedBall_subset_ball (by linarith)) hu'.1), hu'.2⟩
  -- the neighbourhood `V`
  have hψφ : ContinuousOn (ψ ∘ c.φ) c.φ.source :=
    hψcont.comp c.φ.continuousOn_toFun fun x hx => hOU (c.φ.mapsTo_model x hx)
  set V : Set X := (c.φ.source ∩ c.φ ⁻¹' N) ∩
    (c.φ.source ∩ (ψ ∘ c.φ) ⁻¹' (O' ∩ Og ∩ Metric.ball 0 r₀)) with hVdef
  have hVopen : IsOpen V :=
    (c.φ.continuousOn_toFun.isOpen_inter_preimage c.φ.isOpen_source hNopen).inter
      (hψφ.isOpen_inter_preimage c.φ.isOpen_source ((hO'open.inter hOg).inter Metric.isOpen_ball))
  have hx₀V : x₀ ∈ V := by
    refine ⟨⟨hxV, by rw [mem_preimage, h0]; exact h0N⟩, hxV, ?_⟩
    rw [mem_preimage, Function.comp_apply, h0, hψ0]
    exact ⟨⟨h0O', ((hGmem 0).1 (G.zero_mem 0)).1⟩, Metric.mem_ball_self hr₀pos⟩
  refine ⟨c, hc, hxV, V, hVopen, hx₀V, fun x hx => hx.1.1, fun C => ?_⟩
  set Z : Set X := {x ∈ V | ∃ k : c.F 1, c.F.toBase 1 k = (c (f x)).2 ∧ ‖k‖ ≤ C} with hZdef
  set c' : ℝ := M * (C + (‖t₀ 0‖ + 1)) with hc'def
  obtain ⟨K, hKc, hKsub⟩ := hK c'
  -- (1) `ψ(φ(Z))` lies in `K ∩ B̄(r₀) ∩ C'`
  set A := (ψ ∘ c.φ) '' Z with hAdef
  have hA : A ⊆ K ∩ (Metric.closedBall 0 r₀ ∩ Ct ×ˢ univ) := by
    rintro _ ⟨x, ⟨⟨⟨hxV', hxN⟩, -, hxψ⟩, k, hk, hkC⟩, rfl⟩
    set u := c.φ x with hudef
    have huO : u ∈ c.φ.model.O := c.φ.mapsTo_model x hxV'
    have huU : u ∈ c.U := hOU huO
    have hψU' : ψ u ∈ U' := hΨ.toFun.base_mem huU
    have hfbu : fb u = (c (f x)).2 := by
      simp only [hfbdef, StrongBundleChart.principal, hudef, c.φ.symm_apply_apply hxV']
    have hgu : g u = c.F.toBase 1 k := by rw [← (hN₁sub hxN.1.1).1 huO, hfbu, hk]
    -- the bound of `t₀(u)`
    have ht : ‖t₀ u‖ ≤ ‖t₀ 0‖ + 1 := by
      have huGs : u ∈ Gs.U 0 := by
        obtain ⟨Uo, -, hUeq⟩ := c.relOpen.relOpen
        rw [hGsEq]; exact ⟨hxN.1.2.2, (hUeq ▸ huU).2⟩
      have := hδ₂' huGs (by rw [dist_zero_right]; exact (mem_ball_zero_iff.1 hxN.1.2.1))
      have h2 := norm_le_norm_add_norm_sub' (t₀ u) (t₀ 0)
      rw [dist_eq_norm] at this
      linarith
    -- `h(ψ(u))` on level `1`
    have hhu : h (ψ u) = (ScBanach.paramProd Q W).toBase 1 (shiftFiber Ψ (u, k - t₀ u)).2 := by
      rw [hΨ.toFun.toBase_shiftFiber_snd (p := (u, k - t₀ u)) huU, ← (hN₁sub hxN.1.1).2 huU, hgu,
        map_sub]
    have hbd : ‖(shiftFiber Ψ (u, k - t₀ u)).2‖ ≤ c' := by
      refine (hM u huU (by rw [dist_zero_right]; exact mem_ball_zero_iff.1 hxN.2) _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hM0
      have := norm_sub_le k (t₀ u)
      linarith
    refine ⟨hKsub ⟨⟨(hGmem _).2 ⟨hxψ.1.2, hU'C hψU'⟩, hxψ.1.1⟩, _, hhu.symm, hbd⟩, ?_, hU'C hψU'⟩
    exact Metric.ball_subset_closedBall hxψ.2
  have hclA : closure A ⊆ K ∩ (Metric.closedBall 0 r₀ ∩ Ct ×ˢ univ) :=
    closure_minimal hA (hKc.isClosed.inter (Metric.isClosed_closedBall.inter hC'closed))
  have hclAc : IsCompact (closure A) :=
    hKc.of_isClosed_subset isClosed_closure (hclA.trans inter_subset_left)
  have hclAU' : closure A ⊆ U' := fun u' hu' => hcl_mem u' (hclA hu').2
  -- (2) `φ(Z) ⊆ T = ψ'(closure A)`, compact, inside `U`
  set T := ψ' '' closure A with hTdef
  have hTc : IsCompact T := hclAc.image_of_continuousOn (hψ'cont.mono hclAU')
  have hφZT : c.φ '' Z ⊆ T := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨ψ (c.φ x), subset_closure ⟨x, hx, rfl⟩, hψψ' _ ?_⟩
    exact hOU (c.φ.mapsTo_model x hx.1.1.1)
  have hTU : T ⊆ c.U := by
    rintro _ ⟨u', hu', rfl⟩
    exact hΨ.invFun.base_mem (hclAU' hu')
  -- (3) `closure (φ(Z)) ⊆ O`: `O` is the fixed point set of `r` in `U`
  have hφZO : c.φ '' Z ⊆ c.φ.model.O := by
    rintro _ ⟨x, hx, rfl⟩
    exact c.φ.mapsTo_model x hx.1.1.1
  set T' := closure (c.φ '' Z) with hT'def
  have hT'T : T' ⊆ T := closure_minimal hφZT hTc.isClosed
  have hT'O : T' ⊆ c.φ.model.O := by
    intro u hu
    have huU : u ∈ c.U := hTU (hT'T hu)
    have hrc : ContinuousOn (fun v => StrongRetr.r c.R v - v) c.U :=
      (StrongRetr.r_isScSmooth hU c.isRetraction).isSc1.isSc0.continuousOn_base.sub
        continuousOn_id
    have hr : StrongRetr.r c.R u - u = 0 := by
      refine eq_of_mem_closure_of_continuousOn hrc (A := c.φ '' Z) (fun v hv => hOU (hφZO hv))
        (fun v hv => ?_) huU hu
      have hvO := hφZO hv
      rw [← c.r_image] at hvO
      rw [StrongRetr.r_eq_self c.isRetraction hvO, sub_self]
    rw [← c.r_image]
    exact ⟨u, huU, (sub_eq_zero.1 hr)⟩
  -- (4) `closure Z ⊆ φ⁻¹(T')`, compact
  have hT'c : IsCompact T' := hTc.of_isClosed_subset isClosed_closure hT'T
  have hK2 : IsCompact (c.φ.symm '' T') :=
    hT'c.image_of_continuousOn (c.φ.continuousOn_invFun.mono hT'O)
  refine hK2.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK2.isClosed)
  intro x hx
  exact ⟨c.φ x, subset_closure ⟨x, hx, rfl⟩, c.φ.symm_apply_apply hx.1.1.1⟩

end Bundle

/-! ### Definition 5.4, Theorem 5.5, Remark 5.12 -/

section Def54

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

namespace StrongBundle

variable (B) in
/-- `N(y) ≤ r` with the convention of Definition 5.4 (3): `N(y) = ∞` when `y` does not have
biregularity `(0, 1)`.  So `B.AuxLe N y r` says `y ∈ Y_{0,1}` and `N(y) ≤ r`. -/
def AuxLe (N : B.One → ℝ) (y : Y) (r : ℝ) : Prop := ∃ hy : y ∈ B.oneSet, N (B.oneMk y hy) ≤ r

variable (B) in
/-- **Definition 5.4 (2)**: the section `f` is **weakly proper**: it has a compact solution set,
and for every auxiliary norm `N` there is an open neighbourhood `U` of `f⁻¹(0)` such that for
every sc⁺-section `s` with support in `U` (the closure of `{s ≠ 0}`) and `N(s(y)) ≤ 1` for all
`y`, the set `{x ∈ X | f(x) = s(x)}` is compact. -/
def IsWeaklyProper (f : X → Y) : Prop :=
  IsCompact (solutionSet P f) ∧ ∀ N : B.One → ℝ, B.IsAuxNorm N → ∃ U : Set X, IsOpen U ∧
    solutionSet P f ⊆ U ∧ ∀ s : X → Y, B.IsScPlusSection s → closure {x | ¬ IsZeroAt P s x} ⊆ U →
      (∀ y, B.AuxLe N (s y) 1) → IsCompact {x | f x = s x}

variable (B) in
/-- **Definition 5.4 (3)**: the section `f` is **proper**: it has a compact solution set, and for
every auxiliary norm `N` there is an open neighbourhood `U` of `f⁻¹(0)` such that the closure in
`X₀` of `{x ∈ U | N(f(x)) ≤ 1}` is compact (with `N(f(x)) = ∞` if `f(x) ∉ Y_{0,1}`). -/
def IsProper (f : X → Y) : Prop :=
  IsCompact (solutionSet P f) ∧ ∀ N : B.One → ℝ, B.IsAuxNorm N → ∃ U : Set X, IsOpen U ∧
    solutionSet P f ⊆ U ∧ IsCompact (closure {x ∈ U | B.AuxLe N (f x) 1})

/-- `AuxLe` only depends on the point of `Y`. -/
lemma AuxLe.congr {N : B.One → ℝ} {y y' : Y} {r : ℝ} (h : B.AuxLe N y r) (hyy' : y = y') :
    B.AuxLe N y' r := hyy' ▸ h

/-- If `f(x) + s(x) = 0` in the fibre, then `N(f(x)) = N(s(x))`: `f(x) = −s(x)` and `N` is a norm
on the fibre `(Y_{0,1})_x`. -/
lemma IsAuxNorm.auxLe_of_sectionAdd {N : B.One → ℝ} (hN : B.IsAuxNorm N) {s : X → Y}
    (hf : IsSection P f) (hs : IsSection P s) {x : X} (hx : IsZeroAt P (sectionAdd P f s) x)
    {r : ℝ} (h : B.AuxLe N (s x) r) : B.AuxLe N (f x) r := by
  obtain ⟨hs1, hle⟩ := h
  set fx : P ⁻¹' {x} := ⟨f x, hf x⟩ with hfx
  set sx : P ⁻¹' {x} := ⟨s x, hs x⟩ with hsx
  have hsum : fx + sx = 0 := by
    apply Subtype.ext
    have := hx
    rw [IsZeroAt, sectionAdd_apply hf hs] at this
    exact this
  have hneg : fx = -sx := eq_neg_of_add_eq_zero_left hsum
  set v : B.oneFiber x := ⟨sx, hs1⟩ with hv
  have hfv : f x = (((-v : B.oneFiber x) : P ⁻¹' {x}) : Y) := by
    change ((fx : P ⁻¹' {x}) : Y) = (((-v : B.oneFiber x) : P ⁻¹' {x}) : Y)
    rw [hneg]; rfl
  refine ⟨hfv ▸ (-v).2, ?_⟩
  have e1 : B.oneMk (f x) (hfv ▸ (-v).2) = B.toOne (-v) := B.oneVal_injective (by
    rw [oneVal_oneMk, oneVal_toOne, hfv])
  rw [e1, ← neg_one_smul ℝ v, hN.smul, abs_neg, abs_one, one_mul]
  exact hle

end StrongBundle

open StrongBundle

/-- **Theorem 5.5**: an sc-Fredholm section `f` of a strong bundle `P : Y → X` over an M-polyfold
with a compact solution set is proper: for every auxiliary norm `N` there is an open neighbourhood
`U` of `f⁻¹(0)` such that `cl_{X₀}({x ∈ U | N(f(x)) ≤ 1})` is compact.  (The text assumes `X` tame
in §5.2, not in the appendix; tameness is not used.)  Proof (appendix 5.4.1): at each zero `x`,
in the chart `Φ` of the sc-Fredholm germ `(f, x)`, `exists_nbhd_isCompact_closure_bdd` gives an
open `V ∋ x` such that the points of `V` where `Φ(f(·))₂ ∈ F₁` with `|·|₁ ≤ A` have compact closure
for every `A`; Lemma 5.2 (`StrongBundle.IsAuxNorm.exists_norm_liftOne_le`: `|Φ[1](w)₂|₁ ≤ A·N(w)`
near `x`) turns `N(f(y)) ≤ 1` into `|Φ(f(y))₂|₁ ≤ A`; finitely many such `V` cover the compact
`f⁻¹(0)`. -/
theorem theorem_5_5 (hf : B.IsScFredholmSection f) (hS : IsCompact (solutionSet P f)) :
    B.IsProper f := by
  refine ⟨hS, fun N hN => ?_⟩
  have hsec := hf.isScSmooth.1
  -- the local step at each zero
  have hloc : ∀ x ∈ solutionSet P f, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      IsCompact (closure {y ∈ V | B.AuxLe N (f y) 1}) := by
    intro x hx
    obtain ⟨c, hc, hxc, V, hVo, hxV, hVc, hK⟩ :=
      exists_nbhd_isCompact_closure_bdd (hf.germ x (hf.mem_smoothSet_of_isZeroAt hx))
    obtain ⟨V₁, hV₁o, hxV₁, -, A, hA, hV₁⟩ := hN.exists_norm_liftOne_le hc hxc
    refine ⟨V ∩ V₁, hVo.inter hV₁o, ⟨hxV, hxV₁⟩,
      (hK A).of_isClosed_subset isClosed_closure (closure_mono ?_)⟩
    rintro y ⟨⟨hyV, hyV₁⟩, hy1, hyN⟩
    refine ⟨hyV, (c.liftOne (f y)).2, ?_, ?_⟩
    · exact toBase_liftOne_snd hc (c.mem_source_of_proj (by rw [hsec y]; exact hVc hyV)) hy1
    · have := hV₁ (B.oneMk (f y) hy1) (by rw [oneVal_oneMk, hsec y]; exact hyV₁)
      rw [oneVal_oneMk] at this
      calc ‖(c.liftOne (f y)).2‖ ≤ A * N (B.oneMk (f y) hy1) := this
        _ ≤ A * 1 := mul_le_mul_of_nonneg_left hyN hA.le
        _ = A := mul_one A
  choose! V hVo hxV hVK using hloc
  -- finitely many of the `V(x)` cover the compact solution set
  obtain ⟨t, htS, hcover⟩ := hS.elim_nhds_subcover V fun x hx => (hVo x hx).mem_nhds (hxV x hx)
  refine ⟨⋃ x ∈ t, V x, isOpen_biUnion fun x hx => hVo x (htS x hx), hcover, ?_⟩
  have hK : IsCompact (⋃ x ∈ t, closure {y ∈ V x | B.AuxLe N (f y) 1}) :=
    t.isCompact_biUnion fun x hx => hVK x (htS x hx)
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  rintro y ⟨hyU, hyN⟩
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 hyU
  exact mem_iUnion₂.2 ⟨x, hx, subset_closure ⟨hyx, hyN⟩⟩

/-- **Definition 5.4, "proper implies weakly proper"** (for a continuous section `f`): with the
neighbourhood `U` of properness, a solution of `f(x) = s(x)` lies in `U` (outside `U`, `s = 0`,
so `f(x) = 0`, and `f⁻¹(0) ⊆ U`) and has `N(f(x)) = N(s(x)) ≤ 1`; and `{f = s}` is closed. -/
theorem StrongBundle.IsProper.isWeaklyProper (hfc : Continuous f) (h : B.IsProper f) :
    B.IsWeaklyProper f := by
  refine ⟨h.1, fun N hN => ?_⟩
  obtain ⟨U, hUo, hSU, hK⟩ := h.2 N hN
  refine ⟨U, hUo, hSU, fun s hs hsupp hsN => ?_⟩
  have hsc : Continuous s := continuous_iff_continuousAt.2 fun x => by
    obtain ⟨c, hc, hx⟩ := B.exists_chart_mem x
    exact (hs.continuousOn_source (B.isChart_of_mem hc)).continuousAt
      (c.φ.isOpen_source.mem_nhds hx)
  refine hK.of_isClosed_subset (isClosed_eq hfc hsc) fun x hx => subset_closure ⟨?_, ?_⟩
  · by_contra hxU
    have hz : IsZeroAt P s x := by
      by_contra hnz
      exact hxU (hsupp (subset_closure hnz))
    exact hxU (hSU (show IsZeroAt P f x from (show f x = s x from hx).trans hz))
  · exact (hsN x).congr (show f x = s x from hx).symm

/-- **Definition 5.4, "weakly proper implies a compact solution set"**. -/
theorem StrongBundle.IsWeaklyProper.isCompact_solutionSet (h : B.IsWeaklyProper f) :
    IsCompact (solutionSet P f) := h.1

/-- **Theorem 5.5, second sentence**: for an sc-Fredholm section, being proper, being weakly
proper and having a compact solution set are equivalent. -/
theorem theorem_5_5_iff (hf : B.IsScFredholmSection f) :
    (B.IsProper f ↔ B.IsWeaklyProper f) ∧ (B.IsWeaklyProper f ↔ IsCompact (solutionSet P f)) := by
  have hfc : Continuous f := continuousOn_univ.1 hf.isScSmooth.2.continuousOn
  exact ⟨⟨fun h => h.isWeaklyProper hfc, fun h => theorem_5_5 hf h.1⟩,
    ⟨fun h => h.1, fun h => (theorem_5_5 hf h).isWeaklyProper hfc⟩⟩

/-- **Remark 5.12**: let `f` have a compact solution set and let `U` be an open neighbourhood of
`f⁻¹(0)` adapted to the auxiliary norm `N` as in Theorem 5.5 (`cl{x ∈ U | N(f(x)) ≤ 1}` compact).
If the section `s` vanishes outside `U` and has `N(s(x)) ≤ 1` everywhere — which holds for the
limits of sc⁺-sections with support in `U` and `N(s) ≤ 1` in the uniform distance
`ρ(s, s') = sup N(s(x) − s'(x))` (the completion of `Γ^{+,1}_U`) — then the solution set of
`f(x) + s(x) = 0` lies in `{x ∈ U | N(f(x)) ≤ 1}`, so its closure is compact; it is compact when
it is closed (e.g. `f + s` continuous).  No sc⁺ property of `s` is used.  For `s` in the
completion the solution set is closed, so compact: `remark_5_12_completion`
(`SolutionSetClosed.lean`). -/
theorem remark_5_12 {N : B.One → ℝ} (hN : B.IsAuxNorm N) (hf : IsSection P f) {U : Set X}
    (hSU : solutionSet P f ⊆ U) (hU : IsCompact (closure {x ∈ U | B.AuxLe N (f x) 1}))
    {s : X → Y} (hs : IsSection P s) (hsU : ∀ x ∉ U, IsZeroAt P s x)
    (hsN : ∀ x, B.AuxLe N (s x) 1) :
    solutionSet P (sectionAdd P f s) ⊆ {x ∈ U | B.AuxLe N (f x) 1} ∧
      IsCompact (closure (solutionSet P (sectionAdd P f s))) := by
  have hsub : solutionSet P (sectionAdd P f s) ⊆ {x ∈ U | B.AuxLe N (f x) 1} := by
    intro x hx
    refine ⟨?_, hN.auxLe_of_sectionAdd hf hs hx (hsN x)⟩
    by_contra hxU
    refine hxU (hSU ?_)
    have hz := hsU x hxU
    have hx' : IsZeroAt P (sectionAdd P f s) x := hx
    rw [IsZeroAt, sectionAdd_apply hf hs] at hx'
    change f x = fiberZero P x
    change s x = fiberZero P x at hz
    have h1 : (⟨s x, hs x⟩ : P ⁻¹' {x}) = 0 := Subtype.ext hz
    rw [h1, add_zero] at hx'
    exact hx'
  exact ⟨hsub, hU.of_isClosed_subset isClosed_closure (closure_mono hsub)⟩

end Def54

end Polyfold
