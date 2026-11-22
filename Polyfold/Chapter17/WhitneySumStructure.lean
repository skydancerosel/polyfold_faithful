import Polyfold.Chapter17.TangentTransitionStructure
import Polyfold.Chapter17.TangentUnifExamples
import Polyfold.Chapter8.TangentWhitneyLocal
import Polyfold.Chapter8.BundleOrbitParacompact

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.6 (pp. 817–819): **Proposition 17.6.1** beyond the fibres, the M-polyfold bundle structure of
the transition sets `M(⊕ᵏ TΨ, ⊕ᵏ TΨ')` and the metrics of the orbit spaces.  Numbers and pages
are the 2021 text's.

# The Whitney sum `⊕ᵏ TC → C¹` on the transition sets

## The text, paraphrased

(**Proposition 17.6.1**, pp. 818–819) The `k`-fold Whitney sum `⊕ᵏ TC → C¹` has a natural
structure as a polyfold bundle.  The uniformizers are `⊕ᵏ TΨ : G ⋉ ⊕ᵏ TO → ⊕ᵏ TC`,
`(h₁, …, h_k) ↦ (TΨ(h₁), …, TΨ(h_k))`, covering `Ψ¹`, with `⊕ᵏ TO → O¹` the M-polyfold bundle of
§4.4.  The transition sets `M(⊕ᵏ TΨ, ⊕ᵏ TΨ')` are identified with a `k`-fold Whitney sum of
`M(TΨ, TΨ') → M(Ψ¹, Ψ'¹)`; this defines the M-polyfold bundle structure of
`M(⊕ᵏ TΨ, ⊕ᵏ TΨ') → M(Ψ¹, Ψ'¹)` and metrics for the orbit spaces, and the source and target maps
are sc-smooth local bundle isomorphisms.

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* `WTrM hU Ψ₁ Ψ₂ k` (**`M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)`**, the `k`-fold Whitney sum of
  `P : M(TΨ₁, TΨ₂) → M(Ψ₁, Ψ₂)¹`: the tuples `(b, x₁, …, x_k)` with `P(xᵢ) = b`), `wtrBase`,
  `wtrVec`, `wtr_ext`.
* **`whitneyTrHomeomorph`**: the identification `⊕ₖ T M(Ψ₁, Ψ₂) ≃ₜ M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)`, the
  identification `TM(Ψ₁, Ψ₂) ≃ₜ M(TΨ₁, TΨ₂)` of Proposition 17.2.15 on each factor;
  `metrizableSpace_WTrM`.
* **`whitneyTrPolyfold`** (the M-polyfold structure, transported from Part I's `⊕ₖ T M(Ψ₁, Ψ₂)`,
  an M-polyfold bundle over `M(Ψ₁, Ψ₂)¹` by `MPolyfold.whitneySum_bundle`),
  `isScDiffeoOn_whitneyTrHomeomorph`, `isScSmoothMap_wtrBase` (the bundle projection),
  `isScSmoothMap_wtrVec` (the `k` projections to `M(TΨ₁, TΨ₂)`), `isScSmoothOn_wtrLift` (the
  universal property of the fibred product).
* The structure maps: `wtrSrc`, `wtrTgt` (`s`, `t`; `whitneyVec_wtrSrc`, `whitneyVec_wtrTgt`: on
  each factor the source and target of `M(TΨ₁, TΨ₂)`), `whitneyTr_isLocalScDiffeo_src`, `_tgt`,
  `whitneyTr_bijective_fiber_src`, `_tgt` (**`s` and `t` are local bundle isomorphisms**: local
  sc-diffeomorphisms covering `s¹`, `t¹`, linear isomorphisms on the fibres),
  `whitneyVec_wtrTgt_eq_transMap` (`t = ⊕ᵏ Tσ_b ∘ s` over `b`, the relation of
  `proposition_17_6_1`); `wtrUnit`, `wtrVec_wtrUnit`, `whitneyTr_isScSmoothMap_unit`; `wtrInv`,
  `wtrVec_wtrInv`, `whitneyTr_isScDiffeoOn_inv`.
* The orbit spaces: the action `g ∗ (h₁, …, h_k) = (T(g ∗ ·)h₁, …, T(g ∗ ·)h_k)` of `G` on
  `⊕ᵏ TO` (`GroupoidalCategory.Uniformizer.whitneyMulAction`), `continuous_whitney_smul`,
  `whitneyProj_smul`, and **`metrizableSpace_whitneyOrbit`**: `G\⊕ᵏ TO` is metrizable.
* **`proposition_17_6_1_transition`**: the statement of p. 819 for `M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)`.
* The witness, `k = 2`, on the reflection `ℤ/2 ⋉ ℝ` with the isotropy `ℤ/2` at `0`:
  `reflNegOne` (`−1 ∈ ℤ/2`), `reflWhitneyVec` (`(e, e)`, `e = (0, 1) ∈ T_0ℝ`),
  `reflection_whitney_smul_ne` (`−1` moves it), and **`reflection_whitneyTr_nondegenerate`**: a
  point of `M(⊕² TΨ₀, ⊕² TΨ₀)` over `Ψ̂(−1, 0)` with `t = (−1) ∗ s ≠ s`.

## Readings

* `M(⊕ᵏ TΨ, ⊕ᵏ TΨ')` is read as the text identifies it: the `k`-fold Whitney sum of
  `M(TΨ, TΨ') → M(Ψ¹, Ψ'¹)` (`WTrM`), a `k`-tuple of morphisms of `TC` over one morphism of `C¹`.
  "The bundle structure" is the one carried over from Part I's `⊕ₖ T M(Ψ, Ψ') → M(Ψ, Ψ')¹`
  (Section 4.4, `MPolyfold.whitneySum_bundle`) along the identification, which on each factor is
  the identification of Proposition 17.2.15.
* "Metrics for the orbit spaces" is read for the uniformizers: the orbit space `G\⊕ᵏ TO` of the
  translation groupoid `G ⋉ ⊕ᵏ TO` is metrizable (`metrizableSpace_whitneyOrbit`), and
  `M(⊕ᵏ TΨ, ⊕ᵏ TΨ')` is metrizable (`metrizableSpace_WTrM`).
* "Sc-smooth local bundle isomorphisms" is read as: local sc-diffeomorphisms covering `s¹`
  (resp. `t¹`) that are linear isomorphisms on the fibres.
* The category `⊕ᵏ TC`, its orbit space `|⊕ᵏ TC|` and the functors `⊕ᵏ TΨ` on morphisms are not
  built here.  On morphisms `⊕ᵏ TΨ` uses `TΨ(g, h)`, a functor when `Ψ̂` is continuous
  (`lemma_17_2_10_of_continuous`; `not_lemma_17_2_10` without it); the reflection witness has
  continuous `Ψ̂`.  The multiplication of `M(⊕ᵏ TΨ, ⊕ᵏ TΨ')` is not formalized.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

/-! ### The action of `G` on `⊕ᵏ TO` -/

namespace GroupoidalCategory.Uniformizer

variable {D : GroupoidalCategory.{u}} (Ψ : D.Uniformizer) (k : ℕ)

theorem whitneyMapOf_congr_fun {f f' : Ψ.O → Ψ.O} (h : f = f') (hf : Ψ.P.IsScSmoothMap Ψ.P f)
    (hf' : Ψ.P.IsScSmoothMap Ψ.P f') :
    MPolyfold.whitneyMapOf (k := k) hf = MPolyfold.whitneyMapOf hf' := by
  subst h; rfl

/-- **The action `g ∗ (h₁, …, h_k) = (T(g ∗ ·)h₁, …, T(g ∗ ·)h_k)` of `G` on `⊕ᵏ TO`**
(2021 p. 818, `G ⋉ ⊕ᵏ TO`). -/
instance whitneyMulAction : MulAction Ψ.G (Ψ.P.WhitneySum k) where
  smul g v := MPolyfold.whitneyMapOf (Ψ.smooth_smul g) v
  one_smul v := by
    change MPolyfold.whitneyMapOf (Ψ.smooth_smul 1) v = v
    rw [whitneyMapOf_congr_fun Ψ k (funext (one_smul Ψ.G)) (Ψ.smooth_smul 1)
      MPolyfold.isScSmoothMap_id, MPolyfold.whitneyMapOf_id]
    rfl
  mul_smul g g' v := by
    change MPolyfold.whitneyMapOf (Ψ.smooth_smul (g * g')) v =
      MPolyfold.whitneyMapOf (Ψ.smooth_smul g) (MPolyfold.whitneyMapOf (Ψ.smooth_smul g') v)
    rw [whitneyMapOf_congr_fun Ψ k (funext (mul_smul g g')) (Ψ.smooth_smul (g * g'))
      ((Ψ.smooth_smul g).comp (Ψ.smooth_smul g')), MPolyfold.whitneyMapOf_comp]
    rfl

variable {k}

theorem whitney_smul_def (g : Ψ.G) (v : Ψ.P.WhitneySum k) :
    g • v = MPolyfold.whitneyMapOf (Ψ.smooth_smul g) v := rfl

theorem whitneyVec_smul (g : Ψ.G) (v : Ψ.P.WhitneySum k) (i : Fin k) :
    MPolyfold.whitneyVec (g • v) i = g • MPolyfold.whitneyVec v i := rfl

/-- The base point of `g ∗ v` is `g ∗` the base point of `v`. -/
theorem whitneyProj_smul (g : Ψ.G) (v : Ψ.P.WhitneySum k) :
    Ψ.P.levelVal 1 (MPolyfold.whitneyProj (g • v)) =
      g • Ψ.P.levelVal 1 (MPolyfold.whitneyProj v) := rfl

theorem continuous_whitney_smul (g : Ψ.G) :
    Continuous fun v : Ψ.P.WhitneySum k => g • v :=
  continuousOn_univ.1 (MPolyfold.isScSmoothMap_whitneyMapOf (Ψ.smooth_smul g)).continuousOn

/-- **The orbit space `G\⊕ᵏ TO` is metrizable** (2021 p. 819, "metrics for the orbit spaces"): a
finite group acting by homeomorphisms on the metrizable `⊕ᵏ TO`. -/
theorem metrizableSpace_whitneyOrbit :
    TopologicalSpace.MetrizableSpace (MulAction.orbitRel.Quotient Ψ.G (Ψ.P.WhitneySum k)) :=
  have := Ψ.P.metrizableSpace_whitneySum k
  metrizableSpace_orbitRel_quotient_finite (continuous_whitney_smul Ψ)

end GroupoidalCategory.Uniformizer

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction}

/-! ### `M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)` -/

section WhitneyTransition

variable {hU : S.HasUniformizers} {Ψ₁ Ψ₂ : S.Unif} {k : ℕ}

variable (S) in
/-- **`M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)`** (2021 p. 819), read as the `k`-fold Whitney sum of
`P : M(TΨ₁, TΨ₂) → M(Ψ₁, Ψ₂)¹`: the tuples `(b, x₁, …, x_k)` with `P(xᵢ) = b`. -/
def WTrM (hU : S.HasUniformizers) (Ψ₁ Ψ₂ : S.Unif) (k : ℕ) : Type (max u 1) :=
  {w : (S.transPolyfold Ψ₁ Ψ₂).Level 1 × (Fin k → S.TTrM hU Ψ₁ Ψ₂) //
    ∀ i, tangentTrProj hU (w.2 i) = w.1}

instance (hU : S.HasUniformizers) (Ψ₁ Ψ₂ : S.Unif) (k : ℕ) :
    TopologicalSpace (S.WTrM hU Ψ₁ Ψ₂ k) :=
  inferInstanceAs (TopologicalSpace
    {w : (S.transPolyfold Ψ₁ Ψ₂).Level 1 × (Fin k → S.TTrM hU Ψ₁ Ψ₂) //
      ∀ i, tangentTrProj hU (w.2 i) = w.1})

/-- The base point `b ∈ M(Ψ₁, Ψ₂)¹`. -/
def wtrBase (w : S.WTrM hU Ψ₁ Ψ₂ k) : (S.transPolyfold Ψ₁ Ψ₂).Level 1 := w.1.1

/-- The `i`-th entry `xᵢ ∈ M(TΨ₁, TΨ₂)`. -/
def wtrVec (w : S.WTrM hU Ψ₁ Ψ₂ k) (i : Fin k) : S.TTrM hU Ψ₁ Ψ₂ := w.1.2 i

theorem tangentTrProj_wtrVec (w : S.WTrM hU Ψ₁ Ψ₂ k) (i : Fin k) :
    tangentTrProj hU (wtrVec w i) = wtrBase w := w.2 i

theorem wtr_ext {w w' : S.WTrM hU Ψ₁ Ψ₂ k} (h₁ : wtrBase w = wtrBase w')
    (h₂ : ∀ i, wtrVec w i = wtrVec w' i) : w = w' :=
  Subtype.ext (Prod.ext h₁ (funext h₂))

theorem continuous_wtrBase : Continuous (wtrBase : S.WTrM hU Ψ₁ Ψ₂ k → _) :=
  continuous_fst.comp continuous_subtype_val

theorem continuous_wtrVec (i : Fin k) : Continuous fun w : S.WTrM hU Ψ₁ Ψ₂ k => wtrVec w i :=
  (continuous_apply i).comp (continuous_snd.comp continuous_subtype_val)

variable (hU Ψ₁ Ψ₂ k) in
/-- **The identification `⊕ₖ T M(Ψ₁, Ψ₂) ≃ₜ M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)`** (2021 p. 819): the
identification `TM(Ψ₁, Ψ₂) ≃ₜ M(TΨ₁, TΨ₂)` of Proposition 17.2.15 on each factor. -/
def whitneyTrHomeomorph :
    (S.transPolyfold Ψ₁ Ψ₂).WhitneySum k ≃ₜ S.WTrM hU Ψ₁ Ψ₂ k where
  toFun v := ⟨(MPolyfold.whitneyProj v,
      fun i => tangentTrHomeomorph hU Ψ₁ Ψ₂ (MPolyfold.whitneyVec v i)), fun i => by
    change (S.transPolyfold Ψ₁ Ψ₂).tangentProj ((tangentTrHomeomorph hU Ψ₁ Ψ₂).symm
      (tangentTrHomeomorph hU Ψ₁ Ψ₂ (MPolyfold.whitneyVec v i))) = _
    rw [Homeomorph.symm_apply_apply]
    exact MPolyfold.tangentProj_whitneyVec v i⟩
  invFun w := MPolyfold.whitneyMk (wtrBase w)
    (fun i => (tangentTrHomeomorph hU Ψ₁ Ψ₂).symm (wtrVec w i)) (tangentTrProj_wtrVec w)
  left_inv v := MPolyfold.whitneySum_ext rfl fun i =>
    (tangentTrHomeomorph hU Ψ₁ Ψ₂).symm_apply_apply _
  right_inv w := wtr_ext rfl fun i => (tangentTrHomeomorph hU Ψ₁ Ψ₂).apply_symm_apply _
  continuous_toFun := (MPolyfold.continuous_whitneyProj.prodMk (continuous_pi fun i =>
    (tangentTrHomeomorph hU Ψ₁ Ψ₂).continuous.comp
      (MPolyfold.continuous_whitneyVec i))).subtype_mk _
  continuous_invFun := by
    rw [← continuousOn_univ, MPolyfold.continuousOn_whitney_iff]
    exact ⟨continuous_wtrBase.continuousOn, fun i =>
      ((tangentTrHomeomorph hU Ψ₁ Ψ₂).symm.continuous.comp (continuous_wtrVec i)).continuousOn⟩

theorem wtrBase_whitneyTrHomeomorph (v : (S.transPolyfold Ψ₁ Ψ₂).WhitneySum k) :
    wtrBase (whitneyTrHomeomorph hU Ψ₁ Ψ₂ k v) = MPolyfold.whitneyProj v := rfl

theorem wtrVec_whitneyTrHomeomorph (v : (S.transPolyfold Ψ₁ Ψ₂).WhitneySum k) (i : Fin k) :
    wtrVec (whitneyTrHomeomorph hU Ψ₁ Ψ₂ k v) i =
      tangentTrHomeomorph hU Ψ₁ Ψ₂ (MPolyfold.whitneyVec v i) := rfl

theorem whitneyProj_whitneyTrHomeomorph_symm (w : S.WTrM hU Ψ₁ Ψ₂ k) :
    MPolyfold.whitneyProj ((whitneyTrHomeomorph hU Ψ₁ Ψ₂ k).symm w) = wtrBase w := rfl

theorem whitneyVec_whitneyTrHomeomorph_symm (w : S.WTrM hU Ψ₁ Ψ₂ k) (i : Fin k) :
    MPolyfold.whitneyVec ((whitneyTrHomeomorph hU Ψ₁ Ψ₂ k).symm w) i =
      (tangentTrHomeomorph hU Ψ₁ Ψ₂).symm (wtrVec w i) := rfl

instance (hU : S.HasUniformizers) (Ψ₁ Ψ₂ : S.Unif) (k : ℕ) : T2Space (S.WTrM hU Ψ₁ Ψ₂ k) :=
  (whitneyTrHomeomorph hU Ψ₁ Ψ₂ k).symm.isEmbedding.t2Space

instance (hU : S.HasUniformizers) (Ψ₁ Ψ₂ : S.Unif) (k : ℕ) :
    ParacompactSpace (S.WTrM hU Ψ₁ Ψ₂ k) :=
  (whitneyTrHomeomorph hU Ψ₁ Ψ₂ k).symm.isClosedEmbedding.paracompactSpace

/-- **`M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)` is metrizable** (2021 p. 819): it is homeomorphic to Part I's
`⊕ₖ T M(Ψ₁, Ψ₂)`. -/
instance metrizableSpace_WTrM (hU : S.HasUniformizers) (Ψ₁ Ψ₂ : S.Unif) (k : ℕ) :
    TopologicalSpace.MetrizableSpace (S.WTrM hU Ψ₁ Ψ₂ k) :=
  have := (S.transPolyfold Ψ₁ Ψ₂).metrizableSpace_whitneySum k
  (whitneyTrHomeomorph hU Ψ₁ Ψ₂ k).symm.isEmbedding.metrizableSpace

variable (S hU Ψ₁ Ψ₂ k) in
/-- **The M-polyfold structure of `M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)`** (2021 p. 819): Part I's
`⊕ₖ T M(Ψ₁, Ψ₂)`, an M-polyfold bundle over `M(Ψ₁, Ψ₂)¹` (`MPolyfold.whitneySum_bundle`),
transported along the identification. -/
def whitneyTrPolyfold : MPolyfold (S.WTrM hU Ψ₁ Ψ₂ k) :=
  ((S.transPolyfold Ψ₁ Ψ₂).whitneyPolyfold k).transport (whitneyTrHomeomorph hU Ψ₁ Ψ₂ k)

theorem isScDiffeoOn_whitneyTrHomeomorph :
    ((S.transPolyfold Ψ₁ Ψ₂).whitneyPolyfold k).IsScDiffeoOn (S.whitneyTrPolyfold hU Ψ₁ Ψ₂ k)
      (whitneyTrHomeomorph hU Ψ₁ Ψ₂ k) (whitneyTrHomeomorph hU Ψ₁ Ψ₂ k).symm univ univ :=
  MPolyfold.isScDiffeoOn_transport _ _

theorem isLocalScDiffeo_whitneyTrHomeomorph_symm :
    (S.whitneyTrPolyfold hU Ψ₁ Ψ₂ k).IsLocalScDiffeo ((S.transPolyfold Ψ₁ Ψ₂).whitneyPolyfold k)
      (whitneyTrHomeomorph hU Ψ₁ Ψ₂ k).symm := fun _ =>
  ⟨univ, univ, whitneyTrHomeomorph hU Ψ₁ Ψ₂ k, mem_univ _,
    isScDiffeoOn_whitneyTrHomeomorph.symm⟩

theorem isScSmoothMap_whitneyTrHomeomorph :
    ((S.transPolyfold Ψ₁ Ψ₂).whitneyPolyfold k).IsScSmoothMap (S.whitneyTrPolyfold hU Ψ₁ Ψ₂ k)
      (whitneyTrHomeomorph hU Ψ₁ Ψ₂ k) :=
  isScDiffeoOn_whitneyTrHomeomorph.isScSmoothOn

/-- **The bundle projection `M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂) → M(Ψ₁, Ψ₂)¹` is sc-smooth.** -/
theorem isScSmoothMap_wtrBase :
    (S.whitneyTrPolyfold hU Ψ₁ Ψ₂ k).IsScSmoothMap (S.transPolyfold Ψ₁ Ψ₂).shift
      (wtrBase (hU := hU) (Ψ₁ := Ψ₁) (Ψ₂ := Ψ₂) (k := k)) :=
  MPolyfold.isScSmoothMap_whitneyProj.comp isLocalScDiffeo_whitneyTrHomeomorph_symm.isScSmoothMap

/-- The `i`-th projection `M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂) → M(TΨ₁, TΨ₂)` is sc-smooth. -/
theorem isScSmoothMap_wtrVec (i : Fin k) :
    (S.whitneyTrPolyfold hU Ψ₁ Ψ₂ k).IsScSmoothMap (S.tangentTrPolyfold hU Ψ₁ Ψ₂)
      fun w : S.WTrM hU Ψ₁ Ψ₂ k => wtrVec w i := by
  have h : (fun w : S.WTrM hU Ψ₁ Ψ₂ k => wtrVec w i) = tangentTrHomeomorph hU Ψ₁ Ψ₂ ∘
      (fun v => MPolyfold.whitneyVec v i) ∘ (whitneyTrHomeomorph hU Ψ₁ Ψ₂ k).symm :=
    funext fun w => ((tangentTrHomeomorph hU Ψ₁ Ψ₂).apply_symm_apply _).symm
  rw [h]
  exact isScSmoothMap_tangentTrHomeomorph.comp ((MPolyfold.isScSmoothMap_whitneyVec i).comp
    isLocalScDiffeo_whitneyTrHomeomorph_symm.isScSmoothMap)

/-- **The universal property of the fibred product**: a map into `M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)` is sc-smooth
on an open set as soon as its base and its `k` entries are. -/
theorem isScSmoothOn_wtrLift {Z : Type*} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    {Q : MPolyfold Z} {g : Z → S.WTrM hU Ψ₁ Ψ₂ k} {U : Set Z}
    (h₀ : Q.IsScSmoothOn (S.transPolyfold Ψ₁ Ψ₂).shift (fun z => wtrBase (g z)) U)
    (h : ∀ i, Q.IsScSmoothOn (S.tangentTrPolyfold hU Ψ₁ Ψ₂) (fun z => wtrVec (g z) i) U) :
    Q.IsScSmoothOn (S.whitneyTrPolyfold hU Ψ₁ Ψ₂ k) g U := by
  have h' : Q.IsScSmoothOn ((S.transPolyfold Ψ₁ Ψ₂).whitneyPolyfold k)
      (fun z => (whitneyTrHomeomorph hU Ψ₁ Ψ₂ k).symm (g z)) U :=
    MPolyfold.isScSmoothOn_whitneyLift h₀ fun i => MPolyfold.IsScSmoothOn.comp (U' := univ)
      isLocalScDiffeo_tangentTrHomeomorph_symm.isScSmoothMap (h i) (mapsTo_univ _ _)
  exact (MPolyfold.IsScSmoothOn.comp (U' := univ) isScSmoothMap_whitneyTrHomeomorph h'
    (mapsTo_univ _ _)).congr fun z _ => (whitneyTrHomeomorph hU Ψ₁ Ψ₂ k).apply_symm_apply (g z)

/-! ### The source and target maps -/

variable (hU Ψ₁ Ψ₂ k) in
/-- **The source map `s : M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂) → ⊕ᵏ TO₁`**: `⊕ᵏ Ts` under the identification. -/
def wtrSrc (w : S.WTrM hU Ψ₁ Ψ₂ k) : Ψ₁.1.P.WhitneySum k :=
  MPolyfold.whitneyMapOf (S.isLocalScDiffeo_trSrc Ψ₁ Ψ₂).isScSmoothMap
    ((whitneyTrHomeomorph hU Ψ₁ Ψ₂ k).symm w)

variable (hU Ψ₁ Ψ₂ k) in
/-- **The target map `t : M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂) → ⊕ᵏ TO₂`**: `⊕ᵏ Tt` under the identification. -/
def wtrTgt (w : S.WTrM hU Ψ₁ Ψ₂ k) : Ψ₂.1.P.WhitneySum k :=
  MPolyfold.whitneyMapOf (S.isLocalScDiffeo_trTgt Ψ₁ Ψ₂).isScSmoothMap
    ((whitneyTrHomeomorph hU Ψ₁ Ψ₂ k).symm w)

/-- `s(b, x₁, …, x_k) = (s(x₁), …, s(x_k))`. -/
theorem whitneyVec_wtrSrc (w : S.WTrM hU Ψ₁ Ψ₂ k) (i : Fin k) :
    MPolyfold.whitneyVec (S.wtrSrc hU Ψ₁ Ψ₂ k w) i = (wtrVec w i).src :=
  (src_eq_trTSrc _).symm

/-- `t(b, x₁, …, x_k) = (t(x₁), …, t(x_k))`. -/
theorem whitneyVec_wtrTgt (w : S.WTrM hU Ψ₁ Ψ₂ k) (i : Fin k) :
    MPolyfold.whitneyVec (S.wtrTgt hU Ψ₁ Ψ₂ k w) i = (wtrVec w i).tgt :=
  (tgt_eq_trTTgt _).symm

/-- `s` covers `s¹ : M(Ψ₁, Ψ₂)¹ → O₁¹`. -/
theorem levelVal_whitneyProj_wtrSrc (w : S.WTrM hU Ψ₁ Ψ₂ k) :
    Ψ₁.1.P.levelVal 1 (MPolyfold.whitneyProj (S.wtrSrc hU Ψ₁ Ψ₂ k w)) =
      ((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (wtrBase w)).src := rfl

/-- `t` covers `t¹ : M(Ψ₁, Ψ₂)¹ → O₂¹`. -/
theorem levelVal_whitneyProj_wtrTgt (w : S.WTrM hU Ψ₁ Ψ₂ k) :
    Ψ₂.1.P.levelVal 1 (MPolyfold.whitneyProj (S.wtrTgt hU Ψ₁ Ψ₂ k w)) =
      ((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (wtrBase w)).tgt := rfl

theorem wtrSrc_whitneyTrHomeomorph (v : (S.transPolyfold Ψ₁ Ψ₂).WhitneySum k) :
    S.wtrSrc hU Ψ₁ Ψ₂ k (whitneyTrHomeomorph hU Ψ₁ Ψ₂ k v) =
      MPolyfold.whitneyMapOf (S.isLocalScDiffeo_trSrc Ψ₁ Ψ₂).isScSmoothMap v := by
  rw [wtrSrc, Homeomorph.symm_apply_apply]

theorem wtrTgt_whitneyTrHomeomorph (v : (S.transPolyfold Ψ₁ Ψ₂).WhitneySum k) :
    S.wtrTgt hU Ψ₁ Ψ₂ k (whitneyTrHomeomorph hU Ψ₁ Ψ₂ k v) =
      MPolyfold.whitneyMapOf (S.isLocalScDiffeo_trTgt Ψ₁ Ψ₂).isScSmoothMap v := by
  rw [wtrTgt, Homeomorph.symm_apply_apply]

/-- **`s` is a local sc-diffeomorphism** (Definition 17.1.8 (a) for `M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)`). -/
theorem whitneyTr_isLocalScDiffeo_src :
    (S.whitneyTrPolyfold hU Ψ₁ Ψ₂ k).IsLocalScDiffeo (Ψ₁.1.P.whitneyPolyfold k)
      (S.wtrSrc hU Ψ₁ Ψ₂ k) :=
  (S.isLocalScDiffeo_trSrc Ψ₁ Ψ₂).whitneyMapOf.comp isLocalScDiffeo_whitneyTrHomeomorph_symm

/-- **`t` is a local sc-diffeomorphism** (Definition 17.1.8 (a) for `M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)`). -/
theorem whitneyTr_isLocalScDiffeo_tgt :
    (S.whitneyTrPolyfold hU Ψ₁ Ψ₂ k).IsLocalScDiffeo (Ψ₂.1.P.whitneyPolyfold k)
      (S.wtrTgt hU Ψ₁ Ψ₂ k) :=
  (S.isLocalScDiffeo_trTgt Ψ₁ Ψ₂).whitneyMapOf.comp isLocalScDiffeo_whitneyTrHomeomorph_symm

/-- **`s` is a linear isomorphism on the fibres**: over `b ∈ M(Ψ₁, Ψ₂)¹` (read through the
identification with `⊕ₖ T M(Ψ₁, Ψ₂)`), onto the fibre of `⊕ᵏ TO₁` over `s(b)`. -/
theorem whitneyTr_bijective_fiber_src (b : (S.transPolyfold Ψ₁ Ψ₂).Level 1)
    (x : Ψ₁.1.P.Level 1) (hx : ((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 b).src = Ψ₁.1.P.levelVal 1 x) :
    Bijective (MPolyfold.whitneyFiberMap (k := k) (S.isLocalScDiffeo_trSrc Ψ₁ Ψ₂).isScSmoothMap
        hx) ∧
      ∀ v, (MPolyfold.whitneyFiberMap (S.isLocalScDiffeo_trSrc Ψ₁ Ψ₂).isScSmoothMap hx v :
        Ψ₁.1.P.WhitneySum k) = S.wtrSrc hU Ψ₁ Ψ₂ k (whitneyTrHomeomorph hU Ψ₁ Ψ₂ k v.1) :=
  ⟨(S.isLocalScDiffeo_trSrc Ψ₁ Ψ₂).bijective_whitneyFiberMap hx, fun v => by
    rw [wtrSrc_whitneyTrHomeomorph, MPolyfold.coe_whitneyFiberMap_apply]⟩

/-- **`t` is a linear isomorphism on the fibres**. -/
theorem whitneyTr_bijective_fiber_tgt (b : (S.transPolyfold Ψ₁ Ψ₂).Level 1)
    (y : Ψ₂.1.P.Level 1) (hy : ((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 b).tgt = Ψ₂.1.P.levelVal 1 y) :
    Bijective (MPolyfold.whitneyFiberMap (k := k) (S.isLocalScDiffeo_trTgt Ψ₁ Ψ₂).isScSmoothMap
        hy) ∧
      ∀ v, (MPolyfold.whitneyFiberMap (S.isLocalScDiffeo_trTgt Ψ₁ Ψ₂).isScSmoothMap hy v :
        Ψ₂.1.P.WhitneySum k) = S.wtrTgt hU Ψ₁ Ψ₂ k (whitneyTrHomeomorph hU Ψ₁ Ψ₂ k v.1) :=
  ⟨(S.isLocalScDiffeo_trTgt Ψ₁ Ψ₂).bijective_whitneyFiberMap hy, fun v => by
    rw [wtrTgt_whitneyTrHomeomorph, MPolyfold.coe_whitneyFiberMap_apply]⟩

/-- **`t = ⊕ᵏ Tσ_b ∘ s` over `b`** (the relation of `proposition_17_6_1` on
`M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)`): `t(xᵢ) = Tσ_b(s(xᵢ))` for `σ` of the base point `b`. -/
theorem whitneyVec_wtrTgt_eq_transMap (w : S.WTrM hU Ψ₁ Ψ₂ k) (i : Fin k) :
    MPolyfold.whitneyVec (S.wtrTgt hU Ψ₁ Ψ₂ k w) i =
      S.transMap ((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (wtrBase w))
        (MPolyfold.whitneyVec (S.wtrSrc hU Ψ₁ Ψ₂ k w) i) := by
  have h := trTTgt_eq_transMap ((tangentTrHomeomorph hU Ψ₁ Ψ₂).symm (wtrVec w i))
  have hb : trBase ((tangentTrHomeomorph hU Ψ₁ Ψ₂).symm (wtrVec w i)) =
      (S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (wtrBase w) :=
    congrArg ((S.transPolyfold Ψ₁ Ψ₂).levelVal 1) (tangentTrProj_wtrVec w i)
  rw [hb] at h
  exact h

/-! ### The unit and the inversion -/

variable (hU k) in
/-- **The unit map `u : ⊕ᵏ TO → M(⊕ᵏ TΨ, ⊕ᵏ TΨ)`**: `⊕ᵏ Tu` under the identification. -/
def wtrUnit (Ψ : S.Unif) (v : Ψ.1.P.WhitneySum k) : S.WTrM hU Ψ Ψ k :=
  whitneyTrHomeomorph hU Ψ Ψ k (MPolyfold.whitneyMapOf (S.isScSmoothMap_trUnit Ψ) v)

/-- `u(h₁, …, h_k) = (u(h₁), …, u(h_k))`, the units of `M(TΨ, TΨ)`. -/
theorem wtrVec_wtrUnit (Ψ : S.Unif) (v : Ψ.1.P.WhitneySum k) (i : Fin k) :
    wtrVec (S.wtrUnit hU k Ψ v) i =
      toTTrM (hU := hU) (GroupoidStr.TransitionSet.unit (MPolyfold.whitneyVec v i)) :=
  tangentTrMap_trTUnit Ψ _

/-- **The unit map is sc-smooth** (Definition 17.1.8 (b) for `M(⊕ᵏ TΨ, ⊕ᵏ TΨ)`). -/
theorem whitneyTr_isScSmoothMap_unit (Ψ : S.Unif) :
    (Ψ.1.P.whitneyPolyfold k).IsScSmoothMap (S.whitneyTrPolyfold hU Ψ Ψ k) (S.wtrUnit hU k Ψ) :=
  isScSmoothMap_whitneyTrHomeomorph.comp (MPolyfold.isScSmoothMap_whitneyMapOf _)

variable (hU Ψ₁ Ψ₂ k) in
/-- **The inversion `ι : M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂) → M(⊕ᵏ TΨ₂, ⊕ᵏ TΨ₁)`**: `⊕ᵏ Tι` under the
identification. -/
def wtrInv (w : S.WTrM hU Ψ₁ Ψ₂ k) : S.WTrM hU Ψ₂ Ψ₁ k :=
  whitneyTrHomeomorph hU Ψ₂ Ψ₁ k (MPolyfold.whitneyMapOf (S.isScSmoothMap_trInv Ψ₁ Ψ₂)
    ((whitneyTrHomeomorph hU Ψ₁ Ψ₂ k).symm w))

/-- `ι(b, x₁, …, x_k) = (ι(b), ι(x₁), …, ι(x_k))`. -/
theorem wtrVec_wtrInv (w : S.WTrM hU Ψ₁ Ψ₂ k) (i : Fin k) :
    wtrVec (S.wtrInv hU Ψ₁ Ψ₂ k w) i =
      toTTrM (hU := hU) (GroupoidStr.TransitionSet.inv (wtrVec w i)) := by
  change tangentTrMap hU (trTInv Ψ₁ Ψ₂ ((tangentTrHomeomorph hU Ψ₁ Ψ₂).symm (wtrVec w i))) = _
  rw [tangentTrMap_trTInv]
  exact congrArg GroupoidStr.TransitionSet.inv ((tangentTrHomeomorph hU Ψ₁ Ψ₂).apply_symm_apply _)

theorem levelVal_wtrBase_wtrInv (w : S.WTrM hU Ψ₁ Ψ₂ k) :
    (S.transPolyfold Ψ₂ Ψ₁).levelVal 1 (wtrBase (S.wtrInv hU Ψ₁ Ψ₂ k w)) =
      S.toTr (GroupoidStr.TransitionSet.inv ((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (wtrBase w))) :=
  rfl

theorem wtrInv_wtrInv (w : S.WTrM hU Ψ₁ Ψ₂ k) : S.wtrInv hU Ψ₂ Ψ₁ k (S.wtrInv hU Ψ₁ Ψ₂ k w) = w :=
  wtr_ext (MPolyfold.level_ext (by
      rw [levelVal_wtrBase_wtrInv, levelVal_wtrBase_wtrInv]
      exact GroupoidStr.TransitionSet.inv_inv _)) fun i => by
    rw [wtrVec_wtrInv, wtrVec_wtrInv]
    exact GroupoidStr.TransitionSet.inv_inv _

theorem whitneyTr_isScSmoothMap_inv :
    (S.whitneyTrPolyfold hU Ψ₁ Ψ₂ k).IsScSmoothMap (S.whitneyTrPolyfold hU Ψ₂ Ψ₁ k)
      (S.wtrInv hU Ψ₁ Ψ₂ k) :=
  isScSmoothMap_whitneyTrHomeomorph.comp ((MPolyfold.isScSmoothMap_whitneyMapOf _).comp
    isLocalScDiffeo_whitneyTrHomeomorph_symm.isScSmoothMap)

/-- **The inversion is an sc-diffeomorphism** (Definition 17.1.8 (b) for
`M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)`). -/
theorem whitneyTr_isScDiffeoOn_inv :
    (S.whitneyTrPolyfold hU Ψ₁ Ψ₂ k).IsScDiffeoOn (S.whitneyTrPolyfold hU Ψ₂ Ψ₁ k)
      (S.wtrInv hU Ψ₁ Ψ₂ k) (S.wtrInv hU Ψ₂ Ψ₁ k) univ univ :=
  ⟨whitneyTr_isScSmoothMap_inv, whitneyTr_isScSmoothMap_inv, mapsTo_univ _ _, mapsTo_univ _ _,
    fun w _ => wtrInv_wtrInv w, fun w _ => wtrInv_wtrInv w⟩

end WhitneyTransition

/-! ### Proposition 17.6.1 on the transition sets -/

/-- **Proposition 17.6.1 on the transition sets** (2021 p. 819): `M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)`, the `k`-fold
Whitney sum of `M(TΨ₁, TΨ₂) → M(Ψ₁, Ψ₂)¹`, is identified (homeomorphically and
sc-diffeomorphically) with Part I's M-polyfold bundle `⊕ₖ T M(Ψ₁, Ψ₂) → M(Ψ₁, Ψ₂)¹` by the
identification of Proposition 17.2.15 on each factor; it is metrizable; its projection to
`M(Ψ₁, Ψ₂)¹` and its `k` projections to `M(TΨ₁, TΨ₂)` are sc-smooth; the source and target maps
are local sc-diffeomorphisms, given on each factor by those of `M(TΨ₁, TΨ₂)`, linear isomorphisms
on the fibres, and related by `t = ⊕ᵏ Tσ_b ∘ s` over `b`; the inversion is an sc-diffeomorphism and
the unit is sc-smooth. -/
theorem proposition_17_6_1_transition (hU : S.HasUniformizers) (Ψ₁ Ψ₂ : S.Unif) (k : ℕ) :
    ((S.transPolyfold Ψ₁ Ψ₂).whitneyPolyfold k).IsScDiffeoOn (S.whitneyTrPolyfold hU Ψ₁ Ψ₂ k)
      (whitneyTrHomeomorph hU Ψ₁ Ψ₂ k) (whitneyTrHomeomorph hU Ψ₁ Ψ₂ k).symm univ univ ∧
    TopologicalSpace.MetrizableSpace (S.WTrM hU Ψ₁ Ψ₂ k) ∧
    (S.whitneyTrPolyfold hU Ψ₁ Ψ₂ k).IsScSmoothMap (S.transPolyfold Ψ₁ Ψ₂).shift
      (wtrBase (hU := hU) (Ψ₁ := Ψ₁) (Ψ₂ := Ψ₂) (k := k)) ∧
    (∀ i, (S.whitneyTrPolyfold hU Ψ₁ Ψ₂ k).IsScSmoothMap (S.tangentTrPolyfold hU Ψ₁ Ψ₂)
      fun w : S.WTrM hU Ψ₁ Ψ₂ k => wtrVec w i) ∧
    (S.whitneyTrPolyfold hU Ψ₁ Ψ₂ k).IsLocalScDiffeo (Ψ₁.1.P.whitneyPolyfold k)
      (S.wtrSrc hU Ψ₁ Ψ₂ k) ∧
    (S.whitneyTrPolyfold hU Ψ₁ Ψ₂ k).IsLocalScDiffeo (Ψ₂.1.P.whitneyPolyfold k)
      (S.wtrTgt hU Ψ₁ Ψ₂ k) ∧
    (∀ w i, MPolyfold.whitneyVec (S.wtrSrc hU Ψ₁ Ψ₂ k w) i = (wtrVec w i).src ∧
      MPolyfold.whitneyVec (S.wtrTgt hU Ψ₁ Ψ₂ k w) i = (wtrVec w i).tgt) ∧
    (∀ (b : (S.transPolyfold Ψ₁ Ψ₂).Level 1) (x : Ψ₁.1.P.Level 1)
      (hx : ((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 b).src = Ψ₁.1.P.levelVal 1 x),
      Bijective (MPolyfold.whitneyFiberMap (k := k)
        (S.isLocalScDiffeo_trSrc Ψ₁ Ψ₂).isScSmoothMap hx)) ∧
    (∀ (b : (S.transPolyfold Ψ₁ Ψ₂).Level 1) (y : Ψ₂.1.P.Level 1)
      (hy : ((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 b).tgt = Ψ₂.1.P.levelVal 1 y),
      Bijective (MPolyfold.whitneyFiberMap (k := k)
        (S.isLocalScDiffeo_trTgt Ψ₁ Ψ₂).isScSmoothMap hy)) ∧
    (∀ w i, MPolyfold.whitneyVec (S.wtrTgt hU Ψ₁ Ψ₂ k w) i =
      S.transMap ((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (wtrBase w))
        (MPolyfold.whitneyVec (S.wtrSrc hU Ψ₁ Ψ₂ k w) i)) ∧
    (S.whitneyTrPolyfold hU Ψ₁ Ψ₂ k).IsScDiffeoOn (S.whitneyTrPolyfold hU Ψ₂ Ψ₁ k)
      (S.wtrInv hU Ψ₁ Ψ₂ k) (S.wtrInv hU Ψ₂ Ψ₁ k) univ univ ∧
    (Ψ₁.1.P.whitneyPolyfold k).IsScSmoothMap (S.whitneyTrPolyfold hU Ψ₁ Ψ₁ k)
      (S.wtrUnit hU k Ψ₁) :=
  ⟨isScDiffeoOn_whitneyTrHomeomorph, inferInstance, isScSmoothMap_wtrBase, isScSmoothMap_wtrVec,
    whitneyTr_isLocalScDiffeo_src, whitneyTr_isLocalScDiffeo_tgt,
    fun w i => ⟨whitneyVec_wtrSrc w i, whitneyVec_wtrTgt w i⟩,
    fun b x hx => (whitneyTr_bijective_fiber_src (hU := hU) b x hx).1,
    fun b y hy => (whitneyTr_bijective_fiber_tgt (hU := hU) b y hy).1,
    whitneyVec_wtrTgt_eq_transMap, whitneyTr_isScDiffeoOn_inv, whitneyTr_isScSmoothMap_unit Ψ₁⟩

/-! ### The witness: `k = 2` on the reflection `ℤ/2 ⋉ ℝ` -/

section Reflection

open EpGroupoid.Examples MPolyfold

/-- The isotropy element `−1 ∈ ℤ/2` of `0` in the reflection uniformizer. -/
def reflNegOne : reflectionUnif.1.G := (-1 : ℤˣ)

/-- The point `(0; e, e)` of `⊕² Tℝ`, `e = (0, 1) ∈ T_0ℝ`. -/
def reflWhitneyVec : reflectionUnif.1.P.WhitneySum 2 :=
  whitneyMk ((rnPolyfold 1).tangentProj fstSwapTangent) (fun _ => fstSwapTangent) fun _ => rfl

/-- **The isotropy `−1` of `0` acts non-trivially on `⊕² T_0ℝ`**:
`(−1) ∗ (e, e) = (T(−1 ∗ ·)e, T(−1 ∗ ·)e) = (−e, −e) ≠ (e, e)`. -/
theorem reflection_whitney_smul_ne :
    whitneyMapOf (reflectionUnif.1.smooth_smul reflNegOne) reflWhitneyVec ≠ reflWhitneyVec := by
  intro h
  have h0 := congrArg (fun v => tangentChartMap (isChart_rnChart 0) (whitneyVec v 0)) h
  change tangentChartMap (isChart_rnChart 0)
      (MPolyfold.tangentMap (isScSmoothMap_units_smul (-1)) fstSwapTangent) =
    tangentChartMap (isChart_rnChart 0) fstSwapTangent at h0
  rw [tangentChartMap_tangentMap_neg, tangentChartMap_fstSwapTangent] at h0
  have h1 := congrFun (congrArg Prod.snd h0) 0
  norm_num [fstSwapVec] at h1

/-- **The non-degenerate witness for `M(⊕² TΨ₀, ⊕² TΨ₀)`**: over the morphism `Ψ̂(−1, 0)` of the
isotropy of `0`, there is a point `w` with `s(w) = (e, e)` and `t(w) = (−1) ∗ s(w) ≠ s(w)`. -/
theorem reflection_whitneyTr_nondegenerate :
    ∃ w : reflectionConstruction.WTrM reflectionConstruction_hasUniformizers reflectionUnif
        reflectionUnif 2,
      reflectionConstruction.wtrSrc reflectionConstruction_hasUniformizers reflectionUnif
          reflectionUnif 2 w = reflWhitneyVec ∧
      reflectionConstruction.wtrTgt reflectionConstruction_hasUniformizers reflectionUnif
          reflectionUnif 2 w = whitneyMapOf (reflectionUnif.1.smooth_smul reflNegOne)
        (reflectionConstruction.wtrSrc reflectionConstruction_hasUniformizers reflectionUnif
          reflectionUnif 2 w) ∧
      reflectionConstruction.wtrTgt reflectionConstruction_hasUniformizers reflectionUnif
          reflectionUnif 2 w ≠ reflectionConstruction.wtrSrc
          reflectionConstruction_hasUniformizers reflectionUnif reflectionUnif 2 w := by
  have hs := reflectionConstruction.isLocalScDiffeo_trSrc reflectionUnif reflectionUnif
  have ha : reflectionConstruction.hat reflectionUnif
      (reflNegOne, basePt reflectionUnif fstSwapTangent) ∈
        (reflectionConstruction.transPolyfold reflectionUnif reflectionUnif).levelSet 1 := by
    refine (hs.mem_levelSet_iff _ 1).1 ?_
    change _ ∈ (rnPolyfold 1).levelSet 1
    rw [rnPolyfold_levelSet]; exact mem_univ _
  have hab : (reflectionConstruction.transPolyfold reflectionUnif reflectionUnif).levelVal 1
      ((reflectionConstruction.transPolyfold reflectionUnif reflectionUnif).levelMk 1 _ ha) =
      reflectionConstruction.hat reflectionUnif
        (reflNegOne, basePt reflectionUnif fstSwapTangent) :=
    levelVal_levelMk _ _ _
  have hx : ((reflectionConstruction.transPolyfold reflectionUnif reflectionUnif).levelVal 1
      ((reflectionConstruction.transPolyfold reflectionUnif reflectionUnif).levelMk 1 _ ha)).src =
      reflectionUnif.1.P.levelVal 1 (whitneyProj reflWhitneyVec) := by
    rw [hab]; rfl
  obtain ⟨u, hu⟩ := (hs.bijective_whitneyFiberMap (k := 2) hx).2 ⟨reflWhitneyVec, rfl⟩
  have hu' := congrArg Subtype.val hu
  rw [coe_whitneyFiberMap_apply] at hu'
  have hu2 : whitneyProj u.1 =
      (reflectionConstruction.transPolyfold reflectionUnif reflectionUnif).levelMk 1 _ ha := u.2
  have hsrc : reflectionConstruction.wtrSrc reflectionConstruction_hasUniformizers reflectionUnif
      reflectionUnif 2 (whitneyTrHomeomorph _ reflectionUnif reflectionUnif 2 u.1) =
      reflWhitneyVec := by
    rw [wtrSrc_whitneyTrHomeomorph]; exact hu'
  have htgt : reflectionConstruction.wtrTgt reflectionConstruction_hasUniformizers reflectionUnif
      reflectionUnif 2 (whitneyTrHomeomorph _ reflectionUnif reflectionUnif 2 u.1) =
      whitneyMapOf (reflectionUnif.1.smooth_smul reflNegOne) reflWhitneyVec := by
    refine whitneySum_ext (level_ext ?_) fun i => ?_
    · rw [levelVal_whitneyProj_wtrTgt, levelVal_whitneyProj_whitneyMapOf,
        wtrBase_whitneyTrHomeomorph, hu2, hab]
      rfl
    · rw [whitneyVec_wtrTgt_eq_transMap, whitneyVec_whitneyMapOf, wtrBase_whitneyTrHomeomorph,
        hu2, hab, hsrc]
      exact transMap_hat_of_continuous reflection_continuous_hat _ _
  refine ⟨whitneyTrHomeomorph _ reflectionUnif reflectionUnif 2 u.1, hsrc, ?_, ?_⟩
  · rw [htgt, hsrc]
  · rw [htgt, hsrc]
    exact reflection_whitney_smul_ne

end Reflection

end GCT.PolyfoldConstruction

end Polyfold
