import Polyfold.Chapter19.CoveringSquareTheorem
import Polyfold.Chapter19.CoveringMetrizability
import Polyfold.Chapter19.StrongBundleTopology

/-!
# The topology of `|E_A|`, `|E_B|` and the transition squares (HWZ 2021 §19.8, pp. 956–957)

2021 Definition 19.8.20, Lemma 19.8.21 (p. 956) and Theorem 19.8.22 (pp. 956–957); also
Definition 19.6.7 (p. 897) for the strong bundle uniformizers `F̄` of `F̃` (Theorem 19.8.6 (5) for
`|E_B|`).  The uniformizers `Γ̂ : Ŵ → E_A` are not translation-groupoid uniformizers, so the
§19.6 arguments (Definition 19.6.7, Theorem 19.6.8, Proposition 19.6.9) are repeated here for
`Γ̂` and for `Γ`, following the printed proofs.

## What is formalized

* `isProperStrongBundleCoveringSquare_of_sheets`: Definition 19.8.19 from open sheets of the base
  map and local strong bundle isomorphisms (the sheets are shrunk to the local isomorphism
  neighbourhoods).
* `CoveringBasicConstruction.exists_sheets_pB`: `p : M(Ψ̂, Ψ̂') → M(Ψ, Ψ')` is a trivial covering,
  with sheets `ŝ⁻¹(U(y))` from the proper covering model of `Ψ̂` (Definition 17.8.4, Lemma 19.7.9).
* For `M(Γ, Γ')` (Theorem 19.8.6 (1)): `srcGmap`, `tgtGmap`, `isLocalHomeomorph_srcGmap`,
  `continuous_tgtGmap`, `tgtGmap_eq` (`t = pr₂ ∘ C ∘ H⁻¹`), `isStrongBundleMap_tgtGmap`,
  **`isLocalStrongBundleIso_tgtGmap`** (for coherent `𝓕`).
* `T̄_B` (Definition 19.6.7 for `(F̄, 𝓕)`): `NatOpenEB`, `natOpenEB_empty`, `natOpenEB_sUnion`,
  `natOpenEB_univ`, `natOpenEB_inter`, `natTopEB`, `isOpenEmbedding_orbitMap_Γ`,
  `continuous_orbitProjB`, **`metrizableSpace_natTopEB`** (Proposition 19.6.9 for `(F̄, 𝓕)`).
* For `M(Γ̂, Γ̂')`: `continuous_USq`, `continuous_mSq`, `continuous_pbarSq`,
  `isLocalHomeomorph_srcSq`, `tgtSq`, `tgtSq_eq`, `continuous_tgtSq`; the target analogue of
  Lemma 19.8.18, `TMapT`, `SMapT` (`t = T ∘ U`), `isStrongBundleMap_tgtSq`,
  **`isLocalStrongBundleIso_tgtSq`**.
* **Definition 19.8.20**: `NatOpenEA` (as printed), `natTopEA`; `natOpenEA_empty`,
  `natOpenEA_univ`, `natOpenEA_inter`, `natOpenEA_sUnion`; `isOpenEmbedding_orbitMap_Γh`
  (`|Γ̂| : |Ŵ| → |E_A|` is an open embedding), `orbitProj_preimage_range`
  (`|P_A|⁻¹(|Ψ̂(Ê)|) = |Γ̂(Ŵ)|`), `continuous_orbitProjA`, `metrizableSpace_orbitSpace_Wh`
  (Proposition 8.4.1), **`metrizableSpace_natTopEA`**, **`lemma_19_8_21_hyp`**.
* **`isProperSquare_pbarSq`** (the square `p̂` over `p` of Theorem 19.8.22 is a proper strong
  bundle covering square) and **`theorem_19_8_22_topology_hyp`** (the topologies, the square
  `p̂` and the local isomorphisms `s`, `t` of Theorem 19.8.22; the complete form is
  `SquareBasicConstruction.theorem_19_8_22_hyp`, `CoveringSquareFibredProper.lean`).

## Readings

* `IsCompatible` (the top target maps `t̂` are continuous), an added hypothesis, the reading of
  l. 44572 used for `T̄_{|A|}` and for `t̂` being a local sc-diffeomorphism, is a hypothesis of
  `lemma_19_8_21_hyp` and `theorem_19_8_22_topology_hyp` (hence `_hyp`); it holds for the example
  (`absSqBasic_isCompatible`).  Coherence, class uniformizers and the metrizability of `T_{|B|}`
  are the conditions of Definition 19.8.14.
* "Follow the proof of Theorem 19.6.8" (Lemma 19.8.21) is read as: `|Γ̂|` is an open embedding of
  `|Ŵ|`, `|Ŵ|` is metrizable by Proposition 8.4.1 (`|Ê|` is metrizable as an open subset of the
  metrizable `|A|`), and `|E_A|` is metrizable as a space over the metrizable `|A|` locally
  metrizable over open sets.
* "The orbit spaces of `A`, `E_A`, `B` and `E_B` have natural metrizable topologies" is read
  with `T_{|B|}` of `(F, 𝓕)`, `T̄_{|A|}` of Theorem 19.7.25, `T̄_B` of Definition 19.6.7 for
  `(F̄, 𝓕)` and `T̄_A` of Definition 19.8.20.
* "The local isomorphisms `s, t` between proper strong bundle covering squares" is read as: the
  source and target maps of `M(Γ̂, Γ̂')` and of `M(Γ, Γ')` are local strong bundle isomorphisms
  (over the local sc-diffeomorphisms `ŝ`, `t̂`, `s`, `t`).

The inversion `ι` as an isomorphism of squares and the unit and multiplication maps as strong
bundle maps of squares are in `CoveringSquareMultiplication.lean` and
`CoveringSquareFibredProper.lean`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

namespace Polyfold

noncomputable section

universe u

open Set Function Topology TopologicalSpace

/-! ### Proper strong bundle covering squares from sheets -/

section ProperSquareSheets

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {W : Type*} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {p : W → X}
  [∀ x, AddCommGroup (p ⁻¹' {x})] [∀ x, Module ℝ (p ⁻¹' {x})]
  {Xh : Type*} [TopologicalSpace Xh] [T2Space Xh] [ParacompactSpace Xh] {PXh : MPolyfold Xh}
  {Wh : Type*} [TopologicalSpace Wh] [T2Space Wh] [ParacompactSpace Wh] {ph : Wh → Xh}
  [∀ x, AddCommGroup (ph ⁻¹' {x})] [∀ x, Module ℝ (ph ⁻¹' {x})]

/-- **A proper strong bundle covering square from sheets** (Definition 19.8.19, read form): a
strong bundle map `â` over a surjective local sc-diffeomorphism `a` with finite fibres, which is
near every point a strong bundle isomorphism, and such that every `x` has an open `U ∋ x` with
`a⁻¹(U)` the disjoint union of open sets `U'(x̂ᵢ) ∋ x̂ᵢ`, `a⁻¹(x) = {x̂ᵢ}`, on which `a` is
injective.  (The sheets are shrunk to `U'(x̂ᵢ) ∩ a⁻¹(U₂)` with `U₂ ⊂ U` the intersection of the
images of the local isomorphism neighbourhoods.) -/
theorem isProperStrongBundleCoveringSquare_of_sheets {Bh : StrongBundle PXh ph}
    {B : StrongBundle PX p} {a : Xh → X} {ah : Wh → W} (h : Bh.IsStrongBundleMap B a ah)
    (hs : Surjective a) (hd : PXh.IsLocalScDiffeo PX a) (hfin : ∀ x, (a ⁻¹' {x}).Finite)
    (hloc : ∀ y, ∃ (U₀ : Set Xh) (U₀' : Set X), y ∈ U₀ ∧ Bh.IsStrongBundleIsoOn B h U₀ U₀')
    (hsheet : ∀ x, ∃ (U : Set X) (U' : Xh → Set Xh), IsOpen U ∧ x ∈ U ∧
      (a ⁻¹' {x}).PairwiseDisjoint U' ∧
      (∀ y ∈ a ⁻¹' {x}, y ∈ U' y ∧ IsOpen (U' y) ∧ InjOn a (U' y)) ∧
      a ⁻¹' U = ⋃ y ∈ a ⁻¹' {x}, U' y) :
    IsProperStrongBundleCoveringSquare Bh B a ah := by
  refine ⟨h, hs, hd, hfin, fun x => ?_⟩
  obtain ⟨U, U', hU, hxU, hdisj, hU', hpre⟩ := hsheet x
  choose! U₀ U₀' hy₀ hi₀ using hloc
  have hc : Continuous a := hd.isLocalHomeomorph.continuous
  set U₂ : Set X := U ∩ ⋂ y ∈ a ⁻¹' {x}, a '' (U' y ∩ U₀ y) with hU₂def
  have hU₂ : IsOpen U₂ := hU.inter ((hfin x).isOpen_biInter fun y hy => hd.isOpenMap _
    ((hU' y hy).2.1.inter (Classical.choose_spec (hi₀ y).isScDiffeoOn_base).isOpen_source))
  have hxU₂ : x ∈ U₂ := ⟨hxU, mem_iInter₂.2 fun y hy => ⟨y, ⟨(hU' y hy).1, hy₀ y⟩, hy⟩⟩
  refine ⟨U₂, fun y => U' y ∩ a ⁻¹' U₂, hU₂, hxU₂,
    hdisj.mono fun y => inter_subset_left, fun y hy => ⟨⟨(hU' y hy).1, ?_⟩, ?_⟩, ?_⟩
  · change a y ∈ U₂
    rw [show a y = x from hy]
    exact hxU₂
  · obtain ⟨g, hg⟩ := (hi₀ y).isScDiffeoOn_base
    have hsub : U' y ∩ a ⁻¹' U₂ ⊆ U₀ y := by
      rintro z ⟨hz1, hz2⟩
      obtain ⟨z', ⟨hz'1, hz'2⟩, hz'⟩ := mem_iInter₂.1 hz2.2 y hy
      rw [← (hU' y hy).2.2 hz'1 hz1 hz']
      exact hz'2
    have hopen : IsOpen (U' y ∩ a ⁻¹' U₂) := (hU' y hy).2.1.inter (hU₂.preimage hc)
    have hr := (hi₀ y).restrict hg hopen hsub
    have heq : U₀' y ∩ g ⁻¹' (U' y ∩ a ⁻¹' U₂) = U₂ := by
      ext z'
      constructor
      · rintro ⟨h1, h2⟩
        rw [← hg.right_inv z' h1]
        exact h2.2
      · intro hz'
        obtain ⟨z'', ⟨hz''1, hz''2⟩, rfl⟩ := mem_iInter₂.1 hz'.2 y hy
        refine ⟨hg.mapsTo hz''2, ?_⟩
        change g (a z'') ∈ U' y ∩ a ⁻¹' U₂
        rw [hg.left_inv z'' hz''2]
        exact ⟨hz''1, hz'⟩
    rw [heq] at hr
    exact hr
  · ext z
    simp only [mem_iUnion, mem_inter_iff, mem_preimage, exists_prop]
    constructor
    · intro hz
      have hzU : z ∈ a ⁻¹' U := hz.1
      rw [hpre] at hzU
      obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.1 hzU
      exact ⟨y, hy, hzy, hz⟩
    · rintro ⟨y, -, -, hz⟩
      exact hz

end ProperSquareSheets

namespace GroupoidalCategory

open GroupoidStr (TransitionSet)
open EpGroupoid EpGroupoid.Examples

variable {A B : GroupoidalCategory.{u}}

/-! ### The sheets of `p : M(Ψ̂, Ψ̂') → M(Ψ, Ψ')` -/

namespace CoveringBasicConstruction

variable {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr} (Bh : CoveringBasicConstruction P)

/-- **The sheets of `p : M(Ψ̂, Ψ̂') → M(Ψ, Ψ')`**: `p` is a trivial covering.  For `k` the sets
`U'(ĥ) = ŝ⁻¹(U(y_{s(ĥ)}))`, `ĥ ∈ p⁻¹(k)`, of the elements whose source lies in the sheet
`U(y)` of the proper covering model containing `s(ĥ)` (Definition 17.8.4 (2)) are open, pairwise
disjoint, contain `ĥ`, `p` is injective on each of them (Lemma 19.7.10), and they cover
`M(Ψ̂, Ψ̂')`. -/
theorem exists_sheets_pB (hP : IsFiniteToOneCovering P) (x y : Bh.hatU.Unif) (k : Bh.MB x y) :
    ∃ U' : Bh.MHat x y → Set (Bh.MHat x y), (Bh.pB x y ⁻¹' {k}).PairwiseDisjoint U' ∧
      (∀ a ∈ Bh.pB x y ⁻¹' {k}, a ∈ U' a ∧ IsOpen (U' a) ∧ InjOn (Bh.pB x y) (U' a)) ∧
      Bh.pB x y ⁻¹' univ = ⋃ a ∈ Bh.pB x y ⁻¹' {k}, U' a := by
  set M := x.Ψh.model
  have hbij := fun h : x.Ψh.Ψ.Trans y.Ψh.Ψ => ((x.Ψh.lemma_19_7_9 y.Ψh hP).2 h).1
  have hsrc : Continuous (Bh.srcHat x y) := (Bh.isLocalHomeomorph_srcHat hP x y).continuous
  refine ⟨fun a => Bh.srcHat x y ⁻¹' M.U (M.sheetIndex (Bh.srcHat x y a)), ?_, fun a _ =>
    ⟨M.mem_U_sheetIndex _, (M.isOpen_U (M.sheetIndex_mem _)).preimage hsrc, ?_⟩, ?_⟩
  · intro a ha a' ha' hne
    by_cases hi : M.sheetIndex (Bh.srcHat x y a) = M.sheetIndex (Bh.srcHat x y a')
    · refine absurd ?_ hne
      have hs : Bh.srcHat x y a = Bh.srcHat x y a' := M.eq_of_obj_eq hi (by
        rw [Bh.τ_srcHat, Bh.τ_srcHat, show Bh.pB x y a = k from ha,
          show Bh.pB x y a' = k from ha'])
      exact (hbij k).injOn ha ha' hs
    · exact (M.pairwiseDisjoint_U (M.sheetIndex_mem _) (M.sheetIndex_mem _) hi).preimage _
  · intro b hb b' hb' hbb
    have hi : M.sheetIndex (Bh.srcHat x y b) = M.sheetIndex (Bh.srcHat x y b') :=
      (M.sheetIndex_eq (M.sheetIndex_mem _) hb).trans
        (M.sheetIndex_eq (M.sheetIndex_mem _) hb').symm
    have hs : Bh.srcHat x y b = Bh.srcHat x y b' := M.eq_of_obj_eq hi (by
      rw [Bh.τ_srcHat, Bh.τ_srcHat, hbb])
    exact (hbij (Bh.pB x y b)).injOn rfl hbb.symm hs
  · ext b
    simp only [mem_preimage, mem_univ, mem_iUnion, exists_prop, true_iff]
    set yb := M.sheetIndex (Bh.srcHat x y b)
    have hyb : yb ∈ M.fiber := M.sheetIndex_mem _
    obtain ⟨a, ha, has⟩ := (hbij k).surjOn (show M.σ yb (k : x.Ψh.Ψ.Trans y.Ψh.Ψ).src ∈
      x.Ψh.τ.obj ⁻¹' {(k : x.Ψh.Ψ.Trans y.Ψh.Ψ).src} from M.obj_σ hyb _)
    have h1 : M.sheetIndex (Bh.srcHat x y a) = yb := M.sheetIndex_eq hyb (by
      rw [show Bh.srcHat x y a = M.σ yb _ from has]
      exact M.σ_mem_U hyb _)
    refine ⟨a, ha, ?_⟩
    rw [h1]
    exact M.mem_U_sheetIndex _

end CoveringBasicConstruction

/-! ### The structural maps of `M(Γ, Γ')` -/

namespace PullbackUniformizerConstruction

variable {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr} {μ : B.BanFunctor}
  (Ft : PullbackUniformizerConstruction P μ)
  (𝓕 : Ft.toUniformizerConstruction.TransitionConstruction) (x y : Ft.Unif)

/-- The source map `s : M(Γ, Γ') → W`. -/
def srcGmap (h : Ft.MG 𝓕 x y) : x.x.bun.W := (h : x.x.TransG y.x).src

/-- The target map `t : M(Γ, Γ') → W'`. -/
def tgtGmap (h : Ft.MG 𝓕 x y) : y.x.bun.W := (h : x.x.TransG y.x).tgt

/-- **`s : M(Γ, Γ') → W` is a local homeomorphism**: it is `H⁻¹` followed by the projection
`M(Ψ, Ψ') ₛ×_Q W → W`, a local homeomorphism over the local sc-diffeomorphism `s`. -/
theorem isLocalHomeomorph_srcGmap : IsLocalHomeomorph (Ft.srcGmap 𝓕 x y) := by
  have h1 : IsLocalHomeomorph (pullbackProj' x.x.bun.Q (Ft.srcB 𝓕 x y)) := by
    intro z
    obtain ⟨V, V', σ, hk, hd⟩ :=
      (Ft.toCBC 𝓕).isLocalScDiffeo_srcB' x.toHat y.toHat (z : Ft.MBase 𝓕 x y × x.x.bun.W).1
    obtain ⟨Ψ, hΨ⟩ := (x.x.bun.bundle.isStrongBundleIsoOn_pullbackProj'
      (Ft.isScSmoothMap_srcB 𝓕 x y) hd (z : Ft.MBase 𝓕 x y × x.x.bun.W).1).isScDiffeoOn_zero
    exact ⟨hΨ.toOpenPartialHomeomorph, hk, rfl⟩
  exact h1.comp (Ft.altHHomeo 𝓕 x y).symm.isLocalHomeomorph

theorem altH'inv_eq_altC (h : x.x.TransG y.x) :
    Ft.altH'inv 𝓕 x y h = Ft.altC 𝓕 x y (Ft.altHinv 𝓕 x y h) := by
  rw [altC, altH_altHinv]

/-- **`t : M(Γ, Γ') → W'` is continuous** for a coherent `𝓕`: `t = pr₂ ∘ C ∘ H⁻¹`. -/
theorem continuous_tgtGmap (hcoh : Ft.IsCoherent 𝓕) : Continuous (Ft.tgtGmap 𝓕 x y) := by
  obtain ⟨hm, -⟩ := hcoh x y
  have e : Ft.tgtGmap 𝓕 x y = fun h =>
      ((Ft.altC 𝓕 x y (Ft.altHinv 𝓕 x y h) : Ft.MBase 𝓕 x y × y.x.bun.W)).2 := by
    funext h
    exact congrArg (fun z : Ft.TgtPB 𝓕 x y => (z : Ft.MBase 𝓕 x y × y.x.bun.W).2)
      (Ft.altH'inv_eq_altC 𝓕 x y h)
  rw [e]
  exact continuous_snd.comp (continuous_subtype_val.comp
    (hm.continuous.comp continuous_induced_dom))

/-- `t = pr₂ ∘ C ∘ H⁻¹` on `M(Γ, Γ')`. -/
theorem tgtGmap_eq : Ft.tgtGmap 𝓕 x y = pullbackProj' y.x.bun.Q (Ft.tgtB 𝓕 x y) ∘
    Ft.altC 𝓕 x y ∘ (Ft.altHHomeo 𝓕 x y).symm := by
  funext h
  exact congrArg (fun z : Ft.TgtPB 𝓕 x y => (z : Ft.MBase 𝓕 x y × y.x.bun.W).2)
    (Ft.altH'inv_eq_altC 𝓕 x y h)

/-- **`t : M(Γ, Γ') → W'` is a strong bundle map covering `t : M(Ψ, Ψ') → O'`**, for a coherent
`𝓕`. -/
theorem isStrongBundleMap_tgtGmap (hcoh : Ft.IsCoherent 𝓕) :
    (Ft.bundleG 𝓕 x y).IsStrongBundleMap y.x.bun.bundle (Ft.tgtB 𝓕 x y) (Ft.tgtGmap 𝓕 x y) := by
  obtain ⟨hm, -⟩ := hcoh x y
  rw [Ft.tgtGmap_eq 𝓕 x y]
  exact (y.x.bun.bundle.isStrongBundleMap_pullbackProj' (Ft.isScSmoothMap_tgtB 𝓕 x y)).comp
    (hm.comp (Ft.isStrongBundleIso_altH 𝓕 x y).invMap)

/-- **`t : M(Γ, Γ') → W'` is a local strong bundle isomorphism** (Theorem 19.6.13 for the
members of `F̃`), for a coherent `𝓕`: `C` and `H⁻¹` are strong bundle isomorphisms and the
projection `M(Ψ, Ψ') ₜ×_{Q'} W' → W'` is one over the local sc-diffeomorphism `t`. -/
theorem isLocalStrongBundleIso_tgtGmap (hcoh : Ft.IsCoherent 𝓕) (k : Ft.MBase 𝓕 x y) :
    ∃ (U : Set (Ft.MBase 𝓕 x y)) (U' : Set y.x.Ψh.Ψ.O), k ∈ U ∧
      (Ft.bundleG 𝓕 x y).IsStrongBundleIsoOn y.x.bun.bundle
        (Ft.isStrongBundleMap_tgtGmap 𝓕 x y hcoh) U U' := by
  obtain ⟨hm, hiso⟩ := hcoh x y
  obtain ⟨V, V', σ, hk, hd⟩ :=
    (Ft.toCBC 𝓕).toBasic.rep.isLocalScDiffeo_tgt x.toHat.toUnif y.toHat.toUnif k
  have hπ := y.x.bun.bundle.isStrongBundleIsoOn_pullbackProj' (Ft.isScSmoothMap_tgtB 𝓕 x y) hd k
  obtain ⟨U₁, U₁', hk₁, h₁⟩ := hπ.exists_comp hiso (mem_univ k) hk
  obtain ⟨U₂, U₂', hk₂, h₂⟩ := h₁.exists_comp
    (Ft.isStrongBundleIso_altH 𝓕 x y).symm.isStrongBundleIsoOn_univ (mem_univ k) hk₁
  exact ⟨U₂, U₂', hk₂, StrongBundle.isStrongBundleIsoOn_of_eqOn h₂ (fun _ _ => rfl)
    fun z _ => (congrFun (Ft.tgtGmap_eq 𝓕 x y) z).symm⟩

/-! ### The natural topology `T̄_B` on `|E_B|` (Definition 19.6.7 for `(F̄, 𝓕)`) -/

/-- **2021 Definition 19.6.7, p. 897, for the strong bundle uniformizers `F̄` of `F̃`**
(Theorem 19.8.6 (5), Theorem 19.8.22): `U ⊂ |E_B|` is open if for every `z̄ ∈ U` there are an
object `β` with `|β| = |P_B|(z̄)`, a member `(Ψ, Ψ̂, Γ)` of `F̃(β)`, a `w ∈ W` with `|Γ(w)| = z̄`
and an open `V ∋ w` with `|Γ(V)| ⊂ U`. -/
def NatOpenEB (W : Set μ.cat.OrbitSpace) : Prop :=
  ∀ z ∈ W, ∃ β : B.Obj, B.π β = μ.orbitProj z ∧ ∃ x ∈ Ft.F β, ∃ w : x.bun.W,
    μ.cat.π (x.bun.functor.obj w) = z ∧ ∃ V : Set x.bun.W, IsOpen V ∧ w ∈ V ∧
      (fun q => μ.cat.π (x.bun.functor.obj q)) '' V ⊆ W

theorem natOpenEB_empty : Ft.NatOpenEB ∅ := fun _ hz => absurd hz (notMem_empty _)

theorem natOpenEB_sUnion {T : Set (Set μ.cat.OrbitSpace)} (hT : ∀ W ∈ T, Ft.NatOpenEB W) :
    Ft.NatOpenEB (⋃₀ T) := by
  rintro z ⟨W, hW, hz⟩
  obtain ⟨β, hβ, x, hx, w, hw, V, hV, hwV, hsub⟩ := hT W hW z hz
  exact ⟨β, hβ, x, hx, w, hw, V, hV, hwV, hsub.trans (subset_sUnion_of_mem hW)⟩

variable {Ft}

/-- Every `z̄` with `|P_B|(z̄) = |β|` is `|Γ(w)|` for some `w`, for `(Ψ, Ψ̂, Γ)` at `β`. -/
theorem exists_Γ_of_pt {β : B.Obj} (x : PullbackUniformizer P μ β) {z : μ.cat.OrbitSpace}
    (hz : B.π β = μ.orbitProj z) : ∃ w : x.bun.W, μ.cat.π (x.bun.functor.obj w) = z := by
  induction z using Quotient.inductionOn with
  | h v =>
  obtain ⟨v', hv', hvv'⟩ := μ.exists_mem_fiber_of_π_eq (e := v)
    (α := x.Ψh.Ψ.obj x.Ψh.model.pt) (by rw [x.Ψh.obj_pt]; exact hz.symm)
  let w : x.bun.Q ⁻¹' {x.Ψh.model.pt} := (x.bun.fiberCLE _).symm ⟨v', hv'⟩
  have hw : x.bun.functor.obj w = v' := by
    rw [← x.bun.fiberCLE_apply _ w, ContinuousLinearEquiv.apply_symm_apply]
  exact ⟨w, by rw [hw, hvv']; rfl⟩

/-- An isomorphism `Γ(w) ≅ Γ'(w')` gives an element of `M(Γ, Γ')` from `w` to `w'`. -/
theorem exists_G_of_π_eq {x y : Ft.Unif} {w : x.x.bun.W} {w' : y.x.bun.W}
    (h : μ.cat.π (x.x.bun.functor.obj w) = μ.cat.π (y.x.bun.functor.obj w')) :
    ∃ a : Ft.MG 𝓕 x y, Ft.srcGmap 𝓕 x y a = w ∧ Ft.tgtGmap 𝓕 x y a = w' := by
  obtain ⟨φ, hs, ht⟩ := (μ.cat.π_eq_π_iff).1 h
  exact ⟨(⟨w, φ, w', hs, ht⟩ : x.x.TransG y.x), rfl, rfl⟩

variable (Ft)

/-- Every class of `B` contains the base object `β` of a member of `F̃`. -/
theorem exists_unifB (hU : (Ft.toCBC 𝓕).HasClassUniformizers) (z : B.OrbitSpace) :
    ∃ x : Ft.Unif, B.π x.β = z := by
  obtain ⟨β, hβ, Ψh, ⟨x, hx, rfl⟩⟩ := hU z
  exact ⟨⟨β, x, hx⟩, hβ⟩

/-- **The step of the proof of Theorem 19.6.8 (1) for `M(Γ, Γ')`**: for `h ∈ M(Γ, Γ')` and an
open `V' ∋ t(h)`, `N = s(t⁻¹(V')) ∋ s(h)` is open with `|Γ(N)| ⊂ |Γ'(V')|`. -/
theorem exists_nbhd_G (hcoh : Ft.IsCoherent 𝓕) (h : Ft.MG 𝓕 x y) {V' : Set y.x.bun.W}
    (hV' : IsOpen V') (ht : Ft.tgtGmap 𝓕 x y h ∈ V') :
    ∃ N : Set x.x.bun.W, IsOpen N ∧ Ft.srcGmap 𝓕 x y h ∈ N ∧
      ∀ d ∈ N, ∃ d' ∈ V',
        μ.cat.π (x.x.bun.functor.obj d) = μ.cat.π (y.x.bun.functor.obj d') := by
  refine ⟨Ft.srcGmap 𝓕 x y '' (Ft.tgtGmap 𝓕 x y ⁻¹' V'),
    (Ft.isLocalHomeomorph_srcGmap 𝓕 x y).isOpenMap _
      (hV'.preimage (Ft.continuous_tgtGmap 𝓕 x y hcoh)), ⟨h, ht, rfl⟩, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨Ft.tgtGmap 𝓕 x y b, hb, (μ.cat.π_eq_π_iff).2
    ⟨(b : x.x.TransG y.x).mor, (b : x.x.TransG y.x).src_mor, (b : x.x.TransG y.x).tgt_mor⟩⟩

theorem natOpenEB_univ (hU : (Ft.toCBC 𝓕).HasClassUniformizers) : Ft.NatOpenEB univ := by
  intro z _
  obtain ⟨x, hx⟩ := Ft.exists_unifB 𝓕 hU (μ.orbitProj z)
  obtain ⟨w, hw⟩ := exists_Γ_of_pt x.x hx
  exact ⟨x.β, hx, x.x, x.mem, w, hw, univ, isOpen_univ, mem_univ _, subset_univ _⟩

theorem natOpenEB_inter (hcoh : Ft.IsCoherent 𝓕) {W₁ W₂ : Set μ.cat.OrbitSpace}
    (h₁ : Ft.NatOpenEB W₁) (h₂ : Ft.NatOpenEB W₂) : Ft.NatOpenEB (W₁ ∩ W₂) := by
  rintro z ⟨hz₁, hz₂⟩
  obtain ⟨β₁, hβ₁, x₁, hx₁, w₁, hw₁, V₁, hV₁, hwV₁, hsub₁⟩ := h₁ z hz₁
  obtain ⟨β₂, -, x₂, hx₂, w₂, hw₂, V₂, hV₂, hwV₂, hsub₂⟩ := h₂ z hz₂
  obtain ⟨a, ha₁, ha₂⟩ := exists_G_of_π_eq (𝓕 := 𝓕) (x := ⟨β₁, x₁, hx₁⟩) (y := ⟨β₂, x₂, hx₂⟩)
    (hw₁.trans hw₂.symm)
  obtain ⟨N, hN, haN, hNf⟩ := Ft.exists_nbhd_G 𝓕 ⟨β₁, x₁, hx₁⟩ ⟨β₂, x₂, hx₂⟩ hcoh a hV₂
    (ha₂ ▸ hwV₂)
  refine ⟨β₁, hβ₁, x₁, hx₁, w₁, hw₁, N ∩ V₁, hN.inter hV₁, ⟨ha₁ ▸ haN, hwV₁⟩, ?_⟩
  rintro _ ⟨d, ⟨hdN, hdV⟩, rfl⟩
  obtain ⟨d', hd', hdd'⟩ := hNf d hdN
  refine ⟨hsub₁ ⟨d, hdV, rfl⟩, ?_⟩
  change μ.cat.π (x₁.bun.functor.obj d) ∈ W₂
  rw [show μ.cat.π (x₁.bun.functor.obj d) = μ.cat.π (x₂.bun.functor.obj d') from hdd']
  exact hsub₂ ⟨d', hd', rfl⟩

/-- **The natural topology `T̄_B` on `|E_B|`** (Definition 19.6.7 for `(F̄, 𝓕)`), for a
coherent `𝓕` with class uniformizers. -/
abbrev natTopEB (hcoh : Ft.IsCoherent 𝓕) (hU : (Ft.toCBC 𝓕).HasClassUniformizers) :
    TopologicalSpace μ.cat.OrbitSpace where
  IsOpen := Ft.NatOpenEB
  isOpen_univ := Ft.natOpenEB_univ 𝓕 hU
  isOpen_inter _ _ := Ft.natOpenEB_inter 𝓕 hcoh
  isOpen_sUnion _ := Ft.natOpenEB_sUnion

theorem isOpen_image_Γ (hcoh : Ft.IsCoherent 𝓕) (hU : (Ft.toCBC 𝓕).HasClassUniformizers)
    (x : Ft.Unif) {V : Set x.x.bun.W} (hV : IsOpen V) :
    Ft.NatOpenEB ((fun d => μ.cat.π (x.x.bun.functor.obj d)) '' V) := by
  rintro _ ⟨d, hdV, rfl⟩
  obtain ⟨y, hy⟩ := Ft.exists_unifB 𝓕 hU (μ.orbitProj (μ.cat.π (x.x.bun.functor.obj d)))
  obtain ⟨e', he'⟩ := exists_Γ_of_pt y.x hy
  obtain ⟨a, ha₁, ha₂⟩ := exists_G_of_π_eq (𝓕 := 𝓕) (x := y) (y := x) he'
  obtain ⟨N, hN, haN, hNf⟩ := Ft.exists_nbhd_G 𝓕 y x hcoh a hV (ha₂ ▸ hdV)
  refine ⟨y.β, hy, y.x, y.mem, e', he', N, hN, ha₁ ▸ haN, ?_⟩
  rintro _ ⟨d₁, hd₁, rfl⟩
  obtain ⟨d₂, hd₂, h⟩ := hNf d₁ hd₁
  exact ⟨d₂, hd₂, h.symm⟩

theorem continuous_π_Γ (hcoh : Ft.IsCoherent 𝓕) (hU : (Ft.toCBC 𝓕).HasClassUniformizers)
    (x : Ft.Unif) :
    Continuous[_, Ft.natTopEB 𝓕 hcoh hU] fun d : x.x.bun.W => μ.cat.π (x.x.bun.functor.obj d) := by
  let _inst := Ft.natTopEB 𝓕 hcoh hU
  refine continuous_def.2 fun W hW => isOpen_iff_forall_mem_open.2 fun d hd => ?_
  obtain ⟨β', -, x', hx', e', he', V', hV', heV', hsub'⟩ := hW _ hd
  obtain ⟨a, ha₁, ha₂⟩ := exists_G_of_π_eq (𝓕 := 𝓕) (x := x) (y := ⟨β', x', hx'⟩)
    (he'.symm : μ.cat.π (x.x.bun.functor.obj d) = _)
  obtain ⟨N, hN, haN, hNf⟩ := Ft.exists_nbhd_G 𝓕 x ⟨β', x', hx'⟩ hcoh a hV' (ha₂ ▸ heV')
  refine ⟨N, fun d₁ hd₁ => ?_, hN, ha₁ ▸ haN⟩
  obtain ⟨d₂, hd₂, h⟩ := hNf d₁ hd₁
  change μ.cat.π (x.x.bun.functor.obj d₁) ∈ W
  rw [h]
  exact hsub' ⟨d₂, hd₂, rfl⟩

/-- **`|Γ| : |G ⋉ W| → |E_B|` is a homeomorphism onto an open subset** (Theorem 19.6.8 (3) for
`(F̄, 𝓕)`). -/
theorem isOpenEmbedding_orbitMap_Γ (hcoh : Ft.IsCoherent 𝓕)
    (hU : (Ft.toCBC 𝓕).HasClassUniformizers) (x : Ft.Unif) :
    @IsOpenEmbedding _ _ _ (Ft.natTopEB 𝓕 hcoh hU) x.x.bun.functor.orbitMap := by
  let _inst := Ft.natTopEB 𝓕 hcoh hU
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact continuous_quot_lift _ (Ft.continuous_π_Γ 𝓕 hcoh hU x)
  · intro z z' h
    induction z using Quotient.inductionOn with
    | h e =>
    induction z' using Quotient.inductionOn with
    | h e' =>
    obtain ⟨φ, hφs, hφt⟩ := (μ.cat.π_eq_π_iff).1 h
    obtain ⟨ψ, hψs, hψt, -⟩ := (GroupoidFunctor.full_iff _).1 x.x.bun.full e e' φ hφs hφt
    exact (GroupoidStr.π_eq_π_iff _).2 ⟨ψ, hψs, hψt⟩
  · intro W hW
    have : x.x.bun.functor.orbitMap '' W =
        (fun d => μ.cat.π (x.x.bun.functor.obj d)) ''
          ((GroupoidStr.translation x.x.Ψh.Ψ.G x.x.bun.W).π ⁻¹' W) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        induction w using Quotient.inductionOn with
        | h e => exact ⟨e, hw, rfl⟩
      · rintro ⟨e, he, rfl⟩
        exact ⟨_, he, rfl⟩
    rw [this]
    exact Ft.isOpen_image_Γ 𝓕 hcoh hU x (hW.preimage continuous_quot_mk)

/-- **`|P_B| : (|E_B|, T̄_B) → (|B|, T_{|B|})` is continuous** (Theorem 19.6.8 (5) for
`(F̄, 𝓕)`). -/
theorem continuous_orbitProjB (hcoh : Ft.IsCoherent 𝓕) (hU : (Ft.toCBC 𝓕).HasClassUniformizers) :
    Continuous[Ft.natTopEB 𝓕 hcoh hU, (Ft.toCBC 𝓕).toBasic.natTop hU.toBasic] μ.orbitProj := by
  let _i₁ := Ft.natTopEB 𝓕 hcoh hU
  let _i₂ := (Ft.toCBC 𝓕).toBasic.natTop hU.toBasic
  refine continuous_def.2 fun W hW => ?_
  intro z hz
  obtain ⟨x, hx⟩ := Ft.exists_unifB 𝓕 hU (μ.orbitProj z)
  obtain ⟨w, hw⟩ := exists_Γ_of_pt x.x hx
  have hc := (Ft.toCBC 𝓕).toBasic.continuous_π_obj hU.toBasic (α := x.β) (Ψ := x.x.Ψh.Ψ)
    ⟨x.x.Ψh, ⟨x.x, x.mem, rfl⟩, rfl⟩
  refine ⟨x.β, hx, x.x, x.mem, w, hw,
    x.x.bun.Q ⁻¹' ((fun q => B.π (x.x.Ψh.Ψ.obj q)) ⁻¹' W),
    (hW.preimage hc).preimage x.x.bun.bundle.continuous, ?_, ?_⟩
  · change B.π (x.x.Ψh.Ψ.obj (x.x.bun.Q w)) ∈ W
    rw [← x.x.bun.P_obj w]
    change μ.orbitProj (μ.cat.π (x.x.bun.functor.obj w)) ∈ W
    rw [hw]
    exact hz
  · rintro _ ⟨q, hq, rfl⟩
    change B.π (μ.P (x.x.bun.functor.obj q)) ∈ W
    rw [x.x.bun.P_obj]
    exact hq

/-- **`T̄_B` is metrizable** (Proposition 19.6.9 `⇒` for `(F̄, 𝓕)`): `|P_B|⁻¹(|Ψ(O)|) = |Γ(W)|`
is homeomorphic to the metrizable `G\W`, and `|E_B|` is metrizable over the metrizable `|B|`. -/
theorem metrizableSpace_natTopEB (hcoh : Ft.IsCoherent 𝓕)
    (hU : (Ft.toCBC 𝓕).HasClassUniformizers)
    (hm : @MetrizableSpace _ ((Ft.toCBC 𝓕).toBasic.natTop hU.toBasic)) :
    @MetrizableSpace _ (Ft.natTopEB 𝓕 hcoh hU) := by
  let _i := Ft.natTopEB 𝓕 hcoh hU
  let _iB := (Ft.toCBC 𝓕).toBasic.natTop hU.toBasic
  have : ParacompactSpace B.OrbitSpace := paracompactSpace_of_metrizableSpace _
  refine metrizableSpace_of_pullback μ.orbitProj (Ft.continuous_orbitProjB 𝓕 hcoh hU)
    fun z => ?_
  obtain ⟨x, hx⟩ := Ft.exists_unifB 𝓕 hU z
  have hΨ : x.x.Ψh.Ψ ∈ (Ft.toCBC 𝓕).toBasic.U.F x.β := ⟨x.x.Ψh, ⟨x.x, x.mem, rfl⟩, rfl⟩
  have hset := x.x.str.orbitProj_preimage_range
  rw [← image_univ] at hset
  refine ⟨_, (Ft.toCBC 𝓕).toBasic.theorem_19_2_2_two hU.toBasic hΨ isOpen_univ,
    ⟨x.x.Ψh.model.pt, trivial, (congrArg B.π x.x.Ψh.obj_pt).trans hx⟩, ?_⟩
  rw [hset, ← StrongBundleStr.range_orbitMap (Ψe := x.x.Γ)]
  have := metrizableSpace_translation_orbitSpace (fun g : x.x.Ψh.Ψ.G =>
    (x.x.bun.isStrongBundleMap_smul g).isScSmoothMap)
  exact (Ft.isOpenEmbedding_orbitMap_Γ 𝓕 hcoh hU x).isEmbedding.toHomeomorph.symm.isEmbedding
    |>.metrizableSpace

end PullbackUniformizerConstruction

/-! ### The structural maps of `M(Γ̂, Γ̂')` -/

namespace SquareUniformizerConstruction

variable {S : BundleCoveringSquare A B} (Ft : SquareUniformizerConstruction S)
  (𝓕 : Ft.toPullback.toUniformizerConstruction.TransitionConstruction) (X Y : Ft.Unif)

theorem continuous_USq : Continuous (Ft.USq 𝓕 X Y) := continuous_induced_dom

theorem continuous_mSq : Continuous (Ft.mSq 𝓕 X Y) :=
  continuous_fst.comp (continuous_subtype_val.comp (Ft.continuous_USq 𝓕 X Y))

theorem continuous_pbarSq : Continuous (Ft.pbarSq 𝓕 X Y) :=
  continuous_snd.comp (continuous_subtype_val.comp (Ft.continuous_USq 𝓕 X Y))

/-- **`s : M(Γ̂, Γ̂') → Ŵ` is a local homeomorphism** (it is a local strong bundle isomorphism,
`isLocalStrongBundleIso_srcSq`). -/
theorem isLocalHomeomorph_srcSq : IsLocalHomeomorph (Ft.srcSq 𝓕 X Y) := by
  intro h
  obtain ⟨U, U', ha, hi⟩ := Ft.isLocalStrongBundleIso_srcSq 𝓕 X Y (Ft.mSq 𝓕 X Y h)
  obtain ⟨Ψ, hΨ⟩ := hi.isScDiffeoOn_zero
  exact ⟨hΨ.toOpenPartialHomeomorph, ha, rfl⟩

/-- The target map `t : M(Γ̂, Γ̂') → Ŵ'`, `(ŵ, (φ̂, Â(ŵ)), ŵ') ↦ ŵ'`. -/
def tgtSq (h : Ft.MSq 𝓕 X Y) : Y.x.K.Wh := h.toTrans.tgt

/-- `t(h)` is the point over `t̂(m̂ h)` with `Ξ'(t(h)) = t(p̂ h)`. -/
theorem tgtSq_eq (h : Ft.MSq 𝓕 X Y) : Ft.tgtSq 𝓕 X Y h = Y.x.K.liftKinv
    ⟨((Ft.mSq 𝓕 X Y h : X.x.Ψh.Trans Y.x.Ψh).tgt,
      Ft.toPullback.tgtGmap 𝓕 X.toPU Y.toPU (Ft.pbarSq 𝓕 X Y h)), Y.x.K.Q_Ξ _⟩ :=
  (Y.x.K.liftPt_eq _ rfl rfl).symm

/-- **`t : M(Γ̂, Γ̂') → Ŵ'` is continuous** for a coherent `𝓕` with continuous top target maps
`t̂` (`IsCompatible`). -/
theorem continuous_tgtSq (hcoh : Ft.toPullback.IsCoherent 𝓕)
    (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) : Continuous (Ft.tgtSq 𝓕 X Y) := by
  rw [show Ft.tgtSq 𝓕 X Y = _ from funext (Ft.tgtSq_eq 𝓕 X Y)]
  refine Y.x.K.isStrongBundleIso_liftK.invMap.continuous.comp (Continuous.subtype_mk ?_ _)
  exact ((hC X.toPU.toHat Y.toPU.toHat).comp (Ft.continuous_mSq 𝓕 X Y)).prodMk
    ((Ft.toPullback.continuous_tgtGmap 𝓕 X.toPU Y.toPU hcoh).comp (Ft.continuous_pbarSq 𝓕 X Y))

/-! ### The target map `t : M(Γ̂, Γ̂') → Ŵ'` (Theorem 19.8.22) -/

/-- The top target `t̂ : M(Ψ̂, Ψ̂') → Ê'`, `(ê, φ̂, ê') ↦ ê'`. -/
abbrev tgtH (a : Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU) : Y.toPU.x.Ψh.ObjE :=
  (Ft.toPullback.toCBC 𝓕).tgtHat X.toPU.toHat Y.toPU.toHat a

theorem isLocalScDiffeo_tgtH (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) :
    (Ft.toPullback.hatPoly 𝓕 X.toPU Y.toPU).IsLocalScDiffeo Y.toPU.x.Ψh.E.PObj (Ft.tgtH 𝓕 X Y) :=
  (Ft.toPullback.toCBC 𝓕).isLocalScDiffeo_tgtHat Fact.out hC X.toPU.toHat Y.toPU.toHat

/-- `(ê', w')` for `((ê, φ̂, ê'), (w, (φ, A(w)), w')) ∈ p*M(Γ, Γ')`, a point of `τ'*W'`. -/
def TMapT : Ft.toPullback.PB 𝓕 X.toPU Y.toPU → pullbackSpace Y.toPU.x.bun.Q Y.toPU.x.Ψh.τ.obj :=
  pullbackPair Y.toPU.x.bun.Q Y.toPU.x.Ψh.τ.obj
    (Ft.tgtH 𝓕 X Y ∘ pullbackProj (Ft.toPullback.mGmap 𝓕 X.toPU Y.toPU)
      (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU))
    (Ft.toPullback.tgtGmap 𝓕 X.toPU Y.toPU ∘ pullbackProj' (Ft.toPullback.mGmap 𝓕 X.toPU Y.toPU)
      (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU))
    fun z => congrArg TransitionSet.tgt z.2

theorem isStrongBundleMap_tgtG_pullbackProj' (hcoh : Ft.toPullback.IsCoherent 𝓕) :
    (Ft.toPullback.pullBundle 𝓕 X.toPU Y.toPU).IsStrongBundleMap Y.x.K.BW
      (Y.toPU.x.Ψh.τ.obj ∘ Ft.tgtH 𝓕 X Y)
      (Ft.toPullback.tgtGmap 𝓕 X.toPU Y.toPU ∘ pullbackProj'
        (Ft.toPullback.mGmap 𝓕 X.toPU Y.toPU) (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU)) :=
  (Ft.toPullback.isStrongBundleMap_tgtGmap 𝓕 X.toPU Y.toPU hcoh).comp
    ((Ft.toPullback.bundleG 𝓕 X.toPU Y.toPU).isStrongBundleMap_pullbackProj'
      (Ft.toPullback.isLocalScDiffeo_pBmap 𝓕 X.toPU Y.toPU).isScSmoothMap)

theorem isStrongBundleMap_TMapT (hcoh : Ft.toPullback.IsCoherent 𝓕)
    (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) :
    (Ft.toPullback.pullBundle 𝓕 X.toPU Y.toPU).IsStrongBundleMap
      (Y.toPU.x.bun.bundle.pullback Y.toPU.x.Ψh.τ.isScSmoothMap_obj) (Ft.tgtH 𝓕 X Y)
      (Ft.TMapT 𝓕 X Y) :=
  Y.toPU.x.bun.bundle.isStrongBundleMap_pullbackPair Y.toPU.x.Ψh.τ.isScSmoothMap_obj
    (Ft.isLocalScDiffeo_tgtH 𝓕 X Y hC).isScSmoothMap
    (Ft.isStrongBundleMap_tgtG_pullbackProj' 𝓕 X Y hcoh)

/-- `(ê', w') ↦ (ê', w')` is near every point a strong bundle isomorphism covering `t̂`: its
composition with the projection `τ'*W' → W'` is `t ∘ π`, and `t : M(Γ, Γ') → W'` and the
projections are local strong bundle isomorphisms. -/
theorem isLocalStrongBundleIso_TMapT (hcoh : Ft.toPullback.IsCoherent 𝓕)
    (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) (a : Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU) :
    ∃ (U : Set (Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU)) (U' : Set Y.toPU.x.Ψh.ObjE), a ∈ U ∧
      (Ft.toPullback.pullBundle 𝓕 X.toPU Y.toPU).IsStrongBundleIsoOn
        (Y.toPU.x.bun.bundle.pullback Y.toPU.x.Ψh.τ.isScSmoothMap_obj)
        (Ft.isStrongBundleMap_TMapT 𝓕 X Y hcoh hC) U U' := by
  obtain ⟨U₁, U₁', σ₁, ha, hd₁⟩ := Ft.toPullback.isLocalScDiffeo_pBmap 𝓕 X.toPU Y.toPU a
  have hπ₁ := (Ft.toPullback.bundleG 𝓕 X.toPU Y.toPU).isStrongBundleIsoOn_pullbackProj'
    (Ft.toPullback.isLocalScDiffeo_pBmap 𝓕 X.toPU Y.toPU).isScSmoothMap hd₁ a
  obtain ⟨U₂, U₂', hk, hs⟩ := Ft.toPullback.isLocalStrongBundleIso_tgtGmap 𝓕 X.toPU Y.toPU hcoh
    (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU a)
  obtain ⟨U₀, U₀'', ha₀, hc₀⟩ := hs.exists_comp hπ₁ ha hk
  obtain ⟨V, V', σ, hV, hd⟩ := Y.toPU.x.Ψh.model.isLocalScDiffeo (Ft.tgtH 𝓕 X Y a)
  have hπ := Y.toPU.x.bun.bundle.isStrongBundleIsoOn_pullbackProj'
    Y.toPU.x.Ψh.τ.isScSmoothMap_obj hd (Ft.tgtH 𝓕 X Y a)
  obtain ⟨g, hg⟩ := hc₀.isScDiffeoOn_base
  have hW : IsOpen (U₀ ∩ Ft.tgtH 𝓕 X Y ⁻¹' V) := hg.isOpen_source.inter
    (hd.isOpen_source.preimage (Ft.isLocalScDiffeo_tgtH 𝓕 X Y hC).continuous)
  have hc := hc₀.restrict hg hW inter_subset_left
  have hc' : (Ft.toPullback.pullBundle 𝓕 X.toPU Y.toPU).IsStrongBundleIsoOn Y.x.K.BW
      ((Y.toPU.x.bun.bundle.isStrongBundleMap_pullbackProj' Y.toPU.x.Ψh.τ.isScSmoothMap_obj).comp
        (Ft.isStrongBundleMap_TMapT 𝓕 X Y hcoh hC))
      (U₀ ∩ Ft.tgtH 𝓕 X Y ⁻¹' V) (U₀'' ∩ g ⁻¹' (U₀ ∩ Ft.tgtH 𝓕 X Y ⁻¹' V)) := hc
  exact ⟨U₀ ∩ Ft.tgtH 𝓕 X Y ⁻¹' V, _, ⟨ha₀, hV⟩,
    hc'.of_comp (h := Ft.isStrongBundleMap_TMapT 𝓕 X Y hcoh hC) hπ fun _ hx => hx.2⟩

/-- `T : p*M(Γ, Γ') → Ŵ'`, `((ê, φ̂, ê'), (w, (P(φ̂), A(w)), w')) ↦ ŵ'` with `Ξ'(ŵ') = w'`,
`Q̂'(ŵ') = ê'` (the target analogue of (19.93)). -/
def SMapT (z : Ft.toPullback.PB 𝓕 X.toPU Y.toPU) : Y.x.K.Wh :=
  Y.x.K.liftKinv (Ft.TMapT 𝓕 X Y z)

/-- **`t = T ∘ U`.** -/
theorem SMapT_USq (h : Ft.MSq 𝓕 X Y) : Ft.SMapT 𝓕 X Y (Ft.USq 𝓕 X Y h) = Ft.tgtSq 𝓕 X Y h :=
  (Ft.tgtSq_eq 𝓕 X Y h).symm

/-- **`t : M(Γ̂, Γ̂') → Ŵ'` is a strong bundle map covering `t̂ : M(Ψ̂, Ψ̂') → Ê'`**, for coherent
`𝓕` under `IsCompatible`. -/
theorem isStrongBundleMap_tgtSq (hcoh : Ft.toPullback.IsCoherent 𝓕)
    (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) :
    (Ft.bundleSq 𝓕 X Y).IsStrongBundleMap Y.x.K.BWh (Ft.tgtH 𝓕 X Y) (Ft.tgtSq 𝓕 X Y) := by
  have h := (Y.x.K.isStrongBundleIso_liftK.invMap.comp
    (Ft.isStrongBundleMap_TMapT 𝓕 X Y hcoh hC)).comp (Ft.isStrongBundleIso_USq 𝓕 X Y).toMap
  have e : Ft.SMapT 𝓕 X Y ∘ Ft.USq 𝓕 X Y = Ft.tgtSq 𝓕 X Y := funext (Ft.SMapT_USq 𝓕 X Y)
  change (Ft.bundleSq 𝓕 X Y).IsStrongBundleMap Y.x.K.BWh (Ft.tgtH 𝓕 X Y)
    (Ft.SMapT 𝓕 X Y ∘ Ft.USq 𝓕 X Y) at h
  rw [e] at h
  exact h

/-- **The target map `t : M(Γ̂, Γ̂') → Ŵ'` is a local strong bundle isomorphism** covering
`t̂`, for the structure of Definition 19.8.17 (Theorem 19.8.22, "the local isomorphisms
`s, t`"): `t = T ∘ U` with `U` a strong bundle isomorphism, `T = (Q̂', Ξ')⁻¹ ∘ (t̂, t)`. -/
theorem isLocalStrongBundleIso_tgtSq (hcoh : Ft.toPullback.IsCoherent 𝓕)
    (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) (a : Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU) :
    ∃ (U : Set (Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU)) (U' : Set Y.toPU.x.Ψh.ObjE), a ∈ U ∧
      (Ft.bundleSq 𝓕 X Y).IsStrongBundleIsoOn Y.x.K.BWh (Ft.isStrongBundleMap_tgtSq 𝓕 X Y hcoh hC)
        U U' := by
  obtain ⟨U, U', ha, hT⟩ := Ft.isLocalStrongBundleIso_TMapT 𝓕 X Y hcoh hC a
  obtain ⟨U₁, U₁', ha₁, hS⟩ :=
    Y.x.K.isStrongBundleIso_liftK.symm.isStrongBundleIsoOn_univ.exists_comp hT ha (mem_univ _)
  obtain ⟨U₀, U₀', ha₀, hc⟩ := hS.exists_comp
    (Ft.isStrongBundleIso_USq 𝓕 X Y).isStrongBundleIsoOn_univ (mem_univ a) ha₁
  exact ⟨U₀, U₀', ha₀, StrongBundle.isStrongBundleIsoOn_of_eqOn hc (fun _ _ => rfl)
    fun z _ => Ft.SMapT_USq 𝓕 X Y z⟩

/-! ### Definition 19.8.20 and Lemma 19.8.21: the natural topology `T̄_A` on `|E_A|` -/

/-- **2021 Definition 19.8.20, p. 956**, as printed: `U ⊂ |E_A|` belongs to `T̄_A` if for every
`ẑ ∈ U` with `z = |P_A|(ẑ)` there are an object `β` representing `|P|(z) ∈ |B|`, a uniformizer
`Γ̂ : K → 𝔈` in `F̃(β)` with associated `Γ̂ : Ŵ → E_A`, a `ŵ ∈ Ŵ` with `|Γ̂(ŵ)| = ẑ` and an open
`V(ŵ) ∋ ŵ` with `|Γ̂(V(ŵ))| ⊂ U`. -/
def NatOpenEA (W : Set S.μA.cat.OrbitSpace) : Prop :=
  ∀ z ∈ W, ∃ β : B.Obj, B.π β = S.P.orbitMap (S.μA.orbitProj z) ∧ ∃ x ∈ Ft.F β, ∃ w : x.K.Wh,
    S.μA.cat.π (x.Γh.obj w) = z ∧ ∃ V : Set x.K.Wh, IsOpen V ∧ w ∈ V ∧
      (fun q => S.μA.cat.π (x.Γh.obj q)) '' V ⊆ W

theorem natOpenEA_empty : Ft.NatOpenEA ∅ := fun _ hz => absurd hz (notMem_empty _)

theorem natOpenEA_sUnion {T : Set (Set S.μA.cat.OrbitSpace)} (hT : ∀ W ∈ T, Ft.NatOpenEA W) :
    Ft.NatOpenEA (⋃₀ T) := by
  rintro z ⟨W, hW, hz⟩
  obtain ⟨β, hβ, x, hx, w, hw, V, hV, hwV, hsub⟩ := hT W hW z hz
  exact ⟨β, hβ, x, hx, w, hw, V, hV, hwV, hsub.trans (subset_sUnion_of_mem hW)⟩

variable {Ft}

/-- **Points over `|Ψ̂(ê)|` lie in `|Γ̂(Q̂⁻¹(ê))|`**: if `|P_A|(ẑ) = |Ψ̂(ê)|` then `ẑ = |Γ̂(ŵ)|`
for some `ŵ` with `Q̂(ŵ) = ê` (`Â` is onto the fibre over `Ψ̂(ê)`). -/
theorem exists_Γh_of_orbitProj_eq {β : B.Obj} (x : SquareUniformizer S β) (e : x.Ψh.ObjE)
    {z : S.μA.cat.OrbitSpace} (hz : S.μA.orbitProj z = A.π (x.Ψh.hat.obj e)) :
    ∃ w : x.K.Wh, x.K.Qh w = e ∧ S.μA.cat.π (x.Γh.obj w) = z := by
  induction z using Quotient.inductionOn with
  | h v =>
  obtain ⟨v', hv', hvv'⟩ := S.μA.exists_mem_fiber_of_π_eq (e := v) (α := x.Ψh.hat.obj e) hz
  let w : x.K.Qh ⁻¹' {e} := (x.fiberCLEh e).symm ⟨v', hv'⟩
  have hw : x.Γh.obj w = v' := by
    rw [← x.fiberCLEh_apply e w, ContinuousLinearEquiv.apply_symm_apply]
  exact ⟨w, w.2, by rw [hw, hvv']; rfl⟩

/-- Every `ẑ` with `|P|(|P_A|(ẑ)) = |β|` is `|Γ̂(ŵ)|` for some `ŵ`, for `Γ̂ ∈ F̃(β)`. -/
theorem exists_Γh_of_pt {β : B.Obj} (x : SquareUniformizer S β) {z : S.μA.cat.OrbitSpace}
    (hz : B.π β = S.P.orbitMap (S.μA.orbitProj z)) :
    ∃ w : x.K.Wh, S.μA.cat.π (x.Γh.obj w) = z := by
  obtain ⟨e, he⟩ :=
    CoveringBasicConstruction.exists_hat_of_orbitMap_eq_pt S.isFiniteToOneCovering x.Ψh hz
  obtain ⟨w, -, hw⟩ := exists_Γh_of_orbitProj_eq x e he.symm
  exact ⟨w, hw⟩

/-- An isomorphism `Γ̂(ŵ) ≅ Γ̂'(ŵ')` gives an element of `M(Γ̂, Γ̂')` from `ŵ` to `ŵ'`. -/
theorem exists_sq_of_π_eq {X Y : Ft.Unif} {w : X.x.K.Wh} {w' : Y.x.K.Wh}
    (h : S.μA.cat.π (X.x.Γh.obj w) = S.μA.cat.π (Y.x.Γh.obj w')) :
    ∃ a : Ft.MSq 𝓕 X Y, a.toTrans.src = w ∧ a.toTrans.tgt = w' := by
  obtain ⟨φ, hs, ht⟩ := (S.μA.cat.π_eq_π_iff).1 h
  exact ⟨⟨w, φ, w', hs, ht⟩, rfl, rfl⟩

variable (Ft)

/-- Every class of `B` contains the base object `β` of a member of `F̃`, when every class of `B`
has a representative `β` with `F̂(β) ≠ ∅`. -/
theorem exists_unif (hU : (Ft.toPullback.toCBC 𝓕).HasClassUniformizers) (z : B.OrbitSpace) :
    ∃ X : Ft.Unif, B.π X.β = z := by
  obtain ⟨β, hβ, Ψh, ⟨_, ⟨x, hx, rfl⟩, rfl⟩⟩ := hU z
  exact ⟨⟨β, x, hx⟩, hβ⟩

/-- **The step of the proof** (as for Lemma 19.7.17 (1), with `M(Γ̂, Γ̂')`): for
`h ∈ M(Γ̂, Γ̂')` and an open `V' ∋ t(h)` the open set `N = s(t⁻¹(V')) ∋ s(h)` satisfies
`|Γ̂(N)| ⊂ |Γ̂'(V')|`. -/
theorem exists_nbhd_sq (hcoh : Ft.toPullback.IsCoherent 𝓕)
    (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) (h : Ft.MSq 𝓕 X Y) {V' : Set Y.x.K.Wh}
    (hV' : IsOpen V') (ht : h.toTrans.tgt ∈ V') :
    ∃ N : Set X.x.K.Wh, IsOpen N ∧ h.toTrans.src ∈ N ∧
      ∀ d ∈ N, ∃ d' ∈ V', S.μA.cat.π (X.x.Γh.obj d) = S.μA.cat.π (Y.x.Γh.obj d') := by
  refine ⟨Ft.srcSq 𝓕 X Y '' (Ft.tgtSq 𝓕 X Y ⁻¹' V'),
    (Ft.isLocalHomeomorph_srcSq 𝓕 X Y).isOpenMap _
      (hV'.preimage (Ft.continuous_tgtSq 𝓕 X Y hcoh hC)), ⟨h, ht, rfl⟩, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨Ft.tgtSq 𝓕 X Y b, hb, (S.μA.cat.π_eq_π_iff).2
    ⟨b.toTrans.mor, b.toTrans.src_mor, b.toTrans.tgt_mor⟩⟩

/-- `|E_A| ∈ T̄_A`, when every class of `B` has a representative `β` with `F̂(β) ≠ ∅`. -/
theorem natOpenEA_univ (hU : (Ft.toPullback.toCBC 𝓕).HasClassUniformizers) :
    Ft.NatOpenEA univ := by
  intro z _
  obtain ⟨X, hX⟩ := Ft.exists_unif 𝓕 hU (S.P.orbitMap (S.μA.orbitProj z))
  obtain ⟨w, hw⟩ := exists_Γh_of_pt X.x hX
  exact ⟨X.β, hX, X.x, X.mem, w, hw, univ, isOpen_univ, mem_univ _, subset_univ _⟩

/-- `T̄_A` is closed under finite intersections, for coherent `𝓕` and under `IsCompatible`. -/
theorem natOpenEA_inter (hcoh : Ft.toPullback.IsCoherent 𝓕)
    (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) {W₁ W₂ : Set S.μA.cat.OrbitSpace}
    (h₁ : Ft.NatOpenEA W₁) (h₂ : Ft.NatOpenEA W₂) : Ft.NatOpenEA (W₁ ∩ W₂) := by
  rintro z ⟨hz₁, hz₂⟩
  obtain ⟨β₁, hβ₁, x₁, hx₁, w₁, hw₁, V₁, hV₁, hwV₁, hsub₁⟩ := h₁ z hz₁
  obtain ⟨β₂, -, x₂, hx₂, w₂, hw₂, V₂, hV₂, hwV₂, hsub₂⟩ := h₂ z hz₂
  obtain ⟨a, ha₁, ha₂⟩ := exists_sq_of_π_eq (𝓕 := 𝓕) (X := ⟨β₁, x₁, hx₁⟩) (Y := ⟨β₂, x₂, hx₂⟩)
    (hw₁.trans hw₂.symm)
  obtain ⟨N, hN, haN, hNf⟩ := Ft.exists_nbhd_sq 𝓕 ⟨β₁, x₁, hx₁⟩ ⟨β₂, x₂, hx₂⟩ hcoh hC a hV₂
    (ha₂ ▸ hwV₂)
  refine ⟨β₁, hβ₁, x₁, hx₁, w₁, hw₁, N ∩ V₁, hN.inter hV₁, ⟨ha₁ ▸ haN, hwV₁⟩, ?_⟩
  rintro _ ⟨d, ⟨hdN, hdV⟩, rfl⟩
  obtain ⟨d', hd', hdd'⟩ := hNf d hdN
  refine ⟨hsub₁ ⟨d, hdV, rfl⟩, ?_⟩
  change S.μA.cat.π (x₁.Γh.obj d) ∈ W₂
  rw [show S.μA.cat.π (x₁.Γh.obj d) = S.μA.cat.π (x₂.Γh.obj d') from hdd']
  exact hsub₂ ⟨d', hd', rfl⟩

/-- **The natural topology `T̄_A` on `|E_A|`** (Definition 19.8.20, Lemma 19.8.21), for a
coherent `𝓕`, under `IsCompatible` and `HasClassUniformizers`. -/
abbrev natTopEA (hcoh : Ft.toPullback.IsCoherent 𝓕) (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible)
    (hU : (Ft.toPullback.toCBC 𝓕).HasClassUniformizers) :
    TopologicalSpace S.μA.cat.OrbitSpace where
  IsOpen := Ft.NatOpenEA
  isOpen_univ := Ft.natOpenEA_univ 𝓕 hU
  isOpen_inter _ _ := Ft.natOpenEA_inter 𝓕 hcoh hC
  isOpen_sUnion _ := Ft.natOpenEA_sUnion

/-- For `Γ̂ ∈ F̃(β)` and an open `V ⊂ Ŵ`, `|Γ̂(V)| ∈ T̄_A`. -/
theorem isOpen_image_Γh (hcoh : Ft.toPullback.IsCoherent 𝓕)
    (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) (hU : (Ft.toPullback.toCBC 𝓕).HasClassUniformizers)
    (X : Ft.Unif) {V : Set X.x.K.Wh} (hV : IsOpen V) :
    Ft.NatOpenEA ((fun d => S.μA.cat.π (X.x.Γh.obj d)) '' V) := by
  rintro _ ⟨d, hdV, rfl⟩
  obtain ⟨Y, hY⟩ :=
    Ft.exists_unif 𝓕 hU (S.P.orbitMap (S.μA.orbitProj (S.μA.cat.π (X.x.Γh.obj d))))
  obtain ⟨e', he'⟩ := exists_Γh_of_pt Y.x hY
  obtain ⟨a, ha₁, ha₂⟩ := exists_sq_of_π_eq (𝓕 := 𝓕) (X := Y) (Y := X) he'
  obtain ⟨N, hN, haN, hNf⟩ := Ft.exists_nbhd_sq 𝓕 Y X hcoh hC a hV (ha₂ ▸ hdV)
  refine ⟨Y.β, hY, Y.x, Y.mem, e', he', N, hN, ha₁ ▸ haN, ?_⟩
  rintro _ ⟨d₁, hd₁, rfl⟩
  obtain ⟨d₂, hd₂, h⟩ := hNf d₁ hd₁
  exact ⟨d₂, hd₂, h.symm⟩

/-- `ŵ ↦ |Γ̂(ŵ)|` is continuous `Ŵ → (|E_A|, T̄_A)`. -/
theorem continuous_π_Γh (hcoh : Ft.toPullback.IsCoherent 𝓕)
    (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) (hU : (Ft.toPullback.toCBC 𝓕).HasClassUniformizers)
    (X : Ft.Unif) :
    Continuous[_, Ft.natTopEA 𝓕 hcoh hC hU] fun d : X.x.K.Wh => S.μA.cat.π (X.x.Γh.obj d) := by
  let _inst := Ft.natTopEA 𝓕 hcoh hC hU
  refine continuous_def.2 fun W hW => isOpen_iff_forall_mem_open.2 fun d hd => ?_
  obtain ⟨β', -, x', hx', e', he', V', hV', heV', hsub'⟩ := hW _ hd
  obtain ⟨a, ha₁, ha₂⟩ := exists_sq_of_π_eq (𝓕 := 𝓕) (X := X) (Y := ⟨β', x', hx'⟩)
    (he'.symm : S.μA.cat.π (X.x.Γh.obj d) = _)
  obtain ⟨N, hN, haN, hNf⟩ := Ft.exists_nbhd_sq 𝓕 X ⟨β', x', hx'⟩ hcoh hC a hV' (ha₂ ▸ heV')
  refine ⟨N, fun d₁ hd₁ => ?_, hN, ha₁ ▸ haN⟩
  obtain ⟨d₂, hd₂, h⟩ := hNf d₁ hd₁
  change S.μA.cat.π (X.x.Γh.obj d₁) ∈ W
  rw [h]
  exact hsub' ⟨d₂, hd₂, rfl⟩

variable {Ft}

/-- `|Γ̂| : |Ŵ| → |E_A|` is injective (`Γ̂` is full). -/
theorem injective_orbitMap_Γh {β : B.Obj} (x : SquareUniformizer S β) :
    Injective x.Γh.orbitMap := by
  intro z z' h
  induction z using Quotient.inductionOn with
  | h e =>
  induction z' using Quotient.inductionOn with
  | h e' =>
  obtain ⟨φ, hφs, hφt⟩ := (S.μA.cat.π_eq_π_iff).1 h
  obtain ⟨ψ, hψs, hψt, -⟩ := (GroupoidFunctor.full_iff _).1 x.full_Γh e e' φ hφs hφt
  exact (GroupoidStr.π_eq_π_iff _).2 ⟨ψ, hψs, hψt⟩

variable (Ft)

/-- **`|Γ̂| : |Ŵ| → |E_A|` is a homeomorphism onto the open subset `|Γ̂(Ŵ)|` of `(|E_A|, T̄_A)`**
(as Theorem 19.6.8 (3)). -/
theorem isOpenEmbedding_orbitMap_Γh (hcoh : Ft.toPullback.IsCoherent 𝓕)
    (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) (hU : (Ft.toPullback.toCBC 𝓕).HasClassUniformizers)
    (X : Ft.Unif) :
    @IsOpenEmbedding _ _ _ (Ft.natTopEA 𝓕 hcoh hC hU) X.x.Γh.orbitMap := by
  let _inst := Ft.natTopEA 𝓕 hcoh hC hU
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ (injective_orbitMap_Γh X.x) ?_
  · exact continuous_quot_lift _ (Ft.continuous_π_Γh 𝓕 hcoh hC hU X)
  · intro W hW
    have : X.x.Γh.orbitMap '' W =
        (fun d => S.μA.cat.π (X.x.Γh.obj d)) '' ((epAction X.x.K.μWh).groupoid.π ⁻¹' W) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        induction w using Quotient.inductionOn with
        | h e => exact ⟨e, hw, rfl⟩
      · rintro ⟨e, he, rfl⟩
        exact ⟨_, he, rfl⟩
    rw [this]
    exact Ft.isOpen_image_Γh 𝓕 hcoh hC hU X (hW.preimage continuous_quot_mk)

variable {Ft} in
/-- **`|P_A|⁻¹(|Ψ̂(Ê)|) = |Γ̂(Ŵ)|`** (as `StrongBundleStr.orbitProj_preimage_range` in §19.6). -/
theorem orbitProj_preimage_range {β : B.Obj} (x : SquareUniformizer S β) :
    S.μA.orbitProj ⁻¹' range x.Ψh.hat.orbitMap = range x.Γh.orbitMap := by
  ext z
  constructor
  · rintro ⟨w, hw⟩
    induction w using Quotient.inductionOn with
    | h e =>
    obtain ⟨v, -, hv⟩ := exists_Γh_of_orbitProj_eq x e hw.symm
    exact ⟨_, (x.Γh.orbitMap_π v).trans hv⟩
  · rintro ⟨w, rfl⟩
    induction w using Quotient.inductionOn with
    | h v =>
    refine ⟨x.Ψh.E.toGroupoidStr.π (x.K.Qh v), ?_⟩
    change A.π (x.Ψh.hat.obj (x.K.Qh v)) = A.π (S.μA.P (x.Γh.obj v))
    rw [x.PA_obj]

/-- **`|P_A| : (|E_A|, T̄_A) → (|A|, T_{|A|})` is continuous** (Lemma 19.8.21; the proof of
Theorem 19.6.8 (5)). -/
theorem continuous_orbitProjA (hcoh : Ft.toPullback.IsCoherent 𝓕)
    (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible)
    (hU : (Ft.toPullback.toCBC 𝓕).HasClassUniformizers) :
    Continuous[Ft.natTopEA 𝓕 hcoh hC hU,
      (Ft.toPullback.toCBC 𝓕).natTopA S.isFiniteToOneCovering hC hU] S.μA.orbitProj := by
  let _i₁ := Ft.natTopEA 𝓕 hcoh hC hU
  let _i₂ := (Ft.toPullback.toCBC 𝓕).natTopA S.isFiniteToOneCovering hC hU
  refine continuous_def.2 fun W hW => ?_
  intro z hz
  obtain ⟨X, hX⟩ := Ft.exists_unif 𝓕 hU (S.P.orbitMap (S.μA.orbitProj z))
  obtain ⟨w, hw⟩ := exists_Γh_of_pt X.x hX
  have hc :=
    (Ft.toPullback.toCBC 𝓕).continuous_π_hat S.isFiniteToOneCovering hC hU X.toPU.toHat
  refine ⟨X.β, hX, X.x, X.mem, w, hw,
    X.x.K.Qh ⁻¹' ((fun d => A.π (X.x.Ψh.hat.obj d)) ⁻¹' W),
    (hW.preimage hc).preimage X.x.K.BWh.continuous, ?_, ?_⟩
  · change A.π (X.x.Ψh.hat.obj (X.x.K.Qh w)) ∈ W
    rw [← X.x.PA_obj w]
    change S.μA.orbitProj (S.μA.cat.π (X.x.Γh.obj w)) ∈ W
    rw [hw]
    exact hz
  · rintro _ ⟨q, hq, rfl⟩
    change A.π (S.μA.P (X.x.Γh.obj q)) ∈ W
    rw [X.x.PA_obj]
    exact hq

variable {Ft} in
/-- **`|Ŵ|` is metrizable** when `|Ê|` is paracompact: the orbit space of the action groupoid of
`Q̂ : Ŵ → Ê` is that of the ep-groupoid of the strong bundle `(Ŵ, μ̂)` (Proposition 8.4.1). -/
theorem metrizableSpace_orbitSpace_Wh {β : B.Obj} (x : SquareUniformizer S β)
    (h : x.Ψh.E.HasParacompactOrbitSpace) :
    MetrizableSpace (epAction x.K.μWh).groupoid.OrbitSpace := by
  have := x.K.BWh.paracompactSpace_pullback x.Ψh.E.PMor x.Ψh.E.src
  exact x.K.μWh.metrizableSpace_orbitSpace h

/-- **2021 Lemma 19.8.21, p. 956**, for a basic construction `(F̃, 𝓕)` of `𝔈` (`𝓕` coherent,
`T_{|B|}` metrizable), under `IsCompatible` and `HasClassUniformizers`: `T̄_A` is a metrizable
topology on `|E_A|` for which `|P_A| : |E_A| → |A|` is continuous.  ("Follow the proof of
Theorem 19.6.8": `|P_A|⁻¹(|Ψ̂(Ê)|) = |Γ̂(Ŵ)| ≅ |Ŵ|` is metrizable (Proposition 8.4.1, `|Ê|` being
metrizable as an open subset of `|A|`), and `|E_A|` is metrizable over the metrizable `|A|`,
`metrizableSpace_of_pullback`.) -/
theorem metrizableSpace_natTopEA (hcoh : Ft.toPullback.IsCoherent 𝓕)
    (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) (hU : (Ft.toPullback.toCBC 𝓕).HasClassUniformizers)
    (hm : @MetrizableSpace _ ((Ft.toPullback.toCBC 𝓕).toBasic.natTop hU.toBasic)) :
    @MetrizableSpace _ (Ft.natTopEA 𝓕 hcoh hC hU) := by
  let _i := Ft.natTopEA 𝓕 hcoh hC hU
  let _iA := (Ft.toPullback.toCBC 𝓕).natTopA S.isFiniteToOneCovering hC hU
  have hmA := ((Ft.toPullback.toCBC 𝓕).theorem_19_7_25_one_hyp S.isFiniteToOneCovering hC hU hm).1
  have : ParacompactSpace A.OrbitSpace := paracompactSpace_of_metrizableSpace _
  refine metrizableSpace_of_pullback S.μA.orbitProj (Ft.continuous_orbitProjA 𝓕 hcoh hC hU)
    fun z => ?_
  obtain ⟨X, hX⟩ := Ft.exists_unif 𝓕 hU (S.P.orbitMap z)
  obtain ⟨e, he⟩ := CoveringBasicConstruction.exists_hat_of_orbitMap_eq_pt
    S.isFiniteToOneCovering X.x.Ψh hX
  have hemb := (Ft.toPullback.toCBC 𝓕).lemma_19_7_17_two_hyp S.isFiniteToOneCovering hC hU
    X.toPU.toHat
  refine ⟨range X.x.Ψh.hat.orbitMap, hemb.isOpen_range, ⟨X.x.Ψh.E.toGroupoidStr.π e, he⟩, ?_⟩
  rw [orbitProj_preimage_range]
  have : MetrizableSpace X.x.Ψh.E.OrbitSpace := hemb.isEmbedding.metrizableSpace
  have := metrizableSpace_orbitSpace_Wh X.x (paracompactSpace_of_metrizableSpace _)
  exact (Ft.isOpenEmbedding_orbitMap_Γh 𝓕 hcoh hC hU X).isEmbedding.toHomeomorph.symm.isEmbedding
    |>.metrizableSpace

/-- **2021 Lemma 19.8.21, p. 956**, with the hypotheses of `metrizableSpace_natTopEA`: `T̄_A`
(Definition 19.8.20) is a topology (`∅`, `|E_A|`, finite intersections, unions), it is
metrizable, and `|P_A| : (|E_A|, T̄_A) → (|A|, T_{|A|})` is continuous. -/
theorem lemma_19_8_21_hyp (hcoh : Ft.toPullback.IsCoherent 𝓕)
    (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) (hU : (Ft.toPullback.toCBC 𝓕).HasClassUniformizers)
    (hm : @MetrizableSpace _ ((Ft.toPullback.toCBC 𝓕).toBasic.natTop hU.toBasic)) :
    (Ft.NatOpenEA ∅ ∧ Ft.NatOpenEA univ ∧
      (∀ W₁ W₂, Ft.NatOpenEA W₁ → Ft.NatOpenEA W₂ → Ft.NatOpenEA (W₁ ∩ W₂)) ∧
      ∀ T : Set (Set S.μA.cat.OrbitSpace), (∀ W ∈ T, Ft.NatOpenEA W) → Ft.NatOpenEA (⋃₀ T)) ∧
    @MetrizableSpace _ (Ft.natTopEA 𝓕 hcoh hC hU) ∧
    Continuous[Ft.natTopEA 𝓕 hcoh hC hU,
      (Ft.toPullback.toCBC 𝓕).natTopA S.isFiniteToOneCovering hC hU] S.μA.orbitProj :=
  ⟨⟨Ft.natOpenEA_empty, Ft.natOpenEA_univ 𝓕 hU, fun _ _ => Ft.natOpenEA_inter 𝓕 hcoh hC,
    fun _ => Ft.natOpenEA_sUnion⟩, Ft.metrizableSpace_natTopEA 𝓕 hcoh hC hU hm,
    Ft.continuous_orbitProjA 𝓕 hcoh hC hU⟩

/-! ### Theorem 19.8.22: `p̂ : M(Γ̂, Γ̂') → M(Γ, Γ')` over `p : M(Ψ̂, Ψ̂') → M(Ψ, Ψ')` -/

/-- **2021 Theorem 19.8.22, p. 956, the square of transition sets**: `m̂ : M(Γ̂, Γ̂') → M(Ψ̂, Ψ̂')`
(Definition 19.8.17) and `m : M(Γ, Γ') → M(Ψ, Ψ')` (Theorem 19.8.6 (1)) with the horizontal
arrows `p̂`, `p` form a proper strong bundle covering square (Definition 19.8.19): `p` is a
surjective local sc-diffeomorphism with finite fibres, trivially covered by the sheets of
`exists_sheets_pB`, and `p̂` is a strong bundle map which is near every point a strong bundle
isomorphism. -/
theorem isProperSquare_pbarSq :
    IsProperStrongBundleCoveringSquare (Ft.bundleSq 𝓕 X Y) (Ft.toPullback.bundleG 𝓕 X.toPU Y.toPU)
      (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU) (Ft.pbarSq 𝓕 X Y) := by
  refine isProperStrongBundleCoveringSquare_of_sheets (Ft.isStrongBundleMap_pbarSq 𝓕 X Y)
    (Ft.toPullback.surjective_pBmap 𝓕 X.toPU Y.toPU)
    (Ft.toPullback.isLocalScDiffeo_pBmap 𝓕 X.toPU Y.toPU)
    (fun k => ((X.x.Ψh.lemma_19_7_9 Y.x.Ψh S.isFiniteToOneCovering).2 k).2)
    (Ft.isLocalStrongBundleIso_pbarSq 𝓕 X Y) fun k => ?_
  obtain ⟨U', hd, hU', hpre⟩ := (Ft.toPullback.toCBC 𝓕).exists_sheets_pB S.isFiniteToOneCovering
    X.toPU.toHat Y.toPU.toHat k
  exact ⟨univ, U', isOpen_univ, mem_univ _, hd, hU', hpre⟩

/-- **2021 Theorem 19.8.22, p. 956**, for a basic construction `(F̃, 𝓕)` of `𝔈` (`𝓕` coherent,
`T_{|B|}` metrizable), under `IsCompatible` (an added hypothesis, the reading of l. 44572) and
`HasClassUniformizers`, the topologies, the square `p̂` and the local isomorphisms (the complete
form is `SquareBasicConstruction.theorem_19_8_22_hyp`):
the orbit spaces `|B|`, `|A|`, `|E_B|`, `|E_A|` carry the natural metrizable topologies
(`T_{|B|}`, `T̄_{|A|}` of Theorem 19.7.25, `T̄_B` of Definition 19.6.7 for `(F̄, 𝓕)`, `T̄_A` of
Definition 19.8.20); for two members `Γ̂`, `Γ̂'` the square `p̂ : M(Γ̂, Γ̂') → M(Γ, Γ')` over
`p : M(Ψ̂, Ψ̂') → M(Ψ, Ψ')` is a proper strong bundle covering square; and the source and target
maps `s : M(Γ̂, Γ̂') → Ŵ`, `t : M(Γ̂, Γ̂') → Ŵ'` (over `ŝ`, `t̂`) and `s : M(Γ, Γ') → W`,
`t : M(Γ, Γ') → W'` (over `s`, `t`) are local strong bundle isomorphisms. -/
theorem theorem_19_8_22_topology_hyp (hcoh : Ft.toPullback.IsCoherent 𝓕)
    (hC : (Ft.toPullback.toCBC 𝓕).IsCompatible) (hU : (Ft.toPullback.toCBC 𝓕).HasClassUniformizers)
    (hm : @MetrizableSpace _ ((Ft.toPullback.toCBC 𝓕).toBasic.natTop hU.toBasic)) :
    @MetrizableSpace _ ((Ft.toPullback.toCBC 𝓕).natTopA S.isFiniteToOneCovering hC hU) ∧
    @MetrizableSpace _ (Ft.toPullback.natTopEB 𝓕 hcoh hU) ∧
    @MetrizableSpace _ (Ft.natTopEA 𝓕 hcoh hC hU) ∧
    ∀ X Y : Ft.Unif,
      IsProperStrongBundleCoveringSquare (Ft.bundleSq 𝓕 X Y)
        (Ft.toPullback.bundleG 𝓕 X.toPU Y.toPU) (Ft.toPullback.pBmap 𝓕 X.toPU Y.toPU)
        (Ft.pbarSq 𝓕 X Y) ∧
      (∀ a, ∃ (U : Set (Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU)) (U' : Set X.x.Ψh.ObjE), a ∈ U ∧
        (Ft.bundleSq 𝓕 X Y).IsStrongBundleIsoOn X.x.K.BWh (Ft.isStrongBundleMap_srcSq 𝓕 X Y)
          U U') ∧
      (∀ a, ∃ (U : Set (Ft.toPullback.MHatB 𝓕 X.toPU Y.toPU)) (U' : Set Y.toPU.x.Ψh.ObjE),
        a ∈ U ∧ (Ft.bundleSq 𝓕 X Y).IsStrongBundleIsoOn Y.x.K.BWh
          (Ft.isStrongBundleMap_tgtSq 𝓕 X Y hcoh hC) U U') ∧
      (∀ k, ∃ (U : Set (Ft.toPullback.MBase 𝓕 X.toPU Y.toPU)) (U' : Set X.toPU.x.Ψh.Ψ.O),
        k ∈ U ∧ (Ft.toPullback.bundleG 𝓕 X.toPU Y.toPU).IsStrongBundleIsoOn X.x.K.BW
          (Ft.isStrongBundleMap_srcG 𝓕 X Y) U U') ∧
      ∀ k, ∃ (U : Set (Ft.toPullback.MBase 𝓕 X.toPU Y.toPU)) (U' : Set Y.toPU.x.Ψh.Ψ.O),
        k ∈ U ∧ (Ft.toPullback.bundleG 𝓕 X.toPU Y.toPU).IsStrongBundleIsoOn Y.toPU.x.bun.bundle
          (Ft.toPullback.isStrongBundleMap_tgtGmap 𝓕 X.toPU Y.toPU hcoh) U U' :=
  ⟨((Ft.toPullback.toCBC 𝓕).theorem_19_7_25_one_hyp S.isFiniteToOneCovering hC hU hm).1,
    Ft.toPullback.metrizableSpace_natTopEB 𝓕 hcoh hU hm,
    Ft.metrizableSpace_natTopEA 𝓕 hcoh hC hU hm,
    fun X Y => ⟨Ft.isProperSquare_pbarSq 𝓕 X Y, Ft.isLocalStrongBundleIso_srcSq 𝓕 X Y,
      Ft.isLocalStrongBundleIso_tgtSq 𝓕 X Y hcoh hC, Ft.isLocalStrongBundleIso_srcG 𝓕 X Y,
      Ft.toPullback.isLocalStrongBundleIso_tgtGmap 𝓕 X.toPU Y.toPU hcoh⟩⟩

end SquareUniformizerConstruction

end GroupoidalCategory

end

end Polyfold
