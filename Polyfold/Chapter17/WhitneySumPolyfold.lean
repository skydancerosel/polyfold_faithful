import Polyfold.Chapter17.WhitneySumCategory
import Polyfold.Chapter17.TangentConstruction

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.6 (pp. 817–819): the rest of **Proposition 17.6.1**, the orbit space `|⊕ᵏ TC|` with its
topology, the polyfold structure `(⊕ᵏ TF, M)` of `⊕ᵏ TC` (with the sc-smooth multiplication of the
transition M-polyfolds `M(⊕ᵏ TΨ, ⊕ᵏ TΨ')`) and the bundle `⊕ᵏ P : ⊕ᵏ TC → C¹`.  Numbers and pages
are the 2021 text's.

# The polyfold bundle `⊕ᵏ TC → C¹`

## The text, paraphrased

(**Proposition 17.6.1**, pp. 818–819) If `C` is a polyfold, the `k`-fold Whitney sum
`⊕ᵏ TC → C¹` has a natural structure as a polyfold bundle.  The uniformizers are the
`⊕ᵏ TΨ : G ⋉ ⊕ᵏ TO → ⊕ᵏ TC`, `Ψ ∈ F(α)`, covering `Ψ¹`; the transition sets
`M(⊕ᵏ TΨ, ⊕ᵏ TΨ')` are identified with a `k`-fold Whitney sum of `M(TΨ, TΨ') → M(Ψ¹, Ψ'¹)`, which
gives their M-polyfold bundle structure and metrics for the orbit spaces; source and target are
sc-smooth local bundle isomorphisms; "clearly `⊕ᵏ TC` is a GCT", and the `⊕ᵏ TΨ` with the `Ψ¹`
have the polyfold bundle uniformizer properties ("easily verified").

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* `whitneyUnifObj` (`⊕ᵏ TΨ` on objects), `injective_whitneyUnifObj`; `WTr` (the transition set of
  the `⊕ᵏ TΨ`), `WTr.ext'`, and **`wtrEquiv`**: `WTr ≃ WTrM`, the transition set is the `k`-fold
  Whitney sum of `M(TΨ, TΨ') → M(Ψ, Ψ')¹` (`WhitneySumStructure.lean`), with `wtrOf`, `wtrTo`,
  `src_eq_wtrSrc`, `tgt_eq_wtrTgt`.
* `whitneyUnif_exists_smul`, `whitneyUnifFunctor_full`, `whitneyUnifFunctor_faithful`.
* **The topology of `|⊕ᵏ TC|`**: `whitneyOrbitTopology` (the final topology of the
  `|⊕ᵏ TΨ|`, `whitneyOrbitChart`), `preimage_whitneyOrbitChart_image` (the overlaps are
  `s(t⁻¹(·))` in `M(⊕ᵏ TΨ, ⊕ᵏ TΨ')`), **`isOpenEmbedding_whitneyOrbitChart`**,
  `continuous_orbitMap_whitneyCatProj` (`|⊕ᵏ P|` continuous into `|C¹|`),
  `exists_whitneyUnifObj_isomorphic`, `preimage_footprint_eq_range`,
  **`metrizableSpace_whitneyOrbitTopology`**, **`whitneyGCT`**, **`whitneyUnif`** (`⊕ᵏ TΨ` as a
  local uniformizer of the GCT `⊕ᵏ TC`), `eq_whitneyOrbitTopology` (uniqueness).
* **The transition M-polyfolds**: `WTrN` (`WTr` with the topology of `WTrM`), `wtrNEquiv`
  (`⊕ₖ T M(Ψ, Ψ') ≃ₜ M(⊕ᵏ TΨ, ⊕ᵏ TΨ')`), `wtrNPolyfold` (Part I's Whitney sum transported),
  `wtrN_isLocalScDiffeo_src`, `_tgt`, `wtrN_isScSmoothMap_unit`, `_inv`, and
  **`wtrN_isScSmoothMap_mul`** (the multiplication is sc-smooth on the fibred product).
* **The polyfold structure**: `whitneyF`, `whitneyUnif_isAt`, `whitneyData`, the casts
  `whitneyTopOf`, …, `whitneyMulOf`, **`whitneyConstruction`**,
  `whitneyConstruction_hasUniformizers`.
* **The bundle**: `whitneyTrBundleProj` (`M(⊕ᵏ TΨ, ⊕ᵏ TΨ') → M(Ψ¹, Ψ'¹)`),
  `isScSmoothMap_whitneyTrBundleProj`, `whitneyTrBundleProj_spec`; **`proposition_17_6_1_hyp`**.
* Witness: `reflectionWhitneyConstruction`, **`reflection_proposition_17_6_1`**.

## Readings and proof

* **The hypothesis `hcont`** (every `Ψ̂` continuous) is the one of Theorem 17.2.17
  (`theorem_17_2_17_hyp`): on morphisms `⊕ᵏ TΨ` is built from `TΨ(g, h)`, a functor for continuous
  `Ψ̂` (`lemma_17_2_10_of_continuous`).  The reflection witness satisfies it
  (`reflection_continuous_hat_all`).
* **"Clearly `⊕ᵏ TC` is a GCT."**  The topology of `|⊕ᵏ TC|` is read as the one for which every
  `|⊕ᵏ TΨ|` is a homeomorphism onto an open set; it exists (the final topology, since the overlaps
  `s(t⁻¹(W))` are open: `s` is a local homeomorphism and `t` continuous on
  `M(⊕ᵏ TΨ, ⊕ᵏ TΨ')`) and is unique.  Metrizability goes through Smirnov's theorem pulled back
  along the continuous `|⊕ᵏ P| : |⊕ᵏ TC| → |C¹|`, as for `|TX|` (Theorem 8.1.15): `|C¹|` is
  metrizable (Theorem 17.1.28) and the preimage of the footprint of `Ψ¹` is the footprint of
  `⊕ᵏ TΨ`, homeomorphic to the metrizable `G\⊕ᵏ TO`.  For `k = 1` this is a second description of
  the topology of `|TC|`; the comparison with `tangentOrbitTopology` is not made here.
* **`M(⊕ᵏ TΨ, ⊕ᵏ TΨ')`** carries the structure of Part I's `⊕ₖ T M(Ψ, Ψ')` along the identification
  of the text (componentwise the identification of Proposition 17.2.15); under it `s`, `t`, `u`,
  `ι` are `⊕ᵏ Ts`, `⊕ᵏ Tt`, `⊕ᵏ Tu`, `⊕ᵏ Tι`, and near a point the multiplication is `⊕ᵏ T` of the
  sheet map `b ↦ m(σ(t b), b)` composed with `pr₂`, as in `tangentTr_isScSmoothMap_mul`.
* **"Polyfold bundle"** is read as for Theorem 17.2.17 (V17.55): the structure `(⊕ᵏ TF, M)` on
  `⊕ᵏ TC` and `(F¹, M_{F¹})` on `C¹`, related by `⊕ᵏ P` (`⊕ᵏ P ∘ ⊕ᵏ TΨ = Ψ¹ ∘ ⊕ᵏ p`, the bundle
  projections `M(⊕ᵏ TΨ, ⊕ᵏ TΨ') → M(Ψ¹, Ψ'¹)` sc-smooth and compatible with `s`, `t`, `φ`, and
  `|⊕ᵏ P|` continuous); the fibrewise linear structure is that of `TΨ` in each entry.  No strong
  bundle structure is involved.
* `⊕ᵏ TF(β)` is indexed through `⊕ᵏ P(β)` (the text's family of the `⊕ᵏ TΨ`, `Ψ ∈ F(α)`), and
  `M(L, L')` uses the uniformizer `Ψ = whitneyData L` chosen with `L = ⊕ᵏ TΨ`, as for
  `tangentConstruction`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction}

/-! ### `⊕ᵏ TΨ` on objects and the transition sets `M(⊕ᵏ TΨ, ⊕ᵏ TΨ')` -/

section WhitneyTransitionSet

variable (hU : S.HasUniformizers) (k : ℕ)

variable (S) in
/-- **`⊕ᵏ TΨ` on objects**, `(h₁, …, h_k) ↦ (Ψ(x); TΨ(h₁), …, TΨ(h_k))` (it does not involve the
continuity of `Ψ̂`). -/
def whitneyUnifObj (Ψ : S.Unif) (v : Ψ.1.P.WhitneySum k) : S.tangentCatProj.WhitneyObj k :=
  ⟨⟨Ψ.1.obj (Ψ.1.P.levelVal 1 (MPolyfold.whitneyProj v)), S.obj_levelVal_mem Ψ _⟩,
    fun i => S.tangentUnifObj hU Ψ (MPolyfold.whitneyVec v i), fun i =>
      Subtype.ext (congrArg (fun y => Ψ.1.obj (Ψ.1.P.levelVal 1 y))
        (MPolyfold.tangentProj_whitneyVec v i))⟩

theorem whitneyUnifFunctor_obj (Ψ : S.Unif) (hc : Continuous (S.hat Ψ)) :
    (S.whitneyUnifFunctor hU Ψ hc k).obj = S.whitneyUnifObj hU k Ψ := rfl

variable {hU k}

/-- **`⊕ᵏ TΨ` is injective on objects.** -/
theorem injective_whitneyUnifObj (Ψ : S.Unif) : Injective (S.whitneyUnifObj hU k Ψ) := by
  intro v w h
  have hb : Ψ.1.P.levelVal 1 (MPolyfold.whitneyProj v) =
      Ψ.1.P.levelVal 1 (MPolyfold.whitneyProj w) :=
    Ψ.1.injective_obj (congrArg (fun x => x.base.1) h)
  refine MPolyfold.whitneySum_ext (MPolyfold.level_ext hb) fun i => ?_
  exact injective_tangentUnifObj hU Ψ (congrFun (congrArg GroupoidFunctor.WhitneyObj.vec h) i)

variable (S hU k) in
/-- **The transition set `M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)`** (Definition 17.1.5 for the uniformizers `⊕ᵏ TΨ`):
the tuples `(v, Φ, v')` with `Φ : ⊕ᵏ TΨ₁(v) → ⊕ᵏ TΨ₂(v')` in `⊕ᵏ TC`. -/
abbrev WTr (Ψ₁ Ψ₂ : S.Unif) : Type (max u 1) :=
  GroupoidStr.TransitionSet (S.whitneyCatGroupoid k) (S.whitneyUnifObj hU k Ψ₁)
    (S.whitneyUnifObj hU k Ψ₂)

variable {Ψ₁ Ψ₂ : S.Unif}

/-- An element of `M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)` is determined by its source and the morphism of `C¹`. -/
theorem WTr.ext' {a b : S.WTr hU k Ψ₁ Ψ₂} (h₁ : a.src = b.src)
    (h₂ : a.mor.base = b.mor.base) : a = b := by
  have hv : a.mor.vec = b.mor.vec := funext fun i => by
    refine TangentCatMor.ext' ?_ ?_
    · have ha := congrFun (congrArg GroupoidFunctor.WhitneyObj.vec a.src_mor) i
      have hb := congrFun (congrArg GroupoidFunctor.WhitneyObj.vec b.src_mor) i
      change (a.mor.vec i).src = _ at ha
      change (b.mor.vec i).src = _ at hb
      rw [ha, hb, h₁]
    · have ha := congrArg Subtype.val (a.mor.mor_vec i)
      have hb := congrArg Subtype.val (b.mor.mor_vec i)
      change (a.mor.vec i).mor = _ at ha
      change (b.mor.vec i).mor = _ at hb
      rw [ha, hb, h₂]
  have hm : a.mor = b.mor := GroupoidFunctor.WhitneyMor.ext' h₂ hv
  refine GroupoidStr.TransitionSet.ext h₁ hm (injective_whitneyUnifObj (hU := hU) Ψ₂ ?_)
  exact a.tgt_mor.symm.trans ((congrArg (S.whitneyCatGroupoid k).tgt hm).trans b.tgt_mor)

/-- The base `(x, φ, x') ∈ M(Ψ₁, Ψ₂)¹` of `(v, Φ, v')`. -/
def wtrBaseOf (a : S.WTr hU k Ψ₁ Ψ₂) : (S.transPolyfold Ψ₁ Ψ₂).Level 1 :=
  (S.transPolyfold Ψ₁ Ψ₂).levelMk 1
    (S.toTr ⟨Ψ₁.1.P.levelVal 1 (MPolyfold.whitneyProj a.src), a.mor.base.1,
      Ψ₂.1.P.levelVal 1 (MPolyfold.whitneyProj a.tgt),
      congrArg (fun x => x.base.1) a.src_mor, congrArg (fun x => x.base.1) a.tgt_mor⟩)
    ((tr_mem_levelSet_iff _ 1).2 (MPolyfold.levelVal_mem _))

/-- The `i`-th entry `(hᵢ, Φᵢ, h'ᵢ) ∈ M(TΨ₁, TΨ₂)` of `(v, Φ, v')`. -/
def wtrVecOf (a : S.WTr hU k Ψ₁ Ψ₂) (i : Fin k) : S.TTrM hU Ψ₁ Ψ₂ :=
  (⟨MPolyfold.whitneyVec a.src i, a.mor.vec i, MPolyfold.whitneyVec a.tgt i,
    congrFun (congrArg GroupoidFunctor.WhitneyObj.vec a.src_mor) i,
    congrFun (congrArg GroupoidFunctor.WhitneyObj.vec a.tgt_mor) i⟩ : S.TTr hU Ψ₁ Ψ₂)

theorem tangentTrProj_wtrVecOf (a : S.WTr hU k Ψ₁ Ψ₂) (i : Fin k) :
    tangentTrProj hU (wtrVecOf a i) = wtrBaseOf a := by
  refine MPolyfold.level_ext (GroupoidStr.TransitionSet.ext ?_ ?_ ?_)
  · rw [tangentTrProj_src]
    exact congrArg (Ψ₁.1.P.levelVal 1) (MPolyfold.tangentProj_whitneyVec a.src i)
  · rw [tangentTrProj_mor]
    exact congrArg Subtype.val (a.mor.mor_vec i)
  · rw [tangentTrProj_tgt]
    exact congrArg (Ψ₂.1.P.levelVal 1) (MPolyfold.tangentProj_whitneyVec a.tgt i)

/-- `(v, Φ, v') ↦ (b; x₁, …, x_k)`, into Part I's reading `WTrM` of `M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)`. -/
def wtrOf (a : S.WTr hU k Ψ₁ Ψ₂) : S.WTrM hU Ψ₁ Ψ₂ k :=
  ⟨(wtrBaseOf a, fun i => wtrVecOf a i), fun i => tangentTrProj_wtrVecOf a i⟩

theorem wtrMor_mem (w : S.WTrM hU Ψ₁ Ψ₂ k) :
    C.toGroupoidStr.src ((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (wtrBase w)).mor ∈ S.regSet 1 ∧
      C.toGroupoidStr.tgt ((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (wtrBase w)).mor ∈ S.regSet 1 := by
  refine ⟨?_, ?_⟩
  · rw [((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (wtrBase w)).src_mor]
    exact S.obj_levelVal_mem Ψ₁ (MPolyfold.whitneyProj (S.wtrSrc hU Ψ₁ Ψ₂ k w))
  · rw [((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (wtrBase w)).tgt_mor]
    exact S.obj_levelVal_mem Ψ₂ (MPolyfold.whitneyProj (S.wtrTgt hU Ψ₁ Ψ₂ k w))

/-- `(b; x₁, …, x_k) ↦ (s, (φ; Φ₁, …, Φ_k), t)`, the inverse of `wtrOf`. -/
def wtrTo (w : S.WTrM hU Ψ₁ Ψ₂ k) : S.WTr hU k Ψ₁ Ψ₂ where
  src := S.wtrSrc hU Ψ₁ Ψ₂ k w
  mor := ⟨⟨((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (wtrBase w)).mor, wtrMor_mem w⟩,
    fun i => (wtrVec w i).mor, fun i => Subtype.ext (by
      have h := tangentTrProj_mor (wtrVec w i)
      rw [tangentTrProj_wtrVec] at h
      exact h.symm)⟩
  tgt := S.wtrTgt hU Ψ₁ Ψ₂ k w
  src_mor := by
    refine GroupoidFunctor.WhitneyObj.ext' (Subtype.ext ?_) (funext fun i => ?_)
    · exact ((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (wtrBase w)).src_mor
    · change (wtrVec w i).mor.src = S.tangentUnifObj hU Ψ₁ (MPolyfold.whitneyVec _ i)
      rw [whitneyVec_wtrSrc]
      exact (wtrVec w i).src_mor
  tgt_mor := by
    refine GroupoidFunctor.WhitneyObj.ext' (Subtype.ext ?_) (funext fun i => ?_)
    · exact ((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (wtrBase w)).tgt_mor
    · change S.tangentCatGroupoid.tgt (wtrVec w i).mor =
        S.tangentUnifObj hU Ψ₂ (MPolyfold.whitneyVec _ i)
      rw [whitneyVec_wtrTgt]
      exact (wtrVec w i).tgt_mor

@[simp] theorem wtrTo_src (w : S.WTrM hU Ψ₁ Ψ₂ k) : (wtrTo w).src = S.wtrSrc hU Ψ₁ Ψ₂ k w := rfl

@[simp] theorem wtrTo_tgt (w : S.WTrM hU Ψ₁ Ψ₂ k) : (wtrTo w).tgt = S.wtrTgt hU Ψ₁ Ψ₂ k w := rfl

theorem wtrTo_mor_base (w : S.WTrM hU Ψ₁ Ψ₂ k) :
    (wtrTo w).mor.base.1 = ((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (wtrBase w)).mor := rfl

theorem wtrOf_wtrTo (w : S.WTrM hU Ψ₁ Ψ₂ k) : wtrOf (wtrTo w) = w := by
  refine wtr_ext (MPolyfold.level_ext ?_) fun i => ?_
  · refine GroupoidStr.TransitionSet.ext ?_ rfl ?_
    · exact levelVal_whitneyProj_wtrSrc w
    · exact levelVal_whitneyProj_wtrTgt w
  · refine GroupoidStr.TransitionSet.ext ?_ rfl ?_
    · exact whitneyVec_wtrSrc w i
    · exact whitneyVec_wtrTgt w i

theorem wtrTo_wtrOf (a : S.WTr hU k Ψ₁ Ψ₂) : wtrTo (wtrOf a) = a := by
  refine WTr.ext' ?_ (Subtype.ext ?_)
  · refine MPolyfold.whitneySum_ext (MPolyfold.level_ext ?_) fun i => ?_
    · rw [wtrTo_src, levelVal_whitneyProj_wtrSrc]
      rfl
    · rw [wtrTo_src, whitneyVec_wtrSrc]
      rfl
  · rw [wtrTo_mor_base]
    rfl

variable (hU k Ψ₁ Ψ₂) in
/-- **`M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂) ≃ WTrM`**: the transition set of the uniformizers `⊕ᵏ TΨ` is the
`k`-fold Whitney sum of `M(TΨ₁, TΨ₂) → M(Ψ₁, Ψ₂)¹` (the reading of `WhitneySumStructure.lean`). -/
def wtrEquiv : S.WTr hU k Ψ₁ Ψ₂ ≃ S.WTrM hU Ψ₁ Ψ₂ k where
  toFun := wtrOf
  invFun := wtrTo
  left_inv := wtrTo_wtrOf
  right_inv := wtrOf_wtrTo

theorem src_eq_wtrSrc (a : S.WTr hU k Ψ₁ Ψ₂) : a.src = S.wtrSrc hU Ψ₁ Ψ₂ k (wtrOf a) :=
  (congrArg GroupoidStr.TransitionSet.src (wtrTo_wtrOf a)).symm

theorem tgt_eq_wtrTgt (a : S.WTr hU k Ψ₁ Ψ₂) : a.tgt = S.wtrTgt hU Ψ₁ Ψ₂ k (wtrOf a) :=
  (congrArg GroupoidStr.TransitionSet.tgt (wtrTo_wtrOf a)).symm

end WhitneyTransitionSet

/-! ### `⊕ᵏ TΨ` is full and faithful -/

section WhitneyUnifFunctor

variable (hU : S.HasUniformizers) (k : ℕ)

/-- **Fullness of `⊕ᵏ TΨ`**: a morphism `⊕ᵏ TΨ(v) → ⊕ᵏ TΨ(v')` of `⊕ᵏ TC` is `⊕ᵏ TΨ(g, v)` with
`g ∗ v = v'` (`Ψ̂` continuous). -/
theorem whitneyUnif_exists_smul (Ψ : S.Unif) (hc : Continuous (S.hat Ψ))
    {v v' : Ψ.1.P.WhitneySum k} {Φ : S.tangentCatProj.WhitneyMor k}
    (hs : (S.whitneyCatGroupoid k).src Φ = S.whitneyUnifObj hU k Ψ v)
    (ht : (S.whitneyCatGroupoid k).tgt Φ = S.whitneyUnifObj hU k Ψ v') :
    ∃ g : ULift.{1} Ψ.1.G, g • v = v' ∧ (S.whitneyUnifFunctor hU Ψ hc k).mor (g, v) = Φ := by
  have hbs : C.toGroupoidStr.src Φ.base.1 =
      Ψ.1.obj (Ψ.1.P.levelVal 1 (MPolyfold.whitneyProj v)) :=
    congrArg (fun x => x.base.1) hs
  have hbt : C.toGroupoidStr.tgt Φ.base.1 =
      Ψ.1.obj (Ψ.1.P.levelVal 1 (MPolyfold.whitneyProj v')) :=
    congrArg (fun x => x.base.1) ht
  obtain ⟨g, hg, hgm⟩ := Ψ.1.toUniformizer.exists_smul_eq_mor hbs hbt
  have hvec : ∀ i, ULift.up.{1} g • MPolyfold.whitneyVec v i = MPolyfold.whitneyVec v' i ∧
      S.tangentUnifMor hU Ψ (ULift.up g, MPolyfold.whitneyVec v i) = Φ.vec i := by
    intro i
    obtain ⟨g', hg', hm'⟩ := tangentUnif_exists_smul hU Ψ hc
      (congrFun (congrArg GroupoidFunctor.WhitneyObj.vec hs) i)
      (congrFun (congrArg GroupoidFunctor.WhitneyObj.vec ht) i)
    have hmor : Ψ.1.mor (g'.down, basePt Ψ (MPolyfold.whitneyVec v i)) = Φ.base.1 :=
      (congrArg TangentCatMor.mor hm').trans (congrArg Subtype.val (Φ.mor_vec i))
    have hb : basePt Ψ (MPolyfold.whitneyVec v i) =
        Ψ.1.P.levelVal 1 (MPolyfold.whitneyProj v) :=
      congrArg (Ψ.1.P.levelVal 1) (MPolyfold.tangentProj_whitneyVec v i)
    rw [hb] at hmor
    have hgg : g' = ULift.up g :=
      ULift.ext _ _ (Ψ.1.toUniformizer.mor_eq_mor_iff.1 (hmor.trans hgm.symm))
    subst hgg
    exact ⟨hg', hm'⟩
  refine ⟨ULift.up g, MPolyfold.whitneySum_ext (MPolyfold.level_ext hg) fun i => (hvec i).1, ?_⟩
  exact GroupoidFunctor.WhitneyMor.ext' (Subtype.ext hgm) (funext fun i => (hvec i).2)

theorem whitneyUnifFunctor_full (Ψ : S.Unif) (hc : Continuous (S.hat Ψ)) :
    (S.whitneyUnifFunctor hU Ψ hc k).toFunctor.Full := by
  refine (GroupoidFunctor.full_iff _).2 fun v v' Φ hs ht => ?_
  obtain ⟨g, hg, hm⟩ := S.whitneyUnif_exists_smul hU k Ψ hc hs ht
  exact ⟨(g, v), rfl, hg, hm⟩

theorem whitneyUnifFunctor_faithful (Ψ : S.Unif) (hc : Continuous (S.hat Ψ)) :
    (S.whitneyUnifFunctor hU Ψ hc k).toFunctor.Faithful := by
  refine (GroupoidFunctor.faithful_iff _).2 fun φ φ' hs _ he => ?_
  obtain ⟨g, v⟩ := φ
  obtain ⟨g', v'⟩ := φ'
  change v = v' at hs
  subst hs
  have hm : Ψ.1.mor (g.down, Ψ.1.P.levelVal 1 (MPolyfold.whitneyProj v)) =
      Ψ.1.mor (g'.down, Ψ.1.P.levelVal 1 (MPolyfold.whitneyProj v)) :=
    congrArg (fun Φ : S.tangentCatProj.WhitneyMor k => Φ.base.1) he
  rw [ULift.ext _ _ (Ψ.1.toUniformizer.mor_eq_mor_iff.1 hm)]

end WhitneyUnifFunctor

/-! ### The topology of `|⊕ᵏ TC|` -/

section WhitneyOrbit

variable (hU : S.HasUniformizers) (k : ℕ) (hcont : ∀ Ψ : S.Unif, Continuous (S.hat Ψ))

/-- `|⊕ᵏ TΨ| : G\⊕ᵏ TO → |⊕ᵏ TC|`. -/
abbrev whitneyOrbitChart (Ψ : S.Unif) :
    (S.whitneyTranslation Ψ k).OrbitSpace → (S.whitneyCatGroupoid k).OrbitSpace :=
  (S.whitneyUnifFunctor hU Ψ (hcont Ψ) k).orbitMap

/-- **The natural topology of `|⊕ᵏ TC|`**: the final topology of the maps `|⊕ᵏ TΨ|`, `Ψ ∈ F`
(`isOpenEmbedding_whitneyOrbitChart`: each of them is an open embedding;
`eq_whitneyOrbitTopology`: it is the only such topology). -/
@[instance_reducible]
def whitneyOrbitTopology : TopologicalSpace (S.whitneyCatGroupoid k).OrbitSpace :=
  chartTopology (S.whitneyOrbitChart hU k hcont)

/-- `|⊕ᵏ TΨ| ∘ π = π ∘ ⊕ᵏ TΨ`. -/
theorem whitneyOrbitChart_π (Ψ : S.Unif) (v : Ψ.1.P.WhitneySum k) :
    S.whitneyOrbitChart hU k hcont Ψ ((S.whitneyTranslation Ψ k).π v) =
      (S.whitneyCatGroupoid k).π (S.whitneyUnifObj hU k Ψ v) := rfl

/-- The points of `⊕ᵏ TO` whose class lies in `|⊕ᵏ TΨ'|(W)` are the sources of the elements of
`M(⊕ᵏ TΨ, ⊕ᵏ TΨ')` with target over `W`. -/
theorem preimage_whitneyOrbitChart_image (Ψ Ψ' : S.Unif)
    (W : Set (S.whitneyTranslation Ψ' k).OrbitSpace) :
    (S.whitneyTranslation Ψ k).π ⁻¹'
        (S.whitneyOrbitChart hU k hcont Ψ ⁻¹' (S.whitneyOrbitChart hU k hcont Ψ' '' W)) =
      S.wtrSrc hU Ψ Ψ' k '' (S.wtrTgt hU Ψ Ψ' k ⁻¹' ((S.whitneyTranslation Ψ' k).π ⁻¹' W)) := by
  ext v
  constructor
  · rintro ⟨z, hz, hzv⟩
    induction z using Quotient.inductionOn with | h v' => ?_
    change (S.whitneyCatGroupoid k).π (S.whitneyUnifObj hU k Ψ' v') =
      (S.whitneyCatGroupoid k).π (S.whitneyUnifObj hU k Ψ v) at hzv
    obtain ⟨Φ, hs, ht⟩ := (S.whitneyCatGroupoid k).π_eq_π_iff.1 hzv.symm
    let a : S.WTr hU k Ψ Ψ' := ⟨v, Φ, v', hs, ht⟩
    refine ⟨wtrOf a, ?_, (src_eq_wtrSrc a).symm⟩
    change S.wtrTgt hU Ψ Ψ' k (wtrOf a) ∈ (S.whitneyTranslation Ψ' k).π ⁻¹' W
    rw [← tgt_eq_wtrTgt a]
    exact hz
  · rintro ⟨w, hw, rfl⟩
    refine ⟨(S.whitneyTranslation Ψ' k).π (S.wtrTgt hU Ψ Ψ' k w), hw, ?_⟩
    change (S.whitneyCatGroupoid k).π (S.whitneyUnifObj hU k Ψ' (S.wtrTgt hU Ψ Ψ' k w)) =
      (S.whitneyCatGroupoid k).π (S.whitneyUnifObj hU k Ψ (S.wtrSrc hU Ψ Ψ' k w))
    exact ((S.whitneyCatGroupoid k).π_eq_π_iff.2
      ⟨(wtrTo w).mor, (wtrTo w).src_mor, (wtrTo w).tgt_mor⟩).symm

theorem isOpen_preimage_whitneyOrbitChart_image (Ψ Ψ' : S.Unif)
    (W : Set (S.whitneyTranslation Ψ' k).OrbitSpace) (hW : IsOpen W) :
    IsOpen (S.whitneyOrbitChart hU k hcont Ψ ⁻¹' (S.whitneyOrbitChart hU k hcont Ψ' '' W)) := by
  have hq : IsQuotientMap (S.whitneyTranslation Ψ k).π := isQuotientMap_quotient_mk'
  have hq' : IsQuotientMap (S.whitneyTranslation Ψ' k).π := isQuotientMap_quotient_mk'
  rw [← hq.isOpen_preimage, preimage_whitneyOrbitChart_image]
  exact whitneyTr_isLocalScDiffeo_src.isOpenMap _
    ((hW.preimage hq'.continuous).preimage whitneyTr_isLocalScDiffeo_tgt.continuous)

theorem injective_whitneyOrbitChart (Ψ : S.Unif) :
    Injective (S.whitneyOrbitChart hU k hcont Ψ) :=
  GroupoidFunctor.injective_orbitMap_of_full _ (S.whitneyUnifFunctor_full hU k Ψ (hcont Ψ))

/-- **`|⊕ᵏ TΨ| : G\⊕ᵏ TO → |⊕ᵏ TC|` is an open embedding** (a homeomorphism onto an open set). -/
theorem isOpenEmbedding_whitneyOrbitChart (Ψ : S.Unif) :
    @IsOpenEmbedding _ _ _ (S.whitneyOrbitTopology hU k hcont) (S.whitneyOrbitChart hU k hcont Ψ) :=
  isOpenEmbedding_chartTopology _ (S.injective_whitneyOrbitChart hU k hcont)
    (fun Ψ Ψ' W hW => S.isOpen_preimage_whitneyOrbitChart_image hU k hcont Ψ Ψ' W hW) Ψ

/-- **`|⊕ᵏ P| : |⊕ᵏ TC| → |C¹|` is continuous.** -/
theorem continuous_orbitMap_whitneyCatProj :
    @Continuous _ _ (S.whitneyOrbitTopology hU k hcont)
      (S.levelOneTopology (S.hasCoveringUniformizers_of_hasUniformizers hU))
      (S.whitneyCatProj k).orbitMap := by
  let hc := S.hasCoveringUniformizers_of_hasUniformizers hU
  let := S.levelOneTopology hc
  have h : ∀ Ψ : S.Unif,
      Continuous ((S.whitneyCatProj k).orbitMap ∘ S.whitneyOrbitChart hU k hcont Ψ) := fun Ψ => by
    have hq : IsQuotientMap (S.whitneyTranslation Ψ k).π := isQuotientMap_quotient_mk'
    rw [hq.continuous_iff]
    exact (S.levelOneUnif hc Ψ).continuous_π_obj.comp MPolyfold.continuous_whitneyProj
  exact continuous_iSup_dom.2 fun Ψ => continuous_coinduced_dom.2 (h Ψ)

/-- Every object of `⊕ᵏ TC` over an object isomorphic to `Ψ(x)`, `x ∈ O¹`, is isomorphic to some
`⊕ᵏ TΨ(v)`. -/
theorem exists_whitneyUnifObj_isomorphic (Ψ : S.Unif) (β : S.tangentCatProj.WhitneyObj k)
    (x : Ψ.1.P.Level 1)
    (h : (S.regSub 1).Isomorphic β.base ((S.levelOneFunctor Ψ).obj x)) :
    ∃ v, (S.whitneyCatGroupoid k).Isomorphic β (S.whitneyUnifObj hU k Ψ v) := by
  obtain ⟨ψ, hs, ht⟩ := h
  have hvs : ∀ i, C.toGroupoidStr.src ψ.1 = (β.vec i).base := fun i =>
    (congrArg Subtype.val hs).trans (congrArg Subtype.val (β.obj_vec i)).symm
  have hreg : C.toGroupoidStr.tgt ψ.1 ∈ S.regSet 1 := ψ.2.2
  let Φv : Fin k → S.TangentCatMor := fun i => ⟨β.vec i, ψ.1, hvs i, ⟨hreg, hU _⟩⟩
  have hq : ∀ i, Ψ.1.obj (Ψ.1.P.levelVal 1 x) = (Φv i).tgt.base := fun i =>
    (congrArg Subtype.val ht).symm
  choose kv hkb hkv using fun i => exists_tangentUnifObj_eq hU Ψ (Φv i).tgt _ (hq i)
  let v : Ψ.1.P.WhitneySum k := MPolyfold.whitneyMk x kv fun i => MPolyfold.level_ext (hkb i)
  let Φ : S.tangentCatProj.WhitneyMor k := ⟨ψ, Φv, fun i => Subtype.ext rfl⟩
  refine ⟨v, Φ, ?_, ?_⟩
  · exact GroupoidFunctor.WhitneyObj.ext' hs (funext fun _ => rfl)
  · refine GroupoidFunctor.WhitneyObj.ext' (ht.trans (Subtype.ext rfl)) (funext fun i => ?_)
    exact (hkv i).symm

/-- `|⊕ᵏ P|⁻¹(|Ψ¹|(G\O¹)) = |⊕ᵏ TΨ|(G\⊕ᵏ TO)`. -/
theorem preimage_footprint_eq_range (Ψ : S.Unif) :
    (S.whitneyCatProj k).orbitMap ⁻¹'
        (S.levelOneUnif (S.hasCoveringUniformizers_of_hasUniformizers hU) Ψ).footprint =
      range (S.whitneyOrbitChart hU k hcont Ψ) := by
  ext y
  induction y using Quotient.inductionOn with | h β => ?_
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (S.levelOneUnif _ Ψ).mem_footprint_iff.1 hy
    have hx' : (S.regSub 1).Isomorphic β.base ((S.levelOneFunctor Ψ).obj x) :=
      ((S.regSub 1).π_eq_π_iff.1 hx).symm
    obtain ⟨v, hv⟩ := S.exists_whitneyUnifObj_isomorphic hU k Ψ β x hx'
    exact ⟨(S.whitneyTranslation Ψ k).π v, ((S.whitneyCatGroupoid k).π_eq_π_iff.2 hv).symm⟩
  · rintro ⟨z, hz⟩
    induction z using Quotient.inductionOn with | h v => ?_
    rw [← hz]
    exact (S.levelOneUnif _ Ψ).π_obj_mem_footprint (MPolyfold.whitneyProj v)

/-- **`|⊕ᵏ TC|` is metrizable**: Smirnov's theorem pulled back along `|⊕ᵏ P| : |⊕ᵏ TC| → |C¹|`
(`metrizableSpace_of_pullback`), the preimage of the footprint of `Ψ¹` being the image of
`|⊕ᵏ TΨ|`, homeomorphic to the metrizable `G\⊕ᵏ TO`. -/
theorem metrizableSpace_whitneyOrbitTopology :
    @TopologicalSpace.MetrizableSpace (S.whitneyCatGroupoid k).OrbitSpace
      (S.whitneyOrbitTopology hU k hcont) := by
  let := S.whitneyOrbitTopology hU k hcont
  let hc := S.hasCoveringUniformizers_of_hasUniformizers hU
  let := S.levelOneTopology hc
  have := S.metrizableSpace_levelOne hc
  have : ParacompactSpace (S.regSub 1).OrbitSpace := paracompactSpace_of_metrizableSpace _
  refine metrizableSpace_of_pullback (S.whitneyCatProj k).orbitMap
    (S.continuous_orbitMap_whitneyCatProj hU k hcont) fun z => ?_
  induction z using Quotient.inductionOn with | h α => ?_
  obtain ⟨L, hL⟩ := hU α.1
  let Ψ : S.Unif := ⟨L, α.1, hL⟩
  obtain ⟨q, hq⟩ := S.isAt _ L hL
  have hq1 : q ∈ Ψ.1.P.levelSet 1 :=
    (hasRegularity_iff Ψ (hq ▸ C.toGroupoidStr.isomorphic_refl _ : C.toGroupoidStr.Isomorphic
      (Ψ.1.obj q) α.1) 1).1 α.2
  refine ⟨(S.levelOneUnif hc Ψ).footprint, (S.levelOneUnif hc Ψ).isOpen_footprint, ?_, ?_⟩
  · refine (S.levelOneUnif hc Ψ).mem_footprint_iff.2 ⟨Ψ.1.P.levelMk 1 q hq1, ?_⟩
    exact congrArg (S.regSub 1).π (Subtype.ext hq)
  · rw [S.preimage_footprint_eq_range hU k hcont Ψ]
    have := metrizableSpace_translation_orbitSpace (G := ULift.{1} Ψ.1.G)
      (P := Ψ.1.P.whitneyPolyfold k)
      fun g => MPolyfold.isScSmoothMap_whitneyMapOf (Ψ.1.smooth_smul g.down)
    exact (S.isOpenEmbedding_whitneyOrbitChart hU k hcont Ψ).isEmbedding.toHomeomorph.symm
      |>.isEmbedding.metrizableSpace

/-- **The GCT `⊕ᵏ TC`** (2021 p. 819, "clearly, `⊕ᵏ TC` is a GCT"): the groupoidal category
`⊕ᵏ TC` with the natural metrizable topology on `|⊕ᵏ TC|` (`Ψ̂` continuous). -/
def whitneyGCT : GCT.{max u 1} where
  toGroupoidalCategory := S.whitneyCategory k
  top := S.whitneyOrbitTopology hU k hcont
  metrizable := S.metrizableSpace_whitneyOrbitTopology hU k hcont

theorem whitneyGCT_toGroupoidStr :
    (S.whitneyGCT hU k hcont).toGroupoidStr = S.whitneyCatGroupoid k := rfl

/-- **The uniformizer `⊕ᵏ TΨ : G ⋉ ⊕ᵏ TO → ⊕ᵏ TC`** (2021 p. 818) as a local uniformizer of the
GCT `⊕ᵏ TC`: the M-polyfold `⊕ᵏ TO` (Part I, §4.4), `G` (lifted) acting by
`g ∗ (h₁, …, h_k) = (T(g ∗ ·)h₁, …, T(g ∗ ·)h_k)`, the functor `whitneyUnifFunctor`. -/
def whitneyUnif (Ψ : S.Unif) : (S.whitneyGCT hU k hcont).LocalUniformizer where
  O := Ψ.1.P.WhitneySum k
  P := Ψ.1.P.whitneyPolyfold k
  G := ULift.{1} Ψ.1.G
  smooth_smul g := MPolyfold.isScSmoothMap_whitneyMapOf (Ψ.1.smooth_smul g.down)
  functor := S.whitneyUnifFunctor hU Ψ (hcont Ψ) k
  injective_obj := injective_whitneyUnifObj (hU := hU) Ψ
  full := S.whitneyUnifFunctor_full hU k Ψ (hcont Ψ)
  faithful := S.whitneyUnifFunctor_faithful hU k Ψ (hcont Ψ)
  isOpenEmbedding_orbitMap := S.isOpenEmbedding_whitneyOrbitChart hU k hcont Ψ

end WhitneyOrbit

/-! ### The M-polyfold structure of `M(⊕ᵏ TΨ, ⊕ᵏ TΨ')` -/

section WhitneyTransitionPolyfold

variable {hU : S.HasUniformizers} {k : ℕ}

variable (S hU k) in
/-- **`M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)` with its topology** (a type synonym of `WTr` carrying the topology and
the M-polyfold structure, transported from Part I's `⊕ₖ T M(Ψ₁, Ψ₂)`). -/
def WTrN (Ψ₁ Ψ₂ : S.Unif) : Type (max u 1) := S.WTr hU k Ψ₁ Ψ₂

instance (Ψ₁ Ψ₂ : S.Unif) : TopologicalSpace (S.WTrN hU k Ψ₁ Ψ₂) :=
  TopologicalSpace.induced (wtrEquiv hU k Ψ₁ Ψ₂) inferInstance

variable (hU k) in
/-- `M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂) ≃ₜ WTrM`. -/
def wtrNHomeomorph (Ψ₁ Ψ₂ : S.Unif) : S.WTrN hU k Ψ₁ Ψ₂ ≃ₜ S.WTrM hU Ψ₁ Ψ₂ k :=
  Equiv.toHomeomorphOfIsInducing (wtrEquiv hU k Ψ₁ Ψ₂ : S.WTrN hU k Ψ₁ Ψ₂ ≃ _) ⟨rfl⟩

variable (hU k) in
/-- **The identification `⊕ₖ T M(Ψ₁, Ψ₂) ≃ₜ M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)`**, the identification
`TM(Ψ₁, Ψ₂) ≃ₜ M(TΨ₁, TΨ₂)` of Proposition 17.2.15 on each factor. -/
def wtrNEquiv (Ψ₁ Ψ₂ : S.Unif) : (S.transPolyfold Ψ₁ Ψ₂).WhitneySum k ≃ₜ S.WTrN hU k Ψ₁ Ψ₂ :=
  (whitneyTrHomeomorph hU Ψ₁ Ψ₂ k).trans (wtrNHomeomorph hU k Ψ₁ Ψ₂).symm

instance (Ψ₁ Ψ₂ : S.Unif) : T2Space (S.WTrN hU k Ψ₁ Ψ₂) :=
  (wtrNEquiv hU k Ψ₁ Ψ₂).symm.isEmbedding.t2Space

instance (Ψ₁ Ψ₂ : S.Unif) : ParacompactSpace (S.WTrN hU k Ψ₁ Ψ₂) :=
  (wtrNEquiv hU k Ψ₁ Ψ₂).symm.isClosedEmbedding.paracompactSpace

instance (Ψ₁ Ψ₂ : S.Unif) : TopologicalSpace.MetrizableSpace (S.WTrN hU k Ψ₁ Ψ₂) :=
  have := (S.transPolyfold Ψ₁ Ψ₂).metrizableSpace_whitneySum k
  (wtrNEquiv hU k Ψ₁ Ψ₂).symm.isEmbedding.metrizableSpace

variable (S hU k) in
/-- **The M-polyfold structure of `M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)`** (2021 p. 819): Part I's Whitney sum
`⊕ₖ T M(Ψ₁, Ψ₂)`, an M-polyfold bundle over `M(Ψ₁, Ψ₂)¹` (`MPolyfold.whitneySum_bundle`),
transported along the identification. -/
def wtrNPolyfold (Ψ₁ Ψ₂ : S.Unif) : MPolyfold (S.WTrN hU k Ψ₁ Ψ₂) :=
  ((S.transPolyfold Ψ₁ Ψ₂).whitneyPolyfold k).transport (wtrNEquiv hU k Ψ₁ Ψ₂)

variable {Ψ₁ Ψ₂ Ψ₃ : S.Unif}

theorem isScDiffeoOn_wtrNEquiv :
    ((S.transPolyfold Ψ₁ Ψ₂).whitneyPolyfold k).IsScDiffeoOn (S.wtrNPolyfold hU k Ψ₁ Ψ₂)
      (wtrNEquiv hU k Ψ₁ Ψ₂) (wtrNEquiv hU k Ψ₁ Ψ₂).symm univ univ :=
  MPolyfold.isScDiffeoOn_transport _ _

theorem isScSmoothMap_wtrNEquiv :
    ((S.transPolyfold Ψ₁ Ψ₂).whitneyPolyfold k).IsScSmoothMap (S.wtrNPolyfold hU k Ψ₁ Ψ₂)
      (wtrNEquiv hU k Ψ₁ Ψ₂) :=
  isScDiffeoOn_wtrNEquiv.isScSmoothOn

theorem isLocalScDiffeo_wtrNEquiv_symm :
    (S.wtrNPolyfold hU k Ψ₁ Ψ₂).IsLocalScDiffeo ((S.transPolyfold Ψ₁ Ψ₂).whitneyPolyfold k)
      (wtrNEquiv hU k Ψ₁ Ψ₂).symm := fun _ =>
  ⟨univ, univ, wtrNEquiv hU k Ψ₁ Ψ₂, mem_univ _, isScDiffeoOn_wtrNEquiv.symm⟩

theorem wtrNEquiv_symm_apply (a : S.WTrN hU k Ψ₁ Ψ₂) :
    (wtrNEquiv hU k Ψ₁ Ψ₂).symm a = (whitneyTrHomeomorph hU Ψ₁ Ψ₂ k).symm (wtrOf a) := rfl

theorem wtrNEquiv_apply (u : (S.transPolyfold Ψ₁ Ψ₂).WhitneySum k) :
    wtrNEquiv hU k Ψ₁ Ψ₂ u = wtrTo (whitneyTrHomeomorph hU Ψ₁ Ψ₂ k u) := rfl

/-- The base point of `(wtrNEquiv)⁻¹(a)` is `(x, φ, x')`. -/
theorem levelVal_whitneyProj_wtrNEquiv_symm (a : S.WTrN hU k Ψ₁ Ψ₂) :
    (S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (MPolyfold.whitneyProj ((wtrNEquiv hU k Ψ₁ Ψ₂).symm a)) =
      S.toTr ⟨Ψ₁.1.P.levelVal 1 (MPolyfold.whitneyProj a.src), a.mor.base.1,
        Ψ₂.1.P.levelVal 1 (MPolyfold.whitneyProj a.tgt),
        congrArg (fun x => x.base.1) a.src_mor, congrArg (fun x => x.base.1) a.tgt_mor⟩ := rfl

/-- `s = ⊕ᵏ Ts` under the identification. -/
theorem wtrN_src_eq (a : S.WTrN hU k Ψ₁ Ψ₂) :
    a.src = MPolyfold.whitneyMapOf (S.isLocalScDiffeo_trSrc Ψ₁ Ψ₂).isScSmoothMap
      ((wtrNEquiv hU k Ψ₁ Ψ₂).symm a) :=
  src_eq_wtrSrc (S := S) (hU := hU) (k := k) a

/-- `t = ⊕ᵏ Tt` under the identification. -/
theorem wtrN_tgt_eq (a : S.WTrN hU k Ψ₁ Ψ₂) :
    a.tgt = MPolyfold.whitneyMapOf (S.isLocalScDiffeo_trTgt Ψ₁ Ψ₂).isScSmoothMap
      ((wtrNEquiv hU k Ψ₁ Ψ₂).symm a) :=
  tgt_eq_wtrTgt (S := S) (hU := hU) (k := k) a

theorem wtrNEquiv_src (u : (S.transPolyfold Ψ₁ Ψ₂).WhitneySum k) :
    (wtrNEquiv hU k Ψ₁ Ψ₂ u).src =
      MPolyfold.whitneyMapOf (S.isLocalScDiffeo_trSrc Ψ₁ Ψ₂).isScSmoothMap u :=
  wtrSrc_whitneyTrHomeomorph u

theorem wtrNEquiv_mor_base (u : (S.transPolyfold Ψ₁ Ψ₂).WhitneySum k) :
    (wtrNEquiv hU k Ψ₁ Ψ₂ u).mor.base.1 =
      ((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (MPolyfold.whitneyProj u)).mor := rfl

/-- **Definition 17.1.8 (a) for `M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)`**: `s` is a local sc-diffeomorphism. -/
theorem wtrN_isLocalScDiffeo_src :
    (S.wtrNPolyfold hU k Ψ₁ Ψ₂).IsLocalScDiffeo (Ψ₁.1.P.whitneyPolyfold k)
      fun a : S.WTrN hU k Ψ₁ Ψ₂ => a.src := by
  have h : (fun a : S.WTrN hU k Ψ₁ Ψ₂ => a.src) =
      MPolyfold.whitneyMapOf (S.isLocalScDiffeo_trSrc Ψ₁ Ψ₂).isScSmoothMap ∘
        (wtrNEquiv hU k Ψ₁ Ψ₂).symm := funext wtrN_src_eq
  rw [h]
  exact (S.isLocalScDiffeo_trSrc Ψ₁ Ψ₂).whitneyMapOf.comp isLocalScDiffeo_wtrNEquiv_symm

/-- **Definition 17.1.8 (a) for `M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)`**: `t` is a local sc-diffeomorphism. -/
theorem wtrN_isLocalScDiffeo_tgt :
    (S.wtrNPolyfold hU k Ψ₁ Ψ₂).IsLocalScDiffeo (Ψ₂.1.P.whitneyPolyfold k)
      fun a : S.WTrN hU k Ψ₁ Ψ₂ => a.tgt := by
  have h : (fun a : S.WTrN hU k Ψ₁ Ψ₂ => a.tgt) =
      MPolyfold.whitneyMapOf (S.isLocalScDiffeo_trTgt Ψ₁ Ψ₂).isScSmoothMap ∘
        (wtrNEquiv hU k Ψ₁ Ψ₂).symm := funext wtrN_tgt_eq
  rw [h]
  exact (S.isLocalScDiffeo_trTgt Ψ₁ Ψ₂).whitneyMapOf.comp isLocalScDiffeo_wtrNEquiv_symm

/-- The unit of `M(⊕ᵏ TΨ, ⊕ᵏ TΨ)` is `⊕ᵏ Tu` under the identification. -/
theorem wtrOf_unit (Ψ : S.Unif) (v : Ψ.1.P.WhitneySum k) :
    wtrOf (GroupoidStr.TransitionSet.unit v : S.WTr hU k Ψ Ψ) = S.wtrUnit hU k Ψ v := by
  refine wtr_ext (MPolyfold.level_ext ?_) fun i => ?_
  · change _ = (S.transPolyfold Ψ Ψ).levelVal 1 (MPolyfold.whitneyProj
      (MPolyfold.whitneyMapOf (S.isScSmoothMap_trUnit Ψ) v))
    rw [MPolyfold.levelVal_whitneyProj_whitneyMapOf]
    rfl
  · rw [wtrVec_wtrUnit]
    rfl

theorem wtrN_unit_eq (Ψ : S.Unif) :
    (fun v : Ψ.1.P.WhitneySum k =>
      (GroupoidStr.TransitionSet.unit v : S.WTrN hU k Ψ Ψ)) =
      wtrNEquiv hU k Ψ Ψ ∘ MPolyfold.whitneyMapOf (S.isScSmoothMap_trUnit Ψ) := by
  funext v
  change _ = wtrTo (S.wtrUnit hU k Ψ v)
  rw [← wtrOf_unit]
  exact (wtrTo_wtrOf _).symm

/-- **Definition 17.1.8 (b) for `M(⊕ᵏ TΨ, ⊕ᵏ TΨ)`**: the unit map is sc-smooth. -/
theorem wtrN_isScSmoothMap_unit (Ψ : S.Unif) :
    (Ψ.1.P.whitneyPolyfold k).IsScSmoothMap (S.wtrNPolyfold hU k Ψ Ψ)
      fun v => (GroupoidStr.TransitionSet.unit v : S.WTrN hU k Ψ Ψ) := by
  rw [wtrN_unit_eq]
  exact isScSmoothMap_wtrNEquiv.comp (MPolyfold.isScSmoothMap_whitneyMapOf _)

/-- The inversion of `M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)` is `⊕ᵏ Tι` under the identification. -/
theorem wtrOf_inv (a : S.WTr hU k Ψ₁ Ψ₂) :
    wtrOf (GroupoidStr.TransitionSet.inv a) = S.wtrInv hU Ψ₁ Ψ₂ k (wtrOf a) := by
  refine wtr_ext (MPolyfold.level_ext ?_) fun i => ?_
  · rw [levelVal_wtrBase_wtrInv]
    rfl
  · rw [wtrVec_wtrInv]
    rfl

theorem wtrN_inv_eq :
    (fun a : S.WTrN hU k Ψ₁ Ψ₂ => (GroupoidStr.TransitionSet.inv a : S.WTrN hU k Ψ₂ Ψ₁)) =
      wtrNEquiv hU k Ψ₂ Ψ₁ ∘ MPolyfold.whitneyMapOf (S.isScSmoothMap_trInv Ψ₁ Ψ₂) ∘
        (wtrNEquiv hU k Ψ₁ Ψ₂).symm := by
  funext a
  change _ = wtrTo (S.wtrInv hU Ψ₁ Ψ₂ k (wtrOf a))
  exact (wtrTo_wtrOf _).symm.trans (congrArg wtrTo (wtrOf_inv a))

/-- **Definition 17.1.8 (b) for `M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂)`**: the inversion is sc-smooth. -/
theorem wtrN_isScSmoothMap_inv :
    (S.wtrNPolyfold hU k Ψ₁ Ψ₂).IsScSmoothMap (S.wtrNPolyfold hU k Ψ₂ Ψ₁)
      fun a : S.WTrN hU k Ψ₁ Ψ₂ => (GroupoidStr.TransitionSet.inv a : S.WTrN hU k Ψ₂ Ψ₁) := by
  rw [wtrN_inv_eq]
  exact isScSmoothMap_wtrNEquiv.comp ((MPolyfold.isScSmoothMap_whitneyMapOf _).comp
    isLocalScDiffeo_wtrNEquiv_symm.isScSmoothMap)

theorem regSub_comp_val {φ ψ : C.toGroupoidStr.morOn (S.regSet 1)}
    (h : C.toGroupoidStr.src φ.1 = C.toGroupoidStr.tgt ψ.1) :
    ((S.regSub 1).comp φ ψ).1 = C.toGroupoidStr.comp φ.1 ψ.1 := by
  simp only [GroupoidStr.fullSub, dif_pos h]

/-- **Definition 17.1.8 (c) for `M(⊕ᵏ TΨ, ⊕ᵏ TΨ')`** (the point left open in
`WhitneySumStructure.lean`): the multiplication
`M(⊕ᵏ TΨ₂, ⊕ᵏ TΨ₃) ₛ×ₜ M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₂) → M(⊕ᵏ TΨ₁, ⊕ᵏ TΨ₃)` is sc-smooth.  Near a point it is
`⊕ᵏ T(b ↦ m(σ(t b), b))` (Definition 17.1.8 (c) for `M` on a sheet `σ` of `s`) composed with
`pr₂`, as for `M(TΨ, TΨ')` (`tangentTr_isScSmoothMap_mul`). -/
theorem wtrN_isScSmoothMap_mul :
    MPolyfold.IsScSmoothOnFibredProduct (S.wtrNPolyfold hU k Ψ₂ Ψ₃)
      (S.wtrNPolyfold hU k Ψ₁ Ψ₂) (S.wtrNPolyfold hU k Ψ₁ Ψ₃)
      wtrN_isLocalScDiffeo_src wtrN_isLocalScDiffeo_tgt.isScSmoothMap
      fun p => (GroupoidStr.TransitionSet.mul p : S.WTrN hU k Ψ₁ Ψ₃) := by
  classical
  refine MPolyfold.isScSmoothOnFibredProduct_of_local _ _ fun a₀ => ?_
  set E₁ := wtrNEquiv hU k Ψ₂ Ψ₃
  set E₂ := wtrNEquiv hU k Ψ₁ Ψ₂
  set E₃ := wtrNEquiv hU k Ψ₁ Ψ₃
  have hbase : ∀ p : MPolyfold.fibredProduct (fun a : S.WTrN hU k Ψ₂ Ψ₃ => a.src)
      (fun a : S.WTrN hU k Ψ₁ Ψ₂ => a.tgt),
      ((S.transPolyfold Ψ₂ Ψ₃).levelVal 1 (MPolyfold.whitneyProj (E₁.symm p.1.1))).src =
        ((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (MPolyfold.whitneyProj (E₂.symm p.1.2))).tgt :=
    fun p => by
      rw [levelVal_whitneyProj_wtrNEquiv_symm, levelVal_whitneyProj_wtrNEquiv_symm]
      exact congrArg (fun v => Ψ₂.1.P.levelVal 1 (MPolyfold.whitneyProj v)) p.2
  obtain ⟨U, V, σ, hU₀, hd⟩ := S.isLocalScDiffeo_trSrc Ψ₂ Ψ₃
    ((S.transPolyfold Ψ₂ Ψ₃).levelVal 1 (MPolyfold.whitneyProj (E₁.symm a₀.1.1)))
  have hg₀ := (S.isLocalScDiffeo_trTgt Ψ₁ Ψ₂).isScSmoothMap
  let _ := MPolyfold.paracompactSpace_prod (S.transPolyfold Ψ₂ Ψ₃) (S.transPolyfold Ψ₁ Ψ₂)
  let p₀ : MPolyfold.fibredProduct (fun a : S.Tr Ψ₂ Ψ₃ => a.src)
      (fun a : S.Tr Ψ₁ Ψ₂ => a.tgt) :=
    ⟨((S.transPolyfold Ψ₂ Ψ₃).levelVal 1 (MPolyfold.whitneyProj (E₁.symm a₀.1.1)),
      (S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (MPolyfold.whitneyProj (E₂.symm a₀.1.2))), hbase a₀⟩
  let d := MPolyfold.fibredSubDataL hd hg₀
  let r : S.Tr Ψ₁ Ψ₂ → MPolyfold.fibredProduct (fun a : S.Tr Ψ₂ Ψ₃ => a.src)
      (fun a : S.Tr Ψ₁ Ψ₂ => a.tgt) := fun b => d.retractInto p₀ (σ b.tgt, b)
  have hr : ∀ b : S.Tr Ψ₁ Ψ₂, b.tgt ∈ V → (r b : S.Tr Ψ₂ Ψ₃ × S.Tr Ψ₁ Ψ₂) = (σ b.tgt, b) :=
    fun b hb => d.retractInto_val p₀ ⟨hd.mapsTo_inv hb, hb⟩
  let k₀ : S.Tr Ψ₁ Ψ₂ → S.Tr Ψ₁ Ψ₃ := fun b => S.toTr (GroupoidStr.TransitionSet.mul (r b))
  have hk₀ : (S.transPolyfold Ψ₁ Ψ₂).IsScSmoothOn (S.transPolyfold Ψ₁ Ψ₃) k₀
      ((fun b : S.Tr Ψ₁ Ψ₂ => b.tgt) ⁻¹' V) :=
    (S.isScSmoothMap_trMul Ψ₁ Ψ₂ Ψ₃).isScSmoothOn_sheet hd p₀
  have hk₀src : ∀ b : S.Tr Ψ₁ Ψ₂, b.tgt ∈ V → (k₀ b).src = b.src := fun b hb =>
    congrArg (fun q : S.Tr Ψ₂ Ψ₃ × S.Tr Ψ₁ Ψ₂ => q.2.src) (hr b hb)
  have hk₀mor : ∀ b : S.Tr Ψ₁ Ψ₂, b.tgt ∈ V →
      (k₀ b).mor = C.toGroupoidStr.comp (σ b.tgt).mor b.mor := fun b hb =>
    congrArg (fun q : S.Tr Ψ₂ Ψ₃ × S.Tr Ψ₁ Ψ₂ => C.toGroupoidStr.comp q.1.mor q.2.mor) (hr b hb)
  have hV : IsOpen ((fun b : S.Tr Ψ₁ Ψ₂ => b.tgt) ⁻¹' V) := hk₀.isOpen
  let W : Set (S.WTrN hU k Ψ₁ Ψ₂) :=
    E₂.symm ⁻¹' (S.transPolyfold Ψ₁ Ψ₂).whitneyPreimage k ((fun b : S.Tr Ψ₁ Ψ₂ => b.tgt) ⁻¹' V)
  have hWo : IsOpen W := (MPolyfold.isOpen_whitneyPreimage hV).preimage E₂.symm.continuous
  refine ⟨{p | E₁.symm p.1 ∈ (S.transPolyfold Ψ₂ Ψ₃).whitneyPreimage k U ∧ p.2 ∈ W}, W,
    E₃ ∘ MPolyfold.whitneyMapOn hk₀ (E₃.symm (GroupoidStr.TransitionSet.mul a₀)) ∘ E₂.symm,
    ((MPolyfold.isOpen_whitneyPreimage hd.isOpen_source).preimage
      (E₁.symm.continuous.comp continuous_fst)).inter (hWo.preimage continuous_snd),
    ⟨hU₀, ?_⟩, ?_, fun p hp => ⟨hp.2, ?_⟩⟩
  · change (S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (MPolyfold.whitneyProj (E₂.symm a₀.1.2)) ∈
      (fun b : S.Tr Ψ₁ Ψ₂ => b.tgt) ⁻¹' V
    change ((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (MPolyfold.whitneyProj (E₂.symm a₀.1.2))).tgt ∈ V
    rw [← hbase a₀]
    exact hd.mapsTo hU₀
  · exact MPolyfold.IsScSmoothOn.comp isScSmoothMap_wtrNEquiv
      (MPolyfold.IsScSmoothOn.comp (MPolyfold.isScSmoothOn_whitneyMapOn hk₀ _)
        (isLocalScDiffeo_wtrNEquiv_symm.isScSmoothMap.mono hWo (subset_univ _))
        fun x hx => hx) (mapsTo_univ _ _)
  · set x := E₂.symm p.1.2 with hx_def
    have hx : x ∈ (S.transPolyfold Ψ₁ Ψ₂).whitneyPreimage k
        ((fun b : S.Tr Ψ₁ Ψ₂ => b.tgt) ⁻¹' V) := hp.2
    have hσ : σ ((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (MPolyfold.whitneyProj x)).tgt =
        (S.transPolyfold Ψ₂ Ψ₃).levelVal 1 (MPolyfold.whitneyProj (E₁.symm p.1.1)) := by
      rw [← hbase p]
      exact hd.left_inv _ hp.1
    have hcomp : (S.whitneyCatGroupoid k).src p.1.1.mor = (S.whitneyCatGroupoid k).tgt p.1.2.mor :=
      GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt p.2
    have hm : C.toGroupoidStr.src p.1.1.mor.base.1 = C.toGroupoidStr.tgt p.1.2.mor.base.1 :=
      congrArg (fun x => x.base.1) hcomp
    refine WTr.ext' ?_ (Subtype.ext ?_)
    · change p.1.2.src = (E₃ (MPolyfold.whitneyMapOn hk₀ _ x)).src
      rw [wtrNEquiv_src, wtrN_src_eq p.1.2, ← hx_def]
      refine MPolyfold.whitneySum_ext (MPolyfold.level_ext ?_) fun i => ?_
      · rw [MPolyfold.levelVal_whitneyProj_whitneyMapOf, MPolyfold.levelVal_whitneyProj_whitneyMapOf,
          MPolyfold.levelVal_whitneyProj_whitneyMapOn hk₀ _ hx]
        exact (hk₀src _ hx).symm
      · rw [MPolyfold.whitneyVec_whitneyMapOf, MPolyfold.whitneyVec_whitneyMapOf,
          MPolyfold.whitneyVec_whitneyMapOn hk₀ _ hx]
        exact (MPolyfold.tangentMap_tangentMapOn_of_eqOn hk₀ _ _ (fun b hb => hk₀src b hb)
          (MPolyfold.whitneyVec_mem_tangentPreimage hx i)).symm
    · change (S.tangentCatProj.whitneyComp k p.1.1.mor p.1.2.mor).base.1 = (E₃ (MPolyfold.whitneyMapOn hk₀ _ x)).mor.base.1
      rw [GroupoidFunctor.whitneyComp_base hcomp, regSub_comp_val hm, wtrNEquiv_mor_base,
        MPolyfold.levelVal_whitneyProj_whitneyMapOn hk₀ _ hx, hk₀mor _ hx, hσ]
      rfl

end WhitneyTransitionPolyfold

/-! ### The polyfold structure `(⊕ᵏ TF, M)` of `⊕ᵏ TC` -/

section WhitneyConstruction

variable (hU : S.HasUniformizers) (k : ℕ) (hcont : ∀ Ψ : S.Unif, Continuous (S.hat Ψ))

theorem whitneyUnif_obj (Ψ : S.Unif) :
    (S.whitneyUnif hU k hcont Ψ).obj = S.whitneyUnifObj hU k Ψ := rfl

/-- `⊕ᵏ TΨ` is at `β` when `Ψ ∈ F(⊕ᵏ P(β))`: every object of `⊕ᵏ TC` over `Ψ(q)` is
`⊕ᵏ TΨ(v)`. -/
theorem whitneyUnif_isAt {β : (S.whitneyGCT hU k hcont).Obj} {Ψ : S.Unif}
    (hΨ : Ψ.1 ∈ S.F (show S.tangentCatProj.WhitneyObj k from β).base.1) :
    (S.whitneyUnif hU k hcont Ψ).IsAt β := by
  let β' : S.tangentCatProj.WhitneyObj k := β
  obtain ⟨q, hq⟩ := S.isAt _ Ψ.1 hΨ
  have hb : ∀ i, Ψ.1.obj q = (β'.vec i).base := fun i =>
    hq.trans (congrArg Subtype.val (β'.obj_vec i)).symm
  choose kv hkb hkv using fun i => exists_tangentUnifObj_eq hU Ψ (β'.vec i) q (hb i)
  have hq1 : q ∈ Ψ.1.P.levelSet 1 :=
    (hasRegularity_iff Ψ (hq ▸ C.toGroupoidStr.isomorphic_refl _ : C.toGroupoidStr.Isomorphic
      (Ψ.1.obj q) β'.base.1) 1).1 β'.base.2
  let v : Ψ.1.P.WhitneySum k :=
    MPolyfold.whitneyMk (Ψ.1.P.levelMk 1 q hq1) kv fun i => MPolyfold.level_ext (hkb i)
  exact ⟨v, GroupoidFunctor.WhitneyObj.ext' (Subtype.ext hq) (funext hkv)⟩

/-- **`⊕ᵏ TF(β)`** (p. 819): the uniformizers `⊕ᵏ TΨ` of the `Ψ ∈ F(⊕ᵏ P(β))`. -/
def whitneyF (β : (S.whitneyGCT hU k hcont).Obj) :
    Set (S.whitneyGCT hU k hcont).LocalUniformizer :=
  {L | ∃ Ψ : S.Unif, Ψ.1 ∈ S.F (show S.tangentCatProj.WhitneyObj k from β).base.1 ∧
    L = S.whitneyUnif hU k hcont Ψ}

theorem exists_whitneyData (L : GCT.Unif (S.whitneyF hU k hcont)) :
    ∃ Ψ : S.Unif, L.1 = S.whitneyUnif hU k hcont Ψ := by
  obtain ⟨L, β, Ψ, -, rfl⟩ := L
  exact ⟨Ψ, rfl⟩

/-- The uniformizer `Ψ ∈ F` chosen for `L ∈ ⊕ᵏ TF` with `L = ⊕ᵏ TΨ`. -/
def whitneyData (L : GCT.Unif (S.whitneyF hU k hcont)) : S.Unif :=
  (S.exists_whitneyData hU k hcont L).choose

theorem whitneyData_eq (L : GCT.Unif (S.whitneyF hU k hcont)) :
    L.1 = S.whitneyUnif hU k hcont (S.whitneyData hU k hcont L) :=
  (S.exists_whitneyData hU k hcont L).choose_spec

/-- The topology of `M(L, L')` for `L = ⊕ᵏ TΨ`, `L' = ⊕ᵏ TΨ'`. -/
@[instance_reducible]
def whitneyTopOf : ∀ (L L' : (S.whitneyGCT hU k hcont).LocalUniformizer) (Ψ Ψ' : S.Unif),
    L = S.whitneyUnif hU k hcont Ψ → L' = S.whitneyUnif hU k hcont Ψ' →
      TopologicalSpace (L.Trans L')
  | _, _, Ψ, Ψ', rfl, rfl => (inferInstance : TopologicalSpace (S.WTrN hU k Ψ Ψ'))

theorem whitneyT2Of : ∀ (L L' : (S.whitneyGCT hU k hcont).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (h : L = S.whitneyUnif hU k hcont Ψ) (h' : L' = S.whitneyUnif hU k hcont Ψ'),
    @T2Space (L.Trans L') (S.whitneyTopOf hU k hcont L L' Ψ Ψ' h h')
  | _, _, Ψ, Ψ', rfl, rfl => (inferInstance : T2Space (S.WTrN hU k Ψ Ψ'))

theorem whitneyParaOf : ∀ (L L' : (S.whitneyGCT hU k hcont).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (h : L = S.whitneyUnif hU k hcont Ψ) (h' : L' = S.whitneyUnif hU k hcont Ψ'),
    @ParacompactSpace (L.Trans L') (S.whitneyTopOf hU k hcont L L' Ψ Ψ' h h')
  | _, _, Ψ, Ψ', rfl, rfl => (inferInstance : ParacompactSpace (S.WTrN hU k Ψ Ψ'))

/-- The M-polyfold `M(L, L')` for `L = ⊕ᵏ TΨ`, `L' = ⊕ᵏ TΨ'`: `wtrNPolyfold`. -/
def whitneyMOf : ∀ (L L' : (S.whitneyGCT hU k hcont).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (h : L = S.whitneyUnif hU k hcont Ψ) (h' : L' = S.whitneyUnif hU k hcont Ψ'),
    @MPolyfold (L.Trans L') (S.whitneyTopOf hU k hcont L L' Ψ Ψ' h h')
      (S.whitneyT2Of hU k hcont L L' Ψ Ψ' h h') (S.whitneyParaOf hU k hcont L L' Ψ Ψ' h h')
  | _, _, Ψ, Ψ', rfl, rfl => S.wtrNPolyfold hU k Ψ Ψ'

theorem whitneySrcOf : ∀ (L L' : (S.whitneyGCT hU k hcont).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (h : L = S.whitneyUnif hU k hcont Ψ) (h' : L' = S.whitneyUnif hU k hcont Ψ'),
    letI := S.whitneyTopOf hU k hcont L L' Ψ Ψ' h h'
    letI := S.whitneyT2Of hU k hcont L L' Ψ Ψ' h h'
    letI := S.whitneyParaOf hU k hcont L L' Ψ Ψ' h h'
    (S.whitneyMOf hU k hcont L L' Ψ Ψ' h h').IsLocalScDiffeo L.P GroupoidStr.TransitionSet.src
  | _, _, _, _, rfl, rfl => wtrN_isLocalScDiffeo_src

theorem whitneyTgtOf : ∀ (L L' : (S.whitneyGCT hU k hcont).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (h : L = S.whitneyUnif hU k hcont Ψ) (h' : L' = S.whitneyUnif hU k hcont Ψ'),
    letI := S.whitneyTopOf hU k hcont L L' Ψ Ψ' h h'
    letI := S.whitneyT2Of hU k hcont L L' Ψ Ψ' h h'
    letI := S.whitneyParaOf hU k hcont L L' Ψ Ψ' h h'
    (S.whitneyMOf hU k hcont L L' Ψ Ψ' h h').IsLocalScDiffeo L'.P GroupoidStr.TransitionSet.tgt
  | _, _, _, _, rfl, rfl => wtrN_isLocalScDiffeo_tgt

theorem whitneyUnitOf : ∀ (L : (S.whitneyGCT hU k hcont).LocalUniformizer) (Ψ : S.Unif)
    (h : L = S.whitneyUnif hU k hcont Ψ),
    letI := S.whitneyTopOf hU k hcont L L Ψ Ψ h h
    letI := S.whitneyT2Of hU k hcont L L Ψ Ψ h h
    letI := S.whitneyParaOf hU k hcont L L Ψ Ψ h h
    L.P.IsScSmoothMap (S.whitneyMOf hU k hcont L L Ψ Ψ h h) GroupoidStr.TransitionSet.unit
  | _, Ψ, rfl => wtrN_isScSmoothMap_unit Ψ

theorem whitneyInvOf : ∀ (L L' : (S.whitneyGCT hU k hcont).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (h : L = S.whitneyUnif hU k hcont Ψ) (h' : L' = S.whitneyUnif hU k hcont Ψ'),
    letI := S.whitneyTopOf hU k hcont L L' Ψ Ψ' h h'
    letI := S.whitneyT2Of hU k hcont L L' Ψ Ψ' h h'
    letI := S.whitneyParaOf hU k hcont L L' Ψ Ψ' h h'
    letI := S.whitneyTopOf hU k hcont L' L Ψ' Ψ h' h
    letI := S.whitneyT2Of hU k hcont L' L Ψ' Ψ h' h
    letI := S.whitneyParaOf hU k hcont L' L Ψ' Ψ h' h
    (S.whitneyMOf hU k hcont L L' Ψ Ψ' h h').IsScSmoothMap (S.whitneyMOf hU k hcont L' L Ψ' Ψ h' h)
      GroupoidStr.TransitionSet.inv
  | _, _, _, _, rfl, rfl => wtrN_isScSmoothMap_inv

theorem whitneyMulOf : ∀ (L L' L'' : (S.whitneyGCT hU k hcont).LocalUniformizer)
    (Ψ Ψ' Ψ'' : S.Unif) (h : L = S.whitneyUnif hU k hcont Ψ)
    (h' : L' = S.whitneyUnif hU k hcont Ψ') (h'' : L'' = S.whitneyUnif hU k hcont Ψ''),
    letI := S.whitneyTopOf hU k hcont L' L'' Ψ' Ψ'' h' h''
    letI := S.whitneyT2Of hU k hcont L' L'' Ψ' Ψ'' h' h''
    letI := S.whitneyParaOf hU k hcont L' L'' Ψ' Ψ'' h' h''
    letI := S.whitneyTopOf hU k hcont L L' Ψ Ψ' h h'
    letI := S.whitneyT2Of hU k hcont L L' Ψ Ψ' h h'
    letI := S.whitneyParaOf hU k hcont L L' Ψ Ψ' h h'
    letI := S.whitneyTopOf hU k hcont L L'' Ψ Ψ'' h h''
    letI := S.whitneyT2Of hU k hcont L L'' Ψ Ψ'' h h''
    letI := S.whitneyParaOf hU k hcont L L'' Ψ Ψ'' h h''
    MPolyfold.IsScSmoothOnFibredProduct (S.whitneyMOf hU k hcont L' L'' Ψ' Ψ'' h' h'')
      (S.whitneyMOf hU k hcont L L' Ψ Ψ' h h') (S.whitneyMOf hU k hcont L L'' Ψ Ψ'' h h'')
      (S.whitneySrcOf hU k hcont L' L'' Ψ' Ψ'' h' h'')
      (S.whitneyTgtOf hU k hcont L L' Ψ Ψ' h h').isScSmoothMap GroupoidStr.TransitionSet.mul
  | _, _, _, _, _, _, rfl, rfl, rfl => wtrN_isScSmoothMap_mul

/-- **2021 Proposition 17.6.1, p. 818, the polyfold structure `(⊕ᵏ TF, M)` on `⊕ᵏ TC`**:
`⊕ᵏ TF(β)` consists of the uniformizers `⊕ᵏ TΨ : G ⋉ ⊕ᵏ TO → ⊕ᵏ TC` of the `Ψ ∈ F(⊕ᵏ P(β))`, and
`M(⊕ᵏ TΨ, ⊕ᵏ TΨ')` carries the M-polyfold structure of Part I's `⊕ₖ T M(Ψ, Ψ')` (for the chosen
`Ψ = whitneyData L` with `L = ⊕ᵏ TΨ`). -/
def whitneyConstruction : (S.whitneyGCT hU k hcont).PolyfoldConstruction where
  F := S.whitneyF hU k hcont
  isAt β L hL := by
    obtain ⟨Ψ, hΨ, rfl⟩ := hL
    exact S.whitneyUnif_isAt hU k hcont hΨ
  topM L L' := S.whitneyTopOf hU k hcont L.1 L'.1 (S.whitneyData hU k hcont L)
    (S.whitneyData hU k hcont L') (S.whitneyData_eq hU k hcont L) (S.whitneyData_eq hU k hcont L')
  t2M L L' := S.whitneyT2Of hU k hcont L.1 L'.1 (S.whitneyData hU k hcont L)
    (S.whitneyData hU k hcont L') (S.whitneyData_eq hU k hcont L) (S.whitneyData_eq hU k hcont L')
  paraM L L' := S.whitneyParaOf hU k hcont L.1 L'.1 (S.whitneyData hU k hcont L)
    (S.whitneyData hU k hcont L') (S.whitneyData_eq hU k hcont L) (S.whitneyData_eq hU k hcont L')
  M L L' := S.whitneyMOf hU k hcont L.1 L'.1 (S.whitneyData hU k hcont L)
    (S.whitneyData hU k hcont L') (S.whitneyData_eq hU k hcont L) (S.whitneyData_eq hU k hcont L')
  isLocalScDiffeo_src L L' := S.whitneySrcOf hU k hcont L.1 L'.1 (S.whitneyData hU k hcont L)
    (S.whitneyData hU k hcont L') (S.whitneyData_eq hU k hcont L) (S.whitneyData_eq hU k hcont L')
  isLocalScDiffeo_tgt L L' := S.whitneyTgtOf hU k hcont L.1 L'.1 (S.whitneyData hU k hcont L)
    (S.whitneyData hU k hcont L') (S.whitneyData_eq hU k hcont L) (S.whitneyData_eq hU k hcont L')
  isScSmoothMap_unit L := S.whitneyUnitOf hU k hcont L.1 (S.whitneyData hU k hcont L)
    (S.whitneyData_eq hU k hcont L)
  isScSmoothMap_inv L L' := S.whitneyInvOf hU k hcont L.1 L'.1 (S.whitneyData hU k hcont L)
    (S.whitneyData hU k hcont L') (S.whitneyData_eq hU k hcont L) (S.whitneyData_eq hU k hcont L')
  isScSmoothMap_mul L L' L'' := S.whitneyMulOf hU k hcont L.1 L'.1 L''.1
    (S.whitneyData hU k hcont L) (S.whitneyData hU k hcont L') (S.whitneyData hU k hcont L'')
    (S.whitneyData_eq hU k hcont L) (S.whitneyData_eq hU k hcont L')
    (S.whitneyData_eq hU k hcont L'')

theorem whitneyConstruction_hasUniformizers :
    (S.whitneyConstruction hU k hcont).HasUniformizers := fun β => by
  obtain ⟨L, hL⟩ := hU (show S.tangentCatProj.WhitneyObj k from β).base.1
  have hα : ∃ α, L ∈ S.F α := ⟨_, hL⟩
  exact ⟨S.whitneyUnif hU k hcont ⟨L, hα⟩, ⟨L, hα⟩, hL, rfl⟩

/-- **The topology of `|⊕ᵏ TC|` is the only one for which every `|⊕ᵏ TΨ|` is an open
embedding** (`HasUniformizers`: the `|⊕ᵏ TΨ|` cover `|⊕ᵏ TC|`). -/
theorem eq_whitneyOrbitTopology (t : TopologicalSpace (S.whitneyCatGroupoid k).OrbitSpace)
    (ht : ∀ Ψ : S.Unif, @IsOpenEmbedding _ _ _ t (S.whitneyOrbitChart hU k hcont Ψ)) :
    t = S.whitneyOrbitTopology hU k hcont := by
  refine eq_chartTopology _ (fun y => ?_) t ht
  induction y using Quotient.inductionOn with | h β => ?_
  obtain ⟨L, hL⟩ := hU β.base.1
  let Ψ : S.Unif := ⟨L, _, hL⟩
  obtain ⟨v, hv⟩ := S.whitneyUnif_isAt hU k hcont (β := β) (Ψ := Ψ) hL
  exact ⟨Ψ, (S.whitneyTranslation Ψ k).π v, congrArg (S.whitneyCatGroupoid k).π hv⟩

end WhitneyConstruction

/-! ### The bundle `⊕ᵏ P : ⊕ᵏ TC → C¹` -/

section WhitneyBundle

variable {hU : S.HasUniformizers} {k : ℕ} (hc : S.HasCoveringUniformizers)

variable (hU k) in
/-- **The bundle projection `M(⊕ᵏ TΨ, ⊕ᵏ TΨ') → M(Ψ¹, Ψ'¹)`** (p. 819): `(v, Φ, v') ↦ (x, φ, x')`,
read in `M(Ψ, Ψ')¹ = M(Ψ¹, Ψ'¹)` (Theorem 17.1.28). -/
def whitneyTrBundleProj {Ψ Ψ' : S.Unif} (a : S.WTrN hU k Ψ Ψ') : S.LTr hc Ψ Ψ' :=
  (S.ltrHomeomorph hc Ψ Ψ').symm (MPolyfold.whitneyProj ((wtrNEquiv hU k Ψ Ψ').symm a))

/-- **`M(⊕ᵏ TΨ, ⊕ᵏ TΨ') → M(Ψ¹, Ψ'¹)` is sc-smooth.** -/
theorem isScSmoothMap_whitneyTrBundleProj (Ψ Ψ' : S.Unif) :
    (S.wtrNPolyfold hU k Ψ Ψ').IsScSmoothMap (S.ltrPolyfold hc Ψ Ψ')
      (S.whitneyTrBundleProj hU k hc (Ψ := Ψ) (Ψ' := Ψ')) :=
  (S.ltr_isScSmoothMap_homeomorph_symm hc Ψ Ψ').comp
    (MPolyfold.isScSmoothMap_whitneyProj.comp isLocalScDiffeo_wtrNEquiv_symm.isScSmoothMap)

/-- The bundle projection commutes with `s`, `t` (the projections `⊕ᵏ TO → O¹`) and keeps the
morphism of `C`. -/
theorem whitneyTrBundleProj_spec {Ψ Ψ' : S.Unif} (a : S.WTrN hU k Ψ Ψ') :
    (S.whitneyTrBundleProj hU k hc a).src = MPolyfold.whitneyProj a.src ∧
      (S.whitneyTrBundleProj hU k hc a).tgt = MPolyfold.whitneyProj a.tgt ∧
      (S.whitneyTrBundleProj hU k hc a).mor.1 = a.mor.base.1 :=
  ⟨MPolyfold.level_ext rfl, MPolyfold.level_ext rfl, rfl⟩

end WhitneyBundle

/-! ### Proposition 17.6.1 -/

/-- **2021 Proposition 17.6.1, p. 818** (with the hypothesis `hcont`: every `Ψ̂` is continuous, as in
Theorem 17.2.17, `theorem_17_2_17_hyp`): for a polyfold structure `(F, M)` on `C` with
`F(α) ≠ ∅`, the `k`-fold Whitney sum `⊕ᵏ TC` is a GCT (`whitneyGCT`, the topology of `|⊕ᵏ TC|`
being the only one for which the `|⊕ᵏ TΨ|` are open embeddings) and carries the polyfold structure
`(⊕ᵏ TF, M)` (`whitneyConstruction`), `⊕ᵏ TF(β) = {⊕ᵏ TΨ | Ψ ∈ F(⊕ᵏ P(β))}`, `⊕ᵏ TF(β) ≠ ∅`, with
`M(⊕ᵏ TΨ, ⊕ᵏ TΨ')` sc-diffeomorphic to Part I's `⊕ₖ T M(Ψ, Ψ')`; and `⊕ᵏ P : ⊕ᵏ TC → C¹` is a
polyfold bundle in the reading of the module docstring: `⊕ᵏ P ∘ ⊕ᵏ TΨ = Ψ¹ ∘ ⊕ᵏ p`, on the fibres
`⊕ᵏ TΨ` is `TΨ` in each entry, `|⊕ᵏ P|⁻¹` of the footprint of `Ψ¹` is the footprint of `⊕ᵏ TΨ`,
the bundle projections `M(⊕ᵏ TΨ, ⊕ᵏ TΨ') → M(Ψ¹, Ψ'¹)` are sc-smooth and compatible with `s`,
`t` and the morphisms, and `|⊕ᵏ P| : |⊕ᵏ TC| → |C¹|` is continuous. -/
theorem proposition_17_6_1_hyp (hU : S.HasUniformizers)
    (hcont : ∀ Ψ : S.Unif, Continuous (S.hat Ψ)) (k : ℕ) :
    (S.whitneyGCT hU k hcont).toGroupoidStr = S.whitneyCatGroupoid k ∧
    (∀ t : TopologicalSpace (S.whitneyCatGroupoid k).OrbitSpace,
      (∀ Ψ : S.Unif, @IsOpenEmbedding _ _ _ t (S.whitneyOrbitChart hU k hcont Ψ)) →
        t = S.whitneyOrbitTopology hU k hcont) ∧
    (S.whitneyConstruction hU k hcont).HasUniformizers ∧
    (∀ β L, L ∈ (S.whitneyConstruction hU k hcont).F β ↔
      ∃ Ψ : S.Unif, Ψ.1 ∈ S.F (show S.tangentCatProj.WhitneyObj k from β).base.1 ∧
        L = S.whitneyUnif hU k hcont Ψ) ∧
    (∀ Ψ Ψ' : S.Unif,
      ((S.transPolyfold Ψ Ψ').whitneyPolyfold k).IsScDiffeoOn (S.wtrNPolyfold hU k Ψ Ψ')
        (wtrNEquiv hU k Ψ Ψ') (wtrNEquiv hU k Ψ Ψ').symm univ univ) ∧
    (∀ Ψ : S.Unif,
      (S.whitneyCatProj k).comp (S.whitneyUnif hU k hcont Ψ).functor = S.whitneyBaseFunctor Ψ k) ∧
    (∀ (Ψ : S.Unif) v i, ((S.whitneyUnif hU k hcont Ψ).obj v).vec i =
      S.tangentUnifObj hU Ψ (MPolyfold.whitneyVec v i)) ∧
    (∀ Ψ : S.Unif, (S.whitneyCatProj k).orbitMap ⁻¹'
        (S.levelOneUnif (S.hasCoveringUniformizers_of_hasUniformizers hU) Ψ).footprint =
      (S.whitneyUnif hU k hcont Ψ).footprint) ∧
    (∀ Ψ Ψ' : S.Unif, (S.wtrNPolyfold hU k Ψ Ψ').IsScSmoothMap
      (S.ltrPolyfold (S.hasCoveringUniformizers_of_hasUniformizers hU) Ψ Ψ')
      (S.whitneyTrBundleProj hU k (S.hasCoveringUniformizers_of_hasUniformizers hU)
        (Ψ := Ψ) (Ψ' := Ψ'))) ∧
    (∀ (Ψ Ψ' : S.Unif) (a : S.WTrN hU k Ψ Ψ'),
      (S.whitneyTrBundleProj hU k (S.hasCoveringUniformizers_of_hasUniformizers hU) a).src =
          MPolyfold.whitneyProj a.src ∧
        (S.whitneyTrBundleProj hU k (S.hasCoveringUniformizers_of_hasUniformizers hU) a).tgt =
          MPolyfold.whitneyProj a.tgt ∧
        (S.whitneyTrBundleProj hU k (S.hasCoveringUniformizers_of_hasUniformizers hU) a).mor.1 =
          a.mor.base.1) ∧
    @Continuous _ _ (S.whitneyOrbitTopology hU k hcont)
      (S.levelOneTopology (S.hasCoveringUniformizers_of_hasUniformizers hU))
      (S.whitneyCatProj k).orbitMap :=
  ⟨rfl, S.eq_whitneyOrbitTopology hU k hcont, S.whitneyConstruction_hasUniformizers hU k hcont,
    fun _ _ => Iff.rfl, fun _ _ => isScDiffeoOn_wtrNEquiv, fun _ => rfl, fun _ _ _ => rfl,
    fun Ψ => S.preimage_footprint_eq_range hU k hcont Ψ,
    fun Ψ Ψ' => S.isScSmoothMap_whitneyTrBundleProj _ Ψ Ψ',
    fun _ _ a => S.whitneyTrBundleProj_spec _ a, S.continuous_orbitMap_whitneyCatProj hU k hcont⟩

/-! ### The witness: the reflection `ℤ/2 ⋉ ℝ` -/

section Reflection

open EpGroupoid.Examples MPolyfold

/-- **The polyfold structure `(⊕ᵏ TF, M)` of the reflection witness** (`ℤ/2` acting on `ℝ` by
`x ↦ -x`; every `Ψ̂` is continuous, `reflection_continuous_hat_all`). -/
def reflectionWhitneyConstruction (k : ℕ) :
    (reflectionConstruction.whitneyGCT reflectionConstruction_hasUniformizers k
      reflection_continuous_hat_all).PolyfoldConstruction :=
  reflectionConstruction.whitneyConstruction reflectionConstruction_hasUniformizers k
    reflection_continuous_hat_all

/-- **The hypotheses of `proposition_17_6_1_hyp` are satisfiable, non-degenerately**: for the
reflection witness the structure `(⊕² TF, M)` has uniformizers at every object, and the
uniformizer `⊕² TΨ₀` maps `(−1, (e, e))` to a morphism of `⊕² TC` whose source and target differ
(the isotropy `ℤ/2` of `0` acts non-trivially on `⊕² T₀ℝ`). -/
theorem reflection_proposition_17_6_1 :
    (reflectionWhitneyConstruction 2).HasUniformizers ∧
      (reflectionConstruction.whitneyCatGroupoid 2).src
          ((reflectionConstruction.whitneyUnif reflectionConstruction_hasUniformizers 2
            reflection_continuous_hat_all reflectionUnif).mor (ULift.up reflNegOne, reflWhitneyVec)) ≠
        (reflectionConstruction.whitneyCatGroupoid 2).tgt
          ((reflectionConstruction.whitneyUnif reflectionConstruction_hasUniformizers 2
            reflection_continuous_hat_all reflectionUnif).mor (ULift.up reflNegOne, reflWhitneyVec)) :=
  ⟨reflectionConstruction.whitneyConstruction_hasUniformizers _ _ _,
    reflection_whitneyUnif_nondegenerate⟩

end Reflection

end GCT.PolyfoldConstruction

end Polyfold
