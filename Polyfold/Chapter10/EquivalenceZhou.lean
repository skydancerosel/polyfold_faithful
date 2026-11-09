import Polyfold.Chapter10.EquivalenceReduced
import Polyfold.Chapter9.Tangent

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, §10.1 "Equivalences", pp. 475–477: **Proposition 10.1.17** and the
reduction of **Proposition 10.1.19** to Proposition 10.1.9 (all new in the 2021 edition).

# The Zhou condition under equivalences

## The text, paraphrased

(Proposition 10.1.17, p. 475) If `F : X → Y` is an equivalence and one of `X`, `Y` satisfies the
Zhou condition (Definition 7.4.5: for a smooth `x` and `g ∈ G_x`, `Tg = id` on `T_xX` implies
`g ∈ T_x`), so does the other.  *Proof* (text): for smooth `y`, `ψ : F(x) → y`, the isomorphism
`τ(g) = ψ ∘ F(g) ∘ ψ⁻¹ : G_x → G_y` maps `T_x` onto `T_y`, and `σ ∘ F` (`σ = t ∘ (s|U(ψ))⁻¹`)
intertwines the natural representations, so `Tg = id` iff `Tτ(g) = id`.  (Proposition 10.1.19,
p. 477) (SLR) passes along equivalences.  *Proof* (text): as for Proposition 10.1.18, with the
lifts `Fⁱ` and Proposition 10.1.9 ((LR) along equivalences).

## What is formalized

* `EpGroupoid.mem_smoothSet_src_iff`, `mem_smoothSet_tgt_iff`; `EpFunctor.tangentMor_mor`
  (naturality `T(F(φ)) ∘ TF = TF ∘ Tφ` on `T_{s(φ)}X`).
* `IsEquivalence.isZhou_of_isZhou`, `isZhou_of_isZhou_right`, and
  `EpFunctor.proposition_10_1_17` (**Proposition 10.1.17**).
* `EP.isSLR_iff_of_isLR_iff`: the proof of Proposition 10.1.19, i.e. (SLR) passes along `F` once
  (LR) passes along the lifts `Fⁱ` (hypothesis satisfiable: `EP.isLR_iff_lift_self`).
  Proposition 10.1.9 itself is proved later, in `EquivalenceLR.lean` (`proposition_10_1_9`), and
  Proposition 10.1.19 without the hypothesis is `EP.proposition_10_1_19` there.

## What the text leaves implicit, and the choices made

* (ZHOU) is the existing `EpGroupoid.IsZhou`, with `Tg` Chapter 7's `tangentMor`; the proof
  uses `Tψ⁻¹ ∘ Tk ∘ Tψ = T(ψ⁻¹ ∘ k ∘ ψ)` (`tangentMor_comp`) and the bijectivity of `TF` on the
  tangent fibres instead of natural representations.  In (b) of the proof the text writes `U(F(y))`
  for `U(F(x))` (possible misprint).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u v

section Zhou

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

/-- `s(φ)` is smooth iff `φ` is. -/
theorem EpGroupoid.mem_smoothSet_src_iff (X : EpGroupoid Obj Mor) (φ : Mor) :
    X.src φ ∈ X.PObj.smoothSet ↔ φ ∈ X.PMor.smoothSet := by
  simp only [MPolyfold.smoothSet, mem_iInter, X.mem_levelSet_src_iff]

/-- `t(φ)` is smooth iff `φ` is. -/
theorem EpGroupoid.mem_smoothSet_tgt_iff (X : EpGroupoid Obj Mor) (φ : Mor) :
    X.tgt φ ∈ X.PObj.smoothSet ↔ φ ∈ X.PMor.smoothSet := by
  simp only [MPolyfold.smoothSet, mem_iInter, X.mem_levelSet_tgt_iff]

namespace EpFunctor

/-- **Naturality of `Tφ`**: `T(F(φ)) ∘ TF = TF ∘ Tφ` on `T_{s(φ)}X`. -/
theorem tangentMor_mor (F : EpFunctor X Y) {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1)
    {a : X.PObj.TangentSpace} (ha : X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src φ) :
    Y.tangentMor (F.mor φ) (F.tangent.obj a) = F.tangent.obj (X.tangentMor φ a) := by
  obtain ⟨h, rfl, rfl⟩ := X.exists_tSrc_eq' hφ ha
  have hTF : Y.tSrc (F.tangent.mor h) = F.tangent.obj (X.tSrc h) := F.tangent.src_mor h
  have hTF' : Y.tTgt (F.tangent.mor h) = F.tangent.obj (X.tTgt h) := F.tangent.tgt_mor h
  have hmor : Y.tBase (F.tangent.mor h) = F.mor (X.tBase h) :=
    Y.tBase_tangentMap F.isScSmoothMap_mor h
  rw [X.tangentMor_tSrc, ← hTF', ← hmor, ← hTF, Y.tangentMor_tSrc]

namespace IsEquivalence

variable {F : EpFunctor X Y} (hF : F.IsEquivalence)
include hF

/-- `X` satisfies (ZHOU) ⇒ `Y` does (one half of Proposition 10.1.17). -/
theorem isZhou_of_isZhou (hX : X.IsZhou) : Y.IsZhou := by
  have hd := hF.isLocalScDiffeo_obj
  intro y k hk
  have hyS : Y.PObj.smoothVal y ∈ Y.PObj.smoothSet := Y.PObj.smoothVal_mem y
  obtain ⟨x, ψ, hs, ht⟩ := hF.exists_iso (Y.PObj.smoothVal y)
  have hψS : ψ ∈ Y.PMor.smoothSet := (Y.mem_smoothSet_tgt_iff ψ).1 (ht ▸ hyS)
  have hψ1 : ψ ∈ Y.PMor.levelSet 1 := mem_iInter.1 hψS 1
  have hxS : x ∈ X.PObj.smoothSet :=
    (hd.mem_smoothSet_iff x).1 (hs ▸ (Y.mem_smoothSet_src_iff ψ).2 hψS)
  have hx1 : x ∈ X.PObj.levelSet 1 := mem_iInter.1 hxS 1
  -- `k' = ψ⁻¹ ∘ k ∘ ψ ∈ G_{F(x)}` and `g ∈ G_x` with `F(g) = k'`
  have hs' : Y.src (Y.inv ψ) = Y.PObj.smoothVal y := by rw [Y.src_inv, ht]
  have ht' : Y.tgt (Y.inv ψ) = F.obj x := by rw [Y.tgt_inv, hs]
  obtain ⟨g, hg⟩ := (hF.bijective_isotropyHom x).2 (Y.isotropyConj (Y.inv ψ) hs' ht' k)
  have hgk : F.mor g.val = Y.comp (Y.comp (Y.inv ψ) k.val) (Y.inv (Y.inv ψ)) :=
    congrArg GroupoidStr.Isotropy.val hg
  rw [EpGroupoid.mem_trivialSubgroup, ← Y.isotropyConj_mem_trivialSet_iff (Y.inv ψ) hs' ht', ← hg,
    F.isotropyHom_mem_trivialSet_iff hd]
  -- `T(k') = id` on `T_{F(x)}Y`
  have hk1 : k.val ∈ Y.PMor.levelSet 1 :=
    (Y.mem_levelSet_src_iff _ 1).1 (by rw [k.src_val]; exact mem_iInter.1 hyS 1)
  have hc : Y.src (Y.inv ψ) = Y.tgt k.val := by rw [Y.src_inv, k.tgt_val, ht]
  have hk' : ∀ b : Y.PObj.TangentSpace, Y.PObj.levelVal 1 (Y.PObj.tangentProj b) = F.obj x →
      Y.tangentMor (F.mor g.val) b = b := by
    intro b hb
    have hbψ : Y.PObj.levelVal 1 (Y.PObj.tangentProj b) = Y.src ψ := hb.trans hs.symm
    have hTψ : Y.PObj.levelVal 1 (Y.PObj.tangentProj (Y.tangentMor ψ b)) =
        Y.PObj.smoothVal y := (Y.levelVal_tangentProj_tangentMor hψ1 hbψ).trans ht
    have hfib : Y.tangentMor ψ b ∈ Y.PObj.tangentFiber (Y.PObj.smoothIncl y 1) :=
      MPolyfold.level_ext hTψ
    rw [hgk, GroupoidStr.inv_inv,
      Y.tangentMor_comp hψ1 (by rw [Y.src_comp _ _ hc, k.src_val, ht]) hbψ,
      Y.tangentMor_comp hk1 hc (by rw [hTψ, k.src_val]), hk _ hfib,
      Y.tangentMor_inv_tangentMor hψ1 hbψ]
  -- `Tg = id` on `T_xX`, by `TF ∘ Tg = T(F g) ∘ TF` and the injectivity of `TF` on `T_xX`
  refine hX (X.PObj.smoothMk x hxS) g fun v hv => ?_
  have hvb : X.PObj.levelVal 1 (X.PObj.tangentProj v) = x := by rw [hv]; rfl
  have hg1 : g.val ∈ X.PMor.levelSet 1 :=
    (X.mem_levelSet_src_iff _ 1).1 (by rw [g.src_val]; exact hx1)
  have hvs : X.PObj.levelVal 1 (X.PObj.tangentProj v) = X.src g.val := hvb.trans g.src_val.symm
  have hTv : X.PObj.levelVal 1 (X.PObj.tangentProj (X.tangentMor g.val v)) = x :=
    (X.levelVal_tangentProj_tangentMor hg1 hvs).trans g.tgt_val
  refine hd.injOn_tangentFiber (X.PObj.tangentProj v) (MPolyfold.level_ext (hTv.trans hvb.symm))
    rfl ?_
  change F.tangent.obj (X.tangentMor g.val v) = F.tangent.obj v
  rw [← F.tangentMor_mor hg1 hvs]
  exact hk' _ ((MPolyfold.levelVal_tangentProj_tangentMap F.isScSmoothMap_obj v).trans
    (by rw [hvb]))

/-- `Y` satisfies (ZHOU) ⇒ `X` does (the other half of Proposition 10.1.17). -/
theorem isZhou_of_isZhou_right (hY : Y.IsZhou) : X.IsZhou := by
  have hd := hF.isLocalScDiffeo_obj
  intro x' g hg
  have hxS : X.PObj.smoothVal x' ∈ X.PObj.smoothSet := X.PObj.smoothVal_mem x'
  have hFxS : F.obj (X.PObj.smoothVal x') ∈ Y.PObj.smoothSet :=
    (hd.mem_smoothSet_iff _).2 hxS
  rw [EpGroupoid.mem_trivialSubgroup, ← F.isotropyHom_mem_trivialSet_iff hd]
  refine hY (Y.PObj.smoothMk _ hFxS) (F.isotropyHom _ g) fun b hb => ?_
  obtain ⟨a, ha, rfl⟩ := hd.tangentFiber_subset_image (X.PObj.smoothIncl x' 1)
    (Y.PObj.smoothIncl (Y.PObj.smoothMk _ hFxS) 1) rfl hb
  have hg1 : g.val ∈ X.PMor.levelSet 1 :=
    (X.mem_levelSet_src_iff _ 1).1 (by rw [g.src_val]; exact mem_iInter.1 hxS 1)
  have hab : X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src g.val := by
    rw [g.src_val, ha]
    rfl
  change Y.tangentMor (F.mor g.val) (F.tangent.obj a) = F.tangent.obj a
  rw [F.tangentMor_mor hg1 hab, hg a ha]

end IsEquivalence

/-- **2021 Proposition 10.1.17, p. 475 (new in the 2021 edition)**: if `F : X → Y` is an
equivalence, `X` satisfies the Zhou condition (Definition 7.4.5) iff `Y` does. -/
theorem proposition_10_1_17 {F : EpFunctor X Y} (hF : F.IsEquivalence) :
    X.IsZhou ↔ Y.IsZhou :=
  ⟨hF.isZhou_of_isZhou, hF.isZhou_of_isZhou_right⟩

end EpFunctor

end Zhou

/-- **The reduction of Proposition 10.1.19 to Proposition 10.1.9** (the proof of 2021
Proposition 10.1.19, p. 477): if (LR) is invariant under the equivalences `Fⁱ : Xⁱ → Yⁱ` of the
lifts (Proposition 10.1.9, proved in `EquivalenceLR.lean`, which also gives
`EP.proposition_10_1_19` without this hypothesis), then (SLR) is invariant under `F`. -/
theorem EP.isSLR_iff_of_isLR_iff {A B : EP.{u}} {F : EpFunctor A.X B.X} (hF : F.IsEquivalence)
    (h109 : ∀ (i : ℕ) (G : EpFunctor (A.lift i).X (B.lift i).X), G.IsEquivalence →
      ((A.lift i).X.IsLR ↔ (B.lift i).X.IsLR)) :
    A.IsSLR ↔ B.IsSLR :=
  ⟨fun h i => by
    obtain ⟨G, hG⟩ := EP.exists_isEquivalence_lift hF i
    exact (h109 i G hG).1 (h i),
  fun h i => by
    obtain ⟨G, hG⟩ := EP.exists_isEquivalence_lift hF i
    exact (h109 i G hG).2 (h i)⟩

/-- The hypothesis of `EP.isSLR_iff_of_isLR_iff` is satisfiable: it holds for `B = A`. -/
theorem EP.isLR_iff_lift_self (A : EP.{u}) :
    ∀ (i : ℕ) (G : EpFunctor (A.lift i).X (A.lift i).X), G.IsEquivalence →
      ((A.lift i).X.IsLR ↔ (A.lift i).X.IsLR) :=
  fun _ _ _ => Iff.rfl

end Polyfold
