import Polyfold.Chapter8.TangentZhou
import Polyfold.Chapter8.TangentVertical2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 8,
§8.1, **Proposition 8.1.16** (p. 369, new in the 2021 edition), without added hypothesis.

# The Zhou condition passes to the tangent ep-groupoid

## The text, paraphrased

(Proposition 8.1.16) If `X` satisfies (ZHOU), so does `TX`.  The proof writes an isotropy element
of a smooth `b ∈ T_xX` as `(g, h)`, `g ∈ G_x`, and concludes from `T(g, h) = id` that `Tg = id` by
differentiating (8.16) and using that `Tτ_X` is onto; then `g ∈ T_x` by (ZHOU) for `X`, and
`(g, h)` acts trivially near `b`.

## What is formalized

* **`EpGroupoid.tangentZhouReflect`**: the step "`T(g, h) = id` ⇒ `Tg = id`", i.e. Chapter 8's
  `TangentZhouReflect`, holds for **every** ep-groupoid.
* **`EpGroupoid.proposition_8_1_16_2021`**: (ZHOU) for `X` gives (ZHOU) for `TX`, with no
  hypothesis besides the text's.

## The proof, and how it relates to the text's

Let `k = (g, h)` be in the isotropy group of a smooth `b ∈ TX`, with `T k = id` on `T_b(TX)`, and
let `v ∈ T_xX`, `x = p(b)`.  Choose `u ∈ T_g𝐗` with `Ts(u) = v` (fibre surjectivity of `Ts`) and
take the vertical vector `V = vert k u ∈ T_k(T𝐗)` (`TangentVertical2021.lean`).  By naturality of
vertical vectors, `T(Ts)(V) = vert b v` and `T(Tt)(V) = vert b (Tt u)`.  As `Tk` sends
`T(Ts)(V)` to `T(Tt)(V)` (`tangentMor_tSrc`), `Tk = id` gives `vert b (Tt u) = vert b v`, hence
`Tt(u) = v` (`vert_injective`), i.e. `Tg(v) = Tg(Ts u) = Tt(u) = v`.  This is the text's
"differentiate (8.16)" restricted to the vertical directions of `T_b(TX)`, on which `TH(b)` acts
as `Tg`; it needs no surjectivity of `Tτ_X`.
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **The step "`T(g, h) = id` ⇒ `Tg = id`" of the proof of 2021 Proposition 8.1.16** (p. 370)
holds for every ep-groupoid: `TangentZhouReflect` is not an extra hypothesis. -/
theorem tangentZhouReflect : X.TangentZhouReflect := by
  intro y k hk v hv
  have hb1 : X.tangentEpGroupoid.PObj.smoothVal y ∈ X.PObj.tangentPolyfold.levelSet 1 :=
    MPolyfold.levelVal_mem (X.tangentEpGroupoid.PObj.smoothIncl y 1)
  have hk1 : k.val ∈ X.PMor.tangentPolyfold.levelSet 1 :=
    (X.tangentEpGroupoid.mem_levelSet_src_iff k.val 1).1 (by rw [k.src_val]; exact hb1)
  have hv' : X.PObj.tangentProj v = X.PObj.tangentProj (X.tangentEpGroupoid.PObj.smoothVal y) := hv
  -- `u ∈ T_g𝐗` with `Ts(u) = v`
  have hvb : X.PObj.levelVal 1 (X.PObj.tangentProj v) =
      X.src (X.PMor.levelVal 1 (X.PMor.tangentProj k.val)) := by
    rw [hv']
    exact (congrArg (fun a => X.PObj.levelVal 1 (X.PObj.tangentProj a)) k.src_val.symm).trans
      (X.levelVal_tangentProj_tSrc k.val)
  obtain ⟨u, hu, hus⟩ := X.exists_tSrc_eq (φ := X.PMor.tangentProj k.val) hvb
  -- the vertical vector `V = vert k u` and its images under `T(Ts)`, `T(Tt)`
  set V := X.PMor.vert k.val hk1 u hu
  have hS := MPolyfold.tangentMap_tangentMap_vert X.isScSmoothMap_src
    X.tangentEpGroupoid.isScSmoothMap_src k.val hk1 u hu
  have hT := MPolyfold.tangentMap_tangentMap_vert X.isScSmoothMap_tgt
    X.tangentEpGroupoid.isScSmoothMap_tgt k.val hk1 u hu
  have hTu : X.PObj.tangentProj (X.tTgt u) =
      X.PObj.tangentProj (X.tangentEpGroupoid.PObj.smoothVal y) := by
    refine MPolyfold.level_ext ?_
    rw [X.levelVal_tangentProj_tTgt]
    change X.tgt (X.PMor.levelVal 1 (X.PMor.tangentProj u)) = _
    rw [hu]
    exact (X.levelVal_tangentProj_tTgt k.val).symm.trans
      (congrArg (fun a => X.PObj.levelVal 1 (X.PObj.tangentProj a)) k.tgt_val)
  have hS' : X.tangentEpGroupoid.tSrc V =
      X.PObj.vert (X.tangentEpGroupoid.PObj.smoothVal y) hb1 v hv' :=
    hS.trans (MPolyfold.vert_congr k.src_val _ _ hus _ _)
  have hT' : X.tangentEpGroupoid.tTgt V =
      X.PObj.vert (X.tangentEpGroupoid.PObj.smoothVal y) hb1 (X.tTgt u) hTu :=
    hT.trans (MPolyfold.vert_congr k.tgt_val _ _ rfl _ _)
  have hbase : X.tangentEpGroupoid.tBase V = k.val :=
    MPolyfold.levelVal_tangentProj_vert k.val hk1 u hu
  -- `Tk` maps `T(Ts)(V)` to `T(Tt)(V)`, and is the identity
  have hmor := X.tangentEpGroupoid.tangentMor_tSrc V
  rw [hbase, hS', hT'] at hmor
  have hq : X.PObj.vert (X.tangentEpGroupoid.PObj.smoothVal y) hb1 v hv' ∈
      X.tangentEpGroupoid.PObj.tangentFiber (X.tangentEpGroupoid.PObj.smoothIncl y 1) := by
    change X.PObj.tangentPolyfold.tangentProj
      (X.PObj.vert (X.tangentEpGroupoid.PObj.smoothVal y) hb1 v hv') = _
    rw [MPolyfold.tangentProj_vert]
    exact MPolyfold.level_ext rfl
  have heq := (hk _ hq).symm.trans hmor
  have hvu : v = X.tTgt u := MPolyfold.vert_injective heq
  -- `Tg(v) = Tg(Ts u) = Tt(u) = v`
  have hgu : X.tBase k.val = X.tBase u := by
    change X.PMor.levelVal 1 (X.PMor.tangentProj k.val) = X.PMor.levelVal 1 (X.PMor.tangentProj u)
    rw [hu]
  rw [hgu, ← hus, X.tangentMor_tSrc u, ← hvu, hus]

/-- **2021 Proposition 8.1.16**, p. 369 (new in the 2021 edition): if the ep-groupoid `X`
satisfies the Zhou condition (Definition 7.4.5), so does its tangent ep-groupoid `TX`.  No
hypothesis beyond the text's: the step `TangentZhouReflect` of `proposition_8_1_16` is
`tangentZhouReflect`. -/
theorem proposition_8_1_16_2021 (hZ : X.IsZhou) : X.tangentEpGroupoid.IsZhou :=
  X.proposition_8_1_16 hZ X.tangentZhouReflect

end EpGroupoid

end Polyfold
