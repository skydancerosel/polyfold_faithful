import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_28

/-! Round trip for V8_28 (the degeneracy index of `𝐗 ₛ×_F Y`, after Definition 8.5.1 = 2017
Definition 8.8).

The item lists seven theorems; `A` is the conjunction of their types, universes at `0`:
`IsProperCovering.degIndex_fibredMap` (`d_𝐘(φ) = d_{𝐗 ₛ×_F Y}(L φ)`), `degIndex_mor`
(`d_𝐗(F φ) = d_𝐘(φ)`), `degIndex_prod_fibredMap_le` (`d_{𝐗×Y}(F φ, s φ) ≤ 2 d_𝐘(φ)`),
`degIndex_prod_fibredMap` (for **tame** `X`, `Y`: `d_{𝐗×Y}(F φ, s φ) = 2 d_𝐘(φ)` and
`2 d_{𝐗 ₛ×_F Y} = d_{𝐗×Y}`), and Part I's `MPolyfold.degIndex_prod_le`
(`d_{X×Y} ≤ d_X + d_Y`), `MPolyfold.isTame_prod` (tame product, with `d_{X×Y} = d_X + d_Y`) and
`proposition_2_24` (sc-diffeomorphism germs preserve `d`).

`B` asserts, for every proper covering functor, (a) `d_𝐘 = d_{𝐗 ₛ×_F Y} ∘ L`, (b) the product
formula `d_{𝐗×Y}(φ, y) = d_𝐗(φ) + d_Y(y)` for **all** `(φ, y)`, (c) `d_𝐗(F φ) = d_𝐘(φ) = d_Y(s φ)`,
(d) `d_{𝐗×Y}(F φ, s φ) = 2 d_𝐘(φ)`, (e) `2 d_{𝐗 ₛ×_F Y}(L φ) = d_{𝐗×Y}(F φ, s φ)`, with no
tameness hypothesis.

* `B_to_A` (proved): the four proper-covering theorems are read off `B` (the sub-M-polyfold
  structure does not depend on the proof `hA`, the paracompactness instances are Props); the
  three Part I lemmas are general statements about M-polyfolds, not consequences of `B`, and
  are re-proved outright (the project's proofs, copied).
* `A_to_B` (failed): `A` gives the product formula, hence (b), (d), (e), only for tame `X`, `Y`
  (in general only `≤`).  The project's degeneracy index (Definition 2.22: minimum over all
  charts of the structure) satisfies `d_{X×Y} ≤ d_X + d_Y` by product charts, but non-product
  charts of `X × Y` might give smaller values; we have neither a proof of `=` nor a
  counterexample for non-tame M-polyfolds.  With tameness of `X` and `Y` added to `B`
  (`BTame`), `A → BTame` is proved, so tameness is the only difference. -/

namespace RoundTrip.V8_28
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpFunctor.IsProperCovering.degIndex_fibredMap.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.degIndex_mor.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.degIndex_prod_fibredMap_le.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.degIndex_prod_fibredMap.{0, 0}) ∧
  (type_of% @Polyfold.MPolyfold.degIndex_prod_le.{0, 0}) ∧
  (type_of% @Polyfold.MPolyfold.isTame_prod.{0, 0}) ∧
  (type_of% @Polyfold.proposition_2_24.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpFunctor.IsProperCovering.degIndex_fibredMap.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.degIndex_mor.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.degIndex_prod_fibredMap_le.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.degIndex_prod_fibredMap.{0, 0},
    @Polyfold.MPolyfold.degIndex_prod_le.{0, 0},
    @Polyfold.MPolyfold.isTame_prod.{0, 0},
    @Polyfold.proposition_2_24.{0, 0}⟩

/-! ### `B → A` -/

section Reproved

variable {X Y : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : MPolyfold X) (Q : MPolyfold Y)

/-- Part I's `degIndex_prod_le`, re-proved (the project's proof). -/
theorem degIndex_prod_le' [ParacompactSpace (X × Y)] (x : X) (y : Y) :
    (P.prod Q).degIndex (x, y) ≤ P.degIndex x + Q.degIndex y := by
  obtain ⟨φ, hφ, hx, hdx⟩ := P.exists_isChart_degIndex_eq x
  obtain ⟨ψ, hψ, hy, hdy⟩ := Q.exists_isChart_degIndex_eq y
  rw [hdx, hdy, ← MPolyfold.chartDegIndex_prod φ ψ hx hy]
  exact (P.prod Q).degIndex_le (hφ.prod hψ) ⟨hx, hy⟩

/-- Part I's `isTame_prod`, re-proved (the project's proof). -/
theorem isTame_prod' [ParacompactSpace (X × Y)] (hP : P.IsTame) (hQ : Q.IsTame) :
    (P.prod Q).IsTame ∧ ∀ x y, (P.prod Q).degIndex (x, y) = P.degIndex x + Q.degIndex y := by
  have key : ∀ (x : X) (y : Y), ∃ χ : MChart (X × Y), (P.prod Q).IsChart χ ∧ (x, y) ∈ χ.source ∧
      IsTameRetract χ.model.E χ.model.C χ.model.O ∧
      (P.prod Q).degIndex (x, y) = P.degIndex x + Q.degIndex y := by
    intro x y
    obtain ⟨φ, hφ, hx, R, hRO, hRt⟩ := MPolyfold.IsTame.exists_chart P hP x
    obtain ⟨ψ, hψ, hy, R', hR'O, hR't⟩ := MPolyfold.IsTame.exists_chart Q hQ y
    obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
    obtain ⟨n', W', T', hT'⟩ := ψ.model.isPartialQuadrant
    have hR := hRt n W T hT
    have hR' := hR't n' W' T' hT'
    have hTT' := prod_eq_prodPresentation T T' hT hT'
    have htame := ScRetraction.IsTameWith.prod hT hT' hR hR'
    have hret : (R.prod R').retract = (φ.prod ψ).model.O := by
      rw [R.prod_retract, hRO, hR'O]; rfl
    refine ⟨φ.prod ψ, hφ.prod hψ, ⟨hx, hy⟩, ⟨R.prod R', hret, htame.isTame hTT'⟩, ?_⟩
    rw [(P.prod Q).degIndex_eq_chartDegIndex_of_isTameWith (hφ.prod hψ) (R.prod R') hret hTT'
      htame ⟨hx, hy⟩, MPolyfold.chartDegIndex_prod φ ψ hx hy,
      P.degIndex_eq_chartDegIndex_of_isTameWith hφ R hRO hT hR hx,
      Q.degIndex_eq_chartDegIndex_of_isTameWith hψ R' hR'O hT' hR' hy]
  refine ⟨MPolyfold.isTame_of_forall_exists_chart _ fun p => ?_,
    fun x y => (key x y).choose_spec.2.2.2⟩
  obtain ⟨χ, h1, h2, h3, -⟩ := key p.1 p.2
  exact ⟨χ, h1, h2, h3⟩

variable {P Q} in
/-- Proposition 2.24, re-proved (the project's proof). -/
theorem proposition_2_24' {f : X → Y} {g : Y → X} {U : Set X} {V : Set Y}
    (h : P.IsScDiffeoOn Q f g U V) {x : X} (hx : x ∈ U) : P.degIndex x = Q.degIndex (f x) := by
  refine le_antisymm (MPolyfold.degIndex_le_of_isScDiffeoOn h hx) ?_
  have := MPolyfold.degIndex_le_of_isScDiffeoOn h.symm (h.mapsTo hx)
  rwa [h.left_inv x hx] at this

end Reproved

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, @degIndex_prod_le', @isTame_prod',
    fun h => proposition_2_24' h⟩
  · intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF φ
    obtain ⟨_, hA, _, ha, -⟩ := hB ObjY MorY ObjX MorX Y X F hF
    exact ha φ
  · intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF φ
    obtain ⟨_, hA, _, -, -, hc, -⟩ := hB ObjY MorY ObjX MorX Y X F hF
    exact (hc φ).1
  · intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF φ
    obtain ⟨_, hA, _, -, -, -, hd, -⟩ := hB ObjY MorY ObjX MorX Y X F hF
    exact (hd φ).le
  · intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF _ _ φ
    obtain ⟨_, hA, _, -, -, -, hd, he⟩ := hB ObjY MorY ObjX MorX Y X F hF
    exact ⟨hd φ, he φ⟩

/-! ### `A → B` fails without tameness; `A → BTame` -/

/-- `B` with the hypotheses that `X` and `Y` are tame (`EpGroupoid.IsTame`: tame object
M-polyfolds; the morphism M-polyfolds are then tame, `s` being a local sc-diffeomorphism). -/
def BTame : Prop :=
  ∀ (ObjY MorY : Type) [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    (ObjX MorX : Type) [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    (Y : EpGroupoid ObjY MorY) (X : EpGroupoid ObjX MorX) (F : EpFunctor Y X),
    F.IsProperCovering → X.IsTame → Y.IsTame →
    ∃ (_ : ParacompactSpace (MorX × ObjY))
      (hA : (X.PMor.prod Y.PObj).IsSubMPolyfold (MPolyfold.fibredProduct X.src F.obj))
      (_ : ParacompactSpace (MPolyfold.fibredProduct X.src F.obj)),
      (∀ φ : MorY, Y.PMor.degIndex φ = ((X.PMor.prod Y.PObj).subPolyfold hA).degIndex (LB F φ)) ∧
      (∀ p : MorX × ObjY,
        (X.PMor.prod Y.PObj).degIndex p = X.PMor.degIndex p.1 + Y.PObj.degIndex p.2) ∧
      (∀ φ : MorY, X.PMor.degIndex (F.mor φ) = Y.PMor.degIndex φ ∧
        Y.PObj.degIndex (Y.src φ) = Y.PMor.degIndex φ) ∧
      (∀ φ : MorY, (X.PMor.prod Y.PObj).degIndex (F.mor φ, Y.src φ) = 2 * Y.PMor.degIndex φ) ∧
      (∀ φ : MorY, 2 * ((X.PMor.prod Y.PObj).subPolyfold hA).degIndex (LB F φ) =
        (X.PMor.prod Y.PObj).degIndex (F.mor φ, Y.src φ))

theorem A_to_BTame : A → BTame := by
  rintro ⟨ha, hc, -, hde, -, htame, h224⟩
  intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF hX hY
  let _ := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
  let _ := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
  refine ⟨_, MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src F.isScSmoothMap_obj, _,
    fun φ => ha hF φ, fun p => (htame X.PMor Y.PObj (X.isLocalScDiffeo_src.isTame hX) hY).2 p.1 p.2,
    fun φ => ⟨hc hF φ, ?_⟩, fun φ => (hde hF hX hY φ).1, fun φ => (hde hF hX hY φ).2⟩
  obtain ⟨W, V, σ, hφ, hd⟩ := Y.isLocalScDiffeo_src φ
  exact (h224 hd hφ).symm

/-- With tameness the hypothesis is the only difference: `BTame` follows from `B`. -/
theorem B_to_BTame : B → BTame := fun hB ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF _ _ =>
  hB ObjY MorY ObjX MorX Y X F hF

#rt_check RoundTrip.V8_28.B_to_A [Polyfold.EpFunctor.IsProperCovering.degIndex_fibredMap,
  Polyfold.EpFunctor.IsProperCovering.degIndex_mor,
  Polyfold.EpFunctor.IsProperCovering.degIndex_prod_fibredMap_le,
  Polyfold.EpFunctor.IsProperCovering.degIndex_prod_fibredMap, Polyfold.MPolyfold.degIndex_prod_le,
  Polyfold.MPolyfold.isTame_prod, Polyfold.proposition_2_24]
#rt_check RoundTrip.V8_28.A_to_BTame [Polyfold.EpFunctor.IsProperCovering.degIndex_fibredMap,
  Polyfold.EpFunctor.IsProperCovering.degIndex_mor,
  Polyfold.EpFunctor.IsProperCovering.degIndex_prod_fibredMap_le,
  Polyfold.EpFunctor.IsProperCovering.degIndex_prod_fibredMap, Polyfold.MPolyfold.degIndex_prod_le,
  Polyfold.MPolyfold.isTame_prod, Polyfold.proposition_2_24]
#rt_overlap RoundTrip.V8_28.B_to_A [Polyfold.EpFunctor.IsProperCovering.degIndex_fibredMap,
  Polyfold.EpFunctor.IsProperCovering.degIndex_mor,
  Polyfold.EpFunctor.IsProperCovering.degIndex_prod_fibredMap_le,
  Polyfold.EpFunctor.IsProperCovering.degIndex_prod_fibredMap, Polyfold.MPolyfold.degIndex_prod_le,
  Polyfold.MPolyfold.isTame_prod, Polyfold.proposition_2_24]

end RoundTrip.V8_28
