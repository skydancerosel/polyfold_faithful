import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_51

/-!
Round trip for V8_51 (2021 Lemma 8.5.10, `W ≅ F*V` for a proper strong bundle covering
functor, p. 395).

The item lists the definitions `pullbackμ`, `bundleB`, `bundleBInv` (vocabulary) and nine
theorems: `bundleB_val` (`B(w) = (P w, A w)`), `bundleB_μ` ((8.23)), `eq_of_isStrongBundleIsoOn`
(`F` injective on a local isomorphism domain), `bijective_bundleB`, `bundleBInv_eq_of` (local
formula for `B⁻¹`), `isStrongBundleMap_bundleB`, `mapsTo_oneSet_bundleBInv`,
`isStrongBundleMap_bundleBInv` and `lemma_8_5_10` (`B` is a strong bundle isomorphism over
`id_Y` with inverse `B⁻¹`, `pr₁ ∘ B = P`, and (8.23)).  `A` is the conjunction of their types,
universes at `0`.

`B` asserts (a) `w ↦ (P w, A w)` is a strong bundle isomorphism `W → F*V` over `id_Y` (some
inverse), (b) (8.23), (c) `A = Ā ∘ B`, (d) `F*V` carries an `EpStrongBundle` structure over `Y`
with structure map `μ_{F*V}`.

* `A ⇒ B`: (a), (b) from `lemma_8_5_10`, (c) by `rfl`; (d) is **not** in `A` (the project's
  file says the `EpStrongBundle` structure of `F*V` is not proved there), but the project has it
  in Chapter 10: `EpStrongBundle.pullbackAlong EV F` (the pull-back `F*V` along the sc-smooth
  functor `F`, structure map `(t(m), μ(F(m), v))`, definitionally `μ_{F*V}`), which does not use
  the item's theorems.
* `B ⇒ A`: `bundleB_μ`, `bijective_bundleB`, `isStrongBundleMap_bundleB`, the two `bundleBInv`
  conjuncts and `lemma_8_5_10` come from (a), (b) (the inverse `Binv` from (a) equals
  `bundleBInv`, both being inverses of the bijection `B`); `bundleB_val` is `rfl` and
  `eq_of_isStrongBundleIsoOn` (injectivity of the base sc-diffeomorphism) is re-proved (B does
  not contain it); `bundleBInv_eq_of` combines it with the bijectivity from (a).

**Harness note.** `bundleBInv` is `surjInv` of the surjectivity half of `bijective_bundleB` (an
item theorem), so every term mentioning `bundleBInv` reaches it through the abstracted proof
field `bundleBInv._proof_1`; the directions are checked with `#rt_check_soft`.  Our proofs never
use that field: they get the inverse properties from `Function.surjInv_eq` with surjectivity
obtained from B's (a).
-/

namespace RoundTrip.V8_51
open Polyfold Function

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.bundleB_val.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.bundleB_μ.{0}) ∧
  (type_of%
    @Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.eq_of_isStrongBundleIsoOn.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.bijective_bundleB.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.bundleBInv_eq_of.{0}) ∧
  (type_of%
    @Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.isStrongBundleMap_bundleB.{0}) ∧
  (type_of%
    @Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.mapsTo_oneSet_bundleBInv.{0}) ∧
  (type_of%
    @Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.isStrongBundleMap_bundleBInv.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.lemma_8_5_10.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.bundleB_val.{0},
    @Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.bundleB_μ.{0},
    @Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.eq_of_isStrongBundleIsoOn.{0},
    @Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.bijective_bundleB.{0},
    @Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.bundleBInv_eq_of.{0},
    @Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.isStrongBundleMap_bundleB.{0},
    @Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.mapsTo_oneSet_bundleBInv.{0},
    @Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.isStrongBundleMap_bundleBInv.{0},
    @Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.lemma_8_5_10.{0}⟩

theorem A_to_B : A → B := by
  intro hA ObjY MorY _ _ _ _ _ _ Y ObjX MorX _ _ _ _ _ _ X W _ _ _ P _ _ BW _ V _ _ _ Q _ _ BV
    EW EV F Am _ h hQA Bm
  have hL := hA.2.2.2.2.2.2.2.2 h
  have hBm : Bm = h.bundleB := rfl
  refine ⟨⟨h.bundleBInv, hBm ▸ hL.1⟩, fun φ w hw _ => ?_, fun _ => rfl, ?_⟩
  · rw [hBm, hL.2.2 φ w hw]
    rfl
  · -- (d): not in `A`; the project's pull-back of `EV` along `F` (Chapter 10)
    have := BV.paracompactSpace_pullback X.PMor X.src
    have := (BV.pullback F.isScSmoothMap_obj).paracompactSpace_pullback Y.PMor Y.src
    exact ⟨EV.pullbackAlong F, fun _ _ _ _ => rfl⟩

section
variable {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY] {Y : EpGroupoid ObjY MorY}
  {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX] {X : EpGroupoid ObjX MorX}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → ObjY}
  [∀ y, AddCommGroup (P ⁻¹' {y})] [∀ y, Module ℝ (P ⁻¹' {y})] {BW : StrongBundle Y.PObj P}
  [ParacompactSpace (pullbackSpace P Y.src)]
  {V : Type} [TopologicalSpace V] [T2Space V] [ParacompactSpace V] {Q : V → ObjX}
  [∀ x, AddCommGroup (Q ⁻¹' {x})] [∀ x, Module ℝ (Q ⁻¹' {x})] {BV : StrongBundle X.PObj Q}
  {EW : EpStrongBundle Y BW} {EV : EpStrongBundle X BV} {F : EpFunctor Y X} {Am : W → V}

/-- (a) of `B`, for `bundleB`. -/
theorem isoB (hB : B) (h : EW.IsProperStrongBundleCovering2021 EV F Am)
    [ParacompactSpace (pullbackSpace Q F.obj)] :
    ∃ Binv : pullbackSpace Q F.obj → W,
      BW.IsStrongBundleIso (BV.pullback F.isScSmoothMap_obj) id h.bundleB id Binv :=
  (hB ObjY MorY Y ObjX MorX X W P BW V Q BV EW EV F Am h h.isMap.isStrongBundleMap.covers).1

/-- (b) of `B`, for `bundleB`. -/
theorem muB (hB : B) (h : EW.IsProperStrongBundleCovering2021 EV F Am)
    [ParacompactSpace (pullbackSpace Q F.obj)] (φ : MorY) (w : W) (hw : P w = Y.src φ)
    (hv : Q (Am w) = X.src (F.mor φ)) :
    (h.bundleB (EW.μ ⟨(φ, w), hw⟩) : ObjY × V) = (Y.tgt φ, EV.μ ⟨(F.mor φ, Am w), hv⟩) :=
  (hB ObjY MorY Y ObjX MorX X W P BW V Q BV EW EV F Am h h.isMap.isStrongBundleMap.covers).2.1
    φ w hw hv

theorem bijB (hB : B) (h : EW.IsProperStrongBundleCovering2021 EV F Am) :
    Bijective h.bundleB := by
  have := BV.paracompactSpace_pullback Y.PObj F.obj
  obtain ⟨Binv, hiso⟩ := isoB hB h
  exact ⟨LeftInverse.injective hiso.left_inv, RightInverse.surjective hiso.right_inv⟩

/-- `B(B⁻¹ q) = q`, from the surjectivity given by `B`. -/
theorem bundleB_bundleBInv' (hB : B) (h : EW.IsProperStrongBundleCovering2021 EV F Am)
    (q : pullbackSpace Q F.obj) : h.bundleB (h.bundleBInv q) = q :=
  surjInv_eq (bijB hB h).2 q

/-- The inverse given by `B` is `bundleBInv`. -/
theorem bundleBInv_eq (hB : B) (h : EW.IsProperStrongBundleCovering2021 EV F Am)
    {Binv : pullbackSpace Q F.obj → W} (hr : ∀ q, h.bundleB (Binv q) = q) :
    h.bundleBInv = Binv :=
  funext fun q => (bijB hB h).1 ((bundleB_bundleBInv' hB h q).trans (hr q).symm)

/-- `eq_of_isStrongBundleIsoOn`, re-proved (not part of `B`). -/
theorem eqOf (h : EW.IsProperStrongBundleCovering2021 EV F Am) {U : Set ObjY} {U' : Set ObjX}
    (hi : BW.IsStrongBundleIsoOn BV h.isMap.isStrongBundleMap U U') {w : W} {y : ObjY}
    (hw : P w ∈ U) (hy : y ∈ U) (hQ : Q (Am w) = F.obj y) : P w = y := by
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  exact hg.injOn hw hy ((h.isMap.isStrongBundleMap.covers w).symm.trans hQ)

theorem invEqOf (hB : B) (h : EW.IsProperStrongBundleCovering2021 EV F Am) {U : Set ObjY}
    {U' : Set ObjX} (hi : BW.IsStrongBundleIsoOn BV h.isMap.isStrongBundleMap U U')
    {q : pullbackSpace Q F.obj} (hq : (q : ObjY × V).1 ∈ U) {w : W} (hw : P w ∈ U)
    (hA : Am w = (q : ObjY × V).2) : h.bundleBInv q = w := by
  have hP : P w = (q : ObjY × V).1 := eqOf h hi hw hq (by rw [hA]; exact q.2)
  refine (bijB hB h).1 ((bundleB_bundleBInv' hB h q).trans ?_)
  exact Subtype.ext (Prod.ext hP.symm hA.symm)

theorem invMapB (hB : B) (h : EW.IsProperStrongBundleCovering2021 EV F Am)
    [ParacompactSpace (pullbackSpace Q F.obj)] :
    (BV.pullback F.isScSmoothMap_obj).IsStrongBundleMap BW id h.bundleBInv := by
  obtain ⟨Binv, hiso⟩ := isoB hB h
  rw [bundleBInv_eq hB h hiso.right_inv]
  exact hiso.invMap

end

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun h w => rfl, fun h φ w hw => ?_, fun h _ _ hi _ _ hw hy hQ => eqOf h hi hw hy hQ,
    fun h => bijB hB h, fun h _ _ hi _ hq _ hw hA => invEqOf hB h hi hq hw hA,
    fun h _ => (isoB hB h).choose_spec.toMap, fun h _ => (invMapB hB h).mapsTo_oneSet,
    fun h _ => invMapB hB h, fun h _ => ?_⟩
  · rename_i ObjY MorY _ _ _ _ _ _ Y ObjX MorX _ _ _ _ _ _ X W _ _ _ P _ _ BW _ V _ _ _ Q _ _ BV
      EW EV F Am
    have := BV.paracompactSpace_pullback Y.PObj F.obj
    exact Subtype.ext (muB hB h φ w hw _)
  · refine ⟨⟨(isoB hB h).choose_spec.toMap, invMapB hB h, fun w => ?_,
      bundleB_bundleBInv' hB h⟩, fun _ => rfl, fun φ w hw => Subtype.ext (muB hB h φ w hw _)⟩
    exact (bijB hB h).1 (bundleB_bundleBInv' hB h _)

#rt_check_soft RoundTrip.V8_51.A_to_B
  [Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.bundleB_val,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.bundleB_μ,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.eq_of_isStrongBundleIsoOn,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.bijective_bundleB,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.bundleBInv_eq_of,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.isStrongBundleMap_bundleB,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.mapsTo_oneSet_bundleBInv,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.isStrongBundleMap_bundleBInv,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.lemma_8_5_10]
#rt_check_soft RoundTrip.V8_51.B_to_A
  [Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.bundleB_val,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.bundleB_μ,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.eq_of_isStrongBundleIsoOn,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.bijective_bundleB,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.bundleBInv_eq_of,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.isStrongBundleMap_bundleB,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.mapsTo_oneSet_bundleBInv,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.isStrongBundleMap_bundleBInv,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.lemma_8_5_10]
#rt_overlap RoundTrip.V8_51.B_to_A
  [Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.bundleB_val,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.bundleB_μ,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.eq_of_isStrongBundleIsoOn,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.bijective_bundleB,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.bundleBInv_eq_of,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.isStrongBundleMap_bundleB,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.mapsTo_oneSet_bundleBInv,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.isStrongBundleMap_bundleBInv,
  Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021.lemma_8_5_10]

end RoundTrip.V8_51
