import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_36

/-! Round trip for V11_36 (2021 Definition 11.6.4, p. 553; 2017: Definition 11.6: functors
`(Ψ, Φ) : F → F'` between proper coverings and equivalences of proper coverings).

The item lists the definitions `ProperCoveringHom` (1), `id`, `comp`, `IsFiberBijective`,
`IsEquivalence` (2) and the witness `pairToPointCovering` (vocabulary) and seven theorems; `A` is
the conjunction of their types, universes at `0` (`B` lives in `Type`): `ProperCoveringHom.ext`,
`mapsTo_fiber`, `IsEquivalence.id`, `IsEquivalence.comp`, `isFiberBijective_of_isEquivalence`
(the fibre condition of (2) follows from the other two for proper coverings),
`isEquivalence_iff`, and `isEquivalence_pairToPointCovering` (no universes).

`B` says that `ProperCoveringHom F F'` is exactly the set of pairs of sc-smooth functors with
`Φ ∘ F = F' ∘ Ψ`, and that `Γ.IsEquivalence` is the text's (2), with the fibre condition.

* The definitions agree: `B_holds` proves `B` outright, without `A`.  `B` (1) holds by the fields
  `comm_obj`, `comm_mor`, the constructor and `cases`; `B` (2) holds by the definition of
  `IsEquivalence`, for every `F`, `F'` (`isEquivalence_iff_text`, its three fields).
* `A_to_B`: (1) as above, uniqueness from `A`'s `ext`; (2) from `A`'s `isEquivalence_iff` and
  `isFiberBijective_of_isEquivalence`.
* `B_to_A`: `isEquivalence_iff` and the witness from `B` (2).  `ext`, `mapsTo_fiber`,
  `IsEquivalence.id`, `IsEquivalence.comp` are stated for arbitrary functors `F`, `F'`, not only
  proper coverings, so they are not consequences of `B` (whose claims are under
  `F.IsProperCovering`, `F'.IsProperCovering`); they are definitional and re-proved outright.
  `isFiberBijective_of_isEquivalence` is genuine extra content of `A` (the text states the fibre
  condition as part of the definition; the project proves it redundant).  It is not a
  consequence of `B` and is re-proved outright (the project's argument, from the non-item
  lemmas `EpFunctor.IsEquivalence.exists_mor_eq`, `mor_injective`, `exists_iso` and unique
  lifting along `F`, `F'`). -/

namespace RoundTrip.V11_36
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.ProperCoveringHom.ext.{0, 0, 0, 0}) ∧
  (type_of% @Polyfold.ProperCoveringHom.mapsTo_fiber.{0, 0, 0, 0}) ∧
  (type_of% @Polyfold.ProperCoveringHom.IsEquivalence.id.{0, 0}) ∧
  (type_of% @Polyfold.ProperCoveringHom.IsEquivalence.comp.{0, 0, 0, 0, 0, 0}) ∧
  (type_of% @Polyfold.ProperCoveringHom.isFiberBijective_of_isEquivalence.{0, 0, 0, 0}) ∧
  (type_of% @Polyfold.ProperCoveringHom.isEquivalence_iff.{0, 0, 0, 0}) ∧
  (type_of% @Polyfold.CoveringEquivalence.Examples.isEquivalence_pairToPointCovering)

theorem A_holds : A :=
  ⟨@Polyfold.ProperCoveringHom.ext.{0, 0, 0, 0},
    @Polyfold.ProperCoveringHom.mapsTo_fiber.{0, 0, 0, 0},
    @Polyfold.ProperCoveringHom.IsEquivalence.id.{0, 0},
    @Polyfold.ProperCoveringHom.IsEquivalence.comp.{0, 0, 0, 0, 0, 0},
    @Polyfold.ProperCoveringHom.isFiberBijective_of_isEquivalence.{0, 0, 0, 0},
    @Polyfold.ProperCoveringHom.isEquivalence_iff.{0, 0, 0, 0},
    @Polyfold.CoveringEquivalence.Examples.isEquivalence_pairToPointCovering⟩

section Defs

variable {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {ObjY' MorY' : Type} [TopologicalSpace ObjY'] [T2Space ObjY'] [ParacompactSpace ObjY']
  [TopologicalSpace MorY'] [T2Space MorY'] [ParacompactSpace MorY']
  {ObjX' MorX' : Type} [TopologicalSpace ObjX'] [T2Space ObjX'] [ParacompactSpace ObjX']
  [TopologicalSpace MorX'] [T2Space MorX'] [ParacompactSpace MorX']
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}
  {Y' : EpGroupoid ObjY' MorY'} {X' : EpGroupoid ObjX' MorX'}
  {F : EpFunctor Y X} {F' : EpFunctor Y' X'}

/-- The project's Definition 11.6.4 (2) is the text's, for all functors `F`, `F'` (not only
proper coverings): its three fields. -/
theorem isEquivalence_iff_text (Γ : ProperCoveringHom F F') :
    Γ.IsEquivalence ↔ Γ.Ψ.IsEquivalence ∧ Γ.Φ.IsEquivalence ∧
      ∀ x : ObjX, BijOn Γ.Ψ.obj (F.obj ⁻¹' {x}) (F'.obj ⁻¹' {Γ.Φ.obj x}) :=
  ⟨fun h => ⟨h.isEquivalence_Ψ, h.isEquivalence_Φ, h.isFiberBijective⟩,
    fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- The fibre condition follows from `Ψ`, `Φ` equivalences (re-proved outright: the project's
argument). -/
theorem isFiberBijective_of_isEquivalence' (hF : F.IsProperCovering)
    (hF' : F'.IsProperCovering) (Γ : ProperCoveringHom F F') (hΨ : Γ.Ψ.IsEquivalence)
    (hΦ : Γ.Φ.IsEquivalence) (x : ObjX) :
    BijOn Γ.Ψ.obj (F.obj ⁻¹' {x}) (F'.obj ⁻¹' {Γ.Φ.obj x}) := by
  refine ⟨fun y hy => ?_, fun y₁ hy₁ y₂ hy₂ he => ?_, fun y' hy' => ?_⟩
  · change F'.obj (Γ.Ψ.obj y) = Γ.Φ.obj x
    rw [← Γ.comm_obj, show F.obj y = x from hy]
  · have hy₁ : F.obj y₁ = x := hy₁
    have hy₂ : F.obj y₂ = x := hy₂
    obtain ⟨ψ, hψs, hψt, hψ⟩ := hΨ.exists_mor_eq (x := y₁) (x' := y₂)
      (ψ := Y'.unit (Γ.Ψ.obj y₁)) (Y'.src_unit _) ((Y'.tgt_unit _).trans he)
    have hFψ : F.mor ψ = X.unit x := by
      refine hΦ.mor_injective (by rw [F.src_mor, hψs, hy₁, X.src_unit])
        (by rw [F.tgt_mor, hψt, hy₂, X.tgt_unit]) ?_
      rw [Γ.comm_mor, hψ, F'.mor_unit, Γ.Φ.mor_unit, ← Γ.comm_obj, hy₁]
    have h₀ : X.src (X.unit x) = F.obj y₁ := by rw [X.src_unit, hy₁]
    have : ψ = Y.unit y₁ :=
      (hF.existsUnique_lift h₀).unique ⟨hFψ, hψs⟩ ⟨by rw [F.mor_unit, hy₁], Y.src_unit _⟩
    rw [← hψt, this, Y.tgt_unit]
  · have hy' : F'.obj y' = Γ.Φ.obj x := hy'
    obtain ⟨y, χ, hχs, hχt⟩ := hΨ.exists_iso y'
    obtain ⟨φ, hφs, hφt, hφ⟩ := hΦ.exists_mor_eq (x := F.obj y) (x' := x) (ψ := F'.mor χ)
      (by rw [F'.src_mor, hχs, Γ.comm_obj]) (by rw [F'.tgt_mor, hχt, hy'])
    have h₀ : X.src φ = F.obj y := hφs
    obtain ⟨ψ, ⟨hψm, hψs⟩, -⟩ := hF.existsUnique_lift h₀
    refine ⟨Y.tgt ψ, ?_, ?_⟩
    · change F.obj (Y.tgt ψ) = x
      rw [← F.tgt_mor, hψm, hφt]
    · have : Γ.Ψ.mor ψ = χ :=
        (hF'.existsUnique_lift (φ := F'.mor χ) (y := Γ.Ψ.obj y)
          (by rw [F'.src_mor, hχs])).unique
          ⟨by rw [← Γ.comm_mor, hψm, hφ], by rw [Γ.Ψ.src_mor, hψs]⟩ ⟨rfl, hχs⟩
      rw [← Γ.Ψ.tgt_mor, this, hχt]

end Defs

/-- `B` holds outright: the project's definitions are the text's (without `A`). -/
theorem B_holds : B := by
  intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ ObjY' MorY' _ _ _ _ _ _
    ObjX' MorX' _ _ _ _ _ _ Y X Y' X' F F' _ _
  refine ⟨fun Γ => ⟨Γ.comm_obj, Γ.comm_mor⟩, fun Ψ Φ h₁ h₂ => ⟨⟨Ψ, Φ, h₁, h₂⟩, rfl, rfl⟩,
    fun Γ Γ' hΨ hΦ => ?_, isEquivalence_iff_text⟩
  cases Γ; cases Γ'; cases hΨ; cases hΦ; rfl

theorem A_to_B : A → B := by
  rintro ⟨hext, -, -, -, hfib, hiff, -⟩
  intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ ObjY' MorY' _ _ _ _ _ _
    ObjX' MorX' _ _ _ _ _ _ Y X Y' X' F F' hF hF'
  refine ⟨fun Γ => ⟨Γ.comm_obj, Γ.comm_mor⟩, fun Ψ Φ h₁ h₂ => ⟨⟨Ψ, Φ, h₁, h₂⟩, rfl, rfl⟩,
    fun Γ Γ' hΨ hΦ => hext hΨ hΦ, fun Γ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨hΨ, hΦ⟩ := (hiff hF hF' Γ).1 h
    exact ⟨hΨ, hΦ, hfib hF hF' Γ hΨ hΦ⟩
  · exact (hiff hF hF' Γ).2 ⟨h.1, h.2.1⟩

open CoveringEquivalence.Examples EpGroupoid.Examples in
theorem B_to_A : B → A := by
  intro hB
  -- `isEquivalence_iff`, from `B` (2) and the re-proved fibre lemma
  have hiff : type_of% @Polyfold.ProperCoveringHom.isEquivalence_iff.{0, 0, 0, 0} := by
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ ObjY' MorY' _ _ _ _ _ _
      ObjX' MorX' _ _ _ _ _ _ Y X Y' X' F F' hF hF' Γ
    have h2 := (hB ObjY MorY ObjX MorX ObjY' MorY' ObjX' MorX' Y X Y' X' F F' hF hF').2.2.2 Γ
    exact ⟨fun h => ⟨(h2.1 h).1, (h2.1 h).2.1⟩, fun h =>
      h2.2 ⟨h.1, h.2, isFiberBijective_of_isEquivalence' hF hF' Γ h.1 h.2⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hiff, ?_⟩
  · -- `ext` (outright: for arbitrary `F`, `F'`)
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ ObjY' MorY' _ _ _ _ _ _
      ObjX' MorX' _ _ _ _ _ _ Y X Y' X' F F' Γ Γ' hΨ hΦ
    cases Γ; cases Γ'; cases hΨ; cases hΦ; rfl
  · -- `mapsTo_fiber` (outright)
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ ObjY' MorY' _ _ _ _ _ _
      ObjX' MorX' _ _ _ _ _ _ Y X Y' X' F F' Γ x y hy
    change F'.obj (Γ.Ψ.obj y) = Γ.Φ.obj x
    rw [← Γ.comm_obj, show F.obj y = x from hy]
  · -- `IsEquivalence.id` (outright)
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F
    exact ⟨EpFunctor.IsEquivalence.id Y, EpFunctor.IsEquivalence.id X, fun x => bijOn_id _⟩
  · -- `IsEquivalence.comp` (outright)
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ ObjY' MorY' _ _ _ _ _ _
      ObjX' MorX' _ _ _ _ _ _ ObjY'' MorY'' _ _ _ _ _ _ ObjX'' MorX'' _ _ _ _ _ _
      Y X Y' X' Y'' X'' F F' F'' Γ₂ Γ₁ h₂ h₁
    exact ⟨h₂.isEquivalence_Ψ.comp h₁.isEquivalence_Ψ, h₂.isEquivalence_Φ.comp h₁.isEquivalence_Φ,
      fun x => (h₂.isFiberBijective (Γ₁.Φ.obj x)).comp (h₁.isFiberBijective x)⟩
  · -- `isFiberBijective_of_isEquivalence` (outright, the project's argument)
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ ObjY' MorY' _ _ _ _ _ _
      ObjX' MorX' _ _ _ _ _ _ Y X Y' X' F F' hF hF' Γ hΨ hΦ x
    exact isFiberBijective_of_isEquivalence' hF hF' Γ hΨ hΦ x
  · -- the witness, from `isEquivalence_iff` (from `B`)
    exact (hiff EpFunctor.isProperCovering_id EpFunctor.isProperCovering_id
      pairToPointCovering).2 ⟨isEquivalence_pairToPoint, isEquivalence_pairToPoint⟩

#rt_check RoundTrip.V11_36.A_to_B [Polyfold.ProperCoveringHom.ext,
  Polyfold.ProperCoveringHom.mapsTo_fiber, Polyfold.ProperCoveringHom.IsEquivalence.id,
  Polyfold.ProperCoveringHom.IsEquivalence.comp,
  Polyfold.ProperCoveringHom.isFiberBijective_of_isEquivalence,
  Polyfold.ProperCoveringHom.isEquivalence_iff,
  Polyfold.CoveringEquivalence.Examples.isEquivalence_pairToPointCovering]
#rt_check RoundTrip.V11_36.B_to_A [Polyfold.ProperCoveringHom.ext,
  Polyfold.ProperCoveringHom.mapsTo_fiber, Polyfold.ProperCoveringHom.IsEquivalence.id,
  Polyfold.ProperCoveringHom.IsEquivalence.comp,
  Polyfold.ProperCoveringHom.isFiberBijective_of_isEquivalence,
  Polyfold.ProperCoveringHom.isEquivalence_iff,
  Polyfold.CoveringEquivalence.Examples.isEquivalence_pairToPointCovering]
#rt_check RoundTrip.V11_36.B_holds [Polyfold.ProperCoveringHom.ext,
  Polyfold.ProperCoveringHom.mapsTo_fiber, Polyfold.ProperCoveringHom.IsEquivalence.id,
  Polyfold.ProperCoveringHom.IsEquivalence.comp,
  Polyfold.ProperCoveringHom.isFiberBijective_of_isEquivalence,
  Polyfold.ProperCoveringHom.isEquivalence_iff,
  Polyfold.CoveringEquivalence.Examples.isEquivalence_pairToPointCovering]
#rt_check RoundTrip.V11_36.isEquivalence_iff_text [Polyfold.ProperCoveringHom.ext,
  Polyfold.ProperCoveringHom.mapsTo_fiber, Polyfold.ProperCoveringHom.IsEquivalence.id,
  Polyfold.ProperCoveringHom.IsEquivalence.comp,
  Polyfold.ProperCoveringHom.isFiberBijective_of_isEquivalence,
  Polyfold.ProperCoveringHom.isEquivalence_iff,
  Polyfold.CoveringEquivalence.Examples.isEquivalence_pairToPointCovering]
#rt_overlap RoundTrip.V11_36.B_to_A [Polyfold.ProperCoveringHom.ext,
  Polyfold.ProperCoveringHom.mapsTo_fiber, Polyfold.ProperCoveringHom.IsEquivalence.id,
  Polyfold.ProperCoveringHom.IsEquivalence.comp,
  Polyfold.ProperCoveringHom.isFiberBijective_of_isEquivalence,
  Polyfold.ProperCoveringHom.isEquivalence_iff,
  Polyfold.CoveringEquivalence.Examples.isEquivalence_pairToPointCovering]

end RoundTrip.V11_36
