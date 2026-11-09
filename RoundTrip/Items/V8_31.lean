import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_31

/-! Round trip for V8_31 (Remark 8.2 of the 2017 text, 2021: Remark 8.5.4: `F` maps morphisms
over `F⁻¹(x)` into `G_x`; everything in Theorem 8.5 is determined by `U(x)`).

`A` is the conjunction of the types of the four listed theorems, universes at `0`:
`EpFunctor.remark_8_5_4_a` (`F(φ) ∈ mor(x, x)`, any functor), `EpFunctor.remark_8_5_4_b` (two charts
`C, C' : F.ProperCoveringChart x` with the same `U(x)` have the same `Φ`, `Γ` on `U(x)`, the same
`U(y)` and the same `𝐔(ψ₀)`; any functor `F`), `ProperCoveringChart.connectedComponentIn_U`,
`ProperCoveringChart.connectedComponentIn_sheet` (in a chart, `U(y)` and `𝐔(ψ₀)` are connected
components).  `EpFunctor.isotropyMor` is a definition.

* `A → B`: (a) is `remark_8_5_4_a`.  `A`'s other three theorems are about charts
  `F.ProperCoveringChart x` (all of (0)–(5)), and `B`'s `U(x)` need not be small enough to carry
  one, so they do not apply to (b).  (b)(i) (uniqueness of `(Φ, Γ)` on a connected `U(x)`) is
  proved outright from Chapter 7 (`NaturalRep.Φ_eqOn`, `Γ_eqOn`, after `toRep`).  [It would also
  follow from `remark_8_5_4_b` applied to two charts of the identity functor built by
  `Data.toChart` (for `𝟭` the input exists for every `U(x)`), but `Data.toChart`'s field
  `pairwiseDisjoint_sheet := Data.pairwiseDisjoint_sheet` reaches `remark_8_5_4_a` through
  `Data.val_g` as a plain constant, which `#rt_check_soft` counts as hard.]  (b)(ii) (uniqueness
  of the `U(y)`, `𝐔(ψ₀)` satisfying (0) and (2)) is proved outright from (0), (2) by
  `ProperCoveringLocal.connectedComponentIn_eq_of_iUnion` (a non-item lemma), the same argument
  as `connectedComponentIn_U`, `connectedComponentIn_sheet`.
* `B → A`: `A` is stated for an arbitrary functor `F` (no proper covering hypothesis), `B` for
  proper coverings.  The `Φ`, `Γ` part of `remark_8_5_4_b` comes from `B` (b)(i) applied to the
  identity functor of `X` (`EpFunctor.isProperCovering_id`); `remark_8_5_4_a`, the `U(y)`, `𝐔(ψ₀)`
  part of `remark_8_5_4_b` and the two component lemmas are re-proved outright from the chart
  fields (`B` (b)(ii) needs a proper covering). -/

namespace RoundTrip.V8_31
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpFunctor.remark_8_5_4_a.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.remark_8_5_4_b.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.ProperCoveringChart.connectedComponentIn_U.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.ProperCoveringChart.connectedComponentIn_sheet.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpFunctor.remark_8_5_4_a.{0, 0}, @Polyfold.EpFunctor.remark_8_5_4_b.{0, 0},
    @Polyfold.EpFunctor.ProperCoveringChart.connectedComponentIn_U.{0, 0},
    @Polyfold.EpFunctor.ProperCoveringChart.connectedComponentIn_sheet.{0, 0}⟩

/-! ### Glue: natural actions and natural representations; charts of the identity -/

section Glue
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor} {x : Obj}
  {U : Set Obj} {Φ : X.Isotropy x → Obj → Obj} {Γ : X.Isotropy x → Obj → Mor}

theorem Φ_one_of (h : IsNatAction X x U Φ Γ) : ∀ y ∈ U, Φ 1 y = y := fun y hy => by
  obtain ⟨ψ, hψ⟩ := h.diffeo 1
  have h1 : Φ 1 y = Φ 1 (Φ 1 y) := by rw [← h.hom 1 1 y hy, mul_one]
  calc Φ 1 y = ψ (Φ 1 (Φ 1 y)) := (hψ.left_inv _ (hψ.mapsTo hy)).symm
    _ = ψ (Φ 1 y) := by rw [← h1]
    _ = y := hψ.left_inv y hy

/-- A natural action on a connected `U` is a natural representation (inverse `Φ(g⁻¹)`). -/
def toRep (h : IsNatAction X x U Φ Γ) (hc : IsConnected U) : X.NaturalRep x where
  U := U
  isOpen_U := h.isOpen
  isConnected_U := hc
  mem_U := h.mem
  Φ := Φ
  Γ := Γ
  isScDiffeoOn_Φ g := by
    obtain ⟨ψ, hψ⟩ := h.diffeo g
    obtain ⟨ψ', hψ'⟩ := h.diffeo g⁻¹
    exact ⟨hψ.isScSmoothOn, hψ'.isScSmoothOn, hψ.mapsTo, hψ'.mapsTo,
      fun y hy => by rw [← h.hom _ _ y hy, inv_mul_cancel, Φ_one_of h y hy],
      fun y hy => by rw [← h.hom _ _ y hy, mul_inv_cancel, Φ_one_of h y hy]⟩
  Φ_mul := h.hom
  isScSmoothOn_Γ := h.smooth
  Γ_self := h.Γ_x
  src_Γ g y hy := (h.src_tgt g y hy).1
  tgt_Γ g y hy := (h.src_tgt g y hy).2
  existsUnique_Γ := h.unique

/-- The natural action underlying a natural representation. -/
theorem isNatAction_of_rep (R : X.NaturalRep x) : IsNatAction X x R.U R.Φ R.Γ where
  isOpen := R.isOpen_U
  mem := R.mem_U
  diffeo g := ⟨_, R.isScDiffeoOn_Φ g⟩
  hom := R.Φ_mul
  smooth := R.isScSmoothOn_Γ
  Γ_x := R.Γ_self
  src_tgt g y hy := ⟨R.src_Γ g y hy, R.tgt_Γ g y hy⟩
  unique := R.existsUnique_Γ

end Glue

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  intro hA ObjY MorY ObjX MorX _ _ _ _ _ _ _ _ _ _ _ _ Y X F _ x
  refine ⟨fun φ h1 h2 => hA.1 F (φ := φ) ⟨h1, h2⟩, ?_, ?_⟩
  · -- outright (Chapter 7): `Γ(g, ·)` is the continuous section of `s` through `g`
    intro U Φ Φ' Γ Γ' h h' hc g y hy
    have hcc : connectedComponentIn ((toRep h hc).U ∩ (toRep h' hc).U) x = U := by
      change connectedComponentIn (U ∩ U) x = U
      rw [inter_self]
      exact hc.isPreconnected.connectedComponentIn h.mem
    have hy' : y ∈ connectedComponentIn ((toRep h hc).U ∩ (toRep h' hc).U) x := by
      rw [hcc]; exact hy
    exact ⟨(toRep h hc).Φ_eqOn (toRep h' hc) g hy', (toRep h hc).Γ_eqOn (toRep h' hc) g hy'⟩
  · intro U Φ Γ _ _ Uy Uy' UY UY' h0 h2 h0' h2'
    have keyU : ∀ Uy : ObjY → Set ObjY, Cond0 F x U Uy →
        ∀ y ∈ F.obj ⁻¹' {x}, connectedComponentIn (F.obj ⁻¹' U) y = Uy y := by
      intro Uy h0 y hy
      rw [h0.2.2]
      exact EpFunctor.ProperCoveringLocal.connectedComponentIn_eq_of_iUnion
        (fun y hy => (h0.1 y hy).1) (fun y hy => (h0.1 y hy).2.1) h0.2.1 hy (h0.1 y hy).2.2.1
    have hU : ∀ y ∈ F.obj ⁻¹' {x}, Uy y = Uy' y := fun y hy => by
      rw [← keyU Uy h0 y hy, ← keyU Uy' h0' y hy]
    refine ⟨hU, fun ψ₀ hψ₀ => ?_⟩
    have keyS : ∀ (Uy : ObjY → Set ObjY) (UY : MorY → Set MorY), Cond2 F x Uy UY →
        connectedComponentIn {ψ : MorY | Y.src ψ ∈ Uy (Y.src ψ₀) ∧ Y.tgt ψ ∈ Uy (Y.tgt ψ₀)} ψ₀ =
          UY ψ₀ := by
      intro Uy UY h2
      obtain ⟨heq, hdisj, hprop⟩ := h2 _ hψ₀.1 _ hψ₀.2
      rw [heq]
      exact EpFunctor.ProperCoveringLocal.connectedComponentIn_eq_of_iUnion
        (fun ψ hψ => (hprop ψ hψ).1) (fun ψ hψ => (hprop ψ hψ).2.1) hdisj ⟨rfl, rfl⟩
        (hprop ψ₀ ⟨rfl, rfl⟩).2.2
    rw [← keyS Uy UY h2, ← keyS Uy' UY' h2', hU _ hψ₀.1, hU _ hψ₀.2]

/-! ### `B → A` -/

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F x φ hφ
    exact ⟨(F.src_mor φ).trans hφ.1, (F.tgt_mor φ).trans hφ.2⟩
  · intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F x C C' h
    -- `Φ`, `Γ`: from `B` (b)(i) for the identity functor of `X`
    have hi := (hB ObjX MorX ObjX MorX X X (EpFunctor.id X) EpFunctor.isProperCovering_id x).2.1
      C.R.U C.R.Φ C'.R.Φ C.R.Γ C'.R.Γ (isNatAction_of_rep C.R)
      (h ▸ isNatAction_of_rep C'.R) C.R.isConnected_U
    -- `U(y)`, `𝐔(ψ₀)`: outright, they are connected components
    have cU : ∀ C : F.ProperCoveringChart x, ∀ y ∈ F.obj ⁻¹' {x},
        connectedComponentIn (F.obj ⁻¹' C.R.U) y = C.U y := fun C y hy => by
      rw [C.preimage_eq]
      exact EpFunctor.ProperCoveringLocal.connectedComponentIn_eq_of_iUnion C.isOpen_U
        C.isConnected_U C.pairwiseDisjoint_U hy (C.mem_U y hy)
    have hU : ∀ y ∈ F.obj ⁻¹' {x}, C.U y = C'.U y := fun y hy => by
      rw [← cU C y hy, ← cU C' y hy, h]
    have cS : ∀ C : F.ProperCoveringChart x, ∀ ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x}),
        connectedComponentIn {ψ | Y.src ψ ∈ C.U (Y.src ψ₀) ∧ Y.tgt ψ ∈ C.U (Y.tgt ψ₀)} ψ₀ =
          C.sheet ψ₀ := fun C ψ₀ hψ₀ => by
      have hsub : Y.mor (Y.src ψ₀) (Y.tgt ψ₀) ⊆ Y.morOn (F.obj ⁻¹' {x}) := fun ψ hψ =>
        ⟨by rw [hψ.1]; exact hψ₀.1, by rw [hψ.2]; exact hψ₀.2⟩
      rw [C.morOn_U_eq _ hψ₀.1 _ hψ₀.2]
      exact EpFunctor.ProperCoveringLocal.connectedComponentIn_eq_of_iUnion
        (fun ψ hψ => C.isOpen_sheet ψ (hsub hψ)) (fun ψ hψ => C.isConnected_sheet ψ (hsub hψ))
        (C.pairwiseDisjoint_sheet.subset hsub) ⟨rfl, rfl⟩ (C.mem_sheet ψ₀ hψ₀)
    refine ⟨fun g y hy => (hi g y hy).1, fun g y hy => (hi g y hy).2, hU, fun ψ₀ hψ₀ => ?_⟩
    rw [← cS C ψ₀ hψ₀, ← cS C' ψ₀ hψ₀, hU _ hψ₀.1, hU _ hψ₀.2]
  · intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F x C y hy
    rw [C.preimage_eq]
    exact EpFunctor.ProperCoveringLocal.connectedComponentIn_eq_of_iUnion C.isOpen_U
      C.isConnected_U C.pairwiseDisjoint_U hy (C.mem_U y hy)
  · intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F x C ψ₀ hψ₀
    have hsub : Y.mor (Y.src ψ₀) (Y.tgt ψ₀) ⊆ Y.morOn (F.obj ⁻¹' {x}) := fun ψ hψ =>
      ⟨by rw [hψ.1]; exact hψ₀.1, by rw [hψ.2]; exact hψ₀.2⟩
    rw [C.morOn_U_eq _ hψ₀.1 _ hψ₀.2]
    exact EpFunctor.ProperCoveringLocal.connectedComponentIn_eq_of_iUnion
      (fun ψ hψ => C.isOpen_sheet ψ (hsub hψ)) (fun ψ hψ => C.isConnected_sheet ψ (hsub hψ))
      (C.pairwiseDisjoint_sheet.subset hsub) ⟨rfl, rfl⟩ (C.mem_sheet ψ₀ hψ₀)

#rt_check RoundTrip.V8_31.A_to_B [Polyfold.EpFunctor.remark_8_5_4_a,
  Polyfold.EpFunctor.remark_8_5_4_b, Polyfold.EpFunctor.ProperCoveringChart.connectedComponentIn_U,
  Polyfold.EpFunctor.ProperCoveringChart.connectedComponentIn_sheet]
#rt_check RoundTrip.V8_31.B_to_A [Polyfold.EpFunctor.remark_8_5_4_a,
  Polyfold.EpFunctor.remark_8_5_4_b, Polyfold.EpFunctor.ProperCoveringChart.connectedComponentIn_U,
  Polyfold.EpFunctor.ProperCoveringChart.connectedComponentIn_sheet]
#rt_overlap RoundTrip.V8_31.B_to_A [Polyfold.EpFunctor.remark_8_5_4_a,
  Polyfold.EpFunctor.remark_8_5_4_b, Polyfold.EpFunctor.ProperCoveringChart.connectedComponentIn_U,
  Polyfold.EpFunctor.ProperCoveringChart.connectedComponentIn_sheet]

end RoundTrip.V8_31
