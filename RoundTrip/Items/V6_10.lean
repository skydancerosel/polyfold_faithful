import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_10

/-!
Round trip for V6_10 (Definition 6.9 and the remarks after it).  `A` is the conjunction of the
types of the nine theorems of the item (`ProjLE.refl/antisymm/trans`,
`IsGoodLeftProj.isFredholm/fredholmIndex_eq_zero/isFredholm_comp/fredholmIndex_comp/
finiteDimensional_quotient_inf`, `exists_isGoodLeftProj`), universes instantiated at `0`.

The definitions agree: B's `IsGLP`, `PiT`, `PLe` are the project's `IsGoodLeftProj` (same three
fields), `goodLeftProjs`, `ProjLE` (`isGLP_iff`, `piT_eq`, `pLe_iff`).  Glue for `A → B`: B's
classical `IsFredholmOp` gives Mathlib's `IsFredholm` on Banach spaces (`isFredholm_of_banach`),
and back by the fields; the project's `fredholmIndex` is literally B's `fredIdx`.
-/

namespace RoundTrip.V6_10
open Polyfold

/-- The project's statement (Definition 6.9 and the remarks after it), universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.ProjLE.refl.{0} ∧
  type_of% @Polyfold.ProjLE.antisymm.{0} ∧
  type_of% @Polyfold.ProjLE.trans.{0} ∧
  type_of% @Polyfold.IsGoodLeftProj.isFredholm.{0, 0} ∧
  type_of% @Polyfold.IsGoodLeftProj.fredholmIndex_eq_zero.{0, 0} ∧
  type_of% @Polyfold.IsGoodLeftProj.isFredholm_comp.{0, 0} ∧
  type_of% @Polyfold.IsGoodLeftProj.fredholmIndex_comp.{0, 0} ∧
  type_of% @Polyfold.IsGoodLeftProj.finiteDimensional_quotient_inf.{0, 0} ∧
  type_of% @Polyfold.exists_isGoodLeftProj.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.ProjLE.refl, @Polyfold.ProjLE.antisymm, @Polyfold.ProjLE.trans,
    @Polyfold.IsGoodLeftProj.isFredholm, @Polyfold.IsGoodLeftProj.fredholmIndex_eq_zero,
    @Polyfold.IsGoodLeftProj.isFredholm_comp, @Polyfold.IsGoodLeftProj.fredholmIndex_comp,
    @Polyfold.IsGoodLeftProj.finiteDimensional_quotient_inf, @Polyfold.exists_isGoodLeftProj⟩

section Glue

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- B's good left-projections are the project's. -/
theorem isGLP_iff (T : E →L[ℝ] F) (P : F →L[ℝ] F) : IsGLP T P ↔ IsGoodLeftProj T P :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.isProj, h.finite_coker, h.range_comp⟩⟩

/-- B's `Π_T` is the project's. -/
theorem piT_eq (T : E →L[ℝ] F) : PiT T = goodLeftProjs T := by
  ext P
  exact isGLP_iff T P

/-- B's order is the project's. -/
theorem pLe_iff (P Q : F →L[ℝ] F) : PLe P Q ↔ ProjLE P Q := Iff.rfl

/-- B's index is the project's `fredholmIndex`. -/
theorem fredIdx_eq (L : E →L[ℝ] F) : fredIdx L = fredholmIndex L := rfl

/-- Mathlib's `IsFredholm` gives B's classical `IsFredholmOp`. -/
theorem isFredholmOp_of_isFredholm {L : E →L[ℝ] F} (h : L.IsFredholm) : IsFredholmOp L :=
  ⟨h.finite_ker, h.isClosed_range, h.finite_coker⟩

/-- On Banach spaces, B's classical `IsFredholmOp` gives Mathlib's `IsFredholm`. -/
theorem isFredholm_of_isFredholmOp [CompleteSpace E] [CompleteSpace F] {L : E →L[ℝ] F}
    (h : IsFredholmOp L) : L.IsFredholm :=
  isFredholm_of_banach L h.1 h.2.1 h.2.2

end Glue

theorem A_to_B : A → B := by
  intro hA E F _ _ _ _ _ _ T hT
  obtain ⟨hrefl, hanti, htrans, hfred, hind0, hfredc, hindc, hinf, -⟩ := hA
  have hT' : T.IsFredholm := isFredholm_of_isFredholmOp hT
  refine ⟨fun P hP => ?_, fun P hP => hrefl hP.1, fun P _ Q _ h h' => hanti h h',
    fun P _ Q _ R _ h h' => htrans h h', fun P hP P' hP' =>
      hinf ((isGLP_iff T P).1 hP) ((isGLP_iff T P').1 hP')⟩
  have hP' : IsGoodLeftProj T P := (isGLP_iff T P).1 hP
  exact ⟨isFredholmOp_of_isFredholm (hfred hP'), hind0 hP',
    isFredholmOp_of_isFredholm (hfredc hT' hP'), hindc hT' hP'⟩

/-! `B ⇒ A` is not proved.  A has content that B lacks:
* `exists_isGoodLeftProj` (`Π_T ≠ ∅` for `T` Fredholm) is not part of B (the text uses it without
  stating it);
* A's remarks are more general than B's: `ProjLE.refl/antisymm/trans` for all projections (B: on
  `Π_T`), `fredholmIndex_eq_zero` and `finiteDimensional_quotient_inf` for any normed spaces and
  any `T` (B: Banach spaces, `T` Fredholm), `isFredholm` for `E` not complete and `T` arbitrary,
  `fredholmIndex_comp` for `E` not complete.
Deriving these from B would mean re-proving them (or completing the spaces). -/

#rt_check RoundTrip.V6_10.A_to_B [Polyfold.ProjLE.refl, Polyfold.ProjLE.antisymm,
  Polyfold.ProjLE.trans, Polyfold.IsGoodLeftProj.isFredholm,
  Polyfold.IsGoodLeftProj.fredholmIndex_eq_zero, Polyfold.IsGoodLeftProj.isFredholm_comp,
  Polyfold.IsGoodLeftProj.fredholmIndex_comp,
  Polyfold.IsGoodLeftProj.finiteDimensional_quotient_inf, Polyfold.exists_isGoodLeftProj]
#rt_check RoundTrip.V6_10.isGLP_iff [Polyfold.ProjLE.refl, Polyfold.ProjLE.antisymm,
  Polyfold.ProjLE.trans, Polyfold.IsGoodLeftProj.isFredholm,
  Polyfold.IsGoodLeftProj.fredholmIndex_eq_zero, Polyfold.IsGoodLeftProj.isFredholm_comp,
  Polyfold.IsGoodLeftProj.fredholmIndex_comp,
  Polyfold.IsGoodLeftProj.finiteDimensional_quotient_inf, Polyfold.exists_isGoodLeftProj]

end RoundTrip.V6_10
