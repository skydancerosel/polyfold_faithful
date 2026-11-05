import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_33

/-! Round trip for V1_33 (proof of Proposition 1.7: the smooth points of a quotient).

`A` is the conjunction of the types of `Polyfold.ScBanach.exists_smooth_mem_coset` and
`Polyfold.ScBanach.mk_mem_quotient_smooth_iff`.  Neither has universe parameters (`ScBanach`
lives in `Type`). -/

namespace RoundTrip.V1_33
open Polyfold

/-! ### Glue: the text's sc-subspaces are the project's -/

theorem isScSubspace_of_text {E : ScBanach} {A : Submodule ℝ (E.lvl 0)}
    (h : IsScSubspaceText E A) : E.IsScSubspace A := by
  refine ⟨h.1, fun m => ?_⟩
  have hd := (Subtype.dense_iff (s := (E.levelSub A m : Set (E m)))).1 (h.2.2.2 m)
  refine hd.trans (closure_mono ?_)
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x.2, hx⟩

theorem text_of_isScSubspace {E : ScBanach} {A : Submodule ℝ (E.lvl 0)}
    (h : E.IsScSubspace A) : IsScSubspaceText E A := by
  refine ⟨h.1, fun m => ?_, fun m => ?_, fun m => ?_⟩
  · have := E.isClosed_levelSub h.1 m
    exact this.completeSpace_coe
  · exact (E.ofSubspaceScale h.1).incl_isCompactOperator m
  · refine (Subtype.dense_iff (s := (E.levelSub A m : Set (E m)))).2 fun x hx => ?_
    refine closure_mono ?_ (h.2 m hx)
    rintro y ⟨hy1, hy2⟩
    exact ⟨⟨y, hy1⟩, hy2, rfl⟩

theorem quotLevelMap_mk (E : ScBanach) (A : Submodule ℝ (E.lvl 0)) (j : ℕ) (y : E j) :
    quotLevelMap E A j (Submodule.Quotient.mk y) = Submodule.Quotient.mk (E.toBase j y) := rfl

theorem smoothQuotMap_mk (E : ScBanach) (A : Submodule ℝ (E.lvl 0)) (z : E.smooth) :
    smoothQuotMap E A (Submodule.Quotient.mk z) = Submodule.Quotient.mk (z : E 0) := rfl

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.ScBanach.exists_smooth_mem_coset) ∧
  (type_of% @Polyfold.ScBanach.mk_mem_quotient_smooth_iff)

theorem A_holds : A :=
  ⟨@Polyfold.ScBanach.exists_smooth_mem_coset, @Polyfold.ScBanach.mk_mem_quotient_smooth_iff⟩

theorem A_to_B : A → B := by
  intro hA E A hT
  have hS := isScSubspace_of_text hT
  refine ⟨Set.Subset.antisymm ?_ ?_, ?_⟩
  · rintro _ ⟨q, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [smoothQuotMap_mk]
    refine Set.mem_iInter.2 fun j => ?_
    obtain ⟨y, hy⟩ := (ScScale.mem_smooth_iff _).1 z.2 j
    exact ⟨Submodule.Quotient.mk y, by rw [quotLevelMap_mk, hy]⟩
  · intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hx : ∀ j, ∃ y : E j, E.toBase j y - x ∈ A := by
      intro j
      obtain ⟨r, hr⟩ := Set.mem_iInter.1 hq j
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ r
      rw [quotLevelMap_mk] at hr
      exact ⟨y, (Submodule.Quotient.eq _).1 hr⟩
    obtain ⟨y, hy, hyx⟩ := hA.1 E hS hx
    exact ⟨Submodule.Quotient.mk ⟨y, hy⟩, by
      rw [smoothQuotMap_mk]; exact (Submodule.Quotient.eq _).2 hyx⟩
  · rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [smoothQuotMap_mk, Submodule.Quotient.mk_eq_zero] at hq
    exact (Submodule.Quotient.mk_eq_zero _).2 hq

/-- `B → A`: the Mittag-Leffler statement `exists_smooth_mem_coset` is `B`'s
`range (E_∞/A_∞ → E/A) ⊇ ⋂_j (E_j/A_j)`; the description of the smooth points of the project's
quotient `E.quotient` follows from it as in the project. -/
theorem B_to_A : B → A := by
  intro hB
  have key : ∀ (E : ScBanach) {A : Submodule ℝ (E 0)}, E.IsScSubspace A → ∀ {x : E 0},
      (∀ j, ∃ y : E j, E.toBase j y - x ∈ A) → ∃ y ∈ E.smooth, y - x ∈ A := by
    intro E A hA x hx
    have hmem : (Submodule.Quotient.mk x : E 0 ⧸ A) ∈ quotSmooth E A := by
      refine Set.mem_iInter.2 fun j => ?_
      obtain ⟨y, hy⟩ := hx j
      exact ⟨Submodule.Quotient.mk y, by
        rw [quotLevelMap_mk]; exact (Submodule.Quotient.eq _).2 hy⟩
    rw [← (hB E A (text_of_isScSubspace hA)).1] at hmem
    obtain ⟨q, hq⟩ := hmem
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [smoothQuotMap_mk] at hq
    exact ⟨z, z.2, (Submodule.Quotient.eq _).1 hq⟩
  refine ⟨fun {E} {A} hA {x} hx => key E hA hx, ?_⟩
  intro E A hA x
  refine (ScScale.mem_smooth_iff _).trans ?_
  constructor
  · intro h
    refine key E hA fun j => ?_
    obtain ⟨z, hz⟩ := h j
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    refine ⟨y, ?_⟩
    have hz' := (E.quotientScale_toBase_mk hA.isClosed j y).symm.trans hz
    exact (Submodule.Quotient.eq _).1 hz'
  · rintro ⟨y, hy, hyx⟩ j
    obtain ⟨z, hz⟩ := (ScScale.mem_smooth_iff _).1 hy j
    refine ⟨Submodule.Quotient.mk z, ?_⟩
    refine (E.quotientScale_toBase_mk hA.isClosed j z).trans ?_
    rw [hz]
    exact (Submodule.Quotient.eq _).2 hyx

#rt_check RoundTrip.V1_33.A_to_B [Polyfold.ScBanach.exists_smooth_mem_coset,
  Polyfold.ScBanach.mk_mem_quotient_smooth_iff]
#rt_check RoundTrip.V1_33.B_to_A [Polyfold.ScBanach.exists_smooth_mem_coset,
  Polyfold.ScBanach.mk_mem_quotient_smooth_iff]
#rt_overlap RoundTrip.V1_33.B_to_A [Polyfold.ScBanach.exists_smooth_mem_coset,
  Polyfold.ScBanach.mk_mem_quotient_smooth_iff]

end RoundTrip.V1_33
