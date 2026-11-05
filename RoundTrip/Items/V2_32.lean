import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_32

/-! Round trip for V2_32 (Definition 2.27: the partial cone `C_xO` and the reduced tangent space
`T^R_xO`).

`A` is the conjunction of the types of the theorems listed for the item,
`Polyfold.quotDim_inf_minimalSubspace_le` and `Polyfold.quotDim_reducedTangentSpaceWith_le` (no
universe parameters).  `reducedTangentSpaceWith`, `partialConeWith`, `quotDim` are vocabulary.

The comparison that matters is between the definitions: B says the project's `partialConeWith R T
x₁` and `reducedTangentSpaceWith R T x₁` are `T_xO ∩ C_x` and `T_xO ∩ E_x`, with `T_xO` the fibre
of `Tr(TU)` over `x₁`.  This holds (at every `x ∈ O₁`, smoothness is not needed): the fibre is
`range Dr(x)` by `ScRetraction.mem_tangent_iff_mem_range` (Definition 2.17's remark), and `C_x`,
`E_x` unfold to the project's `partialQuadrantAtWith`, `minimalSubspaceWith`.  So `A → B` is
proved outright (A unused).

`B → A`: A's two theorems (`dim(A/(A ∩ E_e)) ≤ d_C(e)`, and its instance `dim(T_xO/T^R_xO) ≤
d_C(x)`) are not part of Definition 2.27 nor of B; they are proved directly (the project's
four-line argument re-proved from `finrank_quotient_minimalSubspaceWith`), without B. -/

namespace RoundTrip.V2_32
open Polyfold Set Module

section Glue
variable {k : ℕ} {W : ScBanach}

lemma coordB_apply (i : Fin k) (a : (EB k W).lvl 0) : coordB (W := W) i a = a.1 i := rfl

lemma mem_EiB_iff (i : Fin k) (a : (EB k W).lvl 0) : a ∈ EiB (W := W) i ↔ a.1 i = 0 := by
  rw [EiB, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, coordB_apply]

lemma mem_ExB_iff (x v : (EB k W).lvl 0) : v ∈ ExB x ↔ ∀ i, x.1 i = 0 → v.1 i = 0 := by
  simp only [ExB, IxB, Submodule.mem_iInf, mem_ofPred_eq]
  exact forall_congr' fun i => by rw [mem_EiB_iff, mem_EiB_iff]

lemma mem_CxB_iff (x v : (EB k W).lvl 0) : v ∈ CxB x ↔ ∀ i, x.1 i = 0 → 0 ≤ v.1 i := by
  simp only [CxB, IxB, mem_iInter, mem_ofPred_eq]
  exact forall_congr' fun i => by rw [mem_EiB_iff, coordB_apply]

/-- B's `T_xO` (fibre of `Tr(TU)` over `x₁`) is `range Dr(x₁)` at `x₁ ∈ O₁`. -/
lemma mem_TxOB_iff {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C) {x₁ : E.lvl 1}
    (hx : x₁ ∈ E.lvlSet R.retract 1) (h : E.lvl 0) :
    h ∈ TxOB R x₁ ↔ h ∈ range (scDeriv R.U R x₁) :=
  R.mem_tangent_iff_mem_range hx

end Glue

/-- The project's statement (the listed theorems). -/
def A : Prop :=
  (type_of% @Polyfold.quotDim_inf_minimalSubspace_le) ∧
  (type_of% @Polyfold.quotDim_reducedTangentSpaceWith_le)

theorem A_holds : A :=
  ⟨@Polyfold.quotDim_inf_minimalSubspace_le, @Polyfold.quotDim_reducedTangentSpaceWith_le⟩

/-- `A → B`: the definitions agree (A is not used). -/
theorem A_to_B : A → B := by
  intro _ E C O R hRO n W T _ x₁ hxO _
  have hx : x₁ ∈ E.lvlSet R.retract 1 := by rw [hRO]; exact hxO
  constructor
  · ext v
    simp only [partialConeWith, mem_inter_iff, mem_preimage]
    rw [mem_TxOB_iff R hx, mem_CxB_iff]
    rfl
  · ext v
    simp only [reducedTangentSpaceWith, SetLike.mem_coe, Submodule.mem_inf, mem_inter_iff,
      mem_preimage]
    rw [mem_TxOB_iff R hx, mem_ExB_iff, mem_minimalSubspaceWith]
    rfl

/-- `dim(A/(A ∩ E_e)) ≤ d_C(e)`, re-proved (not from B). -/
theorem quotDim_le' {E : ScBanach} {n : ℕ} {W : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (A : Submodule ℝ (E 0)) (e : E 0) :
    quotDim A (A ⊓ minimalSubspaceWith T e) ≤ degIndexWith T e := by
  set Ex := minimalSubspaceWith T e
  let Ψ : A →ₗ[ℝ] E 0 ⧸ Ex := Ex.mkQ.comp A.subtype
  have hΨker : LinearMap.ker Ψ = (A ⊓ Ex).comap A.subtype := by
    ext ⟨w, hw⟩
    simp only [Ψ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_inf]
    exact ⟨fun h => ⟨hw, h⟩, fun h => h.2⟩
  have hemb : (A ⧸ (A ⊓ Ex).comap A.subtype) ≃ₗ[ℝ] LinearMap.range Ψ :=
    hΨker ▸ Ψ.quotKerEquivRange
  rw [quotDim, ← finrank_quotient_minimalSubspaceWith T, hemb.finrank_eq]
  exact Submodule.finrank_le _

/-- `B → A`: A's inequalities are proved directly (B is not used). -/
theorem B_to_A : B → A := fun _ =>
  ⟨@quotDim_le', fun _ T _ => quotDim_le' T _ _⟩

#rt_check RoundTrip.V2_32.A_to_B [Polyfold.quotDim_inf_minimalSubspace_le, Polyfold.quotDim_reducedTangentSpaceWith_le]
#rt_check RoundTrip.V2_32.B_to_A [Polyfold.quotDim_inf_minimalSubspace_le, Polyfold.quotDim_reducedTangentSpaceWith_le]
#rt_overlap RoundTrip.V2_32.B_to_A [Polyfold.quotDim_inf_minimalSubspace_le, Polyfold.quotDim_reducedTangentSpaceWith_le]

end RoundTrip.V2_32
