import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_21

/-! Round trip for V8_21 (after Definition 8.3.1 = 2017 Definition 8.4, 2017 p. 271: the fibre
maps `μ(ψ, ·) : W_x → W_y`).

The item lists the definitions `EpStrongBundle.fiberMor` (`μ(ψ, ·)` as a bounded linear operator)
and `fiberMorEquiv` (as a topological linear isomorphism), and the theorems `fiberMor_apply`,
`μ_add`, `μ_smul`, `μ_inv_μ`, `μ_μ_inv`.  `A` is the conjunction of the types of the theorems,
universes at `0` (B lives in `Type`).

`B`: for every project strong bundle `E` over `X` (characterized in V8_20) there is a family
`L ψ : W_{s ψ} ≃ₗ W_{t ψ}` of linear isomorphisms with `L ψ = μ(ψ, ·)`, `L(1_x) = id` and
`L(ψ ∘ γ) = L(ψ) ∘ L(γ)` (stated on points of `W`).

* `A ⇒ B`: `L ψ` is built from A: additivity and homogeneity from `μ_add`, `μ_smul`, the inverse
  `μ(ψ⁻¹, ·)` with `μ_inv_μ`, `μ_μ_inv`; the membership `μ(ψ, w) ∈ W_{t ψ}` is the V8_20 theorem
  `P_μ` (not an item theorem here).  The unit and composition laws are the fields `μ_unit`,
  `μ_comp` of the structure (Definition 8.3.1 (2), (3)), after `μ_congr`.
* `B ⇒ A`: `fiberMor_apply` is `rfl` (proved outright: it is the definition of `fiberMor`);
  `μ_add`, `μ_smul` are the linearity of B's `L ψ`; `μ_inv_μ`, `μ_μ_inv` follow from B's
  composition law for `ψ⁻¹ ∘ ψ`, `ψ ∘ ψ⁻¹` and B's unit law (with the groupoid laws of `X`).
-/

namespace RoundTrip.V8_21
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpStrongBundle.fiberMor_apply.{0, 0}) ∧
  (type_of% @Polyfold.EpStrongBundle.μ_add.{0, 0}) ∧
  (type_of% @Polyfold.EpStrongBundle.μ_smul.{0, 0}) ∧
  (type_of% @Polyfold.EpStrongBundle.μ_inv_μ.{0, 0}) ∧
  (type_of% @Polyfold.EpStrongBundle.μ_μ_inv.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.fiberMor_apply.{0, 0}, @Polyfold.EpStrongBundle.μ_add.{0, 0},
    @Polyfold.EpStrongBundle.μ_smul.{0, 0}, @Polyfold.EpStrongBundle.μ_inv_μ.{0, 0},
    @Polyfold.EpStrongBundle.μ_μ_inv.{0, 0}⟩

section Glue
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

/-- `μ(ψ, ·)` as a linear isomorphism, built from the conjuncts of `A`. -/
def Lof (hA : A) (E : EpStrongBundle X B) (ψ : Mor) :
    (P ⁻¹' {X.src ψ}) ≃ₗ[ℝ] (P ⁻¹' {X.tgt ψ}) where
  toFun v := ⟨E.μ ⟨(ψ, v), v.2⟩, E.P_μ _⟩
  map_add' v v' := Subtype.ext (hA.2.1 E ψ v v')
  map_smul' a v := Subtype.ext (hA.2.2.1 E ψ a v)
  invFun v := ⟨E.μ ⟨(X.inv ψ, v), v.2.trans (X.src_inv ψ).symm⟩, by
    change P (E.μ _) = X.src ψ; rw [E.P_μ]; exact X.tgt_inv ψ⟩
  left_inv v := Subtype.ext (hA.2.2.2.1 E ⟨(ψ, v), v.2⟩ _)
  right_inv v := Subtype.ext (hA.2.2.2.2 E ψ v _ _)

theorem Lof_apply (hA : A) (E : EpStrongBundle X B) (ψ : Mor) (v : P ⁻¹' {X.src ψ}) :
    (Lof hA E ψ v : W) = E.μ ⟨(ψ, v), v.2⟩ := rfl

end Glue

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E
  refine ⟨Lof hA E, fun ψ w => rfl, ?_, ?_⟩
  · intro x w
    have hx : P (w : W) = x := w.2.trans (X.src_unit x)
    rw [Lof_apply]
    refine (E.μ_congr ?_).trans (E.μ_unit w)
    change (X.unit x, (w : W)) = (X.unit (P w), (w : W))
    rw [hx]
  · intro ψ γ hψγ w w' v hw hv
    rw [Lof_apply, Lof_apply]
    rw [Lof_apply] at hv
    have h₁ : P (w' : W) = X.src γ := w'.2
    refine (E.μ_congr ?_).trans ((E.μ_comp ψ γ w' h₁ hψγ).trans (E.μ_congr ?_))
    · change (X.comp ψ γ, (w : W)) = (X.comp ψ γ, (w' : W))
      rw [hw]
    · change (ψ, E.μ ⟨(γ, (w' : W)), h₁⟩) = (ψ, (v : W))
      rw [hv]

/-! ### `B ⇒ A` -/

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E ψ v
    rfl
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E ψ v v'
    obtain ⟨L, hL, -, -⟩ := hB Obj Mor X W P B E
    refine (hL ψ (v + v')).symm.trans ?_
    rw [map_add]
    congr 1
    congr 1 <;> exact Subtype.ext (hL ψ _)
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E ψ a v
    obtain ⟨L, hL, -, -⟩ := hB Obj Mor X W P B E
    refine (hL ψ (a • v)).symm.trans ?_
    rw [map_smul]
    congr 1
    congr 1
    exact Subtype.ext (hL ψ _)
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E q h
    obtain ⟨L, hL, hunit, hcomp⟩ := hB Obj Mor X W P B E
    obtain ⟨⟨ψ, w⟩, hq⟩ := q
    have hq' : P w = X.src ψ := hq
    have hw₀ : P w = X.src (X.comp (X.inv ψ) ψ) := by rw [X.inv_comp, X.src_unit]; exact hq'
    have hw₁ : P w = X.src (X.unit (X.src ψ)) := by rw [X.src_unit]; exact hq'
    have hc := hcomp (X.inv ψ) ψ (X.src_inv ψ) ⟨w, hw₀⟩ ⟨w, hq⟩ ⟨E.μ ⟨(ψ, w), hq⟩, h⟩ rfl
      (hL ψ ⟨w, hq⟩).symm
    have hu := hunit (X.src ψ) ⟨w, hw₁⟩
    rw [hL] at hc hu
    rw [hL] at hc
    refine hc.symm.trans ((E.μ_congr ?_).trans hu)
    change (X.comp (X.inv ψ) ψ, w) = (X.unit (X.src ψ), w)
    rw [X.inv_comp]
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E ψ w h h'
    obtain ⟨L, hL, hunit, hcomp⟩ := hB Obj Mor X W P B E
    have ht : P w = X.tgt ψ := h.trans (X.src_inv ψ)
    have hw₀ : P w = X.src (X.comp ψ (X.inv ψ)) := by rw [X.comp_inv, X.src_unit]; exact ht
    have hw₁ : P w = X.src (X.unit (X.tgt ψ)) := by rw [X.src_unit]; exact ht
    have hc := hcomp ψ (X.inv ψ) (X.tgt_inv ψ).symm ⟨w, hw₀⟩ ⟨w, h⟩
      ⟨E.μ ⟨(X.inv ψ, w), h⟩, h'⟩ rfl (hL (X.inv ψ) ⟨w, h⟩).symm
    have hu := hunit (X.tgt ψ) ⟨w, hw₁⟩
    rw [hL] at hc hu
    rw [hL] at hc
    refine hc.symm.trans ((E.μ_congr ?_).trans hu)
    change (X.comp ψ (X.inv ψ), w) = (X.unit (X.tgt ψ), w)
    rw [X.comp_inv]

#rt_check RoundTrip.V8_21.A_to_B [Polyfold.EpStrongBundle.fiberMor_apply,
  Polyfold.EpStrongBundle.μ_add, Polyfold.EpStrongBundle.μ_smul,
  Polyfold.EpStrongBundle.μ_inv_μ, Polyfold.EpStrongBundle.μ_μ_inv]
#rt_check RoundTrip.V8_21.B_to_A [Polyfold.EpStrongBundle.fiberMor_apply,
  Polyfold.EpStrongBundle.μ_add, Polyfold.EpStrongBundle.μ_smul,
  Polyfold.EpStrongBundle.μ_inv_μ, Polyfold.EpStrongBundle.μ_μ_inv]
#rt_overlap RoundTrip.V8_21.B_to_A [Polyfold.EpStrongBundle.fiberMor_apply,
  Polyfold.EpStrongBundle.μ_add, Polyfold.EpStrongBundle.μ_smul,
  Polyfold.EpStrongBundle.μ_inv_μ, Polyfold.EpStrongBundle.μ_μ_inv]

end RoundTrip.V8_21
