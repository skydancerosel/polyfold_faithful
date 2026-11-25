import Polyfold.Examples.OrbifoldSquareOrientation
import Polyfold.Examples.OrbifoldSquareInfNorm

/-!
# Examples for the orientation space `O_f` and the fibres `(Y_{0,1})_x`

Non-examples for the rows V6.71 and V6.73 (the orientation space `O_f` of Theorem 6.6.17) and
V5.2 (the fibre `(Y_{0,1})_x`) of Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory*
(Springer 2021), pp. 274–275 and §5.3.

* `not_isOrientationTopology_top`: the indiscrete topology on `O_f` is never a topology with the
  properties of Theorem 6.6.17 (it is not Hausdorff, since `Or_x^f` has two points);
  `not_isOrientationTopology_top_sq`: the same for the section `z ↦ z²` of the worked example.
* `harm_not_mem_oneSet_BH`: in the bundle `H ◁ H` over the weighted `ℓ²` space `H`, the vector
  `(1/(k+1))_k` of the fibre over `0` does not lie in `(Y_{0,1})_0`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold.Examples.Path

open Polyfold

universe u v

/-! ### The indiscrete topology on `O_f` (rows V6.71, V6.73) -/

section Indiscrete

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- Rows V6.71 and V6.73, Theorem 6.6.17 (pp. 274–275): over a nonempty `X_∞`, the indiscrete
topology on `O_f` does not have the properties of the theorem, since it is not Hausdorff. -/
theorem not_isOrientationTopology_top (hf : B.IsScFredholmSection f)
    (hsec : B.HasScPlusSectionsThrough) (y : PX.SmoothLevel) :
    ¬ IsOrientationTopology f hf ⊤ := by
  intro h
  obtain ⟨a, b, hab, -⟩ := exists_two_orx hf (PX.smoothVal_mem y) hsec
  have ht2 := h.t2Space
  have hne : (⟨y, a⟩ : OrSpace f hf) ≠ ⟨y, b⟩ := fun h' => hab (eq_of_heq (Sigma.mk.inj h').2)
  obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ := @t2_separation _ ⊤ ht2 _ _ hne
  rw [TopologicalSpace.isOpen_top_iff] at hU hV
  rcases hU with rfl | rfl
  · exact haU
  rcases hV with rfl | rfl
  · exact hbV
  rw [disjoint_univ.1 hUV] at haU
  exact haU

end Indiscrete

section Square

open OrbifoldSquare TrivialBundle EpGroupoid.Examples StrongBundle

/-- Rows V6.71 and V6.73, Theorem 6.6.17 (pp. 274–275): for the section `z ↦ z²` of the worked
example the indiscrete topology on `O_f` is not an orientation topology, while the topology
`isOrientationTopology_sqSection` is one. -/
theorem not_isOrientationTopology_top_sq :
    haveI := paracompactSpace_rn_prod A5.X.PObj
    haveI := paracompactSpace_rn_pullback A5.B
    ¬ IsOrientationTopology (B := A5.B) sqSection isScFredholmSectionFunctor_sqSection.2 ⊤ := by
  have := paracompactSpace_rn_prod A5.X.PObj
  have := paracompactSpace_rn_pullback A5.B
  exact not_isOrientationTopology_top _ hasScPlusSectionsThrough_A5
    (A5.X.PObj.smoothMk (0 : Fin 2 → ℝ) (mem_smoothSet_A5 (0 : Fin 2 → ℝ)))

end Square

/-! ### The fibre `(Y_{0,1})_x` (row V5.2) -/

section OneFiber

open OrbifoldSquareInf WeightedEllTwo

/-- The map `H_1 → H_0` of the weighted `ℓ²` space is the diagonal operator `incl`. -/
theorem toBase_one_eq_incl (y : H 1) : H.toBase 1 y = incl y := by
  change (scale.toBase 1 y : L2) = incl y
  refine lp.ext (funext fun k => ?_)
  have h := toBase_apply 1 y k
  rw [pow_one] at h
  exact h.trans (incl_apply y k).symm

/-- Row V5.2, the fibre `(Y_{0,1})_x` and its chart norm `|·|_1` (§5.3): in the bundle
`H ◁ H → H` of the worked example, the vector `(1/(k+1))_k` of the fibre over `0` does not lie in
`(Y_{0,1})_0`, so `(Y_{0,1})_0` is a proper subspace of the fibre. -/
theorem harm_not_mem_oneSet_BH : ((h0, WeightedEllTwo.harmH) : HObj × H 0) ∉ BH.oneSet := by
  rw [mem_oneSet_BH]
  rintro ⟨y, hy⟩
  exact incl_ne_harm y ((toBase_one_eq_incl y).symm.trans hy)

end OneFiber

end Polyfold.Examples.Path
