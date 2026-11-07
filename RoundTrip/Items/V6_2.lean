import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_2

/-! Round trip for V6_2 (§6.2, pp. 203–204: `λ(E)`, `λ*(E)`, `λ(Φ)`, `λ*(Φ)`, `v*`).  A is the
conjunction of the eleven theorems of the comparison row, universes at `0`.  The definitions
`maxPow`, `maxPowDual`, `maxPowDualMap` are literally the text's (B's clauses (1), (2), (6) hold by
`rfl`).  A also contains five lemmas on wedges (`wedge_eq_det_smul` and the four two-block lemmas)
which the text does not state and B does not mention; in `B_to_A` they are re-proved outright
(from the non-item project lemmas `wedge_eq_det_smul'`, `alternatingMap_eq_det_smul`,
`alternatingMap_eq_of_sub_mem_span`, `appendLeftMap`, `appendRightMap`).  A's `maxPowMap_wedge`
(any `k`) and `maxPowMap_comp` carry no finite-dimensionality hypothesis; B states them for
finite-dimensional spaces, so their infinite-dimensional cases are re-proved outright too. -/

namespace RoundTrip.V6_2
open Polyfold Module

/-- The project's statement, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.finrank_maxPow.{0} ∧
  type_of% @Polyfold.wedge_eq_det_smul.{0} ∧
  type_of% @Polyfold.wedge_append_basis_left.{0, 0} ∧
  type_of% @Polyfold.wedge_append_basis_right.{0, 0} ∧
  type_of% @Polyfold.wedge_append_add_left.{0} ∧
  type_of% @Polyfold.wedge_append_add_right.{0} ∧
  type_of% @Polyfold.dualVec_self.{0} ∧
  type_of% @Polyfold.eq_dualVec_of_apply_eq_one.{0} ∧
  type_of% @Polyfold.maxPowMap_wedge.{0, 0} ∧
  type_of% @Polyfold.maxPowMap_comp.{0, 0, 0} ∧
  type_of% @Polyfold.maxPowMap_ne_zero_iff.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.finrank_maxPow.{0}, @Polyfold.wedge_eq_det_smul.{0},
    @Polyfold.wedge_append_basis_left.{0, 0}, @Polyfold.wedge_append_basis_right.{0, 0},
    @Polyfold.wedge_append_add_left.{0}, @Polyfold.wedge_append_add_right.{0},
    @Polyfold.dualVec_self.{0}, @Polyfold.eq_dualVec_of_apply_eq_one.{0},
    @Polyfold.maxPowMap_wedge.{0, 0}, @Polyfold.maxPowMap_comp.{0, 0, 0},
    @Polyfold.maxPowMap_ne_zero_iff.{0, 0}⟩

theorem A_to_B : A → B := by
  rintro ⟨hFin, -, -, -, -, -, hDS, -, hMW, hComp, hNZ⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro E _ _ _
    exact ⟨rfl, hFin⟩
  · intro E _ _
    rfl
  · intro E F _ _ _ _ _ _ Φ h a
    exact hMW Φ h a rfl
  · intro E F _ _ _ _ _ _ Φ h
    exact hNZ Φ h
  · intro E F G _ _ _ _ _ _ _ _ _ Φ Ψ h₁ h₂
    exact hComp Φ Ψ h₁ h₂
  · intro E F _ _ _ _ _ _ Φ h φ w
    rfl
  · intro L _ _ h1 v hv
    exact hDS h1 hv

/-! ### Outright facts used in `B_to_A` (not in B) -/

section Outright
variable {E F G W : Type} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup W] [Module ℝ W]

/-- `λ(Φ)` on wedges, any spaces (the defining formula, re-proved from Mathlib's
`exteriorPower.map_apply_ιMulti`). -/
theorem maxPowMap_wedge' (Φ : E →ₗ[ℝ] F) (h : finrank ℝ E = finrank ℝ F) {k : ℕ}
    (v : Fin k → E) (hk : k = finrank ℝ E) :
    maxPowMap Φ h (wedge v hk) = wedge (Φ ∘ v) (hk.trans h) := by
  subst hk
  apply Subtype.ext
  simp only [maxPowMap, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.coe_ofEq_apply, wedge_eq_ιMulti, exteriorPower.map_apply_ιMulti,
    exteriorPower.ιMulti_apply_coe, coe_wedge]

theorem maxPowMap_comp' (Φ : E →ₗ[ℝ] F) (Ψ : F →ₗ[ℝ] G) (h : finrank ℝ E = finrank ℝ F)
    (h' : finrank ℝ F = finrank ℝ G) :
    maxPowMap (Ψ ∘ₗ Φ) (h.trans h') = maxPowMap Ψ h' ∘ₗ maxPowMap Φ h := by
  apply exteriorPower.linearMap_ext
  ext v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
    ← wedge_eq_ιMulti, maxPowMap_wedge', coe_wedge]
  rfl

theorem wedge_append_basis_left' {p q : ℕ}
    (f : W →ₗ[ℝ] E) (u : Basis (Fin p) ℝ W) (u' : Fin p → W) (w : Fin q → E)
    (hk : p + q = finrank ℝ E) :
    wedge (Fin.append (f ∘ u') w) hk = u.det u' • wedge (Fin.append (f ∘ u) w) hk := by
  apply Subtype.ext
  simp only [coe_wedge, SetLike.val_smul]
  exact alternatingMap_eq_det_smul
    ((appendLeftMap (ExteriorAlgebra.ιMulti ℝ (p + q)) w).compLinearMap f) u u'

theorem wedge_append_basis_right' {p q : ℕ}
    (g : W →ₗ[ℝ] E) (u : Fin p → E) (w : Basis (Fin q) ℝ W) (w' : Fin q → W)
    (hk : p + q = finrank ℝ E) :
    wedge (Fin.append u (g ∘ w')) hk = w.det w' • wedge (Fin.append u (g ∘ w)) hk := by
  apply Subtype.ext
  simp only [coe_wedge, SetLike.val_smul]
  exact alternatingMap_eq_det_smul
    ((appendRightMap (ExteriorAlgebra.ιMulti ℝ (p + q)) u).compLinearMap g) w w'

theorem wedge_append_add_right' {p q : ℕ} (u : Fin p → E) (w x : Fin q → E)
    (hx : ∀ i, x i ∈ Submodule.span ℝ (Set.range u)) (hk : p + q = finrank ℝ E) :
    wedge (Fin.append u (w + x)) hk = wedge (Fin.append u w) hk := by
  apply Subtype.ext
  simp only [coe_wedge]
  apply alternatingMap_eq_of_sub_mem_span _ (Set.range (Fin.castAdd q))
  · rintro _ ⟨i, rfl⟩
    simp
  · intro i hi
    rw [image_append_range_castAdd]
    induction i using Fin.addCases with
    | left i => exact absurd ⟨i, rfl⟩ hi
    | right i => simpa using hx i

theorem wedge_append_add_left' {p q : ℕ} (u x : Fin p → E) (w : Fin q → E)
    (hx : ∀ i, x i ∈ Submodule.span ℝ (Set.range w)) (hk : p + q = finrank ℝ E) :
    wedge (Fin.append (u + x) w) hk = wedge (Fin.append u w) hk := by
  apply Subtype.ext
  simp only [coe_wedge]
  apply alternatingMap_eq_of_sub_mem_span _ (Set.range (Fin.natAdd p))
  · rintro _ ⟨i, rfl⟩
    simp
  · intro i hi
    rw [image_append_range_natAdd]
    induction i using Fin.addCases with
    | left i => simpa using hx i
    | right i => exact absurd ⟨i, rfl⟩ hi

end Outright

theorem B_to_A : B → A := by
  rintro ⟨hB1, -, hB3, hB4, hB5, -, hB7⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `finrank_maxPow`: B (1)
    intro E _ _ _
    exact (hB1 E).2
  · -- `wedge_eq_det_smul`: not in B (outright, `wedge_eq_det_smul'`)
    intro E _ _ _ b w
    exact wedge_eq_det_smul' b w rfl
  · intro E _ _ W _ _ p q f u u' w hk
    exact wedge_append_basis_left' f u u' w hk
  · intro E _ _ W _ _ p q g u w w' hk
    exact wedge_append_basis_right' g u w w' hk
  · intro E _ _ p q u x w hx hk
    exact wedge_append_add_left' u x w hx hk
  · intro E _ _ p q u w x hx hk
    exact wedge_append_add_right' u w x hx hk
  · -- `dualVec_self`: B (7)
    intro L _ _ h1 v hv
    exact hB7 L h1 v hv
  · -- `eq_dualVec_of_apply_eq_one`: B (7) and "a functional on a line is fixed by one value"
    intro L _ _ h1 v hv φ h
    exact dual_ext_of_ne_zero h1 hv (by rw [h, hB7 L h1 v hv])
  · -- `maxPowMap_wedge`: B (3) for finite-dimensional spaces; otherwise outright
    intro E F _ _ _ _ Φ h k v hk
    by_cases hfd : FiniteDimensional ℝ E ∧ FiniteDimensional ℝ F
    · obtain ⟨_, _⟩ := hfd
      subst hk
      exact hB3 E F Φ h v
    · exact maxPowMap_wedge' Φ h v hk
  · -- `maxPowMap_comp`: B (5) for finite-dimensional spaces; otherwise outright
    intro E F G _ _ _ _ _ _ Φ Ψ h h'
    by_cases hfd : FiniteDimensional ℝ E ∧ FiniteDimensional ℝ F ∧ FiniteDimensional ℝ G
    · obtain ⟨_, _, _⟩ := hfd
      exact hB5 E F G Φ Ψ h h'
    · exact maxPowMap_comp' Φ Ψ h h'
  · -- `maxPowMap_ne_zero_iff`: B (4)
    intro E F _ _ _ _ _ _ Φ h
    exact hB4 E F Φ h

#rt_check RoundTrip.V6_2.A_to_B [Polyfold.finrank_maxPow, Polyfold.wedge_eq_det_smul,
  Polyfold.wedge_append_basis_left, Polyfold.wedge_append_basis_right,
  Polyfold.wedge_append_add_left, Polyfold.wedge_append_add_right, Polyfold.dualVec_self,
  Polyfold.eq_dualVec_of_apply_eq_one, Polyfold.maxPowMap_wedge, Polyfold.maxPowMap_comp,
  Polyfold.maxPowMap_ne_zero_iff]
#rt_check RoundTrip.V6_2.B_to_A [Polyfold.finrank_maxPow, Polyfold.wedge_eq_det_smul,
  Polyfold.wedge_append_basis_left, Polyfold.wedge_append_basis_right,
  Polyfold.wedge_append_add_left, Polyfold.wedge_append_add_right, Polyfold.dualVec_self,
  Polyfold.eq_dualVec_of_apply_eq_one, Polyfold.maxPowMap_wedge, Polyfold.maxPowMap_comp,
  Polyfold.maxPowMap_ne_zero_iff]
#rt_overlap RoundTrip.V6_2.B_to_A [Polyfold.finrank_maxPow, Polyfold.wedge_eq_det_smul,
  Polyfold.wedge_append_basis_left, Polyfold.wedge_append_basis_right,
  Polyfold.wedge_append_add_left, Polyfold.wedge_append_add_right, Polyfold.dualVec_self,
  Polyfold.eq_dualVec_of_apply_eq_one, Polyfold.maxPowMap_wedge, Polyfold.maxPowMap_comp,
  Polyfold.maxPowMap_ne_zero_iff]

end RoundTrip.V6_2
