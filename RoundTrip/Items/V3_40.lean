import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_40

/-!
Round trip for V3_40 (Lemma 3.45: good position under linear isomorphisms).

`A` is the conjunction of the types of `Polyfold.IsGoodComplement.map` and
`Polyfold.IsInGoodPosition.map` (no universe parameters): a continuous linear isomorphism
`S : E₀ ≃ E'₀` with `x ∈ C ↔ Sx ∈ C'` carries an (algebraic) good complement `P` of `N` to a good
complement `S(P)` of `S(N)`, and good position to good position.

Glue for `A → B`:
* `ψ = base Φ`, `ψ' = base Φ'` are inverse sc-smooth maps `U ⇄ U'` with `ψ(0) = 0`
  (`IsStrongBundleIso.base_*`); B's `Dφ 0` is the chosen `scDeriv U ψ 0` (uniqueness of the
  derivative at `0 ∈ U₁`, `IsSc1With.eq_of_eq_near`);
* `S = Dψ(0)` with inverse `Dψ'(0)` (chain rule `scDeriv_comp_eq_self`), `x ∈ C ↔ Sx ∈ C'`
  (`scDeriv_mem_iff_of_inverse`, the one-sided sign argument for `ψ` and `ψ'`);
* B's good complement is an sc-complement; its level-`0` part is A's algebraic good complement,
  and A (`IsGoodComplement.map`) gives the `ε`-property of the image; the sc-splitting of the
  image is carried by the sc-isomorphism `Dψ(0)` (derivatives at the smooth point `0` are
  sc-operators, `scOperator_deriv`; `IsScSplitting.map`).
-/

namespace RoundTrip.V3_40
open Polyfold Set

/-- The project's statement: Lemma 3.45 in its linear form. -/
def A : Prop :=
  type_of% @Polyfold.IsGoodComplement.map ∧ type_of% @Polyfold.IsInGoodPosition.map

theorem A_holds : A := ⟨@Polyfold.IsGoodComplement.map, @Polyfold.IsInGoodPosition.map⟩

section Glue

variable {E F E' F' : ScBanach} {C U : Set (E.lvl 0)} {C' U' : Set (E'.lvl 0)}
  {Φ : E.lvl 0 × F.lvl 0 → E'.lvl 0 × F'.lvl 0} {Φ' : E'.lvl 0 × F'.lvl 0 → E.lvl 0 × F.lvl 0}

/-- The derivative of the base map of a strong bundle isomorphism at `0`, as a linear
isomorphism `E₀ ≃ E'₀` that is an sc-isomorphism, carries `C` onto `C'`, and equals any other
derivative family at `0`. -/
theorem deriv_data (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U')
    (hΦ : IsStrongBundleIso U U' Φ Φ') (h0 : (0 : E.lvl 0) ∈ U)
    (hψ0 : IsStrongBundleMap.base Φ 0 = 0) :
    let D := scDeriv U (IsStrongBundleMap.base Φ) 0
    let D' := scDeriv U' (IsStrongBundleMap.base Φ') 0
    IsScOperator D ∧ IsScOperator D' ∧ (∀ v, D' (D v) = v) ∧ (∀ w, D (D' w) = w) ∧
      (∀ x, x ∈ C ↔ D x ∈ C') := by
  intro D D'
  have h01 : (0 : E.lvl 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have h0U' : (0 : E'.lvl 0) ∈ U' := hψ0 ▸ hΦ.toFun.base_mem h0
  have h01' : (0 : E'.lvl 1) ∈ E'.lvlSet U' 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0U'
  set ψ := IsStrongBundleMap.base Φ with hψdef
  set ψ' := IsStrongBundleMap.base Φ' with hψ'def
  have hψψ' : ∀ u ∈ U, ψ' (ψ u) = u := fun u hu => hΦ.base_base hu
  have hψ'ψ : ∀ u' ∈ U', ψ (ψ' u') = u' := fun u' hu' => hΦ.base_base' hu'
  have hψ'0 : ψ' 0 = 0 := hΦ.base_zero' h0 hψ0
  have hψsm : IsScSmooth U ψ := hΦ.toFun.base_isScSmooth hU
  have hψ'sm : IsScSmooth U' ψ' := hΦ.invFun.base_isScSmooth hU'
  have hψU' : MapsTo ψ U U' := fun u hu => hΦ.toFun.base_mem hu
  have hψ'U : MapsTo ψ' U' U := fun u hu => hΦ.invFun.base_mem hu
  have hlevψ : levelMap ψ 1 (0 : E.lvl 1) = 0 :=
    levelMap_eq_of_toBase_eq (by rw [map_zero, map_zero, hψ0])
  have hlevψ' : levelMap ψ' 1 (0 : E'.lvl 1) = 0 :=
    levelMap_eq_of_toBase_eq (by rw [map_zero, map_zero, hψ'0])
  have hs : (0 : E.lvl 1) ∈ E.smoothLvl 1 := by
    simp [ScScale.smoothLvl]
  have hs' : (0 : E'.lvl 1) ∈ E'.smoothLvl 1 := by
    simp [ScScale.smoothLvl]
  refine ⟨hψsm.isSc1.isSc1With_scDeriv.scOperator_deriv h01 hs,
    hψ'sm.isSc1.isSc1With_scDeriv.scOperator_deriv h01' hs', fun x => ?_, fun x => ?_,
    fun x => scDeriv_mem_iff_of_inverse hU hU' hψsm hψ'sm hψU' hψ'U hψψ' h0 hψ0 x⟩
  · have := scDeriv_comp_eq_self hU hU' hψsm.isSc1 hψ'sm.isSc1 hψU' hψψ' h01 x
    rwa [hlevψ] at this
  · have := scDeriv_comp_eq_self hU' hU hψ'sm.isSc1 hψsm.isSc1 hψ'U hψ'ψ h01' x
    rwa [hlevψ'] at this

end Glue

theorem A_to_B : A → B := by
  intro hA n N W Ct G h Bh s _hCt _hh _hs _hs0 f D _hD _hsurj _ _hpos n' N' W' Ct' U U' Φ Φ' _hCt'
    hU h0 _hUG hU' hΦ hψ0 _hraised Kperp hKperp Dφ hDφ
  obtain ⟨hDop, hD'op, hD'D, hDD', hCC'⟩ := deriv_data hU hU' hΦ h0 hψ0
  -- B's `Dφ 0` is the chosen derivative
  have h01 : (0 : (ScBanach.paramProd (Fin n → ℝ) W).lvl 1) ∈
      (ScBanach.paramProd (Fin n → ℝ) W).lvlSet U 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have hDeq : Dφ 0 = scDeriv U (IsStrongBundleMap.base Φ) 0 := by
    have hsm : IsScSmooth U (IsStrongBundleMap.base Φ) := hΦ.toFun.base_isScSmooth hU
    have h1 : IsSc1With (U ∩ univ) (IsStrongBundleMap.base Φ) Dφ := by rwa [inter_univ]
    have h2 : IsSc1With (U ∩ univ) (IsStrongBundleMap.base Φ)
        (scDeriv U (IsStrongBundleMap.base Φ)) := by
      rw [inter_univ]; exact hsm.isSc1.isSc1With_scDeriv
    exact IsSc1With.eq_of_eq_near isOpen_univ isOpen_univ hU.isScDomain h1 h2 h01
      (by rw [ScBanach.mem_lvlSet]; trivial) (by rw [ScBanach.mem_lvlSet]; trivial)
  rw [hDeq]
  have hS := ContinuousLinearEquiv.equivOfInverse _ _ hD'D hDD'
  obtain ⟨hsplit, ε, hε, hgood⟩ := hKperp
  have hgc : IsGoodComplement (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ univ) (kerOf (D 0))
      Kperp := by
    refine ⟨?_, ε, hε, hgood⟩
    have := hsplit.2.2 0
    rwa [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at this
  have hmap := hA.1 (ContinuousLinearEquiv.equivOfInverse _ _ hD'D hDD') (fun x => hCC' x) hgc
  exact ⟨IsScSplitting.map hDop hD'op hD'D hDD' hsplit, hmap.exists_eps⟩

#rt_check RoundTrip.V3_40.A_to_B [Polyfold.IsGoodComplement.map, Polyfold.IsInGoodPosition.map]
#rt_overlap RoundTrip.V3_40.A_to_B [Polyfold.IsGoodComplement.map, Polyfold.IsInGoodPosition.map]

end RoundTrip.V3_40
