import Polyfold.Chapter2.TameRetracts
import Polyfold.Chapter2.DegeneracyIndex
import Polyfold.Chapter2.Boundary
import Polyfold.Chapter2.TameFaces

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §2.4:
**the invariance of tameness under sc-diffeomorphisms** (used silently by the text, e.g. in the
proof of Theorem 3.6.8 (preprint 3.54), where the chart `ψ ∘ ϕ` onto `ψ(O)` is taken to be a chart of the tame
M-polyfold `X`, and in Proposition 3.2.2 (preprint 3.26), "`X' = ψ(X)` is tame").

# Tameness is carried by sc-diffeomorphisms

## What is formalized

* `Polyfold.IsScDiffeoQuadrant`: an sc-diffeomorphism `ψ : U → U'` with inverse `ψ'` between
  relatively open subsets of partial quadrants.
* `Polyfold.IsScDiffeoQuadrant.transport`: the **transported retraction** `r' = ψ ∘ r ∘ ψ⁻¹` of an
  sc-smooth retraction `r : U → U`, with `r'(U') = ψ(O)` (`transport_retract`) and
  `Dr'(y) = Dψ(x) Dr(x) Dψ'(y)` at `y = ψ(x)` (`scDeriv_transport`).
* `Polyfold.IsScSubspace.map`, `Polyfold.IsScSplitting.map`: sc-subspaces and sc-splittings are
  carried by an sc-isomorphism (an sc-operator `D` with an sc-operator inverse `D'`; the level
  maps `scIsoLevel` are linear homeomorphisms `E_m ≃ E'_m`).
* `Polyfold.IsScDiffeoQuadrant.isTameWith_transport`, `isTame_transport`,
  `isTameRetract_image`: **tameness is carried by `ψ`**: if `r` is tame then so is
  `ψ ∘ r ∘ ψ⁻¹`, and `(ψ(O), C', E')` is a tame retract.  Condition (1) of Definition 2.5.2 (preprint 2.34) is
  Theorem 1.3.5 (preprint 1.25) (`ψ` preserves the degeneracy index, `degIndex_eq`); for (2), at a smooth point
  `y = ψ(x) ∈ ψ(O)` the derivative `Dψ(x)` is an sc-isomorphism (Proposition 1.2.1 (preprint 1.16)'s remark,
  `IsSc1With.scOperator_deriv`) carrying the sc-splitting `E = T_xO ⊕ A` to
  `E' = T_yψ(O) ⊕ Dψ(x)A`, and `Dψ(x)E_x ⊆ E'_y` by the one-sided sign argument
  (`IsSc1With.mapsTo_minimalSubspace`).

## What the text leaves implicit

The text never states that tameness is invariant under sc-diffeomorphisms; Definition 2.5.2 (preprint 2.34) (2)
is formulated with the sc-complement `A ⊆ E_x` of `T_xO`, and the transport needs `Dψ(x)` to be an
sc-isomorphism (true at smooth points only) and to map `E_x` into `E'_{ψ(x)}` (the sign argument
of Lemma 2.4.9 (preprint 2.29)), both of which are in the Lean proof.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

variable {E E' : ScBanach}

/-! ### Sc-splittings are carried by sc-isomorphisms -/

section Splitting

variable {D : E 0 →L[ℝ] E' 0} {D' : E' 0 →L[ℝ] E 0}

/-- The level-`m` map of an sc-operator `D` with an sc-operator inverse `D'`, as a continuous
linear equivalence `E_m ≃ E'_m`. -/
def scIsoLevel (hD : IsScOperator D) (hD' : IsScOperator D') (hD'D : ∀ v, D' (D v) = v)
    (hDD' : ∀ w, D (D' w) = w) (m : ℕ) : E m ≃L[ℝ] E' m :=
  ContinuousLinearEquiv.equivOfInverse (hD m).choose (hD' m).choose
    (fun x => E.toBase_injective m (by rw [(hD' m).choose_spec, (hD m).choose_spec, hD'D]))
    (fun y => E'.toBase_injective m (by rw [(hD m).choose_spec, (hD' m).choose_spec, hDD']))

lemma toBase_scIsoLevel (hD : IsScOperator D) (hD' : IsScOperator D') (hD'D : ∀ v, D' (D v) = v)
    (hDD' : ∀ w, D (D' w) = w) (m : ℕ) (x : E m) :
    E'.toBase m (scIsoLevel hD hD' hD'D hDD' m x) = D (E.toBase m x) :=
  (hD m).choose_spec x

lemma toBase_scIsoLevel_symm (hD : IsScOperator D) (hD' : IsScOperator D')
    (hD'D : ∀ v, D' (D v) = v) (hDD' : ∀ w, D (D' w) = w) (m : ℕ) (y : E' m) :
    E.toBase m ((scIsoLevel hD hD' hD'D hDD' m).symm y) = D' (E'.toBase m y) :=
  (hD' m).choose_spec y

/-- The level-`m` map of an sc-isomorphism carries `A_m = A ∩ E_m` onto `(DA)_m`. -/
lemma levelSub_map_eq (hD : IsScOperator D) (hD' : IsScOperator D') (hD'D : ∀ v, D' (D v) = v)
    (hDD' : ∀ w, D (D' w) = w) (A : Submodule ℝ (E 0)) (m : ℕ) :
    E'.levelSub (A.map (D : E 0 →ₗ[ℝ] E' 0)) m =
      (E.levelSub A m).map (scIsoLevel hD hD' hD'D hDD' m : E m →ₗ[ℝ] E' m) := by
  ext y
  rw [ScBanach.mem_levelSub, Submodule.mem_map, Submodule.mem_map]
  constructor
  · rintro ⟨a, ha, hay⟩
    refine ⟨(scIsoLevel hD hD' hD'D hDD' m).symm y, ?_, (scIsoLevel hD hD' hD'D hDD' m).apply_symm_apply y⟩
    rw [ScBanach.mem_levelSub, toBase_scIsoLevel_symm, ← hay]
    change D' (D a) ∈ A
    rw [hD'D]; exact ha
  · rintro ⟨x, hx, rfl⟩
    refine ⟨E.toBase m x, hx, ?_⟩
    change D (E.toBase m x) = E'.toBase m (scIsoLevel hD hD' hD'D hDD' m x)
    rw [toBase_scIsoLevel]

/-- Smooth points are carried to smooth points by the level maps of an sc-operator. -/
lemma mem_smoothLvl_of_isScOperator (hD : IsScOperator D) {m : ℕ} {x : E m}
    (hx : x ∈ E.smoothLvl m) {y : E' m} (hy : E'.toBase m y = D (E.toBase m x)) :
    y ∈ E'.smoothLvl m := by
  rw [ScScale.mem_smoothLvl_iff] at hx ⊢
  intro j
  obtain ⟨z, hz⟩ := hx j
  obtain ⟨Dj, hDj⟩ := hD j
  exact ⟨Dj z, by rw [hDj, hz, hy]⟩

/-- **Sc-subspaces are carried by sc-isomorphisms**: if `A` is an sc-subspace of `E` and `D` is an
sc-operator with an sc-operator inverse `D'`, then `DA` is an sc-subspace of `E'`. -/
theorem IsScSubspace.map (hD : IsScOperator D) (hD' : IsScOperator D') (hD'D : ∀ v, D' (D v) = v)
    (hDD' : ∀ w, D (D' w) = w) {A : Submodule ℝ (E 0)} (hA : E.IsScSubspace A) :
    E'.IsScSubspace (A.map (D : E 0 →ₗ[ℝ] E' 0)) := by
  refine ⟨?_, fun m => ?_⟩
  · have heq : (A.map (D : E 0 →ₗ[ℝ] E' 0) : Set (E' 0)) = D' ⁻¹' (A : Set (E 0)) := by
      ext w
      rw [Submodule.map_coe, mem_preimage]
      constructor
      · rintro ⟨a, ha, rfl⟩
        change D' (D a) ∈ A
        rw [hD'D]; exact ha
      · intro hw
        exact ⟨D' w, hw, hDD' w⟩
    rw [heq]
    exact hA.1.preimage D'.continuous
  · intro y hy
    rw [levelSub_map_eq hD hD' hD'D hDD'] at hy ⊢
    set em := scIsoLevel hD hD' hD'D hDD' m with hem
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    have hxcl := hA.2 m hx
    have h1 : em x ∈ closure (em '' (E.levelSub A m ∩ E.smoothLvl m)) :=
      image_closure_subset_closure_image em.continuous ⟨x, hxcl, rfl⟩
    refine closure_mono ?_ h1
    rintro _ ⟨z, ⟨hzA, hzs⟩, rfl⟩
    refine ⟨Submodule.mem_map.2 ⟨z, hzA, rfl⟩, ?_⟩
    exact mem_smoothLvl_of_isScOperator hD hzs (toBase_scIsoLevel hD hD' hD'D hDD' m z)

/-- **Sc-splittings are carried by sc-isomorphisms**: `E = F ⊕ A` an sc-splitting gives the
sc-splitting `E' = DF ⊕ DA`. -/
theorem IsScSplitting.map (hD : IsScOperator D) (hD' : IsScOperator D') (hD'D : ∀ v, D' (D v) = v)
    (hDD' : ∀ w, D (D' w) = w) {F A : Submodule ℝ (E 0)} (h : E.IsScSplitting F A) :
    E'.IsScSplitting (F.map (D : E 0 →ₗ[ℝ] E' 0)) (A.map (D : E 0 →ₗ[ℝ] E' 0)) := by
  refine ⟨IsScSubspace.map hD hD' hD'D hDD' h.1, IsScSubspace.map hD hD' hD'D hDD' h.2.1,
    fun m => ?_⟩
  rw [levelSub_map_eq hD hD' hD'D hDD', levelSub_map_eq hD hD' hD'D hDD']
  set em := scIsoLevel hD hD' hD'D hDD' m with hem
  have hc := h.2.2 m
  refine IsCompl.of_eq ?_ ?_
  · rw [← Submodule.map_inf _ em.injective, hc.inf_eq_bot, Submodule.map_bot]
  · rw [← Submodule.map_sup, hc.sup_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact em.surjective

end Splitting

/-! ### The transported retraction `ψ ∘ r ∘ ψ⁻¹` -/

section Transport

variable {C : Set (E 0)} {C' : Set (E' 0)} {U : Set (E 0)} {U' : Set (E' 0)} {ψ : E 0 → E' 0}
  {ψ' : E' 0 → E 0}

/-- The data of an **sc-diffeomorphism `ψ : U → U'` between relatively open subsets of partial
quadrants**, with inverse `ψ'`. -/
structure IsScDiffeoQuadrant (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U')
    (ψ : E 0 → E' 0) (ψ' : E' 0 → E 0) : Prop where
  isScSmooth : IsScSmooth U ψ
  isScSmooth_inv : IsScSmooth U' ψ'
  mapsTo : MapsTo ψ U U'
  mapsTo_inv : MapsTo ψ' U' U
  left_inv : ∀ u ∈ U, ψ' (ψ u) = u
  right_inv : ∀ u' ∈ U', ψ (ψ' u') = u'

variable {hU : IsRelOpenInQuadrant E C U} {hU' : IsRelOpenInQuadrant E' C' U'}

namespace IsScDiffeoQuadrant

variable (h : IsScDiffeoQuadrant hU hU' ψ ψ')
include h

lemma symm : IsScDiffeoQuadrant hU' hU ψ' ψ :=
  ⟨h.isScSmooth_inv, h.isScSmooth, h.mapsTo_inv, h.mapsTo, h.right_inv, h.left_inv⟩

/-- **The transported retraction `r' = ψ ∘ r ∘ ψ⁻¹ : U' → U'`** of an sc-smooth retraction
`r : U → U`. -/
def transport (R : ScRetraction E C) (hRU : R.U = U) : ScRetraction E' C' where
  U := U'
  toFun := ψ ∘ R ∘ ψ'
  relOpen := hU'
  mapsTo := fun u' hu' => h.mapsTo (hRU ▸ R.mapsTo (hRU ▸ h.mapsTo_inv hu'))
  isScSmooth := by
    have hRsm : IsScSmooth U R := hRU ▸ R.isScSmooth
    have h1 : IsScSmooth U' (R ∘ ψ') :=
      IsScSmooth.comp hU'.isScDomain hU.isScDomain hRsm h.isScSmooth_inv h.mapsTo_inv
    exact IsScSmooth.comp hU'.isScDomain hU.isScDomain h.isScSmooth h1
      fun u' hu' => hRU ▸ R.mapsTo (hRU ▸ h.mapsTo_inv hu')
  idem := fun u' hu' => by
    have hu : ψ' u' ∈ R.U := hRU ▸ h.mapsTo_inv hu'
    have hRu : R (ψ' u') ∈ R.U := R.mapsTo hu
    simp only [Function.comp_apply]
    rw [h.left_inv _ (hRU ▸ hRu), R.idem _ hu]

lemma transport_apply (R : ScRetraction E C) (hRU : R.U = U) (u' : E' 0) :
    h.transport R hRU u' = ψ (R (ψ' u')) := rfl

lemma transport_U (R : ScRetraction E C) (hRU : R.U = U) : (h.transport R hRU).U = U' := rfl

/-- The retract of `ψ ∘ r ∘ ψ⁻¹` is `ψ(O)`. -/
theorem transport_retract (R : ScRetraction E C) (hRU : R.U = U) :
    (h.transport R hRU).retract = ψ '' R.retract := by
  ext y
  constructor
  · rintro ⟨u', hu', rfl⟩
    exact ⟨R (ψ' u'), R.apply_mem_retract (hRU ▸ h.mapsTo_inv hu'), rfl⟩
  · rintro ⟨z, hz, rfl⟩
    have hzU : z ∈ U := hRU ▸ R.retract_subset hz
    refine ⟨ψ z, h.mapsTo hzU, ?_⟩
    show ψ (R (ψ' (ψ z))) = ψ z
    rw [h.left_inv z hzU, R.apply_eq_self_of_mem_retract hz]

/-- **The degeneracy index is preserved by `ψ`** (Theorem 1.3.5 (preprint 1.25)). -/
theorem degIndex_eq {u : E 0} (hu : u ∈ U) : degIndex E' C' (ψ u) = degIndex E C u :=
  (theorem_1_3_5 hU hU' h.isScSmooth.isSc1 h.isScSmooth_inv.isSc1 h.mapsTo h.mapsTo_inv h.left_inv
    h.right_inv hu).symm

/-- `Dψ'(ψ(x)) ∘ Dψ(x) = id` on level `0`, for `x ∈ U₁`. -/
theorem deriv_inv_deriv {x : E 1} (hx : x ∈ E.lvlSet U 1) (v : E 0) :
    scDeriv U' ψ' (levelMap ψ 1 x) (scDeriv U ψ x v) = v :=
  scDeriv_comp_eq_self hU hU' h.isScSmooth.isSc1 h.isScSmooth_inv.isSc1 h.mapsTo h.left_inv hx v

/-- `Dψ(ψ'(y)) ∘ Dψ'(y) = id` on level `0`, for `y ∈ U'₁`. -/
theorem deriv_deriv_inv {y : E' 1} (hy : y ∈ E'.lvlSet U' 1) (w : E' 0) :
    scDeriv U ψ (levelMap ψ' 1 y) (scDeriv U' ψ' y w) = w :=
  scDeriv_comp_eq_self hU' hU h.isScSmooth_inv.isSc1 h.isScSmooth.isSc1 h.mapsTo_inv h.right_inv hy w

/-- **The derivative of the transported retraction**: for `y ∈ U'₁` with `x = ψ'₁(y)`,
`Dr'(y) = Dψ(x) ∘ Dr(x) ∘ Dψ'(y)` if `ψ'(y) ∈ O`. -/
theorem scDeriv_transport (R : ScRetraction E C) (hRU : R.U = U) {y : E' 1}
    (hy : y ∈ E'.lvlSet U' 1) (hyO : ψ' (E'.toBase 1 y) ∈ R.retract) (w : E' 0) :
    scDeriv U' (h.transport R hRU) y w =
      scDeriv U ψ (levelMap ψ' 1 y) (scDeriv R.U R (levelMap ψ' 1 y) (scDeriv U' ψ' y w)) := by
  have hRsm : IsScSmooth U R := hRU ▸ R.isScSmooth
  have hRsc1 : IsSc1 R.U R := R.isSc1
  have hxU : levelMap ψ' 1 y ∈ E.lvlSet U 1 :=
    h.isScSmooth_inv.isSc1.isSc0.levelMap_mapsTo h.mapsTo_inv 1 hy
  have hlev : levelMap (R ∘ ψ') 1 y = levelMap ψ' 1 y := by
    apply levelMap_eq_of_toBase_eq
    rw [h.isScSmooth_inv.isSc1.isSc0.toBase_levelMap hy, Function.comp_apply,
      R.apply_eq_self_of_mem_retract hyO]
  have hRψ' : IsScSmooth U' (R ∘ ψ') :=
    IsScSmooth.comp hU'.isScDomain hU.isScDomain hRsm h.isScSmooth_inv h.mapsTo_inv
  have hmaps : MapsTo (R ∘ ψ') U' U := fun u' hu' => hRU ▸ R.mapsTo (hRU ▸ h.mapsTo_inv hu')
  show scDeriv U' (ψ ∘ (R ∘ ψ')) y w = _
  rw [← scDeriv_comp_apply_of_isScDomain hU'.isScDomain hU.isScDomain hRψ'.isSc1
    h.isScSmooth.isSc1 hmaps hy w, hlev,
    scDeriv_comp_apply_of_isScDomain hU'.isScDomain R.isScDomain h.isScSmooth_inv.isSc1 hRsc1
    (hRU ▸ h.mapsTo_inv) hy w]

/-- **Tameness is carried by `ψ`** (for a presentation `T'` of `C'`): if `r : U → U` is tame then
so is `r' = ψ ∘ r ∘ ψ⁻¹ : U' → U'`.  Condition (1) of Definition 2.5.2 (preprint 2.34) is Theorem 1.3.5 (preprint 1.25) (`ψ`
preserves the degeneracy index); for (2), at a smooth point `y = ψ(x)` of `ψ(O)` the derivative
`Dψ(x)` is an sc-isomorphism carrying the sc-splitting `E = T_xO ⊕ A` to
`E' = T_yψ(O) ⊕ Dψ(x)A` (`Dr'(y) = Dψ(x) Dr(x) Dψ'(y)`), and `Dψ(x)E_x ⊆ E'_y` by the one-sided
sign argument (`IsSc1With.mapsTo_minimalSubspace`). -/
theorem isTameWith_transport (R : ScRetraction E C) (hRU : R.U = U) {n n' : ℕ} {W W' : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod W')) (hT' : C' = T' 0 ⁻¹' quadrant n' W' 0)
    (hR : R.IsTameWith T) : (h.transport R hRU).IsTameWith T' where
  degIndex_apply u' hu' := by
    rw [transport_apply, h.degIndex_eq (hRU ▸ R.mapsTo (hRU ▸ h.mapsTo_inv hu')),
      hR.degIndex_apply _ (hRU ▸ h.mapsTo_inv hu'), ← h.degIndex_eq (h.mapsTo_inv hu'),
      h.right_inv u' hu']
  exists_complement y hy hs := by
    have hU'C : U' ⊆ C' := by obtain ⟨O, -, rfl⟩ := hU'.relOpen; exact inter_subset_right
    rw [ScBanach.mem_lvlSet, h.transport_retract] at hy
    have hyU' : y ∈ E'.lvlSet U' 1 := by
      rw [ScBanach.mem_lvlSet]
      obtain ⟨z, hz, hzy⟩ := hy
      rw [← hzy]; exact h.mapsTo (hRU ▸ R.retract_subset hz)
    obtain ⟨x, hxdef⟩ : ∃ x : E 1, x = levelMap ψ' 1 y := ⟨_, rfl⟩
    have hxbase : E.toBase 1 x = ψ' (E'.toBase 1 y) := by
      rw [hxdef]; exact h.isScSmooth_inv.isSc1.isSc0.toBase_levelMap hyU'
    have hxO : ψ' (E'.toBase 1 y) ∈ R.retract := by
      obtain ⟨z, hz, hzy⟩ := hy
      rw [← hzy, h.left_inv z (hRU ▸ R.retract_subset hz)]; exact hz
    have hxret : x ∈ E.lvlSet R.retract 1 := by rw [ScBanach.mem_lvlSet, hxbase]; exact hxO
    have hxU : x ∈ E.lvlSet U 1 := hRU ▸ R.lvlSet_retract_subset 1 hxret
    have hxs : x ∈ E.smoothLvl 1 := by
      change E.toBase 1 x ∈ E.smooth
      rw [hxbase]
      exact h.isScSmooth_inv.isSc1.isSc0.mem_smooth hyU' hs
    obtain ⟨A, hA, hAle⟩ := hR.exists_complement x hxret hxs
    -- the derivatives `Dψ(x)`, `Dψ'(y)`, inverse to each other
    have hlevψ : levelMap ψ 1 x = y := by
      apply levelMap_eq_of_toBase_eq
      rw [hxbase, h.right_inv _ hyU']
    have hD'D : ∀ v, scDeriv U' ψ' y (scDeriv U ψ x v) = v := fun v => by
      have := h.deriv_inv_deriv hxU v; rwa [hlevψ] at this
    have hDD' : ∀ w, scDeriv U ψ x (scDeriv U' ψ' y w) = w := fun w => by
      have := h.deriv_deriv_inv hyU' w; rwa [← hxdef] at this
    have hDop : IsScOperator (scDeriv U ψ x) :=
      h.isScSmooth.isSc1.isSc1With_scDeriv.scOperator_deriv hxU hxs
    have hD'op : IsScOperator (scDeriv U' ψ' y) :=
      h.isScSmooth_inv.isSc1.isSc1With_scDeriv.scOperator_deriv hyU' hs
    have hDr : ∀ w, scDeriv U' (h.transport R hRU) y w =
        scDeriv U ψ x (scDeriv R.U R x (scDeriv U' ψ' y w)) := fun w => by
      rw [h.scDeriv_transport R hRU hyU' hxO, ← hxdef]
    refine ⟨A.map (scDeriv U ψ x : E 0 →ₗ[ℝ] E' 0), ?_, ?_⟩
    · -- `T_yψ(O) = Dψ(x)(T_xO)`
      have hrange : LinearMap.range (scDeriv U' (h.transport R hRU) y : E' 0 →ₗ[ℝ] E' 0) =
          (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)).map
            (scDeriv U ψ x : E 0 →ₗ[ℝ] E' 0) := by
        ext w
        rw [LinearMap.mem_range, Submodule.mem_map]
        constructor
        · rintro ⟨v, rfl⟩
          exact ⟨scDeriv R.U R x (scDeriv U' ψ' y v), ⟨scDeriv U' ψ' y v, rfl⟩, (hDr v).symm⟩
        · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
          refine ⟨scDeriv U ψ x v, ?_⟩
          rw [ContinuousLinearMap.coe_coe, hDr, hD'D]
          rfl
      change E'.IsScSplitting
        (LinearMap.range (scDeriv U' (h.transport R hRU) y : E' 0 →ₗ[ℝ] E' 0))
        (A.map (scDeriv U ψ x : E 0 →ₗ[ℝ] E' 0))
      rw [hrange]
      exact IsScSplitting.map hDop hD'op hD'D hDD' hA
    · -- `Dψ(x)A ⊆ E'_y`
      rintro _ ⟨a, ha, rfl⟩
      have h1 := IsSc1With.mapsTo_minimalSubspace T hT T' hT' hU
        h.isScSmooth.isSc1.isSc1With_scDeriv (fun u hu => hU'C (h.mapsTo hu)) hxU (hAle ha)
      rwa [hxbase, h.right_inv _ hyU'] at h1

/-- **Tameness is carried by `ψ`**: the transported retraction of a tame retraction is tame. -/
theorem isTame_transport (R : ScRetraction E C) (hRU : R.U = U) (hR : R.IsTame) :
    (h.transport R hRU).IsTame := by
  intro n' W' T' hT'
  obtain ⟨n, W, T, hT⟩ := hU.isPartialQuadrant
  exact h.isTameWith_transport R hRU T hT T' hT' (hR n W T hT)

/-- **The image of a tame retract under an sc-diffeomorphism is a tame retract**: for a tame
retraction `r : U → U` onto `O` and an sc-diffeomorphism `ψ : U → U'`, `(ψ(O), C', E')` is a
tame retract (with the retraction `ψ ∘ r ∘ ψ⁻¹`). -/
theorem isTameRetract_image (R : ScRetraction E C) (hRU : R.U = U) (hR : R.IsTame) :
    IsTameRetract E' C' (ψ '' R.retract) :=
  ⟨h.transport R hRU, h.transport_retract R hRU, h.isTame_transport R hRU hR⟩

end IsScDiffeoQuadrant

end Transport

end Polyfold
