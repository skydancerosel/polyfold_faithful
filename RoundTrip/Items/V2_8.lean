import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_8

/-! Round trip for V2_8 (the tangent functor on retracts, after Theorem 2.8 and Definition 2.9).

`A` is the conjunction of the types of `Polyfold.IsPartialQuadrant.tangentSet`,
`Polyfold.IsRelOpenInQuadrant.tangentSet`, `Polyfold.ScRetraction.tangentRetraction_retract`,
`Polyfold.IsScRetract.tangentSet`, `Polyfold.IsScSmoothRetractMap.tangent`,
`Polyfold.retractTangentMap_id`, `Polyfold.retractTangent_inter_isOpen` and
`Polyfold.retractTangentMap_inter_isOpen` (no universe parameters: `ScBanach` lives in `Type`).
`ScRetraction.tangentRetraction` and `LocalModel.tangent` are definitions (vocabulary).

`A → B`: B's `TEB`, `TCB`, `TUB` are the project's `E.tangent`, `E.tangentSet C`,
`E.tangentSet U` definitionally, and B's explicit `TOB R` is `Tr(TU) = retractTangent E C O`
(glue + `retractTangent_eq`).  (1) is `IsScRetract.tangentSet`; (2) is
`IsScSmoothRetractMap.tangent` (B's existential hypothesis converted by
`isScSmoothRetractMap_iff_exists`, and `Tf` identified with `T(f ∘ r)` on `TO` by
`retractTangentMap_eqOn`), the formula `Tf(x, h) = (f(x), D(f∘r)(x)h)` being proved directly;
(3) `T(g ∘ f) = Tg ∘ Tf` is NOT in A: it is Theorem 2.8 (`retractTangentMap_comp`, item V2_7, not
banned here); (4) is `retractTangentMap_id`; (5) uses `IsRelOpenInQuadrant.tangentSet` for `TU`
relatively open in `TC`, the rest (sc-smoothness, idempotence, bundle form) being project lemmas
about `Tr` that are not item theorems.

`B → A`: `IsRelOpenInQuadrant.tangentSet` and `IsPartialQuadrant.tangentSet` come from B (5)
applied to identity retractions; `IsScRetract.tangentSet` from B (1); `IsScSmoothRetractMap.tangent`
from B (2) (the morphism clause, with `ρ`-sc-smoothness for every retraction `ρ` onto `TO`);
`retractTangentMap_id` from B (4).  `tangentRetraction_retract` is the definition of
`tangentRetraction` plus `retractTangent_eq`, and the two locality statements
`retractTangent_inter_isOpen`, `retractTangentMap_inter_isOpen` (`T(O ∩ W) = TO ∩ (W₁ ⊕ E)` and
the corresponding statement for `Tf`) are not in the text's sentence nor in B; they are re-proved
directly (the project's argument, through `ScRetraction.restrict`), without B. -/

namespace RoundTrip.V2_8
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.IsPartialQuadrant.tangentSet) ∧
    (type_of% @Polyfold.IsRelOpenInQuadrant.tangentSet) ∧
    (type_of% @Polyfold.ScRetraction.tangentRetraction_retract) ∧
    (type_of% @Polyfold.IsScRetract.tangentSet) ∧
    (type_of% @Polyfold.IsScSmoothRetractMap.tangent) ∧
    (type_of% @Polyfold.retractTangentMap_id) ∧
    (type_of% @Polyfold.retractTangent_inter_isOpen) ∧
    (type_of% @Polyfold.retractTangentMap_inter_isOpen)

theorem A_holds : A :=
  ⟨@Polyfold.IsPartialQuadrant.tangentSet, @Polyfold.IsRelOpenInQuadrant.tangentSet,
    @Polyfold.ScRetraction.tangentRetraction_retract, @Polyfold.IsScRetract.tangentSet,
    @Polyfold.IsScSmoothRetractMap.tangent, @Polyfold.retractTangentMap_id,
    @Polyfold.retractTangent_inter_isOpen, @Polyfold.retractTangentMap_inter_isOpen⟩

/-! ### Glue -/

/-- `Tr(TU)` is B's explicit set `{(r(x), Dr(x)h)}`. -/
theorem tangent_eq_TOB {E : ScBanach} {C : Set (E 0)} (R : ScRetraction E C) :
    R.tangent = TOB R := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.1, hq, q.2, R.isSc1.isSc0.toBase_levelMap (m := 1) hq, rfl⟩
  · rintro ⟨x, hx, h, h1, h2⟩
    exact ⟨(x, h), hx, Prod.ext (levelMap_eq_of_toBase_eq h1) h2.symm⟩

theorem retractTangent_eq_TOB {E : ScBanach} {C O : Set (E 0)} (R : ScRetraction E C)
    (hR : R.retract = O) : retractTangent E C O = TOB R := by
  subst hR
  rw [retractTangent_eq, tangent_eq_TOB]

variable {E E' : ScBanach} {C O : Set (E 0)} {C' O' : Set (E' 0)} {f : E 0 → E' 0}

theorem toProj (hO : IsScRetract E C O) (h : IsScSmoothRetractMapB E C O E' O' f) :
    IsScSmoothRetractMap E C O E' C' O' f :=
  (isScSmoothRetractMap_iff_exists hO).2 h

theorem toB (hf : IsScSmoothRetractMap E C O E' C' O' f) (R : ScRetraction E C)
    (hR : R.retract = O) : IsScSmoothRetractMapB E C O E' O' f :=
  ⟨hf.mapsTo, R, hR, hf.comp_isScSmooth R hR⟩

/-- `Tf = T(f ∘ r)` on `TOB R`. -/
theorem eqOn_TOB (hf : IsScSmoothRetractMap E C O E' C' O' f) (R : ScRetraction E C)
    (hR : R.retract = O) :
    EqOn (retractTangentMap E C O f) (tangentMap R.U (f ∘ R.toFun)) (TOB R) := by
  rw [← retractTangent_eq_TOB R hR]
  exact retractTangentMap_eqOn hf R hR

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  rintro ⟨-, hRO, -, hRet, hTan, hId, -, -⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (1) `(TO, TC, TE)` is a retract
    intro E C O hO R hR
    rw [← retractTangent_eq_TOB R hR]
    exact hRet hO
  · -- (2) `Tf` is a morphism, and its formula
    intro E E' C O C' O' f hO hO' hfB R R' hR hR'
    have hf : IsScSmoothRetractMap E C O E' C' O' f := toProj hO hfB
    have hT := hTan hf hO hO'
    have heq := eqOn_TOB hf R hR
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro p hp
      rw [← heq hp, ← retractTangent_eq_TOB R' hR']
      exact hT.mapsTo (by rw [retractTangent_eq_TOB R hR]; exact hp)
    · intro ρ hρ
      have hρ' : ρ.retract = retractTangent E C O := by rw [hρ, retractTangent_eq_TOB R hR]
      refine (hT.comp_isScSmooth ρ hρ').congr ρ.isScDomain fun q hq => ?_
      have : ρ.toFun q ∈ TOB R := hρ ▸ ρ.apply_mem_retract hq
      exact heq this
    · intro p hp
      have hpT : p ∈ R.tangent := by rw [tangent_eq_TOB]; exact hp
      have hp1 : p.1 ∈ E.lvlSet R.retract 1 := R.fst_mem_of_mem_tangent hpT
      have hpU : p.1 ∈ E.lvlSet R.U 1 := R.lvlSet_retract_subset 1 hp1
      refine ⟨?_, rfl⟩
      have := (hf.comp_isScSmooth R hR).isSc1.isSc0.toBase_levelMap (m := 1) hpU
      change E'.toBase 1 (levelMap (f ∘ R.toFun) 1 p.1) = _
      rw [this, Function.comp_apply, R.apply_eq_self_of_mem_retract (x := E.toBase 1 p.1) hp1]
  · -- (3) `T(g ∘ f) = Tg ∘ Tf`: Theorem 2.8 (not part of A)
    intro E E' E'' C O C' O' C'' O'' f g hO hO' _ hfB hgB R R' hR hR' p hp
    have hf : IsScSmoothRetractMap E C O E' C' O' f := toProj hO hfB
    have hg : IsScSmoothRetractMap E' C' O' E'' C'' O'' g := toProj hO' hgB
    have hgf := hg.comp hf hO'
    have hpO : p ∈ retractTangent E C O := by rw [retractTangent_eq_TOB R hR]; exact hp
    have hTf : retractTangentMap E C O f p ∈ retractTangent E' C' O' :=
      hf.tangentMap_mapsTo hO hO' hpO
    rw [← eqOn_TOB hgf R hR hp, retractTangentMap_comp hg hf hO hO' hpO, Function.comp_apply,
      Function.comp_apply, retractTangentMap_eqOn hg R' hR' hTf, eqOn_TOB hf R hR hp]
  · -- (4) `T(1) = 1`
    intro E C O hO R hR p hp
    have hpO : p ∈ retractTangent E C O := by rw [retractTangent_eq_TOB R hR]; exact hp
    rw [← eqOn_TOB (isScSmoothRetractMap_id (C := C) O) R hR hp]
    exact hId hO (f := id) (fun _ _ => rfl) hpO
  · -- (5) `Tr` is a bundle retraction
    intro E C R
    refine ⟨⟨hRO R.relOpen, R.tangentMap_mapsTo, LocalModel.tangent_isScSmooth R,
      fun p hp => R.tangentMap_tangentMap hp⟩, ?_⟩
    intro p hp
    exact ⟨R.isSc1.isSc0.toBase_levelMap (m := 1) (x := p.1) hp, scDeriv R.U R.toFun p.1,
      fun h => rfl⟩

/-! ### `B → A` -/

/-- `T(O ∩ W) = TO ∩ (W₁ ⊕ E)`, re-proved (the project's argument). -/
theorem retractTangent_inter_isOpen' {E : ScBanach} {C O : Set (E 0)} (hO : IsScRetract E C O)
    {W : Set (E 0)} (hW : IsOpen W) :
    retractTangent E C (O ∩ W) = retractTangent E C O ∩ (E.lvlSet W 1 ×ˢ univ) := by
  obtain ⟨R, rfl⟩ := hO
  rw [← R.restrict_retract hW, retractTangent_eq, retractTangent_eq]
  have hsub : (R.restrict hW).U ⊆ R.U := inter_subset_left
  have heq := R.isSc1.tangentMap_eqOn_of_subset (R.restrict hW).isScDomain hsub
  ext p
  rw [(R.restrict hW).mem_tangent_iff, mem_inter_iff, R.mem_tangent_iff]
  constructor
  · rintro ⟨hp, hfix⟩
    have hpU : p ∈ E.tangentSet R.U := E.tangentSet_mono hsub hp
    refine ⟨⟨hpU, ?_⟩, ?_, mem_univ _⟩
    · have hfix' : tangentMap (R.restrict hW).U R p = p := hfix
      rw [← heq hp]; exact hfix'
    · have : p.1 ∈ E.lvlSet (R.U ∩ R ⁻¹' W) 1 := hp
      rw [ScBanach.lvlSet_inter] at this
      have h1 : R (E.toBase 1 p.1) ∈ W := this.2
      have h2 : levelMap R 1 p.1 = p.1 := congrArg Prod.fst hfix
      have h3 : E.toBase 1 (levelMap R 1 p.1) = R (E.toBase 1 p.1) :=
        R.isSc1.isSc0.toBase_levelMap this.1
      rw [h2] at h3
      change E.toBase 1 p.1 ∈ W
      rw [h3]; exact h1
  · rintro ⟨⟨hpU, hfix⟩, hpW, -⟩
    have h2 : levelMap R 1 p.1 = p.1 := congrArg Prod.fst hfix
    have h3 : E.toBase 1 (levelMap R 1 p.1) = R (E.toBase 1 p.1) :=
      R.isSc1.isSc0.toBase_levelMap hpU
    rw [h2] at h3
    have hp : p ∈ E.tangentSet (R.restrict hW).U := by
      change p.1 ∈ E.lvlSet (R.U ∩ R ⁻¹' W) 1
      rw [ScBanach.lvlSet_inter]
      refine ⟨hpU, ?_⟩
      change R (E.toBase 1 p.1) ∈ W
      rw [← h3]; exact hpW
    refine ⟨hp, ?_⟩
    change tangentMap (R.restrict hW).U R p = p
    rw [heq hp]; exact hfix

/-- `Tf` computed on `O ∩ W` is `Tf` computed on `O`, re-proved (the project's argument). -/
theorem retractTangentMap_inter_isOpen' {E E' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)}
    {O : Set (E 0)} {O' : Set (E' 0)} {f : E 0 → E' 0}
    (hf : IsScSmoothRetractMap E C O E' C' O' f) (hO : IsScRetract E C O) {W : Set (E 0)}
    (hW : IsOpen W) :
    EqOn (retractTangentMap E C (O ∩ W) f) (retractTangentMap E C O f)
      (retractTangent E C (O ∩ W)) := by
  obtain ⟨R, rfl⟩ := hO
  intro p hp
  have hp' : p ∈ retractTangent E C R.retract := by
    rw [retractTangent_inter_isOpen' R.isScRetract hW] at hp; exact hp.1
  rw [retractTangentMap_eqOn hf R rfl hp',
    retractTangentMap_eqOn (hf.restrict R.isScRetract) (R.restrict hW) (R.restrict_retract hW) hp]
  have hsub : (R.restrict hW).U ⊆ R.U := inter_subset_left
  have hpU : p ∈ E.tangentSet (R.restrict hW).U := by
    rw [← R.restrict_retract hW, retractTangent_eq] at hp
    exact (R.restrict hW).tangent_subset hp
  exact (hf.comp_isScSmooth R rfl).isSc1.tangentMap_eqOn_of_subset (R.restrict hW).isScDomain hsub hpU

theorem B_to_A : B → A := by
  rintro ⟨h1, h2, -, h4, h5⟩
  have hRO : type_of% @Polyfold.IsRelOpenInQuadrant.tangentSet := by
    intro E C U hU
    exact (h5 E C (ScRetraction.id hU)).1.1
  have hPQ : type_of% @Polyfold.IsPartialQuadrant.tangentSet := by
    intro E C hC
    exact (hRO (U := C) ⟨hC, univ, isOpen_univ, (univ_inter C).symm⟩).isPartialQuadrant
  have hTR : type_of% @Polyfold.ScRetraction.tangentRetraction_retract := by
    intro E C R
    rw [retractTangent_eq]; rfl
  have hRet : type_of% @Polyfold.IsScRetract.tangentSet := by
    intro E C O hO
    obtain ⟨R, hR⟩ := hO
    rw [retractTangent_eq_TOB R hR]
    exact h1 E C O ⟨R, hR⟩ R hR
  have hTan : type_of% @Polyfold.IsScSmoothRetractMap.tangent := by
    intro E E' C C' O O' f hf hO hO'
    obtain ⟨R, hR⟩ := hO
    obtain ⟨R', hR'⟩ := hO'
    have hB := h2 E E' C O C' O' f ⟨R, hR⟩ ⟨R', hR'⟩ (toB hf R hR) R R' hR hR'
    have heq := eqOn_TOB hf R hR
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [retractTangent_eq_TOB R hR] at hp
      rw [heq hp, retractTangent_eq_TOB R' hR']
      exact hB.1.1 hp
    · intro ρ hρ
      have hρ' : ρ.retract = TOB R := by rw [hρ, retractTangent_eq_TOB R hR]
      refine (hB.1.2 ρ hρ').congr ρ.isScDomain fun q hq => ?_
      exact (heq (hρ' ▸ ρ.apply_mem_retract hq)).symm
  have hId : type_of% @Polyfold.retractTangentMap_id := by
    intro E C O hO f hf p hp
    obtain ⟨R, hR⟩ := hO
    have hfs : IsScSmoothRetractMap E C O E C O f := (isScSmoothRetractMap_id O).congr hf.symm
    rw [retractTangent_eq_TOB R hR] at hp
    rw [eqOn_TOB hfs R hR hp]
    have hpU : p ∈ E.tangentSet R.U := by
      rw [← tangent_eq_TOB] at hp; exact R.tangent_subset hp
    have hcongr : EqOn (f ∘ R.toFun) (id ∘ R.toFun) R.U := fun y hy =>
      hf (hR ▸ R.apply_mem_retract hy)
    rw [(hfs.comp_isScSmooth R hR).isSc1.tangentMap_congr R.isScDomain hcongr hpU]
    exact h4 E C O ⟨R, hR⟩ R hR hp
  exact ⟨hPQ, hRO, hTR, hRet, hTan, hId, @retractTangent_inter_isOpen',
    @retractTangentMap_inter_isOpen'⟩

#rt_check_soft RoundTrip.V2_8.A_to_B [Polyfold.IsPartialQuadrant.tangentSet,
  Polyfold.IsRelOpenInQuadrant.tangentSet, Polyfold.ScRetraction.tangentRetraction_retract,
  Polyfold.IsScRetract.tangentSet, Polyfold.IsScSmoothRetractMap.tangent,
  Polyfold.retractTangentMap_id, Polyfold.retractTangent_inter_isOpen,
  Polyfold.retractTangentMap_inter_isOpen]
#rt_check_soft RoundTrip.V2_8.B_to_A [Polyfold.IsPartialQuadrant.tangentSet,
  Polyfold.IsRelOpenInQuadrant.tangentSet, Polyfold.ScRetraction.tangentRetraction_retract,
  Polyfold.IsScRetract.tangentSet, Polyfold.IsScSmoothRetractMap.tangent,
  Polyfold.retractTangentMap_id, Polyfold.retractTangent_inter_isOpen,
  Polyfold.retractTangentMap_inter_isOpen]
#rt_overlap RoundTrip.V2_8.B_to_A [Polyfold.IsPartialQuadrant.tangentSet,
  Polyfold.IsRelOpenInQuadrant.tangentSet, Polyfold.ScRetraction.tangentRetraction_retract,
  Polyfold.IsScRetract.tangentSet, Polyfold.IsScSmoothRetractMap.tangent,
  Polyfold.retractTangentMap_id, Polyfold.retractTangent_inter_isOpen,
  Polyfold.retractTangentMap_inter_isOpen]

end RoundTrip.V2_8
