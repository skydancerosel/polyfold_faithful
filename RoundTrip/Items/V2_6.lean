import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_6

/-! Round trip for V2_6 (Definition 2.7: sc-smooth maps between retracts and the tangent map).

`A` is the conjunction of the types of `Polyfold.isScSmoothRetractMap_iff_exists`,
`Polyfold.retractTangentMap_eqOn`, `Polyfold.IsScSmoothRetractMap.tangentMap_mapsTo`,
`Polyfold.retractTangentMap_apply`, `Polyfold.IsScSmoothRetractMap.continuousOn` and
`Polyfold.IsScSmoothRetractMap.mem_range_toBase` (no universe parameters: `ScBanach` lives in
`Type`).  `IsScSmoothRetractMap` and `retractTangentMap` are definitions (vocabulary).

`A → B`: B's "for one `r`" reading is `isScSmoothRetractMap_iff_exists`; with B's explicit
`TOB R` identified with `R.tangent` (glue below) and `retractTangent E C O = R.tangent`
(`retractTangent_eq`, not an item theorem), independence of `r`, `Tf(TO) ⊆ TO'` and
"`retractTangentMap` is `T(f ∘ r)` on `TO`" are `retractTangentMap_eqOn` and
`tangentMap_mapsTo`; the fibrewise linearity is the formula `T(f∘r)(o, h) = (f(o), D(f∘r)(o)h)`
plus `Tf(TO) ⊆ TO'`.

`B → A`: the nontrivial half of `isScSmoothRetractMap_iff_exists` (one `r` ⇒ every `r`,
Proposition 2.6 (1)) comes from B applied with the target retract `(E'₀, E'₀, E')`
(`isScRetract_univ`), since `IsScSmoothRetractMap` sees the target only through `f(O) ⊆ O'`;
`retractTangentMap_eqOn`, `tangentMap_mapsTo` and `retractTangentMap_apply` come from B's
clauses (iii) and (ii).  `IsScSmoothRetractMap.continuousOn` and `mem_range_toBase` (continuity
and level preservation of `f` on `O`) are not in the text's Definition 2.7 nor in B; they are
proved directly from the definitions, without B. -/

namespace RoundTrip.V2_6
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.isScSmoothRetractMap_iff_exists) ∧
    (type_of% @Polyfold.retractTangentMap_eqOn) ∧
    (type_of% @Polyfold.IsScSmoothRetractMap.tangentMap_mapsTo) ∧
    (type_of% @Polyfold.retractTangentMap_apply) ∧
    (type_of% @Polyfold.IsScSmoothRetractMap.continuousOn) ∧
    (type_of% @Polyfold.IsScSmoothRetractMap.mem_range_toBase)

theorem A_holds : A :=
  ⟨@Polyfold.isScSmoothRetractMap_iff_exists, @Polyfold.retractTangentMap_eqOn,
    @Polyfold.IsScSmoothRetractMap.tangentMap_mapsTo, @Polyfold.retractTangentMap_apply,
    @Polyfold.IsScSmoothRetractMap.continuousOn, @Polyfold.IsScSmoothRetractMap.mem_range_toBase⟩

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

theorem A_to_B : A → B := by
  rintro ⟨hiff, heqOn, hmaps, -, -, -⟩ E E' C O C' O' f hO hO'
  have hiff' : IsScSmoothRetractMap E C O E' C' O' f ↔ IsScSmoothRetractMapB E C O E' O' f :=
    hiff hO
  refine ⟨hiff', fun hB => ?_⟩
  have hf := hiff'.2 hB
  -- (iii) the project's `Tf` is `T(f ∘ r)` on `TO`
  have h3 : ∀ R : ScRetraction E C, R.retract = O →
      EqOn (retractTangentMap E C O f) (tangentMap R.U (f ∘ R.toFun)) (TOB R) := by
    intro R hR
    rw [← retractTangent_eq_TOB R hR]
    exact heqOn hf R hR
  -- (ii) `T(f ∘ r)` maps `TO` into `TO'`
  have h2 : ∀ (R : ScRetraction E C) (R' : ScRetraction E' C'), R.retract = O →
      R'.retract = O' → MapsTo (tangentMap R.U (f ∘ R.toFun)) (TOB R) (TOB R') := by
    intro R R' hR hR' p hp
    rw [← h3 R hR hp, ← retractTangent_eq_TOB R' hR']
    exact hmaps hf hO hO' (by rw [retractTangent_eq_TOB R hR]; exact hp)
  refine ⟨?_, h2, h3, ?_⟩
  · -- (i) independence of `r`
    intro R R' hR hR' p hp
    have hp' : p ∈ TOB R' := by
      rw [← retractTangent_eq_TOB R' hR', retractTangent_eq_TOB R hR]; exact hp
    rw [← h3 R hR hp, h3 R' hR' hp']
  · -- (iv) linear on fibres
    intro R R' hR hR' o₁ fo₁ ho hfo
    refine ⟨scDeriv R.U (f ∘ R.toFun) o₁, fun h hh => ?_⟩
    have hfix : R.toFun (E.toBase 1 o₁) = E.toBase 1 o₁ :=
      R.apply_eq_self_of_mem_retract (hR ▸ ho)
    have heq : tangentMap R.U (f ∘ R.toFun) (o₁, h) = (fo₁, scDeriv R.U (f ∘ R.toFun) o₁ h) := by
      change (levelMap (f ∘ R.toFun) 1 o₁, _) = _
      rw [levelMap_eq_of_toBase_eq (show E'.toBase 1 fo₁ = (f ∘ R.toFun) (E.toBase 1 o₁) by
        rw [Function.comp_apply, hfix]; exact hfo)]
    refine ⟨heq, ?_⟩
    have := h2 R R' hR hR' hh
    rw [heq] at this
    exact this

/-- One retraction suffices (Proposition 2.6 (1)), from B with the target retract `(E'₀, E'₀, E')`. -/
theorem of_exists (hB : B) {E E' : ScBanach} {C O : Set (E 0)} {f : E 0 → E' 0}
    (hO : IsScRetract E C O)
    (hex : ∃ R : ScRetraction E C, R.retract = O ∧ IsScSmooth R.U (f ∘ R.toFun)) :
    IsScSmoothRetractMap E C O E' univ univ f :=
  ((hB E E' C O univ univ f hO (isScRetract_univ E')).1).2 ⟨mapsTo_univ _ _, hex⟩

theorem B_to_A : B → A := by
  intro hB
  -- the target-free form of `IsScSmoothRetractMap`
  have hU : ∀ {E E' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)} {f : E 0 → E' 0}
      {O : Set (E 0)} {O' : Set (E' 0)}, IsScSmoothRetractMap E C O E' C' O' f →
      IsScSmoothRetractMap E C O E' univ univ f :=
    fun hf => ⟨mapsTo_univ _ _, hf.comp_isScSmooth⟩
  -- (iii) of B, for the project's notion
  have hEq : ∀ {E E' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)} {f : E 0 → E' 0}
      {O : Set (E 0)} {O' : Set (E' 0)}, IsScSmoothRetractMap E C O E' C' O' f →
      ∀ R : ScRetraction E C, R.retract = O →
        EqOn (retractTangentMap E C O f) (tangentMap R.U (f ∘ R.toFun)) (retractTangent E C O) := by
    intro E E' C C' f O O' hf R hR
    have h := hB E E' C O univ univ f ⟨R, hR⟩ (isScRetract_univ E')
    have hb : IsScSmoothRetractMapB E C O E' univ f := h.1.1 (hU hf)
    rw [retractTangent_eq_TOB R hR]
    exact (h.2 hb).2.2.1 R hR
  refine ⟨?_, hEq, ?_, ?_, ?_, ?_⟩
  · intro E E' C C' f O O' hO
    constructor
    · intro hf
      obtain ⟨R, hR⟩ := hO
      exact ⟨hf.mapsTo, R, hR, hf.comp_isScSmooth R hR⟩
    · rintro ⟨hmaps, hex⟩
      exact ⟨hmaps, (of_exists hB hO hex).comp_isScSmooth⟩
  · intro E E' C C' f O O' hf hO hO' p hp
    obtain ⟨R, hR⟩ := hO
    obtain ⟨R', hR'⟩ := hO'
    have h := hB E E' C O C' O' f ⟨R, hR⟩ ⟨R', hR'⟩
    have hb : IsScSmoothRetractMapB E C O E' O' f := h.1.1 hf
    rw [hEq hf R hR hp, retractTangent_eq_TOB R' hR']
    rw [retractTangent_eq_TOB R hR] at hp
    exact (h.2 hb).2.1 R R' hR hR' hp
  · intro E E' C C' f O O' hf R hR p hp
    exact hEq hf R hR hp
  · -- continuity on `O` (not part of B): direct
    intro E E' C C' f O O' hf hO
    obtain ⟨R, rfl⟩ := hO
    have := ((hf.comp_isScSmooth R rfl).isSc1.isSc0.continuousOn_base).mono R.retract_subset
    exact this.congr fun x hx => by
      simp only [Function.comp_apply, R.apply_eq_self_of_mem_retract hx]
  · -- level preservation on `O` (not part of B): direct
    intro E E' C C' f O O' hf hO m x hx hxm
    obtain ⟨R, rfl⟩ := hO
    obtain ⟨z, rfl⟩ := hxm
    have hz : z ∈ E.lvlSet R.U m := R.retract_subset hx
    have := (hf.comp_isScSmooth R rfl).isSc1.isSc0.mem_range m z hz
    rwa [Function.comp_apply, R.apply_eq_self_of_mem_retract hx] at this

#rt_check RoundTrip.V2_6.A_to_B [Polyfold.isScSmoothRetractMap_iff_exists,
  Polyfold.retractTangentMap_eqOn, Polyfold.IsScSmoothRetractMap.tangentMap_mapsTo,
  Polyfold.retractTangentMap_apply, Polyfold.IsScSmoothRetractMap.continuousOn,
  Polyfold.IsScSmoothRetractMap.mem_range_toBase]
#rt_check RoundTrip.V2_6.B_to_A [Polyfold.isScSmoothRetractMap_iff_exists,
  Polyfold.retractTangentMap_eqOn, Polyfold.IsScSmoothRetractMap.tangentMap_mapsTo,
  Polyfold.retractTangentMap_apply, Polyfold.IsScSmoothRetractMap.continuousOn,
  Polyfold.IsScSmoothRetractMap.mem_range_toBase]
#rt_overlap RoundTrip.V2_6.B_to_A [Polyfold.isScSmoothRetractMap_iff_exists,
  Polyfold.retractTangentMap_eqOn, Polyfold.IsScSmoothRetractMap.tangentMap_mapsTo,
  Polyfold.retractTangentMap_apply, Polyfold.IsScSmoothRetractMap.continuousOn,
  Polyfold.IsScSmoothRetractMap.mem_range_toBase]

end RoundTrip.V2_6
