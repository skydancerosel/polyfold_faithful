import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_55

/-! Round trip for V2_55 (Definition 2.48 and the remarks after it: local strong bundle retracts,
`K_{m,k}`, `K[i]`, `p : K[i] → O` sc-smooth).

`A` is the conjunction of the types of the theorems `IsStrongBundleRetraction.mem_image_iff`,
`IsStrongBundleRetraction.toScRetractionOne_retract`, `IsStrongBundleRetract.isScRetract`,
`IsStrongBundleRetract.isScRetract_one`, `IsStrongBundleRetract.isScSmoothRetractMap_fst`,
`IsStrongBundleRetract.isScSmoothRetractMap_fst_one` and
`IsStrongBundleRetract.isScSmoothRetractMap_shiftIncl` (no universe parameters: `ScBanach` lives
in `Type`).  `IsStrongBundleRetract`, `strongLevel`, `strongLevelShift`, `strongShiftOne` are
definitions (vocabulary).

Glue: the project's `IsStrongBundleRetraction U R` and B's `IsStrongBundleRetractionB U R` agree
when `U` is relatively open in a partial quadrant (`retr_to_B`, `B_to_retr`): the `[1]`-map of
B is any sc-smooth lift `Φ₁`, the project's is `shiftFiber R`; they agree on `U ⊕ F₁`, so
sc-smoothness transfers by `IsScSmooth.congr`.  `strongLevel`, `strongShiftOne` are B's
`KcapB`, `KoneB` definitionally; B's base `O = r(U)` is the project's
`(baseRetraction hU hR).retract` definitionally.

`A → B`: the formula `K_{m,k} = {Γ(u,h) = h, u ∈ O_m}` is `mem_image_iff` at the points
`(ι_m u, ι_k h)`; the level descriptions of `K[0]`, `K[1]` are this plus `prod_toBase` and
`shiftScale_toBase`; the sc-smoothness of `p : K[i] → O` is `isScSmoothRetractMap_fst(_one)`
with `isScRetract(_one)` (B's Definition 2.7 is the existential form), using `base K = r(U)`.

`B → A`: `mem_image_iff` is B's `K_{0,0}` formula; `isScRetract(_one)` and
`isScSmoothRetractMap_fst(_one)` are B's sc-smoothness of `p : K[i] → O` (whose existential form
provides retractions onto `K`, `K[1]`), via `isScSmoothRetractMap_iff_exists`;
`isScSmoothRetractMap_shiftIncl` composes the sc-operator `E ⊕ F¹ → E ⊕ F` with B's retraction
onto `K[1]`.  `toScRetractionOne_retract` is a statement about the project's own construction
`toScRetractionOne` (the retraction `shiftFiber R` on `U ⊕ F¹`), which B cannot mention; it is
re-proved directly from the definitions (set-level, from idempotence and the lift of fibre
components), using B's description of `K[1]` for the inclusion `K[1] ⊆ R[1](U ⊕ F¹)`. -/

namespace RoundTrip.V2_55
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.IsStrongBundleRetraction.mem_image_iff) ∧
    (type_of% @Polyfold.IsStrongBundleRetraction.toScRetractionOne_retract) ∧
    (type_of% @Polyfold.IsStrongBundleRetract.isScRetract) ∧
    (type_of% @Polyfold.IsStrongBundleRetract.isScRetract_one) ∧
    (type_of% @Polyfold.IsStrongBundleRetract.isScSmoothRetractMap_fst) ∧
    (type_of% @Polyfold.IsStrongBundleRetract.isScSmoothRetractMap_fst_one) ∧
    (type_of% @Polyfold.IsStrongBundleRetract.isScSmoothRetractMap_shiftIncl)

theorem A_holds : A :=
  ⟨@Polyfold.IsStrongBundleRetraction.mem_image_iff,
    @Polyfold.IsStrongBundleRetraction.toScRetractionOne_retract,
    @Polyfold.IsStrongBundleRetract.isScRetract,
    @Polyfold.IsStrongBundleRetract.isScRetract_one,
    @Polyfold.IsStrongBundleRetract.isScSmoothRetractMap_fst,
    @Polyfold.IsStrongBundleRetract.isScSmoothRetractMap_fst_one,
    @Polyfold.IsStrongBundleRetract.isScSmoothRetractMap_shiftIncl⟩

section Glue

variable {E F : ScBanach} {C U : Set (E.lvl 0)} {R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0}

/-- The project's strong bundle retractions are B's. -/
theorem retr_to_B (hR : IsStrongBundleRetraction U R) : IsStrongBundleRetractionB U R := by
  refine ⟨⟨⟨IsStrongBundleMap.base R, fun u hu => ⟨(hR.mapsTo ⟨hu, mem_univ _⟩).1,
    fun h => hR.fst_independent u hu h 0⟩⟩, hR.fiber_linear, ?_, hR.isScSmooth_zero,
    ⟨shiftFiber R, fun u hu h => ⟨rfl, ?_⟩, hR.isScSmooth_one⟩⟩,
    fun u hu h => hR.idem (u, h) ⟨hu, mem_univ _⟩⟩
  · intro m k hk q hq
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ :=
      hR.preserves_filtration m k hk _ hq ⟨q.1, rfl⟩ _ ⟨q.2, rfl⟩
    exact ⟨(a, b), Prod.ext ha.symm hb.symm⟩
  · exact hR.toBase_shiftFiber_snd (p := (u, h)) hu

/-- B's strong bundle retractions (on a relatively open `U`) are the project's. -/
theorem B_to_retr (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetractionB U R) :
    IsStrongBundleRetraction U R := by
  obtain ⟨⟨⟨φ, hφ⟩, hlin, hfilt, h0, ⟨Φ₁, hΦ₁, h1⟩⟩, hidem⟩ := hR
  refine ⟨⟨?_, ?_, hlin, ?_, h0, ?_⟩, ?_⟩
  · rintro ⟨u, h⟩ ⟨hu, -⟩
    refine ⟨?_, mem_univ _⟩
    rw [(hφ u hu).2 h]; exact (hφ u hu).1
  · intro u hu h h'
    rw [(hφ u hu).2 h, (hφ u hu).2 h']
  · rintro m k hk u hu ⟨a, rfl⟩ h ⟨b, rfl⟩
    obtain ⟨q', hq'⟩ := hfilt m k hk (a, b) hu
    exact ⟨⟨q'.1, by rw [hq']⟩, ⟨q'.2, by rw [hq']⟩⟩
  · refine IsScSmooth.congr (hU.prod_univ F.shift).isScDomain ?_ h1
    rintro ⟨u, h⟩ ⟨hu, -⟩
    obtain ⟨e1, e2⟩ := hΦ₁ u hu h
    have hr : (R (u, F.toBase 1 h)).2 ∈ range (F.toBase 1) := ⟨_, e2⟩
    refine Prod.ext e1 ?_
    change (Φ₁ (u, h)).2 = Function.invFun (F.toBase 1) (R (u, F.toBase 1 h)).2
    apply F.toBase_injective 1
    rw [Function.invFun_eq hr, e2]
  · rintro ⟨u, h⟩ ⟨hu, -⟩
    exact hidem u hu h

/-- The project's local strong bundle retracts are B's. -/
theorem retract_iff (K : Set (E.lvl 0 × F.lvl 0)) :
    IsStrongBundleRetract C K ↔ IsLocalStrongBundleRetractB C K := by
  constructor
  · rintro ⟨U, R, hU, hR, rfl⟩
    exact ⟨U, R, hU, retr_to_B hR, rfl⟩
  · rintro ⟨U, R, hU, hR, rfl⟩
    exact ⟨U, R, hU, B_to_retr hU hR, rfl⟩

/-- `p(K) = r(U)`: the projection of `K = R(U ◁ F)` is B's base. -/
theorem fst_image_eq (hR : IsStrongBundleRetractionB U R) :
    Prod.fst '' KB U R = baseB U R := by
  obtain ⟨⟨⟨φ, hφ⟩, -⟩, -⟩ := hR
  ext u
  constructor
  · rintro ⟨_, ⟨⟨v, h⟩, ⟨hv, -⟩, rfl⟩, rfl⟩
    exact ⟨v, hv, ((hφ v hv).2 0).trans ((hφ v hv).2 h).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨R (v, 0), ⟨(v, 0), ⟨hv, mem_univ _⟩, rfl⟩, rfl⟩

end Glue

theorem A_to_B : A → B := by
  rintro ⟨hmem, -, hret, hret1, hfst, hfst1, -⟩ E F C
  refine ⟨retract_iff, fun U R hU hRB => ?_⟩
  have hR := B_to_retr hU hRB
  have hK : IsStrongBundleRetract C (KB U R) := ⟨U, R, hU, hR, rfl⟩
  have hbase : IsStrongBundleRetract.base (KB U R) = baseB U R := fst_image_eq hRB
  -- the formula for `K_{m,k}`, from `mem_image_iff`
  have hcap : ∀ m k : ℕ, KcapB (KB U R) m k = KmkB U R m k := fun m k =>
    Set.ext fun q => hmem hU hR
  refine ⟨fun q hq => (hmem hU hR (p := q)).1 hq |>.1, fun m k _ => hcap m k,
    fun m k _ => hcap m k, fun m => ?_, fun m => ?_, rfl, fun i m _ => hcap m (m + i), ?_, ?_⟩
  · rw [← hcap m m]
    ext q
    change (E.prod F).toBase m q ∈ KB U R ↔ _
    rw [ScBanach.prod_toBase]; rfl
  · rw [← hcap m (m + 1)]
    ext q
    change (E.prod F.shift).toBase m q ∈ KoneB (KB U R) ↔ _
    rw [ScBanach.prod_toBase]
    change ((E.toBase m) q.1, F.toBase 1 (F.shift.toBase m q.2)) ∈ KB U R ↔
      ((E.toBase m) q.1, F.toBase (m + 1) q.2) ∈ KB U R
    rw [ScBanach.shiftScale_toBase F.toScScale m q.2]
  · have h := hfst hK
    rw [hbase] at h
    obtain ⟨ρ, hρ⟩ := hret hK
    exact ⟨h.mapsTo, ρ, hρ, h.comp_isScSmooth ρ hρ⟩
  · have h := hfst1 hK
    rw [hbase] at h
    obtain ⟨ρ, hρ⟩ := hret1 hK
    exact ⟨h.mapsTo, ρ, hρ, h.comp_isScSmooth ρ hρ⟩

/-- `toScRetractionOne_retract`, re-proved from the definitions (B cannot mention the project's
construction `toScRetractionOne`), with B's description of `K[1]`. -/
theorem toScRetractionOne_retract_of_B (hB : B) {E F : ScBanach} {C U : Set (E.lvl 0)}
    {R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0} (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) :
    (hR.toScRetractionOne hU).retract = strongShiftOne (R '' (U ×ˢ univ)) := by
  have hRB := retr_to_B hR
  obtain ⟨-, -, -, -, hone, -⟩ := (hB E F C).2 U R hU hRB
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    change ((shiftFiber R p).1, F.toBase 1 (shiftFiber R p).2) ∈ R '' (U ×ˢ univ)
    have hr : (R (p.1, F.toBase 1 p.2)).2 ∈ range (F.toBase 1) :=
      (hR.preserves_filtration 0 1 (by norm_num) p.1 hp.1 ⟨p.1, rfl⟩ _ ⟨p.2, rfl⟩).2
    have : F.toBase 1 (shiftFiber R p).2 = (R (p.1, F.toBase 1 p.2)).2 := Function.invFun_eq hr
    rw [this]
    exact ⟨_, ⟨hp.1, mem_univ _⟩, rfl⟩
  · intro hq
    -- B's `K[1]` description at level `0`: `q.1 ∈ O` and `Γ(q.1, ι q.2) = ι q.2`
    have hq' : q ∈ KmkB U R 0 (0 + 1) := by
      rw [← hone 0]; exact hq
    obtain ⟨⟨v, hv, hvq⟩, hfib⟩ := hq'
    have hvq' : (R (v, 0)).1 = q.1 := hvq
    obtain ⟨⟨⟨φ, hφ⟩, -⟩, hidem⟩ := hRB
    have hqU : q.1 ∈ U := by
      rw [← hvq', (hφ v hv).2 0]; exact (hφ v hv).1
    refine ⟨q, ⟨hqU, mem_univ _⟩, ?_⟩
    -- `R(q.1, ι q.2) = (q.1, ι q.2)`
    have hfst : (R (q.1, F.toBase 1 q.2)).1 = q.1 := by
      have h1 := congrArg Prod.fst (hidem v hv 0)
      rw [← hvq']
      have e1 : R (v, 0) = ((R (v, 0)).1, (R (v, 0)).2) := rfl
      rw [e1] at h1
      have hvU : (R (v, 0)).1 ∈ U := by rw [(hφ v hv).2 0]; exact (hφ v hv).1
      rw [(hφ _ hvU).2] at h1 ⊢
      exact h1
    change ((R (q.1, F.toBase 1 q.2)).1,
      Function.invFun (F.toBase 1) (R (q.1, F.toBase 1 q.2)).2) = q
    refine Prod.ext hfst ?_
    change Function.invFun (F.toBase 1) (R (E.toBase 0 q.1, F.toBase 1 q.2)).2 = q.2
    rw [hfib]
    exact Function.leftInverse_invFun (F.toBase_injective 1) q.2

theorem B_to_A : B → A := by
  intro hB
  -- from `IsStrongBundleRetract C K`, B's sc-smoothness of `p : K[i] → O`
  have hp : ∀ {E F : ScBanach} {C : Set (E.lvl 0)} {K : Set (E.lvl 0 × F.lvl 0)},
      IsStrongBundleRetract C K →
        IsScSmoothRetractMapB (E.prod F) (C ×ˢ univ) K E (Prod.fst '' K)
          (fun q : E.lvl 0 × F.lvl 0 => q.1) ∧
        IsScSmoothRetractMapB (E.prod F.shift) (C ×ˢ univ) (KoneB K) E (Prod.fst '' K)
          (fun q : E.lvl 0 × F.lvl 1 => q.1) := by
    intro E F C K hK
    obtain ⟨U, R, hU, hRB, rfl⟩ := ((hB E F C).1 K).1 hK
    obtain ⟨-, -, -, -, -, -, -, ⟨-, ρ, hρ, hs⟩, ⟨-, ρ₁, hρ₁, hs₁⟩⟩ := (hB E F C).2 U R hU hRB
    exact ⟨⟨fun q hq => ⟨q, hq, rfl⟩, ρ, hρ, hs⟩, ⟨fun q hq => ⟨_, hq, rfl⟩, ρ₁, hρ₁, hs₁⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro E F C U R hU hR p
    have h := ((hB E F C).2 U R hU (retr_to_B hR)).2.1 0 0 (by norm_num)
    exact Set.ext_iff.1 h p
  · intro E F C U R hU hR
    exact toScRetractionOne_retract_of_B hB hU hR
  · intro E F C K hK
    obtain ⟨-, ρ, hρ, -⟩ := (hp hK).1
    exact ⟨ρ, hρ⟩
  · intro E F C K hK
    obtain ⟨-, ρ, hρ, -⟩ := (hp hK).2
    exact ⟨ρ, hρ⟩
  · intro E F C K hK
    obtain ⟨hm, ρ, hρ, hs⟩ := (hp hK).1
    exact (isScSmoothRetractMap_iff_exists ⟨ρ, hρ⟩).2 ⟨hm, ρ, hρ, hs⟩
  · intro E F C K hK
    obtain ⟨hm, ρ, hρ, hs⟩ := (hp hK).2
    exact (isScSmoothRetractMap_iff_exists ⟨ρ, hρ⟩).2 ⟨hm, ρ, hρ, hs⟩
  · intro E F C K hK
    obtain ⟨-, ρ, hρ, -⟩ := (hp hK).2
    refine (isScSmoothRetractMap_iff_exists ⟨ρ, hρ⟩).2 ⟨fun q hq => ?_, ρ, hρ, ?_⟩
    · rw [ScBanach.prodShiftInclOp_apply]; exact hq
    · exact IsScSmooth.comp ρ.isScDomain (isScDomain_univ _)
        ((E.prodShiftInclOp F).isScSmooth (isScDomain_univ _)) ρ.isScSmooth (mapsTo_univ _ _)

#rt_check RoundTrip.V2_55.A_to_B [Polyfold.IsStrongBundleRetraction.mem_image_iff,
  Polyfold.IsStrongBundleRetraction.toScRetractionOne_retract,
  Polyfold.IsStrongBundleRetract.isScRetract, Polyfold.IsStrongBundleRetract.isScRetract_one,
  Polyfold.IsStrongBundleRetract.isScSmoothRetractMap_fst,
  Polyfold.IsStrongBundleRetract.isScSmoothRetractMap_fst_one,
  Polyfold.IsStrongBundleRetract.isScSmoothRetractMap_shiftIncl]
#rt_check RoundTrip.V2_55.B_to_A [Polyfold.IsStrongBundleRetraction.mem_image_iff,
  Polyfold.IsStrongBundleRetraction.toScRetractionOne_retract,
  Polyfold.IsStrongBundleRetract.isScRetract, Polyfold.IsStrongBundleRetract.isScRetract_one,
  Polyfold.IsStrongBundleRetract.isScSmoothRetractMap_fst,
  Polyfold.IsStrongBundleRetract.isScSmoothRetractMap_fst_one,
  Polyfold.IsStrongBundleRetract.isScSmoothRetractMap_shiftIncl]
#rt_overlap RoundTrip.V2_55.B_to_A [Polyfold.IsStrongBundleRetraction.mem_image_iff,
  Polyfold.IsStrongBundleRetraction.toScRetractionOne_retract,
  Polyfold.IsStrongBundleRetract.isScRetract, Polyfold.IsStrongBundleRetract.isScRetract_one,
  Polyfold.IsStrongBundleRetract.isScSmoothRetractMap_fst,
  Polyfold.IsStrongBundleRetract.isScSmoothRetractMap_fst_one,
  Polyfold.IsStrongBundleRetract.isScSmoothRetractMap_shiftIncl]

end RoundTrip.V2_55
