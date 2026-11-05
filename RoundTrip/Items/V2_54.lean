import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_54

/-! Round trip for V2_54 (Definition 2.47: `U ◁ F`, strong bundle maps and retractions).

`A` is the conjunction of the types of the theorems among the item's declarations:
`Polyfold.IsPartialQuadrant.prod_univ`, `Polyfold.IsRelOpenInQuadrant.prod_univ` and
`Polyfold.IsStrongBundleRetraction.fiber_idem` (no universe parameters).  The definitions
`doubleLevel`, `shiftFiber`, `IsStrongBundleMap`, `IsStrongBundleRetraction`, `baseRetraction`,
`toScRetraction`, `toScRetractionOne` are vocabulary.

The substance of the item is the comparison of definitions, which `B` itself asserts: the
project's `doubleLevel`, `IsStrongBundleMap`, `IsStrongBundleRetraction` agree with the blind
`doubleLevelB`, `IsStrongBundleMapB`, `IsStrongBundleRetractionB` (`map_iff`, `retraction_iff`,
proved here), the levels of `(U ◁ F)[i]` are `U_m ⊕ F_{m+i}`, and the base map of a strong bundle
retraction is an sc-smooth retraction.  So `B` is proved outright (`B_holds`), and `A_to_B` does
not use `A`.  Conversely the three theorems of `A` are elementary facts about the definitions,
proved directly (`prod_univ` re-proved by the project's construction; `fiber_idem` from `R ∘ R = R`
and `r(u) = u` on `O`), so `B_to_A` does not use `B` either.

Harness: the statement of `fiber_idem` mentions `baseRetraction`, whose proof field `isScSmooth`
uses the banned `IsRelOpenInQuadrant.prod_univ`; every proof mentioning `A` (and the last clause
of `B`, which uses `baseRetraction`) therefore reaches it through that proof field only:
`#rt_check_soft`. -/

namespace RoundTrip.V2_54
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.IsPartialQuadrant.prod_univ) ∧
    (type_of% @Polyfold.IsRelOpenInQuadrant.prod_univ) ∧
    (type_of% @Polyfold.IsStrongBundleRetraction.fiber_idem)

theorem A_holds : A :=
  ⟨@Polyfold.IsPartialQuadrant.prod_univ, @Polyfold.IsRelOpenInQuadrant.prod_univ,
    @Polyfold.IsStrongBundleRetraction.fiber_idem⟩

/-! ### The theorems of `A`, directly -/

theorem pq_prod_univ' : type_of% @Polyfold.IsPartialQuadrant.prod_univ := by
  intro E C hC F
  obtain ⟨n, W, T, rfl⟩ := hC
  let T₁ : ScIso (E.prod F) (((ScBanach.const (Fin n → ℝ)).prod W).prod F) :=
    { lvl := fun m => (T m).prodCongr (ContinuousLinearEquiv.refl ℝ (F m))
      incl_comm := fun m x => Prod.ext (T.incl_comm m x.1) rfl }
  refine ⟨n, W.prod F, T₁.trans (prodQuadrantIso n W F), ?_⟩
  ext p
  change (p.1 ∈ T 0 ⁻¹' quadrant n W 0 ∧ p.2 ∈ univ) ↔ ∀ i, 0 ≤ (T 0 p.1).1 i
  simp only [mem_preimage, mem_univ, and_true]
  rfl

theorem relOpen_prod_univ' : type_of% @Polyfold.IsRelOpenInQuadrant.prod_univ := by
  intro E C U hU F
  obtain ⟨O, hO, rfl⟩ := hU.relOpen
  refine ⟨pq_prod_univ' hU.isPartialQuadrant F, O ×ˢ univ, hO.prod isOpen_univ, ?_⟩
  rw [prod_inter_prod, inter_univ]

theorem fiber_idem' : type_of% @Polyfold.IsStrongBundleRetraction.fiber_idem := by
  intro E F C U R hU hR u hu h
  have huU : u ∈ U := (hR.baseRetraction hU).retract_subset hu
  have hfix : (R (u, 0)).1 = u := (hR.baseRetraction hU).apply_eq_self_of_mem_retract hu
  have h1 := congrArg Prod.snd (hR.idem (u, h) ⟨huU, mem_univ _⟩)
  have h2 : R (u, h) = (u, (R (u, h)).2) :=
    Prod.ext ((hR.fst_independent u huU h 0).trans hfix) rfl
  rw [h2] at h1
  exact h1

/-! ### The definitions agree -/

section Defs

variable {E F E' F' : ScBanach}

theorem map_iff {C U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U) (U' : Set (E' 0))
    (Φ : E 0 × F 0 → E' 0 × F' 0) : IsStrongBundleMap U U' Φ ↔ IsStrongBundleMapB U U' Φ := by
  have hdom : IsScDomain (E.prod F.shift) (U ×ˢ univ) :=
    (relOpen_prod_univ' hU F.shift).isScDomain
  constructor
  · intro hΦ
    refine ⟨⟨fun u => (Φ (u, 0)).1, fun u hu => ⟨(hΦ.mapsTo ⟨hu, mem_univ _⟩).1,
      fun h => hΦ.fst_independent u hu h 0⟩⟩, hΦ.fiber_linear, ?_, hΦ.isScSmooth_zero,
      ⟨shiftFiber Φ, fun u hu h => ⟨rfl, ?_⟩, hΦ.isScSmooth_one⟩⟩
    · intro m k hk q hq
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ :=
        hΦ.preserves_filtration m k hk _ hq ⟨q.1, rfl⟩ _ ⟨q.2, rfl⟩
      exact ⟨(a, b), Prod.ext ha.symm hb.symm⟩
    · exact Function.invFun_eq
        (hΦ.preserves_filtration 0 1 (by norm_num) u hu ⟨u, rfl⟩ _ ⟨h, rfl⟩).2
  · rintro ⟨⟨φ, hφ⟩, hlin, hfilt, h0, ⟨Φ₁, hagree, h1⟩⟩
    refine ⟨fun p hp => ?_, fun u hu h h' => ?_, hlin, ?_, h0, ?_⟩
    · refine ⟨?_, mem_univ _⟩
      have := (hφ p.1 hp.1).2 p.2
      rw [this]; exact (hφ p.1 hp.1).1
    · rw [(hφ u hu).2 h, (hφ u hu).2 h']
    · rintro m k hk u hu ⟨a, rfl⟩ h ⟨b, rfl⟩
      obtain ⟨q', hq'⟩ := hfilt m k hk (a, b) hu
      exact ⟨⟨q'.1, (congrArg Prod.fst hq').symm⟩, ⟨q'.2, (congrArg Prod.snd hq').symm⟩⟩
    · refine h1.congr hdom fun p hp => ?_
      obtain ⟨hfst, hsnd⟩ := hagree p.1 hp.1 p.2
      refine Prod.ext hfst ?_
      apply F'.toBase_injective 1
      change F'.toBase 1 (Φ₁ p).2 =
        F'.toBase 1 (Function.invFun (F'.toBase 1) (Φ (p.1, F.toBase 1 p.2)).2)
      rw [hsnd, Function.invFun_eq ⟨(Φ₁ p).2, hsnd⟩]

theorem retraction_iff {C U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U)
    (R : E 0 × F 0 → E 0 × F 0) : IsStrongBundleRetraction U R ↔ IsStrongBundleRetractionB U R := by
  constructor
  · intro hR
    exact ⟨(map_iff hU U R).1 hR.toIsStrongBundleMap, fun u hu h => hR.idem (u, h) ⟨hu, mem_univ _⟩⟩
  · rintro ⟨hmap, hidem⟩
    exact ⟨(map_iff hU U R).2 hmap, fun p hp => hidem p.1 hp.1 p.2⟩

end Defs

/-- `B` holds outright: the project's definitions are B's. -/
theorem B_holds : B := by
  intro E F C U hU
  refine ⟨fun m k _ => ?_, fun m => ?_, fun m => ?_, fun E' F' C' U' _ Φ => map_iff hU U' Φ,
    fun R => retraction_iff hU R, fun R hR => ?_⟩
  · ext q
    simp [doubleLevel, doubleLevelB, ScBanach.mem_lvlSet]
  · ext q
    change (E.prod F).toBase m q ∈ U ×ˢ univ ↔ E.toBase m q.1 ∈ U
    rw [ScBanach.prod_toBase]
    simp
  · ext q
    change (E.prod F.shift).toBase m q ∈ U ×ˢ univ ↔ E.toBase m q.1 ∈ U
    rw [ScBanach.prod_toBase]
    simp
  · have hR' := (retraction_iff hU R).2 hR
    exact ⟨hR'.baseRetraction hU, rfl, fun u hu h => hR'.fst_independent u hu h 0⟩

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := fun _ => ⟨pq_prod_univ', relOpen_prod_univ', fiber_idem'⟩

#rt_check_soft RoundTrip.V2_54.A_to_B [Polyfold.IsPartialQuadrant.prod_univ,
  Polyfold.IsRelOpenInQuadrant.prod_univ, Polyfold.IsStrongBundleRetraction.fiber_idem]
#rt_check_soft RoundTrip.V2_54.B_to_A [Polyfold.IsPartialQuadrant.prod_univ,
  Polyfold.IsRelOpenInQuadrant.prod_univ, Polyfold.IsStrongBundleRetraction.fiber_idem]
#rt_overlap RoundTrip.V2_54.B_to_A [Polyfold.IsPartialQuadrant.prod_univ,
  Polyfold.IsRelOpenInQuadrant.prod_univ, Polyfold.IsStrongBundleRetraction.fiber_idem]

end RoundTrip.V2_54
