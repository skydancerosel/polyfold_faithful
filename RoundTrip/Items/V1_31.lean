import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_31

/-! Round trip for V1_31 (after Definition 1.1: finite-dimensional spaces carry only the constant
sc-structure; on an infinite-dimensional space the constant structure violates (1)).

`A` is the conjunction of the types of the theorems among the item's declarations:
`ScBanach.smooth_eq_top_of_finiteDimensional`, `ScBanach.toBase_bijective_of_finiteDimensional`,
`ScScale.finiteDimensional_of_surjective_incl`.  `ScBanach.isoConstOfFiniteDimensional` is a
definition (vocabulary; it packages `toBase_bijective_of_finiteDimensional` into an `ScIso` with
`ScBanach.const`).  No universe parameters (`ScScale`/`ScBanach` live in `Type`). -/

namespace RoundTrip.V1_31
open Polyfold

/-! ### Glue: the blind sc-structures are the project's scales -/

theorem toBase_eq_inclTo0 (E : ScScale) : ∀ m, E.toBase m = inclTo0 E.lvl E.incl m
  | 0 => rfl
  | m + 1 => by
    show (E.toBase m).comp (E.incl m) = (inclTo0 E.lvl E.incl m).comp (E.incl m)
    rw [toBase_eq_inclTo0 E m]

theorem smooth_eq_smoothPts (E : ScScale) :
    (E.smooth : Set (E 0)) = smoothPts E.lvl E.incl := by
  ext x
  rw [SetLike.mem_coe, ScScale.mem_smooth_iff, smoothPts, Set.mem_iInter]
  refine forall_congr' fun m => ?_
  rw [toBase_eq_inclTo0]
  rfl

/-- A blind sc-structure as a project scale. -/
def toScScaleB (X : ℕ → Type) [∀ m, NormedAddCommGroup (X m)] [∀ m, NormedSpace ℝ (X m)]
    (ι : ∀ m, X (m + 1) →L[ℝ] X m) (h : IsScStructure X ι) : ScScale where
  lvl := X
  complete := h.1
  incl := ι
  incl_injective := h.2.1
  incl_isCompactOperator := h.2.2.1

/-- A blind sc-structure as a project `ScBanach`. -/
def toScBanach (X : ℕ → Type) [∀ m, NormedAddCommGroup (X m)] [∀ m, NormedSpace ℝ (X m)]
    (ι : ∀ m, X (m + 1) →L[ℝ] X m) (h : IsScStructure X ι) : ScBanach where
  toScScale := toScScaleB X ι h
  dense_smooth m := by
    have := h.2.2.2 m
    show Dense ((toScScaleB X ι h).toBase m ⁻¹'
      ((toScScaleB X ι h).smooth : Set ((toScScaleB X ι h) 0)))
    rw [smooth_eq_smoothPts, toBase_eq_inclTo0]
    exact this

/-- A project `ScBanach` is a blind sc-structure. -/
theorem isScStructure_of_scBanach (E : ScBanach) : IsScStructure E.lvl E.incl := by
  refine ⟨E.complete, E.incl_injective, E.incl_isCompactOperator, fun m => ?_⟩
  have := E.dense_smooth m
  change Dense ((E.toBase m) ⁻¹' (E.smooth : Set (E 0))) at this
  rwa [smooth_eq_smoothPts, toBase_eq_inclTo0] at this

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.ScBanach.smooth_eq_top_of_finiteDimensional) ∧
  (type_of% @Polyfold.ScBanach.toBase_bijective_of_finiteDimensional) ∧
  (type_of% @Polyfold.ScScale.finiteDimensional_of_surjective_incl)

theorem A_holds : A :=
  ⟨@Polyfold.ScBanach.smooth_eq_top_of_finiteDimensional,
    @Polyfold.ScBanach.toBase_bijective_of_finiteDimensional,
    @Polyfold.ScScale.finiteDimensional_of_surjective_incl⟩

/-- The constant structure on a finite-dimensional space is an sc-structure (no hypothesis
needed: this is the project's `ScBanach.const`, a definition). -/
theorem const_isScStructure (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] :
    IsScStructure (fun _ : ℕ => V) (fun _ => ContinuousLinearMap.id ℝ V) := by
  have hid : ∀ m, ⇑(inclTo0 (fun _ : ℕ => V) (fun _ => ContinuousLinearMap.id ℝ V) m) = id := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      funext x
      show inclTo0 (fun _ : ℕ => V) (fun _ => ContinuousLinearMap.id ℝ V) m x = x
      rw [ih]; rfl
  refine ⟨fun _ => FiniteDimensional.complete ℝ V, fun _ => fun _ _ h => h, fun _ => ?_,
    fun m => ?_⟩
  · simpa [ContinuousLinearMap.coe_id'] using
      (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℝ) (E := V)).2 inferInstance
  · have : smoothPts (fun _ : ℕ => V) (fun _ => ContinuousLinearMap.id ℝ V) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => Set.mem_iInter.2 fun j => ⟨x, ?_⟩
      rw [hid]; rfl
    rw [this, Set.preimage_univ]
    exact dense_univ

theorem A_to_B : A → B := by
  intro hA
  refine ⟨fun V _ _ _ => const_isScStructure V, ?_, ?_⟩
  · intro X _ _ ι hS hfin m
    have := hS.1 m
    have := hS.1 0
    let E := toScBanach X ι hS
    have : FiniteDimensional ℝ (E 0) := hfin
    have hb : Function.Bijective (inclTo0 X ι m) := by
      have := hA.2.1 E m
      rwa [toBase_eq_inclTo0] at this
    exact ⟨ContinuousLinearEquiv.ofBijective (inclTo0 X ι m)
      (LinearMap.ker_eq_bot.2 hb.1) (LinearMap.range_eq_top.2 hb.2), rfl⟩
  · intro V _ _ _ hV
    have hc : ¬ IsCompactOperator (ContinuousLinearMap.id ℝ V) := by
      intro hc
      let E : ScScale :=
        { lvl := fun _ => V
          incl := fun _ => ContinuousLinearMap.id ℝ V
          incl_injective := fun _ _ _ h => h
          incl_isCompactOperator := fun _ => hc }
      exact hV (hA.2.2 E 0 fun x => ⟨x, rfl⟩)
    exact ⟨hc, fun hS => hc (hS.2.2.1 0)⟩

/-- `B → A`: the uniqueness part of `B` makes every `E_m → E₀` bijective (hence `E_∞ = E₀`); the
infinite-dimensional part gives `finiteDimensional_of_surjective_incl` (a bijective inclusion
`E_{m+1} → E_m` makes `id_{E_m}` compact). -/
theorem B_to_A : B → A := by
  intro hB
  have hbij : ∀ (E : ScBanach) [FiniteDimensional ℝ (E 0)] (m : ℕ),
      Function.Bijective (E.toBase m) := by
    intro E hfin m
    obtain ⟨φ, hφ⟩ := hB.2.1 E.lvl E.incl (isScStructure_of_scBanach E) hfin m
    rw [toBase_eq_inclTo0, ← hφ]
    exact φ.bijective
  refine ⟨fun E _ => ?_, fun E _ m => hbij E m, fun E m h => ?_⟩
  · refine Submodule.eq_top_iff'.2 fun x => (ScScale.mem_smooth_iff _).2 fun m => ?_
    exact (hbij E m).2 x
  · by_contra hV
    set e := ContinuousLinearEquiv.ofBijective (E.incl m)
      (LinearMap.ker_eq_bot.2 (E.incl_injective m)) (LinearMap.range_eq_top.2 h) with he
    have hid : (E.incl m).comp (e.symm : E m →L[ℝ] E (m + 1)) =
        ContinuousLinearMap.id ℝ (E m) := by
      ext x
      change E.incl m (e.symm x) = x
      have : E.incl m (e.symm x) = e (e.symm x) := rfl
      rw [this, ContinuousLinearEquiv.apply_symm_apply]
    have hc : IsCompactOperator ((E.incl m).comp (e.symm : E m →L[ℝ] E (m + 1))) :=
      (E.incl_isCompactOperator m).comp_clm _
    rw [hid] at hc
    exact (hB.2.2 (E m) hV).1 hc

#rt_check RoundTrip.V1_31.A_to_B [Polyfold.ScBanach.smooth_eq_top_of_finiteDimensional,
  Polyfold.ScBanach.toBase_bijective_of_finiteDimensional,
  Polyfold.ScBanach.isoConstOfFiniteDimensional,
  Polyfold.ScScale.finiteDimensional_of_surjective_incl]
#rt_check RoundTrip.V1_31.B_to_A [Polyfold.ScBanach.smooth_eq_top_of_finiteDimensional,
  Polyfold.ScBanach.toBase_bijective_of_finiteDimensional,
  Polyfold.ScBanach.isoConstOfFiniteDimensional,
  Polyfold.ScScale.finiteDimensional_of_surjective_incl]
#rt_overlap RoundTrip.V1_31.B_to_A [Polyfold.ScBanach.smooth_eq_top_of_finiteDimensional,
  Polyfold.ScBanach.toBase_bijective_of_finiteDimensional,
  Polyfold.ScBanach.isoConstOfFiniteDimensional,
  Polyfold.ScScale.finiteDimensional_of_surjective_incl]

end RoundTrip.V1_31
