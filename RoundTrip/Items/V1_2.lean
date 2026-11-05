import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_2

/-! Round trip for V1_2 (Definition 1.3: sc-operators and linear sc-isomorphisms).

`A` is the conjunction of the types of the theorems `ScOperator.ext_base`,
`ScOperator.isScOperator`, `ScOperator.mapsTo_smoothLvl` and `isScOperator_of_mapsTo` (no universe
parameters); the definitions `ScOperator`, `IsScOperator`, `IsScOperator.toScOperator`,
`ScOperator.comp`, `ScIso`, `ScIso.symm`, `ScIso.trans`, `ScIso.ofBijective` are vocabulary.
(Refresh 2026-11-02: `isScOperator_of_mapsTo` and `ScIso.ofBijective` were added to the row.)
`B` says that the project's `IsScOperator`, `ScOperator` and `ScIso` are exactly the text's
notions.

* `A → B` (proved): the level maps of the text's definition are automatically linear (the
  inclusions are injective), so a text sc-operator is an `IsScOperator` and hence an `ScOperator`
  (`IsScOperator.toScOperator`); the converse uses `A`'s `isScOperator`.  A text sc-isomorphism
  gives level maps `T_m`, `S_m` which are mutually inverse (again by injectivity of the
  inclusions), i.e. an `ScIso`; the converse uses `isScOperator` and `ScIso.symm`.
* `B → A` (proved): `isScOperator` follows from `B` (an `ScOperator` is a text sc-operator by
  `B.2.1`, hence an `IsScOperator` by `B.1`); `ext_base` and `mapsTo_smoothLvl` are elementary
  consequences of the definitions which `B` (a characterization) does not mention; they are
  re-proved from the definitions.  Likewise `isScOperator_of_mapsTo` (a bounded `T₀` with
  `T₀(E_m) ⊆ F_m` is an sc-operator: the continuity that Definition 1.3 asks for is automatic) is
  not part of `B`; it is re-proved from Mathlib's closed graph theorem
  (`LinearMap.continuous_of_seq_closed_graph`), without `B`. -/

namespace RoundTrip.V1_2
open Polyfold

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.ScOperator.ext_base) ∧
    (type_of% @Polyfold.ScOperator.isScOperator) ∧
    (type_of% @Polyfold.ScOperator.mapsTo_smoothLvl) ∧
    (type_of% @Polyfold.isScOperator_of_mapsTo)

theorem A_holds : A :=
  ⟨@Polyfold.ScOperator.ext_base, @Polyfold.ScOperator.isScOperator,
    @Polyfold.ScOperator.mapsTo_smoothLvl, @Polyfold.isScOperator_of_mapsTo⟩

section Glue

variable {E F : ScBanach}

/-- A level map of a text sc-operator is linear: it is a continuous linear map. -/
noncomputable def linOf (T : E.lvl 0 →ₗ[ℝ] F.lvl 0) {m : ℕ} (Tm : E.lvl m → F.lvl m)
    (h : ∀ x, F.toBase m (Tm x) = T (E.toBase m x)) (hc : Continuous Tm) :
    E.lvl m →L[ℝ] F.lvl m where
  toFun := Tm
  map_add' x y := F.toBase_injective m (by simp only [map_add, h])
  map_smul' c x := F.toBase_injective m (by simp only [map_smul, h, RingHom.id_apply])
  cont := hc

theorem isScOperator_iff_text (T₀ : E.lvl 0 →L[ℝ] F.lvl 0) :
    IsScOperator T₀ ↔ IsScOperatorText (T₀ : E.lvl 0 →ₗ[ℝ] F.lvl 0) := by
  constructor
  · intro h m
    obtain ⟨Tm, hTm⟩ := h m
    exact ⟨Tm, hTm, Tm.continuous⟩
  · intro h m
    obtain ⟨Tm, h1, h2⟩ := h m
    exact ⟨linOf _ Tm h1 h2, h1⟩

/-- The base map of a text sc-operator is continuous (it is its own level-0 map). -/
noncomputable def baseL {T : E.lvl 0 →ₗ[ℝ] F.lvl 0} (h : IsScOperatorText T) :
    E.lvl 0 →L[ℝ] F.lvl 0 :=
  ⟨T, by
    obtain ⟨T0, h1, h2⟩ := h 0
    have : (T0 : E.lvl 0 → F.lvl 0) = T := funext fun x => h1 x
    change Continuous (T : E.lvl 0 → F.lvl 0)
    rw [← this]; exact h2⟩

/-- The `ScOperator` of a text sc-operator. -/
noncomputable def ofText {T : E.lvl 0 →ₗ[ℝ] F.lvl 0} (h : IsScOperatorText T) : ScOperator E F :=
  IsScOperator.toScOperator ((isScOperator_iff_text (baseL h)).2 h)

theorem ofText_zero {T : E.lvl 0 →ₗ[ℝ] F.lvl 0} (h : IsScOperatorText T) (x : E.lvl 0) :
    (ofText h).lvl 0 x = T x := by
  unfold ofText
  rw [IsScOperator.toScOperator_zero]
  rfl

/-- `A`'s `isScOperator`, turned into the text's notion. -/
theorem text_of_scOperator (hA : A) {T : E.lvl 0 →ₗ[ℝ] F.lvl 0} (T' : ScOperator E F)
    (h : ∀ x, T'.lvl 0 x = T x) : IsScOperatorText T := by
  have h1 := (isScOperator_iff_text (T'.lvl 0)).1 (hA.2.1 T')
  have h2 : ((T'.lvl 0 : E.lvl 0 →L[ℝ] F.lvl 0) : E.lvl 0 →ₗ[ℝ] F.lvl 0) = T :=
    LinearMap.ext h
  rwa [h2] at h1

end Glue

theorem A_to_B : A → B := by
  intro hA
  refine ⟨fun E F T₀ => isScOperator_iff_text T₀, fun E F T => ⟨?_, ?_⟩,
    fun E F T => ⟨?_, ?_⟩⟩
  · rintro ⟨T', hT'⟩
    exact text_of_scOperator hA T' hT'
  · intro h
    exact ⟨ofText h, ofText_zero h⟩
  · rintro ⟨T', hT'⟩
    refine ⟨text_of_scOperator hA T'.toScOperator hT', ?_,
      ((T'.lvl 0).symm : F.lvl 0 →L[ℝ] E.lvl 0), fun x => ?_, fun y => ?_,
      text_of_scOperator hA T'.symm.toScOperator fun _ => rfl⟩
    · have : (T : E.lvl 0 → F.lvl 0) = T'.lvl 0 := funext fun x => (hT' x).symm
      rw [this]
      exact (T'.lvl 0).bijective
    · change (T'.lvl 0).symm (T x) = x
      rw [← hT', ContinuousLinearEquiv.symm_apply_apply]
    · change T ((T'.lvl 0).symm y) = y
      rw [← hT', ContinuousLinearEquiv.apply_symm_apply]
  · rintro ⟨hT, -, S, hl, hr, hS⟩
    let T' := ofText hT
    let S' := ofText hS
    have hST : ∀ m x, S'.lvl m (T'.lvl m x) = x := fun m x => by
      apply E.toBase_injective m
      rw [S'.toBase_comm, T'.toBase_comm, ofText_zero, ofText_zero]
      exact hl _
    have hTS : ∀ m y, T'.lvl m (S'.lvl m y) = y := fun m y => by
      apply F.toBase_injective m
      rw [T'.toBase_comm, S'.toBase_comm, ofText_zero, ofText_zero]
      exact hr _
    let e : ∀ m, E.lvl m ≃L[ℝ] F.lvl m := fun m =>
      { toFun := T'.lvl m
        invFun := S'.lvl m
        map_add' := map_add _
        map_smul' := map_smul _
        left_inv := hST m
        right_inv := hTS m
        continuous_toFun := (T'.lvl m).continuous
        continuous_invFun := (S'.lvl m).continuous }
    exact ⟨⟨e, fun m x => T'.incl_comm m x⟩, ofText_zero hT⟩

/-- `ext_base`, re-proved from the definitions. -/
theorem ext_base' {E F : ScBanach} {T T' : ScOperator E F} (h : T.lvl 0 = T'.lvl 0) : T = T' := by
  obtain ⟨T, hT⟩ := T
  obtain ⟨T', hT'⟩ := T'
  simp only at h
  congr
  ext m x
  apply F.toBase_injective m
  rw [ScOperator.toBase_comm ⟨T, hT⟩ m x, ScOperator.toBase_comm ⟨T', hT'⟩ m x]
  simp only [h]

/-- `mapsTo_smoothLvl`, re-proved from the definitions. -/
theorem mapsTo_smoothLvl' {E F : ScBanach} (T : ScOperator E F) (m : ℕ) :
    Set.MapsTo (T.lvl m) (E.smoothLvl m) (F.smoothLvl m) := by
  intro x hx
  rw [ScScale.mem_smoothLvl_iff] at hx ⊢
  intro j
  obtain ⟨y, hy⟩ := hx j
  exact ⟨T.lvl j y, by rw [ScOperator.toBase_comm, ScOperator.toBase_comm, hy]⟩

/-- `isScOperator_of_mapsTo`, re-proved from Mathlib's closed graph theorem (not from `B`). -/
theorem isScOperator_of_mapsTo' {E F : ScBanach} {T₀ : E 0 →L[ℝ] F 0}
    (h : ∀ m (x : E m), T₀ (E.toBase m x) ∈ Set.range (F.toBase m)) : IsScOperator T₀ := by
  intro m
  have h' : ∀ x : E m, ∃ y : F m, F.toBase m y = T₀ (E.toBase m x) := fun x => h m x
  choose g hg using h'
  have hadd : ∀ x y, g (x + y) = g x + g y := fun x y =>
    F.toBase_injective m (by rw [hg, map_add, map_add, map_add, hg, hg])
  have hsmul : ∀ (c : ℝ) x, g (c • x) = c • g x := fun c x =>
    F.toBase_injective m (by rw [hg, map_smul, map_smul, map_smul, hg])
  let gl : E m →ₗ[ℝ] F m := ⟨⟨g, hadd⟩, hsmul⟩
  have hcont : Continuous gl := gl.continuous_of_seq_closed_graph fun u x y hu hgu => by
    apply F.toBase_injective m
    change F.toBase m y = F.toBase m (g x)
    rw [hg]
    have h1 : Filter.Tendsto (fun n => F.toBase m (g (u n))) Filter.atTop
        (nhds (F.toBase m y)) := ((F.toBase m).continuous.tendsto y).comp hgu
    have h2 : Filter.Tendsto (fun n => F.toBase m (g (u n))) Filter.atTop
        (nhds (T₀ (E.toBase m x))) := by
      simp_rw [hg]
      exact ((T₀.comp (E.toBase m)).continuous.tendsto x).comp hu
    exact tendsto_nhds_unique h1 h2
  exact ⟨⟨gl, hcont⟩, hg⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun h => ext_base' h, fun {E F} T => ?_, fun T m => mapsTo_smoothLvl' T m,
    fun h => isScOperator_of_mapsTo' h⟩
  exact (hB.1 E F (T.lvl 0)).2 ((hB.2.1 E F (T.lvl 0)).1 ⟨T, fun _ => rfl⟩)

#rt_check RoundTrip.V1_2.A_to_B [Polyfold.ScOperator.ext_base, Polyfold.ScOperator.isScOperator,
  Polyfold.ScOperator.mapsTo_smoothLvl, Polyfold.isScOperator_of_mapsTo]
#rt_check RoundTrip.V1_2.B_to_A [Polyfold.ScOperator.ext_base, Polyfold.ScOperator.isScOperator,
  Polyfold.ScOperator.mapsTo_smoothLvl, Polyfold.isScOperator_of_mapsTo]
#rt_overlap RoundTrip.V1_2.B_to_A [Polyfold.ScOperator.ext_base, Polyfold.ScOperator.isScOperator,
  Polyfold.ScOperator.mapsTo_smoothLvl, Polyfold.isScOperator_of_mapsTo]

end RoundTrip.V1_2
