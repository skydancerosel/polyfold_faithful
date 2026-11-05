import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_30

/-! Round trip for V1_30 (Proposition 1.10: compact perturbation of sc-Fredholm operators; the
project's item is the index statement).

`A` is the conjunction of the types of `Polyfold.proposition_1_10_index` (`ind(T + S) = ind T`)
and `Polyfold.proposition_1_10_index_lvl` (every `(T + S)_m` is Fredholm of index `ind T`).
Neither has universe parameters (`ScBanach` lives in `Type`).

* `A → B` is proved *using* `A`: an sc-operator `T'` all of whose level maps are Fredholm with the
  same index is regularizing (`ker T'_m = ker T'_0` and `F_m/R_m ≅ F_0/R_0` by a dimension count:
  `dim ker T'_m ≤ dim ker T'_0`, `codim R_m ≥ codim R_0` since `F_m` is dense, and the indices
  agree), and a regularizing sc-operator with Fredholm level maps is sc-Fredholm (the construction
  of the project's proof of Proposition 1.10, with its bootstrap `ScPlus.regularizing_add`
  replaced by the index argument).  `proposition_1_10` itself is not used.
* `B → A`: `B` gives that `T + S` is sc-Fredholm, hence (Lemma 2.D, `IsScFredholm.fredholmIndex_lvl`)
  every level map is Fredholm of index `ind(T + S)`; the index equality `ind(T + S) = ind T` is
  not in `B` and is supplied by the classical invariance of the Fredholm index under compact
  perturbations (`fredholmIndex_add_isCompactOperator`, a project lemma, used without `B`). -/

namespace RoundTrip.V1_30
open Polyfold Set Module

/-- The blind `IsScFredholmB` is the project's `IsScFredholm` (same fields, repackaged). -/
theorem isScFredholmB_iff {E F : ScBanach} (T : ScOperator E F) :
    IsScFredholmB T ↔ IsScFredholm T := by
  constructor
  · rintro ⟨K, X, C, Y, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨⟨K, X, C, Y, h1, h2, h3, h4, h5, h6, h7⟩⟩
  · rintro ⟨s⟩
    exact ⟨s.K, s.X, s.C, s.Y, s.splitE, s.splitF, s.ker_eq, s.finite_K, s.finite_C, s.range_eq,
      s.bijOn⟩

/-- An sc-operator whose level maps are Fredholm **with the same index** is regularizing. -/
theorem regularizing_of_index {E F : ScBanach} (T' : ScOperator E F)
    (hFred : ∀ m, (T' m).IsFredholm)
    (hI : ∀ m, fredholmIndex (T' m) = fredholmIndex (T' 0)) {m : ℕ} {e : E 0}
    (he : T' 0 e ∈ range (F.toBase m)) : e ∈ range (E.toBase m) := by
  -- kernels: `ker T'_m ↪ ker T'_0`
  set K0 := LinearMap.ker (T' 0 : E 0 →ₗ[ℝ] F 0) with hK0
  set Km := LinearMap.ker (T' m : E m →ₗ[ℝ] F m) with hKm
  have : FiniteDimensional ℝ K0 := (hFred 0).finite_ker
  have : FiniteDimensional ℝ Km := (hFred m).finite_ker
  have hmaps : ∀ x ∈ Km, (E.toBase m : E m →ₗ[ℝ] E 0) x ∈ K0 := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe, ← T'.toBase_comm]
    rw [ContinuousLinearMap.coe_coe] at hx
    rw [hx, map_zero]
  let ι : Km →ₗ[ℝ] K0 := (E.toBase m : E m →ₗ[ℝ] E 0).restrict hmaps
  have hι : Function.Injective ι := fun x y hxy =>
    Subtype.ext (E.toBase_injective m (congrArg Subtype.val hxy))
  have hk : finrank ℝ Km ≤ finrank ℝ K0 := LinearMap.finrank_le_finrank_of_injective hι
  -- cokernels: `F_m / R_m ↠ F_0 / R_0`
  set R0 := LinearMap.range (T' 0 : E 0 →ₗ[ℝ] F 0) with hR0
  set Rm := LinearMap.range (T' m : E m →ₗ[ℝ] F m) with hRm
  have hR0cl : IsClosed (R0 : Set (F 0)) := (hFred 0).isClosed_range
  have : FiniteDimensional ℝ (F 0 ⧸ R0) := (hFred 0).finite_coker
  have : FiniteDimensional ℝ (F m ⧸ Rm) := (hFred m).finite_coker
  have hRle : Rm ≤ R0.comap (F.toBase m : F m →ₗ[ℝ] F 0) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨E.toBase m x, by
      rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe, ← T'.toBase_comm]; rfl⟩
  let Φ : (F m ⧸ Rm) →ₗ[ℝ] (F 0 ⧸ R0) := Rm.mapQ R0 (F.toBase m : F m →ₗ[ℝ] F 0) hRle
  have hΦmk : ∀ y : F m, Φ (Submodule.Quotient.mk y) = Submodule.Quotient.mk (F.toBase m y) :=
    fun _ => rfl
  have hΦsurj : Function.Surjective Φ := by
    have hdense : Dense ((LinearMap.range Φ : Submodule ℝ (F 0 ⧸ R0)) : Set (F 0 ⧸ R0)) := by
      have h1 : DenseRange R0.mkQL := (Submodule.mkQ_surjective _).denseRange
      have h2 : Dense (R0.mkQL '' (F.smooth : Set (F 0))) :=
        h1.dense_image R0.mkQL.continuous
          (by rw [← ScScale.smoothLvl_zero]; exact F.dense_smooth 0)
      refine h2.mono ?_
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨w, hw⟩ := (ScScale.mem_smooth_iff _).1 hz m
      exact ⟨Submodule.Quotient.mk w, by rw [hΦmk, hw]; rfl⟩
    have hcl : IsClosed ((LinearMap.range Φ : Submodule ℝ (F 0 ⧸ R0)) : Set (F 0 ⧸ R0)) :=
      Submodule.closed_of_finiteDimensional _
    rw [← LinearMap.range_eq_top, ← Submodule.coe_eq_univ, ← hcl.closure_eq, hdense.closure_eq]
  have hc : finrank ℝ (F 0 ⧸ R0) ≤ finrank ℝ (F m ⧸ Rm) := by
    have := LinearMap.finrank_range_le Φ
    rwa [LinearMap.range_eq_top.2 hΦsurj, finrank_top] at this
  -- the indices agree, so both inequalities are equalities
  have hIm : (finrank ℝ Km : ℤ) - finrank ℝ (F m ⧸ Rm) =
      (finrank ℝ K0 : ℤ) - finrank ℝ (F 0 ⧸ R0) := hI m
  have hkeq : finrank ℝ Km = finrank ℝ K0 := by omega
  have hceq : finrank ℝ (F m ⧸ Rm) = finrank ℝ (F 0 ⧸ R0) := by omega
  have hΦinj : Function.Injective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hceq).2 hΦsurj
  have hιsurj : Function.Surjective ι :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hkeq).1 hι
  -- conclusion
  obtain ⟨y, hy⟩ := he
  have h0 : Φ (Submodule.Quotient.mk y) = Φ 0 := by
    rw [hΦmk, hy, map_zero, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self _ e
  have hyR : y ∈ Rm := (Submodule.Quotient.mk_eq_zero Rm).1 (hΦinj h0)
  obtain ⟨x, hx⟩ := hyR
  have hk0 : e - E.toBase m x ∈ K0 := by
    rw [LinearMap.mem_ker, map_sub, ContinuousLinearMap.coe_coe, ← T'.toBase_comm]
    rw [ContinuousLinearMap.coe_coe] at hx
    rw [hx, hy, sub_self]
  obtain ⟨k, hk'⟩ := hιsurj ⟨_, hk0⟩
  refine ⟨x + k, ?_⟩
  have hkv : E.toBase m k = e - E.toBase m x := congrArg Subtype.val hk'
  rw [map_add, hkv, add_sub_cancel]

/-- A regularizing sc-operator whose level maps are Fredholm is sc-Fredholm (the construction of
the project's proof of Proposition 1.10, with the bootstrap replaced by the hypothesis `hreg`). -/
theorem isScFredholm_of_regularizing {E F : ScBanach} (T' : ScOperator E F)
    (hFred : ∀ m, (T' m).IsFredholm)
    (hreg : ∀ {m : ℕ} {e : E 0}, T' 0 e ∈ range (F.toBase m) → e ∈ range (E.toBase m)) :
    IsScFredholm T' := by
  -- the kernel `K'` is finite-dimensional and consists of smooth points
  set K' := LinearMap.ker (T' 0 : E 0 →ₗ[ℝ] F 0) with hK'
  have hK'fin : FiniteDimensional ℝ K' := (hFred 0).finite_ker
  have hK'smooth : K' ≤ E.smooth := by
    intro x hx
    rw [ScScale.mem_smooth_iff]
    intro m
    have hx0 : T' 0 x = 0 := hx
    exact hreg (m := m) (e := x) (by rw [hx0]; exact ⟨0, map_zero _⟩)
  obtain ⟨X', hX'⟩ := E.proposition_1_6 K' hK'smooth
  -- the range `Y'` is closed and its smooth points are dense on every level
  set Y' := LinearMap.range (T' 0 : E 0 →ₗ[ℝ] F 0) with hY'
  have hY'cl : IsClosed (Y' : Set (F 0)) := (hFred 0).isClosed_range
  have hY'lvl : ∀ m, LinearMap.range (T' m : E m →ₗ[ℝ] F m) = F.levelSub Y' m := by
    intro m
    refine le_antisymm (T'.range_lvl_le m) fun y hy => ?_
    rw [ScBanach.mem_levelSub] at hy
    obtain ⟨e, he⟩ := hy
    obtain ⟨e', rfl⟩ := hreg (m := m) (e := e) ⟨y, he.symm⟩
    refine ⟨e', F.toBase_injective m ?_⟩
    rw [ContinuousLinearMap.coe_coe, T'.toBase_comm]
    exact he
  have hY'sc : F.IsScSubspace Y' := by
    refine ⟨hY'cl, fun m y hy => ?_⟩
    rw [SetLike.mem_coe, ← hY'lvl m] at hy
    obtain ⟨e, rfl⟩ := hy
    have hcl : e ∈ closure (E.smoothLvl m) := by
      rw [(E.dense_smooth m).closure_eq]; exact mem_univ _
    refine closure_mono ?_ (image_closure_subset_closure_image (T' m).continuous ⟨e, hcl, rfl⟩)
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨?_, T'.mapsTo_smoothLvl m hz⟩
    rw [SetLike.mem_coe, ← hY'lvl m]
    exact LinearMap.mem_range_self _ _
  -- the complement `C'`: a right inverse of `F₀ → F₀/Y'` with values in the smooth points
  have hQfin : FiniteDimensional ℝ (F 0 ⧸ Y') := (hFred 0).finite_coker
  set p := Y'.mkQ with hp
  have hpsurj : LinearMap.range (p.domRestrict F.smooth) = ⊤ := by
    -- `p(F_∞)` is a dense subspace of the finite-dimensional `F₀/Y'`
    have hdense : Dense ((LinearMap.range (p.domRestrict F.smooth) : Submodule ℝ (F 0 ⧸ Y')) :
        Set (F 0 ⧸ Y')) := by
      have h1 : DenseRange Y'.mkQL := (Submodule.mkQ_surjective _).denseRange
      have h2 : Dense (Y'.mkQL '' (F.smooth : Set (F 0))) :=
        h1.dense_image Y'.mkQL.continuous (by rw [← ScScale.smoothLvl_zero]; exact F.dense_smooth 0)
      refine h2.mono ?_
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    have hcl : IsClosed ((LinearMap.range (p.domRestrict F.smooth) : Submodule ℝ (F 0 ⧸ Y')) :
        Set (F 0 ⧸ Y')) := Submodule.closed_of_finiteDimensional _
    rw [← Submodule.coe_eq_univ, ← hcl.closure_eq, hdense.closure_eq]
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective (p.domRestrict F.smooth) hpsurj
  set σ : (F 0 ⧸ Y') →ₗ[ℝ] F 0 := F.smooth.subtype ∘ₗ g with hσ
  have hpσ : ∀ q, p (σ q) = q := fun q => by
    have := LinearMap.congr_fun hg q
    simpa [σ] using this
  set C' := LinearMap.range σ with hC'
  have hC'smooth : C' ≤ F.smooth := by
    rintro _ ⟨q, rfl⟩
    exact (g q).2
  have hC'fin : FiniteDimensional ℝ C' := inferInstance
  -- `F₀ = Y' ⊕ C'` and `F_m = Y'_m ⊕ C'_m`
  have hcompl : ∀ m, IsCompl (F.levelSub Y' m) (F.levelSub C' m) := by
    intro m
    refine ⟨Submodule.disjoint_def.2 fun x hx hx' => ?_,
      Submodule.codisjoint_iff_exists_add_eq.2 fun z => ?_⟩
    · rw [ScBanach.mem_levelSub] at hx hx'
      obtain ⟨q, hq⟩ := hx'
      have h0 : (Submodule.Quotient.mk (F.toBase m x) : F 0 ⧸ Y') = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 hx
      have : q = 0 := by rw [← hpσ q, hq]; exact h0
      apply F.toBase_injective m
      rw [← hq, this, map_zero, map_zero]
    · obtain ⟨c, hc⟩ := (ScScale.mem_smooth_iff _).1 (hC'smooth (LinearMap.mem_range_self σ
        (Submodule.Quotient.mk (F.toBase m z)))) m
      refine ⟨z - c, c, ?_, ?_, sub_add_cancel z c⟩
      · rw [ScBanach.mem_levelSub, map_sub, hc, ← Submodule.Quotient.mk_eq_zero (p := Y'),
          Submodule.Quotient.mk_sub]
        have : (Submodule.Quotient.mk (σ (Submodule.Quotient.mk (F.toBase m z))) : F 0 ⧸ Y') =
            Submodule.Quotient.mk (F.toBase m z) := hpσ _
        rw [this, sub_self]
      · rw [ScBanach.mem_levelSub, hc]
        exact LinearMap.mem_range_self σ _
  have hsplitF : F.IsScSplitting C' Y' :=
    ⟨(F.proposition_1_6_iff C').2 hC'smooth, hY'sc, fun m => (hcompl m).symm⟩
  -- the bijections `X'_m → Y'_m`
  refine ⟨⟨K', X', C', Y', hX', hsplitF, rfl, hK'fin, hC'fin, rfl, fun m => ⟨?_, ?_, ?_⟩⟩⟩
  · intro x _
    rw [SetLike.mem_coe, ScBanach.mem_levelSub, T'.toBase_comm]
    exact LinearMap.mem_range_self _ _
  · intro x hx x' hx' hxx'
    have hker : x - x' ∈ LinearMap.ker (T' m : E m →ₗ[ℝ] F m) := by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, hxx', sub_self]
    rw [T'.ker_lvl] at hker
    have hX : x - x' ∈ E.levelSub X' m := Submodule.sub_mem _ hx hx'
    have := (Submodule.disjoint_def.1 (hX'.2.2 m).disjoint) _ hker hX
    exact sub_eq_zero.1 this
  · intro y hy
    rw [← hY'lvl m] at hy
    obtain ⟨e, rfl⟩ := hy
    obtain ⟨k, hk, x, hx, rfl⟩ := Submodule.mem_sup.1
      ((hX'.2.2 m).sup_eq_top ▸ Submodule.mem_top (x := e))
    refine ⟨x, hx, ?_⟩
    have hk0 : T' m k = 0 := by
      have : k ∈ LinearMap.ker (T' m : E m →ₗ[ℝ] F m) := by rw [T'.ker_lvl]; exact hk
      exact this
    rw [ContinuousLinearMap.coe_coe, map_add, hk0, zero_add]

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.proposition_1_10_index) ∧ (type_of% @Polyfold.proposition_1_10_index_lvl)

theorem A_holds : A := ⟨@Polyfold.proposition_1_10_index, @Polyfold.proposition_1_10_index_lvl⟩

/-- `A → B`, using `A`'s second conjunct: the level maps of `T + S` are Fredholm, all of index
`ind T`. -/
theorem A_to_B : A → B := by
  intro hA E F T S hT
  have hT' := (isScFredholmB_iff T).1 hT
  have hlvl := hA.2 hT' S
  refine (isScFredholmB_iff _).2 (isScFredholm_of_regularizing (T + S.toScOperator)
    (fun m => (hlvl m).1) fun {m} {e} he => ?_)
  exact regularizing_of_index (T + S.toScOperator) (fun m => (hlvl m).1)
    (fun m => by rw [(hlvl m).2, (hlvl 0).2]) he

/-- `B → A`: `B` makes `T + S` sc-Fredholm, which gives the level-wise Fredholm property; the
index equality is not in `B` and comes from `fredholmIndex_add_isCompactOperator`. -/
theorem B_to_A : B → A := by
  intro hB
  have hind : ∀ {E F : ScBanach} {T : ScOperator E F}, IsScFredholm T → ∀ (S : ScPlus E F),
      scIndex (T + S.toScOperator) = scIndex T := by
    intro E F T hT S
    obtain ⟨s⟩ := hT
    rw [scIndex_eq_fredholmIndex, scIndex_eq_fredholmIndex]
    exact fredholmIndex_add_isCompactOperator (s.isFredholm 0) (S.isCompactOperator 0)
  refine ⟨hind, fun {E F T} hT S m => ?_⟩
  have hTS : IsScFredholm (T + S.toScOperator) :=
    (isScFredholmB_iff _).1 (hB E F T S ((isScFredholmB_iff T).2 hT))
  rw [← hind hT S]
  exact hTS.fredholmIndex_lvl m

#rt_check RoundTrip.V1_30.A_to_B [Polyfold.proposition_1_10_index,
  Polyfold.proposition_1_10_index_lvl]
#rt_check RoundTrip.V1_30.B_to_A [Polyfold.proposition_1_10_index,
  Polyfold.proposition_1_10_index_lvl]
#rt_overlap RoundTrip.V1_30.A_to_B [Polyfold.proposition_1_10_index,
  Polyfold.proposition_1_10_index_lvl]
#rt_overlap RoundTrip.V1_30.B_to_A [Polyfold.proposition_1_10_index,
  Polyfold.proposition_1_10_index_lvl]

end RoundTrip.V1_30
