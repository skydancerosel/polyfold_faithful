import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_55

/-! Round trip for V4_55 (Remark 4.24).

`A` is the conjunction of the types of `Polyfold.quotDim_le_finrank_of_eq_sup`,
`Polyfold.remark_4_3_2_chart`, `Polyfold.MPolyfold.remark_4_3_2_codim`,
`Polyfold.MPolyfold.remark_4_3_2` and `Polyfold.MPolyfold.remark_4_3_2_not_mem_boundary`
(universes instantiated at `0`).

`A → B`:
* (b), (c) use A's `remark_4_3_2` (tame charts only) and a **chart change**: B quantifies over
  every chart `φ` of the structure, not only tame ones.  At a tame chart `ψ` (which exists since
  `X` is tame) A gives `d_X(x) ≤ dim T_z(ψ(W ∩ A'))`; the dimension of the tangent space of the
  chart model of `A'` can only grow under the chart transition (`rank_le_transport`: the
  derivative of the transition maps `T_zQ` injectively into `T_{z'}Q'`), transported with the
  project's `chart_change_of_transport`.  B's data `(V, s)` with `V ⊆ dom φ` is the project's
  `SubmanifoldData` with `shrink φ = V`.
* (a) (`codim T^R = d_X(x)` in EVERY tame chart, at every presentation): A's
  `remark_4_3_2_codim` gives it only in SOME tame chart `ψ` (an `∃`); it is moved to the given
  tame chart by a chart change of the codimension (`codim_transport`: the transition derivative
  is an isomorphism `T_zO ≅ T_{z'}O'` carrying `T^R` onto `T^R`, the project's
  `proposition_2_4_10_reduced`, so the quotients are isomorphic), with
  `T_zO / (T_zO ∩ E_z)` finite-dimensional (B uses `Module.rank`, A `finrank`).  (The codimension
  half of `remark_4_3_2_chart` is not usable: it is guarded by a general-position hypothesis on an
  unrelated finite-dimensional `Q`.)

`B → A`: proved for the three M-polyfold conjuncts, two of them only for tame `X`:
`remark_4_3_2_codim` from (a) at the tame chart of `IsTame.exists_chart` (`B_to_A_codim`);
`remark_4_3_2` and `remark_4_3_2_not_mem_boundary` from (b), (c) applied to the submanifold
`A ∩ V` (A's `A` only carries submanifold data near `a`), for TAME `X` (`B_to_A424Tame`,
`B_to_ANotMemBoundaryTame`): A assumes only a tame chart at `a`, B a tame `X`.  The two chart
lemmas `quotDim_le_finrank_of_eq_sup` (pure linear algebra) and `remark_4_3_2_chart` (an arbitrary
set `Q ⊆ E`, a retraction tame for one presentation) are not consequences of B, which only speaks
of submanifolds of tame M-polyfolds. -/

open Set

noncomputable section

namespace RoundTrip.V4_55
open Polyfold

/-- The project's statement, universes `0`. -/
def A : Prop :=
  (type_of% @Polyfold.quotDim_le_finrank_of_eq_sup.{0}) ∧
  (type_of% @Polyfold.remark_4_3_2_chart) ∧
  (type_of% @Polyfold.MPolyfold.remark_4_3_2_codim.{0}) ∧
  (type_of% @Polyfold.MPolyfold.remark_4_3_2.{0}) ∧
  (type_of% @Polyfold.MPolyfold.remark_4_3_2_not_mem_boundary.{0})

theorem A_holds : A :=
  ⟨@Polyfold.quotDim_le_finrank_of_eq_sup.{0}, @Polyfold.remark_4_3_2_chart,
    @Polyfold.MPolyfold.remark_4_3_2_codim.{0}, @Polyfold.MPolyfold.remark_4_3_2.{0},
    @Polyfold.MPolyfold.remark_4_3_2_not_mem_boundary.{0}⟩

/-! ### Linear algebra glue -/

theorem comap_inf_self {V : Type} [AddCommGroup V] [Module ℝ V] (M K : Submodule ℝ V) :
    Submodule.comap M.subtype (M ⊓ K) = Submodule.comap M.subtype K := by
  ext x
  simp

/-- `M / (M ∩ E_x)` is finite-dimensional (it embeds into the finite-dimensional `E₀ / E_x`). -/
theorem finiteDimensional_quot_minimal {E : ScBanach} {n : ℕ} {W : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (x : E 0) (M : Submodule ℝ (E 0)) :
    FiniteDimensional ℝ (M ⧸ Submodule.comap M.subtype (minimalSubspaceWith T x)) := by
  set f := (coordMapL T x).toLinearMap ∘ₗ M.subtype with hf
  have hk : LinearMap.ker f = Submodule.comap M.subtype (minimalSubspaceWith T x) := by
    rw [hf, LinearMap.ker_comp]; rfl
  exact ((Submodule.quotEquivOfEq _ _ hk.symm).trans f.quotKerEquivRange).symm.finiteDimensional

/-! ### Chart change: the dimension of `T_zA` does not drop under the chart transition -/

theorem rank_le_transport (κ : Cardinal.{0}) :
    ∀ (E E' : ScBanach) (C : Set (E 0)) (C' : Set (E' 0)) (R : ScRetraction E C)
      (R' : ScRetraction E' C') (F : E 0 → E' 0) (G : E' 0 → E 0), R.IsDiffeoGerm R' F G →
      IsScSmooth R.U (F ∘ R) → IsScSmooth R'.U (G ∘ R') → ∀ (Q : Set (E 0)) (Q' : Set (E' 0)),
      IsScRetract E C Q → IsScRetract E' C' Q' → Q ⊆ R.retract → Q' ⊆ R'.retract →
      MapsTo F Q Q' → MapsTo G Q' Q → ∀ z : E 1, z ∈ E.lvlSet Q 1 → z ∈ E.smoothLvl 1 →
      ∀ (n : ℕ) (Wq : ScBanach) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq)),
      C = T 0 ⁻¹' quadrant n Wq 0 → ∀ (n' : ℕ) (Wq' : ScBanach)
      (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod Wq')), C' = T' 0 ⁻¹' quadrant n' Wq' 0 →
      (∀ N : Submodule ℝ (E 0), (N : Set (E 0)) = tangentSpace E C Q z → κ ≤ Module.rank ℝ N) →
      (∀ N : Submodule ℝ (E' 0), (N : Set (E' 0)) =
        tangentSpace E' C' Q' (levelMap (F ∘ R) 1 z) → κ ≤ Module.rank ℝ N) := by
  intro E E' C C' R R' F G h hFs _ Q Q' hQ hQ' hQR _ hFQ _ z hz _ _ _ _ _ _ _ _ _ hΦ N' hN'
  obtain ⟨S, hS⟩ := hQ
  have hzS : z ∈ E.lvlSet S.retract 1 := hS ▸ hz
  set N : Submodule ℝ (E 0) := LinearMap.range (scDeriv S.U S z : E 0 →ₗ[ℝ] E 0) with hNdef
  have hN : (N : Set (E 0)) = tangentSpace E C Q z := by
    rw [← hS]; exact (tangentSpace_eq_coe_submodule S hzS).symm
  have hκ := hΦ N hN
  have hx : z ∈ E.lvlSet R.retract 1 := hQR hz
  set A₀ : E 0 →ₗ[ℝ] E' 0 := (scDeriv R.U (F ∘ R) z : E 0 →ₗ[ℝ] E' 0) with hA₀
  have hmem : ∀ v : N, (A₀ ∘ₗ N.subtype) v ∈ N' := by
    intro v
    rw [← SetLike.mem_coe, hN']
    have hv : (v : E 0) ∈ tangentSpace E C Q z := by rw [← hN]; exact v.2
    exact scDeriv_mem_tangentSpace_of_subset R hFs ⟨S, hS⟩ hQ' hQR hFQ hz hv
  set f : N →ₗ[ℝ] N' := LinearMap.codRestrict N' (A₀ ∘ₗ N.subtype) hmem with hf
  -- `Dr(z) v = v` on `T_zQ ⊆ T_zO`
  have hfix : ∀ v : N, scDeriv R.U R z (v : E 0) = v := by
    intro v
    have hv : (v : E 0) ∈ tangentSpace E C Q z := by rw [← hN]; exact v.2
    have hvO := tangentSpace_subset_of_subset R ⟨S, hS⟩ hQR hz hv
    rw [tangentSpace_eq_range R hx] at hvO
    obtain ⟨u, hu⟩ := hvO
    rw [← hu]
    exact congrArg (fun L : E 0 →L[ℝ] E 0 => L u) (R.scDeriv_comp_self hx)
  have hinj : Function.Injective f := by
    intro v w hvw
    have h1 : A₀ v = A₀ w := congrArg Subtype.val hvw
    have h2 := congrArg (scDeriv R'.U (G ∘ R') (levelMap (F ∘ R) 1 z)) h1
    change scDeriv R'.U (G ∘ R') _ (scDeriv R.U (F ∘ R) z v) =
      scDeriv R'.U (G ∘ R') _ (scDeriv R.U (F ∘ R) z w) at h2
    rw [h.deriv_inv_deriv hx, h.deriv_inv_deriv hx, hfix, hfix] at h2
    exact Subtype.ext h2
  exact hκ.trans (LinearMap.rank_le_of_injective f hinj)

/-! ### Chart change: the codimension of `T^R` is carried by the transition (Proposition 2.30) -/

theorem codim_transport (κ : Cardinal.{0}) :
    ∀ (E E' : ScBanach) (C : Set (E 0)) (C' : Set (E' 0)) (R : ScRetraction E C)
      (R' : ScRetraction E' C') (F : E 0 → E' 0) (G : E' 0 → E 0), R.IsDiffeoGerm R' F G →
      IsScSmooth R.U (F ∘ R) → IsScSmooth R'.U (G ∘ R') → ∀ (Q : Set (E 0)) (Q' : Set (E' 0)),
      IsScRetract E C Q → IsScRetract E' C' Q' → Q ⊆ R.retract → Q' ⊆ R'.retract →
      MapsTo F Q Q' → MapsTo G Q' Q → ∀ z : E 1, z ∈ E.lvlSet Q 1 → z ∈ E.smoothLvl 1 →
      ∀ (n : ℕ) (Wq : ScBanach) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq)),
      C = T 0 ⁻¹' quadrant n Wq 0 → ∀ (n' : ℕ) (Wq' : ScBanach)
      (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod Wq')), C' = T' 0 ⁻¹' quadrant n' Wq' 0 →
      (∀ M : Submodule ℝ (E 0), (M : Set (E 0)) = tangentSpace E C R.retract z →
        Module.rank ℝ (M ⧸ Submodule.comap M.subtype (minimalSubspaceWith T (E.toBase 1 z))) = κ) →
      (∀ M : Submodule ℝ (E' 0), (M : Set (E' 0)) =
        tangentSpace E' C' R'.retract (levelMap (F ∘ R) 1 z) →
        Module.rank ℝ (M ⧸ Submodule.comap M.subtype
          (minimalSubspaceWith T' (E'.toBase 1 (levelMap (F ∘ R) 1 z)))) = κ) := by
  intro E E' C C' R R' F G h _ _ Q Q' _ _ hQR _ _ _ z hz _ n Wq T hT n' Wq' T' hT' hΦ M' hM'
  have hx : z ∈ E.lvlSet R.retract 1 := hQR hz
  set y := levelMap (F ∘ R) 1 z with hydef
  have hy : y ∈ E'.lvlSet R'.retract 1 := h.image_mem hx
  set M : Submodule ℝ (E 0) := LinearMap.range (scDeriv R.U R z : E 0 →ₗ[ℝ] E 0) with hMdef
  have hM : (M : Set (E 0)) = tangentSpace E C R.retract z :=
    (tangentSpace_eq_coe_submodule R hx).symm
  have hM'eq : M' = LinearMap.range (scDeriv R'.U R' y : E' 0 →ₗ[ℝ] E' 0) :=
    SetLike.coe_injective (hM'.trans (tangentSpace_eq_coe_submodule R' hy))
  subst hM'eq
  set A₀ : E 0 →ₗ[ℝ] E' 0 := (scDeriv R.U (F ∘ R) z : E 0 →ₗ[ℝ] E' 0) with hA₀
  set A₀' : E' 0 →ₗ[ℝ] E 0 := (scDeriv R'.U (G ∘ R') y : E' 0 →ₗ[ℝ] E 0) with hA₀'
  have hTA : ∀ v ∈ M, A₀ v ∈ LinearMap.range (scDeriv R'.U R' y : E' 0 →ₗ[ℝ] E' 0) := by
    intro v hv
    obtain ⟨u, hu⟩ := h.deriv_mem_range hx (v := v) (by obtain ⟨w, hw⟩ := hv; exact ⟨w, hw⟩)
    exact ⟨u, hu⟩
  have hTA' : ∀ w ∈ LinearMap.range (scDeriv R'.U R' y : E' 0 →ₗ[ℝ] E' 0), A₀' w ∈ M := by
    intro w hw
    have := h.symm.deriv_mem_range hy (v := w) (by obtain ⟨u, hu⟩ := hw; exact ⟨u, hu⟩)
    rw [h.image_image hx] at this
    obtain ⟨u, hu⟩ := this
    exact ⟨u, hu⟩
  have hinv1 : ∀ v ∈ M, A₀' (A₀ v) = v := by
    rintro _ ⟨w, rfl⟩
    change scDeriv R'.U (G ∘ R') y (scDeriv R.U (F ∘ R) z (scDeriv R.U R z w)) = _
    rw [h.deriv_inv_deriv hx]
    exact congrArg (fun L : E 0 →L[ℝ] E 0 => L w) (R.scDeriv_comp_self hx)
  have hinv2 : ∀ w ∈ LinearMap.range (scDeriv R'.U R' y : E' 0 →ₗ[ℝ] E' 0), A₀ (A₀' w) = w := by
    rintro _ ⟨u, rfl⟩
    change scDeriv R.U (F ∘ R) z (scDeriv R'.U (G ∘ R') y (scDeriv R'.U R' y u)) = _
    rw [h.deriv_deriv_inv hx]
    exact congrArg (fun L : E' 0 →L[ℝ] E' 0 => L u) (R'.scDeriv_comp_self hy)
  let e : M ≃ₗ[ℝ] LinearMap.range (scDeriv R'.U R' y : E' 0 →ₗ[ℝ] E' 0) :=
    { toFun := fun v => ⟨A₀ v, hTA v v.2⟩
      invFun := fun w => ⟨A₀' w, hTA' w w.2⟩
      map_add' := fun v w => Subtype.ext (map_add A₀ (v : E 0) (w : E 0))
      map_smul' := fun c v => Subtype.ext (map_smul A₀ c (v : E 0))
      left_inv := fun v => Subtype.ext (hinv1 v v.2)
      right_inv := fun w => Subtype.ext (hinv2 w w.2) }
  have hred := proposition_2_4_10_reduced h hx T hT T' hT'
  have hmap : (Submodule.comap M.subtype (minimalSubspaceWith T (E.toBase 1 z))).map
      (e : M →ₗ[ℝ] LinearMap.range (scDeriv R'.U R' y : E' 0 →ₗ[ℝ] E' 0)) =
      Submodule.comap (LinearMap.range (scDeriv R'.U R' y : E' 0 →ₗ[ℝ] E' 0)).subtype
        (minimalSubspaceWith T' (E'.toBase 1 y)) := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      have : A₀ v ∈ (reducedTangentSpaceWith R T z).map A₀ := ⟨v, ⟨v.2, hv⟩, rfl⟩
      rw [hred] at this
      exact this.2
    · intro hw
      have : (w : E' 0) ∈ reducedTangentSpaceWith R' T' y := ⟨w.2, hw⟩
      rw [← hred] at this
      obtain ⟨v, ⟨hvM, hvK⟩, hv⟩ := this
      exact ⟨⟨v, hvM⟩, hvK, Subtype.ext hv⟩
  rw [← hΦ M hM]
  exact (Submodule.Quotient.equiv _ _ e hmap).rank_eq.symm

section KeyLemma

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- The core of `A → B` (b), (c): for ANY chart `φ` (not only tame ones), A's Remark 4.24 at a tame
chart and the chart change give `d_X(x) ≤ dim T_z(φ(W ∩ A'))`. -/
theorem degIndex_le_rank (h424 : type_of% @Polyfold.MPolyfold.remark_4_3_2.{0})
    (hP : P.IsTame) {A' : Set X} {x : X} (hx : x ∈ A') (hgp : P.IsGeneralPositionAt A' x)
    (d : P.SubmanifoldData A') (hxd : x ∈ d.V) {φ : MChart X} (hφ : P.IsChart φ)
    (hxφ : x ∈ φ.source) {z : φ.model.E 1} (hz : φ.model.E.toBase 1 z = φ x)
    (N : Submodule ℝ (φ.model.E 0))
    (hN : (N : Set (φ.model.E 0)) =
      tangentSpace φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ A')) z) :
    (P.degIndex x : Cardinal) ≤ Module.rank ℝ N := by
  obtain ⟨ψ, hψ, hxψ, htame⟩ := MPolyfold.IsTame.exists_chart P hP x
  obtain ⟨zψ, hzψ, hzψs⟩ := exists_smoothLvl_one_of_mem_smooth (d.apply_mem_smooth hψ hx hxd hxψ)
  obtain ⟨-, -, -, Nψ, hNψ, hfin⟩ := d.remark_4_2_2 hψ hx hxd hxψ hzψ
  have h1 : P.degIndex x ≤ Module.finrank ℝ Nψ := h424 hgp d hxd hψ hxψ htame hzψ hNψ
  obtain ⟨n, Wq, T, hT⟩ := ψ.model.isPartialQuadrant
  obtain ⟨n', Wq', T', hT'⟩ := φ.model.isPartialQuadrant
  have h2 := MPolyfold.chart_change_of_transport
    (fun E C _ Q _ _ _ z => ∀ N : Submodule ℝ (E 0), (N : Set (E 0)) = tangentSpace E C Q z →
      Module.rank ℝ Nψ ≤ Module.rank ℝ N)
    (fun _ _ _ _ _ _ _ _ _ _ hQ _ h N hN => h N (hN.trans hQ.symm))
    (rank_le_transport (Module.rank ℝ Nψ)) hψ hφ (d.toSubData.isOpen_shrink ψ)
    (d.toSubData.isOpen_shrink φ) (d.toSubData.shrink_subset_source ψ)
    (d.toSubData.shrink_subset_source φ) (d.toSubData.isScRetract_image ψ hψ)
    (d.toSubData.isScRetract_image φ hφ) hx (d.toSubData.mem_shrink ψ hx hxd hxψ)
    (d.toSubData.mem_shrink φ hx hxd hxφ) hzψ hz hzψs T hT T' hT'
    (fun N' hN' => by
      have : N' = Nψ := SetLike.coe_injective (hN'.trans hNψ.symm)
      rw [this]) N hN
  calc (P.degIndex x : Cardinal) ≤ (Module.finrank ℝ Nψ : Cardinal) := by exact_mod_cast h1
    _ = Module.rank ℝ Nψ := Module.finrank_eq_rank ℝ Nψ
    _ ≤ Module.rank ℝ N := h2

/-- B's data `(V, s)` with `V ⊆ dom φ` as the project's `SubmanifoldData`; then `shrink φ = V`. -/
def dataOf {A' : Set X} {V : Set X} {s : X → X} (hs : P.IsScPlusRetractionOn s V)
    (himg : s '' V = A' ∩ V) : P.SubmanifoldData A' :=
  ⟨V, s, hs.isScSmoothOn.isOpen, hs, himg⟩

theorem shrink_dataOf {A' : Set X} {V : Set X} {s : X → X} (hs : P.IsScPlusRetractionOn s V)
    (himg : s '' V = A' ∩ V) {φ : MChart X} (hVφ : V ⊆ φ.source) :
    (dataOf hs himg).toSubData.shrink φ = V := by
  ext y
  constructor
  · intro hy; exact hy.1.1
  · intro hy
    exact ⟨⟨hy, hVφ hy⟩, ⟨hs.mapsTo hy, hVφ (hs.mapsTo hy)⟩⟩

end KeyLemma

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  rintro ⟨-, -, hcodim, h424, -⟩ X _ _ _ P hP
  -- the common core of (b), (c)
  have hbc : ∀ (A' : Set X) (x : X), x ∈ A' → P.IsGeneralPositionAt A' x →
      ∀ (V : Set X) (s : X → X) (φ : MChart X) (z : φ.model.E.lvl 1)
        (N : Submodule ℝ (φ.model.E.lvl 0)),
        P.IsScPlusRetractionOn s V → s '' V = A' ∩ V → x ∈ V →
        P.IsChart φ → V ⊆ φ.toPartialEquiv.source →
        φ.model.E.toBase 1 z = φ.toPartialEquiv x →
        (N : Set (φ.model.E.lvl 0)) =
          tangentSpace φ.model.E φ.model.C (φ.toPartialEquiv '' (A' ∩ V)) z →
          (P.degIndex x : Cardinal) ≤ Module.rank ℝ N := by
    intro A' x hx hgp V s φ z N hs himg hxV hφ hVφ hz hN
    refine degIndex_le_rank h424 hP hx hgp (dataOf hs himg) hxV hφ (hVφ hxV) hz N ?_
    rw [shrink_dataOf hs himg hVφ, inter_comm]
    exact hN
  refine ⟨?_, fun A' x _ hx hgp V s φ z N hs himg hxV hφ hVφ hz hN =>
    hbc A' x hx hgp V s φ z N hs himg hxV hφ hVφ hz hN, ?_⟩
  · -- (a): A's `remark_4_3_2_codim` (in one tame chart `ψ`) moved to the given tame chart `φ`
    -- by the chart change `codim_transport` (Proposition 2.30)
    intro φ n Wq T x z M hφ _ hT hxφ hxs hz hM
    obtain ⟨ψ, hψ, hxψ, Rψ, nψ, Wψ, Tψ, hRψ, hTψ, _, hcod⟩ := hcodim (P := P) hP hxs
    obtain ⟨zψ, hzψ, hzψs⟩ :=
      exists_smoothLvl_one_of_mem_smooth ((MPolyfold.mem_smoothSet_iff hψ hxψ).1 hxs)
    have hzψ1 : zψ ∈ ψ.model.E.lvlSet Rψ.retract 1 := by
      rw [ScBanach.mem_lvlSet, hzψ, hRψ]; exact ψ.mapsTo_model x hxψ
    have hΦψ : ∀ Mψ : Submodule ℝ (ψ.model.E 0),
        (Mψ : Set (ψ.model.E 0)) = tangentSpace ψ.model.E ψ.model.C ψ.model.O zψ →
        Module.rank ℝ (Mψ ⧸ Submodule.comap Mψ.subtype
          (minimalSubspaceWith Tψ (ψ.model.E.toBase 1 zψ))) = (P.degIndex x : Cardinal) := by
      intro Mψ hMψ
      have hMeq : Mψ = LinearMap.range (scDeriv Rψ.U Rψ zψ : ψ.model.E 0 →ₗ[ℝ] ψ.model.E 0) :=
        SetLike.coe_injective
          (hMψ.trans (by rw [← hRψ]; exact tangentSpace_eq_coe_submodule Rψ hzψ1))
      have hq := hcod zψ hzψ
      rw [quotDim, reducedTangentSpaceWith, comap_inf_self, ← hMeq] at hq
      have := finiteDimensional_quot_minimal Tψ (ψ.model.E.toBase 1 zψ) Mψ
      rw [← Module.finrank_eq_rank, hq]
    have hQψ : IsScRetract ψ.model.E ψ.model.C (ψ '' (ψ.source ∩ (univ : Set X))) := by
      rw [inter_univ, ψ.image_source]; exact ψ.model.isScRetract
    have hQφ : IsScRetract φ.model.E φ.model.C (φ '' (φ.source ∩ (univ : Set X))) := by
      rw [inter_univ, φ.image_source]; exact φ.model.isScRetract
    have h2 := MPolyfold.chart_change_of_transport (A := (univ : Set X))
      (fun E C O _ _ _ T z => ∀ M : Submodule ℝ (E 0), (M : Set (E 0)) = tangentSpace E C O z →
        Module.rank ℝ (M ⧸ Submodule.comap M.subtype (minimalSubspaceWith T (E.toBase 1 z))) =
          (P.degIndex x : Cardinal))
      (fun _ _ _ _ _ _ _ _ _ _ _ hO h M hM => h M (hM.trans hO.symm))
      (codim_transport _) hψ hφ ψ.isOpen_source φ.isOpen_source subset_rfl subset_rfl hQψ hQφ
      (mem_univ x) hxψ hxφ hzψ hz hzψs Tψ hTψ T hT hΦψ
    exact h2 M hM
  · -- (c)
    rintro A' x _ hx hgp ⟨V, s, φ, z, N, hs, himg, hxV, hφ, hVφ, hz, hN, h0⟩ hbd
    have := hbc A' x hx hgp V s φ z N hs himg hxV hφ hVφ hz hN
    rw [h0] at this
    have h1 : P.degIndex x = 0 := by exact_mod_cast le_zero_iff.1 this
    change 1 ≤ P.degIndex x at hbd
    omega

#rt_check RoundTrip.V4_55.A_to_B [Polyfold.quotDim_le_finrank_of_eq_sup,
  Polyfold.remark_4_3_2_chart, Polyfold.MPolyfold.remark_4_3_2_codim,
  Polyfold.MPolyfold.remark_4_3_2, Polyfold.MPolyfold.remark_4_3_2_not_mem_boundary]

/-! ### `B → A` (the M-polyfold conjuncts) -/

/-- `remark_4_3_2_codim` from B (a), at the tame chart of `IsTame.exists_chart`. -/
theorem B_to_A_codim : B → type_of% @Polyfold.MPolyfold.remark_4_3_2_codim.{0} := by
  intro hB X _ _ _ P hP x hx
  obtain ⟨φ, hφ, hxφ, R, hR, hRt⟩ := MPolyfold.IsTame.exists_chart P hP x
  obtain ⟨n, Wq, T, hT⟩ := φ.model.isPartialQuadrant
  have hRT := hRt n Wq T hT
  refine ⟨φ, hφ, hxφ, R, n, Wq, T, hR, hT, hRT, fun z hz => ?_⟩
  have hz1 : z ∈ φ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, hz, hR]; exact φ.mapsTo_model x hxφ
  set M := LinearMap.range (scDeriv R.U R z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0) with hMdef
  have hM : (M : Set (φ.model.E 0)) = tangentSpace φ.model.E φ.model.C φ.model.O z := by
    rw [← hR]; exact (tangentSpace_eq_coe_submodule R hz1).symm
  have h := (hB X P hP).1 φ n Wq T x z M hφ ⟨R, hR, hRt⟩ hT hxφ hx hz hM
  rw [quotDim, reducedTangentSpaceWith, ← hMdef, comap_inf_self]
  exact Module.finrank_eq_of_rank_eq h

section BtoA

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- `A ∩ V` is a smooth submanifold for the data `d` of `A`. -/
def dataInter {A : Set X} (d : P.SubmanifoldData A) : P.SubmanifoldData (A ∩ d.V) :=
  ⟨d.V, d.s, d.isOpen, d.isScPlusRetractionOn, by rw [d.image, inter_assoc, inter_self]⟩

theorem isSmoothSubmanifold_inter {A : Set X} (d : P.SubmanifoldData A) :
    P.IsSmoothSubmanifold (A ∩ d.V) := fun _ hb =>
  ⟨d.V, d.isOpen, hb.2, d.s, d.isScPlusRetractionOn, (dataInter d).image⟩

theorem shrink_inter {A : Set X} (d : P.SubmanifoldData A) (φ : MChart X) :
    d.toSubData.shrink φ ∩ (A ∩ d.V) = d.toSubData.shrink φ ∩ A := by
  ext y
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2, h1.1.1⟩

/-- General position of `A` at `a` is general position of `A ∩ V` at `a`. -/
theorem isGeneralPositionAt_inter {A : Set X} {a : X} (hgp : P.IsGeneralPositionAt A a)
    (d : P.SubmanifoldData A) (had : a ∈ d.V) {φ : MChart X} (hφ : P.IsChart φ)
    (haφ : a ∈ φ.source) {z : φ.model.E 1} (hz : φ.model.E.toBase 1 z = φ a) :
    P.IsGeneralPositionAt (A ∩ d.V) a := by
  obtain ⟨n, Wq, T, hT⟩ := φ.model.isPartialQuadrant
  refine ⟨⟨hgp.1, had⟩, dataInter d, φ, n, Wq, T, z, had, hφ, haφ, hT, hz, ?_⟩
  have := hgp.isGeneralPositionChart d hφ T hT had haφ hz
  unfold MPolyfold.SubmanifoldData.IsGeneralPositionChart at this ⊢
  change IsGeneralPositionRetractAt φ.model.E φ.model.C φ.model.O
    (φ '' (d.toSubData.shrink φ ∩ (A ∩ d.V))) T z
  rw [shrink_inter]
  exact this

/-- The sc⁺-retraction `s` restricted to `W = shrink φ`. -/
theorem isScPlusRetractionOn_shrink {A : Set X} (d : P.SubmanifoldData A) (φ : MChart X) :
    P.IsScPlusRetractionOn d.s (d.toSubData.shrink φ) where
  isScSmoothOn := d.isScPlusRetractionOn.isScSmoothOn.mono (d.toSubData.isOpen_shrink φ)
    (d.toSubData.shrink_subset_V φ)
  mapsTo := d.toSubData.mapsTo_shrink φ
  idem := fun y hy => d.isScPlusRetractionOn.idem y (d.toSubData.shrink_subset_V φ hy)
  mem_levelSet := fun y hy =>
    d.isScPlusRetractionOn.mem_levelSet y (d.toSubData.shrink_subset_V φ hy)
  isScSmoothOn_one := fun x₀ => (d.isScPlusRetractionOn.isScSmoothOn_one x₀).mono
    (d.toSubData.isOpen_shrink φ) (d.toSubData.shrink_subset_V φ)

theorem inter_shrink_eq {A : Set X} (d : P.SubmanifoldData A) (φ : MChart X) :
    (A ∩ d.V) ∩ d.toSubData.shrink φ = d.toSubData.shrink φ ∩ A := by
  rw [inter_comm, shrink_inter]

theorem image_shrink_inter {A : Set X} (d : P.SubmanifoldData A) (φ : MChart X) :
    d.s '' d.toSubData.shrink φ = (A ∩ d.V) ∩ d.toSubData.shrink φ := by
  have := d.toSubData.image_shrink φ
  rw [MPolyfold.SubmanifoldData.toSubData_r] at this
  rw [this, inter_shrink_eq]

end BtoA

/-- `remark_4_3_2` restricted to tame `X` (B's setting): B (b) for the submanifold `A ∩ V`. -/
def A424Tame : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X},
    P.IsTame → ∀ {A : Set X} {a : X}, P.IsGeneralPositionAt A a → ∀ (d : P.SubmanifoldData A),
    a ∈ d.V → ∀ {φ : MChart X}, P.IsChart φ → a ∈ φ.source →
    IsTameRetract φ.model.E φ.model.C φ.model.O → ∀ {z : φ.model.E 1},
    φ.model.E.toBase 1 z = φ a → ∀ {N : Submodule ℝ (φ.model.E 0)} [FiniteDimensional ℝ N],
    (N : Set (φ.model.E 0)) =
      tangentSpace φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ A)) z →
    P.degIndex a ≤ Module.finrank ℝ N

theorem B_to_A424Tame : B → A424Tame := by
  intro hB X _ _ _ P hP A a hgp d had φ hφ haφ _ z hz N _ hN
  have h := (hB X P hP).2.1 (A ∩ d.V) a (isSmoothSubmanifold_inter d) ⟨hgp.1, had⟩
    (isGeneralPositionAt_inter hgp d had hφ haφ hz) (d.toSubData.shrink φ) d.s φ z N
    (isScPlusRetractionOn_shrink d φ) (image_shrink_inter d φ)
    (d.toSubData.mem_shrink φ hgp.1 had haφ) hφ (d.toSubData.shrink_subset_source φ) hz
    (by rw [hN, inter_shrink_eq])
  rw [← Module.finrank_eq_rank] at h
  exact_mod_cast h

/-- `remark_4_3_2_not_mem_boundary` restricted to tame `X`: B (c) for the submanifold `A ∩ V`. -/
def ANotMemBoundaryTame : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X},
    P.IsTame → ∀ {A : Set X} {a : X}, P.IsGeneralPositionAt A a → ∀ (d : P.SubmanifoldData A),
    a ∈ d.V → ∀ {φ : MChart X}, P.IsChart φ → a ∈ φ.source →
    IsTameRetract φ.model.E φ.model.C φ.model.O → ∀ {z : φ.model.E 1},
    φ.model.E.toBase 1 z = φ a →
    tangentSpace φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ A)) z = {0} →
    a ∉ P.boundary

theorem B_to_ANotMemBoundaryTame : B → ANotMemBoundaryTame := by
  intro hB X _ _ _ P hP A a hgp d had φ hφ haφ _ z hz h0
  refine (hB X P hP).2.2 (A ∩ d.V) a (isSmoothSubmanifold_inter d) ⟨hgp.1, had⟩
    (isGeneralPositionAt_inter hgp d had hφ haφ hz)
    ⟨d.toSubData.shrink φ, d.s, φ, z, ⊥, isScPlusRetractionOn_shrink d φ, image_shrink_inter d φ,
      d.toSubData.mem_shrink φ hgp.1 had haφ, hφ, d.toSubData.shrink_subset_source φ, hz, ?_,
      rank_bot ℝ _⟩
  rw [Submodule.bot_coe, inter_shrink_eq, h0]

#rt_check RoundTrip.V4_55.B_to_A_codim [Polyfold.quotDim_le_finrank_of_eq_sup,
  Polyfold.remark_4_3_2_chart, Polyfold.MPolyfold.remark_4_3_2_codim,
  Polyfold.MPolyfold.remark_4_3_2, Polyfold.MPolyfold.remark_4_3_2_not_mem_boundary]
#rt_check RoundTrip.V4_55.B_to_A424Tame [Polyfold.quotDim_le_finrank_of_eq_sup,
  Polyfold.remark_4_3_2_chart, Polyfold.MPolyfold.remark_4_3_2_codim,
  Polyfold.MPolyfold.remark_4_3_2, Polyfold.MPolyfold.remark_4_3_2_not_mem_boundary]
#rt_check RoundTrip.V4_55.B_to_ANotMemBoundaryTame [Polyfold.quotDim_le_finrank_of_eq_sup,
  Polyfold.remark_4_3_2_chart, Polyfold.MPolyfold.remark_4_3_2_codim,
  Polyfold.MPolyfold.remark_4_3_2, Polyfold.MPolyfold.remark_4_3_2_not_mem_boundary]
#rt_overlap RoundTrip.V4_55.B_to_A_codim [Polyfold.quotDim_le_finrank_of_eq_sup,
  Polyfold.remark_4_3_2_chart, Polyfold.MPolyfold.remark_4_3_2_codim,
  Polyfold.MPolyfold.remark_4_3_2, Polyfold.MPolyfold.remark_4_3_2_not_mem_boundary]
#rt_overlap RoundTrip.V4_55.B_to_A424Tame [Polyfold.quotDim_le_finrank_of_eq_sup,
  Polyfold.remark_4_3_2_chart, Polyfold.MPolyfold.remark_4_3_2_codim,
  Polyfold.MPolyfold.remark_4_3_2, Polyfold.MPolyfold.remark_4_3_2_not_mem_boundary]
#rt_overlap RoundTrip.V4_55.B_to_ANotMemBoundaryTame [Polyfold.quotDim_le_finrank_of_eq_sup,
  Polyfold.remark_4_3_2_chart, Polyfold.MPolyfold.remark_4_3_2_codim,
  Polyfold.MPolyfold.remark_4_3_2, Polyfold.MPolyfold.remark_4_3_2_not_mem_boundary]

end RoundTrip.V4_55

end
