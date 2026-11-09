import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_15

/-! Round trip for V3_15 (Corollary 3.13: convergence on every level).

`A` is the conjunction of the types of the listed theorems `corollary_3_1_15_preprint`,
`corollary_3_1_15_section`, `tendsto_of_isCompact_of_tendsto_map` (universe parameters
instantiated at `0`, since B lives in `Type`) and `corollary_3_1_15_local` (no universe
parameters).

Refresh 2026-11-02 (HEAD after the germ reading, phase 2): `corollary_3_1_15_preprint` and
`corollary_3_1_15_section` now state the germ reading of Definition 3.11 (`IsScFredholmGerm`: the
filling `IsFillingGerm` and the sc⁺-section `IsScPlusGerm` are germs whose levels may shrink).  The
audit's obstacle (the project needed them on the chart's whole `U`) is gone, and `A → B` is now
proved.

* `A → B` (proved): `A_to_B_projGerm` (A's `corollary_3_1_15_preprint` gives B verbatim with the project's
  germ notion; `Level m` is `levelSet m` with `levelTopology m`, "eventually" is `∃ K, ∀ k ≥ K`)
  composed with `germB_to_germ`: **B's `IsScFredholmGermB` implies the project's
  `IsScFredholmGerm`**.  The remaining differences between the two germ notions are glue:
  - B's conjugating isomorphism `Ψ` lives on a relatively open `U₀ = O₀ ∩ C ⊆ U`, the project's on
    the whole `U` of the chart.  The chart is shrunk (`shrink`): base domain `V ∩ φ⁻¹(O₀)`,
    retraction domain `U ∩ r⁻¹(O₀) ∩ O₀ ⊆ U₀` (`ScRetraction.restrictIn`,
    `IsStrongBundleRetraction.restrictIn` of `Chapter4/Recentre.lean`), the same `Φ` as
    `StrongBundleChart.restrict`, hence a chart of the bundle (`StrongBundle.IsChart.restrict`).
    `StrongBundleChart.restrict` alone does not do it: its `U ∩ r⁻¹(φ(s))` need not lie in `U₀`.
  - Filling: B's germ is restricted to the new `U`; B's condition (3) (`Dk(0)` bijective from
    `ker Dr(0)` onto `ker ρ(0)` with a bound `‖v‖ ≤ c‖Dk(0)v‖`) is the project's topological
    isomorphism of kernels (`kerEquiv_of_bijOn`), with `Dr(0) = scDeriv U r 0` by uniqueness.
  - Conjugation: `Ψ` restricted to the new `U` and to `{u' ∈ U' | ψ'(u') ∈ U}` (relatively open),
    the basic germ restricted (`IsBasicGerm.inter`), `[0,∞)ᵏ ⊕ ℝⁿ⁻ᵏ` a partial quadrant
    (`isPartialQuadrant_quadC`), `h` = B's push-forward `Ψ ∘ (·, k) ∘ ψ⁻¹`, equal to
    `(Ψ(u, k(u)))₂` at `ψ(u)` because `ψ' ∘ ψ = id`.
  B's tame chart, tame bundle and sc-smooth `f` are not used.
* `B → A` is not proved: genuine difference of scope.  A's `corollary_3_1_15_preprint` needs neither a tame
  bundle, nor a tame chart, nor an sc-smooth section; A also contains the topological lemma
  `tendsto_of_isCompact_of_tendsto_map`, the `IsScFredholmSection` version, and the local statement
  for sc⁰-contraction germs on a general closed partial quadrant `C̃ ⊆ P`, none of which B addresses.
-/

namespace RoundTrip.V3_15
open Polyfold Set Filter Topology

/-- The project's statement, universes instantiated at `0`. -/
def A : Prop :=
  (type_of% @Polyfold.corollary_3_1_15_preprint.{0, 0}) ∧
  (type_of% @Polyfold.corollary_3_1_15_section.{0, 0}) ∧
  (type_of% @Polyfold.tendsto_of_isCompact_of_tendsto_map.{0, 0}) ∧
  (type_of% @Polyfold.corollary_3_1_15_local)

theorem A_holds : A :=
  ⟨@Polyfold.corollary_3_1_15_preprint.{0, 0}, @Polyfold.corollary_3_1_15_section.{0, 0},
    @Polyfold.tendsto_of_isCompact_of_tendsto_map.{0, 0}, @Polyfold.corollary_3_1_15_local⟩

/-- B with the project's sc-Fredholm germ (`Bd.IsScFredholmGerm`) in place of the text's
`IsScFredholmGermB`. -/
def B_projGerm : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X),
    IsTameStrongBundle Bd → Bd.IsScSmoothSection f → Bd.IsScFredholmGerm f x₀ →
    IsZeroAt P f x₀ →
      ∀ xs : ℕ → X, (∀ k, IsZeroAt P f (xs k)) → Tendsto xs atTop (𝓝 x₀) →
        ∀ m : ℕ, ∃ K : ℕ, (∀ k ≥ K, xs k ∈ PX.levelSet m) ∧
          ∃ (y : ℕ → PX.levelSet m) (yLim : PX.levelSet m), (yLim : X) = x₀ ∧
            (∀ k ≥ K, (y k : X) = xs k) ∧
            @Tendsto ℕ (PX.levelSet m) y atTop (@nhds _ (PX.levelTopology m) yLim)

/-- **`A → B` with the project's germ notion**: the conclusions agree. -/
theorem A_to_B_projGerm : A → B_projGerm := by
  rintro ⟨hA, -⟩ X _ _ _ PX Y _ _ _ P _ _ Bd f x₀ _ hf hgerm hx₀ xs hxs htend m
  obtain ⟨y₀, hy₀, y, hev, hy⟩ := hA hf.1 hgerm hx₀ hxs htend m
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  refine ⟨K, fun k hk => ?_, y, y₀, hy₀, hK, hy⟩
  rw [← hK k hk]
  exact (y k).2

/-! ### Shrinking a strong bundle chart to `U ∩ r⁻¹(O₀) ∩ O₀` -/

section Shrink

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

lemma shrink_hs (c : StrongBundleChart PX P) (O₀ : Set (c.φ.model.E 0)) :
    c.φ.source ∩ c.φ ⁻¹' O₀ ⊆ c.φ.source := inter_subset_left

lemma shrink_hso (c : StrongBundleChart PX P) {O₀ : Set (c.φ.model.E 0)} (hO₀ : IsOpen O₀) :
    IsOpen (c.φ.source ∩ c.φ ⁻¹' O₀) :=
  c.φ.continuousOn_toFun.isOpen_inter_preimage c.φ.isOpen_source hO₀

lemma shrink_image (c : StrongBundleChart PX P) (O₀ : Set (c.φ.model.E 0)) :
    c.φ '' (c.φ.source ∩ c.φ ⁻¹' O₀) = c.φ.model.O ∩ O₀ := by
  rw [image_inter_preimage, c.φ.image_source]

/-- The image `K` of the restricted chart is also `R((U ∩ r⁻¹(O₀) ∩ O₀) ◁ F)`. -/
lemma shrink_target (c : StrongBundleChart PX P) {O₀ : Set (c.φ.model.E 0)} (hO₀ : IsOpen O₀) :
    c.R '' ((c.restrictBase (shrink_hs c O₀) (shrink_hso c hO₀)).U ×ˢ univ) =
      c.R '' (((c.isRetraction.baseRetraction c.relOpen).restrictIn hO₀).U ×ˢ univ) := by
    ext p
    rw [c.mem_restrict_K_iff, shrink_image]
    constructor
    · rintro ⟨hK, hp1O, hp10⟩
      have hpO : p.1 ∈ StrongRetr.r c.R '' c.U := by rw [c.r_image]; exact hp1O
      have hpU : p.1 ∈ c.U := StrongRetr.mem_U_of_mem_O c.isRetraction hpO
      have hr : StrongRetr.r c.R p.1 = p.1 := StrongRetr.r_eq_self c.isRetraction hpO
      refine ⟨p, ⟨⟨⟨hpU, ?_⟩, hp10⟩, mem_univ _⟩, c.R_eq_self_of_mem_K hK⟩
      show StrongRetr.r c.R p.1 ∈ O₀
      rw [hr]; exact hp10
    · rintro ⟨q, hq, rfl⟩
      have hq1 : q.1 ∈ c.U := hq.1.1.1
      have hfst : (c.R q).1 = StrongRetr.r c.R q.1 := c.isRetraction.apply_fst hq1 q.2
      refine ⟨⟨q, ⟨hq1, mem_univ _⟩, rfl⟩, ?_, ?_⟩
      · rw [hfst]; exact c.r_mem_O hq1
      · rw [hfst]; exact hq.1.1.2

/-- The chart `c` with base domain `V ∩ φ⁻¹(O₀)` and retraction domain `U ∩ r⁻¹(O₀) ∩ O₀`
(`ScRetraction.restrictIn`), `O₀` open: same `Φ` as `c.restrict`, smaller `U`. -/
noncomputable def shrink (c : StrongBundleChart PX P) {O₀ : Set (c.φ.model.E 0)} (hO₀ : IsOpen O₀) :
    StrongBundleChart PX P where
  φ := c.φ.restrict (shrink_hs c O₀) (shrink_hso c hO₀)
  isChart := MPolyfold.IsChart.restrict PX c.isChart _ _
  F := c.F
  U := ((c.isRetraction.baseRetraction c.relOpen).restrictIn hO₀).U
  R := c.R
  relOpen := ((c.isRetraction.baseRetraction c.relOpen).restrictIn hO₀).relOpen
  isRetraction := c.isRetraction.restrictIn c.relOpen hO₀
  base_retract := by
    have h1 := IsStrongBundleRetraction.restrictIn_base_retract c.relOpen c.isRetraction hO₀
    rw [c.base_retract] at h1
    exact h1.trans (shrink_image c O₀).symm
  toPartialEquiv := c.restrictPE (shrink_hs c O₀) (shrink_hso c hO₀)
  source_eq := rfl
  target_eq := shrink_target c hO₀
  continuousOn_toFun := (c.restrict (shrink_hs c O₀) (shrink_hso c hO₀)).continuousOn_toFun
  continuousOn_invFun := (c.restrict (shrink_hs c O₀) (shrink_hso c hO₀)).continuousOn_invFun
  covers := (c.restrict (shrink_hs c O₀) (shrink_hso c hO₀)).covers
  fiber_linear := (c.restrict (shrink_hs c O₀) (shrink_hso c hO₀)).fiber_linear

variable [T2Space Y] [ParacompactSpace Y] in
/-- The shrunk chart is a chart of the bundle (it has the transition maps of `c.restrict`). -/
lemma shrink_isChart {Bd : StrongBundle PX P} {c : StrongBundleChart PX P} (hc : Bd.IsChart c)
    {O₀ : Set (c.φ.model.E 0)} (hO₀ : IsOpen O₀) : Bd.IsChart (shrink c hO₀) :=
  hc.restrict (shrink_hs c O₀) (shrink_hso c hO₀)

end Shrink

/-! ### Restricting a strong bundle isomorphism -/

section IsoRestrict

variable {E F E' F' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)}

theorem isStrongBundleMap_restrict {U U₁ : Set (E 0)} {U' U₁' : Set (E' 0)}
    {Ψ : E 0 × F 0 → E' 0 × F' 0} (hΨ : IsStrongBundleMap U U' Ψ)
    (hU₁ : IsRelOpenInQuadrant E C U₁) (hsub : U₁ ⊆ U)
    (hmaps : MapsTo (IsStrongBundleMap.base Ψ) U₁ U₁') : IsStrongBundleMap U₁ U₁' Ψ where
  mapsTo p hp := by
    refine ⟨?_, mem_univ _⟩
    change (Ψ (p.1, p.2)).1 ∈ U₁'
    rw [hΨ.fst_independent p.1 (hsub hp.1) p.2 0]
    exact hmaps hp.1
  fst_independent u hu := hΨ.fst_independent u (hsub hu)
  fiber_linear u hu := hΨ.fiber_linear u (hsub hu)
  preserves_filtration m k hk u hu := hΨ.preserves_filtration m k hk u (hsub hu)
  isScSmooth_zero := hΨ.isScSmooth_zero.of_subset (hU₁.prod_univ F).isScDomain
    (prod_mono hsub subset_rfl)
  isScSmooth_one := hΨ.isScSmooth_one.of_subset (hU₁.prod_univ F.shift).isScDomain
    (prod_mono hsub subset_rfl)

theorem isStrongBundleIso_restrict {U U₁ : Set (E 0)} {U' U₁' : Set (E' 0)}
    {Ψ : E 0 × F 0 → E' 0 × F' 0} {Ψ' : E' 0 × F' 0 → E 0 × F 0}
    (hΨ : IsStrongBundleIso U U' Ψ Ψ') (hU₁ : IsRelOpenInQuadrant E C U₁)
    (hU₁' : IsRelOpenInQuadrant E' C' U₁') (hsub : U₁ ⊆ U) (hsub' : U₁' ⊆ U')
    (hmaps : MapsTo (IsStrongBundleMap.base Ψ) U₁ U₁')
    (hmaps' : MapsTo (IsStrongBundleMap.base Ψ') U₁' U₁) : IsStrongBundleIso U₁ U₁' Ψ Ψ' where
  toFun := isStrongBundleMap_restrict hΨ.toFun hU₁ hsub hmaps
  invFun := isStrongBundleMap_restrict hΨ.invFun hU₁' hsub' hmaps'
  left_inv p hp := hΨ.left_inv p ⟨hsub hp.1, mem_univ _⟩
  right_inv p hp := hΨ.right_inv p ⟨hsub' hp.1, mem_univ _⟩

/-- `{u' ∈ U' | g(u') ∈ V}` is relatively open for `g` continuous on `U'` with values in `C`. -/
lemma relOpen_preimage {U' : Set (E' 0)} (hU' : IsRelOpenInQuadrant E' C' U') {g : E' 0 → E 0}
    (hg : ContinuousOn g U') {V : Set (E 0)} (hV : ∃ O : Set (E 0), IsOpen O ∧ V = O ∩ C)
    (hgC : MapsTo g U' C) : IsRelOpenInQuadrant E' C' {u' ∈ U' | g u' ∈ V} := by
  obtain ⟨O, hO, rfl⟩ := hV
  obtain ⟨O', hO', hU'eq⟩ := hU'.relOpen
  obtain ⟨Wv, hWv, hWeq⟩ := continuousOn_iff'.1 hg O hO
  refine ⟨hU'.isPartialQuadrant, Wv ∩ O', hWv.inter hO', ?_⟩
  ext u'
  constructor
  · rintro ⟨hu', hgO, -⟩
    have h1 : u' ∈ g ⁻¹' O ∩ U' := ⟨hgO, hu'⟩
    rw [hWeq] at h1
    have h2 : u' ∈ O' ∩ C' := hU'eq ▸ hu'
    exact ⟨⟨h1.1, h2.1⟩, h2.2⟩
  · rintro ⟨⟨hW, hO'u⟩, hC'⟩
    have hu' : u' ∈ U' := by rw [hU'eq]; exact ⟨hO'u, hC'⟩
    have h1 : u' ∈ Wv ∩ U' := ⟨hW, hu'⟩
    rw [← hWeq] at h1
    exact ⟨hu', h1.1, hgC hu'⟩

end IsoRestrict

/-! ### The standard quadrant `[0,∞)ᵏ ⊕ ℝⁿ⁻ᵏ` is a partial quadrant -/

lemma isPartialQuadrant_stdQuad {n kq : ℕ} (hkq : kq ≤ n) :
    IsPartialQuadrant (ScBanach.const (Fin n → ℝ)) (stdQuad n kq) := by
  let ℓ : (Fin n → ℝ) →ₗ[ℝ] (Fin kq → ℝ) :=
    LinearMap.pi fun j => LinearMap.proj (Fin.castLE hkq j)
  have hℓ : ∀ a j, ℓ a j = a (Fin.castLE hkq j) := fun _ _ => rfl
  have hsurj : Function.Surjective ℓ := by
    intro b
    refine ⟨fun i => if h : (i : ℕ) < kq then b ⟨i, h⟩ else 0, ?_⟩
    funext j
    rw [hℓ]
    simp [Fin.castLE, j.2]
  have heq : stdQuad n kq = quadC ℓ := by
    ext a
    change (∀ i : Fin n, (i : ℕ) < kq → 0 ≤ a i) ↔ ∀ j, 0 ≤ ℓ a j
    constructor
    · intro h j
      rw [hℓ]; exact h _ j.2
    · intro h i hi
      have := h ⟨i, hi⟩
      rwa [hℓ] at this
  rw [heq]
  exact isPartialQuadrant_quadC ℓ hsurj

/-! ### Condition (3): B's bijection with a bound is a topological isomorphism of kernels -/

lemma kerEquiv_of_bijOn {E₀ F₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] (A : E₀ →L[ℝ] E₀) (Rh : F₀ →L[ℝ] F₀)
    (L : E₀ →L[ℝ] F₀) (a : E₀ → E₀) (ρ0 : F₀ → F₀) (hA : ∀ v, A v = a v)
    (hRh : ∀ h, Rh h = ρ0 h) (hbij : BijOn L {v | a v = 0} {h | ρ0 h = 0}) (cst : ℝ)
    (hc : ∀ v, a v = 0 → ‖v‖ ≤ cst * ‖L v‖) :
    ∃ Φ : LinearMap.ker (A : E₀ →ₗ[ℝ] E₀) ≃L[ℝ] LinearMap.ker (Rh : F₀ →ₗ[ℝ] F₀),
      ∀ v : LinearMap.ker (A : E₀ →ₗ[ℝ] E₀), ((Φ v : LinearMap.ker (Rh : F₀ →ₗ[ℝ] F₀)) : F₀) =
        L (v : E₀) := by
  have hkA : ∀ v : E₀, v ∈ LinearMap.ker (A : E₀ →ₗ[ℝ] E₀) ↔ a v = 0 := fun v => by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hA]
  have hkR : ∀ h : F₀, h ∈ LinearMap.ker (Rh : F₀ →ₗ[ℝ] F₀) ↔ ρ0 h = 0 := fun h => by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hRh]
  let f : LinearMap.ker (A : E₀ →ₗ[ℝ] E₀) →ₗ[ℝ] LinearMap.ker (Rh : F₀ →ₗ[ℝ] F₀) :=
    (L : E₀ →ₗ[ℝ] F₀).restrict fun v hv => (hkR _).2 (hbij.mapsTo ((hkA v).1 hv))
  have hf : ∀ v, (f v : F₀) = L v := fun _ => rfl
  have hinj : Function.Injective f := fun v w h =>
    Subtype.ext (hbij.injOn ((hkA _).1 v.2) ((hkA _).1 w.2) (by rw [← hf, ← hf, h]))
  have hsurj : Function.Surjective f := fun w => by
    obtain ⟨v, hv, hvw⟩ := hbij.surjOn ((hkR _).1 w.2)
    exact ⟨⟨v, (hkA v).2 hv⟩, Subtype.ext hvw⟩
  let e := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨e.toContinuousLinearEquivOfBounds ‖L‖ cst ?_ ?_, fun v => rfl⟩
  · intro v
    exact L.le_opNorm v
  · intro w
    obtain ⟨v, rfl⟩ := e.surjective w
    rw [e.symm_apply_apply]
    exact hc v ((hkA v).1 v.2)

/-! ### The text's sc-Fredholm germ gives the project's (germ reading) -/

theorem germB_to_germ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {PX : MPolyfold X} {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    {Bd : StrongBundle PX P} {f : X → Y} {x₀ : X} (h : IsScFredholmGermB Bd f x₀) :
    Bd.IsScFredholmGerm f x₀ := by
  obtain ⟨hxs, c, hc, -, hxV, hφ0, g, s, hfill, hsplus, hs0, hconj⟩ := h
  obtain ⟨⟨G₁, hG₁U, hg, Dk, hDk, Dr, hDr, hbij, cst, hcst⟩, h1, h2⟩ := hfill
  obtain ⟨U₀, hU₀, h0U₀, hU₀U, n, kq, N, hkq, W, U', hU', Ψ, Ψ', hΨ, hΨ0, G, Bc, hGU',
    hbasic⟩ := hconj
  obtain ⟨O₀, hO₀, hU₀eq⟩ := hU₀.relOpen
  have hφ0' : c.φ x₀ = 0 := hφ0
  have h0U : (0 : c.φ.model.E 0) ∈ c.U := c.zero_mem_U hxV hφ0'
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0' ▸ c.φ.mapsTo_model x₀ hxV
  have hr0 : StrongRetr.r c.R 0 = 0 :=
    StrongRetr.r_eq_self c.isRetraction (by rw [c.r_image]; exact h0O)
  have h0O₀ : (0 : c.φ.model.E 0) ∈ O₀ := by
    have : (0 : c.φ.model.E 0) ∈ O₀ ∩ c.φ.model.C := hU₀eq ▸ h0U₀
    exact this.1
  have hc' : Bd.IsChart (shrink c hO₀) := shrink_isChart hc hO₀
  have hxV' : x₀ ∈ (shrink c hO₀).φ.source :=
    ⟨hxV, show c.φ x₀ ∈ O₀ by rw [hφ0']; exact h0O₀⟩
  have h0U' : (0 : c.φ.model.E 0) ∈ (shrink c hO₀).U :=
    ⟨⟨h0U, show StrongRetr.r c.R 0 ∈ O₀ by rw [hr0]; exact h0O₀⟩, h0O₀⟩
  have hU'U : (shrink c hO₀).U ⊆ c.U := fun u hu => hu.1.1
  have hU'U₀ : (shrink c hO₀).U ⊆ U₀ := fun u hu => by
    rw [hU₀eq]; exact ⟨hu.2, c.relOpen.subset_quadrant (hU'U hu)⟩
  have hQ : IsQuadrantLike c.φ.model.E c.φ.model.C := c.isQuadrantLike
  have hrel : ∃ O : Set (c.φ.model.E 0), IsOpen O ∧ (shrink c hO₀).U = O ∩ c.φ.model.C :=
    (shrink c hO₀).relOpen.relOpen
  refine ⟨hxs, shrink c hO₀, hc', hxV', hφ0', h0U', g, s, ⟨?_, ?_, ?_⟩, ?_, hs0, ?_⟩
  · -- (1) of the filling
    filter_upwards [h1] with x hx hxO
    exact hx (image_mono hU'U hxO)
  · -- (2) of the filling
    filter_upwards [h2] with y hy hyU hfix
    obtain ⟨u, hu, hyu⟩ := hy (hU'U hyU) hfix
    have hry : StrongRetr.r c.R y = y := by
      rw [← hyu]; exact StrongRetr.r_r c.isRetraction hu
    exact ⟨y, hyU, hry⟩
  · -- the germ and condition (3) of the filling
    let G₁' := G₁.inter (ScNbhdGerm.ofSet hrel h0U')
    have hsub : ∀ m, G₁'.U m ⊆ G₁.U m := fun m x hx => hx.1
    refine ⟨G₁', fun x hx => hx.2, IsScSmoothGerm.mono hQ hsub hg, Dk, hDk.mono hsub, ?_⟩
    have hDr' : IsSc1With (shrink c hO₀).U (StrongRetr.r (shrink c hO₀).R) Dr :=
      hDr.of_subset hU'U
    have h01 : (0 : c.φ.model.E 1) ∈ c.φ.model.E.lvlSet (shrink c hO₀).U 1 := by
      show c.φ.model.E.toBase 1 0 ∈ (shrink c hO₀).U
      rw [map_zero]; exact h0U'
    have hA : scDeriv (shrink c hO₀).U (StrongRetr.r (shrink c hO₀).R) (0 : c.φ.model.E 1) =
        Dr 0 :=
      IsSc1.scDeriv_eqOn hDr' ((shrink c hO₀).relOpen.isScDomain.uniqueDiffWithinAt 1) h01
    exact kerEquiv_of_bijOn _ _ (Dk 0) (Dr 0) (fun h => (c.R (0, h)).2)
      (fun v => DFunLike.congr_fun hA v) (fun _ => rfl) hbij cst hcst
  · -- the sc⁺-germ
    obtain ⟨G₂, -, hs₂⟩ := hsplus
    exact ⟨G₂.inter (ScNbhdGerm.ofSet hrel h0U'), fun x hx => hx.2,
      IsScSmoothGerm.mono hQ (fun m x hx => hx.1) hs₂⟩
  · -- the conjugation, restricted to the shrunk `U`
    have hψ'cont : ContinuousOn (IsStrongBundleMap.base Ψ') U' :=
      (hΨ.invFun.base_isScSmooth hU').isSc1.isSc0.continuousOn_base
    have hψ'C : MapsTo (IsStrongBundleMap.base Ψ') U' c.φ.model.C := fun u' hu' =>
      hU₀.subset_quadrant (hΨ.invFun.base_mem hu')
    have hU₁' := relOpen_preimage hU' hψ'cont hrel hψ'C
    have hψ0 : IsStrongBundleMap.base Ψ 0 = 0 := hΨ0
    have hψ'0 : IsStrongBundleMap.base Ψ' 0 = 0 := hΨ.base_zero' h0U₀ hψ0
    have h0U₁' : (0 : (ScBanach.paramProd (Fin n → ℝ) W) 0) ∈
        {u' ∈ U' | IsStrongBundleMap.base Ψ' u' ∈ (shrink c hO₀).U} :=
      ⟨hψ0 ▸ hΨ.toFun.base_mem h0U₀, by
        show IsStrongBundleMap.base Ψ' 0 ∈ (shrink c hO₀).U
        rw [hψ'0]; exact h0U'⟩
    have hΨr : IsStrongBundleIso (shrink c hO₀).U
        {u' ∈ U' | IsStrongBundleMap.base Ψ' u' ∈ (shrink c hO₀).U} Ψ Ψ' :=
      isStrongBundleIso_restrict hΨ (shrink c hO₀).relOpen hU₁' hU'U₀ (fun u' hu' => hu'.1)
        (fun u hu => by
          refine ⟨hΨ.toFun.base_mem (hU'U₀ hu), ?_⟩
          show IsStrongBundleMap.base Ψ' (IsStrongBundleMap.base Ψ u) ∈ (shrink c hO₀).U
          rw [hΨ.base_base (hU'U₀ hu)]; exact hu)
        (fun u' hu' => hu'.2)
    have hPQ := isPartialQuadrant_stdQuad (n := n) hkq
    refine ⟨Fin n → ℝ, Fin N → ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, W, stdQuad n kq,
      {u' ∈ U' | IsStrongBundleMap.base Ψ' u' ∈ (shrink c hO₀).U}, Ψ, Ψ',
      G.inter (ScNbhdGerm.ofSet hU₁'.relOpen h0U₁'), _, Bc, hPQ, hU₁', hΨr, hψ0,
      fun x hx => hx.2, hbasic.inter hPQ.isQuadrantLike _, ?_⟩
    refine Eventually.of_forall fun u hu => ?_
    have hb : (Ψ' (IsStrongBundleMap.base Ψ u, 0)).1 = u := hΨ.base_base (hU'U₀ hu)
    show (Ψ (u, g u - c.F.toBase 1 (s u))).2 =
      (Ψ ((Ψ' (IsStrongBundleMap.base Ψ u, 0)).1,
        g (Ψ' (IsStrongBundleMap.base Ψ u, 0)).1 -
          c.F.toBase 1 (s (Ψ' (IsStrongBundleMap.base Ψ u, 0)).1))).2
    rw [hb]

/-- **`A → B`**: B's sc-Fredholm germ is one in the project's germ reading (`germB_to_germ`), and
A's `corollary_3_1_15_preprint` then gives B's conclusion (`A_to_B_projGerm`). -/
theorem A_to_B : A → B := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd f x₀ hT hf hgerm hx₀
  exact A_to_B_projGerm hA PX P Bd f x₀ hT hf (germB_to_germ hgerm) hx₀

#rt_check RoundTrip.V3_15.A_to_B [Polyfold.corollary_3_1_15_preprint, Polyfold.corollary_3_1_15_section,
  Polyfold.tendsto_of_isCompact_of_tendsto_map, Polyfold.corollary_3_1_15_local]
#rt_check RoundTrip.V3_15.A_to_B_projGerm [Polyfold.corollary_3_1_15_preprint, Polyfold.corollary_3_1_15_section,
  Polyfold.tendsto_of_isCompact_of_tendsto_map, Polyfold.corollary_3_1_15_local]
#rt_overlap RoundTrip.V3_15.A_to_B [Polyfold.corollary_3_1_15_preprint, Polyfold.corollary_3_1_15_section,
  Polyfold.tendsto_of_isCompact_of_tendsto_map, Polyfold.corollary_3_1_15_local]

end RoundTrip.V3_15
