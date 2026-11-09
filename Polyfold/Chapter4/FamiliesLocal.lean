import Polyfold.Chapter4.LocalStructure
import Polyfold.Chapter3.QuadrantIFT
import Polyfold.Vendor.MilnorSard.Sard

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §4.3,
the finite-dimensional core of the proof of Theorem 4.3.1 (preprint 4.23) *(book 2017: Theorem 4.4; see
`BookConcordance.md`, not checked against the 2017 text)*.

# Sard's theorem on the strata of a partial quadrant, and fibres over regular values

## The text, paraphrased

(Proof of Theorem 4.3.1 (preprint 4.23), in the chart of Theorem 4.2.11 (preprint 4.22).)  `A ∩ F_σ°` is a manifold without boundary
of dimension `dim A − #σ`; Sard's theorem gives a full-measure set `Σ_σ` of regular values of the
projection `p_σ : A ∩ F_σ° → ℝᵐ`, and `Σ = ⋂_σ Σ_σ`.  For `λ ∈ Σ` the fibre is a manifold with
boundary with corners: its tangent space at `z'` is complementary to a space `ξ_{z'}` mapped
isomorphically onto `ℝᵐ` by `Tp_σ(z')`.

## What is formalized

The finite-dimensional model: a finite-dimensional space `V` with linear coordinates
`ℓ : V → ℝⁿ`, the partial quadrant `C = {ℓ ≥ 0}` (`quadC`), a relatively open `U = O ∩ C` and a
map `f : V → F` of class `C^∞` on `U` (in the application `V = T₀A`, `ℓ` the coordinates of the
tame chart, `U` the domain of the graph map `Γ` of Proposition 4.1.9 (preprint 4.9) and `f = P ∘ Γ`).

* The strata: `stratSub ℓ σ = {ℓ_i = 0, i ∈ σ}` (the tangent space of `A ∩ F_σ`), of dimension
  `dim V − #σ` when `ℓ` is onto (`finrank_stratSub`: the dimension count that the proof of
  Theorem 4.3.1 (preprint 4.23) uses and Theorem 4.2.11 (preprint 4.22) does not state), and `zeroSetOf ℓ v`, the faces through `v`.
* **Stratified critical points** (`stratCritSet`): `v ∈ U` at which `Df(v)` restricted to the
  stratum through `v` is not onto — the critical points of the text's `p_σ`, `σ = σ(v)`.
* **Sard's theorem on the strata** (`measure_image_stratCritSet`): `f(stratCritSet)` is a null set
  for every Haar measure; the open strata `{ℓ_i = 0, i ∈ σ; ℓ_j > 0, j ∉ σ}` are open subsets of
  the subspaces `stratSub ℓ σ`, and Milnor's Sard theorem (vendored, `MilnorSard.sard`) applies
  to `f` restricted to each of them.
* **The fibre over a regular value is a manifold with corners** (`exists_fibre_retraction`): at
  a point `v₀ ∈ U` which is not stratified-critical, the kernel `K = ker Df(v₀)` is in good
  position to the partial quadrant `C_{v₀}` with a good complement `Y` inside the stratum
  subspace (`exists_goodComplement_stratSub`), and the implicit function theorem in partial
  quadrants (Theorem 3.8.22 (preprint 3.78), here in its `C^∞` form `theorem_3_8_22_smooth`) describes the fibre near
  `v₀` as the graph of a `C^∞` map `τ : K ∩ C_{v₀} ⊇ V' → Y`.  This gives a `C^∞` retraction `ρ`
  of a relatively open neighbourhood `U'` of `v₀` in `C` onto the fibre `f⁻¹(f(v₀)) ∩ U'`, with
  `range Dρ(v₀) = ker Df(v₀)`.

## What the text leaves implicit, and the choices made

* The text applies Sard to `p_σ` on the open strata `A ∩ F_σ°`.  Their union is all of `A`
  (near a point), and a point of `A` is stratified-regular iff it is a regular point of the
  `p_σ` for its own `σ`; the null set of critical values is therefore `f(stratCritSet)`, which is
  the union over `σ` of the critical values of the `p_σ`.
* "`A_λ` is a smooth manifold with boundary with corners" needs the implicit function theorem at
  boundary points, with the kernel of the derivative in good position to the corner — the
  argument of Lemma 5.26, which the text does not give here.  Theorem 3.8.22 (preprint 3.78) is stated for one
  finite `j` with a `j`-dependent solution; here the `C^∞` version is proved from the same
  construction (the contraction radii do not depend on `j`).
-/

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff

noncomputable section

namespace Polyfold

/-! ### Strata of a partial quadrant -/

section Strata

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (ℓ : V →ₗ[ℝ] (Fin n → ℝ))

/-- The partial quadrant `C = {v | ℓ_i(v) ≥ 0 for all i}`. -/
def quadC : Set V := {v | ∀ i, 0 ≤ ℓ v i}

/-- The stratum subspace `{v | ℓ_i(v) = 0 for i ∈ σ}` (the tangent space of the intersection of
the faces `F_i`, `i ∈ σ`). -/
def stratSub (σ : Finset (Fin n)) : Submodule ℝ V where
  carrier := {v | ∀ i ∈ σ, ℓ v i = 0}
  add_mem' := fun {a b} ha hb i hi => by
    rw [map_add, Pi.add_apply, ha i hi, hb i hi, add_zero]
  zero_mem' := fun i _ => by rw [map_zero, Pi.zero_apply]
  smul_mem' := fun c v hv i hi => by rw [map_smul, Pi.smul_apply, hv i hi, smul_zero]

lemma mem_stratSub {σ : Finset (Fin n)} {v : V} : v ∈ stratSub ℓ σ ↔ ∀ i ∈ σ, ℓ v i = 0 :=
  Iff.rfl

/-- `σ(v) = {i | ℓ_i(v) = 0}`: the faces through `v`. -/
def zeroSetOf (v : V) : Finset (Fin n) := Finset.univ.filter fun i => ℓ v i = 0

lemma mem_zeroSetOf {v : V} {i : Fin n} : i ∈ zeroSetOf ℓ v ↔ ℓ v i = 0 := by
  simp [zeroSetOf]

lemma mem_stratSub_zeroSetOf (v : V) : v ∈ stratSub ℓ (zeroSetOf ℓ v) :=
  fun _ hi => (mem_zeroSetOf ℓ).1 hi

/-- **The dimension count** `dim(A ∩ F_σ) = dim A − #σ` (in the model: the stratum subspace of
`σ` has codimension `#σ` when the coordinates are onto). -/
theorem finrank_stratSub [FiniteDimensional ℝ V] (hℓ : Surjective ℓ) (σ : Finset (Fin n)) :
    finrank ℝ (stratSub ℓ σ) + σ.card = finrank ℝ V := by
  classical
  -- `stratSub ℓ σ` is the kernel of `v ↦ (ℓ_i v)_{i ∈ σ}`, which is onto `ℝ^σ`
  set L : V →ₗ[ℝ] (σ → ℝ) := (LinearMap.pi fun i : σ => (LinearMap.proj (i : Fin n)).comp ℓ)
    with hL
  have hker : LinearMap.ker L = stratSub ℓ σ := by
    ext v
    simp only [LinearMap.mem_ker, hL, mem_stratSub]
    constructor
    · intro h i hi
      have := congrFun h ⟨i, hi⟩
      simpa using this
    · intro h
      funext i
      simpa using h i i.2
  have hsurj : Surjective L := by
    intro b
    obtain ⟨v, hv⟩ := hℓ (fun i => if h : i ∈ σ then b ⟨i, h⟩ else 0)
    refine ⟨v, funext fun i => ?_⟩
    simp [hL, hv, i.2]
  have := LinearMap.finrank_range_add_finrank_ker L
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe, hker] at this
  omega

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Stratified critical points** of `f` on `U`: the points `v ∈ U` at which the derivative of
`f`, restricted to the stratum subspace through `v`, is not onto (the critical points of the
text's `p_σ : A ∩ F_σ° → ℝᵐ`, `σ = σ(v)`). -/
def stratCritSet (f : V → F) (U : Set V) : Set V :=
  {v ∈ U | ¬ Surjective ((fderivWithin ℝ f U v).comp (stratSub ℓ (zeroSetOf ℓ v)).subtypeL)}

/-- **Sard's theorem on the strata** (the text: "Using Sard's theorem we find a subset `Σ_σ` of
regular values of `p_σ` having full measure"): for `f` of class `C^∞` on a relatively open subset
`U = O ∩ C` of the partial quadrant `C = {ℓ ≥ 0}`, the stratified critical values `f(stratCritSet)`
form a null set for every Haar measure `μ`.  *Proof*: a stratified critical point `v` with
`σ = σ(v)` is a critical point of the restriction of `f` to the open subset
`{k ∈ O | ℓ_i k = 0 (i ∈ σ), ℓ_j k > 0 (j ∉ σ)}` of the subspace `stratSub ℓ σ` (on which `f` is
`C^∞` and its derivative is `Df(v)` restricted), and Sard's theorem (`MilnorSard.sard`) applies to
each of the finitely many strata. -/
theorem measure_image_stratCritSet [FiniteDimensional ℝ V] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure] {O : Set V}
    (hO : IsOpen O) {f : V → F} (hf : ContDiffOn ℝ ∞ f (O ∩ quadC ℓ)) :
    μ (f '' stratCritSet ℓ f (O ∩ quadC ℓ)) = 0 := by
  set U := O ∩ quadC ℓ with hU
  have hℓc : Continuous ℓ := LinearMap.continuous_of_finiteDimensional ℓ
  -- the open strata, as subsets of the stratum subspaces
  set S : (σ : Finset (Fin n)) → Set (stratSub ℓ σ) :=
    fun σ => {k | (k : V) ∈ O ∧ ∀ j, j ∉ σ → 0 < ℓ k j} with hS
  have hSo : ∀ σ, IsOpen (S σ) := by
    intro σ
    refine (hO.preimage continuous_subtype_val).inter
      (?_ : IsOpen {k : stratSub ℓ σ | ∀ j, j ∉ σ → 0 < ℓ k j})
    have : {k : stratSub ℓ σ | ∀ j, j ∉ σ → 0 < ℓ k j} =
        ⋂ j, {k : stratSub ℓ σ | j ∉ σ → 0 < ℓ k j} := by ext; simp
    rw [this]
    refine isOpen_iInter_of_finite fun j => ?_
    by_cases hj : j ∈ σ
    · simp [hj]
    · simp only [hj, not_false_eq_true, forall_const]
      exact isOpen_lt continuous_const
        ((continuous_apply j).comp (hℓc.comp continuous_subtype_val))
  have hSU : ∀ σ, MapsTo (stratSub ℓ σ).subtypeL (S σ) U := by
    intro σ k hk
    refine ⟨hk.1, fun i => ?_⟩
    by_cases hi : i ∈ σ
    · change 0 ≤ ℓ k i
      rw [k.2 i hi]
    · exact (hk.2 i hi).le
  have hcd : ∀ σ, ContDiffOn ℝ ∞ (f ∘ (stratSub ℓ σ).subtypeL) (S σ) := fun σ =>
    hf.comp (stratSub ℓ σ).subtypeL.contDiff.contDiffOn (hSU σ)
  -- every stratified critical value is a critical value of one of the restrictions
  have hsub : f '' stratCritSet ℓ f U ⊆ ⋃ σ : Finset (Fin n),
      (f ∘ (stratSub ℓ σ).subtypeL) '' MilnorSard.Sard.critSet (f ∘ (stratSub ℓ σ).subtypeL)
        (S σ) := by
    rintro _ ⟨v, hv, rfl⟩
    set σ := zeroSetOf ℓ v with hσ
    set k : stratSub ℓ σ := ⟨v, mem_stratSub_zeroSetOf ℓ v⟩ with hk
    have hkS : k ∈ S σ := by
      refine ⟨hv.1.1, fun j hj => ?_⟩
      have hne : ℓ v j ≠ 0 := fun h => hj ((mem_zeroSetOf ℓ).2 h)
      exact lt_of_le_of_ne (hv.1.2 j) hne.symm
    have hdiff : HasFDerivWithinAt f (fderivWithin ℝ f U v) U v :=
      ((hf.differentiableOn (by simp)) v hv.1).hasFDerivWithinAt
    have hcomp : HasFDerivAt (f ∘ (stratSub ℓ σ).subtypeL)
        ((fderivWithin ℝ f U v).comp (stratSub ℓ σ).subtypeL) k :=
      (hdiff.comp k (stratSub ℓ σ).subtypeL.hasFDerivWithinAt (hSU σ)).hasFDerivAt
        ((hSo σ).mem_nhds hkS)
    refine mem_iUnion.2 ⟨σ, k, ⟨hkS, ?_⟩, rfl⟩
    rw [hcomp.fderiv]
    exact hv.2
  refine measure_mono_null hsub (measure_iUnion_null fun σ => ?_)
  exact MilnorSard.sard μ (hSo σ) (hcd σ)

end Strata


/-! ### Theorem 3.8.22 (preprint 3.78) in the `C^∞` form -/

section SmoothIFT

variable {K Y : Type} [NormedAddCommGroup K] [NormedSpace ℝ K] [FiniteDimensional ℝ K]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] {Cp Up : Set (K × Y)}
  {B : K × Y → Y}

/-- **Theorem 3.8.22 (preprint 3.78) in the normalized form, `C^∞`**: if the data of the proof of Theorem 3.8.22 (preprint 3.78) hold
for every `j ≥ 1` (`B` of class `C^∞`), one solution `τ` is `C^j` for every `j`.  The radii of
Lemmas 3.8.23–3.8.24 (preprint 3.79–3.80) (`ContractionData.exists_radii`) and the fixed point `τ(k)` do not depend on
`j`; only the regularity statement `Radii.contDiffOn_τ` does. -/
theorem ContractionData.exists_solution_smooth (h : ∀ j : ℕ, 1 ≤ j → ContractionData Cp Up B j) :
    ∃ (V' : Set K) (τ : K → Y) (ε σ : ℝ),
      (∃ O : Set K, IsOpen O ∧ V' = O ∩ {k | ((k, 0) : K × Y) ∈ Cp}) ∧ (0 : K) ∈ V' ∧
      ContDiffOn ℝ ∞ τ V' ∧ τ 0 = 0 ∧ fderivWithin ℝ τ V' 0 = 0 ∧
      (∀ k ∈ V', (k, τ k) ∈ Up ∧ B (k, τ k) = τ k) ∧
      0 < ε ∧ 0 < σ ∧ (∀ k ∈ V', ‖k‖ ≤ ε → ‖τ k‖ ≤ σ) ∧
      (∀ k ∈ V', ‖k‖ ≤ ε → ∀ y : Y, ‖y‖ ≤ σ → (k, y) ∈ Up → B (k, y) = y → y = τ k) := by
  have h1 := h 1 le_rfl
  obtain ⟨S⟩ := h1.exists_radii
  refine ⟨S.V₀, S.τ h1, S.a, S.b, ⟨Metric.ball 0 S.a, Metric.isOpen_ball, ?_⟩, S.zero_mem_V₀ h1,
    ?_, S.τ_zero h1, ?_, fun k hk => ⟨S.R_sub_U (S.τ_mem_R h1 hk), S.τ_fixed h1 hk⟩,
    S.a_pos, S.b_pos, fun k hk _ => ?_, fun k hk _ y hy hyU hfix => ?_⟩
  · ext k; simp [Radii.V₀, Metric.mem_ball]
  · rw [contDiffOn_infty]
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact (S.contDiffOn_τ h1).of_le (by norm_num)
    · exact S.contDiffOn_τ (h j hj)
  · rw [S.fderivWithin_τ h1 (S.zero_mem_V₀ h1), S.τ_zero h1]
    change (Radii.M Up B (0, 0)).comp (Radii.D₁ Up B (0, 0)) = 0
    have : Radii.D₁ Up B ((0 : K), (0 : Y)) = 0 := by
      change (fderivWithin ℝ B Up 0).comp _ = 0
      rw [h1.deriv_zero, ContinuousLinearMap.zero_comp]
    rw [this, ContinuousLinearMap.comp_zero]
  · calc ‖S.τ h1 k‖ ≤ S.ε / 2 * ‖k‖ := S.norm_τ_le h1 hk
      _ ≤ S.ε * S.a := by nlinarith [S.ε_pos, norm_nonneg k, hk.1.le]
      _ ≤ S.b := S.εa_le
  · have hyC : (k, y) ∈ Cp := by
      obtain ⟨O, -, hU⟩ := h1.relOpen
      rw [hU] at hyU
      exact hyU.2
    exact S.eq_τ h1 hk ⟨hk.1.le, hy, hyC⟩ hfix

end SmoothIFT

section SmoothIFT378

variable {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Theorem 3.8.22 (preprint 3.78), the `C^∞` form** (`theorem_3_8_22` with `f` of class `C^∞`; the solution `τ` is
then `C^∞`, not only `C^j` for one `j`).  The proof is that of `theorem_3_8_22`, with
`ContractionData.exists_solution_smooth` in place of `ContractionData.exists_solution`. -/
theorem theorem_3_8_22_smooth {C U : Set V} (hU : IsRelOpenInQuadrant (ScBanach.const V) C U)
    (h0 : (0 : V) ∈ U) {f : V → F} (hf : ContDiffOn ℝ ∞ f U) (hf0 : f 0 = 0)
    (hsurj : Function.Surjective (fderivWithin ℝ f U 0)) {K Y : Submodule ℝ V}
    (hK : K = LinearMap.ker (fderivWithin ℝ f U 0 : V →ₗ[ℝ] F))
    (hKC : IsInGoodPosition (ScBanach.const V) C K)
    (hY : IsGoodComplement (ScBanach.const V) C K Y) :
    ∃ (V' : Set K) (τ : K → Y) (ε σ : ℝ),
      (∃ O : Set K, IsOpen O ∧ V' = O ∩ Subtype.val ⁻¹' C) ∧ (0 : K) ∈ V' ∧
      ContDiffOn ℝ ∞ τ V' ∧ τ 0 = 0 ∧ fderivWithin ℝ τ V' 0 = 0 ∧
      (∀ k ∈ V', (k : V) + τ k ∈ U ∧ f ((k : V) + τ k) = 0) ∧
      0 < ε ∧ 0 < σ ∧ (∀ k ∈ V', ‖k‖ ≤ ε → ‖τ k‖ ≤ σ) ∧
      (∀ k ∈ V', ‖k‖ ≤ ε → ∀ y ∈ Y, ‖y‖ ≤ σ → (k : V) + y ∈ U → f ((k : V) + y) = 0 →
        y = τ k) := by
  classical
  set L : V →L[ℝ] F := fderivWithin ℝ f U 0 with hL
  have hKY : IsCompl K Y := hY.isCompl
  -- the identification `K × Y ≅ V`
  let add : (K × Y) ≃L[ℝ] V := (Submodule.prodEquivOfIsCompl K Y hKY).toContinuousLinearEquiv
  have hadd : ∀ p : K × Y, add p = (p.1 : V) + p.2 := fun p => by
    change (Submodule.prodEquivOfIsCompl K Y hKY).toContinuousLinearEquiv p = _
    rw [LinearEquiv.coe_toContinuousLinearEquiv', Submodule.coe_prodEquivOfIsCompl']
  have hadd' : ∀ p : K × Y, (add : K × Y →L[ℝ] V) p = (p.1 : V) + p.2 := fun p => hadd p
  -- `L|_Y : Y → F` is an isomorphism
  have hLK : ∀ k : K, L k = 0 := fun k => by
    have : (k : V) ∈ LinearMap.ker (L : V →ₗ[ℝ] F) := hK ▸ k.2
    exact LinearMap.mem_ker.1 this
  have hinj : Function.Injective (L ∘ₗ Y.subtype : Y →ₗ[ℝ] F) := by
    intro y y' hyy'
    have h1 : L ((y : V) - y') = 0 := by
      rw [map_sub]; exact sub_eq_zero.2 hyy'
    have h2 : ((y : V) - y') ∈ K := by rw [hK]; exact LinearMap.mem_ker.2 h1
    have h3 : ((y : V) - y') ∈ Y := Y.sub_mem y.2 y'.2
    have h4 : ((y : V) - y') = 0 := by
      have := hKY.disjoint.le_bot ⟨h2, h3⟩
      simpa using this
    exact Subtype.ext (sub_eq_zero.1 h4)
  have hsurjY : Function.Surjective (L ∘ₗ Y.subtype : Y →ₗ[ℝ] F) := by
    intro z
    obtain ⟨x, hx⟩ := hsurj z
    have hx' : x ∈ K ⊔ Y := by rw [hKY.sup_eq_top]; trivial
    obtain ⟨k, hk, y, hy, rfl⟩ := Submodule.mem_sup.1 hx'
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [map_add, hLK ⟨k, hk⟩, zero_add] at hx
    exact hx
  let LY : Y ≃L[ℝ] F := (LinearEquiv.ofBijective _ ⟨hinj, hsurjY⟩).toContinuousLinearEquiv
  have hLY : ∀ y : Y, LY y = L y := fun y => rfl
  set Linv : F →L[ℝ] Y := (LY.symm : F →L[ℝ] Y) with hLinv
  have hLinvL : ∀ y : Y, Linv (L y) = y := fun y => by
    rw [← hLY]; exact LY.symm_apply_apply y
  -- the normalized map `B(k, y) = y − L⁻¹ f(k + y)`
  set Cp : Set (K × Y) := add ⁻¹' C with hCp
  set Up : Set (K × Y) := add ⁻¹' U with hUp
  set B : K × Y → Y := fun p => p.2 - Linv (f (add p)) with hB
  obtain ⟨O, hO, hUO⟩ := hU.relOpen
  have hCconv : Convex ℝ C := hU.isPartialQuadrant.convex
  have hCint : (interior C).Nonempty := by
    have := hU.isPartialQuadrant.interior_lvlSet_nonempty 0
    rwa [ScBanach.lvlSet_const] at this
  have hCpconv : Convex ℝ Cp := hCconv.linear_preimage (add : K × Y →ₗ[ℝ] V)
  have hCpint : (interior Cp).Nonempty := by
    have hpre : (add : K × Y → V) ⁻¹' interior C = interior (add ⁻¹' C) := by
      simpa using add.toHomeomorph.preimage_interior C
    rw [hCp, ← hpre]
    exact hCint.preimage add.surjective
  have hUpeq : Up = add ⁻¹' O ∩ Cp := by rw [hUp, hCp, hUO, preimage_inter]
  have h0Up : (0 : K × Y) ∈ Up := by
    change add 0 ∈ U
    rw [map_zero]; exact h0
  have hUpUD : UniqueDiffWithinAt ℝ Up 0 := by
    rw [hUpeq, inter_comm]
    refine (uniqueDiffWithinAt_convex hCpconv hCpint (subset_closure ?_)).inter
      ((hO.preimage add.continuous).mem_nhds ?_)
    · have := h0Up; rw [hUpeq] at this; exact this.2
    · have := h0Up; rw [hUpeq] at this; exact this.1
  have hBcd : ContDiffOn ℝ ∞ B Up := by
    have h1 : ContDiffOn ℝ ∞ (f ∘ add) Up :=
      hf.comp (add : K × Y →L[ℝ] V).contDiff.contDiffOn fun p hp => hp
    exact contDiff_snd.contDiffOn.sub (h1.continuousLinearMap_comp Linv)
  have hLf : HasFDerivWithinAt f L U (add 0) := by
    rw [map_zero]
    exact ((hf.differentiableOn (by simp)) 0 h0).hasFDerivWithinAt
  have hBderiv : HasFDerivWithinAt B
      (ContinuousLinearMap.snd ℝ K Y - Linv.comp (L.comp (add : K × Y →L[ℝ] V))) Up 0 := by
    refine hasFDerivWithinAt_snd.sub ?_
    exact Linv.hasFDerivAt.comp_hasFDerivWithinAt (x := (0 : K × Y))
      (hLf.comp (0 : K × Y) (add : K × Y →L[ℝ] V).hasFDerivWithinAt fun p hp => hp)
  have hBderiv0 :
      ContinuousLinearMap.snd ℝ K Y - Linv.comp (L.comp (add : K × Y →L[ℝ] V)) = 0 := by
    refine ContinuousLinearMap.ext fun p => ?_
    simp only [sub_apply, ContinuousLinearMap.coe_snd', ContinuousLinearMap.comp_apply, zero_apply]
    rw [hadd', map_add, hLK, zero_add, hLinvL, sub_self]
  have hdata : ∀ j : ℕ, 1 ≤ j → ContractionData Cp Up B j := fun j hj =>
    { convex := hCpconv
      interior_nonempty := hCpint
      relOpen := ⟨add ⁻¹' O, hO.preimage add.continuous, hUpeq⟩
      zero_mem_U := h0Up
      one_le := hj
      contDiffOn := hBcd.of_le (by exact_mod_cast le_top)
      B_zero := by
        change (0 : K × Y).2 - Linv (f (add 0)) = 0
        rw [map_zero, hf0, map_zero]; simp
      deriv_zero := by rw [hBderiv.fderivWithin hUpUD, hBderiv0]
      good := by
        obtain ⟨ε, hε, hgood⟩ := hY.exists_eps
        refine ⟨ε, hε, fun k y hy => ?_⟩
        have := hgood k k.2 y y.2 hy
        change add (k, 0) ∈ C ↔ add (k, y) ∈ C
        rw [hadd, hadd]
        simpa using this
      interior_K_nonempty := by
        have : {k : K | ((k, 0) : K × Y) ∈ Cp} = Subtype.val ⁻¹' C := by
          ext k
          change add (k, 0) ∈ C ↔ _
          rw [hadd]; simp
        rw [this]; exact hKC.interior_nonempty }
  obtain ⟨V', τ, ε, σ, ⟨O', hO', hV'⟩, h0V', hτcd, hτ0, hDτ0, hsol, hε, hσ, hbound, huniq⟩ :=
    ContractionData.exists_solution_smooth hdata
  have hCK : {k : K | ((k, 0) : K × Y) ∈ Cp} = Subtype.val ⁻¹' C := by
    ext k
    change add (k, 0) ∈ C ↔ _
    rw [hadd]; simp
  have hfix_iff : ∀ (k : K) (y : Y), B (k, y) = y ↔ f ((k : V) + y) = 0 := fun k y => by
    change y - Linv (f (add (k, y))) = y ↔ _
    rw [hadd, sub_eq_self]
    constructor
    · intro h
      have h2 : LY (Linv (f ((k : V) + y))) = f ((k : V) + y) := LY.apply_symm_apply _
      rw [h, map_zero] at h2
      exact h2.symm
    · intro h; rw [h, map_zero]
  refine ⟨V', τ, ε, σ, ⟨O', hO', by rw [hV', hCK]⟩, h0V', hτcd, hτ0, hDτ0, fun k hk => ?_, hε, hσ,
    hbound, fun k hk hkε y hy hyσ hyU hfy => ?_⟩
  · obtain ⟨h1, h2⟩ := hsol k hk
    refine ⟨?_, (hfix_iff k (τ k)).1 h2⟩
    have : add (k, τ k) ∈ U := h1
    rwa [hadd] at this
  · have := huniq k hk hkε ⟨y, hy⟩ hyσ (by show add (k, ⟨y, hy⟩) ∈ U; rw [hadd]; exact hyU)
      ((hfix_iff k ⟨y, hy⟩).2 hfy)
    exact congrArg Subtype.val this

end SmoothIFT378


/-! ### Fibres over stratified regular values -/

section Fibre

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} (ℓ : V →ₗ[ℝ] (Fin n → ℝ))

/-- The partial quadrant `{ℓ_i ≥ 0, i ∈ σ}` (for `σ = σ(v)`, the quadrant `C_v` of Definition 2.5.1 (preprint 2.33)
at `v`). -/
def quadAt (σ : Finset (Fin n)) : Set V := {v | ∀ i ∈ σ, 0 ≤ ℓ v i}

variable {ℓ} in
/-- For onto coordinates `ℓ` with a linear section `s`, the linear isomorphism
`v ↦ (ℓ v, v − s(ℓ v)) : V ≅ ℝⁿ × ker ℓ` (the presentation of `quadC ℓ`, as in `degIndex_slice`). -/
def sliceEquiv (s : (Fin n → ℝ) →ₗ[ℝ] V) (hs : ∀ a, ℓ (s a) = a) :
    V ≃ₗ[ℝ] (Fin n → ℝ) × LinearMap.ker ℓ where
  toFun u := (ℓ u, ⟨u - s (ℓ u), by rw [LinearMap.mem_ker, map_sub, hs, sub_self]⟩)
  map_add' u w := by
    refine Prod.ext (map_add _ _ _) (Subtype.ext ?_)
    change (u + w) - s (ℓ (u + w)) = (u - s (ℓ u)) + (w - s (ℓ w))
    rw [map_add, map_add]
    abel
  map_smul' c u := by
    refine Prod.ext (map_smul _ _ _) (Subtype.ext ?_)
    change c • u - s (ℓ (c • u)) = c • (u - s (ℓ u))
    rw [map_smul, map_smul, smul_sub]
  invFun p := s p.1 + p.2
  left_inv u := by simp
  right_inv p := by
    have h0 : ℓ (p.2 : V) = 0 := p.2.2
    refine Prod.ext ?_ (Subtype.ext ?_)
    · change ℓ (s p.1 + p.2) = p.1
      rw [map_add, hs, h0, add_zero]
    · change s p.1 + (p.2 : V) - s (ℓ (s p.1 + p.2)) = p.2
      rw [map_add, hs, h0, add_zero]
      abel

/-- `quadC ℓ` is a partial quadrant of `V` (constant sc-structure) when `ℓ` is onto. -/
theorem isPartialQuadrant_quadC (hℓ : Surjective ℓ) :
    IsPartialQuadrant (ScBanach.const V) (quadC ℓ) := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective ℓ (LinearMap.range_eq_top.2 hℓ)
  have hs' : ∀ a, ℓ (s a) = a := fun a => congrArg (fun f => f a) hs
  exact ⟨n, ScBanach.const (LinearMap.ker ℓ), scIsoOfLinearEquiv (sliceEquiv s hs'), by
    ext v; rfl⟩

/-- `quadAt ℓ σ(v₀)`, the quadrant `C_{v₀}`, is a partial quadrant of `V` when `ℓ` is onto. -/
theorem isPartialQuadrant_quadAt (hℓ : Surjective ℓ) (v₀ : V) :
    IsPartialQuadrant (ScBanach.const V) (quadAt ℓ (zeroSetOf ℓ v₀)) := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective ℓ (LinearMap.range_eq_top.2 hℓ)
  have hs' : ∀ a, ℓ (s a) = a := fun a => congrArg (fun f => f a) hs
  set T := scIsoOfLinearEquiv (sliceEquiv s hs') with hT
  have : quadAt ℓ (zeroSetOf ℓ v₀) = partialQuadrantAtWith T v₀ := by
    ext v
    change (∀ i ∈ zeroSetOf ℓ v₀, 0 ≤ ℓ v i) ↔ ∀ i, ℓ v₀ i = 0 → 0 ≤ ℓ v i
    simp only [mem_zeroSetOf]
  rw [this]
  exact isPartialQuadrant_partialQuadrantAtWith T v₀

omit [FiniteDimensional ℝ V] in
lemma convex_quadC : Convex ℝ (quadC ℓ) := by
  intro v hv w hw a b ha hb _ i
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha (hv i)) (mul_nonneg hb (hw i))

lemma interior_quadC_nonempty (hℓ : Surjective ℓ) : (interior (quadC ℓ)).Nonempty := by
  obtain ⟨x, hx⟩ := hℓ (fun _ => 1)
  have hℓc : Continuous ℓ := LinearMap.continuous_of_finiteDimensional ℓ
  have hGo : IsOpen {v : V | ∀ i, 0 < ℓ v i} := by
    have : {v : V | ∀ i, 0 < ℓ v i} = ⋂ i, {v : V | 0 < ℓ v i} := by ext; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const ((continuous_apply i).comp hℓc)
  refine ⟨x, interior_maximal (fun v hv i => (hv i).le) hGo fun i => ?_⟩
  rw [hx]; exact one_pos

lemma uniqueDiffWithinAt_quadC (hℓ : Surjective ℓ) {O : Set V} (hO : IsOpen O) {v : V}
    (hv : v ∈ O ∩ quadC ℓ) : UniqueDiffWithinAt ℝ (O ∩ quadC ℓ) v := by
  rw [inter_comm]
  exact (uniqueDiffWithinAt_convex (convex_quadC ℓ) (interior_quadC_nonempty ℓ hℓ)
    (subset_closure hv.2)).inter (hO.mem_nhds hv.1)

/-- **The kernel at a stratified regular point is in good position** (the argument of Lemma 5.26,
which the proof of Theorem 4.3.1 (preprint 4.23) needs and does not give): if `K + {ℓ_i = 0, i ∈ σ} = V` (for
`K = ker Df(v)`, `σ = σ(v)`: `Df(v)` restricted to the stratum is onto), then `K` is in good
position to the partial quadrant `C_σ = {ℓ_i ≥ 0, i ∈ σ}`, with a closed good complement `Y`
inside the stratum subspace (adding a vector of `Y` changes no coordinate `ℓ_i`, `i ∈ σ`). -/
theorem exists_goodComplement_stratSub (hℓ : Surjective ℓ) {σ : Finset (Fin n)}
    {K : Submodule ℝ V} (hK : K ⊔ stratSub ℓ σ = ⊤) :
    ∃ Y : Submodule ℝ V, Y ≤ stratSub ℓ σ ∧ IsClosed (Y : Set V) ∧
      IsInGoodPosition (ScBanach.const V) (quadAt ℓ σ) K ∧
      IsGoodComplement (ScBanach.const V) (quadAt ℓ σ) K Y := by
  obtain ⟨Y, hYσ, hYc, hKY⟩ :=
    exists_isClosed_isCompl_le (stratSub ℓ σ).closed_of_finiteDimensional hK
  have hgood : IsGoodComplement (ScBanach.const V) (quadAt ℓ σ) K Y := by
    refine ⟨hKY, 1, one_pos, fun x _ p hp _ => ?_⟩
    have hp' := hYσ hp
    change (∀ i ∈ σ, 0 ≤ ℓ x i) ↔ ∀ i ∈ σ, 0 ≤ ℓ (x + p) i
    refine forall₂_congr fun i hi => ?_
    rw [map_add, Pi.add_apply, hp' i hi, add_zero]
  refine ⟨Y, hYσ, hYc, ⟨?_, Y, hgood⟩, hgood⟩
  obtain ⟨x, hx⟩ := hℓ (fun _ => 1)
  have hx' : x ∈ K ⊔ Y := by rw [hKY.sup_eq_top]; trivial
  obtain ⟨k, hk, y, hy, rfl⟩ := Submodule.mem_sup.1 hx'
  have hk1 : ∀ i ∈ σ, ℓ k i = 1 := fun i hi => by
    have := congrFun hx i
    rw [map_add, Pi.add_apply, hYσ hy i hi, add_zero] at this
    exact this
  have hℓc : Continuous ℓ := LinearMap.continuous_of_finiteDimensional ℓ
  have hGo : IsOpen {k' : K | ∀ i ∈ σ, 0 < ℓ k' i} := by
    have : {k' : K | ∀ i ∈ σ, 0 < ℓ k' i} = ⋂ i, {k' : K | i ∈ σ → 0 < ℓ k' i} := by ext; simp
    rw [this]
    refine isOpen_iInter_of_finite fun i => ?_
    by_cases hi : i ∈ σ
    · simp only [hi, forall_const]
      exact isOpen_lt continuous_const ((continuous_apply i).comp (hℓc.comp continuous_subtype_val))
    · simp [hi]
  refine ⟨⟨k, hk⟩, interior_maximal (fun k' hk' i hi => (hk' i hi).le) hGo fun i hi => ?_⟩
  change 0 < ℓ k i
  rw [hk1 i hi]; exact one_pos

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The fibre over a stratified regular point is a manifold with corners, with a smooth
retraction onto it** (the text: "for `λ ∈ Σ` ... `A_λ` is a smooth compact manifold with boundary
with corners"; in the model).  Let `f` be `C^∞` on `U = O ∩ C`, `C = {ℓ ≥ 0}` with `ℓ` onto, and
let `v₀ ∈ U` be stratified-regular (`Df(v₀)` restricted to the stratum through `v₀` is onto).
Then there are an open `O' ∋ v₀`, `O' ⊆ O`, and a `C^∞` map `ρ` on `U' = O' ∩ C` with
`ρ(U') ⊆ U' ∩ f⁻¹(f(v₀))`, `ρ = id` on `U' ∩ f⁻¹(f(v₀))` (so `ρ` is a retraction of `U'` onto the
fibre), and `range Dρ(v₀) = ker Df(v₀)` with `Dρ(v₀) = 1` on `ker Df(v₀)`.
*Proof*: `K = ker Df(v₀)` is in good position to `C_{v₀}` with a good complement `Y` in the
stratum (`exists_goodComplement_stratSub`); Theorem 3.8.22 (preprint 3.78) (`theorem_3_8_22_smooth`) for
`g(w) = f(v₀ + w) − f(v₀)` on the relatively open `U₁ ∋ 0` of `C_{v₀}` (near `0`, `v₀ + C_{v₀}`
and `C` agree) gives the fibre as the graph `{v₀ + k + τ(k)}` of a `C^∞` map `τ : V' → Y`,
`V' ⊆ K ∩ C_{v₀}`, unique for small `k` and `y`; `ρ(v) = v₀ + q(v) + τ(q(v))`, `q(v)` the
projection of `v − v₀` onto `K` along `Y`, on a neighbourhood small enough for the uniqueness
and for `ρ(U') ⊆ U'`; `Dτ(0) = 0` gives `Dρ(v₀) = q`, whose range is `K`. -/
theorem exists_fibre_retraction (hℓ : Surjective ℓ) {O : Set V} (hO : IsOpen O) {f : V → F}
    (hf : ContDiffOn ℝ ∞ f (O ∩ quadC ℓ)) {v₀ : V} (hv₀ : v₀ ∈ O ∩ quadC ℓ)
    (hreg : v₀ ∉ stratCritSet ℓ f (O ∩ quadC ℓ)) :
    ∃ (O' : Set V) (ρ : V → V), IsOpen O' ∧ v₀ ∈ O' ∧ O' ⊆ O ∧
      ContDiffOn ℝ ∞ ρ (O' ∩ quadC ℓ) ∧ MapsTo ρ (O' ∩ quadC ℓ) (O' ∩ quadC ℓ) ∧
      (∀ v ∈ O' ∩ quadC ℓ, f (ρ v) = f v₀) ∧ (∀ v ∈ O' ∩ quadC ℓ, f v = f v₀ → ρ v = v) ∧
      LinearMap.range (fderivWithin ℝ ρ (O' ∩ quadC ℓ) v₀ : V →ₗ[ℝ] V) =
        LinearMap.ker (fderivWithin ℝ f (O ∩ quadC ℓ) v₀ : V →ₗ[ℝ] F) ∧
      ∀ k ∈ LinearMap.ker (fderivWithin ℝ f (O ∩ quadC ℓ) v₀ : V →ₗ[ℝ] F),
        fderivWithin ℝ ρ (O' ∩ quadC ℓ) v₀ k = k := by
  classical
  set U := O ∩ quadC ℓ with hUdef
  set σ₀ := zeroSetOf ℓ v₀ with hσ₀
  set L : V →L[ℝ] F := fderivWithin ℝ f U v₀ with hL
  have hℓc : Continuous ℓ := LinearMap.continuous_of_finiteDimensional ℓ
  have hregs : Surjective (L.comp (stratSub ℓ σ₀).subtypeL) := by
    by_contra h; exact hreg ⟨hv₀, h⟩
  set K : Submodule ℝ V := LinearMap.ker (L : V →ₗ[ℝ] F) with hKdef
  have hsurj : Surjective L := fun y => by
    obtain ⟨k, hk⟩ := hregs y; exact ⟨k, hk⟩
  have hKsup : K ⊔ stratSub ℓ σ₀ = ⊤ := by
    rw [eq_top_iff]; intro x _
    obtain ⟨k, hk⟩ := hregs (L x)
    have hxk : x - k ∈ K := by
      rw [hKdef, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, sub_eq_zero]
      exact hk.symm
    have : x = (x - k) + k := by abel
    rw [this]; exact Submodule.add_mem_sup hxk k.2
  obtain ⟨Y, hYσ, hYc, hKC, hY⟩ := exists_goodComplement_stratSub ℓ hℓ hKsup
  have hv₀σ : ∀ i ∈ σ₀, ℓ v₀ i = 0 := fun i hi => (mem_zeroSetOf ℓ).1 hi
  have hv₀pos : ∀ j, j ∉ σ₀ → 0 < ℓ v₀ j := fun j hj =>
    lt_of_le_of_ne (hv₀.2 j) fun h => hj ((mem_zeroSetOf ℓ).2 h.symm)
  -- the translated problem on `U₁ ⊆ C_{v₀}`
  set C₀ := quadAt ℓ σ₀ with hC₀
  set G₀ : Set V := {w | ∀ j, j ∉ σ₀ → 0 < ℓ (v₀ + w) j} with hG₀
  have hG₀o : IsOpen G₀ := by
    have : G₀ = ⋂ j, {w : V | j ∉ σ₀ → 0 < ℓ (v₀ + w) j} := by ext; simp [hG₀]
    rw [this]
    refine isOpen_iInter_of_finite fun j => ?_
    by_cases hj : j ∈ σ₀
    · simp [hj]
    · simp only [hj, not_false_eq_true, forall_const]
      exact isOpen_lt continuous_const
        ((continuous_apply j).comp (hℓc.comp (continuous_const.add continuous_id)))
  set O₁ : Set V := (fun w => v₀ + w) ⁻¹' O ∩ G₀ with hO₁
  have hO₁o : IsOpen O₁ := (hO.preimage (continuous_const.add continuous_id)).inter hG₀o
  set U₁ := O₁ ∩ C₀ with hU₁
  have hU₁rel : IsRelOpenInQuadrant (ScBanach.const V) C₀ U₁ :=
    ⟨isPartialQuadrant_quadAt ℓ hℓ v₀, O₁, hO₁o, rfl⟩
  have hmap : MapsTo (fun w => v₀ + w) U₁ U := by
    intro w hw
    refine ⟨hw.1.1, fun i => ?_⟩
    by_cases hi : i ∈ σ₀
    · have := hw.2 i hi
      change 0 ≤ ℓ (v₀ + w) i
      rw [map_add, Pi.add_apply, hv₀σ i hi, zero_add]
      exact this
    · exact (hw.1.2 i hi).le
  have h0U₁ : (0 : V) ∈ U₁ := by
    refine ⟨⟨by simpa using hv₀.1, fun j hj => by simpa using hv₀pos j hj⟩, fun i _ => ?_⟩
    simp
  set g : V → F := fun w => f (v₀ + w) - f v₀ with hg
  have hgcd : ContDiffOn ℝ ∞ g U₁ :=
    (hf.comp (contDiff_const.add contDiff_id).contDiffOn hmap).sub contDiffOn_const
  have hg0 : g 0 = 0 := by simp [hg]
  have hDf : HasFDerivWithinAt f L U v₀ :=
    ((hf.differentiableOn (by simp)) v₀ hv₀).hasFDerivWithinAt
  have hDg : HasFDerivWithinAt g L U₁ 0 := by
    have h1 : HasFDerivWithinAt (fun w => v₀ + w) (ContinuousLinearMap.id ℝ V) U₁ 0 :=
      ((hasFDerivAt_id (0 : V)).const_add v₀).hasFDerivWithinAt
    have h2 : HasFDerivWithinAt f L U (v₀ + 0) := by rwa [add_zero]
    have h3 := (h2.comp (0 : V) h1 hmap).sub_const (f v₀)
    rw [ContinuousLinearMap.comp_id] at h3
    exact h3
  have hUD : UniqueDiffWithinAt ℝ U₁ 0 := by
    have := hU₁rel.isScDomain.uniqueDiffWithinAt 0 (0 : V)
      (by rw [ScBanach.lvlSet_const]; exact h0U₁)
    rwa [ScBanach.lvlSet_const] at this
  have hDg0 : fderivWithin ℝ g U₁ 0 = L := hDg.fderivWithin hUD
  obtain ⟨V', τ, ε, σ, ⟨OK, hOK, hV'⟩, h0V', hτ, hτ0, hDτ0, hsol, hε, hσ, -, huniq⟩ :=
    theorem_3_8_22_smooth hU₁rel h0U₁ hgcd hg0 (by rw [hDg0]; exact hsurj) (K := K) (Y := Y)
      (by rw [hDg0]) hKC hY
  -- the projection along `Y`
  obtain ⟨π, hπK, hπY, hπker⟩ := exists_proj_of_isCompl hYc hY.isCompl
  set q : V → K := fun v => π (v - v₀) with hq
  have hqc : Continuous q := π.continuous.comp (continuous_id.sub continuous_const)
  -- radii
  set c := ‖π‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg π
  set r := min ε σ / (1 + c) with hr
  have hr0 : 0 < r := div_pos (lt_min hε hσ) (by positivity)
  have h1cr : (1 + c) * r = min ε σ := by rw [hr]; field_simp
  have hcrε : c * r ≤ ε := by nlinarith [min_le_left ε σ]
  have hcrσ : (1 + c) * r ≤ σ := by rw [h1cr]; exact min_le_right ε σ
  obtain ⟨δ, hδ, hδτ⟩ : ∃ δ > 0, ∀ k ∈ V', ‖k‖ < δ → ‖(τ k : V)‖ < r / 2 := by
    have hτc : ContinuousWithinAt τ V' 0 := hτ.continuousOn 0 h0V'
    rw [Metric.continuousWithinAt_iff] at hτc
    obtain ⟨δ, hδ, h⟩ := hτc (r / 2) (by positivity)
    refine ⟨δ, hδ, fun k hk hkδ => ?_⟩
    have := h hk (by rwa [dist_zero_right])
    rw [dist_eq_norm, hτ0, sub_zero] at this
    exact this
  set δ' := min δ (r / 2) with hδ'
  set G' : Set V := {v | ∀ j, j ∉ σ₀ → 0 < ℓ v j} with hG'
  have hG'o : IsOpen G' := by
    have : G' = ⋂ j, {v : V | j ∉ σ₀ → 0 < ℓ v j} := by ext; simp [hG']
    rw [this]
    refine isOpen_iInter_of_finite fun j => ?_
    by_cases hj : j ∈ σ₀
    · simp [hj]
    · simp only [hj, not_false_eq_true, forall_const]
      exact isOpen_lt continuous_const ((continuous_apply j).comp hℓc)
  set O' : Set V := ((O ∩ G') ∩ Metric.ball v₀ r) ∩ q ⁻¹' (OK ∩ Metric.ball 0 δ') with hO'
  have hO'o : IsOpen O' :=
    ((hO.inter hG'o).inter Metric.isOpen_ball).inter
      ((hOK.inter Metric.isOpen_ball).preimage hqc)
  have hq0 : q v₀ = 0 := by simp [hq]
  have h0OK : (0 : K) ∈ OK := by rw [hV'] at h0V'; exact h0V'.1
  have hv₀O' : v₀ ∈ O' := by
    refine ⟨⟨⟨hv₀.1, hv₀pos⟩, Metric.mem_ball_self hr0⟩, ?_⟩
    rw [mem_preimage, hq0]
    exact ⟨h0OK, Metric.mem_ball_self (lt_min hδ (by positivity))⟩
  -- `v − v₀ ∈ U₁` and `q(v) ∈ V'` on `O' ∩ C`
  have hkey : ∀ v ∈ O' ∩ quadC ℓ, v - v₀ ∈ U₁ ∧ q v ∈ V' := by
    intro v hv
    obtain ⟨⟨⟨⟨hvO, hvG⟩, -⟩, hqOK, -⟩, hvC⟩ := hv
    have hw : v - v₀ ∈ U₁ := by
      refine ⟨⟨by simpa using hvO, fun j hj => by simpa using hvG j hj⟩, fun i hi => ?_⟩
      rw [map_sub, Pi.sub_apply, hv₀σ i hi, sub_zero]
      exact hvC i
    refine ⟨hw, ?_⟩
    rw [hV']
    refine ⟨hqOK, fun i hi => ?_⟩
    have hyY : (v - v₀) - (q v : V) ∈ Y := hπker _ (by
      rw [map_sub, hπK]; exact sub_self _)
    have h1 := hYσ hyY i hi
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h1
    change 0 ≤ ℓ (q v : V) i
    rw [← h1]
    exact hw.2 i hi
  set ρ : V → V := fun v => v₀ + ((q v : V) + (τ (q v) : V)) with hρ
  have hqρ : ∀ v, q (ρ v) = q v := fun v => by
    simp only [hq, hρ, add_sub_cancel_left, map_add, hπK, hπY _ (τ _).2, add_zero]
  have hρmem : ∀ v ∈ O' ∩ quadC ℓ, ρ v ∈ O' ∩ quadC ℓ ∧ f (ρ v) = f v₀ := by
    intro v hv
    have hqv := (hkey v hv).2
    obtain ⟨h1, h2⟩ := hsol (q v) hqv
    have hU := hmap h1
    have hvq : q v ∈ OK ∩ Metric.ball 0 δ' := hv.1.2
    have hnq : ‖q v‖ < δ' := by simpa using hvq.2
    refine ⟨⟨⟨⟨⟨hU.1, fun j hj => h1.1.2 j hj⟩, ?_⟩, ?_⟩, hU.2⟩, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      change ‖v₀ + ((q v : V) + (τ (q v) : V)) - v₀‖ < r
      rw [add_sub_cancel_left]
      calc ‖(q v : V) + (τ (q v) : V)‖ ≤ ‖(q v : V)‖ + ‖(τ (q v) : V)‖ := norm_add_le _ _
        _ < r / 2 + r / 2 := add_lt_add_of_le_of_lt
            ((le_of_lt hnq).trans (min_le_right _ _))
            (hδτ _ hqv (hnq.trans_le (min_le_left _ _)))
        _ = r := by ring
    · rw [mem_preimage, hqρ]; exact hvq
    · have := h2
      simp only [hg, sub_eq_zero] at this
      exact this
  have hfix : ∀ v ∈ O' ∩ quadC ℓ, f v = f v₀ → ρ v = v := by
    intro v hv hfv
    obtain ⟨hw, hqv⟩ := hkey v hv
    have hnw : ‖v - v₀‖ < r := by
      have := hv.1.1.2; rwa [Metric.mem_ball, dist_eq_norm] at this
    have hnq : ‖q v‖ ≤ c * ‖v - v₀‖ := π.le_opNorm _
    have hyY : (v - v₀) - (q v : V) ∈ Y := hπker _ (by rw [map_sub, hπK]; exact sub_self _)
    have hy := huniq (q v) hqv (hnq.trans (by nlinarith)) ((v - v₀) - (q v : V)) hyY
      (by
        calc ‖(v - v₀) - (q v : V)‖ ≤ ‖v - v₀‖ + ‖(q v : V)‖ := norm_sub_le _ _
          _ ≤ ‖v - v₀‖ + c * ‖v - v₀‖ := by
              have : ‖(q v : V)‖ = ‖q v‖ := rfl
              rw [this]; linarith
          _ = (1 + c) * ‖v - v₀‖ := by ring
          _ ≤ σ := by nlinarith)
      (by rw [add_sub_cancel]; exact hw)
      (by rw [add_sub_cancel]; simp [hg, hfv])
    change v₀ + ((q v : V) + (τ (q v) : V)) = v
    rw [← hy]
    abel
  -- smoothness of `ρ`
  have hqd : ∀ v, HasFDerivAt q π v := fun v => by
    have := π.hasFDerivAt.comp v ((hasFDerivAt_id v).sub_const v₀)
    rwa [ContinuousLinearMap.comp_id] at this
  have hqcd : ContDiff ℝ ∞ q := π.contDiff.comp (contDiff_id.sub contDiff_const)
  have hτq : ContDiffOn ℝ ∞ (fun v => τ (q v)) (O' ∩ quadC ℓ) :=
    hτ.comp hqcd.contDiffOn fun v hv => (hkey v hv).2
  have hρcd : ContDiffOn ℝ ∞ ρ (O' ∩ quadC ℓ) :=
    contDiffOn_const.add ((K.subtypeL.contDiff.comp hqcd).contDiffOn.add
      (Y.subtypeL.contDiff.comp_contDiffOn hτq))
  -- the derivative at `v₀`
  have hτd : HasFDerivWithinAt τ (0 : K →L[ℝ] Y) V' (q v₀) := by
    rw [hq0, ← hDτ0]
    exact ((hτ.differentiableOn (by simp)) 0 h0V').hasFDerivWithinAt
  have hτqd : HasFDerivWithinAt (fun v => τ (q v)) ((0 : K →L[ℝ] Y).comp π)
      (O' ∩ quadC ℓ) v₀ :=
    hτd.comp v₀ (hqd v₀).hasFDerivWithinAt fun v hv => (hkey v hv).2
  have hρd : HasFDerivWithinAt ρ (K.subtypeL.comp π) (O' ∩ quadC ℓ) v₀ := by
    have := (((K.subtypeL.hasFDerivAt.comp v₀ (hqd v₀)).hasFDerivWithinAt).add
      (Y.subtypeL.hasFDerivAt.comp_hasFDerivWithinAt v₀ hτqd)).const_add v₀
    refine this.congr_fderiv ?_
    ext x
    simp
  have hUD' : UniqueDiffWithinAt ℝ (O' ∩ quadC ℓ) v₀ :=
    uniqueDiffWithinAt_quadC ℓ hℓ hO'o ⟨hv₀O', hv₀.2⟩
  refine ⟨O', ρ, hO'o, hv₀O', fun v hv => hv.1.1.1, hρcd, fun v hv => (hρmem v hv).1,
    fun v hv => (hρmem v hv).2, hfix, ?_, fun k hk => ?_⟩
  · rw [hρd.fderivWithin hUD']
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact (π x).2
    · intro x hx
      exact ⟨x, by simp [hπK ⟨x, hx⟩]⟩
  · rw [hρd.fderivWithin hUD']
    simp [hπK ⟨k, hk⟩]

end Fibre

end Polyfold
