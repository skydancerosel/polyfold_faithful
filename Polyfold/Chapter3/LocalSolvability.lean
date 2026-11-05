import Polyfold.Chapter3.BasicClass
import Polyfold.Chapter3.QuadrantIFT
import Polyfold.Chapter3.BasicGermLinearization

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.5 and
Appendix 3.8.2: **Lemma 3.46** (good position of the kernel of `DH(0)` in `ℝⁿ'`), and the local
germ-solvability Theorems 3.43 and 3.47 with Lemmas 3.42 and 3.44.

# Local germ-solvability

(Work in progress; see the end of the file for what is proved so far.)
-/

open Set Filter Topology Function Asymptotics Metric

noncomputable section

namespace Polyfold

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P}

/-! ### Lemma 3.46 -/

/-- The graph map `α ↦ (α, Lα) : P → P ⊕ W₀` of a linear map `L`. -/
def graphMap (L : P →L[ℝ] W 0) : P →ₗ[ℝ] P × W 0 := LinearMap.prod LinearMap.id (L : P →ₗ[ℝ] W 0)

omit [FiniteDimensional ℝ P] in
@[simp] lemma graphMap_apply (L : P →L[ℝ] W 0) (α : P) : graphMap L α = (α, L α) := rfl

omit [FiniteDimensional ℝ P] in
lemma graphMap_injective (L : P →L[ℝ] W 0) : Injective (graphMap L) := fun _ _ h =>
  congrArg Prod.fst h

omit [FiniteDimensional ℝ P] in
lemma mem_map_graphMap {L : P →L[ℝ] W 0} {Kt : Submodule ℝ P} {x : P × W 0} :
    x ∈ Kt.map (graphMap L) ↔ x.1 ∈ Kt ∧ x.2 = L x.1 := by
  constructor
  · rintro ⟨α, hα, rfl⟩; exact ⟨hα, rfl⟩
  · rintro ⟨h1, h2⟩; exact ⟨x.1, h1, Prod.ext rfl h2.symm⟩

omit [FiniteDimensional ℝ P] in
/-- `(α, Lα) ∈ C̃ ⊕ W` iff `α ∈ C̃`. -/
lemma graphMap_mem_prod_iff (L : P →L[ℝ] W 0) (α : P) :
    graphMap L α ∈ Ct ×ˢ (univ : Set (W 0)) ↔ α ∈ Ct := by
  simp [graphMap_apply]

/-- **Lemma 3.46, the complement** (Appendix 3.8.2): let `K' = {(α, Lα) | α ∈ K̃} ⊆ ℝⁿ' ⊕ W'`
(`L = Dδ(0)`, `K̃ = ker DH(0)`) have the good complement `Y'` with respect to
`C' = C̃ ⊕ W'`.  Then there is a good complement `Z` of `K̃` in `ℝⁿ'` with respect to `C̃` such
that `Z ⊕ W'` is a good complement of `K'` in `ℝⁿ' ⊕ W'`.

Proof (the text's, simplified): `Z' := pr_{ℝⁿ'}(Y')` satisfies `ℝⁿ' = K̃ + Z'`; choose `Z ⊆ Z'`
with `ℝⁿ' = K̃ ⊕ Z` and a linear right inverse `ρ : Z' → Y'` of the projection (bounded, finite
dimensions).  For `z ∈ Z`, `α ∈ K̃` with `|z| ≤ ε'|α|`, `y = ρ(z) = (z, w) ∈ Y'` has
`|y| ≤ ‖ρ‖|z| ≤ ε|(α, Lα)|`, so `(α, Lα) ∈ C'` iff `(α, Lα) + y ∈ C'`, i.e. `α ∈ C̃` iff
`α + z ∈ C̃`.  The text's intermediate complement `Y₀` of `Y' ∩ W'` in `Y'` is not needed. -/
theorem lemma_3_46 {L : P →L[ℝ] W 0} {Kt : Submodule ℝ P} {Y' : Submodule ℝ (P × W 0)}
    (hY' : IsGoodComplement (ScBanach.paramProd P W) (Ct ×ˢ univ) (Kt.map (graphMap L)) Y') :
    ∃ Z : Submodule ℝ P, IsGoodComplement (ScBanach.const P) Ct Kt Z ∧
      IsGoodComplement (ScBanach.paramProd P W) (Ct ×ˢ univ) (Kt.map (graphMap L)) (Z.prod ⊤) := by
  classical
  set K' := Kt.map (graphMap L) with hK'
  obtain ⟨ε, hε, hgood⟩ := hY'.exists_eps
  have hKY : IsCompl K' Y' := hY'.isCompl
  set pr : P × W 0 →ₗ[ℝ] P := LinearMap.fst ℝ P (W 0) with hpr
  set Z' : Submodule ℝ P := Y'.map pr with hZ'
  -- `ℝⁿ' = K̃ + Z'`
  have hsup : Kt ⊔ Z' = ⊤ := by
    rw [eq_top_iff]
    intro a _
    obtain ⟨k, hk, y, hy, hky⟩ :=
      Submodule.mem_sup.1 (hKY.sup_eq_top ▸ Submodule.mem_top (x := ((a, 0) : P × W 0)))
    obtain ⟨α, hα, rfl⟩ := hk
    refine Submodule.mem_sup.2 ⟨α, hα, y.1, ⟨y, hy, rfl⟩, ?_⟩
    have := congrArg Prod.fst hky
    simpa using this
  -- a complement `Z ⊆ Z'` of `K̃`
  obtain ⟨Z₀, hZ₀⟩ := Submodule.exists_isCompl ((Kt ⊓ Z').comap Z'.subtype)
  set Z : Submodule ℝ P := Z₀.map Z'.subtype with hZ
  have hZZ' : Z ≤ Z' := by
    rintro _ ⟨z, _, rfl⟩; exact z.2
  have hKZ : IsCompl Kt Z := by
    refine IsCompl.of_eq ?_ ?_
    · rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxK, z, hz, rfl⟩ := hx
      have h1 : z ∈ (Kt ⊓ Z').comap Z'.subtype := ⟨hxK, z.2⟩
      have := (Submodule.disjoint_def.1 hZ₀.disjoint) z h1 hz
      rw [this]; rfl
    · rw [eq_top_iff]
      intro a _
      obtain ⟨α, hα, b, hb, rfl⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top (x := a))
      obtain ⟨m, hm, z, hz, hmz⟩ := Submodule.mem_sup.1
        (hZ₀.sup_eq_top ▸ Submodule.mem_top (x := (⟨b, hb⟩ : Z')))
      have hmK : (m : P) ∈ Kt := hm.1
      refine Submodule.mem_sup.2 ⟨α + m, Kt.add_mem hα hmK, z, ⟨z, hz, rfl⟩, ?_⟩
      have := congrArg Subtype.val hmz
      simp only [Submodule.coe_add] at this
      rw [add_assoc, this]
  -- a bounded linear right inverse `ρ : Z' → Y'` of the projection
  set prY : Y' →ₗ[ℝ] Z' := (pr.domRestrict Y').codRestrict Z' fun y => ⟨y, y.2, rfl⟩ with hprY
  have hprY_surj : LinearMap.range prY = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨z, y, hy, rfl⟩ _
    exact ⟨⟨y, hy⟩, rfl⟩
  obtain ⟨ρ, hρ⟩ := prY.exists_rightInverse_of_surjective hprY_surj
  have hρ' : ∀ z : Z', ((ρ z : Y') : P × W 0).1 = z := fun z => by
    have := LinearMap.congr_fun hρ z
    exact congrArg Subtype.val this
  set ρc : Z' →L[ℝ] Y' := LinearMap.toContinuousLinearMap ρ with hρc
  set A : ℝ := ‖ρc‖ with hA
  have hApos : 0 ≤ A := norm_nonneg _
  set ε' : ℝ := ε / (A + 1) with hε'
  have hε'pos : 0 < ε' := by positivity
  -- the key estimate: `α + z ∈ C̃ ↔ α ∈ C̃` for `|z| ≤ ε'|α|`
  have hkey : ∀ α ∈ Kt, ∀ z ∈ Z, ‖z‖ ≤ ε' * ‖α‖ → (α ∈ Ct ↔ α + z ∈ Ct) := by
    intro α hα z hz hle
    set y : P × W 0 := (ρc ⟨z, hZZ' hz⟩).val with hy
    have hyY : y ∈ Y' := (ρc ⟨z, hZZ' hz⟩).2
    have hy1 : y.1 = z := hρ' ⟨z, hZZ' hz⟩
    have hynorm : ‖y‖ ≤ A * ‖z‖ := ρc.le_opNorm ⟨z, hZZ' hz⟩
    have hαK : graphMap L α ∈ K' := ⟨α, hα, rfl⟩
    have hle' : ‖y‖ ≤ ε * ‖graphMap L α‖ := by
      calc ‖y‖ ≤ A * ‖z‖ := hynorm
        _ ≤ A * (ε' * ‖α‖) := by gcongr
        _ ≤ ε * ‖α‖ := by
            have : A / (A + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
            calc A * (ε' * ‖α‖) = ε * (A / (A + 1)) * ‖α‖ := by rw [hε']; ring
              _ ≤ ε * 1 * ‖α‖ := by gcongr
              _ = ε * ‖α‖ := by ring
        _ ≤ ε * ‖graphMap L α‖ := by gcongr; exact norm_fst_le (graphMap L α)
    have := hgood _ hαK y hyY hle'
    rw [graphMap_mem_prod_iff] at this
    rw [this]
    have hadd : graphMap L α + y = ((α + z, L α + y.2) : P × W 0) := by
      rw [graphMap_apply, ← hy1]; rfl
    rw [hadd]
    simp
  refine ⟨Z, ⟨hKZ, ε', hε'pos, fun α hα z hz hle => hkey α hα z hz hle⟩, ⟨?_, ?_⟩⟩
  · -- `K' ⊕ (Z ⊕ W') = ℝⁿ' ⊕ W'`
    refine IsCompl.of_eq ?_ ?_
    · rw [eq_bot_iff]
      intro x ⟨hxK, hxZ⟩
      obtain ⟨α, hα, rfl⟩ := hxK
      have hαZ : α ∈ Z := (Submodule.mem_prod.1 hxZ).1
      have : α = 0 := (Submodule.disjoint_def.1 hKZ.disjoint) α hα hαZ
      rw [this]; simp
    · rw [eq_top_iff]
      intro x _
      obtain ⟨α, hα, z, hz, hαz⟩ := Submodule.mem_sup.1 (hKZ.sup_eq_top ▸ Submodule.mem_top (x := x.1))
      refine Submodule.mem_sup.2 ⟨graphMap L α, ⟨α, hα, rfl⟩, (z, x.2 - L α), ⟨hz, Submodule.mem_top⟩, ?_⟩
      rw [graphMap_apply]
      ext
      · simpa using hαz
      · simp
  · -- the estimate
    refine ⟨ε' / (‖L‖ + 1), by positivity, ?_⟩
    rintro _ ⟨α, hα, rfl⟩ p hp hle
    have hp1 : p.1 ∈ Z := (Submodule.mem_prod.1 hp).1
    have hα' : ‖graphMap L α‖ ≤ (‖L‖ + 1) * ‖α‖ := by
      rw [graphMap_apply, Prod.norm_mk]
      refine max_le (by nlinarith [norm_nonneg α, norm_nonneg L]) ?_
      calc ‖L α‖ ≤ ‖L‖ * ‖α‖ := L.le_opNorm α
        _ ≤ (‖L‖ + 1) * ‖α‖ := by gcongr; linarith
    have hz : ‖p.1‖ ≤ ε' * ‖α‖ := by
      calc ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
        _ ≤ ε' / (‖L‖ + 1) * ‖graphMap L α‖ := hle
        _ ≤ ε' / (‖L‖ + 1) * ((‖L‖ + 1) * ‖α‖) := by gcongr
        _ = ε' * ‖α‖ := by field_simp
    have := hkey α hα p.1 hp1 hz
    rw [graphMap_mem_prod_iff, this]
    simp [graphMap_apply]

/-- **Lemma 3.46, the good position**: if `K' = {(α, Lα) | α ∈ K̃}` is in good position to
`C̃ ⊕ W'`, then `K̃` is in good position to `C̃` in `ℝⁿ'`. -/
theorem lemma_3_46_isInGoodPosition {L : P →L[ℝ] W 0} {Kt : Submodule ℝ P}
    (hK' : IsInGoodPosition (ScBanach.paramProd P W) (Ct ×ˢ univ) (Kt.map (graphMap L))) :
    IsInGoodPosition (ScBanach.const P) Ct Kt where
  interior_nonempty := by
    obtain ⟨y, hy⟩ := hK'.interior_nonempty
    have : FiniteDimensional ℝ (Kt.map (graphMap L)) :=
      LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ (graphMap_injective L) Kt)
    let φ : Kt ≃ₗ[ℝ] Kt.map (graphMap L) :=
      Submodule.equivMapOfInjective _ (graphMap_injective L) Kt
    let ψ := φ.toContinuousLinearEquiv.toHomeomorph
    have hpre : ψ ⁻¹' (Subtype.val ⁻¹' (Ct ×ˢ univ) : Set (Kt.map (graphMap L))) =
        (Subtype.val ⁻¹' Ct : Set Kt) := by
      ext z
      simp only [mem_preimage]
      change graphMap L (z : P) ∈ Ct ×ˢ univ ↔ (z : P) ∈ Ct
      exact graphMap_mem_prod_iff L z
    refine ⟨ψ.symm y, ?_⟩
    have : ψ.symm y ∈ ψ ⁻¹' interior (Subtype.val ⁻¹' (Ct ×ˢ univ)) := by
      rw [mem_preimage, Homeomorph.apply_symm_apply]; exact hy
    rwa [ψ.preimage_interior, hpre] at this
  exists_goodComplement := by
    obtain ⟨Y', hY'⟩ := hK'.exists_goodComplement
    obtain ⟨Z, hZ, -⟩ := lemma_3_46 hY'
    exact ⟨Z, hZ⟩


/-! ### The contraction map of a basic germ is sc-smooth -/

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

/-- The contraction map `B` of a basic germ is an sc-smooth germ: `B(a, w) = w − (f(a, w))_W` on
`U₀` (Definition 3.7 asks only for sc⁰). -/
theorem IsBasicGerm.B_isScSmoothGerm (hC : IsQuadrantLike (ScBanach.const P) Ct)
    {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)} {f : P × W 0 → Q × W 0}
    {B : P × W 0 → W 0} (hf : IsBasicGerm Ct G f B) : IsScSmoothGerm (F := W) G B := by
  have hC' := hC.paramProd W
  have h1 : IsScSmoothGerm (F := W) G (W.addOp 0 ∘ pairMap (E := ScBanach.paramProd P W) (F := W)
      (G := W) (ScBanach.sndOp (ScBanach.const P) W 0)
      (W.negOp 0 ∘ (ScBanach.sndOp (ScBanach.const Q) W 0 ∘ f))) := fun k =>
    (((ScBanach.sndOp (ScBanach.const P) W).isSckGerm k _ hC').pair hC'
      (((hf.isScSmooth k).operator_comp hC' _).operator_comp hC' _)).operator_comp hC' _
  refine fun k => (h1 k).congr hC' fun x hx => ?_
  change x.2 + -(f x).2 = B x
  rw [hf.snd_eq x hx]; abel

/-! ### Solutions of a `C¹` map near `0` project into the quadrant -/

section Projection

variable {V Q' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Q'] [NormedSpace ℝ Q']

/-- A linear map injective on a finite-dimensional subspace `Z` is bounded below on `Z`. -/
lemma exists_norm_le_of_injOn {Z : Submodule ℝ V} {T : V →L[ℝ] Q'}
    (hinj : ∀ z ∈ Z, T z = 0 → z = 0) : ∃ c > 0, ∀ z ∈ Z, ‖z‖ ≤ c * ‖T z‖ := by
  classical
  set TZ : Z →ₗ[ℝ] Q' := (T : V →ₗ[ℝ] Q').comp Z.subtype with hTZ
  have hTZinj : Injective TZ := by
    intro a b hab
    apply Subtype.ext
    have : T ((a : V) - b) = 0 := by
      rw [map_sub]; exact sub_eq_zero.2 hab
    exact sub_eq_zero.1 (hinj _ (Z.sub_mem a.2 b.2) this)
  let e : Z ≃ₗ[ℝ] LinearMap.range TZ := LinearEquiv.ofInjective TZ hTZinj
  let einv : LinearMap.range TZ →L[ℝ] Z := LinearMap.toContinuousLinearMap e.symm.toLinearMap
  refine ⟨‖einv‖ + 1, by positivity, fun z hz => ?_⟩
  have h1 : einv (e ⟨z, hz⟩) = ⟨z, hz⟩ := e.symm_apply_apply _
  calc ‖z‖ = ‖(⟨z, hz⟩ : Z)‖ := rfl
    _ = ‖einv (e ⟨z, hz⟩)‖ := by rw [h1]
    _ ≤ ‖einv‖ * ‖e ⟨z, hz⟩‖ := einv.le_opNorm _
    _ = ‖einv‖ * ‖T z‖ := rfl
    _ ≤ (‖einv‖ + 1) * ‖T z‖ := by gcongr; linarith

/-- **Solutions near `0` of a `C¹` map on a partial quadrant project into the quadrant.**  Let
`H : U → Q'` be differentiable at `0` within `U ⊆ C̃` with `H(0) = 0`, `K̃ = ker DH(0)`, and let `Z`
be a good complement of `K̃` with respect to `C̃` (constant `ε`).  Then for every solution
`a = k + z ∈ U` (`k ∈ K̃`, `z ∈ Z`) of `H(a) = 0` close to `0`, `|z| ≤ ε|k|`, hence `k ∈ C̃`.
(The text's proof of Theorem 3.43 uses the statement "if `g(y + w) = 0` for `y ∈ K' ∩ C'` and
`w` small then `w = τ(y)`" without saying why the `K'`-component of a solution lies in `C'`.) -/
theorem exists_proj_mem_of_eq_zero {C U : Set V} (hUC : U ⊆ C) {H : V → Q'} {DH : V →L[ℝ] Q'}
    (hH : HasFDerivWithinAt H DH U 0) (hH0 : H 0 = 0) {Kt Z : Submodule ℝ V}
    (hKt : Kt = LinearMap.ker (DH : V →ₗ[ℝ] Q')) {ε : ℝ} (hε : 0 < ε)
    (hgood : ∀ x ∈ Kt, ∀ z ∈ Z, ‖z‖ ≤ ε * ‖x‖ → (x ∈ C ↔ x + z ∈ C)) (hKZ : IsCompl Kt Z) :
    ∃ r > 0, ∀ a ∈ U, ‖a‖ < r → H a = 0 → ∀ k ∈ Kt, ∀ z ∈ Z, a = k + z →
      ‖z‖ ≤ ε * ‖k‖ ∧ k ∈ C := by
  have hinj : ∀ z ∈ Z, DH z = 0 → z = 0 := fun z hz h0 => by
    have hzK : z ∈ Kt := by rw [hKt]; exact h0
    exact (Submodule.disjoint_def.1 hKZ.disjoint) z hzK hz
  obtain ⟨c, hc, hbound⟩ := exists_norm_le_of_injOn hinj
  set η : ℝ := min (1 / (2 * c)) (ε / (2 * c)) with hη
  have hηpos : 0 < η := lt_min (by positivity) (by positivity)
  have hcη : c * η ≤ 1 / 2 := by
    have : η ≤ 1 / (2 * c) := min_le_left _ _
    calc c * η ≤ c * (1 / (2 * c)) := by gcongr
      _ = 1 / 2 := by field_simp
  have hcη' : 2 * (c * η) ≤ ε := by
    have : η ≤ ε / (2 * c) := min_le_right _ _
    calc 2 * (c * η) ≤ 2 * (c * (ε / (2 * c))) := by gcongr
      _ = ε := by field_simp
  -- the little-`o` estimate at `0`
  have hlo := (hasFDerivWithinAt_iff_isLittleO.1 hH).def hηpos
  obtain ⟨r, hr, hr'⟩ := Metric.mem_nhdsWithin_iff.1 hlo
  refine ⟨r, hr, fun a haU har ha0 k hk z hz hakz => ?_⟩
  have hest : ‖H a - H 0 - DH (a - 0)‖ ≤ η * ‖a - 0‖ :=
    hr' ⟨by rwa [Metric.mem_ball, dist_zero_right], haU⟩
  rw [hH0, sub_zero, sub_zero, ha0, zero_sub, norm_neg] at hest
  have hDHk : DH k = 0 := by
    have : k ∈ LinearMap.ker (DH : V →ₗ[ℝ] Q') := hKt ▸ hk
    exact this
  have hDHa : DH a = DH z := by rw [hakz, map_add, hDHk, zero_add]
  have hz1 : ‖z‖ ≤ c * (η * ‖a‖) := by
    calc ‖z‖ ≤ c * ‖DH z‖ := hbound z hz
      _ = c * ‖DH a‖ := by rw [hDHa]
      _ ≤ c * (η * ‖a‖) := by gcongr
  have ha : ‖a‖ ≤ ‖k‖ + ‖z‖ := by rw [hakz]; exact norm_add_le _ _
  have hz2 : ‖z‖ ≤ ε * ‖k‖ := by
    have h3 : ‖z‖ ≤ c * η * ‖k‖ + c * η * ‖z‖ := by
      calc ‖z‖ ≤ c * (η * ‖a‖) := hz1
        _ ≤ c * (η * (‖k‖ + ‖z‖)) := by gcongr
        _ = c * η * ‖k‖ + c * η * ‖z‖ := by ring
    have h4 : ‖z‖ * (1 - c * η) ≤ c * η * ‖k‖ := by linarith
    have h5 : ‖z‖ / 2 ≤ c * η * ‖k‖ := by
      have : ‖z‖ / 2 ≤ ‖z‖ * (1 - c * η) := by nlinarith [norm_nonneg z]
      linarith
    nlinarith [norm_nonneg k]
  refine ⟨hz2, ?_⟩
  rw [hgood k hk z hz hz2, ← hakz]
  exact hUC haU

end Projection

/-! ### Theorem 3.43: the data -/

/-- **The data of Theorem 3.43**: an sc-smooth germ `g : O(C̃ ⊕ W, 0) → Q ⊕ W` with `g(0) = 0`
whose index-raised germ `g¹` (on `O(C̃ ⊕ W¹, 0)`, levels raised by one) is a basic germ with
contraction map `B` (the text's `g = Φ_*(f)` with `g¹ = (Φ_*(h + s))¹` basic, Theorem 3.38).
The shifted germ of neighbourhoods `G₁` is `(U_{m+1})_m`. -/
structure ShiftedBasicData (Ct : Set P) (W : ScBanach) (Q : Type) [NormedAddCommGroup Q]
    [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] where
  /-- The germ of neighbourhoods on level `0`. -/
  G₀ : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)
  /-- The germ `g`. -/
  g : P × W 0 → Q × W 0
  isScSmooth : IsScSmoothGerm (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) G₀ g
  g_zero : g 0 = 0
  /-- The germ of neighbourhoods of the index-raised germ. -/
  G₁ : ScNbhdGerm (ScBanach.paramProd P W.shift) (Ct ×ˢ univ)
  G₁_U : ∀ m, G₁.U m = G₀.U (m + 1)
  /-- The index-raised germ `g¹`. -/
  g₁ : P × W 1 → Q × W 1
  g₁_eq : ∀ x ∈ G₀.U 1,
    g₁ x = levelMap (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) g 1 x
  /-- Its contraction map. -/
  B : P × W 1 → W 1
  basic : IsBasicGerm Ct G₁ g₁ B

namespace ShiftedBasicData

variable (𝒟 : ShiftedBasicData Ct W Q) (hC : IsQuadrantLike (ScBanach.const P) Ct)

/-- The working form of the contraction germ of `g¹`. -/
abbrev 𝒞 : ContractionGerm P Ct W.shift := 𝒟.basic.contraction.toContractionGerm

/-- The solution germ `δ : O(C̃, 0) → W¹` of `P ∘ g¹`, `δ(a) ∈ W₁`. -/
abbrev δ : P → W 1 := 𝒟.𝒞.sol

lemma δ_zero : 𝒟.δ 0 = 0 := 𝒟.𝒞.sol_zero

include hC in
lemma B_isScSmooth : IsScSmoothGerm (F := W.shift) 𝒟.𝒞.G 𝒟.𝒞.B :=
  𝒟.basic.B_isScSmoothGerm hC

lemma sol_mem {a : P} (ha : a ∈ 𝒟.𝒞.N 0 ∩ Ct) :
    ((a, 𝒟.δ a) : (ScBanach.paramProd P W) 1) ∈ 𝒟.G₀.U 1 := by
  rw [← 𝒟.G₁_U 0]
  exact 𝒟.𝒞.mem_G_fixLvl 0 ha

lemma snd_g₁_sol {a : P} (ha : a ∈ 𝒟.𝒞.N 0 ∩ Ct) : (𝒟.g₁ (a, 𝒟.δ a)).2 = 0 := by
  have h1 := 𝒟.basic.snd_eq (a, 𝒟.δ a) (by rw [𝒟.G₁_U 0]; exact 𝒟.sol_mem ha)
  rw [h1]
  change 𝒟.δ a - 𝒟.𝒞.B (a, 𝒟.δ a) = 0
  rw [𝒟.𝒞.sol_fixed ha, sub_self]

/-- Uniqueness of the solution germ in the contraction region (Theorem 3.29). -/
lemma eq_δ {a : P} (ha : a ∈ 𝒟.𝒞.N 0 ∩ Ct) {w : W 1} (hw : w ∈ 𝒟.𝒞.O 0)
    (hx : ((a, w) : P × W 1) ∈ 𝒟.G₁.U 0) (h : (𝒟.g₁ (a, w)).2 = 0) : w = 𝒟.δ a := by
  refine 𝒟.𝒞.eq_sol ha hw ?_
  have h1 := 𝒟.basic.snd_eq (a, w) hx
  rw [h1] at h
  change w - 𝒟.𝒞.B (a, w) = 0 at h
  exact (sub_eq_zero.1 h).symm

/-- The derivative `Dg(0) : P ⊕ W₀ → Q ⊕ W₀` (the chosen derivative family of the germ). -/
abbrev Dg : P × W 0 →L[ℝ] Q × W 0 :=
  scDerivGerm (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) 𝒟.G₀ 𝒟.g 0

lemma hg1 : IsSc1GermWith (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) 𝒟.G₀ 𝒟.g
    (scDerivGerm 𝒟.G₀ 𝒟.g) := (𝒟.isScSmooth 1).1.isSc1GermWith_scDerivGerm

/-- `P ∘ g(a, δ(a)) = 0` on level `0`. -/
lemma snd_g_sol {a : P} (ha : a ∈ 𝒟.𝒞.N 0 ∩ Ct) :
    (𝒟.g ((ScBanach.paramProd P W).toBase 1 (a, 𝒟.δ a))).2 = 0 := by
  have hmem := 𝒟.sol_mem ha
  have := congrArg Prod.snd ((𝒟.isScSmooth 0).toBase_levelMap hmem)
  rw [← 𝒟.g₁_eq _ hmem, ScBanach.paramProd_toBase] at this
  dsimp only at this
  rw [𝒟.snd_g₁_sol ha, map_zero] at this
  exact this.symm

/-- The map `H(a) = (1 − P) ∘ g(a, δ(a))` of the proof of Theorem 3.43, read on level `0`. -/
def H : P → Q := fun a => (𝒟.g (a, W.toBase 1 (𝒟.δ a))).1

lemma H_eq {a : P} (ha : a ∈ 𝒟.𝒞.N 0 ∩ Ct) : 𝒟.H a = (𝒟.g₁ (a, 𝒟.δ a)).1 := by
  have hmem := 𝒟.sol_mem ha
  rw [𝒟.g₁_eq _ hmem]
  have := congrArg Prod.fst ((𝒟.isScSmooth 0).toBase_levelMap hmem)
  rw [ScBanach.paramProd_toBase] at this
  change (levelMap (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) 𝒟.g 1 (a, 𝒟.δ a)).1 =
    (𝒟.g (a, W.toBase 1 (𝒟.δ a))).1 at this
  exact this.symm

lemma H_zero : 𝒟.H 0 = 0 := by
  unfold H
  rw [𝒟.δ_zero, map_zero]
  change (𝒟.g 0).1 = 0
  rw [𝒟.g_zero]; rfl

include hC in
/-- **The regularity of `H`** ("the map `H` restricted to `U'_i` is of class `C^{i-1}`"): for every
`j ≥ 1` there is a relatively open neighbourhood `V` of `0` in `C̃`, contained in the solution
region, on which `H` is `C^j` and `δ` lifts to a `C^j` map into `W_{2j}` (so that `a ↦ (a, δ(a))`
is `C^j` into `E_{2j}` and `g : E_{2j} → F_j` is `C^j` by Proposition 1.18). -/
theorem H_contDiffOn (j : ℕ) (hj : 1 ≤ j) :
    ∃ V : Set P, (∃ O : Set P, IsOpen O ∧ V = O ∩ Ct) ∧ (0 : P) ∈ V ∧ V ⊆ 𝒟.𝒞.N 0 ∩ Ct ∧
      ContDiffOn ℝ j 𝒟.H V ∧
      ∃ δ' : P → W (j + j), ContDiffOn ℝ j δ' V ∧
        ∀ a ∈ V, W.toBase (j + j) (δ' a) = W.toBase 1 (𝒟.δ a) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hCW := hC.paramProd W
  obtain ⟨s, hsol, hs⟩ := theorem_3_33_smooth 𝒟.𝒞 hC (𝒟.B_isScSmooth hC) (m + 1)
  -- `δ` on level `2m + 1` of `W¹`, i.e. into `W_{2m+2}`
  set δ' : P → W.shift (m + 1 + m) :=
    levelMap (E := ScBanach.const P) (F := W.shift) 𝒟.δ (m + 1 + m) with hδ'
  set V : Set P := (𝒟.𝒞.germ hC s).U (m + 1 + m + (m + 1)) with hV
  have hVsub : ∀ k ≤ m + 1 + m + (m + 1), V ⊆ (𝒟.𝒞.germ hC s).U k := fun k hk a ha =>
    ⟨𝒟.𝒞.N_anti_le (by omega) ha.1, ha.2⟩
  have hδ'C : ContDiffOn ℝ (m + 1) δ' V := by
    have := hs.contDiffOn_levels hC (m + 1 + m)
    refine this.congr fun a _ => ?_
    rw [Function.comp_apply, ScBanach.const_inclK]
  have hδ'base : ∀ a ∈ V, W.shift.toBase (m + 1 + m) (δ' a) = 𝒟.δ a := fun a ha => by
    have := hsol.isSc0.toBase_levelMap (hVsub (m + 1 + m) (by omega) ha)
    rwa [ScBanach.const_toBase] at this
  have hmem : ∀ a ∈ V, ((a, δ' a) : (ScBanach.paramProd P W) (m + 1 + (m + 1))) ∈
      𝒟.G₀.U (m + 1 + (m + 1)) := fun a ha => by
    have h1 : ((a, δ' a) : (ScBanach.paramProd P W.shift) (m + 1 + m)) ∈ 𝒟.G₁.U (m + 1 + m) :=
      hsol.mem_G (m + 1 + m) a (hVsub (m + 1 + m) (by omega) ha)
    rw [𝒟.G₁_U] at h1
    exact h1
  -- `g` from level `2(m+1)` to level `m+1`
  have hgC : ContDiffOn ℝ (m + 1) (levelMap (E := ScBanach.paramProd P W)
      (F := ScBanach.paramProd Q W) 𝒟.g (m + 1) ∘ (ScBanach.paramProd P W).inclK (m + 1) (m + 1))
      (𝒟.G₀.U ((m + 1) + (m + 1))) :=
    (𝒟.isScSmooth (m + 1)).contDiffOn_levels hCW (m + 1)
  have hγC : ContDiffOn ℝ (m + 1) (fun a : P => ((a, δ' a) : (ScBanach.paramProd P W) (m + 1 + (m + 1)))) V :=
    contDiffOn_id.prodMk hδ'C
  refine ⟨V, ⟨𝒟.𝒞.N (m + 1 + m + (m + 1) + s), 𝒟.𝒞.N_open _, rfl⟩, (𝒟.𝒞.germ hC s).zero_mem _,
    fun a ha => ⟨𝒟.𝒞.N_anti_le (by omega) ha.1, ha.2⟩, ?_, ?_⟩
  · -- `H = pr_Q ∘ g_{m+1} ∘ ι ∘ (a ↦ (a, δ'(a)))` on `V`
    have hcomp := contDiff_fst.comp_contDiffOn (hgC.comp hγC hmem)
    refine hcomp.congr fun a ha => ?_
    have hbase := congrArg Prod.fst ((𝒟.isScSmooth 0).toBase_levelMap
      (𝒟.G₀.inclK_mem (hmem a ha)))
    rw [ScBanach.paramProd_toBase, (ScBanach.paramProd P W).toBase_inclK,
      ScBanach.paramProd_toBase] at hbase
    dsimp only at hbase
    have hδ'' : W.toBase (m + 1 + (m + 1)) (δ' a) = W.toBase 1 (𝒟.δ a) := by
      have h := W.shift_toBase (m + 1 + m) (δ' a)
      rw [hδ'base a ha] at h
      exact h
    simp only [Function.comp_apply]
    change (𝒟.g (a, W.toBase 1 (𝒟.δ a))).1 =
      (levelMap (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) 𝒟.g (m + 1)
        ((ScBanach.paramProd P W).inclK (m + 1) (m + 1) (a, δ' a))).1
    rw [hbase, hδ'']
  · refine ⟨δ', hδ'C, fun a ha => ?_⟩
    have h := W.shift_toBase (m + 1 + m) (δ' a)
    rw [hδ'base a ha] at h
    exact h

/-! ### The derivative data: `Dδ(0)`, `DH(0)` and Lemma 3.44 -/

/-- A relatively open neighbourhood `V₁` of `0` in `C̃` on which `H` and `δ : V₁ → W₁` are `C¹`
(the text's `U'_2`), inside the solution region of `δ`. -/
structure Deriv (𝒟 : ShiftedBasicData Ct W Q) where
  /-- The neighbourhood. -/
  V₁ : Set P
  relOpen : ∃ O : Set P, IsOpen O ∧ V₁ = O ∩ Ct
  zero_mem : (0 : P) ∈ V₁
  sub : V₁ ⊆ 𝒟.𝒞.N 0 ∩ Ct
  H_contDiffOn : ContDiffOn ℝ 1 𝒟.H V₁
  δ_contDiffOn : ContDiffOn ℝ 1 𝒟.δ V₁

include hC in
theorem exists_deriv : Nonempty 𝒟.Deriv := by
  obtain ⟨V, ⟨O, hO, hVO⟩, h0V, hVsub, hH, -⟩ := 𝒟.H_contDiffOn hC 1 le_rfl
  obtain ⟨s, hsol, hs⟩ := theorem_3_33_smooth 𝒟.𝒞 hC (𝒟.B_isScSmooth hC) 1
  have hδ : ContDiffOn ℝ 1 𝒟.δ ((𝒟.𝒞.germ hC s).U (0 + 1)) := by
    have := hs.contDiffOn_levels hC 0
    refine this.congr fun a _ => ?_
    rw [Function.comp_apply, ScBanach.const_inclK, levelMap_zero]
  refine ⟨⟨V ∩ (𝒟.𝒞.germ hC s).U (0 + 1), ⟨O ∩ 𝒟.𝒞.N (0 + 1 + s), hO.inter (𝒟.𝒞.N_open _), ?_⟩,
    ⟨h0V, (𝒟.𝒞.germ hC s).zero_mem _⟩, fun a ha => hVsub ha.1, hH.mono inter_subset_left,
    hδ.mono inter_subset_right⟩⟩
  rw [hVO, ContractionGerm.germ_U]
  ext a; simp only [mem_inter_iff]; tauto

namespace Deriv

variable {𝒟} (𝒱 : 𝒟.Deriv)

include hC in
lemma uniqueDiffWithinAt : UniqueDiffWithinAt ℝ 𝒱.V₁ 0 := by
  obtain ⟨O, hO, hV⟩ := 𝒱.relOpen
  have h0 := 𝒱.zero_mem
  rw [hV] at h0 ⊢
  have := hC.uniqueDiffWithinAt (m := 0) hO (x := 0) (by rwa [ScBanach.const_lvlSet])
  rwa [ScBanach.const_lvlSet] at this

/-- `Dδ(0) : P → W₁`. -/
def Dδ₀ : P →L[ℝ] W 1 := fderivWithin ℝ 𝒟.δ 𝒱.V₁ 0

lemma hasFDerivWithinAt_δ : HasFDerivWithinAt 𝒟.δ 𝒱.Dδ₀ 𝒱.V₁ 0 :=
  (𝒱.δ_contDiffOn.differentiableOn one_ne_zero 0 𝒱.zero_mem).hasFDerivWithinAt

/-- `L = ι ∘ Dδ(0) : P → W₀`. -/
def L : P →L[ℝ] W 0 := (W.toBase 1).comp 𝒱.Dδ₀

/-- The graph `α ↦ (α, Lα)` as a continuous linear map. -/
def graphCLM : P →L[ℝ] P × W 0 := (ContinuousLinearMap.id ℝ P).prod 𝒱.L

@[simp] lemma graphCLM_apply (α : P) : 𝒱.graphCLM α = (α, 𝒱.L α) := rfl

/-- `DH(0) = (1 − P) ∘ Dg(0) ∘ (α ↦ (α, Dδ(0)α))`. -/
def DH₀ : P →L[ℝ] Q := (ContinuousLinearMap.fst ℝ Q (W 0)).comp (𝒟.Dg.comp 𝒱.graphCLM)

lemma DH₀_apply (α : P) : 𝒱.DH₀ α = (𝒟.Dg (α, 𝒱.L α)).1 := rfl

/-- The curve `a ↦ (a, δ(a)) ∈ E₁` is differentiable at `0` within `V₁`. -/
lemma hasFDerivWithinAt_curve :
    HasFDerivWithinAt (fun a : P => ((a, 𝒟.δ a) : (ScBanach.paramProd P W) 1))
      ((ContinuousLinearMap.id ℝ P).prod 𝒱.Dδ₀) 𝒱.V₁ 0 :=
  (hasFDerivWithinAt_id 0 𝒱.V₁).prodMk 𝒱.hasFDerivWithinAt_δ

lemma curve_mapsTo : MapsTo (fun a : P => ((a, 𝒟.δ a) : (ScBanach.paramProd P W) 1)) 𝒱.V₁
    (𝒟.G₀.U 1) := fun _a ha => 𝒟.sol_mem (𝒱.sub ha)

/-- The chain rule for `g ∘ (a ↦ (a, δ(a)))` at `0`: the derivative is `Dg(0) ∘ (α ↦ (α, Lα))`. -/
lemma hasFDerivWithinAt_comp :
    HasFDerivWithinAt (fun a : P => 𝒟.g ((ScBanach.paramProd P W).toBase 1 (a, 𝒟.δ a)))
      (𝒟.Dg.comp 𝒱.graphCLM) 𝒱.V₁ 0 := by
  have h0 : (fun a : P => ((a, 𝒟.δ a) : (ScBanach.paramProd P W) 1)) 0 = 0 := by
    change ((0 : P), 𝒟.δ 0) = (0 : (ScBanach.paramProd P W) 1)
    rw [𝒟.δ_zero]; rfl
  have h1 : HasFDerivWithinAt (𝒟.g ∘ (ScBanach.paramProd P W).toBase 1)
      ((𝒟.Dg).comp ((ScBanach.paramProd P W).toBase 1)) (𝒟.G₀.U 1)
      ((fun a : P => ((a, 𝒟.δ a) : (ScBanach.paramProd P W) 1)) 0) := by
    rw [h0]; exact 𝒟.hg1.hasFDerivWithinAt 0 (𝒟.G₀.zero_mem 1)
  have h2 := h1.comp (0 : P) 𝒱.hasFDerivWithinAt_curve 𝒱.curve_mapsTo
  refine h2.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun α => ?_
  rfl

lemma hasFDerivWithinAt_H : HasFDerivWithinAt 𝒟.H 𝒱.DH₀ 𝒱.V₁ 0 := by
  have := (ContinuousLinearMap.fst ℝ Q (W 0)).hasFDerivAt.comp_hasFDerivWithinAt (0 : P)
    𝒱.hasFDerivWithinAt_comp
  refine this.congr (fun a _ => ?_) ?_
  · change (𝒟.g ((ScBanach.paramProd P W).toBase 1 (a, 𝒟.δ a))).1 = 𝒟.H a
    rw [ScBanach.paramProd_toBase]; rfl
  · change (𝒟.g ((ScBanach.paramProd P W).toBase 1 (0, 𝒟.δ 0))).1 = 𝒟.H 0
    rw [ScBanach.paramProd_toBase]; rfl

include hC in
lemma fderivWithin_H : fderivWithin ℝ 𝒟.H 𝒱.V₁ 0 = 𝒱.DH₀ :=
  (𝒱.hasFDerivWithinAt_H).fderivWithin (𝒱.uniqueDiffWithinAt hC)

omit 𝒱 in
include hC in
/-- **Lemma 3.9 at `0`, read on level `0`** ("recalling from Lemma 3.9 that `D₂B(0) = 0`"): the
`W`-component of `Dg(0)(0, ζ)` is `ζ`.  From the basic germ `g¹` on the index-raised structure
(`IsSc0ContractionGerm.deriv_zero_snd`, for `ζ ∈ W₁`) and the density of `W₁` in `W₀`. -/
theorem snd_Dg_inr (ζ : W 0) : (𝒟.Dg ((0 : P), ζ)).2 = ζ := by
  set E := ScBanach.paramProd P W with hE
  set F := ScBanach.paramProd Q W with hF
  set D := scDerivGerm (E := E) (F := F) 𝒟.G₀ 𝒟.g with hD
  have hCW := hC.paramProd W
  -- the level-`1` derivative of `g` at `0`
  have hlev := (𝒟.hg1).hasFDerivWithinAt_level hCW (m := 1) (𝒟.G₀.zero_mem 2)
  set D₁ : E 1 →L[ℝ] F 1 := levelDeriv (E := E) (F := F) D 1 0 with hD₁
  -- the derivative of `B ∘ toBase` on the shifted structure
  set L₀ : (ScBanach.paramProd P W.shift) 0 →L[ℝ] W.shift 0 :=
    ContinuousLinearMap.snd ℝ P (W 1) - (ContinuousLinearMap.snd ℝ Q (W 1)).comp D₁ with hL₀
  have hU1 : 𝒟.G₁.U 1 = 𝒟.G₀.U 2 := 𝒟.G₁_U 1
  have hderiv : HasFDerivWithinAt (𝒟.B ∘ (ScBanach.paramProd P W.shift).toBase 1)
      (L₀.comp ((ScBanach.paramProd P W.shift).toBase 1)) (𝒟.G₁.U 1) 0 := by
    rw [hU1]
    have h1 : HasFDerivWithinAt (fun x : E 2 => (E.incl 1 x).2)
        ((ContinuousLinearMap.snd ℝ P (W 1)).comp (E.incl 1)) (𝒟.G₀.U 2) 0 :=
      ((ContinuousLinearMap.snd ℝ P (W 1)).comp (E.incl 1)).hasFDerivAt.hasFDerivWithinAt
    have h2 := (ContinuousLinearMap.snd ℝ Q (W 1)).hasFDerivAt.comp_hasFDerivWithinAt (0 : E 2) hlev
    have h3 := h1.sub h2
    refine (h3.congr ?_ ?_).congr_fderiv ?_
    · intro x hx
      have hx1 : E.incl 1 x ∈ 𝒟.G₀.U 1 := 𝒟.G₀.nested 1 x hx
      have hx1' : E.incl 1 x ∈ 𝒟.G₁.U 0 := by rw [𝒟.G₁_U 0]; exact hx1
      change 𝒟.B (E.incl 1 x) = (E.incl 1 x).2 - (levelMap (E := E) (F := F) 𝒟.g 1 (E.incl 1 x)).2
      rw [← 𝒟.g₁_eq _ hx1, 𝒟.basic.snd_eq _ hx1']
      abel
    · have hx1' : E.incl 1 (0 : E 2) ∈ 𝒟.G₁.U 0 := by rw [𝒟.G₁_U 0]; exact 𝒟.G₀.nested 1 0 (𝒟.G₀.zero_mem 2)
      change 𝒟.B (E.incl 1 0) = (E.incl 1 0).2 - (levelMap (E := E) (F := F) 𝒟.g 1 (E.incl 1 0)).2
      rw [← 𝒟.g₁_eq _ (𝒟.G₀.nested 1 0 (𝒟.G₀.zero_mem 2)), 𝒟.basic.snd_eq _ hx1']
      abel
    · refine ContinuousLinearMap.ext fun x => ?_
      rfl
  have hζ₁ : ∀ ζ₁ : W 1, (D₁ ((0 : P), ζ₁)).2 = ζ₁ := fun ζ₁ => by
    have := 𝒟.basic.contraction.deriv_zero_snd hderiv ζ₁
    change ζ₁ - (D₁ ((0 : P), ζ₁)).2 = 0 at this
    exact (sub_eq_zero.1 this).symm
  -- density
  have hclosed : IsClosed {ζ : W 0 | (𝒟.Dg (((0 : P), ζ) : (ScBanach.paramProd P W) 0)).2 = ζ} :=
    isClosed_eq (by fun_prop) continuous_id
  refine (W.denseRange_incl 0).induction_on ζ hclosed fun ζ₁ => ?_
  change (D 0 ((0 : P), W.incl 0 ζ₁)).2 = W.incl 0 ζ₁
  have h1 := (𝒟.hg1).toBase_levelDeriv (m := 1) (𝒟.G₀.zero_mem 2) (((0 : P), ζ₁) : E 1)
  rw [ScBanach.paramProd_toBase, ScBanach.paramProd_toBase, map_zero] at h1
  have h2 := congrArg Prod.snd h1
  dsimp only at h2
  rw [hζ₁ ζ₁] at h2
  exact h2.symm

include hC in
/-- Differentiating `P ∘ g(a, δ(a)) = 0` at `a = 0`: `(Dg(0)(α, Lα))_W = 0`. -/
theorem snd_Dg_graph (α : P) : (𝒟.Dg (α, 𝒱.L α)).2 = 0 := by
  have hcomp := (ContinuousLinearMap.snd ℝ Q (W 0)).hasFDerivAt.comp_hasFDerivWithinAt (0 : P)
    𝒱.hasFDerivWithinAt_comp
  have hzero : HasFDerivWithinAt (fun a : P => (𝒟.g ((ScBanach.paramProd P W).toBase 1 (a, 𝒟.δ a))).2)
      (0 : P →L[ℝ] W 0) 𝒱.V₁ 0 := by
    refine (hasFDerivWithinAt_const (0 : W 0) 0 𝒱.V₁).congr (fun a ha => ?_) ?_
    · exact 𝒟.snd_g_sol (𝒱.sub ha)
    · exact 𝒟.snd_g_sol (𝒱.sub 𝒱.zero_mem)
  have := (𝒱.uniqueDiffWithinAt hC).eq hcomp hzero
  have h := congrArg (fun T : P →L[ℝ] W 0 => T α) this
  simpa [graphCLM_apply] using h

include hC in
/-- **Lemma 3.44**: `ker Dg(0) = {(α, Dδ(0)α) | α ∈ ker DH(0)}`. -/
theorem ker_Dg_eq :
    LinearMap.ker (𝒟.Dg : (ScBanach.paramProd P W) 0 →ₗ[ℝ] (ScBanach.paramProd Q W) 0) =
      (LinearMap.ker (𝒱.DH₀ : P →ₗ[ℝ] Q)).map (graphMap 𝒱.L) := by
  ext x
  rw [mem_map_graphMap, LinearMap.mem_ker, LinearMap.mem_ker]
  have hdec : x = ((x.1, 𝒱.L x.1) : P × W 0) + (((0 : P), x.2 - 𝒱.L x.1) : P × W 0) := by
    ext <;> simp
  have hsnd : (𝒟.Dg x).2 = x.2 - 𝒱.L x.1 := by
    conv_lhs => rw [hdec]
    rw [map_add, Prod.snd_add, 𝒱.snd_Dg_graph hC, Deriv.snd_Dg_inr (𝒟 := 𝒟) hC, zero_add]
  constructor
  · intro h
    have h' : 𝒟.Dg x = 0 := h
    have h2 : (𝒟.Dg x).2 = 0 := by rw [h']; rfl
    rw [hsnd, sub_eq_zero] at h2
    refine ⟨?_, h2⟩
    change (𝒟.Dg (x.1, 𝒱.L x.1)).1 = 0
    rw [← h2]
    have : (x.1, x.2) = x := rfl
    rw [this, h']; rfl
  · rintro ⟨h1, h2⟩
    change (𝒟.Dg (x.1, 𝒱.L x.1)).1 = 0 at h1
    have hx : x = (x.1, 𝒱.L x.1) := Prod.ext rfl h2
    change 𝒟.Dg x = 0
    refine Prod.ext ?_ ?_
    · change (𝒟.Dg x).1 = 0
      rw [hx]; exact h1
    · change (𝒟.Dg x).2 = 0
      rw [hsnd, h2, sub_self]

include hC in
/-- `DH(0)` is surjective when `Dg(0)` is. -/
theorem DH₀_surjective (hsurj : Surjective 𝒟.Dg) : Surjective 𝒱.DH₀ := by
  intro q
  obtain ⟨x, hx⟩ := hsurj (q, 0)
  have hdec : x = ((x.1, 𝒱.L x.1) : P × W 0) + (((0 : P), x.2 - 𝒱.L x.1) : P × W 0) := by
    ext <;> simp
  have hsnd : (𝒟.Dg x).2 = x.2 - 𝒱.L x.1 := by
    conv_lhs => rw [hdec]
    rw [map_add, Prod.snd_add, 𝒱.snd_Dg_graph hC, Deriv.snd_Dg_inr (𝒟 := 𝒟) hC, zero_add]
  have h2 : x.2 = 𝒱.L x.1 := by
    have := congrArg Prod.snd hx
    rw [hsnd] at this
    exact sub_eq_zero.1 this
  refine ⟨x.1, ?_⟩
  rw [DH₀_apply, ← h2]
  have : (x.1, x.2) = x := rfl
  rw [this, hx]

end Deriv

/-! ### The choices of the proof of Theorem 3.43 -/

/-- The kernel `K' = ker Dg(0)`. -/
abbrev K' : Submodule ℝ (P × W 0) := LinearMap.ker (𝒟.Dg : P × W 0 →ₗ[ℝ] Q × W 0)

/-- **The data assembled in the proof of Theorem 3.43**: the derivative data, the kernel
`K̃ = ker DH(0)` with `K' = {(α, Lα) | α ∈ K̃}` (Lemma 3.44), the good complement `Z` of `K̃` with
`Z ⊕ W` a good complement of `K'` (Lemma 3.46), and the solution `σ : V' → Z` of `H(a + σ(a)) = 0`
given by Theorem 3.78 with its uniqueness constants. -/
structure Sol (𝒟 : ShiftedBasicData Ct W Q) extends 𝒟.Deriv where
  hker : 𝒟.K' = (LinearMap.ker (toDeriv.DH₀ : P →ₗ[ℝ] Q)).map (graphMap toDeriv.L)
  /-- The good complement `Z` of `K̃` in `ℝⁿ'`. -/
  Z : Submodule ℝ P
  hZ : IsGoodComplement (ScBanach.const P) Ct (LinearMap.ker (toDeriv.DH₀ : P →ₗ[ℝ] Q)) Z
  hY : IsGoodComplement (ScBanach.paramProd P W) (Ct ×ˢ univ) 𝒟.K' (Z.prod ⊤)
  /-- The neighbourhood of `0` in `K̃ ∩ C̃` of Theorem 3.78. -/
  V' : Set (LinearMap.ker (toDeriv.DH₀ : P →ₗ[ℝ] Q))
  V'_relOpen : ∃ O : Set (LinearMap.ker (toDeriv.DH₀ : P →ₗ[ℝ] Q)), IsOpen O ∧
    V' = O ∩ Subtype.val ⁻¹' Ct
  V'_zero : (0 : LinearMap.ker (toDeriv.DH₀ : P →ₗ[ℝ] Q)) ∈ V'
  /-- The solution `σ : V' → Z`. -/
  σ : LinearMap.ker (toDeriv.DH₀ : P →ₗ[ℝ] Q) → Z
  σ_contDiffOn : ContDiffOn ℝ 1 σ V'
  σ_zero : σ 0 = 0
  fderiv_σ : fderivWithin ℝ σ V' 0 = 0
  σ_sol : ∀ k ∈ V', (k : P) + σ k ∈ toDeriv.V₁ ∧ 𝒟.H ((k : P) + σ k) = 0
  ε : ℝ
  ε_pos : 0 < ε
  σ₀ : ℝ
  σ₀_pos : 0 < σ₀
  σ_bound : ∀ k ∈ V', ‖k‖ ≤ ε → ‖σ k‖ ≤ σ₀
  σ_unique : ∀ k ∈ V', ‖k‖ ≤ ε → ∀ z ∈ Z, ‖z‖ ≤ σ₀ → (k : P) + z ∈ toDeriv.V₁ →
    𝒟.H ((k : P) + z) = 0 → z = σ k

/-- The data of `Sol` exist: Lemma 3.46 and Theorem 3.78 applied to `H`. -/
theorem exists_sol (hC : IsPartialQuadrant (ScBanach.const P) Ct) (hsurj : Surjective 𝒟.Dg)
    (hpos : IsInGoodPosition (ScBanach.paramProd P W) (Ct ×ˢ univ) 𝒟.K') : Nonempty 𝒟.Sol := by
  classical
  have hCq := hC.isQuadrantLike
  obtain ⟨𝒱⟩ := 𝒟.exists_deriv hCq
  have hker : 𝒟.K' = (LinearMap.ker (𝒱.DH₀ : P →ₗ[ℝ] Q)).map (graphMap 𝒱.L) := 𝒱.ker_Dg_eq hCq
  have hpos' : IsInGoodPosition (ScBanach.paramProd P W) (Ct ×ˢ univ)
      ((LinearMap.ker (𝒱.DH₀ : P →ₗ[ℝ] Q)).map (graphMap 𝒱.L)) := hker ▸ hpos
  obtain ⟨Y', hY'⟩ := hpos'.exists_goodComplement
  obtain ⟨Z, hZ, hY⟩ := lemma_3_46 hY'
  have hKpos := lemma_3_46_isInGoodPosition hpos'
  have hU : IsRelOpenInQuadrant (ScBanach.const P) Ct 𝒱.V₁ := ⟨hC, 𝒱.relOpen⟩
  have hDH : fderivWithin ℝ 𝒟.H 𝒱.V₁ 0 = 𝒱.DH₀ := 𝒱.fderivWithin_H hCq
  obtain ⟨V', σ, ε, σ₀, hV'rel, hV'0, hσC, hσ0, hDσ, hsol, hε, hσ₀, hbound, huniq⟩ :=
    theorem_3_78 hU 𝒱.zero_mem (j := 1) le_rfl 𝒱.H_contDiffOn 𝒟.H_zero
      (by rw [hDH]; exact 𝒱.DH₀_surjective hCq hsurj) (by rw [hDH]) hKpos hZ
  exact ⟨⟨𝒱, hker, Z, hZ, hker ▸ hY, V', hV'rel, hV'0, σ, hσC, hσ0, hDσ, hsol, ε, hε, σ₀, hσ₀,
    hbound, huniq⟩⟩

namespace Sol

variable {𝒟} (𝒮 : 𝒟.Sol)

/-- `K̃ = ker DH(0)`. -/
abbrev Kt : Submodule ℝ P := LinearMap.ker (𝒮.DH₀ : P →ₗ[ℝ] Q)

lemma mem_K'_iff {x : P × W 0} : x ∈ 𝒟.K' ↔ x.1 ∈ 𝒮.Kt ∧ x.2 = 𝒮.L x.1 := by
  rw [𝒮.hker, mem_map_graphMap]

/-- The projection `π : K' → K̃`, `(α, Lα) ↦ α`. -/
def π : 𝒟.K' →L[ℝ] 𝒮.Kt where
  toFun := fun y => ⟨(y : P × W 0).1, (𝒮.mem_K'_iff.1 y.2).1⟩
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  cont := (continuous_fst.comp continuous_subtype_val).subtype_mk _

@[simp] lemma coe_π (y : 𝒟.K') : (𝒮.π y : P) = (y : P × W 0).1 := rfl

lemma snd_eq_L (y : 𝒟.K') : (y : P × W 0).2 = 𝒮.L (𝒮.π y) := (𝒮.mem_K'_iff.1 y.2).2

lemma coe_eq_graph (y : 𝒟.K') : (y : P × W 0) = graphMap 𝒮.L (𝒮.π y) :=
  Prod.ext rfl (𝒮.snd_eq_L y)

/-- The element `(α, Lα) ∈ K'` over `α ∈ K̃`. -/
def lift (α : 𝒮.Kt) : 𝒟.K' := ⟨graphMap 𝒮.L α, 𝒮.mem_K'_iff.2 ⟨α.2, rfl⟩⟩

@[simp] lemma coe_lift (α : 𝒮.Kt) : ((𝒮.lift α : 𝒟.K') : P × W 0) = graphMap 𝒮.L α := rfl

@[simp] lemma π_lift (α : 𝒮.Kt) : 𝒮.π (𝒮.lift α) = α := rfl

lemma lift_π (y : 𝒟.K') : 𝒮.lift (𝒮.π y) = y := Subtype.ext (𝒮.coe_eq_graph y).symm

lemma mem_C'_iff (y : 𝒟.K') : (y : P × W 0) ∈ Ct ×ˢ (univ : Set (W 0)) ↔ (𝒮.π y : P) ∈ Ct := by
  rw [𝒮.coe_eq_graph y, graphMap_mem_prod_iff]

/-- **The map `τ` of Theorem 3.43**: `τ(y) = −Dδ(0)π(y) + γ(π(y))` with
`γ(a) = σ(a) + δ(a + σ(a))`, i.e. `τ(y) = (σ(v), δ(v + σ(v)) − Lv)` for `y = (v, Lv)`. -/
def τ (y : 𝒟.K') : P × W 0 :=
  ((𝒮.σ (𝒮.π y) : P), W.toBase 1 (𝒟.δ ((𝒮.π y : P) + 𝒮.σ (𝒮.π y))) - 𝒮.L (𝒮.π y))

/-- The neighbourhood `V = π⁻¹(V')` of `0` in `K' ∩ C'`. -/
def V : Set 𝒟.K' := 𝒮.π ⁻¹' 𝒮.V'

lemma mem_V {y : 𝒟.K'} : y ∈ 𝒮.V ↔ 𝒮.π y ∈ 𝒮.V' := Iff.rfl

lemma V_relOpen : ∃ O : Set 𝒟.K', IsOpen O ∧ 𝒮.V = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ) := by
  obtain ⟨O, hO, hV'⟩ := 𝒮.V'_relOpen
  refine ⟨𝒮.π ⁻¹' O, hO.preimage 𝒮.π.continuous, ?_⟩
  ext y
  simp only [mem_V, hV', mem_inter_iff, mem_preimage, 𝒮.mem_C'_iff]

lemma zero_mem_V : (0 : 𝒟.K') ∈ 𝒮.V := by
  rw [mem_V, map_zero]; exact 𝒮.V'_zero

lemma τ_mem_Y (y : 𝒟.K') : 𝒮.τ y ∈ 𝒮.Z.prod ⊤ := ⟨(𝒮.σ (𝒮.π y)).2, Submodule.mem_top⟩

lemma τ_zero : 𝒮.τ 0 = 0 := by
  unfold τ
  rw [map_zero, 𝒮.σ_zero]
  change ((0 : P), W.toBase 1 (𝒟.δ (0 + 0)) - 𝒮.L 0) = 0
  rw [add_zero, 𝒟.δ_zero, map_zero, map_zero, sub_zero]; rfl

/-- `y + τ(y) = (a, δ(a))` with `a = π(y) + σ(π(y))`. -/
lemma coe_add_τ (y : 𝒟.K') :
    (y : P × W 0) + 𝒮.τ y = ((ScBanach.paramProd P W).toBase 1
      (((𝒮.π y : P) + 𝒮.σ (𝒮.π y), 𝒟.δ ((𝒮.π y : P) + 𝒮.σ (𝒮.π y))) :
        (ScBanach.paramProd P W) 1)) := by
  rw [ScBanach.paramProd_toBase, 𝒮.coe_eq_graph y, graphMap_apply]
  unfold τ
  ext
  · rfl
  · change 𝒮.L (𝒮.π y) + (W.toBase 1 (𝒟.δ _) - 𝒮.L (𝒮.π y)) = W.toBase 1 (𝒟.δ _)
    abel

/-- **Theorem 3.43 (3), first half**: `g(y + τ(y)) = 0` for `y ∈ V`, and `y + τ(y) ∈ U`. -/
theorem sol_mem_and_eq_zero {y : 𝒟.K'} (hy : y ∈ 𝒮.V) :
    (y : P × W 0) + 𝒮.τ y ∈ 𝒟.G₀.U 0 ∧ 𝒟.g ((y : P × W 0) + 𝒮.τ y) = 0 := by
  obtain ⟨hmem, hH⟩ := 𝒮.σ_sol _ hy
  have ha : (𝒮.π y : P) + 𝒮.σ (𝒮.π y) ∈ 𝒟.𝒞.N 0 ∩ Ct := 𝒮.sub hmem
  rw [𝒮.coe_add_τ]
  refine ⟨𝒟.G₀.toBase_mem (𝒟.sol_mem ha), ?_⟩
  refine Prod.ext ?_ (𝒟.snd_g_sol ha)
  have := 𝒟.H_eq ha
  unfold H at this
  rw [ScBanach.paramProd_toBase]
  change (𝒟.g (_, W.toBase 1 (𝒟.δ _))).1 = 0
  rw [this, ← 𝒟.H_eq ha, hH]

/-! #### Regularity of `τ` on level `1` -/

lemma a_contDiffOn : ContDiffOn ℝ 1 (fun y : 𝒟.K' => (𝒮.π y : P) + (𝒮.σ (𝒮.π y) : P)) 𝒮.V := by
  have h1 : ContDiffOn ℝ 1 (fun y : 𝒟.K' => (𝒮.π y : P)) 𝒮.V :=
    (𝒮.Kt.subtypeL.comp 𝒮.π).contDiff.contDiffOn
  have h2 : ContDiffOn ℝ 1 (fun y : 𝒟.K' => (𝒮.σ (𝒮.π y) : P)) 𝒮.V :=
    𝒮.Z.subtypeL.contDiff.comp_contDiffOn
      (𝒮.σ_contDiffOn.comp 𝒮.π.contDiff.contDiffOn fun _ hy => hy)
  exact h1.add h2

lemma a_mapsTo : MapsTo (fun y : 𝒟.K' => (𝒮.π y : P) + (𝒮.σ (𝒮.π y) : P)) 𝒮.V 𝒮.V₁ :=
  fun _ hy => (𝒮.σ_sol _ hy).1

/-- **Theorem 3.43, "a `C¹`-map `τ : V → Y'₁`"**: `τ` is `C¹` on `V`. -/
theorem τ_contDiffOn : ContDiffOn ℝ 1 𝒮.τ 𝒮.V := by
  have h1 : ContDiffOn ℝ 1 (fun y : 𝒟.K' => (𝒮.σ (𝒮.π y) : P)) 𝒮.V :=
    𝒮.Z.subtypeL.contDiff.comp_contDiffOn
      (𝒮.σ_contDiffOn.comp 𝒮.π.contDiff.contDiffOn fun _ hy => hy)
  have h2 : ContDiffOn ℝ 1 (fun y : 𝒟.K' =>
      W.toBase 1 (𝒟.δ ((𝒮.π y : P) + (𝒮.σ (𝒮.π y) : P)))) 𝒮.V :=
    (W.toBase 1).contDiff.comp_contDiffOn (𝒮.δ_contDiffOn.comp 𝒮.a_contDiffOn 𝒮.a_mapsTo)
  have h3 : ContDiffOn ℝ 1 (fun y : 𝒟.K' => 𝒮.L (𝒮.π y)) 𝒮.V :=
    (𝒮.L.comp (𝒮.Kt.subtypeL.comp 𝒮.π)).contDiff.contDiffOn
  exact h1.prodMk (h2.sub h3)

/-- `τ(y) ∈ Y'₁ = Z ⊕ W₁`: the `W`-component of `τ(y)` lies on level `1`. -/
theorem snd_τ_mem_range (y : 𝒟.K') : (𝒮.τ y).2 ∈ range (W.toBase 1) :=
  ⟨𝒟.δ ((𝒮.π y : P) + 𝒮.σ (𝒮.π y)) - 𝒮.Dδ₀ (𝒮.π y), by rw [map_sub]; rfl⟩

/-! #### Regularity of `τ` on all levels: Theorem 3.43 (1) -/

/-- **Theorem 3.43 (1), "`τ` is sc-smooth"**: for every `k ≥ 1` there are a relatively open
neighbourhood `V_k ⊆ V` of `0` in `K' ∩ C'` and a `C^k`-map `τ_k : V_k → E_k = ℝⁿ' ⊕ W_k` lifting
`τ` (`ι_k ∘ τ_k = τ` on `V_k`).  Proof: Theorem 3.78 applied to the `C^k`-map `H` on `U'_k ∩ V₁`
gives a `C^k` solution `σ_k` which agrees with `σ` near `0` by the uniqueness clause (3) of
Theorem 3.78 (`σ` is continuous with `σ(0) = 0`); the `W`-component of `τ` is
`ι(δ(a)) − L(πy)`, `a = πy + σ(πy)`, where `δ` lifts to a `C^k`-map `δ' : U'_k → W_{2k}`
(`H_contDiffOn`) and `L = ι_{2k} ∘ Dδ'(0)` by the uniqueness of the derivative at `0`. -/
theorem exists_contDiffOn_level (hCp : IsPartialQuadrant (ScBanach.const P) Ct)
    (hsurj : Surjective 𝒟.Dg) (hpos : IsInGoodPosition (ScBanach.paramProd P W) (Ct ×ˢ univ) 𝒟.K')
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ Vk : Set 𝒟.K', (∃ O : Set 𝒟.K', IsOpen O ∧ Vk = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧
      (0 : 𝒟.K') ∈ Vk ∧ Vk ⊆ 𝒮.V ∧
      ∃ τk : 𝒟.K' → (ScBanach.paramProd P W) k, ContDiffOn ℝ k τk Vk ∧
        ∀ y ∈ Vk, (ScBanach.paramProd P W).toBase k (τk y) = 𝒮.τ y := by
  classical
  have hCq := hCp.isQuadrantLike
  have hkne : (k : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  -- level-`k` regularity of `H` and `δ`
  obtain ⟨VH, ⟨OH, hOH, hVH⟩, h0H, -, hHC, δ', hδ'C, hδ'⟩ := 𝒟.H_contDiffOn hCq k hk
  obtain ⟨O₁, hO₁, hV₁⟩ := 𝒮.relOpen
  -- the common domain `U = U'_k ∩ V₁`
  set U : Set P := VH ∩ 𝒮.V₁ with hU
  have hUeq : U = (OH ∩ O₁) ∩ Ct := by
    rw [hU, hVH, hV₁]; ext a; simp only [mem_inter_iff]; tauto
  have h0U : (0 : P) ∈ U := ⟨h0H, 𝒮.zero_mem⟩
  have hUrel : IsRelOpenInQuadrant (ScBanach.const P) Ct U := ⟨hCp, OH ∩ O₁, hOH.inter hO₁, hUeq⟩
  have huniqU : UniqueDiffWithinAt ℝ U 0 := by
    rw [hUeq]
    exact hCq.uniqueDiffWithinAt (m := 0) (hOH.inter hO₁)
      (show (0 : P) ∈ (OH ∩ O₁) ∩ (ScBanach.const P).lvlSet Ct 0 from hUeq ▸ h0U)
  have h0OH : (0 : P) ∈ OH := by
    have := h0H; rw [hVH] at this; exact this.1
  have hUsub₁ : U ⊆ 𝒮.V₁ := inter_subset_right
  have hUsubH : U ⊆ VH := inter_subset_left
  -- the derivative of `H` on `U`
  have hDH : fderivWithin ℝ 𝒟.H U 0 = 𝒮.DH₀ :=
    (𝒮.hasFDerivWithinAt_H.mono hUsub₁).fderivWithin huniqU
  have hpos' : IsInGoodPosition (ScBanach.paramProd P W) (Ct ×ˢ univ)
      ((LinearMap.ker (𝒮.DH₀ : P →ₗ[ℝ] Q)).map (graphMap 𝒮.L)) := 𝒮.hker ▸ hpos
  have hKpos := lemma_3_46_isInGoodPosition hpos'
  -- Theorem 3.78 for `H` on `U` with regularity `k`
  obtain ⟨V'k, σk, εk, σ₀k, hV'krel, hV'k0, hσkC, -, -, hsolk, hεk, hσ₀k, -, huniqk⟩ :=
    theorem_3_78 hUrel h0U (j := k) hk (hHC.mono hUsubH) 𝒟.H_zero
      (by rw [hDH]; exact 𝒮.DH₀_surjective hCq hsurj) (by rw [hDH]) hKpos 𝒮.hZ
  -- `σ = σ_k` near `0`
  have hσc : ContinuousWithinAt (fun y : 𝒮.Kt => (𝒮.σ y : P)) 𝒮.V' 0 :=
    (𝒮.Z.subtypeL.continuous.comp_continuousOn
      (𝒮.σ_contDiffOn.continuousOn)) 0 𝒮.V'_zero
  have hac : ContinuousWithinAt (fun y : 𝒮.Kt => (y : P) + (𝒮.σ y : P)) 𝒮.V' 0 :=
    (continuous_subtype_val.continuousWithinAt).add hσc
  have hev : ∀ᶠ y in 𝓝[𝒮.V'] (0 : 𝒮.Kt), ‖(𝒮.σ y : P)‖ ≤ σ₀k ∧
      ((y : 𝒮.Kt) : P) + (𝒮.σ y : P) ∈ OH ∧ ‖y‖ ≤ εk := by
    have h1 : ∀ᶠ y in 𝓝[𝒮.V'] (0 : 𝒮.Kt), ‖(𝒮.σ y : P)‖ ≤ σ₀k := by
      have := hσc.tendsto
      rw [𝒮.σ_zero, Submodule.coe_zero] at this
      exact this.eventually (Metric.eventually_nhds_iff.2 ⟨σ₀k, hσ₀k, fun z hz => by
        rw [dist_zero_right] at hz; exact hz.le⟩)
    have h2 : ∀ᶠ y in 𝓝[𝒮.V'] (0 : 𝒮.Kt), ((y : 𝒮.Kt) : P) + (𝒮.σ y : P) ∈ OH := by
      have := hac.tendsto
      rw [Submodule.coe_zero, 𝒮.σ_zero, Submodule.coe_zero, add_zero] at this
      exact this.eventually (hOH.mem_nhds h0OH)
    have h3 : ∀ᶠ y in 𝓝[𝒮.V'] (0 : 𝒮.Kt), ‖y‖ ≤ εk :=
      eventually_nhdsWithin_of_eventually_nhds (Metric.eventually_nhds_iff.2 ⟨εk, hεk,
        fun y hy => by rw [dist_zero_right] at hy; exact hy.le⟩)
    exact h1.and (h2.and h3)
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.mem_nhdsWithin_iff.1 hev
  -- the neighbourhood `V''_k ⊆ K̃` and `V_k = π⁻¹(V''_k)`
  obtain ⟨O'k, hO'k, hV'k⟩ := hV'krel
  obtain ⟨O', hO', hV'⟩ := 𝒮.V'_relOpen
  set V''k : Set 𝒮.Kt := V'k ∩ 𝒮.V' ∩ Metric.ball 0 ρ with hV''k
  have hV''eq : V''k = (O'k ∩ O' ∩ Metric.ball 0 ρ) ∩ Subtype.val ⁻¹' Ct := by
    rw [hV''k, hV'k, hV']; ext y; simp only [mem_inter_iff, mem_preimage]; tauto
  have hσeq : ∀ y ∈ V''k, 𝒮.σ y = σk y := fun y hy => by
    have hyV' : y ∈ 𝒮.V' := hy.1.2
    obtain ⟨hb, hO, hε⟩ := hρ' ⟨hy.2, hyV'⟩
    obtain ⟨hmem, hH⟩ := 𝒮.σ_sol y hyV'
    have hmemU : (y : P) + (𝒮.σ y : P) ∈ U := ⟨by rw [hVH]; exact ⟨hO, (𝒮.sub hmem).2⟩, hmem⟩
    exact Subtype.ext (huniqk y hy.1.1 hε (𝒮.σ y : P) (𝒮.σ y).2 hb hmemU hH)
  have hσC : ContDiffOn ℝ k 𝒮.σ V''k :=
    (hσkC.mono fun y hy => hy.1.1).congr fun y hy => hσeq y hy
  set Vk : Set 𝒟.K' := 𝒮.π ⁻¹' V''k with hVk
  have hVkV : Vk ⊆ 𝒮.V := fun y hy => hy.1.2
  have hVk0 : (0 : 𝒟.K') ∈ Vk := by
    show 𝒮.π 0 ∈ V''k
    rw [map_zero]
    exact ⟨⟨hV'k0, 𝒮.V'_zero⟩, Metric.mem_ball_self hρ⟩
  have hVkrel : ∃ O : Set 𝒟.K', IsOpen O ∧ Vk = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ) := by
    refine ⟨𝒮.π ⁻¹' (O'k ∩ O' ∩ Metric.ball 0 ρ),
      ((hO'k.inter hO').inter Metric.isOpen_ball).preimage 𝒮.π.continuous, ?_⟩
    ext y
    simp only [hVk, mem_preimage, hV''eq, mem_inter_iff, 𝒮.mem_C'_iff]
  -- `a(y) = πy + σ(πy) ∈ U'_k` for `y ∈ V_k`
  have haVH : ∀ y ∈ Vk, (𝒮.π y : P) + (𝒮.σ (𝒮.π y) : P) ∈ VH := fun y hy => by
    rw [hσeq _ hy]
    exact hUsubH (hsolk _ hy.1.1).1
  -- the lift of `L`: `L = ι_{2k} ∘ Dδ'(0)`
  set Dδ'₀ : P →L[ℝ] W (k + k) := fderivWithin ℝ δ' VH 0 with hDδ'₀
  have hδ'd : HasFDerivWithinAt (fun a => W.toBase (k + k) (δ' a)) ((W.toBase (k + k)).comp Dδ'₀) U 0 :=
    (W.toBase (k + k)).hasFDerivAt.comp_hasFDerivWithinAt 0
      (((hδ'C.differentiableOn hkne) 0 h0H).hasFDerivWithinAt.mono hUsubH)
  have hδd : HasFDerivWithinAt (fun a => W.toBase 1 (𝒟.δ a)) 𝒮.L U 0 :=
    (W.toBase 1).hasFDerivAt.comp_hasFDerivWithinAt 0 (𝒮.hasFDerivWithinAt_δ.mono hUsub₁)
  have hL : 𝒮.L = (W.toBase (k + k)).comp Dδ'₀ := by
    refine huniqU.eq hδd (hδ'd.congr (fun a ha => ?_) ?_)
    · exact (hδ' a (hUsubH ha)).symm
    · exact (hδ' 0 h0H).symm
  -- the lift `τ_k`
  set τk : 𝒟.K' → (ScBanach.paramProd P W) k := fun y =>
    ((𝒮.σ (𝒮.π y) : P), W.inclK k k (δ' ((𝒮.π y : P) + (𝒮.σ (𝒮.π y) : P))) -
      W.inclK k k (Dδ'₀ (𝒮.π y))) with hτk
  refine ⟨Vk, hVkrel, hVk0, hVkV, τk, ?_, fun y hy => ?_⟩
  · -- `C^k` regularity
    have hπ : ContDiffOn ℝ k (fun y : 𝒟.K' => 𝒮.π y) Vk := 𝒮.π.contDiff.contDiffOn
    have hπmaps : MapsTo (fun y : 𝒟.K' => 𝒮.π y) Vk V''k := fun y hy => hy
    have h1 : ContDiffOn ℝ k (fun y : 𝒟.K' => (𝒮.σ (𝒮.π y) : P)) Vk :=
      𝒮.Z.subtypeL.contDiff.comp_contDiffOn (hσC.comp hπ hπmaps)
    have ha : ContDiffOn ℝ k (fun y : 𝒟.K' => (𝒮.π y : P) + (𝒮.σ (𝒮.π y) : P)) Vk :=
      ((𝒮.Kt.subtypeL.comp 𝒮.π).contDiff.contDiffOn).add h1
    have h2 : ContDiffOn ℝ k (fun y : 𝒟.K' =>
        W.inclK k k (δ' ((𝒮.π y : P) + (𝒮.σ (𝒮.π y) : P)))) Vk :=
      (W.inclK k k).contDiff.comp_contDiffOn (hδ'C.comp ha haVH)
    have h3 : ContDiffOn ℝ k (fun y : 𝒟.K' => W.inclK k k (Dδ'₀ (𝒮.π y))) Vk :=
      ((W.inclK k k).comp (Dδ'₀.comp (𝒮.Kt.subtypeL.comp 𝒮.π))).contDiff.contDiffOn
    exact h1.prodMk (h2.sub h3)
  · -- `ι_k ∘ τ_k = τ`
    rw [hτk]
    simp only
    rw [ScBanach.paramProd_toBase]
    unfold τ
    refine Prod.ext rfl ?_
    show W.toBase k (W.inclK k k _ - W.inclK k k _) = _
    rw [map_sub, W.toBase_inclK, W.toBase_inclK, hδ' _ (haVH y hy), hL]
    rfl

include hC in
lemma uniqueDiffWithinAt_V (hpos : IsInGoodPosition (ScBanach.paramProd P W) (Ct ×ˢ univ) 𝒟.K') :
    UniqueDiffWithinAt ℝ 𝒮.V 0 := by
  obtain ⟨O, hO, hV⟩ := 𝒮.V_relOpen
  have h0 := 𝒮.zero_mem_V
  rw [hV] at h0 ⊢
  have hconv : Convex ℝ (Subtype.val ⁻¹' (Ct ×ˢ univ) : Set 𝒟.K') := by
    have hC' : Convex ℝ (Ct ×ˢ (univ : Set (W 0))) := by
      have := hC.convex 0
      rw [ScBanach.const_lvlSet] at this
      exact this.prod convex_univ
    exact hC'.linear_preimage 𝒟.K'.subtype
  rw [inter_comm]
  exact (uniqueDiffWithinAt_convex hconv hpos.interior_nonempty (subset_closure h0.2)).inter
    (hO.mem_nhds h0.1)

/-- The derivative of `τ` at `0` vanishes: `Dτ(0)η = −Dδ(0)π(η) + Dδ(0)π(η) = 0`. -/
theorem hasFDerivWithinAt_τ : HasFDerivWithinAt 𝒮.τ (0 : 𝒟.K' →L[ℝ] P × W 0) 𝒮.V 0 := by
  -- `σ ∘ π`
  have hσ : HasFDerivWithinAt 𝒮.σ (0 : 𝒮.Kt →L[ℝ] 𝒮.Z) 𝒮.V' 0 := by
    have := (𝒮.σ_contDiffOn.differentiableOn one_ne_zero 0 𝒮.V'_zero).hasFDerivWithinAt
    rwa [𝒮.fderiv_σ] at this
  have hπ : HasFDerivWithinAt 𝒮.π (𝒮.π : 𝒟.K' →L[ℝ] 𝒮.Kt) 𝒮.V 0 := 𝒮.π.hasFDerivWithinAt
  have hπ0 : 𝒮.π 0 = 0 := map_zero _
  have hσπ : HasFDerivWithinAt (fun y => 𝒮.σ (𝒮.π y)) (0 : 𝒟.K' →L[ℝ] 𝒮.Z) 𝒮.V 0 := by
    have hσ' : HasFDerivWithinAt 𝒮.σ (0 : 𝒮.Kt →L[ℝ] 𝒮.Z) 𝒮.V' (𝒮.π 0) := by rw [hπ0]; exact hσ
    have := hσ'.comp (0 : 𝒟.K') hπ fun _ hy => hy
    rw [ContinuousLinearMap.zero_comp] at this
    exact this
  -- `a = π + σ ∘ π`
  set πP : 𝒟.K' →L[ℝ] P := 𝒮.Kt.subtypeL.comp 𝒮.π with hπP
  have ha : HasFDerivWithinAt (fun y : 𝒟.K' => (𝒮.π y : P) + (𝒮.σ (𝒮.π y) : P)) πP 𝒮.V 0 := by
    have h1 : HasFDerivWithinAt (fun y : 𝒟.K' => (𝒮.π y : P)) πP 𝒮.V 0 := πP.hasFDerivWithinAt
    have h2 := (𝒮.Z.subtypeL.hasFDerivAt).comp_hasFDerivWithinAt (0 : 𝒟.K') hσπ
    have := h1.add h2
    rw [ContinuousLinearMap.comp_zero, add_zero] at this
    exact this
  have ha0 : (fun y : 𝒟.K' => (𝒮.π y : P) + (𝒮.σ (𝒮.π y) : P)) 0 = 0 := by
    simp [hπ0, 𝒮.σ_zero]
  -- `δ ∘ a`
  have hδ : HasFDerivWithinAt 𝒟.δ 𝒮.Dδ₀ 𝒮.V₁
      ((fun y : 𝒟.K' => (𝒮.π y : P) + (𝒮.σ (𝒮.π y) : P)) 0) := by
    rw [ha0]; exact 𝒮.hasFDerivWithinAt_δ
  have hδa := hδ.comp (0 : 𝒟.K') ha 𝒮.a_mapsTo
  have h2 := (W.toBase 1).hasFDerivAt.comp_hasFDerivWithinAt (0 : 𝒟.K') hδa
  have h3 : HasFDerivWithinAt (fun y : 𝒟.K' => 𝒮.L (𝒮.π y)) (𝒮.L.comp πP) 𝒮.V 0 :=
    (𝒮.L.comp πP).hasFDerivWithinAt
  have h4 := (𝒮.Z.subtypeL.hasFDerivAt).comp_hasFDerivWithinAt (0 : 𝒟.K') hσπ
  have h5 := h4.prodMk (h2.sub h3)
  refine h5.congr_fderiv ?_
  ext y
  · simp
  · change (W.toBase 1) (𝒮.Dδ₀ (πP y)) - 𝒮.L (πP y) = 0
    rw [sub_eq_zero]; rfl

include hC in
/-- **Theorem 3.43 (2)**: `Dτ(0) = 0`. -/
theorem fderivWithin_τ (hpos : IsInGoodPosition (ScBanach.paramProd P W) (Ct ×ˢ univ) 𝒟.K') :
    fderivWithin ℝ 𝒮.τ 𝒮.V 0 = 0 :=
  𝒮.hasFDerivWithinAt_τ.fderivWithin (𝒮.uniqueDiffWithinAt_V hC hpos)

/-! #### Every solution near `0` lies on the graph of `τ` -/

/-- The projection `P → K̃` along `Z`. -/
def projK : P →L[ℝ] 𝒮.Kt :=
  𝒮.Kt.projectionOntoL 𝒮.Z (Submodule.IsCompl.isTopCompl_of_isClosed 𝒮.hZ.isCompl
    (Submodule.closed_of_finiteDimensional _) (Submodule.closed_of_finiteDimensional _))

lemma sub_projK_mem (a : P) : a - 𝒮.projK a ∈ 𝒮.Z := by
  obtain ⟨k, hk, z, hz, rfl⟩ := Submodule.mem_sup.1
    (𝒮.hZ.isCompl.sup_eq_top ▸ Submodule.mem_top (x := a))
  have : 𝒮.projK (k + z) = ⟨k, hk⟩ := by
    unfold projK
    rw [map_add, Submodule.projectionOntoL_apply_right _ ⟨z, hz⟩, add_zero]
    exact Submodule.projectionOntoL_apply_left _ ⟨k, hk⟩
  rw [this]; simpa using hz

/-- **Theorem 3.43 (3), second half**: under the regularity hypothesis of Lemma 3.42 (solutions
near `0` on level `0` lie on level `1` and are small there), every solution `x` of `g(x) = 0`
near `0` is of the form `y + τ(y)` with `y ∈ V`.  Proof: `x = (a, w)` with `w = δ(a)` by the
uniqueness of the solution germ on level `1`, so `H(a) = 0`; `a = k + z` with `k ∈ K̃ ∩ C̃`
(`exists_proj_mem_of_eq_zero`) and `z = σ(k)` by the uniqueness clause of Theorem 3.78. -/
theorem exists_eq_add_τ
    (hreg : ∀ ε > 0, ∃ r > 0, ∀ x ∈ 𝒟.G₀.U 0, 𝒟.g x = 0 → ‖x‖ < r →
      ∃ w₁ : W 1, W.toBase 1 w₁ = x.2 ∧ ‖w₁‖ < ε) :
    ∃ U'' : Set (P × W 0), IsOpen U'' ∧ (0 : P × W 0) ∈ U'' ∧
      ∀ x ∈ U'' ∩ 𝒟.G₀.U 0, 𝒟.g x = 0 → ∃ y ∈ 𝒮.V, x = (y : P × W 0) + 𝒮.τ y := by
  classical
  -- the radii
  obtain ⟨r₁, hr₁, hreg'⟩ := hreg (𝒟.basic.contraction.rad' 0) (𝒟.basic.contraction.rad'_pos 0)
  have hprad := 𝒟.basic.contraction.prad_pos 0
  obtain ⟨O₁, hO₁, hV₁⟩ := 𝒮.relOpen
  have h0O₁ : (0 : P) ∈ O₁ := by have := 𝒮.zero_mem; rw [hV₁] at this; exact this.1
  obtain ⟨r₂, hr₂, hr₂'⟩ := Metric.isOpen_iff.1 hO₁ 0 h0O₁
  obtain ⟨ε_g, hε_g, hgood⟩ := 𝒮.hZ.exists_eps
  have hUC : 𝒮.V₁ ⊆ Ct := by rw [hV₁]; exact inter_subset_right
  obtain ⟨r₃, hr₃, hproj⟩ := exists_proj_mem_of_eq_zero hUC 𝒮.hasFDerivWithinAt_H 𝒟.H_zero rfl hε_g
    hgood 𝒮.hZ.isCompl
  obtain ⟨O', hO', hV'⟩ := 𝒮.V'_relOpen
  have h0O' : (0 : 𝒮.Kt) ∈ O' := by have := 𝒮.V'_zero; rw [hV'] at this; exact this.1
  obtain ⟨r₄, hr₄, hr₄'⟩ := Metric.isOpen_iff.1 hO' 0 h0O'
  set c : ℝ := ‖𝒮.projK‖ + 1 with hc
  have hcpos : 0 < c := by positivity
  set r : ℝ := min (min (min r₁ (𝒟.basic.contraction.prad 0)) (min r₂ r₃))
    (min (r₄ / c) (min (𝒮.ε / c) (𝒮.σ₀ / (c + 1)))) with hr
  have hrpos : 0 < r := by
    refine lt_min (lt_min (lt_min hr₁ hprad) (lt_min hr₂ hr₃)) (lt_min ?_ (lt_min ?_ ?_)) <;>
      first | positivity | exact div_pos 𝒮.ε_pos hcpos | exact div_pos 𝒮.σ₀_pos (by positivity)
  have hr1 : r ≤ r₁ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrN : r ≤ 𝒟.basic.contraction.prad 0 :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hr2 : r ≤ r₂ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr3 : r ≤ r₃ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr4 : r ≤ r₄ / c := (min_le_right _ _).trans (min_le_left _ _)
  have hrε : r ≤ 𝒮.ε / c := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrσ : r ≤ 𝒮.σ₀ / (c + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨Metric.ball 0 r, Metric.isOpen_ball, Metric.mem_ball_self hrpos, ?_⟩
  rintro x ⟨hxr, hxU⟩ hx0
  rw [Metric.mem_ball, dist_zero_right] at hxr
  obtain ⟨a, w⟩ := x
  have ha_norm : ‖a‖ < r := lt_of_le_of_lt (norm_fst_le (a, w)) hxr
  have haCt : a ∈ Ct := by
    have := 𝒟.G₀.U_subset 0 hxU
    rw [ScBanach.paramProd_lvlSet] at this
    exact this.1
  -- the solution lies on level `1` and is small there: `w = δ(a)`
  obtain ⟨w₁, hw₁, hw₁r⟩ := hreg' (a, w) hxU hx0 (hxr.trans_le hr1)
  have haN : a ∈ 𝒟.𝒞.N 0 ∩ Ct := by
    refine ⟨?_, haCt⟩
    show a ∈ Metric.ball 0 (𝒟.basic.contraction.prad 0)
    rw [Metric.mem_ball, dist_zero_right]; exact ha_norm.trans_le hrN
  have hwO : w₁ ∈ 𝒟.𝒞.O 0 := by
    show w₁ ∈ Metric.ball 0 (𝒟.basic.contraction.rad' 0)
    rw [Metric.mem_ball, dist_zero_right]; exact hw₁r
  have hmem1 : ((a, w₁) : P × W 1) ∈ 𝒟.G₁.U 0 := 𝒟.𝒞.mem_G 0 a haN w₁ hwO
  have hmem1' : ((a, w₁) : (ScBanach.paramProd P W) 1) ∈ 𝒟.G₀.U 1 := by rw [← 𝒟.G₁_U 0]; exact hmem1
  have hg₁ : 𝒟.g₁ (a, w₁) = 0 := by
    rw [𝒟.g₁_eq _ hmem1']
    apply (ScBanach.paramProd Q W).toBase_injective 1
    rw [(𝒟.isScSmooth 0).toBase_levelMap hmem1', ScBanach.paramProd_toBase, map_zero]
    change 𝒟.g (a, W.toBase 1 w₁) = 0
    rw [hw₁]; exact hx0
  have hwδ : w₁ = 𝒟.δ a := 𝒟.eq_δ haN hwO hmem1 (by rw [hg₁]; rfl)
  have hHa : 𝒟.H a = 0 := by
    rw [𝒟.H_eq haN, ← hwδ, hg₁]; rfl
  have haV₁ : a ∈ 𝒮.V₁ := by
    rw [hV₁]
    exact ⟨hr₂' (by rw [Metric.mem_ball, dist_zero_right]; exact ha_norm.trans_le hr2), haCt⟩
  -- the decomposition `a = k + z`
  set k : 𝒮.Kt := 𝒮.projK a with hk
  set z : P := a - 𝒮.projK a with hz
  have hzZ : z ∈ 𝒮.Z := 𝒮.sub_projK_mem a
  have hakz : a = (k : P) + z := by rw [hz]; abel
  have hknorm : ‖k‖ ≤ ‖𝒮.projK‖ * ‖a‖ := 𝒮.projK.le_opNorm a
  have hznorm : ‖z‖ ≤ (‖𝒮.projK‖ + 1) * ‖a‖ := by
    calc ‖z‖ ≤ ‖a‖ + ‖(k : P)‖ := norm_sub_le _ _
      _ ≤ ‖a‖ + ‖𝒮.projK‖ * ‖a‖ := by gcongr; exact hknorm
      _ = (‖𝒮.projK‖ + 1) * ‖a‖ := by ring
  obtain ⟨-, hkCt⟩ := hproj a haV₁ (ha_norm.trans_le hr3) hHa k k.2 z hzZ hakz
  have hkV' : k ∈ 𝒮.V' := by
    rw [hV']
    refine ⟨hr₄' ?_, hkCt⟩
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖k‖ ≤ ‖𝒮.projK‖ * ‖a‖ := hknorm
      _ ≤ c * ‖a‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < c * r := mul_lt_mul_of_pos_left ha_norm hcpos
      _ ≤ c * (r₄ / c) := by gcongr
      _ = r₄ := by field_simp
  have hkε : ‖k‖ ≤ 𝒮.ε := by
    calc ‖k‖ ≤ ‖𝒮.projK‖ * ‖a‖ := hknorm
      _ ≤ c * r := mul_le_mul (by linarith) ha_norm.le (norm_nonneg _) hcpos.le
      _ ≤ c * (𝒮.ε / c) := by gcongr
      _ = 𝒮.ε := by field_simp
  have hzσ : ‖z‖ ≤ 𝒮.σ₀ := by
    calc ‖z‖ ≤ (‖𝒮.projK‖ + 1) * ‖a‖ := hznorm
      _ ≤ (c + 1) * r := mul_le_mul (by linarith) ha_norm.le (norm_nonneg _) (by positivity)
      _ ≤ (c + 1) * (𝒮.σ₀ / (c + 1)) := by gcongr
      _ = 𝒮.σ₀ := by field_simp
  have hzσk : z = 𝒮.σ k :=
    𝒮.σ_unique k hkV' hkε z hzZ hzσ (hakz ▸ haV₁) (hakz ▸ hHa)
  -- `x = y + τ(y)` with `y = (k, Lk)`
  refine ⟨𝒮.lift k, by rw [mem_V, π_lift]; exact hkV', ?_⟩
  rw [𝒮.coe_add_τ, π_lift, ← hzσk, ← hakz, ScBanach.paramProd_toBase, ← hwδ, hw₁]

end Sol

/-- **Theorem 3.43 (Local Germ-Solvability I), germ form.**  Let `g : O(C̃ ⊕ W, 0) → ℝᴺ ⊕ W` be an
sc-smooth germ with `g(0) = 0` whose index-raised germ `g¹` is a basic germ (the `g = Φ_*(f)` of
Theorem 3.38, with `C̃ ⊆ ℝⁿ'` a partial quadrant).  Assume `Dg(0)` is surjective, `K' = ker Dg(0)`
is in good position to `C' = C̃ ⊕ W`, and (the content of Lemma 3.42, which the text derives from
Theorem 3.40 for `f = h + s`) that the solutions of `g = 0` near `0` on level `0` lie on level
`1` and are small there.  Then there are a good complement `Y' = Z ⊕ W` of `K'`, a relatively
open neighbourhood `V` of `0` in `K' ∩ C'` and a `C¹`-map `τ : V → Y'` with values in `Y'₁`
such that (2) `τ(0) = 0`, `Dτ(0) = 0`, and (3) the zero set of `g` near `0` is
`{y + τ(y) | y ∈ V}`: every `y + τ(y)` is a zero in `U`, and every zero `x` of `g` in `U`
close to `0` is of this form; and (1) `τ` is sc-smooth: for every `k ≥ 1` it lifts, on a
relatively open neighbourhood `V_k ⊆ V` of `0`, to a `C^k`-map `τ_k : V_k → E_k`
(`Sol.exists_contDiffOn_level`).  `theorem_3_43` is the same statement without (1). -/
theorem _root_.Polyfold.theorem_3_43_sc_smooth (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    (𝒟 : ShiftedBasicData Ct W Q) (hsurj : Surjective 𝒟.Dg)
    (hpos : IsInGoodPosition (ScBanach.paramProd P W) (Ct ×ˢ univ) 𝒟.K')
    (hreg : ∀ ε > 0, ∃ r > 0, ∀ x ∈ 𝒟.G₀.U 0, 𝒟.g x = 0 → ‖x‖ < r →
      ∃ w₁ : W 1, W.toBase 1 w₁ = x.2 ∧ ‖w₁‖ < ε) :
    ∃ (Y : Submodule ℝ (P × W 0)) (V : Set 𝒟.K') (τ : 𝒟.K' → P × W 0),
      IsGoodComplement (ScBanach.paramProd P W) (Ct ×ˢ univ) 𝒟.K' Y ∧
      (∃ O : Set 𝒟.K', IsOpen O ∧ V = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧ (0 : 𝒟.K') ∈ V ∧
      (∀ y, τ y ∈ Y) ∧ (∀ y, (τ y).2 ∈ range (W.toBase 1)) ∧
      ContDiffOn ℝ 1 τ V ∧ τ 0 = 0 ∧ fderivWithin ℝ τ V 0 = 0 ∧
      (∀ y ∈ V, (y : P × W 0) + τ y ∈ 𝒟.G₀.U 0 ∧ 𝒟.g ((y : P × W 0) + τ y) = 0) ∧
      (∀ k : ℕ, 1 ≤ k → ∃ Vk : Set 𝒟.K',
        (∃ O : Set 𝒟.K', IsOpen O ∧ Vk = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧
        (0 : 𝒟.K') ∈ Vk ∧ Vk ⊆ V ∧
        ∃ τk : 𝒟.K' → (ScBanach.paramProd P W) k, ContDiffOn ℝ k τk Vk ∧
          ∀ y ∈ Vk, (ScBanach.paramProd P W).toBase k (τk y) = τ y) ∧
      ∃ U'' : Set (P × W 0), IsOpen U'' ∧ (0 : P × W 0) ∈ U'' ∧
        ∀ x ∈ U'' ∩ 𝒟.G₀.U 0, 𝒟.g x = 0 → ∃ y ∈ V, x = (y : P × W 0) + τ y := by
  obtain ⟨𝒮⟩ := 𝒟.exists_sol hC hsurj hpos
  exact ⟨𝒮.Z.prod ⊤, 𝒮.V, 𝒮.τ, 𝒮.hY, 𝒮.V_relOpen, 𝒮.zero_mem_V, 𝒮.τ_mem_Y, 𝒮.snd_τ_mem_range,
    𝒮.τ_contDiffOn, 𝒮.τ_zero, 𝒮.fderivWithin_τ hC.isQuadrantLike hpos,
    fun _ hy => 𝒮.sol_mem_and_eq_zero hy,
    fun k hk => 𝒮.exists_contDiffOn_level hC hsurj hpos k hk, 𝒮.exists_eq_add_τ hreg⟩

/-- **Theorem 3.43** without the regularity clause (1) (the form used by the global
implicit function theorem, §3.6); see `theorem_3_43_sc_smooth` for the full statement. -/
theorem _root_.Polyfold.theorem_3_43 (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    (𝒟 : ShiftedBasicData Ct W Q) (hsurj : Surjective 𝒟.Dg)
    (hpos : IsInGoodPosition (ScBanach.paramProd P W) (Ct ×ˢ univ) 𝒟.K')
    (hreg : ∀ ε > 0, ∃ r > 0, ∀ x ∈ 𝒟.G₀.U 0, 𝒟.g x = 0 → ‖x‖ < r →
      ∃ w₁ : W 1, W.toBase 1 w₁ = x.2 ∧ ‖w₁‖ < ε) :
    ∃ (Y : Submodule ℝ (P × W 0)) (V : Set 𝒟.K') (τ : 𝒟.K' → P × W 0),
      IsGoodComplement (ScBanach.paramProd P W) (Ct ×ˢ univ) 𝒟.K' Y ∧
      (∃ O : Set 𝒟.K', IsOpen O ∧ V = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧ (0 : 𝒟.K') ∈ V ∧
      (∀ y, τ y ∈ Y) ∧ (∀ y, (τ y).2 ∈ range (W.toBase 1)) ∧
      ContDiffOn ℝ 1 τ V ∧ τ 0 = 0 ∧ fderivWithin ℝ τ V 0 = 0 ∧
      (∀ y ∈ V, (y : P × W 0) + τ y ∈ 𝒟.G₀.U 0 ∧ 𝒟.g ((y : P × W 0) + τ y) = 0) ∧
      ∃ U'' : Set (P × W 0), IsOpen U'' ∧ (0 : P × W 0) ∈ U'' ∧
        ∀ x ∈ U'' ∩ 𝒟.G₀.U 0, 𝒟.g x = 0 → ∃ y ∈ V, x = (y : P × W 0) + τ y := by
  obtain ⟨Y, V, τ, h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h10⟩ :=
    theorem_3_43_sc_smooth hC 𝒟 hsurj hpos hreg
  exact ⟨Y, V, τ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

end ShiftedBasicData

/-! ### From Theorem 3.38 to Theorem 3.43: the push-forward of `f + s` -/

namespace StabilityData

variable (𝒮 : StabilityData Ct W) {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [FiniteDimensional ℝ Q] {f : P × W 0 → Q × W 0} {B : P × W 0 → W 0}

/-- The push-forward `g = Φ_*(f + s)` of Theorem 3.38 as the data of Theorem 3.43: `g` on level
`0` (`pushMap₀`) with its index-raised basic germ `g¹ = pushMap f` (Theorem 3.38). -/
def toShiftedBasicData (hC : IsQuadrantLike (ScBanach.const P) Ct) (hf : IsBasicGerm Ct 𝒮.G f B) :
    ShiftedBasicData (Ct ×ˢ (univ : Set 𝒮.Cs)) 𝒮.XB (Q × 𝒮.Zs) where
  G₀ := 𝒮.pushGerm₀
  g := 𝒮.pushMap₀ f
  isScSmooth := 𝒮.pushMap₀_isScSmoothGerm hC hf.isScSmooth
  g_zero := 𝒮.pushMap₀_zero hf.f_zero
  G₁ := 𝒮.pushGerm
  G₁_U := fun _ => rfl
  g₁ := 𝒮.pushMap f
  g₁_eq := fun _ hx => 𝒮.pushMap_eq_levelMap_pushMap₀ hf.isScSmooth hx
  B := 𝒮.pushB B
  basic := theorem_3_38 𝒮 hC hf

/-- **Lemma 3.42** (the regularity of the solutions of the pushed-forward germ, from Theorem
3.40): for every `ε > 0` there is `r > 0` such that every zero `x'` of `g = Φ_*(f + s)` in
`ψ(U)` with `|x'|₀ < r` has its `X`-component on level `1` with `|·|₁ < ε`.  Proof: `ψ⁻¹(x')` is a
zero of `f + s`, so by the lifts of Theorem 3.40 (`IsSc0ContractionGerm.exists_lift`, continuous
at `0`) it lies on level `1` and is small there; `ψ` is linear on level `1`. -/
theorem lemma_3_42 (hC : IsPartialQuadrant (ScBanach.const P) Ct) (hf : IsBasicGerm Ct 𝒮.G f B) :
    ∀ ε > 0, ∃ r > 0, ∀ x ∈ 𝒮.pushGerm₀.U 0, 𝒮.pushMap₀ f x = 0 → ‖x‖ < r →
      ∃ w₁ : 𝒮.XB 1, 𝒮.XB.toBase 1 w₁ = x.2 ∧ ‖w₁‖ < ε := by
  intro ε hε
  obtain ⟨τ, hτ, -, L, hL, hLc⟩ := hf.contraction.exists_lift hC.isClosed (𝒮.isScSmooth 0)
    𝒮.s_zero 1
  have h0sol : (0 : (ScBanach.paramProd P W) 0) ∈ solSet Ct B 𝒮.s τ :=
    hf.contraction.zero_mem_solSet 𝒮.s_zero hτ.le
  have hL0 : L 0 = 0 := (ScBanach.paramProd P W).toBase_injective 1 (by rw [(hL 0 h0sol).1, map_zero])
  set c : ℝ := ‖𝒮.split₀ 1‖ + 1 with hc
  set c' : ℝ := ‖𝒮.glue₀ 0‖ + 1 with hc'
  have hcpos : 0 < c := by rw [hc]; positivity
  have hc'pos : 0 < c' := by rw [hc']; positivity
  have hcont := hLc 0 h0sol
  rw [Metric.continuousWithinAt_iff] at hcont
  obtain ⟨r₀, hr₀, hr₀'⟩ := hcont (ε / c) (by positivity)
  refine ⟨min (r₀ / c') (τ / c'), by positivity, fun x hx hx0 hxr => ?_⟩
  set x' : (ScBanach.paramProd P W) 0 := 𝒮.glue₀ 0 x with hx'
  have hx'U : x' ∈ 𝒮.G.U 0 := hx
  have hx'norm : ‖x'‖ ≤ ‖𝒮.glue₀ 0‖ * ‖x‖ := (𝒮.glue₀ 0).le_opNorm x
  have hx'r₀ : ‖x'‖ < r₀ := by
    calc ‖x'‖ ≤ ‖𝒮.glue₀ 0‖ * ‖x‖ := hx'norm
      _ ≤ c' * ‖x‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < c' * (r₀ / c') := mul_lt_mul_of_pos_left (hxr.trans_le (min_le_left _ _)) hc'pos
      _ = r₀ := mul_div_cancel₀ _ hc'pos.ne'
  have hx'τ : ‖x'‖ ≤ τ := by
    calc ‖x'‖ ≤ c' * ‖x‖ := hx'norm.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
      _ ≤ c' * (τ / c') := by gcongr; exact hxr.le.trans (min_le_right _ _)
      _ = τ := mul_div_cancel₀ _ hc'pos.ne'
  -- `x'` is a solution of `w = B(a, w) − s(a, w)`
  have hfs : 𝒮.fsum f x' = 0 := by
    have : 𝒮.fiber₀ 0 (𝒮.fsum f x') = 0 := hx0
    exact (𝒮.fiber₀_eq_zero_iff 0 _).1 this
  have hsol : x' ∈ solSet Ct B 𝒮.s τ := by
    refine ⟨?_, (norm_fst_le x').trans hx'τ, (norm_snd_le x').trans hx'τ, ?_⟩
    · have := 𝒮.G.U_subset 0 hx'U
      rw [ScBanach.paramProd_lvlSet] at this
      exact this.1
    · have h2 := congrArg Prod.snd hfs
      rw [fsum_apply, Prod.snd_add, hf.snd_eq _ hx'U] at h2
      change x'.2 - B x' + W.toBase 1 (𝒮.s x') = 0 at h2
      rw [sub_add_eq_add_sub, sub_eq_zero] at h2
      exact eq_sub_of_add_eq h2
  have hLx := hr₀' hsol (by rwa [dist_zero_right])
  rw [hL0, dist_zero_right] at hLx
  refine ⟨(𝒮.split₀ 1 (L x')).2, ?_, ?_⟩
  · have h1 := (hL x' hsol).1
    have h2 := congrArg Prod.snd (𝒮.split₀.toBase_comm 1 (L x'))
    rw [h1] at h2
    rw [ScBanach.paramProd_toBase] at h2
    dsimp only at h2
    change 𝒮.XB.toBase 1 (𝒮.split₀ 1 (L x')).2 = x.2
    rw [h2]
    have := congrArg Prod.snd (𝒮.split₀_glue₀ 0 x)
    exact this
  · calc ‖(𝒮.split₀ 1 (L x')).2‖ ≤ ‖𝒮.split₀ 1 (L x')‖ := norm_snd_le _
      _ ≤ ‖𝒮.split₀ 1‖ * ‖L x'‖ := (𝒮.split₀ 1).le_opNorm _
      _ ≤ c * ‖L x'‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < c * (ε / c) := mul_lt_mul_of_pos_left hLx hcpos
      _ = ε := mul_div_cancel₀ _ hcpos.ne'

/-- The derivative of `f + s` at `0`. -/
abbrev Dfs (f : P × W 0 → Q × W 0) : P × W 0 →L[ℝ] Q × W 0 :=
  scDerivGerm (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) 𝒮.G (𝒮.fsum f) 0

/-- `Dg(0) = Ψ ∘ D(f + s)(0) ∘ ψ⁻¹` (the chain rule for the linear coordinate changes). -/
theorem scDerivGerm_pushMap₀ (hC : IsQuadrantLike (ScBanach.const P) Ct)
    (hf : IsScSmoothGerm (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) 𝒮.G f) :
    scDerivGerm (E := 𝒮.E₀') (F := 𝒮.F₀' Q) 𝒮.pushGerm₀ (𝒮.pushMap₀ f) 0 =
      (𝒮.fiber₀ 0).comp ((𝒮.Dfs f).comp (𝒮.glue₀ 0)) := by
  have hE' : IsQuadrantLike 𝒮.E₀' ((Ct ×ˢ univ) ×ˢ univ) :=
    (hC.prod_univ_const (Q := 𝒮.Cs)).paramProd _
  have hCW := hC.paramProd W
  have hfs1 : IsSc1GermWith (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) 𝒮.G
      (𝒮.fsum f) (scDerivGerm 𝒮.G (𝒮.fsum f)) :=
    (𝒮.fsum_isScSmoothGerm hC hf 1).1.isSc1GermWith_scDerivGerm
  have hinner := hfs1.comp (𝒮.G.relOpenConvex hCW 1) (𝒮.glue₀.isSc1GermWith 𝒮.pushGerm₀)
    𝒮.glue₀_mapsToGerm
  have houter := (𝒮.fiber₀ (Q := Q)).isSc1GermWith (ScNbhdGerm.full _) |>.comp
    ((ScNbhdGerm.full _).relOpenConvex (isQuadrantLike_univ _) 1) hinner
    (𝒮.pushGerm₀.mapsToGerm_full _)
  have h := IsSc1Germ.scDerivGerm_eqOn hE' houter (𝒮.pushGerm₀.zero_mem 1)
  change scDerivGerm 𝒮.pushGerm₀ (𝒮.pushMap₀ f) 0 =
    (𝒮.fiber₀ 0).comp ((scDerivGerm 𝒮.G (𝒮.fsum f)
      (levelMap (E := 𝒮.E₀') (F := ScBanach.paramProd P W) (𝒮.glue₀ 0) 1 0)).comp (𝒮.glue₀ 0)) at h
  rw [ScOperator.levelMap_eq, map_zero] at h
  exact h

/-- `C̃ ⊕ V` is a partial quadrant in `P ⊕ V` (constant structure) for a finite-dimensional `V`. -/
lemma _root_.Polyfold.IsPartialQuadrant.const_prod_univ (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    IsPartialQuadrant (ScBanach.const (P × V)) (Ct ×ˢ (univ : Set V)) := by
  obtain ⟨n, W', T, hT⟩ := hC.prod_univ (ScBanach.const V)
  let I : ScIso (ScBanach.const (P × V)) ((ScBanach.const P).prod (ScBanach.const V)) :=
    { lvl := fun _ => ContinuousLinearEquiv.refl ℝ (P × V)
      incl_comm := fun _ _ => rfl }
  exact ⟨n, W', I.trans T, hT⟩

/-- **Theorem 3.47 (Corollary 3.47 of the text), the local core**: let `f : O(C̃ ⊕ W, 0) → ℝᴺ ⊕ W`
be a basic germ and `s` an sc⁺-germ with `s(0) = 0` (the data `𝒮` of Theorem 3.38), and assume
the linearization `D(f + s)(0)` is surjective with kernel `K` in good position to
`C = C̃ ⊕ W`.  Then there are a good complement `Y` of `K`, a relatively open neighbourhood `V` of
`0` in `K ∩ C` and a `C¹`-map `σ : V → Y` with values in `Y₁` such that (2) `σ(0) = 0`,
`Dσ(0) = 0`, and (3) the zero set of `f + s` in `U` near `0` is `{v + σ(v) | v ∈ V}`.  Proof:
Theorem 3.43 for the pushed-forward germ `g = Φ_*(f + s)` of Theorem 3.38 (Lemma 3.42 gives its
regularity hypothesis), transported back by the **linear** coordinate change `ψ`; the text's
nonlinear transport (the degeneracy index argument with Lemma 3.70 and Theorem 3.72) is not
needed since `ψ` is linear. -/
theorem _root_.Polyfold.theorem_3_47_sc_smooth (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    (𝒮 : StabilityData Ct W) (hf : IsBasicGerm Ct 𝒮.G f B) (hsurj : Surjective (𝒮.Dfs f))
    (hpos : IsInGoodPosition (ScBanach.paramProd P W) (Ct ×ˢ univ)
      (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0))) :
    ∃ (Y : Submodule ℝ (P × W 0))
      (V : Set (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)))
      (σ : LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0) → P × W 0),
      IsGoodComplement (ScBanach.paramProd P W) (Ct ×ˢ univ)
        (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)) Y ∧
      (∃ O, IsOpen O ∧ V = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧ 0 ∈ V ∧
      (∀ y, σ y ∈ Y) ∧ (∀ y, (σ y).2 ∈ range (W.toBase 1)) ∧
      ContDiffOn ℝ 1 σ V ∧ σ 0 = 0 ∧ fderivWithin ℝ σ V 0 = 0 ∧
      (∀ y ∈ V, (y : P × W 0) + σ y ∈ 𝒮.G.U 0 ∧ 𝒮.fsum f ((y : P × W 0) + σ y) = 0) ∧
      (∀ k : ℕ, 1 ≤ k → ∃ Vk : Set (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)),
        (∃ O : Set (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)),
          IsOpen O ∧ Vk = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧
        (0 : LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)) ∈ Vk ∧ Vk ⊆ V ∧
        ∃ σk : LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0) → (ScBanach.paramProd P W) k,
          ContDiffOn ℝ k σk Vk ∧ ∀ y ∈ Vk, (ScBanach.paramProd P W).toBase k (σk y) = σ y) ∧
      ∃ U'' : Set (P × W 0), IsOpen U'' ∧ (0 : P × W 0) ∈ U'' ∧
        ∀ x ∈ U'' ∩ 𝒮.G.U 0, 𝒮.fsum f x = 0 → ∃ y ∈ V, x = (y : P × W 0) + σ y := by
  classical
  have hCq := hC.isQuadrantLike
  set K := LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0) with hKdef
  set 𝒟 := 𝒮.toShiftedBasicData hCq hf with h𝒟
  -- the linear coordinate change `S = ψ` on level `0`
  let S : (P × W 0) ≃L[ℝ] 𝒮.E₀' 0 :=
    ContinuousLinearEquiv.equivOfInverse (𝒮.split₀ 0) (𝒮.glue₀ 0) (𝒮.glue₀_split₀ 0)
      (𝒮.split₀_glue₀ 0)
  have hS : ∀ x, S x = 𝒮.split₀ 0 x := fun _ => rfl
  have hS' : ∀ y, S.symm y = 𝒮.glue₀ 0 y := fun _ => rfl
  have hDg : 𝒟.Dg = (𝒮.fiber₀ 0).comp ((𝒮.Dfs f).comp (𝒮.glue₀ 0)) :=
    𝒮.scDerivGerm_pushMap₀ hCq hf.isScSmooth
  have hDg_apply : ∀ y, 𝒟.Dg y = 𝒮.fiber₀ 0 (𝒮.Dfs f (𝒮.glue₀ 0 y)) := fun y => by rw [hDg]; rfl
  -- the kernel
  have hK' : 𝒟.K' = K.map (S : P × W 0 →ₗ[ℝ] 𝒮.E₀' 0) := by
    ext y
    rw [Submodule.mem_map, LinearMap.mem_ker]
    constructor
    · intro hy
      refine ⟨𝒮.glue₀ 0 y, ?_, 𝒮.split₀_glue₀ 0 y⟩
      rw [LinearMap.mem_ker]
      have : 𝒟.Dg y = 0 := hy
      rw [hDg_apply] at this
      exact (𝒮.fiber₀_eq_zero_iff 0 _).1 this
    · rintro ⟨x, hx, rfl⟩
      change 𝒟.Dg (𝒮.split₀ 0 x) = 0
      rw [hDg_apply, 𝒮.glue₀_split₀]
      have : 𝒮.Dfs f x = 0 := hx
      rw [this, map_zero]
  have hS_mem : ∀ x : P × W 0, x ∈ Ct ×ˢ (univ : Set (W 0)) ↔
      S x ∈ (Ct ×ˢ univ) ×ˢ (univ : Set (𝒮.XB 0)) := fun x => by
    rw [hS, split₀_apply]
    constructor
    · intro h; exact ⟨⟨h.1, mem_univ _⟩, mem_univ _⟩
    · intro h; exact ⟨h.1.1, mem_univ _⟩
  have hS'_mem : ∀ y : 𝒮.E₀' 0, y ∈ (Ct ×ˢ univ) ×ˢ (univ : Set (𝒮.XB 0)) ↔
      S.symm y ∈ Ct ×ˢ (univ : Set (W 0)) := fun y => by
    rw [hS_mem (S.symm y), ContinuousLinearEquiv.apply_symm_apply]
  -- the restricted coordinate changes `K ≃ K'`
  have hSK : ∀ y : K, S y ∈ 𝒟.K' := fun y => by
    rw [hK']; exact ⟨y, y.2, rfl⟩
  have hSK' : ∀ y' : 𝒟.K', S.symm y' ∈ K := fun y' => by
    have hy : (y' : 𝒮.E₀' 0) ∈ K.map (S : P × W 0 →ₗ[ℝ] 𝒮.E₀' 0) := by rw [← hK']; exact y'.2
    obtain ⟨x, hx, hxy⟩ := hy
    have : S.symm y' = x := by rw [← hxy]; exact S.symm_apply_apply x
    rw [this]; exact hx
  have hKmap : 𝒟.K'.map (S.symm : 𝒮.E₀' 0 →ₗ[ℝ] P × W 0) = K := by
    ext x
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨y', hy', rfl⟩; exact hSK' ⟨y', hy'⟩
    · intro hx; exact ⟨S x, hSK ⟨x, hx⟩, S.symm_apply_apply x⟩
  -- finite dimensionality of the kernels (Lemma 3.44)
  have hC' : IsPartialQuadrant (ScBanach.const (P × 𝒮.Cs)) (Ct ×ˢ (univ : Set 𝒮.Cs)) :=
    hC.const_prod_univ 𝒮.Cs
  have hfinK' : FiniteDimensional ℝ 𝒟.K' := by
    obtain ⟨𝒱⟩ := 𝒟.exists_deriv hC'.isQuadrantLike
    have hker : 𝒟.K' = _ := 𝒱.ker_Dg_eq hC'.isQuadrantLike
    rw [hker]
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective _ (graphMap_injective 𝒱.L) _)
  have hfinK : FiniteDimensional ℝ K := by
    rw [← hKmap]
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective _ S.symm.injective _)
  have hpos' : IsInGoodPosition 𝒮.E₀' ((Ct ×ˢ univ) ×ˢ univ) 𝒟.K' := by
    rw [hK']; exact hpos.map S hS_mem
  have hsurj' : Surjective 𝒟.Dg := by
    intro z
    obtain ⟨x, hx⟩ := hsurj (𝒮.fiberInv₀ 0 z)
    refine ⟨𝒮.split₀ 0 x, ?_⟩
    rw [hDg_apply, 𝒮.glue₀_split₀, hx, 𝒮.fiber₀_fiberInv₀]
  obtain ⟨Y', V', τ, hY', hV'rel, hV'0, hτY, hτ1, hτC, hτ0, hDτ, hsol, hlev, U'', hU''o, hU''0,
    hU''⟩ := theorem_3_43_sc_smooth hC' 𝒟 hsurj' hpos' (𝒮.lemma_3_42 hC hf)
  let SK : K →L[ℝ] 𝒟.K' :=
    { toFun := fun y => ⟨S y, hSK y⟩
      map_add' := fun _ _ => Subtype.ext (by simp)
      map_smul' := fun _ _ => Subtype.ext (by simp)
      cont := (S.continuous.comp continuous_subtype_val).subtype_mk _ }
  have hSK_apply : ∀ y : K, ((SK y : 𝒟.K') : 𝒮.E₀' 0) = S y := fun _ => rfl
  let GK : 𝒟.K' → K := fun y' => ⟨S.symm y', hSK' y'⟩
  have hSK_GK : ∀ y', SK (GK y') = y' := fun y' => Subtype.ext (S.apply_symm_apply _)
  -- the complement, the neighbourhood and the map
  refine ⟨Y'.map (S.symm : 𝒮.E₀' 0 →ₗ[ℝ] P × W 0), SK ⁻¹' V', fun y => S.symm (τ (SK y)),
    ?_, ?_, ?_, fun y => ⟨τ (SK y), hτY _, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `Y` is a good complement of `K` (Lemma 3.45 for the linear `ψ⁻¹`)
    have h := hY'.map (E' := ScBanach.paramProd P W) (C' := Ct ×ˢ univ) S.symm hS'_mem
    rwa [hKmap] at h
  · obtain ⟨O', hO', hV'⟩ := hV'rel
    refine ⟨SK ⁻¹' O', hO'.preimage SK.continuous, ?_⟩
    ext y
    simp only [mem_preimage, hV', mem_inter_iff, hSK_apply]
    rw [hS_mem]
  · show SK 0 ∈ V'
    rw [map_zero]; exact hV'0
  · -- the values lie on level `1`
    intro y
    obtain ⟨w₁, hw₁⟩ := hτ1 (SK y)
    have hc : ((τ (SK y)).1.2 : W 0) ∈ W.smooth := 𝒮.Cs_le_smooth (τ (SK y)).1.2.2
    obtain ⟨c₁, hc₁⟩ := (ScScale.mem_smooth_iff _).1 hc 1
    refine ⟨c₁ + w₁.val, ?_⟩
    show W.toBase 1 (c₁ + w₁.val) = (S.symm (τ (SK y))).2
    rw [map_add, hc₁, hS', glue₀_apply]
    change _ = 𝒮.liftC 0 (τ (SK y)).1.2 + (τ (SK y)).2.val
    rw [ScBanach.finLift_zero_apply, ← hw₁]
    congr 1
  · exact S.symm.contDiff.comp_contDiffOn (hτC.comp SK.contDiff.contDiffOn fun _ hy => hy)
  · show S.symm (τ (SK 0)) = 0
    rw [map_zero, hτ0, map_zero]
  · -- `Dσ(0) = 0`
    have hτd : HasFDerivWithinAt τ (0 : 𝒟.K' →L[ℝ] 𝒮.E₀' 0) V' 0 := by
      have := (hτC.differentiableOn one_ne_zero 0 hV'0).hasFDerivWithinAt
      rwa [hDτ] at this
    have hSK0 : SK 0 = 0 := map_zero _
    have hτd' : HasFDerivWithinAt τ (0 : 𝒟.K' →L[ℝ] 𝒮.E₀' 0) V' (SK 0) := by rw [hSK0]; exact hτd
    have h1 := hτd'.comp (0 : K) SK.hasFDerivWithinAt fun _ hy => hy
    have h2 := (S.symm : 𝒮.E₀' 0 →L[ℝ] P × W 0).hasFDerivAt.comp_hasFDerivWithinAt (0 : K) h1
    have huniq : UniqueDiffWithinAt ℝ (SK ⁻¹' V') (0 : K) := by
      obtain ⟨O', hO', hV'⟩ := hV'rel
      have hV : SK ⁻¹' V' = (SK ⁻¹' O') ∩ Subtype.val ⁻¹' (Ct ×ˢ univ) := by
        ext y
        simp only [mem_preimage, hV', mem_inter_iff, hSK_apply]
        rw [hS_mem]
      have h0 : (0 : K) ∈ SK ⁻¹' V' := by show SK 0 ∈ V'; rw [hSK0]; exact hV'0
      rw [hV] at h0 ⊢
      have hconv : Convex ℝ (Subtype.val ⁻¹' (Ct ×ˢ univ) : Set K) := by
        have hC'' : Convex ℝ (Ct ×ˢ (univ : Set (W 0))) := by
          have := hCq.convex 0
          rw [ScBanach.const_lvlSet] at this
          exact this.prod convex_univ
        exact hC''.linear_preimage K.subtype
      rw [inter_comm]
      exact (uniqueDiffWithinAt_convex hconv hpos.interior_nonempty (subset_closure h0.2)).inter
        ((hO'.preimage SK.continuous).mem_nhds h0.1)
    have h3 : HasFDerivWithinAt (fun y : K => S.symm (τ (SK y)))
        ((S.symm : 𝒮.E₀' 0 →L[ℝ] P × W 0).comp ((0 : 𝒟.K' →L[ℝ] 𝒮.E₀' 0).comp SK))
        (SK ⁻¹' V') 0 := h2
    rw [h3.fderivWithin huniq, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
  · -- `y + σ(y)` is a zero
    intro y hy
    obtain ⟨hmem, hzero⟩ := hsol (SK y) hy
    have heq : (y : P × W 0) + S.symm (τ (SK y)) = 𝒮.glue₀ 0 ((SK y : 𝒮.E₀' 0) + τ (SK y)) := by
      rw [← hS', map_add, hSK_apply, S.symm_apply_apply]
    rw [heq]
    refine ⟨hmem, ?_⟩
    have : 𝒮.fiber₀ 0 (𝒮.fsum f (𝒮.glue₀ 0 ((SK y : 𝒮.E₀' 0) + τ (SK y)))) = 0 := hzero
    exact (𝒮.fiber₀_eq_zero_iff 0 _).1 this
  · -- the regularity on all levels, transported by the linear `ψ⁻¹`
    intro k hk
    obtain ⟨Vk, ⟨Ok, hOk, hVk⟩, hVk0, hVkV, τk, hτkC, hτk⟩ := hlev k hk
    refine ⟨SK ⁻¹' Vk, ⟨SK ⁻¹' Ok, hOk.preimage SK.continuous, ?_⟩, ?_, fun y hy => hVkV hy,
      fun y => 𝒮.glue₀ k (τk (SK y)),
      (𝒮.glue₀ k).contDiff.comp_contDiffOn (hτkC.comp SK.contDiff.contDiffOn fun _ hy => hy),
      fun y hy => ?_⟩
    · ext y
      simp only [mem_preimage, hVk, mem_inter_iff, hSK_apply]
      rw [hS_mem]
    · show SK 0 ∈ Vk
      rw [map_zero]; exact hVk0
    · show (ScBanach.paramProd P W).toBase k (𝒮.glue₀ k (τk (SK y))) = S.symm (τ (SK y))
      rw [𝒮.glue₀.toBase_comm, hτk _ hy, hS']
  · -- every zero near `0` is of this form
    refine ⟨S ⁻¹' U'', hU''o.preimage S.continuous, by rw [mem_preimage, map_zero]; exact hU''0, ?_⟩
    rintro x ⟨hxU, hxG⟩ hx0
    have hSxG : S x ∈ 𝒮.pushGerm₀.U 0 := by
      rw [mem_pushGerm₀_U, ← hS', S.symm_apply_apply]; exact hxG
    have hSx0 : 𝒮.pushMap₀ f (S x) = 0 := by
      change 𝒮.fiber₀ 0 (𝒮.fsum f (𝒮.glue₀ 0 (S x))) = 0
      rw [← hS', S.symm_apply_apply, hx0, map_zero]
    obtain ⟨y', hy', hxy'⟩ := hU'' (S x) ⟨hxU, hSxG⟩ hSx0
    refine ⟨GK y', by show SK (GK y') ∈ V'; rw [hSK_GK]; exact hy', ?_⟩
    change x = (GK y' : P × W 0) + S.symm (τ (SK (GK y')))
    rw [hSK_GK]
    change x = S.symm y' + S.symm (τ y')
    rw [← map_add, ← hxy', S.symm_apply_apply]

/-- **Theorem 3.47 (Corollary 3.47 of the text)** without the regularity clause (1), the form
used by the global implicit function theorem (§3.6); see `theorem_3_47_sc_smooth` for the full
statement. -/
theorem _root_.Polyfold.theorem_3_47 (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    (𝒮 : StabilityData Ct W) (hf : IsBasicGerm Ct 𝒮.G f B) (hsurj : Surjective (𝒮.Dfs f))
    (hpos : IsInGoodPosition (ScBanach.paramProd P W) (Ct ×ˢ univ)
      (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0))) :
    ∃ (Y : Submodule ℝ (P × W 0))
      (V : Set (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)))
      (σ : LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0) → P × W 0),
      IsGoodComplement (ScBanach.paramProd P W) (Ct ×ˢ univ)
        (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)) Y ∧
      (∃ O, IsOpen O ∧ V = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧ 0 ∈ V ∧
      (∀ y, σ y ∈ Y) ∧ (∀ y, (σ y).2 ∈ range (W.toBase 1)) ∧
      ContDiffOn ℝ 1 σ V ∧ σ 0 = 0 ∧ fderivWithin ℝ σ V 0 = 0 ∧
      (∀ y ∈ V, (y : P × W 0) + σ y ∈ 𝒮.G.U 0 ∧ 𝒮.fsum f ((y : P × W 0) + σ y) = 0) ∧
      ∃ U'' : Set (P × W 0), IsOpen U'' ∧ (0 : P × W 0) ∈ U'' ∧
        ∀ x ∈ U'' ∩ 𝒮.G.U 0, 𝒮.fsum f x = 0 → ∃ y ∈ V, x = (y : P × W 0) + σ y := by
  obtain ⟨Y, V, σ, h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h10⟩ :=
    theorem_3_47_sc_smooth hC 𝒮 hf hsurj hpos
  exact ⟨Y, V, σ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

end StabilityData

end Polyfold
