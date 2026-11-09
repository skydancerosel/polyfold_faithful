import Polyfold.Chapter3.GlobalIFTNearbyGraph

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6 and §6.1:
the linear algebra behind the **perturbation argument of Proposition 6.2.2 (preprint 6.2)** applied to the
surjectivity of `Tf̃(z₀)` at the nearby zeros of Theorem 3.6.8 (preprint 3.54) (Finding 105): the kernel of the
linearization of a parametrized problem must be in good position to the partial quadrant
`Λ × C'` at the corner `(0, 0)` for Theorem 3.5.11 (preprint 3.47) to apply, and this fails for the naive
extension.

# Good position of the kernel of the parametrized problem

## The text, paraphrased

(Proof of Proposition 6.2.2 (preprint 6.2)) "The linearization at `(0, t₀, φ(t₀))` with respect to the first and
second variable is surjective and the kernel of the linearization has a complement contained in
`T^R_{(0,t₀,φ(t₀))}(ℝ^{m+p} ⊕ [0,1] ⊕ X) = ℝ^{m+p} ⊕ T^R_{t₀}[0,1] ⊕ T^R_{φ(t₀)}X`.  Hence
`ker F'(0, t₀, φ(t₀))` is in good position to the boundary."

## What is formalized

* `Polyfold.mem_lineality_of_goodComplement_prod` and
  `Polyfold.sup_lineality_eq_top_of_goodComplement_prod`: **the obstruction**.  For a subspace `N` of
  `V` and a partial-quadrant-like cone `C ⊆ V` (closed under nonnegative scaling), a good
  complement `P` of `ℝ × N` with respect to `ℝ × C` (Definition 3.1.24 (preprint 3.21)) has its `V`-projection in
  the lineality space `C ∩ (−C)`; hence `ℝ × N` is in good position to `ℝ × C` only if
  `N + (C ∩ −C) = V`.  (Take `n = (1, 0)`: `n ∈ ℝ × C`, and `n + p = (1 + μ, y) ∈ ℝ × C` forces
  `y ∈ C` for every small `p = (μ, y) ∈ P`.)  So for the kernel `ℝ × K` of the λ-extended problem
  of Theorem 3.6.8 (preprint 3.54) the good position at the corner fails unless `K` projects onto all boundary
  coordinates — the text's "has a complement contained in `T^R`" is exactly the statement that
  the complement lies in the lineality space.
* `Polyfold.isInGoodPosition_extendedKernel`: **the fix**.  In `(Λ × Pn) ⊕ W` with the partial
  quadrant `(Λ × C̃) ⊕ W`, the subspace `Ñ = {((λ, a), w) | (a, w) + j(λ) ∈ K}` (the kernel of
  `(λ, v) ↦ D(h + t)(0)(v + j(λ))`) is in good position to `(Λ × C̃) ⊕ W` as soon as
  `K ∩ j(Λ) = 0`, `(K ⊕ j(Λ)) ⊕ Y' = Pn ⊕ W` with `Y'` in the lineality space of `C̃ ⊕ W`, and
  `K ⊕ j(Λ)` meets the interior of `C̃ ⊕ W`: the good complement is `Λ_c × Y'` (`Λ_c` a complement
  of `ker j`) and the `ε`-condition holds for every `ε`.  The directions `j(Λ) ⊆ T₀(ψ(O)) ∩ E'_∞`
  with `K + j(Λ) + E'_0 = E'` exist by tameness (`T₀O + E₀ = E`, Proposition 2.5.3 (preprint 2.35)) and are
  realized by the sc⁺-perturbations `ρ(r(u)) Dg(0)Dψ⁻¹(0) j(λ)` (Finding 105).

## What the text leaves implicit, and the choices made (the findings)

* The text's Proposition 6.2.2 (preprint 6.2) asserts the good position of the kernel of the extended problem from
  the existence of "a complement contained in `T^R`" without constructing it; for Theorem 3.6.8 (preprint 3.54) (1)
  at the nearby zeros the untilted extension (parameters multiplying smooth vectors `k̂` with a
  factor vanishing at `0`) has kernel `ℝ × K`, which is **not** in good position in general
  (`sup_lineality_eq_top_of_goodComplement_prod`); the tilt by `j(Λ)` is needed.
* Neither lemma uses the sc-structure: both are statements about Definition 3.1.24 (preprint 3.21) in the Banach
  space `E'₀`, with the cone described by its lineality space.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

/-! ### The obstruction: good complements of `ℝ × N` lie in the lineality space -/

section Obstruction

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The product cone `ℝ × C` in `ℝ × V`, as a set. -/
abbrev prodCone (C : Set V) : Set (ℝ × V) := (univ : Set ℝ) ×ˢ C

/-- The subspace `ℝ × N` of `ℝ × V`. -/
abbrev prodSub (N : Submodule ℝ V) : Submodule ℝ (ℝ × V) := (⊤ : Submodule ℝ ℝ).prod N

/-- **The obstruction to good position at the corner for the λ-extended problem.**  Let `C ⊆ V` be
closed under nonnegative scaling with `0 ∈ C`, `N ⊆ V` a subspace and `P ⊆ ℝ × V` a subspace
with the good-complement property of Definition 3.1.24 (preprint 3.21) for `ℝ × N` with respect to `ℝ × C` (for some
`ε > 0`).  Then every `p = (μ, y) ∈ P` has `y ∈ C` and `−y ∈ C`: the `V`-projection of `P` lies
in the lineality space of `C`.  (With `n = (1, 0) ∈ ℝ × N`: `n ∈ ℝ × C`, so `n + tp ∈ ℝ × C` for
`|t|` small, i.e. `ty ∈ C`.) -/
theorem mem_lineality_of_goodComplement_prod {C : Set V} (hC0 : (0 : V) ∈ C)
    (hCs : ∀ t : ℝ, 0 ≤ t → ∀ y ∈ C, t • y ∈ C) {N : Submodule ℝ V} {P : Submodule ℝ (ℝ × V)}
    {ε : ℝ} (hε : 0 < ε)
    (hgood : ∀ x ∈ prodSub N, ∀ p ∈ P, ‖p‖ ≤ ε * ‖x‖ → (x ∈ prodCone C ↔ x + p ∈ prodCone C))
    {p : ℝ × V} (hp : p ∈ P) : p.2 ∈ C ∧ -p.2 ∈ C := by
  have hn : ((1 : ℝ), (0 : V)) ∈ prodSub N := ⟨mem_univ _, N.zero_mem⟩
  have hnC : ((1 : ℝ), (0 : V)) ∈ prodCone C := ⟨mem_univ _, hC0⟩
  -- scale `p` so that `‖t • p‖ ≤ ε`
  have key : ∀ t : ℝ, t ≠ 0 → ‖t • p‖ ≤ ε → t • p.2 ∈ C := by
    intro t ht hle
    have hmem : t • p ∈ P := P.smul_mem t hp
    have hn1 : ‖((1 : ℝ), (0 : V))‖ = 1 := by
      rw [Prod.norm_mk, norm_one, norm_zero]; exact max_eq_left zero_le_one
    have h1 := (hgood _ hn _ hmem (by rw [hn1, mul_one]; exact hle)).1 hnC
    have h2 := h1.2
    simpa using h2
  by_cases hp0 : p = 0
  · subst hp0; simpa using hC0
  have hnorm : 0 < ‖p‖ := norm_pos_iff.2 hp0
  set t : ℝ := ε / ‖p‖ with ht
  have htpos : 0 < t := div_pos hε hnorm
  have hle : ‖t • p‖ ≤ ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, ht, div_mul_cancel₀ _ hnorm.ne']
  have hle' : ‖(-t) • p‖ ≤ ε := by rw [neg_smul, norm_neg]; exact hle
  have h1 := key t htpos.ne' hle
  have h2 := key (-t) (neg_ne_zero.2 htpos.ne') hle'
  rw [neg_smul] at h2
  constructor
  · have := hCs t⁻¹ (inv_nonneg.2 htpos.le) _ h1
    rwa [smul_smul, inv_mul_cancel₀ htpos.ne', one_smul] at this
  · have := hCs t⁻¹ (inv_nonneg.2 htpos.le) _ h2
    rwa [smul_neg, smul_smul, inv_mul_cancel₀ htpos.ne', one_smul] at this

/-- **`ℝ × N` is in good position to `ℝ × C` only if `N + (C ∩ −C) = V`**: the good complement
projects into the lineality space, and `ℝ × N` together with it spans `ℝ × V`. -/
theorem sup_lineality_eq_top_of_goodComplement_prod {C : Set V} (hC0 : (0 : V) ∈ C)
    (hCs : ∀ t : ℝ, 0 ≤ t → ∀ y ∈ C, t • y ∈ C) {N : Submodule ℝ V} {P : Submodule ℝ (ℝ × V)}
    (hcompl : IsCompl (prodSub N) P) {ε : ℝ} (hε : 0 < ε)
    (hgood : ∀ x ∈ prodSub N, ∀ p ∈ P, ‖p‖ ≤ ε * ‖x‖ → (x ∈ prodCone C ↔ x + p ∈ prodCone C)) :
    ∀ v : V, ∃ n ∈ N, ∃ y, y ∈ C ∧ -y ∈ C ∧ v = n + y := by
  intro v
  have hv : ((0 : ℝ), v) ∈ prodSub N ⊔ P := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨x, hx, p, hp, hxp⟩ := Submodule.mem_sup.1 hv
  obtain ⟨hy, hy'⟩ := mem_lineality_of_goodComplement_prod hC0 hCs hε hgood hp
  refine ⟨x.2, hx.2, p.2, hy, hy', ?_⟩
  have := congrArg Prod.snd hxp
  simpa using this.symm

end Obstruction

/-! ### The fix: the tilted kernel of the extended problem is in good position -/

section Extended

variable {Pn Λ : Type} [NormedAddCommGroup Pn] [NormedSpace ℝ Pn] [FiniteDimensional ℝ Pn]
  [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ] {W : ScBanach} {Ct : Set Pn}

variable (Λ Pn W) in
/-- The projection `((λ, a), w) ↦ (a, w)` of `(Λ × Pn) ⊕ W` onto `Pn ⊕ W`. -/
def extProj : (ScBanach.paramProd (Λ × Pn) W) 0 →ₗ[ℝ] Pn × W 0 :=
  ((LinearMap.snd ℝ Λ Pn).comp (LinearMap.fst ℝ (Λ × Pn) (W 0))).prod
    (LinearMap.snd ℝ (Λ × Pn) (W 0))

variable (Λ Pn W) in
/-- The projection `((λ, a), w) ↦ λ` of `(Λ × Pn) ⊕ W` onto the parameters. -/
def extParam : (ScBanach.paramProd (Λ × Pn) W) 0 →ₗ[ℝ] Λ :=
  (LinearMap.fst ℝ Λ Pn).comp (LinearMap.fst ℝ (Λ × Pn) (W 0))

@[simp] lemma extProj_apply (x : (ScBanach.paramProd (Λ × Pn) W) 0) :
    extProj Pn Λ W x = ((x.1.2, x.2) : Pn × W 0) := rfl

@[simp] lemma extParam_apply (x : (ScBanach.paramProd (Λ × Pn) W) 0) :
    extParam Pn Λ W x = x.1.1 := rfl

/-- The kernel `Ñ = {((λ, a), w) | (a, w) + j(λ) ∈ K}` of the linearization
`((λ, a), w) ↦ D(h + t)(0)((a, w) + j(λ))` of the λ-extended problem on `(Λ × Pn) ⊕ W`. -/
def extendedKernel (K : Submodule ℝ (Pn × W 0)) (j : Λ →ₗ[ℝ] Pn × W 0) :
    Submodule ℝ ((ScBanach.paramProd (Λ × Pn) W) 0) :=
  Submodule.comap (extProj Pn Λ W + j.comp (extParam Pn Λ W)) K

lemma mem_extendedKernel {K : Submodule ℝ (Pn × W 0)} {j : Λ →ₗ[ℝ] Pn × W 0}
    {x : (ScBanach.paramProd (Λ × Pn) W) 0} :
    x ∈ extendedKernel K j ↔ ((x.1.2, x.2) : Pn × W 0) + j x.1.1 ∈ K := by
  rw [extendedKernel, Submodule.mem_comap, LinearMap.add_apply, LinearMap.comp_apply,
    extProj_apply, extParam_apply]

/-- The complement `Λ_c × Y'` of the extended kernel: `((μ, a), w)` with `μ ∈ Λ_c` and
`(a, w) ∈ Y'`. -/
def extendedCompl (Λc : Submodule ℝ Λ) (Y' : Submodule ℝ (Pn × W 0)) :
    Submodule ℝ ((ScBanach.paramProd (Λ × Pn) W) 0) :=
  Submodule.comap (extParam Pn Λ W) Λc ⊓ Submodule.comap (extProj Pn Λ W) Y'

lemma mem_extendedCompl {Λc : Submodule ℝ Λ} {Y' : Submodule ℝ (Pn × W 0)}
    {x : (ScBanach.paramProd (Λ × Pn) W) 0} :
    x ∈ extendedCompl Λc Y' ↔ x.1.1 ∈ Λc ∧ ((x.1.2, x.2) : Pn × W 0) ∈ Y' := by
  rw [extendedCompl, Submodule.mem_inf, Submodule.mem_comap, Submodule.mem_comap, extProj_apply,
    extParam_apply]

/-- **The tilted kernel of the extended problem is in good position at the corner.**  Let `K`,
`Y'` be subspaces of `Pn ⊕ W`, `j : Λ → Pn ⊕ W` linear with `K ∩ j(Λ) = 0` and
`(K ⊔ j(Λ)) ⊕ Y' = Pn ⊕ W`, where `Y'` lies in the lineality space of `C' = C̃ ⊕ W`
(`y ∈ Y'` ⟹ `v + y ∈ C' ↔ v ∈ C'`), and let `K ⊔ j(Λ)` contain an interior point of `C'`.  Then
`Ñ = {((λ, a), w) | (a, w) + j(λ) ∈ K}` is in good position to `(Λ × C̃) ⊕ W` in
`(Λ × Pn) ⊕ W`, with the good complement `Λ_c × Y'` for any complement `Λ_c` of `ker j`; the
`ε`-condition of Definition 3.1.24 (preprint 3.21) holds for every `ε`. -/
theorem isInGoodPosition_extendedKernel {K Y' : Submodule ℝ (Pn × W 0)} (j : Λ →ₗ[ℝ] Pn × W 0)
    (hKj : K ⊓ LinearMap.range j = ⊥) (hcompl : IsCompl (K ⊔ LinearMap.range j) Y')
    (hY' : ∀ y ∈ Y', ∀ v : Pn × W 0, v + y ∈ Ct ×ˢ univ ↔ v ∈ Ct ×ˢ univ)
    (hint : ∃ v₀ ∈ K ⊔ LinearMap.range j, v₀ ∈ interior (Ct ×ˢ (univ : Set (W 0)))) :
    IsInGoodPosition (ScBanach.paramProd (Λ × Pn) W) ((univ ×ˢ Ct) ×ˢ univ) (extendedKernel K j) := by
  classical
  -- a complement `Λc` of `ker j`
  obtain ⟨Λc, hΛc⟩ := Submodule.exists_isCompl (LinearMap.ker j)
  have hjΛc : ∀ m ∈ LinearMap.range j, ∃ μ ∈ Λc, j μ = m := by
    rintro _ ⟨l₀, rfl⟩
    have hl : l₀ ∈ LinearMap.ker j ⊔ Λc := by rw [hΛc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨κ, hκ, μ, hμ, rfl⟩ := Submodule.mem_sup.1 hl
    exact ⟨μ, hμ, by rw [map_add, LinearMap.mem_ker.1 hκ, zero_add]⟩
  have hmemC : ∀ x : (ScBanach.paramProd (Λ × Pn) W) 0,
      x ∈ (univ ×ˢ Ct) ×ˢ (univ : Set (W 0)) ↔ ((x.1.2, x.2) : Pn × W 0) ∈ Ct ×ˢ univ := by
    intro x
    constructor
    · rintro ⟨⟨-, h⟩, -⟩; exact ⟨h, mem_univ _⟩
    · rintro ⟨h, -⟩; exact ⟨⟨mem_univ _, h⟩, mem_univ _⟩
  refine ⟨?_, extendedCompl Λc Y', ⟨IsCompl.of_eq ?_ ?_, 1, zero_lt_one, ?_⟩⟩
  · -- the interior of `Ñ ∩ C̃` in `Ñ`
    obtain ⟨v₀, hv₀, hv₀int⟩ := hint
    obtain ⟨k₀, hk₀, m₀, hm₀, rfl⟩ := Submodule.mem_sup.1 hv₀
    obtain ⟨μ₀, -, hμ₀⟩ := hjΛc m₀ hm₀
    set n₀ : (ScBanach.paramProd (Λ × Pn) W) 0 := ((-μ₀, (k₀ + m₀).1), (k₀ + m₀).2) with hn₀
    have hn₀N : n₀ ∈ extendedKernel K j := by
      rw [mem_extendedKernel]
      change ((k₀ + m₀).1, (k₀ + m₀).2) + j (-μ₀) ∈ K
      rw [Prod.mk.eta, map_neg, hμ₀, add_neg_cancel_right]; exact hk₀
    let pr : (ScBanach.paramProd (Λ × Pn) W) 0 → Pn × W 0 :=
      fun x => ((Prod.snd (α := Λ) (β := Pn) x.1, x.2) : Pn × W 0)
    have hpr : Continuous pr :=
      (continuous_snd.comp (continuous_fst (X := Λ × Pn) (Y := W 0))).prodMk continuous_snd
    refine ⟨⟨n₀, hn₀N⟩, ?_⟩
    rw [mem_interior]
    refine ⟨Subtype.val ⁻¹' (pr ⁻¹' interior (Ct ×ˢ univ)), fun x hx => ?_,
      (isOpen_interior.preimage hpr).preimage continuous_subtype_val, ?_⟩
    · rw [mem_preimage, hmemC]
      exact interior_subset hx
    · show pr n₀ ∈ interior (Ct ×ˢ univ)
      rw [hn₀]
      exact hv₀int
  · -- `Ñ ⊓ (Λc × Y') = ⊥`
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxN, hxP⟩ := Submodule.mem_inf.1 hx
    rw [mem_extendedKernel] at hxN
    rw [mem_extendedCompl] at hxP
    -- `(a, w) ∈ Y'` and `(a, w) + j λ ∈ K`: then `(a, w) ∈ (K ⊔ j Λ) ⊓ Y' = 0`
    have h1 : ((x.1.2, x.2) : Pn × W 0) ∈ K ⊔ LinearMap.range j := by
      have : ((x.1.2, x.2) : Pn × W 0) = (((x.1.2, x.2) : Pn × W 0) + j x.1.1) + (-(j x.1.1)) := by
        abel
      rw [this]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hxN)
        (Submodule.mem_sup_right (Submodule.neg_mem _ ⟨x.1.1, rfl⟩))
    have h2 : ((x.1.2, x.2) : Pn × W 0) = 0 :=
      (Submodule.disjoint_def.1 hcompl.disjoint) _ h1 hxP.2
    have h3 : j x.1.1 ∈ K ⊓ LinearMap.range j := by
      refine ⟨?_, ⟨x.1.1, rfl⟩⟩
      have := hxN
      rwa [h2, zero_add] at this
    rw [hKj] at h3
    have h4 : x.1.1 ∈ LinearMap.ker j ⊓ Λc := ⟨(Submodule.mem_bot ℝ).1 h3, hxP.1⟩
    rw [hΛc.inf_eq_bot] at h4
    have h5 : x.1.1 = 0 := (Submodule.mem_bot ℝ).1 h4
    have ha : x.1.2 = 0 := congrArg Prod.fst h2
    have hw : x.2 = 0 := congrArg Prod.snd h2
    rw [Submodule.mem_bot]
    exact Prod.ext (Prod.ext h5 ha) hw
  · -- `Ñ ⊔ (Λc × Y') = ⊤`
    rw [eq_top_iff]
    rintro x -
    have hv : ((x.1.2, x.2) : Pn × W 0) + j x.1.1 ∈ (K ⊔ LinearMap.range j) ⊔ Y' := by
      rw [hcompl.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨km, hkm, y, hy, hxy⟩ := Submodule.mem_sup.1 hv
    obtain ⟨k, hk, m, hm, rfl⟩ := Submodule.mem_sup.1 hkm
    obtain ⟨μ, hμ, hjμ⟩ := hjΛc m hm
    refine Submodule.mem_sup.2 ⟨((x.1.1 - μ, x.1.2 - y.1), x.2 - y.2), ?_, ((μ, y.1), y.2),
      (mem_extendedCompl).2 ⟨hμ, by simpa using hy⟩, ?_⟩
    · rw [mem_extendedKernel]
      change ((x.1.2 - y.1, x.2 - y.2) : Pn × W 0) + j (x.1.1 - μ) ∈ K
      have e1 : ((x.1.2 - y.1, x.2 - y.2) : Pn × W 0) = ((x.1.2, x.2) : Pn × W 0) - y := rfl
      have : ((x.1.2 - y.1, x.2 - y.2) : Pn × W 0) + j (x.1.1 - μ) =
          (((x.1.2, x.2) : Pn × W 0) + j x.1.1) - y - j μ := by
        rw [e1, map_sub]; abel
      rw [this, ← hxy, hjμ]
      have : k + m + y - y - m = k := by abel
      rw [this]; exact hk
    · ext <;> simp
  · -- the `ε`-condition holds for every `ε`
    intro x _ p hp _
    rw [mem_extendedCompl] at hp
    rw [hmemC, hmemC]
    change ((x.1.2, x.2) : Pn × W 0) ∈ Ct ×ˢ univ ↔
      (((x.1.2, x.2) : Pn × W 0) + ((p.1.2, p.2) : Pn × W 0)) ∈ Ct ×ˢ univ
    exact (hY' _ hp.2 _).symm

end Extended

end Polyfold
