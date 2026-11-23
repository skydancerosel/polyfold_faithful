import Polyfold.Chapter15.RestrictedSeedsPre
import Polyfold.Chapter15.RestrictedSeedsCone
import Polyfold.Chapter15.RestrictedSeedsAtomic

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.9** (Transversal Extension Theorem), steps (c)–(d), pp. 698–699, with the
functions of Remark 9.5.19 (p. 451) in place of sc-smooth bump functions.

# The data at one centre, chosen before the functions

## The text, paraphrased

At a point `x` of `supp(Λ₀ ∘ f)` the proof takes a neighbourhood `U(x)` with the natural action
of `G_x`, an invariant open `V(x)` with `cl V(x) ⊆ U(x)`, and sc⁺-sections supported in `V(x)`
which, together with the images of the operators of `T(f, Λ₀)(x)`, span the fibre at the points
of `supp(Λ₀ ∘ f)` near `x`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `exists_seeds_of_function_bounded`: the seeds `s_j = c · ψ(β) · S_j` of one sc-smooth function
  `β`, when `N(S_j) < M` on `{β ≠ 0}`: `s_j` vanishes where `β` does, `N(s_j) ≤ ε`, and (15.1)
  relative to `Λ₀` passes from the `S_j(y)` to the `s_j(y)` where `β(y) ≠ 0`.
* **`exists_seedCentre`**: at `x ∈ supp(Λ₀ ∘ f)` and inside an open `W₁ ∋ x`: a natural
  representation on `U(x) ⊆ W₁` with the properness property, an invariant open `V(x)`, global
  sc⁺-sections `S_j`, a bound `M`, an open `G₀ ⊆ V(x)` on which `N(S_j) < M` and (15.1) holds
  with the `S_j`, and an invariant open `N' ∋ x` with `cl N' ⊆ G₀` such that every compact
  subset of `cl N'` lies, together with `x`, in a compact connected subset of `U(x)`.

## Reading

All of this is fixed before any function `β` is chosen; the function is asked to have its
support in `G₀` and to be positive on a compact part of `cl N'`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Set Function Topology Filter
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid

variable {A : SEP.{u}}

/-- **Seeds from one function with `N(S_j) < M` on `{β ≠ 0}`** (steps (c)–(d) of the proof of
Theorem 15.3.9, 2021 pp. 698–699).  For global sc⁺-sections `S_j`, an auxiliary norm `N`,
`M, ε > 0` and an sc-smooth `β : X → ℝ` with `N(S_j(y)) < M` wherever `β(y) ≠ 0`, the sections
`s_j = (ε / M) · ψ(β) · S_j` are sc⁺, vanish where `β` does, satisfy `N(s_j) ≤ ε`, and (15.1)
relative to `Λ₀` passes from the `S_j(y)` to the `s_j(y)` at the points with `β(y) ≠ 0`. -/
theorem exists_seeds_of_function_bounded (f : A.Obj → A.W) (Λ₀ : A.W → ℚ≥0) {N : A.B.One → ℝ}
    (hN : A.B.IsAuxNorm N) {ℓ : ℕ} {S : Fin ℓ → A.Obj → A.W}
    (hS : ∀ j, A.B.IsScPlusSection (S j)) {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε)
    {β : A.Obj → ℝ} (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hβM : ∀ y, β y ≠ 0 → ∀ j, normW N (S j y) < M) :
    ∃ (s : Fin ℓ → A.Obj → A.W) (hs : ∀ j, A.B.IsScPlusSection (s j)),
      (∀ j y, s j y ≠ fiberZero A.P y → β y ≠ 0) ∧ (∀ j y, normW N (s j y) ≤ ε) ∧
      ∀ y : A.X.PObj.Level 1, β (A.X.PObj.levelVal 1 y) ≠ 0 →
        IsParamOntoVecRel f Λ₀ y
          (fun j => ⟨S j (A.X.PObj.levelVal 1 y), (hS j).1 _⟩) →
        IsParamOntoVecRel f Λ₀ y
          (fun j => ⟨s j (A.X.PObj.levelVal 1 y), (hs j).1 _⟩) := by
  classical
  set g : A.Obj → ℝ := fun y => ε / M * cutProfile (β y) with hg
  have hgsm : A.X.PObj.IsScSmoothMap realPolyfold g := by
    have h1 : A.X.PObj.IsScSmoothMap realPolyfold (cutProfile ∘ β) :=
      hβ.comp_contDiff contDiff_cutProfile
    have h2 : A.X.PObj.IsScSmoothMap realPolyfold
        ((fun t : ℝ => ε / M * t) ∘ (cutProfile ∘ β)) :=
      h1.comp_contDiff (contDiff_const.mul contDiff_id)
    exact h2
  have hg0 : ∀ y, β y = 0 → g y = 0 := fun y hy => by
    rw [hg]; dsimp only; rw [hy, cutProfile_zero, mul_zero]
  have hgne : ∀ y, β y ≠ 0 → g y ≠ 0 := fun y hy =>
    mul_ne_zero (div_pos hε hM).ne' (cutProfile_ne_zero hy)
  have hgle : ∀ y, |g y| ≤ ε / M := fun y => by
    rw [hg]; dsimp only
    rw [abs_mul, abs_of_pos (div_pos hε hM)]
    exact mul_le_of_le_one_right (div_pos hε hM).le (abs_cutProfile_le_one _)
  have hsec : ∀ j, IsSection A.P (S j) := fun j => (hS j).1
  refine ⟨fun j => Polyfold.sectionSmul A.P g (S j), fun j => (hS j).smul_left hgsm,
    fun j y hy h0 => ?_, fun j y => ?_, fun y hy H => ?_⟩
  · apply hy
    change Polyfold.sectionSmul A.P g (S j) y = fiberZero A.P y
    rw [sectionSmul_apply (hsec j), hg0 y h0, zero_smul]
    rfl
  · rw [normW_sectionSmul hN (hsec j) g ((hS j).mem_oneSet y)]
    by_cases hy : β y = 0
    · rw [hg0 y hy, abs_zero, zero_mul]; exact hε.le
    · have hlt : normW N (S j y) < M := hβM y hy j
      calc |g y| * normW N (S j y) ≤ ε / M * M :=
            mul_le_mul (hgle y) hlt.le (normW_nonneg hN _) (div_pos hε hM).le
        _ = ε := div_mul_cancel₀ ε hM.ne'
  · refine H.smul (a := fun _ => g (A.X.PObj.levelVal 1 y)) (fun _ => hgne _ hy) fun j => ?_
    exact Subtype.ext (sectionSmul_apply (hsec j) _)

/-- **The data at one centre** (steps (c)–(d) of the proof of Theorem 15.3.9, 2021
pp. 698–699; Theorem 7.1.13, p. 244): at `x ∈ supp(Λ₀ ∘ f)`, inside an open `W₁ ∋ x`, a natural
representation on `U(x) ⊆ W₁` with the properness property, an invariant open `V(x) ∋ x` with
`cl V(x) ⊆ U(x)`, global sc⁺-sections `S_j`, `M > 0`, an open `G₀ ⊆ V(x)` with `N(S_j) < M` on
`G₀` and (15.1) relative to `Λ₀` with the `S_j` at the points of `supp(Λ₀ ∘ f) ∩ G₀`, and an
invariant open `N' ∋ x` with `cl N' ⊆ G₀` such that every compact `K ⊆ cl N'` lies, together
with `x`, in a compact connected subset of `U(x)`.  No bump functions are used. -/
theorem exists_seedCentre (hX : A.X.IsTame) (hsec : A.B.HasScPlusSectionsThrough)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {Λ₀ : A.W → ℚ≥0} (hΛ₀ : IsScPlusMultisection A Λ₀)
    {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N) {x : A.Obj} (hx : 0 < Λ₀ (f x))
    {W₁ : Set A.Obj} (hW₁ : IsOpen W₁) (hxW₁ : x ∈ W₁) :
    ∃ (R : A.X.NaturalRep x) (Vat G₀ N' : Set A.Obj) (ℓ : ℕ) (S : Fin ℓ → A.Obj → A.W)
      (hS : ∀ j, A.B.IsScPlusSection (S j)) (M : ℝ),
      A.X.HasPropernessProperty R.U ∧ R.U ⊆ W₁ ∧ IsOpen Vat ∧ x ∈ Vat ∧
      (∀ g, MapsTo (R.Φ g) Vat Vat) ∧ closure Vat ⊆ R.U ∧ 0 < M ∧
      IsOpen G₀ ∧ G₀ ⊆ Vat ∧ (∀ y ∈ G₀, ∀ j, normW N (S j y) < M) ∧
      (∀ y : A.X.PObj.Level 1, A.X.PObj.levelVal 1 y ∈ G₀ →
        0 < Λ₀ (f (A.X.PObj.levelVal 1 y)) →
          IsParamOntoVecRel f Λ₀ y (fun j => ⟨S j (A.X.PObj.levelVal 1 y), (hS j).1 _⟩)) ∧
      IsOpen N' ∧ x ∈ N' ∧ closure N' ⊆ G₀ ∧ (∀ g, MapsTo (R.Φ g) N' N') ∧
      ∀ K : Set A.Obj, IsCompact K → K ⊆ closure N' →
        ∃ Z : Set A.Obj, IsCompact Z ∧ IsPreconnected Z ∧ K ⊆ Z ∧ x ∈ Z ∧ Z ⊆ R.U := by
  classical
  obtain ⟨R, Vat, hprop, hRU, hVo, hxV, hVinv, hVcl⟩ := exists_atomicNbhd x hW₁ hxW₁
  obtain ⟨ℓ, S, hS, Wp, hWpo, hxWp, hWp⟩ := exists_preSeedRel hX hsec hf hft hΛ₀ hx
  set M : ℝ := 1 + ∑ j, normW N (S j x) with hMdef
  have hM0 : ∀ j, 0 ≤ normW N (S j x) := fun j => normW_nonneg hN _
  have hM : 0 < M := by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hM0 j
    rw [hMdef]; linarith
  have hxM : ∀ j, normW N (S j x) < M := fun j => by
    have := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => hM0 i) (Finset.mem_univ j)
    rw [hMdef]; linarith
  obtain ⟨Nc, hNco, hxNc, hNcu, hNc⟩ :=
    A.X.PObj.exists_nhds_compact_connected (R.isOpen_U.mem_nhds R.mem_U)
  set G₀ : Set A.Obj := (Nc ∩ Vat ∩ Wp) ∩ ⋂ j, {y | normW N (S j y) < M} with hG₀def
  have hG₀o : IsOpen G₀ := ((hNco.inter hVo).inter hWpo).inter
    (isOpen_iInter_of_finite fun j => isOpen_normW_lt hN (hS j) M)
  have hxG₀ : x ∈ G₀ := ⟨⟨⟨hxNc, hxV⟩, hxWp⟩, mem_iInter.2 hxM⟩
  obtain ⟨t, ht, htc, htG⟩ := exists_mem_nhds_isClosed_subset (hG₀o.mem_nhds hxG₀)
  set N₀ : Set A.Obj := interior t with hN₀def
  have hN₀o : IsOpen N₀ := isOpen_interior
  have hxN₀ : x ∈ N₀ := mem_interior_iff_mem_nhds.2 ht
  have hN₀cl : closure N₀ ⊆ G₀ := (closure_minimal interior_subset htc).trans htG
  set N' : Set A.Obj := ⋂ g, R.U ∩ R.Φ g ⁻¹' N₀ with hN'def
  have hN'o : IsOpen N' := isOpen_iInter_of_finite fun g =>
    (R.continuousOn_Φ g).isOpen_inter_preimage R.isOpen_U hN₀o
  have hxN' : x ∈ N' :=
    mem_iInter.2 fun g => ⟨R.mem_U, by rw [mem_preimage, R.Φ_self]; exact hxN₀⟩
  have hN'U : N' ⊆ R.U := fun y hy => (mem_iInter.1 hy 1).1
  have hN'N₀ : N' ⊆ N₀ := fun y hy => by
    have h := (mem_iInter.1 hy 1).2
    rwa [mem_preimage, R.Φ_one y (hN'U hy)] at h
  have hN'inv : ∀ g, MapsTo (R.Φ g) N' N' := fun g y hy => mem_iInter.2 fun k =>
    ⟨R.mapsTo_Φ g (hN'U hy), by
      rw [mem_preimage, ← R.Φ_mul k g y (hN'U hy)]
      exact (mem_iInter.1 hy (k * g)).2⟩
  have hN'cl : closure N' ⊆ G₀ := (closure_mono hN'N₀).trans hN₀cl
  refine ⟨R, Vat, G₀, N', ℓ, S, hS, M, hprop, hRU, hVo, hxV, hVinv, hVcl, hM, hG₀o,
    fun y hy => hy.1.1.2, fun y hy j => mem_iInter.1 hy.2 j,
    fun y hy hpos => hWp y hy.1.2 hpos, hN'o, hxN', hN'cl, hN'inv, fun K hK hKN => ?_⟩
  obtain ⟨Z, hZc, hZp, hKZ, hxZ, hZU⟩ := hNc K hK fun y hy => (hN'cl (hKN hy)).1.1.1
  exact ⟨Z, hZc, hZp, hKZ, hxZ, hZU⟩

end SBLocalization

end Polyfold
