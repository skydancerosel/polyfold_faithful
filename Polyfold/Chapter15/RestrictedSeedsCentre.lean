import Polyfold.Chapter15.AdmissibleRelativeStep
import Polyfold.Chapter15.RestrictedSeedsPre
import Polyfold.Chapter15.RestrictedSeedsCone

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.9** (Transversal Extension Theorem), steps (c)–(d), pp. 698–699.

# The data at one interior point of `supp(Λ₀ ∘ f)`

## The text, paraphrased

At a point `x` of `supp(Λ₀ ∘ f)` off `∂X` the proof takes a neighbourhood `U(x)` with the natural
action of `G_x`, an invariant `V(x)` with closure in `U(x)`, and finitely many sc⁺-sections whose
values, with the images of the linearizations, span the fibres at the solution points near `x`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `exists_invariant_nhds_closure_subset`: an open neighbourhood of `x`, invariant under the
  natural action on `R.U`, with closure in a given neighbourhood of `x`.
* **`exists_centreData`**: for `x ∈ supp(Λ₀ ∘ f) ∖ ∂X` with `N(Λ₀)(x) < h(x)`: a natural
  representation `R` with the properness property, `R.U ⊆ U ∖ ∂X`, a margin `c > 0` with
  `c ≤ h − N(Λ₀)` on `R.U`, an invariant open `V ∋ x` with `cl V ⊆ R.U`, global sc⁺-sections
  `S_j` and an open `W` on which (15.1) relative to `Λ₀` holds with the `S_j`, a bound `M`, and
  an invariant open `N' ∋ x` with `cl N' ⊆ V ∩ W ∩ {N(S_j) < M}` such that every compact subset
  of `cl N'` lies, together with `x`, in a compact connected subset of `R.U`.

## Reading

No sc-smooth bump functions are used; the sections `S_j` are global and are cut off later.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}} {f : A.Obj → A.W} {Λ₀ : A.W → ℚ≥0} {N : A.B.One → ℝ} {U : Set A.Obj}

/-- An open neighbourhood of `x`, invariant under the natural action of `G_x` on `R.U`, contained
in `R.U`, with closure in a given neighbourhood `O` of `x` (the construction of `V(x)` in the
proof of Theorem 7.5.7). -/
theorem exists_invariant_nhds_closure_subset {x : A.Obj} (R : A.X.NaturalRep x) {O : Set A.Obj}
    (hO : O ∈ 𝓝 x) :
    ∃ V : Set A.Obj, IsOpen V ∧ x ∈ V ∧ (∀ g, MapsTo (R.Φ g) V V) ∧ V ⊆ R.U ∧ closure V ⊆ O := by
  obtain ⟨t, ht, htc, htO⟩ := exists_mem_nhds_isClosed_subset hO
  let V : Set A.Obj := ⋂ g, R.U ∩ R.Φ g ⁻¹' interior t
  have hVo : IsOpen V := isOpen_iInter_of_finite fun g =>
    (R.continuousOn_Φ g).isOpen_inter_preimage R.isOpen_U isOpen_interior
  have hxV : x ∈ V := mem_iInter.2 fun g =>
    ⟨R.mem_U, by rw [mem_preimage, R.Φ_self]; exact mem_interior_iff_mem_nhds.2 ht⟩
  have hVU : V ⊆ R.U := fun y hy => (mem_iInter.1 hy 1).1
  have hVt : V ⊆ t := fun y hy => by
    have h1 := (mem_iInter.1 hy 1).2
    rw [mem_preimage, R.Φ_one y (hVU hy)] at h1
    exact interior_subset h1
  have hVinv : ∀ g, MapsTo (R.Φ g) V V := fun g y hy => mem_iInter.2 fun h =>
    ⟨R.mapsTo_Φ g (hVU hy), by
      rw [mem_preimage, ← R.Φ_mul h g y (hVU hy)]
      exact (mem_iInter.1 hy (h * g)).2⟩
  exact ⟨V, hVo, hxV, hVinv, hVU, (closure_minimal hVt htc).trans htO⟩

/-- **The data at one interior point of `supp(Λ₀ ∘ f)`** (steps (c)–(d) of the proof of
Theorem 15.3.9, 2021 pp. 698–699): the natural representation, the invariant neighbourhood, the
margin, global sc⁺-sections with (15.1) relative to `Λ₀` near `x`, a bound for their norms, and
an invariant neighbourhood `N'` of `x` whose closure lies in all these sets and whose compact
subsets of the closure lie, together with `x`, in compact connected subsets of `R.U`. -/
theorem exists_centreData (hX : A.X.IsTame) (hsec : A.B.HasScPlusSectionsThrough)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hcc : ControlsCompactness A f N U) (hΛ₀ : IsScPlusMultisection A Λ₀)
    {h : A.Obj → ℝ} (hhc : Continuous h)
    {x : A.Obj} (hxU : x ∈ U) (hxb : x ∉ A.X.PObj.boundary) (hx : 0 < Λ₀ (f x))
    (hlt : pointwiseNorm N Λ₀ x < h x) :
    ∃ (R : A.X.NaturalRep x) (Vat : Set A.Obj) (c : ℝ) (ℓ : ℕ) (S : Fin ℓ → A.Obj → A.W)
      (hS : ∀ j, A.B.IsScPlusSection (S j)) (M : ℝ) (Wpre N' : Set A.Obj),
      A.X.HasPropernessProperty R.U ∧ IsOpen Vat ∧ x ∈ Vat ∧ (∀ g, MapsTo (R.Φ g) Vat Vat) ∧
      closure Vat ⊆ R.U ∧ 0 < c ∧ (∀ y ∈ R.U, c ≤ h y - pointwiseNorm N Λ₀ y) ∧
      R.U ⊆ U ∩ A.X.PObj.boundaryᶜ ∧ 0 < M ∧ IsOpen Wpre ∧
      (∀ y : A.X.PObj.Level 1, A.X.PObj.levelVal 1 y ∈ Wpre →
        0 < Λ₀ (f (A.X.PObj.levelVal 1 y)) →
        IsParamOntoVecRel f Λ₀ y (fun j => ⟨S j (A.X.PObj.levelVal 1 y), (hS j).1 _⟩)) ∧
      IsOpen N' ∧ x ∈ N' ∧ (∀ g, MapsTo (R.Φ g) N' N') ∧
      closure N' ⊆ Vat ∩ Wpre ∩ {y | ∀ j, normW N (S j y) < M} ∧
      ∀ K : Set A.Obj, IsCompact K → K ⊆ closure N' →
        ∃ Z : Set A.Obj, IsCompact Z ∧ IsPreconnected Z ∧ K ⊆ Z ∧ x ∈ Z ∧ Z ⊆ R.U := by
  have hNB : A.B.IsAuxNorm N := hcc.1.isAuxNorm
  set c : ℝ := (h x - pointwiseNorm N Λ₀ x) / 4 with hcdef
  set r : ℝ := (h x + pointwiseNorm N Λ₀ x) / 2 with hrdef
  have hc : 0 < c := by rw [hcdef]; linarith
  set W₁ : Set A.Obj := (U ∩ A.X.PObj.boundaryᶜ) ∩
    ({y | pointwiseNorm N Λ₀ y < r} ∩ {y | r + c < h y}) with hW₁def
  have hW₁ : IsOpen W₁ := (hcc.2.1.inter A.X.PObj.isClosed_boundary.isOpen_compl).inter
    ((isOpen_pointwiseNorm_lt hNB hΛ₀ continuous_const).inter (isOpen_lt continuous_const hhc))
  have hxW₁ : x ∈ W₁ := by
    refine ⟨⟨hxU, hxb⟩, ?_, ?_⟩
    · change pointwiseNorm N Λ₀ x < r
      rw [hrdef]; linarith
    · change r + c < h x
      rw [hrdef, hcdef]; linarith
  obtain ⟨R, Vat, hprop, hRU, hVo, hxV, hVinv, hVcl⟩ := exists_atomicNbhd x hW₁ hxW₁
  obtain ⟨ℓ, S, hS, Wpre, hWo, hxW, hW⟩ := exists_preSeedRel hX hsec hf hft hΛ₀ hx
  have hM0 : ∀ j, 0 ≤ normW N (S j x) := fun j => normW_nonneg hNB _
  set M : ℝ := 1 + ∑ j, normW N (S j x) with hMdef
  have hsum : 0 ≤ ∑ j, normW N (S j x) := Finset.sum_nonneg fun j _ => hM0 j
  have hM : 0 < M := by rw [hMdef]; linarith
  have hxM : ∀ j, normW N (S j x) < M := fun j => by
    have := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => hM0 i) (Finset.mem_univ j)
    rw [hMdef]; linarith
  set B : Set A.Obj := {y | ∀ j, normW N (S j y) < M} with hBdef
  have hBo : IsOpen B := by
    have e : B = ⋂ j, {y | normW N (S j y) < M} := by ext y; simp [hBdef]
    rw [e]; exact isOpen_iInter_of_finite fun j => isOpen_normW_lt hNB (hS j) M
  obtain ⟨Nc, hNco, hxNc, hNcU, hNc⟩ :=
    A.X.PObj.exists_nhds_compact_connected (R.isOpen_U.mem_nhds R.mem_U)
  have hO : (Vat ∩ Wpre ∩ B) ∩ Nc ∈ 𝓝 x :=
    (((hVo.inter hWo).inter hBo).inter hNco).mem_nhds ⟨⟨⟨hxV, hxW⟩, hxM⟩, hxNc⟩
  obtain ⟨N', hN'o, hxN', hN'inv, -, hN'cl⟩ := exists_invariant_nhds_closure_subset R hO
  refine ⟨R, Vat, c, ℓ, S, hS, M, Wpre, N', hprop, hVo, hxV, hVinv, hVcl, hc, fun y hy => ?_,
    hRU.trans inter_subset_left, hM, hWo, hW, hN'o, hxN', hN'inv,
    hN'cl.trans inter_subset_left, fun K hK hKN => hNc K hK (hKN.trans (hN'cl.trans
      inter_subset_right))⟩
  have h1 : pointwiseNorm N Λ₀ y < r := (hRU hy).2.1
  have h2 : r + c < h y := (hRU hy).2.2
  linarith

end SBLocalization

end Polyfold
