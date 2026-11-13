import Polyfold.Chapter8.EpStrongBundle
import Polyfold.Chapter5.AuxNorm
import Polyfold.Chapter7.NaturalRep

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 12,
§12.2, **Theorem 12.2.6** (Good Neighbourhood Theorem), pp. 571–572.

# The good neighbourhood theorem

## The text, paraphrased

(Theorem 12.2.6) For a strong bundle `(P : W → X, μ)` over an ep-groupoid, every object `x` has
open neighbourhoods `U'(x)`, `U''(x)` with (1) `cl(U'(x)) ⊆ U''(x)`; (2) `U''(x)` carries the
natural `G_x`-action `(Φ, Γ)`, which leaves `U'(x)` invariant; (3) `W|U''(x)` is isomorphic to a
local strong bundle model `K → O`; (4) a sequence of morphisms `φ_k` with `s(φ_k) ∈ cl(U''(x))`
and `t(φ_k) → z` has a subsequence converging to some `φ` with `s(φ) ∈ cl(U''(x))`, `t(φ) = z`;
(5) for the saturation `U(x) = π⁻¹(π(U'(x)))`, `(U(x) ∖ U'(x)) ∩ cl(U''(x)) = ∅`.  The proof
takes a natural representation on `V(x)` with `t : s⁻¹(cl V(x)) → X` proper and a bundle chart,
shrinks twice inside it, and gets (5) from the uniqueness in Theorem 7.1.13 (3).

## What is formalized

`EpGroupoid.theorem_12_2_6`, as printed.  Readings:
* (2): `U''(x)` is the domain `R.U` of a natural representation `R` (Theorem 7.1.13), and
  `Φ(g)(U'(x)) = U'(x)` for every `g ∈ G_x`.
* (3): `U''(x)` lies in the base domain of one strong bundle chart of `P` (compatible with the
  atlas), whose restriction to `P⁻¹(U''(x))` is the isomorphism with the local model.
* (4): with sequences and a strictly increasing reindexing, as printed.

## Proof

As the text's: `V = V₀ ∩ dom(c)` with `V₀` from Definition 7.1.3 (3) and `c` a bundle chart, a
natural representation `R` on `U ⊆ V`, then two shrinkings `exists_naturalRep_shrink` with
closures controlled by regularity.  (4) uses properness on `s⁻¹(cl V₀)` and metrizability of the
morphism space; (5) is the text's argument, run from `z ∈ U'(x)` to `y ∈ cl U''(x)` (the unique
`g` with `φ = Γ(g, z)` maps `z` to `y`, so `y ∈ U'(x)` by invariance).
-/

open Set Filter Topology Function TopologicalSpace

noncomputable section

namespace Polyfold

universe u v

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
  {W : Type v} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

namespace EpGroupoid

/-- The image of an invariant set under `Φ(g)` is the set itself. -/
theorem NaturalRep.image_Φ_eq {x : Obj} (R : X.NaturalRep x) (g : X.Isotropy x) :
    R.Φ g '' R.U = R.U := by
  refine Subset.antisymm (image_subset_iff.2 (R.mapsTo_Φ g)) fun y hy => ?_
  refine ⟨R.Φ g⁻¹ y, R.mapsTo_Φ g⁻¹ hy, ?_⟩
  rw [← R.Φ_mul g g⁻¹ y hy, mul_inv_cancel, R.Φ_one y hy]

/-- **Property (4) from properness**: if `t : s⁻¹(cl V₀) → X` is proper and `A ⊆ cl V₀` is
closed, a sequence of morphisms with sources in `A` and convergent targets has a convergent
subsequence, with limit `φ`, `s(φ) ∈ A`, `t(φ) = z`. -/
theorem exists_subseq_of_isProperMap {V₀ A : Set Obj}
    (hprop : IsProperMap ((X.src ⁻¹' closure V₀).domRestrict X.tgt)) (hA : IsClosed A)
    (hAV : A ⊆ closure V₀) (φ : ℕ → Mor) (z : Obj) (hφs : ∀ k, X.src (φ k) ∈ A)
    (hφt : Tendsto (fun k => X.tgt (φ k)) atTop (𝓝 z)) :
    ∃ (ψ : Mor) (σ : ℕ → ℕ), StrictMono σ ∧ Tendsto (φ ∘ σ) atTop (𝓝 ψ) ∧ X.src ψ ∈ A ∧
      X.tgt ψ = z := by
  have := X.PMor.metrizableSpace
  set K : Set Obj := insert z (range fun k => X.tgt (φ k))
  have hK : IsCompact K := hφt.isCompact_insert_range
  set f := (X.src ⁻¹' closure V₀).domRestrict X.tgt
  have hC : IsCompact (f ⁻¹' K) := hprop.isCompact_preimage hK
  set a : ℕ → X.src ⁻¹' closure V₀ := fun k => ⟨φ k, hAV (hφs k)⟩
  have ha : ∀ k, a k ∈ f ⁻¹' K := fun k => Or.inr ⟨k, rfl⟩
  obtain ⟨b, -, σ, hσ, hab⟩ := hC.tendsto_subseq ha
  have hψ : Tendsto (φ ∘ σ) atTop (𝓝 (b : Mor)) := (continuous_subtype_val.tendsto b).comp hab
  refine ⟨b, σ, hσ, hψ, hA.mem_of_tendsto ((X.continuous_src.tendsto _).comp hψ)
    (Eventually.of_forall fun k => hφs (σ k)), ?_⟩
  exact tendsto_nhds_unique ((X.continuous_tgt.tendsto _).comp hψ)
    (hφt.comp hσ.tendsto_atTop)

/-- **Theorem 12.2.6 (Good Neighbourhood Theorem)**, pp. 571–572: every object `x` has open
neighbourhoods `U'(x) ⊆ U''(x)` with (1) `cl U' ⊆ U''`, (2) `U''` the domain of a natural
representation whose `Φ(g)` leave `U'` invariant, (3) `U''` inside the domain of a strong bundle
chart, (4) the sequential compactness of morphisms with sources in `cl U''`, (5)
`(π⁻¹(π(U')) ∖ U') ∩ cl U'' = ∅`.  As printed. -/
theorem theorem_12_2_6 (B : StrongBundle X.PObj P) (x : Obj) :
    ∃ (U' U'' : Set Obj) (R : X.NaturalRep x), IsOpen U' ∧ x ∈ U' ∧ R.U = U'' ∧
      -- (1)
      closure U' ⊆ U'' ∧
      -- (2)
      (∀ g, R.Φ g '' U' = U') ∧
      -- (3)
      (∃ c : StrongBundleChart X.PObj P, B.IsChart c ∧ U'' ⊆ c.φ.source) ∧
      -- (4)
      (∀ (φ : ℕ → Mor) (z : Obj), (∀ k, X.src (φ k) ∈ closure U'') →
        Tendsto (fun k => X.tgt (φ k)) atTop (𝓝 z) →
        ∃ (ψ : Mor) (σ : ℕ → ℕ), StrictMono σ ∧ Tendsto (φ ∘ σ) atTop (𝓝 ψ) ∧
          X.src ψ ∈ closure U'' ∧ X.tgt ψ = z) ∧
      -- (5)
      (X.π ⁻¹' (X.π '' U') \ U') ∩ closure U'' = ∅ := by
  have := X.PObj.metrizableSpace
  obtain ⟨V₀, hV₀o, hxV₀, hprop⟩ := X.exists_isProperMap x
  obtain ⟨c, hcm, hxc⟩ := StrongBundle.exists_chart_mem B x
  obtain ⟨R, hRV⟩ := X.theorem_7_1_13 x (hV₀o.inter c.φ.isOpen_source) ⟨hxV₀, hxc⟩
  -- first shrinking: `cl U'' ⊆ U`
  obtain ⟨t₁, ht₁, ht₁c, ht₁R⟩ := exists_mem_nhds_isClosed_subset (R.isOpen_U.mem_nhds R.mem_U)
  obtain ⟨R₁, hR₁, hΦ₁, hΓ₁⟩ :=
    X.exists_naturalRep_shrink R isOpen_interior (mem_interior_iff_mem_nhds.2 ht₁)
  have hcl₁ : closure R₁.U ⊆ R.U :=
    (closure_minimal (hR₁.trans (inter_subset_left.trans interior_subset)) ht₁c).trans ht₁R
  have hR₁R : R₁.U ⊆ R.U := hR₁.trans inter_subset_right
  -- second shrinking: `cl U' ⊆ U''`
  obtain ⟨t₂, ht₂, ht₂c, ht₂R⟩ :=
    exists_mem_nhds_isClosed_subset (R₁.isOpen_U.mem_nhds R₁.mem_U)
  obtain ⟨R₂, hR₂, hΦ₂, -⟩ :=
    X.exists_naturalRep_shrink R₁ isOpen_interior (mem_interior_iff_mem_nhds.2 ht₂)
  have hcl₂ : closure R₂.U ⊆ R₁.U :=
    (closure_minimal (hR₂.trans (inter_subset_left.trans interior_subset)) ht₂c).trans ht₂R
  refine ⟨R₂.U, R₁.U, R₁, R₂.isOpen_U, R₂.mem_U, rfl, hcl₂, fun g => ?_,
    ⟨c, B.isChart_of_mem hcm, hR₁R.trans (hRV.trans inter_subset_right)⟩,
    fun φ z hφs hφt => ?_, ?_⟩
  · rw [← hΦ₂]; exact NaturalRep.image_Φ_eq X R₂ g
  · exact X.exists_subseq_of_isProperMap hprop isClosed_closure
      (closure_mono (hR₁R.trans (hRV.trans inter_subset_left))) φ z hφs hφt
  · refine eq_empty_iff_forall_notMem.2 fun y ⟨⟨⟨z, hz, hzy⟩, hyU'⟩, hycl⟩ => hyU' ?_
    obtain ⟨φ, hφs, hφt⟩ := X.π_eq_π_iff.1 hzy
    have hzR : z ∈ R.U := hR₁R (hR₂.trans inter_subset_right hz)
    have hyR : y ∈ R.U := hcl₁ hycl
    obtain ⟨g, hg, -⟩ := R.existsUnique_Γ φ (hφs ▸ hzR) (hφt ▸ hyR)
    have hy : y = R₂.Φ g z := by
      rw [hΦ₂, hΦ₁, ← R.tgt_Γ g z hzR, ← hφs, hg, hφt]
    rw [hy]; exact R₂.mapsTo_Φ g hz

end EpGroupoid

end Polyfold
