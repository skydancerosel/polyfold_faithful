import Polyfold.Chapter16.P3W4PB_Multisections
import Polyfold.Chapter14.P3W6A6_Theorem1419

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
**Theorem 16.5.7** (p. 735; 2017: Theorem 16.6), with Theorem 14.1.9 proved.

# Theorem 16.5.7

## What is formalized

* `BoundaryMultisection.IsStructurableNe s`: Definition 16.5.6 with the index sets of the
  structurable representative non-empty (`ChargesBoundary`; the text's `|I_x|⁻¹` in Definition
  14.1.3 (3)).  PB's `IsStructurable` allows empty index sets, and then B1's
  `theorem_14_1_9_statement`, which PB's `theorem_16_5_7_hyp` takes in every model, does not hold
  as we read it for models with boundary (`not_theorem_14_1_9_statement_a6`).
* **`theorem_16_5_7_a6`**: PB's Theorem 16.5.7 with `theorem_14_1_9_charged_a6` in place of the
  hypothesis `h1419`; the models carry tame strong bundle charts (`hB`, the standing assumption).
  The proof is PB's.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

open EPLocalization SBLocalization

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- **Definition 16.5.6 with non-empty index sets**: `λ` over `∂Z` has a representative whose
`Λ` is structurable over `∂X` and charges every boundary fibre. -/
def BoundaryMultisection.IsStructurableNe (s : BoundaryMultisection c) : Prop :=
  ∃ a : BoundaryMultisectionRep c, ⟦a⟧ = s ∧ IsBoundaryStructurable a.S.A a.Λ ∧
    ChargesBoundary a.Λ

theorem BoundaryMultisection.IsStructurableNe.isStructurable {s : BoundaryMultisection c}
    (h : s.IsStructurableNe) : s.IsStructurable :=
  let ⟨a, ha, hs, _⟩ := h
  ⟨a, ha, hs⟩

/-- **2021 Theorem 16.5.7, p. 735 (2017: Theorem 16.6)**, with Theorem 14.1.9 proved
(`theorem_14_1_9_charged_a6`): over a tame polyfold whose models admit sc-smooth partitions of
unity and tame strong bundle charts, with an auxiliary norm `n`, a structurable sc⁺-multisection
`λ` over `∂Z` (non-empty index sets), an open `Ũ ⊇ dom-supp(λ)` and a continuous `f ≥ 0` with
`tsupport f ⊆ Ũ` and `n(λ) < f` on `dom-supp(λ)`, there is a structurable sc⁺-multisection `λ'`
with (1) `n(λ') ≤ f`, (2) `dom-supp(λ') ⊆ Ũ`, (3) `λ' = λ` over `∂Z`. -/
theorem theorem_16_5_7_a6 (hc : c.IsTame) (hPU : ∀ S : StrongPolyfoldBundleStructure p, ⟦S⟧ = c →
      S.A.X.PObj.AdmitsScPartitionsOfUnity)
    (hB : ∀ S : StrongPolyfoldBundleStructure p, ⟦S⟧ = c → ∀ x : S.A.Obj,
      ∃ e : StrongBundleChart S.A.X.PObj S.A.P, S.A.B.IsTameChart e ∧ x ∈ e.φ.source)
    {n : Y → ℝ} (hn : c.IsAuxNorm n) (s : BoundaryMultisection c) (hs : s.IsStructurableNe)
    {U : Set Z} (hU : IsOpen U) (hdom : s.domSupp ⊆ U) {f : Z → ℝ} (hf : Continuous f)
    (hf0 : ∀ z, 0 ≤ f z) (hfU : tsupport f ⊆ U)
    (hlt : ∀ z ∈ s.domSupp, c.normLam n s.toFun z < f z) :
    ∃ t : ScPlusMultisection c, t.IsStructurable ∧ (∀ z, c.normLam n t.toFun z ≤ f z) ∧
      t.domSupp ⊆ U ∧ ∀ y, p y ∈ c.polyfold.boundary → t.toFun y = s.toFun y := by
  obtain ⟨a, rfl, hstr, hch⟩ := hs
  set S := a.S
  set g : S.A.Obj → Z := fun x => S.γ (S.A.X.π x) with hg
  have hgc : Continuous g := S.continuous_γπ
  have hbsub := boundaryDomSupp_subset a
  have hlt' : ∀ x ∈ boundaryDomSupp a.Λ, pointwiseNorm (S.normOf n) a.Λ x < (f ∘ g) x := by
    intro x hx
    have hxb : x ∈ S.A.X.PObj.boundary := closure_minimal (fun y hy => hy.1)
      S.A.X.PObj.isClosed_boundary hx
    have e := normLam_eq a.hS n a.Λ (BoundaryMultisection.toFun (c := c) ⟦a⟧) x fun w hw => by
      have hb : p (S.Γ (S.A.E.toEpGroupoid.π w)) ∈ c.polyfold.boundary := by
        rw [S.p_Γ_π, hw]; exact (mem_boundary_iff_obj a.hS _).2 hxb
      rw [BoundaryMultisection.toFun_mk_of_mem a hb, a.comm w (hw ▸ hxb)]
    rw [← e]
    exact hlt _ (hbsub hx)
  obtain ⟨Λ', hstr', h1, h2, h3⟩ := theorem_14_1_9_charged_a6 ((c.isTame_iff.1 hc) S a.hS)
    S.paracompact (hPU S a.hS) (hB S a.hS) a.Λ hstr hch (S.normOf n) (hn S a.hS) (g ⁻¹' U)
    (hU.preimage hgc) (S.isSaturated_preimage_γπ U) (hbsub.trans (preimage_mono hdom)) (f ∘ g)
    (hf.comp hgc) (fun x => hf0 _)
    (fun φ => congrArg (fun q => f (S.γ q)) (S.A.X.π_src_eq_π_tgt φ).symm)
    ((tsupport_comp_subset_preimage' hgc f).trans (preimage_mono hfU)) hlt'
  set a' := ofFunctor S a.hS Λ' hstr'.1
  refine ⟨⟦a'⟧, ⟨a', rfl, hstr'⟩, fun z => ?_, ?_, fun y hy => ?_⟩
  · obtain ⟨x, rfl⟩ := S.surjective_γπ z
    change c.normLam n a'.lam (S.γ (S.A.X.π x)) ≤ f (S.γ (S.A.X.π x))
    rw [normLam_eq a.hS n Λ' _ x fun w _ => a'.comm w]
    exact h1 x
  · rw [← remark_16_5_3 a']
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact h2 hx
  · obtain ⟨ξ, rfl⟩ := S.Γ.surjective y
    obtain ⟨w, rfl⟩ := S.A.E.toEpGroupoid.surjective_π ξ
    have hw : S.A.P w ∈ S.A.X.PObj.boundary := by
      rw [S.p_Γ_π] at hy; exact (mem_boundary_iff_obj a.hS _).1 hy
    rw [BoundaryMultisection.toFun_mk_of_mem a hy, ScPlusMultisection.toFun_mk,
      show a'.lam (S.Γ (S.A.E.toEpGroupoid.π w)) = Λ' w from a'.comm w, a.comm w hw]
    exact h3 w hw

end StrongPolyfoldBundle

end Polyfold
