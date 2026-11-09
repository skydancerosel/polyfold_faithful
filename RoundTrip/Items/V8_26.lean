import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_26

/-! Round trip for V8_26 (Definition 8.3.4 = 2017 Definition 8.7: section functors, `Γ(P, μ)`,
`Γ⁺(P, μ)`, `Fred(P, μ)`).

The item lists seven definitions (`IsFunctorialSection`, `IsScSmoothSectionFunctor`,
`IsScPlusSectionFunctor`, `IsScFredholmSectionFunctor`, `sectionFunctors`, `plusSectionFunctors`,
`fredholmSectionFunctors`; vocabulary) and eleven theorems; `A` is the conjunction of their
types, universes at `0`: `Γ` contains `fiberZero` and is closed under `sectionAdd` and constant
`sectionSmul`; `Γ⁺ ⊆ Γ`, `Γ⁺` contains `fiberZero` and is closed under the same operations;
`Fred ⊆ Γ`; and Part I's three lemmas on sc-smooth sections of a strong bundle over an arbitrary
M-polyfold (sums, constant multiples, the zero section are sc-smooth).

`B` says that the three project notions and sets are B's literal ones, that `Γ` and `Γ⁺` contain
the zero section and are closed under the fibrewise operations (`zeroB`, `addB`, `smulB`), and
`Γ⁺ ⊆ Γ`.

* `A_to_B`: the three notions agree by unfolding (the functorial condition `f(y) = μ(φ, f(x))`
  for `s φ = x`, `t φ = y` is the project's `f(t φ) = μ(φ, f(s φ))` after `subst`; the sc⁺
  condition is Part I's `isScPlusSection_iff`); B's operations are the project's
  (`fiberZero` by `rfl`, `sectionAdd_apply`, `sectionSmul_apply`), and the closure properties
  are `A`'s theorems.
* `B_to_A`: the eight theorems about `Γ`, `Γ⁺`, `Fred` follow from `B` (same identifications).
  Part I's three lemmas about sections over an arbitrary M-polyfold `Z` also follow from `B`,
  applied to the strong bundle over the trivial ep-groupoid of `Z`
  (`EpStrongBundle.trivial`, `NonVacuityBundle.lean`, where every section is functorial,
  `mem_sectionFunctors_trivial`). -/

namespace RoundTrip.V8_26
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpStrongBundle.fiberZero_mem_sectionFunctors.{0, 0}) ∧
  (type_of% @Polyfold.EpStrongBundle.sectionAdd_mem_sectionFunctors.{0, 0}) ∧
  (type_of% @Polyfold.EpStrongBundle.sectionSmul_mem_sectionFunctors.{0, 0}) ∧
  (type_of% @Polyfold.EpStrongBundle.plusSectionFunctors_subset.{0, 0}) ∧
  (type_of% @Polyfold.EpStrongBundle.fiberZero_mem_plusSectionFunctors.{0, 0}) ∧
  (type_of% @Polyfold.EpStrongBundle.sectionAdd_mem_plusSectionFunctors.{0, 0}) ∧
  (type_of% @Polyfold.EpStrongBundle.sectionSmul_mem_plusSectionFunctors.{0, 0}) ∧
  (type_of% @Polyfold.EpStrongBundle.fredholmSectionFunctors_subset.{0, 0}) ∧
  (type_of% @Polyfold.StrongBundle.IsScSmoothSection.sectionAdd_of_isScSmoothSection.{0, 0}) ∧
  (type_of% @Polyfold.StrongBundle.IsScSmoothSection.sectionSmul_const.{0, 0}) ∧
  (type_of% @Polyfold.StrongBundle.isScSmoothSection_fiberZero.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.fiberZero_mem_sectionFunctors.{0, 0},
    @Polyfold.EpStrongBundle.sectionAdd_mem_sectionFunctors.{0, 0},
    @Polyfold.EpStrongBundle.sectionSmul_mem_sectionFunctors.{0, 0},
    @Polyfold.EpStrongBundle.plusSectionFunctors_subset.{0, 0},
    @Polyfold.EpStrongBundle.fiberZero_mem_plusSectionFunctors.{0, 0},
    @Polyfold.EpStrongBundle.sectionAdd_mem_plusSectionFunctors.{0, 0},
    @Polyfold.EpStrongBundle.sectionSmul_mem_plusSectionFunctors.{0, 0},
    @Polyfold.EpStrongBundle.fredholmSectionFunctors_subset.{0, 0},
    @Polyfold.StrongBundle.IsScSmoothSection.sectionAdd_of_isScSmoothSection.{0, 0},
    @Polyfold.StrongBundle.IsScSmoothSection.sectionSmul_const.{0, 0},
    @Polyfold.StrongBundle.isScSmoothSection_fiberZero.{0, 0}⟩

/-! ### Glue: B's notions and operations are the project's -/

section Glue

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

theorem smooth_iff (E : EpStrongBundle X B) (f : Obj → W) :
    E.IsScSmoothSectionFunctor f ↔ IsScSmoothSectionFunctorB E f := by
  constructor
  · rintro ⟨hf, hf'⟩
    refine ⟨hf.1, hf.2, fun φ x y hx hy h => ?_⟩
    subst hx hy
    exact hf' φ
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, fun φ => h3 φ _ _ rfl rfl _⟩

theorem sectionFunctors_eq (E : EpStrongBundle X B) : E.sectionFunctors = GammaB E :=
  Set.ext fun f => smooth_iff E f

theorem plus_iff (E : EpStrongBundle X B) (f : Obj → W) :
    E.IsScPlusSectionFunctor f ↔ IsScPlusSectionFunctorB E f := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨-, g, hg, hgs⟩ := (B.isScPlusSection_iff f).1 h2
    refine ⟨(smooth_iff E f).1 h1, fun x => ?_, g, fun x => congrFun hg x, hgs⟩
    rw [← congrFun hg x]
    exact (g x).2
  · rintro ⟨h1, -, g, hg, hgs⟩
    exact ⟨(smooth_iff E f).2 h1, (B.isScPlusSection_iff f).2 ⟨h1.1, g, funext hg, hgs⟩⟩

theorem plusSectionFunctors_eq (E : EpStrongBundle X B) :
    E.plusSectionFunctors = GammaPlusB E :=
  Set.ext fun f => plus_iff E f

theorem fred_iff (E : EpStrongBundle X B) (f : Obj → W) :
    E.IsScFredholmSectionFunctor f ↔ IsScFredholmSectionFunctorB E f :=
  ⟨fun h => ⟨(smooth_iff E f).1 h.1, h.2⟩, fun h => ⟨(smooth_iff E f).2 h.1, h.2⟩⟩

end Glue

section Ops

variable {Z W : Type} {P : W → Z} [∀ x, AddCommGroup (P ⁻¹' {x})]

theorem zeroB_eq : zeroB P = fiberZero P := rfl

theorem addB_eq (f g : Z → W) (hf : IsSectionB P f) (hg : IsSectionB P g) :
    addB P f g hf hg = sectionAdd P f g :=
  funext fun x => (sectionAdd_apply (P := P) hf hg x).symm

theorem smulB_eq [∀ x, Module ℝ (P ⁻¹' {x})] (c : ℝ) (f : Z → W) (hf : IsSectionB P f) :
    smulB P c f hf = sectionSmul P (fun _ => c) f :=
  funext fun x => (sectionSmul_apply (P := P) (f := fun _ => c) hf x).symm

end Ops

theorem A_to_B : A → B := by
  rintro ⟨h0, hadd, hsmul, -, h0p, haddp, hsmulp, -, -, -, -⟩
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E
  refine ⟨smooth_iff E, sectionFunctors_eq E, ⟨?_, ?_, ?_⟩, plus_iff E, plusSectionFunctors_eq E,
    fun f hf => hf.1, ⟨?_, ?_, ?_⟩, fred_iff E, Set.ext fun f => fred_iff E f⟩
  · rw [← sectionFunctors_eq, zeroB_eq]; exact h0 E
  · intro f g hf hg hf' hg'
    rw [← sectionFunctors_eq] at hf' hg' ⊢
    rw [addB_eq]; exact hadd E hf' hg'
  · intro c f hf hf'
    rw [← sectionFunctors_eq] at hf' ⊢
    rw [smulB_eq]; exact hsmul E c hf'
  · rw [← plusSectionFunctors_eq, zeroB_eq]; exact h0p E
  · intro f g hf hg hf' hg'
    rw [← plusSectionFunctors_eq] at hf' hg' ⊢
    rw [addB_eq]; exact haddp E hf' hg'
  · intro c f hf hf'
    rw [← plusSectionFunctors_eq] at hf' ⊢
    rw [smulB_eq]; exact hsmulp E c hf'

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E
    have h := (hB Obj Mor X W P B E).2.2.1.1
    rw [(hB Obj Mor X W P B E).2.1, ← zeroB_eq]; exact h
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E f g hf hg
    have hf1 : IsSectionB P f := hf.1.1
    have hg1 : IsSectionB P g := hg.1.1
    rw [(hB Obj Mor X W P B E).2.1] at hf hg ⊢
    rw [← addB_eq f g hf1 hg1]
    exact (hB Obj Mor X W P B E).2.2.1.2.1 f g hf1 hg1 hf hg
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E f a hf
    have hf1 : IsSectionB P f := hf.1.1
    rw [(hB Obj Mor X W P B E).2.1] at hf ⊢
    rw [← smulB_eq a f hf1]
    exact (hB Obj Mor X W P B E).2.2.1.2.2 a f hf1 hf
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E
    rw [(hB Obj Mor X W P B E).2.1, (hB Obj Mor X W P B E).2.2.2.2.1]
    exact (hB Obj Mor X W P B E).2.2.2.2.2.1
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E
    have h := (hB Obj Mor X W P B E).2.2.2.2.2.2.1.1
    rw [(hB Obj Mor X W P B E).2.2.2.2.1, ← zeroB_eq]; exact h
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E f g hf hg
    have hf1 : IsSectionB P f := hf.1.1.1
    have hg1 : IsSectionB P g := hg.1.1.1
    rw [(hB Obj Mor X W P B E).2.2.2.2.1] at hf hg ⊢
    rw [← addB_eq f g hf1 hg1]
    exact (hB Obj Mor X W P B E).2.2.2.2.2.2.1.2.1 f g hf1 hg1 hf hg
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E f a hf
    have hf1 : IsSectionB P f := hf.1.1.1
    rw [(hB Obj Mor X W P B E).2.2.2.2.1] at hf ⊢
    rw [← smulB_eq a f hf1]
    exact (hB Obj Mor X W P B E).2.2.2.2.2.2.1.2.2 a f hf1 hf
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E f hf
    have hf' : f ∈ FredB E := ((hB Obj Mor X W P B E).2.2.2.2.2.2.2.1 f).1 hf
    rw [(hB Obj Mor X W P B E).2.1]
    exact hf'.1
  -- Part I's lemmas, from `B` over the trivial ep-groupoid
  · intro Z _ _ _ PZ W _ _ _ P _ _ B f s hf hs
    have hB' := hB Z Z (EpGroupoid.trivial PZ) W P B (EpStrongBundle.trivial B)
    have hf' : f ∈ GammaB (EpStrongBundle.trivial B) := by
      rw [← hB'.2.1]; exact EpStrongBundle.mem_sectionFunctors_trivial.2 hf
    have hs' : s ∈ GammaB (EpStrongBundle.trivial B) := by
      rw [← hB'.2.1]; exact EpStrongBundle.mem_sectionFunctors_trivial.2 hs
    have h := hB'.2.2.1.2.1 f s hf.1 hs.1 hf' hs'
    rw [addB_eq f s hf.1 hs.1] at h
    exact ⟨h.1, h.2.1⟩
  · intro Z _ _ _ PZ W _ _ _ P _ _ B f a hf
    have hB' := hB Z Z (EpGroupoid.trivial PZ) W P B (EpStrongBundle.trivial B)
    have hf' : f ∈ GammaB (EpStrongBundle.trivial B) := by
      rw [← hB'.2.1]; exact EpStrongBundle.mem_sectionFunctors_trivial.2 hf
    have h := hB'.2.2.1.2.2 a f hf.1 hf'
    rw [smulB_eq a f hf.1] at h
    exact ⟨h.1, h.2.1⟩
  · intro Z _ _ _ PZ W _ _ _ P _ _ B
    have h := (hB Z Z (EpGroupoid.trivial PZ) W P B (EpStrongBundle.trivial B)).2.2.1.1
    rw [zeroB_eq] at h
    exact ⟨h.1, h.2.1⟩

#rt_check RoundTrip.V8_26.A_to_B [Polyfold.EpStrongBundle.fiberZero_mem_sectionFunctors,
  Polyfold.EpStrongBundle.sectionAdd_mem_sectionFunctors,
  Polyfold.EpStrongBundle.sectionSmul_mem_sectionFunctors,
  Polyfold.EpStrongBundle.plusSectionFunctors_subset,
  Polyfold.EpStrongBundle.fiberZero_mem_plusSectionFunctors,
  Polyfold.EpStrongBundle.sectionAdd_mem_plusSectionFunctors,
  Polyfold.EpStrongBundle.sectionSmul_mem_plusSectionFunctors,
  Polyfold.EpStrongBundle.fredholmSectionFunctors_subset,
  Polyfold.StrongBundle.IsScSmoothSection.sectionAdd_of_isScSmoothSection,
  Polyfold.StrongBundle.IsScSmoothSection.sectionSmul_const,
  Polyfold.StrongBundle.isScSmoothSection_fiberZero]
#rt_check RoundTrip.V8_26.B_to_A [Polyfold.EpStrongBundle.fiberZero_mem_sectionFunctors,
  Polyfold.EpStrongBundle.sectionAdd_mem_sectionFunctors,
  Polyfold.EpStrongBundle.sectionSmul_mem_sectionFunctors,
  Polyfold.EpStrongBundle.plusSectionFunctors_subset,
  Polyfold.EpStrongBundle.fiberZero_mem_plusSectionFunctors,
  Polyfold.EpStrongBundle.sectionAdd_mem_plusSectionFunctors,
  Polyfold.EpStrongBundle.sectionSmul_mem_plusSectionFunctors,
  Polyfold.EpStrongBundle.fredholmSectionFunctors_subset,
  Polyfold.StrongBundle.IsScSmoothSection.sectionAdd_of_isScSmoothSection,
  Polyfold.StrongBundle.IsScSmoothSection.sectionSmul_const,
  Polyfold.StrongBundle.isScSmoothSection_fiberZero]
#rt_overlap RoundTrip.V8_26.B_to_A [Polyfold.EpStrongBundle.fiberZero_mem_sectionFunctors,
  Polyfold.EpStrongBundle.sectionAdd_mem_sectionFunctors,
  Polyfold.EpStrongBundle.sectionSmul_mem_sectionFunctors,
  Polyfold.EpStrongBundle.plusSectionFunctors_subset,
  Polyfold.EpStrongBundle.fiberZero_mem_plusSectionFunctors,
  Polyfold.EpStrongBundle.sectionAdd_mem_plusSectionFunctors,
  Polyfold.EpStrongBundle.sectionSmul_mem_plusSectionFunctors,
  Polyfold.EpStrongBundle.fredholmSectionFunctors_subset,
  Polyfold.StrongBundle.IsScSmoothSection.sectionAdd_of_isScSmoothSection,
  Polyfold.StrongBundle.IsScSmoothSection.sectionSmul_const,
  Polyfold.StrongBundle.isScSmoothSection_fiberZero]

end RoundTrip.V8_26
