import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_38

/-! Round trip for V6_38 (Lemma 6.31: the sequence (96) is exact).  A is `lemma_6_6_6`, universes
at `0`.

* `A_to_B` is not proved (see the JSON).  B's first three conjuncts (injectivity of `j`,
  exactness at `ker(T ⊕ φ)` and at `ℝᵏ`) are pure linear algebra, true for every `T` and `φ`:
  `B_alg_part` proves them outright, without A.  The content is the fourth conjunct, `c` onto
  under (P), and there A's hypotheses are not given by B: A needs `S` and the `sᵢ` to be
  sc⁺-sections of `π*P → ℝⁿ × X` on the whole space (B: `S : X → Y` any map with
  `(f − S)(x) = 0`, the `σᵢ` any sections), an sc-smooth curve `Φ` of zeros through `x`, and
  `F'(0, (q, x))` onto for the whole family over `ℝᵏ × ℝⁿ × X`; B's hypothesis is general position
  of the slice `F_t` over `ℝᵏ × X` in SOME tame chart, while its conclusion is read in EVERY chart
  point `p`.
* `B_to_A` is proved only VACUOUSLY: A is re-proved outright from the non-item lemmas
  `exists_sliceKernel` (the slice operators, `T ∈ Lin(f, x)`, `T ⊕ φ` onto, the slice kernel) and
  `lemma_6_4_14` (the stabilization sequence is exact) -- the proof of `lemma_6_6_6` itself.  B cannot
  be used: its surjectivity conjunct needs the general position of the slice `F_t` (tame chart,
  sc-complement of the kernel in the reduced tangent space), which A's hypotheses (only the
  surjectivity of the whole `F'`) do not give, and B says nothing about `T ∈ Lin(f, x)` or the
  identification of `ker F_t'(φ(t), 0)` with `ker(T ⊕ φ)`. -/

namespace RoundTrip.V6_38
open Polyfold

/-- The project's statement (`lemma_6_6_6`), universes instantiated at `0`. -/
def A : Prop := type_of% @Polyfold.lemma_6_6_6.{0, 0}

theorem A_holds : A := @Polyfold.lemma_6_6_6.{0, 0}

/-! ### B's exactness conjuncts are linear algebra -/

section Alg
variable {M N : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup N]
  [NormedSpace ℝ N] {k : ℕ}

theorem jMap_injective (T : M →L[ℝ] N) (φ : (Fin k → ℝ) →L[ℝ] N) :
    Function.Injective (jMap T φ) := by
  intro a b h
  have := congrArg (fun y : LinearMap.ker (T.coprod φ : M × (Fin k → ℝ) →ₗ[ℝ] N) =>
    (y : M × (Fin k → ℝ)).1) h
  exact Subtype.ext this

theorem exact_jMap_pMap (T : M →L[ℝ] N) (φ : (Fin k → ℝ) →L[ℝ] N) :
    Function.Exact (jMap T φ) (pMap T φ) := by
  rintro ⟨⟨v, μ⟩, hy⟩
  constructor
  · intro h0
    have hμ : μ = 0 := h0
    subst hμ
    have hv : T v = 0 := by
      have := LinearMap.mem_ker.1 hy
      simpa using this
    exact ⟨⟨v, LinearMap.mem_ker.2 hv⟩, rfl⟩
  · rintro ⟨x, hx⟩
    rw [← hx]
    rfl

theorem exact_pMap_c (T : M →L[ℝ] N) (K : Submodule ℝ N) (ψ : (Fin k → ℝ) →L[ℝ] ↥K) :
    Function.Exact (pMap T (K.subtypeL ∘L ψ))
      (((LinearMap.range (T : M →ₗ[ℝ] N)).comap K.subtype).mkQ ∘ₗ
        (ψ : (Fin k → ℝ) →ₗ[ℝ] ↥K)) := by
  intro μ
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨⟨(-v, μ), LinearMap.mem_ker.2 ?_⟩, rfl⟩
    change T (-v) + ((ψ μ : ↥K) : N) = 0
    rw [map_neg, ContinuousLinearMap.coe_coe] at *
    rw [show T v = ((ψ μ : ↥K) : N) from hv]
    exact neg_add_cancel _
  · rintro ⟨⟨⟨v, μ'⟩, hy⟩, rfl⟩
    have h := LinearMap.mem_ker.1 hy
    change T v + ((ψ μ' : ↥K) : N) = 0 at h
    exact ⟨-v, by
      change T (-v) = ((ψ μ' : ↥K) : N)
      rw [map_neg]
      exact neg_eq_of_add_eq_zero_right h⟩

end Alg

/-- B's first three conjuncts, proved outright (without A): only the surjectivity of `c` has
content. -/
theorem B_alg_part {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X) (p : ChartPoint Bd x) (S : X → Y) {k : ℕ}
    (σ : Fin k → X → Y) (hσ : ∀ i, IsSection P (σ i)) :
    let T : ↥p.T →L[ℝ] p.c.F.lvl 0 := linAt p.c.U p.c.R (p.c.principal (sectionDiff P f S)) p.z
    let φ : (Fin k → ℝ) →L[ℝ] p.c.F.lvl 0 := p.K.subtypeL ∘L p.stabPhi σ hσ
    let RT : Submodule ℝ ↥p.K :=
      (LinearMap.range (T : ↥p.T →ₗ[ℝ] p.c.F.lvl 0)).comap p.K.subtype
    let c : (Fin k → ℝ) →ₗ[ℝ] ↥p.K ⧸ RT :=
      RT.mkQ ∘ₗ (p.stabPhi σ hσ : (Fin k → ℝ) →ₗ[ℝ] ↥p.K)
    Function.Injective (jMap T φ) ∧ Function.Exact (jMap T φ) (pMap T φ) ∧
      Function.Exact (pMap T φ) c :=
  ⟨jMap_injective _ _, exact_jMap_pMap _ _, exact_pMap_c _ _ _⟩

/-! ### `B ⇒ A`, vacuous -/

/-- `B ⇒ A`, proved outright (the hypothesis is not used): `exists_sliceKernel` and
`lemma_6_4_14`, both non-item lemmas. -/
theorem B_to_A : B → A := by
  intro _ n k X _ _ _ PX Y _ _ _ P _ _ Bd _ _ _ _ f hf S hS s hs Φ hΦ q x hΦq hΦ0 hsurj p q₀ q₁
  obtain ⟨T, φ, hT, hφ, hlin, hsurj', hker⟩ :=
    exists_sliceKernel hf hS hs hΦ hΦq hΦ0 hsurj p q₀ q₁
  exact ⟨T, φ, hT, hφ, hlin, hker, lemma_6_4_14 hsurj'⟩

#rt_check RoundTrip.V6_38.B_to_A [Polyfold.lemma_6_6_6]
#rt_check RoundTrip.V6_38.B_alg_part [Polyfold.lemma_6_6_6]
#rt_overlap RoundTrip.V6_38.B_to_A [Polyfold.lemma_6_6_6]

end RoundTrip.V6_38
