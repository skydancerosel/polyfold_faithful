import Polyfold.Chapter15.CanonicalLiftIndependence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4,
pp. 701–702, **Theorem 15.4.1** (2017: Theorem 15.6): the sheets `Mᵢ = {f = sᵢ}` of `Λ ∘ f` have
the dimension `ind f`.

# The dimension of the sheets is the Fredholm index

## The text, paraphrased

(pp. 701–702) At a point `y` of `supp(Λ ∘ f)` the operators `(f − sᵢ)'(y)` with `f(y) = sᵢ(y)`
are onto, and their kernels are the tangent spaces `T_yMᵢ`.  The operators belong to
`Lin(f, y)`, so they are Fredholm of the index of `f` at `y`, and `dim Mᵢ = ind f`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* **`KernelBranching.dim_eq_of_isIndexAt`**: for a local branching structure `K` of `Λ ∘ f` at `x`
  described by kernels, if `f` has index `n` at `x` (Part I's `IsIndexAt`, Definition 6.2.1), all
  sheets of `K` have dimension `n`.
* **`exists_kernelBranching_dim`**: at a point of good position (Definition 15.2.4) where `f` has
  index `n` there is such a structure with all sheets of dimension `n`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid

variable {A : SEP.{u}} {f : A.Obj → A.W} {Λ : A.W → ℚ≥0} {x : A.Obj}

/-- **The sheets have the dimension `ind f`** (2021 pp. 701–702): if `f` has Fredholm index `n`
at `x`, every sheet of a local branching structure of `Λ ∘ f` at `x` described by kernels has
dimension `n`: `T_xMᵢ` is the kernel of the onto operator `(f − sᵢ)'(x) ∈ Lin(f, x)`. -/
theorem KernelBranching.dim_eq_of_isIndexAt (K : KernelBranching A f Λ x)
    (hf : A.B.IsScFredholmSection f) (hsec : A.B.HasScPlusSectionsThrough) {n : ℕ}
    (hidx : A.B.IsIndexAt f x n) (i : K.ι) : K.dim i = n := by
  have hx : x ∈ K.M i := K.mem_M i
  set p := K.pt (K.mem_O hx) (K.smooth i x hx) with hp
  have hL := subOp_mem_linSet hf K.isOpen_O (K.isScPlus i) p (K.chart_subset x) (K.eq_of_mem hx)
    (K.smooth i x hx) hsec
  obtain ⟨hF, hi⟩ := p.fredholmIndex_of_mem_linSet hf hidx hL
  have h1 := finrank_ker_eq_fredholmIndex_of_surjective hF (K.surj hf hx)
  have h2 := K.finrank_ker hf hx
  have h3 := (Submodule.equivMapOfInjective (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0)
    Subtype.val_injective (LinearMap.ker ((subOp hf.isScSmooth (K.isScPlus i) p
      (K.chart_subset x) (K.eq_of_mem hx) : ↥p.T →L[ℝ] ↥p.K) : ↥p.T →ₗ[ℝ] ↥p.K))).finrank_eq
  have h4 : (K.dim i : ℤ) = n := by
    rw [← h2, ← h3]
    exact h1.trans hi
  exact_mod_cast h4

/-- **Theorem 15.2.5 with the tangent spaces and the dimension** (2021 pp. 690, 701–702): at a
point `x` where `(f, Λ)` is in good position (Definition 15.2.4) and `f` has index `n`,
`Θ = Λ ∘ f` has a tame local branching structure described by kernels all of whose sheets have
dimension `n`. -/
theorem exists_kernelBranching_dim (hF : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hsec : A.B.HasScPlusSectionsThrough)
    (hgp : IsGoodPositionAt f Λ x) {n : ℕ} (hidx : A.B.IsIndexAt f x n) :
    ∃ K : KernelBranching A f Λ x, ∀ i, K.dim i = n := by
  obtain ⟨K⟩ := exists_kernelBranching hF hft hgp
  exact ⟨K, K.dim_eq_of_isIndexAt hF.2 hsec hidx⟩

end SBLocalization

end Polyfold
