import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_34

/-! Round trip for V6_34 (Lemma 6.30: near the curve `(t, φ(t), 0)` the solution set `S` of `F`
is a manifold with boundary with corners, `π : S → [0, 1]` is a submersion, the fibres `S_t` are
manifolds with corners, `L_t = T S_t = ker F_t'(φ(t), 0)`, and `L` is a smooth vector bundle).

A is the conjunction of the five theorems of the row, universes at `0`:
`IsSurjLinOfIndex.finrank_linKer` (the kernel has the dimension of the index, in every chart),
`exists_local_frame_linKer` and `exists_subspaceFamily_linKer` (along a CONTINUOUS family of zeros
in tame good position inside ONE chart, the kernels `ker Lin(z_q)` have continuous local frames and
form a `SubspaceFamily`), `hasFDerivAt_scDeriv_rn` (sc¹ on open subsets of `ℝⁿ` is Fréchet
differentiable) and `fderiv_mem_linKer` (the derivative of an sc-smooth family of zeros lies in
the kernel).

Neither direction is proved; see the JSON.
* `A ⇒ B` would need what A does not state: the implicit function theorem for `F` on
  `ℝ¹ × ℝᵏ × X` (that `S` and the `S_t` are sub-M-polyfolds and manifolds with corners), the
  surjectivity of `Tπ` on `S`, the identification `ker F_t' = span (tangent cone of S_t)`, and
  `C^∞` (not only continuous) local frames in EVERY chart point.  A's hypotheses are also not given
  by B: an sc-Fredholm section with tame germ data on all of `X` (`IsScFredholmSectionTame`; B's
  `F` is built from `s`, `sᵢ` that are sc⁺ only near `[0, 1] × U`), tame good position at every
  point of the family (B's (P) is general position of the slices `F_t`, not of `F`), and the whole
  family inside the domain of one chart.  All are satisfiable.
* `B ⇒ A`: A's lemmas are general (any section, any family, any `Q`), B is about one family; A
  could only be re-proved outright by copying the five proofs (vacuous), not attempted.

`kerProd_eq_TProd_of_not_isSc1` records the mechanism behind the B_issue of the JSON: in a chart
point where the principal part of `F_t` is not sc¹ on the chart domain, B's `kerProd` is the whole
tangent space `ℝᵏ × T_zO`. -/

namespace RoundTrip.V6_34
open Polyfold StrongRetr

/-- The project's statement (the five theorems of the row), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.StrongBundle.IsSurjLinOfIndex.finrank_linKer.{0, 0} ∧
  type_of% @Polyfold.exists_local_frame_linKer.{0, 0, 0} ∧
  type_of% @Polyfold.exists_subspaceFamily_linKer.{0, 0, 0} ∧
  type_of% @Polyfold.hasFDerivAt_scDeriv_rn ∧
  type_of% @Polyfold.fderiv_mem_linKer.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.StrongBundle.IsSurjLinOfIndex.finrank_linKer.{0, 0},
    @Polyfold.exists_local_frame_linKer.{0, 0, 0},
    @Polyfold.exists_subspaceFamily_linKer.{0, 0, 0},
    @Polyfold.hasFDerivAt_scDeriv_rn,
    @Polyfold.fderiv_mem_linKer.{0, 0}⟩

/-- The project's `linAt` is `0` when `f̂ ∘ r` is not sc¹ on the whole chart domain. -/
theorem linAt_eq_zero_of_not_isSc1 {E F : ScBanach} {U : Set (E 0)}
    {R : E 0 × F 0 → E 0 × F 0} {fb : E 0 → F 0} (z : E 1) (h : ¬ IsSc1 U (fb ∘ r R)) :
    linAt U R fb z = 0 := by
  ext v
  show scDeriv U (fb ∘ r R) z v = 0
  unfold scDeriv
  rw [dif_neg h]
  rfl

/-- **The junk kernel**: in a chart point where `Ĝ ∘ r` is not sc¹ on the domain of the product
chart, B's `kerProd` (its reading of `L_t = ker F_t'(φ(t), 0)`) is the whole tangent space
`T_{(0, z)}(ℝᵏ × O)`.  B's sections are sc⁺ only near `[0, 1] × U` while B quantifies over every
chart point, so B's `L_t = span (tangent cone of S_t)` and its finite smooth frames are then
claims about the whole (in general infinite-dimensional) `ℝᵏ × T_zO`. -/
theorem kerProd_eq_TProd_of_not_isSc1 {X : Type} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] {PX : MPolyfold X} {Y : Type} [TopologicalSpace Y] [T2Space Y]
    [ParacompactSpace Y] {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace ↥(pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    [∀ W : Set ((Fin 1 → ℝ) × X), ParacompactSpace ↥W]
    [∀ W : Set ((Fin 1 → ℝ) × X), ParacompactSpace
      ↥(pullbackSpace (pullbackProj P (Prod.snd : (Fin 1 → ℝ) × X → X))
        (Subtype.val : W → (Fin 1 → ℝ) × X))]
    [∀ n : ℕ, ParacompactSpace ((Fin 1 → ℝ) × ((Fin n → ℝ) × X))]
    [∀ n : ℕ, ParacompactSpace ↥(pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin 1 → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]
    (c : StrongBundleChart PX P) (k : ℕ)
    (q₀ : ↥(pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))) (z : c.φ.model.E.lvl 1)
    (G : (Fin k → ℝ) × X → ↥(pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X)))
    (h : ¬ IsSc1 (prodChart c k q₀).U ((prodChart c k q₀).principal G ∘ r (prodChart c k q₀).R)) :
    kerProd c k q₀ z G = TProd c k q₀ z := by
  unfold kerProd
  rw [linAt_eq_zero_of_not_isSc1 _ h]
  simp

end RoundTrip.V6_34
