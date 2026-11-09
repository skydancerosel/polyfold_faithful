import Polyfold.Chapter6.SectionOrientation
import Polyfold.Chapter6.StabilizationContinuity
import Polyfold.Chapter6.AddSections
import Polyfold.Chapter6.ParamKernel
import Polyfold.Chapter6.FamilySections
import Polyfold.Chapter6.PropagationWellDefined
import Polyfold.Chapter6.ChartTransfer
import Polyfold.Chapter3.ParamPerturbationG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5, p. 230:
**Remark 6.6.19 (preprint 6.42)**, the orientation of `f̂(x, t) = f(x) + s(x, t)` over `X × [0, 1]` *(book 2017:
Remark 6.4; see `BookConcordance.md`)*.

# The product orientation of `f + s` over `X × [0, 1]`

## The text, paraphrased

Let `(f, o)` be an oriented sc-Fredholm section of `P : Y → X` and `s` an sc⁺-section of the
pull-back of `Y` to `X × [0, 1]`.  The sc-Fredholm section `f̂(x, t) = f(x) + s(x, t)` has a
natural orientation, made from `o` and the standard orientation of `[0, 1]`.  At a smooth point
`x` take a local sc⁺-section `t̃` with `t̃(x) = f(x)` and `L = (f − t̃)'(x) : T_xX → Y_x`.  If
`h = (a₁ ∧ … ∧ aₙ) ⊗ (b₁ ∧ … ∧ b_l)*` gives the orientation `o_x` of `det(L)`, orient
`L̃ : T_{(x, t)}(X × [0, 1]) → Y_x`, `L̃(a, b) = La`, by
`h̃ = (a₁ ∧ … ∧ aₙ ∧ e) ⊗ (b₁ ∧ … ∧ b_l)*`, where `e` is the standard orientation of `[0, 1]`.
`L̃` lies in the linearization space of `f̂` at `(x, t)`, so `DET(f̂, (x, t))` is oriented.

## What is formalized

* **Linear algebra** for `L̃ = L ⊕ 0 : E × ℝ¹ → F` (`extOp`): `L̃` is Fredholm
  (`isFredholm_extOp`); `ker L̃ = ker L × ℝ`, with `dim ker L̃ = dim ker L + 1`
  (`finrank_ker_extOp`) and `e = (0, 1)` (`extE`); `coker L̃ = coker L` (`range_extOp`,
  `extCoker`).  The map `h ↦ h̃` is the isomorphism `extDet : det(L) ≅ det(L̃)`, and
  `extDet_wedge_tmul` sends `(a₁ ∧ … ∧ aₙ) ⊗ d*` to `((a₁, 0) ∧ … ∧ (aₙ, 0) ∧ e) ⊗ d*`.  Its
  sign-normalized form is `extDetN`.
* **Continuity**: `coord_extDet` and `coord_extDetN` give the chart coordinates; with them
  `isLineOrientation_extPull` and `LineOrientation.extPull` pull an orientation of `DET` over a
  set `C'` of operators `E × ℝ¹ → F` back along `L ↦ L̃` and `extDetN`, to an orientation over a
  set `C` with `L̃ ∈ C'` for all `L ∈ C`.
* **Transport**: `extConjOp` is `L̂ = Γ⁻¹ L̃ A` for isomorphisms `A : E' ≅ E × ℝ¹` and
  `Γ : F' ≅ F`, and `extConjDet : det(L) ≅ det(L̂)` (`extConjDet_apply`,
  `extConjDet_wedge_tmul`).  `existsUnique_extConjOr` gives exactly one orientation `ô` over `Ĉ`
  with `ô(L̂) = extConjDet(o(L))` for all `L ∈ C`.
* **In charts**:
  * `ChartPoint.prodPt` is the product chart point at `(t, x) ∈ ℝ¹ × X`.
  * `mem_prodPt_T_iff` and `mem_prodPt_K_iff` give `T_{(t, z)} = ℝ¹ × T_zO` and fibre `K_z`.
  * `prodT`, `prodK` and `prodLin` are `A`, `Γ` and `L̂`.
  * `prodLin_mem_linSet`: **`L̂ ∈ Lin(f̂, (t, x))`** for every `L ∈ Lin(f, x)`, where
    `f̂ = f̃ + S`.  The proof uses `IsScPlusOp.prodPt` and the `t`-constant lift `constLift`.
* **Remark 6.6.19 (preprint 6.42)**: `ChartPoint.existsUnique_prodOr`, `ChartPoint.prodOr` and `prodOr_apply`.
  An orientation `o` of `DET(f, x)` gives exactly one orientation `ô` of `DET(f̂, (t, x))` with
  `ô(L̂) = extConjDet(o(L))` for **all** `L ∈ Lin(f, x)`.  So the orientation does not depend on
  the choice of `L`.  `prodOr_injective` says that `o ↦ ô` is injective.

## Reading

* **`X × [0, 1]` is read as `ℝ¹ × X`** (decision D2): the parameter lies in `ℝ¹`
  (`rnPolyfold 1`, as for the families of Chapter 6) and comes first.
  * `s` is an sc⁺-section `S` of the pull-back `π*P` along `π = Prod.snd : ℝ¹ × X → X`.
  * `f̂ = f̃ + S` with `f̃(t, x) = f(x)` (`paramLift`); it is sc-Fredholm by
    `IsScFredholmSection.param` and Theorem 3.1.18 (preprint 3.15).
  * At a single point the restriction to `t ∈ [0, 1]` plays no role.
* **The linearization space of `f̂` is read in a product chart point** `prodPt`.
  * The chart is `(r ↦ r) × φ` of `ℝ¹ × X` over a chart point `p = (c, z)` of `x`, taken at
    `(t, z)`.  There `T_{(t, z)} = ℝ¹ × T_zO` and the fibre is `K_z`.
  * The text's `L̃(a, b) = La` puts the `ℝ`-factor second, so it is read as
    `L̂ = Γ⁻¹ (L ⊕ 0) A`, with `A(σ, v) = (v, σ)` (`prodT`) and `Γ` the identity of `K_z`
    (`prodK`).
  * `e = (0, 1)` is the unit vector of the `ℝ`-factor.
  * As in `LinSet.lean`, `Lin(f, x)` uses global sc⁺-sections; the text uses local ones.
* **The sign of `h̃`**.
  * As we read it, `h ↦ (a₁ ∧ … ∧ aₙ ∧ e) ⊗ (b₁ ∧ … ∧ b_l)*` used at every `L` is not
    continuous in `L` where the parity of `dim coker L` changes.
  * In local determinant charts its coordinate is `(−1)^{dim F/R(P) + dim coker L}` times a
    continuous nonzero function (`coord_extDet`).  So the orientation of `DET(f̂, (x, t))` it
    defines could depend on the choice of `L ∈ Lin(f, x)`.
  * We use `extDetN = (−1)^{dim coker L} · extDet` instead (`coord_extDetN`, the sign
    `stabSign` of the stabilization).  It agrees with the text's map whenever `L` is onto
    (`extDetN_eq_of_surjective`).
* **Hypotheses**: `x` is a smooth point and `Lin(f, x)` is nonempty.  The latter holds under
  `B.HasScPlusSectionsThrough` (`ChartPoint.linSet_nonempty`).  The remark needs only an
  orientation `o` of `DET(f, x)` at the one point `x`, not an orientation of `f`.
-/

open Module TensorProduct Bundle Topology Set

noncomputable section

namespace Polyfold

universe u v

section ExtLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {T : E →L[ℝ] F}

/-- **`L̃(a, b) = L a`**: the operator `T ⊕ 0 : E × ℝ → F`. -/
abbrev extOp (T : E →L[ℝ] F) : E × (Fin 1 → ℝ) →L[ℝ] F :=
  T.coprod (0 : (Fin 1 → ℝ) →L[ℝ] F)

omit [CompleteSpace E] [CompleteSpace F] in
/-- `L̃(a, b) = L a`. -/
theorem extOp_apply (T : E →L[ℝ] F) (v : E × (Fin 1 → ℝ)) : extOp T v = T v.1 := by
  simp

omit [CompleteSpace E] [CompleteSpace F] in
/-- `T ↦ T ⊕ 0` is continuous. -/
theorem continuous_extOp : Continuous (extOp : (E →L[ℝ] F) → E × (Fin 1 → ℝ) →L[ℝ] F) :=
  continuous_coprod (Q := E →L[ℝ] F) continuous_id continuous_const

/-- **`e = (0, 1) ∈ ker L̃`**. -/
def extE (T : E →L[ℝ] F) : LinearMap.ker (extOp T : E × (Fin 1 → ℝ) →ₗ[ℝ] F) :=
  ⟨(0, fun _ => 1), mem_ker_coprod.2 (by simp)⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- `e = (0, 1)`. -/
@[simp] theorem coe_extE (T : E →L[ℝ] F) :
    (extE T : E × (Fin 1 → ℝ)) = (0, fun _ => 1) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- The `ℝ`-coordinate of `e` is `1`. -/
theorem stabPi_extE (T : E →L[ℝ] F) : stabPi T 0 (extE T) = Pi.single 0 1 := by
  funext i
  fin_cases i
  simp

omit [CompleteSpace E] [CompleteSpace F] in
/-- `(a, b) ↦ b` is onto `ℝ` on `ker L̃`. -/
theorem stabPi_extOp_surjective (T : E →L[ℝ] F) :
    Function.Surjective (stabPi T (0 : (Fin 1 → ℝ) →L[ℝ] F)) := fun μ =>
  ⟨⟨(0, μ), mem_ker_coprod.2 (by simp)⟩, rfl⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- **`ker L̃ = ker L × ℝ`**: `dim ker L̃ = dim ker L + 1`. -/
theorem finrank_ker_extOp (hT : T.IsFredholm) :
    finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)) + 1 =
      finrank ℝ (LinearMap.ker (extOp T : E × (Fin 1 → ℝ) →ₗ[ℝ] F)) := by
  have := hT.finite_ker
  have := finiteDimensional_ker_coprod (T := T) (φ := (0 : (Fin 1 → ℝ) →L[ℝ] F))
  have h := LinearMap.finrank_range_add_finrank_ker (stabPi T (0 : (Fin 1 → ℝ) →L[ℝ] F))
  rw [LinearMap.range_eq_top.2 (stabPi_extOp_surjective T), finrank_top, Module.finrank_fin_fun,
    ← range_stabJ, LinearMap.finrank_range_of_inj stabJ_injective] at h
  change _ = finrank ℝ (LinearMap.ker ((T.coprod (0 : (Fin 1 → ℝ) →L[ℝ] F) :
    E × (Fin 1 → ℝ) →L[ℝ] F) : E × (Fin 1 → ℝ) →ₗ[ℝ] F))
  omega

omit [CompleteSpace E] [CompleteSpace F] in
/-- **`coker L̃ = coker L`**: `R(L̃) = R(L)`. -/
theorem range_extOp (T : E →L[ℝ] F) :
    LinearMap.range (extOp T : E × (Fin 1 → ℝ) →ₗ[ℝ] F) = LinearMap.range (T : E →ₗ[ℝ] F) := by
  ext y
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v.1, by simp⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(x, 0), by simp⟩

/-- **`L̃` is Fredholm** (of the index of `L` plus one). -/
theorem isFredholm_extOp (hT : T.IsFredholm) : (extOp T).IsFredholm := by
  have := hT.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  refine isFredholm_of_banach _ finiteDimensional_ker_coprod ?_ ?_
  · have h : (extOp T).range = T.range := range_extOp T
    rw [h]
    exact hT.isClosed_range
  · have h : (extOp T).range = T.range := range_extOp T
    rw [h]
    exact hT.finite_coker

omit [CompleteSpace E] [CompleteSpace F] in
/-- `ker L̃` is finite-dimensional. -/
theorem finiteDimensional_ker_extOp (hT : T.IsFredholm) :
    FiniteDimensional ℝ (LinearMap.ker (extOp T : E × (Fin 1 → ℝ) →ₗ[ℝ] F)) :=
  haveI := hT.finite_ker
  finiteDimensional_ker_coprod (T := T) (φ := (0 : (Fin 1 → ℝ) →L[ℝ] F))

/-- **`λ(ker L) ≅ λ(ker L̃)`, `a₁ ∧ … ∧ aₙ ↦ (a₁, 0) ∧ … ∧ (aₙ, 0) ∧ e`**. -/
def extKer (hT : T.IsFredholm) :
    maxPow (LinearMap.ker (T : E →ₗ[ℝ] F)) ≃ₗ[ℝ]
      maxPow (LinearMap.ker (extOp T : E × (Fin 1 → ℝ) →ₗ[ℝ] F)) :=
  haveI := hT.finite_ker
  haveI := finiteDimensional_ker_extOp hT
  LinearEquiv.ofBijective (wedgeExt (stabJ T 0) ![extE T] (finrank_ker_extOp hT))
    (wedgeExt_bijective_of_proj (stabJ T 0) stabJ_injective (stabPi T 0) (fun v => by simp)
      ![extE T] (fun j => by fin_cases j; exact stabPi_extE T) _)

omit [CompleteSpace E] [CompleteSpace F] in
/-- `extKer` on a wedge. -/
theorem extKer_wedge (hT : T.IsFredholm) {n : ℕ} (a : Fin n → LinearMap.ker (T : E →ₗ[ℝ] F))
    (hn : n = finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F))) :
    extKer hT (wedge a hn) =
      wedge (Fin.append (stabJ T 0 ∘ a) ![extE T]) (by rw [hn]; exact finrank_ker_extOp hT) :=
  wedgeExt_wedge _ _ (finrank_ker_extOp hT) a hn

/-- **`coker L̃ = coker L`** as quotients: `F / R(L̃) ≅ F / R(L)`. -/
def extCoker (T : E →L[ℝ] F) :
    (F ⧸ LinearMap.range (extOp T : E × (Fin 1 → ℝ) →ₗ[ℝ] F)) ≃ₗ[ℝ]
      F ⧸ LinearMap.range (T : E →ₗ[ℝ] F) :=
  Submodule.quotEquivOfEq _ _ (range_extOp T)

/-- **`det(L) ≅ det(L̃)`, `(a₁ ∧ … ∧ aₙ) ⊗ ξ ↦ (a₁ ∧ … ∧ aₙ ∧ e) ⊗ ξ`** (the map of Remark 6.6.19 (preprint 6.42),
with `coker L̃ = coker L`). -/
def extDet (hT : T.IsFredholm) : fredholmDet T ≃ₗ[ℝ] fredholmDet (extOp T) :=
  TensorProduct.congr (extKer hT) (maxPowDualEquiv (extCoker T))

omit [CompleteSpace E] [CompleteSpace F] in
/-- **`extDet` on generators**: `(a₁ ∧ … ∧ aₙ) ⊗ (d₁ ∧ … ∧ d_l)* ↦
((a₁, 0) ∧ … ∧ (aₙ, 0) ∧ e) ⊗ (d₁ ∧ … ∧ d_l)*`. -/
theorem extDet_wedge_tmul (hT : T.IsFredholm) {n l : ℕ}
    (a : Fin n → LinearMap.ker (T : E →ₗ[ℝ] F)) (hn : n = finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)))
    {d : Fin l → F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)} (hd : LinearIndependent ℝ d)
    (hl : l = finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))) :
    extDet hT (wedge a hn ⊗ₜ dualVec (wedge d hl)) =
      wedge (Fin.append (stabJ T 0 ∘ a) ![extE T]) (by rw [hn]; exact finrank_ker_extOp hT) ⊗ₜ
        dualVec (wedge ((extCoker T).symm ∘ d) (hl.trans (extCoker T).symm.finrank_eq)) := by
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (extOp T : E × (Fin 1 → ℝ) →ₗ[ℝ] F)) :=
    (extCoker T).symm.finiteDimensional
  rw [extDet, TensorProduct.congr_tmul, extKer_wedge, maxPowDualEquiv_dualVec_symm _ hd hl]

/-- **The sign-normalized isomorphism** `(−1)^{dim coker L} · extDet : det(L) ≅ det(L̃)`: the map
`h ↦ h̃` of Remark 6.6.19 (preprint 6.42), normalized so that it is continuous in `L` (it agrees with the text's map
when `L` is onto). -/
def extDetN (hT : T.IsFredholm) : fredholmDet T ≃ₗ[ℝ] fredholmDet (extOp T) :=
  (LinearEquiv.smulOfUnit (stabSign T)).trans (extDet hT)

omit [CompleteSpace E] [CompleteSpace F] in
/-- `extDetN = (−1)^{dim coker L} · extDet`. -/
theorem extDetN_apply (hT : T.IsFredholm) (x : fredholmDet T) :
    extDetN hT x = ((stabSign T : ℝˣ) : ℝ) • extDet hT x := by
  change extDet hT ((stabSign T : ℝˣ) • x) = _
  rw [Units.smul_def]
  exact (extDet hT).map_smul _ _

omit [CompleteSpace E] [CompleteSpace F] in
/-- `extDetN = extDet` when `L` is onto. -/
theorem extDetN_eq_of_surjective (hT : T.IsFredholm) (hs : Function.Surjective T)
    (x : fredholmDet T) : extDetN hT x = extDet hT x := by
  have h0 : finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) = 0 := by
    have : Subsingleton (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) :=
      Submodule.Quotient.subsingleton_iff.2 (LinearMap.range_eq_top.2 hs)
    exact Module.finrank_zero_of_subsingleton
  have hs1 : ((stabSign T : ℝˣ) : ℝ) = 1 := by
    rw [stabSign, h0, pow_zero, Units.val_one]
  rw [extDetN_apply, hs1, one_smul]

end ExtLinear

/-! ### The chart coordinates of `extDet` -/

section ExtCoord

/-- `u ++ (∅ ++ x) = (u ++ x) ∘ cast`. -/
theorem append_elim0_append {α : Type*} {p q : ℕ} (u : Fin p → α) (x : Fin q → α) :
    Fin.append u (Fin.append (Fin.elim0 : Fin 0 → α) x) =
      Fin.append u x ∘ Fin.cast (by omega) := by
  rw [Fin.elim0_append]
  funext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [Fin.append_left, Function.comp_apply,
      show Fin.cast (by omega) (Fin.castAdd (0 + q) i) = Fin.castAdd q i from Fin.ext rfl,
      Fin.append_left]
  · rw [Fin.append_right, Function.comp_apply, Function.comp_apply]
    change _ = Fin.append u x (Fin.natAdd p (Fin.cast (Nat.zero_add q) i))
    rw [Fin.append_right]

/-- A determinant in a reindexed basis does not see a `Fin.cast` of the family. -/
theorem det_reindex_comp_cast {M : Type*} [AddCommGroup M] [Module ℝ M] {N p q : ℕ}
    (b : Basis (Fin N) ℝ M) (hp : N = p) (hq : N = q) (hpq : p = q) (g : Fin q → M) :
    (b.reindex (finCongr hp)).det (g ∘ Fin.cast hpq) = (b.reindex (finCongr hq)).det g := by
  subst hp hpq
  rfl

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **The comparison on adapted vectors**: in charts `c` at `T` and `c'` at `T ⊕ 0` with the same
projection, the `c'`-coordinate of `extDet` of `(a-wedge) ⊗ (d-wedge)*` is `(−1)^j D(S, 0)` times
the `c`-coordinate, `j = dim ker(P S) − dim ker S`. -/
theorem coord_extDet_aux (c : LocalDetChart E F) (c' : LocalDetChart (E × (Fin 1 → ℝ)) F)
    (hP : c'.P = c.P) (hK : finrank ℝ c'.K = finrank ℝ c.K + 1) (t : Fin 1 → c'.K)
    {S : E →L[ℝ] F} (hSF : S.IsFredholm) (hS : ‖S - c.T‖ < c.ε) (hAF : (extOp S).IsFredholm)
    (hA : ‖extOp S - c'.T‖ < c'.ε)
    (ht : (Pi.basisFun ℝ (Fin 1)).det (fun j => (c'.kerMap (extOp S) (t j)).2) ≠ 0)
    {n l j : ℕ} {a : Fin n → LinearMap.ker (S : E →ₗ[ℝ] F)} (ha : LinearIndependent ℝ a)
    (hn : n = finrank ℝ (LinearMap.ker (S : E →ₗ[ℝ] F)))
    {d : Fin l → F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)} (hd : LinearIndependent ℝ d)
    (hl : l = finrank ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)))
    {b : Fin j → LinearMap.ker ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)}
    (hb : LinearIndependent ℝ (Fin.append (projSeqJ S c.P ∘ a) b))
    (hj : n + j = finrank ℝ (LinearMap.ker ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)))
    (y : Fin l → F)
    (hy : ∀ i, projSeqPi (T := S) (c.isGoodLeftProj_of_lt S hS).isProj
      (Submodule.Quotient.mk (y i)) = d i) :
    c'.coord ⟨extOp S, hAF⟩ (extDet hSF (wedge a hn ⊗ₜ dualVec (wedge d hl))) =
      ((-1 : ℝ) ^ j * stabD c c' hK t S 0) *
        c.coord ⟨S, hSF⟩ (wedge a hn ⊗ₜ dualVec (wedge d hl)) := by
  have hPS : IsGoodLeftProj S c.P := c.isGoodLeftProj_of_lt S hS
  have hPA : IsGoodLeftProj (extOp S) c'.P := c'.isGoodLeftProj_of_lt _ hA
  have := hSF.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) := hSF.finite_coker
  have := c.finiteDimensional_ker S hS
  have := c'.finiteDimensional_ker _ hA
  have := finiteDimensional_ker_extOp hSF
  have hidx := finrank_ker_comp_add hSF hPS
  have hK1 : finrank ℝ c.K = n + j := (c.kerEquiv S hS).finrank_eq.trans hj.symm
  have h2 : finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) = l + j := by omega
  -- the `S`-side coordinate
  let cc : Fin l → F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F) := fun i => Submodule.Quotient.mk (y i)
  have hcS := c.coord_wedge_tmul hSF hS ha hn hd hl hb hj (cc := cc) hy hK1 h2
  -- the `S ⊕ 0`-side vectors
  let a' : Fin (n + 1) → LinearMap.ker (extOp S : E × (Fin 1 → ℝ) →ₗ[ℝ] F) :=
    Fin.append (stabJ S 0 ∘ a) ![extE S]
  have ha' : LinearIndependent ℝ a' :=
    linearIndependent_fin_append_of_single (stabPi S 0)
      (ha.map' _ (LinearMap.ker_eq_bot.2 stabJ_injective)) (fun i => by simp)
      (fun j => by fin_cases j; exact stabPi_extE S)
  have hn' : n + 1 = finrank ℝ (LinearMap.ker (extOp S : E × (Fin 1 → ℝ) →ₗ[ℝ] F)) := by
    rw [hn]
    exact finrank_ker_extOp hSF
  have hd' : LinearIndependent ℝ ((extCoker S).symm ∘ d) := hd.map' _ (extCoker S).symm.ker
  have hl' := hl.trans (extCoker S).symm.finrank_eq
  let e' : LinearMap.ker ((c'.P ∘L extOp S : E × (Fin 1 → ℝ) →L[ℝ] F) :
      E × (Fin 1 → ℝ) →ₗ[ℝ] F) := projSeqJ (extOp S) c'.P (extE S)
  let b' : Fin j → LinearMap.ker ((c'.P ∘L extOp S : E × (Fin 1 → ℝ) →L[ℝ] F) :
      E × (Fin 1 → ℝ) →ₗ[ℝ] F) := stabKerInl hP S 0 ∘ b
  have hJ' : projSeqJ (extOp S) c'.P ∘ a' =
      Fin.append (stabKerInl hP S 0 ∘ (projSeqJ S c.P ∘ a)) ![e'] := by
    rw [comp_append]
    congr 1
    funext i
    fin_cases i
    rfl
  have hker' := (c'.kerEquiv _ hA).finrank_eq
  have hj' : n + 1 + j = finrank ℝ (LinearMap.ker ((c'.P ∘L extOp S :
      E × (Fin 1 → ℝ) →L[ℝ] F) : E × (Fin 1 → ℝ) →ₗ[ℝ] F)) := by omega
  have h1' : finrank ℝ c'.K = n + 1 + j := by omega
  have h1 : finrank ℝ c'.K = n + 1 + (0 + j) := by omega
  have hδ := det_kerProj_stab c c' hP hK t hS hA ht (projSeqJ S c.P ∘ a) b ![e']
    (Fin.elim0 : Fin 0 → LinearMap.ker ((c'.P ∘L extOp S : E × (Fin 1 → ℝ) →L[ℝ] F) :
      E × (Fin 1 → ℝ) →ₗ[ℝ] F)) h1 hK1 rfl
  have hfam : (fun i => c'.kerProj (Fin.append (Fin.append (stabKerInl hP S 0 ∘
      (projSeqJ S c.P ∘ a)) ![e']) (Fin.append (Fin.elim0 : Fin 0 → LinearMap.ker
        ((c'.P ∘L extOp S : E × (Fin 1 → ℝ) →L[ℝ] F) : E × (Fin 1 → ℝ) →ₗ[ℝ] F))
          (stabKerInl hP S 0 ∘ b)) i).1) =
      (fun i => c'.kerProj (Fin.append (projSeqJ (extOp S) c'.P ∘ a') b' i).1) ∘
        Fin.cast (by omega : n + 1 + (0 + j) = n + 1 + j) := by
    rw [append_elim0_append, ← hJ']
    rfl
  have hone : (Pi.basisFun ℝ (Fin 1)).det ((stabKerSnd c'.P S 0 ∘ Fin.append
      (Fin.elim0 : Fin 0 → LinearMap.ker ((c'.P ∘L extOp S : E × (Fin 1 → ℝ) →L[ℝ] F) :
        E × (Fin 1 → ℝ) →ₗ[ℝ] F)) ![e']) ∘ Fin.cast (rfl : 0 + 1 = 1).symm) = 1 := by
    have h : (stabKerSnd c'.P S 0 ∘ Fin.append
        (Fin.elim0 : Fin 0 → LinearMap.ker ((c'.P ∘L extOp S : E × (Fin 1 → ℝ) →L[ℝ] F) :
          E × (Fin 1 → ℝ) →ₗ[ℝ] F)) ![e']) ∘ Fin.cast (rfl : 0 + 1 = 1).symm =
        Pi.basisFun ℝ (Fin 1) := by
      funext i k
      obtain rfl := Fin.fin_one_eq_zero i
      obtain rfl := Fin.fin_one_eq_zero k
      rw [Fin.elim0_append]
      simp only [Function.comp_apply, Matrix.cons_val_fin_one, stabKerSnd_apply,
        Pi.basisFun_apply, Pi.single_eq_same]
      rfl
    rw [h, Basis.det_self]
  have hδS : ((Module.finBasis ℝ c.K).reindex (finCongr hK1)).det
      (fun i => c.kerProj (Fin.append (projSeqJ S c.P ∘ a) b i).1) ≠ 0 := by
    intro h0
    have E := c.wedge_eq_det_smul_wedge_kerFrame S hS (Fin.append (projSeqJ S c.P ∘ a) b) hj hK1
    rw [h0, zero_smul] at E
    exact (wedge_ne_zero_iff hj).2 hb E
  have hnum : ((Module.finBasis ℝ c'.K).reindex (finCongr h1')).det
      (fun i => c'.kerProj (Fin.append (projSeqJ (extOp S) c'.P ∘ a') b' i).1) =
      (-1 : ℝ) ^ j * ((Module.finBasis ℝ c.K).reindex (finCongr hK1)).det
        (fun i => c.kerProj (Fin.append (projSeqJ S c.P ∘ a) b i).1) *
        stabD c c' hK t S 0 := by
    rw [← det_reindex_comp_cast (Module.finBasis ℝ c'.K) h1 h1'
      (by omega : n + 1 + (0 + j) = n + 1 + j), ← hfam, hδ, hone,
      show (1 + 0) * j + 1 * 0 = j by ring]
    ring
  have hvec : LinearIndependent ℝ (Fin.append (projSeqJ (extOp S) c'.P ∘ a') b') := by
    rw [← wedge_ne_zero_iff hj', c'.wedge_eq_det_smul_wedge_kerFrame (extOp S) hA _ hj' h1',
      hnum]
    exact smul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hδS)
      (stabD_ne_zero c c' hP hK t hS hA ht)) (c'.wedge_kerFrame_ne_zero _ hA)
  let cc' : Fin l → F ⧸ LinearMap.range (c'.P : F →ₗ[ℝ] F) :=
    fun i => Submodule.Quotient.mk (y i)
  have hcc' : ∀ i, projSeqPi (T := extOp S) hPA.isProj (cc' i) = ((extCoker S).symm ∘ d) i := by
    intro i
    rw [Function.comp_apply, ← hy i]
    simp only [cc', projSeqPi, extCoker, Submodule.liftQ_apply, LinearMap.coe_comp,
      Function.comp_apply, Submodule.mkQ_apply, hP]
    rfl
  have h2' : finrank ℝ (F ⧸ LinearMap.range (c'.P : F →ₗ[ℝ] F)) = l + j := by
    rw [hP]
    exact h2
  have hcA := c'.coord_wedge_tmul hAF hA ha' hn' hd' hl' hvec hj' (cc := cc') hcc' h1' h2'
  have hden : ((Module.finBasis ℝ (F ⧸ LinearMap.range (c'.P : F →ₗ[ℝ] F))).reindex
      (finCongr h2')).det (Fin.append cc' (projSeqPhi (extOp S) c'.P ∘ b')) =
      ((Module.finBasis ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F))).reindex
        (finCongr h2)).det (Fin.append cc (projSeqPhi S c.P ∘ b)) := by
    have := det_finBasis_quot_congr hP h2 h2' rfl (Fin.append cc (projSeqPhi S c.P ∘ b))
      (Fin.append cc' (projSeqPhi (extOp S) c'.P ∘ b')) fun i => by
        induction i using Fin.addCases with
        | left i => exact ⟨y i, by rw [Fin.append_left], by rw [Fin.append_left]⟩
        | right i =>
          refine ⟨S (b i), by rw [Fin.append_right]; rfl, ?_⟩
          rw [Fin.append_right]
          change Submodule.Quotient.mk ((S.coprod (0 : (Fin 1 → ℝ) →L[ℝ] F))
            ((b i : E), (0 : Fin 1 → ℝ))) = _
          rw [ContinuousLinearMap.coprod_apply, map_zero, add_zero]
    exact this
  rw [extDet_wedge_tmul hSF a hn hd hl]
  refine hcA.trans ?_
  rw [hcS, hnum, hden]
  ring

/-- **The chart coordinate of `extDet`**: in charts `c` at `T` and `c'` at `T ⊕ 0` with the same
projection `P`, `c'(extDet x) = (−1)^{dim F/R(P) + dim coker S} D(S, 0) c(x)`. -/
theorem coord_extDet (c : LocalDetChart E F) (c' : LocalDetChart (E × (Fin 1 → ℝ)) F)
    (hP : c'.P = c.P) (hK : finrank ℝ c'.K = finrank ℝ c.K + 1) (t : Fin 1 → c'.K)
    {S : E →L[ℝ] F} (hSF : S.IsFredholm) (hS : ‖S - c.T‖ < c.ε) (hAF : (extOp S).IsFredholm)
    (hA : ‖extOp S - c'.T‖ < c'.ε)
    (ht : (Pi.basisFun ℝ (Fin 1)).det (fun j => (c'.kerMap (extOp S) (t j)).2) ≠ 0)
    (x : fredholmDet S) :
    c'.coord ⟨extOp S, hAF⟩ (extDet hSF x) =
      ((-1 : ℝ) ^ (finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) +
          finrank ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F))) * stabD c c' hK t S 0) *
        c.coord ⟨S, hSF⟩ x := by
  classical
  have hPS : IsGoodLeftProj S c.P := c.isGoodLeftProj_of_lt S hS
  have := hSF.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) := hSF.finite_coker
  have := c.finiteDimensional_ker S hS
  set a := Module.finBasis ℝ (LinearMap.ker (S : E →ₗ[ℝ] F))
  set d := Module.finBasis ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F))
  obtain ⟨j, b, hb, hj⟩ := exists_linearIndependent_append (projSeqJ S c.P) (proposition_6_4_10 hPS).1
    a.linearIndependent rfl
  have hex : ∀ i, ∃ y : F,
      projSeqPi (T := S) hPS.isProj (Submodule.Quotient.mk y) = d i := fun i => by
    obtain ⟨q, hq⟩ := (proposition_6_4_10 hPS).2.2.2 (d i)
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨y, hq⟩
  choose y hy using hex
  have hidx := finrank_ker_comp_add hSF hPS
  have hjm : finrank ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) + j =
      finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) := by omega
  have key := coord_extDet_aux c c' hP hK t hSF hS hAF hA ht a.linearIndependent rfl
    d.linearIndependent rfl hb hj y hy
  have hsign : (-1 : ℝ) ^ (finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) +
      finrank ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F))) = (-1) ^ j := by
    rw [← hjm, show finrank ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) + j +
      finrank ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) =
        j + 2 * finrank ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) by ring,
      pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  have hx₀ : (wedge a rfl ⊗ₜ dualVec (wedge d rfl) : fredholmDet S) ≠ 0 :=
    tmul_ne_zero_of_ne_zero (wedge_basis_ne_zero' _ rfl)
      (dualVec_ne_zero finrank_maxPow (wedge_basis_ne_zero' _ rfl))
  obtain ⟨r, rfl⟩ := exists_smul_eq_of_finrank_eq_one (finrank_fredholmDet hSF) hx₀ x
  rw [LinearEquiv.map_smul]
  refine ((c'.coord _).map_smul _ _).trans ?_
  refine Eq.trans ?_ (congrArg (fun z => ((-1 : ℝ) ^ (finrank ℝ (F ⧸ LinearMap.range
    (c.P : F →ₗ[ℝ] F)) + finrank ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F))) *
      stabD c c' hK t S 0) * z) ((c.coord ⟨S, hSF⟩).map_smul r _)).symm
  rw [smul_eq_mul, smul_eq_mul, key, hsign]
  ring

/-- **The chart coordinate of the normalized `extDetN`**: `c'(extDetN x) = (−1)^{dim F/R(P)}
D(S, 0) c(x)`; the factor is continuous in `S` (the sign `(−1)^{dim coker S}` of `extDet` is
gone). -/
theorem coord_extDetN (c : LocalDetChart E F) (c' : LocalDetChart (E × (Fin 1 → ℝ)) F)
    (hP : c'.P = c.P) (hK : finrank ℝ c'.K = finrank ℝ c.K + 1) (t : Fin 1 → c'.K)
    {S : E →L[ℝ] F} (hSF : S.IsFredholm) (hS : ‖S - c.T‖ < c.ε) (hAF : (extOp S).IsFredholm)
    (hA : ‖extOp S - c'.T‖ < c'.ε)
    (ht : (Pi.basisFun ℝ (Fin 1)).det (fun j => (c'.kerMap (extOp S) (t j)).2) ≠ 0)
    (x : fredholmDet S) :
    c'.coord ⟨extOp S, hAF⟩ (extDetN hSF x) =
      ((-1 : ℝ) ^ finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) * stabD c c' hK t S 0) *
        c.coord ⟨S, hSF⟩ x := by
  rw [extDetN_apply]
  refine ((c'.coord _).map_smul _ _).trans ?_
  rw [smul_eq_mul, coord_extDet c c' hP hK t hSF hS hAF hA ht]
  have hs : ((stabSign S : ℝˣ) : ℝ) = (-1) ^ finrank ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) := by
    simp [stabSign]
  have hm2 : ((-1 : ℝ) ^ finrank ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F))) *
      (-1) ^ finrank ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [hs, pow_add]
  linear_combination ((-1 : ℝ) ^ finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) *
    stabD c c' hK t S 0 * c.coord ⟨S, hSF⟩ x) * hm2

end ExtCoord

/-! ### Pulling an orientation back along `L ↦ L̃` -/

section ExtPull

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {C : Set (E →L[ℝ] F)} {hC : ∀ T ∈ C, T.IsFredholm}
  {C' : Set (E × (Fin 1 → ℝ) →L[ℝ] F)} {hC' : ∀ T ∈ C', T.IsFredholm}

omit [CompleteSpace E] [CompleteSpace F] in
/-- The map `C → C'`, `L ↦ L̃ = L ⊕ 0`. -/
def extMap (hmem : ∀ S ∈ C, extOp S ∈ C') : C → C' := fun S => ⟨extOp S.1, hmem S.1 S.2⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- `L ↦ L̃` is continuous on `C`. -/
theorem continuous_extMap (hmem : ∀ S ∈ C, extOp S ∈ C') : Continuous (extMap hmem) :=
  (continuous_extOp.comp continuous_subtype_val).subtype_mk _

omit [CompleteSpace E] [CompleteSpace F] in
/-- `extDetN` read on the fibres `DetFiber` of `DET`, for `S' = S ⊕ 0`. -/
def extDetFiber {S : FredholmOp E F} {S' : FredholmOp (E × (Fin 1 → ℝ)) F}
    (h : S'.1 = extOp S.1) : DetFiber S ≃ₗ[ℝ] DetFiber S' :=
  (extDetN S.2).trans (linDetEquivOfEq (congrArg ContinuousLinearMap.toLinearMap h.symm))

/-- **The chart coordinate of `extDetFiber`** (`coord_extDetN` on the fibres of `DET`). -/
theorem coord_extDetFiber (c : LocalDetChart E F) (c' : LocalDetChart (E × (Fin 1 → ℝ)) F)
    (hP : c'.P = c.P) (hK : finrank ℝ c'.K = finrank ℝ c.K + 1) (t : Fin 1 → c'.K)
    {S : FredholmOp E F} {S' : FredholmOp (E × (Fin 1 → ℝ)) F} (h : S'.1 = extOp S.1)
    (hS : ‖S.1 - c.T‖ < c.ε) (hA : ‖S'.1 - c'.T‖ < c'.ε)
    (ht : (Pi.basisFun ℝ (Fin 1)).det (fun j => (c'.kerMap S'.1 (t j)).2) ≠ 0)
    (x : DetFiber S) :
    c'.coord S' (extDetFiber h x) =
      ((-1 : ℝ) ^ finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) * stabD c c' hK t S.1 0) *
        c.coord S x := by
  obtain ⟨S'₁, hS'⟩ := S'
  obtain ⟨S₁, hS₁⟩ := S
  change S'₁ = extOp S₁ at h
  subst h
  have he : extDetFiber (S := ⟨S₁, hS₁⟩) (S' := ⟨extOp S₁, hS'⟩) rfl x =
      (extDetN hS₁ x : DetFiber (⟨extOp S₁, hS'⟩ : FredholmOp (E × (Fin 1 → ℝ)) F)) := by
    exact DFunLike.congr_fun (linDetEquivOfEq_self ((extOp S₁ : E × (Fin 1 → ℝ) →L[ℝ] F) :
      E × (Fin 1 → ℝ) →ₗ[ℝ] F) rfl) (extDetN hS₁ x)
  rw [he]
  exact coord_extDetN c c' hP hK t hS₁ hS hS' hA ht x

/-- **The pulled-back rays** `L ↦ h(L)` with `h̃ = o'(L̃)`, i.e. `extDetN⁻¹ (o'(L̃))`. -/
def extPullRay (hmem : ∀ S ∈ C, extOp S ∈ C') (o' : ∀ b, Module.Ray ℝ (DetOn C' hC' b))
    (b : C) : Module.Ray ℝ (DetOn C hC b) :=
  Module.Ray.map (extDetFiber (S := fredholmIncl hC b) (S' := fredholmIncl hC' (extMap hmem b))
    rfl).symm (o' (extMap hmem b))

/-- **The pulled-back rays form an orientation**: read in charts `c` at `L₀` and `c'` at `L̃₀` with
the same projection, the coordinate of `extDetN` is `(−1)^{dim F/R(P)} D(L, 0)` times that of
`c` (`coord_extDetN`), continuous and nonzero near `L₀`. -/
theorem isLineOrientation_extPull (hmem : ∀ S ∈ C, extOp S ∈ C')
    (o' : LineOrientation (DetOn C' hC')) :
    IsLineOrientation (DetOn C hC) (extPullRay hmem o'.1) := by
  classical
  intro b₀
  have hTF : ∀ b : C, (b : E →L[ℝ] F).IsFredholm := fun b => hC _ b.2
  have hAF : ∀ b : C, (extOp (b : E →L[ℝ] F)).IsFredholm := fun b => hC' _ (hmem _ b.2)
  obtain ⟨U', hU', σ', hσ'c, hσ'⟩ := o'.2 (extMap hmem b₀)
  -- the charts at `L₀` and at `L̃₀`
  obtain ⟨P, hP⟩ := exists_isGoodLeftProj (hTF b₀)
  obtain ⟨c, hcT, hcP⟩ := exists_localDetChart_of_proj (hTF b₀) hP
  obtain ⟨c', hc'T, hc'P⟩ := exists_localDetChart_of_proj (hAF b₀)
    (hP.coprod (0 : (Fin 1 → ℝ) →L[ℝ] F))
  have hPP : c'.P = c.P := hc'P.trans hcP.symm
  have hK : finrank ℝ c'.K = finrank ℝ c.K + 1 := by
    have := (hP.isFredholm_comp (hTF b₀)).finite_ker
    have := ((hP.coprod (0 : (Fin 1 → ℝ) →L[ℝ] F)).isFredholm_comp (hAF b₀)).finite_ker
    have h := finrank_ker_comp_coprod hP (0 : (Fin 1 → ℝ) →L[ℝ] F)
    change finrank ℝ (LinearMap.ker ((c'.P ∘L c'.T : E × (Fin 1 → ℝ) →L[ℝ] F) :
      E × (Fin 1 → ℝ) →ₗ[ℝ] F)) =
      finrank ℝ (LinearMap.ker ((c.P ∘L c.T : E →L[ℝ] F) : E →ₗ[ℝ] F)) + 1
    rw [hc'T, hc'P, hcT, hcP]
    exact h
  have hb₀c : ‖(b₀ : E →L[ℝ] F) - c.T‖ < c.ε := by
    rw [hcT, sub_self, norm_zero]
    exact c.ε_pos
  have hb₀c' : ‖extOp (b₀ : E →L[ℝ] F) - c'.T‖ < c'.ε := by
    rw [hc'T, sub_self, norm_zero]
    exact c'.ε_pos
  -- the vector `t` with `det(kerMap(t)₂) = 1` at `L₀`
  obtain ⟨L, hL⟩ := LinearMap.exists_rightInverse_of_surjective
    (stabKerSnd c'.P (b₀ : E →L[ℝ] F) 0) (LinearMap.range_eq_top.2
      (stabKerSnd_surjective (hPP ▸ c.isGoodLeftProj_of_lt _ hb₀c) 0))
  let t : Fin 1 → c'.K := fun j => c'.kerProj (L (Pi.basisFun ℝ (Fin 1) j) : E × (Fin 1 → ℝ))
  have ht₀ : (Pi.basisFun ℝ (Fin 1)).det
      (fun j => (c'.kerMap (extOp (b₀ : E →L[ℝ] F)) (t j)).2) ≠ 0 := by
    have h : (fun j => (c'.kerMap (extOp (b₀ : E →L[ℝ] F)) (t j)).2) =
        Pi.basisFun ℝ (Fin 1) := by
      funext j
      rw [show (c'.kerMap (extOp (b₀ : E →L[ℝ] F)) (t j) : E × (Fin 1 → ℝ)) =
        (L (Pi.basisFun ℝ (Fin 1) j) : E × (Fin 1 → ℝ)) from
          (c'.lemma_6_5_2).2.2.1 _ hb₀c' _ (L _).2]
      exact LinearMap.congr_fun hL _
    rw [h, Basis.det_self]
    exact one_ne_zero
  -- the neighbourhood
  have hAc : Continuous fun b : C => extOp (b : E →L[ℝ] F) :=
    continuous_extOp.comp continuous_subtype_val
  let U : Set C := {b | extMap hmem b ∈ U' ∧ ‖(b : E →L[ℝ] F) - c.T‖ < c.ε ∧
    ‖extOp (b : E →L[ℝ] F) - c'.T‖ < c'.ε ∧
    (Pi.basisFun ℝ (Fin 1)).det (fun j => (c'.kerMap (extOp (b : E →L[ℝ] F)) (t j)).2) ≠ 0}
  have hU : U ∈ 𝓝 b₀ := by
    have h1 : ∀ᶠ b in 𝓝 b₀, extMap hmem b ∈ U' :=
      (continuous_extMap hmem).continuousAt.preimage_mem_nhds hU'
    have h2 : ∀ᶠ b : C in 𝓝 b₀, ‖(b : E →L[ℝ] F) - c.T‖ < c.ε :=
      (isOpen_lt ((continuous_subtype_val.sub continuous_const).norm) continuous_const).mem_nhds
        hb₀c
    have h3 : ∀ᶠ b : C in 𝓝 b₀, ‖extOp (b : E →L[ℝ] F) - c'.T‖ < c'.ε :=
      (isOpen_lt ((hAc.sub continuous_const).norm) continuous_const).mem_nhds hb₀c'
    have h4 := ((continuousOn_stabD_den c' t hAc).continuousAt h3).eventually_ne ht₀
    filter_upwards [h1, h2, h3, h4] with b a1 a2 a3 a4 using ⟨a1, a2, a3, a4⟩
  -- the section and its chart coordinate
  let σ : ∀ b : C, DetOn C hC b := fun b =>
    (extDetFiber (S := fredholmIncl hC b) (S' := fredholmIncl hC' (extMap hmem b)) rfl).symm
      (σ' (extMap hmem b))
  let κ : C → ℝ := fun b => (-1 : ℝ) ^ finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) *
    stabD c c' hK t (b : E →L[ℝ] F) 0
  have hκ0 : ∀ b ∈ U, κ b ≠ 0 := fun b hb =>
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (stabD_ne_zero c c' hPP hK t hb.2.1 hb.2.2.1 hb.2.2.2)
  have hκc : ContinuousOn κ U := by
    refine continuousOn_const.mul ?_
    exact (continuousOn_stabD c c' hK t (T := fun b : C => (b : E →L[ℝ] F))
      continuous_subtype_val (φ := fun _ => (0 : (Fin 1 → ℝ) →L[ℝ] F)) continuous_const).mono
        fun b hb => ⟨hb.2.1, hb.2.2.1, hb.2.2.2⟩
  have hc'c : ContinuousOn (fun b : C => c'.coord (fredholmIncl hC' (extMap hmem b))
      (σ' (extMap hmem b))) U :=
    (continuousOn_coord_of_section hσ'c c').comp (continuous_extMap hmem).continuousOn
      fun b hb => ⟨hb.1, hb.2.2.1⟩
  have hcoord : ∀ b ∈ U, c.coord (fredholmIncl hC b) (σ b) =
      (κ b)⁻¹ * c'.coord (fredholmIncl hC' (extMap hmem b)) (σ' (extMap hmem b)) := by
    intro b hb
    have h2 := coord_extDetFiber c c' hPP hK t (S := fredholmIncl hC b)
      (S' := fredholmIncl hC' (extMap hmem b)) rfl hb.2.1 hb.2.2.1 hb.2.2.2 (σ b)
    have hσ : extDetFiber (S := fredholmIncl hC b) (S' := fredholmIncl hC' (extMap hmem b)) rfl
        (σ b) = σ' (extMap hmem b) := LinearEquiv.apply_symm_apply _ _
    rw [hσ] at h2
    rw [h2]
    exact (inv_mul_cancel_left₀ (hκ0 b hb) _).symm
  refine ⟨U, hU, σ, ?_, fun b hb => ?_⟩
  · obtain ⟨e, -, he, hee⟩ := (proposition_6_5_8 (E := E) (F := F)).2 c
    have hsrc : U ⊆ (fun b : C => (⟨fredholmIncl hC b, σ b⟩ :
        TotalSpace ℝ (DetFiber (E := E) (F := F)))) ⁻¹' e.source :=
      fun b hb => e.mem_source.2 (by rw [he]; exact hb.2.1)
    have key : ContinuousOn (fun b : C => (⟨fredholmIncl hC b, σ b⟩ :
        TotalSpace ℝ (DetFiber (E := E) (F := F)))) U := by
      refine (e.toOpenPartialHomeomorph.continuousOn_iff_continuousOn_comp_left hsrc).2 ?_
      have heφ : (e.toOpenPartialHomeomorph ∘ fun b : C => (⟨fredholmIncl hC b, σ b⟩ :
          TotalSpace ℝ (DetFiber (E := E) (F := F)))) = fun b =>
            (fredholmIncl hC b, c.coord (fredholmIncl hC b) (σ b)) :=
        funext fun b => hee _
      rw [heφ]
      exact (fredholmIncl hC).continuous.continuousOn.prodMk
        (((hκc.inv₀ hκ0).mul hc'c).congr hcoord)
    exact (inducing_pullbackTotalSpaceEmbedding ℝ _ _).continuousOn_iff.2
      (continuousOn_id.prodMk key)
  · obtain ⟨hne, hray⟩ := hσ' _ hb.1
    refine ⟨(LinearEquiv.map_ne_zero_iff _).2 hne, ?_⟩
    change Module.Ray.map _ (o'.1 _) = _
    rw [hray]
    rfl

/-- **The pulled-back orientation** of `DET` over `C`: `L ↦ extDetN⁻¹ (o'(L̃))`. -/
def LineOrientation.extPull (hmem : ∀ S ∈ C, extOp S ∈ C')
    (o' : LineOrientation (DetOn C' hC')) : LineOrientation (DetOn C hC) :=
  ⟨extPullRay hmem o'.1, isLineOrientation_extPull hmem o'⟩

/-- `o'.extPull` at `L` is `extDetN⁻¹ (o'(L̃))`. -/
theorem LineOrientation.extPull_apply (hmem : ∀ S ∈ C, extOp S ∈ C')
    (o' : LineOrientation (DetOn C' hC')) {S : E →L[ℝ] F} (hS : S ∈ C) :
    o'.extPull (hC := hC) hmem ⟨S, hS⟩ =
      Module.Ray.map (extDetFiber (S := ⟨S, hC S hS⟩)
        (S' := ⟨extOp S, hC' _ (hmem S hS)⟩) rfl).symm (o' ⟨extOp S, hmem S hS⟩) :=
  rfl

end ExtPull

section ConjFredholm

variable {E F E' F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']

omit [CompleteSpace E] [CompleteSpace F] in
/-- **A conjugate of a Fredholm operator is Fredholm**: if `Γ⁻¹ S' A` is Fredholm for
isomorphisms `A`, `Γ`, so is `S'` (`ker S' = A(ker Γ⁻¹ S' A)`, `R(S') = Γ R(Γ⁻¹ S' A)`). -/
theorem isFredholm_of_conj (A : E ≃L[ℝ] E') (Γ : F ≃L[ℝ] F') {S' : E' →L[ℝ] F'}
    (h : ((Γ.symm : F' →L[ℝ] F) ∘L S' ∘L (A : E →L[ℝ] E')).IsFredholm) : S'.IsFredholm := by
  set M := (Γ.symm : F' →L[ℝ] F) ∘L S' ∘L (A : E →L[ℝ] E') with hM
  have hS' : ∀ v, S' v = Γ (M (A.symm v)) := fun v => by simp [hM]
  have := h.finite_ker
  have hcok : Module.Finite ℝ (F ⧸ LinearMap.range (M : E →ₗ[ℝ] F)) := h.finite_coker
  have hrange : LinearMap.range (S' : E' →ₗ[ℝ] F') =
      (LinearMap.range (M : E →ₗ[ℝ] F)).map (Γ.toLinearEquiv : F →ₗ[ℝ] F') := by
    ext y
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨M (A.symm v), ⟨A.symm v, rfl⟩, (hS' v).symm⟩
    · rintro ⟨w, ⟨u, rfl⟩, rfl⟩
      exact ⟨A u, by simp [hM]⟩
  have hker : FiniteDimensional ℝ (LinearMap.ker (S' : E' →ₗ[ℝ] F')) := by
    let g : LinearMap.ker (S' : E' →ₗ[ℝ] F') →ₗ[ℝ] LinearMap.ker (M : E →ₗ[ℝ] F) :=
      (A.symm.toLinearEquiv.toLinearMap).restrict fun v hv => by
        change M (A.symm v) = 0
        have hv' : S' v = 0 := hv
        simp [hM, hv']
    refine Module.Finite.of_injective g fun v w hvw => Subtype.ext ?_
    exact A.symm.injective (congrArg Subtype.val hvw)
  refine isFredholm_of_banach _ hker ?_ ?_
  · rw [hrange, Submodule.map_coe]
    exact Γ.toHomeomorph.isClosedMap _ h.isClosed_range
  · change Module.Finite ℝ (F' ⧸ LinearMap.range (S' : E' →ₗ[ℝ] F'))
    rw [hrange]
    exact Module.Finite.equiv (Submodule.Quotient.equiv _ _ Γ.toLinearEquiv rfl)

end ConjFredholm

section ExtConj

variable {E F E' F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
  (A : E' ≃L[ℝ] E × (Fin 1 → ℝ)) (Γ : F' ≃L[ℝ] F)

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] in
/-- `extDetFiber` along `S' = S ⊕ 0` is `extDetN`. -/
theorem extDetFiber_rfl_apply {T : E →L[ℝ] F} (hS : T.IsFredholm)
    (hS' : (extOp T).IsFredholm) (y : fredholmDet T) :
    extDetFiber (S := ⟨T, hS⟩) (S' := ⟨extOp T, hS'⟩) rfl y = extDetN hS y :=
  DFunLike.congr_fun (linDetEquivOfEq_self
    ((extOp T : E × (Fin 1 → ℝ) →L[ℝ] F) : E × (Fin 1 → ℝ) →ₗ[ℝ] F) rfl) (extDetN hS y)

/-- **`L̂ = Γ⁻¹ (L ⊕ 0) A`**: the operator `L̃(a, b) = La` of Remark 6.6.19 (preprint 6.42) transported along
isomorphisms `A : E' ≅ E × ℝ¹` and `Γ : F' ≅ F`. -/
def extConjOp (L : E →L[ℝ] F) : E' →L[ℝ] F' :=
  (Γ.symm : F →L[ℝ] F') ∘L extOp L ∘L (A : E' →L[ℝ] E × (Fin 1 → ℝ))

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] in
/-- `(L ⊕ 0) ∘ A = Γ ∘ L̂`. -/
theorem extConjOp_conj (L : E →L[ℝ] F) (v : E') :
    extOp L (A v) = Γ (extConjOp A Γ L v) :=
  (Γ.apply_symm_apply _).symm

/-- **The determinant isomorphism `h ↦ h̃`**, `det(L) ≅ det(L̂)`: `extDetN` followed by the
conjugation `det(L ⊕ 0) ≅ det(L̂)` (`conjDet`). -/
def extConjDet {L : E →L[ℝ] F} (hL : L.IsFredholm) (hL' : (extConjOp A Γ L).IsFredholm) :
    DetFiber (⟨L, hL⟩ : FredholmOp E F) ≃ₗ[ℝ]
      DetFiber (⟨extConjOp A Γ L, hL'⟩ : FredholmOp E' F') :=
  (extDetFiber (S := ⟨L, hL⟩) (S' := ⟨extOp L, isFredholm_extOp hL⟩) rfl).trans
    (conjDetFiber (S := ⟨extConjOp A Γ L, hL'⟩) (S' := ⟨extOp L, isFredholm_extOp hL⟩) A Γ
      (extConjOp_conj A Γ L)).symm

omit [CompleteSpace E'] [CompleteSpace F'] in
/-- `extConjDet = conjDet⁻¹ ∘ extDetN`. -/
theorem extConjDet_apply {L : E →L[ℝ] F} (hL : L.IsFredholm)
    (hL' : (extConjOp A Γ L).IsFredholm) (y : fredholmDet L) :
    extConjDet A Γ hL hL' y = (conjDet A Γ (extConjOp_conj A Γ L)).symm (extDetN hL y) :=
  congrArg (conjDetFiber (S := ⟨extConjOp A Γ L, hL'⟩) (S' := ⟨extOp L, isFredholm_extOp hL⟩) A Γ
    (extConjOp_conj A Γ L)).symm (extDetFiber_rfl_apply hL _ y)

omit [CompleteSpace E'] [CompleteSpace F'] in
/-- **`extConjDet` on generators** (the text's `h ↦ h̃`): for
`h = (a₁ ∧ … ∧ aₙ) ⊗ (d₁ ∧ … ∧ d_l)*`, the image is `(−1)^{dim coker L}` times the conjugate of
`((a₁, 0) ∧ … ∧ (aₙ, 0) ∧ e) ⊗ (d₁ ∧ … ∧ d_l)*`, `e = (0, 1)`. -/
theorem extConjDet_wedge_tmul {L : E →L[ℝ] F} (hL : L.IsFredholm)
    (hL' : (extConjOp A Γ L).IsFredholm) {n l : ℕ}
    (a : Fin n → LinearMap.ker (L : E →ₗ[ℝ] F))
    (hn : n = finrank ℝ (LinearMap.ker (L : E →ₗ[ℝ] F)))
    {d : Fin l → F ⧸ LinearMap.range (L : E →ₗ[ℝ] F)} (hd : LinearIndependent ℝ d)
    (hl : l = finrank ℝ (F ⧸ LinearMap.range (L : E →ₗ[ℝ] F))) :
    extConjDet A Γ hL hL' (wedge a hn ⊗ₜ dualVec (wedge d hl)) =
      ((stabSign L : ℝˣ) : ℝ) • (conjDet A Γ (extConjOp_conj A Γ L)).symm
        (wedge (Fin.append (stabJ L 0 ∘ a) ![extE L]) (by rw [hn]; exact finrank_ker_extOp hL) ⊗ₜ
          dualVec (wedge ((extCoker L).symm ∘ d) (hl.trans (extCoker L).symm.finrank_eq))) := by
  rw [extConjDet_apply]
  refine (congrArg (conjDet A Γ (extConjOp_conj A Γ L)).symm ((extDetN_apply hL _).trans
    (congrArg _ (extDet_wedge_tmul hL a hn hd hl)))).trans ?_
  exact LinearEquiv.map_smul _ _ _

/-- `(e₁ ≫ e₂⁻¹)(e₁⁻¹(e₂ r)) = r` on rays. -/
theorem rayMap_trans_symm_cancel {M N Q : Type*} [AddCommMonoid M] [Module ℝ M]
    [AddCommMonoid N] [Module ℝ N] [AddCommMonoid Q] [Module ℝ Q] (e₁ : M ≃ₗ[ℝ] N)
    (e₂ : Q ≃ₗ[ℝ] N) (r : Module.Ray ℝ Q) :
    Module.Ray.map (e₁.trans e₂.symm) (Module.Ray.map e₁.symm (Module.Ray.map e₂ r)) = r :=
  Module.Ray.ind ℝ (C := fun r => Module.Ray.map (e₁.trans e₂.symm)
    (Module.Ray.map e₁.symm (Module.Ray.map e₂ r)) = r) (fun v hv => by
      simp only [Module.Ray.map_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
        LinearEquiv.symm_apply_apply]) r

/-- **One orientation for all `L̂`** (the abstract form of Remark 6.6.19 (preprint 6.42)): for a preconnected `C`
and a simply connected, locally path-connected `Ĉ` with `L̂ ∈ Ĉ` for `L ∈ C`, an orientation `o`
of `DET` over a nonempty `C` gives exactly one orientation `ô` over `Ĉ` with
`ô(L̂) = extConjDet(o(L))` for every `L ∈ C` (`LineOrientation.conj`, `LineOrientation.extPull`). -/
theorem existsUnique_extConjOr {C : Set (E →L[ℝ] F)} (hC : ∀ T ∈ C, T.IsFredholm)
    {Ĉ : Set (E' →L[ℝ] F')} (hĈ : ∀ T ∈ Ĉ, T.IsFredholm)
    (hmem : ∀ L ∈ C, extConjOp A Γ L ∈ Ĉ) [PreconnectedSpace C] [SimplyConnectedSpace Ĉ]
    [LocallyPathConnectedSpace Ĉ] (hne : C.Nonempty) (o : LineOrientation (DetOn C hC)) :
    ∃! ô : LineOrientation (DetOn Ĉ hĈ), ∀ (L : E →L[ℝ] F) (hL : L ∈ C),
      ô ⟨extConjOp A Γ L, hmem L hL⟩ =
        Module.Ray.map (extConjDet A Γ (hC L hL) (hĈ _ (hmem L hL))) (o ⟨L, hL⟩) := by
  set C' : Set (E × (Fin 1 → ℝ) →L[ℝ] F) :=
    {S' | (Γ.symm : F →L[ℝ] F') ∘L S' ∘L (A : E' →L[ℝ] E × (Fin 1 → ℝ)) ∈ Ĉ} with hC'def
  have hC' : ∀ S' ∈ C', S'.IsFredholm := fun S' hS' => isFredholm_of_conj A Γ (hĈ _ hS')
  have hmem' : ∀ S' ∈ C', (Γ.symm : F →L[ℝ] F') ∘L S' ∘L (A : E' →L[ℝ] E × (Fin 1 → ℝ)) ∈ Ĉ :=
    fun _ h => h
  have hext : ∀ L ∈ C, extOp L ∈ C' := hmem
  let Φ : LineOrientation (DetOn Ĉ hĈ) → LineOrientation (DetOn C hC) := fun ô =>
    (ô.conj (hC' := hC') A Γ hmem').extPull hext
  have key : ∀ (ô : LineOrientation (DetOn Ĉ hĈ)) (L : E →L[ℝ] F) (hL : L ∈ C),
      ô ⟨extConjOp A Γ L, hmem L hL⟩ =
        Module.Ray.map (extConjDet A Γ (hC L hL) (hĈ _ (hmem L hL))) (Φ ô ⟨L, hL⟩) := by
    intro ô L hL
    have h2 := ô.conj_apply_of_conj (hC' := hC') A Γ hmem' ⟨extConjOp A Γ L, hmem L hL⟩
      ⟨extOp L, hext L hL⟩ (extConjOp_conj A Γ L)
    set e₁ := extDetFiber (S := ⟨L, hC L hL⟩) (S' := ⟨extOp L, isFredholm_extOp (hC L hL)⟩) rfl
    set e₂ := conjDetFiber (S := ⟨extConjOp A Γ L, hĈ _ (hmem L hL)⟩)
      (S' := ⟨extOp L, isFredholm_extOp (hC L hL)⟩) A Γ (extConjOp_conj A Γ L)
    have h1 : Φ ô ⟨L, hL⟩ = Module.Ray.map e₁.symm (Module.Ray.map e₂
        (ô ⟨extConjOp A Γ L, hmem L hL⟩)) := h2 ▸ rfl
    rw [h1]
    exact (rayMap_trans_symm_cancel e₁ e₂ _).symm
  obtain ⟨L₀, hL₀⟩ := hne
  obtain ⟨ô, hô⟩ := exists_lineOrientation_apply_eq (L := DetOn Ĉ hĈ)
    ⟨extConjOp A Γ L₀, hmem L₀ hL₀⟩
    (Module.Ray.map (extConjDet A Γ (hC L₀ hL₀) (hĈ _ (hmem L₀ hL₀))) (o ⟨L₀, hL₀⟩))
  have hΦ : Φ ô = o := LineOrientation.eq_of_apply_eq ⟨L₀, hL₀⟩
    ((Module.Ray.map _).injective ((key ô L₀ hL₀).symm.trans hô))
  refine ⟨ô, fun L hL => (key ô L hL).trans (by rw [hΦ]), fun ô' hô' => ?_⟩
  exact LineOrientation.eq_of_apply_eq ⟨_, hmem L₀ hL₀⟩ ((hô' L₀ hL₀).trans hô.symm)

end ExtConj

open StrongRetr

section ProdPoint

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]

namespace ChartPoint

variable {x : X} (p : ChartPoint B x)

/-- **The product chart point** at `(t, x) ∈ ℝ¹ × X`: the product chart `(r ↦ r) × φ` of
`ℝ¹ × X` over the chart `c` of `p` (`PullbackChartData.ofProd`), with the level-`1` point
`(t, z)`. -/
def prodPt (t : Fin 1 → ℝ) (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)) :
    ChartPoint (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)) (t, x) where
  c := (PullbackChartData.ofProd p.c 0).toChart q₀
  isChart := (PullbackChartData.ofProd p.c 0).isChart_toChart B _ p.isChart q₀
  mem_source := ⟨mem_univ _, p.mem_source⟩
  z := (t, p.z)
  toBase_z := by
    change ((rnSc 1).prod p.c.φ.model.E).toBase 1 (t, p.z) =
      ((t - 0, p.c.φ x) : (Fin 1 → ℝ) × p.c.φ.model.E 0)
    rw [ScBanach.prod_toBase, ScBanach.const_toBase, sub_zero, p.toBase_z]

variable (t : Fin 1 → ℝ) (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))

/-- **`T_{(t, x)}(ℝ¹ × X) = ℝ¹ × T_xX`** in the product chart. -/
theorem mem_prodPt_T_iff (w : (Fin 1 → ℝ) × p.c.φ.model.E 0) :
    w ∈ (p.prodPt t q₀).T ↔ w.2 ∈ p.T :=
  PullbackChartData.ofProd_mem_tangent_iff p.c 0 q₀ t p.mem_U w

/-- **`Ŷ_{(t, x)} = Y_x`** in the product chart. -/
theorem mem_prodPt_K_iff (k : p.c.F 0) : k ∈ (p.prodPt t q₀).K ↔ k ∈ p.K := by
  have h1 := mem_rangeS_ρCLM_iff (p.prodPt t q₀).c.isRetraction (p.prodPt t q₀).mem_O
    (p.prodPt t q₀).mem_U (k := k)
  have h2 := mem_rangeS_ρCLM_iff p.c.isRetraction p.mem_O p.mem_U (k := k)
  refine h1.trans (Iff.trans ?_ h2.symm)
  have hw : ((p.prodPt t q₀).c.φ.model.E.toBase 1 (p.prodPt t q₀).z) =
      ((t, p.c.φ.model.E.toBase 1 p.z) : (Fin 1 → ℝ) × p.c.φ.model.E 0) := by
    change ((rnSc 1).prod p.c.φ.model.E).toBase 1 (t, p.z) = _
    rw [ScBanach.prod_toBase, ScBanach.const_toBase]
  rw [hw]
  exact PullbackChartData.mem_K_ofProd_iff p.c 0 q₀ (w := (t, p.c.φ.model.E.toBase 1 p.z))
    (p.c.r_image ▸ p.mem_O) k

/-- **`A : T_{(t, z)} → T_zO × ℝ¹`**, `(σ, v) ↦ (v, σ)`: the product chart's tangent space with
the `ℝ¹`-factor moved to the second place (the text's `L̃(a, b) = La` has `b ∈ ℝ` second). -/
def prodT : ↥(p.prodPt t q₀).T ≃L[ℝ] ↥p.T × (Fin 1 → ℝ) :=
  ContinuousLinearEquiv.equivOfInverse
    ((((ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) (p.c.φ.model.E 0)).comp
      (p.prodPt t q₀).T.subtypeL).codRestrict p.T fun w =>
        (p.mem_prodPt_T_iff t q₀ w.1).1 w.2).prod
      ((ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) (p.c.φ.model.E 0)).comp
        (p.prodPt t q₀).T.subtypeL))
    ((((ContinuousLinearMap.inr ℝ (Fin 1 → ℝ) (p.c.φ.model.E 0)).comp
      (p.T.subtypeL.comp (ContinuousLinearMap.fst ℝ ↥p.T (Fin 1 → ℝ)))) +
      ((ContinuousLinearMap.inl ℝ (Fin 1 → ℝ) (p.c.φ.model.E 0)).comp
        (ContinuousLinearMap.snd ℝ ↥p.T (Fin 1 → ℝ)))).codRestrict (p.prodPt t q₀).T fun w =>
          (p.mem_prodPt_T_iff t q₀ _).2 (by simp))
    (fun w => Subtype.ext (Prod.ext (zero_add _) (add_zero _)))
    (fun y => Prod.ext (Subtype.ext (add_zero _)) (zero_add _))

/-- `A(σ, v) = (v, σ)`: the first component. -/
@[simp] theorem coe_prodT_fst (w : ↥(p.prodPt t q₀).T) :
    ((p.prodT t q₀ w).1 : p.c.φ.model.E 0) = (w.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).2 := rfl

/-- `A(σ, v) = (v, σ)`: the second component. -/
@[simp] theorem prodT_snd (w : ↥(p.prodPt t q₀).T) :
    (p.prodT t q₀ w).2 = (w.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 := rfl

/-- **`Γ : Ŷ_{(t, x)} → Y_x`**: the identity of `K_z`, the fibre of the product chart at
`(t, z)` being that of `c` at `z`. -/
def prodK : ↥(p.prodPt t q₀).K ≃L[ℝ] ↥p.K :=
  ContinuousLinearEquiv.equivOfInverse
    ((p.prodPt t q₀).K.subtypeL.codRestrict p.K fun k => (p.mem_prodPt_K_iff t q₀ k.1).1 k.2)
    (p.K.subtypeL.codRestrict (p.prodPt t q₀).K fun k => (p.mem_prodPt_K_iff t q₀ k.1).2 k.2)
    (fun _ => rfl) (fun _ => rfl)

/-- `Γ` is the identity of `K_z`. -/
@[simp] theorem coe_prodK (k : ↥(p.prodPt t q₀).K) :
    ((p.prodK t q₀ k : ↥p.K) : p.c.F 0) = (k.1 : p.c.F 0) := rfl

/-- `Γ⁻¹` is the identity of `K_z`. -/
@[simp] theorem coe_prodK_symm (k : ↥p.K) :
    (((p.prodK t q₀).symm k : ↥(p.prodPt t q₀).K).1 : p.c.F 0) = (k : p.c.F 0) := rfl

/-- **The text's `L̃(a, b) = La` read in the product chart**: `L̂ = Γ⁻¹ (L ⊕ 0) A`, i.e.
`(σ, v) ↦ Lv` (`extConjOp` along `prodT` and `prodK`). -/
abbrev prodLin (L : ↥p.T →L[ℝ] ↥p.K) : ↥(p.prodPt t q₀).T →L[ℝ] ↥(p.prodPt t q₀).K :=
  extConjOp (p.prodT t q₀) (p.prodK t q₀) L

/-- `L̂(σ, v) = Lv`. -/
theorem coe_prodLin_apply (L : ↥p.T →L[ℝ] ↥p.K) (w : ↥(p.prodPt t q₀).T) :
    ((p.prodLin t q₀ L w : ↥(p.prodPt t q₀).K).1 : p.c.F 0) = (L (p.prodT t q₀ w).1 : p.c.F 0) := by
  change (((p.prodK t q₀).symm (extOp L (p.prodT t q₀ w)) : ↥(p.prodPt t q₀).K).1 : p.c.F 0) = _
  rw [extOp_apply]
  rfl

/-- `L̃ ∘ A = Γ ∘ L̂`: the conjugation identity behind `conjDet`. -/
theorem prodLin_conj (L : ↥p.T →L[ℝ] ↥p.K) (w : ↥(p.prodPt t q₀).T) :
    extOp L (p.prodT t q₀ w) = p.prodK t q₀ (p.prodLin t q₀ L w) :=
  extConjOp_conj _ _ L w

/-- **The sc⁺-operators lift**: for an sc⁺-operator `a : T_zO → K_z`, `(σ, v) ↦ a(v)` is an
sc⁺-operator `T_{(t, z)} → K_z` at a smooth point (`(σ, v) ↦ v` and the identity of `F` are
sc-operators). -/
theorem IsScPlusOp.prodPt (hx : x ∈ PX.smoothSet) {a : ↥p.T →L[ℝ] ↥p.K} (ha : p.IsScPlusOp a) :
    (p.prodPt t q₀).IsScPlusOp (((p.prodK t q₀).symm : ↥p.K →L[ℝ] ↥(p.prodPt t q₀).K) ∘L a ∘L
      ((ContinuousLinearMap.fst ℝ ↥p.T (Fin 1 → ℝ)) ∘L
        (p.prodT t q₀ : ↥(p.prodPt t q₀).T →L[ℝ] ↥p.T × (Fin 1 → ℝ)))) := by
  obtain ⟨hT, hK, S, hS⟩ := ha
  have hx' : (t, x) ∈ ((rnPolyfold 1).prod PX).smoothSet := prod_rn_mem_smoothSet_iff.2 hx
  have hT' := (p.prodPt t q₀).isScSubspace_T hx'
  have hK' := (p.prodPt t q₀).isScSubspace_K hx'
  let aop : ScOperator ((p.prodPt t q₀).c.φ.model.E.ofSubspace hT')
      (p.c.φ.model.E.ofSubspace hT) :=
    (ScBanach.prodSndOp (rnSc 1) p.c.φ.model.E).restrict hT' hT
      (fun v hv => (p.mem_prodPt_T_iff t q₀ v).1 hv)
  let γop : ScOperator (p.c.F.ofSubspace hK) ((p.prodPt t q₀).c.F.ofSubspace hK') :=
    (ScOperator.id p.c.F).restrict hK hK' (fun k hk => (p.mem_prodPt_K_iff t q₀ k).2 hk)
  refine ⟨hT', hK', γop.shift.comp (S.comp aop), fun v => ?_⟩
  exact hS (aop 0 v)

end ChartPoint

end ProdPoint

/-! ### Sections over `ℝ¹ × X` -/

section ProdSections

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] in
/-- A section of `π*P` is determined by its slices. -/
theorem eq_of_pullbackSlice_eq {S₁ S₂ : (Fin 1 → ℝ) × X → pullbackSpace P Prod.snd}
    (h₁ : IsSection (pullbackProj P Prod.snd) S₁) (h₂ : IsSection (pullbackProj P Prod.snd) S₂)
    (h : ∀ t, pullbackSlice S₁ t = pullbackSlice S₂ t) : S₁ = S₂ := by
  funext z
  exact Subtype.ext (Prod.ext ((h₁ z).trans (h₂ z).symm) (congrFun (h z.1) z.2))

/-- **The `t`-constant lift `s̃(t, x) = s(x)`** of a section `s` of `P` to `π*P` over `ℝ¹ × X`
(`paramComb` of the one section `s`, reparametrized along the constant `t ↦ 1`). -/
def constLift (s : X → Y) (hs : IsSection P s) :
    (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X) :=
  reparamSection (fun q => (0 : (Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ)) q + 1)
    (paramComb (fun _ : Fin 1 => s) fun _ => hs) (isSection_pullbackLift _)

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] in
/-- The slices of `s̃` are `s`. -/
theorem pullbackSlice_constLift (s : X → Y) (hs : IsSection P s) (t : Fin 1 → ℝ) :
    pullbackSlice (constLift s hs) t = s := by
  funext x
  change ((∑ i : Fin 1, ((0 : (Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ)) t + 1) i •
    (⟨s x, hs x⟩ : P ⁻¹' {x}) : P ⁻¹' {x}) : Y) = s x
  simp

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] in
/-- `s̃` is a section. -/
theorem isSection_constLift (s : X → Y) (hs : IsSection P s) :
    IsSection (pullbackProj P Prod.snd) (constLift s hs) :=
  isSection_pullbackLift _

/-- **`s̃` is an sc⁺-section of `π*P`** for an sc⁺-section `s` of `P`
(`isScPlusSection_paramComb`, `IsScPlusSection.reparam`). -/
theorem isScPlusSection_constLift {s : X → Y} (hs : B.IsScPlusSection s) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection
      (constLift s hs.1) :=
  (StrongBundle.isScPlusSection_paramComb (B := B) (fun _ : Fin 1 => hs)).reparam 0 1

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] in
/-- The slices of `F(t, x) = g(x) + Σ tᵢ · 0` are `g`. -/
theorem pullbackSlice_paramSection_zero (g : X → Y) (hg : IsSection P g) (t : Fin 1 → ℝ) :
    pullbackSlice (paramSection g hg (fun _ : Fin 1 => fiberZero P)
      fun _ => isSection_fiberZero) t = g := by
  funext x
  have h0 : (⟨fiberZero P x, isSection_fiberZero x⟩ : P ⁻¹' {x}) = 0 := rfl
  change (((⟨g x, hg x⟩ : P ⁻¹' {x}) + ∑ i : Fin 1, t i •
    (⟨fiberZero P x, isSection_fiberZero x⟩ : P ⁻¹' {x}) : P ⁻¹' {x}) : Y) = g x
  rw [h0]
  simp

end ProdSections

/-! ### `L̂ ∈ Lin(f̂, (t, x))` -/

section ProdLinSet

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] {f : X → Y}

namespace ChartPoint

variable {x : X} (p : ChartPoint B x) (t : Fin 1 → ℝ)
  (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))

/-- **`L̂ ∈ Lin(f̂, (t, x))`** for `L ∈ Lin(f, x)` (Remark 6.6.19 (preprint 6.42), "`L̃ ∈ Lin(f̂, (x, t))`"), at a
smooth point: for `L = (f + s)'(x) + a`, take `ŝ = s̃ − S` with the `t`-constant lift `s̃` of `s`;
then `f̂ + ŝ = f̃ + s̃` is `(t, y) ↦ (f + s)(y)`, whose linearization at `(t, z)` is
`(σ, v) ↦ (f + s)'(x) v` (`StrongBundle.scDeriv_paramSection_apply`), and `(σ, v) ↦ a(v)` is an
sc⁺-operator (`IsScPlusOp.prodPt`). -/
theorem prodLin_mem_linSet (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    {S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S)
    {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f) :
    p.prodLin t q₀ L ∈ (p.prodPt t q₀).linSet
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) := by
  obtain ⟨s₀, hs₀, hz₀, a, ha, hLa⟩ := hL
  have hfs : IsSection P f := hf.isScSmooth.1
  have h0s := StrongBundle.isScPlusSection_fiberZero (B := B)
  have hg : B.IsScSmoothSection (sectionAdd P f s₀) := hf.isScSmooth.sectionAdd hs₀
  have hŝ₀ := isScPlusSection_constLift (B := B) hs₀
  have hŝ : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection
      (sectionDiff (pullbackProj P Prod.snd) (constLift s₀ hs₀.1) S) :=
    hŝ₀.add (hS.smul_left (isScSmoothMap_real_const _))
  have hpl : IsSection (pullbackProj P Prod.snd) (paramLift (n := 1) f hfs) :=
    isSection_pullbackLift _
  have hGs : IsSection (pullbackProj P Prod.snd) (paramSection (sectionAdd P f s₀) hg.1
      (fun _ : Fin 1 => fiberZero P) fun _ => h0s.1) := by
    rw [paramSection_eq_sectionAdd]
    exact (isSection_pullbackLift _).sectionAdd (isSection_pullbackLift _)
  have hsum : sectionAdd (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hfs) S)
      (sectionDiff (pullbackProj P Prod.snd) (constLift s₀ hs₀.1) S) =
        paramSection (sectionAdd P f s₀) hg.1 (fun _ : Fin 1 => fiberZero P)
          fun _ => h0s.1 := by
    rw [sectionAdd_sectionAdd_sectionDiff hpl hS.1 hŝ₀.1]
    refine eq_of_pullbackSlice_eq (hpl.sectionAdd hŝ₀.1) hGs fun τ => ?_
    rw [pullbackSlice_sectionAdd_paramLift hfs hŝ₀.1, pullbackSlice_constLift,
      pullbackSlice_paramSection_zero]
  refine ⟨_, hŝ, ?_, _, IsScPlusOp.prodPt p t q₀ hx ha, fun v => ?_⟩
  · rw [hsum]
    refine (isZeroAt_pullback_iff_pullbackSlice hGs t x).2 ?_
    rw [pullbackSlice_paramSection_zero]
    exact hz₀
  · have hz0 : ∀ u ∈ p.c.φ.model.O, p.c.principal (fiberZero P) u = 0 := fun u hu =>
      p.c.snd_fiberZero (p.c.φ.symm_mapsTo hu)
    have hgs := hg.isSc1_principal_comp_r p.isChart
    have heq : EqOn (p.c.principal (sectionAdd P f s₀) ∘ r p.c.R)
        ((fun u => p.c.principal (sectionAdd P f s₀) u +
          ∑ i, (t + 0) i • p.c.principal (fiberZero P) u) ∘ r p.c.R) p.c.U := fun u hu => by
      simp only [Function.comp_apply, hz0 _ (p.c.r_mem_O hu), smul_zero, Finset.sum_const_zero,
        add_zero]
    have hD := scDeriv_eq_of_eqOn_relOpen p.c.relOpen (hgs.congr heq) hgs subset_rfl subset_rfl
      heq.symm (z := p.z) p.mem_U
    have h1 := StrongBundle.scDeriv_paramSection_apply hg
      (fun _ : Fin 1 => h0s) p.isChart 0 q₀ t p.mem_U v.1
    have h2 : ∑ i, v.1.1 i • p.c.principal (fiberZero P)
        (r p.c.R (p.c.φ.model.E.toBase 1 p.z)) = 0 := by
      rw [hz0 _ (p.c.r_mem_O p.mem_U)]
      simp
    rw [h2, add_zero, hD] at h1
    have hlin : linAt (p.prodPt t q₀).c.U (p.prodPt t q₀).c.R
        ((p.prodPt t q₀).c.principal (paramSection (sectionAdd P f s₀) hg.1
          (fun _ : Fin 1 => fiberZero P) fun _ => h0s.1))
        (p.prodPt t q₀).z v =
          linAt p.c.U p.c.R (p.c.principal (sectionAdd P f s₀)) p.z (p.prodT t q₀ v).1 := h1
    rw [hsum, hlin, coe_prodLin_apply, hLa]
    rfl

end ChartPoint

end ProdLinSet

/-! ### The orientation of `DET(f̂, (t, x))` -/

section ProdOr

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] {f : X → Y}

namespace ChartPoint

variable {x : X} (p : ChartPoint B x) (t : Fin 1 → ℝ)
  (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))

/-- **Remark 6.6.19 (preprint 6.42): the natural orientation of `f̂ = f̃ + S`** at `(t, x)`, read in the product
chart point `prodPt`.  For an sc-Fredholm `f`, an sc⁺-section `S` of `π*P` over `ℝ¹ × X`, a smooth
point `x` with `Lin(f, x)` nonempty and an orientation `o` of `DET(f, x)`, there is exactly one
orientation `ô` of `DET(f̂, (t, x))` with `ô(L̂) = extConjDet(o(L))` for **every**
`L ∈ Lin(f, x)` (`L̂ = prodLin L`, the text's `L̃(a, b) = La`): the orientation `h̃` of `det(L̂)`
orients `DET(f̂, (t, x))`, independently of the choice of `L`. -/
theorem existsUnique_prodOr (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    {S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S)
    (hne : (p.linSet f).Nonempty) (o : p.Or f hf) :
    ∃! ô : (p.prodPt t q₀).Or
        (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
        (theorem_3_1_18_preprint hf.param hS),
      ∀ (L : ↥p.T →L[ℝ] ↥p.K) (hL : L ∈ p.linSet f),
        ô ⟨p.prodLin t q₀ L, p.prodLin_mem_linSet t q₀ hf hx hS hL⟩ =
          Module.Ray.map (extConjDet (p.prodT t q₀) (p.prodK t q₀)
            (p.isFredholm_of_mem_linSet hf L hL)
            ((p.prodPt t q₀).isFredholm_of_mem_linSet (theorem_3_1_18_preprint hf.param hS) _
              (p.prodLin_mem_linSet t q₀ hf hx hS hL))) (o ⟨L, hL⟩) := by
  obtain ⟨L₀, hL₀⟩ := hne
  have : PreconnectedSpace (p.linSet f) :=
    isPreconnected_iff_preconnectedSpace.1 (p.convex_linSet hf).isPreconnected
  have : ContractibleSpace ((p.prodPt t q₀).linSet
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)) :=
    ((p.prodPt t q₀).convex_linSet (theorem_3_1_18_preprint hf.param hS)).contractibleSpace
      ⟨_, p.prodLin_mem_linSet t q₀ hf hx hS hL₀⟩
  have : LocallyPathConnectedSpace ((p.prodPt t q₀).linSet
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)) :=
    ((p.prodPt t q₀).convex_linSet (theorem_3_1_18_preprint hf.param hS)).locallyPathConnectedSpace
  exact existsUnique_extConjOr (p.prodT t q₀) (p.prodK t q₀) (p.isFredholm_of_mem_linSet hf)
    ((p.prodPt t q₀).isFredholm_of_mem_linSet (theorem_3_1_18_preprint hf.param hS))
    (fun L hL => p.prodLin_mem_linSet t q₀ hf hx hS hL) ⟨L₀, hL₀⟩ o

/-- **The product orientation of Remark 6.6.19 (preprint 6.42)** at `(t, x)`: the orientation `ô` of
`DET(f̂, (t, x))` determined by `o` (`existsUnique_prodOr`). -/
def prodOr (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    {S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S)
    (hne : (p.linSet f).Nonempty) (o : p.Or f hf) :
    (p.prodPt t q₀).Or (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
      (theorem_3_1_18_preprint hf.param hS) :=
  (p.existsUnique_prodOr t q₀ hf hx hS hne o).exists.choose

/-- **`prodOr` at `L̂`** is `h ↦ h̃` (`extConjDet`) of `o(L)`, for every `L ∈ Lin(f, x)`. -/
theorem prodOr_apply (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    {S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S)
    (hne : (p.linSet f).Nonempty) (o : p.Or f hf) (L : ↥p.T →L[ℝ] ↥p.K)
    (hL : L ∈ p.linSet f) :
    p.prodOr t q₀ hf hx hS hne o ⟨p.prodLin t q₀ L, p.prodLin_mem_linSet t q₀ hf hx hS hL⟩ =
      Module.Ray.map (extConjDet (p.prodT t q₀) (p.prodK t q₀)
        (p.isFredholm_of_mem_linSet hf L hL)
        ((p.prodPt t q₀).isFredholm_of_mem_linSet (theorem_3_1_18_preprint hf.param hS) _
          (p.prodLin_mem_linSet t q₀ hf hx hS hL))) (o ⟨L, hL⟩) :=
  (p.existsUnique_prodOr t q₀ hf hx hS hne o).exists.choose_spec L hL

/-- **`o ↦ ô` is injective**: different orientations of `DET(f, x)` give different product
orientations. -/
theorem prodOr_injective (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    {S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S)
    (hne : (p.linSet f).Nonempty) :
    Function.Injective (p.prodOr t q₀ hf hx hS hne) := by
  intro o₁ o₂ h
  obtain ⟨L₀, hL₀⟩ := hne
  have : PreconnectedSpace (p.linSet f) :=
    isPreconnected_iff_preconnectedSpace.1 (p.convex_linSet hf).isPreconnected
  have h3 := congrArg (fun ô => ô ⟨p.prodLin t q₀ L₀, p.prodLin_mem_linSet t q₀ hf hx hS hL₀⟩) h
  exact LineOrientation.eq_of_apply_eq ⟨L₀, hL₀⟩
    ((Module.Ray.map (extConjDet (p.prodT t q₀) (p.prodK t q₀)
      (p.isFredholm_of_mem_linSet hf L₀ hL₀)
      ((p.prodPt t q₀).isFredholm_of_mem_linSet (theorem_3_1_18_preprint hf.param hS) _
        (p.prodLin_mem_linSet t q₀ hf hx hS hL₀)))).injective
      (((p.prodOr_apply t q₀ hf hx hS ⟨L₀, hL₀⟩ o₁ L₀ hL₀).symm.trans h3).trans
        (p.prodOr_apply t q₀ hf hx hS ⟨L₀, hL₀⟩ o₂ L₀ hL₀)))

end ChartPoint

end ProdOr

end Polyfold
