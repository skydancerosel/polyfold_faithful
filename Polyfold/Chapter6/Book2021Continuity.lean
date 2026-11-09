import Polyfold.Chapter6.Book2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 6, "Orientations":
the last sentence of **Proposition 6.4.13** (p. 253, proof pp. 253–255; 2017: Proposition 6.6; no
preprint counterpart), the continuous dependence of `A_T`, `B_T` on `T`.

# Proposition 6.4.13: the continuity in `T`

## The text, paraphrased

(Proposition 6.4.13, p. 253) For `T` Fredholm and `P, Q ∈ Π_T ∩ 𝒫_H` there are isomorphisms
`A_T : ker(P T) → ker(Q T)` and `B_T : F/H → F/H` filling the diagram of the exact sequences
`E(T, P)`, `E(T, Q)`.  Last sentence: for `T'` near `T` with `P, Q ∈ Π_{T'}`, the constructions
of `A_{T'}` and `B_{T'}` depend continuously on `T'`.

*Proof* (pp. 253–255).  Take a closed `X ⊆ E` complementing both `ker(P T)` and `ker(Q T)`.  For
`e ∈ ker(P T)` let `x(e) ∈ X` solve `Q T x = Q T e` (6.15) and `A_T(e) = e − x(e)` (6.16).  For
`f ∈ (I − P) F` solve `T x + f̃ = f` with `x ∈ X`, `f̃ ∈ (I − Q) F` (6.18) and put
`B_T(f + H) = f̃ + H` (6.19).  Keeping `X` fixed, (6.15) stays uniquely solvable for `T'` near `T`,
`ker(P T') ⊕ X = ker(Q T') ⊕ X = E`, and so `A_{T'}`, `B_{T'}` depend continuously on `T'`.

## What is formalized

* `exists_isClosed_isTopCompl_isTopCompl_of_finrank_eq`: two finite-dimensional subspaces of the
  same dimension have a common **closed** (topological) complement `X` (the algebraic common
  complement `exists_isCompl_isCompl_of_finrank_eq` of `Book2021.lean`, cut down to
  `K₁ + K₂` and enlarged by a closed complement of `K₁ + K₂`).
* `solveOp Q X S = (Q S|_X)⁻¹ ∘ Q : F → X ⊆ E` (the solution `x` of `Q S x = Q g`, with
  `projRestrict` and `lemma_6_5_1` of `LocalDetBundle.lean`), `kerTransition Q X S = 1 − solveOp ∘ S`
  (`e ↦ e − x(e)`, the text's `A_S` on all of `E`) and `cokerTransition P Q X S`
  (`f ↦ f̃` for the representative `(1 − P) f`, the text's `B_S` lifted to `F`).
* `diagram_of_solveOp`: for any `S` with `P, Q ∈ Π_S`, `X ⊕ ker(P S) = E` and `X ∩ ker(Q S) = 0`,
  and any solution operator `ξ`, the maps `e ↦ e − ξ(S e)` and `f + H ↦ f̃ + H` are isomorphisms
  `ker(P S) → ker(Q S)`, `F/R(P) → F/R(Q)` filling the diagram.
* `proposition_6_4_13_continuity` (**Proposition 6.4.13**, last sentence): there are a closed
  `X` and `ε > 0` such that `S ↦ kerTransition Q X S` and `S ↦ cokerTransition P Q X S` are
  continuous on `‖S − T‖ < ε` (operator norm; also jointly with the vector, i.e. as maps of the
  kernel bundles of Remark 6.4.5), and for every such `S`: `P, Q ∈ Π_S`,
  `ker(P S) ⊕ X = ker(Q S) ⊕ X = E` topologically, the text's equations (6.15)–(6.16) and
  (6.18)–(6.19) hold, and their restrictions/quotients are isomorphisms `A_S`, `B_S` making the
  diagram of `E(S, P)`, `E(S, Q)` commute.
* `proposition_6_4_13_continuity_hyps`: the hypotheses are satisfiable (`T = 1` on `ℝ`).

## Comments

* "Depend continuously" is read as continuity in the operator norm of the extensions `A_S` (to
  `E`) and `B_S` (lifted to `F`), which determine `A_S = kerTransition|_{ker(P S)}` and
  `B_S(f + H) = cokerTransition(f) + H`; the kernel bundle `⋃ {S} × ker(P S) ⊆ L(E, F) × E` of
  Remark 6.4.5 (Lemma 6.18 of `LocalDetBundle.lean`) carries the subspace topology, so the joint
  continuity clause says that `(S, e) ↦ (S, A_S e)` is continuous on it.  The conditions (6.15),
  (6.18) together with `X ∩ ker(Q S) = 0` determine both maps uniquely.
* "`T'` near `T` so that `P, Q ∈ Π_{T'}`": `P, Q ∈ Π_S` holds automatically for `S` near `T`
  (Lemma 6.5.1 (preprint 6.17)), and is part of the conclusion.
* The algebraic part (the diagram at `T` itself) is also `proposition_6_4_13` of
  `Book2021.lean`, there with an algebraic `X`; here `X` is closed, which the continuity needs.
* `B_S` is an isomorphism by injectivity and `dim F/R(P) = dim F/R(Q)` (the text: five lemma);
  `A_S` is onto by `E = X ⊕ ker(P S)`.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

/-! ### A common closed complement -/

section ClosedCommonCompl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `X₀ ⊕ K' = E`, `K' ⊆ K` and `K ⊕ Z = E`, then `(Z + X₀ ∩ K) ⊕ K' = E`. -/
theorem isCompl_sup_inf_of_isCompl {X₀ K' K Z : Submodule ℝ E} (hK' : K' ≤ K)
    (hX₀ : IsCompl X₀ K') (hKZ : IsCompl K Z) : IsCompl (Z ⊔ X₀ ⊓ K) K' := by
  constructor
  · rw [Submodule.disjoint_def]
    intro v hv hvK'
    obtain ⟨z, hz, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    have hy' := Submodule.mem_inf.1 hy
    have hzK : z ∈ K := by
      have : z = (z + y) - y := by abel
      rw [this]
      exact K.sub_mem (hK' hvK') hy'.2
    have hz0 : z = 0 := Submodule.disjoint_def.1 hKZ.disjoint z hzK hz
    subst hz0
    rw [zero_add] at hvK' ⊢
    exact Submodule.disjoint_def.1 hX₀.disjoint y hy'.1 hvK'
  · rw [codisjoint_iff, eq_top_iff]
    intro w _
    have hw : w ∈ K ⊔ Z := by rw [hKZ.sup_eq_top]; trivial
    obtain ⟨k, hk, z, hz, rfl⟩ := Submodule.mem_sup.1 hw
    have hk' : k ∈ X₀ ⊔ K' := by rw [hX₀.sup_eq_top]; trivial
    obtain ⟨x, hx, k', hk'', rfl⟩ := Submodule.mem_sup.1 hk'
    have hxK : x ∈ K := by
      have : x = (x + k') - k' := by abel
      rw [this]
      exact K.sub_mem hk (hK' hk'')
    have : x + k' + z = (z + x) + k' := by abel
    rw [this]
    exact Submodule.add_mem_sup (Submodule.add_mem_sup hz (Submodule.mem_inf.2 ⟨hx, hxK⟩)) hk''

/-- **A common closed complement** (the text's `X` in the proof of Proposition 6.4.13): two
finite-dimensional subspaces of the same dimension of a normed space have a common closed
complement `X`, and `E = K₁ ⊕ X = K₂ ⊕ X` topologically. -/
theorem exists_isClosed_isTopCompl_isTopCompl_of_finrank_eq (K₁ K₂ : Submodule ℝ E)
    [FiniteDimensional ℝ K₁] [FiniteDimensional ℝ K₂] (heq : finrank ℝ K₁ = finrank ℝ K₂) :
    ∃ X : Submodule ℝ E, IsClosed (X : Set E) ∧ K₁.IsTopCompl X ∧ K₂.IsTopCompl X := by
  obtain ⟨X₀, h₁, h₂⟩ := exists_isCompl_isCompl_of_finrank_eq K₁ K₂ heq
  obtain ⟨Z, hZc, hKZ⟩ :=
    (Submodule.ClosedComplemented.of_finiteDimensional (K₁ ⊔ K₂)).exists_isClosed_isCompl
  have hXc : IsClosed ((Z ⊔ X₀ ⊓ (K₁ ⊔ K₂) : Submodule ℝ E) : Set E) :=
    Submodule.isClosed_sup_finiteDimensional _ _ hZc
  refine ⟨_, hXc, ?_, ?_⟩
  · exact (Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional
      (isCompl_sup_inf_of_isCompl le_sup_left h₁ hKZ) hXc).symm
  · exact (Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional
      (isCompl_sup_inf_of_isCompl le_sup_right h₂ hKZ) hXc).symm

end ClosedCommonCompl

/-! ### The diagram for a given solution operator -/

section Diagram

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **The construction of Proposition 6.4.13 for one operator `S`.**  Let `P, Q ∈ Π_S` with
`R(P) = R(Q)`, `E = X ⊕ ker(P S)`, `X ∩ ker(Q S) = 0`, and let `ξ : F → X` solve
`Q S (ξ g) = Q g`.  Then `A(e) = e − ξ(S e)` ((6.15)–(6.16)) and
`B(f + R(P)) = f̃ + R(Q)`, `f̃ = (1 − P) f − S ξ((1 − P) f)` ((6.18)–(6.19)), are isomorphisms
`ker(P S) → ker(Q S)` and `F/R(P) → F/R(Q)` with `A ∘ j_P = j_Q`, `Φ_Q ∘ A = B ∘ Φ_P` and
`π_Q ∘ B = π_P`. -/
theorem diagram_of_solveOp {S : E →L[ℝ] F} {P Q : F →L[ℝ] F} (hPS : IsGoodLeftProj S P)
    (hQS : IsGoodLeftProj S Q)
    (hrange : LinearMap.range (P : F →ₗ[ℝ] F) = LinearMap.range (Q : F →ₗ[ℝ] F))
    {X : Submodule ℝ E} (hXP : IsCompl X (LinearMap.ker ((P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)))
    (hXQ : Disjoint X (LinearMap.ker ((Q ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)))
    (ξ : F →L[ℝ] E) (hξX : ∀ g, ξ g ∈ X) (hξ : ∀ g, Q (S (ξ g)) = Q g) :
    ∃ (A : LinearMap.ker ((P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F) ≃ₗ[ℝ]
        LinearMap.ker ((Q ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F))
      (B : (F ⧸ LinearMap.range (P : F →ₗ[ℝ] F)) ≃ₗ[ℝ] (F ⧸ LinearMap.range (Q : F →ₗ[ℝ] F))),
      (∀ e, (A e : E) = e - ξ (S e)) ∧
      (∀ f, B (Submodule.Quotient.mk f) =
        Submodule.Quotient.mk ((f - P f) - S (ξ (f - P f)))) ∧
      (A : _ →ₗ[ℝ] _) ∘ₗ projSeqJ S P = projSeqJ S Q ∧
      projSeqPhi S Q ∘ₗ (A : _ →ₗ[ℝ] _) = (B : _ →ₗ[ℝ] _) ∘ₗ projSeqPhi S P ∧
      projSeqPi (T := S) hQS.isProj ∘ₗ (B : _ →ₗ[ℝ] _) = projSeqPi (T := S) hPS.isProj := by
  set K₁ := LinearMap.ker ((P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F) with hK₁
  set K₂ := LinearMap.ker ((Q ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F) with hK₂
  have := hPS.finite_coker
  have := hQS.finite_coker
  have hPP : ∀ y, P (P y) = P y := fun y => by
    simpa using congrArg (fun A : F →L[ℝ] F => A y) hPS.isProj
  have hQQ : ∀ y, Q (Q y) = Q y := fun y => by
    simpa using congrArg (fun A : F →L[ℝ] F => A y) hQS.isProj
  have hcoker : finrank ℝ (F ⧸ LinearMap.range (P : F →ₗ[ℝ] F)) =
      finrank ℝ (F ⧸ LinearMap.range (Q : F →ₗ[ℝ] F)) :=
    (Submodule.quotEquivOfEq _ _ hrange).finrank_eq
  have hK₂mem : ∀ e : E, e ∈ K₂ ↔ Q (S e) = 0 := fun e => Iff.rfl
  have hK₁mem : ∀ e : E, e ∈ K₁ ↔ P (S e) = 0 := fun e => Iff.rfl
  have hAmem : ∀ e : E, e - ξ (S e) ∈ K₂ := fun e => by
    rw [hK₂mem, map_sub, map_sub, hξ, sub_self]
  -- `A(e) = e − x(e)`
  let A₀ : K₁ →ₗ[ℝ] K₂ := LinearMap.codRestrict K₂
    ((LinearMap.id - (ξ : F →ₗ[ℝ] E) ∘ₗ (S : E →ₗ[ℝ] F)) ∘ₗ K₁.subtype) (fun e => hAmem e)
  have hA₀ : ∀ e : K₁, (A₀ e : E) = e - ξ (S e) := fun e => rfl
  have hA₀i : Function.Injective A₀ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨e, he⟩ hAe
    have h0 : e - ξ (S e) = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 hAe)
    have heX : e ∈ X := by rw [sub_eq_zero.1 h0]; exact hξX _
    have := Submodule.disjoint_def.1 hXP.disjoint e heX he
    exact (Submodule.mem_bot ℝ).2 (Subtype.ext this)
  have hA₀s : Function.Surjective A₀ := by
    rintro ⟨k, hk⟩
    have hk' : k ∈ X ⊔ K₁ := by rw [hXP.sup_eq_top]; trivial
    obtain ⟨x, hx, e, he, hxe⟩ := Submodule.mem_sup.1 hk'
    refine ⟨⟨e, he⟩, Subtype.ext ?_⟩
    rw [hA₀]
    have hd : (e - ξ (S e)) - k ∈ X := by
      have : (e - ξ (S e)) - k = -(x + ξ (S e)) := by rw [← hxe]; abel
      rw [this]
      exact X.neg_mem (X.add_mem hx (hξX _))
    have hdK : (e - ξ (S e)) - k ∈ K₂ := K₂.sub_mem (hAmem e) hk
    exact sub_eq_zero.1 (Submodule.disjoint_def.1 hXQ _ hd hdK)
  let A := LinearEquiv.ofBijective A₀ ⟨hA₀i, hA₀s⟩
  -- `B(f + H) = f̃ + H`
  let D : F →ₗ[ℝ] F := LinearMap.id - (P : F →ₗ[ℝ] F)
  let G : F →ₗ[ℝ] F ⧸ LinearMap.range (Q : F →ₗ[ℝ] F) :=
    (LinearMap.range (Q : F →ₗ[ℝ] F)).mkQ ∘ₗ (D - (S : E →ₗ[ℝ] F) ∘ₗ (ξ : F →ₗ[ℝ] E) ∘ₗ D)
  have hDP : ∀ f, D (P f) = 0 := fun f => by simp [D, hPP]
  let B₀ := (LinearMap.range (P : F →ₗ[ℝ] F)).liftQ G (by
    rintro _ ⟨f, rfl⟩
    simp [G, hDP])
  have hB₀ : ∀ f, B₀ (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk ((f - P f) - S (ξ (f - P f))) := fun f => rfl
  have hB₀i : Function.Injective B₀ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro α hα
    induction α using Submodule.Quotient.induction_on with
    | H f =>
    rw [LinearMap.mem_ker, hB₀, Submodule.Quotient.mk_eq_zero] at hα
    obtain ⟨g', hg'⟩ := hα
    have hQg : Q ((f - P f) - S (ξ (f - P f))) = 0 := by
      rw [map_sub, hξ, sub_self]
    have hg0 : (f - P f) - S (ξ (f - P f)) = 0 := by
      have hg'' : Q g' = (f - P f) - S (ξ (f - P f)) := hg'
      rw [← hg''] at hQg ⊢
      rwa [hQQ] at hQg
    have hPx : P (S (ξ (f - P f))) = 0 := by
      have : S (ξ (f - P f)) = f - P f := (sub_eq_zero.1 hg0).symm
      rw [this, map_sub, hPP, sub_self]
    have hx0 : ξ (f - P f) = 0 :=
      Submodule.disjoint_def.1 hXP.disjoint _ (hξX _) ((hK₁mem _).2 hPx)
    rw [hx0, map_zero, sub_zero] at hg0
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact ⟨f, (sub_eq_zero.1 hg0).symm⟩
  let B := LinearEquiv.ofBijective B₀
    ⟨hB₀i, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hcoker).1 hB₀i⟩
  refine ⟨A, B, fun e => rfl, fun f => rfl, ?_, ?_, ?_⟩
  · -- (6.17)
    refine LinearMap.ext fun e => Subtype.ext ?_
    have hSe : S e = 0 := e.2
    change (e : E) - ξ (S e) = e
    rw [hSe, map_zero, sub_zero]
  · -- (6.20)
    refine LinearMap.ext fun e => ?_
    have hPe : P (S e) = 0 := e.2
    change Submodule.Quotient.mk (S ((e : E) - ξ (S e))) =
      B₀ (Submodule.Quotient.mk (S e))
    rw [hB₀, hPe, sub_zero, map_sub]
  · -- (6.21)
    refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
    change projSeqPi (T := S) hQS.isProj (B₀ (Submodule.Quotient.mk f)) =
      projSeqPi (T := S) hPS.isProj (Submodule.Quotient.mk f)
    rw [hB₀, projSeqPi_mk, projSeqPi_mk, Submodule.Quotient.eq]
    refine ⟨-(ξ (f - P f)), ?_⟩
    have hQ0 : Q ((f - P f) - S (ξ (f - P f))) = 0 := by rw [map_sub, hξ, sub_self]
    rw [hQ0, sub_zero]
    change S (-(ξ (f - P f))) = _
    rw [map_neg]
    abel

end Diagram

/-! ### The solution operator and the transition maps, for every `S` -/

section Transition

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `g ↦ Q g`, as a map into `R(Q)`. -/
def projCod (Q : F →L[ℝ] F) : F →L[ℝ] LinearMap.range (Q : F →ₗ[ℝ] F) :=
  Q.codRestrict _ (fun g => LinearMap.mem_range_self (Q : F →ₗ[ℝ] F) g)

/-- The **solution operator** `(Q S|_X)⁻¹ ∘ Q : F → X ⊆ E` of (6.15) and (6.18): `x = ξ(g) ∈ X`
solves `Q S x = Q g` when `Q S|_X : X → R(Q)` is an isomorphism (`ContinuousLinearMap.inverse` is
`0` otherwise). -/
def solveOp (Q : F →L[ℝ] F) (X : Submodule ℝ E) (S : E →L[ℝ] F) : F →L[ℝ] E :=
  X.subtypeL ∘L ContinuousLinearMap.inverse (projRestrict Q S X) ∘L projCod Q

/-- **`A_S` extended to `E`** (6.16): `e ↦ e − x(e)`, `x(e) = ξ(S e) ∈ X` solving
`Q S x = Q S e`. -/
def kerTransition (Q : F →L[ℝ] F) (X : Submodule ℝ E) (S : E →L[ℝ] F) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - solveOp Q X S ∘L S

/-- **`B_S` lifted to `F`** (6.19): `f ↦ f̃ = (1 − P) f − S x`, where `x = ξ((1 − P) f) ∈ X`, so
that `S x + f̃ = (1 − P) f` (6.18). -/
def cokerTransition (P Q : F →L[ℝ] F) (X : Submodule ℝ E) (S : E →L[ℝ] F) : F →L[ℝ] F :=
  (1 - P) - S ∘L solveOp Q X S ∘L (1 - P)

theorem solveOp_mem (Q : F →L[ℝ] F) (X : Submodule ℝ E) (S : E →L[ℝ] F) (g : F) :
    solveOp Q X S g ∈ X :=
  (ContinuousLinearMap.inverse (projRestrict Q S X) (projCod Q g)).2

theorem kerTransition_apply (Q : F →L[ℝ] F) (X : Submodule ℝ E) (S : E →L[ℝ] F) (e : E) :
    kerTransition Q X S e = e - solveOp Q X S (S e) := rfl

theorem cokerTransition_apply (P Q : F →L[ℝ] F) (X : Submodule ℝ E) (S : E →L[ℝ] F) (f : F) :
    cokerTransition P Q X S f = (f - P f) - S (solveOp Q X S (f - P f)) := rfl

/-- If `R S|_X` is an isomorphism `e`, then `R S (ξ g) = R g`. -/
theorem apply_solveOp_of_projRestrict_eq {R : F →L[ℝ] F} {X : Submodule ℝ E} {S : E →L[ℝ] F}
    {e : X ≃L[ℝ] LinearMap.range (R : F →ₗ[ℝ] F)}
    (he : (e : X →L[ℝ] LinearMap.range (R : F →ₗ[ℝ] F)) = projRestrict R S X) (g : F) :
    R (S (solveOp R X S g)) = R g := by
  have h : projRestrict R S X (ContinuousLinearMap.inverse (projRestrict R S X) (projCod R g)) =
      projCod R g := by
    rw [← he, ContinuousLinearMap.inverse_equiv]
    exact e.apply_symm_apply _
  exact congrArg Subtype.val h

/-- If `R S|_X` is an isomorphism, then `X ∩ ker(R S) = 0`. -/
theorem disjoint_ker_comp_of_projRestrict_eq {R : F →L[ℝ] F} {X : Submodule ℝ E}
    {S : E →L[ℝ] F} {e : X ≃L[ℝ] LinearMap.range (R : F →ₗ[ℝ] F)}
    (he : (e : X →L[ℝ] LinearMap.range (R : F →ₗ[ℝ] F)) = projRestrict R S X) :
    Disjoint X (LinearMap.ker ((R ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)) := by
  rw [Submodule.disjoint_def]
  intro x hx hxk
  have h0 : e ⟨x, hx⟩ = 0 := by
    rw [← ContinuousLinearEquiv.coe_coe, he]
    exact Subtype.ext hxk
  exact congrArg Subtype.val (e.map_eq_zero_iff.1 h0)

/-- If `R S|_X` is an isomorphism, then `E = ker(R S) ⊕ X` topologically (the projection onto `X`
is `(R S|_X)⁻¹ ∘ R S`). -/
theorem isTopCompl_ker_comp_of_projRestrict_eq {R : F →L[ℝ] F} {X : Submodule ℝ E}
    {S : E →L[ℝ] F} {e : X ≃L[ℝ] LinearMap.range (R : F →ₗ[ℝ] F)}
    (he : (e : X →L[ℝ] LinearMap.range (R : F →ₗ[ℝ] F)) = projRestrict R S X) :
    (LinearMap.ker ((R ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)).IsTopCompl X := by
  let c : E →L[ℝ] LinearMap.range (R : F →ₗ[ℝ] F) := (R ∘L S).codRestrict _ (fun x => ⟨S x, rfl⟩)
  let f : E →L[ℝ] X := (e.symm : LinearMap.range (R : F →ₗ[ℝ] F) →L[ℝ] X) ∘L c
  have hf : ∀ x : X, f x = x := fun x => by
    have : c (x : E) = e x := by
      rw [← ContinuousLinearEquiv.coe_coe, he]
      rfl
    change e.symm (c x) = x
    rw [this, e.symm_apply_apply]
  have hker : LinearMap.ker (f : E →ₗ[ℝ] X) =
      LinearMap.ker ((R ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    change e.symm (c x) = 0 ↔ R (S x) = 0
    rw [e.symm.map_eq_zero_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have := ContinuousLinearMap.isTopCompl_of_proj hf
  exact hker ▸ this.symm

end Transition

/-! ### Proposition 6.4.13, last sentence -/

section Main

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- `S ↦ ξ_S` is continuous at every `S` for which `Q S|_X` is an isomorphism (`X` closed):
inversion is continuous at isomorphisms. -/
theorem continuousAt_solveOp {Q : F →L[ℝ] F} {X : Submodule ℝ E} (hXc : IsClosed (X : Set E))
    {S : E →L[ℝ] F} {e : X ≃L[ℝ] LinearMap.range (Q : F →ₗ[ℝ] F)}
    (he : (e : X →L[ℝ] LinearMap.range (Q : F →ₗ[ℝ] F)) = projRestrict Q S X) :
    ContinuousAt (solveOp Q X) S := by
  have : CompleteSpace X := hXc.completeSpace_coe
  have h := (contDiffAt_map_inverse (n := 0) e).continuousAt
  rw [he] at h
  have h2 : ContinuousAt
      (fun S' : E →L[ℝ] F => ContinuousLinearMap.inverse (projRestrict Q S' X)) S := by
    have h3 := (continuous_projRestrict Q X).continuousAt (x := S)
    exact ContinuousAt.comp (x := S) h h3
  exact continuousAt_const.clm_comp (h2.clm_comp continuousAt_const)

/-- **2021 Proposition 6.4.13, p. 253, last sentence** (2017: Proposition 6.6): for `T` Fredholm
and `P, Q ∈ Π_T ∩ 𝒫_H`, the constructions of `A_{T'}` and `B_{T'}` with a fixed closed complement
`X` of `ker(P T)` and `ker(Q T)` depend continuously on `T'` near `T`.  Precisely: there are a
closed `X` and `ε > 0` such that on `‖S − T‖ < ε`
* `S ↦ kerTransition Q X S` (`A_S` on `E`) and `S ↦ cokerTransition P Q X S` (`B_S` lifted to
  `F`) are continuous in the operator norm, and jointly with the vector (as maps of the kernel
  bundles `⋃ {S} × ker(P S) ⊆ L(E, F) × E` of Remark 6.4.5);
* `P, Q ∈ Π_S` and `ker(P S) ⊕ X = ker(Q S) ⊕ X = E` (topological complements);
* (6.15)–(6.16): `e − A_S e ∈ X` and `Q S (A_S e) = 0`; (6.18)–(6.19): `Q (B_S f) = 0` and
  `S x + B_S f = (1 − P) f` for some `x ∈ X`;
* `A_S` restricts to an isomorphism `ker(P S) → ker(Q S)`, `B_S` induces an isomorphism
  `F/R(P) → F/R(Q)` (`R(P) = R(Q) = H`), and they fill the diagram of `E(S, P)`, `E(S, Q)`:
  `A ∘ j_P = j_Q`, `Φ_Q ∘ A = B ∘ Φ_P`, `π_Q ∘ B = π_P`. -/
theorem proposition_6_4_13_continuity {T : E →L[ℝ] F} (hT : T.IsFredholm)
    {H : Submodule ℝ F} {P Q : F →L[ℝ] F} (hP : IsGoodLeftProj T P) (hQ : IsGoodLeftProj T Q)
    (hPH : LinearMap.range (P : F →ₗ[ℝ] F) = H) (hQH : LinearMap.range (Q : F →ₗ[ℝ] F) = H) :
    ∃ (X : Submodule ℝ E) (ε : ℝ), IsClosed (X : Set E) ∧ 0 < ε ∧
      ContinuousOn (kerTransition Q X) (Metric.ball T ε) ∧
      ContinuousOn (cokerTransition P Q X) (Metric.ball T ε) ∧
      ContinuousOn (fun p : (E →L[ℝ] F) × E => kerTransition Q X p.1 p.2)
        (Metric.ball T ε ×ˢ univ) ∧
      ContinuousOn (fun p : (E →L[ℝ] F) × F => cokerTransition P Q X p.1 p.2)
        (Metric.ball T ε ×ˢ univ) ∧
      ∀ S ∈ Metric.ball T ε, IsGoodLeftProj S P ∧ IsGoodLeftProj S Q ∧
        (LinearMap.ker ((P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)).IsTopCompl X ∧
        (LinearMap.ker ((Q ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)).IsTopCompl X ∧
        (∀ e, e - kerTransition Q X S e ∈ X ∧ Q (S (kerTransition Q X S e)) = 0) ∧
        (∀ f, Q (cokerTransition P Q X S f) = 0 ∧
          ∃ x ∈ X, S x + cokerTransition P Q X S f = f - P f) ∧
        ∃ (A : LinearMap.ker ((P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F) ≃ₗ[ℝ]
            LinearMap.ker ((Q ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F))
          (B : (F ⧸ LinearMap.range (P : F →ₗ[ℝ] F)) ≃ₗ[ℝ]
            (F ⧸ LinearMap.range (Q : F →ₗ[ℝ] F))),
          (∀ e, (A e : E) = kerTransition Q X S e) ∧
          (∀ f, B (Submodule.Quotient.mk f) =
            Submodule.Quotient.mk (cokerTransition P Q X S f)) ∧
          (A : _ →ₗ[ℝ] _) ∘ₗ projSeqJ S P = projSeqJ S Q ∧
          projSeqPhi S Q ∘ₗ (A : _ →ₗ[ℝ] _) = (B : _ →ₗ[ℝ] _) ∘ₗ projSeqPhi S P ∧
          projSeqPi (T := S) hQ.isProj ∘ₗ (B : _ →ₗ[ℝ] _) = projSeqPi (T := S) hP.isProj := by
  set K₁ := LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) with hK₁
  set K₂ := LinearMap.ker ((Q ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) with hK₂
  have : FiniteDimensional ℝ K₁ := (hP.isFredholm_comp hT).finite_ker
  have : FiniteDimensional ℝ K₂ := (hQ.isFredholm_comp hT).finite_ker
  have := hP.finite_coker
  have := hQ.finite_coker
  have hrangeQ : LinearMap.range (P : F →ₗ[ℝ] F) = LinearMap.range (Q : F →ₗ[ℝ] F) :=
    hPH.trans hQH.symm
  -- `dim ker(P T) = dim ker(Q T)`
  have hrank : finrank ℝ K₁ = finrank ℝ K₂ := by
    have h := (hP.fredholmIndex_comp hT).trans (hQ.fredholmIndex_comp hT).symm
    have hc : finrank ℝ (F ⧸ LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) =
        finrank ℝ (F ⧸ LinearMap.range ((Q ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
      (Submodule.quotEquivOfEq _ _ (by rw [hP.range_comp, hQ.range_comp, hrangeQ])).finrank_eq
    unfold fredholmIndex linIndex at h
    rw [hc] at h
    exact_mod_cast sub_left_inj.1 h
  obtain ⟨X, hXc, hX₁, hX₂⟩ := exists_isClosed_isTopCompl_isTopCompl_of_finrank_eq K₁ K₂ hrank
  -- Lemma 6.5.1 (preprint 6.17) for `(T, P, X)` and `(T, Q, X)`
  obtain ⟨εP, hεP, hP'⟩ := lemma_6_5_1 hP hX₁
  obtain ⟨εQ, hεQ, hQ'⟩ := lemma_6_5_1 hQ hX₂
  have hball : ∀ S ∈ Metric.ball T (min εP εQ), ‖S - T‖ < εP ∧ ‖S - T‖ < εQ := fun S hS => by
    rw [mem_ball_iff_norm] at hS
    exact ⟨hS.trans_le (min_le_left _ _), hS.trans_le (min_le_right _ _)⟩
  have hcont : ∀ S ∈ Metric.ball T (min εP εQ), ContinuousAt (solveOp Q X) S := fun S hS => by
    obtain ⟨-, e, he⟩ := hQ' S (hball S hS).2
    exact continuousAt_solveOp hXc he
  have hcA : ∀ S ∈ Metric.ball T (min εP εQ), ContinuousAt (kerTransition Q X) S := fun S hS =>
    continuousAt_const.sub ((hcont S hS).clm_comp continuousAt_id)
  have hcB : ∀ S ∈ Metric.ball T (min εP εQ), ContinuousAt (cokerTransition P Q X) S :=
    fun S hS => continuousAt_const.sub
      (continuousAt_id.clm_comp ((hcont S hS).clm_comp continuousAt_const))
  refine ⟨X, min εP εQ, hXc, lt_min hεP hεQ, fun S hS => (hcA S hS).continuousWithinAt,
    fun S hS => (hcB S hS).continuousWithinAt, fun p hp => ?_, fun p hp => ?_, fun S hS => ?_⟩
  · exact (((hcA p.1 hp.1).comp continuousAt_fst).clm_apply continuousAt_snd).continuousWithinAt
  · exact (((hcB p.1 hp.1).comp continuousAt_fst).clm_apply continuousAt_snd).continuousWithinAt
  obtain ⟨hPS, eP, heP⟩ := hP' S (hball S hS).1
  obtain ⟨hQS, eQ, heQ⟩ := hQ' S (hball S hS).2
  have hξ := apply_solveOp_of_projRestrict_eq heQ
  obtain ⟨A, B, hA, hB, h1, h2, h3⟩ := diagram_of_solveOp hPS hQS hrangeQ
    (isTopCompl_ker_comp_of_projRestrict_eq heP).isCompl.symm
    (disjoint_ker_comp_of_projRestrict_eq heQ) (solveOp Q X S) (solveOp_mem Q X S) hξ
  refine ⟨hPS, hQS, isTopCompl_ker_comp_of_projRestrict_eq heP,
    isTopCompl_ker_comp_of_projRestrict_eq heQ, fun e => ⟨?_, ?_⟩,
    fun f => ⟨?_, solveOp Q X S (f - P f), solveOp_mem Q X S _, ?_⟩, A, B, hA, hB, h1, h2, h3⟩
  · rw [kerTransition_apply, sub_sub_cancel]
    exact solveOp_mem Q X S _
  · rw [kerTransition_apply, map_sub, map_sub, hξ, sub_self]
  · rw [cokerTransition_apply, map_sub, hξ, sub_self]
  · rw [cokerTransition_apply, add_sub_cancel]

/-- **Non-vacuity of `proposition_6_4_13_continuity`**: its hypotheses hold for `T = 1` on
`ℝ`, `P = Q` a good left-projection of `T` and `H = R(P)`. -/
theorem proposition_6_4_13_continuity_hyps :
    ∃ (T : ℝ →L[ℝ] ℝ) (P Q : ℝ →L[ℝ] ℝ) (H : Submodule ℝ ℝ), T.IsFredholm ∧
      IsGoodLeftProj T P ∧ IsGoodLeftProj T Q ∧ LinearMap.range (P : ℝ →ₗ[ℝ] ℝ) = H ∧
        LinearMap.range (Q : ℝ →ₗ[ℝ] ℝ) = H := by
  have hT : (1 + 0 : ℝ →L[ℝ] ℝ).IsFredholm := isFredholm_one_add isCompactOperator_zero
  obtain ⟨P, hP⟩ := exists_isGoodLeftProj hT
  exact ⟨_, P, P, _, hT, hP, hP, rfl, rfl⟩

end Main

end Polyfold
