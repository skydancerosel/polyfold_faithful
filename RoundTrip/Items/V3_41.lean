import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_41

/-!
Round trip for V3_41 (Lemma 3.46: good position of `ker DH(0)`).

`A` is the conjunction of the types of `Polyfold.lemma_3_46` and
`Polyfold.lemma_3_46_isInGoodPosition` (no universe parameters): the linear-algebra core, for any
finite-dimensional `P`, sc-Banach `W`, `L : P → W₀`, `K̃ ⊆ P`: if the graph
`K' = {(α, Lα) | α ∈ K̃}` has an (algebraic) good complement `Y'` w.r.t. `C̃ × W`, then `K̃` has a
good complement `Z` w.r.t. `C̃` with `Z ⊕ W` a good complement of `K'`; and good position of `K'`
gives good position of `K̃`.

Neither `A → B` nor `B → A` is proved.
* `A → B`: B's `K' = ker Dg(0)` is not given as a graph, nor in good position.  The text gets both
  from other results applied in B's setting: (G1) Lemma 3.44 (`K' = {(α, Dδ(0)α) | α ∈ ker DH(0)}`,
  which also needs `δ` differentiable at `0`, Theorem 3.33 — B only assumes `δ` continuous) and
  (G2) Lemma 3.45 with the chain rule for the push-forward germ `g = Φ_*(f)` (`ker Dg(0) =
  Dφ(0) ker Df(0)` is in good position to `C'`).  `B_of_A_given` proves that A, (G1) and (G2) give
  B's conclusion (glue: sc-complements in `ℝ^{n'}` are algebraic complements; `K'` is smooth by
  Proposition 1.6, so the closed `Z ⊕ W'` is an sc-complement, `isScSplitting_of_isClosed` from
  V3_20).  So A is exactly the last, linear step of the text's lemma.
* `B → A`: A is a general lemma (arbitrary `P`, `L`, `K̃`, algebraic `Y'`); B only speaks about
  `L = ι Dδ(0)`, `K̃ = ker DH(0)` arising from a push-forward `g = Φ_*(h + s)`; no instantiation.
-/

namespace RoundTrip.V3_41
open Polyfold Set Module

/-- The project's statement: Lemma 3.46. -/
def A : Prop := type_of% @Polyfold.lemma_3_46 ∧ type_of% @Polyfold.lemma_3_46_isInGoodPosition

theorem A_holds : A := ⟨@Polyfold.lemma_3_46, @Polyfold.lemma_3_46_isInGoodPosition⟩

/-! ### A closed complement of a smooth finite-dimensional subspace is an sc-complement (V3_20) -/

section Split

variable {E : ScBanach} {N Y : Submodule ℝ (E 0)} [FiniteDimensional ℝ N]

/-- The level-`m` projection `x ↦ lift_m(π x)` onto `N_m` along `Y_m`. -/
noncomputable def projLvl (hN : N ≤ E.smooth) (h : Submodule.IsTopCompl N Y) (m : ℕ) :
    E m →L[ℝ] E m :=
  (LinearMap.toContinuousLinearMap (finSmoothLift hN m)).comp
    ((N.projectionOntoL Y h).comp (E.toBase m))

lemma toBase_projLvl (hN : N ≤ E.smooth) (h : Submodule.IsTopCompl N Y) (m : ℕ) (x : E m) :
    E.toBase m (projLvl hN h m x) = (N.projectionOntoL Y h (E.toBase m x) : E 0) :=
  toBase_finSmoothLift hN m _

noncomputable def projOp (hN : N ≤ E.smooth) (h : Submodule.IsTopCompl N Y) : ScOperator E E where
  lvl := projLvl hN h
  incl_comm m x := by
    apply E.toBase_injective m
    rw [← ScScale.toBase_succ, toBase_projLvl, toBase_projLvl, ScScale.toBase_succ]

lemma projOp_zero (hN : N ≤ E.smooth) (h : Submodule.IsTopCompl N Y) (x : E 0) :
    projOp hN h 0 x = (N.projectionOntoL Y h x : E 0) :=
  toBase_projLvl hN h 0 x

/-- A closed complement `Y` of a smooth finite-dimensional `N` is an sc-complement. -/
theorem isScSplitting_of_isClosed (hN : N ≤ E.smooth) (hNY : IsCompl N Y)
    (hY : IsClosed (Y : Set (E 0))) : E.IsScSplitting N Y := by
  have h : Submodule.IsTopCompl N Y :=
    (Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional hNY.symm hY).symm
  have hidem : ∀ x, projOp hN h 0 (projOp hN h 0 x) = projOp hN h 0 x := fun x => by
    rw [projOp_zero hN h (projOp hN h 0 x), projOp_zero hN h x,
      Submodule.projectionOntoL_apply_left]
  have hS := ScBanach.isScSplitting_of_idem (projOp hN h) hidem
  have hr : LinearMap.range (projOp hN h 0 : E 0 →ₗ[ℝ] E 0) = N := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change projOp hN h 0 y ∈ N
      rw [projOp_zero]
      exact (N.projectionOntoL Y h y).2
    · intro hx
      refine ⟨x, ?_⟩
      change projOp hN h 0 x = x
      rw [projOp_zero, Submodule.projectionOntoL_apply_left h ⟨x, hx⟩]
  have hk : LinearMap.ker (projOp hN h 0 : E 0 →ₗ[ℝ] E 0) = Y := by
    ext x
    rw [LinearMap.mem_ker]
    change projOp hN h 0 x = 0 ↔ x ∈ Y
    rw [projOp_zero, ← Submodule.projectionOntoL_apply_eq_zero_iff h]
    exact ⟨fun h0 => Subtype.ext h0, fun h0 => by rw [h0]; rfl⟩
  rwa [hr, hk] at hS

end Split

/-! ### Glue -/

/-- Every point of a constant sc-structure is smooth. -/
lemma le_smooth_const {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (N : Submodule ℝ V) : N ≤ (ScBanach.const V).smooth := by
  intro x _
  refine ((ScBanach.const V).toScScale.mem_smooth_iff).2 fun j => ⟨show V from x, ?_⟩
  exact ScBanach.const_toBase V j x

/-- In `ℝ^{n'}` (constant structure) an algebraic good complement is an sc-good complement. -/
theorem goodComplementSc_const {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {C : Set V} {N Z : Submodule ℝ V}
    (h : IsGoodComplement (ScBanach.const V) C N Z) :
    IsGoodComplementSc (ScBanach.const V) C N Z :=
  ⟨isScSplitting_of_isClosed (le_smooth_const N) h.isCompl (Submodule.closed_of_finiteDimensional Z),
    h.exists_eps⟩

/-- **B's conclusion from A, given the two identifications of the surrounding proof**:
(G1) `K'` is the graph of some `L' : ℝ^{n'} → W'₀` over `K̃ = ker DH(0)` (Lemma 3.44), and
(G2) `K'` is in good position to `C' = C̃' × W'` with an sc-complement (Lemma 3.45 for `Dφ(0)`,
plus `ker Dg(0) = Dφ(0) ker Df(0)`). -/
theorem B_of_A_given (hA : A) {n' N' : ℕ} {W' : ScBanach} {Ct' : Set (Fin n' → ℝ)}
    {L : (Fin n' → ℝ) →L[ℝ] (Fin N' → ℝ)}
    {K' : Submodule ℝ ((ScBanach.paramProd (Fin n' → ℝ) W').lvl 0)}
    (L' : (Fin n' → ℝ) →L[ℝ] W'.lvl 0)
    (hker : K' = (LinearMap.ker (L : (Fin n' → ℝ) →ₗ[ℝ] (Fin N' → ℝ))).map (graphMap L'))
    (hpos : IsInGoodPositionSc (ScBanach.paramProd (Fin n' → ℝ) W') (Ct' ×ˢ univ) K') :
    IsInGoodPositionSc (ScBanach.const (Fin n' → ℝ)) Ct'
        (LinearMap.ker (L : (Fin n' → ℝ) →ₗ[ℝ] (Fin N' → ℝ))) ∧
      ∃ Z : Submodule ℝ (Fin n' → ℝ),
        IsGoodComplementSc (ScBanach.const (Fin n' → ℝ)) Ct'
          (LinearMap.ker (L : (Fin n' → ℝ) →ₗ[ℝ] (Fin N' → ℝ))) Z ∧
        IsGoodComplementSc (ScBanach.paramProd (Fin n' → ℝ) W') (Ct' ×ˢ univ) K'
          (Z.prod (⊤ : Submodule ℝ (W'.lvl 0))) := by
  obtain ⟨hint, Y', hsplitY, ε, hε, hgood⟩ := hpos
  have hgcY : IsGoodComplement (ScBanach.paramProd (Fin n' → ℝ) W') (Ct' ×ˢ univ) K' Y' := by
    refine ⟨?_, ε, hε, hgood⟩
    have := hsplitY.2.2 0
    rwa [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at this
  subst hker
  obtain ⟨Z, hZ, hZY⟩ := hA.1 hgcY
  have hKpos := hA.2 ⟨hint, Y', hgcY⟩
  have hsm := ((ScBanach.paramProd (Fin n' → ℝ) W').proposition_1_6_iff _).1 hsplitY.1
  have hZc : IsClosed ((Z.prod (⊤ : Submodule ℝ (W'.lvl 0)) : Submodule ℝ _) :
      Set ((ScBanach.paramProd (Fin n' → ℝ) W').lvl 0)) := by
    have : ((Z.prod (⊤ : Submodule ℝ (W'.lvl 0)) : Submodule ℝ _) :
        Set ((Fin n' → ℝ) × W'.lvl 0)) = (Z : Set (Fin n' → ℝ)) ×ˢ univ := by
      ext x; simp
    rw [this]
    exact (Submodule.closed_of_finiteDimensional Z).prod isClosed_univ
  exact ⟨⟨hKpos.interior_nonempty, Z, goodComplementSc_const hZ⟩, Z, goodComplementSc_const hZ,
    isScSplitting_of_isClosed hsm hZY.isCompl hZc, hZY.exists_eps⟩

#rt_check RoundTrip.V3_41.B_of_A_given [Polyfold.lemma_3_46, Polyfold.lemma_3_46_isInGoodPosition]

end RoundTrip.V3_41
