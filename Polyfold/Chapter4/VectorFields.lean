import Polyfold.Chapter1.LevelsWeak
import Polyfold.Chapter2.TangentMap
import Polyfold.Chapter3.StrongBundleSections

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 4, §4.4
"Sc-Differential Forms" (pp. 195–199) and Appendix 4.5 (pp. 199–208), the part on vector fields:
**Definition 4.4.3** (p. 195), **Lemma 4.4.4** (p. 196), **Proposition 4.4.5** (p. 196; 2017:
Proposition 4.5; preprint: Proposition 4.26) and **§4.5.1** (pp. 200–201).  All of these except
Proposition 4.4.5 are new in the 2021 edition.

# Sc-smooth vector fields and their Lie bracket

## The text, paraphrased

(Definition 4.4.3, p. 195) An sc-smooth vector field on an M-polyfold `X` is an sc-smooth section
`A` of the tangent bundle `p : TX → X¹`; its domain is `X¹`, not `X`.

(Lemma 4.4.4, p. 196) By the natural identification of `(TX)^i → (X¹)^i` with
`T(X^i) → X^{i+1}`, the index of a vector field `A` can be raised by `i ≥ 0`: `A^(i)` is an
sc-smooth vector field of `X^i`.

(Proposition 4.4.5, p. 196; proof §4.5.1–§4.5.2) For sc-smooth vector fields `A`, `B` on `X` the
usual formula defines the Lie bracket `[A, B]`, an sc-smooth section of `TX|X² → X²`.

(§4.5.1, pp. 200–201) In a local model `O = r(U)` the principal parts satisfy
`A(x) = Dr(x) A(x)`, `B(x) = Dr(x) B(x)` on `O₁`.  Differentiating the first identity at `x ∈ O₂`
in the direction `B(x)`, the second in the direction `A(x)`, subtracting and using the symmetry of
`D²r(x)` gives `Dr(x)[A, B](x) = [A, B](x)` for `[A, B](x) = DA(x) B(x) − DB(x) A(x)`.
(Lemma 4.5.1, p. 201, proof left to the reader; §4.5.2) The bracket is natural under local
sc-diffeomorphisms, hence independent of the chart.

## What is formalized

In a local model `(O, C, E)`:
* `Polyfold.IsRetractVectorField E C O A` (**Definition 4.4.3**, local form): the principal part
  `A : E₁ → E₀` makes `x ↦ (x, A(x))` an sc-smooth map from `(O¹, C¹, E¹)` to the tangent
  `(TO, TC, TE)`.  Witness: `isRetractVectorField_zero`.
* `Polyfold.retractTangent_shift`: `T(O¹) = (TO)¹`, the identification behind Lemma 4.4.4.
* `Polyfold.IsRetractVectorField.shift` (**Lemma 4.4.4**, local form, `i = 1`; larger `i` by
  iterating): `A₁ : E₂ → E₁` is a vector field on `(O¹, C¹, E¹)`.
* `Polyfold.scSecondDeriv U f z a b`, "`D²f(z)(a, b)`" for `z ∈ U₂`, `a, b ∈ E₁`: the second
  component of `D(Tf)(z, a)(b, 0)`.  `Polyfold.scSecondDeriv_symm`: **the symmetry of the second
  derivative** used in §4.5.1, for an sc² map on a relatively open subset of a partial quadrant.
  `Polyfold.scDeriv_tangentMap_inr`: `D(Tf)(z, a)(0, l) = (0, Df(z) l)`.
* `Polyfold.retractLieBracket R A B x = DÃ(x) B(x) − DB̃(x) A(x)` for `x ∈ E₂`, with
  `Ã = A ∘ r¹`; `retractLieBracket_antisymm`.
* `Polyfold.IsRetractVectorField.diff_identity`: the differentiated identity of §4.5.1,
  `D²r(x)(A(x), b) + Dr(x) DÃ(x) b = DÃ(x) b` for `x ∈ O₂`, `b ∈ T_x(O¹)`.
* `Polyfold.retractLieBracket_mem_tangent` (**§4.5.1**): `Dr(x)[A, B](x) = [A, B](x)` on `O₂`.
* `Polyfold.proposition_4_4_5_local_2021` (**Proposition 4.4.5**, local form): `x ↦ (x, [A, B](x))`
  maps `O₂` into `TO` and is sc-smooth from `(O², C², E²)` to `(TO, TC, TE)`, the local form of
  "`[A, B]` is an sc-smooth section of `TX|X² → X²`".

On an M-polyfold:
* `Polyfold.MPolyfold.IsScVectorField` (**Definition 4.4.3**): `A : X¹ → TX` is sc-smooth for the
  M-polyfold structures `P.shift` of `X¹` and `P.tangentPolyfold` of `TX`, and `p ∘ A = id`.
  Witness: `MPolyfold.isScVectorField_zero`, the zero section `MPolyfold.zeroVectorField`.

## What is not formalized

* Lemma 4.4.4 and Proposition 4.4.5 on an M-polyfold: they need the identification of the
  M-polyfolds `(TX)^i` and `T(X^i)` (gap G.6), the pullback bundle `TX|X² → X²`, and Lemma 4.5.1
  (independence of the chart), whose proof the text leaves to the reader.
* Definitions 4.4.1–4.4.2 (sc-differential forms, the Whitney sum `⊕ₖ TX`, the direct limit
  `Ω∞*`), the exterior derivative and `d ∘ d = 0`, Definition 4.4.6, Theorem 4.4.7 (Stokes),
  Lemma 4.4.8 and Lemma 4.5.2 (Poincaré lemma).

## What the text leaves implicit, and the choices made

* `DA(x)` is the sc-derivative of `Ã = A ∘ r¹ : U¹ → E`, the principal part being defined only on
  `O¹`.  On `T_x(O¹)`, where `B(x)` lies for `x ∈ O₂`, it does not depend on `r`
  (Proposition 2.1.13 (2)).
* `D²r(x)(a, b)` with `a, b ∈ E₁` is defined through the sc²-structure (the derivative of `Tr`):
  `r : U₂ → E₀` is `C²`, but `a, b` need not lie in `E₂`.  Its symmetry is Mathlib's
  `ContDiffWithinAt.isSymmSndFDerivWithinAt` for `a, b ∈ E₂` (points of a partial quadrant lie in
  the closure of its interior), extended by density of `E₂` in `E₁` and continuity of `D(Tr)`.
* "If `x ∈ O₂`, then `[A, B](x)` belongs to the level 1" (p. 201): read as `[A, B](x) ∈ E₁` it
  does not hold as we read it: proved in `Polyfold/Chapter4/BracketLevel.lean` on the weighted
  `c₀` space `ScOneExample.X`.  The first sketch, on `E_m = ℓ²` with weights `4^{mk}`, the
  sc-operators `S = diag(2^k)` and `(Tx)_k = 2^k x_{k+1}` from `E¹` to `E` are vector fields on
  `O = E`, `[S, T]x = −(4^k x_{k+1})_k`, and `x_j = 4^{-j}/j` lies in `E₂` with `[S, T]x ∉ E₁`.
  We read the sentence as: `[A, B](x)` is a tangent vector at the point `x` of level `1` of `X¹`,
  i.e. `x ∈ O_{m+2}` gives `[A, B](x) ∈ E_m`, which is what Proposition 4.4.5 states and what
  is formalized.
* §4.5.2 ends with "The proof of Proposition 4.5.1 is complete"; there is no Proposition 4.5.1 and
  the computation is the one of Lemma 4.5.1: possible misprint.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

variable {E : ScBanach}

/-! ### Vector fields in a local model (Definition 4.4.3, Lemma 4.4.4) -/

section LocalVectorField

variable {C O : Set (E 0)}

variable (E C O) in
/-- **Definition 4.4.3, p. 195 (new in the 2021 edition)**, in a local model `(O, C, E)`: the
principal part `A : E₁ → E₀` of an sc-smooth vector field, i.e. `x ↦ (x, A(x))` is an sc-smooth
map from `(O¹, C¹, E¹)` to the tangent `(TO, TC, TE)` (an sc-smooth section of `TO → O¹`). -/
def IsRetractVectorField (A : E 1 → E 0) : Prop :=
  IsScSmoothRetractMap E.shift (E.lvlSet C 1) (E.lvlSet O 1) E.tangent (E.tangentSet C)
    (retractTangent E C O) (fun x => ((x, A x) : E.tangent 0))

/-- Satisfiability of `IsRetractVectorField`: the zero vector field on any sc-smooth retract. -/
theorem isRetractVectorField_zero (hO : IsScRetract E C O) : IsRetractVectorField E C O 0 := by
  refine ⟨fun x hx => mk_zero_mem_retractTangent hO hx, fun ρ _ => ?_⟩
  have h2 : IsScSmooth (E := E.shift) (F := E) ρ.U (ScOperator.zeroOp E.shift E 0) :=
    (ScOperator.zeroOp E.shift E).isScSmooth ρ.isScDomain
  exact ρ.isScSmooth.scPair ρ.isScDomain h2

variable {A : E 1 → E 0}

/-- `(x, A(x)) ∈ TO` for `x ∈ O₁`. -/
theorem IsRetractVectorField.mem_retractTangent (h : IsRetractVectorField E C O A) {x : E 1}
    (hx : x ∈ E.lvlSet O 1) : ((x, A x) : E.tangent 0) ∈ retractTangent E C O :=
  h.mapsTo hx

/-- `Ã = A ∘ r¹ : U¹ → E` is sc-smooth for a retraction `r` onto `O`. -/
theorem IsRetractVectorField.isScSmooth_comp (h : IsRetractVectorField E C O A)
    (R : ScRetraction E C) (hR : R.retract = O) :
    IsScSmooth (E := E.shift) (F := E) R.shift.U (A ∘ R.shift) := by
  have := h.comp_isScSmooth R.shift (by rw [R.shift_retract, hR])
  exact this.snd R.shift.isScDomain

/-- `A(x) ∈ T_xO`, i.e. `Dr(x) A(x) = A(x)` for `x ∈ O₁` (formula (4.8), p. 200). -/
theorem IsRetractVectorField.scDeriv_apply (h : IsRetractVectorField E C O A)
    (R : ScRetraction E C) (hR : R.retract = O) {x : E 1} (hx : x ∈ E.lvlSet O 1) :
    scDeriv R.U R x (A x) = A x := by
  have h1 := h.mem_retractTangent hx
  rw [← hR, retractTangent_eq, R.mem_tangent_iff] at h1
  exact congrArg Prod.snd h1.2

/-- **The natural identification `T(O¹) = (TO)¹`** (p. 196, before Lemma 4.4.4), in a local model:
the tangent of the retract `O¹ ⊆ E¹` is the level-`1` part of the tangent `TO ⊆ TE`. -/
theorem retractTangent_shift (R : ScRetraction E C) :
    retractTangent E.shift (E.lvlSet C 1) (E.lvlSet R.retract 1) =
      E.tangent.lvlSet (retractTangent E C R.retract) 1 := by
  rw [← R.shift_retract, retractTangent_eq, retractTangent_eq]
  have hD := R.isSc1.isSc1With_scDeriv
  have hDs := hD.shift R.isScDomain
  ext p
  rw [R.shift.mem_tangent_iff, ScBanach.mem_lvlSet, R.mem_tangent_iff]
  have hmem : p ∈ E.shift.tangentSet R.shift.U ↔ E.tangent.toBase 1 p ∈ E.tangentSet R.U := by
    rw [ScBanach.tangent_toBase]; exact Iff.rfl
  rw [hmem]
  refine and_congr_right fun hp => ?_
  have hp1 : p.1 ∈ E.lvlSet R.U (1 + 1) := by
    rw [ScBanach.tangent_toBase] at hp
    change E.toBase 1 (E.shift.toBase 1 p.1) ∈ R.U at hp
    rw [← E.shift_toBase 1 p.1] at hp
    exact hp
  have key : E.tangent.toBase 1 (tangentMap R.shift.U R.shift p) =
      tangentMap R.U R (E.tangent.toBase 1 p) := by
    have hder : scDeriv R.shift.U R.shift p.1 = levelDeriv (scDeriv R.U R) 1 p.1 :=
      IsSc1.scDeriv_eqOn hDs (R.shift.isScDomain.uniqueDiffWithinAt 1) hp1
    rw [ScBanach.tangent_toBase, ScBanach.tangent_toBase]
    change ((E.shift.toBase 1 (levelMap R.shift 1 p.1),
        E.toBase 1 (scDeriv R.shift.U R.shift p.1 p.2)) : E.tangent 0) =
      (levelMap R 1 (E.shift.toBase 1 p.1), scDeriv R.U R (E.shift.toBase 1 p.1) (E.toBase 1 p.2))
    refine Prod.ext ?_ ?_
    · exact R.shift.isSc1.isSc0.toBase_levelMap hp1
    · rw [hder]
      exact hD.toBase_levelDeriv hp1 p.2
  constructor
  · intro h; rw [← key, h]
  · intro h; exact E.tangent.toBase_injective 1 (by rw [key, h])


/-- **Lemma 4.4.4, p. 196 (new in the 2021 edition)**, in a local model, `i = 1`: raising the index
of a vector field `A` on `(O, C, E)` gives the vector field `A₁ : E₂ → E₁` on `(O¹, C¹, E¹)`, a
section of `T(O¹) → O²`. -/
theorem IsRetractVectorField.shift (h : IsRetractVectorField E C O A) (hO : IsScRetract E C O) :
    IsRetractVectorField E.shift (E.lvlSet C 1) (E.lvlSet O 1)
      (levelMap (E := E.shift) (F := E) A 1) := by
  have H := IsScSmoothRetractMap.shift h hO.shift
  have h0 := IsScSmoothRetractMap.isSc0 h hO.shift
  obtain ⟨R, rfl⟩ := hO
  have hT : E.tangent.lvlSet (retractTangent E C R.retract) 1 =
      retractTangent E.shift (E.lvlSet C 1) (E.lvlSet R.retract 1) := (retractTangent_shift R).symm
  have hTC : E.tangent.lvlSet (E.tangentSet C) 1 = E.shift.tangentSet (E.lvlSet C 1) := by
    ext p; rfl
  rw [hT, hTC] at H
  refine H.congr fun x hx => ?_
  obtain ⟨q, hq⟩ := h0.mem_range 1 x hx
  have hq2 := congrArg Prod.snd hq
  change E.toBase 1 q.2 = A (E.shift.toBase 1 x) at hq2
  apply levelMap_eq_of_toBase_eq
  rw [ScBanach.tangent_toBase]
  refine Prod.ext rfl ?_
  change E.toBase 1 (levelMap (E := E.shift) (F := E) A 1 x) = A (E.shift.toBase 1 x)
  exact toBase_levelMap ⟨q.2, hq2⟩

end LocalVectorField


/-! ### The second derivative of an sc² map and its symmetry -/

section SecondDerivative

variable {E F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0}

/-- "`D²f(z)(a, b)`" for `z ∈ U₂` and `a, b ∈ E₁` (§4.5.1, p. 200): the second component of
`D(Tf)(z, a)(b, 0)`, the derivative of `z ↦ Df(z) a` in the direction `b`. -/
def scSecondDeriv (U : Set (E 0)) (f : E 0 → F 0) (z : E.shift 1) (a b : E 1) : F 0 :=
  (scDeriv (E.tangentSet U) (tangentMap U f) ((z, a) : E.tangent 1) ((b, 0) : E.tangent 0)).2

/-- `f : U₂ → F₀` has derivative `Df(z)|_{E₂}` at `z ∈ U₂`. -/
theorem hasFDerivWithinAt_two (hf : IsSc1 U f) {y : E 2} (hy : y ∈ E.lvlSet U 2) :
    HasFDerivWithinAt (f ∘ E.toBase 2) ((scDeriv U f (E.incl 1 y)).comp (E.toBase 2))
      (E.lvlSet U 2) y := by
  have h1 := hf.isSc1With_scDeriv.hasFDerivWithinAt (E.incl 1 y) hy
  have h2 := h1.comp y (E.incl 1).hasFDerivWithinAt (fun z hz => hz)
  exact h2.congr_fderiv (ContinuousLinearMap.ext fun _ => rfl)

/-- `z ↦ Df(z) a` (`a ∈ E₁`), as a map `U₂ → F₀`, has derivative `v ↦ D(Tf)(z, a)(v, 0)₂`. -/
theorem hasFDerivWithinAt_scDeriv_apply {DT : E.tangent 1 → E.tangent 0 →L[ℝ] F.tangent 0}
    (hT : IsSc1With (E.tangentSet U) (tangentMap U f) DT) {z : E 2} (hz : z ∈ E.lvlSet U 2)
    (a : E 1) :
    HasFDerivWithinAt (fun y : E 2 => scDeriv U f (E.incl 1 y) (E.toBase 1 a))
      ((ContinuousLinearMap.snd ℝ (F 1) (F 0)).comp ((DT ((z, a) : E.tangent 1)).comp
        ((E.tangent.toBase 1).comp (ContinuousLinearMap.inl ℝ (E.shift 1) (E 1)))))
      (E.lvlSet U 2) z := by
  have hza : ((z, a) : E.tangent 1) ∈ E.tangent.lvlSet (E.tangentSet U) 1 :=
    E.mem_lvlSet_tangentSet.2 hz
  have h1 := hT.hasFDerivWithinAt _ hza
  have hj : HasFDerivWithinAt (fun y : E.shift 1 => ((y, a) : E.tangent 1))
      (ContinuousLinearMap.inl ℝ (E.shift 1) (E 1)) (E.lvlSet U 2) z :=
    (((hasFDerivAt_id z).prodMk (hasFDerivAt_const a z)).congr_fderiv
      (by ext <;> simp)).hasFDerivWithinAt
  have h2 := h1.comp z hj (fun y hy => E.mem_lvlSet_tangentSet.2 hy)
  have h3 := (ContinuousLinearMap.snd ℝ (F 1) (F 0)).hasFDerivAt.comp_hasFDerivWithinAt z h2
  refine h3.congr (fun y _ => ?_) ?_
  · simp only [Function.comp_apply]; rfl
  · simp only [Function.comp_apply]; rfl

/-- On `E₂`-directions the sc second derivative is the classical second derivative of the `C²`
map `f : U₂ → F₀`. -/
theorem fderivWithin_fderivWithin_eq (hU : IsScDomain E U) (hf : IsSck 2 E F U f) {z : E 2}
    (hz : z ∈ E.lvlSet U 2) (v w : E 2) :
    fderivWithin ℝ (fderivWithin ℝ (f ∘ E.toBase 2) (E.lvlSet U 2)) (E.lvlSet U 2) z v w =
      scSecondDeriv U f z (E.incl 1 w) (E.incl 1 v) := by
  have hUD : UniqueDiffOn ℝ (E.lvlSet U 2) := fun y hy => hU.uniqueDiffWithinAt 2 y hy
  have hg2 : ContDiffOn ℝ (2 : ℕ) (f ∘ E.toBase 2) (E.lvlSet U 2) := hf.contDiffOn_base hU
  have hderiv : ∀ y ∈ E.lvlSet U 2, fderivWithin ℝ (f ∘ E.toBase 2) (E.lvlSet U 2) y =
      (scDeriv U f (E.incl 1 y)).comp (E.toBase 2) := fun y hy =>
    (hasFDerivWithinAt_two hf.1 hy).fderivWithin (hUD y hy)
  have hdiff : DifferentiableWithinAt ℝ (fderivWithin ℝ (f ∘ E.toBase 2) (E.lvlSet U 2))
      (E.lvlSet U 2) z :=
    ((hg2.fderivWithin hUD (m := 1) (by norm_num)).differentiableOn (by norm_num)) z hz
  have h1 := hdiff.hasFDerivWithinAt
  have h2 := (ContinuousLinearMap.apply ℝ (F 0) w).hasFDerivAt.comp_hasFDerivWithinAt z h1
  have hT := hf.2.1.isSc1With_scDeriv
  have h3 := hasFDerivWithinAt_scDeriv_apply hT hz (E.incl 1 w)
  have h3' : HasFDerivWithinAt
      (fun y => fderivWithin ℝ (f ∘ E.toBase 2) (E.lvlSet U 2) y w) _ (E.lvlSet U 2) z :=
    h3.congr (fun y hy => by rw [hderiv y hy]; rfl) (by rw [hderiv z hz]; rfl)
  have heq := congrArg (fun L => L v) ((hUD z hz).eq h2 h3')
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.inl_apply] at heq
  rw [heq, scSecondDeriv, ScBanach.tangent_toBase, map_zero]
  rfl

/-- A point of `U_m`, `U` relatively open in a partial quadrant, is in the closure of the
interior of `U_m`. -/
theorem IsRelOpenInQuadrant.mem_closure_interior_lvlSet {C : Set (E 0)}
    (hU : IsRelOpenInQuadrant E C U) {m : ℕ} {z : E m} (hz : z ∈ E.lvlSet U m) :
    z ∈ closure (interior (E.lvlSet U m)) := by
  have hC := hU.isPartialQuadrant
  obtain ⟨W, hW, rfl⟩ := hU.relOpen
  rw [ScBanach.lvlSet_inter] at hz ⊢
  have hWm := E.isOpen_lvlSet hW m
  have hcl : z ∈ closure (interior (E.lvlSet C m)) := by
    rw [(hC.convex_lvlSet m).closure_interior_eq_closure_of_nonempty_interior
      (hC.interior_lvlSet_nonempty m)]
    exact subset_closure hz.2
  refine closure_mono ?_ (hWm.inter_closure ⟨hz.1, hcl⟩)
  rw [interior_inter, hWm.interior_eq]

/-- **The symmetry of the second derivative** (§4.5.1, p. 200): for an sc² map `f` on a relatively
open subset `U` of a partial quadrant, `D²f(z)(a, b) = D²f(z)(b, a)` for `z ∈ U₂`, `a, b ∈ E₁`. -/
theorem scSecondDeriv_symm {C : Set (E 0)} (hU : IsRelOpenInQuadrant E C U)
    (hf : IsSck 2 E F U f) {z : E 2} (hz : z ∈ E.lvlSet U 2) (a b : E 1) :
    scSecondDeriv U f z a b = scSecondDeriv U f z b a := by
  have hUD : UniqueDiffOn ℝ (E.lvlSet U 2) := fun y hy => hU.isScDomain.uniqueDiffWithinAt 2 y hy
  have hsymm : IsSymmSndFDerivWithinAt ℝ (f ∘ E.toBase 2) (E.lvlSet U 2) z :=
    ((hf.contDiffOn_base hU.isScDomain) z hz).isSymmSndFDerivWithinAt
      (by simp [minSmoothness_of_isRCLikeNormedField]) hUD (hU.mem_closure_interior_lvlSet hz) hz
  have hdense : ∀ v w : E 2, scSecondDeriv U f z (E.incl 1 w) (E.incl 1 v) =
      scSecondDeriv U f z (E.incl 1 v) (E.incl 1 w) := fun v w => by
    rw [← fderivWithin_fderivWithin_eq hU.isScDomain hf hz,
      ← fderivWithin_fderivWithin_eq hU.isScDomain hf hz]
    exact hsymm v w
  have hT := hf.2.1.isSc1With_scDeriv
  have hcont : Continuous fun q : E 1 × E 1 => scSecondDeriv U f z q.1 q.2 := by
    have h2 : Continuous fun q : E 1 × E 1 =>
        ((((z, q.1) : E.tangent 1), ((q.2, 0) : E.tangent 0))) := by fun_prop
    exact continuous_snd.comp (hT.continuousOn_deriv.comp_continuous h2
      fun q => E.mem_lvlSet_tangentSet.2 hz)
  have hcont' : Continuous fun q : E 1 × E 1 => scSecondDeriv U f z q.2 q.1 :=
    hcont.comp continuous_swap
  have hd : Dense (range (Prod.map (E.incl 1) (E.incl 1))) :=
    (E.denseRange_incl 1).prodMap (E.denseRange_incl 1)
  have := hcont.ext_on hd hcont' (by rintro _ ⟨⟨w, v⟩, rfl⟩; exact hdense v w)
  exact congrFun this (a, b)

/-- The vertical part of `D(Tf)`: `D(Tf)(z, a)(0, l) = (0, Df(z) l)`. -/
theorem scDeriv_tangentMap_inr (hf : IsSck 2 E F U f) {p : E.tangent 1}
    (hp : p ∈ E.tangent.lvlSet (E.tangentSet U) 1) (l : E 0) :
    scDeriv (E.tangentSet U) (tangentMap U f) p ((0, l) : E.tangent 0) =
      ((0, scDeriv U f (E.incl 1 p.1) l) : F.tangent 0) := by
  have hT := hf.2.1.isSc1With_scDeriv
  have h1 := hT.hasFDerivWithinAt p hp
  have hj : HasFDerivAt (fun m : E 1 => ((p.1, m) : E.tangent 1))
      (ContinuousLinearMap.inr ℝ (E.shift 1) (E 1)) p.2 :=
    ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)).congr_fderiv (by ext <;> simp)
  have h2 := h1.comp p.2 hj.hasFDerivWithinAt (s := univ)
    (fun m _ => E.mem_lvlSet_tangentSet.2 (E.mem_lvlSet_tangentSet.1 hp))
  have h2' := hasFDerivWithinAt_univ.1 h2
  set L := scDeriv U f (E.incl 1 p.1)
  have h4 : HasFDerivAt (fun m : E 1 => ((levelMap f 1 (E.incl 1 p.1), L (E.toBase 1 m)) :
      F.tangent 0)) ((ContinuousLinearMap.inr ℝ (F 1) (F 0)).comp (L.comp (E.toBase 1))) p.2 :=
    ((hasFDerivAt_const _ p.2).prodMk (L.comp (E.toBase 1)).hasFDerivAt).congr_fderiv
      (by ext <;> simp)
  have h4' : HasFDerivAt ((tangentMap U f ∘ E.tangent.toBase 1) ∘
      fun m : E 1 => ((p.1, m) : E.tangent 1))
      ((ContinuousLinearMap.inr ℝ (F 1) (F 0)).comp (L.comp (E.toBase 1))) p.2 :=
    h4.congr_of_eventuallyEq (Eventually.of_forall fun m => by
      simp only [Function.comp_apply]; rfl)
  have heq := h2'.unique h4'
  have hd : DenseRange (E.toBase 1) := E.denseRange_inclK 0 1
  have := hd.equalizer
    ((scDeriv (E.tangentSet U) (tangentMap U f) p).comp
      (ContinuousLinearMap.inr ℝ (E 1) (E 0))).continuous
    ((ContinuousLinearMap.inr ℝ (F 1) (F 0)).comp L).continuous
    (funext fun m => by
      have hm : scDeriv (E.tangentSet U) (tangentMap U f) p
          (E.tangent.toBase 1 ((0, m) : E.tangent 1)) = ((0, L (E.toBase 1 m)) : F.tangent 0) :=
        congrArg (fun T => T m) heq
      rw [ScBanach.tangent_toBase, map_zero] at hm
      exact hm)
  exact congrFun this l

end SecondDerivative

/-! ### The Lie bracket in a local model (§4.5.1, Proposition 4.4.5) -/

section LieBracket

variable {C : Set (E 0)} {A B : E 1 → E 0}

/-- **The Lie bracket** (§4.5.1, p. 200) of the principal parts `A`, `B` in a local model, with a
retraction `r` onto `O`: `[A, B](x) = DÃ(x) B(x) − DB̃(x) A(x)` for `x ∈ E₂`, where `Ã = A ∘ r¹`
and `B(x) = B₁(x) ∈ E₁`. -/
def retractLieBracket (R : ScRetraction E C) (A B : E 1 → E 0) (x : E.shift 1) : E 0 :=
  scDeriv (E := E.shift) (F := E) R.shift.U (A ∘ R.shift) x
      (levelMap (E := E.shift) (F := E) B 1 x) -
    scDeriv (E := E.shift) (F := E) R.shift.U (B ∘ R.shift) x
      (levelMap (E := E.shift) (F := E) A 1 x)

/-- `[A, B] = −[B, A]`. -/
theorem retractLieBracket_antisymm (R : ScRetraction E C) (A B : E 1 → E 0) (x : E.shift 1) :
    retractLieBracket R A B x = -retractLieBracket R B A x :=
  (neg_sub _ _).symm

/-- `(A ∘ r¹)₁ = A₁` on `O²`. -/
theorem levelMap_comp_shift_eq (R : ScRetraction E C)
    (hAs : IsScSmooth (E := E.shift) (F := E) R.shift.U (A ∘ R.shift)) {x : E.shift 1}
    (hx : x ∈ E.shift.lvlSet (E.lvlSet R.retract 1) 1) :
    levelMap (E := E.shift) (F := E) (A ∘ R.shift) 1 x =
      levelMap (E := E.shift) (F := E) A 1 x := by
  have hρx : R.shift (E.shift.toBase 1 x) = E.shift.toBase 1 x :=
    R.shift.apply_eq_self_of_mem_retract (by rw [R.shift_retract]; exact hx)
  have hx1 : x ∈ E.shift.lvlSet R.shift.U 1 := E.lvlSet_mono R.retract_subset 2 hx
  have hr := (hAs 0 : IsSc0 E.shift E R.shift.U (A ∘ R.shift)).mem_range 1 x hx1
  symm
  apply levelMap_eq_of_toBase_eq
  rw [toBase_levelMap hr, Function.comp_apply, hρx]

/-- The identity `A(x) = Dr(x) A(x)` differentiated at `x ∈ O₂` in a direction `b ∈ T_x(O¹)`
(§4.5.1, p. 200): `D²r(x)(A(x), b) + Dr(x) DÃ(x) b = DÃ(x) b`. -/
theorem IsRetractVectorField.diff_identity {R : ScRetraction E C}
    (h : IsRetractVectorField E C R.retract A) {x : E.shift 1}
    (hx : x ∈ E.shift.lvlSet (E.lvlSet R.retract 1) 1) {b : E 1}
    (hb : scDeriv (E := E.shift) (F := E.shift) R.shift.U R.shift x b = b) :
    scSecondDeriv R.U R x (levelMap (E := E.shift) (F := E) A 1 x) b +
        scDeriv R.U R (E.incl 1 x) (scDeriv (E := E.shift) (F := E) R.shift.U (A ∘ R.shift) x b) =
      scDeriv (E := E.shift) (F := E) R.shift.U (A ∘ R.shift) x b := by
  set ρ := R.shift with hρ
  have hα : IsScSmooth ρ.U (scPair (E := E.shift) (F := E.shift) (G := E) ρ (A ∘ ρ)) :=
    h.comp_isScSmooth ρ (by rw [R.shift_retract])
  have hρs : IsScSmooth ρ.U ρ := ρ.isScSmooth
  have hAs : IsScSmooth (E := E.shift) (F := E) ρ.U (A ∘ ρ) := h.isScSmooth_comp R rfl
  have hx1 : x ∈ E.shift.lvlSet ρ.U 1 := E.lvlSet_mono R.retract_subset 2 hx
  have hDα : scDeriv ρ.U (scPair (E := E.shift) (F := E.shift) (G := E) ρ (A ∘ ρ)) x =
      (scDeriv ρ.U ρ x).prod (scDeriv ρ.U (A ∘ ρ) x) :=
    IsSc1.scDeriv_eqOn ((hρs 1).1.isSc1With_scDeriv.scPair (hAs 1).1.isSc1With_scDeriv)
      (ρ.isScDomain.uniqueDiffWithinAt 1) hx1
  have hT : IsSc1 (E.tangentSet R.U) (tangentMap R.U R) := (R.isScSmooth 2).2.1
  have hmaps : MapsTo (scPair (E := E.shift) (F := E.shift) (G := E) ρ (A ∘ ρ)) ρ.U
      (E.tangentSet R.U) := fun y hy => ρ.mapsTo hy
  have hfix : EqOn (tangentMap R.U R ∘ scPair (E := E.shift) (F := E.shift) (G := E) ρ (A ∘ ρ))
      (scPair (E := E.shift) (F := E.shift) (G := E) ρ (A ∘ ρ)) ρ.U := fun y hy => by
    have hyO : ρ y ∈ E.lvlSet R.retract 1 := by
      rw [← R.shift_retract]; exact ρ.mapsTo_retract hy
    have hmem := h.mapsTo hyO
    rw [retractTangent_eq] at hmem
    exact (R.mem_tangent_iff.1 hmem).2
  obtain ⟨hTα, hchain⟩ := theorem_1_21' ρ.isScDomain R.isScDomain.tangentSet (hα 1).1 hT hmaps
  have hcongr := hTα.tangentMap_congr ρ.isScDomain hfix
  have hq : ((x, b) : E.shift.tangent 0) ∈ E.shift.tangentSet ρ.U := hx1
  have key := congrArg Prod.snd ((hchain hq).symm.trans (hcongr hq))
  change scDeriv (E.tangentSet R.U) (tangentMap R.U R)
      (levelMap (scPair (E := E.shift) (F := E.shift) (G := E) ρ (A ∘ ρ)) 1 x)
      (scDeriv ρ.U (scPair (E := E.shift) (F := E.shift) (G := E) ρ (A ∘ ρ)) x b) =
    scDeriv ρ.U (scPair (E := E.shift) (F := E.shift) (G := E) ρ (A ∘ ρ)) x b at key
  have hlev : levelMap (scPair (E := E.shift) (F := E.shift) (G := E) ρ (A ∘ ρ)) 1 x =
      ((x, levelMap (E := E.shift) (F := E) A 1 x) : E.tangent 1) := by
    rw [IsSc0.levelMap_scPair (hρs 0) (hAs 0) hx1, levelMap_comp_shift_eq R hAs hx,
      ρ.levelMap_one_eq_self (by rw [R.shift_retract]; exact hx)]
  rw [hlev, hDα, ContinuousLinearMap.prod_apply, hb] at key
  have hsplit : ((b, scDeriv ρ.U (A ∘ ρ) x b) : E.tangent 0) =
      ((b, 0) : E.tangent 0) + ((0, scDeriv ρ.U (A ∘ ρ) x b) : E.tangent 0) := by
    simp
  have hp : ((x, levelMap (E := E.shift) (F := E) A 1 x) : E.tangent 1) ∈
      E.tangent.lvlSet (E.tangentSet R.U) 1 :=
    E.mem_lvlSet_tangentSet.2 (E.lvlSet_mono R.retract_subset 2 hx)
  rw [hsplit, map_add, scDeriv_tangentMap_inr (R.isScSmooth 2) hp] at key
  have key2 := congrArg Prod.snd key
  simp only [Prod.snd_add, zero_add] at key2
  exact key2

/-- **§4.5.1, p. 200 (new in the 2021 edition)**: the Lie bracket is tangent to `O`,
`Dr(x)[A, B](x) = [A, B](x)` for `x ∈ O₂`. -/
theorem retractLieBracket_mem_tangent {R : ScRetraction E C}
    (hA : IsRetractVectorField E C R.retract A) (hB : IsRetractVectorField E C R.retract B)
    {x : E.shift 1} (hx : x ∈ E.shift.lvlSet (E.lvlSet R.retract 1) 1) :
    scDeriv R.U R (E.incl 1 x) (retractLieBracket R A B x) = retractLieBracket R A B x := by
  have hBs := (hB.shift R.isScRetract).scDeriv_apply R.shift R.shift_retract hx
  have hAs := (hA.shift R.isScRetract).scDeriv_apply R.shift R.shift_retract hx
  have h1 := hA.diff_identity hx hBs
  have h2 := hB.diff_identity hx hAs
  have hsym := scSecondDeriv_symm R.relOpen (R.isScSmooth 2) (z := x)
    (R.retract_subset hx) (levelMap (E := E.shift) (F := E) A 1 x)
    (levelMap (E := E.shift) (F := E) B 1 x)
  unfold retractLieBracket
  rw [map_sub, eq_sub_of_add_eq' h1, eq_sub_of_add_eq' h2, hsym]
  abel


/-- `B₁ ∘ r² = (B ∘ r¹)₁` on `U²`. -/
theorem levelMap_shift_shift_eq {R : ScRetraction E C} {x : E.shift.shift 0}
    (hx : x ∈ R.shift.shift.U) :
    levelMap (E := E.shift) (F := E) B 1 (R.shift.shift x) =
      levelMap (E := E.shift) (F := E) (B ∘ R.shift) 1 x := by
  change Function.invFun (E.toBase 1) (B (E.shift.toBase 1 (levelMap R.shift 1 x))) =
    Function.invFun (E.toBase 1) ((B ∘ R.shift) (E.shift.toBase 1 x))
  rw [R.shift.isSc1.isSc0.toBase_levelMap hx]
  rfl

/-- `x ↦ DÃ(r²(x)) (B ∘ r¹)₁(x)` is sc-smooth on `U²`. -/
theorem isScSmooth_scDeriv_apply {R : ScRetraction E C}
    (hA : IsScSmooth (E := E.shift) (F := E) R.shift.U (A ∘ R.shift))
    (hB : IsScSmooth (E := E.shift) (F := E) R.shift.U (B ∘ R.shift)) :
    IsScSmooth (E := E.shift.shift) (F := E) R.shift.shift.U fun x =>
      scDeriv (E := E.shift) (F := E) R.shift.U (A ∘ R.shift) (R.shift.shift x)
        (levelMap (E := E.shift) (F := E) (B ∘ R.shift) 1 x) := by
  set ρ := R.shift
  have hpair : IsScSmooth (E := E.shift.shift) (F := E.shift.tangent) ρ.shift.U
      (scPair (E := E.shift.shift) (F := E.shift.shift) (G := E.shift) ρ.shift
        (levelMap (E := E.shift) (F := E) (B ∘ ρ) 1)) :=
    ρ.shift.isScSmooth.scPair ρ.shift.isScDomain (hB.shift ρ.isScDomain)
  have hTA : IsScSmooth (E := E.shift.tangent) (F := E.tangent) (E.shift.tangentSet ρ.U)
      (tangentMap ρ.U (A ∘ ρ)) := fun k => (hA (k + 1)).2
  have hmaps : MapsTo (scPair (E := E.shift.shift) (F := E.shift.shift) (G := E.shift) ρ.shift
      (levelMap (E := E.shift) (F := E) (B ∘ ρ) 1)) ρ.shift.U (E.shift.tangentSet ρ.U) :=
    fun x hx => ρ.shift.mapsTo hx
  have hcomp := IsScSmooth.comp ρ.shift.isScDomain ρ.isScDomain.tangentSet hTA hpair hmaps
  exact hcomp.snd ρ.shift.isScDomain

/-- **Proposition 4.4.5, p. 196** (2017: Proposition 4.5; preprint: Proposition 4.26), in a local
model: for vector fields `A`, `B` on `(O, C, E)`, `x ↦ (x, [A, B](x))` maps `O₂` into `TO` and is
sc-smooth from `(O², C², E²)` to `(TO, TC, TE)`: `[A, B]` is an sc-smooth section of
`TO|O² → O²`. -/
theorem proposition_4_4_5_local_2021 {R : ScRetraction E C}
    (hA : IsRetractVectorField E C R.retract A) (hB : IsRetractVectorField E C R.retract B) :
    (∀ x ∈ E.shift.lvlSet (E.lvlSet R.retract 1) 1,
      ((E.incl 1 x, retractLieBracket R A B x) : E.tangent 0) ∈ retractTangent E C R.retract) ∧
    IsScSmoothRetractMap E.shift.shift (E.shift.lvlSet (E.lvlSet C 1) 1)
      (E.shift.lvlSet (E.lvlSet R.retract 1) 1) E.tangent (E.tangentSet C)
      (retractTangent E C R.retract)
      (fun x => ((E.incl 1 x, retractLieBracket R A B x) : E.tangent 0)) := by
  have h1 : ∀ x ∈ E.shift.lvlSet (E.lvlSet R.retract 1) 1,
      ((E.incl 1 x, retractLieBracket R A B x) : E.tangent 0) ∈ retractTangent E C R.retract := by
    intro x hx
    have hx' : E.incl 1 x ∈ E.lvlSet R.retract 1 := hx
    rw [retractTangent_eq, R.mem_tangent_iff_of_mem hx']
    exact retractLieBracket_mem_tangent hA hB hx
  refine ⟨h1, ?_⟩
  rw [isScSmoothRetractMap_iff_exists R.isScRetract.shift.shift]
  refine ⟨h1, R.shift.shift, by rw [R.shift.shift_retract, R.shift_retract], ?_⟩
  set ρ := R.shift
  have hAs := hA.isScSmooth_comp R rfl
  have hBs := hB.isScSmooth_comp R rfl
  have hU := ρ.shift.isScDomain
  have hfirst : IsScSmooth (E := E.shift.shift) (F := E.shift) ρ.shift.U
      (E.shift.shiftIncl 0 ∘ ρ.shift) :=
    IsScSmooth.comp hU (isScDomain_univ _) ((E.shift.shiftIncl).isScSmooth (isScDomain_univ _))
      ρ.shift.isScSmooth (mapsTo_univ _ _)
  have hsecond : IsScSmooth (E := E.shift.shift) (F := E) ρ.shift.U
      (retractLieBracket R A B ∘ ρ.shift) := by
    refine ((isScSmooth_scDeriv_apply hAs hBs).sub hU (isScSmooth_scDeriv_apply hBs hAs)).congr hU
      fun x hx => ?_
    simp only [Function.comp_apply, retractLieBracket]
    rw [levelMap_shift_shift_eq hx, levelMap_shift_shift_eq hx]
  exact hfirst.scPair hU hsecond

end LieBracket

/-! ### Definition 4.4.3 on an M-polyfold -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

variable (P) in
/-- **Definition 4.4.3, p. 195 (new in the 2021 edition)**: an sc-smooth vector field on the
M-polyfold `X` is an sc-smooth section `A : X¹ → TX` of `p : TX → X¹`. -/
def IsScVectorField [ParacompactSpace P.TangentSpace] [ParacompactSpace (P.Level 1)]
    (A : P.Level 1 → P.TangentSpace) : Prop :=
  P.shift.IsScSmoothMap P.tangentPolyfold A ∧ ∀ x, P.tangentProj (A x) = x

/-- The zero tangent vector at `x ∈ X₁`, in a chart chosen around `x`. -/
def zeroTangentPre (x : P.Level 1) : P.TangentPre where
  x := P.levelVal 1 x
  φ := (P.exists_isChart_mem_source (P.levelVal 1 x)).choose
  h := 0
  isChart := (P.exists_isChart_mem_source _).choose_spec.1
  mem_source := (P.exists_isChart_mem_source _).choose_spec.2
  mem_level := P.levelVal_mem x
  mem_tangent := by
    have hφ := (P.exists_isChart_mem_source (P.levelVal 1 x)).choose_spec
    refine mk_zero_mem_retractTangent (MChart.model _).isScRetract ?_
    rw [ScBanach.mem_lvlSet, P.toBase_levelLift hφ.1 hφ.2 (P.levelVal_mem x)]
    exact MChart.mapsTo_model _ _ hφ.2

variable (P) in
/-- The zero section `X¹ → TX`. -/
def zeroVectorField (x : P.Level 1) : P.TangentSpace := TangentSpace.mk (zeroTangentPre x)

/-- The zero vector, seen in any chart `ψ` around `x`, is `(ψ(x), 0)`. -/
theorem zeroTangentPre_transport (x : P.Level 1) {ψ : MChart X} (hψ : P.IsChart ψ)
    (hx : P.levelVal 1 x ∈ ψ.source) :
    (zeroTangentPre x).transport ψ = (levelLift ψ 1 (P.levelVal 1 x), 0) := by
  set p := zeroTangentPre (P := P) x
  refine Prod.ext (p.transport_fst hψ hx) ?_
  have hcomp := (p.isChart.compatible hψ (P := P)).1
  obtain ⟨R, hR⟩ := p.φ.isScRetract_overlap ψ
  have hmem : p.vec ∈ retractTangent p.φ.model.E p.φ.model.C (p.φ.overlap ψ) :=
    p.vec_mem_image inter_subset_left (p.φ.isOpen_source.inter ψ.isOpen_source) ⟨p.mem_source, hx⟩
  rw [TangentPre.transport, retractTangentMap_apply hcomp R hR hmem]
  exact map_zero _

/-- `Tψ(0_x) = (ψ(x), 0)`. -/
theorem tangentChartMap_zeroVectorField (x : P.Level 1) {ψ : MChart X} (hψ : P.IsChart ψ)
    (hx : P.levelVal 1 x ∈ ψ.source) :
    tangentChartMap hψ (P.zeroVectorField x) = (levelLift ψ 1 (P.levelVal 1 x), 0) := by
  rw [zeroVectorField, tangentChartMap_mk hψ hx]
  exact zeroTangentPre_transport x hψ hx

/-- The zero section is continuous. -/
theorem continuous_zeroVectorField : Continuous P.zeroVectorField := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨ψ, hψ, W, hW, rfl⟩
  have hW' : IsOpen {z : ψ.model.E 1 | ((z, 0) : ψ.model.E.tangent 0) ∈ W} :=
    hW.preimage (by fun_prop)
  convert P.isOpen_level_basic hψ hW' using 1
  ext x
  simp only [mem_preimage, mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rwa [tangentChartMap_zeroVectorField x hψ h1] at h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rwa [tangentChartMap_zeroVectorField x hψ h1]⟩

/-- Satisfiability of `IsScVectorField`: the zero section is an sc-smooth vector field. -/
theorem isScVectorField_zero [ParacompactSpace P.TangentSpace] [ParacompactSpace (P.Level 1)] :
    P.IsScVectorField P.zeroVectorField := by
  refine ⟨?_, fun x => P.level_ext rfl⟩
  refine IsScSmoothOn.of_exists_charts isOpen_univ continuous_zeroVectorField.continuousOn
    fun x _ => ?_
  obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source (P.levelVal 1 x)
  refine ⟨levelChart hφ x, tangentChart hφ (P.zeroVectorField x), {y | P.levelVal 1 y ∈ φ.source},
    P.shift_isChart hφ x, P.tangentPolyfold_isChart hφ _, (levelChart hφ x).isOpen_source, hxφ,
    fun y hy => ⟨mem_univ _, hy⟩, fun y hy => hy, ?_⟩
  have himg : levelChart hφ x '' {y | P.levelVal 1 y ∈ φ.source} =
      φ.model.E.lvlSet φ.model.O 1 := (levelChart hφ x).image_source
  rw [himg]
  refine (isRetractVectorField_zero φ.model.isScRetract).congr fun z hz => ?_
  change ((z, 0) : φ.model.E.tangent 0) =
    tangentChartMap hφ (P.zeroVectorField ((levelChart hφ x).symm z))
  have hz' : φ.model.E.toBase 1 z ∈ φ.model.O := hz
  have hsrc : P.levelVal 1 ((levelChart hφ x).symm z) ∈ φ.source := by
    rw [levelChart_symm_apply hφ x hz']; exact φ.symm_mapsTo hz'
  rw [tangentChartMap_zeroVectorField _ hφ hsrc]
  refine Prod.ext ?_ rfl
  have := (levelChart hφ x).apply_symm_apply hz
  exact this.symm

end MPolyfold

end Polyfold
