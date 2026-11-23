import Polyfold.Examples.OrbifoldSquareInfOrientation

/-!
# The count `2/5` on `(ℂ × H)/ℤ₅`: the worked example in infinite dimensions

For Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), **Theorem 16.6.6**,
2021 p. 739, for Fredholm index `0`.

## The example

`H` is the weighted `ℓ²` sc-Hilbert space with levels `H_m = {x | ∑ (k+1)^{2m} x_k² < ∞}`
(`WeightedEllTwo.lean`): the levels are strictly nested and the inclusions compact.  `G = ℤ/5`
acts on `ℂ × H` by `g · (z, e) = (ζ^g z, e)`; the ep-groupoid is `(ℤ/5 ⋉ ℂ) × H`, with isotropy
`ℤ/5` along `{0} × H` and trivial isotropy elsewhere.  The strong bundle has the fibre `ℂ × H`
over `(z, e)`, with `ℤ/5` acting on the `ℂ` of the fibre with weight `2`, and the double
filtration of `H ◁ H`.  The section is `f(z, e) = (z², e)`: sc-Fredholm of index `0`, with
solution set `{(0, 0)}`, and `f'(0, 0) = (0, id)`.

## What is formalized (namespace `Polyfold.Examples.OrbifoldSquareInf`)

* `subSec_branchInf`: `f − s_j = f + (−s_j)` for the branches `s_j(z, e) = (ζ^{2j} c, 0)`.
* **`signedWeight_canonical_eq_inf`**: for the canonical orientation of `(f, o)`,
  `o = infOrientationPos`, the perturbed zero `(r, 0)` of the five-branch multisection
  `Λinf (r²)` has signed weight `+1/5`.
* `infEval`, `count_tinf_pos`: the count of a `0`-form over the perturbed solution set of
  `λ_{r²}` is the sum over the two orbits of `(r, 0)` and `(−r, 0)`.
* `infOne`, `d_infOne`, `infEval_infOne`: the constant form `1`.
* **`count_eq_two_fifths_inf`**: every admissible perturbation with the canonical orientation
  has count `2/5` on the constant form `1`; `count_eq_two_fifths_inf_all`.
* `exists_not_mem_smoothSet`: not every point of `ℂ × H` is smooth.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.OrbifoldSquareInf

open TrivialBundle EpGroupoid EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure StrongBundleEquivalenceExamples
  StrongBundleLocalizationExamples SBLocalization StrongRetr WeightedEllTwo OrbifoldSquare
  PolyfoldClass

/-! ### The signs of the perturbed zeros -/

/-- `f − s_j = f + (−s_j)` for the branch `s_j(z, e) = ((z, b), (e, 0))`. -/
theorem subSec_branchInf (c : ℂ) (j : ZMod 5) :
    subSec (A := Ainf) sqInf (branchInf c j) univ =
      sectionAdd Ainf.P sqInf (negConstInf (branchVal c j)) := by
  have hsec : IsSection Ainf.P (branchInf c j) := (isScPlusSection_branchInf c j).1
  have he : extendZero (A := Ainf) univ (branchInf c j) = branchInf c j :=
    funext fun y => (extendZero_eqOn (A := Ainf) (fun y _ => hsec y) (mem_univ y)).symm
  unfold subSec
  rw [he]
  congr 1
  funext x
  obtain ⟨z, e⟩ : (Fin 2 → ℝ) × HObj := x
  refine (sectionSmul_apply hsec ((z, e) : Ainf.Obj)).trans ?_
  let PH' : HObj × H 0 → HObj := LocalBundle.proj (E := H) (U := (univ : Set (H 0))) (F := H)
  let Φ := prodFiberCLE (proj 2 2) PH' ((z, e) : (Fin 2 → ℝ) × HObj)
  let v : Prod.map (proj 2 2) PH' ⁻¹' {((z, e) : (Fin 2 → ℝ) × HObj)} :=
    ⟨branchInf c j ((z, e) : Ainf.Obj), rfl⟩
  change ((((-1 : ℝ) • v : Prod.map (proj 2 2) PH' ⁻¹' {((z, e) : (Fin 2 → ℝ) × HObj)}) :
    ((Fin 2 → ℝ) × (Fin 2 → ℝ)) × (HObj × H 0))) = ((z, -branchVal c j), (e, (0 : H 0)))
  have hΦ : Φ ((-1 : ℝ) • v) = (-1 : ℝ) • Φ v := map_smul Φ _ _
  have h1 : (((Φ ((-1 : ℝ) • v)).1 : proj 2 2 ⁻¹' {z}) : (Fin 2 → ℝ) × (Fin 2 → ℝ)) =
      (z, -branchVal c j) := by
    refine (congrArg Subtype.val (congrArg Prod.fst hΦ)).trans ?_
    refine Prod.ext (fst_fiber _) ?_
    refine (snd_smul _ _).trans ?_
    change (-1 : ℝ) • branchVal c j = -branchVal c j
    rw [neg_one_smul]
  have h2 : (((Φ ((-1 : ℝ) • v)).2 : PH' ⁻¹' {e}) : HObj × H 0) = (e, (0 : H 0)) := by
    refine (congrArg Subtype.val (congrArg Prod.snd hΦ)).trans ?_
    have h0' : (Φ v).2 = 0 := by
      apply (LocalBundle.fibEquiv (F := H) e).injective
      exact ((LocalBundle.fibEquiv (F := H) e).linearEquiv ℝ).map_zero.symm
    have hs : ((-1 : ℝ) • Φ v).2 = 0 := by
      change (-1 : ℝ) • (Φ v).2 = 0
      rw [h0', smul_zero]
    refine (congrArg Subtype.val hs).trans ?_
    refine Prod.ext rfl ?_
    exact ((LocalBundle.fibEquiv (F := H) e).linearEquiv ℝ).map_zero
  exact Prod.ext h1 h2

/-- **The perturbed zero `(r, 0)` of the five-branch multisection has signed weight `+1/5`** for
the canonical orientation of `(f, infOrientationPos)`: the orientation is positive at
`(f − s_j)'(r, 0) = (2r, id)`, and exactly one of the five branches passes through `(r, 0)`. -/
theorem signedWeight_canonical_eq_inf {r : ℂ} (hr : r ≠ 0)
    {T : Ainf.Obj → Ainf.X.PObj.OrTangent →₀ ℚ}
    (h : IsCanonicalFor (Λinf (r ^ 2)) infOrientationRepPos.hF.2 infOrientationRepPos.hsec
      infOrientationRepPos.o 0 T) :
    signedWeight (X := Ainf.X) (T ((cE.symm r, h0) : (Fin 2 → ℝ) × HObj)) = 1 / 5 := by
  classical
  have hf := isScFredholmSectionFunctor_sqInf.2
  have hc : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hy0 : (cE.symm r : Fin 2 → ℝ) ≠ 0 := fun h0 => hr (cE.symm.map_eq_zero_iff.1 h0)
  have hsq := sq_symm_eq_branchVal_zero r
  have hex : (∃ j : ZMod 5, OrbifoldSquare.sq
      ((cE.symm r, h0) : (Fin 2 → ℝ) × HObj).1 = branchVal (r ^ 2) j) ∧
      ((cE.symm r, h0) : (Fin 2 → ℝ) × HObj).2 = h0 := ⟨⟨0, hsq⟩, rfl⟩
  have hpos : 0 < Λinf (r ^ 2) (sqInf ((cE.symm r, h0) : (Fin 2 → ℝ) × HObj)) :=
    (Λinf_sqInf_pos_iff (r ^ 2) _).2 hex
  have hy : (((cE.symm r, h0) : (Fin 2 → ℝ) × HObj) : Ainf.Obj) ∈
      EpGroupoid.supp (fun z : Ainf.Obj => ((Λinf (r ^ 2) (sqInf z) : ℚ≥0) : ℚ)) := by
    change (0 : ℚ) < _
    exact_mod_cast hpos
  have hys := mem_smoothSet_mk_h0 (cE.symm r)
  have key := IsCanonicalFor.signedWeight_eq h hy hys isOpen_univ (mem_univ _)
    (isLocalRepOn_Λinf (r ^ 2)) (fun j : Fin 5 => negConstInf (branchVal (r ^ 2) j))
    (fun j => isScPlusSection_negConstInf _)
    (fun j x' _ => congrFun (subSec_branchInf (r ^ 2) j).symm x')
    (fun j hj => by
      have hj' : sqInf ((cE.symm r, h0) : (Fin 2 → ℝ) × HObj) =
          branchInf (r ^ 2) j ((cE.symm r, h0) : (Fin 2 → ℝ) × HObj) := hj.symm
      have e : OrbifoldSquare.sq (cE.symm r) = branchVal (r ^ 2) j :=
        congrArg (fun w : ((Fin 2 → ℝ) × (Fin 2 → ℝ)) × (HObj × H 0) => w.1.2) hj'
      refine ⟨(isZeroAt_negConstInf_iff (x := ((cE.symm r, h0) : (Fin 2 → ℝ) × HObj))).2
        ⟨e, rfl⟩, ?_⟩
      exact (isPosOr_congr hf hys _ (congrArg negConstInf e) (isScPlusSection_negConstInf _)
        (isScPlusSection_negConstInf _) (isZeroAt_negConstInf _)
        ((isZeroAt_negConstInf_iff (x := ((cE.symm r, h0) : (Fin 2 → ℝ) × HObj))).2
          ⟨e, rfl⟩)).1 (isPosAtInf_infOrientationPos hy0))
  have e : Λinf (r ^ 2) (sqInf ((cE.symm r, h0) : (Fin 2 → ℝ) × HObj)) = 1 / 5 :=
    (Λinf_sqInf_eq hc _).trans (if_pos hex)
  refine key.trans ?_
  change (((Λinf (r ^ 2) (sqInf ((cE.symm r, h0) : (Fin 2 → ℝ) × HObj)) : ℚ≥0) : ℚ) : ℝ) = 1 / 5
  rw [e]
  norm_num

/-! ### The count as a sum over two orbits -/

/-- The value of a `0`-form on `(ℂ × H)/ℤ₅` at a point of `ℂ × H`, read in the model. -/
def infEval (τ : ScForm infBundle.polyfold 0) (x : Ainf.Obj) : ℝ :=
  Ainf.baseEP.zeroFormEval
    (ScForm.toStructure infStructure.toPolyfoldStructure (toPolyfoldStructure_mem rfl) τ) x

/-- The point `(r, 0)` of `ℂ × H`. -/
def pt (r : ℂ) : Ainf.Obj := ((cE.symm r, h0) : (Fin 2 → ℝ) × HObj)

theorem π_pt_ne {r : ℂ} (hr : r ≠ 0) : Ainf.X.π (pt r) ≠ Ainf.X.π (pt (-r)) :=
  π_ne_π_neg_inf hr

theorem Λinf_pos_pt (r : ℂ) : 0 < Λinf (r ^ 2) (sqInf (pt r)) :=
  (Λinf_sqInf_pos_iff_orbit r ((cE.symm r, h0) : (Fin 2 → ℝ) × HObj)).2
    (Or.inl ⟨1, by rw [one_smul]⟩)

theorem Λinf_pos_pt_neg (r : ℂ) : 0 < Λinf (r ^ 2) (sqInf (pt (-r))) :=
  (Λinf_sqInf_pos_iff_orbit r ((cE.symm (-r), h0) : (Fin 2 → ℝ) × HObj)).2
    (Or.inr ⟨1, by rw [one_smul]⟩)

/-- Every perturbed solution lies in the orbit of `(r, 0)` or of `(−r, 0)`. -/
theorem π_eq_of_Λinf_pos (r : ℂ) {y : Ainf.Obj} (hy : 0 < Λinf (r ^ 2) (sqInf y)) :
    Ainf.X.π (pt r) = Ainf.X.π y ∨ Ainf.X.π (pt (-r)) = Ainf.X.π y := by
  rcases (Λinf_sqInf_pos_iff_orbit r (y : (Fin 2 → ℝ) × HObj)).1 hy with ⟨g, hg⟩ | ⟨g, hg⟩
  · exact Or.inl ((π_eq_π_iff (x := ((cE.symm r, h0) : (Fin 2 → ℝ) × HObj))
      (y := (y : (Fin 2 → ℝ) × HObj))).2 ⟨g, (congrArg Prod.fst hg).symm,
        (congrArg Prod.snd hg).symm⟩)
  · exact Or.inr ((π_eq_π_iff (x := ((cE.symm (-r), h0) : (Fin 2 → ℝ) × HObj))
      (y := (y : (Fin 2 → ℝ) × HObj))).2 ⟨g, (congrArg Prod.fst hg).symm,
        (congrArg Prod.snd hg).symm⟩)

theorem card_isotropy_of_Λinf_pos {c : ℂ} (hc : c ≠ 0) {x : Ainf.Obj}
    (hx : 0 < Λinf c (sqInf x)) : Nat.card (Ainf.X.Isotropy x) = 1 :=
  card_isotropy_of_ne_zero (x := (x : (Fin 2 → ℝ) × HObj))
    (isRegular_Xinf_iff.1 (isRegular_of_Λinf_pos hc (x := (x : (Fin 2 → ℝ) × HObj)) hx))

set_option maxHeartbeats 1600000 in
-- the model of the orientation is unfolded to `Ainf`
/-- **The count of the five-branch multisection as a sum over its two orbits** (Definition
9.5.6 (1) for `n = 0`): for `r ≠ 0`, a perturbed solution set `Q` of `λ_{r²}` with the canonical
orientation of `(f, o)`, `o = infOrientationPos`, is the class of a point solution set `(Λ, T̂)`
of the model with `Λ = Λinf (r²)` and `T̂` canonical, and its count of a `0`-form `τ` is
`signedWeight (T̂ (r, 0)) · τ(r, 0) + signedWeight (T̂ (−r, 0)) · τ(−r, 0)`. -/
theorem count_tinf_pos {r : ℂ} (hr : r ≠ 0)
    {Q : PointOrientedPerturbation infFredholmSection.1}
    (ht : Q.t = tinf (r ^ 2)) (hcan : IsCanonicalPointSolutionSet infOrientationRepPos Q)
    (τ : ScForm infBundle.polyfold 0) :
    ∃ P : PointSolution Ainf sqInf, P.Λ = Λinf (r ^ 2) ∧
      IsCanonicalFor P.Λ infOrientationRepPos.hF.2 infOrientationRepPos.hsec
        infOrientationRepPos.o 0 P.T ∧
      Q.count τ = signedWeight (X := Ainf.X) (P.T (pt r)) * infEval τ (pt r) +
        signedWeight (X := Ainf.X) (P.T (pt (-r))) * infEval τ (pt (-r)) := by
  classical
  obtain ⟨P, hP, rfl⟩ := hcan
  have hΛ : P.Λ = Λinf (r ^ 2) := by
    have h1 := congrArg ScPlusMultisection.toFun ht
    funext w
    have ca := (ofFunctor infStructure rfl P.Λ P.isScPlusMultisection).comm w
    have cb := (ofFunctor infStructure rfl (Λinf (r ^ 2)) (isScPlusMultisection_Λinf _)).comm w
    exact ca.symm.trans ((congrFun h1 _).trans cb)
  refine ⟨P, hΛ, hP, ?_⟩
  have hc2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hne : pt r ≠ pt (-r) := fun h => π_pt_ne hr (congrArg Ainf.X.π h)
  have hpos : ∀ x ∈ ({pt r, pt (-r)} : Finset Ainf.Obj), 0 < P.Λ (sqInf x) := by
    intro x hx
    rw [hΛ]
    rcases Finset.mem_insert.1 hx with h | h
    · rw [h]; exact Λinf_pos_pt r
    · rw [Finset.mem_singleton.1 h]; exact Λinf_pos_pt_neg r
  have hinj : Set.InjOn Ainf.X.π (↑({pt r, pt (-r)} : Finset Ainf.Obj) : Set Ainf.Obj) := by
    intro x hx y hy hxy
    rcases Finset.mem_insert.1 (Finset.mem_coe.1 hx) with h | h <;>
      rcases Finset.mem_insert.1 (Finset.mem_coe.1 hy) with h' | h'
    · exact h.trans h'.symm
    · replace h' := Finset.mem_singleton.1 h'
      rw [h, h'] at hxy
      exact absurd hxy (π_pt_ne hr)
    · replace h := Finset.mem_singleton.1 h
      rw [h, h'] at hxy
      exact absurd hxy.symm (π_pt_ne hr)
    · replace h := Finset.mem_singleton.1 h
      replace h' := Finset.mem_singleton.1 h'
      exact h.trans h'.symm
  have hcov : ∀ y, 0 < P.Λ (sqInf y) →
      ∃ x ∈ ({pt r, pt (-r)} : Finset Ainf.Obj), Ainf.X.π x = Ainf.X.π y := by
    intro y hy
    rw [hΛ] at hy
    rcases π_eq_of_Λinf_pos r hy with h | h
    · exact ⟨_, Finset.mem_insert_self _ _, h⟩
    · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), h⟩
  have hreg : ∀ x ∈ ({pt r, pt (-r)} : Finset Ainf.Obj),
      Nat.card (Ainf.X.Isotropy x) = 1 := fun x hx =>
    card_isotropy_of_Λinf_pos hc2 (by rw [← hΛ]; exact hpos x hx)
  refine (count_solutionPointSuborbifold (c := infBundle) infOrientationRepPos.a P
    τ).trans ?_
  refine (P.count_eq_sum _ _ hpos hinj hcov).trans ?_
  have key : ∀ x : Ainf.Obj, Nat.card (Ainf.X.Isotropy x) = 1 →
      ((Nat.card (infOrientationRepPos.a.S.A.X.Isotropy x) : ℕ) : ℝ)⁻¹ *
        (signedWeight (P.T x) * infOrientationRepPos.a.S.A.baseEP.zeroFormEval
          (ScForm.toStructure infOrientationRepPos.a.S.toPolyfoldStructure
            (toPolyfoldStructure_mem infOrientationRepPos.a.hS) τ) x) =
      signedWeight (X := Ainf.X) (P.T x) * infEval τ x := fun x h => by
    have h' : Nat.card (infOrientationRepPos.a.S.A.X.Isotropy x) = 1 := h
    rw [h', Nat.cast_one, inv_one, one_mul]
    rfl
  let F : Ainf.Obj → ℝ := fun x =>
    ((Nat.card (infOrientationRepPos.a.S.A.X.Isotropy x) : ℕ) : ℝ)⁻¹ *
      (signedWeight (P.T x) * infOrientationRepPos.a.S.A.baseEP.zeroFormEval
        (ScForm.toStructure infOrientationRepPos.a.S.toPolyfoldStructure
          (toPolyfoldStructure_mem infOrientationRepPos.a.hS) τ) x)
  have k1 : F (pt r) = signedWeight (X := Ainf.X) (P.T (pt r)) * infEval τ (pt r) :=
    key _ (hreg _ (Finset.mem_insert_self _ _))
  have k2 : F (pt (-r)) = signedWeight (X := Ainf.X) (P.T (pt (-r))) * infEval τ (pt (-r)) :=
    key _ (hreg _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  have hsum : ∑ x ∈ ({pt r, pt (-r)} : Finset Ainf.Obj), F x = F (pt r) + F (pt (-r)) :=
    Finset.sum_pair hne
  rw [k1, k2] at hsum
  exact hsum

/-! ### The constant form `1` and the count `2/5` -/

/-- **The constant `0`-form `1` on `(ℂ × H)/ℤ₅`.** -/
def infOne : ScForm infBundle.polyfold 0 :=
  ScForm.mk infStructure.toPolyfoldStructure (toPolyfoldStructure_mem rfl)
    (infStructure.toPolyfoldStructure.X.constFormInfty 1)

/-- The constant form `1` is closed. -/
theorem d_infOne : ScForm.d infOne = 0 := by
  have h : infStructure.toPolyfoldStructure.X.epFormsInftyD 0
      (infStructure.toPolyfoldStructure.X.constFormInfty 1) = 0 :=
    infStructure.toPolyfoldStructure.X.epFormsInftyD_constFormInfty 1
  rw [infOne, ScForm.d_mk, h]
  have h0 := ScForm.mk_toStructure (c := infBundle.polyfold) infStructure.toPolyfoldStructure
    (toPolyfoldStructure_mem rfl) (0 : ScForm infBundle.polyfold (0 + 1))
  rw [ScForm.toStructure_zero] at h0
  exact h0

/-- The constant form `1` has the value `1` at the points `(z, 0)`. -/
theorem infEval_infOne (r : ℂ) : infEval infOne (pt r) = 1 := by
  have h := ScForm.toStructure_mk infStructure.toPolyfoldStructure
    (toPolyfoldStructure_mem (c := infBundle) rfl)
    (infStructure.toPolyfoldStructure.X.constFormInfty 1)
  have h1 : infEval infOne (pt r) = infStructure.toPolyfoldStructure.X.zeroFormEval
      (infStructure.toPolyfoldStructure.X.constFormInfty 1) (pt r) :=
    congrArg (fun η => infStructure.toPolyfoldStructure.X.zeroFormEval η (pt r)) h
  exact h1.trans (infStructure.toPolyfoldStructure.X.zeroFormEval_constFormInfty 1
    (mem_smoothSet_mk_h0 (cE.symm r)))

/-- **The count `2/5`** (Theorem 16.6.6, 2021 p. 739, index `0`), in the infinite-dimensional
example: every admissible perturbation of `|(z, e)| ↦ |(z², e)|` over `(ℂ × H)/ℤ₅` with the
canonical orientation of `(f, infOrientationPos)` has count `2/5` on the constant form `1`: for
`λ_1`, two orbits (`(1, 0)` and `(−1, 0)`) of weight `1/5`, trivial isotropy and sign `+1`. -/
theorem count_eq_two_fifths_inf {Q : PointOrientedPerturbation infFredholmSection.1}
    (a : Q.IsAdmissible ninf (univ : Set Ainf.X.OrbitSpace))
    (hcan : IsCanonicalPointSolutionSet infOrientationRepPos Q) : Q.count infOne = 2 / 5 := by
  obtain ⟨Q₁, ht₁, a₁, c₁⟩ := exists_canonical_tinf (c := 1) one_ne_zero (by rw [norm_one])
  have ht : Q₁.t = tinf ((1 : ℂ) ^ 2) := by rw [one_pow]; exact ht₁
  obtain ⟨P, hΛ, hP, hcount⟩ := count_tinf_pos one_ne_zero ht c₁ infOne
  have hΛ' : P.Λ = Λinf ((-1 : ℂ) ^ 2) := by rw [hΛ]; norm_num
  have w1 : signedWeight (X := Ainf.X) (P.T (pt 1)) = 1 / 5 :=
    signedWeight_canonical_eq_inf one_ne_zero (hΛ ▸ hP)
  have w2 : signedWeight (X := Ainf.X) (P.T (pt (-1))) = 1 / 5 :=
    signedWeight_canonical_eq_inf (neg_ne_zero.2 one_ne_zero) (hΛ' ▸ hP)
  rw [(count_eq_of_isAdmissible_inf a hcan a₁ c₁ infOne d_infOne).1, hcount, w1, w2,
    infEval_infOne, infEval_infOne]
  norm_num

/-- **The invariant of `|(z, e)| ↦ |(z², e)|` over `(ℂ × H)/ℤ₅` is `2/5`**: admissible
perturbations with the canonical orientation of `(f, infOrientationPos)` exist (the five-branch
multisections `λ_c`, `0 < |c| ≤ 1`), and every one of them has count `2/5` on the constant
form `1`. -/
theorem count_eq_two_fifths_inf_all :
    (∀ c : ℂ, c ≠ 0 → ‖c‖ ≤ 1 → ∃ Q : PointOrientedPerturbation infFredholmSection.1,
      Q.t = tinf c ∧ Q.IsAdmissible ninf (univ : Set Ainf.X.OrbitSpace) ∧
      IsCanonicalPointSolutionSet infOrientationRepPos Q) ∧
    ∀ Q : PointOrientedPerturbation infFredholmSection.1,
      Q.IsAdmissible ninf (univ : Set Ainf.X.OrbitSpace) →
      IsCanonicalPointSolutionSet infOrientationRepPos Q → Q.count infOne = 2 / 5 :=
  ⟨fun _ hc0 hc1 => exists_canonical_tinf hc0 hc1,
    fun _ a hcan => count_eq_two_fifths_inf a hcan⟩

/-! ### The levels differ -/

/-- **Not every point of `ℂ × H` is smooth**: `(0, (1/(k+1))_k)` lies on level `0` only. -/
theorem exists_not_mem_smoothSet : ∃ x : Ainf.Obj, x ∉ Ainf.X.PObj.smoothSet :=
  ⟨(((0 : Fin 2 → ℝ), hpt harmH) : (Fin 2 → ℝ) × HObj), fun h =>
    harmH_not_mem_smooth ((mem_smoothSet_Ainf_iff
      (x := (((0 : Fin 2 → ℝ), hpt harmH) : (Fin 2 → ℝ) × HObj))).1 h)⟩

end Polyfold.Examples.OrbifoldSquareInf
