import Polyfold.Examples.OrbifoldSquare
import Polyfold.Examples.PointCountFiniteSupport
import Polyfold.Examples.ConstantFormClosed

/-!
# The orbifold `ℂ/ℤ₅` and the section `z ↦ z²`: the count as a sum over two orbits

A worked example for Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021),
Theorem 16.6.6, 2021 p. 739, for Fredholm index `0`, with Definition 9.5.6 (p. 439).

## What is formalized (namespace `Polyfold.Examples.OrbifoldSquare`)

* `sqEval τ z`: the value of a `0`-form `τ` on `ℂ/ℤ₅` at `z ∈ ℂ`, read in the model.
* `card_isotropy_of_isRegular`: `♯G_z = 1` at a point with trivial isotropy.
* **`count_t5`**: for `r ≠ 0` and a perturbed solution set `Q` of the five-branch multisection
  `λ_{r²}` with the canonical orientation of `(f, o)`, the count is
  `w(r) · τ(r) + w(−r) · τ(−r)`, where `w(z) = signedWeight (T̂ z)` is the signed weight of the
  canonical orientation `T̂` at `z` (`EpGroupoid.signedWeight`): the orbit support is the two
  points `|r|`, `|−r|`, with trivial isotropy.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold.Examples.OrbifoldSquare

open TrivialBundle EpGroupoid EpGroupoid.Examples StrongPolyfoldBundle
  StrongPolyfoldBundleStructure SBLocalization PolyfoldClass

/-- The value of a `0`-form on `ℂ/ℤ₅` at `z ∈ ℂ`, read in the model `ℤ/5 ⋉ ℂ`. -/
def sqEval (τ : ScForm sqBundle.polyfold 0) (z : Fin 2 → ℝ) : ℝ :=
  A5.baseEP.zeroFormEval
    (ScForm.toStructure sqStructure.toPolyfoldStructure (toPolyfoldStructure_mem rfl) τ) z

/-- `♯G_z = 1` at a point with trivial isotropy. -/
theorem card_isotropy_of_isRegular {x : Fin 2 → ℝ} (h : X5.IsRegular x) :
    Nat.card (X5.Isotropy x) = 1 :=
  Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (h a).trans (h b).symm⟩, ⟨1⟩⟩

set_option maxHeartbeats 1600000 in
-- the model of the orientation is unfolded to `A5`
/-- **The count of the five-branch multisection as a sum over its two orbits** (Definition
9.5.6 (1) for `n = 0`): for `r ≠ 0`, a perturbed solution set `Q` of `λ_{r²}` with the canonical
orientation of `(f, o)` is the class of a point solution set `(Λ, T̂)` of the model with
`Λ = Λ5 (r²)` and `T̂` canonical, and its count of a `0`-form `τ` is
`signedWeight (T̂ r) · τ(r) + signedWeight (T̂ (−r)) · τ(−r)`. -/
theorem count_t5 {r : ℂ} (hr : r ≠ 0) {Q : PointOrientedPerturbation sqFredholmSection.1}
    (ht : Q.t = t5 (r ^ 2)) (hcan : IsCanonicalPointSolutionSet sqOrientationRep Q)
    (τ : ScForm sqBundle.polyfold 0) :
    ∃ P : PointSolution A5 sqSection, P.Λ = Λ5 (r ^ 2) ∧
      IsCanonicalFor P.Λ sqOrientationRep.hF.2 sqOrientationRep.hsec sqOrientationRep.o 0 P.T ∧
      Q.count τ = signedWeight (X := X5) (P.T (cE.symm r)) * sqEval τ (cE.symm r) +
        signedWeight (X := X5) (P.T (cE.symm (-r))) * sqEval τ (cE.symm (-r)) := by
  classical
  obtain ⟨P, hP, rfl⟩ := hcan
  have hΛ : P.Λ = Λ5 (r ^ 2) := by
    have h1 := congrArg ScPlusMultisection.toFun ht
    funext w
    have ca := (ofFunctor sqStructure rfl P.Λ P.isScPlusMultisection).comm w
    have cb := (ofFunctor sqStructure rfl (Λ5 (r ^ 2)) (isScPlusMultisection_Λ5 _)).comm w
    exact ca.symm.trans ((congrFun h1 _).trans cb)
  refine ⟨P, hΛ, hP, ?_⟩
  have hc2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hne : cE.symm r ≠ cE.symm (-r) := fun h => π_ne_π_neg hr (congrArg X5.π h)
  have hpos : ∀ x ∈ ({(cE.symm r : A5.Obj), (cE.symm (-r) : A5.Obj)} : Finset A5.Obj),
      0 < P.Λ (sqSection x) := by
    intro x hx
    rw [hΛ]
    rcases Finset.mem_insert.1 hx with h | h
    · exact (Λ5_sqSection_pos_iff_orbit r x).2 (Or.inl ⟨1, by rw [h, one_smul]⟩)
    · replace h := Finset.mem_singleton.1 h
      exact (Λ5_sqSection_pos_iff_orbit r x).2 (Or.inr ⟨1, by rw [h, one_smul]⟩)
  have hinj : Set.InjOn A5.X.π
      (↑({(cE.symm r : A5.Obj), (cE.symm (-r) : A5.Obj)} : Finset A5.Obj) : Set A5.Obj) := by
    intro x hx y hy hxy
    rcases Finset.mem_insert.1 (Finset.mem_coe.1 hx) with h | h <;>
      rcases Finset.mem_insert.1 (Finset.mem_coe.1 hy) with h' | h'
    · exact h.trans h'.symm
    · replace h' := Finset.mem_singleton.1 h'
      rw [h, h'] at hxy
      exact absurd hxy (π_ne_π_neg hr)
    · replace h := Finset.mem_singleton.1 h
      rw [h, h'] at hxy
      exact absurd hxy.symm (π_ne_π_neg hr)
    · replace h := Finset.mem_singleton.1 h
      replace h' := Finset.mem_singleton.1 h'
      exact h.trans h'.symm
  have hcov : ∀ y, 0 < P.Λ (sqSection y) →
      ∃ x ∈ ({(cE.symm r : A5.Obj), (cE.symm (-r) : A5.Obj)} : Finset A5.Obj),
        A5.X.π x = A5.X.π y := by
    intro y hy
    rw [hΛ] at hy
    rcases (Λ5_sqSection_pos_iff_orbit r y).1 hy with ⟨g, hg⟩ | ⟨g, hg⟩
    · exact ⟨_, Finset.mem_insert_self _ _,
        (action_π_eq_π_iff isScSmoothMap_smul).2 ⟨g, hg.symm⟩⟩
    · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
        (action_π_eq_π_iff isScSmoothMap_smul).2 ⟨g, hg.symm⟩⟩
  have hreg : ∀ x ∈ ({(cE.symm r : A5.Obj), (cE.symm (-r) : A5.Obj)} : Finset A5.Obj),
      Nat.card (X5.Isotropy x) = 1 := fun x hx =>
    card_isotropy_of_isRegular (isRegular_of_Λ5_pos hc2 (by rw [← hΛ]; exact hpos x hx))
  refine (count_solutionPointSuborbifold (c := sqBundle) sqOrientationRep.a P
    τ).trans ?_
  refine (P.count_eq_sum _ _ hpos hinj hcov).trans ?_
  have key : ∀ x : A5.Obj, Nat.card (X5.Isotropy x) = 1 →
      ((Nat.card (sqOrientationRep.a.S.A.X.Isotropy x) : ℕ) : ℝ)⁻¹ *
        (signedWeight (P.T x) * sqOrientationRep.a.S.A.baseEP.zeroFormEval
          (ScForm.toStructure sqOrientationRep.a.S.toPolyfoldStructure
            (toPolyfoldStructure_mem sqOrientationRep.a.hS) τ) x) =
      signedWeight (X := X5) (P.T x) * sqEval τ x := fun x h => by
    have h' : Nat.card (sqOrientationRep.a.S.A.X.Isotropy x) = 1 := h
    rw [h', Nat.cast_one, inv_one, one_mul]
    rfl
  let F : A5.Obj → ℝ := fun x =>
    ((Nat.card (sqOrientationRep.a.S.A.X.Isotropy x) : ℕ) : ℝ)⁻¹ *
      (signedWeight (P.T x) * sqOrientationRep.a.S.A.baseEP.zeroFormEval
        (ScForm.toStructure sqOrientationRep.a.S.toPolyfoldStructure
          (toPolyfoldStructure_mem sqOrientationRep.a.hS) τ) x)
  have k1 : F (cE.symm r) = signedWeight (X := X5) (P.T (cE.symm r)) * sqEval τ (cE.symm r) :=
    key _ (hreg _ (Finset.mem_insert_self _ _))
  have k2 : F (cE.symm (-r)) =
      signedWeight (X := X5) (P.T (cE.symm (-r))) * sqEval τ (cE.symm (-r)) :=
    key _ (hreg _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  have hsum : ∑ x ∈ ({(cE.symm r : A5.Obj), (cE.symm (-r) : A5.Obj)} : Finset A5.Obj), F x =
      F (cE.symm r) + F (cE.symm (-r)) := Finset.sum_pair hne
  rw [k1, k2] at hsum
  exact hsum

/-! ### The constant form `1` and the reduction of the value `2/5` to the signs -/

/-- **The constant `0`-form `1` on `ℂ/ℤ₅`.** -/
def sqOne : ScForm sqBundle.polyfold 0 :=
  ScForm.mk sqStructure.toPolyfoldStructure (toPolyfoldStructure_mem rfl)
    (sqStructure.toPolyfoldStructure.X.constFormInfty 1)

/-- The constant form `1` is closed. -/
theorem d_sqOne : ScForm.d sqOne = 0 := by
  have h : sqStructure.toPolyfoldStructure.X.epFormsInftyD 0
      (sqStructure.toPolyfoldStructure.X.constFormInfty 1) = 0 :=
    sqStructure.toPolyfoldStructure.X.epFormsInftyD_constFormInfty 1
  rw [sqOne, ScForm.d_mk, h]
  have h0 := ScForm.mk_toStructure (c := sqBundle.polyfold) sqStructure.toPolyfoldStructure
    (toPolyfoldStructure_mem rfl) (0 : ScForm sqBundle.polyfold (0 + 1))
  rw [ScForm.toStructure_zero] at h0
  exact h0

/-- The constant form `1` has the value `1` at every point. -/
theorem sqEval_sqOne (z : Fin 2 → ℝ) : sqEval sqOne z = 1 := by
  have h := ScForm.toStructure_mk sqStructure.toPolyfoldStructure
    (toPolyfoldStructure_mem (c := sqBundle) rfl)
    (sqStructure.toPolyfoldStructure.X.constFormInfty 1)
  have h1 : sqEval sqOne z = sqStructure.toPolyfoldStructure.X.zeroFormEval
      (sqStructure.toPolyfoldStructure.X.constFormInfty 1) z :=
    congrArg (fun ω => sqStructure.toPolyfoldStructure.X.zeroFormEval ω z) h
  exact h1.trans (sqStructure.toPolyfoldStructure.X.zeroFormEval_constFormInfty 1
    (mem_smoothSet_A5 z))

/-- **The zeros of `z² − ζ^{2j} c` are positive for the orientation `sqOrientationRep`**: for
every canonically oriented point solution set of the five-branch multisection `Λ5 (r²)`, the
signed weight of the canonical orientation at the perturbed solution `r` is `+1/5`.  This holds
for exactly one of the two continuous orientations of `f` (the complex one); it is not proved
here for `sqOrientation`, which is one of the two, chosen by `Classical.choose`. -/
def PositiveZeros : Prop :=
  ∀ (P : PointSolution A5 sqSection) (r : ℂ), r ≠ 0 → P.Λ = Λ5 (r ^ 2) →
    IsCanonicalFor P.Λ sqOrientationRep.hF.2 sqOrientationRep.hsec sqOrientationRep.o 0 P.T →
    signedWeight (X := X5) (P.T (cE.symm r)) = 1 / 5

/-- **The value `2/5`, given the signs** (Theorem 16.6.6, 2021 p. 739, index `0`): if the
perturbed zeros are positive for the orientation (`PositiveZeros`), then every admissible
perturbation with the canonical orientation of `(f, o)` has count `2/5` on the constant form
`1`: two orbits of weight `1/5` with trivial isotropy. -/
theorem count_eq_two_fifths_of_positiveZeros (hpos : PositiveZeros)
    {Q : PointOrientedPerturbation sqFredholmSection.1}
    (a : Q.IsAdmissible n5 (univ : Set A5.X.OrbitSpace))
    (hcan : IsCanonicalPointSolutionSet sqOrientationRep Q) : Q.count sqOne = 2 / 5 := by
  obtain ⟨Q₁, ht₁, a₁, c₁⟩ := exists_canonical_t5 (c := 1) one_ne_zero (by rw [norm_one])
  have ht : Q₁.t = t5 ((1 : ℂ) ^ 2) := by rw [one_pow]; exact ht₁
  obtain ⟨P, hΛ, hP, hcount⟩ := count_t5 one_ne_zero ht c₁ sqOne
  have hΛ' : P.Λ = Λ5 ((-1 : ℂ) ^ 2) := by rw [hΛ]; norm_num
  have w1 := hpos P 1 one_ne_zero hΛ hP
  have w2 := hpos P (-1) (neg_ne_zero.2 one_ne_zero) hΛ' hP
  rw [(count_eq_of_isAdmissible a hcan a₁ c₁ sqOne d_sqOne).1, hcount, w1, w2, sqEval_sqOne,
    sqEval_sqOne]
  norm_num

end Polyfold.Examples.OrbifoldSquare
