import Polyfold.Chapter16.P3W4PB_ZeroSection
import Polyfold.Chapter14.P3W3B1_BoundaryStructured
import Polyfold.Chapter11.MultisectionLocalStructure2021
import Polyfold.Chapter12.P3S_CompactnessEp

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.5 "Sc⁺-Multisections" (pp. 732–735; 2017: §16.5): **Definitions 16.5.1, 16.5.2, Remark
16.5.3, (16.8), Definitions 16.5.4–16.5.6** and **Theorem 16.5.7** (as a reduction to Theorem
14.1.9).  Numbers and pages are the 2021 text's.

## The text, paraphrased

(D16.5.1) An sc⁺-multisection `λ : Y → ℚ⁺` of a strong polyfold bundle `(p, c̄)` is a class of
tuples `(λ, Γ, W, Λ)`: a structure of `c̄` and an sc⁺-multisection functor `Λ` with
`λ(Γ(|w|)) = Λ(w)`; `(λ, Γ, W, Λ) ∼ (λ', Γ', W', Λ')` if `λ = λ'` and a generalized strong bundle
isomorphism `f̄` (over `f`, with the square of orbit maps) has `Λ = f̄^*Λ'`.  (D16.5.2)
`dom-supp(λ)` is the closure of the `z` over which some `y` has `λ(y) > 0`.  (R16.5.3) A
representative gives a homeomorphism `|dom-supp(Λ)| → dom-supp(λ)`.  (16.8)
`n(λ)(z) = max{n(y) | p(y) = z, λ(y) ≠ 0}`, "a continuous map".  (D16.5.4) `λ` is structurable if
one, and therefore all, of its representatives are.  (D16.5.5) Over `∂Z`: classes of
`(λ, Γ, W, Λ)` with `Λ : W|∂X → ℚ⁺` an sc⁺-multisection functor (Definition 14.1.3), with
`λ = λ'`, `Λ = f̄^*Λ'` and `Γ' ∘ |f̄| = Γ`.  (D16.5.6) Structurable over `∂Z`: one representative
is (Definition 14.1.7).  (T16.5.7) Over a tame `Z` with sc-smooth partitions of unity, a
structurable `λ` over `∂Z`, `Ũ ⊇ dom-supp(λ)` open and `f ≥ 0` continuous with support in `Ũ`
and `n(λ) < f` on `dom-supp(λ)` give a structurable `λ'` with (1) `n(λ') ≤ f`,
(2) `dom-supp(λ') ⊆ Ũ`, (3) `λ'|(Y|∂Z) = λ`.

## What is formalized (namespace `Polyfold.StrongPolyfoldBundle`)

* D16.5.1: `MultisectionRep c`, `MultisectionRep.Rel` (as printed, with `f̄^* =
  GenSBMap.pullMult`), **`pullMult_eq_of_Γ`** (`Λ = f̄^*Λ'` holds for *every* `f̄` with
  `Γ' ∘ |f̄| = Γ`, so the condition does not depend on the choice of `f̄`), `rel_iff`,
  `Rel.refl/symm/trans`, `ScPlusMultisection c` (the quotient), `toFun` (`λ`), `ext_toFun`,
  `ofFunctor` (every sc⁺-multisection functor of a structure in `c̄` defines one), and
  **`exists_rep_of_mem`** (every structure of `c̄` carries a representative of every `λ`,
  Proposition 11.5.3).  Witness: `zero c`.
* D16.5.2: `domSupp` (with `y ≠ 0_z`, as in Definition 13.2.2) and the printed form
  `domSuppText`, which is all of `Z` (`domSuppText_eq_univ`).
* R16.5.3: `remark_16_5_3`: `γ(|dom-supp(Λ)|) = dom-supp(λ)` for every representative.
* (16.8): `normLam c n λ`, and `normLam_eq` (`n(λ)(γ|x|) = N(Λ)(x)` with `N = normOf n`).
* D16.5.4: `ScPlusMultisection.IsStructurable` (some representative) and
  `definition_16_5_4_hyp` ("therefore all", from `StructurablePullback`, the generalized
  isomorphism form of Theorems 13.4.1 and 13.4.3).
* D16.5.5: `BoundaryMultisectionRep c`, `Rel` (with `Λ = f̄^*Λ'` in orbit form over `∂X`),
  `rel_iff`, `BoundaryMultisection c`, `toFun` (`0` off `p⁻¹(∂Z)`), `domSupp`.
  D16.5.6: `BoundaryMultisection.IsStructurable`.
* T16.5.7: `theorem_16_5_7_hyp`, from Theorem 14.1.9 (`theorem_14_1_9_statement`) in the models;
  `theorem_16_5_7_hyp_witness`.

## Readings

* D16.5.2 as printed counts `y = 0_z`; since the weights over each fibre sum to `1`, that set is
  all of `Z` (`domSuppText_eq_univ`).  Presumably `y ≠ 0_z` is meant, as in Definition 13.2.2.
* R16.5.3 says `Γ`; the map between domain supports is `γ` (they lie in `Z` and `|X|`).
* D16.5.4 writes `λ : Z → ℚ⁺`; `λ : Y → ℚ⁺` is presumably meant.
* T16.5.7 "partitions of unity on `Z`" is read in the form Theorem 14.1.9 uses (sc-smooth
  partitions of unity of the object M-polyfold of the models, `PObj.AdmitsScPartitionsOfUnity`);
  "support in `Ũ`" is `tsupport f ⊆ Ũ`, as in `theorem_14_1_9_statement`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

open EPLocalization SBLocalization

/-- **Theorems 13.4.1 and 13.4.3 for generalized strong bundle isomorphisms**, as a statement:
the pull-back `[D]^*Λ' = Φ_* Ψ^* Λ'` of a structurable sc⁺-multisection functor is structurable
(Q's gaps Q-1, Q-3; the text before Definition 16.5.1 says this "follows immediately"). -/
def StructurablePullback : Prop :=
  ∀ (A A' : SEP.{u}) (F : GenSBMap A A') (hF : F.IsGeneralizedIso) (Λ' : A'.W → ℚ≥0),
    IsStructurable A' Λ' → IsStructurable A (GenSBMap.pullMult hF Λ')

namespace StrongPolyfoldBundleStructure

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}

/-- The map `x ↦ γ(|x|)`. -/
theorem continuous_γπ (S : StrongPolyfoldBundleStructure p) :
    Continuous fun x : S.A.Obj => S.γ (S.A.X.π x) :=
  S.γ.continuous.comp S.A.X.continuous_π

theorem surjective_γπ (S : StrongPolyfoldBundleStructure p) :
    Surjective fun x : S.A.Obj => S.γ (S.A.X.π x) :=
  S.γ.surjective.comp S.A.X.surjective_π

/-- The preimage of a set of `Z` under `x ↦ γ(|x|)` is saturated. -/
theorem isSaturated_preimage_γπ (S : StrongPolyfoldBundleStructure p) (V : Set Z) :
    S.A.X.IsSaturated ((fun x : S.A.Obj => S.γ (S.A.X.π x)) ⁻¹' V) := by
  change S.A.X.π ⁻¹' (S.A.X.π '' (S.A.X.π ⁻¹' (S.γ ⁻¹' V))) = S.A.X.π ⁻¹' (S.γ ⁻¹' V)
  rw [image_preimage_eq _ S.A.X.surjective_π]

/-- `p(Γ(|w|)) = γ(|P(w)|)`. -/
theorem p_Γ_π (S : StrongPolyfoldBundleStructure p) (w : S.A.W) :
    p (S.Γ (S.A.E.toEpGroupoid.π w)) = S.γ (S.A.X.π (S.A.P w)) :=
  S.p_Γ _

end StrongPolyfoldBundleStructure

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}

/-! ### Transport lemmas -/

/-- **`Λ = f̄^*Λ'` for every `f̄` with `Γ' ∘ |f̄| = Γ`**, when `Λ'` is a functor represented by
`λ` (`λ(Γ'(|w'|)) = Λ'(w')`). -/
theorem pullMult_eq_of_Γ {S S' : StrongPolyfoldBundleStructure p} {F : GenSBMap S.A S'.A}
    (hF : F.IsGeneralizedIso) (hΓ : ⇑S'.Γ ∘ F.orbitMap = ⇑S.Γ) {Λ' : S'.A.W → ℚ≥0}
    (hΛ' : IsWFunctor S'.A Λ') {lam : Y → ℚ≥0}
    (hcomm : ∀ w', lam (S'.Γ (S'.A.E.toEpGroupoid.π w')) = Λ' w') (w : S.A.W) :
    GenSBMap.pullMult hF Λ' w = lam (S.Γ (S.A.E.toEpGroupoid.π w)) := by
  obtain ⟨w', hw'⟩ := S'.A.E.toEpGroupoid.surjective_π
    ((GenSBMap.rep hF).orbitMap (S.A.E.toEpGroupoid.π w))
  have ho : (GenSBMap.rep hF).orbitMap = F.orbitMap := by
    rw [← GenSBMap.orbitMap_cls, GenSBMap.cls_rep]
  change (GenSBMap.rep hF).pullMult (GenSBMap.isEquivalence_rep_Ψ hF) Λ' w = _
  rw [SDiagram.pullMult_eq hΛ' hw'.symm, ← hcomm w', hw', ho, ← congrFun hΓ]
  rfl

/-- `γ(|x|) ∈ ∂Z` iff `x ∈ ∂X`. -/
theorem mem_boundary_iff_obj {c : StrongPolyfoldBundle p} {S : StrongPolyfoldBundleStructure p}
    (hS : ⟦S⟧ = c) (x : S.A.Obj) :
    S.γ (S.A.X.π x) ∈ c.polyfold.boundary ↔ x ∈ S.A.X.PObj.boundary := by
  rw [← hS]
  exact PolyfoldClass.mem_boundary_iff _ S.toPolyfoldStructure rfl rfl

/-- **`n(λ)` and `N(Λ)` have the same set of values** over `γ(|x|)` and `x`, for any `Λ`
represented by `λ` over `x` (`N = normOf n`, read as `0` off `W_{0,1}`). -/
theorem image_normY_eq {c : StrongPolyfoldBundle p} {S : StrongPolyfoldBundleStructure p}
    (hS : ⟦S⟧ = c) (n : Y → ℝ) (Λ : S.A.W → ℚ≥0) (lam : Y → ℚ≥0) (x : S.A.Obj)
    (hcomm : ∀ w, S.A.P w = x → lam (S.Γ (S.A.E.toEpGroupoid.π w)) = Λ w) :
    c.normY n '' {y | p y = S.γ (S.A.X.π x) ∧ 0 < lam y} =
      normW (S.normOf n) '' suppAt Λ x := by
  ext r
  constructor
  · rintro ⟨y, ⟨hy, hpos⟩, rfl⟩
    obtain ⟨ξ, rfl⟩ := S.Γ.surjective y
    obtain ⟨w', rfl⟩ := S.A.E.toEpGroupoid.surjective_π ξ
    rw [S.p_Γ_π] at hy
    obtain ⟨φ, hφs, hφt⟩ := (GroupoidStr.π_eq_π_iff _).1 (S.γ.injective hy)
    have hq : S.A.P w' = S.A.X.src φ := hφs.symm
    set w := S.A.E.μ ⟨(φ, w'), hq⟩
    have hPw : S.A.P w = x := (S.A.E.P_μ _).trans hφt
    have hπ : S.A.E.toEpGroupoid.π w = S.A.E.toEpGroupoid.π w' := EpStrongBundle.π_μ _ _
    refine ⟨w, ⟨hPw, ?_⟩, ?_⟩
    · rw [← hcomm w hPw, hπ]; exact hpos
    · rw [← normY_Γ hS, hπ]
  · rintro ⟨w, ⟨hPw, hpos⟩, rfl⟩
    refine ⟨S.Γ (S.A.E.toEpGroupoid.π w), ⟨?_, ?_⟩, normY_Γ hS n w⟩
    · rw [S.p_Γ_π, hPw]
    · rw [hcomm w hPw]; exact hpos

/-! ### (16.8) -/

/-- **(16.8), p. 733**: `n(λ)(z) = max{n(y) | y ∈ p⁻¹(z), λ(y) ≠ 0}` (a supremum; `n` is read as
`0` off `Y_{0,1}`, `normY`), for any `λ : Y → ℚ⁺`. -/
def normLam (c : StrongPolyfoldBundle p) (n : Y → ℝ) (lam : Y → ℚ≥0) (z : Z) : ℝ :=
  sSup (c.normY n '' {y | p y = z ∧ 0 < lam y})

/-- `n(λ)(γ(|x|)) = N(Λ)(x)` (Definition 13.2.3) for `Λ` represented by `λ` over `x`. -/
theorem normLam_eq {c : StrongPolyfoldBundle p} {S : StrongPolyfoldBundleStructure p}
    (hS : ⟦S⟧ = c) (n : Y → ℝ) (Λ : S.A.W → ℚ≥0) (lam : Y → ℚ≥0) (x : S.A.Obj)
    (hcomm : ∀ w, S.A.P w = x → lam (S.Γ (S.A.E.toEpGroupoid.π w)) = Λ w) :
    c.normLam n lam (S.γ (S.A.X.π x)) = pointwiseNorm (S.normOf n) Λ x := by
  unfold normLam pointwiseNorm
  rw [image_normY_eq hS n Λ lam x hcomm]

/-! ### Definition 16.5.1 -/

/-- **A representative `(λ, Γ, W, Λ)`** (2021 Definition 16.5.1, p. 733): a structure of `c̄`, an
sc⁺-multisection functor `Λ` (Definition 13.2.1) and `λ : Y → ℚ⁺` with `λ(Γ(|w|)) = Λ(w)`. -/
structure MultisectionRep (c : StrongPolyfoldBundle p) : Type (u + 1) where
  /-- The structure `((P : W → X, μ), Γ, γ)`. -/
  S : StrongPolyfoldBundleStructure p
  hS : ⟦S⟧ = c
  /-- The sc⁺-multisection functor `Λ : W → ℚ⁺`. -/
  Λ : S.A.W → ℚ≥0
  isScPlusMultisection : IsScPlusMultisection S.A Λ
  /-- `λ : Y → ℚ⁺`. -/
  lam : Y → ℚ≥0
  /-- `λ ∘ Γ(|w|) = Λ(w)`. -/
  comm : ∀ w, lam (S.Γ (S.A.E.toEpGroupoid.π w)) = Λ w

variable {c : StrongPolyfoldBundle p}

namespace MultisectionRep

/-- **The relation of Definition 16.5.1**: `λ = λ'` and a generalized strong bundle isomorphism
`f̄ : W → W'` (covering `f`, with the square of orbit maps, `Γ' ∘ |f̄| = Γ`) has `Λ = f̄^*Λ'`. -/
def Rel (a b : MultisectionRep c) : Prop :=
  a.lam = b.lam ∧ ∃ (F : GenSBMap a.S.A b.S.A) (hF : F.IsGeneralizedIso),
    ⇑b.S.Γ ∘ F.orbitMap = ⇑a.S.Γ ∧ a.Λ = GenSBMap.pullMult hF b.Λ

/-- **`∼` is "same `λ` and equivalent structures"**: the condition `Λ = f̄^*Λ'` holds for every
`f̄` with `Γ' ∘ |f̄| = Γ` (`pullMult_eq_of_Γ`). -/
theorem rel_iff (a b : MultisectionRep c) : Rel a b ↔ a.lam = b.lam ∧ Equiv a.S b.S := by
  refine ⟨fun ⟨hl, F, hF, hΓ, _⟩ => ⟨hl, equiv_iff_exists_Γ.2 ⟨F, hF, hΓ⟩⟩, fun ⟨hl, h⟩ => ?_⟩
  obtain ⟨F, hF, hΓ⟩ := equiv_iff_exists_Γ.1 h
  refine ⟨hl, F, hF, hΓ, funext fun w => ?_⟩
  rw [pullMult_eq_of_Γ hF hΓ b.isScPlusMultisection.1 b.comm, ← hl, a.comm]

theorem rel_of_lam_eq (a b : MultisectionRep c) (h : a.lam = b.lam) : Rel a b :=
  (rel_iff a b).2 ⟨h, Quotient.exact (a.hS.trans b.hS.symm)⟩

/-- The relation of Definition 16.5.1 is an equivalence relation. -/
instance setoid (c : StrongPolyfoldBundle p) : Setoid (MultisectionRep c) where
  r := Rel
  iseqv := ⟨fun a => rel_of_lam_eq a a rfl, fun h => rel_of_lam_eq _ _ h.1.symm,
    fun h h' => rel_of_lam_eq _ _ (h.1.trans h'.1)⟩

end MultisectionRep

/-- **2021 Definition 16.5.1, p. 733 (2017: Definition 16.35)**: an **sc⁺-multisection**
`λ : Y → ℚ⁺` of the strong polyfold bundle `(p, c̄)`: a class `[(λ, Γ, W, Λ)]`. -/
abbrev ScPlusMultisection (c : StrongPolyfoldBundle p) : Type (u + 1) :=
  Quotient (MultisectionRep.setoid c)

namespace ScPlusMultisection

/-- The function `λ : Y → ℚ⁺` of an sc⁺-multisection (well defined). -/
def toFun (s : ScPlusMultisection c) : Y → ℚ≥0 :=
  Quotient.lift MultisectionRep.lam (fun _ _ h => (h : MultisectionRep.Rel _ _).1) s

@[simp] theorem toFun_mk (a : MultisectionRep c) : ScPlusMultisection.toFun (c := c) ⟦a⟧ = a.lam :=
  rfl

/-- Two sc⁺-multisections with the same `λ` are equal. -/
theorem ext_toFun {s t : ScPlusMultisection c} (h : s.toFun = t.toFun) : s = t := by
  induction s using Quotient.inductionOn with | h a => ?_
  induction t using Quotient.inductionOn with | h b => ?_
  exact Quotient.sound (MultisectionRep.rel_of_lam_eq a b h)

end ScPlusMultisection

/-- **Every sc⁺-multisection functor of a structure in `c̄` defines an sc⁺-multisection**:
`λ(y) = Λ(w)` for any `w` with `Γ(|w|) = y`. -/
def ofFunctor (S : StrongPolyfoldBundleStructure p) (hS : ⟦S⟧ = c) (Λ : S.A.W → ℚ≥0)
    (hΛ : IsScPlusMultisection S.A Λ) : MultisectionRep c where
  S := S
  hS := hS
  Λ := Λ
  isScPlusMultisection := hΛ
  lam y := Λ (S.Γ.symm y).out
  comm w := by
    refine hΛ.1.eq_of_π_eq ?_
    rw [Homeomorph.symm_apply_apply]
    exact Quotient.out_eq _

/-- **Every structure of `c̄` carries a representative of every sc⁺-multisection** (Proposition
11.5.3: `f̄^*` maps sc⁺-multisection functors to sc⁺-multisection functors). -/
theorem exists_rep_of_mem (s : ScPlusMultisection c) {S : StrongPolyfoldBundleStructure p}
    (hS : ⟦S⟧ = c) : ∃ a : MultisectionRep c, ⟦a⟧ = s ∧ a.S = S := by
  obtain ⟨b, rfl⟩ := Quotient.exists_rep s
  obtain ⟨F, hF, hΓ⟩ := equiv_iff_exists_Γ.1 (Quotient.exact (hS.trans b.hS.symm))
  have hpull := (GenSBMap.proposition_11_5_3_book hF).2.1 b.Λ b.isScPlusMultisection
  have e : GenSBMap.pullMult hF b.Λ = fun w => b.lam (S.Γ (S.A.E.toEpGroupoid.π w)) :=
    funext (pullMult_eq_of_Γ hF hΓ b.isScPlusMultisection.1 b.comm)
  refine ⟨⟨S, hS, _, hpull, b.lam, fun w => (congrFun e w).symm⟩, ?_, rfl⟩
  exact Quotient.sound (MultisectionRep.rel_of_lam_eq _ _ rfl)

/-- **Nonvacuity of Definition 16.5.1**: the trivial multisection (`λ = 1` on the zero section,
`0` elsewhere). -/
def zero (c : StrongPolyfoldBundle p) : ScPlusMultisection c :=
  ⟦ofFunctor c.out (Quotient.out_eq c) (zeroMultisection c.out.A)
    (isScPlusMultisection_zeroMultisection c.out.A)⟧

/-! ### Definition 16.5.2 and Remark 16.5.3 -/

namespace ScPlusMultisection

/-- **2021 Definition 16.5.2, p. 733 (2017: Definition 16.36)**, read with `y ≠ 0_z` as in
Definition 13.2.2: `dom-supp(λ) = cl_Z{z ∈ Z | ∃ y ∈ p⁻¹(z) ∖ {0_z}, λ(y) > 0}`. -/
def domSupp (s : ScPlusMultisection c) : Set Z :=
  closure {z | ∃ y, p y = z ∧ y ≠ c.zeroAt z ∧ 0 < s.toFun y}

/-- Definition 16.5.2 as printed (`y = 0_z` allowed). -/
def domSuppText (s : ScPlusMultisection c) : Set Z :=
  closure {z | ∃ y, p y = z ∧ 0 < s.toFun y}

/-- **The printed Definition 16.5.2 gives all of `Z`**: over every `z` some `y` has `λ(y) > 0`
(the weights over a fibre sum to `1`). -/
theorem domSuppText_eq_univ (s : ScPlusMultisection c) : s.domSuppText = univ := by
  induction s using Quotient.inductionOn with | h a => ?_
  refine eq_univ_of_forall fun z => subset_closure ?_
  obtain ⟨x, rfl⟩ := a.S.surjective_γπ z
  obtain ⟨w, hw, hpos⟩ := a.isScPlusMultisection.suppAt_nonempty x
  refine ⟨a.S.Γ (a.S.A.E.toEpGroupoid.π w), ?_, ?_⟩
  · rw [a.S.p_Γ_π, hw]
  · rw [toFun_mk, a.comm]; exact hpos

end ScPlusMultisection

/-- The set `{x | ∃ w ∈ W_x ∖ {0}, Λ(w) > 0}` whose closure is `dom-supp(Λ)`. -/
def nzSet {A : SEP.{u}} (Λ : A.W → ℚ≥0) : Set A.Obj :=
  {x | ∃ w, A.P w = x ∧ w ≠ fiberZero A.P x ∧ 0 < Λ w}

/-- For a functor `Λ`, `{x | ∃ w ∈ W_x ∖ {0}, Λ(w) > 0}` is saturated. -/
theorem isSaturated_nzSet {A : SEP.{u}} {Λ : A.W → ℚ≥0} (hΛ : IsWFunctor A Λ) :
    A.X.IsSaturated (nzSet Λ) := by
  refine (subset_preimage_image _ _).antisymm' ?_
  rintro x ⟨x', ⟨w', hw', hw'0, hpos⟩, hxx'⟩
  obtain ⟨φ, hφs, hφt⟩ := (GroupoidStr.π_eq_π_iff _).1 hxx'
  have hq : A.P w' = A.X.src φ := hw'.trans hφs.symm
  refine ⟨A.E.μ ⟨(φ, w'), hq⟩, (A.E.P_μ _).trans hφt, ?_, ?_⟩
  · have := μ_ne_fiberZero (A := A) ⟨(φ, w'), hq⟩ (by rw [hw']; exact hw'0)
    rwa [show A.P (A.E.μ ⟨(φ, w'), hq⟩) = x from (A.E.P_μ _).trans hφt] at this
  · rw [hΛ]; exact hpos

/-- `dom-supp(λ)` before the closure is the image of the corresponding set of `X`. -/
theorem image_nzSet (a : MultisectionRep c) :
    (fun x => a.S.γ (a.S.A.X.π x)) '' nzSet a.Λ =
      {z | ∃ y, p y = z ∧ y ≠ c.zeroAt z ∧ 0 < ScPlusMultisection.toFun (c := c) ⟦a⟧ y} := by
  rw [zeroAt_eq_of_mem a.hS]
  ext z
  constructor
  · rintro ⟨x, ⟨w, rfl, hw0, hpos⟩, rfl⟩
    refine ⟨a.S.Γ (a.S.A.E.toEpGroupoid.π w), a.S.p_Γ_π w, ?_, ?_⟩
    · beta_reduce
      rw [← a.S.p_Γ_π]
      exact fun h => hw0 ((a.S.Γ_π_eq_zeroAt_iff w).1 h)
    · rw [ScPlusMultisection.toFun_mk, a.comm]; exact hpos
  · rintro ⟨y, rfl, hy0, hpos⟩
    obtain ⟨ξ, rfl⟩ := a.S.Γ.surjective y
    obtain ⟨w, rfl⟩ := a.S.A.E.toEpGroupoid.surjective_π ξ
    refine ⟨a.S.A.P w, ⟨w, rfl, fun h => hy0 ((a.S.Γ_π_eq_zeroAt_iff w).2 h), ?_⟩,
      (a.S.p_Γ_π w).symm⟩
    rw [← a.comm]; exact hpos

/-- **2021 Remark 16.5.3, p. 733**: for a representative `(λ, Γ, W, Λ)`,
`γ(|dom-supp(Λ)|) = dom-supp(λ)`; so `γ` restricts to a homeomorphism
`|dom-supp(Λ)| → dom-supp(λ)`. -/
theorem remark_16_5_3 (a : MultisectionRep c) :
    a.S.γ '' (a.S.A.X.π '' SBLocalization.domSupp a.Λ) =
      ScPlusMultisection.domSupp (c := c) ⟦a⟧ := by
  have hsat := isSaturated_nzSet a.isScPlusMultisection.1
  have e : SBLocalization.domSupp a.Λ = closure (nzSet a.Λ) := rfl
  rw [ScPlusMultisection.domSupp, ← image_nzSet, e, ← a.S.A.X.lemma_12_4_4_1 hsat,
    a.S.γ.image_closure, image_image]

/-! ### Definition 16.5.4 -/

namespace ScPlusMultisection

/-- **2021 Definition 16.5.4, p. 734 (2017: Definition 16.37)**: `λ` is **structurable** if a
representative `Λ` is (Definition 13.3.6). -/
def IsStructurable (s : ScPlusMultisection c) : Prop :=
  ∃ a : MultisectionRep c, ⟦a⟧ = s ∧ SBLocalization.IsStructurable a.S.A a.Λ

/-- **Definition 16.5.4, "one, and therefore all"**, given Theorems 13.4.1/13.4.3 for generalized
strong bundle isomorphisms (`StructurablePullback`). -/
theorem definition_16_5_4_hyp (hT : StructurablePullback.{u}) (s : ScPlusMultisection c) :
    s.IsStructurable ↔
      ∀ a : MultisectionRep c, ⟦a⟧ = s → SBLocalization.IsStructurable a.S.A a.Λ := by
  refine ⟨fun ⟨a, ha, hstr⟩ b hb => ?_, fun h => ?_⟩
  · obtain ⟨-, F, hF, -, he⟩ := (Quotient.exact (hb.trans ha.symm) : MultisectionRep.Rel b a)
    rw [he]
    exact hT _ _ F hF a.Λ hstr
  · obtain ⟨a, rfl⟩ := Quotient.exists_rep s
    exact ⟨a, rfl, h a rfl⟩

end ScPlusMultisection

/-- The zero multisection is structurable (witness for Definition 16.5.4). -/
theorem zero_isStructurable (c : StrongPolyfoldBundle p) : (zero c).IsStructurable :=
  ⟨_, rfl, isStructurable_zeroMultisection c.out.paracompact⟩

/-! ### Definitions 16.5.5 and 16.5.6 -/

/-- **A representative over `∂Z`** (2021 Definition 16.5.5, p. 734): a structure of `c̄`, an
sc⁺-multisection functor `Λ : W|∂X → ℚ⁺` (Definition 14.1.3), and `λ` with
`λ(Γ(|w|)) = Λ(w)` for `P(w) ∈ ∂X`. -/
structure BoundaryMultisectionRep (c : StrongPolyfoldBundle p) : Type (u + 1) where
  /-- The structure. -/
  S : StrongPolyfoldBundleStructure p
  hS : ⟦S⟧ = c
  /-- `Λ : W|∂X → ℚ⁺` (only its values over `∂X` matter). -/
  Λ : S.A.W → ℚ≥0
  isBoundaryScPlusMultisection : IsBoundaryScPlusMultisection S.A Λ
  /-- `λ : Y|∂Z → ℚ⁺` (only its values over `∂Z` matter). -/
  lam : Y → ℚ≥0
  comm : ∀ w, S.A.P w ∈ S.A.X.PObj.boundary → lam (S.Γ (S.A.E.toEpGroupoid.π w)) = Λ w

namespace BoundaryMultisectionRep

/-- **The relation of Definition 16.5.5**: `λ = λ'` over `∂Z` and a generalized strong bundle
isomorphism `f̄` with `Γ' ∘ |f̄| = Γ` and `Λ = f̄^*Λ'` over `∂X`, the pull-back read on orbits:
`Λ(w) = Λ'(w')` whenever `|f̄|(|w|) = |w'|`. -/
def Rel (a b : BoundaryMultisectionRep c) : Prop :=
  (∀ y, p y ∈ c.polyfold.boundary → a.lam y = b.lam y) ∧
    ∃ F : GenSBMap a.S.A b.S.A, F.IsGeneralizedIso ∧ ⇑b.S.Γ ∘ F.orbitMap = ⇑a.S.Γ ∧
      ∀ (w : a.S.A.W) (w' : b.S.A.W), a.S.A.P w ∈ a.S.A.X.PObj.boundary →
        F.orbitMap (a.S.A.E.toEpGroupoid.π w) = b.S.A.E.toEpGroupoid.π w' → a.Λ w = b.Λ w'

/-- `∼` is "same `λ` over `∂Z` and equivalent structures". -/
theorem rel_iff (a b : BoundaryMultisectionRep c) :
    Rel a b ↔ (∀ y, p y ∈ c.polyfold.boundary → a.lam y = b.lam y) ∧ Equiv a.S b.S := by
  refine ⟨fun ⟨hl, F, hF, hΓ, _⟩ => ⟨hl, equiv_iff_exists_Γ.2 ⟨F, hF, hΓ⟩⟩, fun ⟨hl, h⟩ => ?_⟩
  obtain ⟨F, hF, hΓ⟩ := equiv_iff_exists_Γ.1 h
  refine ⟨hl, F, hF, hΓ, fun w w' hw hww' => ?_⟩
  have hy : b.S.Γ (b.S.A.E.toEpGroupoid.π w') = a.S.Γ (a.S.A.E.toEpGroupoid.π w) := by
    rw [← hww']; exact congrFun hΓ _
  have hbd : p (a.S.Γ (a.S.A.E.toEpGroupoid.π w)) ∈ c.polyfold.boundary := by
    rw [a.S.p_Γ_π]; exact (mem_boundary_iff_obj a.hS _).2 hw
  have hw' : b.S.A.P w' ∈ b.S.A.X.PObj.boundary := by
    rw [← hy, b.S.p_Γ_π] at hbd; exact (mem_boundary_iff_obj b.hS _).1 hbd
  rw [← a.comm w hw, ← b.comm w' hw', hy, hl _ hbd]

theorem rel_of_lam_eq (a b : BoundaryMultisectionRep c)
    (h : ∀ y, p y ∈ c.polyfold.boundary → a.lam y = b.lam y) : Rel a b :=
  (rel_iff a b).2 ⟨h, Quotient.exact (a.hS.trans b.hS.symm)⟩

instance setoid (c : StrongPolyfoldBundle p) : Setoid (BoundaryMultisectionRep c) where
  r := Rel
  iseqv := ⟨fun a => rel_of_lam_eq a a fun _ _ => rfl,
    fun h => rel_of_lam_eq _ _ fun y hy => (h.1 y hy).symm,
    fun h h' => rel_of_lam_eq _ _ fun y hy => (h.1 y hy).trans (h'.1 y hy)⟩

end BoundaryMultisectionRep

/-- **2021 Definition 16.5.5, p. 734 (2017: Definition 16.38)**: an **sc⁺-multisection of
`Y|∂Z`**: a class `[(λ, Γ, W, Λ)]`. -/
abbrev BoundaryMultisection (c : StrongPolyfoldBundle p) : Type (u + 1) :=
  Quotient (BoundaryMultisectionRep.setoid c)

namespace BoundaryMultisection

open scoped Classical in
/-- `λ : Y|∂Z → ℚ⁺`, read as `0` off `p⁻¹(∂Z)` (well defined). -/
def toFun (s : BoundaryMultisection c) : Y → ℚ≥0 :=
  Quotient.lift (fun (a : BoundaryMultisectionRep c) (y : Y) =>
    if p y ∈ c.polyfold.boundary then a.lam y else 0) (fun a b h => funext fun y => by
      by_cases hy : p y ∈ c.polyfold.boundary
      · rw [if_pos hy, if_pos hy]; exact (h : BoundaryMultisectionRep.Rel a b).1 y hy
      · rw [if_neg hy, if_neg hy]) s

theorem toFun_mk_of_mem (a : BoundaryMultisectionRep c) {y : Y}
    (hy : p y ∈ c.polyfold.boundary) : BoundaryMultisection.toFun (c := c) ⟦a⟧ y = a.lam y := by
  classical
  change (if p y ∈ c.polyfold.boundary then a.lam y else 0) = _
  rw [if_pos hy]

/-- `dom-supp(λ)` over `∂Z` (Definition 16.5.2 read over `∂Z`, as Theorem 16.5.7 uses it). -/
def domSupp (s : BoundaryMultisection c) : Set Z :=
  closure {z | z ∈ c.polyfold.boundary ∧ ∃ y, p y = z ∧ y ≠ c.zeroAt z ∧ 0 < s.toFun y}

/-- **2021 Definition 16.5.6, p. 734 (2017: Definition 16.39)**: `λ` over `∂Z` is
**structurable** if one of its representatives has a structurable `Λ : W|∂X → ℚ⁺` (Definition
14.1.7). -/
def IsStructurable (s : BoundaryMultisection c) : Prop :=
  ∃ a : BoundaryMultisectionRep c, ⟦a⟧ = s ∧ IsBoundaryStructurable a.S.A a.Λ

end BoundaryMultisection

/-- `|∂-dom-supp(Λ)| ⊆ ∂-dom-supp(λ)` through `x ↦ γ(|x|)`. -/
theorem boundaryDomSupp_subset (a : BoundaryMultisectionRep c) :
    boundaryDomSupp a.Λ ⊆ (fun x => a.S.γ (a.S.A.X.π x)) ⁻¹'
      BoundaryMultisection.domSupp (c := c) ⟦a⟧ := by
  refine (closure_mono ?_).trans (a.S.continuous_γπ.closure_preimage_subset _)
  rintro x ⟨hx, w, rfl, hw0, hpos⟩
  have hbd := (mem_boundary_iff_obj a.hS _).2 hx
  refine ⟨hbd, a.S.Γ (a.S.A.E.toEpGroupoid.π w), a.S.p_Γ_π w, ?_, ?_⟩
  · beta_reduce
    rw [zeroAt_eq_of_mem a.hS, ← a.S.p_Γ_π]
    exact fun h => hw0 ((a.S.Γ_π_eq_zeroAt_iff w).1 h)
  · rw [BoundaryMultisection.toFun_mk_of_mem a (by rw [a.S.p_Γ_π]; exact hbd), a.comm w hx]
    exact hpos

/-- `tsupport (f ∘ g) ⊆ g⁻¹(tsupport f)` for continuous `g`. -/
theorem tsupport_comp_subset_preimage' {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {g : α → β} (hg : Continuous g) (f : β → ℝ) : tsupport (f ∘ g) ⊆ g ⁻¹' tsupport f := by
  rw [tsupport, tsupport, support_comp_eq_preimage]
  exact hg.closure_preimage_subset _

/-! ### Theorem 16.5.7 -/

/-- **2021 Theorem 16.5.7, p. 735 (2017: Theorem 16.6), from Theorem 14.1.9**: over a tame
polyfold whose models admit sc-smooth partitions of unity, with an auxiliary norm `n`, a
structurable sc⁺-multisection `λ` over `∂Z`, an open `Ũ ⊇ dom-supp(λ)` and a continuous
`f ≥ 0` with `tsupport f ⊆ Ũ` and `n(λ) < f` on `dom-supp(λ)`, there is a structurable
sc⁺-multisection `λ'` with (1) `n(λ') ≤ f`, (2) `dom-supp(λ') ⊆ Ũ`, (3) `λ' = λ` over `∂Z`.
`h1419` is Theorem 14.1.9 (`theorem_14_1_9_statement`) in the models of `c̄`; the proof
reduces to it in the model where `λ` is structurable. -/
theorem theorem_16_5_7_hyp
    (h1419 : ∀ S : StrongPolyfoldBundleStructure p, ⟦S⟧ = c → theorem_14_1_9_statement S.A)
    (hc : c.IsTame) (hPU : ∀ S : StrongPolyfoldBundleStructure p, ⟦S⟧ = c →
      S.A.X.PObj.AdmitsScPartitionsOfUnity)
    {n : Y → ℝ} (hn : c.IsAuxNorm n) (s : BoundaryMultisection c) (hs : s.IsStructurable)
    {U : Set Z} (hU : IsOpen U) (hdom : s.domSupp ⊆ U) {f : Z → ℝ} (hf : Continuous f)
    (hf0 : ∀ z, 0 ≤ f z) (hfU : tsupport f ⊆ U)
    (hlt : ∀ z ∈ s.domSupp, c.normLam n s.toFun z < f z) :
    ∃ t : ScPlusMultisection c, t.IsStructurable ∧ (∀ z, c.normLam n t.toFun z ≤ f z) ∧
      t.domSupp ⊆ U ∧ ∀ y, p y ∈ c.polyfold.boundary → t.toFun y = s.toFun y := by
  obtain ⟨a, rfl, hstr⟩ := hs
  set S := a.S
  set g : S.A.Obj → Z := fun x => S.γ (S.A.X.π x) with hg
  have hgc : Continuous g := S.continuous_γπ
  have hbsub := boundaryDomSupp_subset a
  have hlt' : ∀ x ∈ boundaryDomSupp a.Λ, pointwiseNorm (S.normOf n) a.Λ x < (f ∘ g) x := by
    intro x hx
    have hxb : x ∈ S.A.X.PObj.boundary := closure_minimal (fun y hy => hy.1)
      S.A.X.PObj.isClosed_boundary hx
    have e := normLam_eq a.hS n a.Λ (BoundaryMultisection.toFun (c := c) ⟦a⟧) x fun w hw => by
      have hb : p (S.Γ (S.A.E.toEpGroupoid.π w)) ∈ c.polyfold.boundary := by
        rw [S.p_Γ_π, hw]; exact (mem_boundary_iff_obj a.hS _).2 hxb
      rw [BoundaryMultisection.toFun_mk_of_mem a hb, a.comm w (hw ▸ hxb)]
    rw [← e]
    exact hlt _ (hbsub hx)
  obtain ⟨Λ', hstr', h1, h2, h3⟩ := h1419 S a.hS ((c.isTame_iff.1 hc) S a.hS) S.paracompact
    (hPU S a.hS) a.Λ hstr (S.normOf n) (hn S a.hS) (g ⁻¹' U) (hU.preimage hgc)
    (S.isSaturated_preimage_γπ U) (hbsub.trans (preimage_mono hdom)) (f ∘ g) (hf.comp hgc)
    (fun x => hf0 _) (fun φ => congrArg (fun q => f (S.γ q)) (S.A.X.π_src_eq_π_tgt φ).symm)
    ((tsupport_comp_subset_preimage' hgc f).trans (preimage_mono hfU)) hlt'
  · set a' := ofFunctor S a.hS Λ' hstr'.1
    refine ⟨⟦a'⟧, ⟨a', rfl, hstr'⟩, fun z => ?_, ?_, fun y hy => ?_⟩
    · obtain ⟨x, rfl⟩ := S.surjective_γπ z
      change c.normLam n a'.lam (S.γ (S.A.X.π x)) ≤ f (S.γ (S.A.X.π x))
      rw [normLam_eq a.hS n Λ' _ x fun w _ => a'.comm w]
      exact h1 x
    · rw [← remark_16_5_3 a']
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact h2 hx
    · obtain ⟨ξ, rfl⟩ := S.Γ.surjective y
      obtain ⟨w, rfl⟩ := S.A.E.toEpGroupoid.surjective_π ξ
      have hw : S.A.P w ∈ S.A.X.PObj.boundary := by
        rw [S.p_Γ_π] at hy; exact (mem_boundary_iff_obj a.hS _).1 hy
      rw [BoundaryMultisection.toFun_mk_of_mem a hy, ScPlusMultisection.toFun_mk,
        show a'.lam (S.Γ (S.A.E.toEpGroupoid.π w)) = Λ' w from a'.comm w, a.comm w hw]
      exact h3 w hw

/-- **The hypotheses of `theorem_16_5_7_hyp` on `λ`, `Ũ`, `f` are jointly satisfiable** in every
tame strong polyfold bundle: the zero multisection over `∂Z`, `Ũ = ∅`, `f = 0`. -/
theorem theorem_16_5_7_hyp_witness (hc : c.IsTame) {n : Y → ℝ} :
    ∃ s : BoundaryMultisection c, s.IsStructurable ∧ s.domSupp ⊆ (∅ : Set Z) ∧
      tsupport (fun _ : Z => (0 : ℝ)) ⊆ ∅ ∧
      ∀ z ∈ s.domSupp, c.normLam n s.toFun z < (fun _ : Z => (0 : ℝ)) z := by
  set S := c.out
  have hX := (c.isTame_iff.1 hc) S (Quotient.out_eq c)
  set a : BoundaryMultisectionRep c := ⟨S, Quotient.out_eq c, zeroMultisection S.A,
    isBoundaryScPlusMultisection_zero hX, (ofFunctor S (Quotient.out_eq c) _
      (isScPlusMultisection_zeroMultisection S.A)).lam,
    fun w _ => (ofFunctor S (Quotient.out_eq c) _
      (isScPlusMultisection_zeroMultisection S.A)).comm w⟩
  have hempty : BoundaryMultisection.domSupp (c := c) ⟦a⟧ = ∅ := by
    have h := boundaryDomSupp_zero (A := S.A)
    rw [BoundaryMultisection.domSupp, closure_empty_iff, eq_empty_iff_forall_notMem]
    rintro z ⟨hz, y, rfl, hy0, hpos⟩
    obtain ⟨ξ, rfl⟩ := S.Γ.surjective y
    obtain ⟨w, rfl⟩ := S.A.E.toEpGroupoid.surjective_π ξ
    have hw : S.A.P w ∈ S.A.X.PObj.boundary := by
      rw [S.p_Γ_π] at hz; exact (mem_boundary_iff_obj (Quotient.out_eq c) _).1 hz
    have hw0 : w ≠ fiberZero S.A.P (S.A.P w) := fun h' =>
      hy0 (by rw [zeroAt_eq_of_mem (Quotient.out_eq c)]; exact (S.Γ_π_eq_zeroAt_iff w).2 h')
    rw [BoundaryMultisection.toFun_mk_of_mem a hz, a.comm w hw] at hpos
    have : S.A.P w ∈ boundaryDomSupp (zeroMultisection S.A) :=
      subset_closure ⟨hw, w, rfl, hw0, hpos⟩
    rw [h] at this
    exact this
  refine ⟨⟦a⟧, ⟨a, rfl, isBoundaryStructurable_zero hX S.paracompact⟩, by rw [hempty], by simp,
    by simp [hempty]⟩

end StrongPolyfoldBundle

end Polyfold
