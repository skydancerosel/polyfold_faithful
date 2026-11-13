import Polyfold.Chapter16.P3W4PB_Multisections
import Polyfold.Chapter10.FredholmEquivalence
import Polyfold.Chapter12.P3O_OrientationOrbit
import Polyfold.Chapter15.P3W3G_GeneralPosition

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.6 "Fredholm Theory" (pp. 735–740; 2017: §16.6): **Definitions 16.6.1–16.6.3, Theorem 16.6.4,
Definition 16.6.5**, and the reduction of **Theorem 16.6.6** to the ep-groupoid level.  Numbers
and pages are the 2021 text's.

## The text, paraphrased

(p. 735) For a representative `(f, Γ, W, F)` with `F` sc-Fredholm, every other representative
`(f, Γ', W', F')` has `F'` sc-Fredholm (`F' = 𝔉_* F`, Theorems 10.4.5 and 10.5.4).  (D16.6.1) An
sc-Fredholm section of `p` is a class `[(f, Γ, W, F)]` with `F` an sc-Fredholm section functor.
(D16.6.2) `f` has a compact solution set if `S_f = {z | f(z) = 0}` is compact.  (D16.6.3) `f` is
proper (proper`<∞`) if `S_f` is compact and for every auxiliary norm `n` an open `U ⊇ S_f` has
`cl_Z{z ∈ U | n(f(z)) ≤ 1}` compact (for every `0 < C < ∞`, `cl_Z{z ∈ U | n(f(z)) ≤ C}`
compact); `(n, U)` controls compactness.  (T16.6.4) Compact, proper and proper`<∞` are
equivalent (proof: Theorem 12.4.2 in a model).  (D16.6.5) An orientation of `f` is the choice of
an orientation of a representative `(W, F)` (transported to the other representatives by Theorem
12.5.7).  (T16.6.6) For `∂Z = ∅`, `f` oriented with compact solution set and index `k`, `(n, U)`
controlling compactness, and `λ` controlled by `(n, U)` with `(f, λ)` in general position, the
branched integrals of a closed `k`-form over `θ = λ ∘ f` are well defined, independent of `λ`, and
depend only on the cohomology class.

## What is formalized (namespace `Polyfold.StrongPolyfoldBundle`)

* `ScSection.IsFredholm`, `isFredholm_iff` (the text's claim on p. 735: one representative
  sc-Fredholm iff all, Theorem 10.5.4), `FredholmSection c` (**Definition 16.6.1**).
* `ScSection.solutionSet`, `HasCompactSolutionSet` (**Definition 16.6.2**), `solutionSet_eq`
  (`S_f = γ(|S_F|)` in every representative).
* `ScSection.ControlsCompactness`, `IsProper`, `IsProperLtInfty` (**Definition 16.6.3**).
* **Theorem 16.6.4** (`theorem_16_6_4`), proved, through `hasCompactSolutionSet_iff`,
  `isProper_iff`, `isProperLtInfty_iff` (each polyfold notion is the ep-groupoid notion of
  Definition 12.4.1 in any representative) and Theorem 12.4.2.
* **Definition 16.6.5**: `OrientationRep` (a representative with an orientation in the sense of
  Definition 12.5.4 for a topology satisfying Theorem 12.5.3), `IsOrientable`.
* Theorem 16.6.6, the reduction: `theorem_16_6_6_reduction` (the hypotheses of Theorem 16.6.6 in
  any model give the hypotheses of the ep-groupoid statements of §15.3–15.4: `∂X = ∅`, compact
  `|S_F|`, `(N, U')` controlling compactness, an `(N, U')`-admissible representative of `λ`), and
  `exists_generalPosition_hyp` (perturbations as Theorem 16.6.6 requires exist, from Theorem
  15.3.7, `theorem_15_3_7_statement`, in a model).  The integrals themselves need the canonical
  orientation of `λ ∘ f` (Theorem 15.4.1, Definition 15.4.2), not in the project; see the note.

## Readings

* D16.6.3 "`n(f(z)) ≤ C`" for `n : Y_{0,1} → ℝ⁺`: `f(z) ∈ Y_{0,1}` and `n(f(z)) ≤ C`, the form of
  Part I's `AuxLe`.
* T16.6.6 writes `n : Z_{0,1} → ℝ⁺`; `Y_{0,1}` is presumably meant.  "λ controlled by `(n, U)`"
  is read as `n(λ) ≤ 1` and `dom-supp(λ) ⊆ U` (the example after Definition 15.3.3).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

open EPLocalization SBLocalization

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-! ### Definition 16.6.1 -/

namespace ScSection

/-- The sc-smooth section is **sc-Fredholm** if a representative `F` is an sc-Fredholm section
functor (Definition 12.1.1). -/
def IsFredholm (s : ScSection c) : Prop :=
  ∃ a : SectionRep c, ⟦a⟧ = s ∧ a.F ∈ a.S.A.E.fredholmSectionFunctors

/-- **The claim before Definition 16.6.1 (pp. 735–736)**: one representative is sc-Fredholm iff
all are (`F' = 𝔉_* F`, Theorem 10.5.4). -/
theorem isFredholm_iff (s : ScSection c) :
    s.IsFredholm ↔ ∀ a : SectionRep c, ⟦a⟧ = s → a.F ∈ a.S.A.E.fredholmSectionFunctors := by
  refine ⟨fun ⟨a, ha, hfr⟩ b hb => ?_, fun h => ?_⟩
  · obtain ⟨-, 𝔄, h𝔄, -, hpush⟩ := (Quotient.exact (ha.trans hb.symm) : SectionRep.Rel a b)
    rw [← hpush]
    exact (GenSBMap.theorem_10_5_4_fred h𝔄).1 hfr
  · obtain ⟨a, rfl⟩ := Quotient.exists_rep s
    exact ⟨a, rfl, h a rfl⟩

end ScSection

/-- **2021 Definition 16.6.1, p. 736 (2017: Definition 16.40)**: an **sc-Fredholm section** of
the strong polyfold bundle `p`: a class `[(f, Γ, W, F)]` with `F` an sc-Fredholm section
functor. -/
abbrev FredholmSection (c : StrongPolyfoldBundle p) : Type (u + 1) :=
  {s : ScSection c // s.IsFredholm}

/-! ### Definitions 16.6.2 and 16.6.3 -/

namespace ScSection

/-- `S_f = {z ∈ Z | f(z) = 0_z}`. -/
def solutionSet (s : ScSection c) : Set Z := {z | s.toFun z = c.zeroAt z}

/-- **2021 Definition 16.6.2, p. 736 (2017: Definition 16.41)**: `f` has a **compact solution
set**. -/
def HasCompactSolutionSet (s : ScSection c) : Prop := IsCompact s.solutionSet

/-- `{z ∈ U | f(z) ∈ Y_{0,1}, n(f(z)) ≤ C}`. -/
def sublevel (s : ScSection c) (n : Y → ℝ) (U : Set Z) (C : ℝ) : Set Z :=
  {z | z ∈ U ∧ s.toFun z ∈ c.Y01 ∧ n (s.toFun z) ≤ C}

/-- **`(n, U)` controls compactness** (Definition 16.6.3, last sentence; with `C = 1`). -/
def ControlsCompactness (s : ScSection c) (n : Y → ℝ) (U : Set Z) : Prop :=
  c.IsAuxNorm n ∧ IsOpen U ∧ s.solutionSet ⊆ U ∧ IsCompact (closure (s.sublevel n U 1))

/-- **2021 Definition 16.6.3 (1), p. 736 (new in 2021)**: `f` is **proper**. -/
def IsProper (s : ScSection c) : Prop :=
  IsCompact s.solutionSet ∧ ∀ n : Y → ℝ, c.IsAuxNorm n → ∃ U : Set Z, IsOpen U ∧
    s.solutionSet ⊆ U ∧ IsCompact (closure (s.sublevel n U 1))

/-- **2021 Definition 16.6.3 (2), pp. 736–737**: `f` is **proper`<∞`**. -/
def IsProperLtInfty (s : ScSection c) : Prop :=
  IsCompact s.solutionSet ∧ ∀ n : Y → ℝ, c.IsAuxNorm n → ∃ U : Set Z, IsOpen U ∧
    s.solutionSet ⊆ U ∧ ∀ C : ℝ, 0 < C → IsCompact (closure (s.sublevel n U C))

end ScSection

/-- **Every structure of `c̄` carries a representative of every sc-smooth section**: the
push-forward `𝔄_* F` along a generalized strong bundle isomorphism with `Γ' ∘ |𝔄| = Γ`
(Theorem 10.5.4). -/
theorem ScSection.exists_rep_of_mem (s : ScSection c) {S : StrongPolyfoldBundleStructure p}
    (hSc : ⟦S⟧ = c) : ∃ a : SectionRep c, ⟦a⟧ = s ∧ a.S = S := by
  obtain ⟨a₀, rfl⟩ := Quotient.exists_rep s
  obtain ⟨𝔄, h𝔄, hΓ⟩ := equiv_iff_exists_Γ.1 (Quotient.exact (a₀.hS.trans hSc.symm))
  set D := GenSBMap.rep h𝔄
  have hΨ := GenSBMap.isEquivalence_rep_Ψ h𝔄
  have hD : D.cls = 𝔄 := GenSBMap.cls_rep h𝔄
  have hcomm : ∀ x' : S.A.Obj, a₀.f (S.γ (S.A.X.π x')) =
      S.Γ (S.A.E.toEpGroupoid.π (GenSBMap.pushforward h𝔄 a₀.F x')) := by
    intro x'
    obtain ⟨ξ, hξ⟩ := (D.base.isHomeomorph_orbitMap (sbe hΨ).isEquivalence_base).surjective
      (S.A.X.π x')
    induction ξ using Quotient.inductionOn with | h x => ?_
    have hx : D.base.orbitMap (a₀.S.A.X.π x) = S.A.X.π x' := hξ
    have h1 := D.π_pushforward hΨ a₀.hF hx
    change S.A.E.toEpGroupoid.π (D.pushforward hΨ a₀.F x') = _ at h1
    change _ = S.Γ (S.A.E.toEpGroupoid.π (D.pushforward hΨ a₀.F x'))
    rw [h1]
    have hγ := congrFun (Γ_base hΓ) (a₀.S.A.X.π x)
    have hbase : EPLoc.orbitMap 𝔄.base (a₀.S.A.X.π x) = S.A.X.π x' := by
      rw [← hD]; exact hx
    simp only [Function.comp_apply, hbase] at hγ
    rw [hγ, a₀.comm x]
    have hΓx := congrFun hΓ (a₀.S.A.E.toEpGroupoid.π (a₀.F x))
    simp only [Function.comp_apply] at hΓx
    rw [← hΓx, ← hD]
    rfl
  refine ⟨⟨S, hSc, GenSBMap.pushforward h𝔄 a₀.F, (GenSBMap.theorem_10_5_4 h𝔄).2.1.1 a₀.hF,
    a₀.f, a₀.continuous_f, a₀.isSection, hcomm⟩, ?_, rfl⟩
  exact Quotient.sound (SectionRep.rel_of_f_eq _ _ rfl)

/-! ### Reading the notions in a representative -/

/-- `Γ(|w|) ∈ Y_{0,1}` iff `w ∈ W_{0,1}`. -/
theorem Γ_mem_Y01_iff {S : StrongPolyfoldBundleStructure p} (hS : ⟦S⟧ = c) (w : S.A.W) :
    S.Γ (S.A.E.toEpGroupoid.π w) ∈ c.Y01 ↔ w ∈ S.A.B.oneSet := by
  rw [c.Y01_eq hS]
  refine ⟨fun ⟨e, he⟩ => ?_, fun hw => ⟨S.A.B.oneMk w hw, rfl⟩⟩
  have h1 : S.A.E.toEpGroupoid.π (S.A.B.oneVal e) = S.A.E.toEpGroupoid.π w := S.Γ.injective he
  obtain ⟨q, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 h1
  have hs' : (q : S.A.Mor × S.A.W).2 = S.A.B.oneVal e := hs
  have ht' : S.A.E.μ q = w := ht
  rw [← ht']
  exact μ_mem_oneSet S.A q (by rw [hs']; exact S.A.B.oneVal_mem e)

namespace SectionRep

variable (a : SectionRep c)

/-- `x ↦ γ(|x|)` for the structure of a representative. -/
abbrev g : a.S.A.Obj → Z := fun x => a.S.γ (a.S.A.X.π x)

theorem isSection_F : ∀ x, a.S.A.P (a.F x) = x := a.hF.1.1

/-- **`S_f = γ(|S_F|)`**. -/
theorem solutionSet_eq :
    ScSection.solutionSet (c := c) ⟦a⟧ = a.g '' solutionSet a.S.A.P a.F := by
  ext z
  obtain ⟨x, rfl⟩ := a.S.surjective_γπ z
  have key : ScSection.toFun (c := c) ⟦a⟧ (a.g x) = c.zeroAt (a.g x) ↔
      a.F x = fiberZero a.S.A.P x := by
    change a.f (a.g x) = _ ↔ _
    rw [a.comm x, zeroAt_eq_of_mem a.hS, a.S.zeroAt_eq rfl]
    constructor
    · intro h
      have := π_eq_fiberZero_iff (a.S.Γ.injective h)
      rwa [a.isSection_F x] at this
    · intro h; rw [h]
  change _ ↔ _
  refine ⟨fun h => ⟨x, key.1 h, rfl⟩, ?_⟩
  rintro ⟨x', hx', hxx'⟩
  have hπ : a.S.A.X.π x' = a.S.A.X.π x := a.S.γ.injective hxx'
  refine key.2 ?_
  have h1 : a.S.A.E.toEpGroupoid.π (a.F x) = a.S.A.E.toEpGroupoid.π (fiberZero a.S.A.P x') := by
    obtain ⟨φ, hφs, hφt⟩ := (GroupoidStr.π_eq_π_iff _).1 hπ
    have hfun := a.hF.2 φ
    rw [← hx', ← hφs, ← hφt]
    exact ((GroupoidStr.π_eq_π_iff _).2 ⟨EpStrongBundle.sectionPair a.hF.1.1 φ, rfl,
      hfun.symm⟩).symm
  have := π_eq_fiberZero_iff h1
  rwa [a.isSection_F x] at this

/-- `{z ∈ V | f(z) ∈ Y_{0,1}, n(f(z)) ≤ C} = γ(|{x ∈ γπ⁻¹(V) | N(F(x)) ≤ C}|)`, `N = normOf n`. -/
theorem sublevel_eq (n : Y → ℝ) (V : Set Z) (C : ℝ) :
    ScSection.sublevel (c := c) ⟦a⟧ n V C =
      a.g '' {x | x ∈ a.g ⁻¹' V ∧ a.S.A.B.AuxLe (a.S.normOf n) (a.F x) C} := by
  ext z
  obtain ⟨x, rfl⟩ := a.S.surjective_γπ z
  have hfx : ScSection.toFun (c := c) ⟦a⟧ (a.g x) =
      a.S.Γ (a.S.A.E.toEpGroupoid.π (a.F x)) := a.comm x
  constructor
  · rintro ⟨hV, hY, hC⟩
    rw [hfx] at hY hC
    have hmem := (Γ_mem_Y01_iff a.hS _).1 hY
    exact ⟨x, ⟨hV, hmem, hC⟩, rfl⟩
  · rintro ⟨x', ⟨hV, hmem, hC⟩, hxx'⟩
    have hπ : a.S.A.X.π x' = a.S.A.X.π x := a.S.γ.injective hxx'
    have hπF : a.S.A.E.toEpGroupoid.π (a.F x') = a.S.A.E.toEpGroupoid.π (a.F x) := by
      obtain ⟨φ, hφs, hφt⟩ := (GroupoidStr.π_eq_π_iff _).1 hπ
      rw [← hφs, ← hφt]
      exact (GroupoidStr.π_eq_π_iff _).2 ⟨EpStrongBundle.sectionPair a.hF.1.1 φ, rfl,
        (a.hF.2 φ).symm⟩
    refine ⟨hxx' ▸ hV, ?_, ?_⟩
    · rw [hfx, ← hπF, Γ_mem_Y01_iff a.hS]; exact hmem
    · rw [hfx, ← hπF]; exact hC

/-- `x ↦ γ(|x|)` maps compact closures to compact closures and back. -/
theorem isCompact_closure_g_image_iff (K : Set a.S.A.Obj) :
    IsCompact (closure (a.g '' K)) ↔ IsCompact (closure (a.S.A.X.π '' K)) := by
  rw [show a.g '' K = a.S.γ '' (a.S.A.X.π '' K) by rw [image_image], ← a.S.γ.image_closure,
    a.S.γ.isCompact_image]

theorem isOpen_g_image {U : Set a.S.A.Obj} (hU : IsOpen U) : IsOpen (a.g '' U) := by
  rw [show a.g '' U = a.S.γ '' (a.S.A.X.π '' U) by rw [image_image]]
  exact a.S.γ.isOpenMap _ (a.S.A.X.proposition_7_1_8 _ hU)

theorem preimage_g_image {U : Set a.S.A.Obj} (hU : a.S.A.X.IsSaturated U) :
    a.g ⁻¹' (a.g '' U) = U := by
  rw [show a.g '' U = a.S.γ '' (a.S.A.X.π '' U) by rw [image_image]]
  change a.S.A.X.π ⁻¹' (a.S.γ ⁻¹' (a.S.γ '' (a.S.A.X.π '' U))) = U
  rw [a.S.γ.preimage_image]
  exact hU

/-- **Definition 16.6.2 in a representative**: `S_f` is compact iff `|S_F|` is. -/
theorem hasCompactSolutionSet_iff :
    ScSection.HasCompactSolutionSet (c := c) ⟦a⟧ ↔ a.S.A.E.HasCompactSolutionSetEp a.F := by
  unfold ScSection.HasCompactSolutionSet EpStrongBundle.HasCompactSolutionSetEp
  rw [a.solutionSet_eq, show a.g '' solutionSet a.S.A.P a.F =
    a.S.γ '' (a.S.A.X.π '' solutionSet a.S.A.P a.F) by rw [image_image], a.S.γ.isCompact_image]

/-- The two `U`-conditions of Definition 16.6.3 correspond, for each `C`, in a representative. -/
theorem forall_iff_of_saturated (n : Y → ℝ) {U' : Set a.S.A.Obj}
    (hU' : a.S.A.X.IsSaturated U') (C : ℝ) :
    IsCompact (closure (ScSection.sublevel (c := c) ⟦a⟧ n (a.g '' U') C)) ↔
      IsCompact (closure (a.S.A.X.π '' {x | x ∈ U' ∧ a.S.A.B.AuxLe (a.S.normOf n) (a.F x) C})) := by
  rw [a.sublevel_eq, a.preimage_g_image hU', a.isCompact_closure_g_image_iff]

theorem forall_iff_of_open (n : Y → ℝ) (U : Set Z) (C : ℝ) :
    IsCompact (closure (ScSection.sublevel (c := c) ⟦a⟧ n U C)) ↔
      IsCompact (closure (a.S.A.X.π '' {x | x ∈ a.g ⁻¹' U ∧
        a.S.A.B.AuxLe (a.S.normOf n) (a.F x) C})) := by
  rw [a.sublevel_eq, a.isCompact_closure_g_image_iff]

theorem solutionSet_subset_iff {U' : Set a.S.A.Obj} (hU' : a.S.A.X.IsSaturated U') :
    ScSection.solutionSet (c := c) ⟦a⟧ ⊆ a.g '' U' ↔ solutionSet a.S.A.P a.F ⊆ U' := by
  rw [a.solutionSet_eq]
  constructor
  · intro h x hx
    rw [← a.preimage_g_image hU']
    exact h ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩; exact ⟨x, h hx, rfl⟩

theorem solutionSet_subset_preimage_iff (U : Set Z) :
    ScSection.solutionSet (c := c) ⟦a⟧ ⊆ U ↔ solutionSet a.S.A.P a.F ⊆ a.g ⁻¹' U := by
  rw [a.solutionSet_eq, image_subset_iff]

/-- The general shape of Definitions 12.4.1 (2), (3) and 16.6.3 in a representative: an
ep-level `U'`-condition for every auxiliary norm `N` of `W` iff a polyfold-level `U`-condition for
every auxiliary norm `n` of `p`. -/
theorem forall_auxNorm_iff (Q : (a.S.A.B.One → ℝ) → Set a.S.A.Obj → Prop)
    (Q' : (Y → ℝ) → Set Z → Prop)
    (hQ : ∀ n U, Q' n U ↔ Q (a.S.normOf n) (a.g ⁻¹' U))
    (hQ' : ∀ n U', a.S.A.X.IsSaturated U' → (Q' n (a.g '' U') ↔ Q (a.S.normOf n) U')) :
    (∀ n : Y → ℝ, c.IsAuxNorm n → ∃ U : Set Z, IsOpen U ∧
        ScSection.solutionSet (c := c) ⟦a⟧ ⊆ U ∧ Q' n U) ↔
      ∀ N : a.S.A.B.One → ℝ, a.S.A.E.IsAuxNorm N → ∃ U' : Set a.S.A.Obj, IsOpen U' ∧
        a.S.A.X.IsSaturated U' ∧ solutionSet a.S.A.P a.F ⊆ U' ∧ Q N U' := by
  constructor
  · intro h N hN
    obtain ⟨U, hU, hSU, hq⟩ := h (a.S.descend N) (isAuxNorm_descend a.hS hN)
    refine ⟨a.g ⁻¹' U, hU.preimage a.S.continuous_γπ, a.S.isSaturated_preimage_γπ U,
      (a.solutionSet_subset_preimage_iff U).1 hSU, ?_⟩
    have := (hQ _ U).1 hq
    rwa [a.S.normOf_descend hN.isOneInvariant] at this
  · intro h n hn
    obtain ⟨U', hU', hsat, hSU', hq⟩ := h (a.S.normOf n) (hn a.S a.hS)
    exact ⟨a.g '' U', a.isOpen_g_image hU', (a.solutionSet_subset_iff hsat).2 hSU',
      (hQ' n U' hsat).2 hq⟩

/-- **Definition 16.6.3 (1) in a representative** is Definition 12.4.1 (2). -/
theorem isProper_iff :
    ScSection.IsProper (c := c) ⟦a⟧ ↔ a.S.A.E.IsProperFunctor a.F := by
  unfold ScSection.IsProper EpStrongBundle.IsProperFunctor
  refine and_congr a.hasCompactSolutionSet_iff
    (a.forall_auxNorm_iff _ _ (fun n U => ?_) fun n U' hU' => ?_)
  · exact a.forall_iff_of_open n U 1
  · exact a.forall_iff_of_saturated n hU' 1

/-- **Definition 16.6.3 (2) in a representative** is Definition 12.4.1 (3). -/
theorem isProperLtInfty_iff :
    ScSection.IsProperLtInfty (c := c) ⟦a⟧ ↔ a.S.A.E.IsProperLtInftyFunctor a.F := by
  unfold ScSection.IsProperLtInfty EpStrongBundle.IsProperLtInftyFunctor
  refine and_congr a.hasCompactSolutionSet_iff
    (a.forall_auxNorm_iff _ _ (fun n U => ?_) fun n U' hU' => ?_)
  · exact forall₂_congr fun C _ => a.forall_iff_of_open n U C
  · exact forall₂_congr fun C _ => a.forall_iff_of_saturated n hU' C

/-- `(n, U)` controls compactness iff `(normOf n, γπ⁻¹(U))` does (Definition 15.3.1). -/
theorem controlsCompactness_iff {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U) :
    ScSection.ControlsCompactness (c := c) ⟦a⟧ n U ↔
      SBLocalization.ControlsCompactness a.S.A a.F (a.S.normOf n) (a.g ⁻¹' U) := by
  unfold ScSection.ControlsCompactness SBLocalization.ControlsCompactness
  rw [a.solutionSet_subset_preimage_iff, a.forall_iff_of_open n U 1]
  exact ⟨fun ⟨_, _, h1, h2⟩ => ⟨hn a.S a.hS, hU.preimage a.S.continuous_γπ,
    a.S.isSaturated_preimage_γπ U, h1, h2⟩, fun ⟨_, _, _, h1, h2⟩ => ⟨hn, hU, h1, h2⟩⟩

end SectionRep

/-! ### Theorem 16.6.4 -/

/-- **2021 Theorem 16.6.4, p. 737 (2017: Theorem 16.7)**: for an sc-Fredholm section `f` of a
strong polyfold bundle, (1) `f` has a compact solution set, (2) `f` is proper, (3) `f` is
proper`<∞` are equivalent.  Proof: in any representative the three notions are those of
Definition 12.4.1 (`hasCompactSolutionSet_iff`, `isProper_iff`, `isProperLtInfty_iff`), and
Theorem 12.4.2 applies. -/
theorem theorem_16_6_4 (s : FredholmSection c) :
    List.TFAE [s.1.HasCompactSolutionSet, s.1.IsProper, s.1.IsProperLtInfty] := by
  obtain ⟨a, ha⟩ := Quotient.exists_rep s.1
  have hF := (s.1.isFredholm_iff.1 s.2) a ha
  have h := EpStrongBundle.theorem_12_4_2 hF a.S.paracompact
  rw [← ha, a.hasCompactSolutionSet_iff, a.isProper_iff, a.isProperLtInfty_iff]
  tfae_have 1 → 2 := fun h1 => (h.out 1 0).1 h1
  tfae_have 2 → 3 := fun h2 => (h.out 0 2).1 h2
  tfae_have 3 → 1 := fun h3 => (h.out 2 1).1 h3
  tfae_finish

/-! ### Definition 16.6.5 -/

/-- **An orientation of a representative** (2021 Definition 16.6.5, p. 739): a representative
`(f, Γ, W, F)` of the sc-Fredholm section, sc⁺-sections through every point of `W` (the standing
hypothesis of Part I's orientation transport, `HasScPlusSectionsThrough`), a topology on `O_F`
with the properties of Theorem 12.5.3 (`IsOrientationTopology`), and an orientation `o` in the
sense of Definition 12.5.4 for it. -/
structure OrientationRep (s : FredholmSection c) : Type (u + 1) where
  /-- The representative `(W, F)`. -/
  a : SectionRep c
  ha : ⟦a⟧ = s.1
  hF : a.S.A.E.IsScFredholmSectionFunctor a.F
  hsec : a.S.A.B.HasScPlusSectionsThrough
  /-- The topology of `O_F` (Theorem 12.5.3). -/
  t : TopologicalSpace (OrSpace a.F hF.2)
  isOrientationTopology :
    haveI := paracompactSpace_rn_prod a.S.A.X.PObj
    haveI := paracompactSpace_rn_pullback a.S.A.B
    IsOrientationTopology a.F hF.2 t
  /-- The orientation `x ↦ o_x`. -/
  o : ∀ x (hs : x ∈ a.S.A.X.PObj.smoothSet), Orx a.F hF.2 x hs
  isOrientation : a.S.A.E.definition_12_5_4 hF hsec t o

/-- **2021 Definition 16.6.5, p. 739 (2017: Definition 16.42)**: `f` is **orientable** (an
orientation, the choice of an orientation for a representative `(W, F)`, exists). -/
def FredholmSection.IsOrientable (s : FredholmSection c) : Prop := Nonempty (OrientationRep s)

/-! ### Theorem 16.6.6: the reduction to the ep-groupoid level -/

/-- `λ` is **controlled by `(n, U)`** (Theorem 16.6.6; the example after Definition 15.3.3):
`n(λ) ≤ 1` and `dom-supp(λ) ⊆ U`. -/
def ScPlusMultisection.IsControlledBy (t : ScPlusMultisection c) (n : Y → ℝ) (U : Set Z) :
    Prop :=
  (∀ z, c.normLam n t.toFun z ≤ 1) ∧ t.domSupp ⊆ U

/-- **The reduction in Theorem 16.6.6** (2021 p. 739; 2017: Theorem 16.8): for a polyfold with
`∂Z = ∅`, an sc-Fredholm section `f` with compact solution set, `(n, U)` controlling compactness
and `λ` controlled by `(n, U)`, in **every** structure `S ∈ c̄` the representatives `F` of `f` and
`Λ` of `λ` satisfy the hypotheses of the ep-groupoid statements of §§15.3–15.4: `∂X = ∅`, `|S_F|`
compact, `(normOf n, γπ⁻¹(U))` controls compactness (Definition 15.3.1), and `Λ` is
`(normOf n, γπ⁻¹(U))`-admissible (Definition 15.3.3). -/
theorem theorem_16_6_6_reduction (hbd : c.polyfold.boundary = ∅) (s : FredholmSection c)
    (hS : s.1.HasCompactSolutionSet) {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z}
    (hU : IsOpen U) (hcc : s.1.ControlsCompactness n U) (t : ScPlusMultisection c)
    (ht : t.IsControlledBy n U) (S : StrongPolyfoldBundleStructure p) (hSc : ⟦S⟧ = c) :
    ∃ (a : SectionRep c) (b : MultisectionRep c), ⟦a⟧ = s.1 ∧ ⟦b⟧ = t ∧ a.S = S ∧ b.S = S ∧
      S.A.X.PObj.boundary = ∅ ∧ a.S.A.E.IsScFredholmSectionFunctor a.F ∧
      a.S.A.E.HasCompactSolutionSetEp a.F ∧
      SBLocalization.ControlsCompactness a.S.A a.F (a.S.normOf n) (a.g ⁻¹' U) ∧
      (∀ x, pointwiseNorm (b.S.normOf n) b.Λ x ≤ 1) ∧
      SBLocalization.domSupp b.Λ ⊆ (fun x => b.S.γ (b.S.A.X.π x)) ⁻¹' U := by
  obtain ⟨a, haeq, rfl⟩ := ScSection.exists_rep_of_mem s.1 hSc
  obtain ⟨b, hb, hbS⟩ := exists_rep_of_mem t hSc
  have hFa := (s.1.isFredholm_iff.1 s.2) a haeq
  refine ⟨a, b, haeq, hb, rfl, hbS, ?_, hFa, ?_, ?_, fun x => ?_, ?_⟩
  · rw [eq_empty_iff_forall_notMem]
    intro x hx
    have := (mem_boundary_iff_obj hSc x).2 hx
    rw [hbd] at this; exact this
  · rw [← a.hasCompactSolutionSet_iff, haeq]; exact hS
  · rw [← a.controlsCompactness_iff hn hU, haeq]; exact hcc
  · rw [← normLam_eq b.hS n b.Λ b.lam x fun w _ => b.comm w]
    have := ht.1 (b.S.γ (b.S.A.X.π x))
    rwa [← hb] at this
  · intro x hx
    apply ht.2
    rw [← hb, ← remark_16_5_3 b]
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

/-- **The existence step of Theorem 16.6.6, reduced to Theorem 15.3.7** (2021 p. 739; 2017:
Theorem 16.8; the choice of `λ`): given a representative `(W, F)` of `f` in which the ep-groupoid
statement `theorem_15_3_7_statement` holds and the standing hypotheses of Theorem 15.3.7 are met
(tame, pointwise bump functions, `F` tame Fredholm), there is a structurable sc⁺-multisection `λ`
controlled by `(n, U)` with `n(λ) < 1`, whose representative `Λ` in the same structure is
transversal to `F` and in general position (Definitions 15.2.1, 15.3.4). -/
theorem exists_generalPosition_hyp (s : FredholmSection c) (a : SectionRep c) (ha : ⟦a⟧ = s.1)
    (h1537 : SBLocalization.theorem_15_3_7_statement a.S.A) (hX : a.S.A.X.IsTame)
    (hbump : a.S.A.X.AdmitsBumpFunctionsPointwise) (hft : a.S.A.B.IsScFredholmSectionTame a.F)
    (hS : s.1.HasCompactSolutionSet) {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z}
    (hU : IsOpen U) (hcc : s.1.ControlsCompactness n U) :
    ∃ (Λ : a.S.A.W → ℚ≥0) (hΛ : SBLocalization.IsScPlusMultisection a.S.A Λ),
      ScPlusMultisection.IsStructurable (c := c) ⟦ofFunctor a.S a.hS Λ hΛ⟧ ∧
      ScPlusMultisection.IsControlledBy (c := c) ⟦ofFunctor a.S a.hS Λ hΛ⟧ n U ∧
      (∀ z, c.normLam n (ofFunctor a.S a.hS Λ hΛ).lam z < 1) ∧
      SBLocalization.IsTransversal a.F Λ ∧ SBLocalization.IsInGeneralPosition a.S.A a.F Λ := by
  have hFa := (s.1.isFredholm_iff.1 s.2) a ha
  have hSa : a.S.A.E.HasCompactSolutionSetEp a.F := by
    rw [← a.hasCompactSolutionSet_iff, ha]; exact hS
  have hcca := (a.controlsCompactness_iff hn hU).1 (by rw [ha]; exact hcc)
  obtain ⟨Λ, hstr, hlt, hdom, htr, hgp⟩ := h1537 hX hbump a.F hFa hft hSa _ _ hcca
    (fun _ => 1) continuous_const (fun _ => rfl) (fun _ => ⟨one_pos, le_rfl⟩)
  set b := ofFunctor a.S a.hS Λ hstr.1
  have hlt' : ∀ z, c.normLam n b.lam z < 1 := by
    intro z
    obtain ⟨x, rfl⟩ := a.S.surjective_γπ z
    rw [normLam_eq a.hS n Λ _ x fun w _ => b.comm w]
    exact hlt x
  refine ⟨Λ, hstr.1, ⟨b, rfl, hstr⟩, ⟨fun z => (hlt' z).le, ?_⟩, hlt', htr, hgp⟩
  rw [← remark_16_5_3 b]
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact hdom hx

end StrongPolyfoldBundle

end Polyfold
