import Polyfold.Chapter11.AuxiliaryNormTransport2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.5, **Lemma 11.5.2** and **Proposition 11.5.3** (p. 548; 2017: Lemma 11.7
and Proposition 11.7, pp. 400–401), with the local section structures of **Definition 13.2.1**
(p. 607).

# Local section structures of sc⁺-multisections under strong bundle equivalences

## The text, paraphrased

(Definition 13.2.1, p. 607) An sc⁺-multisection of `(P : W → X, μ)` is a functor `Λ : W → ℚ⁺`
with a local section structure around every `x₀ ∈ X`: on the domain `U(x₀)` of a natural
representation, finitely many sc⁺-sections `s₁, …, s_k` with positive rational weights,
`∑ σᵢ = 1`, and `Λ(w) = ∑_{i : w = sᵢ(P(w))} σᵢ` over `U(x₀)`.  (p. 548) For an equivalence
`Φ : W → W'`, the pull-back is `Λ' ∘ Φ` and the push-forward `Φ_*Λ(w') = Λ(w)` for
`Φ(w) → w'`; a local section structure of `Φ_*Λ` around `x'` is `s'ᵢ(y') = μ'(σ', Φ(sᵢ(x)))`
for `σ' : ϕ(x) → x'`, with `σ'` extended to a local sc-diffeomorphism by `t ∘ s⁻¹`.
(Proposition 11.5.3) For a generalized strong bundle isomorphism, push-forward and pull-back of
sc⁺-multisections are well defined, mutually inverse, and depend only on `|[D]|`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* Definition 13.2.1: `IsScPlusSectionOn` (an sc⁺-section on an open set, in the form of
  `isScPlusSection_iff`), `IsLocalRepOn` (a local representation on an open set),
  `HasLocalSectionStructure` (on the domain of a natural representation),
  `IsScPlusMultisection`; a local representation on any open neighbourhood gives a local section
  structure (`hasLocalSectionStructure_of_isLocalRepOn`, by Theorem 7.1.13); witness
  `isScPlusMultisection_zeroMultisection` (the multisection of the zero section).
* Pull-back: `exists_isLocalRepOn_pullMult`, `isScPlusMultisection_pullMult`.
* Push-forward: `exists_isLocalRepOn_pushMult` (the text's construction), **Lemma 11.5.2** with
  the local section structures (`lemma_11_5_2_book`); diagrams:
  `SDiagram.isScPlusMultisection_pushMult`, `SDiagram.isScPlusMultisection_pullMult`.
* **Proposition 11.5.3** as stated: `GenSBMap.proposition_11_5_3_book`, no added hypothesis.

## Choices

* The local representations are stated on an open set and then shrunk to the domain of a
  natural representation; the book's sections `s'ᵢ` are defined on a neighbourhood
  `O' = {y' ∈ V : s(τ(y')) ∈ ϕ(U), g(s(τ(y'))) ∈ O}`, with `τ` the local inverse of `t'` at `σ'`
  and `g` the local inverse of `ϕ` (Definition 10.1.1 (1)); off `O'` they take junk values.
* The weights and values are in `ℚ≥0`, the text's `ℚ⁺` (it contains `0`, the value off the
  sections).
-/

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open EPLocalization StrongBundle

variable {A A' C : SEP.{u}}

/-! ### Definition 13.2.1: local section structures and sc⁺-multisections -/

/-- An **sc⁺-section of `P` on the open set `U`**: `P(s(y)) = y` on `U`, and `s` is sc-smooth as a
map `U → W[1]` (the form of Part I's `IsScPlusSection` given by `isScPlusSection_iff`, on `U`). -/
def IsScPlusSectionOn (A : SEP.{u}) (s : A.Obj → A.W) (U : Set A.Obj) : Prop :=
  (∀ y ∈ U, A.P (s y) = y) ∧ ∃ G : A.Obj → A.B.One, (∀ y ∈ U, A.B.oneVal (G y) = s y) ∧
    A.X.PObj.IsScSmoothOn A.B.toMPolyfold1 G U

open scoped Classical in
/-- **The local representation of 2021 Definition 13.2.1 on an open set `O`**: sc⁺-sections
`s₁, …, s_k` on `O` with positive rational weights `σ₁, …, σ_k`, (1) `∑ σᵢ = 1`, (2)
`Λ(w) = ∑_{i : w = sᵢ(P(w))} σᵢ` for `w ∈ W|O`. -/
def IsLocalRepOn (A : SEP.{u}) (Λ : A.W → ℚ≥0) (O : Set A.Obj) {k : ℕ}
    (s : Fin k → A.Obj → A.W) (σ : Fin k → ℚ≥0) : Prop :=
  (∀ i, 0 < σ i) ∧ (∀ i, IsScPlusSectionOn A (s i) O) ∧ ∑ i, σ i = 1 ∧
    ∀ w, A.P w ∈ O → Λ w = ∑ i, if w = s i (A.P w) then σ i else 0

/-- **A local section structure of `Λ` around `x₀`** (2021 Definition 13.2.1): a local
representation on the domain `U(x₀)` of a natural representation of `G_{x₀}`. -/
def HasLocalSectionStructure (A : SEP.{u}) (Λ : A.W → ℚ≥0) (x₀ : A.Obj) : Prop :=
  ∃ (R : A.X.NaturalRep x₀) (k : ℕ) (s : Fin k → A.Obj → A.W) (σ : Fin k → ℚ≥0),
    IsLocalRepOn A Λ R.U s σ

/-- **2021 Definition 13.2.1, p. 607 (sc⁺-multisection)**: a functor `Λ : W → ℚ⁺` with a local
section structure around every object. -/
def IsScPlusMultisection (A : SEP.{u}) (Λ : A.W → ℚ≥0) : Prop :=
  IsWFunctor A Λ ∧ ∀ x₀, HasLocalSectionStructure A Λ x₀

theorem IsScPlusSectionOn.mono {s : A.Obj → A.W} {U U' : Set A.Obj}
    (h : IsScPlusSectionOn A s U) (hU' : IsOpen U') (hsub : U' ⊆ U) :
    IsScPlusSectionOn A s U' :=
  ⟨fun y hy => h.1 y (hsub hy), let ⟨G, hG, hGs⟩ := h.2
    ⟨G, fun y hy => hG y (hsub hy), hGs.mono hU' hsub⟩⟩

theorem IsLocalRepOn.mono {Λ : A.W → ℚ≥0} {O O' : Set A.Obj} {k : ℕ}
    {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0} (h : IsLocalRepOn A Λ O s σ) (hO' : IsOpen O')
    (hsub : O' ⊆ O) : IsLocalRepOn A Λ O' s σ :=
  ⟨h.1, fun i => (h.2.1 i).mono hO' hsub, h.2.2.1, fun w hw => h.2.2.2 w (hsub hw)⟩

/-- A local representation on any open `O ∋ x₀` gives a local section structure around `x₀`
(natural representations exist inside every open neighbourhood, Theorem 7.1.13). -/
theorem hasLocalSectionStructure_of_isLocalRepOn {Λ : A.W → ℚ≥0} {x₀ : A.Obj}
    {O : Set A.Obj} (hO : IsOpen O) (hx₀ : x₀ ∈ O) {k : ℕ} {s : Fin k → A.Obj → A.W}
    {σ : Fin k → ℚ≥0} (h : IsLocalRepOn A Λ O s σ) : HasLocalSectionStructure A Λ x₀ := by
  obtain ⟨R, hR⟩ := A.X.theorem_7_1_13 x₀ hO hx₀
  exact ⟨R, k, s, σ, h.mono R.isOpen_U hR⟩

/-- A global sc⁺-section restricts to an sc⁺-section on every open set. -/
theorem IsScPlusSectionOn.of_isScPlusSection {s : A.Obj → A.W} (hs : A.B.IsScPlusSection s)
    {U : Set A.Obj} (hU : IsOpen U) : IsScPlusSectionOn A s U := by
  obtain ⟨hsec, G, hG, hGs⟩ := (A.B.isScPlusSection_iff s).1 hs
  exact ⟨fun y _ => hsec y, G, fun y _ => congrFun hG y, hGs.mono hU (subset_univ _)⟩

open scoped Classical in
/-- **The trivial multisection** `Λ₀(w) = 1` if `w = 0_{P(w)}` and `0` otherwise, the
multisection of the zero section (2021 p. 607, `k = 1`, `s₁ = 0`, `σ₁ = 1`). -/
def zeroMultisection (A : SEP.{u}) : A.W → ℚ≥0 :=
  fun w => if w = fiberZero A.P (A.P w) then 1 else 0

theorem isWFunctor_zeroMultisection (A : SEP.{u}) : IsWFunctor A (zeroMultisection A) := by
  classical
  rintro ⟨⟨σ, w⟩, hq⟩
  have hq' : A.P w = A.X.src σ := hq
  have hPμ : A.P (A.E.μ ⟨(σ, w), hq⟩) = A.X.tgt σ := A.E.P_μ _
  unfold zeroMultisection
  refine if_congr ?_ rfl rfl
  rw [hPμ, hq']
  constructor
  · intro e
    have h0 : A.P (fiberZero A.P (A.X.src σ)) = A.X.src σ := isSection_fiberZero _
    refine EpStrongBundle.μ_injective_snd A.E hq' h0 ?_
    rw [μ_fiberZero A σ h0]; exact e
  · intro e
    subst e
    exact μ_fiberZero A σ hq

/-- **The trivial multisection is an sc⁺-multisection**: Definition 13.2.1 is satisfiable. -/
theorem isScPlusMultisection_zeroMultisection (A : SEP.{u}) :
    IsScPlusMultisection A (zeroMultisection A) := by
  classical
  refine ⟨isWFunctor_zeroMultisection A, fun x₀ => hasLocalSectionStructure_of_isLocalRepOn
    isOpen_univ (mem_univ x₀) (k := 1) (s := fun _ => fiberZero A.P) (σ := fun _ => 1)
    ⟨fun _ => one_pos, fun _ => IsScPlusSectionOn.of_isScPlusSection
      StrongBundle.isScPlusSection_fiberZero isOpen_univ, by simp, fun w _ => by
        simp [zeroMultisection]⟩⟩

/-! ### Pull-back of local section structures along a strong bundle equivalence -/

variable {F : C ⟶ A}

/-- **The pull-back of a local representation** along a strong bundle equivalence `Φ : W'' → W`
covering `ϕ`: if `Λ'` has the local representation `(s'ᵢ, σᵢ)` on an open `O' ∋ ϕ(x)`, then
`Φ^*Λ' = Λ' ∘ Φ` has the local representation `(sᵢ, σᵢ)`, `sᵢ(y) = Φ_y⁻¹(s'ᵢ(ϕ(y)))`, on an
open `O ∋ x` (on the level `[1]`, `sᵢ = Ψ₁ ∘ s'ᵢ ∘ ϕ` with `Ψ₁` the inverse of Definition 10.4.1
(2)). -/
theorem exists_isLocalRepOn_pullMult (hF : SEP.equivalences F) {Λ' : A.W → ℚ≥0} {x : C.Obj}
    {O' : Set A.Obj} (hO' : IsOpen O') (hx : (SEP.Hom.ϕ F).obj x ∈ O') {k : ℕ}
    {s' : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0} (h : IsLocalRepOn A Λ' O' s' σ) :
    ∃ (O : Set C.Obj) (s : Fin k → C.Obj → C.W), IsOpen O ∧ x ∈ O ∧
      IsLocalRepOn C (pullMult F Λ') O s σ := by
  classical
  obtain ⟨U, U', hxU, hi⟩ := (sbe hF).isLocalStrongBundleIso_obj x
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  obtain ⟨Ψ₁, hΨ₁⟩ := hi.isScDiffeoOn_one
  choose G' hG'val hG'sm using fun i => (h.2.1 i).2
  have hFs := (SEP.Hom.isStrongBundleFunctor F).isStrongBundleMap_obj
  set O : Set C.Obj := U ∩ (SEP.Hom.ϕ F).obj ⁻¹' O' with hOdef
  have hO : IsOpen O := hg.isScSmoothOn.continuousOn.isOpen_inter_preimage hg.isOpen_source hO'
  have hmem : ∀ i, ∀ y ∈ O, A.P (A.B.oneVal (G' i ((SEP.Hom.ϕ F).obj y))) ∈ U' := fun i y hy => by
    rw [hG'val i _ hy.2, (h.2.1 i).1 _ hy.2]; exact hg.mapsTo hy.1
  let s : Fin k → C.Obj → C.W := fun i y => C.B.oneVal (Ψ₁ (G' i ((SEP.Hom.ϕ F).obj y)))
  have hsec : ∀ i, ∀ y ∈ O, C.P (s i y) = y := fun i y hy => by
    change C.P (C.B.oneVal (Ψ₁ _)) = y
    rw [StrongBundle.IsStrongBundleIsoOn.P_inv_one (h := hFs) hg hΨ₁ (hmem i y hy),
      hG'val i _ hy.2, (h.2.1 i).1 _ hy.2, hg.left_inv y hy.1]
  have hΦs : ∀ i, ∀ y ∈ O, (SEP.Hom.Φ F).obj (s i y) = s' i ((SEP.Hom.ϕ F).obj y) :=
    fun i y hy => by
      have e := congrArg A.B.oneVal (hΨ₁.right_inv _ (hmem i y hy))
      rw [oneVal_oneRestrict] at e
      exact e.trans (hG'val i _ hy.2)
  refine ⟨O, s, hO, ⟨hxU, hx⟩, h.1, fun i => ⟨hsec i, Ψ₁ ∘ G' i ∘ (SEP.Hom.ϕ F).obj,
    fun y _ => rfl, ?_⟩, h.2.2.1, fun w hw => ?_⟩
  · exact MPolyfold.IsScSmoothOn.comp hΨ₁.isScSmoothOn_inv
      (MPolyfold.IsScSmoothOn.comp (hG'sm i) (hg.isScSmoothOn.mono hO inter_subset_left)
        fun y hy => hy.2) fun y hy => hmem i y hy
  · have hPw : A.P ((SEP.Hom.Φ F).obj w) = (SEP.Hom.ϕ F).obj (C.P w) := hFs.covers w
    change Λ' ((SEP.Hom.Φ F).obj w) = _
    rw [h.2.2.2 _ (by rw [hPw]; exact hw.2)]
    refine Finset.sum_congr rfl fun i _ => if_congr ?_ rfl rfl
    rw [hPw]
    constructor
    · intro e
      exact (sbe hF).eq_of_obj_eq (hsec i _ hw).symm ((e.trans (hΦs i _ hw).symm))
    · intro e
      rw [e, hsec i _ hw, hΦs i _ hw]

/-- **The pull-back `Φ^*Λ'` of an sc⁺-multisection along a strong bundle equivalence is an
sc⁺-multisection** (2021 p. 547). -/
theorem isScPlusMultisection_pullMult (hF : SEP.equivalences F) {Λ' : A.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection A Λ') : IsScPlusMultisection C (pullMult F Λ') := by
  refine ⟨hΛ'.1.pullMult F, fun x => ?_⟩
  obtain ⟨R, k, s', σ, h⟩ := hΛ'.2 ((SEP.Hom.ϕ F).obj x)
  obtain ⟨O, s, hO, hxO, hrep⟩ := exists_isLocalRepOn_pullMult hF R.isOpen_U R.mem_U h
  exact hasLocalSectionStructure_of_isLocalRepOn hO hxO hrep

/-! ### Push-forward of local section structures along a strong bundle equivalence -/

/-- **The push-forward of a local representation** (2021 p. 548, after Lemma 11.5.2): for
`σ' : ϕ(x) → x₀'` and a local representation `(sᵢ, σᵢ)` of `Λ` on an open `O ∋ x`, `Φ_*Λ` has the
local representation `(s'ᵢ, σᵢ)`, `s'ᵢ(y') = μ'(τ(y'), Φ(sᵢ(g(s'(τ(y'))))))`, on an open
`O' ∋ x₀'`, with `τ` a local inverse of `t'` at `σ'` and `g` one of `ϕ` at `x` (the text: `σ'`
extends to a local sc-diffeomorphism by `t ∘ s⁻¹`).  On the level `[1]`,
`s'ᵢ = μ'[1] ∘ (τ, Φ[1] ∘ sᵢ[1] ∘ g ∘ s' ∘ τ)`. -/
theorem exists_isLocalRepOn_pushMult (hF : SEP.equivalences F) {Λ : C.W → ℚ≥0}
    (hΛ : IsWFunctor C Λ) {x : C.Obj} {x₀' : A.Obj} {σ' : A.Mor}
    (hs : A.X.src σ' = (SEP.Hom.ϕ F).obj x) (ht : A.X.tgt σ' = x₀') {O : Set C.Obj}
    (hO : IsOpen O) (hxO : x ∈ O) {k : ℕ} {s : Fin k → C.Obj → C.W} {σ : Fin k → ℚ≥0}
    (h : IsLocalRepOn C Λ O s σ) :
    ∃ (O' : Set A.Obj) (s' : Fin k → A.Obj → A.W), IsOpen O' ∧ x₀' ∈ O' ∧
      IsLocalRepOn A (pushMult F hF Λ) O' s' σ := by
  classical
  obtain ⟨T, V, τ, hσT, hτ⟩ := A.X.isLocalScDiffeo_tgt σ'
  obtain ⟨U₁, U₁', g, hxU₁, hg⟩ := (sbe hF).isEquivalence_base.isLocalScDiffeo_obj x
  choose G hGval hGsm using fun i => (h.2.1 i).2
  have hFs := (SEP.Hom.isStrongBundleFunctor F).isStrongBundleMap_obj
  set N₀ : Set A.Obj := V ∩ τ ⁻¹' (A.X.src ⁻¹' U₁') with hN₀def
  have hN₀ : IsOpen N₀ := hτ.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hτ.isOpen_target
    (hg.isOpen_target.preimage A.X.continuous_src)
  set a : A.Obj → C.Obj := fun y' => g (A.X.src (τ y')) with hadef
  have haN₀ : A.X.PObj.IsScSmoothOn C.X.PObj a N₀ :=
    MPolyfold.IsScSmoothOn.comp hg.isScSmoothOn_inv
      (MPolyfold.IsScSmoothOn.comp A.X.isScSmoothMap_src
        (hτ.isScSmoothOn_inv.mono hN₀ inter_subset_left) (mapsTo_univ _ _)) fun y' hy' => hy'.2
  set O' : Set A.Obj := N₀ ∩ a ⁻¹' O with hO'def
  have hO' : IsOpen O' := haN₀.continuousOn.isOpen_inter_preimage hN₀ hO
  have hτx : τ x₀' = σ' := by rw [← ht]; exact hτ.left_inv σ' hσT
  have hx₀' : x₀' ∈ O' := by
    have hV : x₀' ∈ V := by rw [← ht]; exact hτ.mapsTo hσT
    have hU : A.X.src (τ x₀') ∈ U₁' := by rw [hτx, hs]; exact hg.mapsTo hxU₁
    refine ⟨⟨hV, hU⟩, ?_⟩
    change g (A.X.src (τ x₀')) ∈ O
    rw [hτx, hs, hg.left_inv x hxU₁]; exact hxO
  have hϕa : ∀ y' ∈ O', (SEP.Hom.ϕ F).obj (a y') = A.X.src (τ y') := fun y' hy' =>
    hg.right_inv _ hy'.1.2
  -- the level-`[1]` data
  let b : Fin k → A.Obj → A.W := fun i y' => (SEP.Hom.Φ F).obj (C.B.oneVal (G i (a y')))
  have hbs : ∀ i, ∀ y' ∈ O', b i y' = (SEP.Hom.Φ F).obj (s i (a y')) := fun i y' hy' => by
    change (SEP.Hom.Φ F).obj (C.B.oneVal (G i (a y'))) = _
    rw [hGval i _ hy'.2]
  have hPb : ∀ i, ∀ y' ∈ O', A.P (b i y') = A.X.src (τ y') := fun i y' hy' => by
    rw [hbs i y' hy', hFs.covers, (h.2.1 i).1 _ hy'.2, hϕa y' hy']
  let ι : Fin k → A.Obj → pullbackSpace A.P A.X.src := fun i y' =>
    if hx : A.P (b i y') = A.X.src (τ y') then ⟨(τ y', b i y'), hx⟩
    else ⟨(A.X.unit (A.P (b i y')), b i y'), (A.X.src_unit _).symm⟩
  have hι : ∀ i y' (hy' : y' ∈ O'), ι i y' = ⟨(τ y', b i y'), hPb i y' hy'⟩ := fun i y' hy' =>
    dif_pos (hPb i y' hy')
  have hι2 : ∀ i y', (ι i y' : A.Mor × A.W).2 = b i y' := fun i y' => by
    dsimp only [ι]; split_ifs <;> rfl
  have hι1 : ∀ i y', ι i y' ∈ (A.B.pullback A.X.isScSmoothMap_src).oneSet := fun i y' =>
    (A.B.mem_oneSet_pullback_iff A.X.isScSmoothMap_src _).2
      (by rw [hι2]; exact hFs.mapsTo_oneSet (C.B.oneVal_mem _))
  let ι₁ : Fin k → A.Obj → (A.B.pullback A.X.isScSmoothMap_src).One := fun i y' =>
    (A.B.pullback A.X.isScSmoothMap_src).oneMk (ι i y') (hι1 i y')
  let s' : Fin k → A.Obj → A.W := fun i y' => A.E.μ (ι i y')
  have hsec : ∀ i, ∀ y' ∈ O', A.P (s' i y') = y' := fun i y' hy' => by
    change A.P (A.E.μ (ι i y')) = y'
    rw [A.E.P_μ, hι i y' hy']
    exact hτ.right_inv y' hy'.1.1
  have hsm : ∀ i, A.X.PObj.IsScSmoothOn A.B.toMPolyfold1
      (oneRestrict _ A.B A.E.μ A.E.isStrongBundleMap.mapsTo_oneSet ∘ ι₁ i) O' := fun i => by
    have hτO' : A.X.PObj.IsScSmoothOn A.X.PMor τ O' :=
      hτ.isScSmoothOn_inv.mono hO' fun y' hy' => hy'.1.1
    have ha : A.X.PObj.IsScSmoothOn A.X.PMor
        (pullbackProj A.P A.X.src ∘ (A.B.pullback A.X.isScSmoothMap_src).oneVal ∘ ι₁ i) O' :=
      hτO'.congr fun y' hy' => by
        change τ y' = (ι i y' : A.Mor × A.W).1
        rw [hι i y' hy']
    have hb1 : A.X.PObj.IsScSmoothOn A.B.toMPolyfold1
        (A.B.pullbackProj'One A.X.isScSmoothMap_src ∘ ι₁ i) O' := by
      refine (MPolyfold.IsScSmoothOn.comp hFs.isScSmoothMap_one
        (MPolyfold.IsScSmoothOn.comp (hGsm i) (haN₀.mono hO' inter_subset_left)
          fun y' hy' => hy'.2) (mapsTo_univ _ _)).congr fun y' _ => A.B.oneVal_injective ?_
      change (SEP.Hom.Φ F).obj (C.B.oneVal (G i (a y'))) = (ι i y' : A.Mor × A.W).2
      rw [hι2]
    exact MPolyfold.IsScSmoothOn.comp A.E.isStrongBundleMap.isScSmoothMap_one
      (A.B.isScSmoothOn_to_pullback_one A.X.isScSmoothMap_src ha hb1) (mapsTo_univ _ _)
  refine ⟨O', s', hO', hx₀', h.1, fun i => ⟨hsec i, _, fun y' _ => rfl, hsm i⟩, h.2.2.1,
    fun w' hw' => ?_⟩
  -- the formula: `Φ_*Λ(w') = Λ(w)` for `w = Φ⁻¹(μ'(τ(y')⁻¹, w'))` over `a(y')`
  set y' := A.P w' with hy'def
  have hw'1 : A.P w' = A.X.src (A.X.inv (τ y')) := by
    rw [A.X.src_inv]; exact (hτ.right_inv y' hw'.1.1).symm
  set m := A.E.μ ⟨(A.X.inv (τ y'), w'), hw'1⟩ with hmdef
  have hm : A.P m = (SEP.Hom.ϕ F).obj (a y') := by
    rw [hmdef, A.E.P_μ, hϕa y' hw']; exact A.X.tgt_inv _
  set v := ((sbe hF).fiberEquiv (a y')).symm ⟨m, hm⟩ with hvdef
  have hΦv : (SEP.Hom.Φ F).obj (v : C.W) = m := by
    rw [← (sbe hF).fiberEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hPv : C.P (v : C.W) = a y' := v.2
  have hπ : A.E.toEpGroupoid.π ((SEP.Hom.Φ F).obj (v : C.W)) = A.E.toEpGroupoid.π w' := by
    rw [hΦv, hmdef, EpStrongBundle.π_μ]
  rw [pushMult_eq hF hΛ hπ, h.2.2.2 _ (by rw [hPv]; exact hw'.2), hPv]
  refine Finset.sum_congr rfl fun i _ => if_congr ?_ rfl rfl
  have hs'i : s' i y' = A.E.μ ⟨(τ y', b i y'), hPb i y' hw'⟩ := by
    change A.E.μ (ι i y') = _
    rw [hι i y' hw']
  rw [hs'i]
  constructor
  · intro e
    have hb : b i y' = m := by rw [hbs i y' hw', ← e, hΦv]
    have h' : A.P (A.E.μ ⟨(A.X.inv (τ y'), w'), hw'1⟩) = A.X.src (τ y') := by
      change A.P m = _; rw [← hb]; exact hPb i y' hw'
    refine (A.E.μ_μ_inv (τ y') w' hw'1 h').symm.trans (A.E.μ_congr ?_)
    exact Prod.ext rfl hb.symm
  · intro e
    have hm' : m = b i y' := by
      have h' : A.P (A.E.μ ⟨(τ y', b i y'), hPb i y' hw'⟩) =
          A.X.src (A.X.inv ((⟨(τ y', b i y'), hPb i y' hw'⟩ : pullbackSpace A.P A.X.src) :
            A.Mor × A.W).1) := by
        rw [A.E.P_μ, A.X.src_inv]
      refine Eq.trans (A.E.μ_congr ?_) (A.E.μ_inv_μ _ h')
      exact Prod.ext rfl e
    refine (sbe hF).eq_of_obj_eq (hPv.trans ((h.2.1 i).1 _ hw'.2).symm) ?_
    rw [hΦv, hm', hbs i y' hw']

/-- **2021 Lemma 11.5.2, p. 548 (2017: Lemma 11.7, p. 400), with the local section structures**:
for a strong bundle equivalence `Φ` and an sc⁺-multisection `Λ` of `W''`, the push-forward
`Φ_*Λ` is an sc⁺-multisection (a functor by `lemma_11_5_2`, with the local section structure
`s'ᵢ(y') = μ'(σ', Φ(sᵢ(x)))` extended by `t ∘ s⁻¹`, as on p. 548). -/
theorem lemma_11_5_2_book (hF : SEP.equivalences F) {Λ : C.W → ℚ≥0}
    (hΛ : IsScPlusMultisection C Λ) : IsScPlusMultisection A (pushMult F hF Λ) := by
  refine ⟨lemma_11_5_2 hF hΛ.1, fun x₀' => ?_⟩
  obtain ⟨x, σ', hs, ht⟩ := (sbe hF).isEquivalence_base.exists_iso x₀'
  obtain ⟨R, k, s, σ, h⟩ := hΛ.2 x
  obtain ⟨O', s', hO', hx₀', hrep⟩ :=
    exists_isLocalRepOn_pushMult hF hΛ.1 hs ht R.isOpen_U R.mem_U h
  exact hasLocalSectionStructure_of_isLocalRepOn hO' hx₀' hrep

namespace SDiagram

variable {D : SDiagram A A'} (hΨ : SEP.equivalences D.Ψ)

/-- `[D]_*Λ = Ψ_* Φ^* Λ` is an sc⁺-multisection when `Λ` is one. -/
theorem isScPlusMultisection_pushMult {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) :
    IsScPlusMultisection A' (D.pushMult hΨ Λ) :=
  lemma_11_5_2_book hΨ (SBLocalization.isScPlusMultisection_pullMult D.isEquivalence_Φ hΛ)

/-- `[D]^*Λ' = Φ_* Ψ^* Λ'` is an sc⁺-multisection when `Λ'` is one. -/
theorem isScPlusMultisection_pullMult {Λ' : A'.W → ℚ≥0} (hΛ' : IsScPlusMultisection A' Λ') :
    IsScPlusMultisection A (D.pullMult hΨ Λ') :=
  isScPlusMultisection_pushMult (D := D.symm hΨ) D.isEquivalence_Φ hΛ'

end SDiagram

namespace GenSBMap

variable {f : GenSBMap A A'} (hf : f.IsGeneralizedIso)

/-- **2021 Proposition 11.5.3, p. 548 (2017: Proposition 11.7, p. 401)**, for sc⁺-multisections
in the sense of Definition 13.2.1 (functor and local section structures): for a generalized
strong bundle isomorphism `[D] : W → W'`, the push-forward `[D]_*Λ = Ψ_* Φ^* Λ` of an
sc⁺-multisection is an sc⁺-multisection, and so is the pull-back `[D]^*Λ'`; both are
independent of the representative, mutually inverse, and depend only on `|[D]|`.  The book's
statement, with no added hypothesis. -/
theorem proposition_11_5_3_book :
    (∀ Λ : A.W → ℚ≥0, IsScPlusMultisection A Λ → IsScPlusMultisection A' (pushMult hf Λ)) ∧
    (∀ Λ' : A'.W → ℚ≥0, IsScPlusMultisection A' Λ' → IsScPlusMultisection A (pullMult hf Λ')) ∧
    (∀ (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ), D.cls = f →
      (∀ Λ : A.W → ℚ≥0, IsScPlusMultisection A Λ → pushMult hf Λ = D.pushMult hΨ Λ) ∧
      ∀ Λ' : A'.W → ℚ≥0, IsScPlusMultisection A' Λ' → pullMult hf Λ' = D.pullMult hΨ Λ') ∧
    (∀ Λ : A.W → ℚ≥0, IsScPlusMultisection A Λ → pullMult hf (pushMult hf Λ) = Λ) ∧
    (∀ Λ' : A'.W → ℚ≥0, IsScPlusMultisection A' Λ' → pushMult hf (pullMult hf Λ') = Λ') ∧
    (∀ {g : GenSBMap A A'} (hg : g.IsGeneralizedIso), f.orbitMap = g.orbitMap →
      (∀ Λ : A.W → ℚ≥0, IsScPlusMultisection A Λ → pushMult hf Λ = pushMult hg Λ) ∧
      ∀ Λ' : A'.W → ℚ≥0, IsScPlusMultisection A' Λ' → pullMult hf Λ' = pullMult hg Λ') := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := proposition_11_5_3 hf
  exact ⟨fun Λ hΛ => SDiagram.isScPlusMultisection_pushMult _ hΛ,
    fun Λ' hΛ' => SDiagram.isScPlusMultisection_pullMult _ hΛ',
    fun D hΨ hD => ⟨fun Λ hΛ => h1 D hΨ hD Λ hΛ.1, fun Λ' hΛ' => h2 D hΨ hD Λ' hΛ'.1⟩,
    fun Λ hΛ => (h3 Λ hΛ.1).2, fun Λ' hΛ' => (h4 Λ' hΛ'.1).2,
    fun hg hfg => ⟨fun Λ hΛ => (h5 hg hfg).1 Λ hΛ.1, fun Λ' hΛ' => (h5 hg hfg).2 Λ' hΛ'.1⟩⟩

end GenSBMap

end SBLocalization

end Polyfold
