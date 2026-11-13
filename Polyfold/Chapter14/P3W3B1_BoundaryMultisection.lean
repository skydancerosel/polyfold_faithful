import Polyfold.Chapter14.P3W3B1_GoodBoundary
import Polyfold.Chapter13.P3G_GoodSystemExistence
import Polyfold.Chapter13.P3M_MultisectionSymmetric
import Polyfold.Chapter5.P3B_BoundaryExtension2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.1, pp. 642–643:
**Definition 14.1.3** (sc⁺-multisection over `∂X`), **Proposition 14.1.4** (local extension),
**Definition 14.1.5** (good system of neighbourhoods for `∂X`) and **Theorem 14.1.6** (existence)
(2017: Definitions 14.2, 14.3, Remark 14.2, Theorem 14.1).

# Sc⁺-multisections over the boundary

## The text, paraphrased

(Definition 14.1.3) For a strong bundle over a tame ep-groupoid with paracompact `|X|`, a functor
`Λ : W|∂X → ℚ⁺` is an sc⁺-multisection over `∂X` if every `x ∈ ∂X` has a good open neighbourhood
`U(x)` in `∂X`, a finite index set `I_x` with a `G_x`-action and sections `(sˣᵢ)` over `U(x)` with
(1) `sˣᵢ|θ̄_j` an sc⁺-section of `W|θ̄_j` for every face `θ̄_j`, (2)
`sˣ_{g(i)}(g ∗ y) = μ(Γ(g, y), sˣᵢ(y))` on `U(x)`, (3) `Λ(w) = |I_x|⁻¹·#{i | sˣᵢ(P(w)) = w}` over
`U(x)`.  (Proposition 14.1.4) If `X` admits sc-smooth partitions of unity, such a structure on
`U(x) = V(x) ∩ ∂X` extends to sc⁺-sections `s̄ᵢ` on `V(x)` with the same symmetry: extend each
`sᵢ` (Proposition 12.3.7 and a partition of unity), average over the stabiliser of `i`, and
transport along the orbit of `i`.  (Definition 14.1.5) `(U(x))_{x ∈ ∂X}` is a good system for `∂X` if
the `U(x)` are good and, for good `V(x)`, `V(x')` restricting to them, every component of
`V(x, x') = {ψ | s(ψ) ∈ V(x), t(ψ) ∈ V(x')}` maps by `s` and `t` sc-diffeomorphically onto open
sets.  (Theorem 14.1.6) For `|∂X|` paracompact, every open cover `(O(x))` of `∂X` has a good system
with `U(x) ⊆ O(x)`; proof: Theorem 13.1.8 on `X`, then Proposition 14.1.1.

## What is formalized

* (1) of Definition 14.1.3 is `IsFaceScPlusSectionOn A s U`: Definition 5.4.1
  (`StrongBundle.IsBoundaryScPlusSection`) with `∂X` replaced by `U`: in every tame strong bundle
  chart, at every point of `U`, `s` is sc⁺ on every local face germ.  The local faces at a point of
  `U(x)` are the germs of the `θ̄_j` through it, so this is "`s|θ̄_j` is sc⁺ for every `j`".
* **Definition 14.1.3**: `BoundarySymmetricStructure A Λ V` (on `U(x) = V.bdry` for a good `V`),
  `IsBoundaryWFunctor` (a functor on `W|∂X`: invariance along morphisms with source in `∂X`) and
  `IsBoundaryScPlusMultisection`.  Witness: `isBoundaryScPlusMultisection_zero` (the zero
  multisection, for tame `X`).
* **Proposition 14.1.4**: `proposition_14_1_4_hyp`: from any sc⁺-sections `s⁰ᵢ` on `V(x)` with
  `s⁰ᵢ = sᵢ` on `U(x)` the average `s̄_j(y) = |G_x|⁻¹ ∑_g μ(Γ(g⁻¹, g ∗ y), s⁰_{g(j)}(g ∗ y))` is
  an equivariant extension (Definition 13.2.5 (1)).  The existence of the `s⁰ᵢ` on all of
  `V(x)` (the "partition of unity argument" of the text on the open set `V(x)`) is the added
  hypothesis; see the hand-over note.
* **Definition 14.1.5**: `BoundaryGoodSystem` (indexed by the points of `∂X`), with `U x`
  (`U(x)`), `mor x x'` (`𝒰(x, x')`, the morphisms between points of `U(x)` and `U(x')`), the
  inheritance of condition (2) by subsets, and refinements `exists_refinement`.
* **Theorem 14.1.6**: `theorem_14_1_6_hyp` for tame `X` with paracompact `|X|` (the text's proof
  applies Theorem 13.1.8 to `X` and Proposition 14.1.1).
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

open scoped Classical

noncomputable section

namespace Polyfold

universe u

/-! ### Definition 14.1.5 -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **2021 Definition 14.1.5, p. 643 (2017: Definition 14.3)**: a **good system of
neighbourhoods for `∂X`**: for every `x ∈ ∂X` a good open neighbourhood `V(x)` of `x` in `X`
(Definition 14.1.2; `U(x) = V(x) ∩ ∂X`), such that for all `x, x' ∈ ∂X` and every connected
component `Σ` of `V(x, x') = {ψ | s(ψ) ∈ V(x), t(ψ) ∈ V(x')}` the maps `s : Σ → V(x)` and
`t : Σ → V(x')` are sc-diffeomorphisms onto open subsets. -/
structure BoundaryGoodSystem where
  /-- `V(x)` with the natural `G_x`-action. -/
  nbhd : ∀ x : X.PObj.boundary, X.NatNbhd x
  /-- (1) the `V(x)` are good. -/
  isGood : ∀ x, X.IsGoodBoundaryNbhd (nbhd x)
  /-- (2) the components of `V(x, x')`. -/
  isDiffeoComponent : ∀ x x', ∀ φ ∈ X.morBetween (nbhd x).U (nbhd x').U,
    X.IsDiffeoComponent (connectedComponentIn (X.morBetween (nbhd x).U (nbhd x').U) φ)

namespace BoundaryGoodSystem

variable {X} (𝒰 : X.BoundaryGoodSystem)

/-- `U(x) = V(x) ∩ ∂X`. -/
def U (x : X.PObj.boundary) : Set Obj := (𝒰.nbhd x).bdry

/-- **`𝒰(x, x')`** (Definition 14.1.7 (2)): the morphisms `φ` with `s(φ) ∈ U(x)`,
`t(φ) ∈ U(x')` (morphisms of `∂X`). -/
def mor (x x' : X.PObj.boundary) : Set Mor := X.morBetween (𝒰.U x) (𝒰.U x')

theorem mem_U (x : X.PObj.boundary) : (x : Obj) ∈ 𝒰.U x :=
  ⟨(𝒰.nbhd x).mem_U, x.2⟩

theorem U_subset_boundary (x : X.PObj.boundary) : 𝒰.U x ⊆ X.PObj.boundary := inter_subset_right

theorem mor_subset (x x' : X.PObj.boundary) :
    𝒰.mor x x' ⊆ X.morBetween (𝒰.nbhd x).U (𝒰.nbhd x').U :=
  morBetween_mono inter_subset_left inter_subset_left

/-- Condition (2) passes to open subsets of the `V(x)`. -/
theorem isDiffeoComponent_of_subset {x x' : X.PObj.boundary} {A A' : Set Obj} (hA : IsOpen A)
    (hA' : IsOpen A') (hAU : A ⊆ (𝒰.nbhd x).U) (hA'U : A' ⊆ (𝒰.nbhd x').U) {φ : Mor}
    (hφ : φ ∈ X.morBetween A A') :
    X.IsDiffeoComponent (connectedComponentIn (X.morBetween A A') φ) := by
  have hsub : X.morBetween A A' ⊆ X.morBetween (𝒰.nbhd x).U (𝒰.nbhd x').U :=
    morBetween_mono hAU hA'U
  exact (𝒰.isDiffeoComponent x x' φ (hsub hφ)).mono
    (isOpen_connectedComponentIn_mor X (isOpen_morBetween hA hA') φ)
    (connectedComponentIn_mono φ hsub)

/-- **Refinement** (the boundary analogue of Proposition 13.1.3 and the remark after it): inside
open neighbourhoods `W(x)` of the points of `∂X` there is a good system for `∂X` whose
neighbourhoods carry the natural actions of those of `𝒰` (tame `X`, Proposition 14.1.1). -/
theorem exists_refinement (hX : X.IsTame) (W : X.PObj.boundary → Set Obj)
    (hW : ∀ x, IsOpen (W x)) (hxW : ∀ x, (x : Obj) ∈ W x) :
    ∃ 𝒲 : X.BoundaryGoodSystem, (∀ x, (𝒲.nbhd x).Le (𝒰.nbhd x)) ∧
      ∀ x, (𝒲.nbhd x).U ⊆ W x := by
  choose V hrep hsub hgood using fun x : X.PObj.boundary =>
    exists_isGoodBoundaryNbhd_le hX x.2 (𝒰.nbhd x) (𝒰.isGood x).isProperSubset_closure (hW x)
      (hxW x)
  refine ⟨⟨V, hgood, fun x x' φ hφ => 𝒰.isDiffeoComponent_of_subset (V x).isOpen_U
    (V x').isOpen_U (fun y hy => (hsub x hy).1) (fun y hy => (hsub x' hy).1) hφ⟩,
    fun x => NatNbhd.le_of_rep_eq (hrep x) fun y hy => (hsub x hy).1,
    fun x y hy => (hsub x hy).2⟩

end BoundaryGoodSystem

/-! ### Theorem 14.1.6 -/

/-- **2021 Theorem 14.1.6, p. 643 (2017: Theorem 14.1)**, for tame `X` with paracompact `|X|`:
for open neighbourhoods `O(x)` (in `X`) of the points `x ∈ ∂X` there is a good system of
neighbourhoods for `∂X` with `V(x) ⊆ O(x)`, so `U(x) ⊆ O(x) ∩ ∂X`.  (The text assumes `|∂X|`
paracompact; its proof applies Theorem 13.1.8 to `X`, which needs `|X|` paracompact, and
Proposition 14.1.1, which needs `X` tame.  A cover of `∂X` by sets open in `∂X` is
`(O(x) ∩ ∂X)` for sets `O(x)` open in `X`.) -/
theorem theorem_14_1_6_hyp (hX : X.IsTame) (hpara : X.HasParacompactOrbitSpace)
    (O : X.PObj.boundary → Set Obj) (hO : ∀ x, IsOpen (O x)) (hxO : ∀ x, (x : Obj) ∈ O x) :
    ∃ 𝒰 : X.BoundaryGoodSystem, ∀ x, (𝒰.nbhd x).U ⊆ O x ∧ 𝒰.U x ⊆ O x ∩ X.PObj.boundary := by
  classical
  let W : Obj → Set Obj := fun y => if h : y ∈ X.PObj.boundary then O ⟨y, h⟩ else univ
  have hW : ∀ y, IsOpen (W y) := fun y => by
    dsimp only [W]; split_ifs with h
    · exact hO _
    · exact isOpen_univ
  have hyW : ∀ y, y ∈ W y := fun y => by
    dsimp only [W]; split_ifs with h
    · exact hxO ⟨y, h⟩
    · exact mem_univ y
  obtain ⟨𝒰₀, h𝒰₀⟩ := X.theorem_13_1_8 hpara W hW hyW
  have hWx : ∀ x : X.PObj.boundary, W x = O x := fun x => by
    dsimp only [W]; rw [dif_pos x.2]
  choose V hrep hsub hgood using fun x : X.PObj.boundary =>
    exists_isGoodBoundaryNbhd_le hX x.2 (𝒰₀.nbhd x) (𝒰₀.isProperSubset_closure x) isOpen_univ
      (mem_univ _)
  refine ⟨⟨V, hgood, fun x x' φ hφ => 𝒰₀.isDiffeoComponent_of_subset (V x).isOpen_U
    (V x').isOpen_U (fun y hy => (hsub x hy).1) (fun y hy => (hsub x' hy).1) hφ⟩,
    fun x => ⟨fun y hy => ?_, fun y hy => ⟨?_, hy.2⟩⟩⟩
  · rw [← hWx]; exact h𝒰₀ x (hsub x hy).1
  · rw [← hWx]; exact h𝒰₀ x (hsub x hy.1).1

end EpGroupoid

/-! ### Definition 14.1.3 -/

namespace SBLocalization

open StrongBundle EpGroupoid SymmetricStructureOn

variable {A : SEP.{u}}

/-- **(1) of Definition 14.1.3**: `s` is a section with values in `W_{0,1}` over `U ⊆ ∂X` whose
restriction to every local face through every point of `U` is an sc⁺-section: Part I's
Definition 5.4.1 (`StrongBundle.IsBoundaryScPlusSection`) with `∂X` replaced by `U`, read in every
tame strong bundle chart and tame presentation of its corner. -/
def IsFaceScPlusSectionOn (A : SEP.{u}) (s : A.Obj → A.W) (U : Set A.Obj) : Prop :=
  (∀ x ∈ U, A.P (s x) = x ∧ s x ∈ A.B.oneSet) ∧
  ∀ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c →
    ∀ (n : ℕ) (W : ScBanach) (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)),
      c.φ.model.C = T 0 ⁻¹' quadrant n W 0 →
      ∀ x ∈ U ∩ c.φ.source, ∀ i ∈ zeroSet T (c.φ x),
        IsScPlusOnFaceNear T c.φ.model.C c.φ.model.O c.K (localRepOne c s) (c.φ x) i

theorem IsFaceScPlusSectionOn.mono {s : A.Obj → A.W} {U U' : Set A.Obj}
    (h : IsFaceScPlusSectionOn A s U) (hU' : U' ⊆ U) : IsFaceScPlusSectionOn A s U' :=
  ⟨fun x hx => h.1 x (hU' hx), fun c hc n W T hT x hx i hi =>
    h.2 c hc n W T hT x ⟨hU' hx.1, hx.2⟩ i hi⟩

/-- A section over `∂X` in the sense of Definition 5.4.1 restricts to every `U ⊆ ∂X`. -/
theorem isFaceScPlusSectionOn_of_isBoundaryScPlusSection {s : A.Obj → A.W}
    (h : A.B.IsBoundaryScPlusSection s) {U : Set A.Obj} (hU : U ⊆ A.X.PObj.boundary) :
    IsFaceScPlusSectionOn A s U :=
  ⟨fun x hx => h.1 x (hU hx), fun c hc n W T hT x hx i hi =>
    h.2 c hc n W T hT x ⟨hU hx.1, hx.2⟩ i hi⟩

/-- The zero section satisfies (1) of Definition 14.1.3 on every `U ⊆ ∂X`. -/
theorem isFaceScPlusSectionOn_fiberZero {U : Set A.Obj} (hU : U ⊆ A.X.PObj.boundary) :
    IsFaceScPlusSectionOn A (fiberZero A.P) U :=
  isFaceScPlusSectionOn_of_isBoundaryScPlusSection
    StrongBundle.isBoundaryScPlusSection_fiberZero hU

/-- **2021 Definition 14.1.3, p. 642 (2017: Definition 14.2)**, the local data: a **symmetric
sc⁺-section structure for `Λ` near `x` in `∂X`** on the good open neighbourhood
`U(x) = V.bdry` (`V : NatNbhd x` with the natural `G_x`-action): a finite index type `I_x` with a
`G_x`-action and sections `sᵢ` with (1) `sᵢ|θ̄_j` sc⁺ for every face (`IsFaceScPlusSectionOn`),
(2) `s_{g(i)}(g ∗ y) = μ(Γ(g, y), sᵢ(y))` on `U(x)`, (3) `Λ(w) = |I_x|⁻¹·#{i | sᵢ(P(w)) = w}`
for `P(w) ∈ U(x)`. -/
structure BoundarySymmetricStructure (A : SEP.{u}) (Λ : A.W → ℚ≥0) {x : A.Obj}
    (V : A.X.NatNbhd x) where
  /-- The index set `I_x`. -/
  I : Type u
  [fintype : Fintype I]
  [mulAction : MulAction (A.X.Isotropy x) I]
  /-- The sections `sˣᵢ`. -/
  s : I → A.Obj → A.W
  /-- (1) sc⁺ on the faces. -/
  isFaceScPlus : ∀ i, IsFaceScPlusSectionOn A (s i) V.bdry
  /-- (2) `s_{g(i)}(g ∗ y) = μ(Γ(g, y), sᵢ(y))`. -/
  equivariant : ∀ (g : A.X.Isotropy x) (i : I), ∀ y ∈ V.bdry,
    s (g • i) (V.rep.Φ g y) = fibAct (V.rep.Γ g y) (s i y)
  /-- (3) `Λ(w) = |I_x|⁻¹·#{i | sᵢ(P(w)) = w}`. -/
  rep : ∀ w, A.P w ∈ V.bdry →
    Λ w = (Fintype.card I : ℚ≥0)⁻¹ * ((Finset.univ.filter fun i => s i (A.P w) = w).card : ℚ≥0)

attribute [instance] BoundarySymmetricStructure.fintype BoundarySymmetricStructure.mulAction

namespace BoundarySymmetricStructure

variable {Λ : A.W → ℚ≥0} {x : A.Obj} {V : A.X.NatNbhd x}

theorem P_s (S : BoundarySymmetricStructure A Λ V) (i : S.I) {y : A.Obj} (hy : y ∈ V.bdry) :
    A.P (S.s i y) = y := ((S.isFaceScPlus i).1 y hy).1

/-- **Restriction** to a smaller neighbourhood with the same action. -/
def restrict (S : BoundarySymmetricStructure A Λ V) {V' : A.X.NatNbhd x} (h : V'.Le V) :
    BoundarySymmetricStructure A Λ V' where
  I := S.I
  s := S.s
  isFaceScPlus i := (S.isFaceScPlus i).mono (NatNbhd.bdry_mono h.subset)
  equivariant g i y hy := by
    rw [h.Φ_eq g hy.1, h.Γ_eq g y hy.1]
    exact S.equivariant g i y (NatNbhd.bdry_mono h.subset hy)
  rep w hw := S.rep w (NatNbhd.bdry_mono h.subset hw)

@[simp] theorem restrict_I (S : BoundarySymmetricStructure A Λ V) {V' : A.X.NatNbhd x}
    (h : V'.Le V) : (S.restrict h).I = S.I := rfl

@[simp] theorem restrict_s (S : BoundarySymmetricStructure A Λ V) {V' : A.X.NatNbhd x}
    (h : V'.Le V) : (S.restrict h).s = S.s := rfl

end BoundarySymmetricStructure

/-- **A functor `Λ : W|∂X → ℚ⁺`**: `Λ(μ(φ, w)) = Λ(w)` for every morphism `φ` with `s(φ) ∈ ∂X`
(then `t(φ) ∈ ∂X`; only the values of `Λ` over `∂X` enter). -/
def IsBoundaryWFunctor (A : SEP.{u}) (Λ : A.W → ℚ≥0) : Prop :=
  ∀ q : pullbackSpace A.P A.X.src, A.X.src (q : A.Mor × A.W).1 ∈ A.X.PObj.boundary →
    Λ (A.E.μ q) = Λ (q : A.Mor × A.W).2

/-- **2021 Definition 14.1.3, p. 642 (2017: Definition 14.2)**: `Λ : W|∂X → ℚ⁺` is an
**sc⁺-multisection over `∂X`** if it is a functor on `W|∂X` and every `x ∈ ∂X` has a good open
neighbourhood `U(x) = V(x) ∩ ∂X` in `∂X` carrying a symmetric sc⁺-section structure for `Λ`. -/
def IsBoundaryScPlusMultisection (A : SEP.{u}) (Λ : A.W → ℚ≥0) : Prop :=
  IsBoundaryWFunctor A Λ ∧ ∀ x ∈ A.X.PObj.boundary, ∃ V : A.X.NatNbhd x,
    A.X.IsGoodBoundaryNbhd V ∧ Nonempty (BoundarySymmetricStructure A Λ V)

/-! ### The zero multisection over `∂X` (nonvacuity) -/

/-- The symmetric structure `I_x = {∗}`, `s_∗ = 0` of the zero multisection, on any `V`. -/
def zeroBoundaryStructure {x : A.Obj} (V : A.X.NatNbhd x) :
    BoundarySymmetricStructure A (zeroMultisection A) V where
  I := PUnit.{u + 1}
  s _ := fiberZero A.P
  isFaceScPlus _ := isFaceScPlusSectionOn_fiberZero (NatNbhd.bdry_subset_boundary V)
  equivariant g _ y hy :=
    (fibAct_fiberZero (V.src_Γ g hy.1) (V.tgt_Γ g hy.1)).symm
  rep w _ := by
    by_cases h : w = fiberZero A.P (A.P w)
    · have e : (Finset.univ.filter fun _ : PUnit.{u + 1} => fiberZero A.P (A.P w) = w) =
          Finset.univ := Finset.filter_true_of_mem fun _ _ => h.symm
      rw [e]
      simp [zeroMultisection, if_pos h]
    · have e : (Finset.univ.filter fun _ : PUnit.{u + 1} => fiberZero A.P (A.P w) = w) = ∅ :=
        Finset.filter_false_of_mem fun _ _ e => h e.symm
      rw [e]
      simp [zeroMultisection, if_neg h]

/-- **Nonvacuity of Definition 14.1.3**: over a tame ep-groupoid, the zero multisection is an
sc⁺-multisection over `∂X`. -/
theorem isBoundaryScPlusMultisection_zero (hX : A.X.IsTame) :
    IsBoundaryScPlusMultisection A (zeroMultisection A) := by
  refine ⟨fun q _ => isWFunctor_zeroMultisection A q, fun x hx => ?_⟩
  obtain ⟨V, -, hV⟩ := A.X.exists_isGoodBoundaryNbhd hX hx isOpen_univ (mem_univ x)
  exact ⟨V, hV, ⟨zeroBoundaryStructure V⟩⟩

/-! ### Proposition 14.1.4 -/

/-- `μ(ψ ∘ γ, v) = μ(ψ, μ(γ, v))`. -/
theorem fibAct_comp_p3w3 {ψ γ : A.Mor} {v : A.W} (h₁ : A.P v = A.X.src γ)
    (h₂ : A.X.src ψ = A.X.tgt γ) : fibAct (A.X.comp ψ γ) v = fibAct ψ (fibAct γ v) := by
  have h₃ : A.P (A.E.μ ⟨(γ, v), h₁⟩) = A.X.src ψ := by rw [A.E.P_μ]; exact h₂.symm
  rw [fibAct_of (h₁.trans (A.X.src_comp ψ γ h₂).symm), fibAct_of h₁, fibAct_of h₃]
  exact A.E.μ_comp ψ γ v h₁ h₂

/-- `μ(1_y, v) = v`. -/
theorem fibAct_unit_p3w3 {v : A.W} {y : A.Obj} (h : A.P v = y) : fibAct (A.X.unit y) v = v := by
  subst h
  rw [fibAct_of (A.X.src_unit _).symm]
  exact A.E.μ_unit v

section Average

variable {x : A.Obj} (V : A.X.NatNbhd x) {I : Type u} [MulAction (A.X.Isotropy x) I]

/-- The translate `z ↦ μ(Γ(g⁻¹, g ∗ z), σ_{g(j)}(g ∗ z))` of the family `σ`. -/
def avgTerm (σ : I → A.Obj → A.W) (g : A.X.Isotropy x) (j : I) : A.Obj → A.W :=
  transportSection (fun z => V.rep.Γ g⁻¹ (V.rep.Φ g z)) (fun z => σ (g • j) (V.rep.Φ g z))

variable {V} {σ : I → A.Obj → A.W}

theorem src_Γ_inv_Φ (g : A.X.Isotropy x) {y : A.Obj} (hy : y ∈ V.U) :
    A.X.src (V.rep.Γ g⁻¹ (V.rep.Φ g y)) = V.rep.Φ g y := V.src_Γ g⁻¹ (V.Φ_mem g hy)

theorem tgt_Γ_inv_Φ (g : A.X.Isotropy x) {y : A.Obj} (hy : y ∈ V.U) :
    A.X.tgt (V.rep.Γ g⁻¹ (V.rep.Φ g y)) = y := by
  rw [V.tgt_Γ g⁻¹ (V.Φ_mem g hy), V.Φ_inv_Φ g hy]

theorem avgTerm_apply (hσ : ∀ k, ∀ y ∈ V.U, A.P (σ k y) = y) (g : A.X.Isotropy x) (j : I)
    {y : A.Obj} (hy : y ∈ V.U) :
    avgTerm V σ g j y = fibAct (V.rep.Γ g⁻¹ (V.rep.Φ g y)) (σ (g • j) (V.rep.Φ g y)) := by
  have h : A.P (σ (g • j) (V.rep.Φ g y)) = A.X.src (V.rep.Γ g⁻¹ (V.rep.Φ g y)) := by
    rw [hσ _ _ (V.Φ_mem g hy), src_Γ_inv_Φ g hy]
  unfold avgTerm
  rw [transportSection_of_mem (τ := fun z => V.rep.Γ g⁻¹ (V.rep.Φ g z))
    (b := fun z => σ (g • j) (V.rep.Φ g z)) h, fibAct_of h]

theorem isScPlusSectionOn_avgTerm (hσ : ∀ k, IsScPlusSectionOn A (σ k) V.U)
    (g : A.X.Isotropy x) (j : I) : IsScPlusSectionOn A (avgTerm V σ g j) V.U := by
  obtain ⟨hP, G, hG, hGs⟩ := hσ (g • j)
  have hΦ : A.X.PObj.IsScSmoothOn A.X.PObj (V.rep.Φ g) V.U :=
    (V.rep.isScDiffeoOn_Φ g).isScSmoothOn.mono V.isOpen_U V.U_subset
  have hτ : A.X.PObj.IsScSmoothOn A.X.PMor (V.rep.Γ g⁻¹ ∘ V.rep.Φ g) V.U :=
    MPolyfold.IsScSmoothOn.comp (V.rep.isScSmoothOn_Γ g⁻¹) hΦ fun y hy => V.U_subset
      (V.Φ_mem g hy)
  have hGc : A.X.PObj.IsScSmoothOn A.B.toMPolyfold1 (G ∘ V.rep.Φ g) V.U :=
    MPolyfold.IsScSmoothOn.comp hGs hΦ (V.mapsTo_Φ g)
  exact isScPlusSectionOn_transportSection hτ (G := G ∘ V.rep.Φ g)
    (fun z hz => hG _ (V.Φ_mem g hz)) hGc
    (fun z hz => by
      rw [hP _ (V.Φ_mem g hz), src_Γ_inv_Φ g hz])
    (fun z hz => tgt_Γ_inv_Φ g hz)

theorem P_avgTerm (hσ : ∀ k, IsScPlusSectionOn A (σ k) V.U) (g : A.X.Isotropy x) (j : I)
    {y : A.Obj} (hy : y ∈ V.U) : A.P (avgTerm V σ g j y) = y :=
  (isScPlusSectionOn_avgTerm hσ g j).1 y hy

/-- **The key identity of the averaging**: `μ(Γ(h, y), term_{gh, j}(y)) = term_{g, h(j)}(h ∗ y)`. -/
theorem avgTerm_equivariant (hσ : ∀ k, ∀ y ∈ V.U, A.P (σ k y) = y) (g h : A.X.Isotropy x)
    (j : I) {y : A.Obj} (hy : y ∈ V.U) :
    avgTerm V σ g (h • j) (V.rep.Φ h y) = fibAct (V.rep.Γ h y) (avgTerm V σ (g * h) j y) := by
  have hhy := V.Φ_mem h hy
  set z := V.rep.Φ (g * h) y with hz_def
  have hz : z ∈ V.U := V.Φ_mem _ hy
  have hzz : V.rep.Φ g (V.rep.Φ h y) = z := (V.Φ_mul g h hy).symm
  rw [avgTerm_apply hσ g (h • j) hhy, avgTerm_apply hσ (g * h) j hy, hzz, smul_smul]
  have h₁ : A.P (σ ((g * h) • j) z) = A.X.src (V.rep.Γ (g * h)⁻¹ z) := by
    rw [hσ _ _ hz, V.src_Γ _ hz]
  have h₂ : A.X.src (V.rep.Γ h y) = A.X.tgt (V.rep.Γ (g * h)⁻¹ z) := by
    rw [V.src_Γ h hy, V.tgt_Γ _ hz, hz_def, V.Φ_inv_Φ _ hy]
  rw [← fibAct_comp_p3w3 h₁ h₂]
  congr 1
  have hyz : V.rep.Φ (g * h)⁻¹ z = y := V.Φ_inv_Φ _ hy
  have e := V.Γ_mul h (g * h)⁻¹ hz
  rw [hyz] at e
  rw [e, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]

variable [Fintype (A.X.Isotropy x)]

variable (V σ) in
/-- **The average** `s̄_j(y) = |G_x|⁻¹ ∑_g μ(Γ(g⁻¹, g ∗ y), σ_{g(j)}(g ∗ y))` (Proposition 14.1.4;
the text averages one extension over the stabiliser `H` of `j` and transports it along the orbit
of `j`; we average over all of `G_x`, which needs no choice of orbit representatives). -/
def avgSection (j : I) : A.Obj → A.W :=
  smulSection V.U (fun _ => ((Fintype.card (A.X.Isotropy x) : ℝ))⁻¹)
    (sumSection V.U fun g => avgTerm V σ g j)

theorem isSection_sumSection_p3w3 {ι : Type*} [Fintype ι] (U : Set A.Obj)
    (s : ι → A.Obj → A.W) : IsSection A.P (sumSection U s) := fun y => by
  rw [sumSection, sectionSum_apply fun i => isSection_extendZero U (s i)]
  exact (_ : A.P ⁻¹' {y}).2

theorem isScPlusSectionOn_avgSection (hσ : ∀ k, IsScPlusSectionOn A (σ k) V.U) (j : I) :
    IsScPlusSectionOn A (avgSection V σ j) V.U := by
  have hsum : IsScPlusSectionOn A (sumSection V.U fun g => avgTerm V σ g j) V.U :=
    isScPlusSectionOn_sectionSum Finset.univ V.isOpen_U
      (fun g => (isScPlusSectionOn_avgTerm hσ g j).extendZero)
      (fun g => isSection_extendZero _ _)
  exact IsScPlusSectionOn.sectionSmul_const V.isOpen_U hsum.extendZero
    (isSection_extendZero _ _) _

/-- The value of the average in the fibre over `y ∈ V.U`. -/
theorem avgSection_apply (hσ : ∀ k, IsScPlusSectionOn A (σ k) V.U) (j : I) {y : A.Obj}
    (hy : y ∈ V.U) :
    avgSection V σ j y = ((((Fintype.card (A.X.Isotropy x) : ℝ))⁻¹ •
      ∑ g, (⟨avgTerm V σ g j y, P_avgTerm hσ g j hy⟩ : A.P ⁻¹' {y}) : A.P ⁻¹' {y}) : A.W) := by
  have hsum : A.P ((sumSection V.U fun g => avgTerm V σ g j) y) = y :=
    isSection_sumSection_p3w3 _ _ y
  rw [avgSection, smulSection_apply hy hsum]
  congr 2
  exact Subtype.ext (sumSection_apply hy fun g => P_avgTerm hσ g j hy)

/-- **The average is equivariant**: `s̄_{h(j)}(h ∗ y) = μ(Γ(h, y), s̄_j(y))` on `V.U`. -/
theorem avgSection_equivariant (hσ : ∀ k, IsScPlusSectionOn A (σ k) V.U)
    (h : A.X.Isotropy x) (j : I) {y : A.Obj} (hy : y ∈ V.U) :
    avgSection V σ (h • j) (V.rep.Φ h y) = fibAct (V.rep.Γ h y) (avgSection V σ j y) := by
  have hhy := V.Φ_mem h hy
  have hsrc : A.X.src (V.rep.Γ h y) = y := V.src_Γ h hy
  have htgt : A.X.tgt (V.rep.Γ h y) = V.rep.Φ h y := V.tgt_Γ h hy
  -- reindex the sum at `y` by `g ↦ g h`
  have hre : sumSection V.U (fun g => avgTerm V σ g j) y =
      sectionSum A.P Finset.univ (fun g => extendZero V.U (avgTerm V σ (g * h) j)) y := by
    rw [sumSection, sectionSum_apply fun g => isSection_extendZero V.U _,
      sectionSum_apply fun g => isSection_extendZero V.U _]
    congr 1
    exact (Equiv.sum_comp (Equiv.mulRight h)
      (fun g => (⟨extendZero V.U (avgTerm V σ g j) y, isSection_extendZero V.U _ y⟩ :
        A.P ⁻¹' {y}))).symm
  have hS : sumSection V.U (fun g => avgTerm V σ g (h • j)) (V.rep.Φ h y) =
      fibAct (V.rep.Γ h y) (sumSection V.U (fun g => avgTerm V σ g j) y) := by
    rw [hre]
    refine (fibAct_sectionSum Finset.univ (fun g => isSection_extendZero V.U _)
      (fun g => isSection_extendZero V.U _) hsrc htgt fun g => ?_).symm
    rw [← extendZero_eqOn (fun z hz => P_avgTerm hσ g (h • j) hz) hhy,
      ← extendZero_eqOn (fun z hz => P_avgTerm hσ (g * h) j hz) hy]
    exact avgTerm_equivariant (fun k => (hσ k).1) g h j hy
  unfold avgSection smulSection
  refine (fibAct_sectionSmul (isSection_extendZero _ _) (isSection_extendZero _ _) hsrc htgt rfl
    ?_).symm
  rw [← extendZero_eqOn (fun z _ => isSection_sumSection_p3w3 V.U _ z) hhy,
    ← extendZero_eqOn (fun z _ => isSection_sumSection_p3w3 V.U _ z) hy]
  exact hS

/-- **The average extends an equivariant family**: if `σ_{g(j)}(g ∗ y) = μ(Γ(g, y), σ_j(y))` on an
invariant `B ⊆ V.U`, then `s̄_j = σ_j` on `B`. -/
theorem avgSection_eq_of_equivariant (hσ : ∀ k, IsScPlusSectionOn A (σ k) V.U) {B : Set A.Obj}
    (hBU : B ⊆ V.U)
    (heq : ∀ g j, ∀ y ∈ B, σ (g • j) (V.rep.Φ g y) = fibAct (V.rep.Γ g y) (σ j y)) (j : I)
    {y : A.Obj} (hy : y ∈ B) : avgSection V σ j y = σ j y := by
  have hyU := hBU hy
  have hP : A.P (σ j y) = y := (hσ j).1 y hyU
  have hterm : ∀ g, avgTerm V σ g j y = σ j y := fun g => by
    rw [avgTerm_apply (fun k => (hσ k).1) g j hyU, heq g j y hy,
      ← fibAct_comp_p3w3 (by rw [hP, V.src_Γ g hyU]) (by rw [V.src_Γ _ (V.Φ_mem g hyU),
        V.tgt_Γ g hyU]), V.Γ_mul g⁻¹ g hyU, inv_mul_cancel, V.Γ_one hyU]
    exact fibAct_unit_p3w3 hP
  rw [avgSection_apply hσ j hyU]
  have hsum : (∑ g, (⟨avgTerm V σ g j y, P_avgTerm hσ g j hyU⟩ : A.P ⁻¹' {y})) =
      (Fintype.card (A.X.Isotropy x) : ℝ) • (⟨σ j y, hP⟩ : A.P ⁻¹' {y}) := by
    rw [Finset.sum_congr rfl fun g _ => (Subtype.ext (hterm g) :
      (⟨avgTerm V σ g j y, P_avgTerm hσ g j hyU⟩ : A.P ⁻¹' {y}) = ⟨σ j y, hP⟩),
      Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [hsum, inv_smul_smul₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]

end Average

/-- **2021 Proposition 14.1.4, p. 642 (2017: Remark 14.2)**, with the non-equivariant
extension as hypothesis: let `(sᵢ)_{i ∈ I}` be a symmetric sc⁺-section structure on
`U(x) = V(x) ∩ ∂X` (Definition 14.1.3) and let `s⁰ᵢ` be sc⁺-sections on `V(x)` with
`s⁰ᵢ|U(x) = sᵢ`.  Then there are sc⁺-sections `s̄ᵢ` on `V(x)` with `s̄ᵢ|U(x) = sᵢ` and
`s̄_{g(i)}(g ∗ y) = μ(Γ(g, y), s̄ᵢ(y))` for all `y ∈ V(x)` (Definition 13.2.5 (1)).  The text
obtains the `s⁰ᵢ` from Proposition 12.3.7 and an sc-smooth partition of unity on `V(x)`. -/
theorem proposition_14_1_4_hyp {Λ : A.W → ℚ≥0} {x : A.Obj} {V : A.X.NatNbhd x}
    (S : BoundarySymmetricStructure A Λ V) (s₀ : S.I → A.Obj → A.W)
    (h₀ : ∀ i, IsScPlusSectionOn A (s₀ i) V.U) (h₀b : ∀ i, ∀ y ∈ V.bdry, s₀ i y = S.s i y) :
    ∃ sb : S.I → A.Obj → A.W, (∀ i, IsScPlusSectionOn A (sb i) V.U) ∧
      (∀ i, ∀ y ∈ V.bdry, sb i y = S.s i y) ∧
      ∀ (g : A.X.Isotropy x) i, ∀ y ∈ V.U,
        sb (g • i) (V.rep.Φ g y) = fibAct (V.rep.Γ g y) (sb i y) := by
  let _ : Fintype (A.X.Isotropy x) := Fintype.ofFinite _
  refine ⟨avgSection V s₀, fun i => isScPlusSectionOn_avgSection h₀ i, fun i y hy => ?_,
    fun g i y hy => avgSection_equivariant h₀ g i hy⟩
  rw [avgSection_eq_of_equivariant h₀ (NatNbhd.bdry_subset V)
    (fun g j y hy => by
      rw [h₀b _ _ (NatNbhd.mapsTo_Φ_bdry V g hy), h₀b _ _ hy]
      exact S.equivariant g j y hy) i hy, h₀b i y hy]

/-- **Nonvacuity of the hypothesis of `proposition_14_1_4_hyp`**: for the zero structure the zero
sections extend. -/
theorem proposition_14_1_4_hyp_witness {x : A.Obj} (V : A.X.NatNbhd x) :
    ∃ s₀ : (zeroBoundaryStructure (A := A) V).I → A.Obj → A.W,
      (∀ i, IsScPlusSectionOn A (s₀ i) V.U) ∧
      ∀ i, ∀ y ∈ V.bdry, s₀ i y = (zeroBoundaryStructure V).s i y :=
  ⟨fun _ => fiberZero A.P, fun _ => isScPlusSectionOn_fiberZero V.isOpen_U,
    fun _ _ _ => rfl⟩

end SBLocalization

end Polyfold
