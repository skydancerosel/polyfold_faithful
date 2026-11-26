import Polyfold.Chapter16.PolyfoldFredholmSections
import Polyfold.Chapter3.BasicGermCriterionGeneral
import Polyfold.Chapter3.BasicGermCriterionProof
import Polyfold.Chapter3.BookGerms
import Polyfold.Chapter3.NonVacuity
import Polyfold.Chapter3.NonVacuityCorner
import Polyfold.Chapter5.BumpFunctions

/-!
Hofer–Wysocki–Zehnder, *Applications of Polyfold Theory I: The Polyfolds of Gromov–Witten
Theory*, Memoirs AMS 248 (2017), Chapter 4: **Definitions 4.1–4.4** (pp. 99–100), the abstract
part of **Theorem 4.6** (p. 101), **Propositions 4.22, 4.24, 4.26** (pp. 117–122), compared with
the book (*Polyfold and Fredholm Theory*, Springer 2021): Definitions 8.3.4, 16.3.18, 16.6.1–16.6.3,
Theorem 16.6.4, Definition 3.1.4, Lemma 3.7.4, Theorem 3.7.1.

# Fredholm sections in the memoir's form

## The memoir, paraphrased

(Definition 4.1) A section of `P : E → X` is an sc-smooth functor `F : X → E` with `P ∘ F = id`;
on morphisms `F(ϕ) = (ϕ, F(x))`, and functoriality is `μ(ϕ, F(x)) = F(y)`.  (Definition 4.2) A
Fredholm section is one which on objects is an M-polyfold Fredholm section.  (Definition 4.3)
Classes `[f, F]` with `f ∘ γ = Γ ∘ |F|` are the sc-smooth sections of `p : W → Z`.
(Definition 4.4) `f` is Fredholm if a representative is; proper if `S(f) = {f = 0}` is compact.
(p. 4) Component-proper: the restriction to every connected component is proper.  (Theorem 4.6)
`∂̄_J` is an sc-smooth component-proper Fredholm section, with an index formula and an
orientation.  (Proposition 4.22) The map `f` of (4.18) is a filled version: (1), (2), and (3)
holds trivially since `Dr(y₀) = id` and `ρ(y₀) = id`.  (Proposition 4.24, from [28]) For `V ⊆ H`
open, `H` finite-dimensional, and sc-isomorphisms `L(v) : E → F` with `(v, h) ↦ L(v)h`
sc-smooth and `|L(v)h|_m ≥ C_m|h|_m`, the map `(v, k) ↦ L(v)⁻¹k` is sc-smooth.
(Proposition 4.26) For `U ⊆ E` open, `f : U → F` sc-smooth with (1) `Df(x)` sc-Fredholm of
constant index at smooth points, (2) a splitting `E = B ⊕ X`, `ker Df(0) ⊆ B`, with the
compactness property, (3) `|[D₂f(b, 0) − D₂f(b, x)]h|_m ≤ ε|h|_m` for `b`, `x` small on level
`m`, the germ `f − f(0)` is conjugated near `0` to an sc⁰-contraction germ.

## What is formalized (namespace `GWMemoir`)

* `memoir_definition_4_1`: the morphism part of a section functor is `ϕ ↦ (ϕ, F(s ϕ))`, and its
  compatibility with `t` is the functoriality of Definition 8.3.4; `MemoirSection`,
  `MemoirScPlusSection`, `MemoirFredholmSection` (**Definitions 4.1, 4.2**, `abbrev`s).
* `memoir_definition_4_4_fredholm_iff`, `IsMemoirProper`, **`memoir_definition_4_4_proper_iff`**
  (**Definition 4.4**: compact solution set iff proper in the book's Definition 16.6.3, by
  Theorem 16.6.4).
* `IsComponentProper`, `isComponentProper_iff` (in a representative: `|S_F|` component compact,
  the book's Definition 7.3.7), `IsMemoirProper.isComponentProper`, `isMemoirProper_of_finite`.
* **`memoir_proposition_4_22`**: (1), (2), a smooth germ, `ker Dr(0) = 0`, `ker ρ(0) = 0` give
  a filling (Definition 3.1.4); witness `memoir_proposition_4_22_witness`.
* **`memoir_proposition_4_24`**: as printed, `V` any open subset (from `famInv_isScSmooth_of`,
  Lemma 3.7.4, by a translation).
* **`memoir_proposition_4_26`**: as printed (`U` open in `E`, no quadrant), from
  `theorem_3_7_1_general` with `C = E`.

## Readings

* Definitions 4.1–4.4 are read over the book's strong polyfold bundles (Definition 16.3.4):
  the memoir's classes refer to its reference [24] for the equivalence of structures.
* Definition 4.1 is read on objects (Definition 8.3.4 (1)); the morphism part is determined
  (`memoir_definition_4_1`).
* Proposition 4.24 (2): `C_m > 0`.
* Proposition 4.26 (3): `x` on level `m + 1`, small on level `m` (the linearization `D₂f(b, x)`
  on level `m` needs `x ∈ E_{m+1}`); this is the book's form.  "sc⁰-contraction germ" is read as
  the book's basic germ (Definition 3.1.7).
* Theorem 4.6: only "component-proper" is an abstract notion; the index formula and the
  orientation need the Cauchy–Riemann operator.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace GWMemoir

open Polyfold

universe u

/-! ### Definitions 4.1 and 4.2 -/

section Def41

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

/-- **Memoir Definition 4.1, p. 99, the morphism part**: if `F` is a section on objects and
`𝐅 : 𝐗 → X ₛ×_p E` covers the identity (`P ∘ 𝐅 = id`, i.e. `π₁ ∘ 𝐅 = id`) and is compatible
with the sources, then `𝐅(ϕ) = (ϕ, F(s ϕ))`, and `𝐅` is compatible with the targets iff
`μ(ϕ, F(x)) = F(y)` for `ϕ : x → y` (the functoriality of the book's Definition 8.3.4). -/
theorem memoir_definition_4_1 (E : EpStrongBundle X B) {F : Obj → W} (hF : IsSection P F)
    (Fm : Mor → pullbackSpace P X.src) (hπ : ∀ φ, (Fm φ).1.1 = φ)
    (hs : ∀ φ, (Fm φ).1.2 = F (X.src φ)) :
    (∀ φ, Fm φ = EpStrongBundle.sectionPair (X := X) hF φ) ∧
      ((∀ φ, E.μ (Fm φ) = F (X.tgt φ)) ↔ E.IsFunctorialSection hF) := by
  have h : ∀ φ, Fm φ = EpStrongBundle.sectionPair (X := X) hF φ := fun φ =>
    Subtype.ext (Prod.ext (hπ φ) (hs φ))
  refine ⟨h, ⟨fun ht φ => ?_, fun hfun φ => ?_⟩⟩
  · rw [← h φ, ht φ]
  · rw [h φ, ← hfun φ]

/-- **Memoir Definition 4.1**: an sc-smooth section (functor) of `P : E → X`, read on objects:
the book's sc-smooth section functor (Definition 8.3.4 (1)). -/
abbrev MemoirSection (E : EpStrongBundle X B) (F : Obj → W) : Prop :=
  E.IsScSmoothSectionFunctor F

/-- **Memoir Definition 4.1**: an sc⁺-section (Definition 8.3.4 (2)). -/
abbrev MemoirScPlusSection (E : EpStrongBundle X B) (F : Obj → W) : Prop :=
  E.IsScPlusSectionFunctor F

/-- **Memoir Definition 4.2, p. 99**: a Fredholm section, an sc-smooth section which on objects
is an M-polyfold sc-Fredholm section (Definition 8.3.4 (3)). -/
abbrev MemoirFredholmSection (E : EpStrongBundle X B) (F : Obj → W) : Prop :=
  E.IsScFredholmSectionFunctor F

end Def41

/-! ### Definitions 4.3, 4.4 and component-properness -/

section Def44

open StrongPolyfoldBundle StrongPolyfoldBundleStructure

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- **Memoir Definition 4.4, p. 100, "Fredholm"**: some representation `F` of `f` is a Fredholm
section of its strong bundle; this is the book's Definition 16.6.1 (`ScSection.IsFredholm`). -/
theorem memoir_definition_4_4_fredholm_iff (s : ScSection c) :
    s.IsFredholm ↔ ∃ a : SectionRep c, ⟦a⟧ = s ∧ MemoirFredholmSection a.S.A.E a.F :=
  Iff.rfl

/-- **Memoir Definition 4.4, "proper"**: the solution set `S(f)` is compact (the book's
Definition 16.6.2, compact solution set). -/
def IsMemoirProper (s : ScSection c) : Prop := IsCompact s.solutionSet

/-- **Memoir Definition 4.4 versus the book's Definition 16.6.3**: for an sc-Fredholm section,
"proper" in the memoir's sense (compact solution set) is "proper" in the book's sense (compact
solution set and, for every auxiliary norm, control of compactness), by Theorem 16.6.4. -/
theorem memoir_definition_4_4_proper_iff (s : FredholmSection c) :
    IsMemoirProper s.1 ↔ s.1.IsProper :=
  (theorem_16_6_4 s).out 0 1

/-- **Component-proper** (Memoir p. 4, used in Theorem 4.6): the restriction to every connected
component of `Z` is proper, i.e. `S(f) ∩ C` is compact for every component `C`. -/
def IsComponentProper (s : ScSection c) : Prop :=
  ∀ z : Z, IsCompact (s.solutionSet ∩ connectedComponent z)

/-- A proper section is component-proper (components are closed). -/
theorem IsMemoirProper.isComponentProper {s : ScSection c} (h : IsMemoirProper s) :
    IsComponentProper s := fun _ => h.inter_right isClosed_connectedComponent

/-- A component-proper section whose solution set meets only finitely many components is
proper. -/
theorem isMemoirProper_of_finite {s : ScSection c} (h : IsComponentProper s) {T : Set Z}
    (hT : T.Finite) (hS : s.solutionSet ⊆ ⋃ z ∈ T, connectedComponent z) :
    IsMemoirProper s := by
  have : s.solutionSet = ⋃ z ∈ T, (s.solutionSet ∩ connectedComponent z) := by
    rw [← inter_iUnion₂, inter_eq_left.2 hS]
  unfold IsMemoirProper
  rw [this]
  exact hT.isCompact_biUnion fun z _ => h z

/-- A homeomorphism maps connected components onto connected components. -/
theorem homeomorph_image_connectedComponent {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (h : α ≃ₜ β) (x : α) :
    h '' connectedComponent x = connectedComponent (h x) := by
  rw [← connectedComponentIn_univ, h.image_connectedComponentIn (mem_univ x), image_univ,
    h.surjective.range_eq, connectedComponentIn_univ]

/-- **Component-properness in a representative**: `f` is component-proper iff `|S_F| ⊆ |X|` is
component compact (the book's Definition 7.3.7), since `S_f = γ(|S_F|)` and `γ` is a
homeomorphism. -/
theorem isComponentProper_iff (a : SectionRep c) :
    IsComponentProper (c := c) ⟦a⟧ ↔
      a.S.A.X.IsComponentCompact (a.S.A.X.π '' solutionSet a.S.A.P a.F) := by
  have hS : ScSection.solutionSet (c := c) ⟦a⟧ = a.S.γ '' (a.S.A.X.π '' solutionSet a.S.A.P a.F) :=
    by rw [a.solutionSet_eq, image_image]
  unfold IsComponentProper EpGroupoid.IsComponentCompact
  rw [hS]
  constructor
  · intro h q
    have := h (a.S.γ q)
    rw [← homeomorph_image_connectedComponent, ← image_inter a.S.γ.injective,
      a.S.γ.isCompact_image] at this
    exact this
  · intro h z
    obtain ⟨q, rfl⟩ := a.S.γ.surjective z
    rw [← homeomorph_image_connectedComponent, ← image_inter a.S.γ.injective, a.S.γ.isCompact_image]
    exact h q

end Def44

/-! ### Proposition 4.22: the filling condition (3) with trivial kernels -/

section Prop422

open StrongRetr

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

/-- **Memoir Proposition 4.22, p. 117, the abstract step** (the filling of Definition 3.1.4,
2021 p. 91): if `r(0) = 0`, conditions (1) and (2) of a filling hold, `g` is an sc-smooth germ,
and `Dr(0) = id`, `ρ(0) = id` (as at `y₀` in the proof), then `g` is a filling of `f̂`:
condition (3) holds since `ker Dr(0) = 0 = ker ρ(0)`. -/
theorem memoir_proposition_4_22 (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) {fb g : E 0 → F 0}
    (hr0 : r R 0 = 0) (h1 : ∀ᶠ x in 𝓝 (0 : E 0), x ∈ r R '' U → fb x = g x)
    (h2 : ∀ᶠ y in 𝓝 (0 : E 0), y ∈ U → g y = ρ R (r R y) (g y) → y ∈ r R '' U)
    (hg : ∃ G : ScNbhdGerm E C, G.U 0 ⊆ U ∧ IsScSmoothGerm G g)
    (hDr : ∀ v, scDeriv U (r R) (0 : E 1) v = v) (hρ : ∀ h, ρ R 0 h = h) :
    IsFilling2021 hU hR h0 fb g := by
  obtain ⟨G, hGU, hgs⟩ := hg
  obtain ⟨Dg, hDg⟩ := (hgs 1).isSc1
  refine ⟨hr0, h1, h2, G, hGU, hgs, _, fillDefect_isSc1GermWith hU hR h0 hGU hDg, ?_⟩
  set K₁ := LinearMap.ker ((scDeriv U (r R) (0 : E 1) : E 0 →L[ℝ] E 0) : E 0 →ₗ[ℝ] E 0)
  set K₂ := LinearMap.ker ((ρCLM hR h0 : F 0 →L[ℝ] F 0) : F 0 →ₗ[ℝ] F 0)
  have hs₁ : Subsingleton K₁ := ⟨fun a b => by
    have ha : (a : E 0) = 0 := by rw [← hDr a]; exact a.2
    have hb : (b : E 0) = 0 := by rw [← hDr b]; exact b.2
    exact Subtype.ext (ha.trans hb.symm)⟩
  have hs₂ : Subsingleton K₂ := ⟨fun a b => by
    have ha : (a : F 0) = 0 := by rw [← hρ a]; exact a.2
    have hb : (b : F 0) = 0 := by rw [← hρ b]; exact b.2
    exact Subtype.ext (ha.trans hb.symm)⟩
  refine ⟨{ LinearEquiv.ofSubsingleton K₁ K₂ with
    continuous_toFun := continuous_of_const fun _ _ => Subsingleton.elim _ _
    continuous_invFun := continuous_of_const fun _ _ => Subsingleton.elim _ _ }, fun v => ?_⟩
  obtain rfl : v = 0 := Subsingleton.elim _ _
  simp

/-- **Satisfiability of the hypotheses of Proposition 4.22**: for `E = F = ℝ`, `U = ℝ`, `R = id`
and `g = f̂ = 0`, conditions `r(0) = 0`, (1), (2) and the germ hold
(`isFilling2017_rn`), and `Dr(0) = id`, `ρ(0) = id`. -/
theorem memoir_proposition_4_22_witness :
    (∀ v, scDeriv (E := rnSc 1) (F := rnSc 1) univ
        (r (id : (rnSc 1) 0 × (rnSc 1) 0 → (rnSc 1) 0 × (rnSc 1) 0)) 0 v = v) ∧
      ∀ h, ρ (id : (rnSc 1) 0 × (rnSc 1) 0 → (rnSc 1) 0 × (rnSc 1) 0) 0 h = h := by
  refine ⟨fun v => ?_, fun _ => rfl⟩
  have hU := rn_relOpen_univ (n := 1)
  have hid : r (id : (rnSc 1) 0 × (rnSc 1) 0 → (rnSc 1) 0 × (rnSc 1) 0) = _root_.id := rfl
  rw [hid, scDeriv_zero_eq_of_hasFDerivAt hU (isScSmooth_id hU.isScDomain).isSc1 (mem_univ 0)
    (hasFDerivAt_id 0)]
  rfl

end Prop422

/-! ### Proposition 4.24: inverses of families of sc-isomorphisms -/

section Prop424

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {X Y : ScBanach}

lemma isScDomain_prod_univ {W : ScBanach} {V : Set P} (hV : IsOpen V) :
    IsScDomain (ScBanach.paramProd P W) (V ×ˢ univ) :=
  (⟨isPartialQuadrant_univ _, V ×ˢ univ, hV.prod isOpen_univ, (inter_univ _).symm⟩ :
    IsRelOpenInQuadrant (ScBanach.paramProd P W) univ (V ×ˢ univ)).isScDomain

lemma translate_isScSmooth {W : ScBanach} {D : Set ((ScBanach.paramProd P W) 0)}
    (hD : IsScDomain (ScBanach.paramProd P W) D) (a : P) :
    IsScSmooth (E := ScBanach.paramProd P W) (F := ScBanach.paramProd P W) D
      fun p => p + ((a, 0) : P × W 0) := by
  refine IsScSmooth.add hD (isScSmooth_id hD) (isScSmooth_const_of_mem_smooth hD ?_)
  refine (ScBanach.paramProd P W).mem_smooth_iff.2 fun m => ⟨((a, 0) : P × W m), ?_⟩
  rw [ScBanach.paramProd_toBase, map_zero]

/-- **Memoir Proposition 4.24, p. 119** (from [28], Proposition 4.8; the book's **Lemma 3.7.4**,
2021 p. 143, in set form `famInv_isScSmooth_of`, with `C̃ = H`): let `V` be an open subset of a
finite-dimensional space `H` and `L(v) : E → F`, `v ∈ V`, sc-isomorphisms such that
(1) `(v, h) ↦ L(v)h` is sc-smooth on `V ⊕ E` and (2) `|L(v)h|_m ≥ C_m|h|_m` with `C_m > 0`.
Then `(v, k) ↦ L(v)⁻¹k` is sc-smooth on `V ⊕ F`.  The book's lemma is for `0 ∈ V`; the general
`V` follows by translation. -/
theorem memoir_proposition_4_24 {V : Set P} (hV : IsOpen V) {L : P → ScIso X Y}
    (hL : IsScSmooth (E := ScBanach.paramProd P X) (F := Y) (V ×ˢ univ) (famMap L))
    (hc : ∀ m, ∃ c > 0, ∀ v ∈ V, ∀ h : X m, c * ‖h‖ ≤ ‖L v m h‖) :
    IsScSmooth (E := ScBanach.paramProd P Y) (F := X) (V ×ˢ univ) (famInv L) := by
  have hDY := isScDomain_prod_univ (W := Y) hV
  refine IsScSmooth.of_locally hDY fun x hx => ⟨univ, isOpen_univ, mem_univ _, ?_⟩
  rw [inter_univ]
  set v₀ := x.1
  set L' : P → ScIso X Y := fun w => L (w + v₀)
  set V' : Set P := (fun w => w + v₀) ⁻¹' V
  have hV' : IsOpen V' := hV.preimage (continuous_add_const v₀)
  have hV'0 : (0 : P) ∈ V' := by simpa [V'] using hx.1
  have hDX' := isScDomain_prod_univ (W := X) hV'
  have hDX := isScDomain_prod_univ (W := X) hV
  have hL' : IsScSmooth (E := ScBanach.paramProd P X) (F := Y) ((V' ∩ univ) ×ˢ univ)
      (famMap L') := by
    rw [inter_univ]
    refine (IsScSmooth.comp hDX' hDX hL (translate_isScSmooth hDX' v₀)
      fun p hp => ⟨hp.1, mem_univ _⟩).congr hDX' fun p _ => ?_
    simp [famMap, L']
  have hc' : ∀ m, ∃ c > 0, ∀ b ∈ V' ∩ univ, ∀ h : X m, c * ‖h‖ ≤ ‖L' b m h‖ := fun m => by
    obtain ⟨c, hc0, hcm⟩ := hc m
    exact ⟨c, hc0, fun b hb h => hcm _ hb.1 h⟩
  have hinv := famInv_isScSmooth_of (isPartialQuadrant_univ _) hV' hV'0 hL' hc'
  rw [inter_univ] at hinv
  have hDY' := isScDomain_prod_univ (W := Y) hV'
  refine (IsScSmooth.comp hDY hDY' hinv (translate_isScSmooth hDY (-v₀))
    fun p hp => ⟨?_, mem_univ _⟩).congr hDY fun p _ => ?_
  · simpa [V'] using hp.1
  · simp [famInv, L']

end Prop424

/-! ### Proposition 4.26: the basic germ criterion on an open set -/

section Prop426

variable {E F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0} {B X : Submodule ℝ (E 0)}

/-- **Memoir Proposition 4.26, p. 122** (the book's **Theorem 3.7.1**, 2021 p. 140, in the form
`theorem_3_7_1_general` for a general sc-splitting, with the partial quadrant `C = E`): let
`U ⊆ E` be an open neighbourhood of `0` and `f : U → F` sc-smooth with (1) `Df(x)` sc-Fredholm
at smooth points, of constant index, (2) an sc-splitting `E = B ⊕ X`, `B` finite-dimensional,
`ker Df(0) ⊆ B`, with the compactness property, (3) the estimate for `D₂f` (on level `m`, for
`x ∈ X_{m+1}` small on level `m`).  Then `f − f(0)` is conjugated near `0` to a basic germ. -/
theorem memoir_proposition_4_26 (hUo : IsOpen U) (h0 : (0 : E 0) ∈ U) (hf : IsScSmooth U f)
    (h1F : ∀ (x : E 1) (hx : x ∈ E.lvlSet U 1) (hs : x ∈ E.smoothLvl 1),
      IsScFredholm (derivOpAt hf hx hs))
    (h1I : ∀ (x : E 1) (hx : x ∈ E.lvlSet U 1) (hs : x ∈ E.smoothLvl 1)
      (x' : E 1) (hx' : x' ∈ E.lvlSet U 1) (hs' : x' ∈ E.smoothLvl 1),
      scIndex (derivOpAt hf hx hs) = scIndex (derivOpAt hf hx' hs'))
    (hBX : E.IsScSplitting B X) [FiniteDimensional ℝ B]
    (hker : LinearMap.ker (scDeriv U f 0 : E 0 →ₗ[ℝ] F 0) ≤ B)
    (h2 : CompactnessCondition371 U f B X) (h3 : DerivCondition371 U f B X) :
    ∃ V : Set (E 0), IsOpen V ∧ (0 : E 0) ∈ V ∧
      IsConjugateToBasicGerm (U ∩ V) fun u => f u - f 0 :=
  theorem_3_7_1_general (C := univ) ⟨isPartialQuadrant_univ E, U, hUo, (inter_univ U).symm⟩ h0 hf
    h1F h1I hBX hker (subset_univ _) h2 h3

end Prop426

end GWMemoir
