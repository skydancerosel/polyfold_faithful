import Polyfold.Chapter9.Propositions
import Polyfold.Chapter10.EquivalenceLR

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, "Geometry up to Equivalences", §11.3 "Branched Ep⁺-Subgroupoids and
Equivalences" (pp. 535–542; 2017: pp. 389–396): **Definition 11.3.1, Lemma 11.3.2** and
**Theorem 11.3.3 for equivalences** (2017: Definition 11.4, Lemma 11.5, Theorem 11.3).  Numbers
and pages are the 2021 text's, the 2017 ones in parentheses.  The generalized isomorphisms
(Theorem 11.3.3 as stated) are in `BranchedEquivalenceLocalization.lean`.

# Branched ep⁺-subgroupoids along equivalences

## The text, paraphrased

(Definition 11.3.1, p. 535 (2017: Definition 11.4, p. 389)) For an equivalence `F : X → Y` and
functors `Θ : X → ℚ⁺`, `Θ' : Y → ℚ⁺`: the pull-back is `F^*Θ' = Θ' ∘ F`; the push-forward is
`(F_*Θ)(y) = Θ(x)` for a chosen `x` and `ψ : F(x) → y`.

(Lemma 11.3.2, p. 536 (2017: Lemma 11.5, p. 389)) (1) `F_*Θ` is a well-defined functor and
`F^* F_* Θ = Θ`; (2) `F_* F^* Θ' = Θ'`; (3) naturally equivalent equivalences `F ≃ G` have
`F_*Θ = G_*Θ` and `F^*Θ' = G^*Θ'`.  *Proof* (text): for `ψ : F(x) → y`, `ψ' : F(x') → y` the
morphism `ψ⁻¹ ∘ ψ' : F(x') → F(x)` is `F(σ)`, `σ : x' → x`, so `Θ(x) = Θ(x')`.

(Theorem 11.3.3, p. 537 (2017: Theorem 11.3, p. 390)) For a generalized isomorphism `f`, `f_*`
and `f^*` map branched ep⁺-subgroupoids to branched ep⁺-subgroupoids ((1), (2)) and preserve
closedness (3), compactness (4) (Definition 9.1.6), manifold- and orbifold-type (5) (Definition
9.1.8) and the dimensional decomposition of Proposition 9.1.11 (6).  *Proof* (text, pp. 537–538):
for an equivalence, a local branching structure `(M'ᵢ)` of `Θ'` at `F(x)` is pulled back by
`F|U(x)`, keeping the weights; for `F_*Θ` one at `x` is moved by `F` and then by `ψ̂` to `y`;
`|f_*Θ| = |Θ| ∘ |f|⁻¹` gives (3), (4); manifold-type by conjugating a non-trivial morphism with
`ψ` and lifting it to `x`; "(6) is trivial".

## What is formalized

* `EpFunctor.pullbackTheta`, `EpFunctor.pushforwardTheta` (**Definition 11.3.1**).
* **Lemma 11.3.2**: (1) `pushforwardTheta_eq` (independence of the choice),
  `isFunctorial_pushforwardTheta`, `pullbackTheta_pushforwardTheta`; (2)
  `pushforwardTheta_pullbackTheta`; (3)
  `pushforwardTheta_eq_of_naturallyEquivalent`, `pullbackTheta_eq_of_naturallyEquivalent`.  Also
  `pullbackTheta_comp`, `pushforwardTheta_comp`, `pushforwardTheta_id`,
  `isFunctorial_pullbackTheta`.
* `EpGroupoid.LocalBranchingStructure.mapDiffeo`: a local branching structure moved by an
  sc-diffeomorphism between open subsets of the object spaces of two ep-groupoids (the basic step of
  the proof), `isOfDim_mapDiffeo`.
* **Theorem 11.3.3 for an equivalence `F`**: (1) `isBranchedEpSubgroupoid_pushforwardTheta`,
  (2) `isBranchedEpSubgroupoid_pullbackTheta`; (3) `isClosedBranched_pushforwardTheta`,
  `isClosedBranched_pullbackTheta`; (4) `isCompactBranched_pushforwardTheta`,
  `isCompactBranched_pullbackTheta`; (5) `isOrbifoldType_pushforwardTheta`,
  `isOrbifoldType_pullbackTheta`, `isManifoldType_pushforwardTheta`, `isManifoldType_pullbackTheta`;
  (6) `isNDimensional_pushforwardTheta`, `isNDimensional_pullbackTheta`,
  `isDimDecomposition_pushforwardTheta`, `isDimDecomposition_pullbackTheta`.  The identity
  `|F_*Θ| = |Θ| ∘ |F|⁻¹`: `orbitSupp_pushforwardTheta`, `orbitSupp_pullbackTheta`.
* Part I/Chapter 9 facts for sc-diffeomorphisms between *different* M-polyfolds:
  `MPolyfold.hasDimAt_image_iff_of_isScDiffeoOn`, `MPolyfold.IsSubmanifoldOfDim.image_isScDiffeoOn`
  (Chapter 9 has them for `P → P`: `hasDimAt_image_iff`).
* Witnesses (in `BranchedEquivalenceLocalization.lean`): `Θ₀ = 1_{0}` on `ℤ/2 ⋉ ℝ` and its
  pull-back along the covering equivalence `X_𝒰 → ℤ/2 ⋉ ℝ` (`reflectionCover`, Proposition
  10.1.3), which is `1` at two different objects.

## What the text leaves implicit, and the choices made

* `ℚ⁺ = ℚ_{≥0}` and functors `X → ℚ` are as in Chapter 9 (`EpGroupoid.IsFunctorial`).
  `F_*Θ` is defined for every sc-smooth functor through a choice (`0` if no `F(x)` is isomorphic to
  `y`); it is the text's push-forward for an equivalence.  The lemmas record what each claim needs:
  well-definedness only fullness; Lemma 11.3.2 (2) only essential surjectivity; (3) fullness of
  `F` and `G`.
* The local sc-diffeomorphism `ψ̂ ∘ F` near `x` is Chapter 10's `TransportChart` (`Q = ψ̂ ∘ F`,
  `ψ_u : F(u) → Q(u)`); `F_*Θ ∘ Q = Θ` because `ψ_u` is a morphism.  The `Mᵢ` are first
  restricted to the domain of the sc-diffeomorphism (`mapDiffeo` uses `f(Mᵢ ∩ W)`), which the text
  leaves implicit.
* Definition 9.1.2 (1) (2021) also asks `|supp(Θ)|` to be paracompact; for `F_*Θ` and `F^*Θ'` this
  follows from `|supp(F_*Θ)| = |F|(|supp(Θ)|)` and `|F|` a homeomorphism (not mentioned in the
  proof).
* Theorem 11.3.3 (6): the uniqueness in Proposition 9.1.11 does not hold as we read it
  (`not_proposition_9_1_11_rn`), so (6) is read as: every dimensional decomposition
  (`IsDimDecomposition`) of `Θ` is mapped to one of the image.  It needs the invariance of the
  dimension of a submanifold under sc-diffeomorphisms between different M-polyfolds.
* The branched statements take `X`, `Y` in one universe (the index type of a local branching
  structure is kept); generalized isomorphisms live in `EP.{u}` anyway.
* The manifold-type argument is done for two morphisms `y → y'` directly (conjugated by
  `ψ : F(x) → y`, `ψ' : F(x') → y'`), not through a non-trivial `y → y`.
* Possible misprints: Definition 11.3.1 (2) types the push-forward `X' → ℚ⁺` (also 2017); read
  `Y → ℚ⁺`.  In the manifold-type step (p. 538) `ψ ∘ φ' ∘ ψ⁻¹ : F(x) → F(x)` for `ψ : F(x) → y`,
  `φ' : y → y`; read `ψ⁻¹ ∘ φ' ∘ ψ`.
-/

set_option maxSynthPendingDepth 3

open Set Function Module Submodule

noncomputable section

namespace Polyfold

universe u v w

/-! ### The dimension under sc-diffeomorphisms between different M-polyfolds -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- One direction of `hasDimAt_image_iff_of_isScDiffeoOn`. -/
theorem HasDimAt.of_image {f : X → Y} {g : Y → X} {U : Set X} {U' : Set Y}
    (hf : P.IsScDiffeoOn Q f g U U') {A : Set X} (hA : P.IsSmoothSubmanifold A) (hAU : A ⊆ U)
    {a : X} (ha : a ∈ A) {k : ℕ} (h : Q.HasDimAt (f '' A) (f a) k) : P.HasDimAt A a k := by
  obtain ⟨ψ, hψ, hfaψ⟩ := Q.exists_isChart_mem_source (f a)
  set χ := transportChart hf ψ with hχdef
  have hχ : P.IsChart χ := transportChart_isChart hf hψ
  have haχ : a ∈ χ.source := ⟨hAU ha, hfaψ⟩
  set d := hA.data ha
  set G := d.toSubData.shrink χ with hGdef
  have hGχ : G ⊆ χ.source := d.toSubData.shrink_subset_source χ
  have hGU : G ⊆ U := fun x hx => (hGχ hx).1
  have hfG : f '' G = U' ∩ g ⁻¹' G := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hf.mapsTo (hGU hx), by rw [mem_preimage, hf.left_inv x (hGU hx)]; exact hx⟩
    · rintro ⟨hy, hgy⟩
      exact ⟨g y, hgy, hf.right_inv y hy⟩
  have hfGo : IsOpen (f '' G) := by
    rw [hfG]
    exact hf.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hf.isScSmoothOn_inv.isOpen
      (d.toSubData.isOpen_shrink χ)
  have hfGψ : f '' G ⊆ ψ.source := by
    rintro _ ⟨x, hx, rfl⟩; exact (hGχ hx).2
  have haG : a ∈ G := d.toSubData.mem_shrink χ ha (hA.mem_data_V ha) haχ
  have himg : χ '' (G ∩ A) = ψ '' (f '' G ∩ f '' A) := by
    rw [← image_inter_on (fun x hx y hy hxy => by
      rw [← hf.left_inv x (hAU hx), ← hf.left_inv y (hGU hy), hxy])]
    rw [← image_comp]
    rfl
  have hQ : IsScRetract χ.model.E χ.model.C (χ '' (G ∩ A)) :=
    d.toSubData.isScRetract_image χ hχ
  have hs : χ a ∈ χ.model.E.smooth := (mem_smoothSet_iff hχ haχ).1 (hA.subset_smoothSet ha)
  obtain ⟨z, hz, -⟩ := exists_smoothLvl_one_of_mem_smooth hs
  refine hasDimAt_of_finrank hA ha hχ (d.toSubData.isOpen_shrink χ) hGχ hQ haG hz ?_
  have hQ' : IsScRetract ψ.model.E ψ.model.C (ψ '' (f '' G ∩ f '' A)) := himg ▸ hQ
  rw [himg]
  exact h.finrank_eq' hψ hfGo hfGψ hQ' ⟨a, haG, rfl⟩ hz

/-- **The dimension is invariant under sc-diffeomorphisms between open subsets of two
M-polyfolds** (the version of `hasDimAt_image_iff` for `f : U → U'`, `U ⊆ X`, `U' ⊆ Y`). -/
theorem hasDimAt_image_iff_of_isScDiffeoOn {f : X → Y} {g : Y → X} {U : Set X} {U' : Set Y}
    (hf : P.IsScDiffeoOn Q f g U U') {A : Set X} (hA : P.IsSmoothSubmanifold A) (hAU : A ⊆ U)
    {a : X} (ha : a ∈ A) {k : ℕ} : Q.HasDimAt (f '' A) (f a) k ↔ P.HasDimAt A a k := by
  refine ⟨HasDimAt.of_image hf hA hAU ha, fun h => ?_⟩
  have hfA : Q.IsSmoothSubmanifold (f '' A) := hA.image_of_isScDiffeoOn hf hAU
  have hgf : g '' (f '' A) = A := by
    rw [image_image]
    exact (image_congr fun x hx => hf.left_inv x (hAU hx)).trans (image_id' A)
  refine HasDimAt.of_image hf.symm hfA (image_subset_iff.2 fun x hx => hf.mapsTo (hAU hx))
    ⟨a, ha, rfl⟩ ?_
  rw [hgf, hf.left_inv a (hAU ha)]
  exact h

/-- The image of an `n`-dimensional submanifold under an sc-diffeomorphism `U → U'` between open
subsets of two M-polyfolds is `n`-dimensional. -/
theorem IsSubmanifoldOfDim.image_isScDiffeoOn {f : X → Y} {g : Y → X} {U : Set X} {U' : Set Y}
    (hf : P.IsScDiffeoOn Q f g U U') {A : Set X} {n : ℕ} (hA : P.IsSubmanifoldOfDim A n)
    (hAU : A ⊆ U) : Q.IsSubmanifoldOfDim (f '' A) n := by
  refine ⟨hA.1.image_of_isScDiffeoOn hf hAU, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  exact (hasDimAt_image_iff_of_isScDiffeoOn hf hA.1 hAU ha).2 (hA.2 a ha)

end MPolyfold

/-! ### Functors to `ℚ`, isomorphic objects -/

section Algebraic

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {Obj'' Mor'' : Type w} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Z : EpGroupoid Obj'' Mor''}

/-- A functor `Θ : X → ℚ` is constant on isomorphism classes. -/
theorem EpGroupoid.IsFunctorial.eq_of_isomorphic {Θ : Obj → ℚ} (hΘ : X.IsFunctorial Θ)
    {x x' : Obj} (h : X.Isomorphic x x') : Θ x = Θ x' := by
  obtain ⟨φ, rfl, rfl⟩ := h
  exact hΘ φ

namespace EpFunctor

/-- A functor maps isomorphic objects to isomorphic objects. -/
theorem isomorphic_obj (F : EpFunctor X Y) {x x' : Obj} (h : X.Isomorphic x x') :
    Y.Isomorphic (F.obj x) (F.obj x') := by
  obtain ⟨φ, rfl, rfl⟩ := h
  exact ⟨F.mor φ, F.src_mor φ, F.tgt_mor φ⟩

/-- A full functor reflects isomorphy of objects. -/
theorem isomorphic_of_full {F : EpFunctor X Y} (hF : F.toFunctor.Full) {x x' : Obj}
    (h : Y.Isomorphic (F.obj x) (F.obj x')) : X.Isomorphic x x' := by
  obtain ⟨ψ, hs, ht⟩ := h
  obtain ⟨φ, h1, h2, -⟩ := (F.full_iff.1 hF) x x' ψ hs ht
  exact ⟨φ, h1, h2⟩

variable (F : EpFunctor X Y)

/-- **2021 Definition 11.3.1 (1), p. 535 (2017: Definition 11.4 (1), p. 389)**: the
**pull-back** `F^*Θ' = Θ' ∘ F` of a functor `Θ' : Y → ℚ⁺` along `F : X → Y`. -/
def pullbackTheta (Θ' : Obj' → ℚ) : Obj → ℚ := fun x => Θ' (F.obj x)

open scoped Classical in
/-- **2021 Definition 11.3.1 (2), p. 535 (2017: Definition 11.4 (2), p. 389)**: the
**push-forward** `F_*Θ : Y → ℚ⁺`, `(F_*Θ)(y) = Θ(x)` for a chosen `x` with a morphism
`ψ : F(x) → y` (`0` if there is none; for an equivalence there always is one, and the value does
not depend on the choice: `pushforwardTheta_eq`). -/
def pushforwardTheta (Θ : Obj → ℚ) (y : Obj') : ℚ :=
  if h : ∃ x, Y.Isomorphic (F.obj x) y then Θ h.choose else 0

@[simp] theorem pullbackTheta_apply (Θ' : Obj' → ℚ) (x : Obj) :
    F.pullbackTheta Θ' x = Θ' (F.obj x) := rfl

variable {F}

/-- **Lemma 11.3.2 (1), well-definedness**: for a full `F` and a functor `Θ`, `(F_*Θ)(y) = Θ(x)`
for **every** `x` with a morphism `F(x) → y`. -/
theorem pushforwardTheta_eq (hF : F.toFunctor.Full) {Θ : Obj → ℚ} (hΘ : X.IsFunctorial Θ)
    {x : Obj} {y : Obj'} (h : Y.Isomorphic (F.obj x) y) : F.pushforwardTheta Θ y = Θ x := by
  have hex : ∃ x, Y.Isomorphic (F.obj x) y := ⟨x, h⟩
  rw [pushforwardTheta, dif_pos hex]
  exact hΘ.eq_of_isomorphic (isomorphic_of_full hF (hex.choose_spec.trans h.symm))

theorem pushforwardTheta_obj (hF : F.toFunctor.Full) {Θ : Obj → ℚ} (hΘ : X.IsFunctorial Θ)
    (x : Obj) : F.pushforwardTheta Θ (F.obj x) = Θ x :=
  pushforwardTheta_eq hF hΘ (Y.isomorphic_refl _)

theorem pushforwardTheta_of_not_exists {Θ : Obj → ℚ} {y : Obj'}
    (h : ¬ ∃ x, Y.Isomorphic (F.obj x) y) : F.pushforwardTheta Θ y = 0 := by
  rw [pushforwardTheta, dif_neg h]

theorem exists_isomorphic_of_pushforwardTheta_ne_zero {Θ : Obj → ℚ} {y : Obj'}
    (h : F.pushforwardTheta Θ y ≠ 0) : ∃ x, Y.Isomorphic (F.obj x) y := by
  by_contra hn
  exact h (pushforwardTheta_of_not_exists hn)

/-- `F_*Θ` is constant on isomorphism classes (for full `F` and functorial `Θ`). -/
theorem pushforwardTheta_eq_of_isomorphic (hF : F.toFunctor.Full) {Θ : Obj → ℚ}
    (hΘ : X.IsFunctorial Θ) {y y' : Obj'} (h : Y.Isomorphic y y') :
    F.pushforwardTheta Θ y = F.pushforwardTheta Θ y' := by
  by_cases hex : ∃ x, Y.Isomorphic (F.obj x) y
  · obtain ⟨x, hx⟩ := hex
    rw [pushforwardTheta_eq hF hΘ hx, pushforwardTheta_eq hF hΘ (hx.trans h)]
  · rw [pushforwardTheta_of_not_exists hex, pushforwardTheta_of_not_exists fun ⟨x, hx⟩ =>
      hex ⟨x, hx.trans h.symm⟩]

/-- **Lemma 11.3.2 (1), first claim**: `F_*Θ` is a functor. -/
theorem isFunctorial_pushforwardTheta (hF : F.toFunctor.Full) {Θ : Obj → ℚ}
    (hΘ : X.IsFunctorial Θ) : Y.IsFunctorial (F.pushforwardTheta Θ) := fun φ =>
  pushforwardTheta_eq_of_isomorphic hF hΘ ⟨φ, rfl, rfl⟩

/-- The pull-back of a functor is a functor. -/
theorem isFunctorial_pullbackTheta (F : EpFunctor X Y) {Θ' : Obj' → ℚ}
    (hΘ' : Y.IsFunctorial Θ') : X.IsFunctorial (F.pullbackTheta Θ') := fun φ => by
  simp only [pullbackTheta_apply, ← F.src_mor, ← F.tgt_mor]
  exact hΘ' (F.mor φ)

theorem pushforwardTheta_nonneg {Θ : Obj → ℚ} (hΘ : ∀ x, 0 ≤ Θ x) (y : Obj') :
    0 ≤ F.pushforwardTheta Θ y := by
  unfold pushforwardTheta
  split_ifs
  exacts [hΘ _, le_rfl]

/-- **Lemma 11.3.2 (1), second claim**: `F^* F_* Θ = Θ`. -/
theorem pullbackTheta_pushforwardTheta (hF : F.toFunctor.Full) {Θ : Obj → ℚ}
    (hΘ : X.IsFunctorial Θ) : F.pullbackTheta (F.pushforwardTheta Θ) = Θ :=
  funext fun x => pushforwardTheta_obj hF hΘ x

/-- **Lemma 11.3.2 (2)**: `F_* F^* Θ' = Θ'` for an essentially surjective `F` and a functor
`Θ'` (fullness is not needed). -/
theorem pushforwardTheta_pullbackTheta (hF : F.toFunctor.EssSurj) {Θ' : Obj' → ℚ}
    (hΘ' : Y.IsFunctorial Θ') : F.pushforwardTheta (F.pullbackTheta Θ') = Θ' := by
  funext y
  have hex : ∃ x, Y.Isomorphic (F.obj x) y := (F.essSurj_iff.1 hF) y |>.imp
    fun x ⟨ψ, hs, ht⟩ => ⟨ψ, hs, ht⟩
  rw [pushforwardTheta, dif_pos hex, pullbackTheta_apply]
  exact hΘ'.eq_of_isomorphic hex.choose_spec

/-- **Lemma 11.3.2 (3)**: naturally equivalent full functors have the same push-forwards and the
same pull-backs. -/
theorem pushforwardTheta_eq_of_naturallyEquivalent {F G : EpFunctor X Y} (hF : F.toFunctor.Full)
    (hG : G.toFunctor.Full) (hFG : F.NaturallyEquivalent G) {Θ : Obj → ℚ}
    (hΘ : X.IsFunctorial Θ) : F.pushforwardTheta Θ = G.pushforwardTheta Θ := by
  obtain ⟨τ⟩ := hFG
  have hτ : ∀ x, Y.Isomorphic (F.obj x) (G.obj x) := fun x => ⟨τ.app x, τ.src_app x, τ.tgt_app x⟩
  funext y
  by_cases hex : ∃ x, Y.Isomorphic (F.obj x) y
  · obtain ⟨x, hx⟩ := hex
    rw [pushforwardTheta_eq hF hΘ hx, pushforwardTheta_eq hG hΘ ((hτ x).symm.trans hx)]
  · rw [pushforwardTheta_of_not_exists hex, pushforwardTheta_of_not_exists fun ⟨x, hx⟩ =>
      hex ⟨x, (hτ x).trans hx⟩]

/-- **Lemma 11.3.2 (3)**, pull-backs. -/
theorem pullbackTheta_eq_of_naturallyEquivalent {F G : EpFunctor X Y}
    (hFG : F.NaturallyEquivalent G) {Θ' : Obj' → ℚ} (hΘ' : Y.IsFunctorial Θ') :
    F.pullbackTheta Θ' = G.pullbackTheta Θ' := by
  obtain ⟨τ⟩ := hFG
  funext x
  exact hΘ'.eq_of_isomorphic ⟨τ.app x, τ.src_app x, τ.tgt_app x⟩

/-- `(G ∘ F)^* = F^* ∘ G^*`. -/
theorem pullbackTheta_comp (G : EpFunctor Y Z) (F : EpFunctor X Y) (Θ'' : Obj'' → ℚ) :
    (G.comp F).pullbackTheta Θ'' = F.pullbackTheta (G.pullbackTheta Θ'') := rfl

/-- `(G ∘ F)_* = G_* ∘ F_*` for full `F`, `G` (on functors `Θ`). -/
theorem pushforwardTheta_comp {G : EpFunctor Y Z} (hG : G.toFunctor.Full) (hF : F.toFunctor.Full)
    (hGF : (G.comp F).toFunctor.Full) {Θ : Obj → ℚ} (hΘ : X.IsFunctorial Θ) :
    (G.comp F).pushforwardTheta Θ = G.pushforwardTheta (F.pushforwardTheta Θ) := by
  funext z
  by_cases hex : ∃ x, Z.Isomorphic (G.obj (F.obj x)) z
  · obtain ⟨x, hx⟩ := hex
    rw [pushforwardTheta_eq hGF hΘ hx,
      pushforwardTheta_eq hG (isFunctorial_pushforwardTheta hF hΘ) hx, pushforwardTheta_obj hF hΘ]
  · rw [pushforwardTheta_of_not_exists hex]
    by_cases hey : ∃ y, Z.Isomorphic (G.obj y) z
    · obtain ⟨y, hy⟩ := hey
      rw [pushforwardTheta_eq hG (isFunctorial_pushforwardTheta hF hΘ) hy,
        pushforwardTheta_of_not_exists fun ⟨x, hx⟩ => hex ⟨x, (G.isomorphic_obj hx).trans hy⟩]
    · rw [pushforwardTheta_of_not_exists hey]

/-- The push-forward along the identity is the identity on functors. -/
theorem pushforwardTheta_id {Θ : Obj → ℚ} (hΘ : X.IsFunctorial Θ) :
    (EpFunctor.id X).pushforwardTheta Θ = Θ :=
  funext fun x => pushforwardTheta_obj (EpFunctor.IsEquivalence.id X).full hΘ x

end EpFunctor

end Algebraic

/-! ### Moving local branching structures by sc-diffeomorphisms -/

section Branched

variable {Obj Mor Obj' Mor' : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

namespace EpGroupoid.LocalBranchingStructure

variable {Θ : Obj → ℚ} {Θ' : Obj' → ℚ} {x : Obj} (B : X.LocalBranchingStructure Θ x)
  {f : Obj → Obj'} {g : Obj' → Obj} {W : Set Obj} {W' : Set Obj'}

/-- The domain `W' ∩ g⁻¹(U(x) ∩ W) = f(U(x) ∩ W)` of the moved structure. -/
def mapU (g : Obj' → Obj) (W : Set Obj) (W' : Set Obj') : Set Obj' := W' ∩ g ⁻¹' (B.U ∩ W)

theorem mem_image_iff_of_mem_mapU (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W') {i : B.ι}
    {y : Obj'} (hy : y ∈ B.mapU g W W') : y ∈ f '' (B.M i ∩ W) ↔ g y ∈ B.M i := by
  constructor
  · rintro ⟨z, ⟨hzM, hzW⟩, rfl⟩
    rwa [hf.left_inv z hzW]
  · intro h
    exact ⟨g y, ⟨h, hy.2.2⟩, hf.right_inv y hy.1⟩

open scoped Classical in
/-- **Moving a local branching structure by an sc-diffeomorphism** (the basic step of the proof of
2021 Theorem 11.3.3, p. 537): if `f : W → W'` is an sc-diffeomorphism between open subsets of
the object spaces of `X` and `Y`, `x ∈ W`, `f(x) = y` and `Θ'(f(u)) = Θ(u)` on `W`, then the
`f(Mᵢ ∩ W)` with the same weights are a local branching structure of `Θ'` at `y`. -/
def mapDiffeo (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W') (hxW : x ∈ W) {y : Obj'}
    (hxy : f x = y) (hΘ : ∀ u ∈ W, Θ' (f u) = Θ u) : Y.LocalBranchingStructure Θ' y where
  U := B.mapU g W W'
  isOpen_U := hf.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hf.isScSmoothOn_inv.isOpen
    (B.isOpen_U.inter hf.isScSmoothOn.isOpen)
  mem_U := by
    subst hxy
    exact ⟨hf.mapsTo hxW, by rw [mem_preimage, hf.left_inv x hxW]; exact ⟨B.mem_U, hxW⟩⟩
  ι := B.ι
  M i := f '' (B.M i ∩ W)
  subset_U i := by
    rintro _ ⟨z, ⟨hzM, hzW⟩, rfl⟩
    refine ⟨hf.mapsTo hzW, ?_⟩
    rw [mem_preimage, hf.left_inv z hzW]
    exact ⟨B.subset_U i hzM, hzW⟩
  isSmoothSubmanifold i := ((B.isSmoothSubmanifold i).inter_isOpen
    hf.isScSmoothOn.isOpen).image_of_isScDiffeoOn hf inter_subset_right
  mem_M i := ⟨x, ⟨B.mem_M i, hxW⟩, hxy⟩
  isProperMap i := by
    refine (isProperMap_inclusion_iff _).2 ?_
    have hmaps : MapsTo g (B.mapU g W W') B.U := fun y hy => hy.2.1
    have hc := (B.isClosed_M i).preimage
      ((hf.isScSmoothOn_inv.continuousOn.mono inter_subset_left).mapsToRestrict hmaps)
    have heq : ((↑) ⁻¹' (f '' (B.M i ∩ W)) : Set (B.mapU g W W')) =
        hmaps.restrict _ _ _ ⁻¹' ((↑) ⁻¹' B.M i) := by
      ext y
      exact B.mem_image_iff_of_mem_mapU hf y.2
    change IsClosed ((↑) ⁻¹' (f '' (B.M i ∩ W)) : Set (B.mapU g W W'))
    rw [heq]
    exact hc
  σ := B.σ
  σ_pos := B.σ_pos
  eq_sum y hy := by
    have h1 : Θ' y = Θ (g y) := by
      rw [← hΘ _ hy.2.2, hf.right_inv y hy.1]
    rw [h1, B.eq_sum _ hy.2.1]
    exact Finset.sum_congr (Finset.filter_congr fun i _ =>
      (B.mem_image_iff_of_mem_mapU hf hy).symm) fun _ _ => rfl

/-- The moved structure of an `n`-dimensional structure is `n`-dimensional. -/
theorem isOfDim_mapDiffeo (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W') (hxW : x ∈ W) {y : Obj'}
    (hxy : f x = y) (hΘ : ∀ u ∈ W, Θ' (f u) = Θ u) {n : ℕ} (hB : B.IsOfDim n) :
    (B.mapDiffeo hf hxW hxy hΘ).IsOfDim n := fun i =>
  ((hB i).inter_isOpen hf.isScSmoothOn.isOpen).image_isScDiffeoOn hf inter_subset_right

end EpGroupoid.LocalBranchingStructure

namespace EpFunctor

variable {F : EpFunctor X Y}

/-! #### The orbit sets of push-forwards and pull-backs -/

/-- `|supp(F^*Θ')| = |F|⁻¹(|supp(Θ')|)`. -/
theorem orbitSupp_pullbackTheta (F : EpFunctor X Y) {Θ' : Obj' → ℚ} (hΘ' : Y.IsFunctorial Θ') :
    X.orbitSupp (F.pullbackTheta Θ') = F.orbitMap ⁻¹' Y.orbitSupp Θ' := by
  ext q
  obtain ⟨x, rfl⟩ := X.surjective_π q
  rw [mem_preimage, F.orbitMap_π]
  constructor
  · rintro ⟨x', hx', hxx'⟩
    exact ⟨F.obj x', hx', Y.π_eq_π_iff.2 (F.isomorphic_obj (X.π_eq_π_iff.1 hxx'))⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨x, ?_, rfl⟩
    change 0 < Θ' (F.obj x)
    rw [← hΘ'.eq_of_isomorphic (Y.π_eq_π_iff.1 hyx)]
    exact hy

/-- `|supp(F_*Θ)| = |F|(|supp(Θ)|)` (the identity `|f_*Θ| = |Θ| ∘ |f|⁻¹` of the proof of
Theorem 11.3.3, p. 538). -/
theorem orbitSupp_pushforwardTheta (hF : F.toFunctor.Full) {Θ : Obj → ℚ}
    (hΘ : X.IsFunctorial Θ) :
    Y.orbitSupp (F.pushforwardTheta Θ) = F.orbitMap '' X.orbitSupp Θ := by
  ext q
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx⟩ := exists_isomorphic_of_pushforwardTheta_ne_zero hy.ne'
    refine ⟨X.π x, ⟨x, ?_, rfl⟩, ?_⟩
    · change 0 < Θ x
      rw [← pushforwardTheta_eq hF hΘ hx]
      exact hy
    · rw [F.orbitMap_π]
      exact Y.π_eq_π_iff.2 hx
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨F.obj x, ?_, (F.orbitMap_π x).symm⟩
    change 0 < F.pushforwardTheta Θ (F.obj x)
    rw [pushforwardTheta_obj hF hΘ]
    exact hx

/-! #### Theorem 11.3.3 for an equivalence -/

/-- **2021 Theorem 11.3.3 (2) for an equivalence** (p. 537 (2017: Theorem 11.3, p. 390)): the
pull-back `F^*Θ'` of a branched ep⁺-subgroupoid along an equivalence is one (the `Mᵢ` are moved
by a local inverse of `F`, the weights kept). -/
theorem isBranchedEpSubgroupoid_pullbackTheta (hF : F.IsEquivalence) {Θ' : Obj' → ℚ}
    (hΘ' : Y.IsBranchedEpSubgroupoid Θ') : X.IsBranchedEpSubgroupoid (F.pullbackTheta Θ') where
  nonneg _ := hΘ'.nonneg _
  isFunctorial := F.isFunctorial_pullbackTheta hΘ'.isFunctorial
  support_subset x hx := (hF.isLocalScDiffeo_obj.mem_smoothSet_iff x).1 (hΘ'.support_subset hx)
  paracompactSpace_orbitSupp := by
    rw [F.orbitSupp_pullbackTheta hΘ'.isFunctorial]
    set e := IsHomeomorph.homeomorph _ hF.isHomeomorph_orbitMap
    have he : F.orbitMap ⁻¹' Y.orbitSupp Θ' = e.symm '' Y.orbitSupp Θ' :=
      (congrFun e.image_symm _).symm
    have := hΘ'.paracompactSpace_orbitSupp
    rw [he]
    exact (e.symm.image _).paracompactSpace_iff.1 inferInstance
  localBranching x hx := by
    obtain ⟨B'⟩ := hΘ'.localBranching _ hx
    obtain ⟨U, V, g, hxU, hd⟩ := hF.isLocalScDiffeo_obj x
    exact ⟨B'.mapDiffeo hd.symm (hd.mapsTo hxU) (hd.left_inv x hxU) fun z hz => by
      simp only [pullbackTheta_apply, hd.right_inv z hz]⟩

/-- For `y ∈ supp(F_*Θ)`: some `x ∈ supp(Θ)` has a morphism `ψ : F(x) → y`. -/
theorem exists_mem_supp_of_mem_supp_pushforwardTheta (hF : F.toFunctor.Full) {Θ : Obj → ℚ}
    (hΘ : X.IsFunctorial Θ) {y : Obj'} (hy : y ∈ EpGroupoid.supp (F.pushforwardTheta Θ)) :
    ∃ x ∈ EpGroupoid.supp Θ, ∃ ψ, Y.src ψ = F.obj x ∧ Y.tgt ψ = y := by
  obtain ⟨x, ψ, hs, ht⟩ := exists_isomorphic_of_pushforwardTheta_ne_zero hy.ne'
  refine ⟨x, ?_, ψ, hs, ht⟩
  change 0 < Θ x
  rw [← pushforwardTheta_eq hF hΘ ⟨ψ, hs, ht⟩]
  exact hy

/-- The local branching structure of `F_*Θ` at `y`: one of `Θ` at `x` moved by the chart
`Q = ψ̂ ∘ F` along `ψ : F(x) → y` (`TransportChart`). -/
theorem exists_localBranchingStructure_pushforwardTheta (hF : F.IsEquivalence) {Θ : Obj → ℚ}
    (hΘ : X.IsFunctorial Θ) {x : Obj} {y : Obj'} {ψ : Mor'} (hs : Y.src ψ = F.obj x)
    (ht : Y.tgt ψ = y) (B : X.LocalBranchingStructure Θ x) :
    ∃ B' : Y.LocalBranchingStructure (F.pushforwardTheta Θ) y,
      ∀ n, B.IsOfDim n → B'.IsOfDim n := by
  obtain ⟨T, -⟩ := exists_transportChart hF.isLocalScDiffeo_obj hs ht
  have hΘT : ∀ u ∈ T.W, F.pushforwardTheta Θ (T.Q u) = Θ u := fun u hu =>
    pushforwardTheta_eq hF.full hΘ ⟨T.ψ u, T.src_ψ u hu, T.tgt_ψ u hu⟩
  exact ⟨B.mapDiffeo T.isScDiffeoOn_Q T.mem_W T.Q_self hΘT, fun n hn =>
    B.isOfDim_mapDiffeo T.isScDiffeoOn_Q T.mem_W T.Q_self hΘT hn⟩

/-- **2021 Theorem 11.3.3 (1) for an equivalence** (p. 537 (2017: Theorem 11.3, p. 390)): the
push-forward `F_*Θ` of a branched ep⁺-subgroupoid along an equivalence is one (a structure at
`x` is moved by `Q = ψ̂ ∘ F` to `y`). -/
theorem isBranchedEpSubgroupoid_pushforwardTheta (hF : F.IsEquivalence) {Θ : Obj → ℚ}
    (hΘ : X.IsBranchedEpSubgroupoid Θ) : Y.IsBranchedEpSubgroupoid (F.pushforwardTheta Θ) where
  nonneg := pushforwardTheta_nonneg hΘ.nonneg
  isFunctorial := isFunctorial_pushforwardTheta hF.full hΘ.isFunctorial
  support_subset y hy := by
    obtain ⟨x, hx, ψ, hs, ht⟩ :=
      exists_mem_supp_of_mem_supp_pushforwardTheta hF.full hΘ.isFunctorial hy
    have h1 : F.obj x ∈ Y.PObj.smoothSet :=
      (hF.isLocalScDiffeo_obj.mem_smoothSet_iff x).2 (hΘ.support_subset hx)
    rw [← ht]
    exact (Y.mem_smoothSet_tgt_iff ψ).2 ((Y.mem_smoothSet_src_iff ψ).1 (hs ▸ h1))
  paracompactSpace_orbitSupp := by
    rw [orbitSupp_pushforwardTheta hF.full hΘ.isFunctorial]
    set e := IsHomeomorph.homeomorph _ hF.isHomeomorph_orbitMap
    have := hΘ.paracompactSpace_orbitSupp
    exact (e.image _).paracompactSpace_iff.1 inferInstance
  localBranching y hy := by
    obtain ⟨x, hx, ψ, hs, ht⟩ :=
      exists_mem_supp_of_mem_supp_pushforwardTheta hF.full hΘ.isFunctorial hy
    obtain ⟨B⟩ := hΘ.localBranching x hx
    obtain ⟨B', -⟩ := exists_localBranchingStructure_pushforwardTheta hF hΘ.isFunctorial hs ht B
    exact ⟨B'⟩

/-- **Theorem 11.3.3 (3) for an equivalence**: closedness (Definition 9.1.6 (1)) is preserved by
`F_*` and `F^*`. -/
theorem isClosedBranched_pushforwardTheta (hF : F.IsEquivalence) {Θ : Obj → ℚ}
    (hΘ : X.IsFunctorial Θ) (hc : X.IsClosedBranched Θ) :
    Y.IsClosedBranched (F.pushforwardTheta Θ) := by
  unfold EpGroupoid.IsClosedBranched
  rw [orbitSupp_pushforwardTheta hF.full hΘ]
  exact hF.isHomeomorph_orbitMap.isClosedMap _ hc

theorem isClosedBranched_pullbackTheta (F : EpFunctor X Y) {Θ' : Obj' → ℚ}
    (hΘ' : Y.IsFunctorial Θ') (hc : Y.IsClosedBranched Θ') :
    X.IsClosedBranched (F.pullbackTheta Θ') := by
  unfold EpGroupoid.IsClosedBranched
  rw [F.orbitSupp_pullbackTheta hΘ']
  exact hc.preimage F.continuous_orbitMap

/-- **Theorem 11.3.3 (4) for an equivalence**: compactness (Definition 9.1.6 (2)) is preserved by
`F_*` and `F^*`. -/
theorem isCompactBranched_pushforwardTheta (F : EpFunctor X Y) (hF : F.toFunctor.Full)
    {Θ : Obj → ℚ} (hΘ : X.IsFunctorial Θ) (hc : X.IsCompactBranched Θ) :
    Y.IsCompactBranched (F.pushforwardTheta Θ) := by
  unfold EpGroupoid.IsCompactBranched
  rw [orbitSupp_pushforwardTheta hF hΘ]
  exact hc.image F.continuous_orbitMap

theorem isCompactBranched_pullbackTheta (hF : F.IsEquivalence) {Θ' : Obj' → ℚ}
    (hΘ' : Y.IsFunctorial Θ') (hc : Y.IsCompactBranched Θ') :
    X.IsCompactBranched (F.pullbackTheta Θ') := by
  unfold EpGroupoid.IsCompactBranched
  rw [F.orbitSupp_pullbackTheta hΘ']
  exact (IsHomeomorph.homeomorph _ hF.isHomeomorph_orbitMap).isCompact_preimage.2 hc

/-- **Theorem 11.3.3 (5) for an equivalence, orbifold-type** (Definition 9.1.8 (2)): the values
of `F_*Θ` and `F^*Θ'` are values of `Θ`, `Θ'` (or `0`). -/
theorem isOrbifoldType_pushforwardTheta (F : EpFunctor X Y) {Θ : Obj → ℚ}
    (h : EpGroupoid.IsOrbifoldType Θ) :
    EpGroupoid.IsOrbifoldType (F.pushforwardTheta Θ) := fun y => by
  unfold EpFunctor.pushforwardTheta
  split_ifs
  exacts [h _, Or.inl rfl]

theorem isOrbifoldType_pullbackTheta (F : EpFunctor X Y) {Θ' : Obj' → ℚ}
    (h : EpGroupoid.IsOrbifoldType Θ') : EpGroupoid.IsOrbifoldType (F.pullbackTheta Θ') :=
  fun x => h (F.obj x)

/-- **Theorem 11.3.3 (5) for an equivalence, manifold-type** (Definition 9.1.8 (1)), push-forward:
two morphisms `y → y'` between points of `supp(F_*Θ)` are conjugated by `ψ : F(x) → y`,
`ψ' : F(x') → y'` to morphisms `F(x) → F(x')`, lifted by fullness to `x → x'` with
`x, x' ∈ supp(Θ)`. -/
theorem isManifoldType_pushforwardTheta (hF : F.IsEquivalence) {Θ : Obj → ℚ}
    (hΘ : X.IsFunctorial Θ) (h : X.IsManifoldType Θ) :
    Y.IsManifoldType (F.pushforwardTheta Θ) := by
  refine ⟨isOrbifoldType_pushforwardTheta F h.1, fun φ φ' hs ht hss htt => ?_⟩
  obtain ⟨x, hx, ψ, hψs, hψt⟩ := exists_mem_supp_of_mem_supp_pushforwardTheta hF.full hΘ hs
  obtain ⟨x', hx', ψ', hψ's, hψ't⟩ := exists_mem_supp_of_mem_supp_pushforwardTheta hF.full hΘ ht
  -- `χ ↦ ψ'⁻¹ ∘ χ ∘ ψ`, a morphism `F(x) → F(x')`
  let c : Mor' → Mor' := fun χ => Y.comp (Y.comp (Y.inv ψ') χ) ψ
  have hc : ∀ χ, Y.src χ = Y.src φ → Y.tgt χ = Y.tgt φ →
      Y.src (c χ) = F.obj x ∧ Y.tgt (c χ) = F.obj x' := fun χ h1 h2 => by
    have e1 : Y.src (Y.inv ψ') = Y.tgt χ := by rw [Y.src_inv, hψ't, h2]
    have e2 : Y.src (Y.comp (Y.inv ψ') χ) = Y.tgt ψ := by
      rw [Y.src_comp _ _ e1, h1, hψt]
    refine ⟨by rw [Y.src_comp _ _ e2, hψs], ?_⟩
    rw [Y.tgt_comp _ _ e2, Y.tgt_comp _ _ e1, Y.tgt_inv, hψ's]
  obtain ⟨hc1, hc2⟩ := hc φ rfl rfl
  obtain ⟨hc1', hc2'⟩ := hc φ' hss.symm htt.symm
  obtain ⟨σ, hσs, hσt, hσ⟩ := hF.exists_mor_eq hc1 hc2
  obtain ⟨σ', hσ's, hσ't, hσ'⟩ := hF.exists_mor_eq hc1' hc2'
  have hσσ' : σ = σ' := h.2 σ σ' (hσs ▸ hx) (hσt ▸ hx') (hσs.trans hσ's.symm)
    (hσt.trans hσ't.symm)
  have hcc : c φ = c φ' := by rw [← hσ, ← hσ', hσσ']
  -- cancel `ψ` on the right and `ψ'⁻¹` on the left
  have e1 : Y.src (Y.inv ψ') = Y.tgt φ := by rw [Y.src_inv, hψ't]
  have e1' : Y.src (Y.inv ψ') = Y.tgt φ' := by rw [Y.src_inv, hψ't, htt]
  have e2 : Y.src (Y.comp (Y.inv ψ') φ) = Y.tgt ψ := by rw [Y.src_comp _ _ e1, hψt]
  have e2' : Y.src (Y.comp (Y.inv ψ') φ') = Y.tgt ψ := by rw [Y.src_comp _ _ e1', ← hss, hψt]
  have h3 := Y.comp_right_cancel (φ := ψ) e2 e2' hcc
  exact Y.comp_left_cancel e1 e1' h3

/-- **Theorem 11.3.3 (5) for an equivalence, manifold-type**, pull-back (`F` is faithful). -/
theorem isManifoldType_pullbackTheta (hF : F.IsEquivalence) {Θ' : Obj' → ℚ}
    (h : Y.IsManifoldType Θ') : X.IsManifoldType (F.pullbackTheta Θ') := by
  refine ⟨isOrbifoldType_pullbackTheta F h.1, fun φ φ' hs ht hss htt => ?_⟩
  refine hF.mor_injective hss htt (h.2 _ _ ?_ ?_ ?_ ?_)
  · rw [F.src_mor]; exact hs
  · rw [F.tgt_mor]; exact ht
  · rw [F.src_mor, F.src_mor, hss]
  · rw [F.tgt_mor, F.tgt_mor, htt]

/-- **Theorem 11.3.3 (6) for an equivalence, dimension**: `n`-dimensionality (Definition 9.1.2) is
preserved by `F^*`. -/
theorem isNDimensional_pullbackTheta (hF : F.IsEquivalence) {Θ' : Obj' → ℚ} {n : ℕ}
    (h : Y.IsNDimensional Θ' n) : X.IsNDimensional (F.pullbackTheta Θ') n := fun x hx => by
  obtain ⟨B', hB'⟩ := h _ hx
  obtain ⟨U, V, g, hxU, hd⟩ := hF.isLocalScDiffeo_obj x
  have hΘ : ∀ z ∈ V, F.pullbackTheta Θ' (g z) = Θ' z := fun z hz => by
    simp only [pullbackTheta_apply, hd.right_inv z hz]
  exact ⟨B'.mapDiffeo hd.symm (hd.mapsTo hxU) (hd.left_inv x hxU) hΘ,
    B'.isOfDim_mapDiffeo hd.symm (hd.mapsTo hxU) (hd.left_inv x hxU) hΘ hB'⟩

/-- **Theorem 11.3.3 (6) for an equivalence, dimension**, push-forward. -/
theorem isNDimensional_pushforwardTheta (hF : F.IsEquivalence) {Θ : Obj → ℚ}
    (hΘ : X.IsFunctorial Θ) {n : ℕ} (h : X.IsNDimensional Θ n) :
    Y.IsNDimensional (F.pushforwardTheta Θ) n := fun y hy => by
  obtain ⟨x, hx, ψ, hs, ht⟩ := exists_mem_supp_of_mem_supp_pushforwardTheta hF.full hΘ hy
  obtain ⟨B, hB⟩ := h x hx
  obtain ⟨B', hB'⟩ := exists_localBranchingStructure_pushforwardTheta hF hΘ hs ht B
  exact ⟨B', hB' n hB⟩

/-- `F_*` commutes with sums: `(F_*Θ)(y)` is the value at one chosen point `x`, the same for every
`Θ`. -/
theorem exists_pushforwardTheta_eq_apply (F : EpFunctor X Y) (y : Obj') :
    (∃ x, ∀ Θ : Obj → ℚ, F.pushforwardTheta Θ y = Θ x) ∨
      ∀ Θ : Obj → ℚ, F.pushforwardTheta Θ y = 0 := by
  by_cases hex : ∃ x, Y.Isomorphic (F.obj x) y
  · exact Or.inl ⟨hex.choose, fun Θ => by rw [pushforwardTheta, dif_pos hex]⟩
  · exact Or.inr fun Θ => pushforwardTheta_of_not_exists hex

/-- **Theorem 11.3.3 (6) for an equivalence**: the dimensional decomposition of Proposition 9.1.11
(`IsDimDecomposition`: `k`-dimensional branched ep⁺-subgroupoids `Θ_k` with `Θ = ∑ Θ_k`) is
pushed forward. -/
theorem isDimDecomposition_pushforwardTheta (hF : F.IsEquivalence) {Θ : Obj → ℚ}
    {Θk : ℕ → Obj → ℚ} (h : X.IsDimDecomposition Θ Θk) :
    Y.IsDimDecomposition (F.pushforwardTheta Θ) fun k => F.pushforwardTheta (Θk k) where
  isBranched k := isBranchedEpSubgroupoid_pushforwardTheta hF (h.isBranched k)
  isNDimensional k :=
    isNDimensional_pushforwardTheta hF (h.isBranched k).isFunctorial (h.isNDimensional k)
  finite_support y := by
    rcases F.exists_pushforwardTheta_eq_apply y with ⟨x, hx⟩ | h0
    · simp only [hx]; exact h.finite_support x
    · simp [h0]
  eq_finsum y := by
    rcases F.exists_pushforwardTheta_eq_apply y with ⟨x, hx⟩ | h0
    · simp only [hx]; exact h.eq_finsum x
    · simp only [h0, finsum_zero]

/-- **Theorem 11.3.3 (6) for an equivalence**, pull-back. -/
theorem isDimDecomposition_pullbackTheta (hF : F.IsEquivalence) {Θ' : Obj' → ℚ}
    {Θk : ℕ → Obj' → ℚ} (h : Y.IsDimDecomposition Θ' Θk) :
    X.IsDimDecomposition (F.pullbackTheta Θ') fun k => F.pullbackTheta (Θk k) where
  isBranched k := isBranchedEpSubgroupoid_pullbackTheta hF (h.isBranched k)
  isNDimensional k := isNDimensional_pullbackTheta hF (h.isNDimensional k)
  finite_support x := h.finite_support (F.obj x)
  eq_finsum x := h.eq_finsum (F.obj x)

end EpFunctor

end Branched

end Polyfold
