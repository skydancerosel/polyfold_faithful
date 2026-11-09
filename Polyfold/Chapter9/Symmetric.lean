import Polyfold.Chapter9.Basic
import Polyfold.Chapter7.NaturalRep

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.1 "Basic Definitions": the restriction remark after **Definition 9.1.6**
(p. 404; 2017: after Definition 9.2, p. 293), the symmetrization (pp. 404–405; 2017:
pp. 293–294) and **Lemma 9.1.7** (p. 405; 2017: Lemma 9.2, p. 294).  Numbers and pages are the
2021 text's, the 2017 ones in parentheses; the two texts agree on these passages.  The two facts of
Part I that the symmetrization uses are proved first.

# Restricted and symmetric local branching structures

## The text, paraphrased

(p. 404 (2017: p. 293)) If `V(x₀) ⊆ U(x)`, the sets `Nᵢ = Mᵢ ∩ V(x₀)` with the same weights give
an induced representation `Θ(y) = ∑_{i : y ∈ Nᵢ} σᵢ` on `V(x₀)`; some (or all) of the `Nᵢ` might
be empty.  Symmetric representations always exist: take `V(x) ⊆ U(x)` admitting the natural
`G_x`-action, assume the branching structure `(Mᵢ)_{i ∈ I}`, `(σᵢ)` is given on `V(x)`, and put
`J = I × G_x`, `M_{(i,g)} = g ∗ Mᵢ`, `σ_{(i,g)} = σᵢ / |G_x|`.  Since `Θ` is a functor,
`∑_{(i,g) : y ∈ g ∗ Mᵢ} σ_{(i,g)} = |G_x|⁻¹ ∑_g ∑_{i : g⁻¹ ∗ y ∈ Mᵢ} σᵢ
= |G_x|⁻¹ ∑_g Θ(g⁻¹ ∗ y) = Θ(y)`.  `G_x` acts on `J` with `h ∗ M_j = M_{h(j)}`,
`σ_j = σ_{h(j)}`.

(Lemma 9.1.7, p. 405 (2017: Lemma 9.2, p. 294)) For a branched ep⁺-subgroupoid `Θ` and every `x`
with `Θ(x) > 0` there are an open `U(x)` admitting the natural `G_x`-action, submanifolds `Mᵢ`,
`i ∈ I`, properly embedded in `U(x)`, a `G_x`-action on `I`, and rational weights `σᵢ > 0` with
(1) `g ∗ Mᵢ = M_{g(i)}`, (2) `σᵢ = σ_{g(i)}`, (3) `Θ(y) = ∑_{i : y ∈ Mᵢ} σᵢ` for `y ∈ U(x)`.

## What is formalized

* Part I facts on smooth finite-dimensional submanifolds (Definition 4.13 [4.4]):
  `MPolyfold.IsScPlusRetractionOn.mono` (an sc⁺-retraction restricts to open invariant subsets),
  `MPolyfold.IsSmoothSubmanifold.exists_subset` (the retraction data can be taken inside a given
  open set), `MPolyfold.IsSmoothSubmanifold.inter_isOpen` (`A ∩ V` is a submanifold for `V`
  open), `MPolyfold.IsSmoothSubmanifold.image_of_isScDiffeoOn` (the image of a submanifold
  `A ⊆ U` under an sc-diffeomorphism `f : U → U'` between open sets is a submanifold; the
  retraction is `f ∘ s ∘ g`, its level-one part through `IsScSmoothOn.levelOne`).
* `isProperMap_inclusion_iff` (the inclusion `A → U` is proper iff `A` is closed in `U`).
* `EpGroupoid.LocalBranchingStructure.restrict` (the restriction remark, at `x` itself).
* `EpGroupoid.SymmetricBranchingStructure` (the data of Lemma 9.1.7),
  `EpGroupoid.LocalBranchingStructure.symmetrize` (the construction `J = I × G_x`),
  `EpGroupoid.lemma_9_1_7` (**Lemma 9.1.7**, with `U(x)` inside any given open `V ∋ x`) and
  `EpGroupoid.lemma_9_1_7'` (the properties (1)–(3) spelled out).

## What the text leaves implicit, and the choices made

* "The natural `G_x`-action on `U(x)`" is a natural representation `(Φ, Γ)` of Theorem 7.1
  (`NaturalRep`), and `g ∗ A` is `Φ(g)(A)`.  `|G_x|` is `Nat.card (G_x)` (Proposition 7.4: `G_x`
  is finite).
* The restriction remark (reading): Definition 9.1.2 (2) (2017: Definition 9.1 (2)) asks
  `x ∈ Mᵢ` for every `i`, which the `Nᵢ = Mᵢ ∩ V(x₀)` need not satisfy at `x₀` ("some (or all) of
  the `Nᵢ` might be empty").  We formalize the remark for an open `V ⊆ U(x)` containing `x`
  itself, where every `Nᵢ` contains `x` and the restriction is again a local branching structure
  at `x` (`restrict`); this is the case the symmetrization uses (`V(x) ⊆ U(x)`).  The `Nᵢ` are
  submanifolds (`inter_isOpen`) and properly embedded in `V` (closed in `U(x)`, hence in `V`).
* "Without loss of generality the branching structure is given on `V(x)`" is the restriction:
  `symmetrize` takes `Mᵢ ∩ U` for the domain `U ⊆ U(x)` of the natural representation, so
  `M_{(i,g)} = Φ(g)(Mᵢ ∩ U)`.  That `g ∗ (Mᵢ ∩ U)` is a submanifold properly embedded in `U` and
  passing through `x` (`Φ(g)(x) = x`) is used, not stated, in the text; here it is
  `image_of_isScDiffeoOn` and `isProperMap_inclusion_iff` (`Φ(g)` is a homeomorphism of `U`).
* The action of `G_x` on `J = I × G_x` is `h(i, g) = (i, hg)` (`mulActionProdLeft`); with it
  `Φ(h)(M_{(i,g)}) = M_{(i,hg)}` (`Φ(hg) = Φ(h) ∘ Φ(g)` on `U`) and `σ_{(i,hg)} = σ_{(i,g)}`.
* The sum is computed as in the text: `y ∈ Φ(g)(Mᵢ ∩ U)` iff `Φ(g⁻¹)(y) ∈ Mᵢ`
  (`NaturalRep.mem_image_Φ_iff`), and `Θ(Φ(g)(y)) = Θ(y)` because `Γ(g, y)` is a morphism
  `y → Φ(g)(y)` and `Θ` is a functor (`IsFunctorial.apply_Φ`).
* Not formalized here: Remark 9.1.3 (b) (2017: Remark 9.2 (b)), two branching structures by graphs
  in `ℝ²`, which needs graphs of smooth functions as submanifolds of the M-polyfold `ℝ²`.
-/

set_option maxSynthPendingDepth 3

open Set

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- An sc⁺-retraction on `V` restricts to an sc⁺-retraction on every open `W ⊆ V` that it maps
into itself. -/
theorem IsScPlusRetractionOn.mono {s : X → X} {V W : Set X} (h : P.IsScPlusRetractionOn s V)
    (hW : IsOpen W) (hWV : W ⊆ V) (hmaps : MapsTo s W W) : P.IsScPlusRetractionOn s W where
  isScSmoothOn := h.isScSmoothOn.mono hW hWV
  mapsTo := hmaps
  idem x hx := h.idem x (hWV hx)
  mem_levelSet x hx := h.mem_levelSet x (hWV hx)
  isScSmoothOn_one x₀ := (h.isScSmoothOn_one x₀).mono hW hWV

/-- The local data of Definition 4.13 for `A`, inside a given open `V`: every `a ∈ A ∩ V` has an
open neighbourhood `W ⊆ V` with an sc⁺-retraction `s : W → W`, `s(W) = A ∩ W`
(`W = V' ∩ V ∩ s⁻¹(V)` for the data `(V', s)` of `A` at `a`). -/
theorem IsSmoothSubmanifold.exists_subset {A V : Set X} (hA : P.IsSmoothSubmanifold A)
    (hV : IsOpen V) {a : X} (ha : a ∈ A) (haV : a ∈ V) :
    ∃ W : Set X, IsOpen W ∧ a ∈ W ∧ W ⊆ V ∧
      ∃ s : X → X, P.IsScPlusRetractionOn s W ∧ s '' W = A ∩ W := by
  obtain ⟨V', hV', haV', s, hs, himg⟩ := hA a ha
  have hsa : s a = a := by
    obtain ⟨b, hb, hba⟩ := (himg.symm ▸ ⟨ha, haV'⟩ : a ∈ s '' V')
    rw [← hba, hs.idem b hb]
  have hWo : IsOpen (V' ∩ V ∩ s ⁻¹' V) :=
    (hs.isScSmoothOn.continuousOn.mono inter_subset_left).isOpen_inter_preimage
      (hV'.inter hV) hV
  have hmaps : MapsTo s (V' ∩ V ∩ s ⁻¹' V) (V' ∩ V ∩ s ⁻¹' V) := fun y hy => by
    refine ⟨⟨hs.mapsTo hy.1.1, hy.2⟩, ?_⟩
    change s (s y) ∈ V
    rw [hs.idem y hy.1.1]
    exact hy.2
  refine ⟨V' ∩ V ∩ s ⁻¹' V, hWo, ⟨⟨haV', haV⟩, by rw [mem_preimage, hsa]; exact haV⟩,
    fun y hy => hy.1.2, s, hs.mono hWo (fun y hy => hy.1.1) hmaps, ?_⟩
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hz : s y ∈ s '' V' := ⟨y, hy.1.1, rfl⟩
    rw [himg] at hz
    exact ⟨hz.1, hmaps hy⟩
  · rintro ⟨hzA, hz⟩
    obtain ⟨b, hb, hbz⟩ := (himg.symm ▸ ⟨hzA, hz.1.1⟩ : z ∈ s '' V')
    refine ⟨z, hz, ?_⟩
    rw [← hbz, hs.idem b hb]

/-- **The image of a submanifold under an sc-diffeomorphism**: if `f : U → U'` is an
sc-diffeomorphism between open subsets (inverse `g`) and `A ⊆ U` is a smooth finite-dimensional
submanifold (Definition 4.13), so is `f(A)`: at `f(a)` the conjugate `f ∘ s ∘ g` of an
sc⁺-retraction `s : W → W` (`W ⊆ U`) is an sc⁺-retraction of `U' ∩ g⁻¹(W)` onto `f(A)`. -/
theorem IsSmoothSubmanifold.image_of_isScDiffeoOn {f : X → Y} {g : Y → X} {U : Set X}
    {U' : Set Y} (hf : P.IsScDiffeoOn Q f g U U') {A : Set X} (hA : P.IsSmoothSubmanifold A)
    (hAU : A ⊆ U) : Q.IsSmoothSubmanifold (f '' A) := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨W, hW, haW, hWU, s, hs, himg⟩ := hA.exists_subset hf.isScSmoothOn.isOpen ha (hAU ha)
  have hW'o : IsOpen (U' ∩ g ⁻¹' W) :=
    hf.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hf.isScSmoothOn_inv.isOpen hW
  have hgW' : MapsTo g (U' ∩ g ⁻¹' W) W := fun y hy => hy.2
  have hmapsW' : MapsTo (f ∘ s ∘ g) (U' ∩ g ⁻¹' W) (U' ∩ g ⁻¹' W) := fun y hy => by
    have h1 : s (g y) ∈ W := hs.mapsTo hy.2
    refine ⟨hf.mapsTo (hWU h1), ?_⟩
    change g (f (s (g y))) ∈ W
    rw [hf.left_inv _ (hWU h1)]
    exact h1
  have hga : g (f a) = a := hf.left_inv a (hAU ha)
  obtain ⟨w₀, hw₀, hw₀a⟩ : a ∈ s '' W := himg ▸ ⟨ha, haW⟩
  have ha1 : a ∈ P.levelSet 1 := hw₀a ▸ hs.mem_levelSet w₀ hw₀
  have hg_sm : Q.IsScSmoothOn P g (U' ∩ g ⁻¹' W) :=
    hf.isScSmoothOn_inv.mono hW'o inter_subset_left
  refine ⟨U' ∩ g ⁻¹' W, hW'o, ⟨hf.mapsTo (hAU ha), by rw [mem_preimage, hga]; exact haW⟩,
    f ∘ s ∘ g, ⟨?_, hmapsW', fun y hy => ?_, fun y hy => ?_, fun y₀ => ?_⟩, ?_⟩
  · exact hf.isScSmoothOn.comp (hs.isScSmoothOn.comp hg_sm hgW')
      fun y hy => hWU (hs.mapsTo (hgW' hy))
  · simp only [Function.comp_apply]
    rw [hf.left_inv _ (hWU (hs.mapsTo (hgW' hy))), hs.idem _ (hgW' hy)]
  · exact hf.isScSmoothOn.mapsTo_levelSet 1
      ⟨hWU (hs.mapsTo (hgW' hy)), hs.mem_levelSet _ (hgW' hy)⟩
  · let x₀ : P.Level 1 := P.levelMk 1 a ha1
    let F₁ : P.Level 1 → Q.Level 1 := fun x => Q.toLevelOne y₀ (f (P.levelVal 1 x))
    have hF₁ : P.shift.IsScSmoothOn Q.shift F₁ {x | P.levelVal 1 x ∈ U} :=
      hf.isScSmoothOn.levelOne fun x hx =>
        levelVal_toLevelOne y₀ (hf.isScSmoothOn.mapsTo_levelSet 1 ⟨hx, levelVal_mem x⟩)
    have hin : Q.IsScSmoothOn P.shift (P.toLevelOne x₀ ∘ s ∘ g) (U' ∩ g ⁻¹' W) :=
      (hs.isScSmoothOn_one x₀).comp hg_sm hgW'
    have hmaps : MapsTo (P.toLevelOne x₀ ∘ s ∘ g) (U' ∩ g ⁻¹' W) {x | P.levelVal 1 x ∈ U} :=
      fun y hy => by
        change P.levelVal 1 (P.toLevelOne x₀ (s (g y))) ∈ U
        rw [levelVal_toLevelOne x₀ (hs.mem_levelSet _ (hgW' hy))]
        exact hWU (hs.mapsTo (hgW' hy))
    refine (hF₁.comp hin hmaps).congr fun y hy => ?_
    simp only [Function.comp_apply, F₁]
    rw [levelVal_toLevelOne x₀ (hs.mem_levelSet _ (hgW' hy))]
  · ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h1 : s (g y) ∈ s '' W := ⟨g y, hgW' hy, rfl⟩
      rw [himg] at h1
      exact ⟨⟨s (g y), h1.1, rfl⟩, hmapsW' hy⟩
    · rintro ⟨⟨a', ha', rfl⟩, hz⟩
      have hga' : g (f a') = a' := hf.left_inv a' (hAU ha')
      have ha'W : a' ∈ W := by
        have h2 := hz.2
        rwa [mem_preimage, hga'] at h2
      obtain ⟨w, hw, hwa⟩ : a' ∈ s '' W := himg ▸ ⟨ha', ha'W⟩
      refine ⟨f a', hz, ?_⟩
      simp only [Function.comp_apply]
      rw [hga', ← hwa, hs.idem w hw]

/-- **An open piece of a submanifold is a submanifold**: if `A` is a smooth finite-dimensional
submanifold (Definition 4.13) and `V` is open, then `A ∩ V` is one. -/
theorem IsSmoothSubmanifold.inter_isOpen {A V : Set X} (hA : P.IsSmoothSubmanifold A)
    (hV : IsOpen V) : P.IsSmoothSubmanifold (A ∩ V) := by
  rintro a ⟨ha, haV⟩
  obtain ⟨W, hW, haW, hWV, s, hs, himg⟩ := hA.exists_subset hV ha haV
  refine ⟨W, hW, haW, s, hs, ?_⟩
  rw [himg, inter_assoc, inter_eq_right.2 hWV]

end MPolyfold

/-- The inclusion of `A ⊆ U` is proper iff `A` is closed in `U`. -/
theorem isProperMap_inclusion_iff {Z : Type*} [TopologicalSpace Z] {A U : Set Z} (h : A ⊆ U) :
    IsProperMap (inclusion h) ↔ IsClosed ((↑) ⁻¹' A : Set U) := by
  have hr : ((↑) ⁻¹' A : Set U) = range (inclusion h) := (range_inclusion h).symm
  rw [hr]
  exact ⟨fun hp => hp.isClosedMap.isClosed_range,
    fun hc => (Topology.IsClosedEmbedding.mk (Topology.IsEmbedding.inclusion h) hc).isProperMap⟩

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ}

namespace LocalBranchingStructure

variable {x : Obj} (B : X.LocalBranchingStructure Θ x)

/-- `Mᵢ` is closed in `U(x)` (the inclusion is proper). -/
theorem isClosed_M (i : B.ι) : IsClosed ((↑) ⁻¹' B.M i : Set B.U) :=
  (isProperMap_inclusion_iff (B.subset_U i)).1 (B.isProperMap i)

open scoped Classical in
/-- **The restriction remark (p. 404 [2017: p. 293])**: on an open `V ⊆ U(x)` containing `x`,
the sets `Nᵢ = Mᵢ ∩ V` with the same weights `σᵢ` are a local branching structure at `x`. -/
def restrict {V : Set Obj} (hV : IsOpen V) (hxV : x ∈ V) (hVU : V ⊆ B.U) :
    X.LocalBranchingStructure Θ x where
  U := V
  isOpen_U := hV
  mem_U := hxV
  ι := B.ι
  M i := B.M i ∩ V
  subset_U _ := inter_subset_right
  isSmoothSubmanifold i := (B.isSmoothSubmanifold i).inter_isOpen hV
  mem_M i := ⟨B.mem_M i, hxV⟩
  isProperMap i := by
    refine (isProperMap_inclusion_iff _).2 ?_
    have h := (B.isClosed_M i).preimage (continuous_inclusion hVU)
    convert h using 1
    ext y
    exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩
  σ := B.σ
  σ_pos := B.σ_pos
  eq_sum y hy := by
    rw [B.eq_sum y (hVU hy)]
    have hfil : ∀ i, y ∈ B.M i ↔ y ∈ B.M i ∩ V := fun i => ⟨fun h => ⟨h, hy⟩, fun h => h.1⟩
    simp only [hfil]
    congr

@[simp] theorem restrict_U {V : Set Obj} (hV : IsOpen V) (hxV : x ∈ V) (hVU : V ⊆ B.U) :
    (B.restrict hV hxV hVU).U = V := rfl

@[simp] theorem restrict_M {V : Set Obj} (hV : IsOpen V) (hxV : x ∈ V) (hVU : V ⊆ B.U)
    (i : B.ι) : (B.restrict hV hxV hVU).M i = B.M i ∩ V := rfl

end LocalBranchingStructure

variable (X) in
/-- **The data of Lemma 9.1.7 (2017: Lemma 9.2)**, a *symmetric* local branching structure at
`x`: a local branching structure on the domain `U(x) = U` of a natural representation `(Φ, Γ)` of
`G_x` (Theorem 7.1), with an action of `G_x` on the index set `I` such that (1) `g ∗ Mᵢ = M_{g(i)}`
and (2) `σᵢ = σ_{g(i)}`; (3) is the sum formula of the local branching structure. -/
structure SymmetricBranchingStructure (Θ : Obj → ℚ) (x : Obj) extends
    X.LocalBranchingStructure Θ x where
  /-- The natural representation of `G_x` on `U(x)`. -/
  rep : X.NaturalRep x
  U_eq : U = rep.U
  /-- The action of `G_x` on the index set. -/
  [mulAction : MulAction (X.Isotropy x) ι]
  image_M : ∀ (g : X.Isotropy x) (i : ι), rep.Φ g '' M i = M (g • i)
  σ_smul : ∀ (g : X.Isotropy x) (i : ι), σ (g • i) = σ i

attribute [instance] SymmetricBranchingStructure.mulAction

/-- For a functor `Θ`, `Θ(Φ(g)(y)) = Θ(y)` on the domain of a natural representation (`Γ(g, y)`
is a morphism `y → Φ(g)(y)`). -/
theorem IsFunctorial.apply_Φ (hΘ : X.IsFunctorial Θ) {x : Obj} (R : X.NaturalRep x)
    (g : X.Isotropy x) {y : Obj} (hy : y ∈ R.U) : Θ (R.Φ g y) = Θ y := by
  have h := hΘ (R.Γ g y)
  rw [R.src_Γ g y hy, R.tgt_Γ g y hy] at h
  exact h.symm

/-- For `A ⊆ U(x)` and `y ∈ U(x)`: `y ∈ Φ(g)(A)` iff `Φ(g⁻¹)(y) ∈ A`. -/
theorem NaturalRep.mem_image_Φ_iff {x : Obj} (R : X.NaturalRep x) (g : X.Isotropy x)
    {A : Set Obj} (hA : A ⊆ R.U) {y : Obj} (hy : y ∈ R.U) :
    y ∈ R.Φ g '' A ↔ R.Φ g⁻¹ y ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [(R.isScDiffeoOn_Φ g).left_inv a (hA ha)]
    exact ha
  · intro h
    exact ⟨_, h, (R.isScDiffeoOn_Φ g).right_inv y hy⟩

/-- The action `h • (i, g) = (i, h g)` of `G_x` on `J = I × G_x` (p. 404 [2017: p. 293]). -/
@[reducible] def mulActionProdLeft (G I : Type*) [Group G] : MulAction G (I × G) where
  smul h j := (j.1, h * j.2)
  one_smul j := by
    change (j.1, 1 * j.2) = j
    rw [one_mul]
  mul_smul h k j := by
    change (j.1, h * k * j.2) = (j.1, h * (k * j.2))
    rw [mul_assoc]

namespace LocalBranchingStructure

variable {x : Obj} (B : X.LocalBranchingStructure Θ x)

open scoped Classical in
/-- **The symmetrization (p. 404 [2017: pp. 293–294])**: for a natural representation `(Φ, Γ)` on
`U ⊆ U(x)` and a functor `Θ`, the index set `J = I × G_x`, `M_{(i,g)} = g ∗ (Mᵢ ∩ U)` and
`σ_{(i,g)} = σᵢ / |G_x|` give a symmetric local branching structure on `U`. -/
def symmetrize (hΘ : X.IsFunctorial Θ) (R : X.NaturalRep x) (hRU : R.U ⊆ B.U) :
    X.SymmetricBranchingStructure Θ x where
  U := R.U
  isOpen_U := R.isOpen_U
  mem_U := R.mem_U
  ι := B.ι × X.Isotropy x
  fintype := @instFintypeProd _ _ _ (Fintype.ofFinite _)
  M j := R.Φ j.2 '' (B.M j.1 ∩ R.U)
  subset_U j := ((R.mapsTo_Φ j.2).mono_left inter_subset_right).image_subset
  isSmoothSubmanifold j := ((B.isSmoothSubmanifold j.1).inter_isOpen R.isOpen_U)
    |>.image_of_isScDiffeoOn (R.isScDiffeoOn_Φ j.2) inter_subset_right
  mem_M j := ⟨x, ⟨B.mem_M j.1, R.mem_U⟩, R.Φ_self j.2⟩
  isProperMap j := by
    refine (isProperMap_inclusion_iff _).2 ?_
    have hc := ((B.restrict R.isOpen_U R.mem_U hRU).isClosed_M j.1).preimage
      ((R.isScDiffeoOn_Φ j.2⁻¹).isScSmoothOn.continuousOn.mapsToRestrict (R.mapsTo_Φ j.2⁻¹))
    convert hc using 1
    ext y
    exact R.mem_image_Φ_iff j.2 inter_subset_right y.2
  σ j := B.σ j.1 / Nat.card (X.Isotropy x)
  σ_pos j := div_pos (B.σ_pos j.1) (Nat.cast_pos.2 Nat.card_pos)
  eq_sum y hy := by
    let _i : Fintype (X.Isotropy x) := Fintype.ofFinite _
    have hcard : (Nat.card (X.Isotropy x) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    have hg : ∀ g : X.Isotropy x, (∑ i : B.ι, if y ∈ R.Φ g '' (B.M i ∩ R.U) then
        B.σ i / (Nat.card (X.Isotropy x) : ℚ) else 0) = Θ y / Nat.card (X.Isotropy x) := by
      intro g
      have hy' : R.Φ g⁻¹ y ∈ R.U := R.mapsTo_Φ g⁻¹ hy
      rw [← hΘ.apply_Φ R g⁻¹ hy, B.eq_sum _ (hRU hy'), Finset.sum_div, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [R.mem_image_Φ_iff g inter_subset_right hy]
      by_cases h : R.Φ g⁻¹ y ∈ B.M i
      · simp [h, hy']
      · simp [h]
    rw [Finset.sum_filter, Fintype.sum_prod_type_right]
    simp only [hg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Nat.card_eq_fintype_card]
    field_simp
  rep := R
  U_eq := rfl
  mulAction := mulActionProdLeft _ _
  image_M h j := by
    change R.Φ h '' (R.Φ j.2 '' (B.M j.1 ∩ R.U)) = R.Φ (h * j.2) '' (B.M j.1 ∩ R.U)
    rw [image_image]
    exact image_congr fun y hy => (R.Φ_mul h j.2 y hy.2).symm
  σ_smul _ _ := rfl

end LocalBranchingStructure

/-- **Lemma 9.1.7 (2017: Lemma 9.2), p. 405**: for a branched ep⁺-subgroupoid `Θ` and `x` with
`Θ(x) > 0` there is a symmetric local branching structure at `x`: an open neighbourhood `U(x)`
with the natural `G_x`-action `Φ` (Theorem 7.1), submanifolds `Mᵢ`, `i ∈ I`, properly embedded in
`U(x)`, a `G_x`-action on `I` and weights `σᵢ > 0` with (1) `g ∗ Mᵢ = M_{g(i)}`,
(2) `σᵢ = σ_{g(i)}`, (3) `Θ(y) = ∑_{i : y ∈ Mᵢ} σᵢ` for `y ∈ U(x)`.  `U(x)` can be taken inside
any given open neighbourhood `V` of `x`. -/
theorem lemma_9_1_7 (hΘ : X.IsBranchedEpSubgroupoid Θ) {x : Obj} (hx : x ∈ supp Θ)
    {V : Set Obj} (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ S : X.SymmetricBranchingStructure Θ x, S.U ⊆ V := by
  obtain ⟨B⟩ := hΘ.localBranching x hx
  obtain ⟨R, hR⟩ := theorem_7_1_13 X x (B.isOpen_U.inter hV) ⟨B.mem_U, hxV⟩
  exact ⟨B.symmetrize hΘ.isFunctorial R fun y hy => (hR hy).1, fun y hy => (hR hy).2⟩

open scoped Classical in
/-- **Lemma 9.1.7**, the three properties spelled out: `Φ(g)(Mᵢ) = M_{g • i}`,
`σ_{g • i} = σᵢ`, and `Θ(y) = ∑_{i : y ∈ Mᵢ} σᵢ` on `U(x)`, the domain of the natural
representation. -/
theorem lemma_9_1_7' (hΘ : X.IsBranchedEpSubgroupoid Θ) {x : Obj} (hx : x ∈ supp Θ) :
    ∃ S : X.SymmetricBranchingStructure Θ x, S.U = S.rep.U ∧
      (∀ (g : X.Isotropy x) i, S.rep.Φ g '' S.M i = S.M (g • i)) ∧
      (∀ (g : X.Isotropy x) i, S.σ (g • i) = S.σ i) ∧
      ∀ y ∈ S.U, Θ y = ∑ i with y ∈ S.M i, S.σ i := by
  obtain ⟨S, -⟩ := lemma_9_1_7 hΘ hx isOpen_univ (mem_univ x)
  exact ⟨S, S.U_eq, S.image_M, S.σ_smul, S.eq_sum⟩

end EpGroupoid

end Polyfold
