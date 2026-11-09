import Polyfold.Chapter5.PartitionsOfUnity
import Polyfold.Chapter5.StrongBundleShift
import Polyfold.Chapter3.IndexAlongPathsDevice

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017 book), Part II, Chapter 7, §7.1,
pp. 226–228: the local sc-diffeomorphisms `s, t` of **Definition 7.1.3 (2017: 7.3) (1)** and what the text
draws from them: the sheets `U(φ)` and `φ̂ = t ∘ (s|U(φ))⁻¹` before **Definition 7.1.4 (2017: 7.4)**,
`ml(s φ) = ml(φ) = ml(t φ)` and `d_X(s φ) = d_𝐗(φ) = d_X(t φ)` before **Definition 7.1.5 (2017: 7.5)**, the
tameness of the morphism M-polyfold after **Definition 7.1.6 (2017: 7.6)**; the level-`1` local
sc-diffeomorphisms behind "(1), (2) and (4) trivially" in **Proposition 7.3.9 (2017: 7.11)** (p. 327 (2017 p. 247)); and the
witness `ℝⁿ` for the partitions of unity of **Definition 7.5.5 (2017: 7.16)** and **Corollary 7.6.6 (2017: 7.3)** (pp. 250,
256) *(Part II has no 2014 preprint; numbers and pages are those of the 2017 text)*.

# Local sc-diffeomorphisms

## What the text uses

(Before Definition 7.1.4 (2017: 7.4)) "There exist open neighborhoods `U(φ) ⊂ 𝐗` and `U(x), U(y) ⊂ X` such that
`s : U(φ) → U(x)` and `t : U(φ) → U(y)` are sc-diffeomorphisms", and `φ̂ = t ∘ (s|U(φ))⁻¹`.
(p. 227) `ml(x)` is the largest `m ∈ ℕ ∪ {∞}` with `x ∈ X_m`; (p. 228) "the source and the target
maps are local sc-diffeomorphisms and therefore preserve by definition the levels", so
`ml(x) = ml(y) = ml(φ)` for `φ : x → y`; by Proposition 2.4.4 (2017: 2.7) [2.24] the degeneracy indices are
invariant under local sc-diffeomorphisms, so `d_X(s(φ)) = d_𝐗(φ) = d_X(t(φ))`.  (After
Definition 7.1.6 (2017: 7.6)) In a tame ep-groupoid the morphism M-polyfold is tame, since it "is locally
sc-diffeomorphic by `s` to `X` and the tameness condition is invariant under local
sc-diffeomorphisms".  (Proposition 7.3.9 (2017: 7.11)) `X¹ = (X¹, 𝐗¹)` "satisfies trivially properties (1), (2)
and (4) of Definition 7.3".  (Definition 7.5.5 (2017: 7.16), Corollary 7.6.6 (2017: 7.3)) sc-smooth partitions of unity, and
atlases whose `E₀` are Hilbert spaces.

## What is formalized

* **Sc-diffeomorphisms between open subsets** (Part I's `MPolyfold.IsScDiffeoOn`):
  `IsScDiffeoOn.isOpen_source`, `isOpen_target`, `injOn`, `image_eq`, `isScDiffeoOn_id`,
  `IsScDiffeoOn.restrict` (to a smaller open set), `IsScDiffeoOn.comp`,
  `IsScDiffeoOn.toOpenPartialHomeomorph`.
* **Local sc-diffeomorphisms** (Part I's `MPolyfold.IsLocalScDiffeo`): `isLocalScDiffeo_id`,
  `IsLocalScDiffeo.comp`, `IsLocalScDiffeo.isLocalHomeomorph`, `IsLocalScDiffeo.isOpenMap` (for
  Proposition 7.1.8 (2017: 7.1)), `IsLocalScDiffeo.exists_isScDiffeoOn_subset` (sheets inside any open
  neighbourhood), and `IsLocalScDiffeo.exists_isScDiffeoOn_hat` (a common sheet `U(φ)` of `s` and
  `t`, and `φ̂ = t ∘ (s|U(φ))⁻¹` an sc-diffeomorphism `U(s φ) → U(t φ)` with `φ̂(s φ) = t φ`).
* **Levels**: `IsScDiffeoOn.mem_levelSet_iff`, `IsLocalScDiffeo.mem_levelSet_iff`,
  `IsLocalScDiffeo.preimage_levelSet`, `IsLocalScDiffeo.mem_smoothSet_iff`; `MPolyfold.maxLevel`
  (`ml`, with values in `ℕ∞`), `le_maxLevel_iff`, `maxLevel_eq_top_iff`, `maxLevel_eq_coe_iff`, and
  `IsLocalScDiffeo.maxLevel_eq` (`ml(f x) = ml(x)`).
* **Degeneracy**: `IsLocalScDiffeo.degIndex_eq` (`d_Y(f x) = d_X(x)`),
  `IsLocalScDiffeo.mem_boundary_iff`.
* **The transported tame atlas**: `IsScDiffeoOn.exists_tame_chart` (`ψ ∘ f`, Part I's
  `transportChart`, with the tame retraction of `ψ` restricted), `IsLocalScDiffeo.isTame` (the
  source of a local sc-diffeomorphism into a tame M-polyfold is tame: Definition 7.1.6 (2017: 7.6)'s tame `𝐗`),
  `IsLocalScDiffeo.isTame_iff_of_surjective`.
* **Level `1`**: `IsScSmoothOn.levelOne` (Part I's `IsScSmoothMap.levelOne` on an open set),
  `IsScDiffeoOn.levelOne`, `levelOneMap`, and `IsLocalScDiffeo.levelOne` (a local
  sc-diffeomorphism `X → Y` induces one `X¹ → Y¹`).
* **`ℝⁿ`**: `admitsContDiffPartitionsOfUnity_of_finiteDimensional` (Mathlib's
  `SmoothPartitionOfUnity.exists_isSubordinate`), `rnPolyfold_admitsScPartitionsOfUnity` (by
  Proposition 5.5.11 (preprint 5.38) and Theorem 5.5.10 (preprint 5.37)),
  `godefroyTroyanskiWhitfieldZizlerStatement_of_finiteDimensional` (Theorem 5.5.16 (preprint 5.43) for
  finite-dimensional spaces), `rnPolyfold_one_hilbert_hypothesis` and
  `rnPolyfold_one_admitsScPartitionsOfUnity_of_hilbert` (the hypothesis of
  `MPolyfold.admitsScPartitionsOfUnity_of_hilbert`, Corollary 7.6.6 (2017: 7.3)'s, holds for `ℝ¹`),
  `isLocalScDiffeo_rn_of_contDiff`, `isLocalScDiffeo_rn_neg` (the reflection of the witness
  `ℤ/2 ⋉ ℝ`), `rnPolyfold_maxLevel`.

## Readings

* "Local sc-diffeomorphism" is Part I's `IsLocalScDiffeo`: every point has an open `U` on which `f`
  is an sc-diffeomorphism onto an open set (`IsScDiffeoOn`, with an explicit inverse).  "Preserve
  by definition the levels" is a consequence here, not a definition: sc-smooth maps preserve the
  levels (`IsScSmoothOn.mapsTo_levelSet`), and the local inverse gives the converse.
* `ml(x)` is `⨆ {m | x ∈ X_m}` in `ℕ∞`; since `X₀ = X` and the levels decrease, it is the largest
  such `m` when `x ∉ X_∞` (`maxLevel_eq_coe_iff`) and `⊤` on `X_∞` (`maxLevel_eq_top_iff`).  The
  definition concerns a single M-polyfold, so it is made here and not in `EpGroupoid.lean`.
* "The tameness condition is invariant under local sc-diffeomorphisms" is read with Part I's
  `MPolyfold.IsTame` (an equivalent atlas of tame charts exists, plan II.5 (1)): the tame atlas of
  `𝐗` is the transported one, not "every chart".  Tameness passes from the target to the source;
  the converse needs surjectivity (`isTame_iff_of_surjective`), which `s` has (`s(1_x) = x`).
* The level-`1` lift `g₁` of a local inverse `g` is only determined on `V ∩ Y₁`; elsewhere it takes
  a junk value (as Part I's `levelChart`).  Tameness of `X¹` is not treated here (Part I leaves the
  shift of tameness open); it is proved in `Lift.lean` (`MPolyfold.IsTame.levelOne`).
* The sup norm of `ℝⁿ` is not a Hilbert norm for `n ≥ 2`, so the Hilbert witness is `ℝ¹`; for
  every `n`, `ℝⁿ` admits sc-smooth partitions of unity by Proposition 5.5.11 (preprint 5.38).
-/

open Set Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}

/-! ### Sc-diffeomorphisms between open subsets -/

section ScDiffeoOn

variable {f : X → Y} {g : Y → X} {U : Set X} {V : Set Y}

lemma IsScDiffeoOn.isOpen_source (h : P.IsScDiffeoOn Q f g U V) : IsOpen U :=
  h.isScSmoothOn.isOpen

lemma IsScDiffeoOn.isOpen_target (h : P.IsScDiffeoOn Q f g U V) : IsOpen V :=
  h.isScSmoothOn_inv.isOpen

lemma IsScDiffeoOn.injOn (h : P.IsScDiffeoOn Q f g U V) : InjOn f U := fun a ha b hb hab => by
  rw [← h.left_inv a ha, hab, h.left_inv b hb]

lemma IsScDiffeoOn.image_eq (h : P.IsScDiffeoOn Q f g U V) : f '' U = V := by
  refine Subset.antisymm (image_subset_iff.2 h.mapsTo) fun y hy => ?_
  exact ⟨g y, h.mapsTo_inv hy, h.right_inv y hy⟩

/-- The identity of an open subset is an sc-diffeomorphism. -/
theorem isScDiffeoOn_id (hU : IsOpen U) : P.IsScDiffeoOn P id id U U where
  isScSmoothOn := isScSmoothMap_id.mono hU (subset_univ _)
  isScSmoothOn_inv := isScSmoothMap_id.mono hU (subset_univ _)
  mapsTo := mapsTo_id U
  mapsTo_inv := mapsTo_id U
  left_inv _ _ := rfl
  right_inv _ _ := rfl

/-- **Restriction to a smaller open set**: `f : U' → V ∩ g⁻¹(U')` for open `U' ⊆ U`. -/
theorem IsScDiffeoOn.restrict (h : P.IsScDiffeoOn Q f g U V) {U' : Set X} (hU' : IsOpen U')
    (hsub : U' ⊆ U) : P.IsScDiffeoOn Q f g U' (V ∩ g ⁻¹' U') where
  isScSmoothOn := h.isScSmoothOn.mono hU' hsub
  isScSmoothOn_inv := h.isScSmoothOn_inv.mono
    (h.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage h.isOpen_target hU') inter_subset_left
  mapsTo x hx := ⟨h.mapsTo (hsub hx), by rw [mem_preimage, h.left_inv x (hsub hx)]; exact hx⟩
  mapsTo_inv _ hy := hy.2
  left_inv x hx := h.left_inv x (hsub hx)
  right_inv y hy := h.right_inv y hy.1

/-- **Composition** of sc-diffeomorphisms `U → V → W`. -/
theorem IsScDiffeoOn.comp {f₂ : Y → Z} {g₂ : Z → Y} {W : Set Z} (h₂ : Q.IsScDiffeoOn S f₂ g₂ V W)
    (h₁ : P.IsScDiffeoOn Q f g U V) : P.IsScDiffeoOn S (f₂ ∘ f) (g ∘ g₂) U W where
  isScSmoothOn := IsScSmoothOn.comp h₂.isScSmoothOn h₁.isScSmoothOn h₁.mapsTo
  isScSmoothOn_inv := IsScSmoothOn.comp h₁.isScSmoothOn_inv h₂.isScSmoothOn_inv h₂.mapsTo_inv
  mapsTo := h₂.mapsTo.comp h₁.mapsTo
  mapsTo_inv := h₁.mapsTo_inv.comp h₂.mapsTo_inv
  left_inv x hx := by
    simp only [Function.comp_apply, h₂.left_inv _ (h₁.mapsTo hx), h₁.left_inv x hx]
  right_inv z hz := by
    simp only [Function.comp_apply, h₁.right_inv _ (h₂.mapsTo_inv hz), h₂.right_inv z hz]

/-- An sc-diffeomorphism between open subsets as an open partial homeomorphism. -/
def IsScDiffeoOn.toOpenPartialHomeomorph (h : P.IsScDiffeoOn Q f g U V) :
    OpenPartialHomeomorph X Y where
  toFun := f
  invFun := g
  source := U
  target := V
  map_source' := h.mapsTo
  map_target' := h.mapsTo_inv
  left_inv' := h.left_inv
  right_inv' := h.right_inv
  open_source := h.isOpen_source
  open_target := h.isOpen_target
  continuousOn_toFun := h.isScSmoothOn.continuousOn
  continuousOn_invFun := h.isScSmoothOn_inv.continuousOn

end ScDiffeoOn

/-! ### Local sc-diffeomorphisms -/

section Local

variable {f : X → Y}

/-- The identity is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_id : P.IsLocalScDiffeo P id := fun x =>
  ⟨univ, univ, id, mem_univ x, isScDiffeoOn_id isOpen_univ⟩

/-- A local sc-diffeomorphism is a local homeomorphism. -/
theorem IsLocalScDiffeo.isLocalHomeomorph (hf : P.IsLocalScDiffeo Q f) : IsLocalHomeomorph f :=
  fun x => by
    obtain ⟨U, V, g, hx, hd⟩ := hf x
    exact ⟨hd.toOpenPartialHomeomorph, hx, rfl⟩

/-- A local sc-diffeomorphism is an open map (the property used in Proposition 7.1.8 (2017: 7.1)). -/
theorem IsLocalScDiffeo.isOpenMap (hf : P.IsLocalScDiffeo Q f) : IsOpenMap f :=
  hf.isLocalHomeomorph.isOpenMap

/-- **Small sheets**: every open neighbourhood `W` of `x` contains an open `U ∋ x` on which `f`
is an sc-diffeomorphism onto an open subset. -/
theorem IsLocalScDiffeo.exists_isScDiffeoOn_subset (hf : P.IsLocalScDiffeo Q f) {x : X}
    {W : Set X} (hW : IsOpen W) (hx : x ∈ W) :
    ∃ (U : Set X) (V : Set Y) (g : Y → X), x ∈ U ∧ U ⊆ W ∧ P.IsScDiffeoOn Q f g U V := by
  obtain ⟨U, V, g, hxU, hd⟩ := hf x
  exact ⟨U ∩ W, _, g, ⟨hxU, hx⟩, inter_subset_right,
    hd.restrict (hd.isOpen_source.inter hW) inter_subset_left⟩

/-- The composition of local sc-diffeomorphisms is a local sc-diffeomorphism. -/
theorem IsLocalScDiffeo.comp {f₂ : Y → Z} (hf₂ : Q.IsLocalScDiffeo S f₂)
    (hf : P.IsLocalScDiffeo Q f) : P.IsLocalScDiffeo S (f₂ ∘ f) := fun x => by
  obtain ⟨U₁, V₁, h₁, hx, hd₁⟩ := hf x
  obtain ⟨U₂, V₂, h₂, hfx, hd₂⟩ := hf₂ (f x)
  have hU : IsOpen (U₁ ∩ f ⁻¹' U₂) :=
    hd₁.isScSmoothOn.continuousOn.isOpen_inter_preimage hd₁.isOpen_source hd₂.isOpen_source
  have e₁ := hd₁.restrict hU inter_subset_left
  have hsub : V₁ ∩ h₁ ⁻¹' (U₁ ∩ f ⁻¹' U₂) ⊆ U₂ := fun y hy => by
    have := hy.2.2
    rwa [mem_preimage, hd₁.right_inv y hy.1] at this
  exact ⟨U₁ ∩ f ⁻¹' U₂, _, h₁ ∘ h₂, ⟨hx, hfx⟩, (hd₂.restrict e₁.isOpen_target hsub).comp e₁⟩

/-- **The associated local sc-diffeomorphism `φ̂ = t ∘ (s|U(φ))⁻¹`** (the paragraph before
Definition 7.1.4 (2017: 7.4)): for local sc-diffeomorphisms `s, t : 𝐗 → X` and `φ ∈ 𝐗` there is an open
`U(φ) ∋ φ` on which both `s` and `t` are sc-diffeomorphisms, onto `U(s φ)` and `U(t φ)`, and then
`t ∘ (s|U(φ))⁻¹ : U(s φ) → U(t φ)` is an sc-diffeomorphism sending `s(φ)` to `t(φ)`. -/
theorem IsLocalScDiffeo.exists_isScDiffeoOn_hat {s t : X → Y} (hs : P.IsLocalScDiffeo Q s)
    (ht : P.IsLocalScDiffeo Q t) (φ : X) :
    ∃ (U : Set X) (Vs Vt : Set Y) (gs gt : Y → X), φ ∈ U ∧ P.IsScDiffeoOn Q s gs U Vs ∧
      P.IsScDiffeoOn Q t gt U Vt ∧ Q.IsScDiffeoOn Q (t ∘ gs) (s ∘ gt) Vs Vt ∧
      (t ∘ gs) (s φ) = t φ := by
  obtain ⟨Us, Vs, gs, hφs, hds⟩ := hs φ
  obtain ⟨Ut, Wt, gt, hφt, hdt⟩ := ht φ
  have hU : IsOpen (Us ∩ Ut) := hds.isOpen_source.inter hdt.isOpen_source
  have es := hds.restrict hU inter_subset_left
  have et := hdt.restrict hU inter_subset_right
  refine ⟨Us ∩ Ut, _, _, gs, gt, ⟨hφs, hφt⟩, es, et, et.comp es.symm, ?_⟩
  simp only [Function.comp_apply, hds.left_inv φ hφs]

end Local

/-! ### Levels (the text, pp. 227–228: `ml(s φ) = ml(φ) = ml(t φ)`) -/

section Levels

variable {f : X → Y} {g : Y → X} {U : Set X} {V : Set Y}

/-- An sc-diffeomorphism between open subsets preserves the levels in both directions. -/
theorem IsScDiffeoOn.mem_levelSet_iff (h : P.IsScDiffeoOn Q f g U V) {x : X} (hx : x ∈ U)
    (m : ℕ) : f x ∈ Q.levelSet m ↔ x ∈ P.levelSet m := by
  refine ⟨fun hfx => ?_, fun hxm => h.isScSmoothOn.mapsTo_levelSet m ⟨hx, hxm⟩⟩
  have := h.isScSmoothOn_inv.mapsTo_levelSet m ⟨h.mapsTo hx, hfx⟩
  rwa [h.left_inv x hx] at this

/-- **A local sc-diffeomorphism preserves the levels**: `f(x) ∈ Y_m ⟺ x ∈ X_m`. -/
theorem IsLocalScDiffeo.mem_levelSet_iff (hf : P.IsLocalScDiffeo Q f) (x : X) (m : ℕ) :
    f x ∈ Q.levelSet m ↔ x ∈ P.levelSet m := by
  obtain ⟨U, V, g, hx, hd⟩ := hf x
  exact hd.mem_levelSet_iff hx m

theorem IsLocalScDiffeo.preimage_levelSet (hf : P.IsLocalScDiffeo Q f) (m : ℕ) :
    f ⁻¹' Q.levelSet m = P.levelSet m :=
  ext fun x => hf.mem_levelSet_iff x m

theorem IsLocalScDiffeo.mem_smoothSet_iff (hf : P.IsLocalScDiffeo Q f) (x : X) :
    f x ∈ Q.smoothSet ↔ x ∈ P.smoothSet := by
  simp only [smoothSet, mem_iInter, hf.mem_levelSet_iff]

variable (P) in
/-- **`ml(x)`** (p. 227): the largest `m ∈ ℕ ∪ {∞}` with `x ∈ X_m` (`⊤` for `x ∈ X_∞`). -/
def maxLevel (x : X) : ℕ∞ := ⨆ (m : ℕ) (_ : x ∈ P.levelSet m), (m : ℕ∞)

theorem le_maxLevel_iff {x : X} {m : ℕ} : (m : ℕ∞) ≤ P.maxLevel x ↔ x ∈ P.levelSet m := by
  refine ⟨fun h => ?_, fun h => le_iSup₂ (f := fun (k : ℕ) (_ : x ∈ P.levelSet k) => (k : ℕ∞))
    m h⟩
  by_contra hx
  have hlt : ∀ k : ℕ, x ∈ P.levelSet k → k < m := fun k hk => by
    by_contra hkm
    exact hx (P.levelSet_antitone (not_lt.1 hkm) hk)
  cases m with
  | zero => exact hx (by rw [P.levelSet_zero]; exact mem_univ x)
  | succ m =>
    have hle : P.maxLevel x ≤ m := iSup₂_le fun k hk => by
      exact_mod_cast Nat.lt_succ_iff.1 (hlt k hk)
    have := h.trans hle
    norm_cast at this
    omega

/-- `ml(x) = ∞` if and only if `x ∈ X_∞`. -/
theorem maxLevel_eq_top_iff {x : X} : P.maxLevel x = ⊤ ↔ x ∈ P.smoothSet := by
  rw [ENat.eq_top_iff_forall_ge]
  simp only [le_maxLevel_iff, smoothSet, mem_iInter]

/-- `ml(x) = m` if and only if `x ∈ X_m ∖ X_{m+1}`. -/
theorem maxLevel_eq_coe_iff {x : X} {m : ℕ} :
    P.maxLevel x = m ↔ x ∈ P.levelSet m ∧ x ∉ P.levelSet (m + 1) := by
  constructor
  · intro h
    refine ⟨le_maxLevel_iff.1 h.ge, fun h1 => ?_⟩
    have := (le_maxLevel_iff (P := P)).2 h1
    rw [h] at this
    norm_cast at this
    omega
  · rintro ⟨hm, hm1⟩
    refine le_antisymm (iSup₂_le fun k hk => ?_) (le_maxLevel_iff.2 hm)
    by_contra hkm
    have hmk : m + 1 ≤ k := by
      have : ¬ (k : ℕ∞) ≤ m := hkm
      norm_cast at this
      omega
    exact hm1 (P.levelSet_antitone hmk hk)

/-- **`ml(f x) = ml(x)`** for a local sc-diffeomorphism `f` (the text's `ml(x) = ml(y) = ml(φ)` for
a morphism `φ : x → y`, with `f = s` and `f = t`). -/
theorem IsLocalScDiffeo.maxLevel_eq (hf : P.IsLocalScDiffeo Q f) (x : X) :
    Q.maxLevel (f x) = P.maxLevel x := by
  simp only [maxLevel, hf.mem_levelSet_iff]

end Levels

/-! ### The degeneracy index (the text, p. 228: `d(s φ) = d(φ) = d(t φ)`) -/

section Degeneracy

variable {f : X → Y}

/-- **`d_Y(f(x)) = d_X(x)`** for a local sc-diffeomorphism `f` (Proposition 2.4.4 (2017: 2.7) [2.24]). -/
theorem IsLocalScDiffeo.degIndex_eq (hf : P.IsLocalScDiffeo Q f) (x : X) :
    Q.degIndex (f x) = P.degIndex x := by
  obtain ⟨U, V, g, hx, hd⟩ := hf x
  exact (proposition_2_4_4 hd hx).symm

theorem IsLocalScDiffeo.mem_boundary_iff (hf : P.IsLocalScDiffeo Q f) (x : X) :
    f x ∈ Q.boundary ↔ x ∈ P.boundary := by
  change 1 ≤ Q.degIndex (f x) ↔ 1 ≤ P.degIndex x
  rw [hf.degIndex_eq]

end Degeneracy

/-! ### Tameness transported along local sc-diffeomorphisms (the text after Definition 7.1.6 (2017: 7.6)) -/

section Tame

variable {f : X → Y} {g : Y → X} {U : Set X} {V : Set Y}

/-- **The transported tame chart**: if `Y` is tame and `f : U → V` is an sc-diffeomorphism, every
`x ∈ U` lies in a chart of `X` modelled on a tame retract, namely `ψ ∘ f` for a tame chart `ψ` of
`Y` around `f(x)` (`transportChart`), with the retraction of `ψ` restricted to `ψ(V ∩ dom ψ)`. -/
theorem IsScDiffeoOn.exists_tame_chart (h : P.IsScDiffeoOn Q f g U V) (hQ : Q.IsTame) {x : X}
    (hx : x ∈ U) :
    ∃ φ : MChart X, P.IsChart φ ∧ x ∈ φ.source ∧ IsTameRetract φ.model.E φ.model.C φ.model.O := by
  obtain ⟨ψ, hψ, hy, Rψ, hRψ, hRt⟩ := IsTame.exists_chart Q hQ (f x)
  obtain ⟨W', hW', heq⟩ := ψ.exists_isOpen_image_eq (s := V ∩ ψ.source) inter_subset_right
    (h.isOpen_target.inter ψ.isOpen_source)
  refine ⟨transportChart h ψ, transportChart_isChart h hψ, ⟨hx, hy⟩, Rψ.restrict hW', ?_,
    fun n W T hT => (hRt n W T hT).restrict hW'⟩
  have h1 : (Rψ.restrict hW').retract = ψ '' (V ∩ ψ.source) := by
    rw [Rψ.restrict_retract, hRψ]; exact heq.symm
  exact h1

/-- **Tameness pulls back along local sc-diffeomorphisms** (the text after Definition 7.1.6 (2017: 7.6): in a
tame ep-groupoid the morphism M-polyfold is tame, `s : 𝐗 → X` being a local sc-diffeomorphism):
the atlas of the transported tame charts. -/
theorem IsLocalScDiffeo.isTame (hf : P.IsLocalScDiffeo Q f) (hQ : Q.IsTame) : P.IsTame :=
  isTame_of_forall_exists_chart _ fun x => by
    obtain ⟨U, V, g, hx, hd⟩ := hf x
    exact hd.exists_tame_chart hQ hx

/-- For a surjective local sc-diffeomorphism, `X` is tame if and only if `Y` is. -/
theorem IsLocalScDiffeo.isTame_iff_of_surjective (hf : P.IsLocalScDiffeo Q f)
    (hsurj : Surjective f) : P.IsTame ↔ Q.IsTame := by
  refine ⟨fun hP => isTame_of_forall_exists_chart _ fun y => ?_, hf.isTame⟩
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨U, V, g, hx, hd⟩ := hf x
  exact hd.symm.exists_tame_chart hP (hd.mapsTo hx)

end Tame

/-! ### Level-`1` versions (for `X¹`, Proposition 7.3.9 (2017: 7.11)) -/

section LevelOne

variable {f : X → Y} {g : Y → X} {U : Set X} {V : Set Y}

/-- **Raising the index of a map sc-smooth on an open set**: if `f` is sc-smooth on `U`, any
`f₁ : X¹ → Y¹` with `f₁(x) = f(x)` for `x ∈ U ∩ X₁` is sc-smooth on `U ∩ X₁` (the open set
`{x ∈ X¹ | x ∈ U}`).  The proof of `MPolyfold.IsScSmoothMap.levelOne` with `V = U ∩ dom φ ∩
f⁻¹(dom ψ)`. -/
theorem IsScSmoothOn.levelOne (hf : P.IsScSmoothOn Q f U) {f₁ : P.Level 1 → Q.Level 1}
    (hf₁ : ∀ x, P.levelVal 1 x ∈ U → Q.levelVal 1 (f₁ x) = f (P.levelVal 1 x)) :
    P.shift.IsScSmoothOn Q.shift f₁ {x | P.levelVal 1 x ∈ U} := by
  have local_ : ∀ {φ : MChart X} {ψ : MChart Y} (hφ : P.IsChart φ) (hψ : Q.IsChart ψ)
      (x₀ : P.Level 1) (z₀ : Q.Level 1),
      IsOpen {x : P.Level 1 | P.levelVal 1 x ∈ U ∩ φ.source ∩ f ⁻¹' ψ.source} ∧
      ContinuousOn f₁ {x : P.Level 1 | P.levelVal 1 x ∈ U ∩ φ.source ∩ f ⁻¹' ψ.source} ∧
      IsScSmoothRetractMap (levelChart hφ x₀).model.E (levelChart hφ x₀).model.C
        (levelChart hφ x₀ '' {x : P.Level 1 | P.levelVal 1 x ∈ U ∩ φ.source ∩ f ⁻¹' ψ.source})
        (levelChart hψ z₀).model.E (levelChart hψ z₀).model.C (levelChart hψ z₀).model.O
        (levelChart hψ z₀ ∘ f₁ ∘ (levelChart hφ x₀).symm) := by
    intro φ ψ hφ hψ x₀ z₀
    set V' := U ∩ φ.source ∩ f ⁻¹' ψ.source with hV'def
    have hV' : IsOpen V' := (hf.continuousOn.mono inter_subset_left).isOpen_inter_preimage
      (hf.isOpen.inter φ.isOpen_source) ψ.isOpen_source
    have hVφ : V' ⊆ φ.source := fun x hx => hx.1.2
    have hsm := hf.smooth φ ψ hφ hψ V' hV' (fun x hx => hx.1) fun x hx => hx.2
    have hO := φ.isScRetract_image hVφ hV'
    have hrep : ∀ x : P.Level 1, P.levelVal 1 x ∈ V' →
        levelChart hψ z₀ (f₁ x) = levelMap (ψ ∘ f ∘ φ.symm) 1 (levelChart hφ x₀ x) := by
      intro x hx
      symm
      apply levelMap_eq_of_toBase_eq
      have hfx' : Q.levelVal 1 (f₁ x) ∈ ψ.source := by rw [hf₁ x hx.1.1]; exact hx.2
      rw [levelChart_apply, levelChart_apply, Q.toBase_levelLift hψ hfx' (levelVal_mem _),
        P.toBase_levelLift hφ hx.1.2 (levelVal_mem _), hf₁ x hx.1.1]
      simp only [Function.comp_apply, φ.symm_apply_apply hx.1.2]
    have hmaps : MapsTo (levelChart hφ x₀) {x : P.Level 1 | P.levelVal 1 x ∈ V'}
        (φ.model.E.lvlSet (φ '' V') 1) := fun x hx => by
      rw [← levelChart_image_preimage hφ x₀ hVφ]; exact ⟨x, hx, rfl⟩
    refine ⟨(continuous_levelVal 1).isOpen_preimage _ hV', ?_, ?_⟩
    · have h1 : ContinuousOn (fun x => (levelChart hψ z₀).symm
          (levelMap (ψ ∘ f ∘ φ.symm) 1 (levelChart hφ x₀ x)))
          {x : P.Level 1 | P.levelVal 1 x ∈ V'} :=
        (levelChart hψ z₀).continuousOn_invFun.comp
          ((hsm.continuousOn_levelMap hO 1).comp
            ((levelChart hφ x₀).continuousOn_toFun.mono fun x hx => hx.1.2) hmaps)
          fun x hx => hsm.mapsTo_levelMap hO 1 (hmaps hx)
      refine h1.congr fun x hx => ?_
      have hfx : f₁ x ∈ (levelChart hψ z₀).source := by
        change Q.levelVal 1 (f₁ x) ∈ ψ.source
        rw [hf₁ x hx.1.1]; exact hx.2
      simp only
      rw [← hrep x hx, (levelChart hψ z₀).symm_apply_apply hfx]
    · rw [levelChart_image_preimage hφ x₀ hVφ]
      refine (hsm.shift hO).congr fun z hz => ?_
      have hzO : φ.model.E.toBase 1 z ∈ φ.model.O := φ.image_subset_model hVφ hz
      have hx : P.levelVal 1 ((levelChart hφ x₀).symm z) ∈ V' := by
        rw [levelChart_symm_apply hφ x₀ hzO]
        obtain ⟨v, hv, hvz⟩ := hz
        rw [← hvz, φ.symm_apply_apply (hVφ hv)]
        exact hv
      have e := hrep _ hx
      rw [(levelChart hφ x₀).apply_symm_apply (z := z) hzO] at e
      exact e.symm
  refine IsScSmoothOn.of_exists_charts ((continuous_levelVal 1).isOpen_preimage _ hf.isOpen)
    (fun x hx => ?_) fun x hx => ?_
  · obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source (P.levelVal 1 x)
    obtain ⟨ψ, hψ, hfx⟩ := Q.exists_isChart_mem_source (f (P.levelVal 1 x))
    obtain ⟨hV1, hcont, -⟩ := local_ hφ hψ x (f₁ x)
    exact (hcont.continuousAt (hV1.mem_nhds ⟨⟨hx, hxφ⟩, hfx⟩)).continuousWithinAt
  · obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source (P.levelVal 1 x)
    obtain ⟨ψ, hψ, hfx⟩ := Q.exists_isChart_mem_source (f (P.levelVal 1 x))
    obtain ⟨hV1, -, hsm⟩ := local_ hφ hψ x (f₁ x)
    refine ⟨levelChart hφ x, levelChart hψ (f₁ x), _, P.shift_isChart hφ x,
      Q.shift_isChart hψ (f₁ x), hV1, ⟨⟨hx, hxφ⟩, hfx⟩, fun x' hx' => ⟨hx'.1.1, hx'.1.2⟩,
      fun x' hx' => ?_, hsm⟩
    change Q.levelVal 1 (f₁ x') ∈ ψ.source
    rw [hf₁ x' hx'.1.1]; exact hx'.2

/-- **The level-`1` version of `IsScDiffeoOn`**: an sc-diffeomorphism `f : U → V` with inverse `g`
induces an sc-diffeomorphism `f₁ : U ∩ X₁ → V ∩ Y₁` of the M-polyfolds `X¹`, `Y¹`, for any lifts
`f₁`, `g₁` of `f`, `g` on these sets. -/
theorem IsScDiffeoOn.levelOne (h : P.IsScDiffeoOn Q f g U V) {f₁ : P.Level 1 → Q.Level 1}
    {g₁ : Q.Level 1 → P.Level 1}
    (hf₁ : ∀ x, P.levelVal 1 x ∈ U → Q.levelVal 1 (f₁ x) = f (P.levelVal 1 x))
    (hg₁ : ∀ y, Q.levelVal 1 y ∈ V → P.levelVal 1 (g₁ y) = g (Q.levelVal 1 y)) :
    P.shift.IsScDiffeoOn Q.shift f₁ g₁ {x | P.levelVal 1 x ∈ U} {y | Q.levelVal 1 y ∈ V} where
  isScSmoothOn := h.isScSmoothOn.levelOne hf₁
  isScSmoothOn_inv := h.isScSmoothOn_inv.levelOne hg₁
  mapsTo x hx := by
    change Q.levelVal 1 (f₁ x) ∈ V
    rw [hf₁ x hx]; exact h.mapsTo hx
  mapsTo_inv y hy := by
    change P.levelVal 1 (g₁ y) ∈ U
    rw [hg₁ y hy]; exact h.mapsTo_inv hy
  left_inv x hx := by
    have hfx : Q.levelVal 1 (f₁ x) ∈ V := by rw [hf₁ x hx]; exact h.mapsTo hx
    refine level_ext ?_
    rw [hg₁ _ hfx, hf₁ x hx, h.left_inv _ hx]
  right_inv y hy := by
    have hgy : P.levelVal 1 (g₁ y) ∈ U := by rw [hg₁ y hy]; exact h.mapsTo_inv hy
    refine level_ext ?_
    rw [hf₁ _ hgy, hg₁ y hy, h.right_inv _ hy]

variable (P Q) in
/-- The map `X¹ → Y¹` induced by `f : X → Y` with `f(X₁) ⊆ Y₁`. -/
def levelOneMap (f : X → Y) (hf : MapsTo f (P.levelSet 1) (Q.levelSet 1)) :
    P.Level 1 → Q.Level 1 :=
  fun x => Q.levelMk 1 (f (P.levelVal 1 x)) (hf (levelVal_mem x))

@[simp] lemma levelVal_levelOneMap (hf : MapsTo f (P.levelSet 1) (Q.levelSet 1))
    (x : P.Level 1) : Q.levelVal 1 (levelOneMap P Q f hf x) = f (P.levelVal 1 x) := rfl

/-- **The level-`1` version of `IsLocalScDiffeo`**: a local sc-diffeomorphism `f : X → Y` induces a
local sc-diffeomorphism `X¹ → Y¹`. -/
theorem IsLocalScDiffeo.levelOne (hf : P.IsLocalScDiffeo Q f) :
    P.shift.IsLocalScDiffeo Q.shift
      (levelOneMap P Q f (hf.isScSmoothMap.mapsTo_levelSet 1)) := fun x => by
  classical
  obtain ⟨U, V, g, hx, hd⟩ := hf (P.levelVal 1 x)
  let g₁ : Q.Level 1 → P.Level 1 := fun y =>
    if hy : g (Q.levelVal 1 y) ∈ P.levelSet 1 then P.levelMk 1 _ hy else x
  refine ⟨{x' | P.levelVal 1 x' ∈ U}, {y | Q.levelVal 1 y ∈ V}, g₁, hx,
    hd.levelOne (fun _ _ => rfl) fun y hy => ?_⟩
  have hg1 : g (Q.levelVal 1 y) ∈ P.levelSet 1 :=
    hd.isScSmoothOn_inv.mapsTo_levelSet 1 ⟨hy, levelVal_mem y⟩
  simp only [g₁, dif_pos hg1, levelVal_levelMk]

end LevelOne

end MPolyfold

/-! ### `ℝⁿ`: sc-smooth partitions of unity and local sc-diffeomorphisms -/

section Rn

/-- **A finite-dimensional normed space admits `C^∞` partitions of unity**
(`SmoothPartitionOfUnity.exists_isSubordinate`, for the model `𝓘(ℝ, V)`). -/
theorem admitsContDiffPartitionsOfUnity_of_finiteDimensional (V : Type*) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] : AdmitsContDiffPartitionsOfUnity V ⊤ := by
  intro ι U hUo hUcov
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, V) isClosed_univ U hUo
    (by rw [hUcov])
  exact ⟨ρ.toPartitionOfUnity, hρ.toPartitionOfUnity,
    fun i => contMDiff_iff_contDiff.1 (ρ i).contMDiff⟩

/-- **Theorem 5.5.16 (preprint 5.43) holds for finite-dimensional spaces** (its conclusion does), so the explicit
hypothesis of Corollary 5.5.17 (preprint 5.44) [Corollary 7.6.6 (2017: 7.3)'s source] is satisfiable. -/
theorem godefroyTroyanskiWhitfieldZizlerStatement_of_finiteDimensional (V : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    GodefroyTroyanskiWhitfieldZizlerStatement V ⊤ :=
  fun _ _ => admitsContDiffPartitionsOfUnity_of_finiteDimensional V

/-- **`ℝⁿ` admits sc-smooth partitions of unity** (Theorem 5.5.10 (preprint 5.37) with the chart `id`, whose model
has the approximation property by Proposition 5.5.11 (preprint 5.38)). -/
theorem rnPolyfold_admitsScPartitionsOfUnity (n : ℕ) :
    (rnPolyfold n).AdmitsScPartitionsOfUnity := by
  refine theorem_5_5_10.2 ⟨{rnChart n 0}, fun φ hφ => ?_, fun x => ⟨rnChart n 0, mem_singleton _,
    mem_univ x⟩, fun φ hφ => ?_⟩
  · rw [mem_singleton_iff.1 hφ]; exact isChart_rnChart 0
  · rw [mem_singleton_iff.1 hφ]
    exact proposition_5_5_11 _ (admitsContDiffPartitionsOfUnity_of_finiteDimensional (Fin n → ℝ))

/-- The norm of `ℝ¹` comes from the bilinear form `b(v, w) = v₀ w₀`. -/
theorem rn_one_norm_sq_eq (v : Fin 1 → ℝ) : ‖v‖ ^ 2 = v 0 * v 0 := by
  have h : ‖v‖ = ‖v 0‖ := le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by
    rw [Subsingleton.elim i 0]) (norm_le_pi_norm v 0)
  rw [h, Real.norm_eq_abs, sq_abs, sq]

/-- **The hypothesis of `MPolyfold.admitsScPartitionsOfUnity_of_hilbert` (Corollary 7.6.6 (2017: 7.3)'s) is
satisfiable**: it holds for `ℝ¹` (a Hilbert space, finite-dimensional). -/
theorem rnPolyfold_one_hilbert_hypothesis (x : Fin 1 → ℝ) :
    ∃ φ : MChart (Fin 1 → ℝ), (rnPolyfold 1).IsChart φ ∧ x ∈ φ.source ∧
      (∃ b : φ.model.E 0 →L[ℝ] φ.model.E 0 →L[ℝ] ℝ, ∀ v, ‖v‖ ^ 2 = b v v) ∧
      GodefroyTroyanskiWhitfieldZizlerStatement (φ.model.E 0) ⊤ := by
  refine ⟨rnChart 1 0, isChart_rnChart 0, mem_univ x, ?_,
    godefroyTroyanskiWhitfieldZizlerStatement_of_finiteDimensional (Fin 1 → ℝ)⟩
  refine ⟨(ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.proj 0)
    (ContinuousLinearMap.proj 0), fun v => ?_⟩
  exact rn_one_norm_sq_eq v

/-- `ℝ¹` admits sc-smooth partitions of unity also by the Hilbert route (Corollary 5.5.17 (preprint 5.44)). -/
theorem rnPolyfold_one_admitsScPartitionsOfUnity_of_hilbert :
    (rnPolyfold 1).AdmitsScPartitionsOfUnity :=
  MPolyfold.admitsScPartitionsOfUnity_of_hilbert rnPolyfold_one_hilbert_hypothesis

/-- A `C^∞` self-map of `ℝⁿ` with a `C^∞` inverse is a local sc-diffeomorphism of `ℝⁿ` (one sheet,
`ℝⁿ` itself). -/
theorem isLocalScDiffeo_rn_of_contDiff {n : ℕ} {σ τ : (Fin n → ℝ) → Fin n → ℝ}
    (hσ : ContDiff ℝ ∞ σ) (hτ : ContDiff ℝ ∞ τ) (hστ : ∀ r, σ (τ r) = r)
    (hτσ : ∀ r, τ (σ r) = r) : (rnPolyfold n).IsLocalScDiffeo (rnPolyfold n) σ := fun r =>
  ⟨univ, univ, τ, mem_univ r, isScSmoothMap_rn_of_contDiff hσ, isScSmoothMap_rn_of_contDiff hτ,
    mapsTo_univ _ _, mapsTo_univ _ _, fun r _ => hτσ r, fun r _ => hστ r⟩

/-- **The reflection `r ↦ −r` of `ℝⁿ` is a local sc-diffeomorphism** (the `ℤ/2`-action of the
witness `ℤ/2 ⋉ ℝ`). -/
theorem isLocalScDiffeo_rn_neg (n : ℕ) :
    (rnPolyfold n).IsLocalScDiffeo (rnPolyfold n) fun r => -r :=
  isLocalScDiffeo_rn_of_contDiff contDiff_neg contDiff_neg neg_neg neg_neg

/-- Every point of `ℝⁿ` has `ml = ∞`. -/
theorem rnPolyfold_maxLevel (n : ℕ) (r : Fin n → ℝ) : (rnPolyfold n).maxLevel r = ⊤ := by
  refine MPolyfold.maxLevel_eq_top_iff.2 (mem_iInter.2 fun m => ?_)
  rw [rnPolyfold_levelSet]
  exact mem_univ r

end Rn

end Polyfold
