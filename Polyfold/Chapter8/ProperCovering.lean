import Polyfold.Chapter8.Basic

set_option maxSynthPendingDepth 3

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II,
Chapter 8: **Proposition 8.2** (composition of proper covering functors, pp. 276–277), the
degeneracy remark after **Definition 8.8** (pp. 275–276), **Remark 8.2 (a)** (p. 277), and
Appendix 8.5.1, "Local Structure of Proper Coverings": **Lemmas 8.9–8.11** (pp. 286–287) and
**Proposition 8.4** (p. 288).  There is no 2014 preprint of Part II; numbers and pages are the
2017 text's.  `EpFunctor.IsProperCovering` (Definition 8.8) is in `Polyfold/Chapter8/Basic.lean`.

# Proper covering functors: fibres, counting, composition

## The text, paraphrased

(Definition 8.8, p. 275) `F : Y → X` is a proper covering functor if (1) `F` is a surjective local
sc-diffeomorphism on objects, (2) the fibres `F⁻¹(x)` are finite and evenly covered, (3)
`L_F : 𝐘 → 𝐗 ₛ×_F Y`, `φ ↦ (F(φ), s(φ))`, is an sc-diffeomorphism.  (pp. 275–276) `L_F` preserves
the degeneracy index, `d_𝐘(φ) = d_{𝐗 ₛ×_F Y}(F(φ), s(φ))`; with `d_{𝐗 × Y}(φ, y) = d_𝐗(φ) + d_Y(y)`
and `F`, `s` local sc-diffeomorphisms, `d_{𝐗 × Y}(F(φ), s(φ)) = 2 · d_𝐘(φ)`, so
`d_{𝐗 ₛ×_F Y} = ½ · d_{𝐗 × Y}` along `L_F`.  (Proposition 8.2, pp. 276–277) If `F : Y → X` and
`H : Z → Y` are proper covering functors, so is `F ∘ H`: (1), (2) "follow easily"; for (3),
`L_{F∘H} = K̃ ∘ L_H` with `K̃ : Y ₛ×_H Z → X ₛ×_{F∘H} Z`, `(ψ, z) ↦ (F(ψ), z)`, whose inverse is
`L̃(φ, z) = (L_F⁻¹(φ, H(z)), z)`.  (Remark 8.2 (a), p. 277) For `φ : y → y'` with
`y, y' ∈ F⁻¹(x)`, `F(φ) ∈ G_x`.

(Appendix 8.5.1, pp. 286–288) Fix `x ∈ X`; `mor(F⁻¹(x))` are the morphisms between points of
`F⁻¹(x)`.  By Definition 8.8 (3), `mor(F⁻¹(x)) → G_x × F⁻¹(x)`, `φ ↦ (F(φ), s(φ))`, is a
bijection, so `#mor(F⁻¹(x)) = #G_x · #F⁻¹(x)`.  `F⁻¹(x) = Θ₁ ∪ … ∪ Θ_q` is the decomposition into
isomorphism classes (`y ∼ y'` if there is an isomorphism in `mor(F⁻¹(x))` between them); points of
one class have isomorphic isotropy groups.  (Lemma 8.9) `#G_x · #Θ_j = #{ψ ∈ mor(F⁻¹(x)) | s(ψ),
t(ψ) ∈ Θ_j} = #G_{y₀} · (#Θ_j)²` for `y₀ ∈ Θ_j`, hence `#G_x = #G_{y₀} · #Θ_j`; the proof
restricts the bijection to (8.17) and, fixing `ψ_y : y₀ → y`, uses the bijections
`mor(y₀, y₀) → mor(y, y')`, `ψ ↦ ψ_{y'} ∘ ψ ∘ ψ_y⁻¹`.  (Lemma 8.10) For isomorphic `x, x'` there is
a one-to-one correspondence `Θ_j ↔ Θ'_j` of the classes of `F⁻¹(x)` and `F⁻¹(x')`: if
`y ∈ F⁻¹(x)` and `y' ∈ F⁻¹(x')` are connected by an isomorphism, there is a unique `j` with
`y ∈ Θ_j`, `y' ∈ Θ'_j`.  (Lemma 8.11) `#Θ_j = #G_x / #G_{y₀} = #G_{x'} / #G_{y₀'} = #Θ'_j`, and
`#F⁻¹(x) = ∑ #Θ_j = ∑ #Θ'_j = #F⁻¹(x')`.  (Proposition 8.4) For every connected component `c` of
`|X|` there is `k_c` with `#F⁻¹(x) = k_c` whenever `π(x) ∈ c`; "in other words", viewing
`ℕ = {1, 2, …}` as an ep-groupoid with only identities, `x ↦ #F⁻¹(x)` is an sc-smooth functor.

## What is formalized (namespace `Polyfold.EpFunctor`)

* Fibres: `isotropyOfMorOn` (**Remark 8.2 (a)**: `F(φ) ∈ G_x`);
  `IsProperCovering.bijective_fibredMap`, `existsUnique_lift` (unique `ψ` with `F(ψ) = φ`,
  `s(ψ) = y`), `srcFiberEquiv`, `morOnFiberEquiv` (`mor(F⁻¹(x)) ≃ G_x × F⁻¹(x)`),
  `ncard_morOn_fiber` (`#mor(F⁻¹(x)) = #G_x · #F⁻¹(x)`), `finite_morOn_fiber`.
* Isomorphism classes: `fiberIndex x = π(F⁻¹(x)) ⊆ |Y|` (the index set `{1, …, q}`),
  `fiberClass x c = F⁻¹(x) ∩ π⁻¹(c)` (`Θ_c`), `fiberClasses x` (`{Θ₁, …, Θ_q}`);
  `iUnion_fiberClass`, `pairwiseDisjoint_fiberClass`, `injOn_fiberClass`,
  `nonempty_fiberClass_iff`, `mem_fiberClass_iff`, `π_eq_π_iff_exists_morOn`,
  `nat_card_isotropy_eq_of_mem_fiberClass`, `IsProperCovering.finite_fiberIndex`,
  `finite_fiberClass`, `finite_fiberClasses`, `morOn_fiberClass_eq`.
* **Lemma 8.9**: `IsProperCovering.lemma_8_9` (the three equalities), with `morOnClassEquiv`
  ((8.17)) and `nonempty_morOnClass_equiv_isotropy` (`mor(Θ) ≅ (Θ × Θ) × G_{y₀}`).
* **Lemma 8.10**: `IsProperCovering.lemma_8_10` (same index set, unique `j`) and
  `lemma_8_10_equiv` (a bijection `{Θ_j} ≃ {Θ'_j}` matching isomorphic points);
  `exists_isomorphic_of_isomorphic`, `fiberIndex_eq`.
* **Lemma 8.11**: `IsProperCovering.lemma_8_11`, `ncard_fiber_eq_sum` (`#F⁻¹(x) = ∑ #Θ_j`),
  `ncard_fiber_eq_of_isomorphic`.
* **Proposition 8.4**: `IsProperCovering.proposition_8_4` (constant on connected components of
  `|X|`), from `eventually_ncard_fiber_eq`, `isLocallyConstant_ncard_fiber`, `fiberCardOrbit`,
  `isLocallyConstant_fiberCardOrbit`; the functor `fiberCardFunctor :
  EpFunctor X (EpGroupoid.trivial (discretePolyfold ℕ))`, `fiberCardFunctor_obj`;
  `one_le_ncard_fiber`.
* **Proposition 8.2**: `IsProperCovering.proposition_8_2`, from `evenlyCovered_comp` and
  `isScDiffeo_fibredMap_comp`.
* The degeneracy remark after Definition 8.8: `degIndex_fibredMap`
  (`d_𝐘(φ) = d_{𝐗 ₛ×_F Y}(L_F φ)`), `degIndex_mor` (`d_𝐗(F φ) = d_𝐘(φ)`),
  `degIndex_prod_fibredMap_le` (`d_{𝐗 × Y}(F φ, s φ) ≤ 2 d_𝐘(φ)`), `degIndex_prod_fibredMap`
  (for tame `X`, `Y`: `= 2 d_𝐘(φ)` and `2 d_{𝐗 ₛ×_F Y} = d_{𝐗 × Y}`).

## What the text leaves implicit, and the choices made

* `mor(F⁻¹(x))` is `Y.morOn (F⁻¹(x))`; `#` is `Set.ncard` / `Nat.card`, the true cardinality: the
  fibres are finite (Definition 8.8 (2)), the isotropy groups are (Proposition 7.4, an instance),
  hence so is `mor(F⁻¹(x))` (`finite_morOn_fiber`).
* **The classes are indexed by their images in `|Y|`**: `Θ_c = F⁻¹(x) ∩ π⁻¹(c)` for
  `c ∈ π(F⁻¹(x))`.  Then the text's correspondence `Θ_j ↔ Θ'_j` of Lemma 8.10 is "the same index":
  for isomorphic `x, x'` the index sets agree (`fiberIndex_eq`, from the lifting of `x → x'` to
  morphisms out of `F⁻¹(x)`, Definition 8.8 (3)).  `lemma_8_10_equiv` restates it as a bijection
  between the sets of classes.  The statements about `Θ_c` hold for every `c` (for
  `c ∉ π(F⁻¹(x))`, `Θ_c = ∅`).
* Lemma 8.9's set `{ψ ∈ mor(F⁻¹(x)) | s(ψ), t(ψ) ∈ Θ_j}` is `mor(Θ_j)` (`morOn_fiberClass_eq`).
  Restricting the bijection to (8.17) uses that `t(ψ) ∈ Θ_j` is automatic for `s(ψ) ∈ Θ_j`,
  `t(ψ) ∈ F⁻¹(x)`.  The third claim divides by `#Θ_j ≥ 1`; Lemma 8.11's division by
  `#G_{y₀} ≥ 1` is done the same way.
* Proposition 8.4: only the local constancy of `x ↦ #F⁻¹(x)` is used (from Definition 8.8 (2):
  `y ↦ (F|U(y))⁻¹(x')` is a bijection `F⁻¹(x) → F⁻¹(x')` for `x' ∈ U(x)`), not the finer
  "structure of isomorphism classes stays the same"; it descends to `|X|` by Lemma 8.11, is locally
  constant there in the quotient topology, hence constant on connected components.  The text's
  `ℕ = {1, 2, …}` is Lean's `ℕ` (the values are `≥ 1`, `one_le_ncard_fiber`), with the discrete
  M-polyfold structure of Chapter 7 (`discretePolyfold`); a morphism `φ` is sent to the identity of
  `#F⁻¹(s φ)`, which equals `#F⁻¹(t φ)` by Lemma 8.11.
* Proposition 8.2 (2), "follows easily": `U(x)` of `F` is shrunk to `U₀` with
  `(F|U(y))⁻¹(U₀) ⊆ U'(y)` for the evenly covered neighbourhoods `U'(y)` of `H`, `y ∈ F⁻¹(x)`
  (a finite intersection), and `z ∈ H⁻¹(y)` gets `U'(z) ∩ H⁻¹(U(y) ∩ F⁻¹(U₀))`.  (3): the
  sc-smoothness of `K̃`, `L̃`, maps between sub-M-polyfolds of products, comes from "a map into a
  sub-M-polyfold is sc-smooth as soon as it is sc-smooth into the ambient M-polyfold"
  (Proposition 2.21 (2); re-proved privately here as in `Chapter7/SubGroupoid.lean`) and the
  sc-smoothness of the inclusions (Proposition 2.21 (1)).
* The degeneracy remark: the product formula `d_{𝐗 × Y}(φ, y) = d_𝐗(φ) + d_Y(y)` that the text
  uses is available in Part I's formalization for tame factors (`MPolyfold.isTame_prod`), and in
  general only as `≤` (`MPolyfold.degIndex_prod_le`); the equalities are stated for tame `X` and
  `Y` (then `𝐗` is tame, `s` being a local sc-diffeomorphism), the inequality in general.
* **Possible misprints** (as we read the text):
  - p. 287, after Lemma 8.10: "Using the third claim of Lemma 8.10, we infer that
    `#Θ_j = #G_x / #G_{y₀}`": Lemma 8.10 has no third claim; the third claim of Lemma 8.9
    (`#G_x = #G_{y₀} · #Θ_j`) is meant.
  - p. 287, Lemma 8.11: `#F⁻¹(x) = ∑_{i=1}^q #Θ_j = ∑_{i=1}^q #Θ'_j`: the summation index is `i`,
    the summand's `j`.
  - p. 286, (8.17): "`ψ → (Fψ), s(ψ))`", an unbalanced parenthesis for `ψ ↦ (F(ψ), s(ψ))`.
-/

open Set Function Topology

noncomputable section

namespace Polyfold

universe u v w

/-! ### Conjugation in a groupoid -/

namespace GroupoidStr

variable {Obj Mor : Type u} {G : GroupoidStr Obj Mor}

/-- `γ' ∘ (γ'⁻¹ ∘ ψ ∘ γ) ∘ γ⁻¹ = ψ` for `ψ : t(γ) → t(γ')`. -/
private theorem conj_inv_conj {γ γ' ψ : Mor} (h₁ : G.src ψ = G.tgt γ) (h₂ : G.tgt ψ = G.tgt γ') :
    G.comp (G.comp γ' (G.comp (G.comp (G.inv γ') ψ) γ)) (G.inv γ) = ψ := by
  have e₁ : G.src (G.inv γ') = G.tgt ψ := by rw [G.src_inv, h₂]
  have e₂ : G.src (G.comp (G.inv γ') ψ) = G.tgt γ := by rw [G.src_comp _ _ e₁, h₁]
  have e₃ : G.src γ' = G.tgt (G.comp (G.inv γ') ψ) := by rw [G.tgt_comp _ _ e₁, G.tgt_inv]
  have e₄ : G.src (G.comp γ' (G.comp (G.inv γ') ψ)) = G.tgt γ := by
    rw [G.src_comp _ _ e₃, e₂]
  rw [← G.comp_assoc _ _ _ e₃ e₂, comp_inv_cancel_right e₄]
  have := inv_comp_cancel_left (G := G) (φ := G.inv γ') (ψ := ψ) e₁
  rwa [inv_inv] at this

/-- `γ'⁻¹ ∘ (γ' ∘ g ∘ γ⁻¹) ∘ γ = g` for `g : s(γ) → s(γ')`. -/
private theorem inv_conj_conj {γ γ' g : Mor} (h₁ : G.src g = G.src γ) (h₂ : G.tgt g = G.src γ') :
    G.comp (G.comp (G.inv γ') (G.comp (G.comp γ' g) (G.inv γ))) γ = g := by
  have h := conj_inv_conj (G := G) (γ := G.inv γ) (γ' := G.inv γ') (ψ := g)
    (by rw [G.tgt_inv, h₁]) (by rw [G.tgt_inv, h₂])
  rwa [inv_inv, inv_inv] at h

/-- `γ'⁻¹ ∘ ψ ∘ γ : s(γ) → s(γ')` for `ψ : t(γ) → t(γ')`. -/
private theorem src_tgt_conj {γ γ' ψ : Mor} (h₁ : G.src ψ = G.tgt γ) (h₂ : G.tgt ψ = G.tgt γ') :
    G.src (G.comp (G.comp (G.inv γ') ψ) γ) = G.src γ ∧
      G.tgt (G.comp (G.comp (G.inv γ') ψ) γ) = G.src γ' := by
  have e₁ : G.src (G.inv γ') = G.tgt ψ := by rw [G.src_inv, h₂]
  have e₂ : G.src (G.comp (G.inv γ') ψ) = G.tgt γ := by rw [G.src_comp _ _ e₁, h₁]
  exact ⟨G.src_comp _ _ e₂, by rw [G.tgt_comp _ _ e₂, G.tgt_comp _ _ e₁, G.tgt_inv]⟩

/-- `γ' ∘ g ∘ γ⁻¹ : t(γ) → t(γ')` for `g : s(γ) → s(γ')`. -/
private theorem src_tgt_unconj {γ γ' g : Mor} (h₁ : G.src g = G.src γ) (h₂ : G.tgt g = G.src γ') :
    G.src (G.comp (G.comp γ' g) (G.inv γ)) = G.tgt γ ∧
      G.tgt (G.comp (G.comp γ' g) (G.inv γ)) = G.tgt γ' := by
  have h := src_tgt_conj (G := G) (γ := G.inv γ) (γ' := G.inv γ') (ψ := g)
    (by rw [G.tgt_inv, h₁]) (by rw [G.tgt_inv, h₂])
  rwa [inv_inv, G.src_inv, G.src_inv] at h

end GroupoidStr

section Helpers

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- An sc-diffeomorphism `U → V` restricted to an open `W ⊆ V` of the target:
`U ∩ f⁻¹(W) → W`. -/
private theorem isScDiffeoOn_restrictTarget {f : X → Y} {g : Y → X} {U : Set X} {V W : Set Y}
    (h : P.IsScDiffeoOn Q f g U V) (hW : IsOpen W) (hWV : W ⊆ V) :
    P.IsScDiffeoOn Q f g (U ∩ f ⁻¹' W) W :=
  (h.symm.restrict hW hWV).symm

/-- **A map into a sub-M-polyfold** `A ⊆ Y` is sc-smooth into `A` as soon as it is sc-smooth into
`Y` (as `SubGroupoid.lean`'s private lemma of the same name): near `x`, `f = (i⁻¹ ∘ r) ∘ i ∘ f`
for a retraction `r` onto `A` near `f(x)` (Proposition 2.21 (2)). -/
private theorem isScSmoothOn_subPolyfold_of_val {A : Set Y} (hA : Q.IsSubMPolyfold A)
    [ParacompactSpace A] {f : X → A} {U : Set X}
    (hf : P.IsScSmoothOn Q (fun x => (f x : Y)) U) :
    P.IsScSmoothOn (MPolyfold.subPolyfold hA) f U := by
  refine MPolyfold.IsScSmoothOn.of_locally hf.isOpen fun x hx => ?_
  set d := hA.data (f x).2
  have hU' : IsOpen (U ∩ (fun x => (f x : Y)) ⁻¹' d.V) :=
    hf.continuousOn.isOpen_inter_preimage hf.isOpen d.isOpen
  refine ⟨_, hU', ⟨hx, hA.mem_data_V (f x).2⟩, inter_subset_left, ?_⟩
  refine (MPolyfold.IsScSmoothOn.comp (MPolyfold.subPolyfold_retraction_isScSmooth hA d (f x))
    (hf.mono hU' inter_subset_left) fun y hy => hy.2).congr fun y hy => Subtype.ext ?_
  simp only [Function.comp_apply]
  rw [d.retractInto_val (f x) hy.2]
  exact d.apply_eq_self ⟨(f y).2, hy.2⟩

end Helpers

section Fibres

variable {ObjY MorY : Type u} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type v} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}

namespace EpFunctor

/-! #### The bijection of Definition 8.8 (3) on the fibres -/

variable (F : EpFunctor Y X)

/-- **Remark 8.2 (a)**, as used on p. 286: `F(φ) ∈ G_x` for a morphism `φ` of `Y` between points
of `F⁻¹(x)`. -/
def isotropyOfMorOn {x : ObjX} (φ : Y.morOn (F.obj ⁻¹' {x})) : X.Isotropy x :=
  ⟨F.mor φ.1, (F.src_mor _).trans (show F.obj (Y.src φ.1) = x from φ.2.1),
    (F.tgt_mor _).trans (show F.obj (Y.tgt φ.1) = x from φ.2.2)⟩

/-- The isomorphism class `Θ_c = F⁻¹(x) ∩ π⁻¹(c)` of `F⁻¹(x)`, indexed by its image
`c ∈ |Y|`. -/
def fiberClass (x : ObjX) (c : Y.OrbitSpace) : Set ObjY := F.obj ⁻¹' {x} ∩ Y.π ⁻¹' {c}

/-- The index set `{1, …, q}` of the isomorphism classes of `F⁻¹(x)`: their images
`π(F⁻¹(x)) ⊆ |Y|`. -/
def fiberIndex (x : ObjX) : Set Y.OrbitSpace := Y.π '' (F.obj ⁻¹' {x})

/-- The set `{Θ₁, …, Θ_q}` of the isomorphism classes of `F⁻¹(x)`. -/
def fiberClasses (x : ObjX) : Set (Set ObjY) := F.fiberClass x '' F.fiberIndex x

variable {F}

theorem fiberClass_subset (x : ObjX) (c : Y.OrbitSpace) : F.fiberClass x c ⊆ F.obj ⁻¹' {x} :=
  inter_subset_left

/-- Two points of a class `Θ` are isomorphic, and a point of `F⁻¹(x)` isomorphic to a point of `Θ`
lies in `Θ`. -/
theorem mem_fiberClass_iff {x : ObjX} {c : Y.OrbitSpace} {y₀ y : ObjY}
    (h₀ : y₀ ∈ F.fiberClass x c) : y ∈ F.fiberClass x c ↔ F.obj y = x ∧ Y.Isomorphic y₀ y :=
  ⟨fun h => ⟨h.1, Y.π_eq_π_iff.1 ((show Y.π y₀ = c from h₀.2).trans h.2.symm)⟩,
    fun h => ⟨h.1, (Y.π_eq_π_iff.2 h.2).symm.trans h₀.2⟩⟩

/-- "Two objects are isomorphic if there exists an isomorphism in `mor(F⁻¹(x))` between them": for
`y, y' ∈ F⁻¹(x)` this is the isomorphism of `Y` (`π(y) = π(y')`). -/
theorem π_eq_π_iff_exists_morOn {x : ObjX} {y y' : ObjY} (hy : F.obj y = x)
    (hy' : F.obj y' = x) :
    Y.π y = Y.π y' ↔ ∃ ψ ∈ Y.morOn (F.obj ⁻¹' {x}), Y.src ψ = y ∧ Y.tgt ψ = y' := by
  rw [Y.π_eq_π_iff]
  constructor
  · rintro ⟨ψ, hs, ht⟩
    exact ⟨ψ, ⟨show F.obj (Y.src ψ) = x by rw [hs, hy],
      show F.obj (Y.tgt ψ) = x by rw [ht, hy']⟩, hs, ht⟩
  · rintro ⟨ψ, -, hs, ht⟩
    exact ⟨ψ, hs, ht⟩

theorem mem_fiberClass_self {x : ObjX} {y : ObjY} (hy : F.obj y = x) :
    y ∈ F.fiberClass x (Y.π y) :=
  ⟨hy, rfl⟩

/-- **The decomposition** `F⁻¹(x) = Θ₁ ∪ … ∪ Θ_q`. -/
theorem iUnion_fiberClass (x : ObjX) :
    ⋃ c ∈ F.fiberIndex x, F.fiberClass x c = F.obj ⁻¹' {x} := by
  refine Subset.antisymm (iUnion₂_subset fun c _ => fiberClass_subset x c) fun y hy => ?_
  exact mem_iUnion₂.2 ⟨Y.π y, ⟨y, hy, rfl⟩, mem_fiberClass_self hy⟩

/-- The classes are mutually disjoint. -/
theorem pairwiseDisjoint_fiberClass (x : ObjX) :
    (univ : Set Y.OrbitSpace).PairwiseDisjoint (F.fiberClass x) := by
  intro c _ c' _ hcc'
  refine disjoint_left.2 fun y hy hy' => hcc' ?_
  exact (show Y.π y = c from hy.2).symm.trans hy'.2

theorem nonempty_fiberClass_iff {x : ObjX} {c : Y.OrbitSpace} :
    (F.fiberClass x c).Nonempty ↔ c ∈ F.fiberIndex x :=
  ⟨fun ⟨y, hy⟩ => ⟨y, hy.1, hy.2⟩, fun ⟨y, hy, hyc⟩ => ⟨y, hy, hyc⟩⟩

/-- The classes are indexed one-to-one by `fiberIndex`. -/
theorem injOn_fiberClass (x : ObjX) : InjOn (F.fiberClass x) (F.fiberIndex x) := by
  intro c hc c' _ he
  obtain ⟨y, hy⟩ := nonempty_fiberClass_iff.2 hc
  have hy' : y ∈ F.fiberClass x c' := he ▸ hy
  exact (show Y.π y = c from hy.2).symm.trans hy'.2

/-- Lemma 8.9's set `{ψ ∈ mor(F⁻¹(x)) | s(ψ), t(ψ) ∈ Θ}` is `mor(Θ)`. -/
theorem morOn_fiberClass_eq (x : ObjX) (c : Y.OrbitSpace) :
    {ψ | ψ ∈ Y.morOn (F.obj ⁻¹' {x}) ∧ Y.src ψ ∈ F.fiberClass x c ∧
      Y.tgt ψ ∈ F.fiberClass x c} = Y.morOn (F.fiberClass x c) :=
  Set.ext fun _ => ⟨fun h => h.2, fun h => ⟨⟨h.1.1, h.2.1⟩, h⟩⟩

/-- "Clearly, for any two elements `y, y' ∈ Θ_j`, the isotropy groups `G_y` and `G_{y'}` are
isomorphic." -/
theorem nat_card_isotropy_eq_of_mem_fiberClass {x : ObjX} {c : Y.OrbitSpace} {y y' : ObjY}
    (hy : y ∈ F.fiberClass x c) (hy' : y' ∈ F.fiberClass x c) :
    Nat.card (Y.Isotropy y) = Nat.card (Y.Isotropy y') :=
  Y.nat_card_isotropy_eq ((mem_fiberClass_iff hy).1 hy').2

/-- `mor(Θ) ≅ (Θ × Θ) × G_{y₀}`, `ψ ↦ ((s ψ, t ψ), γ_{t ψ}⁻¹ ∘ ψ ∘ γ_{s ψ})`, for a
choice of morphisms `γ_y : y₀ → y` (the proof of Lemma 8.9, p. 287). -/
theorem nonempty_morOnClass_equiv_isotropy {x : ObjX} {c : Y.OrbitSpace} {y₀ : ObjY}
    (h₀ : y₀ ∈ F.fiberClass x c) :
    Nonempty (Y.morOn (F.fiberClass x c) ≃
      (F.fiberClass x c × F.fiberClass x c) × Y.Isotropy y₀) := by
  have hγ : ∀ y : F.fiberClass x c, ∃ γ, Y.src γ = y₀ ∧ Y.tgt γ = y.1 := fun y =>
    ((mem_fiberClass_iff h₀).1 y.2).2
  choose γ hγs hγt using hγ
  have hc : ∀ ψ : Y.morOn (F.fiberClass x c), Y.src (Y.comp (Y.comp (Y.inv
      (γ ⟨Y.tgt ψ.1, ψ.2.2⟩)) ψ.1) (γ ⟨Y.src ψ.1, ψ.2.1⟩)) = y₀ ∧ Y.tgt (Y.comp (Y.comp (Y.inv
      (γ ⟨Y.tgt ψ.1, ψ.2.2⟩)) ψ.1) (γ ⟨Y.src ψ.1, ψ.2.1⟩)) = y₀ := fun ψ => by
    have h := GroupoidStr.src_tgt_conj (G := Y.toGroupoidStr) (γ := γ ⟨Y.src ψ.1, ψ.2.1⟩)
      (γ' := γ ⟨Y.tgt ψ.1, ψ.2.2⟩) (ψ := ψ.1) (hγt ⟨Y.src ψ.1, ψ.2.1⟩).symm
      (hγt ⟨Y.tgt ψ.1, ψ.2.2⟩).symm
    rwa [hγs, hγs] at h
  have hu : ∀ q : (F.fiberClass x c × F.fiberClass x c) × Y.Isotropy y₀,
      Y.src (Y.comp (Y.comp (γ q.1.2) q.2.val) (Y.inv (γ q.1.1))) = q.1.1 ∧
      Y.tgt (Y.comp (Y.comp (γ q.1.2) q.2.val) (Y.inv (γ q.1.1))) = q.1.2 := fun q => by
    have h := GroupoidStr.src_tgt_unconj (G := Y.toGroupoidStr) (γ := γ q.1.1) (γ' := γ q.1.2)
      (g := q.2.val) (q.2.src_val.trans (hγs _).symm) (q.2.tgt_val.trans (hγs _).symm)
    rwa [hγt, hγt] at h
  refine ⟨⟨fun ψ => ((⟨Y.src ψ.1, ψ.2.1⟩, ⟨Y.tgt ψ.1, ψ.2.2⟩), ⟨_, (hc ψ).1, (hc ψ).2⟩),
    fun q => ⟨_, (hu q).1 ▸ q.1.1.2, (hu q).2 ▸ q.1.2.2⟩, fun ψ => Subtype.ext ?_,
    fun q => ?_⟩⟩
  · exact GroupoidStr.conj_inv_conj (hγt ⟨Y.src ψ.1, ψ.2.1⟩).symm (hγt ⟨Y.tgt ψ.1, ψ.2.2⟩).symm
  · have e₁ : (⟨_, (hu q).1 ▸ q.1.1.2⟩ : F.fiberClass x c) = q.1.1 := Subtype.ext (hu q).1
    have e₂ : (⟨_, (hu q).2 ▸ q.1.2.2⟩ : F.fiberClass x c) = q.1.2 := Subtype.ext (hu q).2
    refine Prod.ext (Prod.ext e₁ e₂) (GroupoidStr.Isotropy.ext ?_)
    simp only
    rw [e₁, e₂]
    exact GroupoidStr.inv_conj_conj (q.2.src_val.trans (hγs _).symm)
      (q.2.tgt_val.trans (hγs _).symm)

namespace IsProperCovering

variable (hF : F.IsProperCovering)
include hF

/-- Definition 8.8 (3) makes `L_F : φ ↦ (F(φ), s(φ))` a bijection `𝐘 → 𝐗 ₛ×_F Y`. -/
theorem bijective_fibredMap : Bijective F.fibredMap := by
  let _ := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
  let _ := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
  obtain ⟨g, hg⟩ := hF.isScDiffeo_fibredMap
  refine ⟨fun a b hab => ?_, fun p => ⟨g p, hg.right_inv p (mem_univ _)⟩⟩
  rw [← hg.left_inv a (mem_univ _), hab, hg.left_inv b (mem_univ _)]

/-- **Unique lifting**: for `φ ∈ 𝐗` and `y ∈ Y` with `s(φ) = F(y)` there is a unique `ψ ∈ 𝐘` with
`F(ψ) = φ` and `s(ψ) = y`. -/
theorem existsUnique_lift {φ : MorX} {y : ObjY} (h : X.src φ = F.obj y) :
    ∃! ψ : MorY, F.mor ψ = φ ∧ Y.src ψ = y := by
  obtain ⟨ψ, hψ⟩ := hF.bijective_fibredMap.2 ⟨(φ, y), h⟩
  refine ⟨ψ, ⟨congrArg (fun p => p.1.1) hψ, congrArg (fun p => p.1.2) hψ⟩, fun ψ' hψ' => ?_⟩
  exact hF.bijective_fibredMap.1 ((Subtype.ext (Prod.ext hψ'.1 hψ'.2)).trans hψ.symm)

/-- **The bijection `φ ↦ (F(φ), s(φ))`** (p. 286, from Definition 8.8 (3)) from the morphisms `ψ`
with `s(ψ) ∈ S` and `t(ψ) ∈ F⁻¹(x)` onto `G_x × S`, for `S ⊆ F⁻¹(x)`. -/
def srcFiberEquiv (x : ObjX) (S : Set ObjY) (hS : S ⊆ F.obj ⁻¹' {x}) :
    {ψ : MorY // Y.src ψ ∈ S ∧ F.obj (Y.tgt ψ) = x} ≃ X.Isotropy x × S :=
  Equiv.ofBijective
    (fun ψ => (⟨F.mor ψ.1, (F.src_mor _).trans (show F.obj (Y.src ψ.1) = x from hS ψ.2.1),
      (F.tgt_mor _).trans ψ.2.2⟩, ⟨Y.src ψ.1, ψ.2.1⟩))
    ⟨fun ψ₁ ψ₂ h => Subtype.ext (hF.bijective_fibredMap.1 (Subtype.ext (Prod.ext
      (congrArg (fun p => p.1.val) h) (congrArg (fun p => (p.2 : ObjY)) h)))),
    fun p => by
      obtain ⟨ψ, ⟨hψm, hψs⟩, -⟩ := hF.existsUnique_lift (φ := p.1.val) (y := p.2.1)
        (p.1.src_val.trans (show F.obj p.2.1 = x from hS p.2.2).symm)
      refine ⟨⟨ψ, hψs ▸ p.2.2, ?_⟩, Prod.ext (GroupoidStr.Isotropy.ext hψm) (Subtype.ext hψs)⟩
      rw [← F.tgt_mor, hψm, p.1.tgt_val]⟩

@[simp]
theorem srcFiberEquiv_apply_fst (x : ObjX) (S : Set ObjY) (hS : S ⊆ F.obj ⁻¹' {x})
    (ψ : {ψ : MorY // Y.src ψ ∈ S ∧ F.obj (Y.tgt ψ) = x}) :
    (hF.srcFiberEquiv x S hS ψ).1.val = F.mor ψ.1 := rfl

@[simp]
theorem srcFiberEquiv_apply_snd (x : ObjX) (S : Set ObjY) (hS : S ⊆ F.obj ⁻¹' {x})
    (ψ : {ψ : MorY // Y.src ψ ∈ S ∧ F.obj (Y.tgt ψ) = x}) :
    ((hF.srcFiberEquiv x S hS ψ).2 : ObjY) = Y.src ψ.1 := rfl

/-- **The bijection** `mor(F⁻¹(x)) → G_x × F⁻¹(x)`, `φ ↦ (F(φ), s(φ))` (p. 286). -/
def morOnFiberEquiv (x : ObjX) : Y.morOn (F.obj ⁻¹' {x}) ≃ X.Isotropy x × (F.obj ⁻¹' {x}) :=
  hF.srcFiberEquiv x _ subset_rfl

theorem morOnFiberEquiv_apply (x : ObjX) (φ : Y.morOn (F.obj ⁻¹' {x})) :
    hF.morOnFiberEquiv x φ = (F.isotropyOfMorOn φ, ⟨Y.src φ.1, φ.2.1⟩) := rfl

/-- `#mor(F⁻¹(x)) = #G_x · #F⁻¹(x)` (p. 286). -/
theorem ncard_morOn_fiber (x : ObjX) :
    (Y.morOn (F.obj ⁻¹' {x})).ncard = Nat.card (X.Isotropy x) * (F.obj ⁻¹' {x}).ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_prod]
  exact Nat.card_congr (hF.morOnFiberEquiv x)

/-- `mor(F⁻¹(x))` is finite. -/
theorem finite_morOn_fiber (x : ObjX) : (Y.morOn (F.obj ⁻¹' {x})).Finite := by
  have := (hF.finite_fiber x).to_subtype
  exact Set.finite_coe_iff.1 (Finite.of_equiv _ (hF.morOnFiberEquiv x).symm)

theorem finite_fiberIndex (x : ObjX) : (F.fiberIndex x).Finite :=
  (hF.finite_fiber x).image _

theorem finite_fiberClass (x : ObjX) (c : Y.OrbitSpace) : (F.fiberClass x c).Finite :=
  (hF.finite_fiber x).subset (fiberClass_subset x c)

theorem finite_fiberClasses (x : ObjX) : (F.fiberClasses x).Finite :=
  (hF.finite_fiberIndex x).image _

/-- (8.17): the bijection `{ψ ∈ mor(F⁻¹(x)) | s(ψ), t(ψ) ∈ Θ} → G_x × Θ`, `ψ ↦ (F(ψ), s(ψ))`. -/
def morOnClassEquiv (x : ObjX) (c : Y.OrbitSpace) :
    Y.morOn (F.fiberClass x c) ≃ X.Isotropy x × F.fiberClass x c :=
  (Equiv.subtypeEquivRight fun ψ => ⟨fun h => ⟨h.1, h.2.1⟩, fun h =>
    ⟨h.1, h.2, (Y.π_src_eq_π_tgt ψ).symm.trans h.1.2⟩⟩).trans
    (hF.srcFiberEquiv x _ (fiberClass_subset x c))

/-! #### Lemma 8.9 -/

/-- **Lemma 8.9** (p. 286): for every isomorphism class `Θ = Θ_c` of `F⁻¹(x)`,
`#G_x · #Θ = #{ψ ∈ mor(F⁻¹(x)) | s(ψ), t(ψ) ∈ Θ}`, and for every `y₀ ∈ Θ`,
`#{ψ ∈ mor(F⁻¹(x)) | s(ψ), t(ψ) ∈ Θ} = #G_{y₀} · (#Θ)²` and `#G_x = #G_{y₀} · #Θ`.  The set
`{ψ ∈ mor(F⁻¹(x)) | s(ψ), t(ψ) ∈ Θ}` is `mor(Θ)` (`Y.morOn Θ`), as `Θ ⊆ F⁻¹(x)`. -/
theorem lemma_8_9 (x : ObjX) (c : Y.OrbitSpace) :
    Nat.card (X.Isotropy x) * (F.fiberClass x c).ncard = (Y.morOn (F.fiberClass x c)).ncard ∧
    ∀ y₀ ∈ F.fiberClass x c,
      (Y.morOn (F.fiberClass x c)).ncard =
          Nat.card (Y.Isotropy y₀) * (F.fiberClass x c).ncard ^ 2 ∧
        Nat.card (X.Isotropy x) = Nat.card (Y.Isotropy y₀) * (F.fiberClass x c).ncard := by
  have h1 : Nat.card (X.Isotropy x) * (F.fiberClass x c).ncard =
      (Y.morOn (F.fiberClass x c)).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_prod]
    exact (Nat.card_congr (hF.morOnClassEquiv x c)).symm
  refine ⟨h1, fun y₀ h₀ => ?_⟩
  obtain ⟨e⟩ := nonempty_morOnClass_equiv_isotropy h₀
  have h2 : (Y.morOn (F.fiberClass x c)).ncard =
      Nat.card (Y.Isotropy y₀) * (F.fiberClass x c).ncard ^ 2 := by
    rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_prod, Nat.card_prod,
      Nat.card_coe_set_eq]
    ring
  refine ⟨h2, ?_⟩
  have hpos : 0 < (F.fiberClass x c).ncard := (Set.ncard_pos (hF.finite_fiberClass x c)).2 ⟨y₀, h₀⟩
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h1, h2]
  ring

/-! #### Lemma 8.10 -/

/-- For isomorphic `x, x'`, every `y ∈ F⁻¹(x)` is isomorphic to some `y' ∈ F⁻¹(x')`: lift
`φ : x → x'` to `ψ` with `F(ψ) = φ`, `s(ψ) = y` (Definition 8.8 (3)) and take `y' = t(ψ)`. -/
theorem exists_isomorphic_of_isomorphic {x x' : ObjX} (h : X.Isomorphic x x') {y : ObjY}
    (hy : F.obj y = x) : ∃ y', F.obj y' = x' ∧ Y.Isomorphic y y' := by
  obtain ⟨φ, hφs, hφt⟩ := h
  obtain ⟨ψ, ⟨hψm, hψs⟩, -⟩ := hF.existsUnique_lift (φ := φ) (y := y) (hφs.trans hy.symm)
  exact ⟨Y.tgt ψ, by rw [← F.tgt_mor, hψm, hφt], ψ, hψs, rfl⟩

/-- For isomorphic `x, x'` the isomorphism classes of `F⁻¹(x)` and `F⁻¹(x')` have the same index
set `π(F⁻¹(x)) = π(F⁻¹(x')) ⊆ |Y|`. -/
theorem fiberIndex_eq {x x' : ObjX} (h : X.Isomorphic x x') : F.fiberIndex x = F.fiberIndex x' := by
  have key : ∀ {x x' : ObjX}, X.Isomorphic x x' → F.fiberIndex x ⊆ F.fiberIndex x' := by
    rintro x x' h _ ⟨y, hy, rfl⟩
    obtain ⟨y', hy', hyy'⟩ := hF.exists_isomorphic_of_isomorphic h hy
    exact ⟨y', hy', (Y.π_eq_π_iff.2 hyy').symm⟩
  exact Subset.antisymm (key h) (key h.symm)

/-- **Lemma 8.10** (p. 287): for isomorphic `x, x'` the isomorphism classes `Θ_c` of `F⁻¹(x)` and
`Θ'_c` of `F⁻¹(x')` are indexed by the same set (`Θ_c ↔ Θ'_c` is the one-to-one correspondence),
and if `y ∈ F⁻¹(x)` and `y' ∈ F⁻¹(x')` are connected by an isomorphism, there is a unique index
`c` with `y ∈ Θ_c` and `y' ∈ Θ'_c`. -/
theorem lemma_8_10 {x x' : ObjX} (h : X.Isomorphic x x') :
    F.fiberIndex x = F.fiberIndex x' ∧
    ∀ y ∈ F.obj ⁻¹' {x}, ∀ y' ∈ F.obj ⁻¹' {x'}, Y.Isomorphic y y' →
      ∃! c, c ∈ F.fiberIndex x ∧ y ∈ F.fiberClass x c ∧ y' ∈ F.fiberClass x' c := by
  refine ⟨hF.fiberIndex_eq h, fun y hy y' hy' hyy' => ⟨Y.π y, ⟨⟨y, hy, rfl⟩,
    mem_fiberClass_self hy, hy', (Y.π_eq_π_iff.2 hyy').symm⟩, fun c hc => ?_⟩⟩
  exact (show Y.π y = c from hc.2.1.2).symm

/-- **Lemma 8.10**, the correspondence between the sets of classes: a bijection
`{Θ_j} ≅ {Θ'_j}` such that the points of corresponding classes are isomorphic. -/
theorem lemma_8_10_equiv {x x' : ObjX} (h : X.Isomorphic x x') :
    ∃ e : F.fiberClasses x ≃ F.fiberClasses x',
      ∀ Θ : F.fiberClasses x, ∀ y ∈ Θ.1, ∀ y' ∈ (e Θ).1, Y.Isomorphic y y' := by
  let b := fun x : ObjX => ((injOn_fiberClass (F := F) x).bijOn_image).equiv (F.fiberClass x)
  refine ⟨(b x).symm.trans ((Equiv.setCongr (hF.fiberIndex_eq h)).trans (b x')),
    fun Θ y hy y' hy' => ?_⟩
  set c := (b x).symm Θ with hc
  have hΘ : (Θ : Set ObjY) = F.fiberClass x c := by
    have := congrArg Subtype.val ((b x).apply_symm_apply Θ)
    exact this.symm
  rw [hΘ] at hy
  have hy'' : y' ∈ F.fiberClass x' c := hy'
  exact Y.π_eq_π_iff.1 ((show Y.π y = c from hy.2).trans hy''.2.symm)

/-! #### Lemma 8.11 -/

/-- `#F⁻¹(x) = ∑_j #Θ_j`. -/
theorem ncard_fiber_eq_sum (x : ObjX) :
    (F.obj ⁻¹' {x}).ncard = ∑ c ∈ (hF.finite_fiberIndex x).toFinset, (F.fiberClass x c).ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card _ (hF.finite_fiber x),
    Finset.card_eq_sum_card_fiberwise (f := Y.π) (t := (hF.finite_fiberIndex x).toFinset)
      fun y hy => by
        rw [Set.Finite.coe_toFinset] at hy ⊢
        exact ⟨y, hy, rfl⟩]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Set.ncard_coe_finset, Finset.coe_filter]
  congr 1
  ext y
  simp only [Set.Finite.mem_toFinset, mem_ofPred_eq, fiberClass, mem_inter_iff, mem_preimage,
    mem_singleton_iff]

/-- **Lemma 8.11** (p. 287): for isomorphic `x, x'`, `#Θ_j = #Θ'_j` for the corresponding classes
of Lemma 8.10, and `#F⁻¹(x) = ∑_j #Θ_j = ∑_j #Θ'_j = #F⁻¹(x')`.  As in the text,
`#Θ_j = #G_x / #G_{y₀} = #G_{x'} / #G_{y₀'} = #Θ'_j` (Lemma 8.9). -/
theorem lemma_8_11 {x x' : ObjX} (h : X.Isomorphic x x') :
    (∀ c, (F.fiberClass x c).ncard = (F.fiberClass x' c).ncard) ∧
      (F.obj ⁻¹' {x}).ncard = (F.obj ⁻¹' {x'}).ncard := by
  have hcl : ∀ c, (F.fiberClass x c).ncard = (F.fiberClass x' c).ncard := by
    intro c
    by_cases hc : c ∈ F.fiberIndex x
    · obtain ⟨y₀, h₀⟩ := nonempty_fiberClass_iff.2 hc
      obtain ⟨y₀', h₀'⟩ := nonempty_fiberClass_iff.2 (hF.fiberIndex_eq h ▸ hc)
      have e₁ := ((hF.lemma_8_9 x c).2 y₀ h₀).2
      have e₂ := ((hF.lemma_8_9 x' c).2 y₀' h₀').2
      have e₃ : Nat.card (Y.Isotropy y₀) = Nat.card (Y.Isotropy y₀') :=
        Y.nat_card_isotropy_eq (Y.π_eq_π_iff.1 ((show Y.π y₀ = c from h₀.2).trans h₀'.2.symm))
      rw [X.nat_card_isotropy_eq h, e₂, e₃] at e₁
      exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos e₁).symm
    · have h₁ : F.fiberClass x c = ∅ :=
        not_nonempty_iff_eq_empty.1 fun hne => hc (nonempty_fiberClass_iff.1 hne)
      have h₂ : F.fiberClass x' c = ∅ :=
        not_nonempty_iff_eq_empty.1 fun hne => hc (hF.fiberIndex_eq h ▸
          nonempty_fiberClass_iff.1 hne)
      rw [h₁, h₂]
  refine ⟨hcl, ?_⟩
  rw [hF.ncard_fiber_eq_sum x, hF.ncard_fiber_eq_sum x']
  refine Finset.sum_congr ?_ fun c _ => hcl c
  ext c
  simp only [Set.Finite.mem_toFinset, hF.fiberIndex_eq h]

/-- `#F⁻¹(x) = #F⁻¹(x')` for isomorphic `x, x'` (Lemma 8.11). -/
theorem ncard_fiber_eq_of_isomorphic {x x' : ObjX} (h : X.Isomorphic x x') :
    (F.obj ⁻¹' {x}).ncard = (F.obj ⁻¹' {x'}).ncard :=
  (hF.lemma_8_11 h).2

/-! #### Proposition 8.4 -/

/-- The text's `ℕ = {1, 2, …}`: `#F⁻¹(x) ≥ 1` (`F` is surjective, Definition 8.8 (1)). -/
theorem one_le_ncard_fiber (x : ObjX) : 1 ≤ (F.obj ⁻¹' {x}).ncard :=
  (Set.ncard_pos (hF.finite_fiber x)).2 (hF.surjective x)

/-- Definition 8.8 (2): `#F⁻¹(x') = #F⁻¹(x)` for `x'` near `x`: `y ↦ (F|U(y))⁻¹(x')` is a
bijection `F⁻¹(x) → F⁻¹(x')` for `x' ∈ U(x)`. -/
theorem eventually_ncard_fiber_eq (x : ObjX) :
    ∀ᶠ x' in 𝓝 x, (F.obj ⁻¹' {x'}).ncard = (F.obj ⁻¹' {x}).ncard := by
  obtain ⟨U, V, σ, hUo, hxU, hdisj, hV, hcov⟩ := hF.evenlyCovered x
  filter_upwards [hUo.mem_nhds hxU] with x' hx'
  refine (Set.ncard_congr (fun y _ => σ y x') (fun y hy => (hV y hy).2.right_inv x' hx')
    (fun y₁ y₂ hy₁ hy₂ he => ?_) fun y' hy' => ?_).symm
  · by_contra hne
    have h1 : σ y₁ x' ∈ V y₁ := (hV y₁ hy₁).2.mapsTo_inv hx'
    have h2 : σ y₂ x' ∈ V y₂ := (hV y₂ hy₂).2.mapsTo_inv hx'
    rw [he] at h1
    exact disjoint_left.1 (hdisj hy₁ hy₂ hne : Disjoint (V y₁) (V y₂)) h1 h2
  · have hy'x : F.obj y' = x' := hy'
    have hU : y' ∈ F.obj ⁻¹' U := by
      change F.obj y' ∈ U
      rw [hy'x]
      exact hx'
    rw [hcov] at hU
    obtain ⟨y, hy, hy'V⟩ := mem_iUnion₂.1 hU
    refine ⟨y, hy, ?_⟩
    have := (hV y hy).2.left_inv y' hy'V
    rwa [hy'x] at this

/-- `x ↦ #F⁻¹(x)` is locally constant on `X` (Definition 8.8 (2)). -/
theorem isLocallyConstant_ncard_fiber : IsLocallyConstant fun x => (F.obj ⁻¹' {x}).ncard :=
  (IsLocallyConstant.iff_eventually_eq _).2 hF.eventually_ncard_fiber_eq

/-- `#F⁻¹(x)` as a function of `π(x) ∈ |X|` (well defined by Lemma 8.11). -/
def fiberCardOrbit : X.OrbitSpace → ℕ :=
  Quotient.lift (fun x => (F.obj ⁻¹' {x}).ncard) fun _ _ h => hF.ncard_fiber_eq_of_isomorphic h

theorem fiberCardOrbit_π (x : ObjX) : hF.fiberCardOrbit (X.π x) = (F.obj ⁻¹' {x}).ncard := rfl

/-- `|x| ↦ #F⁻¹(x)` is locally constant on `|X|` (quotient topology). -/
theorem isLocallyConstant_fiberCardOrbit : IsLocallyConstant hF.fiberCardOrbit :=
  fun s => isOpen_coinduced.2 (hF.isLocallyConstant_ncard_fiber s)

/-- **Proposition 8.4** (p. 288): for every connected component `c` of the orbit space `|X|`
there is a constant `k_c` such that `#F⁻¹(x) = k_c` whenever `z ∈ c` and `π(x) = z`. -/
theorem proposition_8_4 (c : Set X.OrbitSpace) (hc : c ∈ range connectedComponent) :
    ∃ k : ℕ, ∀ z ∈ c, ∀ x : ObjX, X.π x = z → (F.obj ⁻¹' {x}).ncard = k := by
  obtain ⟨z₀, rfl⟩ := hc
  refine ⟨hF.fiberCardOrbit z₀, fun z hz x hx => ?_⟩
  rw [← hF.fiberCardOrbit_π, hx]
  exact hF.isLocallyConstant_fiberCardOrbit.apply_eq_of_isPreconnected
    isPreconnected_connectedComponent hz mem_connectedComponent

/-- **Proposition 8.4**, "in other words": viewing `ℕ` as an ep-groupoid with the identities as
the morphisms (Chapter 7's `EpGroupoid.trivial` of the discrete M-polyfold `ℕ`), `x ↦ #F⁻¹(x)` is
an sc-smooth functor `X → ℕ`; a morphism `φ` goes to the identity of `#F⁻¹(s φ) = #F⁻¹(t φ)`. -/
def fiberCardFunctor : EpFunctor X (EpGroupoid.trivial (discretePolyfold ℕ)) where
  obj x := (F.obj ⁻¹' {x}).ncard
  mor φ := (F.obj ⁻¹' {X.src φ}).ncard
  src_mor _ := rfl
  tgt_mor φ := hF.ncard_fiber_eq_of_isomorphic ⟨φ, rfl, rfl⟩
  mor_comp φ ψ h := by
    change (F.obj ⁻¹' {X.src (X.comp φ ψ)}).ncard = (F.obj ⁻¹' {X.src φ}).ncard
    rw [X.src_comp _ _ h, h]
    exact hF.ncard_fiber_eq_of_isomorphic ⟨ψ, rfl, rfl⟩
  mor_unit x := by
    change (F.obj ⁻¹' {X.src (X.unit x)}).ncard = (F.obj ⁻¹' {x}).ncard
    rw [X.src_unit]
  isScSmoothMap_obj :=
    isScSmoothMap_discrete_of_continuous hF.isLocallyConstant_ncard_fiber.continuous
  isScSmoothMap_mor := isScSmoothMap_discrete_of_continuous
    (hF.isLocallyConstant_ncard_fiber.continuous.comp X.continuous_src)

@[simp]
theorem fiberCardFunctor_obj (x : ObjX) :
    hF.fiberCardFunctor.obj x = (F.obj ⁻¹' {x}).ncard := rfl

/-! #### The degeneracy remark after Definition 8.8 -/

/-- **The degeneracy remark after Definition 8.8** (pp. 275–276), first statement: `L_F` preserves
the degeneracy index, `d_𝐘(φ) = d_{𝐗 ₛ×_F Y}(F(φ), s(φ))` (Proposition 2.24). -/
theorem degIndex_fibredMap (φ : MorY) :
    letI := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
    letI := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
    Y.PMor.degIndex φ = (MPolyfold.subPolyfold (MPolyfold.isSubMPolyfold_fibredProduct
      X.isLocalScDiffeo_src F.isScSmoothMap_obj)).degIndex (F.fibredMap φ) := by
  let _ := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
  let _ := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
  obtain ⟨g, hg⟩ := hF.isScDiffeo_fibredMap
  exact proposition_2_24 hg (mem_univ φ)

/-- `d_𝐗(F(φ)) = d_𝐘(φ)` ("since `F` and `s` are local sc-diffeomorphisms", p. 276):
`d_𝐗(F φ) = d_X(s F φ) = d_X(F s φ) = d_Y(s φ) = d_𝐘(φ)`. -/
theorem degIndex_mor (φ : MorY) : X.PMor.degIndex (F.mor φ) = Y.PMor.degIndex φ := by
  rw [X.degIndex_src, F.src_mor, hF.isLocalScDiffeo.degIndex_eq, ← Y.degIndex_src]

/-- The remark after Definition 8.8, second statement, in general: `d_{𝐗 × Y}(F(φ), s(φ)) ≤
2 · d_𝐘(φ)` (Part I's `degIndex_prod_le`). -/
theorem degIndex_prod_fibredMap_le (φ : MorY) :
    letI := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
    (X.PMor.prod Y.PObj).degIndex (F.mor φ, Y.src φ) ≤ 2 * Y.PMor.degIndex φ := by
  let _ := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
  refine (MPolyfold.degIndex_prod_le X.PMor Y.PObj _ _).trans_eq ?_
  rw [hF.degIndex_mor, ← Y.degIndex_src]
  ring

/-- **The degeneracy remark after Definition 8.8**, for tame `X` and `Y`, where Part I's product
formula `d_{𝐗 × Y}(φ, y) = d_𝐗(φ) + d_Y(y)` holds (`MPolyfold.isTame_prod`):
`d_{𝐗 × Y}(F(φ), s(φ)) = 2 · d_𝐘(φ)` and `d_{𝐗 ₛ×_F Y}(F(φ), s(φ)) = ½ · d_{𝐗 × Y}(F(φ), s(φ))`
(stated as `2 · d_{𝐗 ₛ×_F Y} = d_{𝐗 × Y}`). -/
theorem degIndex_prod_fibredMap (hX : X.IsTame) (hY : Y.IsTame) (φ : MorY) :
    letI := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
    letI := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
    (X.PMor.prod Y.PObj).degIndex (F.mor φ, Y.src φ) = 2 * Y.PMor.degIndex φ ∧
      2 * (MPolyfold.subPolyfold (MPolyfold.isSubMPolyfold_fibredProduct
        X.isLocalScDiffeo_src F.isScSmoothMap_obj)).degIndex (F.fibredMap φ) =
        (X.PMor.prod Y.PObj).degIndex (F.mor φ, Y.src φ) := by
  let _ := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
  let _ := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
  have h2 : (X.PMor.prod Y.PObj).degIndex (F.mor φ, Y.src φ) = 2 * Y.PMor.degIndex φ := by
    rw [(MPolyfold.isTame_prod X.PMor Y.PObj (X.isLocalScDiffeo_src.isTame hX) hY).2,
      hF.degIndex_mor, ← Y.degIndex_src]
    ring
  exact ⟨h2, by rw [h2, ← hF.degIndex_fibredMap]⟩

end IsProperCovering

end EpFunctor

end Fibres

section Composition

variable {ObjY MorY : Type u} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type v} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {ObjZ MorZ : Type w} [TopologicalSpace ObjZ] [T2Space ObjZ] [ParacompactSpace ObjZ]
  [TopologicalSpace MorZ] [T2Space MorZ] [ParacompactSpace MorZ]
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX} {Z : EpGroupoid ObjZ MorZ}
  {F : EpFunctor Y X} {H : EpFunctor Z Y}

namespace EpFunctor.IsProperCovering

/-- **Proposition 8.2, property (2) of `F ∘ H`**: evenly covered neighbourhoods.  Take `U(x)` of
`F`, shrunk to `U₀ ⊆ U(x)` with `(F|U(y))⁻¹(U₀) ⊆ U'(y)` for the evenly covered `U'(y)` of `H`,
`y ∈ F⁻¹(x)`, and for `z ∈ H⁻¹(y)` the sheet `U'(z) ∩ H⁻¹(U(y) ∩ F⁻¹(U₀))`. -/
theorem evenlyCovered_comp (hF : F.IsProperCovering) (hH : H.IsProperCovering) (x : ObjX) :
    ∃ (U : Set ObjX) (V : ObjZ → Set ObjZ) (σ : ObjZ → ObjX → ObjZ),
      IsOpen U ∧ x ∈ U ∧ ((F.comp H).obj ⁻¹' {x}).PairwiseDisjoint V ∧
      (∀ z ∈ (F.comp H).obj ⁻¹' {x}, z ∈ V z ∧
        Z.PObj.IsScDiffeoOn X.PObj (F.comp H).obj (σ z) (V z) U) ∧
      (F.comp H).obj ⁻¹' U = ⋃ z ∈ (F.comp H).obj ⁻¹' {x}, V z := by
  obtain ⟨U, V, σ, hUo, hxU, hdisj, hV, hcov⟩ := hF.evenlyCovered x
  choose U' V' σ' hU'o hyU' hdisj' hV' hcov' using hH.evenlyCovered
  -- the shrunken neighbourhood `U₀` of `x`
  obtain ⟨U₀, hU₀o, hxU₀, hU₀U, hU₀σ⟩ : ∃ U₀ : Set ObjX, IsOpen U₀ ∧ x ∈ U₀ ∧ U₀ ⊆ U ∧
      ∀ y ∈ F.obj ⁻¹' {x}, ∀ u ∈ U₀, σ y u ∈ U' y := by
    refine ⟨U ∩ ⋂ y ∈ F.obj ⁻¹' {x}, (U ∩ σ y ⁻¹' U' y),
      hUo.inter ((hF.finite_fiber x).isOpen_biInter fun y hy =>
        (hV y hy).2.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hUo (hU'o y)),
      ⟨hxU, mem_iInter₂.2 fun y hy => ⟨hxU, ?_⟩⟩, inter_subset_left,
      fun y hy u hu => ((mem_iInter₂.1 hu.2) y hy).2⟩
    change σ y x ∈ U' y
    have := (hV y hy).2.left_inv y (hV y hy).1
    rw [show F.obj y = x from hy] at this
    rw [this]
    exact hyU' y
  -- `A(y) = U(y) ∩ F⁻¹(U₀) ⊆ U'(y)`
  have hA : ∀ y ∈ F.obj ⁻¹' {x}, V y ∩ F.obj ⁻¹' U₀ ⊆ U' y := fun y hy a ha => by
    have h1 := hU₀σ y hy _ ha.2
    rwa [(hV y hy).2.left_inv a ha.1] at h1
  have hAo : ∀ y ∈ F.obj ⁻¹' {x}, IsOpen (V y ∩ F.obj ⁻¹' U₀) := fun y hy =>
    (hV y hy).2.isScSmoothOn.continuousOn.isOpen_inter_preimage (hV y hy).2.isOpen_source hU₀o
  refine ⟨U₀, fun z => V' (H.obj z) z ∩ H.obj ⁻¹' (V (H.obj z) ∩ F.obj ⁻¹' U₀),
    fun z x' => σ' (H.obj z) z (σ (H.obj z) x'), hU₀o, hxU₀, ?_, fun z hz => ?_, ?_⟩
  · -- mutually disjoint
    intro z₁ hz₁ z₂ hz₂ hne
    change Disjoint (V' (H.obj z₁) z₁ ∩ H.obj ⁻¹' (V (H.obj z₁) ∩ F.obj ⁻¹' U₀))
      (V' (H.obj z₂) z₂ ∩ H.obj ⁻¹' (V (H.obj z₂) ∩ F.obj ⁻¹' U₀))
    by_cases h12 : H.obj z₁ = H.obj z₂
    · have hd : Disjoint (V' (H.obj z₁) z₁) (V' (H.obj z₁) z₂) :=
        hdisj' (H.obj z₁) (show H.obj z₁ = H.obj z₁ from rfl) h12.symm hne
      refine hd.mono inter_subset_left ?_
      rw [h12]
      exact inter_subset_left
    · have hd : Disjoint (V (H.obj z₁)) (V (H.obj z₂)) := hdisj hz₁ hz₂ h12
      exact (hd.preimage H.obj).mono (fun w hw => hw.2.1) fun w hw => hw.2.1
  · -- `z ∈ V(z)` and `F ∘ H : V(z) → U₀` is an sc-diffeomorphism
    have hy : H.obj z ∈ F.obj ⁻¹' {x} := hz
    obtain ⟨hzV', hHd⟩ := hV' (H.obj z) z (show H.obj z = H.obj z from rfl)
    obtain ⟨hyV, hFd⟩ := hV (H.obj z) hy
    refine ⟨⟨hzV', hyV, ?_⟩, ?_⟩
    · change F.obj (H.obj z) ∈ U₀
      rw [show F.obj (H.obj z) = x from hz]
      exact hxU₀
    · exact (isScDiffeoOn_restrictTarget hFd hU₀o hU₀U).comp
        (isScDiffeoOn_restrictTarget hHd (hAo _ hy) (hA _ hy))
  · -- `(F ∘ H)⁻¹(U₀) = ⋃ V(z)`
    ext w
    constructor
    · intro hw
      have hwU : H.obj w ∈ F.obj ⁻¹' U := hU₀U hw
      rw [hcov] at hwU
      obtain ⟨y, hy, hwy⟩ := mem_iUnion₂.1 hwU
      have hwA : H.obj w ∈ V y ∩ F.obj ⁻¹' U₀ := ⟨hwy, hw⟩
      have hwU' : w ∈ H.obj ⁻¹' U' y := hA y hy hwA
      rw [hcov' y] at hwU'
      obtain ⟨z, hz, hwz⟩ := mem_iUnion₂.1 hwU'
      have hzy : H.obj z = y := hz
      refine mem_iUnion₂.2 ⟨z, ?_, ?_⟩
      · change F.obj (H.obj z) = x
        rw [hzy]
        exact hy
      · change w ∈ V' (H.obj z) z ∩ H.obj ⁻¹' (V (H.obj z) ∩ F.obj ⁻¹' U₀)
        rw [hzy]
        exact ⟨hwz, hwA⟩
    · intro hw
      obtain ⟨z, -, hwz⟩ := mem_iUnion₂.1 hw
      exact hwz.2.2

/-- **Proposition 8.2, property (3) of `F ∘ H`** (the text's proof, pp. 276–277):
`L_{F∘H} = K̃ ∘ L_H` with `K̃ : Y ₛ×_H Z → X ₛ×_{F∘H} Z`, `(ψ, z) ↦ (F(ψ), z)`, an
sc-diffeomorphism with inverse `L̃(φ, z) = (L_F⁻¹(φ, H(z)), z)`. -/
theorem isScDiffeo_fibredMap_comp (hF : F.IsProperCovering) (hH : H.IsProperCovering) :
    letI := MPolyfold.paracompactSpace_prod X.PMor Z.PObj
    letI := (X.PMor.prod Z.PObj).paracompactSpace_subtype
      (MPolyfold.fibredProduct X.src (F.comp H).obj)
    ∃ g : MPolyfold.fibredProduct X.src (F.comp H).obj → MorZ,
      Z.PMor.IsScDiffeoOn (MPolyfold.subPolyfold
        (MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src
          (F.comp H).isScSmoothMap_obj)) (F.comp H).fibredMap g univ univ := by
  let _ := MPolyfold.paracompactSpace_prod X.PMor Z.PObj
  let _ := (X.PMor.prod Z.PObj).paracompactSpace_subtype
    (MPolyfold.fibredProduct X.src (F.comp H).obj)
  let _ := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
  let _ := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
  let _ := MPolyfold.paracompactSpace_prod Y.PMor Z.PObj
  let _ := (Y.PMor.prod Z.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct Y.src H.obj)
  have hB := MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src
    (F.comp H).isScSmoothMap_obj
  have hAF := MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src F.isScSmoothMap_obj
  have hAH := MPolyfold.isSubMPolyfold_fibredProduct Y.isLocalScDiffeo_src H.isScSmoothMap_obj
  obtain ⟨gF, hgF⟩ := hF.isScDiffeo_fibredMap
  obtain ⟨gH, hgH⟩ := hH.isScDiffeo_fibredMap
  -- `K̃(ψ, z) = (F(ψ), z)`
  let K : MPolyfold.fibredProduct Y.src H.obj → MPolyfold.fibredProduct X.src (F.comp H).obj :=
    fun p => ⟨(F.mor p.1.1, p.1.2),
      (F.src_mor _).trans (congrArg F.obj (show Y.src p.1.1 = H.obj p.1.2 from p.2))⟩
  -- `(φ, z) ↦ (φ, H(z)) ∈ X ₛ×_F Y`
  let a : MPolyfold.fibredProduct X.src (F.comp H).obj → MPolyfold.fibredProduct X.src F.obj :=
    fun q => ⟨(q.1.1, H.obj q.1.2), q.2⟩
  have ha : ∀ q, Y.src (gF (a q)) = H.obj q.1.2 := fun q =>
    congrArg (fun p : MPolyfold.fibredProduct X.src F.obj => p.1.2)
      (hgF.right_inv (a q) (mem_univ _))
  -- `L̃(φ, z) = (L_F⁻¹(φ, H(z)), z)`
  let L : MPolyfold.fibredProduct X.src (F.comp H).obj → MPolyfold.fibredProduct Y.src H.obj :=
    fun q => ⟨(gF (a q), q.1.2), ha q⟩
  have hvalH := MPolyfold.subPolyfold_inclusion_isScSmooth hAH
  have hvalB := MPolyfold.subPolyfold_inclusion_isScSmooth hB
  have hK : (MPolyfold.subPolyfold hAH).IsScSmoothMap (MPolyfold.subPolyfold hB) K :=
    isScSmoothOn_subPolyfold_of_val hB (f := K) (MPolyfold.IsScSmoothOn.prodMk
      (F.isScSmoothMap_mor.comp ((MPolyfold.isScSmoothMap_fst Y.PMor Z.PObj).comp hvalH))
      ((MPolyfold.isScSmoothMap_snd Y.PMor Z.PObj).comp hvalH))
  have hasm : (MPolyfold.subPolyfold hB).IsScSmoothMap (MPolyfold.subPolyfold hAF) a :=
    isScSmoothOn_subPolyfold_of_val hAF (f := a) (MPolyfold.IsScSmoothOn.prodMk
      ((MPolyfold.isScSmoothMap_fst X.PMor Z.PObj).comp hvalB)
      (H.isScSmoothMap_obj.comp ((MPolyfold.isScSmoothMap_snd X.PMor Z.PObj).comp hvalB)))
  have hL : (MPolyfold.subPolyfold hB).IsScSmoothMap (MPolyfold.subPolyfold hAH) L :=
    isScSmoothOn_subPolyfold_of_val hAH (f := L) (MPolyfold.IsScSmoothOn.prodMk
      (MPolyfold.IsScSmoothOn.comp hgF.isScSmoothOn_inv hasm (mapsTo_univ _ _))
      ((MPolyfold.isScSmoothMap_snd X.PMor Z.PObj).comp hvalB))
  have hKL : (MPolyfold.subPolyfold hAH).IsScDiffeoOn (MPolyfold.subPolyfold hB) K L univ univ :=
    ⟨hK, hL, mapsTo_univ _ _, mapsTo_univ _ _, fun p _ => ?_, fun q _ => ?_⟩
  · exact ⟨gH ∘ L, hKL.comp hgH⟩
  · -- `L̃ ∘ K̃ = id`
    refine Subtype.ext (Prod.ext ?_ rfl)
    change gF (a (K p)) = p.1.1
    have : a (K p) = F.fibredMap p.1.1 :=
      Subtype.ext (Prod.ext rfl (show H.obj p.1.2 = Y.src p.1.1 from p.2.symm))
    rw [this]
    exact hgF.left_inv _ (mem_univ _)
  · -- `K̃ ∘ L̃ = id`
    refine Subtype.ext (Prod.ext ?_ rfl)
    exact congrArg (fun p : MPolyfold.fibredProduct X.src F.obj => p.1.1)
      (hgF.right_inv (a q) (mem_univ _))

/-- **Proposition 8.2** (p. 276): the composition `F ∘ H : Z → X` of proper covering functors
`F : Y → X` and `H : Z → Y` is a proper covering functor. -/
theorem proposition_8_2 (hF : F.IsProperCovering) (hH : H.IsProperCovering) :
    (F.comp H).IsProperCovering where
  surjective := hF.surjective.comp hH.surjective
  isLocalScDiffeo := hF.isLocalScDiffeo.comp hH.isLocalScDiffeo
  finite_fiber x := (hF.finite_fiber x).preimage' fun y _ => hH.finite_fiber y
  evenlyCovered := evenlyCovered_comp hF hH
  isScDiffeo_fibredMap := isScDiffeo_fibredMap_comp hF hH

end EpFunctor.IsProperCovering

end Composition

end Polyfold
