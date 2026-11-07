import Polyfold.Chapter7.NaturalRep
import Polyfold.Chapter7.NaturalAction

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II,
Chapter 7: **Proposition 7.5** (the natural representation of a finite set of isomorphic objects,
pp. 233–236, with its proof) and **Definition 7.8** (p. 236; the structure `NaturalRepFinite` is
in `EpGroupoid.lean`).  There is no 2014 preprint of Part II; numbers and pages are the 2017
text's.

# The natural representation of a finite set of isomorphic objects

## The text, paraphrased

(Proposition 7.5, pp. 233–234) Let `Y = {y₁, …, y_k}` be distinct, mutually isomorphic objects and
`𝐘` the morphisms between them (the full subcategory on `Y`).  Given a neighbourhood `V` of `Y`
there is a functor `f` assigning to every `y ∈ Y` a connected open `U(y) ⊆ V`, mutually disjoint,
and to every `ψ : y → y'` in `𝐘` an sc-diffeomorphism `f(ψ) : U(y) → U(y')`; the set `𝐔` of
morphisms with source and target in `⋃ U(y)` decomposes into connected components `𝐔(ψ)`,
`ψ ∈ 𝐘`, and (1) `G_y` acts on `U(y)` by the natural action, (2) `s : 𝐔(ψ) → U(y)` and
`t : 𝐔(ψ) → U(y')` are sc-diffeomorphisms, (3) `f(ψ)(z) = t ∘ (s|𝐔(ψ))⁻¹(z)`.  (Proof, pp.
234–236) By induction on `#Y`; `#Y = 1` is Theorem 7.1.  For `Y = {y₁, y₂}` fix `γ₁ : y₁ → y₂` with
a sheet `V(γ₁)` and `γ̂₁ = t ∘ (s|V(γ₁))⁻¹`, take a `G_{y₁}`-invariant connected `U(y₁)` with
`γ̂₁(U(y₁))` inside a `G_{y₂}`-invariant `W(y₂)`, put `U(y₂) = γ̂₁(U(y₁))` and show it
`G_{y₂}`-invariant; the other morphisms `y₁ → y₂` are `γ_g = g ∘ γ₁`, `g ∈ G_{y₂}`, with components
`𝐔(γ_g) = Φ_g(𝐔(γ₁))`, `Φ_g(φ) = Γ(g, t(φ)) ∘ φ`, and the morphisms `y₂ → y₁` get
`𝐔(φ) = ι(𝐔(φ⁻¹))`.  For `Y = Y' ∪ {y_{k+1}}` fix `δ_j : y_{k+1} → y_j`, shrink as in the case of
two objects to `U(y_{k+1})`, `U(y_j)` with `δ̂_j : U(y_{k+1}) → U(y_j)` sc-diffeomorphisms, and
adjust the components of the morphisms `γ : y_i → y_j` of `Y'` to `𝐔(γ) = (s|𝐔'(γ))⁻¹(U(y_i))`,
showing `t(𝐔(γ)) = U(y_j)`.  (Definition 7.8, p. 236) A functor `f` as constructed in
Proposition 7.5 is the natural representation of `𝐘` on neighbourhoods contained in `V`.

## What is formalized (namespace `Polyfold.EpGroupoid`)

* **Transport along sheets** (namespace `NatRepFinite`; `R` a natural representation at `x`, `𝐒`
  sheets (Definition 7.4) of morphisms out of `x` with `U(x) ⊆ s(𝐒)`): `back` (`φ̂⁻¹`),
  `transportSet` (`φ̂(U(x))`; `isScDiffeoOn_hat_transportSet`, `isOpen_transportSet`,
  `isConnected_transportSet`), `conjMap` (`γ̂₂ ∘ Φ(g) ∘ γ̂₁⁻¹`; `isScDiffeoOn_conjMap`,
  `conjMap_conjMap`, `conjMap_one`, `conjMap_self`), `transport` (`Θ_g(z) = a₂(Φ(g) u) ∘ Γ(g, u) ∘
  a₁(u)⁻¹`, `u = γ̂₁⁻¹(z)`, `aᵢ = (s|𝐒ᵢ)⁻¹`; `src_transport`, `tgt_transport`,
  `transport_hat_self`, `isScSmoothOn_transport`, `existsUnique_transport`: every morphism from
  `γ̂₁(U(x))` to `γ̂₂(U(x))` is `Θ_g(s k)` for a unique `g ∈ G_x`; `transport_injective`).
* **A natural representation transported along a morphism** `γ : x → y`: `transportConj`
  (`h ↦ γ⁻¹ h γ`, `G_y ≅ G_x`), `transportRep : X.NaturalRep y` (`U(y) = γ̂(U(x))`,
  `Φ_y(h) = γ̂ ∘ Φ(γ⁻¹ h γ) ∘ γ̂⁻¹`, `Γ_y(h, ·) = Θ_{γ⁻¹ h γ}`), `transportRep_U`,
  `transportRep_Φ`, `transportRep_Γ`; `exists_spoke` (a shrinking of a given `R`, same `Φ`, `Γ`,
  and a sheet of `γ` to which `transportRep` applies).
* Sections of `s`: `isScDiffeoOn_src_image_of_section`, `isScDiffeoOn_tgt_image_of_section`.
* **The star construction**: `NatRepFinite.Star X Y V` (a base object `x`, a natural
  representation `R` at `x`, sheets `K y` of `γ_y : x → y`, the `γ̂_y(U(x)) ⊆ V` pairwise
  disjoint), `NatRepFinite.exists_star`; `Star.g` (`g_ψ = γ_{y'}⁻¹ ∘ ψ ∘ γ_y ∈ G_x`; `g_comp`,
  `g_unit`, `g_inv`, `g_isotropy`), `Star.F` (`f(ψ) = γ̂_{y'} ∘ Φ(g_ψ) ∘ γ̂_y⁻¹`; `isScDiffeoOn_F`,
  `F_comp`, `F_unit`), `Star.Θ`, `Star.sheet` (`𝐔(ψ) = Θ_{g_ψ}(U(y))`; `mem_sheet`,
  `pairwiseDisjoint_sheet`, `morOn_eq`), `Star.toNaturalRepFinite`.
* **Proposition 7.5**: `proposition_7_5` (open `V ⊇ Y`) and `proposition_7_5_of_mem_nhdsSet`
  (`V ∈ 𝓝ˢ Y`, the text's "neighborhood `V` of `Y`"); `NatRepFinite.emptyNaturalRepFinite`
  (`Y = ∅`), `NatRepFinite.mono` (enlarging `V`).
* **"Decomposes into connected components `𝐔(ψ)`"**: `NatRepFinite.connectedComponentIn_morOn`,
  for every `NaturalRepFinite`: the `𝐔(ψ)` are the connected components of `𝐔`.

## Reading

* **A star construction instead of the induction** (PLAN II.6, 6).  Fix one base object `x`
  isomorphic to every `y ∈ Y` (`y₁`, say; `x ∈ Y` is not used), one natural representation
  `(U(x), Φ, Γ)` of `G_x` (Theorem 7.1) and for each `y ∈ Y` a morphism `γ_y : x → y` with a sheet
  `K y`; `U(x)` is taken inside every `s(K y)` and so small that the `U(y) := γ̂_y(U(x))` lie in
  pairwise disjoint open `W_y ∩ V` (Hausdorff separation of the finite `Y`).  Everything is
  transported from `x`: `ψ ↦ g_ψ = γ_{y'}⁻¹ ∘ ψ ∘ γ_y` is a bijection from the morphisms `y → y'`
  onto `G_x` compatible with composition; a morphism `k` from `U(y)` to `U(y')` pulls back to the
  morphism `a_{y'}⁻¹ ∘ k ∘ a_y` of `U(x)`, which is `Γ(g, u)` for a unique `g` (Theorem 7.1 (3)),
  so `k = Θ_g(s k)`; `f(ψ) = γ̂_{y'} ∘ Φ(g_ψ) ∘ γ̂_y⁻¹` is a functor since `ψ ↦ g_ψ` is one and `Φ`
  is a homomorphism; `𝐔(ψ) = Θ_{g_ψ}(U(y))`.  No `U(y)` is shrunk afterwards, so the adjustment
  of the components of `Y'` in the inductive step (the claim `t(𝐔(γ)) = U(y_j)`) has no
  counterpart.  The text's case `Y = {y₁, y₂}` already has this form (`U(y₂) = γ̂₁(U(y₁))`).
* **(1), the natural action of `G_y` on `U(y)`.**  The text chooses `U(y)` invariant under a
  natural representation of `G_y` given beforehand; here the natural representation of `G_y` on
  `U(y)` is the transported one (`transportRep`).  By the uniqueness on connected neighbourhoods
  (`NaturalRep.Φ_eqOn`, `NaturalAction.lean`) it agrees near `y` with every other one.  The field
  `natural` of `NaturalRepFinite` asks for one natural representation on `U(y)` whose `Φ` is `f` on
  `G_y`.
* **Sc-smoothness.**  `Θ_g` is sc-smooth by condition (4) of Definition 7.3 in the sheet form,
  used twice (for the sheet `𝐔(g) = Γ(g, U(x))` and for `K y'`), and the sc-smoothness of `ι`;
  that `s` and `t` are sc-diffeomorphisms on `𝐔(ψ)` (the text's "`Φ_g` is a sc-diffeomorphism onto
  its image") is `isScDiffeoOn_src_image_of_section`, `isScDiffeoOn_tgt_image_of_section`.
* **"A neighborhood `V` of `Y`"** is `V ∈ 𝓝ˢ Y` (`proposition_7_5_of_mem_nhdsSet`), reduced to an
  open `V` by `mem_nhdsSet_iff_exists`.  "Distinct objects" is `Y : Finset Obj`; `Y = ∅` is
  allowed.  "Mutually isomorphic" is used only through one `x` isomorphic to all of `Y`.
* **Hypotheses.**  No hypothesis "for all …" is added.  `Star X Y V` is inhabited whenever `Y` is
  nonempty and mutually isomorphic and `V ⊇ Y` is open (`exists_star`); the hypotheses of
  `transportRep` are met by `exists_spoke`.
* **Possible misprints** in the proof, as we read it (PLAN II.6, 6; all three stand):
  - p. 234, "Fixing `g ∈ G_{y1}`, we consider the map `Φ_g : 𝐔(γ₁) → X`, `Φ_g(φ) = Γ(g, t(φ)) ∘
    φ`" (the formula on p. 235): `t(φ) ∈ U(y₂)` and `γ_g = g ∘ γ₁` with `g ∈ G_{y₂}`, so `G_{y2}`
    is meant;
  - p. 235, "`𝐔(γ_g) := Ψ_g(𝐔(γ₁))`": `Φ_g` is meant;
  - p. 235, "Let `k ≥ 3` and assume that the statement holds for any set `Y'` of `k` distinct
    objects": the cases done are `#Y = 1, 2`, so the step `k → k + 1` must start at `k ≥ 2` to
    reach `#Y = 3`.
  Further possible misprints on the same pages: "The images `𝐔(ψ_g)`" (p. 235) for `𝐔(γ_g)`;
  "`φ = Γ(g, s(φ)) ∘ ψ` … `ψ ∈ 𝐔(γ₁)`" (p. 235), where `Γ(g, ·)` lives on `U(y₂)` while
  `s(φ) ∈ U(y₁)`: `φ = Γ(g, t(ψ)) ∘ ψ` is meant; "for a unique `g ∈ G_x`" (p. 234) for `G_{y₁}`;
  two morphisms named `φ` ("`φ : u → z` and `φ : u' → z'`", p. 234); "`y : 𝐔(δ_j) → U(y_j)`"
  (p. 235) for `t`; "`Γ(g, z') : z' → z` for some `g ∈ G_{y_i}`" (p. 236) for `G_{y_j}`.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace EpGroupoid

universe u

namespace NatRepFinite

/-! ### Groupoid algebra -/

section Algebra

variable {Obj Mor : Type u} {G : GroupoidStr Obj Mor}

/-- `φ ∘ (φ⁻¹ ∘ ψ) = ψ`. -/
private theorem comp_inv_comp {φ ψ : Mor} (h : G.tgt φ = G.tgt ψ) :
    G.comp φ (G.comp (G.inv φ) ψ) = ψ := by
  have := GroupoidStr.inv_comp_cancel_left (G := G) (φ := G.inv φ) (ψ := ψ)
    (by rw [G.src_inv]; exact h)
  rwa [GroupoidStr.inv_inv] at this

/-- `γ' ∘ ((γ'⁻¹ ∘ ψ ∘ γ) ∘ γ⁻¹) = ψ`. -/
private theorem comp_conj_cancel {γ γ' ψ : Mor} (h : G.tgt γ' = G.tgt ψ)
    (h' : G.src ψ = G.tgt γ) :
    G.comp γ' (G.comp (G.comp (G.comp (G.inv γ') ψ) γ) (G.inv γ)) = ψ := by
  have h1 : G.src (G.comp (G.inv γ') ψ) = G.tgt γ := by
    rw [G.src_comp _ _ (by rw [G.src_inv]; exact h), h']
  rw [GroupoidStr.comp_inv_cancel_right h1, comp_inv_comp h]

/-- The source of the conjugate `A⁻¹ ∘ ψ ∘ B`. -/
private theorem src_conj {A B ψ : Mor} (hA : G.tgt A = G.tgt ψ) (hB : G.tgt B = G.src ψ) :
    G.src (G.comp (G.comp (G.inv A) ψ) B) = G.src B :=
  G.src_comp _ _ (by rw [G.src_comp _ _ (by rw [G.src_inv]; exact hA)]; exact hB.symm)

/-- The target of the conjugate `A⁻¹ ∘ ψ ∘ B`. -/
private theorem tgt_conj {A B ψ : Mor} (hA : G.tgt A = G.tgt ψ) (hB : G.tgt B = G.src ψ) :
    G.tgt (G.comp (G.comp (G.inv A) ψ) B) = G.src A := by
  have e : G.src (G.inv A) = G.tgt ψ := by rw [G.src_inv]; exact hA
  rw [G.tgt_comp _ _ (by rw [G.src_comp _ _ e]; exact hB.symm), G.tgt_comp _ _ e, G.tgt_inv]

/-- `(A⁻¹ ∘ φ ∘ B) ∘ (B⁻¹ ∘ ψ ∘ C) = A⁻¹ ∘ (φ ∘ ψ) ∘ C`. -/
private theorem conj_comp_conj {A B C φ ψ : Mor} (hA : G.tgt A = G.tgt φ)
    (hB : G.tgt B = G.src φ) (hc : G.src φ = G.tgt ψ) (hC : G.tgt C = G.src ψ) :
    G.comp (G.comp (G.comp (G.inv A) φ) B) (G.comp (G.comp (G.inv B) ψ) C) =
      G.comp (G.comp (G.inv A) (G.comp φ ψ)) C := by
  have e1 : G.src (G.inv B) = G.tgt ψ := by rw [G.src_inv, hB, hc]
  have e2 : G.src ψ = G.tgt C := hC.symm
  have e3 : G.src (G.inv A) = G.tgt φ := by rw [G.src_inv, hA]
  have e4 : G.src (G.comp (G.inv A) φ) = G.tgt B := by rw [G.src_comp _ _ e3, hB]
  have e5 : G.src (G.inv B) = G.tgt (G.comp ψ C) := by rw [G.tgt_comp _ _ e2]; exact e1
  have e6 : G.src B = G.tgt (G.comp (G.inv B) (G.comp ψ C)) := by
    rw [G.tgt_comp _ _ e5, G.tgt_inv]
  rw [G.comp_assoc (G.inv B) ψ C e1 e2, G.comp_assoc _ B _ e4 e6,
    comp_inv_comp (by rw [G.tgt_comp _ _ e2, hB, hc]),
    ← G.comp_assoc _ ψ C (by rw [G.src_comp _ _ e3]; exact hc) e2,
    G.comp_assoc (G.inv A) φ ψ e3 hc]

end Algebra

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-! ### Sections of the source map -/

/-- A continuous section `σ` of `s` over an open set has open image. -/
private theorem isOpen_image_section {U : Set Obj} (hU : IsOpen U) {σ : Obj → Mor}
    (hσ : ContinuousOn σ U) (hsec : ∀ z ∈ U, X.src (σ z) = z) : IsOpen (σ '' U) := by
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨W, hWo, hyW, hinj⟩ := X.isLocalScDiffeo_src.isLocallyInjective (σ y)
  have hN : IsOpen (U ∩ σ ⁻¹' W) := hσ.isOpen_inter_preimage hU hWo
  refine ⟨W ∩ X.src ⁻¹' (U ∩ σ ⁻¹' W), fun ψ hψ => ?_,
    hWo.inter (hN.preimage X.continuous_src), hyW, ?_⟩
  · exact ⟨X.src ψ, hψ.2.1, hinj hψ.2.2 hψ.1 (hsec _ hψ.2.1)⟩
  · change X.src (σ y) ∈ U ∩ σ ⁻¹' W
    rw [hsec y hy]
    exact ⟨hy, hyW⟩

/-- **`s` on the image of an sc-smooth section** `σ` over an open `U` is an sc-diffeomorphism
onto `U`, with inverse `σ`. -/
theorem isScDiffeoOn_src_image_of_section {U : Set Obj} {σ : Obj → Mor}
    (hσ : X.PObj.IsScSmoothOn X.PMor σ U) (hsec : ∀ z ∈ U, X.src (σ z) = z) :
    X.PMor.IsScDiffeoOn X.PObj X.src σ (σ '' U) U where
  isScSmoothOn := X.isScSmoothMap_src.mono
    (isOpen_image_section hσ.isOpen hσ.continuousOn hsec) (subset_univ _)
  isScSmoothOn_inv := hσ
  mapsTo := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hsec z hz]
    exact hz
  mapsTo_inv _ hz := mem_image_of_mem σ hz
  left_inv := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hsec z hz]
  right_inv := hsec

/-- **`t` on the image of an sc-smooth section** `σ` of `s` over an open `U`, with `t ∘ σ = f` an
sc-diffeomorphism `U → U'` with inverse `f'`, is an sc-diffeomorphism onto `U'`, with inverse
`σ ∘ f'`. -/
theorem isScDiffeoOn_tgt_image_of_section {U U' : Set Obj} {σ : Obj → Mor} {f f' : Obj → Obj}
    (hσ : X.PObj.IsScSmoothOn X.PMor σ U) (hsec : ∀ z ∈ U, X.src (σ z) = z)
    (hf : X.PObj.IsScDiffeoOn X.PObj f f' U U') (htf : ∀ z ∈ U, X.tgt (σ z) = f z) :
    X.PMor.IsScDiffeoOn X.PObj X.tgt (σ ∘ f') (σ '' U) U' where
  isScSmoothOn := X.isScSmoothMap_tgt.mono
    (isOpen_image_section hσ.isOpen hσ.continuousOn hsec) (subset_univ _)
  isScSmoothOn_inv := MPolyfold.IsScSmoothOn.comp hσ hf.isScSmoothOn_inv hf.mapsTo_inv
  mapsTo := by
    rintro _ ⟨z, hz, rfl⟩
    rw [htf z hz]
    exact hf.mapsTo hz
  mapsTo_inv _ hz := mem_image_of_mem σ (hf.mapsTo_inv hz)
  left_inv := by
    rintro _ ⟨z, hz, rfl⟩
    simp only [Function.comp_apply]
    rw [htf z hz, hf.left_inv z hz]
  right_inv z hz := by
    simp only [Function.comp_apply]
    rw [htf _ (hf.mapsTo_inv hz), hf.right_inv z hz]

/-! ### Transport along a sheet -/

/-- `φ̂⁻¹ = s ∘ (t|𝐔(φ))⁻¹` for a sheet `𝐔(φ)` (Definition 7.4). -/
def back (S : X.Sheet) (z : Obj) : Obj := X.src (S.tgtInv z)

section Transport

variable {x : Obj} (R : X.NaturalRep x)

/-- **The transported neighbourhood** `φ̂(U(x))` of a sheet `𝐒` of `φ : x → y`. -/
def transportSet (S : X.Sheet) : Set Obj := S.hat '' R.U

/-- **The transported action** `γ̂₂ ∘ Φ(g) ∘ γ̂₁⁻¹ : γ̂₁(U(x)) → γ̂₂(U(x))` for two sheets. -/
def conjMap (S₁ S₂ : X.Sheet) (g : X.Isotropy x) (z : Obj) : Obj :=
  S₂.hat (R.Φ g (back S₁ z))

/-- **The transported section** `Θ_g(z) = a₂(Φ(g) u) ∘ Γ(g, u) ∘ a₁(u)⁻¹`, `u = γ̂₁⁻¹(z)`,
`aᵢ = (s|𝐒ᵢ)⁻¹`: a morphism `z → γ̂₂ Φ(g) γ̂₁⁻¹(z)`. -/
def transport (S₁ S₂ : X.Sheet) (g : X.Isotropy x) (z : Obj) : Mor :=
  X.comp (S₂.srcInv (R.Φ g (back S₁ z)))
    (X.comp (R.Γ g (back S₁ z)) (X.inv (S₁.srcInv (back S₁ z))))

variable {R} {S S₁ S₂ S₃ : X.Sheet}

theorem src_srcInv (hS : R.U ⊆ S.srcSet) {u : Obj} (hu : u ∈ R.U) : X.src (S.srcInv u) = u :=
  S.isScDiffeoOn_src.right_inv u (hS hu)

/-- `φ̂ : U(x) → φ̂(U(x))` is an sc-diffeomorphism with inverse `φ̂⁻¹`. -/
theorem isScDiffeoOn_hat_transportSet (hS : R.U ⊆ S.srcSet) :
    X.PObj.IsScDiffeoOn X.PObj S.hat (back S) R.U (transportSet R S) := by
  have h := S.isScDiffeoOn_hat.restrict R.isOpen_U hS
  have he := h.image_eq
  rw [← he] at h
  exact h

theorem isOpen_transportSet (hS : R.U ⊆ S.srcSet) : IsOpen (transportSet R S) :=
  (isScDiffeoOn_hat_transportSet hS).isOpen_target

theorem isConnected_transportSet (hS : R.U ⊆ S.srcSet) : IsConnected (transportSet R S) :=
  R.isConnected_U.image _ (isScDiffeoOn_hat_transportSet hS).isScSmoothOn.continuousOn

theorem hat_mem_transportSet {u : Obj} (hu : u ∈ R.U) : S.hat u ∈ transportSet R S :=
  mem_image_of_mem _ hu

theorem back_mem (hS : R.U ⊆ S.srcSet) {z : Obj} (hz : z ∈ transportSet R S) :
    back S z ∈ R.U :=
  (isScDiffeoOn_hat_transportSet hS).mapsTo_inv hz

theorem hat_back (hS : R.U ⊆ S.srcSet) {z : Obj} (hz : z ∈ transportSet R S) :
    S.hat (back S z) = z :=
  (isScDiffeoOn_hat_transportSet hS).right_inv z hz

theorem back_hat (hS : R.U ⊆ S.srcSet) {u : Obj} (hu : u ∈ R.U) : back S (S.hat u) = u :=
  (isScDiffeoOn_hat_transportSet hS).left_inv u hu

theorem self_mem_transportSet {y : Obj} (hy : S.hat x = y) : y ∈ transportSet R S :=
  hy ▸ hat_mem_transportSet R.mem_U

theorem back_self (hS : R.U ⊆ S.srcSet) {y : Obj} (hy : S.hat x = y) : back S y = x :=
  hy ▸ back_hat hS R.mem_U

/-- `γ̂₂ Φ(g) γ̂₁⁻¹ : γ̂₁(U(x)) → γ̂₂(U(x))` is an sc-diffeomorphism with inverse
`γ̂₁ Φ(g⁻¹) γ̂₂⁻¹`. -/
theorem isScDiffeoOn_conjMap (h₁ : R.U ⊆ S₁.srcSet) (h₂ : R.U ⊆ S₂.srcSet) (g : X.Isotropy x) :
    X.PObj.IsScDiffeoOn X.PObj (conjMap R S₁ S₂ g) (conjMap R S₂ S₁ g⁻¹) (transportSet R S₁)
      (transportSet R S₂) :=
  (isScDiffeoOn_hat_transportSet h₂).comp
    ((R.isScDiffeoOn_Φ g).comp (isScDiffeoOn_hat_transportSet h₁).symm)

theorem conjMap_conjMap (h₁ : R.U ⊆ S₁.srcSet) (h₂ : R.U ⊆ S₂.srcSet) (g h : X.Isotropy x)
    {z : Obj} (hz : z ∈ transportSet R S₁) :
    conjMap R S₂ S₃ g (conjMap R S₁ S₂ h z) = conjMap R S₁ S₃ (g * h) z := by
  have hu := back_mem h₁ hz
  simp only [conjMap]
  rw [back_hat h₂ (R.mapsTo_Φ h hu), R.Φ_mul g h _ hu]

theorem conjMap_one (hS : R.U ⊆ S.srcSet) {z : Obj} (hz : z ∈ transportSet R S) :
    conjMap R S S 1 z = z := by
  simp only [conjMap]
  rw [R.Φ_one _ (back_mem hS hz), hat_back hS hz]

theorem conjMap_self (h₁ : R.U ⊆ S₁.srcSet) {y₁ y₂ : Obj} (hy₁ : S₁.hat x = y₁)
    (hy₂ : S₂.hat x = y₂) (g : X.Isotropy x) : conjMap R S₁ S₂ g y₁ = y₂ := by
  simp only [conjMap]
  rw [back_self h₁ hy₁, R.Φ_self, hy₂]

private theorem transport_comp₁ (h₁ : R.U ⊆ S₁.srcSet) {u : Obj} (hu : u ∈ R.U)
    (g : X.Isotropy x) : X.src (R.Γ g u) = X.tgt (X.inv (S₁.srcInv u)) := by
  rw [R.src_Γ g u hu, X.tgt_inv, src_srcInv h₁ hu]

private theorem transport_comp₂ (h₁ : R.U ⊆ S₁.srcSet) (h₂ : R.U ⊆ S₂.srcSet) {u : Obj}
    (hu : u ∈ R.U) (g : X.Isotropy x) :
    X.src (S₂.srcInv (R.Φ g u)) = X.tgt (X.comp (R.Γ g u) (X.inv (S₁.srcInv u))) := by
  rw [src_srcInv h₂ (R.mapsTo_Φ g hu), X.tgt_comp _ _ (transport_comp₁ h₁ hu g), R.tgt_Γ g u hu]

/-- `s(Θ_g(z)) = z`. -/
theorem src_transport (h₁ : R.U ⊆ S₁.srcSet) (h₂ : R.U ⊆ S₂.srcSet) (g : X.Isotropy x)
    {z : Obj} (hz : z ∈ transportSet R S₁) : X.src (transport R S₁ S₂ g z) = z := by
  have hu := back_mem h₁ hz
  rw [transport, X.src_comp _ _ (transport_comp₂ h₁ h₂ hu g),
    X.src_comp _ _ (transport_comp₁ h₁ hu g), X.src_inv]
  exact hat_back h₁ hz

/-- `t(Θ_g(z)) = γ̂₂ Φ(g) γ̂₁⁻¹(z)`. -/
theorem tgt_transport (h₁ : R.U ⊆ S₁.srcSet) (h₂ : R.U ⊆ S₂.srcSet) (g : X.Isotropy x)
    {z : Obj} (hz : z ∈ transportSet R S₁) :
    X.tgt (transport R S₁ S₂ g z) = conjMap R S₁ S₂ g z := by
  rw [transport, X.tgt_comp _ _ (transport_comp₂ h₁ h₂ (back_mem h₁ hz) g)]
  rfl

/-- `Θ_g(γ̂₁(x)) = γ₂ ∘ g ∘ γ₁⁻¹` with `γᵢ = (s|𝐒ᵢ)⁻¹(x)`. -/
theorem transport_hat_self (h₁ : R.U ⊆ S₁.srcSet) (g : X.Isotropy x) :
    transport R S₁ S₂ g (S₁.hat x) =
      X.comp (S₂.srcInv x) (X.comp g.val (X.inv (S₁.srcInv x))) := by
  rw [transport, back_self h₁ rfl, R.Φ_self, R.Γ_self]

/-- **`Θ_g` is sc-smooth** on `γ̂₁(U(x))`: by condition (4) of Definition 7.3 in the sheet form,
applied to the sheets `𝐔(g) = Γ(g, U)` and `𝐒₂`. -/
theorem isScSmoothOn_transport (h₁ : R.U ⊆ S₁.srcSet) (h₂ : R.U ⊆ S₂.srcSet)
    (g : X.Isotropy x) :
    X.PObj.IsScSmoothOn X.PMor (transport R S₁ S₂ g) (transportSet R S₁) := by
  have hd := isScDiffeoOn_hat_transportSet h₁
  have hbm : MapsTo (back S₁) (transportSet R S₁) R.U := hd.mapsTo_inv
  have ha : X.PObj.IsScSmoothOn X.PMor (fun z => X.inv (S₁.srcInv (back S₁ z)))
      (transportSet R S₁) :=
    MPolyfold.IsScSmoothOn.comp X.isScSmoothMap_inv
      (MPolyfold.IsScSmoothOn.comp S₁.isScDiffeoOn_src.isScSmoothOn_inv hd.isScSmoothOn_inv
        fun z hz => h₁ (hbm hz)) (mapsTo_univ _ _)
  have htw : ∀ z ∈ transportSet R S₁, X.tgt (X.inv (S₁.srcInv (back S₁ z))) = back S₁ z :=
    fun z hz => by rw [X.tgt_inv, src_srcInv h₁ (hbm hz)]
  have hw : X.PObj.IsScSmoothOn X.PMor
      (fun z => X.comp (R.Γ g (back S₁ z)) (X.inv (S₁.srcInv (back S₁ z))))
      (transportSet R S₁) := by
    refine (MPolyfold.IsScSmoothOn.comp (R.isScSmoothOn_comp_Γ_tgt g) ha
      fun z hz => ?_).congr fun z hz => ?_
    · change X.tgt (X.inv (S₁.srcInv (back S₁ z))) ∈ R.U
      rw [htw z hz]
      exact hbm hz
    · simp only [Function.comp_apply, htw z hz]
  have htw' : ∀ z ∈ transportSet R S₁,
      X.tgt (X.comp (R.Γ g (back S₁ z)) (X.inv (S₁.srcInv (back S₁ z)))) =
        R.Φ g (back S₁ z) := fun z hz => by
    rw [X.tgt_comp _ _ (transport_comp₁ h₁ (hbm hz) g), R.tgt_Γ g _ (hbm hz)]
  refine (MPolyfold.IsScSmoothOn.comp (X.isScSmoothCompSheet S₂.srcInv S₂.carrier S₂.srcSet
    S₂.isScDiffeoOn_src) hw fun z hz => ?_).congr fun z hz => ?_
  · change X.tgt (X.comp (R.Γ g (back S₁ z)) (X.inv (S₁.srcInv (back S₁ z)))) ∈ S₂.srcSet
    rw [htw' z hz]
    exact h₂ (R.mapsTo_Φ g (hbm hz))
  · simp only [Function.comp_apply, htw' z hz]
    rfl

/-- **Every morphism `z → z'` between points of `γ̂₁(U(x))` and `γ̂₂(U(x))` is `Θ_g(z)` for a
unique `g ∈ G_x`**: `a₂⁻¹ ∘ k ∘ a₁` is a morphism of `U(x)`, so it is `Γ(g, u)` (Theorem 7.1
(3)). -/
theorem existsUnique_transport (h₁ : R.U ⊆ S₁.srcSet) (h₂ : R.U ⊆ S₂.srcSet) {k : Mor}
    (hs : X.src k ∈ transportSet R S₁) (ht : X.tgt k ∈ transportSet R S₂) :
    ∃! g : X.Isotropy x, transport R S₁ S₂ g (X.src k) = k := by
  obtain ⟨u, hu_def⟩ : ∃ u, u = back S₁ (X.src k) := ⟨_, rfl⟩
  obtain ⟨u', hu'_def⟩ : ∃ u', u' = back S₂ (X.tgt k) := ⟨_, rfl⟩
  have hu : u ∈ R.U := hu_def ▸ back_mem h₁ hs
  have hu' : u' ∈ R.U := hu'_def ▸ back_mem h₂ ht
  have ha₁s : X.src (S₁.srcInv u) = u := src_srcInv h₁ hu
  have ha₁t : X.tgt (S₁.srcInv u) = X.src k := by
    change S₁.hat u = X.src k
    rw [hu_def]
    exact hat_back h₁ hs
  have ha₂s : X.src (S₂.srcInv u') = u' := src_srcInv h₂ hu'
  have ha₂t : X.tgt (S₂.srcInv u') = X.tgt k := by
    change S₂.hat u' = X.tgt k
    rw [hu'_def]
    exact hat_back h₂ ht
  -- the pulled-back morphism `k' = a₂⁻¹ ∘ k ∘ a₁ : u → u'`
  have e1 : X.src (X.inv (S₂.srcInv u')) = X.tgt k := by rw [X.src_inv, ha₂t]
  have e2 : X.src (X.comp (X.inv (S₂.srcInv u')) k) = X.tgt (S₁.srcInv u) := by
    rw [X.src_comp _ _ e1, ha₁t]
  have hk's : X.src (X.comp (X.comp (X.inv (S₂.srcInv u')) k) (S₁.srcInv u)) = u := by
    rw [X.src_comp _ _ e2, ha₁s]
  have hk't : X.tgt (X.comp (X.comp (X.inv (S₂.srcInv u')) k) (S₁.srcInv u)) = u' := by
    rw [X.tgt_comp _ _ e2, X.tgt_comp _ _ e1, X.tgt_inv, ha₂s]
  obtain ⟨g, hg, -⟩ := R.existsUnique_Γ (X.comp (X.comp (X.inv (S₂.srcInv u')) k) (S₁.srcInv u))
    (by rw [hk's]; exact hu) (by rw [hk't]; exact hu')
  rw [hk's] at hg
  have hΦ : R.Φ g u = u' := by rw [← R.tgt_Γ g u hu, hg, hk't]
  have hT : ∀ g' : X.Isotropy x, transport R S₁ S₂ g' (X.src k) =
      X.comp (S₂.srcInv (R.Φ g' u)) (X.comp (R.Γ g' u) (X.inv (S₁.srcInv u))) := by
    intro g'
    rw [transport, ← hu_def]
  have hgk : transport R S₁ S₂ g (X.src k) = k := by
    rw [hT, hΦ, hg]
    exact comp_conj_cancel ha₂t ha₁t.symm
  refine ⟨g, hgk, fun g' hg' => ?_⟩
  -- uniqueness: `t` determines `Φ(g') u = u'`, then cancel `a₂` and `a₁⁻¹`
  have hΦ' : R.Φ g' u = u' := by
    have h1 := congrArg X.tgt hg'
    rw [tgt_transport h₁ h₂ g' hs] at h1
    change S₂.hat (R.Φ g' (back S₁ (X.src k))) = X.tgt k at h1
    rw [← hu_def] at h1
    rw [hu'_def, ← h1, back_hat h₂ (R.mapsTo_Φ g' hu)]
  have hc : ∀ g'' : X.Isotropy x, R.Φ g'' u = u' →
      X.src (S₂.srcInv u') = X.tgt (X.comp (R.Γ g'' u) (X.inv (S₁.srcInv u))) := by
    intro g'' hg''
    rw [← hg'']
    exact transport_comp₂ h₁ h₂ hu g''
  have he : X.comp (S₂.srcInv u') (X.comp (R.Γ g' u) (X.inv (S₁.srcInv u))) =
      X.comp (S₂.srcInv u') (X.comp (R.Γ g u) (X.inv (S₁.srcInv u))) := by
    rw [← hΦ', ← hT, hg', ← hgk, hT, hΦ, hΦ']
  have he' := GroupoidStr.comp_left_cancel (hc g' hΦ') (hc g hΦ) he
  have he'' := GroupoidStr.comp_right_cancel (transport_comp₁ h₁ hu g')
    (transport_comp₁ h₁ hu g) he'
  exact (R.Γ_inj hu).1 he''

/-- `Θ_g(z)` determines `g`. -/
theorem transport_injective (h₁ : R.U ⊆ S₁.srcSet) (h₂ : R.U ⊆ S₂.srcSet) {g g' : X.Isotropy x}
    {z : Obj} (hz : z ∈ transportSet R S₁)
    (he : transport R S₁ S₂ g z = transport R S₁ S₂ g' z) : g = g' := by
  have hs : X.src (transport R S₁ S₂ g z) = z := src_transport h₁ h₂ g hz
  have ht : X.tgt (transport R S₁ S₂ g z) ∈ transportSet R S₂ := by
    rw [tgt_transport h₁ h₂ g hz]
    exact (isScDiffeoOn_conjMap h₁ h₂ g).mapsTo hz
  obtain ⟨g₀, -, huniq⟩ := existsUnique_transport h₁ h₂ (by rw [hs]; exact hz) ht
  rw [hs] at huniq
  exact (huniq g rfl).trans (huniq g' he.symm).symm

/-! ### Transporting a natural representation along a morphism -/

/-- The conjugation `G_y → G_x`, `h ↦ γ⁻¹ ∘ h ∘ γ`, for `γ = (s|𝐒)⁻¹(x) : x → y`. -/
def transportConj (hS : R.U ⊆ S.srcSet) {y : Obj} (hy : S.hat x = y) :
    X.Isotropy y ≃* X.Isotropy x :=
  X.isotropyConj (X.inv (S.srcInv x)) (by rw [X.src_inv]; exact hy)
    (by rw [X.tgt_inv]; exact src_srcInv hS R.mem_U)

theorem transportConj_val (hS : R.U ⊆ S.srcSet) {y : Obj} (hy : S.hat x = y)
    (h : X.Isotropy y) :
    (transportConj hS hy h).val = X.comp (X.comp (X.inv (S.srcInv x)) h.val) (S.srcInv x) := by
  simp only [transportConj, GroupoidStr.isotropyConj_val, GroupoidStr.inv_inv]

/-- **A natural representation transported along a morphism** `γ : x → y` (with a sheet `𝐒` of
`γ`, `γ = (s|𝐒)⁻¹(x)`, `U(x) ⊆ s(𝐒)`): on `U(y) = γ̂(U(x))`, `Φ_y(h) = γ̂ ∘ Φ(γ⁻¹ h γ) ∘ γ̂⁻¹`
and `Γ_y(h, z) = Θ_{γ⁻¹ h γ}(z)`. -/
def transportRep (hS : R.U ⊆ S.srcSet) {y : Obj} (hy : S.hat x = y) : X.NaturalRep y where
  U := transportSet R S
  isOpen_U := isOpen_transportSet hS
  isConnected_U := isConnected_transportSet hS
  mem_U := self_mem_transportSet hy
  Φ h := conjMap R S S (transportConj hS hy h)
  Γ h := transport R S S (transportConj hS hy h)
  isScDiffeoOn_Φ h := by
    have := isScDiffeoOn_conjMap hS hS (transportConj hS hy h)
    rwa [← map_inv] at this
  Φ_mul g h z hz := by
    rw [map_mul, conjMap_conjMap hS hS _ _ hz]
  isScSmoothOn_Γ h := isScSmoothOn_transport hS hS _
  Γ_self h := by
    have e : transport R S S (transportConj hS hy h) y =
        transport R S S (transportConj hS hy h) (S.hat x) := by rw [hy]
    rw [e, transport_hat_self hS, transportConj_val]
    exact comp_conj_cancel (hy.trans h.tgt_val.symm) (h.src_val.trans hy.symm)
  src_Γ h z hz := src_transport hS hS _ hz
  tgt_Γ h z hz := tgt_transport hS hS _ hz
  existsUnique_Γ k hs ht := by
    obtain ⟨g, hg, huniq⟩ := existsUnique_transport hS hS hs ht
    refine ⟨(transportConj hS hy).symm g, ?_, fun h hh => ?_⟩
    · change transport R S S (transportConj hS hy ((transportConj hS hy).symm g)) (X.src k) = k
      rw [MulEquiv.apply_symm_apply]
      exact hg
    · rw [← huniq _ hh, MulEquiv.symm_apply_apply]

@[simp]
theorem transportRep_U (hS : R.U ⊆ S.srcSet) {y : Obj} (hy : S.hat x = y) :
    (transportRep hS hy).U = transportSet R S := rfl

theorem transportRep_Φ (hS : R.U ⊆ S.srcSet) {y : Obj} (hy : S.hat x = y) (h : X.Isotropy y) :
    (transportRep hS hy).Φ h = conjMap R S S (transportConj hS hy h) := rfl

theorem transportRep_Γ (hS : R.U ⊆ S.srcSet) {y : Obj} (hy : S.hat x = y) (h : X.Isotropy y) :
    (transportRep hS hy).Γ h = transport R S S (transportConj hS hy h) := rfl

end Transport

/-- **A spoke** for a morphism `φ : x → y`: a natural representation at `x`, with the same `Φ`
and `Γ` as a given one on a smaller connected neighbourhood, and a sheet `𝐒 ∋ φ` with
`U(x) ⊆ s(𝐒)`; `transportRep` then gives a natural representation at `y`. -/
theorem exists_spoke {x : Obj} (R : X.NaturalRep x) {φ : Mor} (hφ : X.src φ = x) :
    ∃ (R' : X.NaturalRep x) (S : X.Sheet), R'.U ⊆ R.U ∧ R'.Φ = R.Φ ∧ R'.Γ = R.Γ ∧
      φ ∈ S.carrier ∧ R'.U ⊆ S.srcSet ∧ S.hat x = X.tgt φ := by
  obtain ⟨S, hφS⟩ := X.exists_sheet φ
  have hxS : x ∈ S.srcSet := hφ ▸ S.isScDiffeoOn_src.mapsTo hφS
  obtain ⟨R', hR'U, hR'Φ, hR'Γ⟩ := X.exists_naturalRep_shrink R S.isScDiffeoOn_src.isOpen_target hxS
  refine ⟨R', S, fun z hz => (hR'U hz).2, hR'Φ, hR'Γ, hφS, fun z hz => (hR'U hz).1, ?_⟩
  change X.tgt (S.srcInv x) = X.tgt φ
  rw [← hφ, S.isScDiffeoOn_src.left_inv φ hφS]

/-! ### The star construction -/

variable (X) in
/-- **The data of the star construction** for Proposition 7.5 (PLAN II.6, 6): a base object `x`,
a natural representation `R` of `G_x`, and for every `y ∈ Y` a sheet `K y` of a morphism
`γ_y : x → y` (`γ_y = (s|K y)⁻¹(x)`) with `U(x) ⊆ s(K y)`, the transported neighbourhoods
`γ̂_y(U(x))` contained in `V` and pairwise disjoint. -/
structure Star (Y : Finset Obj) (V : Set Obj) where
  /-- The base object. -/
  x : Obj
  /-- The natural representation at the base object. -/
  R : X.NaturalRep x
  /-- The sheets `K y` of the morphisms `γ_y : x → y`. -/
  K : Obj → X.Sheet
  subset_srcSet : ∀ y ∈ Y, R.U ⊆ (K y).srcSet
  hat_self : ∀ y ∈ Y, (K y).hat x = y
  transportSet_subset : ∀ y ∈ Y, transportSet R (K y) ⊆ V
  pairwiseDisjoint : (Y : Set Obj).PairwiseDisjoint fun y => transportSet R (K y)

namespace Star

variable {Y : Finset Obj} {V : Set Obj} (D : Star X Y V)

/-- `γ_y = (s|K y)⁻¹(x) : x → y`. -/
def γ (y : Obj) : Mor := (D.K y).srcInv D.x

theorem src_γ {y : Obj} (hy : y ∈ Y) : X.src (D.γ y) = D.x :=
  src_srcInv (D.subset_srcSet y hy) D.R.mem_U

theorem tgt_γ {y : Obj} (hy : y ∈ Y) : X.tgt (D.γ y) = y := D.hat_self y hy

open scoped Classical in
/-- **The isotropy element of a morphism** `ψ : y → y'` of `Y`: `g_ψ = γ_{y'}⁻¹ ∘ ψ ∘ γ_y ∈ G_x`
(`1` off the morphisms of `Y`). -/
def g (ψ : Mor) : X.Isotropy D.x :=
  if hψ : ψ ∈ X.morOn (Y : Set Obj) then
    ⟨X.comp (X.comp (X.inv (D.γ (X.tgt ψ))) ψ) (D.γ (X.src ψ)),
      (src_conj (D.tgt_γ hψ.2) (D.tgt_γ hψ.1)).trans (D.src_γ hψ.1),
      (tgt_conj (D.tgt_γ hψ.2) (D.tgt_γ hψ.1)).trans (D.src_γ hψ.2)⟩
  else 1

theorem val_g {ψ : Mor} (hψ : ψ ∈ X.morOn (Y : Set Obj)) :
    (D.g ψ).val = X.comp (X.comp (X.inv (D.γ (X.tgt ψ))) ψ) (D.γ (X.src ψ)) := by
  rw [g, dif_pos hψ]

/-- `g_{φ ∘ ψ} = g_φ g_ψ`. -/
theorem g_comp {φ ψ : Mor} (hφ : φ ∈ X.morOn (Y : Set Obj)) (hψ : ψ ∈ X.morOn (Y : Set Obj))
    (hc : X.src φ = X.tgt ψ) : D.g (X.comp φ ψ) = D.g φ * D.g ψ := by
  have hφψ : X.comp φ ψ ∈ X.morOn (Y : Set Obj) :=
    ⟨by rw [X.src_comp _ _ hc]; exact hψ.1, by rw [X.tgt_comp _ _ hc]; exact hφ.2⟩
  ext
  rw [GroupoidStr.Isotropy.val_mul, D.val_g hφψ, D.val_g hφ, D.val_g hψ, X.src_comp _ _ hc,
    X.tgt_comp _ _ hc, hc]
  exact (conj_comp_conj (D.tgt_γ hφ.2) ((D.tgt_γ hψ.2).trans hc.symm) hc
    (D.tgt_γ hψ.1)).symm

/-- `g_{1_y} = 1`. -/
theorem g_unit {y : Obj} (hy : y ∈ Y) : D.g (X.unit y) = 1 := by
  have hu : X.unit y ∈ X.morOn (Y : Set Obj) :=
    ⟨by rw [X.src_unit]; exact hy, by rw [X.tgt_unit]; exact hy⟩
  ext
  rw [D.val_g hu, X.src_unit, X.tgt_unit, GroupoidStr.Isotropy.val_one,
    GroupoidStr.comp_unit_of_eq (by rw [X.src_inv, D.tgt_γ hy]), X.inv_comp, D.src_γ hy]

/-- `g_{ψ⁻¹} = g_ψ⁻¹`. -/
theorem g_inv {ψ : Mor} (hψ : ψ ∈ X.morOn (Y : Set Obj)) : D.g (X.inv ψ) = (D.g ψ)⁻¹ := by
  have hi : X.inv ψ ∈ X.morOn (Y : Set Obj) :=
    ⟨by rw [X.src_inv]; exact hψ.2, by rw [X.tgt_inv]; exact hψ.1⟩
  have h := D.g_comp hi hψ (X.src_inv ψ)
  rw [X.inv_comp, D.g_unit hψ.1] at h
  exact eq_inv_of_mul_eq_one_left h.symm

/-- **The functor** on morphisms: `f(ψ) = γ̂_{y'} ∘ Φ(g_ψ) ∘ γ̂_y⁻¹ : U(y) → U(y')`. -/
def F (ψ : Mor) : Obj → Obj := conjMap D.R (D.K (X.src ψ)) (D.K (X.tgt ψ)) (D.g ψ)

/-- **The section** `(s|𝐔(ψ))⁻¹ = Θ_{g_ψ} : U(y) → 𝐔(ψ)`. -/
def Θ (ψ : Mor) : Obj → Mor := transport D.R (D.K (X.src ψ)) (D.K (X.tgt ψ)) (D.g ψ)

/-- **The component** `𝐔(ψ) = Θ_{g_ψ}(U(y))`. -/
def sheet (ψ : Mor) : Set Mor := D.Θ ψ '' transportSet D.R (D.K (X.src ψ))

theorem Θ_src {ψ : Mor} (hψ : ψ ∈ X.morOn (Y : Set Obj)) : D.Θ ψ (X.src ψ) = ψ := by
  have e : D.Θ ψ (X.src ψ) = D.Θ ψ ((D.K (X.src ψ)).hat D.x) := by
    rw [D.hat_self _ hψ.1]
  rw [e, Θ, transport_hat_self (D.subset_srcSet _ hψ.1), D.val_g hψ]
  exact comp_conj_cancel (D.tgt_γ hψ.2) (D.tgt_γ hψ.1).symm

theorem mem_sheet {ψ : Mor} (hψ : ψ ∈ X.morOn (Y : Set Obj)) : ψ ∈ D.sheet ψ :=
  ⟨X.src ψ, self_mem_transportSet (D.hat_self _ hψ.1), D.Θ_src hψ⟩

theorem F_inv {ψ : Mor} (hψ : ψ ∈ X.morOn (Y : Set Obj)) :
    D.F (X.inv ψ) = conjMap D.R (D.K (X.tgt ψ)) (D.K (X.src ψ)) (D.g ψ)⁻¹ := by
  rw [F, X.src_inv, X.tgt_inv, D.g_inv hψ]

theorem isScDiffeoOn_F {ψ : Mor} (hψ : ψ ∈ X.morOn (Y : Set Obj)) :
    X.PObj.IsScDiffeoOn X.PObj (D.F ψ) (D.F (X.inv ψ)) (transportSet D.R (D.K (X.src ψ)))
      (transportSet D.R (D.K (X.tgt ψ))) := by
  rw [D.F_inv hψ]
  exact isScDiffeoOn_conjMap (D.subset_srcSet _ hψ.1) (D.subset_srcSet _ hψ.2) (D.g ψ)

theorem F_comp {φ ψ : Mor} (hφ : φ ∈ X.morOn (Y : Set Obj)) (hψ : ψ ∈ X.morOn (Y : Set Obj))
    (hc : X.src φ = X.tgt ψ) {z : Obj} (hz : z ∈ transportSet D.R (D.K (X.src ψ))) :
    D.F (X.comp φ ψ) z = D.F φ (D.F ψ z) := by
  rw [F, F, F, X.src_comp _ _ hc, X.tgt_comp _ _ hc, D.g_comp hφ hψ hc, hc,
    conjMap_conjMap (D.subset_srcSet _ hψ.1) (D.subset_srcSet _ hψ.2) _ _ hz]

theorem F_unit {y : Obj} (hy : y ∈ Y) {z : Obj} (hz : z ∈ transportSet D.R (D.K y)) :
    D.F (X.unit y) z = z := by
  rw [F, X.src_unit, X.tgt_unit, D.g_unit hy, conjMap_one (D.subset_srcSet y hy) hz]

theorem src_Θ {ψ : Mor} (hψ : ψ ∈ X.morOn (Y : Set Obj)) {z : Obj}
    (hz : z ∈ transportSet D.R (D.K (X.src ψ))) : X.src (D.Θ ψ z) = z :=
  src_transport (D.subset_srcSet _ hψ.1) (D.subset_srcSet _ hψ.2) _ hz

theorem tgt_Θ {ψ : Mor} (hψ : ψ ∈ X.morOn (Y : Set Obj)) {z : Obj}
    (hz : z ∈ transportSet D.R (D.K (X.src ψ))) : X.tgt (D.Θ ψ z) = D.F ψ z :=
  tgt_transport (D.subset_srcSet _ hψ.1) (D.subset_srcSet _ hψ.2) _ hz

theorem isScSmoothOn_Θ {ψ : Mor} (hψ : ψ ∈ X.morOn (Y : Set Obj)) :
    X.PObj.IsScSmoothOn X.PMor (D.Θ ψ) (transportSet D.R (D.K (X.src ψ))) :=
  isScSmoothOn_transport (D.subset_srcSet _ hψ.1) (D.subset_srcSet _ hψ.2) _

/-- The components `𝐔(ψ)` are pairwise disjoint. -/
theorem pairwiseDisjoint_sheet : (X.morOn (Y : Set Obj)).PairwiseDisjoint D.sheet := by
  intro ψ hψ ψ' hψ' hne
  change Disjoint (D.sheet ψ) (D.sheet ψ')
  refine disjoint_left.2 ?_
  rintro k ⟨z, hz, rfl⟩ ⟨z', hz', he⟩
  apply hne
  have hzz : z' = z := by rw [← D.src_Θ hψ' hz', he, D.src_Θ hψ hz]
  subst hzz
  have hs : X.src ψ = X.src ψ' := by
    by_contra hne'
    exact disjoint_left.1 (D.pairwiseDisjoint hψ.1 hψ'.1 hne') hz hz'
  have hk : X.tgt (D.Θ ψ z') ∈ transportSet D.R (D.K (X.tgt ψ)) := by
    rw [D.tgt_Θ hψ hz]
    exact (D.isScDiffeoOn_F hψ).mapsTo hz
  have hk' : X.tgt (D.Θ ψ z') ∈ transportSet D.R (D.K (X.tgt ψ')) := by
    rw [← he, D.tgt_Θ hψ' hz']
    exact (D.isScDiffeoOn_F hψ').mapsTo hz'
  have ht : X.tgt ψ = X.tgt ψ' := by
    by_contra hne'
    exact disjoint_left.1 (D.pairwiseDisjoint hψ.2 hψ'.2 hne') hk hk'
  have he' : transport D.R (D.K (X.src ψ)) (D.K (X.tgt ψ)) (D.g ψ') z' =
      transport D.R (D.K (X.src ψ)) (D.K (X.tgt ψ)) (D.g ψ) z' := by
    have h0 := he
    unfold Θ at h0
    rw [← hs, ← ht] at h0
    exact h0
  have hg := transport_injective (D.subset_srcSet _ hψ.1) (D.subset_srcSet _ hψ.2) hz he'
  calc ψ = D.Θ ψ (X.src ψ) := (D.Θ_src hψ).symm
    _ = transport D.R (D.K (X.src ψ')) (D.K (X.tgt ψ')) (D.g ψ') (X.src ψ') := by
      rw [Θ, ← hg, hs, ht]
    _ = ψ' := D.Θ_src hψ'

/-- The components `𝐔(ψ)` cover the morphisms between points of `⋃_y U(y)`. -/
theorem morOn_eq :
    X.morOn (⋃ y ∈ Y, transportSet D.R (D.K y)) = ⋃ ψ ∈ X.morOn (Y : Set Obj), D.sheet ψ := by
  ext k
  constructor
  · rintro ⟨hs, ht⟩
    obtain ⟨y, hy, hks⟩ := mem_iUnion₂.1 hs
    obtain ⟨y', hy', hkt⟩ := mem_iUnion₂.1 ht
    have h₁ := D.subset_srcSet y hy
    have h₂ := D.subset_srcSet y' hy'
    obtain ⟨g, hg, -⟩ := existsUnique_transport h₁ h₂ hks hkt
    obtain ⟨ψ, hψdef⟩ : ∃ ψ, ψ = transport D.R (D.K y) (D.K y') g y := ⟨_, rfl⟩
    have hyT : y ∈ transportSet D.R (D.K y) := self_mem_transportSet (D.hat_self y hy)
    have hψs : X.src ψ = y := by rw [hψdef]; exact src_transport h₁ h₂ g hyT
    have hψt : X.tgt ψ = y' := by
      rw [hψdef, tgt_transport h₁ h₂ g hyT]
      exact conjMap_self h₁ (D.hat_self y hy) (D.hat_self y' hy') g
    have hψ : ψ ∈ X.morOn (Y : Set Obj) := ⟨hψs ▸ hy, hψt ▸ hy'⟩
    have hgψ : D.g ψ = g := by
      have e := D.Θ_src hψ
      rw [Θ, hψs, hψt] at e
      exact transport_injective h₁ h₂ hyT (e.trans hψdef)
    refine mem_iUnion₂.2 ⟨ψ, hψ, X.src k, ?_, ?_⟩
    · rw [hψs]
      exact hks
    · rw [Θ, hψs, hψt, hgψ]
      exact hg
  · intro hk
    obtain ⟨ψ, hψ, z, hz, rfl⟩ := mem_iUnion₂.1 hk
    refine ⟨mem_iUnion₂.2 ⟨_, hψ.1, ?_⟩, mem_iUnion₂.2 ⟨_, hψ.2, ?_⟩⟩
    · rw [D.src_Θ hψ hz]
      exact hz
    · rw [D.tgt_Θ hψ hz]
      exact (D.isScDiffeoOn_F hψ).mapsTo hz

/-- The isotropy element of `h ∈ G_y` is its conjugate `γ_y⁻¹ h γ_y`. -/
theorem g_isotropy {y : Obj} (hy : y ∈ Y) (h : X.Isotropy y) :
    D.g h.val = transportConj (D.subset_srcSet y hy) (D.hat_self y hy) h := by
  have hh : h.val ∈ X.morOn (Y : Set Obj) :=
    ⟨by rw [h.src_val]; exact hy, by rw [h.tgt_val]; exact hy⟩
  ext
  rw [D.val_g hh, transportConj_val, h.src_val, h.tgt_val]
  rfl

/-- **The natural representation of `Y`** (Definition 7.8) built from the star data. -/
def toNaturalRepFinite : X.NaturalRepFinite Y V where
  U y := transportSet D.R (D.K y)
  F := D.F
  sheet := D.sheet
  srcInv := D.Θ
  isOpen_U y hy := isOpen_transportSet (D.subset_srcSet y hy)
  isConnected_U y hy := isConnected_transportSet (D.subset_srcSet y hy)
  mem_U y hy := self_mem_transportSet (D.hat_self y hy)
  U_subset := D.transportSet_subset
  pairwiseDisjoint_U := D.pairwiseDisjoint
  isScDiffeoOn_F _ hψ := D.isScDiffeoOn_F hψ
  F_comp _ hφ _ hψ hc _ hz := D.F_comp hφ hψ hc hz
  F_unit _ hy _ hz := D.F_unit hy hz
  isOpen_sheet _ hψ := (isScDiffeoOn_src_image_of_section (D.isScSmoothOn_Θ hψ)
    fun _ hz => D.src_Θ hψ hz).isOpen_source
  isConnected_sheet _ hψ := (isConnected_transportSet (D.subset_srcSet _ hψ.1)).image _
    (D.isScSmoothOn_Θ hψ).continuousOn
  mem_sheet _ hψ := D.mem_sheet hψ
  pairwiseDisjoint_sheet := D.pairwiseDisjoint_sheet
  morOn_eq := D.morOn_eq
  isScDiffeoOn_src _ hψ :=
    isScDiffeoOn_src_image_of_section (D.isScSmoothOn_Θ hψ) fun _ hz => D.src_Θ hψ hz
  isScDiffeoOn_tgt _ hψ := ⟨_, isScDiffeoOn_tgt_image_of_section (D.isScSmoothOn_Θ hψ)
    (fun _ hz => D.src_Θ hψ hz) (D.isScDiffeoOn_F hψ) fun _ hz => D.tgt_Θ hψ hz⟩
  F_eq _ hψ _ hz := (D.tgt_Θ hψ hz).symm
  natural y hy := ⟨transportRep (D.subset_srcSet y hy) (D.hat_self y hy), rfl, fun h z _ => by
    rw [transportRep_Φ, ← D.g_isotropy hy h]
    change _ = conjMap D.R (D.K (X.src h.val)) (D.K (X.tgt h.val)) (D.g h.val) z
    rw [h.src_val, h.tgt_val]⟩

end Star

/-- **The star data exist** for a finite set `Y` of objects isomorphic to `x` and an open
`V ⊇ Y`: choose `γ_y : x → y` with sheets `K y`, pairwise disjoint open `W_y ∋ y`, and a natural
representation of `G_x` on `U(x) ⊆ ⋂_y s(K y) ∩ γ̂_y⁻¹(W_y ∩ V)` (Theorem 7.1). -/
theorem exists_star {Y : Finset Obj} {V : Set Obj} (hV : IsOpen V) (hYV : (Y : Set Obj) ⊆ V)
    {x : Obj} (hx : ∀ y ∈ Y, X.Isomorphic x y) : Nonempty (Star X Y V) := by
  have key : ∀ y : Obj, ∃ S : X.Sheet, y ∈ Y → x ∈ S.srcSet ∧ S.hat x = y := by
    intro y
    by_cases hy : y ∈ Y
    · obtain ⟨φ, hφs, hφt⟩ := hx y hy
      obtain ⟨S, hφS⟩ := X.exists_sheet φ
      refine ⟨S, fun _ => ⟨hφs ▸ S.isScDiffeoOn_src.mapsTo hφS, ?_⟩⟩
      change X.tgt (S.srcInv x) = y
      rw [← hφs, S.isScDiffeoOn_src.left_inv φ hφS, hφt]
    · exact ⟨X.sheetAt (X.unit x), fun h => absurd h hy⟩
  choose K hK using key
  obtain ⟨W, hW, hWdisj⟩ := Y.finite_toSet.t2_separation
  have hU₀ : IsOpen (⋂ y ∈ Y, ((K y).srcSet ∩ (K y).hat ⁻¹' (W y ∩ V))) :=
    isOpen_biInter_finset fun y _ =>
      (K y).isScDiffeoOn_hat.isScSmoothOn.continuousOn.isOpen_inter_preimage
        (K y).isScDiffeoOn_src.isOpen_target ((hW y).2.inter hV)
  have hxU₀ : x ∈ ⋂ y ∈ Y, ((K y).srcSet ∩ (K y).hat ⁻¹' (W y ∩ V)) :=
    mem_iInter₂.2 fun y hy => ⟨(hK y hy).1, by
      rw [mem_preimage, (hK y hy).2]
      exact ⟨(hW y).1, hYV hy⟩⟩
  obtain ⟨R, hRU⟩ := theorem_7_1 X x hU₀ hxU₀
  have hR : ∀ y ∈ Y, ∀ u ∈ R.U, u ∈ (K y).srcSet ∧ (K y).hat u ∈ W y ∩ V :=
    fun y hy u hu => mem_iInter₂.1 (hRU hu) y hy
  refine ⟨⟨x, R, K, fun y hy u hu => (hR y hy u hu).1, fun y hy => (hK y hy).2, ?_, ?_⟩⟩
  · rintro y hy _ ⟨u, hu, rfl⟩
    exact (hR y hy u hu).2.2
  · refine hWdisj.mono_on fun y hy => ?_
    rintro _ ⟨u, hu, rfl⟩
    exact (hR y hy u hu).2.1

/-- A natural representation of the empty set. -/
def emptyNaturalRepFinite (V : Set Obj) : X.NaturalRepFinite ∅ V where
  U _ := ∅
  F _ := id
  sheet _ := ∅
  srcInv _ := X.unit
  isOpen_U _ h := (Finset.notMem_empty _ h).elim
  isConnected_U _ h := (Finset.notMem_empty _ h).elim
  mem_U _ h := (Finset.notMem_empty _ h).elim
  U_subset _ h := (Finset.notMem_empty _ h).elim
  pairwiseDisjoint_U := by
    rw [Finset.coe_empty]
    exact pairwiseDisjoint_empty
  isScDiffeoOn_F _ h := (Finset.notMem_empty _ h.1).elim
  F_comp _ h := (Finset.notMem_empty _ h.1).elim
  F_unit _ h := (Finset.notMem_empty _ h).elim
  isOpen_sheet _ h := (Finset.notMem_empty _ h.1).elim
  isConnected_sheet _ h := (Finset.notMem_empty _ h.1).elim
  mem_sheet _ h := (Finset.notMem_empty _ h.1).elim
  pairwiseDisjoint_sheet := fun _ h => (Finset.notMem_empty _ h.1).elim
  morOn_eq := by
    ext ψ
    simp [GroupoidStr.morOn]
  isScDiffeoOn_src _ h := (Finset.notMem_empty _ h.1).elim
  isScDiffeoOn_tgt _ h := (Finset.notMem_empty _ h.1).elim
  F_eq _ h := (Finset.notMem_empty _ h.1).elim
  natural _ h := (Finset.notMem_empty _ h).elim

/-- A natural representation on neighbourhoods contained in `V` is one on neighbourhoods
contained in any `V' ⊇ V`. -/
def mono {Y : Finset Obj} {V V' : Set Obj} (N : X.NaturalRepFinite Y V) (h : V ⊆ V') :
    X.NaturalRepFinite Y V' :=
  { N with U_subset := fun y hy => (N.U_subset y hy).trans h }

/-- **The `𝐔(ψ)` are the connected components** of the morphism set `𝐔` of `⋃_y U(y)` (the text's
"decomposes into union of connected components `𝐔(ψ)`"), for every natural representation. -/
theorem connectedComponentIn_morOn {Y : Finset Obj} {V : Set Obj} (N : X.NaturalRepFinite Y V)
    {ψ : Mor} (hψ : ψ ∈ X.morOn (Y : Set Obj)) {φ : Mor} (hφ : φ ∈ N.sheet ψ) :
    connectedComponentIn (X.morOn (⋃ y ∈ Y, N.U y)) φ = N.sheet ψ := by
  have hsub : N.sheet ψ ⊆ X.morOn (⋃ y ∈ Y, N.U y) := by
    rw [N.morOn_eq]
    exact subset_biUnion_of_mem (u := N.sheet) hψ
  refine Subset.antisymm ?_
    ((N.isConnected_sheet ψ hψ).isPreconnected.subset_connectedComponentIn hφ hsub)
  refine isPreconnected_connectedComponentIn.subset_left_of_subset_union (N.isOpen_sheet ψ hψ)
    (v := ⋃ ψ' ∈ {ψ' | ψ' ∈ X.morOn (Y : Set Obj) ∧ ψ' ≠ ψ}, N.sheet ψ')
    (isOpen_biUnion fun ψ' hψ' => N.isOpen_sheet ψ' hψ'.1)
    (disjoint_iUnion₂_right.2 fun ψ' hψ' => N.pairwiseDisjoint_sheet hψ hψ'.1 (Ne.symm hψ'.2))
    (fun φ' hφ' => ?_) ⟨φ, mem_connectedComponentIn (hsub hφ), hφ⟩
  have hφ'' := connectedComponentIn_subset _ _ hφ'
  rw [N.morOn_eq] at hφ''
  obtain ⟨ψ', hψ', hk⟩ := mem_iUnion₂.1 hφ''
  by_cases hψψ : ψ' = ψ
  · exact Or.inl (hψψ ▸ hk)
  · exact Or.inr (mem_iUnion₂.2 ⟨ψ', ⟨hψ', hψψ⟩, hk⟩)

end NatRepFinite

/-! ### Proposition 7.5 -/

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **Proposition 7.5** (natural representation of a finite set of isomorphic objects, p. 233):
for a finite set `Y` of mutually isomorphic objects and an open `V ⊇ Y` there is a natural
representation of `Y` on neighbourhoods contained in `V` (Definition 7.8): mutually disjoint
connected open `U(y) ⊆ V`, a functor `ψ ↦ f(ψ)` to sc-diffeomorphisms `U(y) → U(y')`, and the
morphisms between points of `⋃ U(y)` decomposing into connected components `𝐔(ψ)` with
(1) the natural action of `G_y` on `U(y)`, (2) `s, t : 𝐔(ψ) → U(y), U(y')` sc-diffeomorphisms,
(3) `f(ψ) = t ∘ (s|𝐔(ψ))⁻¹`. -/
theorem proposition_7_5 (Y : Finset Obj) (hY : ∀ y ∈ Y, ∀ y' ∈ Y, X.Isomorphic y y')
    {V : Set Obj} (hV : IsOpen V) (hYV : (Y : Set Obj) ⊆ V) :
    Nonempty (X.NaturalRepFinite Y V) := by
  rcases Y.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact ⟨NatRepFinite.emptyNaturalRepFinite V⟩
  · obtain ⟨D⟩ := NatRepFinite.exists_star hV hYV fun y hy => hY x hx y hy
    exact ⟨D.toNaturalRepFinite⟩

/-- **Proposition 7.5** for a neighbourhood `V` of `Y` (`V ∈ 𝓝ˢ Y`), as the text states it. -/
theorem proposition_7_5_of_mem_nhdsSet (Y : Finset Obj) (hY : ∀ y ∈ Y, ∀ y' ∈ Y, X.Isomorphic y y')
    {V : Set Obj} (hV : V ∈ 𝓝ˢ (Y : Set Obj)) : Nonempty (X.NaturalRepFinite Y V) := by
  obtain ⟨W, hWo, hYW, hWV⟩ := mem_nhdsSet_iff_exists.1 hV
  obtain ⟨N⟩ := X.proposition_7_5 Y hY hWo hYW
  exact ⟨NatRepFinite.mono N hWV⟩

end EpGroupoid

end Polyfold
