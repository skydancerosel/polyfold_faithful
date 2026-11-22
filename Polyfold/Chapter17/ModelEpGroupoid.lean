import Polyfold.Chapter17.TransitionProperness
import Polyfold.Chapter8.SigmaPolyfold

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.1 (pp. 752–753): the small category `X_Ψ` of a family of uniformizers (the paragraph after
(17.7), p. 752) and **Theorem 17.1.14** (`X_Ψ` is an ep-groupoid, tame if `(F, M)` is tame).
Numbers and pages are the 2021 text's.

# The sc-smooth model `X_Ψ`

## The text, paraphrased

(p. 752) For a covering family `Ψ = (Ψ_λ)_{λ ∈ Λ}` of uniformizers of a polyfold construction
`(F, M)`, the text forms the M-polyfolds `X = ⊔_λ O_λ` and `𝐗 = ⊔_{(λ, λ')} M(Ψ_λ, Ψ_λ')` (17.7),
with `s(q_λ, φ, q_λ') = q_λ`, `t(q_λ, φ, q_λ') = q_λ'`.  These are local sc-diffeomorphisms since
`(F, M)` is a polyfold structure; "it follows immediately" that the inversion
`(q_λ, φ, q_λ') ↦ (q_λ', φ⁻¹, q_λ)` is an sc-diffeomorphism, the unit map is sc-smooth, `𝐗 ₛ×ₜ 𝐗`
has a natural M-polyfold structure, and the multiplication is sc-smooth.  (Theorem 17.1.14,
p. 753) `X_Ψ` has the structure of an ep-groupoid, tame if `(F, M)` is tame.  *Proof*: only the
properness has to be checked.  At `q_{λ₀}` take `U(q_{λ₀})` from Proposition 17.1.11, so that every
`t : s⁻¹(cl U(q_{λ₀})) → O_λ` of `M(Ψ_{λ₀}, Ψ_λ)` is proper; then `t : s⁻¹(cl_X U) → X` is proper,
since a sequence with targets in a compact set may be taken in one `M(Ψ_{λ₀}, Ψ_λ')`.

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* `GroupoidStr.pullback G f` (the groupoid `f^*G` on `O` with morphisms the transition set
  `G.TransitionSet f f` of Definition 17.1.5) and `GroupoidStr.ofEquiv` (a groupoid transported
  along a bijection of the morphism sets).
* For a family `Ψ : ι → S.Unif`: `ModelObj Ψ = Σ λ, O_λ`, `ModelMor Ψ = Σ (λ, λ'), M(Ψ_λ, Ψ_λ')`
  (17.7), `modelObjMap` (`q_λ ↦ Ψ_λ(q_λ)`), `modelMorEquiv` (`𝐗` is the transition set of
  `X → C ← X`), the groupoid `modelGroupoid`, the M-polyfolds `modelObjPolyfold`,
  `modelMorPolyfold` (`MPolyfold.sigma`).
* The paragraph of p. 752: `isLocalScDiffeo_modelSrc`, `isLocalScDiffeo_modelTgt`,
  `isScSmoothMap_modelUnit`, `isScDiffeoOn_modelInv` (the inversion is an sc-diffeomorphism),
  `isScSmoothCompSheet_model` and `isScSmoothComp_model` (the multiplication is sc-smooth on
  `𝐗 ₛ×ₜ 𝐗`).
* The properness: `exists_isProperMap_model`, from Proposition 17.1.11 and the general
  `isProperMap_domRestrict_sigmaMap` (a map between disjoint unions that is proper on each piece
  is proper).
* `modelEpGroupoid Ψ`, `modelEP Ψ : EP` and **Theorem 17.1.14** (`theorem_17_1_14`), with the
  tame part `isTame_modelEpGroupoid`.
* Witnesses (`ModelExamples.lean`): the model of the reflection construction on `ℤ/2 ⋉ ℝ` for
  the family with two copies of the reflection uniformizer.

## Readings

* The text forms `X_Ψ` for a covering family; the ep-groupoid structure does not use the covering
  condition, so it is built for any family `Ψ : ι → S.Unif` (the covering condition enters
  Lemma 17.1.15, `ModelEquivalence.lean`).
* The morphisms of `X_Ψ` are the disjoint union of (17.7); the composition of two composable
  morphisms `(q_λ', φ', q_λ'')`, `(q_λ, φ, q_λ')` is `(q_λ, φ' ∘ φ, q_λ'')` (Definition 17.1.5's
  `m`).  It is defined on all pairs by `GroupoidStr.pullback` (the first argument off the
  composable pairs, as everywhere in the formalization of Chapter 7).
* "`𝐗 ₛ×ₜ 𝐗` has a natural M-polyfold structure" is the sub-M-polyfold structure of
  Proposition 2.5.20; the sc-smoothness of the multiplication is proved through its sheet form
  (`isScSmoothComp_iff_sheet`), piece by piece from Definition 17.1.8 (c).
* The text's sequence argument for the properness is replaced by the characterization of proper
  maps as closed maps with compact fibres; the neighbourhood is `U = U(q_{λ₀}) ⊂ O_{λ₀} ⊂ X`, as
  in the text.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-! ### Pulling back and transporting groupoid structures -/

namespace GroupoidStr

variable {Obj Mor Mor' : Type u}

/-- **A groupoid transported along a bijection** `e : Mor' ≃ Mor` of the morphism sets. -/
def ofEquiv (G : GroupoidStr Obj Mor) (e : Mor' ≃ Mor) : GroupoidStr Obj Mor' where
  src φ := G.src (e φ)
  tgt φ := G.tgt (e φ)
  comp φ ψ := e.symm (G.comp (e φ) (e ψ))
  unit x := e.symm (G.unit x)
  inv φ := e.symm (G.inv (e φ))
  src_comp φ ψ h := by simp only [Equiv.apply_symm_apply]; exact G.src_comp _ _ h
  tgt_comp φ ψ h := by simp only [Equiv.apply_symm_apply]; exact G.tgt_comp _ _ h
  comp_assoc φ ψ χ h₁ h₂ := by
    simp only [Equiv.apply_symm_apply]
    rw [G.comp_assoc _ _ _ h₁ h₂]
  src_unit x := by simp
  tgt_unit x := by simp
  comp_unit φ := by simp
  unit_comp φ := by simp
  src_inv φ := by simp
  tgt_inv φ := by simp
  comp_inv φ := by simp
  inv_comp φ := by simp

variable (G : GroupoidStr Obj Mor) {O : Type u} (f : O → Obj)

open scoped Classical in
/-- **The pullback groupoid** `f^*G` on `O`: the morphisms `x → y` are the morphisms `f(x) → f(y)`
of `G`, i.e. the transition set `M(f, f)` of Definition 17.1.5 with its unit, inversion and
multiplication (p. 746); the composition is the first argument off the composable pairs. -/
def pullback : GroupoidStr O (G.TransitionSet f f) where
  src := TransitionSet.src
  tgt := TransitionSet.tgt
  comp a b := if h : G.src a.mor = G.tgt b.mor then TransitionSet.comp a b h else a
  unit := TransitionSet.unit
  inv := TransitionSet.inv
  src_comp a b h := by rw [dif_pos (TransitionSet.mor_composable_of_src_eq_tgt h)]; rfl
  tgt_comp a b h := by rw [dif_pos (TransitionSet.mor_composable_of_src_eq_tgt h)]; rfl
  comp_assoc a b c h₁ h₂ := by
    have hab := TransitionSet.mor_composable_of_src_eq_tgt h₁
    have hbc := TransitionSet.mor_composable_of_src_eq_tgt h₂
    have h₃ : G.src (TransitionSet.comp a b hab).mor = G.tgt c.mor := by
      rw [TransitionSet.mor_comp, G.src_comp _ _ hab, hbc]
    have h₄ : G.src a.mor = G.tgt (TransitionSet.comp b c hbc).mor := by
      rw [TransitionSet.mor_comp, G.tgt_comp _ _ hbc, hab]
    simp only [dif_pos hab, dif_pos hbc, dif_pos h₃, dif_pos h₄]
    exact TransitionSet.comp_assoc a b c hab hbc
  src_unit _ := rfl
  tgt_unit _ := rfl
  comp_unit a := by
    have h : G.src a.mor = G.tgt (TransitionSet.unit a.src : G.TransitionSet f f).mor := by
      rw [TransitionSet.mor_unit, G.tgt_unit, a.src_mor]
    simp only [dif_pos h]
    exact TransitionSet.comp_unit a
  unit_comp a := by
    have h : G.src (TransitionSet.unit a.tgt : G.TransitionSet f f).mor = G.tgt a.mor := by
      rw [TransitionSet.mor_unit, G.src_unit, a.tgt_mor]
    simp only [dif_pos h]
    exact TransitionSet.unit_comp a
  src_inv _ := rfl
  tgt_inv _ := rfl
  comp_inv a := by
    have h : G.src a.mor = G.tgt a.inv.mor := by rw [TransitionSet.mor_inv, G.tgt_inv]
    simp only [dif_pos h]
    exact TransitionSet.comp_inv a
  inv_comp a := by
    have h : G.src a.inv.mor = G.tgt a.mor := by rw [TransitionSet.mor_inv, G.src_inv]
    simp only [dif_pos h]
    exact TransitionSet.inv_comp a

theorem pullback_comp_of {a b : G.TransitionSet f f} (h : G.src a.mor = G.tgt b.mor) :
    (G.pullback f).comp a b = TransitionSet.comp a b h := by
  simp only [pullback, dif_pos h]

end GroupoidStr

/-! ### Proper maps between disjoint unions -/

section ProperSigma

variable {K J : Type*} {A : K → Type*} {B : J → Type*} [∀ k, TopologicalSpace (A k)]
  [∀ j, TopologicalSpace (B j)]

/-- **A map between disjoint unions which is proper on every piece is proper**: for
`τ : K → J`, `f k : A k → B (τ k)` continuous and `D ⊆ Σ k, A k` such that the pieces of `D`
over the same `j` coincide, `Sigma.map τ f` restricted to `D` is proper if every restriction
`f k : D ∩ A k → B (τ k)` is. -/
theorem isProperMap_domRestrict_sigmaMap (τ : K → J) (f : ∀ k, A k → B (τ k))
    (hfc : ∀ k, Continuous (f k)) (D : Set (Σ k, A k))
    (hτ : ∀ k k', (Sigma.mk k ⁻¹' D).Nonempty → (Sigma.mk k' ⁻¹' D).Nonempty → τ k = τ k' →
      k = k')
    (hf : ∀ k, IsProperMap ((Sigma.mk k ⁻¹' D).domRestrict (f k))) :
    IsProperMap (D.domRestrict (Sigma.map τ f)) := by
  -- the inclusion of the `k`-th piece of `D` into `D`
  let incl : ∀ k, (Sigma.mk k ⁻¹' D) → D := fun k a => ⟨⟨k, a.1⟩, a.2⟩
  have hincl : ∀ k, Continuous (incl k) := fun k =>
    (continuous_sigmaMk.comp continuous_subtype_val).subtype_mk _
  have hcomp : ∀ k (a : Sigma.mk k ⁻¹' D),
      D.domRestrict (Sigma.map τ f) (incl k a) = ⟨τ k, f k a.1⟩ := fun _ _ => rfl
  -- every element of `D` comes from a piece
  have hsurj : ∀ z : D, ∃ k a, z = incl k a := by
    rintro ⟨⟨k, a⟩, hz⟩
    exact ⟨k, ⟨a, hz⟩, rfl⟩
  -- the preimage of the `j`-th piece of the target
  have hpre : ∀ (Z : Set D) (j : J), Sigma.mk j ⁻¹' (D.domRestrict (Sigma.map τ f) '' Z) ⊆
      ⋃ (k) (hk : τ k = j), (fun y => hk ▸ y) '' ((Sigma.mk k ⁻¹' D).domRestrict (f k) ''
        (incl k ⁻¹' Z)) := by
    intro Z j y ⟨z, hz, hzy⟩
    obtain ⟨k, a, rfl⟩ := hsurj z
    rw [hcomp] at hzy
    obtain ⟨hk, hy⟩ := Sigma.mk.inj_iff.1 hzy
    refine mem_iUnion₂.2 ⟨k, hk, ?_⟩
    subst hk
    exact ⟨f k a.1, ⟨a, hz, rfl⟩, eq_of_heq hy⟩
  have hpre' : ∀ (Z : Set D) (j : J) (k : K) (hk : τ k = j) (a : Sigma.mk k ⁻¹' D),
      incl k a ∈ Z → (hk ▸ f k a.1 : B j) ∈
        Sigma.mk j ⁻¹' (D.domRestrict (Sigma.map τ f) '' Z) := by
    intro Z j k hk a ha
    subst hk
    exact ⟨incl k a, ha, rfl⟩
  -- at most one piece of `D` lies over `j`
  have hunique : ∀ j, ∀ k₁ k₂ (h₁ : τ k₁ = j) (h₂ : τ k₂ = j),
      (Sigma.mk k₁ ⁻¹' D).Nonempty → (Sigma.mk k₂ ⁻¹' D).Nonempty → k₁ = k₂ :=
    fun j k₁ k₂ h₁ h₂ hn₁ hn₂ => hτ k₁ k₂ hn₁ hn₂ (h₁.trans h₂.symm)
  have himage : ∀ (Z : Set D) (j : J), (Sigma.mk j ⁻¹' (D.domRestrict (Sigma.map τ f) '' Z)) =
      ⋃ (k) (hk : τ k = j), (fun y => hk ▸ y) '' ((Sigma.mk k ⁻¹' D).domRestrict (f k) ''
        (incl k ⁻¹' Z)) := by
    intro Z j
    refine (hpre Z j).antisymm ?_
    intro y hy
    obtain ⟨k, hk, _, ⟨a, ha, rfl⟩, rfl⟩ := mem_iUnion₂.1 hy
    exact hpre' Z j k hk a ha
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨?_, ?_, ?_⟩
  · exact (continuous_sigma_map.2 hfc).comp continuous_subtype_val
  · intro Z hZ
    refine isClosed_sigma_iff.2 fun j => ?_
    rw [himage Z j]
    -- the union has at most one non-empty member
    by_cases hex : ∃ k, τ k = j ∧ (Sigma.mk k ⁻¹' D).Nonempty
    · obtain ⟨k₀, hk₀, hn₀⟩ := hex
      have heq : (⋃ (k) (hk : τ k = j), (fun y => hk ▸ y) '' ((Sigma.mk k ⁻¹' D).domRestrict
          (f k) '' (incl k ⁻¹' Z))) = (fun y => hk₀ ▸ y) '' ((Sigma.mk k₀ ⁻¹' D).domRestrict
          (f k₀) '' (incl k₀ ⁻¹' Z)) := by
        refine subset_antisymm ?_ (subset_iUnion₂_of_subset k₀ hk₀ subset_rfl)
        refine iUnion₂_subset fun k hk => ?_
        rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        obtain rfl := hunique j k k₀ hk hk₀ ⟨_, a.2⟩ hn₀
        exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      rw [heq]
      subst hk₀
      have := (hf k₀).isClosedMap _ (hZ.preimage (hincl k₀))
      convert this using 1
      exact Set.image_id _
    · simp only [not_exists, not_and] at hex
      convert isClosed_empty
      refine eq_empty_of_forall_notMem fun y hy => ?_
      obtain ⟨k, hk, _, ⟨a, -, rfl⟩, rfl⟩ := mem_iUnion₂.1 hy
      exact hex k hk ⟨_, a.2⟩
  · rintro ⟨j, y⟩
    have hfib : D.domRestrict (Sigma.map τ f) ⁻¹' {⟨j, y⟩} =
        ⋃ (k) (hk : τ k = j), incl k '' ((Sigma.mk k ⁻¹' D).domRestrict (f k) ⁻¹'
          {hk.symm ▸ y}) := by
      ext z
      obtain ⟨k, a, rfl⟩ := hsurj z
      simp only [mem_preimage, mem_singleton_iff, mem_iUnion]
      rw [hcomp]
      constructor
      · intro h
        obtain ⟨hk, hy⟩ := Sigma.mk.inj_iff.1 h
        refine ⟨k, hk, a, ?_, rfl⟩
        subst hk
        exact eq_of_heq hy
      · rintro ⟨k', hk', a', ha', he⟩
        have hk'' : k' = k := by
          have h1 : (incl k' a').1.1 = (incl k a).1.1 := congrArg (fun z : D => z.1.1) he
          exact h1
        subst hk''
        have : a' = a := by
          have h2 := congrArg (fun z : D => z.1) he
          exact Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.1 h2).2)
        subst this
        subst hk'
        change f k' a'.1 = y at ha'
        rw [ha']
    rw [hfib]
    by_cases hex : ∃ k, τ k = j ∧ (Sigma.mk k ⁻¹' D).Nonempty
    · obtain ⟨k₀, hk₀, hn₀⟩ := hex
      have heq : (⋃ (k) (hk : τ k = j), incl k '' ((Sigma.mk k ⁻¹' D).domRestrict (f k) ⁻¹'
          {hk.symm ▸ y})) = incl k₀ '' ((Sigma.mk k₀ ⁻¹' D).domRestrict (f k₀) ⁻¹'
          {hk₀.symm ▸ y}) := by
        refine subset_antisymm ?_ (subset_iUnion₂_of_subset k₀ hk₀ subset_rfl)
        refine iUnion₂_subset fun k hk => ?_
        rintro _ ⟨a, ha, rfl⟩
        obtain rfl := hunique j k k₀ hk hk₀ ⟨_, a.2⟩ hn₀
        exact ⟨a, ha, rfl⟩
      rw [heq]
      exact ((hf k₀).isCompact_preimage isCompact_singleton).image (hincl k₀)
    · simp only [not_exists, not_and] at hex
      convert isCompact_empty
      refine eq_empty_of_forall_notMem fun z hz => ?_
      obtain ⟨k, hk, a, -, rfl⟩ := mem_iUnion₂.1 hz
      exact hex k hk ⟨_, a.2⟩

/-- A map out of an empty space is proper. -/
theorem isProperMap_of_isEmpty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [IsEmpty X]
    (f : X → Y) : IsProperMap f := by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨⟨fun s _ => ?_⟩, fun s _ => ?_, fun y => ?_⟩
  · rw [Set.eq_empty_of_isEmpty (f ⁻¹' s)]; exact isOpen_empty
  · rw [Set.eq_empty_of_isEmpty s, image_empty]; exact isClosed_empty
  · rw [Set.eq_empty_of_isEmpty (f ⁻¹' {y})]; exact isCompact_empty

end ProperSigma

/-! ### The sheet form of Definition 17.1.8 (c) -/

namespace MPolyfold

variable {A B Z D : Type u} [TopologicalSpace A] [T2Space A] [ParacompactSpace A]
  [TopologicalSpace B] [T2Space B] [ParacompactSpace B] [TopologicalSpace Z] [T2Space Z]
  [ParacompactSpace Z] [TopologicalSpace D] [T2Space D] [ParacompactSpace D]
  {PA : MPolyfold A} {PB : MPolyfold B} {PD : MPolyfold D} {PZ : MPolyfold Z}
  {f : A → Z} {g : B → Z} {hf : PA.IsLocalScDiffeo PZ f} {hg : PB.IsScSmoothMap PZ g}
  {h : fibredProduct f g → D}

/-- **The sheet form of sc-smoothness on a fibred product**: if `h` is sc-smooth on `A ₓ×_g B`
and `f : W → V` is an sc-diffeomorphism with inverse `σ`, then `b ↦ h(σ(g b), b)` is sc-smooth on
`g⁻¹(V)` (written with the retraction onto the fibred product, which is the identity there). -/
theorem IsScSmoothOnFibredProduct.isScSmoothOn_sheet
    (hh : IsScSmoothOnFibredProduct PA PB PD hf hg h) {σ : Z → A} {W : Set A} {V : Set Z}
    (hd : PA.IsScDiffeoOn PZ f σ W V) (a₀ : fibredProduct f g) :
    let _ := MPolyfold.paracompactSpace_prod PA PB
    PB.IsScSmoothOn PD (fun b => h ((fibredSubDataL hd hg).retractInto a₀ (σ (g b), b)))
      (g ⁻¹' V) := by
  let _ := MPolyfold.paracompactSpace_prod PA PB
  let _ := (PA.prod PB).paracompactSpace_subtype (MPolyfold.fibredProduct f g)
  have hA := MPolyfold.isSubMPolyfold_fibredProduct hf hg
  have hD := MPolyfold.isScDiffeoOn_snd_fibredProduct hA hd hg a₀
  exact MPolyfold.IsScSmoothOn.comp hh hD.isScSmoothOn_inv (mapsTo_univ _ _)

end MPolyfold

/-! ### The model `X_Ψ` -/

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} (S : C.PolyfoldConstruction) {ι : Type u} (Ψ : ι → S.Unif)

/-- **The object M-polyfold `X = ⊔_λ O_λ`** of the model (2021 (17.7), p. 752). -/
abbrev ModelObj : Type u := Σ i, (Ψ i).1.O

/-- **The morphism M-polyfold `𝐗 = ⊔_{(λ, λ')} M(Ψ_λ, Ψ_λ')`** of the model (2021 (17.7)). -/
abbrev ModelMor : Type u := Σ p : ι × ι, S.Tr (Ψ p.1) (Ψ p.2)

/-- `q_λ ↦ Ψ_λ(q_λ)`, the object map of the functor `Γ_Ψ` of (17.10). -/
def modelObjMap (x : S.ModelObj Ψ) : C.Obj := (Ψ x.1).1.obj x.2

/-- `𝐗` is the transition set of `X → C ← X` (Definition 17.1.5): `(q_λ, φ, q_λ')` as a tuple
with entries in the disjoint union. -/
def modelMorEquiv :
    S.ModelMor Ψ ≃ C.toGroupoidStr.TransitionSet (S.modelObjMap Ψ) (S.modelObjMap Ψ) where
  toFun φ := ⟨⟨φ.1.1, φ.2.src⟩, φ.2.mor, ⟨φ.1.2, φ.2.tgt⟩, φ.2.src_mor, φ.2.tgt_mor⟩
  invFun b := ⟨(b.src.1, b.tgt.1), ⟨b.src.2, b.mor, b.tgt.2, b.src_mor, b.tgt_mor⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The small category `X_Ψ`** (2021 p. 753): `s(q_λ, φ, q_λ') = q_λ`, `t(q_λ, φ, q_λ') = q_λ'`,
the units `(q, 1, q)`, the inverses `(q_λ', φ⁻¹, q_λ)` and the composition
`(q_λ', φ', q_λ'') ∘ (q_λ, φ, q_λ') = (q_λ, φ' ∘ φ, q_λ'')`. -/
def modelGroupoid : GroupoidStr (S.ModelObj Ψ) (S.ModelMor Ψ) :=
  (C.toGroupoidStr.pullback (S.modelObjMap Ψ)).ofEquiv (S.modelMorEquiv Ψ)

variable {S Ψ}

@[simp] theorem modelGroupoid_src (φ : S.ModelMor Ψ) :
    (S.modelGroupoid Ψ).src φ = ⟨φ.1.1, φ.2.src⟩ := rfl

@[simp] theorem modelGroupoid_tgt (φ : S.ModelMor Ψ) :
    (S.modelGroupoid Ψ).tgt φ = ⟨φ.1.2, φ.2.tgt⟩ := rfl

@[simp] theorem modelGroupoid_unit (x : S.ModelObj Ψ) :
    (S.modelGroupoid Ψ).unit x = ⟨(x.1, x.1), GroupoidStr.TransitionSet.unit x.2⟩ := rfl

@[simp] theorem modelGroupoid_inv (φ : S.ModelMor Ψ) :
    (S.modelGroupoid Ψ).inv φ = ⟨(φ.1.2, φ.1.1), GroupoidStr.TransitionSet.inv φ.2⟩ := rfl

/-- The composition of `X_Ψ` on morphisms with composable morphisms of `C`. -/
theorem modelGroupoid_comp_of {i j j' k : ι} (a : S.Tr (Ψ j') (Ψ k)) (b : S.Tr (Ψ i) (Ψ j))
    (h : C.toGroupoidStr.src a.mor = C.toGroupoidStr.tgt b.mor) :
    (S.modelGroupoid Ψ).comp ⟨(j', k), a⟩ ⟨(i, j), b⟩ =
      ⟨(i, k), GroupoidStr.TransitionSet.comp a b h⟩ := by
  change (S.modelMorEquiv Ψ).symm ((C.toGroupoidStr.pullback _).comp _ _) = _
  rw [GroupoidStr.pullback_comp_of _ _ h]
  rfl

/-- The morphism of `C` underlying a composite. -/
theorem modelGroupoid_comp_mor {φ ψ : S.ModelMor Ψ}
    (h : (S.modelGroupoid Ψ).src φ = (S.modelGroupoid Ψ).tgt ψ) :
    ((S.modelGroupoid Ψ).comp φ ψ).2.mor = C.toGroupoidStr.comp φ.2.mor ψ.2.mor := by
  obtain ⟨⟨j', k⟩, a⟩ := φ
  obtain ⟨⟨i, j⟩, b⟩ := ψ
  have hc : C.toGroupoidStr.src a.mor = C.toGroupoidStr.tgt b.mor := by
    rw [a.src_mor, b.tgt_mor]
    exact congrArg (S.modelObjMap Ψ) h
  rw [modelGroupoid_comp_of a b hc]
  rfl

variable (S Ψ)

/-- The inclusion of `O_λ` into `X`. -/
abbrev objMk (i : ι) : (Ψ i).1.O → S.ModelObj Ψ := Sigma.mk (β := fun i => (Ψ i).1.O) i

/-- The inclusion of `M(Ψ_λ, Ψ_λ')` into `𝐗`. -/
abbrev morMk (p : ι × ι) : S.Tr (Ψ p.1) (Ψ p.2) → S.ModelMor Ψ :=
  Sigma.mk (β := fun p : ι × ι => S.Tr (Ψ p.1) (Ψ p.2)) p

/-- The M-polyfold structure of `X = ⊔_λ O_λ` (Chapter 8's disjoint union). -/
def modelObjPolyfold : MPolyfold (S.ModelObj Ψ) := MPolyfold.sigma fun i => (Ψ i).1.P

/-- The M-polyfold structure of `𝐗 = ⊔ M(Ψ_λ, Ψ_λ')`. -/
def modelMorPolyfold : MPolyfold (S.ModelMor Ψ) :=
  MPolyfold.sigma fun p : ι × ι => S.transPolyfold (Ψ p.1) (Ψ p.2)

/-! #### The structure maps (p. 752) -/

/-- **p. 752**: `s : 𝐗 → X` is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_modelSrc :
    (S.modelMorPolyfold Ψ).IsLocalScDiffeo (S.modelObjPolyfold Ψ) (S.modelGroupoid Ψ).src :=
  (MPolyfold.isLocalScDiffeo_sigma_iff _).2 fun p =>
    (MPolyfold.isLocalScDiffeo_sigmaMk (fun i => (Ψ i).1.P) p.1).comp
      (S.isLocalScDiffeo_trSrc (Ψ p.1) (Ψ p.2))

/-- **p. 752**: `t : 𝐗 → X` is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_modelTgt :
    (S.modelMorPolyfold Ψ).IsLocalScDiffeo (S.modelObjPolyfold Ψ) (S.modelGroupoid Ψ).tgt :=
  (MPolyfold.isLocalScDiffeo_sigma_iff _).2 fun p =>
    (MPolyfold.isLocalScDiffeo_sigmaMk (fun i => (Ψ i).1.P) p.2).comp
      (S.isLocalScDiffeo_trTgt (Ψ p.1) (Ψ p.2))

/-- **p. 752**: the unit map `u : X → 𝐗` is sc-smooth. -/
theorem isScSmoothMap_modelUnit :
    (S.modelObjPolyfold Ψ).IsScSmoothMap (S.modelMorPolyfold Ψ) (S.modelGroupoid Ψ).unit :=
  (MPolyfold.isScSmoothMap_sigma_iff _).2 fun i =>
    (MPolyfold.isScSmoothMap_sigmaMk_comp_iff
      (fun p : ι × ι => S.transPolyfold (Ψ p.1) (Ψ p.2)) (i := (i, i))).2
      (S.isScSmoothMap_trUnit (Ψ i))

/-- **p. 752**: the inversion `ι : 𝐗 → 𝐗` is sc-smooth. -/
theorem isScSmoothMap_modelInv :
    (S.modelMorPolyfold Ψ).IsScSmoothMap (S.modelMorPolyfold Ψ) (S.modelGroupoid Ψ).inv := by
  have := MPolyfold.isScSmoothMap_sigmaMap (fun p : ι × ι => S.transPolyfold (Ψ p.1) (Ψ p.2))
    (R := fun p : ι × ι => S.transPolyfold (Ψ p.1) (Ψ p.2)) (σ := Prod.swap)
    (g := fun p (a : S.Tr (Ψ p.1) (Ψ p.2)) => S.toTr (GroupoidStr.TransitionSet.inv a))
    fun p => S.isScSmoothMap_trInv (Ψ p.1) (Ψ p.2)
  exact this

/-- **p. 752**: "the global inversion map `ι : 𝐗 → 𝐗` is an sc-diffeomorphism". -/
theorem isScDiffeoOn_modelInv :
    (S.modelMorPolyfold Ψ).IsScDiffeoOn (S.modelMorPolyfold Ψ) (S.modelGroupoid Ψ).inv
      (S.modelGroupoid Ψ).inv univ univ :=
  ⟨S.isScSmoothMap_modelInv Ψ, S.isScSmoothMap_modelInv Ψ, mapsTo_univ _ _, mapsTo_univ _ _,
    fun φ _ => (S.modelGroupoid Ψ).inv_inv φ, fun φ _ => (S.modelGroupoid Ψ).inv_inv φ⟩

/-- **p. 752, the multiplication, in the sheet form**: for every sheet `s : W → V` of `𝐗` with
inverse `σ`, `ψ ↦ σ(t ψ) ∘ ψ` is sc-smooth on `t⁻¹(V)`.  Near `ψ₀ ∈ M(Ψ_λ, Ψ_λ')`, `σ ∘ t` lands
in one piece `M(Ψ_λ', Ψ_λ'')`, where it is a local inverse of `s`, and the composite is the
multiplication of Definition 17.1.8 (c) in its sheet form. -/
theorem isScSmoothCompSheet_model :
    IsScSmoothCompSheet (S.modelObjPolyfold Ψ) (S.modelMorPolyfold Ψ)
      (S.modelGroupoid Ψ).src (S.modelGroupoid Ψ).tgt (S.modelGroupoid Ψ).comp := by
  intro σ W V hd
  have hVo : IsOpen V := hd.isScSmoothOn_inv.isOpen
  have htc : Continuous (S.modelGroupoid Ψ).tgt := (S.isLocalScDiffeo_modelTgt Ψ).continuous
  refine (MPolyfold.isScSmoothOn_sigma_iff _ (hVo.preimage htc)).2 fun p => ?_
  obtain ⟨i, j⟩ := p
  refine MPolyfold.IsScSmoothOn.of_locally ((hVo.preimage htc).preimage continuous_sigmaMk)
    fun b₀ hb₀ => ?_
  -- `y₀ = t(ψ₀)` and the morphism `σ(y₀)`
  have hy₀ : (⟨j, b₀.tgt⟩ : S.ModelObj Ψ) ∈ V := hb₀
  rcases hσ₀ : σ ⟨j, b₀.tgt⟩ with ⟨⟨j', k⟩, a₀⟩
  have hsrc₀ : (S.modelGroupoid Ψ).src (σ ⟨j, b₀.tgt⟩) = ⟨j, b₀.tgt⟩ := hd.right_inv _ hy₀
  rw [hσ₀] at hsrc₀
  have hj : j = j' := ((Sigma.mk.inj_iff.1 hsrc₀).1).symm
  subst hj
  have hsrc₀'' : a₀.src = b₀.tgt := eq_of_heq (Sigma.mk.inj_iff.1 hsrc₀).2
  -- a sheet of `s` at `a₀` in `M(Ψ_j, Ψ_k)`
  obtain ⟨W', V', σ', ha₀W', hd'⟩ := S.isLocalScDiffeo_trSrc (Ψ j) (Ψ k) a₀
  -- near `b₀`, `σ(t b)` lies in `Sigma.mk (j, k) '' W'`
  have hσc : ContinuousOn σ V := hd.isScSmoothOn_inv.continuousOn
  have hW'o : IsOpen (S.morMk Ψ (j, k) '' W') :=
    isOpenMap_sigmaMk _ hd'.isOpen_source
  set N : Set (S.Tr (Ψ i) (Ψ j)) :=
    (fun b : S.Tr (Ψ i) (Ψ j) => (⟨j, b.tgt⟩ : S.ModelObj Ψ)) ⁻¹'
      (V ∩ σ ⁻¹' (S.morMk Ψ (j, k) '' W')) ∩ (fun b : S.Tr (Ψ i) (Ψ j) => b.tgt) ⁻¹' V'
  have hbc : Continuous fun b : S.Tr (Ψ i) (Ψ j) => (⟨j, b.tgt⟩ : S.ModelObj Ψ) :=
    continuous_sigmaMk.comp (S.continuous_trTgt _ _)
  have hNo : IsOpen N :=
    ((hσc.isOpen_inter_preimage hVo hW'o).preimage hbc).inter
      (hd'.isOpen_target.preimage (S.continuous_trTgt _ _))
  have hb₀N : b₀ ∈ N := by
    refine ⟨⟨hy₀, ?_⟩, ?_⟩
    · change σ ⟨j, b₀.tgt⟩ ∈ S.morMk Ψ (j, k) '' W'
      rw [hσ₀]
      exact ⟨a₀, ha₀W', rfl⟩
    · change b₀.tgt ∈ V'
      rw [← hsrc₀'']
      exact hd'.mapsTo ha₀W'
  -- on `N`, `σ(t b) = (σ'(t b) in M(Ψ_j, Ψ_k))`
  have hσN : ∀ b ∈ N, σ ⟨j, b.tgt⟩ = ⟨(j, k), σ' b.tgt⟩ := by
    intro b hb
    obtain ⟨⟨hbV, a, haW', ha⟩⟩ := hb
    have hs : (S.modelGroupoid Ψ).src (σ ⟨j, b.tgt⟩) = ⟨j, b.tgt⟩ := hd.right_inv _ hbV
    rw [← ha] at hs ⊢
    obtain ⟨-, hs'⟩ := Sigma.mk.inj_iff.1 hs
    have hs'' : a.src = b.tgt := eq_of_heq hs'
    congr 1
    rw [← hs'', hd'.left_inv a haW']
  have hcomp : ∀ b (hb : b ∈ N), (S.modelGroupoid Ψ).comp (σ ((S.modelGroupoid Ψ).tgt ⟨(i, j), b⟩))
      ⟨(i, j), b⟩ = ⟨(i, k), GroupoidStr.TransitionSet.comp (σ' b.tgt) b
        (by rw [(σ' b.tgt).src_mor, b.tgt_mor]
            change (Ψ j).1.obj (σ' b.tgt).src = (Ψ j).1.obj b.tgt
            rw [hd'.right_inv _ hb.2])⟩ := by
    intro b hb
    change (S.modelGroupoid Ψ).comp (σ ⟨j, b.tgt⟩) ⟨(i, j), b⟩ = _
    rw [hσN b hb, modelGroupoid_comp_of]
  -- the piece of the multiplication of (c)
  let _ := MPolyfold.paracompactSpace_prod (S.transPolyfold (Ψ j) (Ψ k))
    (S.transPolyfold (Ψ i) (Ψ j))
  set d := MPolyfold.fibredSubDataL hd' (S.isLocalScDiffeo_trTgt (Ψ i) (Ψ j)).isScSmoothMap
  let a₀' : MPolyfold.fibredProduct (fun a : S.Tr (Ψ j) (Ψ k) => a.src)
      (fun b : S.Tr (Ψ i) (Ψ j) => b.tgt) := ⟨(σ' b₀.tgt, b₀), by
    change (σ' b₀.tgt).src = b₀.tgt
    exact hd'.right_inv _ hb₀N.2⟩
  have hm := (S.isScSmoothMap_trMul (Ψ i) (Ψ j) (Ψ k)).isScSmoothOn_sheet hd' a₀'
  refine ⟨N, hNo, hb₀N, fun b hb => hb.1.1, ?_⟩
  have hm' := (MPolyfold.isScSmoothOn_sigmaMk_comp_iff
    (fun p : ι × ι => S.transPolyfold (Ψ p.1) (Ψ p.2)) (i := (i, k))).2
    (hm.mono hNo fun b hb => hb.2)
  refine hm'.congr fun b hb => ?_
  simp only [Function.comp_apply]
  rw [hcomp b hb]
  have hv := d.retractInto_val a₀' (x := (σ' b.tgt, b)) ⟨hd'.mapsTo_inv hb.2, hb.2⟩
  refine Sigma.ext rfl (heq_of_eq (GroupoidStr.TransitionSet.ext ?_ ?_ ?_))
  · exact congrArg (fun p : S.Tr (Ψ j) (Ψ k) × S.Tr (Ψ i) (Ψ j) => p.2.src) hv
  · exact congrArg (fun p : S.Tr (Ψ j) (Ψ k) × S.Tr (Ψ i) (Ψ j) =>
      C.toGroupoidStr.comp p.1.mor p.2.mor) hv
  · exact congrArg (fun p : S.Tr (Ψ j) (Ψ k) × S.Tr (Ψ i) (Ψ j) => p.1.tgt) hv

/-- **p. 752**: the multiplication `m : 𝐗 ₛ×ₜ 𝐗 → 𝐗` is sc-smooth (Definition 7.1.3 (4),
literally). -/
theorem isScSmoothComp_model :
    IsScSmoothComp (S.modelObjPolyfold Ψ) (S.modelMorPolyfold Ψ)
      (S.modelGroupoid Ψ).src (S.modelGroupoid Ψ).tgt (S.modelGroupoid Ψ).comp
      (S.isLocalScDiffeo_modelSrc Ψ) (S.isLocalScDiffeo_modelTgt Ψ).isScSmoothMap :=
  (isScSmoothComp_iff_sheet _ _).2 (S.isScSmoothCompSheet_model Ψ)

/-! #### Properness (the proof of Theorem 17.1.14) -/

/-- **The properness of `X_Ψ`** (the proof of Theorem 17.1.14, (17.8), (17.9)): with `U(q_{λ₀})`
from Proposition 17.1.11, `U := U(q_{λ₀}) ⊂ O_{λ₀} ⊂ X` has `t : s⁻¹(cl_X U) → X` proper. -/
theorem exists_isProperMap_model (x : S.ModelObj Ψ) :
    ∃ V : Set (S.ModelObj Ψ), IsOpen V ∧ x ∈ V ∧
      IsProperMap (((S.modelGroupoid Ψ).src ⁻¹' closure V).domRestrict
        (S.modelGroupoid Ψ).tgt) := by
  obtain ⟨i, q⟩ := x
  obtain ⟨U, hU, hqU, hprop⟩ := S.proposition_17_1_11 (Ψ i) q
  refine ⟨S.objMk Ψ i '' U, isOpenMap_sigmaMk (σ := fun i => (Ψ i).1.O) _ hU, ⟨q, hqU, rfl⟩, ?_⟩
  have hcl : closure (S.objMk Ψ i '' U) = S.objMk Ψ i '' closure U :=
    (IsClosedEmbedding.sigmaMk (σ := fun i => (Ψ i).1.O) (i := i)).closure_image_eq U
  rw [hcl]
  set D := (S.modelGroupoid Ψ).src ⁻¹' (S.objMk Ψ i '' closure U)
  -- the pieces of `D` lie over `λ₀ = i`
  have hD : ∀ p : ι × ι, (S.morMk Ψ p ⁻¹' D).Nonempty → p.1 = i := by
    rintro p ⟨a, q', -, hq'⟩
    exact ((Sigma.mk.inj_iff.1 hq').1).symm
  have hτ : ∀ p p' : ι × ι, (S.morMk Ψ p ⁻¹' D).Nonempty → (S.morMk Ψ p' ⁻¹' D).Nonempty →
      p.2 = p'.2 → p = p' := fun p p' hp hp' h => Prod.ext ((hD p hp).trans (hD p' hp').symm) h
  have hpiece : ∀ p : ι × ι, IsProperMap ((S.morMk Ψ p ⁻¹' D).domRestrict
      fun a : S.Tr (Ψ p.1) (Ψ p.2) => a.tgt) := by
    rintro ⟨i', j⟩
    by_cases hi : i' = i
    · subst hi
      have hDp : S.morMk Ψ (i', j) ⁻¹' D =
          (fun a : S.Tr (Ψ i') (Ψ j) => a.src) ⁻¹' closure U := by
        ext a
        constructor
        · rintro ⟨q', hq', he⟩
          have : q' = a.src := eq_of_heq (Sigma.mk.inj_iff.1 he).2
          change a.src ∈ closure U
          rw [← this]
          exact hq'
        · intro ha
          exact ⟨a.src, ha, rfl⟩
      rw [hDp]
      exact hprop (Ψ j)
    · have : IsEmpty (S.morMk Ψ (i', j) ⁻¹' D) :=
        ⟨fun a => hi (hD (i', j) ⟨a.1, a.2⟩)⟩
      exact isProperMap_of_isEmpty _
  exact isProperMap_domRestrict_sigmaMap (A := fun p : ι × ι => S.Tr (Ψ p.1) (Ψ p.2))
    (B := fun i => (Ψ i).1.O) Prod.snd (fun p a => a.tgt)
    (fun p => S.continuous_trTgt (Ψ p.1) (Ψ p.2)) D hτ hpiece

/-! #### Theorem 17.1.14 -/

/-- **The ep-groupoid `X_Ψ`** of a family of uniformizers (2021 Theorem 17.1.14, p. 753): objects
`⊔_λ O_λ`, morphisms `⊔_{(λ, λ')} M(Ψ_λ, Ψ_λ')`, the structure maps of p. 753. -/
def modelEpGroupoid : EpGroupoid (S.ModelObj Ψ) (S.ModelMor Ψ) where
  toGroupoidStr := S.modelGroupoid Ψ
  PObj := S.modelObjPolyfold Ψ
  PMor := S.modelMorPolyfold Ψ
  isLocalScDiffeo_src := S.isLocalScDiffeo_modelSrc Ψ
  isLocalScDiffeo_tgt := S.isLocalScDiffeo_modelTgt Ψ
  isScSmoothMap_unit := S.isScSmoothMap_modelUnit Ψ
  isScSmoothMap_inv := S.isScSmoothMap_modelInv Ψ
  exists_isProperMap := S.exists_isProperMap_model Ψ
  isScSmoothComp := S.isScSmoothComp_model Ψ

/-- **`X_Ψ` as an object of `EP`**. -/
def modelEP : EP.{u} := ⟨S.ModelObj Ψ, S.ModelMor Ψ, S.modelEpGroupoid Ψ⟩

@[simp] theorem modelEP_X : (S.modelEP Ψ).X = S.modelEpGroupoid Ψ := rfl

@[simp] theorem modelEpGroupoid_toGroupoidStr :
    (S.modelEpGroupoid Ψ).toGroupoidStr = S.modelGroupoid Ψ := rfl

/-- **Theorem 17.1.14, the tame part**: if `(F, M)` is tame, `X_Ψ` is a tame ep-groupoid. -/
theorem isTame_modelEpGroupoid (h : S.IsTame) : (S.modelEpGroupoid Ψ).IsTame :=
  (MPolyfold.isTame_sigma_iff _).2 fun i => by
    obtain ⟨α, hα⟩ := (Ψ i).2
    exact h α _ hα

/-- **2021 Theorem 17.1.14, p. 753**: for a covering set `Ψ` of uniformizers of the polyfold
construction `(F, M)`, the small category `X_Ψ` (objects `⊔ O_λ`, morphisms `⊔ M(Ψ_λ, Ψ_λ')`,
with the structure maps of p. 753) has the structure of an ep-groupoid, with the M-polyfold
structures of (17.7); if `(F, M)` is tame, `X_Ψ` is a tame ep-groupoid. -/
theorem theorem_17_1_14 (c : S.CoveringFamily) :
    ∃ X : EpGroupoid (S.ModelObj c.Ψ) (S.ModelMor c.Ψ), X.toGroupoidStr = S.modelGroupoid c.Ψ ∧
      X.PObj = S.modelObjPolyfold c.Ψ ∧ X.PMor = S.modelMorPolyfold c.Ψ ∧
      (S.IsTame → X.IsTame) :=
  ⟨S.modelEpGroupoid c.Ψ, rfl, rfl, rfl, S.isTame_modelEpGroupoid c.Ψ⟩

end GCT.PolyfoldConstruction

end Polyfold
