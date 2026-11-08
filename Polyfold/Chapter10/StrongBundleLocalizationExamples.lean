import Polyfold.Chapter10.StrongBundleLocalizationSections
import Polyfold.Chapter10.StrongBundleEquivalenceExamples
import Polyfold.Chapter7.NonVacuity

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, §10.5 "Localization in the Strong Bundle Case" (pp. 504–508; 2017:
pp. 364–367): witnesses for **Definition 10.5.2** and **Theorem 10.5.4**, and the negative half
of **Remark 10.5.5** (p. 508, new in the 2021 edition).  Numbers and pages are the 2021 text's.
The definitions are in `StrongBundleLocalization.lean`, Theorem 10.5.4 in
`StrongBundleLocalizationSections.lean`.

# Generalized strong bundle isomorphisms: examples

## The text, paraphrased

The text gives no examples in §10.5.  (Remark 10.5.5, p. 508) For generalized strong bundle
isomorphisms `[D], [D'] : P → P'`, `|D| = |D'|` does not in general give `[D] = [D']`, as in the
ep-groupoid case, while it does give `[D]_* = [D']_*` and `[D]* = [D']*`.

## What is formalized

* Helpers on isotropy groups: `GroupoidStr.isotropyConj_isotropyConj`,
  `isotropyConj_isotropyConj_inv`, `isotropyConj_congr`, `EpFunctor.isotropyHom_isotropyConj`,
  `EpNatTrans.isotropyHom_eq` (`ψ(h) = τ(z) ∘ φ(h) ∘ τ(z)⁻¹` for `τ : φ → ψ`).
* **An invariant of the classes of diagrams of ep-groupoids**: `EPLocalization.Diagram.IsotropyRel`
  (`g ∈ G_x`, `g' ∈ G_{x'}` related if `g = a ∘ φ(k) ∘ a⁻¹`, `g' = b ∘ ψ(k) ∘ b⁻¹`; the union of
  the graphs of the homomorphisms `γ` of p. 505 over all choices, `isotropyRel_isotropyHom`),
  invariant under refinement and equivalence (`IsRefinement.isotropyRel_iff`,
  `Equiv.isotropyRel_iff`).
* `SDiagram.pushforward_id` (`[1]_* = 1`), `SDiagram.orbitMap_ofHom` (`|[1, Ψ]| = |Ψ|`).
* **A non-trivial generalized strong bundle isomorphism** (Definition 10.5.2):
  `negDiagram`, `(-id)*W' ←1 (-id)*W' →P' W'` for `W' = ℝⁿ × ℝᵏ → ℝⁿ` over the trivial
  ep-groupoid, `P'` covering `-id` (§10.4's `negSEPHom`); `isGeneralizedIso_negDiagram`, and
  Theorem 10.5.4 for it, `bijOn_pushforward_negDiagram`.
* **A non-trivial refinement**: `foldDiagram`, `W' ←P' (-id)*W' →P' W'`, refines `1_{W'}`
  (`isRefinement_foldDiagram`, `cls_foldDiagram`), and its push-forward is the identity of
  `Γ(W')` (`pushforward_foldDiagram`, by Theorem 10.5.4).
* **Remark 10.5.5**: `z3EpBundle`, the strong bundle `ℝ × ℝᵏ → ℝ` over `ℤ/3 × ℝ ⇉ ℝ`
  (Chapter 7's `trivialZ3EpGroupoid`) with `μ((g, x), w) = w`; `z3Inv`, the functor
  `(g, x) ↦ (g⁻¹, x)`; `z3InvHom`, the strong bundle functor `Inv` covering it, a strong bundle
  equivalence (`z3InvHom_mem_equivalences`).  `remark_10_5_5`: `[1_W]` and `[W ←1 W →Inv W]`
  are generalized strong bundle isomorphisms with `|[Inv]| = |[1]|` (`orbitMap_ofHom_z3InvHom`)
  and `[Inv] ≠ [1]`; already the base classes differ, with equal orbit maps
  (`base_orbitMap_ofHom_z3InvHom`).  The positive half for the example:
  `pushforward_inv_eq_pushforward_id`.

## What the text leaves implicit, and the choices made

* The text gives no example for Remark 10.5.5.  The classes are separated by `IsotropyRel` at
  the generator `z3Gen` of `G_0 = ℤ/3`: for `[1]` the generator is related to itself
  (`isotropyRel_id`, `γ = 1`), for `[Inv]` only to its inverse, since conjugation is trivial in
  the abelian `ℤ/3` and `g⁻¹ ≠ g` there (`not_isotropyRel_inv`).
* `[Inv] ≠ [1]` is proved for the classes of `Quot SDiagram.Equiv`, the finest reading (no chain
  of common refinements connects the two diagrams), so it holds for the text's classes too.
* "Non-trivial" for `negDiagram`: its legs cover `-id ≠ id` (`trivialNeg_obj_ne_id`), between
  two different strong bundles.

## Not formalized

* Nothing beyond the items listed in `StrongBundleLocalization.lean` and
  `StrongBundleLocalizationSections.lean`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-! ### Conjugation in isotropy groups -/

namespace GroupoidStr

variable {Obj Mor : Type u} {G : GroupoidStr Obj Mor}

/-- `ψ ∘ (φ ∘ g ∘ φ⁻¹) ∘ ψ⁻¹ = (ψ ∘ φ) ∘ g ∘ (ψ ∘ φ)⁻¹`. -/
theorem isotropyConj_isotropyConj {x y z : Obj} {φ ψ : Mor} (hx : G.src φ = x)
    (hy : G.tgt φ = y) (hy' : G.src ψ = y) (hz : G.tgt ψ = z) (g : G.Isotropy x) :
    G.isotropyConj ψ hy' hz (G.isotropyConj φ hx hy g) =
      G.isotropyConj (G.comp ψ φ) ((G.src_comp _ _ (hy'.trans hy.symm)).trans hx)
        ((G.tgt_comp _ _ (hy'.trans hy.symm)).trans hz) g := by
  refine Isotropy.ext ?_
  let f := G.homMk φ hx hy
  let f' := G.homMk ψ hy' hz
  let γ := G.homMk g.val g.src_val g.tgt_val
  change (Groupoid.inv f' ≫ (Groupoid.inv f ≫ γ ≫ f) ≫ f').1 =
    (Groupoid.inv (f ≫ f') ≫ γ ≫ f ≫ f').1
  congr 1
  simp [Groupoid.inv_eq_inv]

/-- `φ ∘ (φ⁻¹ ∘ g ∘ φ) ∘ φ⁻¹ = g`. -/
theorem isotropyConj_isotropyConj_inv {x y : Obj} {φ : Mor} (hx : G.src φ = x)
    (hy : G.tgt φ = y) (g : G.Isotropy y) :
    G.isotropyConj φ hx hy
      (G.isotropyConj (G.inv φ) ((G.src_inv φ).trans hy) ((G.tgt_inv φ).trans hx) g) = g := by
  refine Isotropy.ext ?_
  let f := G.homMk φ hx hy
  let γ := G.homMk g.val g.src_val g.tgt_val
  change (Groupoid.inv f ≫ (Groupoid.inv (Groupoid.inv f) ≫ γ ≫ Groupoid.inv f) ≫ f).1 = γ.1
  congr 1
  simp [Groupoid.inv_eq_inv]

/-- The conjugation by equal morphisms. -/
theorem isotropyConj_congr {x y : Obj} {φ φ' : Mor} (e : φ = φ') (hx : G.src φ = x)
    (hy : G.tgt φ = y) (g : G.Isotropy x) :
    G.isotropyConj φ hx hy g = G.isotropyConj φ' (e ▸ hx) (e ▸ hy) g := by
  subst e
  rfl

end GroupoidStr

section IsotropyFunctor

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Obj' Mor' : Type u} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {Y : EpGroupoid Obj' Mor'}

/-- A functor commutes with conjugation: `F(φ ∘ g ∘ φ⁻¹) = F(φ) ∘ F(g) ∘ F(φ)⁻¹`. -/
theorem EpFunctor.isotropyHom_isotropyConj (F : EpFunctor X Y) {x y : Obj} {φ : Mor}
    (hx : X.src φ = x) (hy : X.tgt φ = y) (g : X.Isotropy x) :
    F.isotropyHom y (X.isotropyConj φ hx hy g) =
      Y.isotropyConj (F.mor φ) (by rw [F.src_mor, hx]) (by rw [F.tgt_mor, hy])
        (F.isotropyHom x g) := by
  refine GroupoidStr.Isotropy.ext ?_
  have h₁ : X.src φ = X.tgt g.val := hx.trans g.tgt_val.symm
  rw [EpFunctor.isotropyHom_val, GroupoidStr.isotropyConj_val, GroupoidStr.isotropyConj_val,
    EpFunctor.isotropyHom_val,
    F.mor_comp _ _ (by rw [X.src_comp _ _ h₁, X.tgt_inv, g.src_val, hx]), F.mor_comp _ _ h₁,
    GroupoidFunctor.mor_inv F.toGroupoidFunctor]

/-- A natural transformation `τ : F → G` conjugates the isotropy homomorphisms:
`G(h) = τ(z) ∘ F(h) ∘ τ(z)⁻¹` for `h ∈ G_z`. -/
theorem EpNatTrans.isotropyHom_eq {F G : EpFunctor X Y} (τ : EpNatTrans F G) (z : Obj)
    (h : X.Isotropy z) :
    G.isotropyHom z h =
      Y.isotropyConj (τ.app z) (τ.src_app z) (τ.tgt_app z) (F.isotropyHom z h) := by
  refine GroupoidStr.Isotropy.ext ?_
  change G.mor h.val = Y.comp (Y.comp (τ.app z) (F.mor h.val)) (Y.inv (τ.app z))
  have hn := τ.naturality h.val
  rw [h.tgt_val, h.src_val] at hn
  rw [hn]
  exact (GroupoidStr.comp_inv_cancel_right (by rw [G.src_mor, h.src_val, τ.tgt_app])).symm

end IsotropyFunctor

/-! ### An invariant of the classes of diagrams of ep-groupoids -/

namespace EPLocalization.Diagram

variable {X Y : EP.{u}}

/-- **The relation of the homomorphisms `γ`** (2021 p. 505) of a diagram `d : X ←φ A →ψ Y`:
`g ∈ G_x` and `g' ∈ G_{x'}` are related if `g = a ∘ φ(k) ∘ a⁻¹` and `g' = b ∘ ψ(k) ∘ b⁻¹` for some
`z ∈ A`, `k ∈ G_z`, `a : φ(z) → x`, `b : ψ(z) → x'`.  It is the union of the graphs of the `γ`
for all choices of `z`, `a`, `b`. -/
def IsotropyRel (d : Diagram X Y) {x : X.Obj} {x' : Y.Obj} (g : X.X.Isotropy x)
    (g' : Y.X.Isotropy x') : Prop :=
  ∃ (z : d.A.Obj) (k : d.A.X.Isotropy z) (a : X.Mor) (ha : X.X.src a = d.F.obj z)
    (ha' : X.X.tgt a = x) (b : Y.Mor) (hb : Y.X.src b = d.Φ.obj z) (hb' : Y.X.tgt b = x'),
    X.X.isotropyConj a ha ha' (d.F.isotropyHom z k) = g ∧
      Y.X.isotropyConj b hb hb' (d.Φ.isotropyHom z k) = g'

/-- The value of `γ` is related to its argument. -/
theorem isotropyRel_isotropyHom (d : Diagram X Y) {x : X.Obj} {x' : Y.Obj} {z : d.A.Obj}
    (a : X.Mor) (ha : X.X.src a = d.F.obj z) (ha' : X.X.tgt a = x) (b : Y.Mor)
    (hb : Y.X.src b = d.Φ.obj z) (hb' : Y.X.tgt b = x') (g : X.X.Isotropy x) :
    d.IsotropyRel g (d.isotropyHom a ha ha' b hb hb' g) := by
  obtain ⟨k, hk, hk'⟩ := d.isotropyHom_spec a ha ha' b hb hb' g
  refine ⟨z, k, a, ha, ha', b, hb, hb', GroupoidStr.Isotropy.ext ?_,
    (GroupoidStr.Isotropy.ext hk'.symm)⟩
  rw [GroupoidStr.isotropyConj_val, EpFunctor.isotropyHom_val, hk]
  let f := X.X.homMk a ha ha'
  let γ := X.X.homMk g.val g.src_val g.tgt_val
  change (Groupoid.inv f ≫ (f ≫ γ ≫ Groupoid.inv f) ≫ f).1 = γ.1
  congr 1
  simp

/-- **The relation is invariant under refinement.** -/
theorem IsRefinement.isotropyRel_iff {d' d : Diagram X Y} (hr : d'.IsRefinement d)
    {x : X.Obj} {x' : Y.Obj} (g : X.X.Isotropy x) (g' : Y.X.Isotropy x') :
    d'.IsotropyRel g g' ↔ d.IsotropyRel g g' := by
  obtain ⟨H, hH, ⟨τ⟩, ⟨σ⟩⟩ := hr
  have kF : ∀ (z : d'.A.Obj) (k : d'.A.X.Isotropy z), d'.F.isotropyHom z k =
      X.X.isotropyConj (τ.app z) (τ.src_app z) (τ.tgt_app z)
        (d.F.isotropyHom (H.obj z) (H.isotropyHom z k)) := fun z k => τ.isotropyHom_eq z k
  have kΦ : ∀ (z : d'.A.Obj) (k : d'.A.X.Isotropy z), d'.Φ.isotropyHom z k =
      Y.X.isotropyConj (σ.app z) (σ.src_app z) (σ.tgt_app z)
        (d.Φ.isotropyHom (H.obj z) (H.isotropyHom z k)) := fun z k => σ.isotropyHom_eq z k
  constructor
  · rintro ⟨z, k, a, ha, ha', b, hb, hb', rfl, rfl⟩
    have hτ : X.X.src a = X.X.tgt (τ.app z) := ha.trans (τ.tgt_app z).symm
    have hσ : Y.X.src b = Y.X.tgt (σ.app z) := hb.trans (σ.tgt_app z).symm
    refine ⟨H.obj z, H.isotropyHom z k, X.X.comp a (τ.app z),
      (X.X.src_comp _ _ hτ).trans (τ.src_app z), (X.X.tgt_comp _ _ hτ).trans ha',
      Y.X.comp b (σ.app z), (Y.X.src_comp _ _ hσ).trans (σ.src_app z),
      (Y.X.tgt_comp _ _ hσ).trans hb', ?_, ?_⟩
    · rw [kF]; exact (GroupoidStr.isotropyConj_isotropyConj _ _ _ _ _).symm
    · rw [kΦ]; exact (GroupoidStr.isotropyConj_isotropyConj _ _ _ _ _).symm
  · rintro ⟨z, k, a, ha, ha', b, hb, hb', rfl, rfl⟩
    obtain ⟨z', c, hc, hc'⟩ := hH.exists_iso z
    obtain ⟨k₁, hk₁⟩ : ∃ k₁, k₁ = d.A.X.isotropyConj (d.A.X.inv c)
        ((d.A.X.src_inv c).trans hc') ((d.A.X.tgt_inv c).trans hc) k := ⟨_, rfl⟩
    obtain ⟨k', hk'⟩ := (hH.bijective_isotropyHom z').2 k₁
    have ek : d.A.X.isotropyConj c hc hc' k₁ = k :=
      hk₁ ▸ GroupoidStr.isotropyConj_isotropyConj_inv hc hc' k
    -- `a ∘ F(c) : F(H z') → x` and `b ∘ Φ(c) : Φ(H z') → x'`
    have hFc : X.X.src a = X.X.tgt (d.F.mor c) := by rw [ha, d.F.tgt_mor, hc']
    have hΦc : Y.X.src b = Y.X.tgt (d.Φ.mor c) := by rw [hb, d.Φ.tgt_mor, hc']
    set a₀ := X.X.comp a (d.F.mor c)
    set b₀ := Y.X.comp b (d.Φ.mor c)
    have ha₀ : X.X.src a₀ = X.X.src (τ.app z') := by
      rw [X.X.src_comp _ _ hFc, d.F.src_mor, hc, τ.src_app]; rfl
    have hb₀ : Y.X.src b₀ = Y.X.src (σ.app z') := by
      rw [Y.X.src_comp _ _ hΦc, d.Φ.src_mor, hc, σ.src_app]; rfl
    have ha₁ : X.X.src a₀ = X.X.tgt (X.X.inv (τ.app z')) := ha₀.trans (X.X.tgt_inv _).symm
    have hb₁ : Y.X.src b₀ = Y.X.tgt (Y.X.inv (σ.app z')) := hb₀.trans (Y.X.tgt_inv _).symm
    have ea : X.X.comp (X.X.comp a₀ (X.X.inv (τ.app z'))) (τ.app z') = a₀ := by
      have e := GroupoidStr.comp_inv_cancel_right (G := X.X.toGroupoidStr) ha₁
      rwa [GroupoidStr.inv_inv] at e
    have eb : Y.X.comp (Y.X.comp b₀ (Y.X.inv (σ.app z'))) (σ.app z') = b₀ := by
      have e := GroupoidStr.comp_inv_cancel_right (G := Y.X.toGroupoidStr) hb₁
      rwa [GroupoidStr.inv_inv] at e
    refine ⟨z', k', X.X.comp a₀ (X.X.inv (τ.app z')),
      by rw [X.X.src_comp _ _ ha₁, X.X.src_inv, τ.tgt_app],
      by rw [X.X.tgt_comp _ _ ha₁, X.X.tgt_comp _ _ hFc, ha'],
      Y.X.comp b₀ (Y.X.inv (σ.app z')),
      by rw [Y.X.src_comp _ _ hb₁, Y.X.src_inv, σ.tgt_app],
      by rw [Y.X.tgt_comp _ _ hb₁, Y.X.tgt_comp _ _ hΦc, hb'], ?_, ?_⟩
    · rw [kF, hk']
      refine (GroupoidStr.isotropyConj_isotropyConj _ _ _ _ _).trans ?_
      refine (GroupoidStr.isotropyConj_congr ea _ _ _).trans ?_
      rw [← ek, EpFunctor.isotropyHom_isotropyConj]
      exact (GroupoidStr.isotropyConj_isotropyConj (φ := d.F.mor c) (ψ := a)
        (by rw [d.F.src_mor, hc]) (by rw [d.F.tgt_mor, hc']) ha ha'
        (d.F.isotropyHom (H.obj z') k₁)).symm
    · rw [kΦ, hk']
      refine (GroupoidStr.isotropyConj_isotropyConj _ _ _ _ _).trans ?_
      refine (GroupoidStr.isotropyConj_congr eb _ _ _).trans ?_
      rw [← ek, EpFunctor.isotropyHom_isotropyConj]
      exact (GroupoidStr.isotropyConj_isotropyConj (φ := d.Φ.mor c) (ψ := b)
        (by rw [d.Φ.src_mor, hc]) (by rw [d.Φ.tgt_mor, hc']) hb hb'
        (d.Φ.isotropyHom (H.obj z') k₁)).symm

/-- **The relation is an invariant of the class**: equivalent diagrams have the same relation. -/
theorem Equiv.isotropyRel_iff {d d' : Diagram X Y} (h : Equiv d d') {x : X.Obj} {x' : Y.Obj}
    (g : X.X.Isotropy x) (g' : Y.X.Isotropy x') : d.IsotropyRel g g' ↔ d'.IsotropyRel g g' :=
  let ⟨_, h₁, h₂⟩ := h
  (h₁.isotropyRel_iff g g').symm.trans (h₂.isotropyRel_iff g g')

end EPLocalization.Diagram

namespace SBLocalization.SDiagram

variable {A A' : SEP.{u}}

/-- The push-forward along the identity diagram `W ←1 W →1 W` is the identity on `Γ(P, μ)`
(`1* f = f` since `1` is the identity on `W`, and `1_* 1* f = f`, Theorem 10.4.5). -/
theorem pushforward_id (A : SEP.{u}) :
    EqOn ((SDiagram.id A).pushforward (SEP.equivalences.id_mem A)) _root_.id A.E.sectionFunctors
    := by
  intro f hf
  have hp : (SDiagram.id A).hΦ.pullback f = f := by
    funext x
    exact (SDiagram.id A).hΦ.obj_pullback hf.1.1 x
  change (sbe (SEP.equivalences.id_mem A)).pushforward ((SDiagram.id A).hΦ.pullback f) = f
  rw [hp]
  have hp' := (sbe (SEP.equivalences.id_mem A)).pushforward_pullback hf.1.1 hf.2
  have hq : (sbe (SEP.equivalences.id_mem A)).pullback f = f := by
    funext x
    exact (sbe (SEP.equivalences.id_mem A)).obj_pullback hf.1.1 x
  rw [hq] at hp'
  exact hp'

/-- `|W ←1 W →Ψ W'| = |Ψ|`. -/
theorem orbitMap_ofHom (Ψ : A ⟶ A') : (SDiagram.ofHom Ψ).orbitMap = (SEP.Hom.Φ Ψ).orbitMap := by
  funext q
  have h := (SDiagram.ofHom Ψ).orbitMap_orbitMap_Φ q
  have e : (SEP.Hom.Φ (SDiagram.ofHom Ψ).Φ).orbitMap q = q := by
    induction q using Quotient.inductionOn with | h w => rfl
  rw [e] at h
  exact h

end SBLocalization.SDiagram

namespace StrongBundleLocalizationExamples

open SBLocalization StrongBundleEquivalenceExamples

/-! ### A generalized strong bundle isomorphism `(-id)*W' → W'` -/

section Neg

variable (n k : ℕ)

/-- **A generalized strong bundle isomorphism** (Definition 10.5.2): the class of
`(-id)*W' ←1 (-id)*W' →P' W'`, `W' = ℝⁿ × ℝᵏ → ℝⁿ`, whose `P'` covers `-id`. -/
def negDiagram : SDiagram (negSEP n k) (epSEP n k) := SDiagram.ofHom (negSEPHom n k)

theorem isGeneralizedIso_negDiagram : (negDiagram n k).cls.IsGeneralizedIso :=
  GenSBMap.isGeneralizedIso_ofHom (negSEPHom_mem_equivalences n k)

/-- **Theorem 10.5.4 for the example**: `[D]_* : Γ((-id)*W') → Γ(W')` is a bijection. -/
theorem bijOn_pushforward_negDiagram :
    BijOn (GenSBMap.pushforward (isGeneralizedIso_negDiagram n k)) (negSEP n k).E.sectionFunctors
      (epSEP n k).E.sectionFunctors :=
  (GenSBMap.theorem_10_5_4 (isGeneralizedIso_negDiagram n k)).2.1.2.2.2

/-- The diagram `W' ←P' (-id)*W' →P' W'`, both legs covering `-id`. -/
def foldDiagram : SDiagram (epSEP n k) (epSEP n k) :=
  ⟨negSEP n k, negSEPHom n k, negSEPHom_mem_equivalences n k, negSEPHom n k⟩

/-- **A non-trivial refinement**: `W' ←P' (-id)*W' →P' W'` refines `1_{W'}` through
`H = P'` (as `X ←F A →F X` refines `1_X` in §10.3). -/
theorem isRefinement_foldDiagram : (foldDiagram n k).IsRefinement (SDiagram.id (epSEP n k)) :=
  have h : SEP.NatEquiv (negSEPHom n k ≫ 𝟙 (epSEP n k)) (negSEPHom n k) := by
    rw [Category.comp_id]; exact .refl _
  ⟨negSEPHom n k, negSEPHom_mem_equivalences n k, h, h⟩

/-- Hence `[W' ←P' (-id)*W' →P' W'] = [1_{W'}]`. -/
theorem cls_foldDiagram : (foldDiagram n k).cls = (SDiagram.id (epSEP n k)).cls :=
  SDiagram.cls_eq_cls_of_equiv (isRefinement_foldDiagram n k).equiv

theorem isGeneralizedIso_foldDiagram : (foldDiagram n k).cls.IsGeneralizedIso :=
  ⟨foldDiagram n k, rfl, negSEPHom_mem_equivalences n k⟩

/-- **Theorem 10.5.4 for the example**: the push-forward along `W' ←P' (-id)*W' →P' W'`, whose
legs both cover `-id`, is the identity of `Γ(W')`. -/
theorem pushforward_foldDiagram :
    EqOn (GenSBMap.pushforward (isGeneralizedIso_foldDiagram n k)) _root_.id
      (epSEP n k).E.sectionFunctors := by
  intro f hf
  rw [(GenSBMap.theorem_10_5_4 (isGeneralizedIso_foldDiagram n k)).1 (SDiagram.id _)
    (SEP.equivalences.id_mem _) (cls_foldDiagram n k).symm |>.1 hf]
  exact SDiagram.pushforward_id _ hf

end Neg

/-! ### Remark 10.5.5: a strong bundle over `ℤ/3 × ℝ ⇉ ℝ` and the inversion -/

section Z3

open EpGroupoid.Examples TrivialBundle

variable (k : ℕ)

instance : ParacompactSpace (pullbackSpace (proj 1 k) trivialZ3EpGroupoid.src) :=
  (bundle 1 k).paracompactSpace_pullback trivialZ3EpGroupoid.PMor _

/-- **A strong bundle over `ℤ/3 × ℝ ⇉ ℝ`** (Definition 8.3.1): Part I's trivial bundle
`ℝ × ℝᵏ → ℝ` with `μ((g, x), w) = w` (the trivial action of `ℤ/3` on the fibres). -/
def z3EpBundle : EpStrongBundle trivialZ3EpGroupoid (bundle 1 k) where
  μ := pullbackProj' (proj 1 k) trivialZ3EpGroupoid.src
  isStrongBundleMap :=
    (bundle 1 k).isStrongBundleMap_pullbackProj' trivialZ3EpGroupoid.isScSmoothMap_src
  surjective w := ⟨⟨((1, w.1), w), rfl⟩, rfl⟩
  isLocalScDiffeo :=
    (bundle 1 k).isLocalScDiffeo_pullbackProj' trivialZ3EpGroupoid.isScSmoothMap_src
      trivialZ3EpGroupoid.isLocalScDiffeo_src
  μ_unit _ := rfl
  μ_comp _ _ _ _ _ := rfl

/-- `ℝ × ℝᵏ → ℝ` over `ℤ/3 × ℝ ⇉ ℝ` as an object of `SEP`. -/
def z3SEP : SEP.{0} :=
  ⟨_, _, trivialZ3EpGroupoid, _, proj 1 k, bundle 1 k, z3EpBundle k⟩

/-- **The inversion functor** `(g, x) ↦ (g⁻¹, x)` of `ℤ/3 × ℝ ⇉ ℝ` (a functor since `ℤ/3` is
abelian), the identity on objects. -/
def z3Inv : EpFunctor trivialZ3EpGroupoid trivialZ3EpGroupoid where
  obj := _root_.id
  mor p := (p.1⁻¹, p.2)
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp φ ψ _ := by
    change ((φ.1 * ψ.1)⁻¹, ψ.2) = (φ.1⁻¹ * ψ.1⁻¹, ψ.2)
    rw [mul_inv]
  mor_unit _ := by
    change ((1 : Multiplicative (ZMod 3))⁻¹, _) = (1, _)
    rw [inv_one]
    rfl
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_id
  isScSmoothMap_mor := trivialZ3EpGroupoid.isScSmoothMap_inv

/-- `id : W → W` is a strong bundle map covering the inversion (Definition 8.3.2):
`μ((g, x), w) = w = μ((g⁻¹, x), w)`. -/
theorem isMap_z3Inv : (z3EpBundle k).IsMap (z3EpBundle k) z3Inv _root_.id where
  isStrongBundleMap := StrongBundle.IsStrongBundleMap.id (bundle 1 k)
  map_μ _ _ _ := rfl

/-- The strong bundle functor `Inv` covering the inversion, a morphism of `SEP`. -/
def z3InvHom : z3SEP k ⟶ z3SEP k :=
  ⟨z3Inv, (isMap_z3Inv k).liftFunctor, (isMap_z3Inv k).isStrongBundleFunctor_liftFunctor⟩

/-- `Inv` is a strong bundle equivalence (it is its own inverse). -/
theorem z3InvHom_mem_equivalences : SEP.equivalences (z3InvHom k) :=
  EpStrongBundle.isStrongBundleEquivalence_of_inverse (isMap_z3Inv k) (isMap_z3Inv k)
    (fun _ => rfl) (fun _ => rfl) (fun p => Prod.ext (inv_inv p.1) rfl)
    (fun p => Prod.ext (inv_inv p.1) rfl) (fun _ => rfl) (fun _ => rfl)

/-! #### `|[1]| = |[Inv]|` -/

/-- `|[W ←1 W →Inv W]| = |[1_W]|`: `Inv` is the identity on objects. -/
theorem orbitMap_ofHom_z3InvHom :
    (SDiagram.ofHom (z3InvHom k)).orbitMap = (SDiagram.id (z3SEP k)).orbitMap := by
  rw [SDiagram.orbitMap_ofHom]
  change _ = (SDiagram.ofHom (𝟙 (z3SEP k))).orbitMap
  rw [SDiagram.orbitMap_ofHom]
  funext q
  induction q using Quotient.inductionOn with | h w => rfl

/-- The base generalized maps have the same orbit map too: `|[d]| = |[1_X]|`. -/
theorem base_orbitMap_ofHom_z3InvHom :
    (SDiagram.ofHom (z3InvHom k)).base.orbitMap = (SDiagram.id (z3SEP k)).base.orbitMap :=
  SDiagram.base_orbitMap_eq_of_orbitMap_eq (orbitMap_ofHom_z3InvHom k)

/-! #### `[1] ≠ [Inv]`, through the relation of the homomorphisms `γ` -/

/-- The generator `(1, 0)` of `G_0 = ℤ/3`. -/
def z3Gen : trivialZ3EpGroupoid.Isotropy (0 : Fin 1 → ℝ) :=
  ⟨(Multiplicative.ofAdd 1, 0), rfl, rfl⟩

/-- For `[1_W]`, the generator is related to itself (`γ = 1`). -/
theorem isotropyRel_id :
    (SDiagram.id (z3SEP k)).base.IsotropyRel (x := (0 : Fin 1 → ℝ)) (x' := (0 : Fin 1 → ℝ))
      z3Gen z3Gen := by
  refine ⟨(0 : Fin 1 → ℝ), z3Gen, trivialZ3EpGroupoid.unit 0, rfl, rfl,
    trivialZ3EpGroupoid.unit 0, rfl, rfl, ?_, ?_⟩ <;>
  exact GroupoidStr.Isotropy.ext (Prod.ext (by
    change (1 * Multiplicative.ofAdd (1 : ZMod 3)) * 1⁻¹ = Multiplicative.ofAdd 1
    rw [one_mul, inv_one, mul_one]) rfl)

/-- For `[W ←1 W →Inv W]`, the generator is not related to itself: a related pair is
`(g, g⁻¹)` up to conjugation, and conjugation is trivial in the abelian `ℤ/3`, where
`g⁻¹ ≠ g` for the generator. -/
theorem not_isotropyRel_inv :
    ¬ (SDiagram.ofHom (z3InvHom k)).base.IsotropyRel (x := (0 : Fin 1 → ℝ))
      (x' := (0 : Fin 1 → ℝ)) z3Gen z3Gen := by
  rintro ⟨z, h, a, ha, ha', b, hb, hb', h₁, h₂⟩
  have e₁ : ((a : Multiplicative (ZMod 3) × (Fin 1 → ℝ)).1 *
      (h.val : Multiplicative (ZMod 3) × (Fin 1 → ℝ)).1) *
      (a : Multiplicative (ZMod 3) × (Fin 1 → ℝ)).1⁻¹ = Multiplicative.ofAdd 1 :=
    congrArg (fun g : trivialZ3EpGroupoid.Isotropy (0 : Fin 1 → ℝ) => g.val.1) h₁
  have e₂ : ((b : Multiplicative (ZMod 3) × (Fin 1 → ℝ)).1 *
      (h.val : Multiplicative (ZMod 3) × (Fin 1 → ℝ)).1⁻¹) *
      (b : Multiplicative (ZMod 3) × (Fin 1 → ℝ)).1⁻¹ = Multiplicative.ofAdd 1 :=
    congrArg (fun g : trivialZ3EpGroupoid.Isotropy (0 : Fin 1 → ℝ) => g.val.1) h₂
  rw [mul_comm, inv_mul_cancel_left] at e₁ e₂
  rw [e₁] at e₂
  exact absurd e₂ (by decide)

/-- **2021 Remark 10.5.5, p. 508 (new in the 2021 edition)**, the negative half: two generalized
strong bundle isomorphisms `[D], [D'] : W → W` with `|[D]| = |[D']|` and `[D] ≠ [D']`, namely
`[1_W]` and `[W ←1 W →Inv W]` for `W = ℝ × ℝᵏ` over `ℤ/3 × ℝ ⇉ ℝ`.  Already the generalized maps
of the base ep-groupoids differ. -/
theorem remark_10_5_5 :
    (SDiagram.ofHom (z3InvHom k)).cls.IsGeneralizedIso ∧
      (SDiagram.id (z3SEP k)).cls.IsGeneralizedIso ∧
      (SDiagram.ofHom (z3InvHom k)).cls.orbitMap = (SDiagram.id (z3SEP k)).cls.orbitMap ∧
      (SDiagram.ofHom (z3InvHom k)).cls.base ≠ (SDiagram.id (z3SEP k)).cls.base ∧
      (SDiagram.ofHom (z3InvHom k)).cls ≠ (SDiagram.id (z3SEP k)).cls := by
  have hb : (SDiagram.ofHom (z3InvHom k)).cls.base ≠ (SDiagram.id (z3SEP k)).cls.base := by
    intro h
    have he := EPLocalization.EPLoc.homMk_eq_homMk_iff.1 h
    exact not_isotropyRel_inv k ((he.isotropyRel_iff _ _).2 (isotropyRel_id k))
  exact ⟨GenSBMap.isGeneralizedIso_ofHom (z3InvHom_mem_equivalences k),
    GenSBMap.isGeneralizedIso_ofHom (SEP.equivalences.id_mem _), orbitMap_ofHom_z3InvHom k, hb,
    fun h => hb (congrArg GenSBMap.base h)⟩

/-- **Remark 10.5.5, the positive half, for the example**: `[Inv]_* = [1]_*` on `Γ(P, μ)`
(Theorem 10.5.4), although `[Inv] ≠ [1]`. -/
theorem pushforward_inv_eq_pushforward_id (hf : (SDiagram.ofHom (z3InvHom k)).cls.IsGeneralizedIso)
    (hf' : (SDiagram.id (z3SEP k)).cls.IsGeneralizedIso) :
    EqOn (GenSBMap.pushforward hf) (GenSBMap.pushforward hf') (z3SEP k).E.sectionFunctors :=
  ((GenSBMap.theorem_10_5_4 hf).2.2.2.2 _ hf' (orbitMap_ofHom_z3InvHom k)).1

end Z3

end StrongBundleLocalizationExamples

end Polyfold
