import Polyfold.Chapter11.BranchedEquivalence
import Polyfold.Chapter10.LocalizationCategory
import Polyfold.Chapter10.EquivalenceRefinement

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.3 "Branched Ep⁺-Subgroupoids and Equivalences", pp. 536–538 (2017:
pp. 390–391): the push-forward and pull-back along **generalized isomorphisms**, the functorial
properties on p. 537, and **Theorem 11.3.3** (2017: Theorem 11.3).  The equivalence case and
Definition 11.3.1, Lemma 11.3.2 are in `BranchedEquivalence.lean`.

# Branched ep⁺-subgroupoids along generalized isomorphisms

## The text, paraphrased

(p. 536) A generalized isomorphism `f : X → Y` is represented by `X ←F A →G Y`, `F`, `G`
equivalences; `f_* = G_* F^*` and `f^* = F_* G^*`, independent of the diagram: for a common
refinement `H : A″ → A` with `F ∘ H ≃ F″`, `G ∘ H ≃ G″`,
`G_* F^* Θ = G_* H_* H^* F^* Θ = G″_* F″^* Θ`.  (p. 537) `(g ∘ f)_* = g_* ∘ f_*`,
`(g ∘ f)^* = f^* ∘ g^*`, `(f⁻¹)_* = f^*` ("easily verified").  Theorem 11.3.3 (statement in
`BranchedEquivalence.lean`): `f_*Θ = G_* F^* Θ` and `f^*Θ' = F_* G^* Θ'` reduce to equivalences.

## What is formalized

* `EPLocalization.Diagram.pushTheta` (`Φ_* F^*`), `Diagram.pullTheta` (`F_* Φ^*`);
  `pushTheta_eq_of_isRefinement`, `pullTheta_eq_of_isRefinement`, `pushTheta_eq_of_equiv`,
  `pullTheta_eq_of_equiv` (the argument of p. 536); `IsRefinement.isEquivalence_Φ_iff`.
* `EPLoc.rep` (a chosen representative), `EPLoc.pushTheta`, `EPLoc.pullTheta` (`f_*`, `f^*`);
  `pushTheta_homMk`, `pullTheta_homMk` (independence of the representative);
  `isFunctorial_pushTheta`, `isFunctorial_pullTheta`.
* p. 537: `pushTheta_comp` (`(g ∘ f)_* = g_* ∘ f_*`), `pullTheta_comp` (`(g ∘ f)^* = f^* ∘ g^*`),
  `pushTheta_inv` (`(f⁻¹)_* = f^*`), `pullTheta_pushTheta`, `pushTheta_pullTheta`; through the base
  change in the weak fibred product `WeakFibredProduct.pushforwardTheta_projRight_pullbackTheta`,
  `pushforwardTheta_projLeft_pullbackTheta`.  `orbitSupp_pushTheta` (`|f_*Θ| = |Θ| ∘ |f|⁻¹`).
* **Theorem 11.3.3**: `theorem_11_3_3_one` … `theorem_11_3_3_six`, `isNDimensional_pushTheta`,
  `isNDimensional_pullTheta`.
* Witnesses: `Examples.isBranchedEpSubgroupoid_reflectionTheta` (`Θ₀ = 1_{0}` on `ℤ/2 ⋉ ℝ`),
  `isBranchedEpSubgroupoid_pullbackTheta_reflectionCover`,
  `pullbackTheta_reflectionCover_two_points` (`F^*Θ₀` is `1` at two different objects of `X_𝒰`),
  `pushforwardTheta_pullbackTheta_reflectionCover`;
  the generalized isomorphism `[ℤ/2 ⋉ ℝ ←F X_𝒰 →1 X_𝒰]` (`isGeneralizedIso_reflectionCoverDiagram`)
  with `pushTheta_reflectionCoverDiagram`.

## What the text leaves implicit, and the choices made

* `f_*`, `f^*` are computed on a chosen representative `rep f`.  For `f^*` no hypothesis is needed:
  it is independent of the representative for every generalized map; `f_*` is independent of it
  when `Φ` is an equivalence, i.e. for generalized isomorphisms (Theorem 10.3.10); `(g ∘ f)^*` holds
  for all generalized maps, `(g ∘ f)_*` for generalized isomorphisms.
* "Easily verified" (p. 537): the composite `[e] ∘ [d]` is represented through the weak fibred
  product `A ×_Y B` (Theorem 10.3.8); the step is the base change `(π_B)_* (π_A)^* = G^* Φ_*`
  (`Φ` an equivalence), resp. `(π_A)_* (π_B)^* = Φ^* G_*` (`G` an equivalence).
* Nothing here uses Theorem 10.3.19 (which does not hold as we read it, `not_theorem_10_3_19`).

## Not formalized (G-items)

* Lemma 11.3.4, Theorem 11.3.5 and Definition 11.3.6 (orientations): the push-forward of section
  functors of `Gr̂(X) → X_∞` needs the tangent map of an equivalence acting on oriented tangent sets
  (`OrTangent`, which Chapter 9 moves only by maps `TX → TX` of one M-polyfold), and Theorem 11.3.5
  the transport of oriented local branching structures (`IsOrientedAt` across M-polyfolds).
* Theorem 11.3.7 (`(Tf)^* TΘ' = T(f^*Θ')`; proof left to the reader): needs the tangent functor
  `Tf = [Td]` on generalized maps, `submanifoldTangent` under sc-diffeomorphisms between different
  M-polyfolds, and the transport of Chapter 9's hypothesis `HasIndependentTangentSums`.
* Theorems 11.3.8, 11.3.9 (`f_*∂Θ = ∂(f_*Θ)`, oriented boundaries; proofs left to the reader): need
  the invariance of `submanifoldBoundary` (degeneracy index of the induced structure) under
  sc-diffeomorphisms between different M-polyfolds, the same independence hypothesis, and for 11.3.9
  the orientation transport above.
-/

set_option maxSynthPendingDepth 3

open Set Function Module Submodule

noncomputable section

namespace Polyfold

universe u v w

/-! ### Base change in the weak fibred product -/

section BaseChange

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {Obj'' Mor'' : Type w} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Z : EpGroupoid Obj'' Mor''}
  {F : EpFunctor X Y} {G : EpFunctor Z Y}

namespace WeakFibredProduct

open EpFunctor

/-- **Base change for push-forwards**: for the weak fibred product `X ×_Y Z` of an equivalence
`F : X → Y` and `G : Z → Y`, `(π_Z)_* (π_X)^* Θ = G^* F_* Θ` (both are `Θ(x)` at `z`, for any
`ϕ : F(x) → G(z)`). -/
theorem pushforwardTheta_projRight_pullbackTheta (hF : F.IsEquivalence) (h : Admissible F G)
    {Θ : Obj → ℚ} (hΘ : X.IsFunctorial Θ) :
    (projRight F G h).pushforwardTheta ((projLeft F G h).pullbackTheta Θ) =
      G.pullbackTheta (F.pushforwardTheta Θ) := by
  funext z
  obtain ⟨x, φ, hs, ht⟩ := hF.exists_iso (G.obj z)
  have hp : Z.Isomorphic ((projRight F G h).obj (WeakFibredProduct.Obj.mk F G x φ z hs ht)) z :=
    Z.isomorphic_refl z
  rw [pushforwardTheta_eq (isEquivalence_projRight hF h).full
    ((projLeft F G h).isFunctorial_pullbackTheta hΘ) hp, pullbackTheta_apply,
    pullbackTheta_apply, pushforwardTheta_eq hF.full hΘ ⟨φ, hs, ht⟩]
  rfl

/-- **Base change for pull-backs**: for an equivalence `G : Z → Y`,
`(π_X)_* (π_Z)^* Θ = F^* G_* Θ`. -/
theorem pushforwardTheta_projLeft_pullbackTheta (hG : G.IsEquivalence) (h : Admissible F G)
    {Θ : Obj'' → ℚ} (hΘ : Z.IsFunctorial Θ) :
    (projLeft F G h).pushforwardTheta ((projRight F G h).pullbackTheta Θ) =
      F.pullbackTheta (G.pushforwardTheta Θ) := by
  funext x
  obtain ⟨z, ψ, hs, ht⟩ := hG.exists_iso (F.obj x)
  have h₁ : Y.src (Y.inv ψ) = F.obj x := by rw [Y.src_inv, ht]
  have h₂ : Y.tgt (Y.inv ψ) = G.obj z := by rw [Y.tgt_inv, hs]
  have hp : X.Isomorphic
      ((projLeft F G h).obj (WeakFibredProduct.Obj.mk F G x (Y.inv ψ) z h₁ h₂)) x :=
    X.isomorphic_refl x
  rw [pushforwardTheta_eq (isEquivalence_projLeft hG h).full
    ((projRight F G h).isFunctorial_pullbackTheta hΘ) hp, pullbackTheta_apply,
    pullbackTheta_apply, pushforwardTheta_eq hG.full hΘ ⟨ψ, hs, ht⟩]
  rfl

end WeakFibredProduct

end BaseChange

/-! ### Generalized isomorphisms -/

namespace EPLocalization

open EpFunctor WeakFibredProduct CategoryTheory

namespace Diagram

variable {X Y Z : EP.{u}}

/-- `d_*Θ = Φ_* F^* Θ` for a diagram `d : X ←F A →Φ Y` (2021 p. 536: `f_* = G_* F^*`). -/
def pushTheta (d : Diagram X Y) (Θ : X.Obj → ℚ) : Y.Obj → ℚ :=
  d.Φ.pushforwardTheta (d.F.pullbackTheta Θ)

/-- `d^*Θ' = F_* Φ^* Θ'` for a diagram `d : X ←F A →Φ Y` (2021 p. 536: `f^* = F_* G^*`). -/
def pullTheta (d : Diagram X Y) (Θ' : Y.Obj → ℚ) : X.Obj → ℚ :=
  d.F.pushforwardTheta (d.Φ.pullbackTheta Θ')

/-- A refinement `d'` of `d` has `Φ'` an equivalence iff `Φ` is one (Propositions 10.1.5,
10.1.6). -/
theorem IsRefinement.isEquivalence_Φ_iff {d d' : Diagram X Y} (h : d'.IsRefinement d) :
    d.Φ.IsEquivalence ↔ d'.Φ.IsEquivalence := by
  obtain ⟨H, hH, -, hΦH⟩ := h
  refine ⟨fun hΦ => (proposition_10_1_5 hΦH).1 (hΦ.comp hH), fun hΦ' => ?_⟩
  exact proposition_10_1_6 hH ((proposition_10_1_5 hΦH).2 hΦ')

/-- **The refinement step of p. 536**: `G″_* F″^* Θ = G_* F^* Θ` for a refinement. -/
theorem pushTheta_eq_of_isRefinement {d d' : Diagram X Y} (h : d'.IsRefinement d)
    (hΦ : d.Φ.IsEquivalence) {Θ : X.Obj → ℚ} (hΘ : X.X.IsFunctorial Θ) :
    d'.pushTheta Θ = d.pushTheta Θ := by
  have hΦ' := h.isEquivalence_Φ_iff.1 hΦ
  obtain ⟨H, hH, hF, hΦH⟩ := h
  have hΦH' : (d.Φ.comp H).IsEquivalence := hΦ.comp hH
  unfold pushTheta
  rw [← pullbackTheta_eq_of_naturallyEquivalent hF hΘ,
    ← pushforwardTheta_eq_of_naturallyEquivalent hΦH'.full hΦ'.full hΦH
      ((d.F.comp H).isFunctorial_pullbackTheta hΘ),
    pullbackTheta_comp, pushforwardTheta_comp hΦ.full hH.full hΦH'.full
      (H.isFunctorial_pullbackTheta (d.F.isFunctorial_pullbackTheta hΘ)),
    pushforwardTheta_pullbackTheta hH.essSurj (d.F.isFunctorial_pullbackTheta hΘ)]

/-- The refinement step for pull-backs (no hypothesis on `Φ`). -/
theorem pullTheta_eq_of_isRefinement {d d' : Diagram X Y} (h : d'.IsRefinement d)
    {Θ' : Y.Obj → ℚ} (hΘ' : Y.X.IsFunctorial Θ') : d'.pullTheta Θ' = d.pullTheta Θ' := by
  obtain ⟨H, hH, hF, hΦH⟩ := h
  have hFH : (d.F.comp H).IsEquivalence := d.isEquivalence_F.comp hH
  unfold pullTheta
  rw [← pullbackTheta_eq_of_naturallyEquivalent hΦH hΘ',
    ← pushforwardTheta_eq_of_naturallyEquivalent hFH.full d'.isEquivalence_F.full hF
      ((d.Φ.comp H).isFunctorial_pullbackTheta hΘ'),
    pullbackTheta_comp, pushforwardTheta_comp d.isEquivalence_F.full hH.full hFH.full
      (H.isFunctorial_pullbackTheta (d.Φ.isFunctorial_pullbackTheta hΘ')),
    pushforwardTheta_pullbackTheta hH.essSurj (d.Φ.isFunctorial_pullbackTheta hΘ')]

/-- **Well-definedness of `f_*` (2021 p. 536)**: equivalent diagrams with `Φ` an equivalence
have the same push-forwards. -/
theorem pushTheta_eq_of_equiv {d d' : Diagram X Y} (h : Equiv d d') (hΦ : d.Φ.IsEquivalence)
    {Θ : X.Obj → ℚ} (hΘ : X.X.IsFunctorial Θ) : d.pushTheta Θ = d'.pushTheta Θ := by
  obtain ⟨d'', h1, h2⟩ := h
  have hΦ'' := h1.isEquivalence_Φ_iff.1 hΦ
  rw [← pushTheta_eq_of_isRefinement h1 hΦ hΘ,
    pushTheta_eq_of_isRefinement h2 (h2.isEquivalence_Φ_iff.2 hΦ'') hΘ]

/-- **Well-definedness of `f^*` (2021 p. 536, "similarly")**: equivalent diagrams have the same
pull-backs. -/
theorem pullTheta_eq_of_equiv {d d' : Diagram X Y} (h : Equiv d d') {Θ' : Y.Obj → ℚ}
    (hΘ' : Y.X.IsFunctorial Θ') : d.pullTheta Θ' = d'.pullTheta Θ' := by
  obtain ⟨d'', h1, h2⟩ := h
  rw [← pullTheta_eq_of_isRefinement h1 hΘ', pullTheta_eq_of_isRefinement h2 hΘ']

end Diagram

namespace EPLoc

variable {X Y Z : EP.{u}}

/-- A chosen representative diagram of a generalized map. -/
def rep (f : of X ⟶ of Y) : Diagram X Y := Quotient.out f

theorem homMk_rep (f : of X ⟶ of Y) : homMk (rep f) = f := Quotient.out_eq f

theorem equiv_rep_homMk (d : Diagram X Y) : Diagram.Equiv (rep (homMk d)) d :=
  Quotient.mk_out (s := Diagram.setoid X Y) d

/-- The representative of a generalized isomorphism has `Φ` an equivalence (Theorem 10.3.10). -/
theorem isEquivalence_rep_Φ {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) :
    (rep f).Φ.IsEquivalence :=
  (theorem_10_3_10 (rep f)).1.1 (by rw [homMk_rep]; exact hf)

/-- **The push-forward `f_*Θ = G_* F^* Θ`** along a generalized map `f = [X ←F A →G Y]`
(2021 p. 536), computed on a chosen representative; for a generalized isomorphism it does not
depend on the representative (`pushTheta_homMk`). -/
def pushTheta (f : of X ⟶ of Y) (Θ : X.Obj → ℚ) : Y.Obj → ℚ := (rep f).pushTheta Θ

/-- **The pull-back `f^*Θ' = F_* G^* Θ'`** along a generalized map `f = [X ←F A →G Y]`
(2021 p. 536); it does not depend on the representative (`pullTheta_homMk`). -/
def pullTheta (f : of X ⟶ of Y) (Θ' : Y.Obj → ℚ) : X.Obj → ℚ := (rep f).pullTheta Θ'

/-- **`f_*` is well defined (2021 p. 536)**: for every representative `d` (with `Φ` an
equivalence) of the generalized isomorphism `[d]`, `[d]_*Θ = Φ_* F^* Θ`. -/
theorem pushTheta_homMk (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) {Θ : X.Obj → ℚ}
    (hΘ : X.X.IsFunctorial Θ) : pushTheta (homMk d) Θ = d.pushTheta Θ :=
  (Diagram.pushTheta_eq_of_equiv (equiv_rep_homMk d).symm hΦ hΘ).symm

/-- **`f^*` is well defined (2021 p. 536)**: `[d]^*Θ' = F_* Φ^* Θ'` for every representative. -/
theorem pullTheta_homMk (d : Diagram X Y) {Θ' : Y.Obj → ℚ} (hΘ' : Y.X.IsFunctorial Θ') :
    pullTheta (homMk d) Θ' = d.pullTheta Θ' :=
  Diagram.pullTheta_eq_of_equiv (equiv_rep_homMk d) hΘ'

theorem isFunctorial_pushTheta {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ : X.Obj → ℚ}
    (hΘ : X.X.IsFunctorial Θ) : Y.X.IsFunctorial (pushTheta f Θ) :=
  isFunctorial_pushforwardTheta (isEquivalence_rep_Φ hf).full
    ((rep f).F.isFunctorial_pullbackTheta hΘ)

theorem isFunctorial_pullTheta (f : of X ⟶ of Y) {Θ' : Y.Obj → ℚ}
    (hΘ' : Y.X.IsFunctorial Θ') : X.X.IsFunctorial (pullTheta f Θ') :=
  isFunctorial_pushforwardTheta (rep f).isEquivalence_F.full
    ((rep f).Φ.isFunctorial_pullbackTheta hΘ')

/-- **`(g ∘ f)_* = g_* ∘ f_*`** (2021 p. 537) for generalized isomorphisms `f`, `g`: the
composite `[d] ∘ [e]` is represented through the weak fibred product, and the base change
`(π_B)_* (π_A)^* = G^* Φ_*` turns `(Ψ ∘ π_B)_* (F ∘ π_A)^*` into `Ψ_* G^* Φ_* F^*`. -/
theorem pushTheta_comp {f : of X ⟶ of Y} {g : of Y ⟶ of Z} (hf : IsGeneralizedIso f)
    (hg : IsGeneralizedIso g) {Θ : X.Obj → ℚ} (hΘ : X.X.IsFunctorial Θ) :
    pushTheta (f ≫ g) Θ = pushTheta g (pushTheta f Θ) := by
  have hd := isEquivalence_rep_Φ hf
  have he := isEquivalence_rep_Φ hg
  have hπ := isEquivalence_projRight hd ((rep f).admissible (rep g))
  have hc : ((rep f).comp (rep g)).Φ.IsEquivalence := he.comp hπ
  have hfg : f ≫ g = homMk ((rep f).comp (rep g)) := by
    rw [← homMk_comp, homMk_rep, homMk_rep]
  rw [hfg, pushTheta_homMk _ hc hΘ]
  change ((rep g).Φ.comp (projRight _ _ _)).pushforwardTheta
    (((rep f).F.comp (projLeft _ _ _)).pullbackTheta Θ) = _
  rw [pullbackTheta_comp, pushforwardTheta_comp he.full hπ.full hc.full
    ((projLeft _ _ _).isFunctorial_pullbackTheta ((rep f).F.isFunctorial_pullbackTheta hΘ)),
    pushforwardTheta_projRight_pullbackTheta hd _ ((rep f).F.isFunctorial_pullbackTheta hΘ)]
  rfl

/-- **`(g ∘ f)^* = f^* ∘ g^*`** (2021 p. 537), for all generalized maps. -/
theorem pullTheta_comp (f : of X ⟶ of Y) (g : of Y ⟶ of Z) {Θ'' : Z.Obj → ℚ}
    (hΘ'' : Z.X.IsFunctorial Θ'') : pullTheta (f ≫ g) Θ'' = pullTheta f (pullTheta g Θ'') := by
  have hG := (rep g).isEquivalence_F
  have hπ := isEquivalence_projLeft hG ((rep f).admissible (rep g))
  have hc := ((rep f).comp (rep g)).isEquivalence_F
  have hfg : f ≫ g = homMk ((rep f).comp (rep g)) := by
    rw [← homMk_comp, homMk_rep, homMk_rep]
  rw [hfg, pullTheta_homMk _ hΘ'']
  change ((rep f).F.comp (projLeft _ _ _)).pushforwardTheta
    (((rep g).Φ.comp (projRight _ _ _)).pullbackTheta Θ'') = _
  rw [pullbackTheta_comp, pushforwardTheta_comp (rep f).isEquivalence_F.full hπ.full hc.full
    ((projRight _ _ _).isFunctorial_pullbackTheta ((rep g).Φ.isFunctorial_pullbackTheta hΘ'')),
    pushforwardTheta_projLeft_pullbackTheta hG _ ((rep g).Φ.isFunctorial_pullbackTheta hΘ'')]
  rfl

/-- **`(f⁻¹)_* = f^*`** (2021 p. 537): the inverse of `[X ←F A →Φ Y]` is `[Y ←Φ A →F X]`
(Theorem 10.3.10 (2)). -/
theorem pushTheta_inv {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {g : of Y ⟶ of X}
    (h₁ : f ≫ g = 𝟙 _) (h₂ : g ≫ f = 𝟙 _) {Θ' : Y.Obj → ℚ} (hΘ' : Y.X.IsFunctorial Θ') :
    pushTheta g Θ' = pullTheta f Θ' := by
  have hd := isEquivalence_rep_Φ hf
  rw [← homMk_rep f] at h₁ h₂
  rw [(theorem_10_3_10 (rep f)).2 hd g h₁ h₂, pushTheta_homMk _ (rep f).isEquivalence_F hΘ']
  rfl

/-- `f^* f_* Θ = Θ` for a generalized isomorphism (Lemma 11.3.2 (1) twice). -/
theorem pullTheta_pushTheta {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ : X.Obj → ℚ}
    (hΘ : X.X.IsFunctorial Θ) : pullTheta f (pushTheta f Θ) = Θ := by
  have hd := isEquivalence_rep_Φ hf
  unfold pullTheta pushTheta Diagram.pullTheta Diagram.pushTheta
  rw [pullbackTheta_pushforwardTheta hd.full ((rep f).F.isFunctorial_pullbackTheta hΘ),
    pushforwardTheta_pullbackTheta (rep f).isEquivalence_F.essSurj hΘ]

/-- `f_* f^* Θ' = Θ'` for a generalized isomorphism. -/
theorem pushTheta_pullTheta {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ' : Y.Obj → ℚ}
    (hΘ' : Y.X.IsFunctorial Θ') : pushTheta f (pullTheta f Θ') = Θ' := by
  have hd := isEquivalence_rep_Φ hf
  unfold pullTheta pushTheta Diagram.pullTheta Diagram.pushTheta
  rw [pullbackTheta_pushforwardTheta (rep f).isEquivalence_F.full
    ((rep f).Φ.isFunctorial_pullbackTheta hΘ'), pushforwardTheta_pullbackTheta hd.essSurj hΘ']

/-- **The identity `|f_*Θ| = |Θ| ∘ |f|⁻¹`** of the proof of Theorem 11.3.3 (p. 538), in the form
`|supp(f_*Θ)| = |f|(|supp(Θ)|)`. -/
theorem orbitSupp_pushTheta {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ : X.Obj → ℚ}
    (hΘ : X.X.IsFunctorial Θ) :
    Y.X.orbitSupp (pushTheta f Θ) = orbitMap f '' X.X.orbitSupp Θ := by
  set d := rep f
  have hd := isEquivalence_rep_Φ hf
  have hfd : orbitMap f = d.orbitMap := by rw [← homMk_rep f]; rfl
  rw [hfd]
  change Y.X.orbitSupp (d.Φ.pushforwardTheta (d.F.pullbackTheta Θ)) = _
  rw [orbitSupp_pushforwardTheta hd.full (d.F.isFunctorial_pullbackTheta hΘ),
    d.F.orbitSupp_pullbackTheta hΘ]
  ext q
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨d.F.orbitMap r, hr, d.orbitMap_orbitMap_F r⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨r, rfl⟩ := d.isEquivalence_F.isHomeomorph_orbitMap.surjective p
    exact ⟨r, hp, (d.orbitMap_orbitMap_F r).symm⟩

/-! #### Theorem 11.3.3 -/

/-- **2021 Theorem 11.3.3 (1), p. 537 (2017: Theorem 11.3, p. 390)**: for a generalized
isomorphism `f : X → Y` and a branched ep⁺-subgroupoid `Θ` of `X`, `f_*Θ` is a branched
ep⁺-subgroupoid of `Y`. -/
theorem theorem_11_3_3_one {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ : X.Obj → ℚ}
    (hΘ : X.X.IsBranchedEpSubgroupoid Θ) : Y.X.IsBranchedEpSubgroupoid (pushTheta f Θ) :=
  isBranchedEpSubgroupoid_pushforwardTheta (isEquivalence_rep_Φ hf)
    (isBranchedEpSubgroupoid_pullbackTheta (rep f).isEquivalence_F hΘ)

/-- **2021 Theorem 11.3.3 (2), p. 537 (2017: Theorem 11.3, p. 390)**: for a branched
ep⁺-subgroupoid `Θ'` of `Y`, `f^*Θ'` is one of `X`. -/
theorem theorem_11_3_3_two {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ' : Y.Obj → ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') : X.X.IsBranchedEpSubgroupoid (pullTheta f Θ') :=
  isBranchedEpSubgroupoid_pushforwardTheta (rep f).isEquivalence_F
    (isBranchedEpSubgroupoid_pullbackTheta (isEquivalence_rep_Φ hf) hΘ')

/-- **2021 Theorem 11.3.3 (3)**: `f_*` and `f^*` preserve closedness (Definition 9.1.6 (1)). -/
theorem theorem_11_3_3_three {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ : X.Obj → ℚ}
    {Θ' : Y.Obj → ℚ} (hΘ : X.X.IsFunctorial Θ) (hΘ' : Y.X.IsFunctorial Θ') :
    (X.X.IsClosedBranched Θ → Y.X.IsClosedBranched (pushTheta f Θ)) ∧
      (Y.X.IsClosedBranched Θ' → X.X.IsClosedBranched (pullTheta f Θ')) :=
  ⟨fun hc => isClosedBranched_pushforwardTheta (isEquivalence_rep_Φ hf)
      ((rep f).F.isFunctorial_pullbackTheta hΘ) ((rep f).F.isClosedBranched_pullbackTheta hΘ hc),
    fun hc => isClosedBranched_pushforwardTheta (rep f).isEquivalence_F
      ((rep f).Φ.isFunctorial_pullbackTheta hΘ') ((rep f).Φ.isClosedBranched_pullbackTheta hΘ' hc)⟩

/-- **2021 Theorem 11.3.3 (4)**: `f_*` and `f^*` preserve compactness (Definition 9.1.6 (2)). -/
theorem theorem_11_3_3_four {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ : X.Obj → ℚ}
    {Θ' : Y.Obj → ℚ} (hΘ : X.X.IsFunctorial Θ) (hΘ' : Y.X.IsFunctorial Θ') :
    (X.X.IsCompactBranched Θ → Y.X.IsCompactBranched (pushTheta f Θ)) ∧
      (Y.X.IsCompactBranched Θ' → X.X.IsCompactBranched (pullTheta f Θ')) :=
  ⟨fun hc => (rep f).Φ.isCompactBranched_pushforwardTheta (isEquivalence_rep_Φ hf).full
      ((rep f).F.isFunctorial_pullbackTheta hΘ)
      (isCompactBranched_pullbackTheta (rep f).isEquivalence_F hΘ hc),
    fun hc => (rep f).F.isCompactBranched_pushforwardTheta (rep f).isEquivalence_F.full
      ((rep f).Φ.isFunctorial_pullbackTheta hΘ')
      (isCompactBranched_pullbackTheta (isEquivalence_rep_Φ hf) hΘ' hc)⟩

/-- **2021 Theorem 11.3.3 (5)**: `f_*` and `f^*` preserve orbifold-type and manifold-type
(Definition 9.1.8). -/
theorem theorem_11_3_3_five {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ : X.Obj → ℚ}
    {Θ' : Y.Obj → ℚ} (hΘ : X.X.IsFunctorial Θ) (hΘ' : Y.X.IsFunctorial Θ') :
    (EpGroupoid.IsOrbifoldType Θ → EpGroupoid.IsOrbifoldType (pushTheta f Θ)) ∧
      (EpGroupoid.IsOrbifoldType Θ' → EpGroupoid.IsOrbifoldType (pullTheta f Θ')) ∧
      (X.X.IsManifoldType Θ → Y.X.IsManifoldType (pushTheta f Θ)) ∧
      (Y.X.IsManifoldType Θ' → X.X.IsManifoldType (pullTheta f Θ')) :=
  ⟨fun h => (rep f).Φ.isOrbifoldType_pushforwardTheta ((rep f).F.isOrbifoldType_pullbackTheta h),
    fun h => (rep f).F.isOrbifoldType_pushforwardTheta ((rep f).Φ.isOrbifoldType_pullbackTheta h),
    fun h => isManifoldType_pushforwardTheta (isEquivalence_rep_Φ hf)
      ((rep f).F.isFunctorial_pullbackTheta hΘ)
      (isManifoldType_pullbackTheta (rep f).isEquivalence_F h),
    fun h => isManifoldType_pushforwardTheta (rep f).isEquivalence_F
      ((rep f).Φ.isFunctorial_pullbackTheta hΘ')
      (isManifoldType_pullbackTheta (isEquivalence_rep_Φ hf) h)⟩

/-- **2021 Theorem 11.3.3 (6)**: `f_*` and `f^*` preserve `n`-dimensionality and the dimensional
decomposition of Proposition 9.1.11 (`IsDimDecomposition`). -/
theorem theorem_11_3_3_six {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) :
    (∀ {Θ : X.Obj → ℚ} {Θk : ℕ → X.Obj → ℚ}, X.X.IsDimDecomposition Θ Θk →
      Y.X.IsDimDecomposition (pushTheta f Θ) fun k => pushTheta f (Θk k)) ∧
    (∀ {Θ' : Y.Obj → ℚ} {Θk : ℕ → Y.Obj → ℚ}, Y.X.IsDimDecomposition Θ' Θk →
      X.X.IsDimDecomposition (pullTheta f Θ') fun k => pullTheta f (Θk k)) :=
  ⟨fun h => isDimDecomposition_pushforwardTheta (isEquivalence_rep_Φ hf)
      (isDimDecomposition_pullbackTheta (rep f).isEquivalence_F h),
    fun h => isDimDecomposition_pushforwardTheta (rep f).isEquivalence_F
      (isDimDecomposition_pullbackTheta (isEquivalence_rep_Φ hf) h)⟩

/-- **2021 Theorem 11.3.3 (6), `n`-dimensionality**. -/
theorem isNDimensional_pushTheta {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ : X.Obj → ℚ}
    (hΘ : X.X.IsFunctorial Θ) {n : ℕ} (h : X.X.IsNDimensional Θ n) :
    Y.X.IsNDimensional (pushTheta f Θ) n :=
  isNDimensional_pushforwardTheta (isEquivalence_rep_Φ hf)
    ((rep f).F.isFunctorial_pullbackTheta hΘ)
    (isNDimensional_pullbackTheta (rep f).isEquivalence_F h)

theorem isNDimensional_pullTheta {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ' : Y.Obj → ℚ}
    (hΘ' : Y.X.IsFunctorial Θ') {n : ℕ} (h : Y.X.IsNDimensional Θ' n) :
    X.X.IsNDimensional (pullTheta f Θ') n :=
  isNDimensional_pushforwardTheta (rep f).isEquivalence_F
    ((rep f).Φ.isFunctorial_pullbackTheta hΘ')
    (isNDimensional_pullbackTheta (isEquivalence_rep_Φ hf) h)

end EPLoc

end EPLocalization

/-! ### Witnesses: `ℤ/2 ⋉ ℝ` and its two-set covering -/

namespace EpGroupoid.Examples

open EpFunctor EPLocalization EPLoc CategoryTheory

/-- `Θ₀ = 1_{0}`, the indicator of the fixed point `0` of `ℤ/2 ⋉ ℝ`. -/
def reflectionTheta : (Fin 1 → ℝ) → ℚ := ({0} : Set (Fin 1 → ℝ)).indicator 1

theorem reflectionTheta_apply (z : Fin 1 → ℝ) :
    reflectionTheta z = if z = 0 then 1 else 0 := by
  by_cases h : z = 0 <;> simp [reflectionTheta, h]

open scoped Classical in
/-- The local branching structure of `Θ₀` at `0`: `U = ℝ`, `M = {0}`, weight `1`. -/
def localBranchingStructure_reflectionTheta :
    reflectionEpGroupoid.LocalBranchingStructure reflectionTheta 0 where
  U := univ
  isOpen_U := isOpen_univ
  mem_U := mem_univ _
  ι := Unit
  M _ := {0}
  subset_U _ := subset_univ _
  isSmoothSubmanifold _ := rnPolyfold_isSmoothSubmanifold_singleton 1 0
  mem_M _ := rfl
  isProperMap _ := (continuous_inclusion _).isProperMap
  σ _ := 1
  σ_pos _ := one_pos
  eq_sum y _ := by
    by_cases hy : y = 0
    · subst hy; simp [reflectionTheta]
    · simp [reflectionTheta, hy]

/-- `Θ₀ = 1_{0}` is a branched ep⁺-subgroupoid of `ℤ/2 ⋉ ℝ` (a non-trivial action groupoid; `0`
has isotropy `ℤ/2`). -/
theorem isBranchedEpSubgroupoid_reflectionTheta :
    reflectionEpGroupoid.IsBranchedEpSubgroupoid reflectionTheta where
  nonneg z := by rw [reflectionTheta_apply]; split_ifs <;> norm_num
  isFunctorial p := by
    change reflectionTheta p.2 = reflectionTheta (p.1 • p.2)
    rcases Int.units_eq_one_or p.1 with h | h <;> simp [reflectionTheta_apply, h]
  support_subset z _ := by
    change z ∈ (rnPolyfold 1).smoothSet
    rw [TrivialBundle.rnPolyfold_smoothSet]; exact mem_univ z
  paracompactSpace_orbitSupp := by
    have hs : supp reflectionTheta = {0} := by
      ext z
      by_cases h : z = 0 <;> simp [supp, reflectionTheta_apply, h]
    have hc : IsCompact (reflectionEpGroupoid.orbitSupp reflectionTheta) := by
      unfold orbitSupp
      rw [hs, image_singleton]
      exact isCompact_singleton
    have := isCompact_iff_compactSpace.1 hc
    infer_instance
  localBranching z hz := by
    have hz0 : z = 0 := by
      by_contra h
      have : ¬ (0 < reflectionTheta z) := by simp [reflectionTheta_apply, h]
      exact this hz
    subst hz0
    exact ⟨localBranchingStructure_reflectionTheta⟩

/-- **Theorem 11.3.3 (2) for the equivalence `X_𝒰 → ℤ/2 ⋉ ℝ` of the two-set covering
(Proposition 10.1.3)**: `F^*Θ₀` is a branched ep⁺-subgroupoid of `X_𝒰`. -/
theorem isBranchedEpSubgroupoid_pullbackTheta_reflectionCover :
    reflectionCover.epGroupoid.IsBranchedEpSubgroupoid
      (reflectionCover.functor.pullbackTheta reflectionTheta) :=
  isBranchedEpSubgroupoid_pullbackTheta isEquivalence_reflectionCover
    isBranchedEpSubgroupoid_reflectionTheta

/-- `F^*Θ₀` takes the value `1` at the two different objects `(true, 0)`, `(false, 0)` of `X_𝒰`
(`F` is not injective on objects). -/
theorem pullbackTheta_reflectionCover_two_points :
    ∃ p q : reflectionCover.objSet, p ≠ q ∧
      reflectionCover.functor.pullbackTheta reflectionTheta p = 1 ∧
      reflectionCover.functor.pullbackTheta reflectionTheta q = 1 := by
  refine ⟨⟨(true, 0), show (-1 : ℝ) < (0 : Fin 1 → ℝ) 0 by norm_num⟩,
    ⟨(false, 0), show (0 : Fin 1 → ℝ) 0 < 1 by norm_num⟩, fun h => ?_, ?_, ?_⟩
  · exact absurd (congrArg (fun p : reflectionCover.objSet => p.1.1) h) (by decide)
  · simp [pullbackTheta_apply, reflectionTheta_apply, OpenCover.functor]
  · simp [pullbackTheta_apply, reflectionTheta_apply, OpenCover.functor]

/-- `F_* F^* Θ₀ = Θ₀` (Lemma 11.3.2 (2)) for the covering equivalence. -/
theorem pushforwardTheta_pullbackTheta_reflectionCover :
    reflectionCover.functor.pushforwardTheta
      (reflectionCover.functor.pullbackTheta reflectionTheta) = reflectionTheta :=
  pushforwardTheta_pullbackTheta isEquivalence_reflectionCover.essSurj
    isBranchedEpSubgroupoid_reflectionTheta.isFunctorial

/-- `ℤ/2 ⋉ ℝ` as an object of `EP`. -/
abbrev reflectionEP : EP.{0} := ⟨_, _, reflectionEpGroupoid⟩

/-- The covering ep-groupoid `X_𝒰` of `ℤ/2 ⋉ ℝ` as an object of `EP`. -/
abbrev reflectionCoverEP : EP.{0} := ⟨_, _, reflectionCover.epGroupoid⟩

/-- The diagram `ℤ/2 ⋉ ℝ ←F X_𝒰 →1 X_𝒰`. -/
def reflectionCoverDiagram : Diagram reflectionEP reflectionCoverEP :=
  ⟨reflectionCoverEP, reflectionCover.functor, isEquivalence_reflectionCover, EpFunctor.id _⟩

/-- `[ℤ/2 ⋉ ℝ ←F X_𝒰 →1 X_𝒰]` is a generalized isomorphism (Theorem 10.3.10). -/
theorem isGeneralizedIso_reflectionCoverDiagram :
    IsGeneralizedIso (homMk reflectionCoverDiagram) :=
  (theorem_10_3_10 _).1.2 (EpFunctor.IsEquivalence.id _)

/-- **Witness for `EPLoc.pushTheta`**: the push-forward of `Θ₀` along the generalized isomorphism
`[ℤ/2 ⋉ ℝ ←F X_𝒰 →1 X_𝒰]` is `F^*Θ₀`, a branched ep⁺-subgroupoid (Theorem 11.3.3 (1)), and
`f^* f_* Θ₀ = Θ₀`. -/
theorem pushTheta_reflectionCoverDiagram :
    pushTheta (homMk reflectionCoverDiagram) reflectionTheta =
        reflectionCover.functor.pullbackTheta reflectionTheta ∧
      reflectionCover.epGroupoid.IsBranchedEpSubgroupoid
        (pushTheta (homMk reflectionCoverDiagram) reflectionTheta) ∧
      pullTheta (homMk reflectionCoverDiagram)
        (pushTheta (homMk reflectionCoverDiagram) reflectionTheta) = reflectionTheta := by
  have hΘ := isBranchedEpSubgroupoid_reflectionTheta
  refine ⟨?_, theorem_11_3_3_one isGeneralizedIso_reflectionCoverDiagram hΘ,
    pullTheta_pushTheta isGeneralizedIso_reflectionCoverDiagram hΘ.isFunctorial⟩
  rw [pushTheta_homMk _ (EpFunctor.IsEquivalence.id _) hΘ.isFunctorial]
  exact pushforwardTheta_id (reflectionCover.functor.isFunctorial_pullbackTheta hΘ.isFunctorial)

end EpGroupoid.Examples

end Polyfold
