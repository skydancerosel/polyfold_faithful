import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_58

/-! Round trip for V10_58 (2021 §10.5, p. 507; 2017 p. 367: the push-forward `[D]_* f = Ψ_* Φ* f`
and its independence of the representative).

The item lists the definitions `SDiagram.pushforward`, `SDiagram.pullback` (vocabulary) and eight
theorems; `A` is the conjunction of their types, universes at `0`:
`pushforward_eq_of_isRefinement` (the text's step: a refinement does not change `Ψ_* Φ*`), the
orbit lemmas `EpStrongBundle.π_μ`, `π_eq_π_of_isFunctorialSection`, `eq_of_forall_π_eq` (a section
functor is determined by the orbits of its values), `SDiagram.π_pushforward`
(`|Ψ_* Φ* f (x')| = |D|(|f(x)|)`), `base_orbitMap_eq_of_orbitMap_eq`, and
`pushforward_eq_of_orbitMap_eq`, `pullback_eq_of_orbitMap_eq` (diagrams with the same `|D|` have
the same push-forward and pull-back: the project's route to well-definedness).

`B`: (a), (b) `[D]_* f = Ψ_* Φ* f`, `[D]* g = Φ_* Ψ* g` for every representative with both legs
strong bundle equivalences (the project's `GenSBMap.pushforward`, `.pullback` use a chosen one);
(c) the three equalities of the text's chain for a refinement by `H`; (d) equivalent diagrams have
the same push-forward.

* `A_to_B`: (a), (b) from `A`'s `pushforward_eq_of_orbitMap_eq`, `pullback_eq_of_orbitMap_eq`, the
  representative and `D` having the same `|D|` (the non-item `GenSBMap.cls_rep`, `orbitMap_cls`);
  (c) the first two equalities from the non-item Theorem 10.4.5 (`H_* H* = 1`) and
  Proposition 10.4.4, the third from them and `A`'s `pushforward_eq_of_isRefinement`; (d) from
  `pushforward_eq_of_orbitMap_eq` and the non-item `SDiagram.Equiv.orbitMap_eq`.
* `B_to_A`: `pushforward_eq_of_isRefinement` from `B` (c).  The seven other conjuncts are not
  consequences of `B`: `B` speaks only of diagrams in one class, while
  `pushforward_eq_of_orbitMap_eq` covers any two diagrams with the same `|D|`, and the orbit
  lemmas are general facts about section functors.  They are re-proved outright below (the
  project's proofs, copied, from non-item project lemmas). -/

namespace RoundTrip.V10_58
open Polyfold CategoryTheory Set Function SBLocalization EPLocalization

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.SDiagram.pushforward_eq_of_isRefinement.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.π_μ.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.π_eq_π_of_isFunctorialSection.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.eq_of_forall_π_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.π_pushforward.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.base_orbitMap_eq_of_orbitMap_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.pushforward_eq_of_orbitMap_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.pullback_eq_of_orbitMap_eq.{0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.SDiagram.pushforward_eq_of_isRefinement.{0},
    @Polyfold.EpStrongBundle.π_μ.{0},
    @Polyfold.EpStrongBundle.π_eq_π_of_isFunctorialSection.{0},
    @Polyfold.EpStrongBundle.eq_of_forall_π_eq.{0},
    @Polyfold.SBLocalization.SDiagram.π_pushforward.{0},
    @Polyfold.SBLocalization.SDiagram.base_orbitMap_eq_of_orbitMap_eq.{0},
    @Polyfold.SBLocalization.SDiagram.pushforward_eq_of_orbitMap_eq.{0},
    @Polyfold.SBLocalization.SDiagram.pullback_eq_of_orbitMap_eq.{0}⟩

/-- The chosen representative of `f` and any representative `D` have the same `|D|`. -/
theorem orbitMap_rep_eq {A A' : SEP.{0}} {f : GenSBMap A A'} (hf : f.IsGeneralizedIso)
    {D : SDiagram A A'} (hD : D.cls = f) : (GenSBMap.rep hf).orbitMap = D.orbitMap := by
  rw [← GenSBMap.orbitMap_cls, ← GenSBMap.orbitMap_cls, GenSBMap.cls_rep, hD]

theorem A_to_B : A → B := by
  rintro ⟨hRef, -, -, -, -, -, hPush, hPull⟩
  intro A A'
  refine ⟨fun f hf D hΨ hD s hs => ?_, fun f hf D hΨ hD t ht => ?_,
    fun D D' hΨ hΨ' H hH hNΦ hNΨ hΦH hΨH s hs => ?_, fun D D' hΨ hΨ' hE s hs => ?_⟩
  · exact hPush (GenSBMap.isEquivalence_rep_Ψ hf) hΨ (orbitMap_rep_eq hf hD) hs
  · exact hPull (GenSBMap.isEquivalence_rep_Ψ hf) hΨ (orbitMap_rep_eq hf hD) ht
  · -- the three equalities of the text's chain
    have hk' : pullB D.Φ D.isEquivalence_Φ s ∈ D.B.E.sectionFunctors :=
      (EpStrongBundle.theorem_10_4_5 D.hΦ).1.2.1 hs
    have hk'' : pullB H hH (pullB D.Φ D.isEquivalence_Φ s) ∈ D'.B.E.sectionFunctors :=
      (EpStrongBundle.theorem_10_4_5 (sbe hH)).1.2.1 hk'
    -- `H_* H* = 1` (Theorem 10.4.5)
    have e₁ : pushB H hH (pullB H hH (pullB D.Φ D.isEquivalence_Φ s)) =
        pullB D.Φ D.isEquivalence_Φ s :=
      (sbe hH).pushforward_pullback hk'.1.1 hk'.2
    -- `(Φ ∘ H)* = H* Φ*`, `(Ψ ∘ H)_* = Ψ_* H_*` (Proposition 10.4.4)
    have e₂ : pullB (H ≫ D.Φ) hΦH s = pullB H hH (pullB D.Φ D.isEquivalence_Φ s) :=
      (EpStrongBundle.proposition_10_4_4 (sbe hH) D.hΦ).1 s hs.1.1
    have e₃ : pushB (H ≫ D.Ψ) hΨH (pullB H hH (pullB D.Φ D.isEquivalence_Φ s)) =
        pushB D.Ψ hΨ (pushB H hH (pullB H hH (pullB D.Φ D.isEquivalence_Φ s))) :=
      (EpStrongBundle.proposition_10_4_4 (sbe hH) (sbe hΨ)).2 _ hk''.1.1 hk''.2
    have c₁ : pushB D.Ψ hΨ (pullB D.Φ D.isEquivalence_Φ s) =
        pushB D.Ψ hΨ (pushB H hH (pullB H hH (pullB D.Φ D.isEquivalence_Φ s))) := by
      rw [e₁]
    have c₂ : pushB D.Ψ hΨ (pushB H hH (pullB H hH (pullB D.Φ D.isEquivalence_Φ s))) =
        pushB (H ≫ D.Ψ) hΨH (pullB (H ≫ D.Φ) hΦH s) := by
      rw [e₂, e₃]
    -- the third equality: `A`'s `pushforward_eq_of_isRefinement`
    have hR : D'.pushforward hΨ' s = D.pushforward hΨ s := hRef hΨ hΨ' ⟨H, hH, hNΦ, hNΨ⟩ hs
    refine ⟨c₁, c₂, ?_⟩
    exact (c₁.trans c₂).symm.trans hR.symm
  · exact hPush hΨ hΨ' hE.orbitMap_eq hs

/-! ### The general lemmas of `A`, re-proved outright (the project's proofs, copied) -/

section Orbits

universe u

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)] {E : EpStrongBundle X B}

theorem π_μ' (E : EpStrongBundle X B) (q : pullbackSpace P X.src) :
    E.toEpGroupoid.π (E.μ q) = E.toEpGroupoid.π (q : Mor × W).2 :=
  ((GroupoidStr.π_eq_π_iff _).2 ⟨q, rfl, rfl⟩).symm

theorem π_eq_π_of_isFunctorialSection' {f : Obj → W} {hf : IsSection P f}
    (hfun : E.IsFunctorialSection hf) {x y : Obj} (h : X.π x = X.π y) :
    E.toEpGroupoid.π (f x) = E.toEpGroupoid.π (f y) := by
  obtain ⟨k, hk, hk'⟩ := X.π_eq_π_iff.1 h
  refine (GroupoidStr.π_eq_π_iff _).2 ⟨EpStrongBundle.sectionPair hf k, ?_, ?_⟩
  · change f (X.src k) = f x
    rw [hk]
  · change E.μ (EpStrongBundle.sectionPair hf k) = f y
    rw [← hfun k, hk']

theorem eq_of_forall_π_eq' {f g : Obj → W} {hf : IsSection P f} (hfun : E.IsFunctorialSection hf)
    (hg : IsSection P g) (h : ∀ x, E.toEpGroupoid.π (f x) = E.toEpGroupoid.π (g x)) : f = g := by
  funext x
  obtain ⟨q, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 (h x)
  have hs' : (q : Mor × W).2 = f x := hs
  have ht' : E.μ q = g x := ht
  have hsσ : X.src (q : Mor × W).1 = x := by
    rw [← (q.2 : P (q : Mor × W).2 = X.src (q : Mor × W).1), hs', hf x]
  have htσ : X.tgt (q : Mor × W).1 = x := by rw [← E.P_μ q, ht', hg x]
  calc f x = f (X.tgt (q : Mor × W).1) := by rw [htσ]
    _ = E.μ (EpStrongBundle.sectionPair hf (q : Mor × W).1) := hfun _
    _ = E.μ q := E.μ_congr (Prod.ext rfl (by
          change f (X.src (q : Mor × W).1) = (q : Mor × W).2
          rw [hsσ, hs']))
    _ = g x := ht'

end Orbits

section Diagrams

universe u

variable {A A' : SEP.{u}}

theorem π_pushforward' (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ) {f : A.Obj → A.W}
    (hf : f ∈ A.E.sectionFunctors) {x : A.Obj} {x' : A'.Obj}
    (hx : D.base.orbitMap (A.X.π x) = A'.X.π x') :
    A'.E.toEpGroupoid.π (D.pushforward hΨ f x') = D.orbitMap (A.E.toEpGroupoid.π (f x)) := by
  obtain ⟨hs, hfun⟩ := hf
  set a := (sbe hΨ).preObj x'
  set h := D.hΦ.pullback f
  have hh : IsSection D.B.P h := D.hΦ.isSection_pullback f
  have hxa : A.X.π x = A.X.π ((SEP.Hom.ϕ D.Φ).obj a) :=
    (D.base.isHomeomorph_orbitMap (sbe hΨ).isEquivalence_base).injective
      (hx.trans (D.base_orbitMap_preObj hΨ x').symm)
  have h₁ : D.orbitMap (A.E.toEpGroupoid.π (f x)) =
      A'.E.toEpGroupoid.π ((SEP.Hom.Φ D.Ψ).obj (h a)) := by
    refine (Diagram.orbitMap_eq_of (d := D.total) (r := D.B.E.toEpGroupoid.π (h a)) ?_).trans ?_
    · change (SEP.Hom.Φ D.Φ).orbitMap _ = _
      rw [GroupoidFunctor.orbitMap_π, D.hΦ.obj_pullback hs.1]
      exact (π_eq_π_of_isFunctorialSection' hfun hxa).symm
    · change (SEP.Hom.Φ D.Ψ).orbitMap _ = _
      rw [GroupoidFunctor.orbitMap_π]
  rw [h₁]
  change A'.E.toEpGroupoid.π ((sbe hΨ).pushforward h x') = _
  rw [(sbe hΨ).pushforward_def hh]
  exact π_μ' A'.E _

theorem base_orbitMap_eq_of_orbitMap_eq' {D₁ D₂ : SDiagram A A'}
    (h : D₁.orbitMap = D₂.orbitMap) : D₁.base.orbitMap = D₂.base.orbitMap := by
  funext q
  obtain ⟨r, rfl⟩ := A.E.surjective_orbitMap_projFunctor q
  have h₁ := congrFun D₁.orbitMap_square r
  have h₂ := congrFun D₂.orbitMap_square r
  simp only [Function.comp_apply] at h₁ h₂
  rw [← h₁, ← h₂, h]

theorem pushforward_eq_of_orbitMap_eq' {D₁ D₂ : SDiagram A A'} (hΨ₁ : SEP.equivalences D₁.Ψ)
    (hΨ₂ : SEP.equivalences D₂.Ψ) (h : D₁.orbitMap = D₂.orbitMap) :
    EqOn (D₁.pushforward hΨ₁) (D₂.pushforward hΨ₂) A.E.sectionFunctors := by
  intro f hf
  have hb := base_orbitMap_eq_of_orbitMap_eq' h
  obtain ⟨hs₁, hfun₁⟩ := D₁.mapsTo_pushforward hΨ₁ hf
  obtain ⟨hs₂, -⟩ := D₂.mapsTo_pushforward hΨ₂ hf
  refine eq_of_forall_π_eq' hfun₁ hs₂.1 fun x' => ?_
  set x := (SEP.Hom.ϕ D₁.Φ).obj ((sbe hΨ₁).preObj x')
  have hx₁ : D₁.base.orbitMap (A.X.π x) = A'.X.π x' := D₁.base_orbitMap_preObj hΨ₁ x'
  have hx₂ : D₂.base.orbitMap (A.X.π x) = A'.X.π x' := by rw [← hb]; exact hx₁
  rw [π_pushforward' D₁ hΨ₁ hf hx₁, π_pushforward' D₂ hΨ₂ hf hx₂, h]

theorem pullback_eq_of_orbitMap_eq' {D₁ D₂ : SDiagram A A'} (hΨ₁ : SEP.equivalences D₁.Ψ)
    (hΨ₂ : SEP.equivalences D₂.Ψ) (h : D₁.orbitMap = D₂.orbitMap) :
    EqOn (D₁.pullback hΨ₁) (D₂.pullback hΨ₂) A'.E.sectionFunctors :=
  pushforward_eq_of_orbitMap_eq' D₁.isEquivalence_Φ D₂.isEquivalence_Φ
    (SDiagram.orbitMap_symm_eq hΨ₁ hΨ₂ h)

end Diagrams

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {A A' D D'} hΨ hΨ' h f hf => ?_, @π_μ'.{0}, @π_eq_π_of_isFunctorialSection'.{0},
    @eq_of_forall_π_eq'.{0}, @π_pushforward'.{0}, @base_orbitMap_eq_of_orbitMap_eq'.{0},
    @pushforward_eq_of_orbitMap_eq'.{0}, @pullback_eq_of_orbitMap_eq'.{0}⟩
  obtain ⟨H, hH, hΦH, hΨH⟩ := h
  obtain ⟨c₁, c₂, c₃⟩ := (hB A A').2.2.1 D D' hΨ hΨ' H hH hΦH hΨH
    (SEP.equivalences.comp_mem _ _ hH D.isEquivalence_Φ) (SEP.equivalences.comp_mem _ _ hH hΨ) f hf
  exact (c₁.trans (c₂.trans c₃)).symm

#rt_check RoundTrip.V10_58.A_to_B [Polyfold.SBLocalization.SDiagram.pushforward_eq_of_isRefinement,
  Polyfold.EpStrongBundle.π_μ, Polyfold.EpStrongBundle.π_eq_π_of_isFunctorialSection,
  Polyfold.EpStrongBundle.eq_of_forall_π_eq, Polyfold.SBLocalization.SDiagram.π_pushforward,
  Polyfold.SBLocalization.SDiagram.base_orbitMap_eq_of_orbitMap_eq,
  Polyfold.SBLocalization.SDiagram.pushforward_eq_of_orbitMap_eq,
  Polyfold.SBLocalization.SDiagram.pullback_eq_of_orbitMap_eq]
#rt_check RoundTrip.V10_58.B_to_A [Polyfold.SBLocalization.SDiagram.pushforward_eq_of_isRefinement,
  Polyfold.EpStrongBundle.π_μ, Polyfold.EpStrongBundle.π_eq_π_of_isFunctorialSection,
  Polyfold.EpStrongBundle.eq_of_forall_π_eq, Polyfold.SBLocalization.SDiagram.π_pushforward,
  Polyfold.SBLocalization.SDiagram.base_orbitMap_eq_of_orbitMap_eq,
  Polyfold.SBLocalization.SDiagram.pushforward_eq_of_orbitMap_eq,
  Polyfold.SBLocalization.SDiagram.pullback_eq_of_orbitMap_eq]
#rt_overlap RoundTrip.V10_58.B_to_A [Polyfold.SBLocalization.SDiagram.pushforward_eq_of_isRefinement,
  Polyfold.EpStrongBundle.π_μ, Polyfold.EpStrongBundle.π_eq_π_of_isFunctorialSection,
  Polyfold.EpStrongBundle.eq_of_forall_π_eq, Polyfold.SBLocalization.SDiagram.π_pushforward,
  Polyfold.SBLocalization.SDiagram.base_orbitMap_eq_of_orbitMap_eq,
  Polyfold.SBLocalization.SDiagram.pushforward_eq_of_orbitMap_eq,
  Polyfold.SBLocalization.SDiagram.pullback_eq_of_orbitMap_eq]

end RoundTrip.V10_58
