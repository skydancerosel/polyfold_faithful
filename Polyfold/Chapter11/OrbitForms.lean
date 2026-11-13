import Polyfold.Chapter11.GeneralizedForms
import Polyfold.Chapter10.EquivalenceLR

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §11.2,
pp. 532–535: **Proposition 11.2.8**, **Proposition 11.2.9** (2017: Propositions 11.4, 11.5) and
**Theorem 11.2.1 (4)** (gap G.129).  Numbers and pages are the 2021 text's.

# Forms and the maps of orbit spaces, under the local regularity property

## The text, paraphrased

(Proposition 11.2.8) For equivalences `F, G : X → Y` between ep-groupoids with the local
regularity property and `|F| = |G|`: `F_*ω = G_*ω` and `F^*ω' = G^*ω'`.  The proof takes from
Proposition 10.1.10, for `x ∈ X₁`, a morphism `ψ : F(x) → G(x)` with `Tψ ∘ TF(x) = TG(x)`.
(Proposition 11.2.9) For generalized isomorphisms `f, g : X → Y` between ep-groupoids with the
local regularity property and `|f| = |g|`: `f_* = g_*` and `f^* = g^*`.  (Theorem 11.2.1 (4))
The same statement.

## What is formalized

* `EpFunctor.HasLocalNatIso F G`: every object `x` has an open neighbourhood `U` with an
  sc-smooth `α : U → 𝐘`, `α_z : F(z) → G(z)` (the conclusion of Proposition 10.1.10 (1));
  `hasLocalNatIso_of_orbitMap_eq` (Proposition 10.1.10 (1): it holds for equivalences with
  `|F| = |G|` when `X` or `Y` has the local regularity property), `HasLocalNatIso.liftOne`,
  `EP.hasLocalNatIso_liftFunctor` (it passes to the index raises `Fⁱ, Gⁱ : Xⁱ → Yⁱ`), and
  `HasLocalNatIso.formPullback_eq`: then `F^*ω = G^*ω` for every form `ω` of the ep-groupoid
  `Y` (locally `F = s ∘ α`, `G = t ∘ α` and `s^*ω = t^*ω`).
* **`EP.proposition_11_2_8`**: for equivalences `F, G : X → Y` with `|F| = |G|`, `X` and `Y`
  with the local regularity property: `F^* = G^*` and `F_* = G_*` on `Ω*_{ep,∞}`.
  `EP.epFormsInftyPullback_eq_of_orbitMap_eq`, `EP.epFormsInftyPush_eq_of_orbitMap_eq`: the
  same with the local regularity property for one of `X`, `Y` only.
* **`EPLocalization.EPLoc.proposition_11_2_9`**: for generalized isomorphisms `f, g : X → Y`
  with `|f| = |g|`, `X` and `Y` with the local regularity property: `f_* = g_*` and
  `f^* = g^*`; `formsPullback_eq_of_orbitMap_eq`, `formsPush_eq_of_orbitMap_eq` with the
  property for `Y` only.
* **`EPLocalization.EPLoc.theorem_11_2_1_four`**: Theorem 11.2.1 (4).

## The reading

* The local regularity property is `EpGroupoid.IsLR` (Definition 7.4.19) of the ep-groupoid;
  `Ω_{ep,∞}` involves the index lifts `Xⁱ`, and the text's proof is applied on each level
  through the restrictions of the local families `α` of Proposition 10.1.10 to the levels (no
  local regularity property of the lifts `Xⁱ` is assumed or needed).
* The text proves `F_* = G_*` by a second computation; here it follows from `F^* = G^*`, the
  push-forwards being the inverses (Lemma 11.2.4 (3)).  In Proposition 11.2.9 the weak fibred
  product `A ×_X A'` is used as in the text; the local regularity property enters through
  Proposition 11.2.8 for the equivalences `G ∘ π_A`, `G' ∘ π_{A'} : A ×_X A' → Y`, where the
  property of `Y` suffices (Proposition 10.1.9).

Hypotheses: those of the text.  The local regularity property is satisfiable (Chapter 10:
`EpGroupoid.Examples.isLR_trivialZ3`, `EP.lreg_pointEP`).
-/

set_option maxSynthPendingDepth 3

open Set Function CategoryTheory

noncomputable section

namespace Polyfold

open MPolyfold

universe u v

namespace EpFunctor

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {k : ℕ}

/-- **Local natural isomorphisms** between sc-smooth functors `F, G : X → Y` (the conclusion of
Proposition 10.1.10 (1)): every object `x` has an open neighbourhood `U` with an sc-smooth map
`α : U → 𝐘`, `α_z : F(z) → G(z)`. -/
def HasLocalNatIso (F G : EpFunctor X Y) : Prop :=
  ∀ x : Obj, ∃ (U : Set Obj) (α : Obj → Mor'), x ∈ U ∧ X.PObj.IsScSmoothOn Y.PMor α U ∧
    ∀ z ∈ U, Y.src (α z) = F.obj z ∧ Y.tgt (α z) = G.obj z

/-- **2021 Proposition 10.1.10 (1)**: equivalences `F, G : X → Y` with `|F| = |G|` have local
natural isomorphisms, if `X` has the local regularity property. -/
theorem hasLocalNatIso_of_orbitMap_eq {F G : EpFunctor X Y} (hF : F.IsEquivalence)
    (hG : G.IsEquivalence) (hFG : F.orbitMap = G.orbitMap) (hX : X.IsLR) :
    F.HasLocalNatIso G := fun x => by
  obtain ⟨R, -, α, hα, h⟩ := proposition_10_1_10_one hF hG hFG hX x isOpen_univ (mem_univ x)
  exact ⟨R.U, α, R.mem_U, hα, h⟩

/-- A natural equivalence gives local natural isomorphisms. -/
theorem NaturallyEquivalent.hasLocalNatIso {F G : EpFunctor X Y} (h : F.NaturallyEquivalent G) :
    F.HasLocalNatIso G := fun x => by
  obtain ⟨τ⟩ := h
  exact ⟨univ, τ.app, mem_univ x, τ.isScSmoothMap_app, fun z _ => ⟨τ.src_app z, τ.tgt_app z⟩⟩

open scoped Classical in
/-- Local natural isomorphisms pass to the index raises `F¹, G¹ : X¹ → Y¹`. -/
theorem HasLocalNatIso.liftOne {F G : EpFunctor X Y} (h : F.HasLocalNatIso G) :
    F.liftOne.HasLocalNatIso G.liftOne := fun x => by
  obtain ⟨U, α, hxU, hα, hsrc⟩ := h (X.PObj.levelVal 1 x)
  refine ⟨{z | X.PObj.levelVal 1 z ∈ U}, fun z =>
    if hz : X.PObj.levelVal 1 z ∈ U then
      Y.PMor.levelMk 1 (α (X.PObj.levelVal 1 z))
        (hα.mapsTo_levelSet 1 ⟨hz, MPolyfold.levelVal_mem z⟩)
    else Y.liftOne.unit (F.liftOne.obj z), hxU, hα.levelOne fun z hz => ?_, fun z hz => ?_⟩
  · rw [dif_pos hz, MPolyfold.levelVal_levelMk]
  · have hz' : X.PObj.levelVal 1 z ∈ U := hz
    simp only [dif_pos hz']
    exact ⟨MPolyfold.level_ext (hsrc _ hz').1, MPolyfold.level_ext (hsrc _ hz').2⟩

/-- **Functors with local natural isomorphisms have the same pull-back of forms** (the
computation in the proof of Proposition 11.2.8): locally `F = s ∘ α` and `G = t ∘ α`, and
`s^*ω = t^*ω` for a form `ω` of the ep-groupoid `Y`. -/
theorem HasLocalNatIso.formPullback_eq {F G : EpFunctor X Y} (h : F.HasLocalNatIso G)
    {ω : ∀ y : Y.PObj.Level 1, Y.PObj.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ} (hω : ω ∈ Y.epForms k) :
    formPullback F.isScSmoothMap_obj ω = formPullback G.isScSmoothMap_obj ω := by
  funext x
  ext l
  obtain ⟨U, α, hxU, hα, hsrc⟩ := h (X.PObj.levelVal 1 x)
  have hl : ∀ i, (l i).1 ∈ X.PObj.tangentPreimage U := fun i =>
    tangentFiber_subset_tangentPreimage hxU (l i).2
  have hφ : α (X.PObj.levelVal 1 x) ∈ Y.PMor.levelSet 1 :=
    hα.mapsTo_levelSet 1 ⟨hxU, MPolyfold.levelVal_mem x⟩
  have hbase : ∀ i, Y.PMor.tangentProj (tangentMapOn hα (l i).1) =
      Y.PMor.levelMk 1 _ hφ := fun i => by
    apply MPolyfold.level_ext
    rw [levelVal_tangentProj_tangentMapOn hα (hl i), MPolyfold.levelVal_levelMk,
      show X.PObj.tangentProj (l i).1 = x from (l i).2]
  have e1 : formPullback Y.isScSmoothMap_src ω (Y.PMor.levelMk 1 _ hφ)
      (fun i => ⟨tangentMapOn hα (l i).1, hbase i⟩) =
      formPullback F.isScSmoothMap_obj ω x l := by
    rw [formPullback_apply F.isScSmoothMap_obj]
    refine MPolyfold.formPullback_eq Y.isScSmoothMap_src ω _ ?_ _ fun i => ?_
    · rw [MPolyfold.levelVal_levelMk]; exact (hsrc _ hxU).1
    · rw [coe_tangentFiberMap_apply]
      exact tangentMap_tangentMapOn_of_eqOn hα Y.isScSmoothMap_src F.isScSmoothMap_obj
        (fun z hz => (hsrc z hz).1) (hl i)
  have e2 : formPullback Y.isScSmoothMap_tgt ω (Y.PMor.levelMk 1 _ hφ)
      (fun i => ⟨tangentMapOn hα (l i).1, hbase i⟩) =
      formPullback G.isScSmoothMap_obj ω x l := by
    rw [formPullback_apply G.isScSmoothMap_obj]
    refine MPolyfold.formPullback_eq Y.isScSmoothMap_tgt ω _ ?_ _ fun i => ?_
    · rw [MPolyfold.levelVal_levelMk]; exact (hsrc _ hxU).2
    · rw [coe_tangentFiberMap_apply]
      exact tangentMap_tangentMapOn_of_eqOn hα Y.isScSmoothMap_tgt G.isScSmoothMap_obj
        (fun z hz => (hsrc z hz).2) (hl i)
  rw [← e1, ← e2, Y.isMorCompatible_iff_formPullback.1 hω.2]

end EpFunctor

namespace EP

variable {A : EP.{u}} {B : EP.{v}}

/-- Local natural isomorphisms pass to all index raises `Fⁱ, Gⁱ : Xⁱ → Yⁱ`. -/
theorem hasLocalNatIso_liftFunctor {F G : EpFunctor A.X B.X} (h : F.HasLocalNatIso G) :
    ∀ i : ℕ, (liftFunctor F i).HasLocalNatIso (liftFunctor G i)
  | 0 => h
  | i + 1 => (hasLocalNatIso_liftFunctor h i).liftOne

/-- Functors with local natural isomorphisms have the same pull-back on `Ω*_{ep,∞}`. -/
theorem epFormsInftyPullback_eq_of_hasLocalNatIso {F G : EpFunctor A.X B.X}
    (h : F.HasLocalNatIso G) (k : ℕ) : epFormsInftyPullback F k = epFormsInftyPullback G k := by
  refine Module.DirectLimit.hom_ext fun i => LinearMap.ext fun ω => ?_
  have e : epFormsPullback F k i ω = epFormsPullback G k i ω :=
    Subtype.ext ((hasLocalNatIso_liftFunctor h i).formPullback_eq ω.2)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, epFormsInftyPullback_of,
    epFormsInftyPullback_of, e]

/-- **Proposition 11.2.8, the pull-backs, with the local regularity property for one of the
two ep-groupoids**: equivalences `F, G : X → Y` with `|F| = |G|` have `F^* = G^*`. -/
theorem epFormsInftyPullback_eq_of_orbitMap_eq {F G : EpFunctor A.X B.X} (hF : F.IsEquivalence)
    (hG : G.IsEquivalence) (hFG : F.orbitMap = G.orbitMap) (hLR : A.X.IsLR ∨ B.X.IsLR) (k : ℕ) :
    epFormsInftyPullback F k = epFormsInftyPullback G k :=
  epFormsInftyPullback_eq_of_hasLocalNatIso
    (EpFunctor.hasLocalNatIso_of_orbitMap_eq hF hG hFG
      (hLR.elim _root_.id (EpFunctor.proposition_10_1_9 hF).2)) k

/-- **Proposition 11.2.8, the push-forwards, with the local regularity property for one of
the two ep-groupoids**: equivalences `F, G : X → Y` with `|F| = |G|` have `F_* = G_*`. -/
theorem epFormsInftyPush_eq_of_orbitMap_eq {F G : EpFunctor A.X B.X} (hF : F.IsEquivalence)
    (hG : G.IsEquivalence) (hFG : F.orbitMap = G.orbitMap) (hLR : A.X.IsLR ∨ B.X.IsLR) (k : ℕ) :
    epFormsInftyPush hF k = epFormsInftyPush hG k :=
  epFormsInftyPush_eq_of_comp_eq_id hG k
    ((congrArg (fun T => T.comp (epFormsInftyPush hF k))
      (epFormsInftyPullback_eq_of_orbitMap_eq hF hG hFG hLR k).symm).trans
      (epFormsInftyPullback_comp_epFormsInftyPush hF k))

/-- **2021 Proposition 11.2.8, p. 532 (2017: Proposition 11.4)**: for equivalences
`F, G : X → Y` between ep-groupoids with the local regularity property and `|F| = |G|`:
`F_* = G_*` and `F^* = G^*` on `Ω*_{ep,∞}`. -/
theorem proposition_11_2_8 {F G : EpFunctor A.X B.X} (hF : F.IsEquivalence)
    (hG : G.IsEquivalence) (hX : A.X.IsLR) (_hY : B.X.IsLR) (hFG : F.orbitMap = G.orbitMap)
    (k : ℕ) :
    epFormsInftyPush hF k = epFormsInftyPush hG k ∧
      epFormsInftyPullback F k = epFormsInftyPullback G k :=
  ⟨epFormsInftyPush_eq_of_orbitMap_eq hF hG hFG (Or.inl hX) k,
    epFormsInftyPullback_eq_of_orbitMap_eq hF hG hFG (Or.inl hX) k⟩

end EP

namespace EPLocalization

open WeakFibredProduct

variable {X Y : EP.{u}}

/-- **Proposition 11.2.9 on diagrams**: two diagrams `X ←F A →G Y`, `X ←F' A' →G' Y` of
equivalences with the same map of orbit spaces have the same pull-back of forms, if `Y` has
the local regularity property. -/
theorem Diagram.formsPullback_eq_of_orbitMap_eq (d e : Diagram X Y) (hd : d.Φ.IsEquivalence)
    (he : e.Φ.IsEquivalence) (hde : d.orbitMap = e.orbitMap) (hY : Y.X.IsLR) (k : ℕ) :
    d.formsPullback k = e.formsPullback k := by
  have hadm : Admissible d.F e.F := .of_isEquivalence_left d.isEquivalence_F
  have hL : (projLeft d.F e.F hadm).IsEquivalence := isEquivalence_projLeft e.isEquivalence_F hadm
  have hR : (projRight d.F e.F hadm).IsEquivalence :=
    isEquivalence_projRight d.isEquivalence_F hadm
  have hnat := naturallyEquivalent (F := d.F) (G := e.F) hadm
  have horb : (d.Φ.comp (projLeft d.F e.F hadm)).orbitMap =
      (e.Φ.comp (projRight d.F e.F hadm)).orbitMap := by
    funext q
    have h1 : (d.Φ.comp (projLeft d.F e.F hadm)).orbitMap q =
        d.orbitMap ((d.F.comp (projLeft d.F e.F hadm)).orbitMap q) :=
      (congrFun (EpFunctor.orbitMap_comp d.Φ (projLeft d.F e.F hadm)) q).trans
        ((d.orbitMap_orbitMap_F ((projLeft d.F e.F hadm).orbitMap q)).symm.trans
          (congrArg d.orbitMap
            (congrFun (EpFunctor.orbitMap_comp d.F (projLeft d.F e.F hadm)) q).symm))
    have h2 : (e.Φ.comp (projRight d.F e.F hadm)).orbitMap q =
        e.orbitMap ((e.F.comp (projRight d.F e.F hadm)).orbitMap q) :=
      (congrFun (EpFunctor.orbitMap_comp e.Φ (projRight d.F e.F hadm)) q).trans
        ((e.orbitMap_orbitMap_F ((projRight d.F e.F hadm).orbitMap q)).symm.trans
          (congrArg e.orbitMap
            (congrFun (EpFunctor.orbitMap_comp e.F (projRight d.F e.F hadm)) q).symm))
    rw [h1, h2, hde, hnat.orbitMap_eq]
  have e1 := EP.epFormsInftyPullback_eq_of_orbitMap_eq (A := wfp d.F e.F hadm)
    (hd.comp hL) (he.comp hR) horb (Or.inr hY) k
  have e2 := EP.lemma_11_2_5_push (A := wfp d.F e.F hadm) (d.isEquivalence_F.comp hL) k
    (e.isEquivalence_F.comp hR) hnat
  have e3 : (d.precomp (A' := wfp d.F e.F hadm) (projLeft d.F e.F hadm) hL).formsPullback k =
      (e.precomp (A' := wfp d.F e.F hadm) (projRight d.F e.F hadm) hR).formsPullback k :=
    (congrArg (fun T => T.comp (EP.epFormsInftyPullback (A := wfp d.F e.F hadm)
      (d.Φ.comp (projLeft d.F e.F hadm)) k)) e2).trans
      (congrArg (fun T => (EP.epFormsInftyPush (A := wfp d.F e.F hadm)
        (e.isEquivalence_F.comp hR) k).comp T) e1)
  exact ((Diagram.formsPullback_eq_of_isRefinement (d.isRefinement_precomp _ hL) k).symm.trans
    e3).trans (Diagram.formsPullback_eq_of_isRefinement (e.isRefinement_precomp _ hR) k)

namespace EPLoc

/-- **Proposition 11.2.9, the pull-backs, with the local regularity property for `Y`**:
generalized isomorphisms `f, g : X → Y` with `|f| = |g|` have `f^* = g^*`. -/
theorem formsPullback_eq_of_orbitMap_eq (f g : of X ⟶ of Y) (hf : IsGeneralizedIso f)
    (hg : IsGeneralizedIso g) (hfg : orbitMap f = orbitMap g) (hY : Y.X.IsLR) (k : ℕ) :
    formsPullback f k = formsPullback g k := by
  obtain ⟨d, rfl⟩ := homMk_surjective f
  obtain ⟨e, rfl⟩ := homMk_surjective g
  exact Diagram.formsPullback_eq_of_orbitMap_eq d e ((theorem_10_3_10 d).1.1 hf)
    ((theorem_10_3_10 e).1.1 hg) hfg hY k

/-- **Proposition 11.2.9, the push-forwards, with the local regularity property for `Y`**:
generalized isomorphisms `f, g : X → Y` with `|f| = |g|` have `f_* = g_*`. -/
theorem formsPush_eq_of_orbitMap_eq (f g : of X ⟶ of Y) (hf : IsGeneralizedIso f)
    (hg : IsGeneralizedIso g) (hfg : orbitMap f = orbitMap g) (hY : Y.X.IsLR) (k : ℕ) :
    formsPush f hf k = formsPush g hg k := by
  have h := formsPullback_eq_of_orbitMap_eq f g hf hg hfg hY k
  have hf3 := (theorem_11_2_1_three f hf k).2.1
  have hg3 := (theorem_11_2_1_three g hg k).2.2
  refine LinearMap.ext fun a => ?_
  have h1 : formsPullback g k (formsPush g hg k a) = a := LinearMap.congr_fun hg3 a
  have h2 : formsPush f hf k (formsPullback f k (formsPush g hg k a)) = formsPush g hg k a :=
    LinearMap.congr_fun hf3 (formsPush g hg k a)
  have h3 : formsPullback f k (formsPush g hg k a) = a :=
    (LinearMap.congr_fun h (formsPush g hg k a)).trans h1
  exact (congrArg (formsPush f hf k) h3).symm.trans h2

/-- **2021 Proposition 11.2.9, p. 534 (2017: Proposition 11.5)**: for ep-groupoids `X`, `Y`
with the local regularity property and generalized isomorphisms `f, g : X → Y` with
`|f| = |g|`: `f_* = g_*` and `f^* = g^*`. -/
theorem proposition_11_2_9 (_hX : X.X.IsLR) (hY : Y.X.IsLR) (f g : of X ⟶ of Y)
    (hf : IsGeneralizedIso f) (hg : IsGeneralizedIso g) (hfg : orbitMap f = orbitMap g) (k : ℕ) :
    formsPush f hf k = formsPush g hg k ∧ formsPullback f k = formsPullback g k :=
  ⟨formsPush_eq_of_orbitMap_eq f g hf hg hfg hY k,
    formsPullback_eq_of_orbitMap_eq f g hf hg hfg hY k⟩

/-- **2021 Theorem 11.2.1 (4), p. 526 (2017: Theorem 11.2)**: if `X` and `Y` have the local
regularity property and the generalized isomorphisms `h, k : X → Y` induce the same map of
orbit spaces, `|h| = |k|`, then `h_* = k_*` and `h^* = k^*`. -/
theorem theorem_11_2_1_four (hX : X.X.IsLR) (hY : Y.X.IsLR) (h k : of X ⟶ of Y)
    (hh : IsGeneralizedIso h) (hk : IsGeneralizedIso k) (hhk : orbitMap h = orbitMap k)
    (j : ℕ) : formsPush h hh j = formsPush k hk j ∧ formsPullback h j = formsPullback k j :=
  proposition_11_2_9 hX hY h k hh hk hhk j

end EPLoc

end EPLocalization

end Polyfold
