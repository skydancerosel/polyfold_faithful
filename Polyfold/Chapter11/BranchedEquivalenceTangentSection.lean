import Polyfold.Chapter11.BranchedEquivalenceTangent
import Polyfold.Chapter9.OrientationRn

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.3 "Branched Ep⁺-Subgroupoids and Equivalences" (pp. 538–539; 2017:
pp. 392–393): the push-forward (11.8) and pull-back (11.9) of section functors of `Gr̂` and
**Lemma 11.3.4** (2017: Lemma 11.4).  Numbers and pages are the 2021 text's.

# Section functors of `Gr̂` along equivalences

## The text, paraphrased

(p. 538) `Γ(π̂_X)` is the set of section functors `h : X_∞ → Gr̂(X)` of `π̂ : Gr̂(X) → X_∞`, with
no continuity requirement.  For an equivalence `F : X → Y` and `y ∈ Y_∞` pick `x` and
`ψ : F(x) → y` and put `(F_*h)(y) = Tψ ∘ TF(x) h(x)` (11.8); it does not depend on the choices
since `h` is functorial.  (p. 539) `F^*h'` is defined by `TF(x) (F^*h')(x) = h'(F(x))` (11.9).
`F_*`, `F^*` are mutually inverse, naturally equivalent equivalences give the same maps, and for
`f = [X ←F A →G Y]` one puts `f_* h = G_* F^* h`, `f^* h' = F_* G^* h'`, which do not depend on the
diagram.  **Lemma 11.3.4**: for a generalized isomorphism `f` these are well-defined maps
`f_* : Γ(π̂_X) → Γ(π̂_Y)`, `f^* : Γ(π̂_Y) → Γ(π̂_X)` with `(f⁻¹)_* = f^*`,
`(g ∘ f)_* = g_* ∘ f_*`, `(g ∘ f)^* = f^* ∘ g^*`, and `f_* = G_* F^*`, `f^* = F_* G^*` for every
representative.

## What is formalized

* `EpGroupoid.IsGrHatSection` (naturality and values in `Gr̂(x)`; `IsGrHatSection.toFunctor` is
  the functor `X_∞ → Gr̂(X)`), `EpGroupoid.GrHatSections` (`Γ(π̂_X)`, functions vanishing off
  `X_∞`); every orientation is a section functor.
* (11.8) `EpFunctor.pushSection`, independent of the choices (`pushSection_eq`); (11.9)
  `EpFunctor.pullSection`, with `TF(x)⁻¹` the inverse `MPolyfold.fibreInv` of `TF` on `T_xX`.
* For equivalences: `isGrHatSection_pushSection`, `isGrHatSection_pullSection`,
  `pullSection_pushSection`, `pushSection_pullSection`, invariance under natural equivalence,
  composition laws, base change in the weak fibred product.
* Lemma 11.3.4: `EPLocalization.EPLoc.pushSection`, `pullSection`, `pushSection_homMk`,
  `pullSection_homMk`, `pushSection_comp`, `pullSection_comp`, `pushSection_inv`,
  `lemma_11_3_4`.
* Witness: the orientation `T̂¹` of Example 9.3.5 is in `Γ(π̂)` and is fixed by the push-forward
  and pull-back of the identity equivalence.

## Choices

* Sections are functions on all of `X` with values `0` off `X_∞`; the text's sections are
  defined on `X_∞` only.
* The formal sums `∑ σ_L · L` are moved by `OrTangent.map` (image of carrier and frames).
* Lemma 11.3.4 is stated for generalized isomorphisms, as in the text; the composition laws use
  that both factors are generalized isomorphisms.
-/

set_option maxSynthPendingDepth 3

open Set Function Module Submodule

noncomputable section

namespace Polyfold

universe u v

/-! ### The inverse of a tangent map on a fibre -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- **The inverse of `f : TX → TY` on the fibre `T_xX`**: for `β` a chosen `α ∈ T_xX` with
`f(α) = β` (any vector of `T_xX` if there is none); for the tangent of a local
sc-diffeomorphism it is `T(F|U)⁻¹` on `T_{F(x)}Y` (`EpFunctor.fibreInv_eq_tangentMapOn`). -/
def fibreInv (f : P.TangentSpace → Q.TangentSpace) (x : X) (β : Q.TangentSpace) :
    P.TangentSpace :=
  @Classical.epsilon _ (P.nonempty_tangentSpace x)
    fun α => P.levelVal 1 (P.tangentProj α) = x ∧ f α = β

theorem fibreInv_spec {f : P.TangentSpace → Q.TangentSpace} {x : X} {β : Q.TangentSpace}
    (h : ∃ α, P.levelVal 1 (P.tangentProj α) = x ∧ f α = β) :
    P.levelVal 1 (P.tangentProj (fibreInv f x β)) = x ∧ f (fibreInv f x β) = β :=
  Classical.epsilon_spec h

theorem fibreInv_apply {f : P.TangentSpace → Q.TangentSpace} {x : X}
    (hinj : InjOn f {α | P.levelVal 1 (P.tangentProj α) = x}) {α : P.TangentSpace}
    (hα : P.levelVal 1 (P.tangentProj α) = x) : fibreInv f x (f α) = α :=
  hinj (fibreInv_spec ⟨α, hα, rfl⟩).1 hα (fibreInv_spec ⟨α, hα, rfl⟩).2

end MPolyfold

section Sections

variable {Obj Mor Obj' Mor' Obj'' Mor'' : Type u}
  [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Z : EpGroupoid Obj'' Mor''}

open MPolyfold CategoryTheory

/-! ### Section functors of `Gr̂(X) → X_∞` -/

namespace EpGroupoid

variable (X) in
/-- **A section functor of `π̂ : Gr̂(X) → X_∞`** (2021 p. 538, "no continuity requirement"):
`x ↦ T(x) ∈ Gr̂(x)` on `X_∞`, natural, `t(T(s φ), φ) = T(t φ)` (the first two conditions of
Definition 9.3.2; `orientedSection`, `IsGrHatSection.toFunctor` give the functor). -/
structure IsGrHatSection (T : Obj → X.PObj.OrTangent →₀ ℚ) : Prop where
  mem : ∀ x ∈ X.PObj.smoothSet, T x ∈ X.GrHat x
  natural : ∀ φ : Mor, X.src φ ∈ X.PObj.smoothSet → X.grHatPush φ (T (X.src φ)) = T (X.tgt φ)

variable (X) in
/-- **`Γ(π̂_X)`** (2021 p. 538): the section functors, as functions on `X` vanishing off `X_∞`
(the text's sections are defined on `X_∞` only). -/
def GrHatSections : Set (Obj → X.PObj.OrTangent →₀ ℚ) :=
  {T | X.IsGrHatSection T ∧ ∀ x, x ∉ X.PObj.smoothSet → T x = 0}

/-- An orientation (Definition 9.3.2) is a section functor. -/
theorem IsOrientation.isGrHatSection {Θ : Obj → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hT : X.IsOrientation Θ T) : X.IsGrHatSection T := ⟨hT.mem, hT.natural⟩

/-- The section `x ↦ T(x)`, `φ ↦ (T(s φ), φ)` as a functor `X_∞ → Gr̂(X)`. -/
def IsGrHatSection.toFunctor {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsGrHatSection T) :
    X.SmoothCat ⥤ X.GrHatObj where
  obj x := ⟨x.pt, x.smooth, T x.pt, hT.mem _ x.smooth⟩
  map {x y} f := ⟨SmoothCat.mor f, SmoothCat.src_mor f, SmoothCat.tgt_mor f, by
    change X.grHatPush (SmoothCat.mor f) (T x.pt) = T y.pt
    rw [← SmoothCat.src_mor f, ← SmoothCat.tgt_mor f]
    exact hT.natural _ (by rw [SmoothCat.src_mor f]; exact x.smooth)⟩
  map_id x := Subtype.ext (SmoothCat.mor_id x)
  map_comp f g := Subtype.ext (SmoothCat.mor_comp f g)

theorem IsGrHatSection.toFunctor_comp_grHatProj {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hT : X.IsGrHatSection T) : hT.toFunctor ⋙ X.grHatProj = 𝟭 X.SmoothCat := rfl

/-- The oriented tangent sets in the support of an element of `Gr̂(x)` are oriented at `x`. -/
theorem isOrientedAt_of_mem_support {x : Obj} {w : X.PObj.OrTangent →₀ ℚ} (hw : w ∈ X.GrHat x)
    {g : X.PObj.OrTangent} (hg : g ∈ w.support) : X.PObj.IsOrientedAt x g := hw.2 g hg

/-- `∑ σ_L · f(L)` lies in `Gr̂(y)` if `f` maps oriented tangent sets at `x` to ones at `y`. -/
theorem mapDomain_mem_GrHat {x : Obj} {y : Obj'} {w : X.PObj.OrTangent →₀ ℚ} (hw : w ∈ X.GrHat x)
    {f : X.PObj.TangentSpace → Y.PObj.TangentSpace}
    (hf : ∀ g, X.PObj.IsOrientedAt x g → Y.PObj.IsOrientedAt y (g.map f)) :
    w.mapDomain (OrTangent.map f) ∈ Y.GrHat y := by
  classical
  refine ⟨fun g => ?_, fun g hg => ?_⟩
  · rw [Finsupp.mapDomain, Finsupp.sum_apply]
    refine Finset.sum_nonneg fun g' _ => ?_
    dsimp only
    rw [Finsupp.single_apply]
    split_ifs
    · exact hw.1 g'
    · exact le_rfl
  · obtain ⟨g', hg', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
    exact hf g' (hw.2 g' hg')

/-- `∑ σ_L · f(L) = ∑ σ_L · f'(L)` if `f = f'` on `T_xX`. -/
theorem mapDomain_map_congr {x : Obj} {w : X.PObj.OrTangent →₀ ℚ} (hw : w ∈ X.GrHat x)
    {f f' : X.PObj.TangentSpace → Y.PObj.TangentSpace}
    (h : ∀ α, X.PObj.levelVal 1 (X.PObj.tangentProj α) = x → f α = f' α) :
    w.mapDomain (OrTangent.map f) = w.mapDomain (OrTangent.map f') :=
  Finsupp.mapDomain_congr fun g hg =>
    OrTangent.map_congr (fun α hα => h α ((hw.2 g hg).1 α hα)) fun _ hv i =>
      (hw.2 g hg).mem_carrier hv i

theorem mapDomain_map_map {w : X.PObj.OrTangent →₀ ℚ}
    (f : X.PObj.TangentSpace → Y.PObj.TangentSpace)
    (f' : Y.PObj.TangentSpace → Z.PObj.TangentSpace) :
    (w.mapDomain (OrTangent.map f)).mapDomain (OrTangent.map f') =
      w.mapDomain (OrTangent.map (f' ∘ f)) := by
  rw [← Finsupp.mapDomain_comp]
  exact Finsupp.mapDomain_congr fun g _ => OrTangent.map_map f f' g

theorem grHatPush_mapDomain_map {w : X.PObj.OrTangent →₀ ℚ}
    (f : X.PObj.TangentSpace → Y.PObj.TangentSpace) (φ : Mor') :
    Y.grHatPush φ (w.mapDomain (OrTangent.map f)) =
      w.mapDomain (OrTangent.map (Y.tangentMor φ ∘ f)) :=
  mapDomain_map_map f (Y.tangentMor φ)

theorem mapDomain_map_grHatPush {w : X.PObj.OrTangent →₀ ℚ} (φ : Mor)
    (f : X.PObj.TangentSpace → Y.PObj.TangentSpace) :
    (X.grHatPush φ w).mapDomain (OrTangent.map f) =
      w.mapDomain (OrTangent.map (f ∘ X.tangentMor φ)) :=
  mapDomain_map_map (X.tangentMor φ) f

theorem mapDomain_map_id {x : Obj} {w : X.PObj.OrTangent →₀ ℚ} (hw : w ∈ X.GrHat x)
    {f : X.PObj.TangentSpace → X.PObj.TangentSpace}
    (h : ∀ α, X.PObj.levelVal 1 (X.PObj.tangentProj α) = x → f α = α) :
    w.mapDomain (OrTangent.map f) = w := by
  rw [mapDomain_map_congr hw (f' := id) h]
  conv_rhs => rw [← Finsupp.mapDomain_id (v := w)]
  exact Finsupp.mapDomain_congr fun g _ => OrTangent.map_id g

/-- `Tψ⁻¹`, read as `Tψ ∘ Tψ⁻¹ = id` on `T_{t ψ}X`. -/
theorem tangentMor_tangentMor_inv {ψ : Mor} (hψ : ψ ∈ X.PMor.levelSet 1)
    {β : X.PObj.TangentSpace} (hβ : X.PObj.levelVal 1 (X.PObj.tangentProj β) = X.tgt ψ) :
    X.tangentMor ψ (X.tangentMor (X.inv ψ) β) = β := by
  have h1 : X.inv ψ ∈ X.PMor.levelSet 1 := by
    rw [← X.mem_levelSet_src_iff, X.src_inv, X.mem_levelSet_tgt_iff]; exact hψ
  have h := X.tangentMor_inv_tangentMor h1 (by rw [X.src_inv]; exact hβ)
  rwa [X.inv_inv] at h

/-- Smooth targets have smooth morphisms in level `1`. -/
theorem mem_levelSet_one_of_tgt_mem_smoothSet {ψ : Mor} (h : X.tgt ψ ∈ X.PObj.smoothSet) :
    ψ ∈ X.PMor.levelSet 1 :=
  mem_iInter.1 ((X.mem_smoothSet_tgt_iff ψ).1 h) 1

theorem src_mem_smoothSet_of_tgt {ψ : Mor} (h : X.tgt ψ ∈ X.PObj.smoothSet) :
    X.src ψ ∈ X.PObj.smoothSet :=
  (X.mem_smoothSet_src_iff ψ).2 ((X.mem_smoothSet_tgt_iff ψ).1 h)

theorem tgt_mem_smoothSet_of_src {ψ : Mor} (h : X.src ψ ∈ X.PObj.smoothSet) :
    X.tgt ψ ∈ X.PObj.smoothSet :=
  (X.mem_smoothSet_tgt_iff ψ).2 ((X.mem_smoothSet_src_iff ψ).1 h)

theorem mem_levelSet_one_of_mem_smoothSet {x : Obj} (h : x ∈ X.PObj.smoothSet) :
    x ∈ X.PObj.levelSet 1 :=
  mem_iInter.1 h 1

end EpGroupoid

namespace EpFunctor

open EpGroupoid

variable {F : EpFunctor X Y}

/-! ### Tangent maps of functors on fibres -/

theorem levelVal_tangentProj_tangent_obj (F : EpFunctor X Y) (α : X.PObj.TangentSpace) :
    Y.PObj.levelVal 1 (Y.PObj.tangentProj (F.tangent.obj α)) =
      F.obj (X.PObj.levelVal 1 (X.PObj.tangentProj α)) :=
  MPolyfold.levelVal_tangentProj_tangentMap _ α

/-- `TF` is injective on `T_xX` for a local sc-diffeomorphism `F`. -/
theorem injOn_tangent_obj (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj) (x : Obj) :
    InjOn F.tangent.obj {α | X.PObj.levelVal 1 (X.PObj.tangentProj α) = x} := by
  obtain ⟨U, V, g, hxU, hd⟩ := hF x
  intro α hα α' hα' h
  have h1 : α ∈ X.PObj.tangentPreimage U := by change _ ∈ U; rw [hα]; exact hxU
  have h2 : α' ∈ X.PObj.tangentPreimage U := by change _ ∈ U; rw [hα']; exact hxU
  rw [tangent_obj_eq_tangentMapOn hd h1, tangent_obj_eq_tangentMapOn hd h2] at h
  exact hd.injOn_tangent h1 h2 h

/-- On `T_{F(x)}Y`, `fibreInv TF x` is the tangent map of a local inverse of `F` at `x`. -/
theorem fibreInv_eq_tangentMapOn (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj) {x : Obj}
    {U : Set Obj} {V : Set Obj'} {g : Obj' → Obj} (hd : X.PObj.IsScDiffeoOn Y.PObj F.obj g U V)
    (hxU : x ∈ U) {β : Y.PObj.TangentSpace}
    (hβ : Y.PObj.levelVal 1 (Y.PObj.tangentProj β) = F.obj x) :
    fibreInv F.tangent.obj x β = tangentMapOn hd.isScSmoothOn_inv β := by
  have hβV : β ∈ Y.PObj.tangentPreimage V := by change _ ∈ V; rw [hβ]; exact hd.mapsTo hxU
  have hαU : tangentMapOn hd.isScSmoothOn_inv β ∈ X.PObj.tangentPreimage U :=
    tangentMapOn_mapsTo hd.isScSmoothOn_inv hd.mapsTo_inv hβV
  have hbase : X.PObj.levelVal 1 (X.PObj.tangentProj (tangentMapOn hd.isScSmoothOn_inv β)) = x := by
    rw [levelVal_tangentProj_tangentMapOn hd.isScSmoothOn_inv hβV, hβ, hd.left_inv x hxU]
  have hβ' : F.tangent.obj (tangentMapOn hd.isScSmoothOn_inv β) = β := by
    rw [tangent_obj_eq_tangentMapOn hd hαU]; exact hd.tangent.right_inv β hβV
  conv_lhs => rw [← hβ']
  exact fibreInv_apply (injOn_tangent_obj hF x) hbase

theorem fibreInv_spec_tangent (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj) {x : Obj}
    {β : Y.PObj.TangentSpace} (hβ : Y.PObj.levelVal 1 (Y.PObj.tangentProj β) = F.obj x) :
    X.PObj.levelVal 1 (X.PObj.tangentProj (fibreInv F.tangent.obj x β)) = x ∧
      F.tangent.obj (fibreInv F.tangent.obj x β) = β := by
  obtain ⟨U, V, g, hxU, hd⟩ := hF x
  have hβV : β ∈ Y.PObj.tangentPreimage V := by change _ ∈ V; rw [hβ]; exact hd.mapsTo hxU
  have hαU : tangentMapOn hd.isScSmoothOn_inv β ∈ X.PObj.tangentPreimage U :=
    tangentMapOn_mapsTo hd.isScSmoothOn_inv hd.mapsTo_inv hβV
  refine fibreInv_spec ⟨tangentMapOn hd.isScSmoothOn_inv β, ?_, ?_⟩
  · rw [levelVal_tangentProj_tangentMapOn hd.isScSmoothOn_inv hβV, hβ, hd.left_inv x hxU]
  · rw [tangent_obj_eq_tangentMapOn hd hαU]; exact hd.tangent.right_inv β hβV

theorem fibreInv_tangent_obj (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj) {x : Obj}
    {α : X.PObj.TangentSpace} (hα : X.PObj.levelVal 1 (X.PObj.tangentProj α) = x) :
    fibreInv F.tangent.obj x (F.tangent.obj α) = α :=
  fibreInv_apply (injOn_tangent_obj hF x) hα

/-- `TF` maps oriented tangent sets at `x` to oriented tangent sets at `F(x)`. -/
theorem isOrientedAt_map_tangent_obj (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj) {x : Obj}
    {g : X.PObj.OrTangent} (h : X.PObj.IsOrientedAt x g) :
    Y.PObj.IsOrientedAt (F.obj x) (g.map F.tangent.obj) := by
  obtain ⟨U, V, f', hxU, hd⟩ := hF x
  rw [OrTangent.map_congr (f' := tangentMapOn hd.isScSmoothOn) (fun α hα =>
    tangent_obj_eq_tangentMapOn hd (show _ ∈ U from by rw [h.1 α hα]; exact hxU))
    fun v hv i => h.mem_carrier hv i]
  exact h.map_tangentMapOn hd hxU

/-- `Tψ ∘ TF(x) : T_xX → T_yY` of (11.8) maps oriented tangent sets at `x` to ones at `y`. -/
theorem isOrientedAt_map_transfer (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj) {x : Obj}
    {ψ : Mor'} (hs : Y.src ψ = F.obj x) {g : X.PObj.OrTangent} (h : X.PObj.IsOrientedAt x g) :
    Y.PObj.IsOrientedAt (Y.tgt ψ) (g.map (Y.tangentMor ψ ∘ F.tangent.obj)) := by
  rw [← OrTangent.map_map, OrTangent.map_eq_push]
  exact isOrientedAt_push_tangentMor (hs ▸ isOrientedAt_map_tangent_obj hF h)

/-- `TF(x)⁻¹ : T_{F(x)}Y → T_xX` maps oriented tangent sets at `F(x)` to ones at `x`. -/
theorem isOrientedAt_map_fibreInv (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj) {x : Obj}
    {g : Y.PObj.OrTangent} (h : Y.PObj.IsOrientedAt (F.obj x) g) :
    X.PObj.IsOrientedAt x (g.map (fibreInv F.tangent.obj x)) := by
  obtain ⟨U, V, f', hxU, hd⟩ := hF x
  rw [OrTangent.map_congr (f' := tangentMapOn hd.isScSmoothOn_inv) (fun β hβ =>
    fibreInv_eq_tangentMapOn hF hd hxU (h.1 β hβ)) fun v hv i => h.mem_carrier hv i]
  have := h.map_tangentMapOn hd.symm (hd.mapsTo hxU)
  rwa [hd.left_inv x hxU] at this

/-- For a natural transformation `τ : F → G`: `TG = Tτ(x) ∘ TF` on `T_xX`. -/
theorem _root_.Polyfold.EpNatTrans.tangent_obj_eq {G : EpFunctor X Y} (τ : EpNatTrans F G)
    (α : X.PObj.TangentSpace) :
    G.tangent.obj α =
      Y.tangentMor (τ.app (X.PObj.levelVal 1 (X.PObj.tangentProj α))) (F.tangent.obj α) := by
  have hb : Y.tBase (MPolyfold.tangentMap τ.isScSmoothMap_app α) =
      τ.app (X.PObj.levelVal 1 (X.PObj.tangentProj α)) :=
    Y.tBase_tangentMap τ.isScSmoothMap_app α
  have hs : Y.tSrc (MPolyfold.tangentMap τ.isScSmoothMap_app α) = F.tangent.obj α :=
    MPolyfold.tangentMap_tangentMap_of_eq Y.isScSmoothMap_src τ.isScSmoothMap_app
      F.isScSmoothMap_obj (funext τ.src_app) α
  have ht : Y.tTgt (MPolyfold.tangentMap τ.isScSmoothMap_app α) = G.tangent.obj α :=
    MPolyfold.tangentMap_tangentMap_of_eq Y.isScSmoothMap_tgt τ.isScSmoothMap_app
      G.isScSmoothMap_obj (funext τ.tgt_app) α
  rw [← hb, ← hs, ← ht, Y.tangentMor_tSrc]

/-! ### Definition (11.8): the push-forward of sections -/

variable (F) in
open scoped Classical in
/-- **The push-forward `F_* : Γ(π̂_X) → Γ(π̂_Y)` of (11.8)** (2021 p. 538):
`(F_*h)(y) = Tψ ∘ TF(x) h(x)` for a chosen `x` and `ψ : F(x) → y` (`0` off `Y_∞` or if there is
none); the formal sums are moved by `OrTangent.map`.  It does not depend on the choice
(`pushSection_eq`). -/
def pushSection (T : Obj → X.PObj.OrTangent →₀ ℚ) (y : Obj') : Y.PObj.OrTangent →₀ ℚ :=
  if h : y ∈ Y.PObj.smoothSet ∧ ∃ p : Obj × Mor', Y.src p.2 = F.obj p.1 ∧ Y.tgt p.2 = y then
    (T h.2.choose.1).mapDomain (OrTangent.map (Y.tangentMor h.2.choose.2 ∘ F.tangent.obj))
  else 0

variable (F) in
/-- **The pull-back `F^* : Γ(π̂_Y) → Γ(π̂_X)` of (11.9)** (2021 p. 539): `TF(x) (F^*h')(x) =
h'(F(x))`, i.e. `(F^*h')(x) = TF(x)⁻¹ h'(F(x))` with the inverse `fibreInv` of `TF` on `T_xX`
(`0` off `X_∞`). -/
def pullSection (T' : Obj' → Y.PObj.OrTangent →₀ ℚ) (x : Obj) : X.PObj.OrTangent →₀ ℚ :=
  open scoped Classical in
  if x ∈ X.PObj.smoothSet then (T' (F.obj x)).mapDomain (OrTangent.map (fibreInv F.tangent.obj x))
  else 0

theorem pushSection_of_not_mem {T : Obj → X.PObj.OrTangent →₀ ℚ} {y : Obj'}
    (hy : y ∉ Y.PObj.smoothSet) : F.pushSection T y = 0 := by
  classical
  rw [pushSection, dif_neg fun h => hy h.1]

theorem pullSection_of_not_mem {T' : Obj' → Y.PObj.OrTangent →₀ ℚ} {x : Obj}
    (hx : x ∉ X.PObj.smoothSet) : F.pullSection T' x = 0 := by
  classical
  rw [pullSection, if_neg hx]

theorem pullSection_of_mem {T' : Obj' → Y.PObj.OrTangent →₀ ℚ} {x : Obj}
    (hx : x ∈ X.PObj.smoothSet) : F.pullSection T' x =
      (T' (F.obj x)).mapDomain (OrTangent.map (fibreInv F.tangent.obj x)) := by
  classical
  rw [pullSection, if_pos hx]

/-- The two ways `ψ : F(x) → y`, `ψ₀ : F(x₀) → y` of computing (11.8) agree (the morphism
`ψ₀⁻¹ ∘ ψ = F(γ)`, `γ : x → x₀`, and the naturality of `T`). -/
theorem mapDomain_transfer_eq (hF : F.IsEquivalence) {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hT : X.IsGrHatSection T) {x x₀ : Obj} {ψ ψ₀ : Mor'} (hs : Y.src ψ = F.obj x)
    (hs₀ : Y.src ψ₀ = F.obj x₀) (ht : Y.tgt ψ₀ = Y.tgt ψ) (hy : Y.tgt ψ ∈ Y.PObj.smoothSet) :
    (T x₀).mapDomain (OrTangent.map (Y.tangentMor ψ₀ ∘ F.tangent.obj)) =
      (T x).mapDomain (OrTangent.map (Y.tangentMor ψ ∘ F.tangent.obj)) := by
  have hd := hF.isLocalScDiffeo_obj
  have hψ1 := Y.mem_levelSet_one_of_tgt_mem_smoothSet hy
  have hxs : x ∈ X.PObj.smoothSet :=
    (hd.mem_smoothSet_iff x).1 (hs ▸ Y.src_mem_smoothSet_of_tgt hy)
  -- `γ : x → x₀` with `F(γ) = ψ₀⁻¹ ∘ ψ`
  have e1 : Y.src (Y.inv ψ₀) = Y.tgt ψ := by rw [Y.src_inv, ht]
  have hc1 : Y.src (Y.comp (Y.inv ψ₀) ψ) = F.obj x := by rw [Y.src_comp _ _ e1, hs]
  have hc2 : Y.tgt (Y.comp (Y.inv ψ₀) ψ) = F.obj x₀ := by
    rw [Y.tgt_comp _ _ e1, Y.tgt_inv, hs₀]
  obtain ⟨γ, hγs, hγt, hγ⟩ := hF.exists_mor_eq hc1 hc2
  have hnat := hT.natural γ (by rw [hγs]; exact hxs)
  rw [hγs, hγt] at hnat
  have hγ1 : γ ∈ X.PMor.levelSet 1 := by
    rw [← X.mem_levelSet_src_iff, hγs]; exact X.mem_levelSet_one_of_mem_smoothSet hxs
  rw [← hnat, mapDomain_map_grHatPush]
  refine mapDomain_map_congr (hT.mem x hxs) fun α hα => ?_
  have hαs : X.PObj.levelVal 1 (X.PObj.tangentProj α) = X.src γ := by rw [hγs]; exact hα
  have hβ : Y.PObj.levelVal 1 (Y.PObj.tangentProj (F.tangent.obj α)) = Y.src ψ := by
    rw [levelVal_tangentProj_tangent_obj, hα, hs]
  have hδ : Y.PObj.levelVal 1 (Y.PObj.tangentProj (Y.tangentMor ψ (F.tangent.obj α))) =
      Y.tgt ψ₀ := by
    rw [Y.levelVal_tangentProj_tangentMor hψ1 hβ, ht]
  simp only [Function.comp_apply]
  rw [← F.tangentMor_mor hγ1 hαs, hγ, Y.tangentMor_comp hψ1 e1 hβ,
    Y.tangentMor_tangentMor_inv (Y.mem_levelSet_one_of_tgt_mem_smoothSet (ht ▸ hy)) hδ]

/-- **(11.8) is independent of the choices** (2021 p. 538, "since `h` is functorial and `F` an
equivalence"): `(F_*h)(y) = Tψ ∘ TF(x) h(x)` for **every** `ψ : F(x) → y`, `y ∈ Y_∞`. -/
theorem pushSection_eq (hF : F.IsEquivalence) {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hT : X.IsGrHatSection T) {x : Obj} {ψ : Mor'} (hs : Y.src ψ = F.obj x)
    (hy : Y.tgt ψ ∈ Y.PObj.smoothSet) :
    F.pushSection T (Y.tgt ψ) =
      (T x).mapDomain (OrTangent.map (Y.tangentMor ψ ∘ F.tangent.obj)) := by
  classical
  have hex : Y.tgt ψ ∈ Y.PObj.smoothSet ∧
      ∃ p : Obj × Mor', Y.src p.2 = F.obj p.1 ∧ Y.tgt p.2 = Y.tgt ψ := ⟨hy, ⟨(x, ψ), hs, rfl⟩⟩
  rw [pushSection, dif_pos hex]
  exact mapDomain_transfer_eq hF hT hs hex.2.choose_spec.1 hex.2.choose_spec.2 hy

/-- `(F_*h)(F(x)) = TF(x) h(x)`. -/
theorem pushSection_obj (hF : F.IsEquivalence) {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hT : X.IsGrHatSection T) {x : Obj} (hx : x ∈ X.PObj.smoothSet) :
    F.pushSection T (F.obj x) = (T x).mapDomain (OrTangent.map F.tangent.obj) := by
  have hFx : F.obj x ∈ Y.PObj.smoothSet := (hF.isLocalScDiffeo_obj.mem_smoothSet_iff x).2 hx
  have h := pushSection_eq hF hT (ψ := Y.unit (F.obj x)) (Y.src_unit _)
    (by rw [Y.tgt_unit]; exact hFx)
  rw [Y.tgt_unit] at h
  rw [h]
  refine mapDomain_map_congr (hT.mem x hx) fun α hα => ?_
  exact Y.tangentMor_unit_of_eq (by rw [levelVal_tangentProj_tangent_obj, hα])

/-- **Lemma 11.3.4 for an equivalence, `F_*`**: the push-forward of a section functor is a section
functor, vanishing off `Y_∞`. -/
theorem isGrHatSection_pushSection (hF : F.IsEquivalence) {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hT : X.IsGrHatSection T) : Y.IsGrHatSection (F.pushSection T) := by
  have hd := hF.isLocalScDiffeo_obj
  refine ⟨fun y hy => ?_, fun φ hφ => ?_⟩
  · obtain ⟨x, ψ, hs, rfl⟩ := hF.exists_iso y
    have hxs : x ∈ X.PObj.smoothSet :=
      (hd.mem_smoothSet_iff x).1 (hs ▸ Y.src_mem_smoothSet_of_tgt hy)
    rw [pushSection_eq hF hT hs hy]
    exact mapDomain_mem_GrHat (hT.mem x hxs) fun g hg => isOrientedAt_map_transfer hd hs hg
  · obtain ⟨x, ψ, hs, ht⟩ := hF.exists_iso (Y.src φ)
    have hψy : Y.tgt ψ ∈ Y.PObj.smoothSet := ht ▸ hφ
    have hxs : x ∈ X.PObj.smoothSet :=
      (hd.mem_smoothSet_iff x).1 (hs ▸ Y.src_mem_smoothSet_of_tgt hψy)
    have hφψ : Y.src φ = Y.tgt ψ := ht.symm
    have hφt : Y.tgt φ ∈ Y.PObj.smoothSet := Y.tgt_mem_smoothSet_of_src hφ
    have h1 := pushSection_eq hF hT (ψ := Y.comp φ ψ) (by rw [Y.src_comp _ _ hφψ, hs])
      (by rw [Y.tgt_comp _ _ hφψ]; exact hφt)
    rw [Y.tgt_comp _ _ hφψ] at h1
    rw [h1, ← ht, pushSection_eq hF hT hs hψy, grHatPush_mapDomain_map]
    refine mapDomain_map_congr (hT.mem x hxs) fun α hα => ?_
    have hβ : Y.PObj.levelVal 1 (Y.PObj.tangentProj (F.tangent.obj α)) = Y.src ψ := by
      rw [levelVal_tangentProj_tangent_obj, hα, hs]
    simp only [Function.comp_apply]
    rw [Y.tangentMor_comp (Y.mem_levelSet_one_of_tgt_mem_smoothSet hψy) hφψ hβ]

theorem pushSection_mem_grHatSections (hF : F.IsEquivalence) {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hT : X.IsGrHatSection T) : F.pushSection T ∈ Y.GrHatSections :=
  ⟨isGrHatSection_pushSection hF hT, fun _ hy => pushSection_of_not_mem hy⟩

/-- **Lemma 11.3.4 for an equivalence, `F^*`** (11.9): the pull-back of a section functor is a
section functor (only the local sc-diffeomorphism property of `F` on objects is used). -/
theorem isGrHatSection_pullSection (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj)
    {T' : Obj' → Y.PObj.OrTangent →₀ ℚ} (hT' : Y.IsGrHatSection T') :
    X.IsGrHatSection (F.pullSection T') := by
  refine ⟨fun x hx => ?_, fun φ hφ => ?_⟩
  · rw [pullSection_of_mem hx]
    exact mapDomain_mem_GrHat (hT'.mem _ ((hF.mem_smoothSet_iff x).2 hx)) fun g hg =>
      isOrientedAt_map_fibreInv hF hg
  · have hφt : X.tgt φ ∈ X.PObj.smoothSet := X.tgt_mem_smoothSet_of_src hφ
    have hFs : F.obj (X.src φ) ∈ Y.PObj.smoothSet := (hF.mem_smoothSet_iff _).2 hφ
    have hφ1 : φ ∈ X.PMor.levelSet 1 := by
      rw [← X.mem_levelSet_src_iff]; exact X.mem_levelSet_one_of_mem_smoothSet hφ
    have hnat := hT'.natural (F.mor φ) (by rw [F.src_mor]; exact hFs)
    rw [F.src_mor, F.tgt_mor] at hnat
    rw [pullSection_of_mem hφ, pullSection_of_mem hφt, ← hnat, grHatPush_mapDomain_map,
      mapDomain_map_grHatPush]
    refine mapDomain_map_congr (hT'.mem _ hFs) fun β hβ => ?_
    obtain ⟨hα, hFα⟩ := fibreInv_spec_tangent hF hβ
    simp only [Function.comp_apply]
    have hTφ : X.PObj.levelVal 1 (X.PObj.tangentProj
        (X.tangentMor φ (fibreInv F.tangent.obj (X.src φ) β))) = X.tgt φ :=
      X.levelVal_tangentProj_tangentMor hφ1 hα
    conv_rhs => rw [← hFα]
    rw [F.tangentMor_mor hφ1 hα, fibreInv_tangent_obj hF hTφ]

theorem pullSection_mem_grHatSections (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj)
    {T' : Obj' → Y.PObj.OrTangent →₀ ℚ} (hT' : Y.IsGrHatSection T') :
    F.pullSection T' ∈ X.GrHatSections :=
  ⟨isGrHatSection_pullSection hF hT', fun _ hx => pullSection_of_not_mem hx⟩

/-- **`F^* F_* h = h`** for an equivalence `F` and `h ∈ Γ(π̂_X)`. -/
theorem pullSection_pushSection (hF : F.IsEquivalence) {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hT : T ∈ X.GrHatSections) : F.pullSection (F.pushSection T) = T := by
  funext x
  by_cases hx : x ∈ X.PObj.smoothSet
  · rw [pullSection_of_mem hx, pushSection_obj hF hT.1 hx, mapDomain_map_map]
    exact mapDomain_map_id (hT.1.mem x hx) fun α hα =>
      fibreInv_tangent_obj hF.isLocalScDiffeo_obj hα
  · rw [pullSection_of_not_mem hx, hT.2 x hx]

/-- **`F_* F^* h' = h'`** for an equivalence `F` and `h' ∈ Γ(π̂_Y)`. -/
theorem pushSection_pullSection (hF : F.IsEquivalence) {T' : Obj' → Y.PObj.OrTangent →₀ ℚ}
    (hT' : T' ∈ Y.GrHatSections) : F.pushSection (F.pullSection T') = T' := by
  have hd := hF.isLocalScDiffeo_obj
  funext y
  by_cases hy : y ∈ Y.PObj.smoothSet
  · obtain ⟨x, ψ, hs, rfl⟩ := hF.exists_iso y
    have hxs : x ∈ X.PObj.smoothSet :=
      (hd.mem_smoothSet_iff x).1 (hs ▸ Y.src_mem_smoothSet_of_tgt hy)
    have hFs : F.obj x ∈ Y.PObj.smoothSet := (hd.mem_smoothSet_iff x).2 hxs
    rw [pushSection_eq hF (isGrHatSection_pullSection hd hT'.1) hs hy, pullSection_of_mem hxs,
      mapDomain_map_map, ← hT'.1.natural ψ (hs ▸ hFs), hs, grHatPush]
    refine mapDomain_map_congr (hT'.1.mem _ hFs) fun β hβ => ?_
    simp only [Function.comp_apply]
    rw [(fibreInv_spec_tangent hd hβ).2]
  · rw [pushSection_of_not_mem hy, hT'.2 y hy]

/-- **Lemma 11.3.2 (3) for sections** (2021 p. 538, "one immediately deduces"): naturally
equivalent equivalences have the same push-forward `F_* = G_*`. -/
theorem pushSection_eq_of_natTrans {G : EpFunctor X Y} (hF : F.IsEquivalence)
    (hG : G.IsEquivalence) (τ : EpNatTrans F G) {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hT : X.IsGrHatSection T) : F.pushSection T = G.pushSection T := by
  have hd := hF.isLocalScDiffeo_obj
  funext y
  by_cases hy : y ∈ Y.PObj.smoothSet
  · obtain ⟨x, ψ, hs, rfl⟩ := hF.exists_iso y
    have hxs : x ∈ X.PObj.smoothSet :=
      (hd.mem_smoothSet_iff x).1 (hs ▸ Y.src_mem_smoothSet_of_tgt hy)
    have e1 : Y.src ψ = Y.tgt (Y.inv (τ.app x)) := by rw [Y.tgt_inv, τ.src_app, hs]
    have h1 := pushSection_eq hG hT (ψ := Y.comp ψ (Y.inv (τ.app x)))
      (by rw [Y.src_comp _ _ e1, Y.src_inv, τ.tgt_app]) (by rw [Y.tgt_comp _ _ e1]; exact hy)
    rw [Y.tgt_comp _ _ e1] at h1
    rw [h1, pushSection_eq hF hT hs hy]
    refine mapDomain_map_congr (hT.mem x hxs) fun α hα => ?_
    have hFα : Y.PObj.levelVal 1 (Y.PObj.tangentProj (F.tangent.obj α)) = Y.src (τ.app x) := by
      rw [levelVal_tangentProj_tangent_obj, hα, τ.src_app]
    have hτ1 : τ.app x ∈ Y.PMor.levelSet 1 := by
      rw [← Y.mem_levelSet_src_iff, τ.src_app]
      exact Y.mem_levelSet_one_of_mem_smoothSet ((hd.mem_smoothSet_iff x).2 hxs)
    have hGα : Y.PObj.levelVal 1 (Y.PObj.tangentProj (G.tangent.obj α)) =
        Y.src (Y.inv (τ.app x)) := by
      rw [levelVal_tangentProj_tangent_obj, hα, Y.src_inv, τ.tgt_app]
    have hτi : Y.inv (τ.app x) ∈ Y.PMor.levelSet 1 := by
      rw [← Y.mem_levelSet_src_iff, Y.src_inv, Y.mem_levelSet_tgt_iff]; exact hτ1
    simp only [Function.comp_apply]
    rw [Y.tangentMor_comp hτi e1 hGα, τ.tangent_obj_eq, hα,
      Y.tangentMor_inv_tangentMor hτ1 hFα]
  · rw [pushSection_of_not_mem hy, pushSection_of_not_mem hy]

/-- **Lemma 11.3.2 (3) for sections, pull-backs**: `F^* = G^*` for naturally equivalent local
sc-diffeomorphisms (on objects). -/
theorem pullSection_eq_of_natTrans {G : EpFunctor X Y} (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj)
    (τ : EpNatTrans F G) {T' : Obj' → Y.PObj.OrTangent →₀ ℚ} (hT' : Y.IsGrHatSection T') :
    F.pullSection T' = G.pullSection T' := by
  have hG := τ.isLocalScDiffeo_obj hF
  funext x
  by_cases hx : x ∈ X.PObj.smoothSet
  · have hFs : F.obj x ∈ Y.PObj.smoothSet := (hF.mem_smoothSet_iff x).2 hx
    have hnat := hT'.natural (τ.app x) (by rw [τ.src_app]; exact hFs)
    rw [τ.src_app, τ.tgt_app] at hnat
    rw [pullSection_of_mem hx, pullSection_of_mem hx, ← hnat, mapDomain_map_grHatPush]
    refine mapDomain_map_congr (hT'.mem _ hFs) fun β hβ => ?_
    obtain ⟨hα, hFα⟩ := fibreInv_spec_tangent hF hβ
    have e := τ.tangent_obj_eq (fibreInv F.tangent.obj x β)
    rw [hα] at e
    simp only [Function.comp_apply]
    conv_rhs => rw [← hFα]
    rw [← e, fibreInv_tangent_obj hG hα]
  · rw [pullSection_of_not_mem hx, pullSection_of_not_mem hx]

/-- `(G ∘ F)_* = G_* ∘ F_*` on section functors. -/
theorem pushSection_comp {G : EpFunctor Y Z} (hG : G.IsEquivalence) (hF : F.IsEquivalence)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsGrHatSection T) :
    (G.comp F).pushSection T = G.pushSection (F.pushSection T) := by
  have hGF := hG.comp hF
  have hd := hF.isLocalScDiffeo_obj
  have hdG := hG.isLocalScDiffeo_obj
  funext z
  by_cases hz : z ∈ Z.PObj.smoothSet
  · obtain ⟨x, χ, hs, rfl⟩ := hGF.exists_iso z
    have hFxs : F.obj x ∈ Y.PObj.smoothSet :=
      (hdG.mem_smoothSet_iff _).1 (hs ▸ Z.src_mem_smoothSet_of_tgt hz)
    have hxs : x ∈ X.PObj.smoothSet := (hd.mem_smoothSet_iff x).1 hFxs
    rw [pushSection_eq hGF hT hs hz, pushSection_eq hG (isGrHatSection_pushSection hF hT) hs hz,
      pushSection_obj hF hT hxs, mapDomain_map_map, tangent_comp]
    rfl
  · rw [pushSection_of_not_mem hz, pushSection_of_not_mem hz]

/-- `(G ∘ F)^* = F^* ∘ G^*` on section functors. -/
theorem pullSection_comp {G : EpFunctor Y Z} (hG : Y.PObj.IsLocalScDiffeo Z.PObj G.obj)
    (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj) {T'' : Obj'' → Z.PObj.OrTangent →₀ ℚ}
    (hT'' : Z.IsGrHatSection T'') :
    (G.comp F).pullSection T'' = F.pullSection (G.pullSection T'') := by
  have hGF : X.PObj.IsLocalScDiffeo Z.PObj (G.comp F).obj := hG.comp hF
  funext x
  by_cases hx : x ∈ X.PObj.smoothSet
  · have hFs : F.obj x ∈ Y.PObj.smoothSet := (hF.mem_smoothSet_iff x).2 hx
    have hGs : G.obj (F.obj x) ∈ Z.PObj.smoothSet := (hG.mem_smoothSet_iff _).2 hFs
    rw [pullSection_of_mem hx, pullSection_of_mem hx, pullSection_of_mem hFs, mapDomain_map_map]
    refine mapDomain_map_congr (hT''.mem _ hGs) fun γ hγ => ?_
    obtain ⟨hβ, hGβ⟩ := fibreInv_spec_tangent hG hγ
    obtain ⟨hα, hFα⟩ := fibreInv_spec_tangent hF hβ
    simp only [Function.comp_apply]
    have e : (G.comp F).tangent.obj (fibreInv F.tangent.obj x (fibreInv G.tangent.obj
        (F.obj x) γ)) = γ := by
      rw [tangent_comp]; change G.tangent.obj (F.tangent.obj _) = γ; rw [hFα, hGβ]
    conv_lhs => rw [← e]
    exact fibreInv_tangent_obj hGF hα
  · rw [pullSection_of_not_mem hx, pullSection_of_not_mem hx]

/-- The identity pushes sections forward to themselves. -/
theorem pushSection_id {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : T ∈ X.GrHatSections) :
    (EpFunctor.id X).pushSection T = T := by
  funext x
  by_cases hx : x ∈ X.PObj.smoothSet
  · rw [show x = (EpFunctor.id X).obj x from rfl, pushSection_obj (IsEquivalence.id X) hT.1 hx,
      tangent_id]
    exact mapDomain_map_id (hT.1.mem x hx) fun _ _ => rfl
  · rw [pushSection_of_not_mem hx, hT.2 x hx]

/-- The identity pulls sections back to themselves. -/
theorem pullSection_id {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : T ∈ X.GrHatSections) :
    (EpFunctor.id X).pullSection T = T := by
  conv_lhs => rw [← pushSection_id hT]
  exact pullSection_pushSection (IsEquivalence.id X) hT

end EpFunctor

/-! ### Base change in the weak fibred product -/

namespace WeakFibredProduct

open EpFunctor EpGroupoid

/-- **Base change for section push-forwards**: for equivalences `F : X → Y`, `G : Z → Y`,
`(π_Z)_* (π_X)^* h = G^* F_* h` (from `π_Z` an equivalence and `F ∘ π_X ≃ G ∘ π_Z`). -/
theorem pushSection_projRight_pullSection {F : EpFunctor X Y} {G : EpFunctor Z Y}
    (hF : F.IsEquivalence) (hG : G.IsEquivalence) (h : Admissible F G)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : T ∈ X.GrHatSections) :
    (projRight F G h).pushSection ((projLeft F G h).pullSection T) =
      G.pullSection (F.pushSection T) := by
  have hπZ := isEquivalence_projRight hF h
  have hπX := isEquivalence_projLeft hG h
  have hFT := isGrHatSection_pushSection hF hT.1
  rw [← pushSection_pullSection hπZ (pullSection_mem_grHatSections hG.isLocalScDiffeo_obj hFT),
    ← pullSection_comp hG.isLocalScDiffeo_obj hπZ.isLocalScDiffeo_obj hFT,
    ← pullSection_eq_of_natTrans (hF.comp hπX).isLocalScDiffeo_obj (natTrans F G h) hFT,
    pullSection_comp hF.isLocalScDiffeo_obj hπX.isLocalScDiffeo_obj hFT,
    pullSection_pushSection hF hT]

/-- **Base change for section pull-backs**: for equivalences `F`, `G`,
`(π_X)_* (π_Z)^* h = F^* G_* h`. -/
theorem pushSection_projLeft_pullSection {F : EpFunctor X Y} {G : EpFunctor Z Y}
    (hF : F.IsEquivalence) (hG : G.IsEquivalence) (h : Admissible F G)
    {T : Obj'' → Z.PObj.OrTangent →₀ ℚ} (hT : T ∈ Z.GrHatSections) :
    (projLeft F G h).pushSection ((projRight F G h).pullSection T) =
      F.pullSection (G.pushSection T) := by
  have hπZ := isEquivalence_projRight hF h
  have hπX := isEquivalence_projLeft hG h
  have hGT := isGrHatSection_pushSection hG hT.1
  rw [← pushSection_pullSection hπX (pullSection_mem_grHatSections hF.isLocalScDiffeo_obj hGT),
    ← pullSection_comp hF.isLocalScDiffeo_obj hπX.isLocalScDiffeo_obj hGT,
    pullSection_eq_of_natTrans (hF.comp hπX).isLocalScDiffeo_obj (natTrans F G h) hGT,
    pullSection_comp hG.isLocalScDiffeo_obj hπZ.isLocalScDiffeo_obj hGT,
    pullSection_pushSection hG hT]

end WeakFibredProduct

end Sections

/-! ### Lemma 11.3.4: generalized isomorphisms -/

namespace EPLocalization

open EpFunctor EpGroupoid WeakFibredProduct CategoryTheory

namespace Diagram

variable {X Y Z : EP.{u}}

/-- `d_* h = Φ_* F^* h` for a diagram `d : X ←F A →Φ Y` (2021 p. 539: `f_* h := G_* F^* h`). -/
def pushSection (d : Diagram X Y) (T : X.Obj → X.X.PObj.OrTangent →₀ ℚ) :
    Y.Obj → Y.X.PObj.OrTangent →₀ ℚ :=
  d.Φ.pushSection (d.F.pullSection T)

/-- `d^* h' = F_* Φ^* h'` for a diagram `d : X ←F A →Φ Y` (2021 p. 539: `f^* h' := F_* G^* h'`). -/
def pullSection (d : Diagram X Y) (T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ) :
    X.Obj → X.X.PObj.OrTangent →₀ ℚ :=
  d.F.pushSection (d.Φ.pullSection T')

/-- The refinement step for section push-forwards. -/
theorem pushSection_eq_of_isRefinement {d d' : Diagram X Y} (h : d'.IsRefinement d)
    (hΦ : d.Φ.IsEquivalence) {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ}
    (hT : X.X.IsGrHatSection T) : d'.pushSection T = d.pushSection T := by
  have hΦ' := h.isEquivalence_Φ_iff.1 hΦ
  obtain ⟨H, hH, ⟨τF⟩, ⟨τΦ⟩⟩ := h
  have hFH := d.isEquivalence_F.comp hH
  have hS := isGrHatSection_pullSection d.isEquivalence_F.isLocalScDiffeo_obj hT
  unfold pushSection
  rw [← pullSection_eq_of_natTrans hFH.isLocalScDiffeo_obj τF hT,
    ← pushSection_eq_of_natTrans (hΦ.comp hH) hΦ' τΦ
      (isGrHatSection_pullSection hFH.isLocalScDiffeo_obj hT),
    pullSection_comp d.isEquivalence_F.isLocalScDiffeo_obj hH.isLocalScDiffeo_obj hT,
    pushSection_comp hΦ hH (isGrHatSection_pullSection hH.isLocalScDiffeo_obj hS),
    pushSection_pullSection hH
      (pullSection_mem_grHatSections d.isEquivalence_F.isLocalScDiffeo_obj hT)]

/-- The refinement step for section pull-backs. -/
theorem pullSection_eq_of_isRefinement {d d' : Diagram X Y} (h : d'.IsRefinement d)
    (hΦ : d.Φ.IsEquivalence) {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hT' : Y.X.IsGrHatSection T') : d'.pullSection T' = d.pullSection T' := by
  obtain ⟨H, hH, ⟨τF⟩, ⟨τΦ⟩⟩ := h
  have hFH := d.isEquivalence_F.comp hH
  have hΦH := hΦ.comp hH
  have hS := isGrHatSection_pullSection hΦ.isLocalScDiffeo_obj hT'
  unfold pullSection
  rw [← pullSection_eq_of_natTrans hΦH.isLocalScDiffeo_obj τΦ hT',
    ← pushSection_eq_of_natTrans hFH d'.isEquivalence_F τF
      (isGrHatSection_pullSection hΦH.isLocalScDiffeo_obj hT'),
    pullSection_comp hΦ.isLocalScDiffeo_obj hH.isLocalScDiffeo_obj hT',
    pushSection_comp d.isEquivalence_F hH (isGrHatSection_pullSection hH.isLocalScDiffeo_obj hS),
    pushSection_pullSection hH (pullSection_mem_grHatSections hΦ.isLocalScDiffeo_obj hT')]

/-- **`f_*` on sections is well defined (2021 p. 539)**: equivalent diagrams (with `Φ` an
equivalence) have the same push-forwards. -/
theorem pushSection_eq_of_equiv {d d' : Diagram X Y} (h : Equiv d d') (hΦ : d.Φ.IsEquivalence)
    {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ} (hT : X.X.IsGrHatSection T) :
    d.pushSection T = d'.pushSection T := by
  obtain ⟨d'', h1, h2⟩ := h
  have hΦ'' := h1.isEquivalence_Φ_iff.1 hΦ
  rw [← pushSection_eq_of_isRefinement h1 hΦ hT,
    pushSection_eq_of_isRefinement h2 (h2.isEquivalence_Φ_iff.2 hΦ'') hT]

/-- **`f^*` on sections is well defined (2021 p. 539)**. -/
theorem pullSection_eq_of_equiv {d d' : Diagram X Y} (h : Equiv d d') (hΦ : d.Φ.IsEquivalence)
    {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ} (hT' : Y.X.IsGrHatSection T') :
    d.pullSection T' = d'.pullSection T' := by
  obtain ⟨d'', h1, h2⟩ := h
  have hΦ'' := h1.isEquivalence_Φ_iff.1 hΦ
  rw [← pullSection_eq_of_isRefinement h1 hΦ hT',
    pullSection_eq_of_isRefinement h2 (h2.isEquivalence_Φ_iff.2 hΦ'') hT']

end Diagram

namespace EPLoc

variable {X Y Z : EP.{u}}

/-- **The push-forward `f_* : Γ(π̂_X) → Γ(π̂_Y)` of Lemma 11.3.4** (2021 p. 539), computed on a
chosen representative `X ←F A →G Y`: `f_* h = G_* F^* h`. -/
def pushSection (f : of X ⟶ of Y) (T : X.Obj → X.X.PObj.OrTangent →₀ ℚ) :
    Y.Obj → Y.X.PObj.OrTangent →₀ ℚ :=
  (rep f).pushSection T

/-- **The pull-back `f^* : Γ(π̂_Y) → Γ(π̂_X)` of Lemma 11.3.4** (2021 p. 539):
`f^* h' = F_* G^* h'`. -/
def pullSection (f : of X ⟶ of Y) (T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ) :
    X.Obj → X.X.PObj.OrTangent →₀ ℚ :=
  (rep f).pullSection T'

/-- **Lemma 11.3.4, representatives, `f_*`** (2021 p. 539): `[d]_* = Φ_* F^*` for every
representative `d` with `Φ` an equivalence. -/
theorem pushSection_homMk (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence)
    {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ} (hT : X.X.IsGrHatSection T) :
    pushSection (homMk d) T = d.pushSection T :=
  (Diagram.pushSection_eq_of_equiv (equiv_rep_homMk d).symm hΦ hT).symm

/-- **Lemma 11.3.4, representatives, `f^*`**: `[d]^* = F_* Φ^*`. -/
theorem pullSection_homMk (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence)
    {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ} (hT' : Y.X.IsGrHatSection T') :
    pullSection (homMk d) T' = d.pullSection T' :=
  (Diagram.pullSection_eq_of_equiv (equiv_rep_homMk d).symm hΦ hT').symm

/-- **Lemma 11.3.4, `f_* : Γ(π̂_X) → Γ(π̂_Y)`**. -/
theorem pushSection_mem {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ} (hT : X.X.IsGrHatSection T) :
    pushSection f T ∈ Y.X.GrHatSections :=
  pushSection_mem_grHatSections (isEquivalence_rep_Φ hf)
    (isGrHatSection_pullSection (rep f).isEquivalence_F.isLocalScDiffeo_obj hT)

/-- **Lemma 11.3.4, `f^* : Γ(π̂_Y) → Γ(π̂_X)`**. -/
theorem pullSection_mem {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ} (hT' : Y.X.IsGrHatSection T') :
    pullSection f T' ∈ X.X.GrHatSections :=
  pushSection_mem_grHatSections (rep f).isEquivalence_F
    (isGrHatSection_pullSection (isEquivalence_rep_Φ hf).isLocalScDiffeo_obj hT')

/-- **Lemma 11.3.4, `(g ∘ f)_* = g_* ∘ f_*`** (2021 p. 539). -/
theorem pushSection_comp {f : of X ⟶ of Y} {g : of Y ⟶ of Z} (hf : IsGeneralizedIso f)
    (hg : IsGeneralizedIso g) {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ}
    (hT : X.X.IsGrHatSection T) : pushSection (f ≫ g) T = pushSection g (pushSection f T) := by
  have hd := isEquivalence_rep_Φ hf
  have he := isEquivalence_rep_Φ hg
  have hπ := isEquivalence_projRight hd ((rep f).admissible (rep g))
  have hπL := isEquivalence_projLeft (rep g).isEquivalence_F ((rep f).admissible (rep g))
  have hc : ((rep f).comp (rep g)).Φ.IsEquivalence := he.comp hπ
  have hfg : f ≫ g = homMk ((rep f).comp (rep g)) := by
    rw [← homMk_comp, homMk_rep, homMk_rep]
  have hS := isGrHatSection_pullSection (rep f).isEquivalence_F.isLocalScDiffeo_obj hT
  rw [hfg, pushSection_homMk _ hc hT]
  change ((rep g).Φ.comp (projRight _ _ _)).pushSection
    (((rep f).F.comp (projLeft _ _ _)).pullSection T) = _
  rw [EpFunctor.pullSection_comp (rep f).isEquivalence_F.isLocalScDiffeo_obj
      hπL.isLocalScDiffeo_obj hT,
    EpFunctor.pushSection_comp he hπ (isGrHatSection_pullSection hπL.isLocalScDiffeo_obj hS),
    pushSection_projRight_pullSection hd (rep g).isEquivalence_F _
      (pullSection_mem_grHatSections (rep f).isEquivalence_F.isLocalScDiffeo_obj hT)]
  rfl

/-- **Lemma 11.3.4, `(g ∘ f)^* = f^* ∘ g^*`** (2021 p. 539). -/
theorem pullSection_comp {f : of X ⟶ of Y} {g : of Y ⟶ of Z} (hf : IsGeneralizedIso f)
    (hg : IsGeneralizedIso g) {T'' : Z.Obj → Z.X.PObj.OrTangent →₀ ℚ}
    (hT'' : Z.X.IsGrHatSection T'') :
    pullSection (f ≫ g) T'' = pullSection f (pullSection g T'') := by
  have hd := isEquivalence_rep_Φ hf
  have he := isEquivalence_rep_Φ hg
  have hπ := isEquivalence_projRight hd ((rep f).admissible (rep g))
  have hπL := isEquivalence_projLeft (rep g).isEquivalence_F ((rep f).admissible (rep g))
  have hc : ((rep f).comp (rep g)).Φ.IsEquivalence := he.comp hπ
  have hfg : f ≫ g = homMk ((rep f).comp (rep g)) := by
    rw [← homMk_comp, homMk_rep, homMk_rep]
  have hS := isGrHatSection_pullSection he.isLocalScDiffeo_obj hT''
  rw [hfg, pullSection_homMk _ hc hT'']
  change ((rep f).F.comp (projLeft _ _ _)).pushSection
    (((rep g).Φ.comp (projRight _ _ _)).pullSection T'') = _
  rw [EpFunctor.pullSection_comp he.isLocalScDiffeo_obj hπ.isLocalScDiffeo_obj hT'',
    EpFunctor.pushSection_comp (rep f).isEquivalence_F hπL
      (isGrHatSection_pullSection hπ.isLocalScDiffeo_obj hS),
    pushSection_projLeft_pullSection hd (rep g).isEquivalence_F _
      (pullSection_mem_grHatSections he.isLocalScDiffeo_obj hT'')]
  rfl

/-- **Lemma 11.3.4, `(f⁻¹)_* = f^*`** (2021 p. 539). -/
theorem pushSection_inv {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {g : of Y ⟶ of X}
    (h₁ : f ≫ g = 𝟙 _) (h₂ : g ≫ f = 𝟙 _) {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hT' : Y.X.IsGrHatSection T') : pushSection g T' = pullSection f T' := by
  have hd := isEquivalence_rep_Φ hf
  rw [← homMk_rep f] at h₁ h₂
  rw [(theorem_10_3_10 (rep f)).2 hd g h₁ h₂, pushSection_homMk _ (rep f).isEquivalence_F hT']
  rfl

/-- `f^* f_* h = h` for a generalized isomorphism and `h ∈ Γ(π̂_X)`. -/
theorem pullSection_pushSection {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ} (hT : T ∈ X.X.GrHatSections) :
    pullSection f (pushSection f T) = T := by
  have hd := isEquivalence_rep_Φ hf
  unfold pullSection pushSection Diagram.pullSection Diagram.pushSection
  rw [EpFunctor.pullSection_pushSection hd (pullSection_mem_grHatSections
      (rep f).isEquivalence_F.isLocalScDiffeo_obj hT.1),
    EpFunctor.pushSection_pullSection (rep f).isEquivalence_F hT]

/-- `f_* f^* h' = h'` for a generalized isomorphism and `h' ∈ Γ(π̂_Y)`. -/
theorem pushSection_pullSection {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ} (hT' : T' ∈ Y.X.GrHatSections) :
    pushSection f (pullSection f T') = T' := by
  have hd := isEquivalence_rep_Φ hf
  unfold pullSection pushSection Diagram.pullSection Diagram.pushSection
  rw [EpFunctor.pullSection_pushSection (rep f).isEquivalence_F (pullSection_mem_grHatSections
      hd.isLocalScDiffeo_obj hT'.1), EpFunctor.pushSection_pullSection hd hT']

/-- **Lemma 11.3.4** (2021 p. 539), collected: for a generalized isomorphism `f : X → Y`,
`f_*` and `f^*` map section functors to section functors, `(f⁻¹)_* = f^*`, and for every
representative `X ←F A →G Y`, `f_* = G_* F^*` and `f^* = F_* G^*` (the composition laws are
`pushSection_comp`, `pullSection_comp`). -/
theorem lemma_11_3_4 {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) :
    (∀ T, X.X.IsGrHatSection T → pushSection f T ∈ Y.X.GrHatSections) ∧
    (∀ T', Y.X.IsGrHatSection T' → pullSection f T' ∈ X.X.GrHatSections) ∧
    (∀ g : of Y ⟶ of X, f ≫ g = 𝟙 _ → g ≫ f = 𝟙 _ →
      ∀ T', Y.X.IsGrHatSection T' → pushSection g T' = pullSection f T') ∧
    (∀ d : Diagram X Y, homMk d = f → ∀ T, X.X.IsGrHatSection T →
      pushSection f T = d.Φ.pushSection (d.F.pullSection T)) ∧
    (∀ d : Diagram X Y, homMk d = f → ∀ T', Y.X.IsGrHatSection T' →
      pullSection f T' = d.F.pushSection (d.Φ.pullSection T')) := by
  refine ⟨fun T hT => pushSection_mem hf hT, fun T' hT' => pullSection_mem hf hT',
    fun g h₁ h₂ T' hT' => pushSection_inv hf h₁ h₂ hT', fun d hd T hT => ?_,
    fun d hd T' hT' => ?_⟩
  · subst hd
    exact pushSection_homMk d ((theorem_10_3_10 d).1.1 hf) hT
  · subst hd
    exact pullSection_homMk d ((theorem_10_3_10 d).1.1 hf) hT'

end EPLoc

end EPLocalization

/-! ### Witnesses -/

namespace EpGroupoid.Examples

open MPolyfold EpFunctor

/-- **A section functor of `Gr̂` on `ℝ²`**: the orientation `T̂¹` of Example 9.3.5 lies in
`Γ(π̂)` (every point of `ℝ²` is smooth). -/
theorem exampleT1_mem_grHatSections : exampleT1 ∈ (trivial (rnPolyfold 2)).GrHatSections :=
  ⟨example_9_3_5_rn.2.1.isGrHatSection, fun x hx => (hx (by
    change x ∈ (rnPolyfold 2).smoothSet
    rw [TrivialBundle.rnPolyfold_smoothSet]; exact mem_univ x)).elim⟩

/-- `T̂¹` pushed forward (and pulled back) along the identity equivalence of the trivial
ep-groupoid on `ℝ²` (the hypotheses of the push-forward lemmas are satisfiable). -/
theorem pushSection_id_exampleT1 :
    (EpFunctor.id (trivial (rnPolyfold 2))).pushSection exampleT1 = exampleT1 ∧
      (EpFunctor.id (trivial (rnPolyfold 2))).pullSection exampleT1 = exampleT1 :=
  ⟨pushSection_id exampleT1_mem_grHatSections, pullSection_id exampleT1_mem_grHatSections⟩

end EpGroupoid.Examples

end Polyfold
