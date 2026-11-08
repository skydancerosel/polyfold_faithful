import Polyfold.Chapter10.LocalizationProperties

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11 "Geometry up to Equivalences", §11.1 "Ep-Groupoids and Equivalences"
(pp. 521–522; 2017: pp. 375–377): **Theorem 11.1.1** (2017: Theorem 11.1) and **Proposition
11.1.2** (2017: Proposition 11.1).  Numbers and pages are the 2021 text's, the 2017 ones in
parentheses.  Faces (Definition 11.1.3 to Proposition 11.1.8) are in
`EpEquivalenceGeometryFaces.lean`.

# The tangent functor and the degeneracy index on `EP(E⁻¹)`

## The text, paraphrased

(p. 521) Morphisms of `EP(E⁻¹)` are classes `[X ←F A →Φ Y]`, `F` an equivalence; the invertible
ones have `Φ` an equivalence too (Theorem 10.3.10).  (Theorem 11.1.1) The tangent functor induces
a functor `T : EP(E⁻¹) → EP(E⁻¹)`, `X ↦ TX`, `[X ←F A →Φ Y] ↦ [TX ←TF TA →TΦ TY]`.  *Proof*:
`TX` is an ep-groupoid (Theorem 8.1.1), `TF` an equivalence (Theorem 10.1.7); if `H : B → A`
refines, `σ : G → F ∘ H` gives `Tσ : TG → TF ∘ TH` (Proposition 8.1.14); "the remaining argument
is similar".  (p. 522) `d_X(s φ) = d_X(t φ)` gives `d_{|X|} : |X| → ℕ`.  (Proposition 11.1.2) If
`[d] : X → Y` is an isomorphism of `EP(E⁻¹)` and `|[d]|(|x|) = |y|`, then `d_X(x₀) = d_Y(y₀)` for
`x₀ ∈ |x|`, `y₀ ∈ |y|`, and `d_{|X|}(|x|) = d_{|Y|}(|y|)`.  *Proof*: a representative with both
legs equivalences, and equivalences are local sc-diffeomorphisms.

## What is formalized

* `EpFunctor.tangent_comp`, `EpFunctor.tangent_id`, `EpNatTrans.castEq` (helpers).
* `EPLocalization.wfpLift` (`wfpLiftObj`, `wfpLiftMor`, `conj_wfpLiftMor`): the functor
  `C → X ×_Y Z`, `c ↦ (P(c), τ(c), Q(c))`, of functors `P`, `Q` and `τ : Φ ∘ P → G ∘ Q`, with
  `projLeft_comp_wfpLift`, `projRight_comp_wfpLift`.
* `Diagram.tangent`; `Diagram.IsRefinement.tangent`, `Diagram.Equiv.tangent` (the text's
  argument); `isRefinement_tangent_id`, `isRefinement_tangent_comp` (identities and composition).
* `EPLoc.tangentFunctor : EP(E⁻¹) ⥤ EP(E⁻¹)`; **Theorem 11.1.1**: `EPLoc.theorem_11_1_1`, including
  `T(i(Φ)) = i(TΦ)` (`tangentFunctor_map_localizationFunctor`); `isGeneralizedIso_tangent`.
* `Diagram.degIndexOrbit_orbitMap`, `EPLoc.degIndexOrbit_orbitMap`; **Proposition 11.1.2**:
  `EPLoc.proposition_11_1_2`.  `d_{|X|}` is Chapter 7's `EpGroupoid.degIndexOrbit`.

## What the text leaves implicit, and the choices made

* **Composition.**  The text checks only that `T` respects refinements ("the remaining argument is
  similar").  That `T` preserves composition needs a comparison of `T(A ×_Y B)` with
  `TA ×_{TY} TB`: the functor `v ↦ (TπA(v), Tσ(v), TπB(v))` (`wfpLift` of the tangent of the natural
  transformation `σ(a, ϕ, b) = ϕ` of Theorem 10.2.2) is an equivalence by two out of three, and
  `T(d ∘ e)` refines `Td ∘ Te` through it.
* **Universes.**  `T` lives on `EP(E⁻¹)` in universe `max u 1` (Chapter 8's `EP.tangent`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u v

/-! ### Tangents of compositions and identities -/

namespace EpFunctor

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {Obj'' Mor'' : Type u} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Z : EpGroupoid Obj'' Mor''}

/-- `T(G ∘ F) = TG ∘ TF` (Theorem 8.1.3's functoriality, for functors between unbundled
ep-groupoids). -/
theorem tangent_comp (G : EpFunctor Y Z) (F : EpFunctor X Y) :
    (G.comp F).tangent = G.tangent.comp F.tangent :=
  EpFunctor.ext (MPolyfold.tangentMap_comp G.isScSmoothMap_obj F.isScSmoothMap_obj)
    (MPolyfold.tangentMap_comp G.isScSmoothMap_mor F.isScSmoothMap_mor)

/-- `T1_X = 1_{TX}`. -/
theorem tangent_id : (EpFunctor.id X).tangent = EpFunctor.id X.tangentEpGroupoid :=
  EpFunctor.ext MPolyfold.tangentMap_id MPolyfold.tangentMap_id

end EpFunctor

namespace EpNatTrans

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

/-- A natural transformation `Φ → Ψ` read as one `Φ' → Ψ'` for `Φ = Φ'`, `Ψ = Ψ'`. -/
def castEq {Φ Ψ Φ' Ψ' : EpFunctor X Y} (τ : EpNatTrans Φ Ψ) (h₁ : Φ = Φ') (h₂ : Ψ = Ψ') :
    EpNatTrans Φ' Ψ' :=
  h₁ ▸ h₂ ▸ τ

@[simp] theorem castEq_app {Φ Ψ Φ' Ψ' : EpFunctor X Y} (τ : EpNatTrans Φ Ψ) (h₁ : Φ = Φ')
    (h₂ : Ψ = Ψ') : (τ.castEq h₁ h₂).app = τ.app := by
  subst h₁ h₂
  rfl

end EpNatTrans

namespace EPLocalization

open WeakFibredProduct

/-! ### Functors into a weak fibred product -/

section Lift

variable {ObjX MorX : Type u} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {ObjY MorY : Type u} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjZ MorZ : Type u} [TopologicalSpace ObjZ] [T2Space ObjZ] [ParacompactSpace ObjZ]
  [TopologicalSpace MorZ] [T2Space MorZ] [ParacompactSpace MorZ]
  {ObjC MorC : Type u} [TopologicalSpace ObjC] [T2Space ObjC] [ParacompactSpace ObjC]
  [TopologicalSpace MorC] [T2Space MorC] [ParacompactSpace MorC]
  {X : EpGroupoid ObjX MorX} {Y : EpGroupoid ObjY MorY} {Z : EpGroupoid ObjZ MorZ}
  {C : EpGroupoid ObjC MorC} {Φ : EpFunctor X Y} {G : EpFunctor Z Y}
  (P : EpFunctor C X) (Q : EpFunctor C Z) (τ : EpNatTrans (Φ.comp P) (G.comp Q))

/-- `c ↦ (P(c), τ(c), Q(c))`. -/
def wfpLiftObj (c : ObjC) : Obj Φ G :=
  Obj.mk Φ G (P.obj c) (τ.app c) (Q.obj c) (τ.src_app c) (τ.tgt_app c)

/-- `m ↦ (P(m), τ(s m), Q(m))`. -/
def wfpLiftMor (m : MorC) : Mor Φ G :=
  Mor.mk Φ G (P.mor m) (τ.app (C.src m)) (Q.mor m)
    ((τ.src_app _).trans (congrArg Φ.obj (P.src_mor m).symm))
    ((τ.tgt_app _).trans (congrArg G.obj (Q.src_mor m).symm))

variable {P Q τ}

theorem conj_wfpLiftMor (m : MorC) :
    conj Φ G (P.mor m) (τ.app (C.src m)) (Q.mor m) = τ.app (C.tgt m) := by
  have h₁ : Y.src (τ.app (C.src m)) = Φ.obj (X.src (P.mor m)) := (wfpLiftMor P Q τ m).src_φ
  have h₂ : Y.tgt (τ.app (C.src m)) = G.obj (Z.src (Q.mor m)) := (wfpLiftMor P Q τ m).tgt_φ
  refine GroupoidStr.comp_right_cancel (G := Y.toGroupoidStr) (φ := Φ.mor (P.mor m)) ?_ ?_ ?_
  · rw [src_conj h₁ h₂, Φ.tgt_mor]
  · rw [τ.src_app, Φ.tgt_mor, P.tgt_mor]
    rfl
  · rw [conj_comp_mor h₁ h₂]
    exact (τ.naturality m).symm

theorem src_wfpLiftMor (m : MorC) : src (wfpLiftMor P Q τ m) = wfpLiftObj P Q τ (C.src m) :=
  Obj.ext (P.src_mor m) rfl (Q.src_mor m)

theorem tgt_wfpLiftMor (m : MorC) : tgt (wfpLiftMor P Q τ m) = wfpLiftObj P Q τ (C.tgt m) :=
  Obj.ext (P.tgt_mor m) (conj_wfpLiftMor m) (Q.tgt_mor m)

variable (P Q τ)

/-- **The functor `C → X ×_Y Z` of `(P, Q, τ)`**, `τ : Φ ∘ P → G ∘ Q` (the universal property of
the weak fibred product, used for Theorem 11.1.1). -/
def wfpLift (h : Admissible Φ G) : EpFunctor C (epGroupoid Φ G h) where
  obj := wfpLiftObj P Q τ
  mor := wfpLiftMor P Q τ
  src_mor := src_wfpLiftMor
  tgt_mor := tgt_wfpLiftMor
  mor_comp m m' hc := by
    have hc : C.src m = C.tgt m' := hc
    have hc' : src (wfpLiftMor P Q τ m) = tgt (wfpLiftMor P Q τ m') := by
      rw [src_wfpLiftMor, tgt_wfpLiftMor, hc]
    change wfpLiftMor P Q τ (C.comp m m') = comp (wfpLiftMor P Q τ m) (wfpLiftMor P Q τ m')
    refine Mor.ext ?_ ?_ ?_
    · rw [h_comp hc']
      exact P.mor_comp _ _ hc
    · rw [φ_comp hc']
      change τ.app (C.src (C.comp m m')) = τ.app (C.src m')
      rw [C.src_comp _ _ hc]
    · rw [k_comp hc']
      exact Q.mor_comp _ _ hc
  mor_unit c := by
    refine Mor.ext (P.mor_unit c) ?_ (Q.mor_unit c)
    change τ.app (C.src (C.unit c)) = τ.app c
    rw [C.src_unit]
  isScSmoothMap_obj := isScSmoothOn_obj_of h P.isScSmoothMap_obj τ.isScSmoothMap_app
    Q.isScSmoothMap_obj
  isScSmoothMap_mor := isScSmoothOn_mor_of h P.isScSmoothMap_mor
    (τ.isScSmoothMap_app.comp C.isScSmoothMap_src) Q.isScSmoothMap_mor

theorem projLeft_comp_wfpLift (h : Admissible Φ G) :
    (projLeft Φ G h).comp (wfpLift P Q τ h) = P :=
  EpFunctor.ext rfl rfl

theorem projRight_comp_wfpLift (h : Admissible Φ G) :
    (projRight Φ G h).comp (wfpLift P Q τ h) = Q :=
  EpFunctor.ext rfl rfl

end Lift

/-! ### The tangent of a diagram -/

namespace Diagram

variable {X Y Z : EP.{max u 1}}

/-- **The tangent diagram** `TX ←TF TA →TΦ TY` of `d : X ←F A →Φ Y` (Theorem 10.1.7). -/
def tangent (d : Diagram X Y) : Diagram X.tangent Y.tangent :=
  ⟨d.A.tangent, d.F.tangent, EpFunctor.theorem_10_1_7 d.isEquivalence_F, d.Φ.tangent⟩

/-- A refinement `H : d' → d` gives the refinement `TH : Td' → Td` (2021 p. 522). -/
theorem IsRefinement.tangent {d d' : Diagram X Y} (h : d'.IsRefinement d) :
    d'.tangent.IsRefinement d.tangent := by
  obtain ⟨H, hH, ⟨σ⟩, ⟨τ⟩⟩ := h
  refine ⟨H.tangent, EpFunctor.theorem_10_1_7 hH, ⟨σ.tangent.castEq ?_ rfl⟩,
    ⟨τ.tangent.castEq ?_ rfl⟩⟩
  · exact EpFunctor.tangent_comp _ _
  · exact EpFunctor.tangent_comp _ _

theorem Equiv.tangent {d d' : Diagram X Y} (h : Equiv d d') : Equiv d.tangent d'.tangent := by
  obtain ⟨d'', h₁, h₂⟩ := h
  exact ⟨d''.tangent, h₁.tangent, h₂.tangent⟩

/-- `T1_X` refines `1_{TX}`. -/
theorem isRefinement_tangent_id (X : EP.{max u 1}) :
    (Diagram.id X).tangent.IsRefinement (Diagram.id X.tangent) := by
  refine ⟨EpFunctor.id _, EpFunctor.IsEquivalence.id _, .of_eq ?_, .of_eq ?_⟩ <;>
  · change EpFunctor.id _ = (EpFunctor.id X.X).tangent
    rw [EpFunctor.tangent_id]

/-- **`T(d ∘ e)` refines `Td ∘ Te`**, by the functor `T(A ×_Y B) → TA ×_{TY} TB`,
`v ↦ (TπA(v), Tσ(v), TπB(v))`, an equivalence by two out of three. -/
theorem isRefinement_tangent_comp (d : Diagram X Y) (e : Diagram Y Z) :
    (d.comp e).tangent.IsRefinement (d.tangent.comp e.tangent) := by
  have h := d.admissible e
  have h' : Admissible d.Φ.tangent e.F.tangent :=
    .of_isEquivalence_right (EpFunctor.theorem_10_1_7 e.isEquivalence_F)
  let πA := projLeft d.Φ e.F (d.admissible e)
  let πB := projRight d.Φ e.F (d.admissible e)
  let τ : EpNatTrans (d.Φ.tangent.comp πA.tangent) (e.F.tangent.comp πB.tangent) :=
    (natTrans d.Φ e.F (d.admissible e)).tangent.castEq (EpFunctor.tangent_comp _ _)
      (EpFunctor.tangent_comp _ _)
  let L := wfpLift πA.tangent πB.tangent τ h'
  have hL : L.IsEquivalence :=
    EpFunctor.IsEquivalence.of_comp_left
      (isEquivalence_projLeft (EpFunctor.theorem_10_1_7 e.isEquivalence_F) h')
      (by
        rw [projLeft_comp_wfpLift]
        exact EpFunctor.theorem_10_1_7 (isEquivalence_projLeft e.isEquivalence_F h))
  refine ⟨L, hL, .of_eq ?_, .of_eq ?_⟩
  · exact EpFunctor.ext
      (MPolyfold.tangentMap_comp d.F.isScSmoothMap_obj πA.isScSmoothMap_obj).symm
      (MPolyfold.tangentMap_comp d.F.isScSmoothMap_mor πA.isScSmoothMap_mor).symm
  · exact EpFunctor.ext
      (MPolyfold.tangentMap_comp e.Φ.isScSmoothMap_obj πB.isScSmoothMap_obj).symm
      (MPolyfold.tangentMap_comp e.Φ.isScSmoothMap_mor πB.isScSmoothMap_mor).symm

end Diagram

/-! ### Theorem 11.1.1 -/

namespace EPLoc

/-- **The tangent functor `T : EP(E⁻¹) → EP(E⁻¹)`** (2021 Theorem 11.1.1, p. 521), `X ↦ TX`,
`[d] ↦ [Td]`. -/
def tangentFunctor : EPLoc.{max u 1} ⥤ EPLoc.{max u 1} where
  obj X := of X.toEP.tangent
  map f := Quotient.map Diagram.tangent (fun _ _ h => Diagram.Equiv.tangent h) f
  map_id X := Quotient.sound (Diagram.isRefinement_tangent_id X.toEP).equiv
  map_comp f g := Quotient.inductionOn₂ f g fun d e =>
    Quotient.sound (Diagram.isRefinement_tangent_comp d e).equiv

@[simp] theorem tangentFunctor_obj (X : EP.{max u 1}) : tangentFunctor.obj (of X) = of X.tangent :=
  rfl

@[simp] theorem tangentFunctor_map_homMk {X Y : EP.{max u 1}} (d : Diagram X Y) :
    tangentFunctor.map (homMk d) = homMk d.tangent :=
  rfl

/-- `T` on `EP(E⁻¹)` extends `T` on `EP` (Theorem 8.1.3): `T(i(Φ)) = i(TΦ)`. -/
theorem tangentFunctor_map_localizationFunctor {X Y : EP.{max u 1}} (Φ : X ⟶ Y) :
    tangentFunctor.map (localizationFunctor.map Φ) =
      localizationFunctor.map (Polyfold.tangentFunctor.map Φ) := by
  refine homMk_eq_homMk_iff.2 (Diagram.IsRefinement.equiv ?_)
  refine ⟨EpFunctor.id _, EpFunctor.IsEquivalence.id _, .of_eq ?_, .of_eq (EpFunctor.ext rfl rfl)⟩
  change EpFunctor.id _ = (EpFunctor.id X.X).tangent
  rw [EpFunctor.tangent_id]

/-- **2021 Theorem 11.1.1, p. 521 (2017: Theorem 11.1, p. 375)**: the tangent functor induces a
functor `T : EP(E⁻¹) → EP(E⁻¹)` (`tangentFunctor`), `X ↦ TX` and
`[X ←F A →Φ Y] ↦ [TX ←TF TA →TΦ TY]`: refinements and equivalent diagrams go to refinements and
equivalent diagrams, `T` preserves identities and compositions, and it extends `T : EP → EP`. -/
theorem theorem_11_1_1 :
    (∀ X : EP.{max u 1}, tangentFunctor.obj (of X) = of X.tangent) ∧
      (∀ {X Y : EP.{max u 1}} (d : Diagram X Y), tangentFunctor.map (homMk d) = homMk d.tangent) ∧
      (∀ {X Y : EP.{max u 1}} {d d' : Diagram X Y}, d'.IsRefinement d →
        d'.tangent.IsRefinement d.tangent) ∧
      (∀ {X Y : EP.{max u 1}} {d d' : Diagram X Y}, Diagram.Equiv d d' →
        Diagram.Equiv d.tangent d'.tangent) ∧
      (∀ X : EPLoc.{max u 1}, tangentFunctor.map (𝟙 X) = 𝟙 (tangentFunctor.obj X)) ∧
      (∀ {X Y Z : EPLoc.{max u 1}} (f : X ⟶ Y) (g : Y ⟶ Z),
        tangentFunctor.map (f ≫ g) = tangentFunctor.map f ≫ tangentFunctor.map g) ∧
      (∀ {X Y : EP.{max u 1}} (Φ : X ⟶ Y), tangentFunctor.map (localizationFunctor.map Φ) =
        localizationFunctor.map (Polyfold.tangentFunctor.map Φ)) :=
  ⟨tangentFunctor_obj, tangentFunctor_map_homMk, fun h => h.tangent, fun h => h.tangent,
    tangentFunctor.map_id, tangentFunctor.map_comp, tangentFunctor_map_localizationFunctor⟩

/-- `T` maps generalized isomorphisms to generalized isomorphisms (with Theorem 10.3.10: if `F`, `Φ`
are equivalences, so are `TF`, `TΦ`). -/
theorem isGeneralizedIso_tangent {X Y : EPLoc.{max u 1}} {f : X ⟶ Y} (hf : IsGeneralizedIso f) :
    IsGeneralizedIso (tangentFunctor.map f) :=
  (isGeneralizedIso_iff_isIso _).2 <| by
    have := (isGeneralizedIso_iff_isIso f).1 hf
    infer_instance

/-! ### Proposition 11.1.2 -/

variable {X Y : EP.{u}}

/-- `d_{|Y|}(|d|(q)) = d_{|X|}(q)` for a diagram whose legs are equivalences. -/
theorem _root_.Polyfold.EPLocalization.Diagram.degIndexOrbit_orbitMap (d : Diagram X Y)
    (hΦ : d.Φ.IsEquivalence) (q : X.X.OrbitSpace) :
    Y.X.degIndexOrbit (d.orbitMap q) = X.X.degIndexOrbit q := by
  obtain ⟨r, rfl⟩ := d.isEquivalence_F.isHomeomorph_orbitMap.surjective q
  obtain ⟨a, rfl⟩ := d.A.X.surjective_π r
  rw [Diagram.orbitMap_orbitMap_F, GroupoidFunctor.orbitMap_π, GroupoidFunctor.orbitMap_π,
    EpGroupoid.degIndexOrbit_π, EpGroupoid.degIndexOrbit_π, hΦ.degIndex_obj,
    d.isEquivalence_F.degIndex_obj]

/-- A generalized isomorphism preserves the induced degeneracy index of the orbit spaces. -/
theorem degIndexOrbit_orbitMap {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (q : X.X.OrbitSpace) :
    Y.X.degIndexOrbit (orbitMap f q) = X.X.degIndexOrbit q := by
  obtain ⟨d, rfl, hΦ⟩ := exists_diagram_of_isGeneralizedIso hf
  exact d.degIndexOrbit_orbitMap hΦ q

/-- **2021 Proposition 11.1.2, p. 522 (2017: Proposition 11.1, p. 376)**: if `[d] : X → Y` is an
isomorphism of `EP(E⁻¹)` and `|[d]|(|x|) = |y|`, then `d_X(x₀) = d_Y(y₀)` for all `x₀ ∈ |x|`,
`y₀ ∈ |y|`, and `d_{|X|}(|x|) = d_{|Y|}(|y|)`. -/
theorem proposition_11_1_2 {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {x : X.Obj} {y : Y.Obj}
    (h : orbitMap f (X.X.π x) = Y.X.π y) :
    (∀ x₀ y₀, X.X.π x₀ = X.X.π x → Y.X.π y₀ = Y.X.π y →
        X.X.PObj.degIndex x₀ = Y.X.PObj.degIndex y₀) ∧
      X.X.degIndexOrbit (X.X.π x) = Y.X.degIndexOrbit (Y.X.π y) := by
  have key : X.X.degIndexOrbit (X.X.π x) = Y.X.degIndexOrbit (Y.X.π y) := by
    rw [← h, degIndexOrbit_orbitMap hf]
  refine ⟨fun x₀ y₀ hx hy => ?_, key⟩
  rw [← EpGroupoid.degIndexOrbit_π, ← EpGroupoid.degIndexOrbit_π, hx, hy, key]

end EPLoc

end EPLocalization

end Polyfold
