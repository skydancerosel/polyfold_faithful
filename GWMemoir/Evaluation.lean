import GWMemoir.CauchyRiemannFredholm
import Polyfold.Chapter16.FormsPullback

/-!
Hofer–Wysocki–Zehnder, *Applications of Polyfold Theory I: The Polyfolds of Gromov–Witten
Theory*, Memoirs AMS 248 (2017), **Theorem 1.12** (p. 9): the evaluation maps
`ev_i : Z_{A,g,m} → Q`, compared with the book (*Polyfold and Fredholm Theory*, Springer 2021):
Definition 2.3.4 (M-polyfolds), Definitions 16.1.1, 16.1.3 (polyfolds), Definition 16.1.8
(sc-smooth maps between polyfolds).

## The memoir, paraphrased

(Theorem 1.12) The integrand of `Ψ^Q_{A,g,m}` contains `ev_1^*α_1 ∧ … ∧ ev_m^*α_m`, the
`ev_i` evaluating a stable map `(S, j, M, D, u)` at its `i`-th marked point, into the closed
symplectic manifold `Q`; the `α_i` are de Rham forms on `Q`.

## What is formalized (namespace `GWMemoir`)

* `manifoldMPolyfold I M h`: a finite-dimensional manifold `M` without boundary (Mathlib, `C^∞`),
  read on `X ≃ₜ M`, as an M-polyfold with the constant sc-structure; its charts are the extended
  charts `e.extend I`, transitions `I.extendCoordChange` (`manifoldChart_compatible`).  Every point
  is on every level (`manifoldMPolyfold_levelSet`).
* `manifoldStructure`, `manifoldClass`: the polyfold of `M` (trivial ep-groupoid), effective.
* `isManifold_pi`: `Mᵐ` is a `C^∞` manifold for the product model (an instance not in Mathlib).
* `toTrivialScMap`: an sc-smooth map from the object M-polyfold of a polyfold structure `p`
  that is constant along morphisms gives an sc-smooth map `⟦p⟧ → M` of polyfolds.
* `evObj`, `evOrbit`: `ev = (u(z₁), …, u(z_m))`, constant on isomorphism classes
  (`evObj_src_eq_tgt`).  **`gwEv`**: `ev : Z → Qᵐ` as an sc-smooth map of polyfolds, from the
  named proposition `Evaluation_ScSmooth` (sc-smoothness of `o ↦ ev(Ψ(o))` on each uniformizer);
  `toFun_gwEv`: its continuous map is `ev`.

## Readings

* `Q` and `Qᵐ` enter on `ULift (Fin m → Q)`, in the universe of `Z`.
* The sc-smoothness of `ev ∘ Ψ` is stated, not derived from the construction of the
  uniformizers of §3: it rests on the marked points lying off the necks and on `H³ ⊂ C⁰` on
  the discs.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter
open scoped Manifold ContDiff

noncomputable section

namespace GWMemoir

open Polyfold

universe u

/-! ### Finite-dimensional manifolds as M-polyfolds -/

section ManifoldPolyfold

/-- A `C^∞` map between open subsets of finite-dimensional spaces is sc-smooth between the
retracts, for the constant sc-structures (Corollary 1.2.5 of the book, with `r = id`). -/
theorem isScSmoothRetractMap_const_of_contDiffOn {V V' : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V']
    [FiniteDimensional ℝ V'] {S : Set V} {S' : Set V'} (hS : IsOpen S) {g : V → V'}
    (hg : ContDiffOn ℝ ∞ g S) (hmaps : MapsTo g S S') :
    IsScSmoothRetractMap (ScBanach.const V) univ S (ScBanach.const V') univ S' g := by
  have hU : IsRelOpenInQuadrant (ScBanach.const V) univ S :=
    ⟨isPartialQuadrant_univ _, S, hS, (inter_univ _).symm⟩
  refine (isScSmoothRetractMap_iff_exists hU.isScRetract).2
    ⟨hmaps, ScRetraction.id hU, image_id _, ?_⟩
  exact IsScSmooth.of_contDiffOn_finiteDimensional (V := V') hU.isScDomain
    (f := g ∘ ScRetraction.id hU) hg

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {X : Type u} [TopologicalSpace X] (h : X ≃ₜ M)

/-- The local model `((e.extend I).target, F, F)` of a chart `e` of `M` (constant sc-structure). -/
def chartModel (I : ModelWithCorners ℝ F H) [I.Boundaryless] (e : OpenPartialHomeomorph M H) :
    LocalModel where
  E := ScBanach.const F
  C := univ
  O := (e.extend I).target
  isScRetract := IsRelOpenInQuadrant.isScRetract
    ⟨isPartialQuadrant_univ _, _, e.isOpen_extend_target, (inter_univ _).symm⟩

variable (I) in
/-- **The M-polyfold chart of a chart `e` of `M`**, read on `X` through `h : X ≃ₜ M`:
`x ↦ (e.extend I)(h x)`, onto `(e.extend I).target`. -/
def manifoldChart (e : OpenPartialHomeomorph M H) : MChart X where
  model := chartModel I e
  toPartialEquiv :=
    { toFun := fun x => e.extend I (h x)
      invFun := fun y => h.symm ((e.extend I).symm y)
      source := h ⁻¹' e.source
      target := (e.extend I).target
      map_source' := fun x hx => (e.extend I).map_source (by rwa [e.extend_source])
      map_target' := fun y hy => by
        change h (h.symm _) ∈ e.source
        rw [h.apply_symm_apply, ← e.extend_source (I := I)]
        exact (e.extend I).map_target hy
      left_inv' := fun x hx => by
        rw [e.extend_left_inv hx, h.symm_apply_apply]
      right_inv' := fun y hy => by
        change e.extend I (h (h.symm _)) = y
        rw [h.apply_symm_apply]
        exact (e.extend I).right_inv hy }
  isOpen_source := e.open_source.preimage h.continuous
  target_eq := rfl
  continuousOn_toFun := (e.continuousOn_extend (I := I)).comp h.continuous.continuousOn
    fun x hx => by rwa [e.extend_source]
  continuousOn_invFun := h.symm.continuous.comp_continuousOn (e.continuousOn_extend_symm (I := I))

@[simp] lemma manifoldChart_apply (e : OpenPartialHomeomorph M H) (x : X) :
    manifoldChart I h e x = e.extend I (h x) := rfl

@[simp] lemma manifoldChart_symm_apply (e : OpenPartialHomeomorph M H) (y : F) :
    (manifoldChart I h e).symm y = h.symm ((e.extend I).symm y) := rfl

lemma manifoldChart_source (e : OpenPartialHomeomorph M H) :
    (manifoldChart I h e).source = h ⁻¹' e.source := rfl

lemma manifoldChart_model_O (e : OpenPartialHomeomorph M H) :
    (manifoldChart I h e).model.O = (e.extend I).target := rfl

/-- The overlap of two manifold charts lies in the source of the extended coordinate change. -/
lemma manifoldChart_overlap_subset (e e' : OpenPartialHomeomorph M H) :
    (manifoldChart I h e).overlap (manifoldChart I h e') ⊆ (I.extendCoordChange e e').source := by
  rintro _ ⟨x, hx, rfl⟩
  rw [← OpenPartialHomeomorph.extend_image_source_inter]
  exact ⟨h x, hx, rfl⟩

lemma isOpen_manifoldChart_overlap (e e' : OpenPartialHomeomorph M H) :
    IsOpen ((manifoldChart I h e).overlap (manifoldChart I h e')) := by
  obtain ⟨W, hW, hWeq⟩ := (manifoldChart I h e).exists_isOpen_image_eq
    (s := (manifoldChart I h e).source ∩ (manifoldChart I h e').source) inter_subset_left
    ((manifoldChart I h e).isOpen_source.inter (manifoldChart I h e').isOpen_source)
  change IsOpen (_ '' _)
  rw [hWeq]
  exact (e.isOpen_extend_target (I := I)).inter hW

/-- The transition map of two manifold charts is the extended coordinate change. -/
lemma manifoldChart_transition (e e' : OpenPartialHomeomorph M H) :
    (manifoldChart I h e).transition (manifoldChart I h e') = I.extendCoordChange e e' := by
  funext y
  change e'.extend I (h (h.symm _)) = _
  rw [h.apply_symm_apply]
  rfl

variable [IsManifold I ∞ M]

/-- **Two charts of the maximal atlas of `M` give compatible M-polyfold charts**: the transition
maps are the extended coordinate changes, `C^∞` (Mathlib's `contDiffOn_extendCoordChange`). -/
theorem manifoldChart_compatible {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) (he' : e' ∈ IsManifold.maximalAtlas I ∞ M) :
    (manifoldChart I h e).Compatible (manifoldChart I h e') := by
  have key : ∀ {e e' : OpenPartialHomeomorph M H}, e ∈ IsManifold.maximalAtlas I ∞ M →
      e' ∈ IsManifold.maximalAtlas I ∞ M →
      IsScSmoothRetractMap (manifoldChart I h e).model.E (manifoldChart I h e).model.C
        ((manifoldChart I h e).overlap (manifoldChart I h e')) (manifoldChart I h e').model.E
        (manifoldChart I h e').model.C ((manifoldChart I h e').overlap (manifoldChart I h e))
        ((manifoldChart I h e).transition (manifoldChart I h e')) := by
    intro e e' he he'
    refine isScSmoothRetractMap_const_of_contDiffOn (V := F) (V' := F)
      (isOpen_manifoldChart_overlap h e e') ?_ (MChart.transition_mapsTo _ _)
    rw [manifoldChart_transition]
    exact (I.contDiffOn_extendCoordChange he he').mono (manifoldChart_overlap_subset h e e')
  exact ⟨key he he', key he' he⟩

variable [T2Space X] [ParacompactSpace X]

variable (I M) in
/-- **A finite-dimensional manifold without boundary as an M-polyfold** (the book's remark that
finite-dimensional manifolds are M-polyfolds, Definition 2.3.4 with the constant sc-structure):
on `X ≃ₜ M`, the charts `(e.extend I) ∘ h` of the atlas of `M`, modelled on the constant
sc-structure of `F`. -/
def manifoldMPolyfold : MPolyfold X where
  atlas :=
    { charts := (manifoldChart I h) '' atlas H M
      compatible := by
        rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
        exact manifoldChart_compatible h (IsManifold.subset_maximalAtlas he)
          (IsManifold.subset_maximalAtlas he')
      cover := fun x => ⟨_, ⟨chartAt H (h x), chart_mem_atlas H (h x), rfl⟩,
        show h x ∈ (chartAt H (h x)).source from mem_chart_source H (h x)⟩ }

/-- Every chart of the maximal atlas of `M` is a chart of the M-polyfold. -/
theorem isChart_manifoldChart {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) :
    (manifoldMPolyfold I M h).IsChart (manifoldChart I h e) := by
  rintro _ ⟨e', he', rfl⟩
  exact manifoldChart_compatible h he (IsManifold.subset_maximalAtlas he')

theorem isChart_manifoldChart_chartAt (x : X) :
    (manifoldMPolyfold I M h).IsChart (manifoldChart I h (chartAt H (h x))) :=
  isChart_manifoldChart h (IsManifold.subset_maximalAtlas (chart_mem_atlas H (h x)))

lemma mem_manifoldChart_chartAt_source (x : X) :
    x ∈ (manifoldChart I h (chartAt H (h x))).source :=
  mem_chart_source H (h x)

/-- **Every point is on every level** (the constant sc-structure). -/
theorem manifoldMPolyfold_levelSet (m : ℕ) : (manifoldMPolyfold I M h).levelSet m = univ := by
  refine eq_univ_of_forall fun x => ?_
  rw [(manifoldMPolyfold I M h).mem_levelSet_iff (isChart_manifoldChart_chartAt h x)
    (mem_manifoldChart_chartAt_source h x)]
  exact ⟨manifoldChart I h (chartAt H (h x)) x, ScBanach.const_toBase _ m _⟩

theorem manifoldMPolyfold_smoothSet : (manifoldMPolyfold I M h).smoothSet = univ := by
  simp [MPolyfold.smoothSet, manifoldMPolyfold_levelSet]

variable (I M) in
/-- **The polyfold structure of a manifold** (Definition 16.1.1): the trivial ep-groupoid of
`manifoldMPolyfold` (paracompact orbit space, (ZHOU)), with `|X| ≃ X`. -/
def manifoldStructure : PolyfoldStructure X :=
  ⟨EP.mk X X (EpGroupoid.trivial (manifoldMPolyfold I M h)),
    EpGroupoid.hasParacompactOrbitSpace_trivial _, EpGroupoid.isZhou_trivial _,
    EpGroupoid.trivialOrbitHomeomorph _⟩

variable (I M) in
/-- **A finite-dimensional manifold as a polyfold** (Definition 16.1.3): the class of
`manifoldStructure`, with the constant sc-scale and the trivial groupoid. -/
def manifoldClass : PolyfoldClass X := ⟦manifoldStructure I M h⟧

/-- The polyfold of a manifold is effective (trivial isotropy). -/
theorem manifoldClass_isEffective : (manifoldClass I M h).IsEffective :=
  ⟨_, rfl, EpGroupoid.isEffective_trivial _⟩

end ManifoldPolyfold

/-! ### The product `Q^m` -/

section Pi

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {m : ℕ}

/-- The product model `Iᵐ` has no boundary. -/
instance boundaryless_pi : (ModelWithCorners.pi fun _ : Fin m => I).Boundaryless :=
  ⟨eq_univ_of_forall fun y => ⟨fun i => I.symm (y i), funext fun i =>
    I.right_inv (by rw [ModelWithCorners.Boundaryless.range_eq_univ]; exact mem_univ _)⟩⟩

variable [IsManifold I ∞ M]

/-- **`Mᵐ` is a smooth manifold** for the product model `Iᵐ` (the chart changes are the
products of the chart changes of `M`; Mathlib has the charted space `Π i, M` but not this
instance). -/
instance isManifold_pi : IsManifold (ModelWithCorners.pi fun _ : Fin m => I) ∞ (Fin m → M) := by
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
  refine contDiffOn_pi' fun i => ?_
  have hc := (HasGroupoid.compatible (G := contDiffGroupoid ∞ I) (he i (mem_univ i))
    (he' i (mem_univ i))).1
  refine (hc.comp (contDiff_apply ℝ F i).contDiffOn ?_).congr fun y _ => rfl
  rintro y ⟨hy, -⟩
  refine ⟨⟨hy.1 i (mem_univ i), hy.2 i (mem_univ i)⟩, ?_⟩
  rw [ModelWithCorners.Boundaryless.range_eq_univ]
  exact mem_univ _

end Pi

/-! ### Sc-smooth maps into the polyfold of a manifold -/

section ToTrivial

open EPLocalization EPLocalization.EPLoc CategoryTheory

/-- The orbit map of the generalized map of an sc-smooth functor: `|[Φ]|(|x|) = |Φ(x)|`. -/
theorem orbitMap_localizationFunctor_map_π {A B : EP.{u}} (Φ : A ⟶ B) (x : A.Obj) :
    orbitMap (localizationFunctor.map Φ) (A.X.π x) = B.X.π (Φ.obj x) := by
  have h := (Diagram.ofFunctor Φ).orbitMap_orbitMap_F (A.X.π x)
  change (Diagram.ofFunctor Φ).orbitMap ((EpFunctor.id A.X).orbitMap (A.X.π x)) =
    Φ.orbitMap (A.X.π x) at h
  rw [EpFunctor.orbitMap_id, GroupoidFunctor.orbitMap_π] at h
  exact h

variable {Z : Type u} [TopologicalSpace Z] (p : PolyfoldStructure Z)
  {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- **The sc-smooth functor `X → (trivial ep-groupoid of P)`** of an sc-smooth map `f` on objects
that is constant along morphisms: `φ ↦ f(s(φ))` on morphisms. -/
def toTrivialFunctor {f : p.X.Obj → X} (hf : p.X.X.PObj.IsScSmoothMap P f)
    (hinv : ∀ φ : p.X.Mor, f (p.X.X.src φ) = f (p.X.X.tgt φ)) :
    EpFunctor p.X.X (EpGroupoid.trivial P) where
  obj := f
  mor φ := f (p.X.X.src φ)
  src_mor _ := rfl
  tgt_mor φ := hinv φ
  mor_comp φ ψ hφψ := by
    change f (p.X.X.src (p.X.X.comp φ ψ)) = f (p.X.X.src φ)
    rw [p.X.X.src_comp φ ψ hφψ, hφψ, hinv ψ]
  mor_unit x := by
    change f (p.X.X.src (p.X.X.unit x)) = f x
    rw [p.X.X.src_unit]
  isScSmoothMap_obj := hf
  isScSmoothMap_mor := hf.comp p.X.X.isScSmoothMap_src

/-- The structure `(trivial ep-groupoid of P, id)` on `X`. -/
def trivialStructure : PolyfoldStructure X :=
  ⟨EP.mk X X (EpGroupoid.trivial P), EpGroupoid.hasParacompactOrbitSpace_trivial _,
    EpGroupoid.isZhou_trivial _, EpGroupoid.trivialOrbitHomeomorph _⟩

/-- **The morphism `(F, [Φ]) : (X, β) → (trivial, id)` of `PS`** for the functor `Φ` of `f`,
when `F ∘ β ∘ π = f`. -/
def toTrivialPSHom {f : p.X.Obj → X} (hf : p.X.X.PObj.IsScSmoothMap P f)
    (hinv : ∀ φ : p.X.Mor, f (p.X.X.src φ) = f (p.X.X.tgt φ)) {F : Z → X}
    (hF : ∀ x, F (p.β (p.X.X.π x)) = f x) : PSHom p (trivialStructure P) where
  f := F
  gen := localizationFunctor.map (X := p.X) (Y := EP.mk X X (EpGroupoid.trivial P))
    (toTrivialFunctor p P hf hinv)
  comm := by
    funext z
    obtain ⟨x, rfl⟩ := p.X.X.surjective_π z
    have e := orbitMap_localizationFunctor_map_π (B := EP.mk X X (EpGroupoid.trivial P))
      (toTrivialFunctor p P hf hinv) x
    simp only [Function.comp_apply]
    rw [hF]
    erw [e]
    rfl

/-- **The sc-smooth map `[(F, [Φ])] : (Z, ⟦p⟧) → (X, ⟦trivial⟧)`** (Definition 16.1.8). -/
def toTrivialScMap {f : p.X.Obj → X} (hf : p.X.X.PObj.IsScSmoothMap P f)
    (hinv : ∀ φ : p.X.Mor, f (p.X.X.src φ) = f (p.X.X.tgt φ)) {F : Z → X}
    (hF : ∀ x, F (p.β (p.X.X.π x)) = f x) {c : PolyfoldClass Z}
    (hp : (⟦p⟧ : PolyfoldClass Z) = c) :
    PolyfoldClass.ScMap c (⟦trivialStructure P⟧ : PolyfoldClass X) :=
  PolyfoldClass.ScMap.mk p hp _ rfl (toTrivialPSHom p P hf hinv hF)

/-- Its continuous map (Remark 16.1.9) is `F`. -/
theorem toFun_toTrivialScMap {f : p.X.Obj → X} (hf : p.X.X.PObj.IsScSmoothMap P f)
    (hinv : ∀ φ : p.X.Mor, f (p.X.X.src φ) = f (p.X.X.tgt φ)) {F : Z → X}
    (hF : ∀ x, F (p.β (p.X.X.π x)) = f x) {c : PolyfoldClass Z}
    (hp : (⟦p⟧ : PolyfoldClass Z) = c) :
    (toTrivialScMap p P hf hinv hF hp).toFun = F := rfl

end ToTrivial

/-! ### The evaluation maps `ev_i : Z → Q` -/

section GW

open GroupoidalCategory GroupoidalCategory.BasicConstruction
  GCT.VectorBundle.StrongPolyfoldBundleConstruction

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  {om : SymplecticForm E Q} {m k : ℕ} {δ : ℝ}

variable (E m) in
/-- The model `𝓘(ℝ, E)ᵐ` of `Qᵐ`. -/
abbrev powModel : ModelWithCorners ℝ (Fin m → E) (ModelPi fun _ : Fin m => E) :=
  ModelWithCorners.pi fun _ : Fin m => 𝓘(ℝ, E)

variable [T2Space Q] [CompactSpace Q]

variable (E Q m) in
/-- **`Qᵐ` as an M-polyfold**, on `ULift (Fin m → Q)` (the universe of `Z`). -/
abbrev powMPolyfold : MPolyfold (ULift.{1} (Fin m → Q)) :=
  manifoldMPolyfold (powModel E m) (Fin m → Q) Homeomorph.ulift

variable (E Q m) in
/-- **`Qᵐ` as a polyfold** (constant sc-scale, trivial groupoid). -/
abbrev powClass : PolyfoldClass (ULift.{1} (Fin m → Q)) :=
  manifoldClass (powModel E m) (Fin m → Q) Homeomorph.ulift

variable {C : GroupoidalCategory.{1}}

/-- **The evaluation at the marked points** (memoir p. 9): `ev(α) = (u(z₁), …, u(z_m))` for the
stable map `α = L(a) = (S, j, M, D, u)`, `M = {z₁, …, z_m}`. -/
def evObj (L : StableMapLabel om m k δ C) (a : C.Obj) : Fin m → Q :=
  fun i => (L.obj a).u ((L.obj a).dom.marked i)

/-- `ev` is constant on isomorphism classes: an isomorphism `φ` of stable maps preserves the
marked points and `u' ∘ φ = u`. -/
theorem evObj_src_eq_tgt (L : StableMapLabel om m k δ C) (φ : C.Mor) :
    evObj L (C.toGroupoidStr.src φ) = evObj L (C.toGroupoidStr.tgt φ) := by
  funext i
  have h := (L.iso φ).comm ((L.obj (C.toGroupoidStr.src φ)).dom.marked i)
  rw [(L.iso φ).φ.marked i] at h
  exact h.symm

/-- **`ev : Z → Qᵐ`** on the orbit space. -/
def evOrbit (L : StableMapLabel om m k δ C) : C.OrbitSpace → ULift.{1} (Fin m → Q) :=
  Quotient.lift (fun a => ULift.up (evObj L a)) (by
    rintro _ _ ⟨φ, rfl, rfl⟩
    rw [evObj_src_eq_tgt])

@[simp] theorem evOrbit_π (L : StableMapLabel om m k δ C) (a : C.Obj) :
    evOrbit L (C.toGroupoidStr.π a) = ULift.up (evObj L a) := rfl

variable {U : C.UniformizerConstruction} {CS : CSPred U}
  {h310 : U.HasClassUniformizers} {H : Theorem_3_13 U CS} {hCS : CSClosed U CS}
  {hPF : PointFinite U}
  {h322 : Theorem_3_22 U (gwTransitionData H hCS hPF)}
  {h16 : Theorem_1_6_sc U (gwTransitionData H hCS hPF) h310}

variable (E Q h310 H hCS hPF h322 h16) in
/-- **The sc-smoothness of the evaluation maps** (memoir p. 9; named): on the parameter
M-polyfold `O` of every uniformizer `Ψ` of `Z`, `o ↦ ev(Ψ(o))` is sc-smooth into `Qᵐ`.  The
marked points lie off the necks, so `ev ∘ Ψ` evaluates the `H³`-maps of §3.1 at points of the
discs, where `H³ ⊂ C⁰`. -/
def Evaluation_ScSmooth (L : StableMapLabel om m k δ C) : Prop :=
  ∀ Ψ : (gwPolyfoldConstruction h310 H hCS hPF h322 h16).Unif,
    Ψ.1.P.IsScSmoothMap (powMPolyfold E Q m) fun o => ULift.up (evObj L (Ψ.1.obj o))

variable {hTF : ∀ (α : C.Obj), ∀ Ψ ∈ U.F α, ∀ y : Ψ.P.SmoothLevel, IsTangentFaithfulAt Ψ y}
  {hLF : ∀ (α : C.Obj), ∀ Ψ ∈ U.F α, IsLocallyFaithful Ψ}
  {V : (gwGCT h310 H hCS hPF h322 h16).VectorBundle}
  {Fb : V.StrongBundleUniformizerConstruction (gwPolyfoldConstruction h310 H hCS hPF h322 h16)}
  {h339 : Proposition_3_39 Fb}

/-- The representative `(X_Ψ, |Γ_Ψ|)` of the polyfold `Z` of `gwBundle` (Theorem 17.1.26). -/
abbrev gwRep (hTF : ∀ (α : C.Obj), ∀ Ψ ∈ U.F α, ∀ y : Ψ.P.SmoothLevel, IsTangentFaithfulAt Ψ y)
    (c : (ofProposition_3_39 Fb h339).BundleCoveringFamily) :
    PolyfoldStructure (gwGCT h310 H hCS hPF h322 h16).toGroupoidStr.OrbitSpace :=
  (gwPolyfoldConstruction h310 H hCS hPF h322 h16).modelPolyfoldStructure c.base
    ((gwZhou hTF).model c.base)

theorem gwRep_mem (c : (ofProposition_3_39 Fb h339).BundleCoveringFamily) :
    (⟦gwRep hTF c⟧ : PolyfoldClass (gwGCT h310 H hCS hPF h322 h16).toGroupoidStr.OrbitSpace) =
      (gwBundle hTF hLF Fb h339 c).polyfold :=
  ((gwPolyfoldConstruction h310 H hCS hPF h322 h16).polyfoldClass_eq (gwZhou hTF) c.base).trans
    (polyfold_bundleOf _ _ _ c).symm

variable {L : StableMapLabel om m k δ C}

/-- **`ev = (ev₁, …, ev_m) : Z → Qᵐ` as an sc-smooth map of polyfolds** (Definition 16.1.8), from
the named `Evaluation_ScSmooth`: the class of `(ev, [Φ])` with `Φ : X_Ψ → (trivial ep-groupoid
of Qᵐ)`, `Φ(q_λ) = ev(Ψ_λ(q_λ))`. -/
def gwEv (hev : Evaluation_ScSmooth E Q h310 H hCS hPF h322 h16 L)
    (c : (ofProposition_3_39 Fb h339).BundleCoveringFamily) :
    PolyfoldClass.ScMap (gwBundle hTF hLF Fb h339 c).polyfold (powClass E Q m) :=
  toTrivialScMap (gwRep hTF c) (powMPolyfold E Q m)
    (f := fun x => ULift.up (evObj L
      ((gwPolyfoldConstruction h310 H hCS hPF h322 h16).modelObjMap c.base.Ψ x)))
    ((MPolyfold.isScSmoothMap_sigma_iff _).2 fun _ => hev _)
    (fun φ => congrArg ULift.up
      ((congrArg (evObj L)
        (((gwPolyfoldConstruction h310 H hCS hPF h322 h16).modelFunctor c.base.Ψ).src_mor
          φ).symm).trans
      ((evObj_src_eq_tgt L _).trans (congrArg (evObj L)
        (((gwPolyfoldConstruction h310 H hCS hPF h322 h16).modelFunctor c.base.Ψ).tgt_mor φ)))))
    (F := evOrbit L) (fun _ => rfl) (gwRep_mem c)

/-- The continuous map of `gwEv` (Remark 16.1.9) is `ev` on classes of stable maps. -/
theorem toFun_gwEv (hev : Evaluation_ScSmooth E Q h310 H hCS hPF h322 h16 L)
    (c : (ofProposition_3_39 Fb h339).BundleCoveringFamily) :
    (gwEv (hTF := hTF) (hLF := hLF) hev c).toFun = evOrbit L :=
  toFun_toTrivialScMap _ _ _ _ _ _

end GW

end GWMemoir
