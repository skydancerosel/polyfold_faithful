import Polyfold.Chapter18.SectionFunctors
import Polyfold.Chapter17.PolyfoldLevels

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.1 "Basic Concepts", p. 844: **Definition 18.1.1** (sc-Fredholm section functor) and
**Remark 18.1.2** (a), (b), (c), and their transfer to the strong bundle model `W_Ψ̄ → X_Ψ`.
Numbers and pages are the 2021 text's.

# sc-Fredholm section functors

## The text, paraphrased

(D18.1.1) A section functor `f` of `P : E → C` is sc-Fredholm if for every object `α` and every
`Ψ̄ ∈ F̄(α)` covering `Ψ`, the representative `f_Ψ̄ : O → K` is sc-Fredholm (Definition 3.1.16).
(R18.1.2 (a)) If `Ψ̄` is a covering family (the underlying `Ψ` covers `C`) and all `f_Ψ̄`,
`Ψ̄ ∈ Ψ̄`, are sc-Fredholm, then `f_Ψ̄` is sc-Fredholm for every `α` and `Ψ̄ ∈ F̄(α)` ("an easy
exercise"); so the property is checkable with a covering family, and the pull-back `f^Ψ̄_Ψ` of `f`
by `Γ̄_Ψ̄ : W_Ψ̄ → E` is an sc-Fredholm section of a strong bundle over an ep-groupoid if and only
if `f` is sc-Fredholm.  (b) An sc-Fredholm section functor is regularizing: `α ∈ C_m` and
`f(α) ∈ E_{m,m+1}` imply `α ∈ C_{m+1}`.  (c) An equivalent definition: `f` regularizing, sc-smooth
(checkable by a covering family), and for every smooth `z ∈ |C|` there are `α` with `|α| = z`,
`Ψ̄ ∈ F̄(α)` with `Ψ(q̄) = α`, such that `(f_Ψ̄, q̄)` is an sc-Fredholm germ (Definition 3.1.11).

## What is formalized

* Sections of disjoint unions (`StrongBundle.sigmaSection`): `isScSmoothSection_sigma_iff`,
  `isScFredholmGerm_sigma_iff`, `isScFredholmSection_sigma_iff`,
  `isScFredholmSectionTame_sigma_iff` (a section of `⊔ K_λ → ⊔ O_λ` is sc-smooth / sc-Fredholm /
  tame sc-Fredholm iff every piece is), through `isStrongBundleIsoOn_sigmaMk` (the inclusion of a
  piece is a strong bundle isomorphism onto its image) and Part I's `isScFredholmSection_of_forall`.
* `IsScFredholmSectionFunctor` (**Definition 18.1.1**), `IsScSmoothSectionFunctor`,
  `IsScFredholmSectionFunctorTame` (the tame form, Definition 3.6.5 in every representative),
  `IsRegularizing`.
* `isScFredholmSectionFunctor_model_iff` and its smooth and tame forms: in a model, `f^Ψ̄_Ψ` is an
  sc-Fredholm section functor (Definition 8.3.4) iff every `f_{Ψ̄_λ}` is sc-Fredholm.
* `remark_18_1_2_a` (**the easy exercise**: a covering family suffices), `_smooth`, `_tame`,
  through `isScFredholmSection_of_covering` (and `isScSmoothSection_of_covering`,
  `isScFredholmSectionTame_of_covering`): in the model of `Ψ̄ ⊔ {Ψ̄'}` (`adjoin`,
  `equivalences_adjoin`) the section `f^{Ψ̄ ⊔ Ψ̄'}` is the push-forward of `f^Ψ̄` along the strong
  bundle equivalence `W_Ψ̄ → W_{Ψ̄ ⊔ Ψ̄'}` (`modelSection_adjoin`), hence sc-Fredholm by
  Theorem 10.4.5, and so is its piece `f_Ψ̄'`;
  `remark_18_1_2_a_model` (`f^Ψ̄_Ψ` sc-Fredholm iff `f` is), `isScFredholm_model_iff_model`
  (independence of the covering family).
* `remark_18_1_2_b` (regularizing, in the representatives and in the levels `C_m` of p. 765).
* `remark_18_1_2_c` (**the equivalent definition**): `f` is sc-Fredholm iff it is sc-smooth,
  regularizing, and has an sc-Fredholm germ in one representative over every smooth point of `|C|`.
  The germ is moved from `Ψ̄₀` at `q₀` to any `Ψ̄'` at `q'` with `Ψ₀(q₀) ≅ Ψ'(q')` through the model
  of `{Ψ̄₀, Ψ̄'}`: the action of the morphism `(q₀, φ, q')` is a local strong bundle isomorphism
  along which `f^Ψ̄` is its own pull-back (`exists_localIso_mor`, Chapter 10); this is
  `isScFredholmGerm_of_isomorphic`, with `HasFredholmGerms` (the germ condition),
  `isSmoothObj_obj` and `isScFredholmSectionFunctor_of_germs` (the direction "⇐").

## Readings

* "Covering family `Ψ̄`" is read as in `BundleModel.lean`: a `BundleCoveringFamily` (the base
  family covers `|C|`).
* (b) "`α ∈ C_m`" is `S.HasRegularity m α` (p. 765), and "`f(α) ∈ E_{m,m+1}`" is read in a strong
  bundle uniformizer at `α`: `f_Ψ̄(q) ∈ K_{m,m+1}` for `Ψ(q) = α`.
* (c) For the direction "sc-Fredholm ⇒ germ form" an object over `z` with `F̄(α) ≠ ∅` is needed;
  we use the standing reading `F̄(α) ≠ ∅` for every `α` (`HasStrongBundleUniformizers`), the bundle
  form of the reading `F(α) ≠ ∅` of Chapter 17.  The converse holds without it.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u v

/-! ### Sections of disjoint unions of strong bundles -/

section Sigma

variable {ι : Type*} {X : ι → Type u} [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
  [∀ i, ParacompactSpace (X i)] {PX : ∀ i, MPolyfold (X i)}
  {Y : ι → Type v} [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)]
  [∀ i, ParacompactSpace (Y i)] {p : ∀ i, Y i → X i}
  [∀ i x, AddCommGroup (p i ⁻¹' {x})] [∀ i x, Module ℝ (p i ⁻¹' {x})]
  (B : ∀ i, StrongBundle (PX i) (p i))

namespace StrongBundle

/-- The section `(i, x) ↦ (i, g_i(x))` of `⊔ K_λ → ⊔ O_λ`. -/
def sigmaSection (g : ∀ i, X i → Y i) (x : Σ i, X i) : Σ i, Y i := ⟨x.1, g x.1 x.2⟩

variable {B} in
theorem isSection_sigmaSection {g : ∀ i, X i → Y i} (hg : ∀ i, IsSection (p i) (g i)) :
    IsSection (sigmaBundleProj p) (sigmaSection g) := by
  rintro ⟨i, x⟩
  change (⟨i, p i (g i x)⟩ : Σ i, X i) = ⟨i, x⟩
  rw [hg i x]

/-- **The inclusion of a piece is a strong bundle isomorphism onto its image**:
`K_i → (⊔ K_λ)|range(mk i)` over `O_i → range(mk i)`. -/
theorem isStrongBundleIsoOn_sigmaMk (i : ι) (x₀ : X i) :
    (B i).IsStrongBundleIsoOn (StrongBundle.sigma B) (isStrongBundleMap_sigmaMk B i) univ
      (range (Sigma.mk i)) := by
  have y₀ : Y i := (fiberZero (p i) x₀)
  refine ⟨⟨_, MPolyfold.isScDiffeoOn_sigmaMk PX i x₀⟩, ?_, ?_⟩
  · have hs : sigmaBundleProj p ⁻¹' range (Sigma.mk i) = range (Sigma.mk i) := by
      ext ⟨j, y⟩
      constructor
      · rintro ⟨x, hx⟩
        obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.1 hx
        exact ⟨y, rfl⟩
      · rintro ⟨y', hy'⟩
        obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 hy'
        exact ⟨_, rfl⟩
    rw [sigma_toMPolyfold0, preimage_univ, hs]
    exact ⟨_, MPolyfold.isScDiffeoOn_sigmaMk (fun i => (B i).toMPolyfold0) i y₀⟩
  · set u₀ : (B i).One :=
      (B i).oneMk (fiberZero (p i) x₀) ((B i).fiberZero_mem_oneSet _)
    have h1 := MPolyfold.isScDiffeoOn_sigmaMk (fun i => (B i).toMPolyfold1) i u₀
    have h2 := ((isScDiffeoOn_sigmaOneEquiv B).restrict_preimage
      (isOpen_range_sigmaMk (σ := fun i => (B i).One) (i := i))).symm
    have hs : (sigmaBundleProj p ∘ (StrongBundle.sigma B).oneVal) ⁻¹' range (Sigma.mk i) =
        sigmaOneEquiv B ⁻¹' range (Sigma.mk i) := by
      have := sigmaOneEquiv_preimage_image B (i := i) univ
      rw [preimage_univ, image_univ, image_univ] at this
      exact this.symm
    rw [preimage_univ, hs]
    refine ⟨_, (h2.comp h1).congr fun u _ => ?_⟩
    apply (StrongBundle.sigma B).oneVal_injective
    rfl

/-- `isStrongBundleIsoOn_sigmaMk` as a `LocalIso` (`ϕ = Φ = Sigma.mk i`). -/
def sigmaMkLocalIso (i : ι) (x₀ : X i) :
    LocalIso (B i) (StrongBundle.sigma B) univ (range (Sigma.mk i)) :=
  (isStrongBundleIsoOn_sigmaMk B i x₀).toLocalIso

@[simp] theorem sigmaMkLocalIso_ϕ (i : ι) (x₀ : X i) :
    (sigmaMkLocalIso B i x₀).ϕ = Sigma.mk i := rfl

@[simp] theorem sigmaMkLocalIso_Φ (i : ι) (x₀ : X i) :
    (sigmaMkLocalIso B i x₀).Φ = Sigma.mk i := rfl

theorem sigmaMkLocalIso_Ψ_mk (i : ι) (x₀ : X i) (y : Y i) :
    (sigmaMkLocalIso B i x₀).Ψ ⟨i, y⟩ = y :=
  (sigmaMkLocalIso B i x₀).zero.left_inv y (mem_univ _)

theorem sigmaMkLocalIso_g_mk (i : ι) (x₀ : X i) (x : X i) :
    (sigmaMkLocalIso B i x₀).g ⟨i, x⟩ = x :=
  (sigmaMkLocalIso B i x₀).base.left_inv x (mem_univ _)

/-- **Sc-smooth sections of a disjoint union** are the families of sc-smooth sections. -/
theorem isScSmoothSection_sigma_iff (g : ∀ i, X i → Y i) :
    (StrongBundle.sigma B).IsScSmoothSection (sigmaSection g) ↔
      ∀ i, (B i).IsScSmoothSection (g i) := by
  constructor
  · intro h i
    refine ⟨fun x => sigma_mk_injective (h.1 ⟨i, x⟩), ?_⟩
    have := h.2
    rw [sigma_toMPolyfold0, MPolyfold.isScSmoothMap_sigma_iff] at this
    exact (MPolyfold.isScSmoothMap_sigmaMk_comp_iff (fun i => (B i).toMPolyfold0)
      (i := i)).1 (this i)
  · intro h
    refine ⟨isSection_sigmaSection fun i => (h i).1, ?_⟩
    rw [sigma_toMPolyfold0, MPolyfold.isScSmoothMap_sigma_iff]
    exact fun i => (MPolyfold.isScSmoothMap_sigmaMk_comp_iff (fun i => (B i).toMPolyfold0)
      (i := i)).2 (h i).2

/-- On the piece `range (mk i)`, `sigmaSection g` is `g i` transported by the inverse of
`sigmaMkLocalIso`. -/
theorem eqOn_sigmaSection (g : ∀ i, X i → Y i) (i : ι) (x : X i) :
    EqOn (sigmaSection g) ((sigmaMkLocalIso B i x).symm.Ψ ∘ g i ∘ (sigmaMkLocalIso B i x).symm.ϕ)
      (range (Sigma.mk i)) := by
  rintro _ ⟨y, rfl⟩
  change sigmaSection g ⟨i, y⟩ = Sigma.mk i (g i ((sigmaMkLocalIso B i x).g ⟨i, y⟩))
  rw [sigmaMkLocalIso_g_mk]
  rfl

/-- On `O_i`, `g i` is `sigmaSection g` transported by `sigmaMkLocalIso`. -/
theorem eqOn_piece (g : ∀ i, X i → Y i) (i : ι) (x : X i) :
    EqOn (g i) ((sigmaMkLocalIso B i x).Ψ ∘ sigmaSection g ∘ (sigmaMkLocalIso B i x).ϕ) univ :=
  fun y _ => (sigmaMkLocalIso_Ψ_mk B i x (g i y)).symm

/-- **sc-Fredholm germs of a disjoint union** are those of the pieces. -/
theorem isScFredholmGerm_sigma_iff {g : ∀ i, X i → Y i} (hg : ∀ i, IsSection (p i) (g i))
    (i : ι) (x : X i) :
    (StrongBundle.sigma B).IsScFredholmGerm (sigmaSection g) ⟨i, x⟩ ↔
      (B i).IsScFredholmGerm (g i) x := by
  constructor
  · exact (sigmaMkLocalIso B i x).isScFredholmGerm (eqOn_piece B g i x)
      (isSection_sigmaSection hg) (mem_univ x)
  · intro h
    refine (sigmaMkLocalIso B i x).symm.isScFredholmGerm (eqOn_sigmaSection B g i x) (hg i)
      (mem_range_self x) ?_
    change (B i).IsScFredholmGerm (g i) ((sigmaMkLocalIso B i x).g ⟨i, x⟩)
    rwa [sigmaMkLocalIso_g_mk]

/-- **Tame sc-Fredholm germs of a disjoint union** are those of the pieces. -/
theorem isScFredholmGermTame_sigma_iff {g : ∀ i, X i → Y i} (hg : ∀ i, IsSection (p i) (g i))
    (i : ι) (x : X i) :
    (StrongBundle.sigma B).IsScFredholmGermTame (sigmaSection g) ⟨i, x⟩ ↔
      (B i).IsScFredholmGermTame (g i) x := by
  constructor
  · exact (sigmaMkLocalIso B i x).isScFredholmGermTame (eqOn_piece B g i x)
      (isSection_sigmaSection hg) (mem_univ x)
  · intro h
    refine (sigmaMkLocalIso B i x).symm.isScFredholmGermTame (eqOn_sigmaSection B g i x) (hg i)
      (mem_range_self x) ?_
    change (B i).IsScFredholmGermTame (g i) ((sigmaMkLocalIso B i x).g ⟨i, x⟩)
    rwa [sigmaMkLocalIso_g_mk]

/-- The regularizing property of a family of regularizing sections gives that of
`sigmaSection g`. -/
theorem regularizing_sigmaSection {g : ∀ i, X i → Y i} (hg : ∀ i, IsSection (p i) (g i))
    (h : ∀ i, ∀ m, ∀ x ∈ (PX i).levelSet m, g i x ∈ (B i).doubleLevel m (m + 1) →
      x ∈ (PX i).levelSet (m + 1)) :
    ∀ m, ∀ x ∈ (MPolyfold.sigma PX).levelSet m,
      sigmaSection g x ∈ (StrongBundle.sigma B).doubleLevel m (m + 1) →
        x ∈ (MPolyfold.sigma PX).levelSet (m + 1) := by
  rintro m ⟨i, x⟩ hxm hfx
  exact (sigmaMkLocalIso B i x).symm.regularizing_at (eqOn_sigmaSection B g i x)
    (isSection_sigmaSection hg) (hg i) (mem_range_self x) m (h i m _) hxm hfx

/-- **sc-Fredholm sections of a disjoint union** are the families of sc-Fredholm sections
(Definition 3.1.16 is local). -/
theorem isScFredholmSection_sigma_iff (g : ∀ i, X i → Y i) :
    (StrongBundle.sigma B).IsScFredholmSection (sigmaSection g) ↔
      ∀ i, (B i).IsScFredholmSection (g i) := by
  constructor
  · intro h i
    exact isScFredholmSection_of_forall (B' := StrongBundle.sigma B)
      ((isScSmoothSection_sigma_iff B g).1 h.isScSmooth i) fun x =>
        ⟨univ, range (Sigma.mk i), sigmaMkLocalIso B i x, sigmaSection g, mem_univ x,
          eqOn_piece B g i x, h⟩
  · intro h
    have hg : ∀ i, IsSection (p i) (g i) := fun i => (h i).isScSmooth.1
    refine ⟨(isScSmoothSection_sigma_iff B g).2 fun i => (h i).isScSmooth,
      regularizing_sigmaSection B hg fun i => (h i).regularizing, ?_⟩
    rintro ⟨i, x⟩ hx
    exact (isScFredholmGerm_sigma_iff B hg i x).2
      ((h i).germ x ((MPolyfold.mem_smoothSet_sigma_iff PX x).1 hx))

/-- **Tame sc-Fredholm sections of a disjoint union** (Definition 3.6.5) are the families of tame
sc-Fredholm sections. -/
theorem isScFredholmSectionTame_sigma_iff (g : ∀ i, X i → Y i) :
    (StrongBundle.sigma B).IsScFredholmSectionTame (sigmaSection g) ↔
      ∀ i, (B i).IsScFredholmSectionTame (g i) := by
  constructor
  · intro h i
    exact isScFredholmSectionTame_of_forall (B' := StrongBundle.sigma B)
      ((isScSmoothSection_sigma_iff B g).1 h.isScSmooth i) fun x =>
        ⟨univ, range (Sigma.mk i), sigmaMkLocalIso B i x, sigmaSection g, mem_univ x,
          eqOn_piece B g i x, h⟩
  · intro h
    have hg : ∀ i, IsSection (p i) (g i) := fun i => (h i).isScSmooth.1
    refine ⟨(isScFredholmSection_sigma_iff B g).2 fun i => (h i).toIsScFredholmSection, ?_⟩
    rintro ⟨i, x⟩ hx
    exact (isScFredholmGermTame_sigma_iff B hg i x).2
      ((h i).germTame x ((MPolyfold.mem_smoothSet_sigma_iff PX x).1 hx))

end StrongBundle

end Sigma

/-! ### Definition 18.1.1 -/

namespace GCT.VectorBundle.StrongPolyfoldBundleConstruction

open GroupoidalCategory GroupoidalCategory.BanachFunctor StrongBundleUniformizerConstruction
  StrongBundleUniformizerData PolyfoldConstruction

variable {C : GCT.{u}} {V : C.VectorBundle} {S : C.PolyfoldConstruction}
  (Q : V.StrongPolyfoldBundleConstruction S) (f : V.SectionFunctor)

/-- **2021 Definition 18.1.1, p. 844 (sc-Fredholm section functor)**: for every object `α` and
every `Ψ̄ ∈ F̄(α)`, the representative `f_Ψ̄ : O → K` is sc-Fredholm (Definition 3.1.16). -/
def IsScFredholmSectionFunctor : Prop :=
  ∀ α, ∀ Ψ ∈ Q.F α, Ψ.B.IsScFredholmSection (Ψ.localRep f)

/-- `f` is **sc-smooth** (Remark 18.1.2 (c)): every representative `f_Ψ̄` is sc-smooth. -/
def IsScSmoothSectionFunctor : Prop :=
  ∀ α, ∀ Ψ ∈ Q.F α, Ψ.B.IsScSmoothSection (Ψ.localRep f)

/-- The tame form of Definition 18.1.1: every representative is a tame sc-Fredholm section
(Definition 3.6.5), the form Part III's implicit function theorems use. -/
def IsScFredholmSectionFunctorTame : Prop :=
  ∀ α, ∀ Ψ ∈ Q.F α, Ψ.B.IsScFredholmSectionTame (Ψ.localRep f)

/-- `f` is **regularizing** (Remark 18.1.2 (b)), in the representatives: `q ∈ O_m` and
`f_Ψ̄(q) ∈ K_{m,m+1}` imply `q ∈ O_{m+1}`. -/
def IsRegularizing : Prop :=
  ∀ α, ∀ Ψ ∈ Q.F α, ∀ m, ∀ q ∈ Ψ.base.P.levelSet m,
    Ψ.localRep f q ∈ Ψ.B.doubleLevel m (m + 1) → q ∈ Ψ.base.P.levelSet (m + 1)

/-- The standing reading `F̄(α) ≠ ∅` for every object (the bundle form of Chapter 17's
`HasUniformizers`). -/
def HasStrongBundleUniformizers : Prop := ∀ α, (Q.F α).Nonempty

theorem isScFredholmSectionFunctor_iff_unif :
    Q.IsScFredholmSectionFunctor f ↔ ∀ Ψ : Q.Unif, Ψ.1.B.IsScFredholmSection (Ψ.1.localRep f) :=
  ⟨fun h Ψ => Ψ.2.elim fun α hα => h α _ hα, fun h α Ψ hΨ => h ⟨Ψ, α, hΨ⟩⟩

theorem isScSmoothSectionFunctor_iff_unif :
    Q.IsScSmoothSectionFunctor f ↔ ∀ Ψ : Q.Unif, Ψ.1.B.IsScSmoothSection (Ψ.1.localRep f) :=
  ⟨fun h Ψ => Ψ.2.elim fun α hα => h α _ hα, fun h α Ψ hΨ => h ⟨Ψ, α, hΨ⟩⟩

theorem isScFredholmSectionFunctorTame_iff_unif :
    Q.IsScFredholmSectionFunctorTame f ↔
      ∀ Ψ : Q.Unif, Ψ.1.B.IsScFredholmSectionTame (Ψ.1.localRep f) :=
  ⟨fun h Ψ => Ψ.2.elim fun α hα => h α _ hα, fun h α Ψ hΨ => h ⟨Ψ, α, hΨ⟩⟩

theorem IsScFredholmSectionFunctorTame.toIsScFredholmSectionFunctor
    (h : Q.IsScFredholmSectionFunctorTame f) : Q.IsScFredholmSectionFunctor f :=
  fun α Ψ hΨ => (h α Ψ hΨ).toIsScFredholmSection

theorem IsScFredholmSectionFunctor.isScSmoothSectionFunctor (h : Q.IsScFredholmSectionFunctor f) :
    Q.IsScSmoothSectionFunctor f :=
  fun α Ψ hΨ => (h α Ψ hΨ).isScSmooth

/-! ### The model section -/

variable {ι : Type u} (Ψb : ι → Q.Unif)

theorem modelSection_eq_sigmaSection :
    Q.modelSection Ψb f = StrongBundle.sigmaSection fun i => (Ψb i).1.localRep f := rfl

/-- **In a model, `f^Ψ̄_Ψ` is an sc-smooth section functor** (Definition 8.3.4) iff every
representative `f_{Ψ̄_λ}` is sc-smooth. -/
theorem isScSmoothSectionFunctor_model_iff :
    (Q.modelEpStrongBundle Ψb).IsScSmoothSectionFunctor (Q.modelSection Ψb f) ↔
      ∀ i, (Ψb i).1.B.IsScSmoothSection ((Ψb i).1.localRep f) := by
  constructor
  · rintro ⟨h, -⟩
    exact (StrongBundle.isScSmoothSection_sigma_iff (fun i => (Ψb i).1.B) _).1 h
  · intro h
    exact ⟨(StrongBundle.isScSmoothSection_sigma_iff (fun i => (Ψb i).1.B) _).2 h,
      Q.isFunctorialSection_modelSection Ψb f⟩

/-- **In a model, `f^Ψ̄_Ψ` is an sc-Fredholm section functor** (Definition 8.3.4 (3)) iff every
representative `f_{Ψ̄_λ}` is sc-Fredholm. -/
theorem isScFredholmSectionFunctor_model_iff :
    (Q.modelEpStrongBundle Ψb).IsScFredholmSectionFunctor (Q.modelSection Ψb f) ↔
      ∀ i, (Ψb i).1.B.IsScFredholmSection ((Ψb i).1.localRep f) := by
  constructor
  · rintro ⟨-, h⟩
    exact (StrongBundle.isScFredholmSection_sigma_iff (fun i => (Ψb i).1.B) _).1 h
  · intro h
    exact ⟨(Q.isScSmoothSectionFunctor_model_iff f Ψb).2 fun i => (h i).isScSmooth,
      (StrongBundle.isScFredholmSection_sigma_iff (fun i => (Ψb i).1.B) _).2 h⟩

/-- **The tame form in a model**: `f^Ψ̄_Ψ` is a tame sc-Fredholm section of `W_Ψ̄ → X_Ψ` iff
every representative is. -/
theorem isScFredholmSectionTame_model_iff :
    (Q.modelSEP Ψb).B.IsScFredholmSectionTame (Q.modelSection Ψb f) ↔
      ∀ i, (Ψb i).1.B.IsScFredholmSectionTame ((Ψb i).1.localRep f) :=
  StrongBundle.isScFredholmSectionTame_sigma_iff (fun i => (Ψb i).1.B)
    (fun i => (Ψb i).1.localRep f)

/-! ### Remark 18.1.2 (a): a covering family suffices -/

/-- The family `Ψ̄ ⊔ {Ψ̄'}`. -/
abbrev adjoin (c : Q.BundleCoveringFamily) (Ψ : Q.Unif) : c.ι ⊕ PUnit.{u + 1} → Q.Unif :=
  Sum.elim c.Ψ fun _ => Ψ

/-- The inclusion `W_Ψ̄ → W_{Ψ̄ ⊔ {Ψ̄'}}` is a strong bundle equivalence. -/
theorem equivalences_adjoin (c : Q.BundleCoveringFamily) (Ψ : Q.Unif) :
    SEP.equivalences (Q.bundleIncl c.Ψ (Q.adjoin c Ψ) Sum.inl rfl) :=
  Q.equivalences_bundleIncl rfl c.cover

/-- `f^{Ψ̄ ⊔ {Ψ̄'}}` is the push-forward of `f^Ψ̄`. -/
theorem modelSection_adjoin (c : Q.BundleCoveringFamily) (Ψ : Q.Unif) :
    (SBLocalization.sbe (Q.equivalences_adjoin c Ψ)).pushforward (Q.modelSection c.Ψ f) =
      Q.modelSection (Q.adjoin c Ψ) f :=
  Q.pushforward_modelSection (Ψb' := c.Ψ) (σ := Sum.inl) f (Q.adjoin c Ψ) rfl c.cover

/-- **The easy exercise of Remark 18.1.2 (a), sc-smooth form**: if the representatives of a
covering family are sc-smooth, so is `f_Ψ̄'` for every `Ψ̄'` of `F̄`. -/
theorem isScSmoothSection_of_covering (c : Q.BundleCoveringFamily)
    (h : ∀ i, (c.Ψ i).1.B.IsScSmoothSection ((c.Ψ i).1.localRep f)) (Ψ : Q.Unif) :
    Ψ.1.B.IsScSmoothSection (Ψ.1.localRep f) := by
  have h1 := (Q.isScSmoothSectionFunctor_model_iff f c.Ψ).2 h
  have h2 := (EpStrongBundle.theorem_10_4_5 (SBLocalization.sbe (Q.equivalences_adjoin c Ψ))).1.1 h1
  rw [Q.modelSection_adjoin f c Ψ] at h2
  exact (Q.isScSmoothSectionFunctor_model_iff f (Q.adjoin c Ψ)).1 h2 (Sum.inr PUnit.unit)

/-- **The easy exercise of Remark 18.1.2 (a)**: if the representatives `f_Ψ̄`, `Ψ̄` in a covering
family, are sc-Fredholm, so is `f_Ψ̄'` for every `Ψ̄'` of `F̄`: in the model of `Ψ̄ ⊔ {Ψ̄'}`,
`f^{Ψ̄ ⊔ {Ψ̄'}}` is the push-forward of the sc-Fredholm section functor `f^Ψ̄` along a strong bundle
equivalence (Theorem 10.4.5), and `f_Ψ̄'` is one of its pieces. -/
theorem isScFredholmSection_of_covering (c : Q.BundleCoveringFamily)
    (h : ∀ i, (c.Ψ i).1.B.IsScFredholmSection ((c.Ψ i).1.localRep f)) (Ψ : Q.Unif) :
    Ψ.1.B.IsScFredholmSection (Ψ.1.localRep f) := by
  have h1 := (Q.isScFredholmSectionFunctor_model_iff f c.Ψ).2 h
  have h2 :=
    (EpStrongBundle.theorem_10_4_5_fred (SBLocalization.sbe (Q.equivalences_adjoin c Ψ))).1 h1
  rw [Q.modelSection_adjoin f c Ψ] at h2
  exact (Q.isScFredholmSectionFunctor_model_iff f (Q.adjoin c Ψ)).1 h2 (Sum.inr PUnit.unit)

/-- **The easy exercise of Remark 18.1.2 (a), tame form.** -/
theorem isScFredholmSectionTame_of_covering (c : Q.BundleCoveringFamily)
    (h : ∀ i, (c.Ψ i).1.B.IsScFredholmSectionTame ((c.Ψ i).1.localRep f)) (Ψ : Q.Unif) :
    Ψ.1.B.IsScFredholmSectionTame (Ψ.1.localRep f) := by
  have h1 := (Q.isScFredholmSectionFunctor_model_iff f c.Ψ).2 fun i =>
    (h i).toIsScFredholmSection
  have h2 := (SBLocalization.sbe (Q.equivalences_adjoin c Ψ)).isScFredholmSectionTame_pushforward
    h1.1 ((Q.isScFredholmSectionTame_model_iff f c.Ψ).2 h)
  rw [Q.modelSection_adjoin f c Ψ] at h2
  exact (Q.isScFredholmSectionTame_model_iff f (Q.adjoin c Ψ)).1 h2 (Sum.inr PUnit.unit)

/-- **2021 Remark 18.1.2 (a), p. 844**: the sc-Fredholm property is checkable with a covering
family. -/
theorem remark_18_1_2_a (c : Q.BundleCoveringFamily) :
    Q.IsScFredholmSectionFunctor f ↔
      ∀ i, (c.Ψ i).1.B.IsScFredholmSection ((c.Ψ i).1.localRep f) :=
  ⟨fun h i => (Q.isScFredholmSectionFunctor_iff_unif f).1 h (c.Ψ i), fun h =>
    (Q.isScFredholmSectionFunctor_iff_unif f).2 (Q.isScFredholmSection_of_covering f c h)⟩

/-- Remark 18.1.2 (a), the sc-smooth property (Remark 18.1.2 (c): "which can be checked by a
covering family"). -/
theorem remark_18_1_2_a_smooth (c : Q.BundleCoveringFamily) :
    Q.IsScSmoothSectionFunctor f ↔
      ∀ i, (c.Ψ i).1.B.IsScSmoothSection ((c.Ψ i).1.localRep f) :=
  ⟨fun h i => (Q.isScSmoothSectionFunctor_iff_unif f).1 h (c.Ψ i), fun h =>
    (Q.isScSmoothSectionFunctor_iff_unif f).2 (Q.isScSmoothSection_of_covering f c h)⟩

/-- Remark 18.1.2 (a), tame form. -/
theorem remark_18_1_2_a_tame (c : Q.BundleCoveringFamily) :
    Q.IsScFredholmSectionFunctorTame f ↔
      ∀ i, (c.Ψ i).1.B.IsScFredholmSectionTame ((c.Ψ i).1.localRep f) :=
  ⟨fun h i => (Q.isScFredholmSectionFunctorTame_iff_unif f).1 h (c.Ψ i), fun h =>
    (Q.isScFredholmSectionFunctorTame_iff_unif f).2 (Q.isScFredholmSectionTame_of_covering f c h)⟩

/-- **2021 Remark 18.1.2 (a), p. 844, last sentence**: the pull-back `f^Ψ̄_Ψ` of `f` by
`Γ̄_Ψ̄ : W_Ψ̄ → E`, for a covering family, is an sc-Fredholm section functor of the strong bundle
`W_Ψ̄ → X_Ψ` over an ep-groupoid iff `f` is an sc-Fredholm section functor. -/
theorem remark_18_1_2_a_model (c : Q.BundleCoveringFamily) :
    (Q.modelEpStrongBundle c.Ψ).IsScFredholmSectionFunctor (Q.modelSection c.Ψ f) ↔
      Q.IsScFredholmSectionFunctor f :=
  (Q.isScFredholmSectionFunctor_model_iff f c.Ψ).trans (Q.remark_18_1_2_a f c).symm

/-- The sc-smooth form of `remark_18_1_2_a_model`. -/
theorem remark_18_1_2_a_model_smooth (c : Q.BundleCoveringFamily) :
    (Q.modelEpStrongBundle c.Ψ).IsScSmoothSectionFunctor (Q.modelSection c.Ψ f) ↔
      Q.IsScSmoothSectionFunctor f :=
  (Q.isScSmoothSectionFunctor_model_iff f c.Ψ).trans (Q.remark_18_1_2_a_smooth f c).symm

/-- The tame form of `remark_18_1_2_a_model`. -/
theorem remark_18_1_2_a_model_tame (c : Q.BundleCoveringFamily) :
    (Q.modelSEP c.Ψ).B.IsScFredholmSectionTame (Q.modelSection c.Ψ f) ↔
      Q.IsScFredholmSectionFunctorTame f :=
  (Q.isScFredholmSectionTame_model_iff f c.Ψ).trans (Q.remark_18_1_2_a_tame f c).symm

/-- **Independence of the covering family**: `f^Ψ̄_Ψ` is sc-Fredholm in one model iff in every
model. -/
theorem isScFredholm_model_iff_model (c c' : Q.BundleCoveringFamily) :
    (Q.modelEpStrongBundle c.Ψ).IsScFredholmSectionFunctor (Q.modelSection c.Ψ f) ↔
      (Q.modelEpStrongBundle c'.Ψ).IsScFredholmSectionFunctor (Q.modelSection c'.Ψ f) :=
  (Q.remark_18_1_2_a_model f c).trans (Q.remark_18_1_2_a_model f c').symm

/-! ### Remark 18.1.2 (b) -/

/-- **2021 Remark 18.1.2 (b), p. 844**: an sc-Fredholm section functor is regularizing. -/
theorem remark_18_1_2_b (hf : Q.IsScFredholmSectionFunctor f) : Q.IsRegularizing f :=
  fun α Ψ hΨ m q hq hfq => (hf α Ψ hΨ).regularizing m q hq hfq

/-- **2021 Remark 18.1.2 (b) in the levels `C_m` of p. 765**: if `α ∈ C_m` and `f(α) ∈ E_{m,m+1}`
(read in a strong bundle uniformizer `Ψ̄` with `Ψ(q) = α`), then `α ∈ C_{m+1}`. -/
theorem remark_18_1_2_b_levels (hf : Q.IsScFredholmSectionFunctor f) {α β : C.Obj}
    {Ψ : V.StrongBundleUniformizer} (hΨ : Ψ ∈ Q.F β) {q : Ψ.base.O} (hq : Ψ.base.obj q = α)
    (m : ℕ) (hα : S.HasRegularity m α) (hfq : Ψ.localRep f q ∈ Ψ.B.doubleLevel m (m + 1)) :
    S.HasRegularity (m + 1) α := by
  have hiso : C.toGroupoidStr.Isomorphic ((Q.baseUnif ⟨Ψ, β, hΨ⟩).1.obj q) α :=
    hq ▸ GroupoidStr.isomorphic_refl _ _
  rw [hasRegularity_iff _ hiso] at hα ⊢
  exact (hf β Ψ hΨ).regularizing m q hα hfq

/-! ### Remark 18.1.2 (c) -/

/-- The germ condition of Remark 18.1.2 (c): over every smooth point `|α|` of `|C|` there are an
object `α'` with `|α'| = |α|`, `Ψ̄ ∈ F̄(α')` with `Ψ(q̄) = α'`, and `(f_Ψ̄, q̄)` is an sc-Fredholm
germ (Definition 3.1.11). -/
def HasFredholmGerms : Prop :=
  ∀ α, S.IsSmoothObj α → ∃ α', C.π α' = C.π α ∧ ∃ Ψ ∈ Q.F α', ∃ q : Ψ.base.O,
    Ψ.base.obj q = α' ∧ Ψ.B.IsScFredholmGerm (Ψ.localRep f) q

/-- `Ψ(q)` is a smooth object for a smooth point `q`. -/
theorem isSmoothObj_obj {β : C.Obj} {Ψ : V.StrongBundleUniformizer} (hΨ : Ψ ∈ Q.F β)
    {q : Ψ.base.O} (hq : q ∈ Ψ.base.P.smoothSet) : S.IsSmoothObj (Ψ.base.obj q) := fun m =>
  (hasRegularity_iff (Q.baseUnif ⟨Ψ, β, hΨ⟩) (GroupoidStr.isomorphic_refl _ _) m).2
    (mem_iInter.1 hq m)

/-- **The germ transfer**: an sc-Fredholm germ of `f_Ψ̄₀` at `q₀` gives one of `f_Ψ̄'` at every
`q'` with `Ψ₀(q₀) ≅ Ψ'(q')`.  In the model of `{Ψ̄₀, Ψ̄'}` the morphism `(q₀, φ, q')` acts by a
local strong bundle isomorphism along which `f^Ψ̄` is its own pull-back (Chapter 10's
`exists_localIso_mor`), and the germ moves along it (Part I's key lemma). -/
theorem isScFredholmGerm_of_isomorphic (Ψ₀ Ψ' : Q.Unif) {q₀ : Ψ₀.1.base.O} {q' : Ψ'.1.base.O}
    (hiso : C.toGroupoidStr.Isomorphic (Ψ₀.1.base.obj q₀) (Ψ'.1.base.obj q'))
    (h : Ψ₀.1.B.IsScFredholmGerm (Ψ₀.1.localRep f) q₀) :
    Ψ'.1.B.IsScFredholmGerm (Ψ'.1.localRep f) q' := by
  obtain ⟨φ, hφs, hφt⟩ := hiso
  let Φb : PUnit.{u + 1} ⊕ PUnit.{u + 1} → Q.Unif := Sum.elim (fun _ => Ψ₀) fun _ => Ψ'
  let a : S.Tr (Q.modelBase Φb (Sum.inl PUnit.unit)) (Q.modelBase Φb (Sum.inr PUnit.unit)) :=
    { src := q₀, mor := φ, tgt := q', src_mor := hφs, tgt_mor := hφt }
  let σ : S.ModelMor (Q.modelBase Φb) := ⟨(Sum.inl PUnit.unit, Sum.inr PUnit.unit), a⟩
  have hg : ∀ i, IsSection (Φb i).1.p ((Φb i).1.localRep f) := fun i =>
    (Φb i).1.isSection_localRep f
  obtain ⟨U, U', L, htU, hϕ, heq⟩ := (Q.modelEpStrongBundle Φb).exists_localIso_mor σ
  have heq' := heq (Q.modelSection Φb f) (Q.isSection_modelSection Φb f)
    (Q.isFunctorialSection_modelSection Φb f)
  have h₀ : (Q.modelBundle Φb).IsScFredholmGerm (Q.modelSection Φb f)
      (L.ϕ ((S.modelEpGroupoid (Q.modelBase Φb)).tgt σ)) := by
    rw [hϕ]
    exact (StrongBundle.isScFredholmGerm_sigma_iff (fun i => (Φb i).1.B) hg
      (Sum.inl PUnit.unit) q₀).2 h
  have h₁ := L.isScFredholmGerm heq' (Q.isSection_modelSection Φb f) htU h₀
  exact (StrongBundle.isScFredholmGerm_sigma_iff (fun i => (Φb i).1.B) hg
    (Sum.inr PUnit.unit) q').1 h₁

/-- **Remark 18.1.2 (c), "⇐"**: a regularizing sc-smooth section functor with an sc-Fredholm germ
in one representative over every smooth point is an sc-Fredholm section functor. -/
theorem isScFredholmSectionFunctor_of_germs (hs : Q.IsScSmoothSectionFunctor f)
    (hr : Q.IsRegularizing f) (hg : Q.HasFredholmGerms f) : Q.IsScFredholmSectionFunctor f := by
  intro β Ψ hΨ
  refine ⟨hs β Ψ hΨ, hr β Ψ hΨ, fun q hq => ?_⟩
  obtain ⟨α₀, hπ, Ψ₀, hΨ₀, q₀, hq₀, hgerm⟩ := hg _ (Q.isSmoothObj_obj hΨ hq)
  refine Q.isScFredholmGerm_of_isomorphic f ⟨Ψ₀, α₀, hΨ₀⟩ ⟨Ψ, β, hΨ⟩ ?_ hgerm
  rw [hq₀]
  exact (GroupoidalCategory.π_eq_π_iff (C := C.toGroupoidalCategory)).1 hπ

/-- **2021 Remark 18.1.2 (c), p. 844**: under the standing reading `F̄(α) ≠ ∅`, `f` is an
sc-Fredholm section functor iff it is sc-smooth (checkable by a covering family,
`remark_18_1_2_a_smooth`), regularizing, and over every smooth `z ∈ |C|` there are `α` with
`|α| = z` and `Ψ̄ ∈ F̄(α)`, `Ψ(q̄) = α`, with `(f_Ψ̄, q̄)` an sc-Fredholm germ. -/
theorem remark_18_1_2_c (hF : Q.HasStrongBundleUniformizers) :
    Q.IsScFredholmSectionFunctor f ↔
      Q.IsScSmoothSectionFunctor f ∧ Q.IsRegularizing f ∧ Q.HasFredholmGerms f := by
  refine ⟨fun hf => ⟨hf.isScSmoothSectionFunctor, Q.remark_18_1_2_b f hf, fun α hα => ?_⟩,
    fun ⟨hs, hr, hg⟩ => Q.isScFredholmSectionFunctor_of_germs f hs hr hg⟩
  obtain ⟨Ψ, hΨ⟩ := hF α
  obtain ⟨q, hq⟩ := S.isAt α Ψ.base (Q.base_mem α Ψ hΨ)
  refine ⟨α, rfl, Ψ, hΨ, q, hq, (hf α Ψ hΨ).germ q (mem_iInter.2 fun m => ?_)⟩
  exact (regularity_eq_of_mem (Q.base_mem α Ψ hΨ) hq m).1 (hα m)

end GCT.VectorBundle.StrongPolyfoldBundleConstruction

end Polyfold
