import Polyfold.Chapter17.StrongBundleStructures
import Polyfold.Chapter17.SigmaStrongBundle
import Polyfold.Chapter17.ModelEquivalence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.7 "Strong Bundle Structures", pp. 826–828: **the strong bundle model** `W_Ψ̄ → X_Ψ` of a
family of strong bundle uniformizers of a strong polyfold bundle construction, and its functor
`Γ̄_Ψ̄ : W_Ψ̄ → E`.  These are the strong bundle analogues of Theorem 17.1.14 and Lemma 17.1.15,
which §17.7 leaves to the reader (Chapter 18 uses them).  Numbers and pages are the 2021 text's.

# The strong bundle model

## The text, paraphrased

(§17.7, pp. 826–828) For a strong polyfold bundle construction `(F̄, M)` (Definition 17.7.4) the
transition sets `M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` carry strong bundle structures for which the source and
target maps `s̄`, `t̄` are sc-smooth strong bundle maps and local strong bundle isomorphisms
covering `s`, `t`, and the unit, inversion and multiplication are strong bundle maps covering
those of `M(Ψ, Ψ')`.  The section ends there.  We read it as leaving to the reader the strong
bundle analogues of §17.1: for a family `Ψ̄ = (Ψ̄_λ)` the strong bundle
`W = ⊔_λ K_λ → X = ⊔_λ O_λ` over the ep-groupoid `X_Ψ` of Theorem 17.1.14, with the morphisms
`⊔ M(Ψ̄_λ, Ψ̄_λ')`, is a strong bundle over an ep-groupoid, and the functors `Ψ̄_λ` assemble to
`Γ̄_Ψ̄ : W → E` covering `Γ_Ψ`.

## What is formalized (namespace `Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction`)

For `Q : V.StrongPolyfoldBundleConstruction S` and a family `Ψb : ι → Q.Unif` with base family
`modelBase Ψb = (Ψ_λ)`:
* `ModelW Ψb = Σ λ, K_λ`, the projection `modelP` (`sigmaBundleProj`), the strong bundle
  `modelBundle` (`StrongBundle.sigma`) over `X = ⊔ O_λ`.
* `modelMu`, the structure map `μ(φ, k) = t̄(φ, k)` on `𝐗 ₛ×_P W = ⊔ M(Ψ̄_λ, Ψ̄_λ')`
  (`pullbackSigmaEquiv`), with `isStrongBundleMap_modelMu` (from `t̄` being a strong bundle map),
  `isLocalScDiffeo_modelMu` (from `t̄` being a local strong bundle isomorphism), `modelMu_unit`
  and `modelMu_comp` (the unit and multiplication of p. 828).
* `modelEpStrongBundle` (Definition 8.3.1 for `W_Ψ̄ → X_Ψ`), `modelSEP` (the object of `SEP`),
  `theorem_17_1_14_bundle`.
* `bundleModelFunctor` (`Γ̄_Ψ̄ : W_Ψ̄ → E`, `k_λ ↦ Ψ̄_λ(k_λ)`, `(φ, k) ↦ (Γ_Ψ(φ), Ψ̄_λ(k))`),
  `proj_comp_bundleModelFunctor` (`P ∘ Γ̄ = Γ_Ψ ∘ P_W`), `bundleModelFiber` (the fibre maps
  `W_x → μ(Γ_Ψ(x))`, Banach space isomorphisms), `bundleModelFunctor_full`,
  `bundleModelFunctor_faithful`, `bundleModelFunctor_essSurj` (covering families),
  `isHomeomorph_bundleModelOrbitMap` (`|Γ̄| : |W_Ψ̄| → |E|` is a homeomorphism for covering
  families) and `lemma_17_1_15_bundle`.

## Readings

* The strong bundle structure of `M(Ψ̄, Ψ̄')` is the pull-back `s*K` of Definition 17.7.4 as read
  in `StrongBundleStructures.lean`; the morphism space `𝐗 ₛ×_P W` of the model is then the disjoint
  union of these pull-backs (`pullbackSigmaEquiv`), and `μ` is `t̄` on every piece.
* "Covering family" for `Ψ̄` is read as: the base family `Ψ` covers `|C|`.  Since the footprint of
  `Ψ̄` is `|P|⁻¹` of the footprint of `Ψ` (Definition 17.7.2 (3)) and `|P|` is surjective
  (Definition 17.7.1 (2)), this is the same as the footprints of `Ψ̄` covering `|E|`.
* `|E|` carries the topology `T` of Definition 17.7.1, not a quotient topology; `|Γ̄|` is a
  homeomorphism for `T` because every `|Ψ̄_λ|` is an open embedding for `T` (Definition 17.7.2 (3)).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace GCT.VectorBundle.StrongPolyfoldBundleConstruction

open GroupoidalCategory GroupoidalCategory.BanachFunctor StrongBundleUniformizerConstruction
  StrongBundleUniformizerData PolyfoldConstruction

variable {C : GCT.{u}} {V : C.VectorBundle} {S : C.PolyfoldConstruction}
  (Q : V.StrongPolyfoldBundleConstruction S) {ι : Type u} (Ψb : ι → Q.Unif)

/-- The base family `Ψ = (Ψ_λ)` of a family `Ψb` of strong bundle uniformizers. -/
abbrev modelBase : ι → S.Unif := fun i => Q.baseUnif (Ψb i)

/-- **The total space `W = ⊔_λ K_λ`** of the model strong bundle. -/
abbrev ModelW : Type u := Σ i, (Ψb i).1.K

/-- The projection `W = ⊔ K_λ → X = ⊔ O_λ`. -/
abbrev modelP : Q.ModelW Ψb → S.ModelObj (Q.modelBase Ψb) :=
  sigmaBundleProj fun i => (Ψb i).1.p

/-- The source map `s : M(Ψ_λ, Ψ_λ') → O_λ` on the piece `j = (λ, λ')` of `𝐗`. -/
abbrev modelSrcPiece (j : ι × ι) (a : S.Tr (Q.modelBase Ψb j.1) (Q.modelBase Ψb j.2)) :
    (Ψb j.1).1.base.O := a.src

/-- The source map of `X_Ψ`, written as `Sigma.map`. -/
abbrev modelSrc : S.ModelMor (Q.modelBase Ψb) → S.ModelObj (Q.modelBase Ψb) :=
  Sigma.map Prod.fst (Q.modelSrcPiece Ψb)

/-- The source map of `X_Ψ` is `modelSrc`. -/
theorem modelEpGroupoid_src : (S.modelEpGroupoid (Q.modelBase Ψb)).src = Q.modelSrc Ψb := rfl

/-- **The strong bundle `W = ⊔_λ K_λ → X = ⊔_λ O_λ`** (the disjoint union of the strong bundles
`p_λ : K_λ → O_λ` of Definition 17.7.2 (1), `StrongBundle.sigma`). -/
def modelBundle : StrongBundle (S.modelEpGroupoid (Q.modelBase Ψb)).PObj (Q.modelP Ψb) :=
  StrongBundle.sigma fun i => (Ψb i).1.B

instance : ParacompactSpace (pullbackSpace (Q.modelP Ψb) (Q.modelSrc Ψb)) :=
  (Q.modelBundle Ψb).paracompactSpace_pullback (S.modelEpGroupoid (Q.modelBase Ψb)).PMor _

instance :
    ParacompactSpace (pullbackSpace (Q.modelP Ψb) (S.modelEpGroupoid (Q.modelBase Ψb)).src) :=
  (Q.modelBundle Ψb).paracompactSpace_pullback (S.modelEpGroupoid (Q.modelBase Ψb)).PMor _

/-- **The structure map `μ : 𝐗 ₛ×_P W → W`** of the model: on the piece
`M(Ψ̄_λ, Ψ̄_λ') = s*K_λ` of `𝐗 ₛ×_P W = ⊔ s*K_λ` (`pullbackSigmaEquiv`) it is `t̄`, i.e.
`μ((q_λ, φ, q_λ'), k) = k'` with `Ψ̄_λ'(k') = μ(φ)(Ψ̄_λ(k))`. -/
def modelMu (q : pullbackSpace (Q.modelP Ψb) (Q.modelSrc Ψb)) : Q.ModelW Ψb :=
  Sigma.map Prod.snd (fun j x => Q.transT (Ψb j.1) (Ψb j.2) x)
    (pullbackSigmaProj (p := fun i => (Ψb i).1.p) (σ := Prod.fst)
    (s := Q.modelSrcPiece Ψb) q)

/-- `μ` on the piece `M(Ψ̄_λ, Ψ̄_λ')` is `t̄`. -/
@[simp] theorem modelMu_incl (j : ι × ι) (x : Q.TransSpace (Ψb j.1) (Ψb j.2)) :
    Q.modelMu Ψb (pullbackSigmaIncl (p := fun i => (Ψb i).1.p) (s := Q.modelSrcPiece Ψb) j x) =
      ⟨j.2, Q.transT (Ψb j.1) (Ψb j.2) x⟩ := rfl

/-- `s : 𝐗 → X` is sc-smooth (written with `modelSrc`). -/
theorem isScSmoothMap_modelSrc :
    (MPolyfold.sigma fun j : ι × ι =>
      S.transPolyfold (Q.modelBase Ψb j.1) (Q.modelBase Ψb j.2)).IsScSmoothMap
      (MPolyfold.sigma fun i => (Ψb i).1.base.P) (Q.modelSrc Ψb) :=
  (S.modelEpGroupoid (Q.modelBase Ψb)).isScSmoothMap_src

/-- **`μ` is a strong bundle map covering `t`**: on every piece it is `t̄`, a strong bundle map
covering `t` (Definition 17.7.4). -/
theorem isStrongBundleMap_modelMu :
    ((Q.modelBundle Ψb).pullback
      (S.modelEpGroupoid (Q.modelBase Ψb)).isScSmoothMap_src).IsStrongBundleMap
      (Q.modelBundle Ψb) (S.modelEpGroupoid (Q.modelBase Ψb)).tgt (Q.modelMu Ψb) := by
  refine (StrongBundle.isStrongBundleMap_pullbackSigma_iff (fun i => (Ψb i).1.B)
    (σ := Prod.fst) (s := Q.modelSrcPiece Ψb)
    (fun j : ι × ι => Q.isScSmoothMap_trSrc (Ψb j.1) (Ψb j.2))
    (Q.isScSmoothMap_modelSrc Ψb) _).2 fun j => ?_
  exact (StrongBundle.isStrongBundleMap_sigmaMk_comp_iff (fun i => (Ψb i).1.B) _).2
    (Q.isStrongBundleMap_trans (Ψb j.1) (Ψb j.2))

/-- `t̄ : M(Ψ̄, Ψ̄') → K'` is a local sc-diffeomorphism of the total spaces `[0]` (it is a local
strong bundle isomorphism, Definition 17.7.4). -/
theorem isLocalScDiffeo_transT (Ψ Ψ' : Q.Unif) :
    (Q.transBundle Ψ Ψ').toMPolyfold0.IsLocalScDiffeo Ψ'.1.B.toMPolyfold0 (Q.transT Ψ Ψ') :=
  fun x => by
    obtain ⟨W, W', hx, hi⟩ := Q.isLocalStrongBundleIso_trans Ψ Ψ' x.1.1
    obtain ⟨Ψ₀, h₀⟩ := hi.isScDiffeoOn_zero
    exact ⟨_, _, Ψ₀, hx, h₀⟩

/-- **`μ` is a local sc-diffeomorphism** (Definition 8.3.1 (1)). -/
theorem isLocalScDiffeo_modelMu :
    ((Q.modelBundle Ψb).pullback (Q.isScSmoothMap_modelSrc Ψb)).toMPolyfold0.IsLocalScDiffeo
      (Q.modelBundle Ψb).toMPolyfold0 (Q.modelMu Ψb) := by
  refine (StrongBundle.isLocalScDiffeo_pullbackSigma_iff (fun i => (Ψb i).1.B)
    (σ := Prod.fst) (s := Q.modelSrcPiece Ψb)
    (fun j : ι × ι => Q.isScSmoothMap_trSrc (Ψb j.1) (Ψb j.2))
    (Q.isScSmoothMap_modelSrc Ψb)).2 fun j => ?_
  have := (MPolyfold.isLocalScDiffeo_sigmaMk (fun i => (Ψb i).1.B.toMPolyfold0) j.2).comp
    (Q.isLocalScDiffeo_transT (Ψb j.1) (Ψb j.2))
  rw [← StrongBundle.sigma_toMPolyfold0] at this
  exact this

/-- `μ` depends only on the underlying pair. -/
theorem modelMu_congr {q q' : pullbackSpace (Q.modelP Ψb) (Q.modelSrc Ψb)}
    (h : (q : S.ModelMor (Q.modelBase Ψb) × Q.ModelW Ψb) = q') :
    Q.modelMu Ψb q = Q.modelMu Ψb q' := by
  rw [Subtype.ext h]

/-- **`μ(1_x, w) = w`** (Definition 8.3.1 (2); `T(1_q, k) = k`, p. 828). -/
theorem modelMu_unit (w : Q.ModelW Ψb) :
    Q.modelMu Ψb ((S.modelEpGroupoid (Q.modelBase Ψb)).unitPair w) = w := by
  obtain ⟨i, k⟩ := w
  exact congrArg (Sigma.mk i) (transAct_unit (Ψ := (Ψb i).1.toStrongBundleUniformizerData) k)

/-- **`μ(ψ ∘ γ, w) = μ(ψ, μ(γ, w))`** (Definition 8.3.1 (3); `T(b ∘ a, k) = T(b, T(a, k))`,
the multiplication of p. 828). -/
theorem modelMu_comp (ψ γ : S.ModelMor (Q.modelBase Ψb)) (w : Q.ModelW Ψb)
    (h₁ : Q.modelP Ψb w = (S.modelEpGroupoid (Q.modelBase Ψb)).src γ)
    (h₂ : (S.modelEpGroupoid (Q.modelBase Ψb)).src ψ = (S.modelEpGroupoid (Q.modelBase Ψb)).tgt γ) :
    Q.modelMu Ψb ⟨((S.modelEpGroupoid (Q.modelBase Ψb)).comp ψ γ, w),
      h₁.trans ((S.modelEpGroupoid (Q.modelBase Ψb)).src_comp ψ γ h₂).symm⟩ =
    Q.modelMu Ψb ⟨(ψ, Q.modelMu Ψb ⟨(γ, w), h₁⟩),
      ((Q.isStrongBundleMap_modelMu Ψb).covers ⟨(γ, w), h₁⟩).trans h₂.symm⟩ := by
  obtain ⟨⟨j', k⟩, b⟩ := ψ
  obtain ⟨⟨i, j⟩, a⟩ := γ
  obtain ⟨i', kk⟩ := w
  change (⟨i', (Ψb i').1.p kk⟩ : S.ModelObj (Q.modelBase Ψb)) = ⟨i, a.src⟩ at h₁
  change (⟨j', b.src⟩ : S.ModelObj (Q.modelBase Ψb)) = ⟨j, a.tgt⟩ at h₂
  obtain ⟨rfl, hk⟩ := Sigma.mk.inj_iff.1 h₁
  have hk' : (Ψb i').1.p kk = a.src := eq_of_heq hk
  obtain ⟨rfl, hb⟩ := Sigma.mk.inj_iff.1 h₂
  have hba : b.src = a.tgt := eq_of_heq hb
  have hc := GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt (a := b) (b := a) hba
  have e := modelGroupoid_comp_of (Ψ := Q.modelBase Ψb) b a hc
  have key : ∀ (φ : S.ModelMor (Q.modelBase Ψb))
      (_ : φ = ⟨(i', k), GroupoidStr.TransitionSet.comp b a hc⟩)
      (h : Q.modelP Ψb ⟨i', kk⟩ = Q.modelSrc Ψb φ),
      Q.modelMu Ψb ⟨(φ, ⟨i', kk⟩), h⟩ =
        ⟨k, transAct (GroupoidStr.TransitionSet.comp b a hc) kk hk'⟩ := by
    rintro _ rfl h; rfl
  refine (key _ e _).trans ?_
  exact congrArg (Sigma.mk k) (transAct_comp b a hba kk hk')

/-- **The strong bundle `W_Ψ̄ → X_Ψ` over the ep-groupoid `X_Ψ`** (Definition 8.3.1), the strong
bundle analogue of Theorem 17.1.14 which §17.7 leaves to the reader: the structure map is `t̄`
on every `M(Ψ̄_λ, Ψ̄_λ')`. -/
def modelEpStrongBundle :
    EpStrongBundle (S.modelEpGroupoid (Q.modelBase Ψb)) (Q.modelBundle Ψb) where
  μ := Q.modelMu Ψb
  isStrongBundleMap := Q.isStrongBundleMap_modelMu Ψb
  surjective w := ⟨_, Q.modelMu_unit Ψb w⟩
  isLocalScDiffeo := Q.isLocalScDiffeo_modelMu Ψb
  μ_unit := Q.modelMu_unit Ψb
  μ_comp := Q.modelMu_comp Ψb

/-- **The strong bundle model `W_Ψ̄ → X_Ψ` as an object of `SEP`** (Definition 10.4.11). -/
def modelSEP : SEP.{u} where
  Obj := S.ModelObj (Q.modelBase Ψb)
  Mor := S.ModelMor (Q.modelBase Ψb)
  X := S.modelEpGroupoid (Q.modelBase Ψb)
  W := Q.ModelW Ψb
  P := Q.modelP Ψb
  B := Q.modelBundle Ψb
  E := Q.modelEpStrongBundle Ψb

/-! ### The functor `Γ̄_Ψ̄` -/

/-- `Γ̄(k_λ) = Ψ̄_λ(k_λ)`. -/
def bundleModelObj (w : Q.ModelW Ψb) : V.EObj := (Ψb w.1).1.obj w.2

/-- `P(Γ̄(w)) = Γ_Ψ(P_W(w))`. -/
theorem base_bundleModelObj (w : Q.ModelW Ψb) :
    V.base (Q.bundleModelObj Ψb w) = (S.modelFunctor (Q.modelBase Ψb)).obj (Q.modelP Ψb w) := rfl

/-- `Γ̄(φ, k) = (Γ_Ψ(φ), Γ̄(k))`. -/
def bundleModelMor (q : pullbackSpace (Q.modelP Ψb) (Q.modelSrc Ψb)) : V.EMor :=
  ⟨((S.modelFunctor (Q.modelBase Ψb)).mor q.1.1, Q.bundleModelObj Ψb q.1.2),
    (congrArg (S.modelFunctor (Q.modelBase Ψb)).obj q.2).trans
      ((S.modelFunctor (Q.modelBase Ψb)).src_mor q.1.1).symm⟩

/-- `Γ̄(μ(φ, k)) = μ(Γ_Ψ(φ))(Γ̄(k))` (`obj_transAct` on every piece). -/
theorem bundleModelObj_modelMu (q : pullbackSpace (Q.modelP Ψb) (Q.modelSrc Ψb)) :
    Q.bundleModelObj Ψb (Q.modelMu Ψb q) =
      V.act (Q.bundleModelMor Ψb q).φ (Q.bundleModelMor Ψb q).e (Q.bundleModelMor Ψb q).2 := by
  obtain ⟨⟨j, x⟩, rfl⟩ := (pullbackSigmaEquiv (p := fun i => (Ψb i).1.p) (σ := Prod.fst)
    (s := Q.modelSrcPiece Ψb)).surjective q
  exact obj_transAct x.1.1 x.1.2 x.2

/-- **The functor `Γ̄_Ψ̄ : W_Ψ̄ → E`** (the strong bundle analogue of `Γ_Ψ`, (17.10)):
`k_λ ↦ Ψ̄_λ(k_λ)`, `((q_λ, φ, q_λ'), k) ↦ (φ, Ψ̄_λ(k))`. -/
def bundleModelFunctor :
    GroupoidFunctor (Q.modelEpStrongBundle Ψb).toGroupoidStr V.groupoid where
  obj := Q.bundleModelObj Ψb
  mor := Q.bundleModelMor Ψb
  src_mor _ := rfl
  tgt_mor q := (Q.bundleModelObj_modelMu Ψb q).symm
  mor_comp φ ψ h := by
    have h' : (φ : S.ModelMor (Q.modelBase Ψb) × Q.ModelW Ψb).2 = Q.modelMu Ψb ψ := h
    have hX := EpStrongBundle.src_eq_tgt_of_eq_μ (E := Q.modelEpStrongBundle Ψb) h'
    have hc : V.groupoid.src (Q.bundleModelMor Ψb φ) = V.groupoid.tgt (Q.bundleModelMor Ψb ψ) := by
      change Q.bundleModelObj Ψb φ.1.2 = _
      rw [h']
      exact Q.bundleModelObj_modelMu Ψb ψ
    obtain ⟨h1, h2⟩ := groupoid_comp_of hc
    refine EMor.ext ?_ ?_
    · rw [h1]
      change (S.modelFunctor (Q.modelBase Ψb)).mor
        ((EpStrongBundle.morComp φ ψ : pullbackSpace (Q.modelP Ψb) (Q.modelSrc Ψb)) :
          S.ModelMor (Q.modelBase Ψb) × Q.ModelW Ψb).1 = _
      rw [EpStrongBundle.morComp_val (E := Q.modelEpStrongBundle Ψb) h']
      exact (S.modelFunctor (Q.modelBase Ψb)).mor_comp _ _ hX
    · rw [h2]
      change Q.bundleModelObj Ψb
        ((EpStrongBundle.morComp φ ψ : pullbackSpace (Q.modelP Ψb) (Q.modelSrc Ψb)) :
          S.ModelMor (Q.modelBase Ψb) × Q.ModelW Ψb).2 = _
      rw [EpStrongBundle.morComp_val (E := Q.modelEpStrongBundle Ψb) h']
      rfl
  mor_unit _ := rfl

/-- **`Γ̄` covers `Γ_Ψ`**: `P ∘ Γ̄ = Γ_Ψ ∘ P_W`. -/
theorem proj_comp_bundleModelFunctor :
    V.proj.comp (Q.bundleModelFunctor Ψb) =
      (S.modelFunctor (Q.modelBase Ψb)).comp
        (Q.modelEpStrongBundle Ψb).projFunctor.toGroupoidFunctor :=
  GroupoidFunctor.ext rfl rfl

/-- **The fibre maps of `Γ̄`**: `W_x → P⁻¹(Γ_Ψ(x)) = μ(Γ_Ψ(x))`, Banach space isomorphisms. -/
def bundleModelFiber (x : S.ModelObj (Q.modelBase Ψb)) :
    (Q.modelP Ψb ⁻¹' {x}) ≃L[ℝ] V.V ((S.modelFunctor (Q.modelBase Ψb)).obj x) :=
  (sigmaFiberCLE (fun i => (Ψb i).1.p) x).trans ((Ψb x.1).1.fiber x.2)

/-- The fibre map of `Γ̄` at `x` is `w ↦ Γ̄(w)`. -/
theorem objMk_bundleModelFiber (x : S.ModelObj (Q.modelBase Ψb)) (w : Q.modelP Ψb ⁻¹' {x}) :
    V.objMk _ (Q.bundleModelFiber Ψb x w) = Q.bundleModelObj Ψb w.1 := by
  obtain ⟨⟨i, k⟩, hw⟩ := w
  obtain ⟨i', q⟩ := x
  have hw' : (⟨i, (Ψb i).1.p k⟩ : S.ModelObj (Q.modelBase Ψb)) = ⟨i', q⟩ := hw
  obtain ⟨rfl, hq⟩ := Sigma.mk.inj_iff.1 hw'
  have hq' : (Ψb i).1.p k = q := eq_of_heq hq
  subst hq'
  rfl

/-- `Γ̄` is injective on every fibre of `P_W`. -/
theorem bundleModelObj_injective {w w' : Q.ModelW Ψb} (hP : Q.modelP Ψb w = Q.modelP Ψb w')
    (h : Q.bundleModelObj Ψb w = Q.bundleModelObj Ψb w') : w = w' := by
  obtain ⟨i, k⟩ := w
  obtain ⟨i', k'⟩ := w'
  obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.1 hP
  exact congrArg (Sigma.mk i) ((Ψb i).1.obj_injective h)

/-- **`Γ̄` is full**: a morphism `Ψ̄_λ(k) → Ψ̄_λ'(k')` of `E` lies over a morphism
`Ψ_λ(p k) → Ψ_λ'(p' k')` of `C`, which is `Γ_Ψ(φ)` (Lemma 17.1.15), and `μ(φ, k) = k'` since
`Ψ̄_λ'` is injective (Definition 17.7.2 (2)). -/
theorem bundleModelFunctor_full : (Q.bundleModelFunctor Ψb).toFunctor.Full := by
  refine (GroupoidFunctor.full_iff _).2 fun w w' e hs ht => ?_
  have hs' : e.e = Q.bundleModelObj Ψb w := hs
  have ht' : V.act e.φ e.e e.2 = Q.bundleModelObj Ψb w' := ht
  have hφs : C.toGroupoidStr.src e.φ = (S.modelFunctor (Q.modelBase Ψb)).obj (Q.modelP Ψb w) :=
    e.2.symm.trans (congrArg V.base hs')
  have hφt : C.toGroupoidStr.tgt e.φ = (S.modelFunctor (Q.modelBase Ψb)).obj (Q.modelP Ψb w') :=
    congrArg V.base ht'
  obtain ⟨φ, h₁, h₂, h₃⟩ :=
    (GroupoidFunctor.full_iff _).1 (S.modelFunctor_full (Q.modelBase Ψb)) _ _ e.φ hφs hφt
  let q : pullbackSpace (Q.modelP Ψb) (Q.modelSrc Ψb) := ⟨(φ, w), h₁.symm⟩
  have hm : Q.bundleModelMor Ψb q = e := EMor.ext h₃ hs'.symm
  refine ⟨q, rfl, ?_, hm⟩
  apply Q.bundleModelObj_injective Ψb
  · exact ((Q.modelEpStrongBundle Ψb).P_μ q).trans h₂
  · refine (Q.bundleModelObj_modelMu Ψb q).trans ?_
    rw [hm]
    exact ht'

/-- **`Γ̄` is faithful** (from the faithfulness of `Γ_Ψ`, Lemma 17.1.15). -/
theorem bundleModelFunctor_faithful : (Q.bundleModelFunctor Ψb).toFunctor.Faithful := by
  refine (GroupoidFunctor.faithful_iff _).2 fun q q' hs ht hm => ?_
  have hs' : (q : S.ModelMor (Q.modelBase Ψb) × Q.ModelW Ψb).2 = q'.1.2 := hs
  have ht' : Q.modelMu Ψb q = Q.modelMu Ψb q' := ht
  have hφ : q.1.1 = q'.1.1 := by
    refine (GroupoidFunctor.faithful_iff _).1 (S.modelFunctor_faithful (Q.modelBase Ψb)) _ _ ?_ ?_
      (congrArg EMor.φ hm)
    · exact q.2.symm.trans ((congrArg (Q.modelP Ψb) hs').trans q'.2)
    · exact ((Q.modelEpStrongBundle Ψb).P_μ q).symm.trans
        ((congrArg (Q.modelP Ψb) ht').trans ((Q.modelEpStrongBundle Ψb).P_μ q'))
  exact Subtype.ext (Prod.ext hφ hs')

variable {Q Ψb} in
/-- **`Γ̄` is essentially surjective** for a covering family: `e ∈ E` lies over `α ≅ Γ_Ψ(x)`
(Lemma 17.1.15), and `μ(φ⁻¹)(e)` lies in the image of the fibre `K_{x}` (Definition 17.7.2 (2)). -/
theorem bundleModelFunctor_essSurj (h : S.IsCoveringFamily (Q.modelBase Ψb)) :
    (Q.bundleModelFunctor Ψb).toFunctor.EssSurj := by
  refine (GroupoidFunctor.essSurj_iff _).2 fun e => ?_
  obtain ⟨x, φ, hs, ht⟩ := (GroupoidFunctor.essSurj_iff _).1 (modelFunctor_essSurj h) (V.base e)
  have he : V.base e = C.toGroupoidStr.src (C.toGroupoidStr.inv φ) :=
    ht.symm.trans (C.toGroupoidStr.src_inv φ).symm
  have hb : V.base (V.act (C.toGroupoidStr.inv φ) e he) = (Ψb x.1).1.base.obj x.2 :=
    (C.toGroupoidStr.tgt_inv φ).trans hs
  let w : Q.ModelW Ψb := ⟨x.1, (Ψb x.1).1.lift x.2 _ hb⟩
  have hw : Q.bundleModelObj Ψb w = V.act (C.toGroupoidStr.inv φ) e he := (Ψb x.1).1.obj_lift _ _ hb
  refine ⟨w, ⟨(φ, Q.bundleModelObj Ψb w), (congrArg V.base hw).trans
    (C.toGroupoidStr.tgt_inv φ)⟩, rfl, ?_⟩
  exact (act_congr rfl hw ((congrArg V.base hw).trans (C.toGroupoidStr.tgt_inv φ))
    (C.toGroupoidStr.tgt_inv φ)).trans (act_act_inv φ e he)

/-- `k ↦ |Ψ̄_λ(k)|` is continuous `K_λ → |E|`. -/
theorem continuous_π_bundleObj (Ψ : Q.Unif) :
    Continuous fun k : Ψ.1.K => V.groupoid.π (Ψ.1.obj k) :=
  Ψ.1.isOpenEmbedding_orbitMap.continuous.comp continuous_quot_mk

/-- `k ↦ |Ψ̄_λ(k)|` is open `K_λ → |E|`. -/
theorem isOpenMap_π_bundleObj (Ψ : Q.Unif) :
    IsOpenMap fun k : Ψ.1.K => V.groupoid.π (Ψ.1.obj k) :=
  Ψ.1.isOpenEmbedding_orbitMap.isOpenMap.comp (GroupoidStr.isOpenMap_π_translation fun g =>
    continuousOn_univ.1 (Ψ.1.isStrongBundleMap_smul g).isScSmoothMap.continuousOn)

/-- `|Γ̄|` is continuous. -/
theorem continuous_bundleModelOrbitMap : Continuous (Q.bundleModelFunctor Ψb).orbitMap :=
  (Q.modelEpStrongBundle Ψb).toEpGroupoid.proposition_7_1_8_isOpenQuotientMap.isQuotientMap
    |>.continuous_iff.2
    (continuous_sigma fun i => Q.continuous_π_bundleObj (Ψb i))

/-- `|Γ̄|` is open. -/
theorem isOpenMap_bundleModelOrbitMap : IsOpenMap (Q.bundleModelFunctor Ψb).orbitMap := by
  intro W hW
  have he : (Q.bundleModelFunctor Ψb).orbitMap '' W = ⋃ i, (fun k : (Ψb i).1.K =>
      V.groupoid.π ((Ψb i).1.obj k)) ''
        ((fun k => (Q.modelEpStrongBundle Ψb).toEpGroupoid.π ⟨i, k⟩) ⁻¹' W) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨⟨i, k⟩, rfl⟩ := (Q.modelEpStrongBundle Ψb).toEpGroupoid.surjective_π w
      exact mem_iUnion.2 ⟨i, k, hw, rfl⟩
    · intro hz
      obtain ⟨i, k, hk, rfl⟩ := mem_iUnion.1 hz
      exact ⟨_, hk, rfl⟩
  rw [he]
  exact isOpen_iUnion fun i => Q.isOpenMap_π_bundleObj (Ψb i) _
    (hW.preimage ((Q.modelEpStrongBundle Ψb).toEpGroupoid.continuous_π.comp continuous_sigmaMk))

variable {Q Ψb} in
/-- For a covering family, `Γ̄` is an equivalence of categories. -/
theorem bundleModelFunctor_isEquivalence (h : S.IsCoveringFamily (Q.modelBase Ψb)) :
    (Q.bundleModelFunctor Ψb).toFunctor.IsEquivalence :=
  { faithful := Q.bundleModelFunctor_faithful Ψb, full := Q.bundleModelFunctor_full Ψb,
    essSurj := bundleModelFunctor_essSurj h }

variable {Q Ψb} in
/-- For a covering family, `|Γ̄| : |W_Ψ̄| → |E|` is a homeomorphism. -/
theorem isHomeomorph_bundleModelOrbitMap (h : S.IsCoveringFamily (Q.modelBase Ψb)) :
    IsHomeomorph (Q.bundleModelFunctor Ψb).orbitMap :=
  ⟨Q.continuous_bundleModelOrbitMap Ψb, Q.isOpenMap_bundleModelOrbitMap Ψb,
    GroupoidFunctor.bijective_orbitMap_of_isEquivalence _ (bundleModelFunctor_isEquivalence h)⟩

/-- `|P| ∘ |Γ̄| = |Γ_Ψ| ∘ |P_W|`. -/
theorem orbitMap_proj_comp_bundleModel :
    V.proj.orbitMap ∘ (Q.bundleModelFunctor Ψb).orbitMap =
      (S.modelFunctor (Q.modelBase Ψb)).orbitMap ∘
        (Q.modelEpStrongBundle Ψb).projFunctor.toGroupoidFunctor.orbitMap := by
  funext z
  induction z using Quotient.inductionOn with
  | h w => rfl

/-! ### The packaged statements -/

/-- **The strong bundle analogue of 2021 Theorem 17.1.14** (§17.7, pp. 826–828, left to the
reader): for a family `Ψ̄` of strong bundle uniformizers of `(F̄, M)`, `W_Ψ̄ = ⊔ K_λ → X_Ψ` is a
strong bundle over the ep-groupoid `X_Ψ` of Theorem 17.1.14, whose structure map is `t̄` on every
transition set `M(Ψ̄_λ, Ψ̄_λ')`. -/
theorem theorem_17_1_14_bundle :
    (Q.modelSEP Ψb).X = S.modelEpGroupoid (Q.modelBase Ψb) ∧ (Q.modelSEP Ψb).W = Q.ModelW Ψb ∧
      ∀ (j : ι × ι) (x : Q.TransSpace (Ψb j.1) (Ψb j.2)),
        (Q.modelEpStrongBundle Ψb).μ
            (pullbackSigmaIncl (p := fun i => (Ψb i).1.p) (s := Q.modelSrcPiece Ψb) j x) =
          ⟨j.2, Q.transT (Ψb j.1) (Ψb j.2) x⟩ :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

variable {Q Ψb} in
/-- **The strong bundle analogue of 2021 Lemma 17.1.15** (§17.7, left to the reader): for a
family `Ψ̄` whose base family covers `|C|`, the functor `Γ̄_Ψ̄ : W_Ψ̄ → E` covers `Γ_Ψ`
(`P ∘ Γ̄ = Γ_Ψ ∘ P_W`), is a Banach space isomorphism `W_x → P⁻¹(Γ_Ψ(x))` on every fibre, is an
equivalence of categories, and `|Γ̄| : |W_Ψ̄| → |E|` is a homeomorphism covering
`|Γ_Ψ| : |X_Ψ| → |C|`. -/
theorem lemma_17_1_15_bundle (h : S.IsCoveringFamily (Q.modelBase Ψb)) :
    V.proj.comp (Q.bundleModelFunctor Ψb) =
        (S.modelFunctor (Q.modelBase Ψb)).comp
          (Q.modelEpStrongBundle Ψb).projFunctor.toGroupoidFunctor ∧
      (∀ x (w : Q.modelP Ψb ⁻¹' {x}),
        V.objMk _ (Q.bundleModelFiber Ψb x w) = (Q.bundleModelFunctor Ψb).obj w.1) ∧
      (Q.bundleModelFunctor Ψb).toFunctor.IsEquivalence ∧
      IsHomeomorph (Q.bundleModelFunctor Ψb).orbitMap ∧
      V.proj.orbitMap ∘ (Q.bundleModelFunctor Ψb).orbitMap =
        (S.modelFunctor (Q.modelBase Ψb)).orbitMap ∘
          (Q.modelEpStrongBundle Ψb).projFunctor.toGroupoidFunctor.orbitMap :=
  ⟨Q.proj_comp_bundleModelFunctor Ψb, Q.objMk_bundleModelFiber Ψb,
    bundleModelFunctor_isEquivalence h, isHomeomorph_bundleModelOrbitMap h,
    Q.orbitMap_proj_comp_bundleModel Ψb⟩

end GCT.VectorBundle.StrongPolyfoldBundleConstruction

end Polyfold
