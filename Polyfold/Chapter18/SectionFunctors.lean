import Polyfold.Chapter17.BundleModelComparison
import Polyfold.Chapter10.FredholmEquivalence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18
"Fredholm Theory in Polyfolds", the chapter introduction, pp. 843–844: **section functors of
`P : E → C`, their local representatives `f_Ψ̄ : O → K`, and their pull-backs `f^Ψ̄_Ψ` to the
strong bundle model `W_Ψ̄ → X_Ψ`**.  Numbers and pages are the 2021 text's.

# Section functors and their representatives

## The text, paraphrased

(pp. 843–844) `C` is a GCT with a polyfold structure `(F, M)`, `μ : C → Ban` defines the bundle
`P : E → C`, and `E` carries a strong bundle structure `(F̄, M)` (Definition 17.7.4).  Many
concepts are carried over using an sc-smooth model `X_Ψ` with the equivalence `Γ_Ψ : X_Ψ → C` and
its bundle version `Γ̄_Ψ̄ : W_Ψ̄ → E`, or, more locally, the diagrams `G ⋉ K → E` over
`G ⋉ O → C` for `Ψ̄ ∈ F̄(α)` covering `Ψ ∈ F(α)`.  "If `f : C → E` is a section functor, we obtain
for every choice `Ψ̄` a local representative `f_Ψ̄ : O → K`, which satisfies `Ψ̄ ∘ f_Ψ̄ = f ∘ Ψ`
and which is `G`-equivariant."  The relevant properties are those defined by requirements on
`(f_Ψ̄)` for `Ψ̄` in a covering family which do not depend on the family.

## What is formalized

* `GCT.VectorBundle.SectionFunctor` (a section functor of `P : E → C`), its functor
  `toGroupoidFunctor : C → E` with `P ∘ f = Id` (`proj_obj_toGroupoidFunctor`,
  `proj_mor_toGroupoidFunctor`).
* `StrongBundleUniformizerData.localRep` (`f_Ψ̄`), `isSection_localRep`, `obj_localRep`
  (`Ψ̄ ∘ f_Ψ̄ = f ∘ Ψ`), `localRep_eq_iff` (it is the only such map), `localRep_smul`
  (`G`-equivariance), `localRep_transAct` (the representatives of two uniformizers are related by
  the transition maps `T` of `M(Ψ̄, Ψ̄')`, p. 828).
* `StrongPolyfoldBundleConstruction.modelSection` (**the pull-back `f^Ψ̄_Ψ : X_Ψ → W_Ψ̄` of `f` by
  `Γ̄_Ψ̄`**), `isSection_modelSection`, `bundleModelFunctor_obj_modelSection`
  (`Γ̄_Ψ̄ ∘ f^Ψ̄_Ψ = f ∘ Γ_Ψ`), `modelSection_eq_of` (the only such section),
  `isFunctorialSection_modelSection` (a section functor of `W_Ψ̄ → X_Ψ`, Definition 8.3.4),
  `modelSection_comp_incl` (pull-back along the inclusions of model families) and
  `pullback_modelSection` (`i^*(f^Φ̄) = f^Ψ̄` for the strong bundle equivalence `i : W_Ψ̄ → W_Φ̄`).
* **The orbit identity (18.3)** `orbitMap_modelSection`: `|f| ∘ |Γ_Ψ| = |Γ̄_Ψ̄| ∘ |f^Ψ̄_Ψ|`, so
  `|f| = |Γ̄| ∘ |f^Ψ̄_Ψ| ∘ |Γ|⁻¹` for covering families.

## Readings

* "Section functor" is read as a functor `f : C → E` with `P ∘ f = Id_C`; such a functor is
  determined by its object map, `f(φ) = (φ, f(s(φ)))`, and the condition on the object map is
  `f(t φ) = μ(φ)(f(s φ))`; the structure records the object map and this condition.
* `f_Ψ̄(q)` is the unique `k ∈ K_q` with `Ψ̄(k) = f(Ψ(q))` (Definition 17.7.2 (2): `Ψ̄` is a
  Banach space isomorphism `K_q → P⁻¹(Ψ(q))`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace GCT.VectorBundle

open GroupoidalCategory GroupoidalCategory.BanachFunctor

variable {C : GCT.{u}} (V : C.VectorBundle)

/-- **A section functor of `P : E → C`** (2021 p. 844): an object map `f : C → E` with
`P(f(α)) = α` which is functorial, `f(t φ) = μ(φ)(f(s φ))`.  The functor `C → E` is
`toGroupoidFunctor`. -/
structure SectionFunctor : Type u where
  /-- The object map `α ↦ f(α) ∈ P⁻¹(α)`. -/
  toFun : C.Obj → V.EObj
  /-- `P ∘ f = Id` on objects. -/
  base_toFun : ∀ α, V.base (toFun α) = α
  /-- Functoriality: `f(t φ) = μ(φ)(f(s φ))`. -/
  toFun_tgt : ∀ φ : C.Mor, toFun (C.toGroupoidStr.tgt φ) =
    V.act φ (toFun (C.toGroupoidStr.src φ)) (base_toFun _)

namespace SectionFunctor

variable {V} (f : V.SectionFunctor)

/-- The morphism `f(φ) = (φ, f(s φ)) : f(s φ) → f(t φ)`. -/
def morMap (φ : C.Mor) : V.EMor := ⟨(φ, f.toFun (C.toGroupoidStr.src φ)), f.base_toFun _⟩

/-- **The functor `f : C → E`** of a section functor. -/
def toGroupoidFunctor : GroupoidFunctor C.toGroupoidStr V.groupoid where
  obj := f.toFun
  mor := f.morMap
  src_mor _ := rfl
  tgt_mor φ := (f.toFun_tgt φ).symm
  mor_comp φ ψ h := by
    have hc : V.groupoid.src (f.morMap φ) = V.groupoid.tgt (f.morMap ψ) := by
      change f.toFun (C.toGroupoidStr.src φ) = _
      rw [h]; exact f.toFun_tgt ψ
    obtain ⟨h1, h2⟩ := groupoid_comp_of hc
    refine EMor.ext h1.symm ?_
    rw [h2]
    change f.toFun (C.toGroupoidStr.src (C.toGroupoidStr.comp φ ψ)) = _
    rw [C.toGroupoidStr.src_comp φ ψ h]
    rfl
  mor_unit α := by
    refine EMor.ext ?_ ?_
    · change C.toGroupoidStr.unit α = C.toGroupoidStr.unit (V.base (f.toFun α))
      rw [f.base_toFun]
    · change f.toFun (C.toGroupoidStr.src (C.toGroupoidStr.unit α)) = f.toFun α
      rw [C.toGroupoidStr.src_unit]

/-- `P ∘ f = Id` on objects. -/
theorem proj_obj_toGroupoidFunctor (α : C.Obj) : V.proj.obj (f.toGroupoidFunctor.obj α) = α :=
  f.base_toFun α

/-- `P ∘ f = Id` on morphisms. -/
theorem proj_mor_toGroupoidFunctor (φ : C.Mor) : V.proj.mor (f.toGroupoidFunctor.mor φ) = φ :=
  rfl

/-- The functorial condition with an arbitrary proof term. -/
theorem toFun_tgt' (φ : C.Mor) (h : V.base (f.toFun (C.toGroupoidStr.src φ)) =
    C.toGroupoidStr.src φ) :
    f.toFun (C.toGroupoidStr.tgt φ) = V.act φ (f.toFun (C.toGroupoidStr.src φ)) h :=
  f.toFun_tgt φ

/-- `f(α') = μ(φ)(f(α))` for `φ : α → α'`. -/
theorem toFun_eq_act {φ : C.Mor} {α α' : C.Obj} (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (h : V.base (f.toFun α) = C.toGroupoidStr.src φ) :
    f.toFun α' = V.act φ (f.toFun α) h := by
  subst hs ht
  exact f.toFun_tgt φ

end SectionFunctor

/-! ### Local representatives -/

namespace StrongBundleUniformizerData

variable {V} (Ψ : V.StrongBundleUniformizerData) (f : V.SectionFunctor)

/-- **The local representative `f_Ψ̄ : O → K`** (2021 p. 844): `f_Ψ̄(q)` is the point of `K_q`
with `Ψ̄(f_Ψ̄(q)) = f(Ψ(q))`. -/
def localRep (q : Ψ.base.O) : Ψ.K := Ψ.lift q (f.toFun (Ψ.base.obj q)) (f.base_toFun _)

/-- `f_Ψ̄` is a section of `p : K → O`. -/
theorem p_localRep (q : Ψ.base.O) : Ψ.p (Ψ.localRep f q) = q := Ψ.p_lift _ _ _

/-- `f_Ψ̄` is a section of `p : K → O`. -/
theorem isSection_localRep : IsSection Ψ.p (Ψ.localRep f) := Ψ.p_localRep f

/-- **`Ψ̄ ∘ f_Ψ̄ = f ∘ Ψ`** (2021 p. 844). -/
theorem obj_localRep (q : Ψ.base.O) : Ψ.obj (Ψ.localRep f q) = f.toFun (Ψ.base.obj q) :=
  Ψ.obj_lift _ _ _

/-- `f_Ψ̄(q)` is the only `k` with `Ψ̄(k) = f(Ψ(q))`. -/
theorem localRep_eq_iff (q : Ψ.base.O) (k : Ψ.K) :
    Ψ.localRep f q = k ↔ Ψ.obj k = f.toFun (Ψ.base.obj q) :=
  Ψ.lift_eq_iff _ k

/-- **`f_Ψ̄` is `G`-equivariant** (2021 p. 844): `f_Ψ̄(g ∗ q) = g ∗ f_Ψ̄(q)`. -/
theorem localRep_smul (g : Ψ.base.G) (q : Ψ.base.O) :
    Ψ.localRep f (g • q) = g • Ψ.localRep f q := by
  rw [localRep_eq_iff]
  refine (Ψ.obj_smul' g (Ψ.localRep f q)).symm.trans ?_
  have hp := Ψ.p_localRep f q
  have hφs : C.toGroupoidStr.src (Ψ.base.mor (g, q)) = Ψ.base.obj q :=
    Ψ.base.functor.src_mor (g, q)
  have hφt : C.toGroupoidStr.tgt (Ψ.base.mor (g, q)) = Ψ.base.obj (g • q) :=
    Ψ.base.functor.tgt_mor (g, q)
  refine (act_congr (by rw [hp]) (Ψ.obj_localRep f q) _
    ((f.base_toFun _).trans hφs.symm)).trans ?_
  exact (f.toFun_eq_act hφs hφt _).symm

variable {Ψ' : V.StrongBundleUniformizerData}

/-- **The representatives of two uniformizers are related by the transition maps** (p. 828):
for `a = (q, φ, q') ∈ M(Ψ, Ψ')`, `f_Ψ̄'(q') = T(a, f_Ψ̄(q))`. -/
theorem localRep_transAct (a : Ψ.base.Trans Ψ'.base) :
    Ψ'.localRep f a.tgt = transAct a (Ψ.localRep f a.src) (Ψ.p_localRep f a.src) := by
  refine (localRep_eq_iff _ f _ _).2 ?_
  rw [obj_transAct]
  refine (act_congr rfl (Ψ.obj_localRep f a.src) _
    ((f.base_toFun _).trans a.src_mor.symm)).trans ?_
  exact (f.toFun_eq_act a.src_mor a.tgt_mor _).symm

end StrongBundleUniformizerData

/-! ### The pull-back to the strong bundle model -/

namespace StrongPolyfoldBundleConstruction

open StrongBundleUniformizerConstruction StrongBundleUniformizerData PolyfoldConstruction

variable {S : C.PolyfoldConstruction} (Q : V.StrongPolyfoldBundleConstruction S) {ι : Type u}
  (Ψb : ι → Q.Unif) {V} (f : V.SectionFunctor)

/-- **The pull-back `f^Ψ̄_Ψ : X_Ψ → W_Ψ̄` of `f` by `Γ̄_Ψ̄`** (2021 Remark 18.1.2 (a), p. 844):
`(λ, q) ↦ (λ, f_{Ψ̄_λ}(q))`. -/
def modelSection (x : S.ModelObj (Q.modelBase Ψb)) : Q.ModelW Ψb :=
  ⟨x.1, (Ψb x.1).1.localRep f x.2⟩

@[simp] theorem modelSection_mk (i : ι) (q : (Ψb i).1.base.O) :
    Q.modelSection Ψb f ⟨i, q⟩ = ⟨i, (Ψb i).1.localRep f q⟩ := rfl

/-- `f^Ψ̄_Ψ` is a section of `W_Ψ̄ → X_Ψ`. -/
theorem isSection_modelSection : IsSection (Q.modelP Ψb) (Q.modelSection Ψb f) := by
  rintro ⟨i, q⟩
  change (⟨i, (Ψb i).1.p ((Ψb i).1.localRep f q)⟩ : S.ModelObj (Q.modelBase Ψb)) = ⟨i, q⟩
  rw [p_localRep]

/-- **`Γ̄_Ψ̄ ∘ f^Ψ̄_Ψ = f ∘ Γ_Ψ`**. -/
theorem bundleModelFunctor_obj_modelSection (x : S.ModelObj (Q.modelBase Ψb)) :
    (Q.bundleModelFunctor Ψb).obj (Q.modelSection Ψb f x) =
      f.toFun ((S.modelFunctor (Q.modelBase Ψb)).obj x) :=
  (Ψb x.1).1.obj_localRep f x.2

/-- `f^Ψ̄_Ψ` is the only section `s` of `W_Ψ̄ → X_Ψ` with `Γ̄_Ψ̄ ∘ s = f ∘ Γ_Ψ`. -/
theorem modelSection_eq_of {s : S.ModelObj (Q.modelBase Ψb) → Q.ModelW Ψb}
    (hs : IsSection (Q.modelP Ψb) s)
    (h : ∀ x, (Q.bundleModelFunctor Ψb).obj (s x) =
      f.toFun ((S.modelFunctor (Q.modelBase Ψb)).obj x)) :
    s = Q.modelSection Ψb f := by
  funext x
  exact Q.bundleModelObj_injective Ψb ((hs x).trans (Q.isSection_modelSection Ψb f x).symm)
    ((h x).trans (Q.bundleModelFunctor_obj_modelSection Ψb f x).symm)

/-- **`f^Ψ̄_Ψ` is a section functor** of the strong bundle `W_Ψ̄ → X_Ψ` over the ep-groupoid `X_Ψ`
(Definition 8.3.4): `f^Ψ̄_Ψ(t φ) = μ(φ, f^Ψ̄_Ψ(s φ))`. -/
theorem isFunctorialSection_modelSection :
    (Q.modelEpStrongBundle Ψb).IsFunctorialSection (Q.isSection_modelSection Ψb f) := by
  intro φ
  set Γ := S.modelFunctor (Q.modelBase Ψb)
  let q : pullbackSpace (Q.modelP Ψb) (S.modelEpGroupoid (Q.modelBase Ψb)).src :=
    ⟨(φ, Q.modelSection Ψb f ((S.modelEpGroupoid (Q.modelBase Ψb)).src φ)),
      Q.isSection_modelSection Ψb f ((S.modelEpGroupoid (Q.modelBase Ψb)).src φ)⟩
  change Q.modelSection Ψb f _ = (Q.modelEpStrongBundle Ψb).μ q
  refine Q.bundleModelObj_injective Ψb ?_ ?_
  · exact (Q.isSection_modelSection Ψb f _).trans ((Q.modelEpStrongBundle Ψb).P_μ q).symm
  · change (Q.bundleModelFunctor Ψb).obj _ = Q.bundleModelObj Ψb (Q.modelMu Ψb q)
    rw [Q.bundleModelFunctor_obj_modelSection]
    refine Eq.trans ?_ (Q.bundleModelObj_modelMu Ψb q).symm
    have he : (Q.bundleModelMor Ψb q).e = f.toFun (C.toGroupoidStr.src (Γ.mor φ)) := by
      change (Q.bundleModelFunctor Ψb).obj (Q.modelSection Ψb f _) = _
      rw [Q.bundleModelFunctor_obj_modelSection]
      exact congrArg f.toFun (Γ.src_mor φ).symm
    refine Eq.trans ?_ (act_congr rfl he.symm ((f.base_toFun _)) _)
    rw [← f.toFun_tgt (Γ.mor φ)]
    exact congrArg f.toFun (Γ.tgt_mor φ).symm

/-- **The orbit identity (18.3)**: `|f| ∘ |Γ_Ψ| = |Γ̄_Ψ̄| ∘ |f^Ψ̄_Ψ|` on `|X_Ψ|`. -/
theorem orbitMap_modelSection (x : S.ModelObj (Q.modelBase Ψb)) :
    V.groupoid.π (f.toFun ((S.modelFunctor (Q.modelBase Ψb)).obj x)) =
      (Q.bundleModelFunctor Ψb).orbitMap
        ((Q.modelEpStrongBundle Ψb).toEpGroupoid.π (Q.modelSection Ψb f x)) := by
  rw [← Q.bundleModelFunctor_obj_modelSection Ψb f x]
  rfl

/-! ### Pull-back along inclusions of families -/

variable {Ψb} {κ : Type u} {Φb : ι → Q.Unif} {Ψb' : κ → Q.Unif} {σ : κ → ι}

/-- The inclusion `i : W_Ψ̄ → W_Φ̄` for `Ψ̄ = Φ̄ ∘ σ` maps `f^Ψ̄` to `f^Φ̄`:
`i(f^Ψ̄(x)) = f^Φ̄(i(x))`. -/
theorem modelSection_comp_incl (h : Φb ∘ σ = Ψb') (x : S.ModelObj (Q.modelBase Ψb')) :
    (SEP.Hom.Φ (Q.bundleIncl Ψb' Φb σ h)).obj (Q.modelSection Ψb' f x) =
      Q.modelSection Φb f ((SEP.Hom.ϕ (Q.bundleIncl Ψb' Φb σ h)).obj x) := by
  subst h
  rfl

variable (Φb) in
/-- **The pull-back of `f^Φ̄` along the inclusion `i : W_Ψ̄ → W_Φ̄` is `f^Ψ̄`** (for a family
whose base family covers, so that `i` is a strong bundle equivalence). -/
theorem pullback_modelSection (h : Φb ∘ σ = Ψb') (hc : S.IsCoveringFamily (Q.modelBase Ψb')) :
    (SBLocalization.sbe (Q.equivalences_bundleIncl h hc)).pullback (Q.modelSection Φb f) =
      Q.modelSection Ψb' f := by
  funext x
  exact (SBLocalization.sbe (Q.equivalences_bundleIncl h hc)).pullback_eq
    (Q.isSection_modelSection Φb f) (Q.isSection_modelSection Ψb' f x)
    (Q.modelSection_comp_incl f h x)

variable (Φb) in
/-- **The push-forward of `f^Ψ̄` along the inclusion `i : W_Ψ̄ → W_Φ̄` is `f^Φ̄`**. -/
theorem pushforward_modelSection (h : Φb ∘ σ = Ψb') (hc : S.IsCoveringFamily (Q.modelBase Ψb')) :
    (SBLocalization.sbe (Q.equivalences_bundleIncl h hc)).pushforward (Q.modelSection Ψb' f) =
      Q.modelSection Φb f := by
  rw [← Q.pullback_modelSection f Φb h hc]
  exact (SBLocalization.sbe (Q.equivalences_bundleIncl h hc)).pushforward_pullback
    (Q.isSection_modelSection Φb f) (Q.isFunctorialSection_modelSection Φb f)

end StrongPolyfoldBundleConstruction

end GCT.VectorBundle

end Polyfold
