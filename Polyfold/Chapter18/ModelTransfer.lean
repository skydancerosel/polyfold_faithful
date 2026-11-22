import Polyfold.Chapter18.SectionFunctors
import Polyfold.Chapter3.GlobalIFT

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
the chapter introduction (pp. 843–844) and (18.3) (p. 849): **functions on `E` and solution sets
carried to the strong bundle model** `Γ̄_Ψ̄ : W_Ψ̄ → E`, and their independence of the model.
These are the transfer steps the later sections of Chapter 18 use for auxiliary norms
`N : E → [0, ∞]` (Definition 18.1.7, Lemma 18.1.8), sc⁺-multisection functors `Λ : E → ℚ⁺`
(Definition 18.3.1) and the solution set `S_f` (Definition 18.2.1).  Numbers and pages are the
2021 text's.

## The text, paraphrased

(pp. 843–844) Many concepts are carried over using a model `X_Ψ` and `Γ̄_Ψ̄ : W_Ψ̄ → E`; the
relevant properties are those defined through a covering family which do not depend on the
family.  (18.3, p. 849) `|f| = |Γ̄| ∘ |f^Ψ̄_Ψ| ∘ |Γ|⁻¹`, and the solution set `S_f` (the full
subcategory of objects with `f(α) = 0`) corresponds to that of `f^Ψ̄_Ψ`.

## What is formalized (namespace `Polyfold.GCT.VectorBundle`)

* `IsMorInvariant N`: a function `N : E → β` constant along the morphisms of `E`, i.e. a functor
  from `E` into the discrete category `β` (the reading of "a functor `N : E → [0, ∞]`",
  "`Λ : E → ℚ⁺`"); `orbitFun` (`|N| : |E| → β`), `IsMorInvariant.eq_of_isomorphic`.
* `StrongPolyfoldBundleConstruction.bundlePull` (`N ∘ Γ̄_Ψ̄`), `bundlePull_μ`,
  `bundlePull_eq_of_isomorphic` (invariant along the morphisms of `W_Ψ̄`), `bundleOrbitFun`,
  `orbitFun_bundlePull` (`|N ∘ Γ̄| = |N| ∘ |Γ̄|`), `bundlePull_comparison` (**independence of the
  model**: `|N ∘ Γ̄_Ψ̄| = |N ∘ Γ̄_Ψ̄'| ∘ |f̄_{Ψ̄,Ψ̄'}|`), and for covering families
  `bundleOrbitEquiv`, `bundlePush` with `bundlePull_bundlePush`, `bundlePush_bundlePull`,
  `isMorInvariant_bundlePush`: invariant functions on `E` and on `W_Ψ̄` correspond bijectively.
* `act_objMk_zero`, `SectionFunctor.zeroSet` (`S_f`), `isZeroAt_modelSection_iff`
  (`f^Ψ̄_Ψ(x) = 0` iff `f(Γ_Ψ(x)) = 0`), `modelSolutionSet`, `mem_modelSolutionSet_iff`,
  `image_solutionSet_modelSection` (`|Γ_Ψ|(|S_{f^Ψ̄_Ψ}|) = |S_f|`) and `isCompact_zeroSet_iff`
  (**`|S_f|` is compact iff `|S_{f^Ψ̄_Ψ}|` is**, for a covering family).

## Readings

* The categories `[0, ∞]` and `ℚ⁺` are read as discrete (only identities): a functor into them is
  a function constant along morphisms.
* "`f(α) = 0`" is `f(α) = (α, 0)`, the zero of `μ(α)`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u v

namespace GCT.VectorBundle

open GroupoidalCategory GroupoidalCategory.BanachFunctor

variable {C : GCT.{u}} {V : C.VectorBundle} {β : Type v}

/-- **A functor `N : E → β` into a discrete category** (the reading of "functor `N : E → [0, ∞]`"
and "`Λ : E → ℚ⁺`"): `N` is constant along the morphisms of `E`. -/
def IsMorInvariant (N : V.EObj → β) : Prop :=
  ∀ a : V.EMor, N (V.groupoid.tgt a) = N (V.groupoid.src a)

theorem IsMorInvariant.eq_of_isomorphic {N : V.EObj → β} (hN : IsMorInvariant N) {e e' : V.EObj}
    (h : V.groupoid.Isomorphic e e') : N e = N e' := by
  obtain ⟨a, hs, ht⟩ := h
  rw [← hs, ← ht, hN a]

/-- `|N| : |E| → β`. -/
def orbitFun {N : V.EObj → β} (hN : IsMorInvariant N) : V.groupoid.OrbitSpace → β :=
  Quotient.lift N fun _ _ h => hN.eq_of_isomorphic h

@[simp] theorem orbitFun_π {N : V.EObj → β} (hN : IsMorInvariant N) (e : V.EObj) :
    orbitFun hN (V.groupoid.π e) = N e := rfl

/-- `μ(φ)` sends the zero of `μ(α)` to the zero of `μ(t φ)`. -/
theorem act_objMk_zero {φ : C.Mor} {α : C.Obj} (hα : C.toGroupoidStr.src φ = α)
    (h : V.base (V.objMk α 0) = C.toGroupoidStr.src φ) :
    V.act φ (V.objMk α 0) h = V.objMk (C.toGroupoidStr.tgt φ) 0 := by
  subst hα
  change V.objMk _ (V.map φ 0) = _
  rw [map_zero]

namespace SectionFunctor

variable (f : V.SectionFunctor)

/-- **The solution set `S_f`** (p. 849): the objects with `f(α) = 0`. -/
def zeroSet : Set C.Obj := {α | f.toFun α = V.objMk α 0}

end SectionFunctor

namespace StrongPolyfoldBundleConstruction

open StrongBundleUniformizerConstruction StrongBundleUniformizerData PolyfoldConstruction

variable {S : C.PolyfoldConstruction} (Q : V.StrongPolyfoldBundleConstruction S) {ι : Type u}
  (Ψb : ι → Q.Unif)

/-! ### Functions on `E` -/

/-- **The pull-back `N ∘ Γ̄_Ψ̄ : W_Ψ̄ → β`** of a function on `E`. -/
def bundlePull (N : V.EObj → β) (w : Q.ModelW Ψb) : β := N ((Q.bundleModelFunctor Ψb).obj w)

/-- **`N ∘ Γ̄` is invariant along the morphisms of `W_Ψ̄`**: `N(Γ̄(μ(φ, w))) = N(Γ̄(w))`. -/
theorem bundlePull_μ {N : V.EObj → β} (hN : IsMorInvariant N)
    (q : pullbackSpace (Q.modelP Ψb) (S.modelEpGroupoid (Q.modelBase Ψb)).src) :
    Q.bundlePull Ψb N ((Q.modelEpStrongBundle Ψb).μ q) = Q.bundlePull Ψb N q.1.2 := by
  exact (congrArg N ((Q.bundleModelFunctor Ψb).tgt_mor q)).symm.trans
    ((hN _).trans (congrArg N ((Q.bundleModelFunctor Ψb).src_mor q)))

/-- `N ∘ Γ̄` is constant on the isomorphism classes of `W_Ψ̄`. -/
theorem bundlePull_eq_of_isomorphic {N : V.EObj → β} (hN : IsMorInvariant N)
    {w w' : Q.ModelW Ψb}
    (h : (Q.modelEpStrongBundle Ψb).toGroupoidStr.Isomorphic w w') :
    Q.bundlePull Ψb N w = Q.bundlePull Ψb N w' := by
  obtain ⟨a, hs, ht⟩ := h
  rw [← hs, ← ht]
  exact (Q.bundlePull_μ Ψb hN a).symm

/-- `|N ∘ Γ̄| : |W_Ψ̄| → β`. -/
def bundleOrbitFun {N : V.EObj → β} (hN : IsMorInvariant N) :
    (Q.modelEpStrongBundle Ψb).toGroupoidStr.OrbitSpace → β :=
  Quotient.lift (Q.bundlePull Ψb N) fun _ _ h => Q.bundlePull_eq_of_isomorphic Ψb hN h

/-- **`|N ∘ Γ̄| = |N| ∘ |Γ̄|`**. -/
theorem orbitFun_bundlePull {N : V.EObj → β} (hN : IsMorInvariant N) :
    Q.bundleOrbitFun Ψb hN = orbitFun hN ∘ (Q.bundleModelFunctor Ψb).orbitMap := by
  funext z
  induction z using Quotient.inductionOn with | h w => rfl

/-- **Independence of the model**: for covering families `Ψ̄`, `Ψ̄'`,
`|N ∘ Γ̄_Ψ̄| = |N ∘ Γ̄_Ψ̄'| ∘ |f̄_{Ψ̄,Ψ̄'}|` (Theorem 17.1.18, bundle form). -/
theorem bundlePull_comparison {N : V.EObj → β} (hN : IsMorInvariant N)
    (c c' : Q.BundleCoveringFamily) :
    Q.bundleOrbitFun c.Ψ hN =
      Q.bundleOrbitFun c'.Ψ hN ∘ SBLocalization.GenSBMap.orbitMap (Q.bundleComparison c c') := by
  rw [orbitFun_bundlePull, orbitFun_bundlePull]
  funext z
  exact congrArg (orbitFun hN) (congrFun (Q.orbitMap_bundleComparison c c') z).symm

variable {Ψb}

/-- `|Γ̄|` as an equivalence for a covering family. -/
def bundleOrbitEquiv (h : S.IsCoveringFamily (Q.modelBase Ψb)) :
    (Q.modelEpStrongBundle Ψb).toGroupoidStr.OrbitSpace ≃ V.groupoid.OrbitSpace :=
  Equiv.ofBijective _ (isHomeomorph_bundleModelOrbitMap h).bijective

/-- **The push-forward of an invariant function on `W_Ψ̄`** to `E`, for a covering family:
`N(e) = N'(w)` for any `w` with `Γ̄(w) ≅ e`. -/
def bundlePush (h : S.IsCoveringFamily (Q.modelBase Ψb)) (N' : Q.ModelW Ψb → β)
    (hN' : ∀ w w', (Q.modelEpStrongBundle Ψb).toGroupoidStr.Isomorphic w w' → N' w = N' w')
    (e : V.EObj) : β :=
  Quotient.lift N' hN' ((Q.bundleOrbitEquiv h).symm (V.groupoid.π e))

theorem isMorInvariant_bundlePush (h : S.IsCoveringFamily (Q.modelBase Ψb))
    (N' : Q.ModelW Ψb → β)
    (hN' : ∀ w w', (Q.modelEpStrongBundle Ψb).toGroupoidStr.Isomorphic w w' → N' w = N' w') :
    IsMorInvariant (Q.bundlePush h N' hN') := by
  intro a
  unfold bundlePush
  rw [show V.groupoid.π (V.groupoid.tgt a) = V.groupoid.π (V.groupoid.src a) from
    Quotient.sound ⟨V.groupoid.inv a, V.groupoid.src_inv a, V.groupoid.tgt_inv a⟩]

theorem bundlePull_bundlePush (h : S.IsCoveringFamily (Q.modelBase Ψb)) (N' : Q.ModelW Ψb → β)
    (hN' : ∀ w w', (Q.modelEpStrongBundle Ψb).toGroupoidStr.Isomorphic w w' → N' w = N' w') :
    Q.bundlePull Ψb (Q.bundlePush h N' hN') = N' := by
  funext w
  change Quotient.lift N' hN' ((Q.bundleOrbitEquiv h).symm
    ((Q.bundleOrbitEquiv h) ((Q.modelEpStrongBundle Ψb).toGroupoidStr.π w))) = N' w
  rw [Equiv.symm_apply_apply]
  rfl

theorem bundlePush_bundlePull (h : S.IsCoveringFamily (Q.modelBase Ψb)) {N : V.EObj → β}
    (hN : IsMorInvariant N) :
    Q.bundlePush h (Q.bundlePull Ψb N) (fun _ _ h' => Q.bundlePull_eq_of_isomorphic Ψb hN h') =
      N := by
  funext e
  unfold bundlePush
  obtain ⟨z, hz⟩ := (Q.bundleOrbitEquiv h).surjective (V.groupoid.π e)
  rw [← hz, Equiv.symm_apply_apply]
  induction z using Quotient.inductionOn with | h w => ?_
  have hz' : V.groupoid.π ((Q.bundleModelFunctor Ψb).obj w) = V.groupoid.π e := hz
  exact hN.eq_of_isomorphic (Quotient.exact hz')

/-! ### Solution sets -/

variable (Ψb) (f : V.SectionFunctor)

/-- **`f^Ψ̄_Ψ(x) = 0` iff `f(Γ_Ψ(x)) = 0`**: `Γ̄` is a linear isomorphism on the fibres. -/
theorem isZeroAt_modelSection_iff (x : S.ModelObj (Q.modelBase Ψb)) :
    IsZeroAt (Q.modelP Ψb) (Q.modelSection Ψb f) x ↔
      (S.modelFunctor (Q.modelBase Ψb)).obj x ∈ f.zeroSet := by
  have h0 : (Q.bundleModelFunctor Ψb).obj (fiberZero (Q.modelP Ψb) x) =
      V.objMk ((S.modelFunctor (Q.modelBase Ψb)).obj x) 0 := by
    refine (Q.objMk_bundleModelFiber Ψb x 0).symm.trans ?_
    rw [map_zero]
  constructor
  · intro h
    change f.toFun _ = _
    rw [← Q.bundleModelFunctor_obj_modelSection Ψb f x, h, h0]
  · intro h
    refine Q.bundleModelObj_injective Ψb ((Q.isSection_modelSection Ψb f x).trans
      (isSection_fiberZero x).symm) ?_
    change (Q.bundleModelFunctor Ψb).obj _ = (Q.bundleModelFunctor Ψb).obj _
    rw [Q.bundleModelFunctor_obj_modelSection, h0]
    exact h

/-- **The solution set `S_{f^Ψ̄_Ψ}`** of the model section, as a set of objects of `X_Ψ`. -/
def modelSolutionSet : Set (S.ModelObj (Q.modelBase Ψb)) :=
  solutionSet (Q.modelP Ψb) (Q.modelSection Ψb f)

theorem mem_modelSolutionSet_iff (x : S.ModelObj (Q.modelBase Ψb)) :
    x ∈ Q.modelSolutionSet Ψb f ↔ (S.modelFunctor (Q.modelBase Ψb)).obj x ∈ f.zeroSet :=
  Q.isZeroAt_modelSection_iff Ψb f x

/-- **`|Γ_Ψ|(|S_{f^Ψ̄_Ψ}|) = |S_f|`** for a covering family (the solution sets correspond). -/
theorem image_solutionSet_modelSection (h : S.IsCoveringFamily (Q.modelBase Ψb)) :
    (S.modelFunctor (Q.modelBase Ψb)).orbitMap ''
        ((S.modelEP (Q.modelBase Ψb)).X.π '' Q.modelSolutionSet Ψb f) =
      C.toGroupoidStr.π '' f.zeroSet := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, (Q.mem_modelSolutionSet_iff Ψb f x).1 hx, rfl⟩
  · rintro ⟨α, hα, rfl⟩
    obtain ⟨x, φ, hs, ht⟩ := (GroupoidFunctor.essSurj_iff _).1 (modelFunctor_essSurj h) α
    have hiso : C.toGroupoidStr.Isomorphic ((S.modelFunctor (Q.modelBase Ψb)).obj x) α :=
      ⟨φ, hs, ht⟩
    have hx : (S.modelFunctor (Q.modelBase Ψb)).obj x ∈ f.zeroSet := by
      obtain ⟨φ', hs', ht'⟩ := hiso.symm
      have hb : V.base (f.toFun α) = C.toGroupoidStr.src φ' := (f.base_toFun α).trans hs'.symm
      have hα' : f.toFun α = V.objMk α 0 := hα
      change f.toFun _ = _
      rw [f.toFun_eq_act hs' ht' hb, act_congr rfl hα' hb (by rw [← hs']),
        act_objMk_zero hs', ht']
    refine ⟨_, ⟨x, (Q.mem_modelSolutionSet_iff Ψb f x).2 hx, rfl⟩, ?_⟩
    exact Quotient.sound hiso

/-- **`|S_f|` is compact iff `|S_{f^Ψ̄_Ψ}|` is**, for a covering family (`|Γ_Ψ|` is a
homeomorphism, Lemma 17.1.15). -/
theorem isCompact_zeroSet_iff (h : S.IsCoveringFamily (Q.modelBase Ψb)) :
    IsCompact (C.toGroupoidStr.π '' f.zeroSet) ↔
      IsCompact ((S.modelEP (Q.modelBase Ψb)).X.π '' Q.modelSolutionSet Ψb f) := by
  rw [← Q.image_solutionSet_modelSection Ψb f h]
  exact (isHomeomorph_modelOrbitMap h).homeomorph.isCompact_image

end StrongPolyfoldBundleConstruction

end GCT.VectorBundle

end Polyfold
