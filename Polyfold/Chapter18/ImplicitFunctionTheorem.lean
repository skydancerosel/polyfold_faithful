import Polyfold.Chapter18.Linearization
import Polyfold.Chapter15.TameBranched
import Polyfold.Chapter15.ParamFamily
import Polyfold.Chapter17.BranchedSubcategory
import Polyfold.Chapter14.TransportStatement

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.1, pp. 845–846: **Theorem 18.1.5 (implicit function theorem), the Note after it, and
Remark 18.1.6**.

# The implicit function theorem for sc-Fredholm section functors

## The text, paraphrased

(Theorem 18.1.5) Let `P : E → C` be a strong bundle over a tame polyfold and `f` an sc-Fredholm
section functor.  If the smooth object `α` has `f(α) = 0`, `f'(α)` is onto and its kernel is in
good position to the boundary (Remark 17.2.18), there is an open neighbourhood `U` of `|α|` in
`|C|` such that (1) `Θ : C_U → {0, 1}`, `Θ(β) = 1` iff `f(β) = 0`, is a tame orbifold-type
ep⁺-subcategory, and (2) at every `β` of `C_U` with `Θ(β) = 1`, `f'(β)` is onto with kernel in
good position.  (Note) `|supp(Θ)|` is a smooth orbifold with boundary with corners: locally a
smooth manifold divided by a finite group.  The proof is Theorems 15.2.2, 15.2.5 and
Proposition 9.1.9.

(Remark 18.1.6) `Λ : E → {0, 1}`, `1` on the zero vectors, is an sc⁺-multisection functor,
`(f, Λ)` is in good position at `α`, and `Θ = Λ ∘ f`.

## What is formalized

* `VectorBundle.zeroFunctor` (`Λ`), `isMorInvariant_zeroFunctor` (`Λ` is a functor `E → ℚ⁺`),
  `SectionFunctor.zeroIndicator` (`Θ`), `isFunctorial_zeroIndicator`,
  `isOrbifoldTypeBranched_zeroIndicator`, `zeroIndicator_eq_one_iff`.
* **`remark_18_1_6`**: `Λ` is morphism invariant, `Θ = Λ ∘ f`, and in every model `W_Ψ̄ → X_Ψ`
  the pull-back `Λ ∘ Γ̄` is the trivial multisection `Λ₀` of Part III (`zeroMultisection`), an
  sc⁺-multisection; `remark_18_1_6_goodPosition`: `(f^Ψ̄, Λ₀)` is in good position at `x₀`
  (Definition 15.2.4) when `f_Ψ̄` is in good position at `q₀` (the hypothesis of Theorem 18.1.5).
* `surjective_linearization_iff`: `f'(α)` is onto iff `f'_Ψ̄(q₀)` is, for every `Ψ̄ ∈ F̄(α)`.
* **`theorem_18_1_5_model`**: from `theorem_15_2_5_hyp` and `theorem_15_2_5_tame_hyp` applied to
  the model section `f^Ψ̄` and `Λ₀` at `x₀ = (λ, q₀)`: a natural representation `U(x₀)` of
  `G_{x₀}` whose image `U = |Γ|(π(U(x₀)))` is an open neighbourhood of `|α|`; on `U(x₀)`
  `Θ ∘ Γ = Λ₀ ∘ f^Ψ̄`, with a tame local branching structure (Definition 9.3.6) at every point of
  its support and `(f^Ψ̄, Λ₀)` in good position (Definition 15.2.4) there; and (the Note)
  `{y ∈ U(x₀) | f(Γ y) = 0}` is a smooth finite-dimensional submanifold (Definition 4.2.1)
  carrying the action of the finite group `G_{x₀}`.

## Readings

* "`f'(α)` onto with kernel in good position to the boundary" (Remark 17.2.18) is read in a
  strong bundle uniformizer `Ψ̄ ∈ F̄(α)` with `Ψ(q₀) = α`: `f_Ψ̄` is in good position at `q₀`
  in Part I's sense (Definition 3.6.6 in a tame chart, `IsGoodPositionGermTame`).  Its
  surjectivity part matches the text's through `surjective_linearization_iff`
  (`f'(α) = Ψ̄(q₀) ∘ f'_Ψ̄(q₀) ∘ S_Ψ`).
* The full subcategory `C_U` is read through a model: the conclusions are stated on the
  natural representation `U(x₀)` in `X_Ψ` for the family `Ψ̄`, with `U = |Γ|(π(U(x₀)))`.
  "Tame orbifold-type ep⁺-subcategory" is read as: `Θ` takes the values `0` and `1`
  (Definition 17.5.4 (2)) and `Θ ∘ Γ` has a tame local branching structure at every point of its
  support in `U(x₀)` (the local conditions of Definitions 9.1.2 and 9.3.6).
* (2) is read in the model, as good position of `(f^Ψ̄, Λ₀)` (Definition 15.2.4), the
  ep-groupoid statement the text's proof uses.
* The representatives `f_Ψ̄` have germ data in tame charts (`IsScFredholmSectionFunctorTame`,
  `hft`): the standing reading of tame polyfolds (README: the germ data of §§3.6, 6.2, 6.6 and
  12.5 are taken in a tame chart), as in Part III's `theorem_15_3_7_existence`; this is how
  "over a tame polyfold" enters.  It holds for `reflDiag` (`ImplicitFunctionTheoremExamples.lean`).
  The intrinsic form with the text's hypothesis on `f'(α)` is `theorem_18_1_5`
  (`GoodPositionIntrinsic.lean`); `theorem_18_1_5_model` is the form in a model.
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u

/-! ### `subSec f 0 = f` -/

namespace SBLocalization

/-- `f − 0 = f` (`subSec` with the zero section). -/
theorem subSec_fiberZero {A : SEP.{u}} {f : A.Obj → A.W} (hf : IsSection A.P f) (O : Set A.Obj) :
    subSec f (fiberZero A.P) O = f := by
  have he : extendZero O (fiberZero A.P) = fiberZero A.P := by
    funext y
    unfold extendZero
    split_ifs <;> rfl
  unfold subSec
  rw [he, sectionSmul_fiberZero, sectionAdd_fiberZero hf]

end SBLocalization

namespace GCT.VectorBundle

open GroupoidalCategory GroupoidalCategory.BanachFunctor

variable {C : GCT.{u}} {V : C.VectorBundle}

/-! ### `Λ` and `Θ` -/

/-- `μ(φ) e = 0` iff `e = 0`. -/
theorem act_eq_objMk_zero_iff (φ : C.Mor) (e : V.EObj) (h : V.base e = C.toGroupoidStr.src φ) :
    V.act φ e h = V.objMk (C.toGroupoidStr.tgt φ) 0 ↔ e = V.objMk (V.base e) 0 := by
  have hz : V.act φ (V.objMk (V.base e) 0) h = V.objMk (C.toGroupoidStr.tgt φ) 0 :=
    act_objMk_zero h.symm h
  constructor
  · intro he
    exact act_injective h h (he.trans hz.symm)
  · intro he
    exact (act_congr rfl he h h).trans hz

variable (V) in
open Classical in
/-- **The functor `Λ : E → {0, 1}` of Remark 18.1.6** (2021 p. 846): `1` on the zero vectors,
`0` elsewhere. -/
def zeroFunctor : V.EObj → ℚ≥0 := fun e => if e = V.objMk (V.base e) 0 then 1 else 0

/-- **`Λ` is a functor** (constant along the morphisms of `E`). -/
theorem isMorInvariant_zeroFunctor : IsMorInvariant V.zeroFunctor := by
  classical
  intro a
  unfold zeroFunctor
  exact if_congr (act_eq_objMk_zero_iff a.φ a.e a.2) rfl rfl

namespace SectionFunctor

variable (f : V.SectionFunctor)

open Classical in
/-- **The functor `Θ : C → {0, 1}` of Theorem 18.1.5 (1)** (2021 p. 846): `Θ(β) = 1` if
`f(β) = 0` and `Θ(β) = 0` otherwise. -/
def zeroIndicator : C.Obj → ℚ := fun β => if f.toFun β = V.objMk β 0 then 1 else 0

theorem zeroIndicator_eq_one_iff (β : C.Obj) : f.zeroIndicator β = 1 ↔ β ∈ f.zeroSet := by
  unfold zeroIndicator
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun e => absurd e zero_ne_one, fun e => absurd e h⟩

theorem zeroIndicator_pos_iff (β : C.Obj) : 0 < f.zeroIndicator β ↔ β ∈ f.zeroSet := by
  unfold zeroIndicator
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => one_pos⟩
  · exact ⟨fun e => absurd e (lt_irrefl _), fun e => absurd e h⟩

/-- **`Θ = Λ ∘ f`** (Remark 18.1.6). -/
theorem zeroIndicator_eq : f.zeroIndicator = fun β => (V.zeroFunctor (f.toFun β) : ℚ) := by
  funext β
  unfold zeroIndicator zeroFunctor
  rw [f.base_toFun β]
  split_ifs <;> simp

/-- `Θ` is a functor `C → ℚ⁺`. -/
theorem isFunctorial_zeroIndicator : C.toGroupoidStr.IsFunctorial f.zeroIndicator := by
  intro φ
  rw [f.zeroIndicator_eq]
  change ((V.zeroFunctor (f.toFun (C.toGroupoidStr.src φ)) : ℚ≥0) : ℚ) =
    ((V.zeroFunctor (f.toFun (C.toGroupoidStr.tgt φ)) : ℚ≥0) : ℚ)
  rw [f.toFun_tgt φ]
  exact congrArg _ (isMorInvariant_zeroFunctor
    ⟨(φ, f.toFun (C.toGroupoidStr.src φ)), f.base_toFun _⟩).symm

/-- **`Θ` is of orbifold-type** (Definition 17.5.4 (2)): it takes the values `0` and `1`. -/
theorem isOrbifoldTypeBranched_zeroIndicator : C.IsOrbifoldTypeBranched f.zeroIndicator := by
  intro β
  unfold zeroIndicator
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

end SectionFunctor

namespace StrongPolyfoldBundleConstruction

variable {S : C.PolyfoldConstruction} (Q : V.StrongPolyfoldBundleConstruction S) {ι : Type u}
  (Ψb : ι → Q.Unif) (f : V.SectionFunctor)

open SBLocalization

/-- **`Λ ∘ Γ̄ = Λ₀`**: the pull-back of `Λ` to a model `W_Ψ̄ → X_Ψ` is the trivial multisection. -/
theorem bundlePull_zeroFunctor :
    Q.bundlePull Ψb V.zeroFunctor = zeroMultisection (Q.modelSEP Ψb) := by
  classical
  funext w
  set x := Q.modelP Ψb w
  have h0 : (Q.bundleModelFunctor Ψb).obj (fiberZero (Q.modelP Ψb) x) =
      V.objMk ((S.modelFunctor (Q.modelBase Ψb)).obj x) 0 := by
    refine (Q.objMk_bundleModelFiber Ψb x 0).symm.trans ?_
    rw [map_zero]
  have hiff : (Q.bundleModelFunctor Ψb).obj w =
      V.objMk (V.base ((Q.bundleModelFunctor Ψb).obj w)) 0 ↔
        w = fiberZero (Q.modelP Ψb) (Q.modelP Ψb w) := by
    constructor
    · intro h
      refine Q.bundleModelObj_injective Ψb (isSection_fiberZero x).symm ?_
      change (Q.bundleModelFunctor Ψb).obj w = (Q.bundleModelFunctor Ψb).obj _
      rw [h0]
      exact h
    · intro h
      change (Q.bundleModelFunctor Ψb).obj w = V.objMk ((S.modelFunctor (Q.modelBase Ψb)).obj x) 0
      rw [← h0]
      exact congrArg _ h
  unfold bundlePull zeroFunctor zeroMultisection
  exact if_congr hiff rfl rfl

/-- **`Θ ∘ Γ = Λ₀ ∘ f^Ψ̄`** on the objects of a model. -/
theorem zeroIndicator_modelFunctor (x : S.ModelObj (Q.modelBase Ψb)) :
    f.zeroIndicator ((S.modelFunctor (Q.modelBase Ψb)).obj x) =
      (zeroMultisection (Q.modelSEP Ψb) (Q.modelSection Ψb f x) : ℚ) := by
  classical
  have hiff : Q.modelSection Ψb f x =
      fiberZero (Q.modelP Ψb) (Q.modelP Ψb (Q.modelSection Ψb f x)) ↔
        (S.modelFunctor (Q.modelBase Ψb)).obj x ∈ f.zeroSet := by
    rw [Q.isSection_modelSection Ψb f x]
    exact Q.isZeroAt_modelSection_iff Ψb f x
  unfold SectionFunctor.zeroIndicator zeroMultisection
  split_ifs with h1 h2 h2
  · simp
  · exact absurd (hiff.2 h1) h2
  · exact absurd (hiff.1 h2) h1
  · simp

/-- **Remark 18.1.6** (2021 p. 846): `Λ` is a functor `E → {0, 1}`, `Θ = Λ ∘ f`, and in every
model `W_Ψ̄ → X_Ψ` the functor `Λ ∘ Γ̄` is the trivial multisection `Λ₀`, an sc⁺-multisection
(Definition 13.2.1); `Θ ∘ Γ = Λ₀ ∘ f^Ψ̄`. -/
theorem remark_18_1_6 :
    IsMorInvariant V.zeroFunctor ∧
      f.zeroIndicator = (fun β => (V.zeroFunctor (f.toFun β) : ℚ)) ∧
      Q.bundlePull Ψb V.zeroFunctor = zeroMultisection (Q.modelSEP Ψb) ∧
      IsScPlusMultisection (Q.modelSEP Ψb) (Q.bundlePull Ψb V.zeroFunctor) ∧
      ∀ x, f.zeroIndicator ((S.modelFunctor (Q.modelBase Ψb)).obj x) =
        (zeroMultisection (Q.modelSEP Ψb) (Q.modelSection Ψb f x) : ℚ) := by
  refine ⟨isMorInvariant_zeroFunctor, f.zeroIndicator_eq, Q.bundlePull_zeroFunctor Ψb, ?_,
    Q.zeroIndicator_modelFunctor Ψb f⟩
  rw [Q.bundlePull_zeroFunctor Ψb]
  exact isScPlusMultisection_zeroMultisection _

/-! ### Good position in the model -/

variable {Ψb f}

/-- **Good position of `f_Ψ̄` at `q₀` gives good position of the branch `f^Ψ̄ − 0` at
`x₀ = (λ, q₀)`** (Definition 15.2.4 (1), (3) for `Λ₀`): carried along the inclusion of the piece
`K_λ` into `W_Ψ̄` and the restriction of `W_Ψ̄` to `X_Ψ`. -/
theorem isBranchGoodPosition_modelSection {i : ι} {q₀ : (Ψb i).1.base.O}
    (h : (Ψb i).1.B.IsGoodPositionGermTame ((Ψb i).1.localRep f) q₀) :
    IsBranchGoodPosition (A := Q.modelSEP Ψb) (Q.modelSection Ψb f)
      (fiberZero (Q.modelSEP Ψb).P) isOpen_univ ⟨i, q₀⟩ (mem_univ _) := by
  have hsec := Q.isSection_modelSection Ψb f
  have hσ : (Q.modelSEP Ψb).B.IsGoodPositionGermTame (Q.modelSection Ψb f) ⟨i, q₀⟩ := by
    refine (StrongBundle.sigmaMkLocalIso (fun j => (Ψb j).1.B) i q₀).symm.isGoodPositionGermTame
      (StrongBundle.eqOn_sigmaSection (fun j => (Ψb j).1.B) (fun j => (Ψb j).1.localRep f) i q₀)
      ((Ψb i).1.isSection_localRep f) (mem_range_self q₀) ?_
    change (Ψb i).1.B.IsGoodPositionGermTame _
      ((StrongBundle.sigmaMkLocalIso (fun j => (Ψb j).1.B) i q₀).g ⟨i, q₀⟩)
    rwa [StrongBundle.sigmaMkLocalIso_g_mk]
  have : Nonempty (univ : Set (Q.modelSEP Ψb).Obj) := ⟨⟨⟨i, q₀⟩, mem_univ _⟩⟩
  have := (Q.modelSEP Ψb).X.PObj.paracompactSpace_subtype univ
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : ↥(univ : Set (Q.modelSEP Ψb).Obj) →
    (Q.modelSEP Ψb).Obj)) ((Q.modelSEP Ψb).X.PObj.restrictOpen isOpen_univ) (Q.modelSEP Ψb).B
  refine ⟨hsec, ((Q.modelSEP Ψb).B.restrictIso isOpen_univ).isGoodPositionGermTame ?_ hsec
    (mem_univ _) hσ⟩
  intro y _
  have e : (subRestrict (A := Q.modelSEP Ψb) (O := univ) (Q.modelSection Ψb f)
      (fiberZero (Q.modelSEP Ψb).P) hsec y).1.2 = Q.modelSection Ψb f y.1 :=
    congrFun (subSec_fiberZero (A := Q.modelSEP Ψb) hsec univ) y.1
  exact ((Q.modelSEP Ψb).B.restrictIsoInv_snd_self _).symm.trans
    (congrArg ((Q.modelSEP Ψb).B.restrictIsoInv univ) e)

/-- **Remark 18.1.6, "`(f, Λ)` will be in good position at `α`"**, in the model: if `f(α) = 0`
for `α = Ψ_λ(q₀)` and `f_Ψ̄` is in good position at `q₀` (Definition 3.6.6 in a tame chart), then
`(f^Ψ̄, Λ₀)` is in good position at `x₀ = (λ, q₀)` (Definition 15.2.4), with the local section
structure `(0, 1)` on `X_Ψ`.  `hft` is the tame germ data of the standing reading (as in
`theorem_15_2_5_hyp`). -/
theorem remark_18_1_6_goodPosition (hf : Q.IsScFredholmSectionFunctor f)
    (hft : Q.IsScFredholmSectionFunctorTame f) {i : ι} {q₀ : (Ψb i).1.base.O}
    (h0 : (S.modelFunctor (Q.modelBase Ψb)).obj ⟨i, q₀⟩ ∈ f.zeroSet)
    (hgp : (Ψb i).1.B.IsGoodPositionGermTame ((Ψb i).1.localRep f) q₀) :
    SBLocalization.IsGoodPositionAt (A := Q.modelSEP Ψb) (Q.modelSection Ψb f)
      (zeroMultisection (Q.modelSEP Ψb)) ⟨i, q₀⟩ := by
  set A := Q.modelSEP Ψb
  set F := Q.modelSection Ψb f
  set x₀ : A.Obj := ⟨i, q₀⟩
  have hfA : A.E.IsScFredholmSectionFunctor F :=
    (Q.isScFredholmSectionFunctor_model_iff (f := f) (Ψb := Ψb)).2 fun j =>
      (Q.isScFredholmSectionFunctor_iff_unif (f := f)).1 hf (Ψb j)
  have hftA : A.B.IsScFredholmSectionTame F :=
    (Q.isScFredholmSectionTame_model_iff (f := f) (Ψb := Ψb)).2 fun j =>
      (Q.isScFredholmSectionFunctorTame_iff_unif (f := f)).1 hft (Ψb j)
  have hF0 : F x₀ = fiberZero A.P x₀ := (Q.isZeroAt_modelSection_iff Ψb f x₀).2 h0
  have hrep := isLocalRepOn_zeroMultisection (A := A) isOpen_univ
  have hs : IsScPlusSectionOn A (fiberZero A.P) univ := hrep.2.1 0
  have hbr := Q.isBranchGoodPosition_modelSection hgp
  obtain ⟨c₀, hc₀, hxc₀⟩ := StrongBundle.exists_chart_mem A.B x₀
  have hc := StrongBundle.isChart_of_mem A.B hc₀
  have : Nonempty (univ : Set A.Obj) := ⟨⟨x₀, mem_univ _⟩⟩
  have := A.X.PObj.paracompactSpace_subtype univ
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : ↥(univ : Set A.Obj) → A.Obj))
    (A.X.PObj.restrictOpen isOpen_univ) A.B
  obtain ⟨_, hg⟩ : ∃ hF : IsSection A.P F, (A.B.restrictOpen isOpen_univ).IsGoodPositionGermTame
      (subRestrict (O := univ) F (fiberZero A.P) hF) ⟨x₀, mem_univ _⟩ := id hbr
  obtain ⟨V, -, hxV, -, -, hVall⟩ :=
    exists_solutionSet_of_isGoodPosition hftA isOpen_univ hs hc (subset_univ _) hxc₀ hF0 hg
  have hx1 : x₀ ∈ A.X.PObj.levelSet 1 :=
    MPolyfold.smoothSet_subset_levelSet 1 (hVall x₀ hxV hF0).1
  let d : LocalLinData A (zeroMultisection A) (A.X.PObj.levelMk 1 x₀ hx1) :=
    ⟨univ, isOpen_univ, 1, fun _ => fiberZero A.P, fun _ => 1, hrep, c₀, hc, subset_univ _, hxc₀⟩
  have hpos : 0 < zeroMultisection A (F x₀) := by
    classical
    unfold zeroMultisection
    rw [if_pos (by rw [show A.P (F x₀) = x₀ from Q.isSection_modelSection Ψb f x₀]; exact hF0)]
    exact one_pos
  refine ⟨hpos, ⟨hx1, (isOntoAtLevel_iff hfA d).2 fun j hj => ?_⟩, univ, isOpen_univ,
    mem_univ _, 1, _, _, hrep, fun _ _ => hbr⟩
  exact (surjective_toIntr_subDeriv_iff hftA.isScSmooth hs hc (subset_univ _)
    (x := A.X.PObj.levelMk 1 x₀ hx1) hxc₀ hj.symm).2
    ((hVall x₀ hxV hF0).2.2 _ (A.X.PObj.toBase_levelLift c₀.isChart hxc₀ hx1))

/-! ### Surjectivity of `f'(α)` -/

variable (f) in
/-- **`f'(α)` is onto iff `f'_Ψ̄(q₀)` is**, for every `Ψ̄ ∈ F̄(α)` and its point `q₀` over `α`
(`f'(α) = Ψ̄(q₀) ∘ f'_Ψ̄(q₀) ∘ S_Ψ`, with `Ψ̄(q₀)` and `S_Ψ` isomorphisms). -/
theorem surjective_linearization_iff (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj)
    [Fact (S.TangentObj α)] (h0 : f.toFun α = V.objMk α 0) (hne : (Q.F α).Nonempty)
    {Ψ : Q.Unif} (hΨ : Ψ.1 ∈ Q.F α) (x : Ψ.1.base.P.Level 1)
    (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α) :
    Surjective (Q.linearization f hf α h0 hne) ↔
      Surjective (Ψ.1.B.linZeroAt (hf α Ψ.1 hΨ) x (isZeroAt_localRep h0 hx)) := by
  rw [← Q.definition_18_1_3 hf α h0 hne hΨ x hx]
  simp only [sectionLin, LinearMap.coe_comp, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv]
  rw [EquivLike.comp_surjective, EquivLike.comp_surjective, EquivLike.surjective_comp]

/-! ### Theorem 18.1.5 -/

/-- **Theorem 18.1.5 (implicit function theorem), p. 846, in a model**, with tame germ data
(`hft`, the standing reading, as in `theorem_15_2_5_hyp`: the representatives have germ data in
tame charts; the reading of "over a tame polyfold").  The form with the text's intrinsic
hypothesis on `f'(α)` is `theorem_18_1_5` (`GoodPositionIntrinsic.lean`). Let `f` be an sc-Fredholm
section functor, `Ψ̄_λ` a member of a family `Ψ̄` of strong bundle uniformizers and `q₀` a point
with `f(Ψ_λ(q₀)) = 0` at which `f_Ψ̄_λ` is in good position (Definition 3.6.6 in a tame chart: the
reading of "`f'(α)` onto with kernel in good position to the boundary",
`surjective_linearization_iff`). Then there is a natural representation `U(x₀)` of `G_{x₀}` at
`x₀ = (λ, q₀)` in the model `X_Ψ` such that `U = |Γ|(π(U(x₀)))` is an open neighbourhood of `|α|` in
`|C|` and: (1) `Θ` is of orbifold-type, `Θ ∘ Γ = Λ₀ ∘ f^Ψ̄`, and `Θ ∘ Γ` has a tame local branching
structure (Definition 9.3.6) at every point of `U(x₀)` where `f(Γ y) = 0`;
(2) at those points `(f^Ψ̄, Λ₀)` is in good position (Definition 15.2.4: `T(f^Ψ̄, Λ₀)(y)` onto,
branch in good position);
(Note) `{y ∈ U(x₀) | f(Γ y) = 0}` is a smooth finite-dimensional submanifold (Definition 4.2.1),
invariant under the natural action of the finite group `G_{x₀}`. -/
theorem theorem_18_1_5_model (hf : Q.IsScFredholmSectionFunctor f)
    (hft : Q.IsScFredholmSectionFunctorTame f) {i : ι} {q₀ : (Ψb i).1.base.O}
    (h0 : (S.modelFunctor (Q.modelBase Ψb)).obj ⟨i, q₀⟩ ∈ f.zeroSet)
    (hgp : (Ψb i).1.B.IsGoodPositionGermTame ((Ψb i).1.localRep f) q₀) :
    ∃ R : (Q.modelSEP Ψb).X.NaturalRep ⟨i, q₀⟩,
      IsOpen ((S.modelFunctor (Q.modelBase Ψb)).orbitMap ''
        ((S.modelEP (Q.modelBase Ψb)).X.π '' R.U)) ∧
      C.toGroupoidStr.π ((S.modelFunctor (Q.modelBase Ψb)).obj ⟨i, q₀⟩) ∈
        (S.modelFunctor (Q.modelBase Ψb)).orbitMap ''
          ((S.modelEP (Q.modelBase Ψb)).X.π '' R.U) ∧
      C.IsOrbifoldTypeBranched f.zeroIndicator ∧
      (∀ y, f.zeroIndicator ((S.modelFunctor (Q.modelBase Ψb)).obj y) =
        (zeroMultisection (Q.modelSEP Ψb) (Q.modelSection Ψb f y) : ℚ)) ∧
      (∀ y ∈ R.U, (S.modelFunctor (Q.modelBase Ψb)).obj y ∈ f.zeroSet →
        Nonempty ((Q.modelSEP Ψb).X.TameBranchingStructure
          (fun z => f.zeroIndicator ((S.modelFunctor (Q.modelBase Ψb)).obj z)) y)) ∧
      (∀ y ∈ R.U, (S.modelFunctor (Q.modelBase Ψb)).obj y ∈ f.zeroSet →
        SBLocalization.IsGoodPositionAt (A := Q.modelSEP Ψb) (Q.modelSection Ψb f)
          (zeroMultisection (Q.modelSEP Ψb)) y) ∧
      (Q.modelSEP Ψb).X.PObj.IsSmoothSubmanifold
        {y ∈ R.U | (S.modelFunctor (Q.modelBase Ψb)).obj y ∈ f.zeroSet} ∧
      ∀ g, ∀ y ∈ R.U, (S.modelFunctor (Q.modelBase Ψb)).obj y ∈ f.zeroSet →
        (S.modelFunctor (Q.modelBase Ψb)).obj (R.Φ g y) ∈ f.zeroSet := by
  set A := Q.modelSEP Ψb
  set F := Q.modelSection Ψb f
  set x₀ : A.Obj := ⟨i, q₀⟩
  have hfA : A.E.IsScFredholmSectionFunctor F :=
    (Q.isScFredholmSectionFunctor_model_iff (f := f) (Ψb := Ψb)).2 fun j =>
      (Q.isScFredholmSectionFunctor_iff_unif (f := f)).1 hf (Ψb j)
  have hftA : A.B.IsScFredholmSectionTame F :=
    (Q.isScFredholmSectionTame_model_iff (f := f) (Ψb := Ψb)).2 fun j =>
      (Q.isScFredholmSectionFunctorTame_iff_unif (f := f)).1 hft (Ψb j)
  have hΛ := isScPlusMultisection_zeroMultisection A
  have hgpA := Q.remark_18_1_6_goodPosition hf hft h0 hgp
  have hΘ := Q.zeroIndicator_modelFunctor Ψb f
  have hpos : ∀ y, (S.modelFunctor (Q.modelBase Ψb)).obj y ∈ f.zeroSet →
      0 < zeroMultisection A (F y) := fun y hy => by
    have h := (f.zeroIndicator_pos_iff _).2 hy
    rw [hΘ y] at h
    exact_mod_cast h
  -- the local solution set of `f^Ψ̄ = 0` (Part I's Theorem 3.6.8 on `W|X`)
  have hrep := isLocalRepOn_zeroMultisection (A := A) isOpen_univ
  have hs : IsScPlusSectionOn A (fiberZero A.P) univ := hrep.2.1 0
  have hbr := Q.isBranchGoodPosition_modelSection hgp
  obtain ⟨c₀, hc₀, hxc₀⟩ := StrongBundle.exists_chart_mem A.B x₀
  have hc := StrongBundle.isChart_of_mem A.B hc₀
  have : Nonempty (univ : Set A.Obj) := ⟨⟨x₀, mem_univ _⟩⟩
  have := A.X.PObj.paracompactSpace_subtype univ
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : ↥(univ : Set A.Obj) → A.Obj))
    (A.X.PObj.restrictOpen isOpen_univ) A.B
  have hF0 : F x₀ = fiberZero A.P x₀ := (Q.isZeroAt_modelSection_iff Ψb f x₀).2 h0
  obtain ⟨_, hg⟩ : ∃ hF : IsSection A.P F, (A.B.restrictOpen isOpen_univ).IsGoodPositionGermTame
      (subRestrict (O := univ) F (fiberZero A.P) hF) ⟨x₀, mem_univ _⟩ := id hbr
  obtain ⟨V, hVo, hxV, -, hVS, -⟩ :=
    exists_solutionSet_of_isGoodPosition hftA isOpen_univ hs hc (subset_univ _) hxc₀ hF0 hg
  -- Theorem 15.2.5 for `(f^Ψ̄, Λ₀)` at `x₀`
  obtain ⟨R₁, -, -, -, -, -, -, -, -, -, -, -, -, -, h2, -, -, -⟩ :=
    theorem_15_2_5_hyp hfA hftA hΛ hgpA
  obtain ⟨R, hRU, -, -⟩ := A.X.exists_naturalRep_shrink R₁ hVo hxV
  have hzero : ∀ y, (S.modelFunctor (Q.modelBase Ψb)).obj y ∈ f.zeroSet ↔
      F y = fiberZero A.P y := fun y => (Q.isZeroAt_modelSection_iff Ψb f y).symm
  refine ⟨R, S.isOpenMap_modelOrbitMap (Q.modelBase Ψb) _
      ((S.modelEP (Q.modelBase Ψb)).X.proposition_7_1_8 _ R.isOpen_U),
    ⟨_, ⟨x₀, R.mem_U, rfl⟩, rfl⟩, f.isOrbifoldTypeBranched_zeroIndicator, hΘ,
    fun y hy hz => ?_, fun y hy hz => h2 y (hRU hy).2 (hpos y hz), ?_, fun g y hy hz => ?_⟩
  · have e : (fun z => f.zeroIndicator ((S.modelFunctor (Q.modelBase Ψb)).obj z)) =
        fun z => (zeroMultisection A (F z) : ℚ) := funext hΘ
    exact (congrArg (fun Θ => Nonempty (A.X.TameBranchingStructure Θ y)) e).mpr
      (theorem_15_2_5_tame_hyp hfA hftA (h2 y (hRU hy).2 (hpos y hz)))
  · have e : {y ∈ R.U | (S.modelFunctor (Q.modelBase Ψb)).obj y ∈ f.zeroSet} =
        {y ∈ V | F y = fiberZero A.P y} ∩ R.U := by
      ext y
      constructor
      · rintro ⟨hy, hz⟩
        exact ⟨⟨(hRU hy).1, (hzero y).1 hz⟩, hy⟩
      · rintro ⟨⟨-, hz⟩, hy⟩
        exact ⟨hy, (hzero y).2 hz⟩
    rw [e]
    exact hVS.inter_isOpen R.isOpen_U
  · -- `Θ` is constant along the morphism `Γ(g, y) : y → Φ_g(y)` of `X_Ψ`
    have hsrc := R.src_Γ g y hy
    have htgt := R.tgt_Γ g y hy
    have hfun : S.modelPull (Q.modelBase Ψb) f.zeroIndicator y =
        S.modelPull (Q.modelBase Ψb) f.zeroIndicator (R.Φ g y) := by
      have h := PolyfoldConstruction.isFunctorial_modelPull (S := S) (Ψ := Q.modelBase Ψb)
        f.isFunctorial_zeroIndicator (R.Γ g y)
      rwa [show (S.modelEP (Q.modelBase Ψb)).X.src (R.Γ g y) = y from hsrc,
        show (S.modelEP (Q.modelBase Ψb)).X.tgt (R.Γ g y) = R.Φ g y from htgt] at h
    rw [← f.zeroIndicator_pos_iff] at hz ⊢
    change 0 < S.modelPull (Q.modelBase Ψb) f.zeroIndicator (R.Φ g y)
    rw [← hfun]
    exact hz

end StrongPolyfoldBundleConstruction

end GCT.VectorBundle

end Polyfold
