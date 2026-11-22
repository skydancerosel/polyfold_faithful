import Polyfold.Chapter17.TangentTransition
import Polyfold.Chapter4.BoundaryFormsAgreement
import Polyfold.Chapter4.BracketLevel

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.2 (p. 773): **Lemma 17.2.10** without the continuity of `Ψ̂`.  Numbers and pages are the 2021
text's.

# The tangent uniformizer on morphisms

## The text, paraphrased

(Lemma 17.2.10, p. 773) `TΨ : G ⋉ TO → TC`, `h ↦ TΨ(h)`, `(g, h) ↦ (TΨ(h), Ψ(g, q),
T(Ψ(g, q))TΨ(h))`, `q = τ(h)`, is a well-defined functor; in particular `TΨ(g ∗ h) =
T(Ψ(g, q))(TΨ(h))` (17.40).

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* `transMap_eq_tangentMap_of_section`: `Tσ_a = Tτ` over `s(a)` for a continuous section `f` of `s`
  through `a` with `t ∘ f = τ` sc-smooth.
* `tangentUnifMor_tgt` (for every `Ψ`): the target of `TΨ(g, h)` is `TΨ(Tσ(h))`, `σ` the
  sc-diffeomorphism of `Ψ̂(g, q)`.
* The witness: `(ℤ/2 × ℤ/2) ⋉ ℝ`, acting through the first factor (`fstSwapAction`), with
  `M(Ψ, Ψ)` twisted by exchanging the two factors over `0` (`fstSwapTwist`,
  `fstSwapConstruction`, `fstSwapConstruction_hasUniformizers`); the vector `(0, 1)` of `T_0ℝ`
  (`fstSwapTangent`) and `T(y ↦ ∓y)` on it (`tangentChartMap_tangentMap_neg`, `_one`);
  `fstSwap_transMap_hat` (`Tσ = T(y ↦ −y)` for `Ψ̂((1, −1), 0)`).
* **`not_lemma_17_2_10`**: Lemma 17.2.10 does not hold as we read it without the continuity of
  `Ψ̂`; for continuous `Ψ̂` it holds (`lemma_17_2_10_of_continuous` in `TangentCategory.lean`).

## Readings

* We read Lemma 17.2.10 as the statement that the target of `TΨ(g, h)` is `TΨ(g ∗ h)` for every
  `g` and `h`, i.e. that `TΨ` is a functor `G ⋉ TO → TC`.  The text's proof uses
  `σ = (g ∗ ·)` near `q` for `Ψ̂(g, q)`; this is the place where the continuity of `Ψ̂` enters
  (`transMap_hat_of_continuous`).  In the witness, `Ψ̂((1, −1), 0)` lies on the sheet
  `p ↦ (p, (−1, 1), −p)`, so its `σ` is `y ↦ −y` while `(1, −1) ∗ ·` is the identity.
-/

open Set Function

universe u

namespace Polyfold

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction}

/-- **`Tσ_a = Tτ` over `s(a)`** for a continuous section `f` of `s` through `a` with `t ∘ f = τ`
sc-smooth. -/
theorem transMap_eq_tangentMap_of_section {Ψ Ψ' : S.Unif} (a : S.Tr Ψ Ψ')
    {f : Ψ.1.O → S.Tr Ψ Ψ'} (hf : Continuous f) (hfs : ∀ p, (f p).src = p) (hfa : f a.src = a)
    {τ : Ψ.1.O → Ψ'.1.O} (hτ : Ψ.1.P.IsScSmoothMap Ψ'.1.P τ) (hfτ : ∀ p, (f p).tgt = τ p)
    {k : Ψ.1.P.TangentSpace} (hk : basePt Ψ k = a.src) :
    S.transMap a k = MPolyfold.tangentMap hτ k := by
  obtain ⟨W', hW'o, hqW', hW'sub, hW'eq⟩ := (S.triple a).exists_srcInv_eq (f := f) isOpen_univ
    (mem_univ _) hf.continuousOn (fun p _ => hfs p) hfa
  have hσ : EqOn (S.triple a).sigma τ W' := fun p hp => by
    change ((S.triple a).srcInv p).tgt = τ p
    rw [hW'eq p hp]; exact hfτ p
  have hmem : k ∈ Ψ.1.P.tangentPreimage W' := by
    rw [MPolyfold.mem_tangentPreimage]
    have h' : basePt Ψ k ∈ W' := hk ▸ hqW'
    exact h'
  exact (MPolyfold.tangentMapOn_congr (S.triple a).isScSmoothOn_sigma hτ hW'o
    (fun p hp => (hW'sub hp).2) (subset_univ _) hσ hmem).trans
    (congrFun (MPolyfold.tangentMapOn_univ hτ) k)

/-- **The target of `TΨ(g, h)`, for every `Ψ`** (2021 (17.39), (17.40)): it is
`TΨ(Tσ(h))`, `σ` the sc-diffeomorphism of `Ψ̂(g, q)`, `q = τ(h)`. -/
theorem tangentUnifMor_tgt (hU : S.HasUniformizers) (Ψ : S.Unif)
    (p : ULift.{1} Ψ.1.G × Ψ.1.P.TangentSpace) :
    (S.tangentUnifMor hU Ψ p).tgt =
      S.tangentUnifObj hU Ψ (S.transMap (S.hat Ψ (p.1.down, basePt Ψ p.2)) p.2) := by
  obtain ⟨g, k⟩ := p
  have hq : basePt Ψ (S.transMap (S.hat Ψ (g.down, basePt Ψ k)) k) = g.down • basePt Ψ k :=
    base_transMap _ rfl
  have hb : C.toGroupoidStr.tgt (Ψ.1.mor (g.down, basePt Ψ k)) =
      Ψ.1.obj (basePt Ψ (S.transMap (S.hat Ψ (g.down, basePt Ψ k)) k)) :=
    (Ψ.1.tgt_mor _).trans (congrArg Ψ.1.obj hq.symm)
  refine TangentCatObj.ext_of hb ?_
  have h₂ : C.toGroupoidStr.comp (C.toGroupoidStr.comp
      (C.toGroupoidStr.unit (Ψ.1.obj (basePt Ψ (S.transMap (S.hat Ψ (g.down, basePt Ψ k)) k))))
        (Ψ.1.mor (g.down, basePt Ψ k)))
      (C.toGroupoidStr.unit (Ψ.1.obj (basePt Ψ k))) =
      C.toGroupoidStr.comp
        (C.toGroupoidStr.unit (Ψ.1.obj (basePt Ψ (S.transMap (S.hat Ψ (g.down, basePt Ψ k)) k))))
        (Ψ.1.mor (g.down, basePt Ψ k)) :=
    GroupoidStr.comp_unit_of_eq ((C.toGroupoidStr.src_comp _ _
      ((C.toGroupoidStr.src_unit _).trans hb.symm)).trans (Ψ.1.src_mor _))
  exact transMap_three_eq
    (S.refUnitTr (S.tangentUnifMor hU Ψ (g, k)).isObj_tgt
      (tangentObj_of_unif hU Ψ (S.transMap (S.hat Ψ (g.down, basePt Ψ k)) k)) hb)
    (S.refTr (tangentObj_of_unif hU Ψ k) (S.tangentUnifMor hU Ψ (g, k)).isObj_tgt
      (Ψ.1.mor (g.down, basePt Ψ k)) (Ψ.1.src_mor _) rfl)
    (S.unitTr (basePt Ψ k) (S.refQ (tangentObj_of_unif hU Ψ k)) rfl (obj_refPoint _))
    (S.unitTr (basePt Ψ (S.transMap (S.hat Ψ (g.down, basePt Ψ k)) k))
      (S.refQ (tangentObj_of_unif hU Ψ (S.transMap (S.hat Ψ (g.down, basePt Ψ k)) k))) rfl
      (obj_refPoint _))
    (S.hat Ψ (g.down, basePt Ψ k)) rfl rfl hq rfl h₂ rfl rfl

/-! ### The counterexample -/

noncomputable section SwapTwist

open EpGroupoid.Examples MPolyfold

/-- `ℤ/2 × ℤ/2` acting on `ℝ` through the first factor, `(u, v) ∗ y = u y`. -/
@[reducible] def fstSwapAction : MulAction (ℤˣ × ℤˣ) (Fin 1 → ℝ) :=
  MulAction.compHom _ (MonoidHom.fst ℤˣ ℤˣ)

attribute [local instance] fstSwapAction

theorem fstSwap_smul_def (g : ℤˣ × ℤˣ) (y : Fin 1 → ℝ) : g • y = g.1 • y := rfl

theorem fstSwap_smul_eq_zero (g : ℤˣ × ℤˣ) (y : Fin 1 → ℝ) : g • y = 0 ↔ y = 0 :=
  smul_eq_zero_iff_eq g.1

theorem isScSmoothMap_fstSwap_smul (g : ℤˣ × ℤˣ) :
    (rnPolyfold 1).IsScSmoothMap (rnPolyfold 1) fun y : Fin 1 → ℝ => g • y :=
  isScSmoothMap_units_smul g.1

/-- `β(g, p) = (g, p)` for `p ≠ 0` and `(swap g, p)` for `p = 0`. -/
def fstSwapTwistFun (x : (ℤˣ × ℤˣ) × (Fin 1 → ℝ)) : (ℤˣ × ℤˣ) × (Fin 1 → ℝ) :=
  (if x.2 = 0 then x.1.swap else x.1, x.2)

theorem fstSwapTwistFun_involutive : Involutive fstSwapTwistFun := by
  rintro ⟨g, p⟩
  unfold fstSwapTwistFun
  split_ifs <;> simp_all

/-- **The twist of `(ℤ/2 × ℤ/2) ⋉ ℝ`** exchanging the two factors over `0`. -/
def fstSwapTwist : TranslationTwist (ℤˣ × ℤˣ) (Fin 1 → ℝ) where
  toEquiv := fstSwapTwistFun_involutive.toPerm _
  snd_apply _ := rfl
  smul_apply x := by
    change (if x.2 = 0 then x.1.swap else x.1) • x.2 = x.1 • x.2
    split_ifs with h
    · rw [h, (fstSwap_smul_eq_zero _ _).2 rfl, (fstSwap_smul_eq_zero _ _).2 rfl]
    · rfl
  apply_one y := by
    change fstSwapTwistFun (1, y) = (1, y)
    unfold fstSwapTwistFun
    split_ifs <;> rfl
  apply_inv x := by
    change fstSwapTwistFun (x.1⁻¹, x.1 • x.2) = ((fstSwapTwistFun x).1⁻¹, x.1 • x.2)
    unfold fstSwapTwistFun
    by_cases h : x.2 = 0
    · rw [if_pos ((fstSwap_smul_eq_zero _ _).2 h), if_pos h]; rfl
    · rw [if_neg (mt (fstSwap_smul_eq_zero _ _).1 h), if_neg h]
  apply_mul x y hxy := by
    change fstSwapTwistFun (x.1 * y.1, y.2) =
      ((fstSwapTwistFun x).1 * (fstSwapTwistFun y).1, y.2)
    unfold fstSwapTwistFun
    by_cases h : y.2 = 0
    · have hx : x.2 = 0 := by rw [hxy]; exact (fstSwap_smul_eq_zero _ _).2 h
      rw [if_pos h, if_pos hx, if_pos h]; rfl
    · have hx : x.2 ≠ 0 := by rw [hxy]; exact mt (fstSwap_smul_eq_zero _ _).1 h
      rw [if_neg h, if_neg hx, if_neg h]

theorem fstSwapTwist_symm_apply (x : (ℤˣ × ℤˣ) × (Fin 1 → ℝ)) :
    fstSwapTwist.toEquiv.symm x = fstSwapTwistFun x := by
  change (fstSwapTwistFun_involutive.toPerm _).symm x = _
  rw [Function.Involutive.toPerm_symm]
  rfl

/-- **The twisted polyfold structure on `(ℤ/2 × ℤ/2) ⋉ ℝ`** (Definition 17.1.8). -/
abbrev fstSwapConstruction : (GCT.translation (ℤˣ × ℤˣ) (Fin 1 → ℝ)
    isScSmoothMap_fstSwap_smul).PolyfoldConstruction :=
  twistConstruction isScSmoothMap_fstSwap_smul fstSwapTwist

/-- The tautological uniformizer of `fstSwapConstruction`, at `0`. -/
abbrev fstSwapUnif : fstSwapConstruction.Unif := tautUnif _ _ 0

theorem fstSwapConstruction_hasUniformizers : fstSwapConstruction.HasUniformizers :=
  twistConstruction_hasUniformizers _ _

/-- The vector `(0, 1)` of `T_0ℝ`, in the chart `y ↦ y`. -/
def fstSwapVec : (rnChart 1 0).model.E.tangent 0 := ((0 : Fin 1 → ℝ), fun _ => (1 : ℝ))

theorem fstSwapVec_mem : fstSwapVec ∈ retractTangent (rnChart 1 0).model.E (rnChart 1 0).model.C
    (rnChart 1 0).model.O := by
  change fstSwapVec ∈ retractTangent (rnSc 1) univ univ
  rw [retractTangent_univ]
  exact mem_univ _

/-- `[0, y ↦ y, 1] ∈ T_0ℝ`. -/
def fstSwapTangent : (rnPolyfold 1).TangentSpace :=
  TangentSpace.mk (TangentPre.ofVec (isChart_rnChart 0) fstSwapVec_mem)

theorem basePt_fstSwapTangent : basePt fstSwapUnif fstSwapTangent = 0 := by
  change (rnChart 1 0).model.E.toBase 1 0 + 0 = 0
  rw [map_zero, add_zero]

theorem tangentChartMap_fstSwapTangent :
    tangentChartMap (isChart_rnChart 0) fstSwapTangent = fstSwapVec :=
  tangentChartMap_mk_ofVec _ fstSwapVec_mem

/-- `T(y ↦ −y)` reverses `(0, 1)`. -/
theorem tangentChartMap_tangentMap_neg :
    tangentChartMap (isChart_rnChart 0)
        (MPolyfold.tangentMap (isScSmoothMap_units_smul (-1)) fstSwapTangent) =
      ((0 : Fin 1 → ℝ), fun _ => (-1 : ℝ)) := by
  rw [tangentChartMap_tangentMap_of_linear (isScSmoothMap_units_smul (-1)) (isChart_rnChart 0)
    (isChart_rnChart 0) (ScOperator.ofConst (-ContinuousLinearMap.id ℝ (Fin 1 → ℝ)))
    (fun _ _ => mem_univ _) (fun x _ => ?_) (mem_univ _), tangentChartMap_fstSwapTangent]
  · refine Prod.ext ?_ ?_
    · change -(0 : Fin 1 → ℝ) = 0
      exact neg_zero
    · change -(fun _ => (1 : ℝ)) = fun _ => (-1 : ℝ)
      rfl
  · change (-1 : ℤˣ) • x - 0 = -(x - 0)
    rw [units_smul_rn_neg_one, sub_zero, sub_zero]

/-- `T(y ↦ y)` fixes `(0, 1)`. -/
theorem tangentChartMap_tangentMap_one :
    tangentChartMap (isChart_rnChart 0)
        (MPolyfold.tangentMap (isScSmoothMap_units_smul 1) fstSwapTangent) = fstSwapVec := by
  rw [tangentChartMap_tangentMap_of_linear (isScSmoothMap_units_smul 1) (isChart_rnChart 0)
    (isChart_rnChart 0) (ScOperator.ofConst (ContinuousLinearMap.id ℝ (Fin 1 → ℝ)))
    (fun _ _ => mem_univ _) (fun x _ => ?_) (mem_univ _), tangentChartMap_fstSwapTangent]
  · rfl
  · change (1 : ℤˣ) • x - 0 = x - 0
    rw [one_smul]

/-- For `g = (1, −1)` at `0`: `Ψ̂(g, 0)` is `(0, (−1, 1), 0)`, whose sheet is `p ↦ (p, (−1, 1), −p)`,
so `Tσ(h) = T(−1 ∗ ·)(h)`. -/
theorem fstSwap_transMap_hat :
    fstSwapConstruction.transMap (fstSwapConstruction.hat fstSwapUnif
        (((1 : ℤˣ), (-1 : ℤˣ)), basePt fstSwapUnif fstSwapTangent)) fstSwapTangent =
      MPolyfold.tangentMap (isScSmoothMap_units_smul (-1)) fstSwapTangent := by
  have hhat : fstSwapConstruction.hat fstSwapUnif (((1 : ℤˣ), (-1 : ℤˣ)), basePt fstSwapUnif fstSwapTangent) =
      twistHomeomorph isScSmoothMap_fstSwap_smul fstSwapTwist
        (((-1 : ℤˣ), (1 : ℤˣ)), basePt fstSwapUnif fstSwapTangent) := by
    rw [twist_hat_eq, fstSwapTwist_symm_apply]
    unfold fstSwapTwistFun
    rw [if_pos basePt_fstSwapTangent]
    rfl
  exact transMap_eq_tangentMap_of_section (S := fstSwapConstruction) (Ψ := fstSwapUnif) (Ψ' := fstSwapUnif) _
    (f := fun p => (twistHomeomorph isScSmoothMap_fstSwap_smul fstSwapTwist (((-1 : ℤˣ), (1 : ℤˣ)), p) : fstSwapConstruction.Tr fstSwapUnif fstSwapUnif))
    ((twistHomeomorph _ _).continuous.comp (Continuous.prodMk_right _)) (fun _ => rfl)
    hhat.symm (isScSmoothMap_units_smul (-1)) (fun _ => rfl) rfl

/-- **2021 Lemma 17.2.10, p. 773, does not hold as we read it without the continuity of `Ψ̂`**:
there are a GCT with a polyfold structure (Definition 17.1.8, every `F(α) ≠ ∅`) and a
uniformizer `Ψ` for which the target of `TΨ(g, h)` is not `TΨ(g ∗ h)`, so `TΨ : G ⋉ TO → TC`
is not a functor.  Here `(ℤ/2 × ℤ/2) ⋉ ℝ` acts through the first factor and `M(Ψ, Ψ)` is
twisted by exchanging the factors over `0`; for `g = (1, −1)` at `0`, `Tσ` is `T(y ↦ −y)` while
`g ∗ ·` is the identity.  For continuous `Ψ̂` the statement holds
(`lemma_17_2_10_of_continuous`). -/
theorem not_lemma_17_2_10 : ¬ ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction)
    (hU : S.HasUniformizers) (Ψ : S.Unif) (p : ULift.{1} Ψ.1.G × Ψ.1.P.TangentSpace),
    (S.tangentUnifMor hU Ψ p).tgt = S.tangentUnifObj hU Ψ (p.1 • p.2) := by
  intro h
  have h1 := h _ fstSwapConstruction fstSwapConstruction_hasUniformizers fstSwapUnif
    (ULift.up ((1 : ℤˣ), (-1 : ℤˣ)), fstSwapTangent)
  rw [tangentUnifMor_tgt] at h1
  have h2 := injective_tangentUnifObj _ _ h1
  change fstSwapConstruction.transMap (fstSwapConstruction.hat fstSwapUnif
      (((1 : ℤˣ), (-1 : ℤˣ)), basePt fstSwapUnif fstSwapTangent)) fstSwapTangent =
    MPolyfold.tangentMap (isScSmoothMap_units_smul 1) fstSwapTangent at h2
  rw [fstSwap_transMap_hat] at h2
  have h3 := congrArg (tangentChartMap (isChart_rnChart 0)) h2
  rw [tangentChartMap_tangentMap_neg, tangentChartMap_tangentMap_one] at h3
  have h4 := congrFun (congrArg Prod.snd h3) 0
  change (-1 : ℝ) = 1 at h4
  norm_num at h4

end SwapTwist

end GCT.PolyfoldConstruction

end Polyfold
