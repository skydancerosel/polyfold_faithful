import Polyfold.Chapter7.ReducedCriterion
import Polyfold.Chapter2.TangentMapLocal
import Polyfold.Chapter5.DenseSmooth

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, §7.4 "Regularity Assumptions and the Zhou Condition" (pp. 328–340, new in the 2021
edition; there is no 2017 counterpart): **Definitions 7.4.1, 7.4.5, 7.4.7, 7.4.12, 7.4.14, 7.4.19,
7.4.21, 7.4.23**, **Proposition 7.4.2**, **Remark 7.4.3**, **Lemmas 7.4.4, 7.4.6, 7.4.15, 7.4.20**,
**Propositions 7.4.8, 7.4.10, 7.4.16–7.4.18, 7.4.22**, **Corollary 7.4.11** and **Theorems 7.4.13,
7.4.24**; and Appendix 7.6.4, **Corollary 7.6.8** (p. 351) without its hypothesis
"(ZHOU) ⇒ (LUC) for `X¹`".  Numbers and pages are the 2021 text's.

# The Zhou condition, unique continuation and local regularity

## The text, paraphrased

(Definition 7.4.1, p. 328 = Definition 7.2.18) (LUC): every `x` has a natural representation
`U(x)` on which `ĝ = id` on a nonempty open set forces `ĝ = id`.  (Proposition 7.4.2) Under (LUC),
the conclusion passes from a connected invariant `U(x)` to a larger connected invariant `W(x)`.
(Remark 7.4.3, p. 329) So `U(x)` may be taken small or large.  (Lemma 7.4.4) If `Xⁱ` has (LUC) so
has every `Xᵏ`, `k ≤ i`; proof for `i = 1` through the connected set `U(x) ∩ X₁` and a density
argument.  (Definition 7.4.5, p. 331) (ZHOU): for smooth `x` and `g ∈ G_x`, `Tg = id` on `T_xX`
implies `g ∈ T_x`.  `T_x^∞ ⊇ T_x` consists of the `g` acting trivially near `x` in `X_∞`.
(Lemma 7.4.6) Under (ZHOU), `Tg = id` on `(T_xX)_∞` gives `g ∈ T_x^∞`.  (Definition 7.4.7)
(ZHOU') is this implication.  (Proposition 7.4.8, p. 332) (ZHOU) ⇔ (ZHOU'), by a connectedness
argument in `U(x)_∞`.  (Proposition 7.4.9, p. 333) (ZHOU) for `X` gives (ZHOU) for every `Xⁱ`.
(Proposition 7.4.10) (ZHOU) ⇒ (LUC): the set of smooth `y` near which `ĝ = id` is open and closed
in the connected `U(x)_∞`; closedness approximates tangent vectors at `z` by tangent vectors at
nearby smooth points.  (Corollary 7.4.11, p. 334) (ZHOU) ⇒ every `Xⁱ` has (LUC).
(Definition 7.4.12) (SLUC): every `Xⁱ` has (LUC).  (Theorem 7.4.13) (ZHOU) ⇒ (SLUC).
(Definition 7.4.14, p. 335) (VSLUC): (LUC) for `X_∞`, with `G_x`-invariant open
`V(x) ⊆ X_∞`.  (Lemma 7.4.15) (VSLUC) ⇒ (LUC), by a maximality argument and density of `X_∞`.
(Propositions 7.4.16–7.4.18, p. 336) (VSLUC) passes to `Xⁱ`, implies (SLUC), and is equivalent
to it.  (Definition 7.4.19, p. 337) (LR): arbitrarily small `U(x)` such that every
sc-diffeomorphism `β` of `U(x)` with `|β(y)| = |y|` is some `ĝ`.  (Lemma 7.4.20) If `β` is an
sc-diffeomorphism of `U(x)` onto an open image with `β(x) = x` and `|β(y)| = |y|`, then
`β(U(x)) = U(x)`.  (Definition 7.4.21, p. 338) (LR') uses such `β`; (LR) = (LR').
(Proposition 7.4.22) (ZHOU) ⇒ (LR).  (Definition 7.4.23, p. 339) (SLR): every `Xⁱ` has (LR).
(Theorem 7.4.24, p. 340) (ZHOU) ⇒ (SLR).

## What is formalized

* `EP.liftOne`, `EP.lift` (`Xⁱ`, bundled), `lift_succ'`.
* (LUC) is the existing `EpGroupoid.IsLUC` / `NaturalRep.HasLUC` (**Definition 7.4.1**, in
  `ReducedCriterion.lean`).  `proposition_7_4_2`, `remark_7_4_3`.
* `HasLevelOneConnectedDenseReps`, `NaturalRep.eqOn_of_isClosed_liftOne`,
  `isLUC_of_isLUC_liftOne`, `lemma_7_4_4` (**Lemma 7.4.4**).
* **The encoding of `Tg`.**  `NaturalRep.tangentMor_Γ`, `tangentMor_eq_tΦ`, `tΦ_eq_tΦ`: Chapter 7's
  `tangentMor g` (2021 Definition 7.1.4; 2017 Definition 7.4), defined without charts, equals on
  `T_xX` the tangent map `TΦ(g)` of `ĝ` for every natural representation.
* `IsZhou` (**Definition 7.4.5**), `trivialSubgroupInf` (`T_x^∞`),
  `trivialSubgroup_le_trivialSubgroupInf`, `IsZhou'` (**Definition 7.4.7**),
  `lemma_7_4_6`, `isZhou_of_isZhou'`, `proposition_7_4_8`.
* `proposition_7_4_10`; `IsSmoothUC` (unique continuation through `X_∞`),
  `isSmoothUC_of_isZhou`, `isLUC_of_isSmoothUC`, `isLUC_liftOne_of_isSmoothUC`;
  `corollary_7_4_11` (`X` and `X¹`), `corollary_7_4_11_lift`; `EP.IsSLUC`
  (**Definition 7.4.12**), `theorem_7_4_13`.
* `IsVSLUC` (**Definition 7.4.14**), `isSmoothUC_of_isVSLUC`, `isVSLUC_of_isSmoothUC`,
  `lemma_7_4_15`, `proposition_7_4_16`, `proposition_7_4_17`, `isVSLUC_of_isZhou`.
* `corollary_7_6_8_of_isZhou` (**Corollary 7.6.8** with Corollary 7.4.11 for `X¹` in place of
  its hypothesis).
* `IsLR`, `IsLR'` (**Definitions 7.4.19, 7.4.21**), `lemma_7_4_20`, `isLR_iff_isLR'`,
  `NaturalRep.eqOn_Φ_of_tangent`, `NaturalRep.exists_eq_Φ_of_isZhou`, `proposition_7_4_22`,
  `EP.IsSLR` (**Definition 7.4.23**), `theorem_7_4_24`.
* `JumpingRetract.not_isZhou`: the ep-groupoid of Appendix 7.6.3 fails (ZHOU) (p. 331), given the
  Part I facts `SmoothRegular` for its object M-polyfold.
* Witnesses: (ZHOU), (ZHOU') for `trivial P` and for `trivialZ3EpGroupoid` (where `T_x = G_x ≠ 1`);
  `IsSmoothUC`, `IsVSLUC` for `trivial P`; `smoothRegular_discrete_unit`,
  `denseSmoothTangent_discrete_unit`, `smoothRegular_of_subsingleton`; for the point ep-groupoid
  `pointEP` and all its lifts: (ZHOU), `SmoothRegular`, `HasLevelOneConnectedDenseReps`, (SLUC)
  and (SLR) (`theorem_7_4_13_pointEP`, `isSLR_pointEP`), and the hypotheses of
  `proposition_7_4_8`, `lemma_7_4_4` and `corollary_7_6_8_of_isZhou`.

## What the text leaves implicit, and the choices made

* **No linear structure is needed.**  (ZHOU) asks that `Tg : T_xX → T_xX` be the identity map, a
  statement about the set map `tangentMor g` on the fibre `T_xX` (the project has no linear
  structure on `T_xX`, point G.7).  `tangentMor_eq_tΦ` shows that this map is `TΦ(g)` on `T_xX`
  for every natural representation, so (ZHOU) agrees with the text's `T ĝ(x) = id`.
* **Part I facts as hypotheses**, each satisfied by `discretePolyfold Unit` and by every
  M-polyfold on a subsingleton with all points smooth: `DenseSmooth` (`X_∞` dense in every `X_m`,
  2021 p. 289, point G.73), `SmoothConnected` (`U ∩ X_∞` connected in `X_∞` for connected open
  `U`), `IsOpenMap tangentProj` (point G.8), `TangentDeterminedSmooth` (maps agreeing near a smooth
  `y` in `X_∞` have the same tangent on `T_yX`), bundled as `SmoothRegular`; and
  `DenseSmoothTangent` (`(T_xX)_∞` dense in `T_xX`) for Lemma 7.4.6.  Lemma 7.4.4 assumes, as its
  proof does, that `U(x) ∩ X₁` is connected in `X¹` and dense in `U(x)`
  (`HasLevelOneConnectedDenseReps`).
* **`Xⁱ` for `i ≥ 2`.**  Here Corollary 7.4.11 is proved for `X` and `X¹`
  (`corollary_7_4_11`), through `IsSmoothUC`; Theorems 7.4.13 and 7.4.24 take (ZHOU) for every
  `Xⁱ` as a hypothesis, Proposition 7.4.16 is proved for `X¹`, and Proposition 7.4.17 takes (VSLUC)
  for every `Xⁱ`.  `Chapter8/ZhouLevels.lean` removes these hypotheses: Proposition 7.4.9
  (`EP.proposition_7_4_9`), the all-`i` forms `EP.corollary_7_4_11_all`,
  `EP.theorem_7_4_13_all`, `EP.proposition_7_4_16_all`, `EP.proposition_7_4_17_all`,
  `EP.theorem_7_4_24_all`, and Proposition 7.4.18 in both directions
  (`EP.proposition_7_4_18`), with the Part I facts per level as explicit hypotheses.
* (VSLUC) is read with `V(x)` open in `X_∞`, inside some natural representation `U(x)` and
  invariant under its action; (LUC)-type conclusions are stated for points of `V(x)`.
* Proposition 7.4.2: given (LUC) for `X`, the conclusion holds for every natural representation
  (`isLUC_iff_forall_naturalRep`), so the hypotheses `U(x) ⊆ W(x)` and (LUC) on `U(x)` are not
  used.
* `|β(y)| = |y|` is `X.π (β y) = X.π y`; "arbitrarily small" is "inside every open `O ∋ x`".
* **Proofs.**  Propositions 7.4.8, 7.4.10 and Lemma 7.4.15 use connectedness of `U(x)_∞`
  (`eq_self_of_smooth_clopen`) in place of sequences and Zorn's lemma; the approximation of
  tangent vectors at the end of the proof of 7.4.10 is `eqOn_tangentFiber_of_mem_closure` (from
  the openness of `p : TX → X¹`).  Lemma 7.4.20 uses the finite closed cover
  `U(x) = ⋃_g {β = ĝ}` and connectedness in place of paths.  Proposition 7.4.22 is proved without
  passing to the reduced ep-groupoid: on the open dense union of the `X_∞`-interiors of
  `{β = ĝ}`, two pieces whose closures meet have `T(ĝ) = T(ĝ')` at a common smooth point, so
  `ĝ = ĝ'` by (ZHOU) and (LUC) (`eqOn_Φ_of_tangent`); connectedness of `U(x)_∞` finishes.  The
  text's claim that the regular points are dense is not used.
* Notation, as we read it: in the proof of Lemma 7.4.4, "`s : W(g) → W(y)`" for
  `W(h)`; in the proof of Proposition 7.4.8, "`z_k → Y`" for `z_k → y`.

Density of smooth points (`MPolyfold.DenseSmooth`, `MPolyfold.DenseSmooth.dense`):
`Chapter5/DenseSmooth.lean`.

The Zhou property and tangent maps (`EpGroupoid.lemma_7_4_6`, `EpGroupoid.theorem_7_4_13`,
`EpGroupoid.theorem_7_4_24`, `EpGroupoid.corollary_7_4_11`, …): `Chapter8/ZhouTangent.lean`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

/-! ### The index lift `Xⁱ` -/

namespace EP

/-- The index lift `X¹` of a bundled ep-groupoid (Chapter 7's `EpGroupoid.liftOne`). -/
def liftOne (A : EP.{u}) : EP.{u} where
  Obj := A.X.PObj.Level 1
  Mor := A.X.PMor.Level 1
  X := A.X.liftOne

/-- `Xⁱ`, obtained by raising the index `i` times: `X⁰ = X`, `X^{i+1} = (Xⁱ)¹` (2021 p. 329). -/
def lift (A : EP.{u}) : ℕ → EP.{u}
  | 0 => A
  | i + 1 => (A.lift i).liftOne

@[simp] theorem lift_zero (A : EP.{u}) : A.lift 0 = A := rfl

theorem lift_succ (A : EP.{u}) (i : ℕ) : A.lift (i + 1) = (A.lift i).liftOne := rfl

/-- `X^{i+1} = (X¹)ⁱ`. -/
theorem lift_succ' (A : EP.{u}) (i : ℕ) : A.lift (i + 1) = A.liftOne.lift i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [lift_succ, ih, lift_succ]

end EP

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### Proposition 7.4.2, Remark 7.4.3 -/

/-- **2021 Proposition 7.4.2, p. 328 (new in the 2021 edition)**: under (LUC), the (LUC)
conclusion holds on a larger connected invariant `W(x) ⊇ U(x)`; in fact on every natural
representation, so the hypotheses on `U(x)` are not needed. -/
theorem proposition_7_4_2 (h : X.IsLUC) {x : Obj} (R W : X.NaturalRep x)
    (_hRW : R.U ⊆ W.U) (_hR : R.HasLUC) : W.HasLUC :=
  X.isLUC_iff_forall_naturalRep.1 h x W

/-- **2021 Remark 7.4.3, p. 329 (new in the 2021 edition)**: under (LUC), every natural
representation has the (LUC) property, and there are such inside every neighbourhood of `x`. -/
theorem remark_7_4_3 (h : X.IsLUC) (x : Obj) :
    (∀ R : X.NaturalRep x, R.HasLUC) ∧
      ∀ O : Set Obj, IsOpen O → x ∈ O → ∃ R : X.NaturalRep x, R.U ⊆ O ∧ R.HasLUC :=
  ⟨X.isLUC_iff_forall_naturalRep.1 h x, fun _ hO hx => X.remark_7_2_20 h x hO hx⟩

/-! ### Lemma 7.4.4 -/

/-- The assumption made in the proof of 2021 Lemma 7.4.4 (p. 330): every `x ∈ X` has a natural
representation `U(x)` with `U(x) ∩ X₁` connected in `X¹` and dense in `U(x)`.  Satisfiable:
`hasLevelOneConnectedDenseReps_of_subsingleton`,
`Examples.hasLevelOneConnectedDenseReps_lift_pointEP`. -/
def HasLevelOneConnectedDenseReps : Prop :=
  ∀ x : Obj, ∃ R : X.NaturalRep x, IsPreconnected R.liftU ∧ R.U ⊆ closure (R.U ∩ X.PObj.levelSet 1)

namespace NaturalRep

variable {X} {x : Obj} (R : X.NaturalRep x)

/-- The core of the proof of 2021 Lemma 7.4.4: if `(𝐗¹)^T` is closed, `U(x) ∩ X₁` is connected and
dense, and `ĝ` is the identity near one point of `U(x) ∩ X₁` in `X¹`, then `ĝ = id` on `U(x)`. -/
theorem eqOn_of_isClosed_liftOne (hcl : IsClosed X.liftOne.nonEffectivePart)
    (hconn : IsPreconnected R.liftU) (hdense : R.U ⊆ closure (R.U ∩ X.PObj.levelSet 1))
    (g : X.Isotropy x) {y₀ : X.PObj.Level 1} (hy₀ : y₀ ∈ R.liftU)
    (h₀ : ∀ᶠ z in 𝓝 y₀, R.Φ g (X.PObj.levelVal 1 z) = X.PObj.levelVal 1 z) :
    ∀ y ∈ R.U, R.Φ g y = y := by
  set u := {y : X.PObj.Level 1 |
    ∀ᶠ z in 𝓝 y, z ∈ R.liftU ∧ R.Φ g (X.PObj.levelVal 1 z) = X.PObj.levelVal 1 z}
  have huo : IsOpen u := isOpen_setOfPred_eventually_nhds
  have hsub : R.liftU ⊆ u := by
    refine hconn.subset_of_closure_inter_subset huo ⟨y₀, hy₀, ?_⟩ ?_
    · filter_upwards [h₀, R.isOpen_liftU.mem_nhds hy₀] with z hz hzU using ⟨hzU, hz⟩
    · rintro y ⟨hyc, hyU⟩
      have hc : ContinuousAt (R.levelOneΓ g) y :=
        (R.continuousOn_levelOneΓ g).continuousAt (R.isOpen_liftU.mem_nhds hyU)
      have himg : R.levelOneΓ g '' u ⊆ X.liftOne.nonEffectivePart := by
        rintro _ ⟨y', hy', rfl⟩
        exact R.levelOneΓ_mem_of_eventually g hy'.self_of_nhds.1 (hy'.mono fun z hz => hz.2)
      exact R.eventually_of_levelOneΓ_mem g hyU
        (hcl.closure_subset_iff.2 himg (mem_closure_image hc hyc))
  have hlev : EqOn (R.Φ g) id (R.U ∩ X.PObj.levelSet 1) := fun y hy =>
    (hsub (show X.PObj.levelMk 1 y hy.2 ∈ R.liftU from hy.1)).self_of_nhds.2
  have hall : EqOn (R.Φ g) id R.U := hlev.of_subset_closure
    (R.isScDiffeoOn_Φ g).isScSmoothOn.continuousOn continuousOn_id inter_subset_left hdense
  exact fun y hy => hall hy

end NaturalRep

/-- **2021 Lemma 7.4.4 for `i = 1`**: (LUC) for `X¹` gives (LUC) for `X`. -/
theorem isLUC_of_isLUC_liftOne (h : X.liftOne.IsLUC) (hR : X.HasLevelOneConnectedDenseReps) :
    X.IsLUC := by
  have hcl := X.liftOne.proposition_7_2_21.1 h
  intro x
  obtain ⟨R, hconn, hdense⟩ := hR x
  refine ⟨R, fun g V hVo hVne hVU hV => ?_⟩
  obtain ⟨v, hv⟩ := hVne
  obtain ⟨y, hyV, hyU, hy1⟩ := mem_closure_iff.1 (hdense (hVU hv)) V hVo hv
  refine R.eqOn_of_isClosed_liftOne hcl hconn hdense g (y₀ := X.PObj.levelMk 1 y hy1) hyU ?_
  filter_upwards [(hVo.preimage (MPolyfold.continuous_levelVal 1)).mem_nhds
    (show X.PObj.levelVal 1 (X.PObj.levelMk 1 y hy1) ∈ V from hyV)] with z hz
  exact hV _ hz

/-- **2021 Lemma 7.4.4, p. 329 (new in the 2021 edition)**: if `Xⁱ` has (LUC), so do `X` and
every `Xᵏ`, `k ≤ i`. -/
theorem lemma_7_4_4 (A : EP.{u}) (i : ℕ)
    (hR : ∀ k < i, (A.lift k).X.HasLevelOneConnectedDenseReps) (h : (A.lift i).X.IsLUC) :
    A.X.IsLUC ∧ ∀ k ≤ i, (A.lift k).X.IsLUC := by
  have key : ∀ j, j ≤ i → (A.lift (i - j)).X.IsLUC := by
    intro j
    induction j with
    | zero => intro _; simpa using h
    | succ j ih =>
      intro hj
      have hk : i - (j + 1) < i := by omega
      have h1 : i - (j + 1) + 1 = i - j := by omega
      have h2 := ih (by omega)
      rw [← h1] at h2
      exact (A.lift (i - (j + 1))).X.isLUC_of_isLUC_liftOne h2 (hR _ hk)
  refine ⟨?_, fun k hk => ?_⟩
  · have h0 := key i le_rfl
    rw [Nat.sub_self] at h0
    exact h0
  have h3 := key (i - k) (by omega)
  rwa [show i - (i - k) = k by omega] at h3

end EpGroupoid

/-! ### Part I facts used in §7.4 -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- The fact used in the proofs of 2021 Propositions 7.4.8 and 7.4.10 that `U ∩ X_∞` is connected
in `X_∞` for a connected open `U ⊆ X`, as a hypothesis. -/
def SmoothConnected : Prop :=
  ∀ U : Set X, IsOpen U → IsConnected U → IsPreconnected (P.smoothVal ⁻¹' U)

/-- The density of `(T_xX)_∞` in `T_xX` for smooth `x`, used in the proof of 2021 Lemma 7.4.6,
as a hypothesis.  Satisfiable: `denseSmoothTangent_discrete_unit`. -/
def DenseSmoothTangent : Prop :=
  ∀ y : P.SmoothLevel, P.tangentFiber (P.smoothIncl y 1) ⊆
    closure (P.tangentFiber (P.smoothIncl y 1) ∩ P.tangentPolyfold.smoothSet)

/-- The Part I fact used in the proofs of 2021 Propositions 7.4.8 and 7.4.22: two sc-smooth maps
agreeing near a smooth `y` in `X_∞` have the same tangent on `T_yX` (`X_∞` is dense in the
tangent directions), as a hypothesis. -/
def TangentDeterminedSmooth : Prop :=
  ∀ (f₁ f₂ : X → X) (U₁ U₂ : Set X) (hf₁ : P.IsScSmoothOn P f₁ U₁) (hf₂ : P.IsScSmoothOn P f₂ U₂)
    (y : P.SmoothLevel), P.smoothVal y ∈ U₁ → P.smoothVal y ∈ U₂ →
    (∀ᶠ z in 𝓝 y, f₁ (P.smoothVal z) = f₂ (P.smoothVal z)) →
    ∀ v ∈ P.tangentFiber (P.smoothIncl y 1), tangentMapOn hf₁ v = tangentMapOn hf₂ v

/-- `TangentDeterminedSmooth` for a map agreeing with the identity near `y` in `X_∞`. -/
theorem TangentDeterminedSmooth.eq_self {P : MPolyfold X} (h : P.TangentDeterminedSmooth)
    {f : X → X} {U : Set X} (hf : P.IsScSmoothOn P f U) (y : P.SmoothLevel)
    (hy : P.smoothVal y ∈ U) (hev : ∀ᶠ z in 𝓝 y, f (P.smoothVal z) = P.smoothVal z)
    {v : P.TangentSpace} (hv : v ∈ P.tangentFiber (P.smoothIncl y 1)) : tangentMapOn hf v = v := by
  have hid : P.IsScSmoothOn P id U := isScSmoothMap_id.mono hf.isOpen (subset_univ _)
  rw [h f id U U hf hid y hy hy hev v hv]
  refine tangentMapOn_id hid ?_
  change P.levelVal 1 (P.tangentProj v) ∈ U
  rw [show P.tangentProj v = P.smoothIncl y 1 from hv]; exact hy

variable {P}

/-- `U ⊆ cl(U ∩ X_∞)` for open `U`. -/
theorem DenseSmooth.subset_closure_inter (h : P.DenseSmooth) {U : Set X} (hU : IsOpen U) :
    U ⊆ closure (U ∩ P.smoothSet) :=
  h.dense.open_subset_closure_inter hU

/-- A nonempty open subset of `X_m` contains a smooth point. -/
theorem DenseSmooth.exists_smooth (h : P.DenseSmooth) {m : ℕ} {W : Set (P.Level m)}
    (hW : IsOpen W) (hne : W.Nonempty) : ∃ y : P.SmoothLevel, P.smoothIncl y m ∈ W := by
  obtain ⟨z, hzW, hz⟩ := dense_iff_inter_open.1 (h m) W hW hne
  exact ⟨P.smoothMk _ hz, by
    have : P.smoothIncl (P.smoothMk _ hz) m = z := level_ext rfl
    rw [this]; exact hzW⟩

/-- **Approximation of tangent vectors** (the claim proved at the end of the proof of 2021
Proposition 7.4.10): if `p : TX → X¹` is open and `F` is continuous on an open `W ⊆ TX` and the
identity on `T_aX ∩ W` for all `a` in `A ⊆ X_∞`, then also on `T_yX ∩ W` for `y` in the closure of
`A` in `X_∞`. -/
theorem eqOn_tangentFiber_of_mem_closure (hp : IsOpenMap P.tangentProj)
    {F G : P.TangentSpace → P.TangentSpace} {W : Set P.TangentSpace} (hW : IsOpen W)
    (hF : ContinuousOn F W) (hG : ContinuousOn G W) {A : Set P.SmoothLevel} {y : P.SmoothLevel}
    (hy : y ∈ closure A)
    (hA : ∀ a ∈ A, ∀ v ∈ P.tangentFiber (P.smoothIncl a 1), v ∈ W → F v = G v)
    {v : P.TangentSpace} (hv : v ∈ P.tangentFiber (P.smoothIncl y 1)) (hvW : v ∈ W) :
    F v = G v := by
  by_contra hne
  have hev : ∀ᶠ w in 𝓝 v, w ∈ W ∧ F w ≠ G w :=
    Filter.Eventually.and (hW.mem_nhds hvW)
      (((hF.continuousAt (hW.mem_nhds hvW)).ne_iff_eventually_ne
        (hG.continuousAt (hW.mem_nhds hvW))).1 hne)
  obtain ⟨N, hNs, hNo, hvN⟩ := mem_nhds_iff.1 hev
  have hpN : IsOpen ((fun a : P.SmoothLevel => P.smoothIncl a 1) ⁻¹' (P.tangentProj '' N)) :=
    (hp N hNo).preimage (P.continuous_smoothIncl 1)
  have hyN : y ∈ (fun a : P.SmoothLevel => P.smoothIncl a 1) ⁻¹' (P.tangentProj '' N) :=
    ⟨v, hvN, hv⟩
  obtain ⟨a, ⟨w, hwN, hwa⟩, haA⟩ := mem_closure_iff.1 hy _ hpN hyN
  exact (hNs hwN).2 (hA a haA w hwa (hNs hwN).1)

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

namespace NaturalRep

variable {X} {x : Obj} (R : X.NaturalRep x)

/-- **Natural representations at nearby points are compatible**: for `z ∈ U(x)`, `g ∈ G_x` and a
natural representation `U(z)`, the element `h = Γ(g, z) ∈ G_z` acts near `z` as `g` does. -/
theorem eventually_Φ_eq_Γ {z : Obj} (R' : X.NaturalRep z) (hz : z ∈ R.U) (g : X.Isotropy x)
    (h : X.Isotropy z) (hh : h.val = R.Γ g z) :
    ∀ᶠ y in 𝓝 z, y ∈ R.U ∧ y ∈ R'.U ∧ R'.Φ h y = R.Φ g y := by
  have hzC : z ∈ connectedComponentIn (R.U ∩ R'.U) z := mem_connectedComponentIn ⟨hz, R'.mem_U⟩
  have hC := connectedComponentIn_subset (R.U ∩ R'.U) z
  have heq : EqOn (R'.Γ h) (R.Γ g) (connectedComponentIn (R.U ∩ R'.U) z) :=
    eqOn_sections_of_isPreconnected X.isLocalScDiffeo_src.isLocallyInjective
      isPreconnected_connectedComponentIn ((R'.continuousOn_Γ h).mono fun y hy => (hC hy).2)
      ((R.continuousOn_Γ g).mono fun y hy => (hC hy).1) (fun y hy => R'.src_Γ h y (hC hy).2)
      (fun y hy => R.src_Γ g y (hC hy).1) hzC ((R'.Γ_self h).trans hh)
  filter_upwards [(X.PObj.isOpen_connectedComponentIn (R.isOpen_U.inter R'.isOpen_U) z).mem_nhds
    hzC] with y hy
  refine ⟨(hC hy).1, (hC hy).2, ?_⟩
  rw [← R'.tgt_Γ h y (hC hy).2, heq hy, R.tgt_Γ g y (hC hy).1]

/-- `Γ(g, z) ∈ G_z` for a fixed point `z` of `Φ(g)`. -/
def isoΓ (g : X.Isotropy x) {z : Obj} (hz : z ∈ R.U) (hfix : R.Φ g z = z) : X.Isotropy z :=
  ⟨R.Γ g z, R.src_Γ g z hz, (R.tgt_Γ g z hz).trans hfix⟩

theorem isoΓ_val (g : X.Isotropy x) {z : Obj} (hz : z ∈ R.U) (hfix : R.Φ g z = z) :
    (R.isoΓ g hz hfix).val = R.Γ g z := rfl

/-- `Γ(g, z) ∈ T_z` iff `Φ(g)` is the identity near `z`. -/
theorem isoΓ_mem_trivialSubgroup_iff (g : X.Isotropy x) {z : Obj} (hz : z ∈ R.U)
    (hfix : R.Φ g z = z) :
    R.isoΓ g hz hfix ∈ X.trivialSubgroup z ↔ ∀ᶠ y in 𝓝 z, R.Φ g y = y := by
  rw [mem_trivialSubgroup, ← val_mem_nonEffectivePart_iff, isoΓ_val]
  exact ⟨fun h => (R.eventually_Φ_eq_of_Γ_mem hz h).mono fun _ h => h.2,
    R.Γ_mem_of_eventually hz⟩

/-! ### The tangent `Tg` through the natural representation -/

end NaturalRep

/-! ### Definition 7.4.5: the Zhou condition -/

/-- **2021 Definition 7.4.5, p. 331 (new in the 2021 edition)**: the **Zhou condition**
(ZHOU).  For a smooth object `x` and `g ∈ G_x`, if `Tg : T_xX → T_xX` is the identity then
`g ∈ T_x`.  `Tg` is Chapter 7's `tangentMor g` on the fibre `T_xX` (equal to `TΦ(g)` there,
`NaturalRep.tangentMor_eq_tΦ`); no linear structure is needed. -/
def IsZhou : Prop :=
  ∀ (y : X.PObj.SmoothLevel) (g : X.Isotropy (X.PObj.smoothVal y)),
    (∀ v ∈ X.PObj.tangentFiber (X.PObj.smoothIncl y 1), X.tangentMor g.val v = v) →
      g ∈ X.trivialSubgroup (X.PObj.smoothVal y)

/-! ### `T_x^∞` -/

/-- `T_x^∞` (2021 p. 331): the elements of `G_x` acting trivially near `x` in `X_∞`. -/
def trivialSetInf (y : X.PObj.SmoothLevel) : Set (X.Isotropy (X.PObj.smoothVal y)) :=
  {g | ∃ R : X.NaturalRep (X.PObj.smoothVal y),
    ∀ᶠ z in 𝓝 y, R.Φ g (X.PObj.smoothVal z) = X.PObj.smoothVal z}

/-- Membership in `T_x^∞` can be tested in any natural representation. -/
theorem mem_trivialSetInf_iff {y : X.PObj.SmoothLevel} (R : X.NaturalRep (X.PObj.smoothVal y))
    {g : X.Isotropy (X.PObj.smoothVal y)} :
    g ∈ X.trivialSetInf y ↔ ∀ᶠ z in 𝓝 y, R.Φ g (X.PObj.smoothVal z) = X.PObj.smoothVal z := by
  refine ⟨fun ⟨R', hR'⟩ => ?_, fun h => ⟨R, h⟩⟩
  filter_upwards [hR', X.PObj.continuous_smoothVal.continuousAt.eventually
    ((R.isOpen_connectedComponentIn_inter R').mem_nhds (R.mem_connectedComponentIn_inter R'))]
    with z hz hzC
  rw [R.Φ_eqOn R' g hzC]
  exact hz

/-- `T_x^∞` as a subgroup of `G_x`. -/
def trivialSubgroupInf (y : X.PObj.SmoothLevel) : Subgroup (X.Isotropy (X.PObj.smoothVal y)) where
  carrier := X.trivialSetInf y
  mul_mem' {g h} hg hh := by
    obtain ⟨R, -⟩ := X.theorem_7_1_13 (X.PObj.smoothVal y) isOpen_univ (mem_univ _)
    rw [X.mem_trivialSetInf_iff R] at hg hh ⊢
    filter_upwards [hg, hh, X.PObj.continuous_smoothVal.continuousAt.eventually
      (R.isOpen_U.mem_nhds R.mem_U)] with z hgz hhz hzU
    rw [R.Φ_mul g h _ hzU, hhz, hgz]
  one_mem' := by
    obtain ⟨R, -⟩ := X.theorem_7_1_13 (X.PObj.smoothVal y) isOpen_univ (mem_univ _)
    refine (X.mem_trivialSetInf_iff R).2 ?_
    filter_upwards [X.PObj.continuous_smoothVal.continuousAt.eventually
      (R.isOpen_U.mem_nhds R.mem_U)] with z hzU
    exact R.Φ_one _ hzU
  inv_mem' {g} hg := by
    obtain ⟨R, -⟩ := X.theorem_7_1_13 (X.PObj.smoothVal y) isOpen_univ (mem_univ _)
    rw [X.mem_trivialSetInf_iff R] at hg ⊢
    filter_upwards [hg, X.PObj.continuous_smoothVal.continuousAt.eventually
      (R.isOpen_U.mem_nhds R.mem_U)] with z hgz hzU
    have h1 := R.Φ_inv_Φ g hzU
    rwa [hgz] at h1

theorem mem_trivialSubgroupInf_iff {y : X.PObj.SmoothLevel}
    (R : X.NaturalRep (X.PObj.smoothVal y)) {g : X.Isotropy (X.PObj.smoothVal y)} :
    g ∈ X.trivialSubgroupInf y ↔
      ∀ᶠ z in 𝓝 y, R.Φ g (X.PObj.smoothVal z) = X.PObj.smoothVal z :=
  X.mem_trivialSetInf_iff R

/-- `T_x ⊆ T_x^∞` (2021 p. 331). -/
theorem trivialSubgroup_le_trivialSubgroupInf (y : X.PObj.SmoothLevel) :
    X.trivialSubgroup (X.PObj.smoothVal y) ≤ X.trivialSubgroupInf y := fun g hg => by
  obtain ⟨R, -⟩ := X.theorem_7_1_13 (X.PObj.smoothVal y) isOpen_univ (mem_univ _)
  exact (X.mem_trivialSubgroupInf_iff R).2
    (X.PObj.continuous_smoothVal.continuousAt.eventually (R.actsTrivially_iff.1 hg))

/-! ### Definition 7.4.7 -/

/-- **2021 Definition 7.4.7, p. 331 (new in the 2021 edition)**: the alternative Zhou condition
(ZHOU').  For smooth `x` and `g ∈ G_x`, if `Tg` is the identity on `(T_xX)_∞` (the smooth points
of the M-polyfold `TX` in the fibre `T_xX`) then `g ∈ T_x^∞`. -/
def IsZhou' : Prop :=
  ∀ (y : X.PObj.SmoothLevel) (g : X.Isotropy (X.PObj.smoothVal y)),
    (∀ v ∈ X.PObj.tangentFiber (X.PObj.smoothIncl y 1) ∩ X.PObj.tangentPolyfold.smoothSet,
      X.tangentMor g.val v = v) → g ∈ X.trivialSubgroupInf y

/-! ### Witnesses -/

/-- (ZHOU) holds when every isotropy group acts trivially near its point. -/
theorem isZhou_of_trivialSubgroup_eq_top (h : ∀ x, X.trivialSubgroup x = ⊤) : X.IsZhou :=
  fun y g _ => by rw [h]; exact Subgroup.mem_top g

theorem isZhou'_of_trivialSubgroup_eq_top (h : ∀ x, X.trivialSubgroup x = ⊤) : X.IsZhou' :=
  fun y g _ => X.trivialSubgroup_le_trivialSubgroupInf y (by rw [h]; exact Subgroup.mem_top g)

/-- (ZHOU) holds when all isotropy groups are trivial. -/
theorem isZhou_of_subsingleton (h : ∀ x, Subsingleton (X.Isotropy x)) : X.IsZhou :=
  fun y g _ => by rw [Subsingleton.elim g 1]; exact Subgroup.one_mem _

theorem isZhou'_of_subsingleton (h : ∀ x, Subsingleton (X.Isotropy x)) : X.IsZhou' :=
  fun y g _ => by rw [Subsingleton.elim g 1]; exact Subgroup.one_mem _

/-- **Witness**: the trivial ep-groupoid of an M-polyfold satisfies (ZHOU). -/
theorem isZhou_trivial {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (P : MPolyfold Z) : (trivial P).IsZhou :=
  isZhou_of_subsingleton _ fun _ => inferInstance

/-- **Witness**: the trivial ep-groupoid of an M-polyfold satisfies (ZHOU'). -/
theorem isZhou'_trivial {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (P : MPolyfold Z) : (trivial P).IsZhou' :=
  isZhou'_of_subsingleton _ fun _ => inferInstance

/-- **Witness** with nontrivial isotropy: `ℤ/3` acting trivially satisfies (ZHOU). -/
theorem Examples.isZhou_trivialZ3 : Examples.trivialZ3EpGroupoid.IsZhou :=
  isZhou_of_trivialSubgroup_eq_top _ Examples.trivialSubgroup_trivialZ3

theorem Examples.isZhou'_trivialZ3 : Examples.trivialZ3EpGroupoid.IsZhou' :=
  isZhou'_of_trivialSubgroup_eq_top _ Examples.trivialSubgroup_trivialZ3

/-! ### The closure step through `X_∞` -/

/-- Two maps continuous at `a ∈ cl s` and equal on `s` agree at `a`. -/
theorem _root_.Polyfold.eq_of_mem_closure_of_continuousAt {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [T2Space β] {f g : α → β} {s : Set α} {a : α} (hf : ContinuousAt f a)
    (hg : ContinuousAt g a) (h : EqOn f g s) (ha : a ∈ closure s) : f a = g a := by
  by_contra hne
  obtain ⟨b, hbs, hb⟩ :=
    ((mem_closure_iff_frequently.1 ha).and_eventually ((hf.ne_iff_eventually_ne hg).1 hne)).exists
  exact hb (h hbs)

namespace NaturalRep

variable {X} {x : Obj} (R : X.NaturalRep x)

/-- **Unique continuation through `U(x)_∞`**: an open, nonempty `S ⊆ U(x)_∞` of points near which
`Φ(g)` is the identity and which is closed in `U(x)_∞` forces `Φ(g) = id` on `U(x)`. -/
theorem eq_self_of_smooth_clopen (hd : X.PObj.DenseSmooth) (hc : X.PObj.SmoothConnected)
    (g : X.Isotropy x) {S : Set X.PObj.SmoothLevel} (hSo : IsOpen S) (hSne : S.Nonempty)
    (hS : ∀ a ∈ S, X.PObj.smoothVal a ∈ R.U ∧ R.Φ g (X.PObj.smoothVal a) = X.PObj.smoothVal a)
    (hcl : ∀ z, X.PObj.smoothVal z ∈ R.U → z ∈ closure S → z ∈ S) :
    ∀ y ∈ R.U, R.Φ g y = y := by
  have hZ : X.PObj.smoothVal ⁻¹' R.U ⊆ S := by
    obtain ⟨a, ha⟩ := hSne
    exact (hc R.U R.isOpen_U R.isConnected_U).subset_of_closure_inter_subset hSo
      ⟨a, (hS a ha).1, ha⟩ fun z hz => hcl z hz.2 hz.1
  have hsm : EqOn (R.Φ g) id (R.U ∩ X.PObj.smoothSet) := fun y hy =>
    (hS _ (hZ (show X.PObj.smoothVal (X.PObj.smoothMk y hy.2) ∈ R.U from hy.1))).2
  have hall : EqOn (R.Φ g) id R.U := hsm.of_subset_closure
    (R.isScDiffeoOn_Φ g).isScSmoothOn.continuousOn continuousOn_id inter_subset_left
    (hd.subset_closure_inter R.isOpen_U)
  exact fun y hy => hall hy

end NaturalRep

end EpGroupoid

/-! ### The Part I facts as one hypothesis -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- The Part I facts used in §7.4 (2021 pp. 331–340), bundled: `X_∞` dense in every `X_m`,
`U ∩ X_∞` connected for connected open `U`, `p : TX → X¹` open (point G.8), and
`TangentDeterminedSmooth`.  Satisfiable: `smoothRegular_discrete_unit`,
`smoothRegular_of_subsingleton`. -/
structure SmoothRegular : Prop where
  denseSmooth : P.DenseSmooth
  smoothConnected : P.SmoothConnected
  isOpenMap_tangentProj : IsOpenMap P.tangentProj
  tangentDeterminedSmooth : P.TangentDeterminedSmooth

variable {P}

/-- **Witness**: an M-polyfold on a subsingleton all of whose points are smooth satisfies the Part I
facts. -/
theorem smoothRegular_of_subsingleton [Subsingleton X] (hs : P.smoothSet = univ) :
    P.SmoothRegular := by
  have hL : ∀ m, Subsingleton (P.Level m) := fun m =>
    ⟨fun a b => level_ext (Subsingleton.elim _ _)⟩
  have hS : Subsingleton P.SmoothLevel := ⟨fun a b => Subtype.ext (Subsingleton.elim a.1 b.1)⟩
  refine ⟨fun m => ?_, fun U _ _ => Set.subsingleton_of_subsingleton.isPreconnected,
    fun s _ => ?_, fun f₁ f₂ U₁ U₂ hf₁ hf₂ y hy₁ hy₂ _ v hv => ?_⟩
  · have : {y : P.Level m | P.levelVal m y ∈ P.smoothSet} = univ := by
      rw [hs]; rfl
    rw [this]; exact dense_univ
  · rcases (P.tangentProj '' s).eq_empty_or_nonempty with h | ⟨a, ha⟩
    · rw [h]; exact isOpen_empty
    · have : P.tangentProj '' s = univ := eq_univ_of_forall fun b => Subsingleton.elim a b ▸ ha
      rw [this]; exact isOpen_univ
  · have hvU : ∀ U : Set X, P.smoothVal y ∈ U → v ∈ P.tangentPreimage U := fun U hy => by
      change P.levelVal 1 (P.tangentProj v) ∈ U
      rw [show P.tangentProj v = P.smoothIncl y 1 from hv]; exact hy
    rw [tangentMapOn_eqOn_id hf₁ (fun _ _ => Subsingleton.elim _ _) (hvU U₁ hy₁),
      tangentMapOn_eqOn_id hf₂ (fun _ _ => Subsingleton.elim _ _) (hvU U₂ hy₂)]

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### Lemma 7.4.6, Proposition 7.4.8 -/

/-! ### Proposition 7.4.10 -/

/-! ### Smooth unique continuation -/

/-- Unique continuation through `X_∞` (the content of (VSLUC), used for `X¹`): if `ĝ` is the
identity on the smooth points of a nonempty open subset of `X_∞` inside `U(x)`, then `ĝ = id` on
`U(x)`.  Satisfiable: `isSmoothUC_trivial`. -/
def IsSmoothUC : Prop :=
  ∀ (x : Obj) (R : X.NaturalRep x) (g : X.Isotropy x) (W : Set X.PObj.SmoothLevel), IsOpen W →
    W.Nonempty →
    (∀ w ∈ W, X.PObj.smoothVal w ∈ R.U ∧ R.Φ g (X.PObj.smoothVal w) = X.PObj.smoothVal w) →
    ∀ y ∈ R.U, R.Φ g y = y

/-- Unique continuation through `X_∞` gives (LUC). -/
theorem isLUC_of_isSmoothUC (hd : X.PObj.DenseSmooth) (h : X.IsSmoothUC) : X.IsLUC := by
  rw [isLUC_iff_forall_naturalRep]
  intro x R g V hVo hVne hVU hV
  obtain ⟨w, hwV, hws⟩ := hd.dense.inter_open_nonempty V hVo hVne
  exact h x R g (X.PObj.smoothVal ⁻¹' V) (hVo.preimage X.PObj.continuous_smoothVal)
    ⟨X.PObj.smoothMk w hws, hwV⟩ fun w' hw' => ⟨hVU hw', hV _ hw'⟩

/-- Smooth unique continuation for `X` gives `(LUC)` for `X¹`: by 2021 Proposition 7.2.21 it
suffices that `(𝐗¹)^T = (𝐗^T)¹` is closed in `𝐗¹`. -/
theorem isLUC_liftOne_of_isSmoothUC (hd : X.PObj.DenseSmooth) (h : X.IsSmoothUC) :
    X.liftOne.IsLUC := by
  have hcl0 : IsClosed X.nonEffectivePart :=
    X.proposition_7_2_21.1 (X.isLUC_of_isSmoothUC hd h)
  have hT : X.liftOne.nonEffectivePart = X.PMor.levelVal 1 ⁻¹' X.nonEffectivePart := by
    ext φ
    refine ⟨fun hφ => ?_, X.mem_nonEffectivePart_liftOne_of_levelVal⟩
    have hst : X.liftOne.src φ = X.liftOne.tgt φ := src_eq_tgt_of_mem_nonEffectivePart hφ
    have hst0 : X.src (X.PMor.levelVal 1 φ) = X.tgt (X.PMor.levelVal 1 φ) :=
      congrArg (X.PObj.levelVal 1) hst
    let g : X.Isotropy (X.src (X.PMor.levelVal 1 φ)) := ⟨X.PMor.levelVal 1 φ, rfl, hst0.symm⟩
    obtain ⟨R, -⟩ := X.theorem_7_1_13 (X.src (X.PMor.levelVal 1 φ)) isOpen_univ (mem_univ _)
    have hx₁ : X.liftOne.src φ ∈ R.liftU := R.mem_U
    have hΓx : R.levelOneΓ g (X.liftOne.src φ) = φ :=
      MPolyfold.level_ext ((R.levelVal_levelOneΓ g hx₁).trans (R.Γ_self g))
    have hev := R.eventually_of_levelOneΓ_mem g hx₁ (by rw [hΓx]; exact hφ)
    obtain ⟨N, hNs, hNo, hxN⟩ := mem_nhds_iff.1 hev
    obtain ⟨y, hy⟩ := hd.exists_smooth hNo ⟨_, hxN⟩
    have hall := h _ R g ((fun a : X.PObj.SmoothLevel => X.PObj.smoothIncl a 1) ⁻¹' N)
      (hNo.preimage (X.PObj.continuous_smoothIncl 1)) ⟨y, hy⟩ fun w hw => hNs hw
    have hmem := R.Γ_mem_of_eventually R.mem_U
      (Filter.mem_of_superset (R.isOpen_U.mem_nhds R.mem_U) hall)
    rwa [R.Γ_self] at hmem
  refine X.liftOne.proposition_7_2_21.2 ?_
  rw [hT]
  exact hcl0.preimage (MPolyfold.continuous_levelVal 1)

/-! ### Corollary 7.4.11, Definition 7.4.12, Theorem 7.4.13 -/

end EpGroupoid

/-- **2021 Definition 7.4.12, p. 334 (new in the 2021 edition)**: the strong local unique
continuation property (SLUC), (LUC) for every `Xⁱ`.  Satisfiable: `Examples.isSLUC_pointEP`. -/
def EP.IsSLUC (A : EP.{u}) : Prop := ∀ i, (A.lift i).X.IsLUC

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### Definition 7.4.14, Lemma 7.4.15, Propositions 7.4.16–7.4.18 -/

/-- **2021 Definition 7.4.14, p. 335 (new in the 2021 edition)**: the very strong local unique
continuation property (VSLUC).  For smooth `x` there are a natural representation `U(x)` and an
open `V(x) ⊆ X_∞` inside it, containing `x` and invariant under `G_x`, such that `ĝ = id` on a
nonempty open subset of `V(x)` forces `ĝ = id` on `V(x)`.  Satisfiable: `isVSLUC_trivial`. -/
def IsVSLUC : Prop :=
  ∀ y : X.PObj.SmoothLevel, ∃ (R : X.NaturalRep (X.PObj.smoothVal y))
    (V : Set X.PObj.SmoothLevel), IsOpen V ∧ y ∈ V ∧ (∀ v ∈ V, X.PObj.smoothVal v ∈ R.U) ∧
    (∀ g, ∀ v ∈ V, ∀ v' : X.PObj.SmoothLevel,
      X.PObj.smoothVal v' = R.Φ g (X.PObj.smoothVal v) → v' ∈ V) ∧
    ∀ (g : X.Isotropy (X.PObj.smoothVal y)) (W : Set X.PObj.SmoothLevel), IsOpen W →
      W.Nonempty → W ⊆ V → (∀ w ∈ W, R.Φ g (X.PObj.smoothVal w) = X.PObj.smoothVal w) →
      ∀ v ∈ V, R.Φ g (X.PObj.smoothVal v) = X.PObj.smoothVal v

/-- The core of 2021 Lemma 7.4.15: (VSLUC) gives unique continuation through `X_∞`. -/
theorem isSmoothUC_of_isVSLUC (hd : X.PObj.DenseSmooth) (hc : X.PObj.SmoothConnected)
    (h : X.IsVSLUC) : X.IsSmoothUC := by
  intro x R g W hWo hWne hW
  set S := {z : X.PObj.SmoothLevel | ∀ᶠ w in 𝓝 z,
    X.PObj.smoothVal w ∈ R.U ∧ R.Φ g (X.PObj.smoothVal w) = X.PObj.smoothVal w}
  have hSo : IsOpen S := isOpen_setOfPred_eventually_nhds
  obtain ⟨w₀, hw₀⟩ := hWne
  refine R.eq_self_of_smooth_clopen hd hc g hSo ⟨w₀, ?_⟩ (fun a ha => ha.self_of_nhds)
    (fun z hz hzc => ?_)
  · filter_upwards [hWo.mem_nhds hw₀] with w hw using hW w hw
  have hfix : R.Φ g (X.PObj.smoothVal z) = X.PObj.smoothVal z :=
    eq_of_mem_closure_of_continuousAt (f := fun a => R.Φ g (X.PObj.smoothVal a))
      (((R.isScDiffeoOn_Φ g).isScSmoothOn.continuousOn.continuousAt
        (R.isOpen_U.mem_nhds hz)).comp X.PObj.continuous_smoothVal.continuousAt)
      X.PObj.continuous_smoothVal.continuousAt (fun a ha => ha.self_of_nhds.2) hzc
  obtain ⟨Rz, V, hVo, hzV, -, -, hLUC⟩ := h z
  have hcomp := X.PObj.continuous_smoothVal.continuousAt.eventually
    (R.eventually_Φ_eq_Γ Rz hz g (R.isoΓ g hz hfix) rfl)
  obtain ⟨N, hNs, hNo, hzN⟩ := mem_nhds_iff.1 hcomp
  obtain ⟨a, ⟨haV, haN⟩, haS⟩ := mem_closure_iff.1 hzc (V ∩ N) (hVo.inter hNo) ⟨hzV, hzN⟩
  have hid := hLUC (R.isoΓ g hz hfix) (V ∩ N ∩ S) ((hVo.inter hNo).inter hSo)
    ⟨a, ⟨haV, haN⟩, haS⟩ (fun w hw => hw.1.1) fun w hw => by
      rw [(hNs hw.1.2).2.2]; exact hw.2.self_of_nhds.2
  filter_upwards [(hVo.inter hNo).mem_nhds ⟨hzV, hzN⟩] with w hw
  refine ⟨(hNs hw.2).1, ?_⟩
  rw [← (hNs hw.2).2.2]
  exact hid w hw.1

/-- Unique continuation through `X_∞` gives (VSLUC), with `V(x) = U(x) ∩ X_∞`. -/
theorem isVSLUC_of_isSmoothUC (h : X.IsSmoothUC) : X.IsVSLUC := by
  intro y
  obtain ⟨R, -⟩ := X.theorem_7_1_13 (X.PObj.smoothVal y) isOpen_univ (mem_univ _)
  refine ⟨R, X.PObj.smoothVal ⁻¹' R.U, R.isOpen_U.preimage X.PObj.continuous_smoothVal, R.mem_U,
    fun v hv => hv, fun g v hv v' hv' => ?_, fun g W hWo hWne hWV hW v hv => ?_⟩
  · change X.PObj.smoothVal v' ∈ R.U
    rw [hv']; exact R.mapsTo_Φ g hv
  · exact h _ R g W hWo hWne (fun w hw => ⟨hWV hw, hW w hw⟩) _ hv

/-- **2021 Lemma 7.4.15, p. 335 (new in the 2021 edition)**: (VSLUC) ⇒ (LUC). -/
theorem lemma_7_4_15 (hd : X.PObj.DenseSmooth) (hc : X.PObj.SmoothConnected)
    (h : X.IsVSLUC) : X.IsLUC :=
  X.isLUC_of_isSmoothUC hd (X.isSmoothUC_of_isVSLUC hd hc h)

/-- **2021 Proposition 7.4.16, p. 336 (new in the 2021 edition), for `X¹`**: (VSLUC) gives (LUC)
for `X` and `X¹`. -/
theorem proposition_7_4_16 (hd : X.PObj.DenseSmooth) (hc : X.PObj.SmoothConnected)
    (h : X.IsVSLUC) : X.IsLUC ∧ X.liftOne.IsLUC :=
  ⟨X.lemma_7_4_15 hd hc h, X.isLUC_liftOne_of_isSmoothUC hd (X.isSmoothUC_of_isVSLUC hd hc h)⟩

/-- **2021 Proposition 7.4.17, p. 336 (new in the 2021 edition)**: (VSLUC) ⇒ (SLUC), with (VSLUC)
for every `Xⁱ` (Proposition 7.4.16) as a hypothesis. -/
theorem proposition_7_4_17 (A : EP.{u}) (h : ∀ i, (A.lift i).X.IsVSLUC)
    (hd : ∀ i, (A.lift i).X.PObj.DenseSmooth) (hc : ∀ i, (A.lift i).X.PObj.SmoothConnected) :
    A.IsSLUC := fun i => (A.lift i).X.lemma_7_4_15 (hd i) (hc i) (h i)

/-! ### Corollary 7.6.8 without the hypothesis "(ZHOU) ⇒ LUC for `X¹`" -/

/-! ### Witnesses -/

/-- Unique continuation through `X_∞` holds when all isotropy groups are trivial. -/
theorem isSmoothUC_of_subsingleton (h : ∀ x, Subsingleton (X.Isotropy x)) : X.IsSmoothUC :=
  fun _ R g _ _ _ _ y hy => by rw [Subsingleton.elim g 1]; exact R.Φ_one y hy

/-- (VSLUC) holds when all isotropy groups are trivial. -/
theorem isVSLUC_of_subsingleton (h : ∀ x, Subsingleton (X.Isotropy x)) : X.IsVSLUC :=
  X.isVSLUC_of_isSmoothUC (X.isSmoothUC_of_subsingleton h)

/-- (LUC) holds when there is at most one morphism. -/
theorem isLUC_of_subsingleton_mor [Subsingleton Mor] : X.IsLUC :=
  X.proposition_7_2_21.2 (Set.Subsingleton.isClosed fun _ _ _ _ => Subsingleton.elim _ _)

/-- **Witness**: the trivial ep-groupoid of an M-polyfold satisfies (VSLUC). -/
theorem isVSLUC_trivial {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (P : MPolyfold Z) : (trivial P).IsVSLUC :=
  isVSLUC_of_subsingleton _ fun _ => inferInstance

/-- **Witness**: the trivial ep-groupoid satisfies unique continuation through `X_∞`. -/
theorem isSmoothUC_trivial {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (P : MPolyfold Z) : (trivial P).IsSmoothUC :=
  isSmoothUC_of_subsingleton _ fun _ => inferInstance

end EpGroupoid

namespace MPolyfold

/-- **Witness** for `DenseSmoothTangent`: every tangent vector of the one-point M-polyfold is
smooth. -/
theorem denseSmoothTangent_discrete_unit : (discretePolyfold Unit).DenseSmoothTangent := by
  intro y v hv
  refine subset_closure ⟨hv, mem_iInter.2 fun m => ?_⟩
  have hc := (discretePolyfold Unit).tangentPolyfold_isChart (isChart_discreteChart ()) v
  rw [(discretePolyfold Unit).tangentPolyfold.mem_levelSet_iff hc (by
    change (discretePolyfold Unit).levelVal 1 _ ∈ ({()} : Set Unit); exact rfl)]
  refine ⟨0, ?_⟩
  apply Prod.ext
  · exact Subsingleton.elim (α := Fin 0 → ℝ) _ _
  · exact Subsingleton.elim (α := Fin 0 → ℝ) _ _

/-- **Witness** for `SmoothRegular`: the one-point M-polyfold. -/
theorem smoothRegular_discrete_unit : (discretePolyfold Unit).SmoothRegular :=
  smoothRegular_of_subsingleton discretePolyfold_smoothSet

end MPolyfold

namespace EpGroupoid.Examples

/-- The point ep-groupoid as an object of `EP`. -/
def pointEP : EP.{0} where
  Obj := Unit
  Mor := Unit
  X := pointEpGroupoid

/-- All lifts of the point ep-groupoid have at most one object and one morphism, all smooth. -/
theorem lift_pointEP (i : ℕ) : Subsingleton (pointEP.lift i).Obj ∧
    Subsingleton (pointEP.lift i).Mor ∧ (pointEP.lift i).X.PObj.smoothSet = univ := by
  induction i with
  | zero => exact ⟨inferInstanceAs (Subsingleton Unit), inferInstanceAs (Subsingleton Unit),
      (discretePolyfold_smoothSet (G := Unit) :)⟩
  | succ i ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨⟨fun a b => MPolyfold.level_ext (Subsingleton.elim _ _)⟩,
      ⟨fun a b => MPolyfold.level_ext (Subsingleton.elim _ _)⟩, ?_⟩
    refine eq_univ_of_forall fun y => (MPolyfold.mem_shift_smoothSet_iff y).2 ?_
    rw [h3]; exact mem_univ _

/-- **Witness**: the Part I facts hold for all lifts of the point ep-groupoid. -/
theorem smoothRegular_lift_pointEP (i : ℕ) : (pointEP.lift i).X.PObj.SmoothRegular := by
  obtain ⟨h1, -, h3⟩ := lift_pointEP i
  exact MPolyfold.smoothRegular_of_subsingleton h3

/-- **Witness**: (ZHOU) holds for all lifts of the point ep-groupoid. -/
theorem isZhou_lift_pointEP (i : ℕ) : (pointEP.lift i).X.IsZhou := by
  obtain ⟨-, h2, -⟩ := lift_pointEP i
  exact isZhou_of_subsingleton _ fun x =>
    ⟨fun a b => GroupoidStr.Isotropy.ext (Subsingleton.elim a.val b.val)⟩

/-- **Witness** for (SLUC). -/
theorem isSLUC_pointEP : pointEP.IsSLUC := fun i => by
  obtain ⟨-, h2, -⟩ := lift_pointEP i
  exact isLUC_of_subsingleton_mor _

end EpGroupoid.Examples

/-! ## The local regularity condition -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **2021 Definition 7.4.19, p. 337 (new in the 2021 edition)**: the local regularity property
(LR).  Inside every open `O ∋ x` there is a natural representation `U(x)` such that every
sc-diffeomorphism `β : U(x) → U(x)` with `|β(y)| = |y|` is `ĝ` for some `g ∈ G_x`.
Satisfiable: `Examples.isSLR_pointEP`. -/
def IsLR : Prop :=
  ∀ (x : Obj) (O : Set Obj), IsOpen O → x ∈ O → ∃ R : X.NaturalRep x, R.U ⊆ O ∧
    ∀ β β' : Obj → Obj, X.PObj.IsScDiffeoOn X.PObj β β' R.U R.U →
      (∀ y ∈ R.U, X.π (β y) = X.π y) → ∃ g : X.Isotropy x, ∀ y ∈ R.U, β y = R.Φ g y

/-- **2021 Definition 7.4.21, p. 338 (new in the 2021 edition)**: (LR'), for sc-diffeomorphisms
`β` of `U(x)` onto an open image with `β(x) = x` and `|β(y)| = |y|`. -/
def IsLR' : Prop :=
  ∀ (x : Obj) (O : Set Obj), IsOpen O → x ∈ O → ∃ R : X.NaturalRep x, R.U ⊆ O ∧
    ∀ β β' : Obj → Obj, X.PObj.IsScDiffeoOn X.PObj β β' R.U (β '' R.U) → β x = x →
      (∀ y ∈ R.U, X.π (β y) = X.π y) → ∃ g : X.Isotropy x, ∀ y ∈ R.U, β y = R.Φ g y

namespace NaturalRep

variable {X} {x : Obj} (R : X.NaturalRep x)

/-- Two points of `U(x)` with the same orbit are related by the natural action. -/
theorem exists_Φ_eq_of_π_eq {y z : Obj} (hy : y ∈ R.U) (hz : z ∈ R.U) (h : X.π z = X.π y) :
    ∃ g : X.Isotropy x, z = R.Φ g y := by
  obtain ⟨φ, hφs, hφt⟩ := (X.π_eq_π_iff.1 h).symm
  obtain ⟨g, hg, -⟩ := R.existsUnique_Γ φ (hφs ▸ hy) (hφt ▸ hz)
  refine ⟨g, ?_⟩
  rw [← R.tgt_Γ g y hy, ← hφs, hg, hφt]

/-- The only point of `U(x)` in the orbit of `x` is `x`. -/
theorem eq_self_of_π_eq {z : Obj} (hz : z ∈ R.U) (h : X.π z = X.π x) : z = x := by
  obtain ⟨g, hg⟩ := R.exists_Φ_eq_of_π_eq R.mem_U hz h
  rw [hg, R.Φ_self]

end NaturalRep

/-- **2021 Lemma 7.4.20** -/
theorem lemma_7_4_20 {x : Obj} (R : X.NaturalRep x) {β β' : Obj → Obj}
    (hβ : X.PObj.IsScDiffeoOn X.PObj β β' R.U (β '' R.U)) (hx : β x = x)
    (hπ : ∀ y ∈ R.U, X.π (β y) = X.π y) :
    β '' R.U = R.U ∧ X.PObj.IsScDiffeoOn X.PObj β β' R.U R.U := by
  have hβc : ContinuousOn β R.U := hβ.isScSmoothOn.continuousOn
  -- Step 1: `β(U) ⊆ U`.
  have h1 : R.U ⊆ R.U ∩ β ⁻¹' R.U := by
    refine R.isConnected_U.isPreconnected.subset_of_closure_inter_subset
      (hβc.isOpen_inter_preimage R.isOpen_U R.isOpen_U)
      ⟨x, R.mem_U, R.mem_U, by rw [mem_preimage, hx]; exact R.mem_U⟩ ?_
    rintro y ⟨hyc, hyU⟩
    have hcov : R.U ∩ β ⁻¹' R.U ⊆ ⋃ g : X.Isotropy x, {a | a ∈ R.U ∧ β a = R.Φ g a} := by
      rintro a ⟨haU, haβ⟩
      obtain ⟨g, hg⟩ := R.exists_Φ_eq_of_π_eq haU haβ (hπ a haU)
      exact mem_iUnion.2 ⟨g, haU, hg⟩
    have hyc' := closure_mono hcov hyc
    rw [closure_iUnion_of_finite] at hyc'
    obtain ⟨g, hg⟩ := mem_iUnion.1 hyc'
    have hyg : β y = R.Φ g y := eq_of_mem_closure_of_continuousAt
      (hβc.continuousAt (R.isOpen_U.mem_nhds hyU))
      ((R.continuousOn_Φ g).continuousAt (R.isOpen_U.mem_nhds hyU)) (fun a ha => ha.2) hg
    exact ⟨hyU, by rw [mem_preimage, hyg]; exact R.mapsTo_Φ g hyU⟩
  -- Step 2: `U ⊆ β(U)`.
  have h2 : R.U ⊆ β '' R.U := by
    refine R.isConnected_U.isPreconnected.subset_of_closure_inter_subset
      hβ.isScSmoothOn_inv.isOpen ⟨x, R.mem_U, x, R.mem_U, hx⟩ ?_
    rintro y ⟨hyc, hyU⟩
    have hcov : β '' R.U ⊆ ⋃ g : X.Isotropy x, {b | b ∈ R.U ∧ β (R.Φ g⁻¹ b) = b} := by
      rintro _ ⟨a, haU, rfl⟩
      obtain ⟨g, hg⟩ := R.exists_Φ_eq_of_π_eq haU (h1 haU).2 (hπ a haU)
      refine mem_iUnion.2 ⟨g, (h1 haU).2, ?_⟩
      rw [hg, R.Φ_inv_Φ g haU]
      exact hg
    have hyc' := closure_mono hcov hyc
    rw [closure_iUnion_of_finite] at hyc'
    obtain ⟨g, hg⟩ := mem_iUnion.1 hyc'
    have hgy : R.Φ g⁻¹ y ∈ R.U := R.mapsTo_Φ g⁻¹ hyU
    have heq : β (R.Φ g⁻¹ y) = y := eq_of_mem_closure_of_continuousAt (f := fun b => β (R.Φ g⁻¹ b))
      ((hβc.continuousAt (R.isOpen_U.mem_nhds hgy)).comp
        ((R.continuousOn_Φ g⁻¹).continuousAt (R.isOpen_U.mem_nhds hyU)))
      continuousAt_id (fun b hb => hb.2) hg
    exact ⟨_, hgy, heq⟩
  have himg : β '' R.U = R.U :=
    Subset.antisymm (image_subset_iff.2 fun y hy => (h1 hy).2) h2
  refine ⟨himg, ?_⟩
  have hβ' := hβ
  rw [himg] at hβ'
  exact hβ'

/-- **2021 p. 338**: (LR) = (LR'). -/
theorem isLR_iff_isLR' : X.IsLR ↔ X.IsLR' := by
  constructor
  · intro h x O hO hxO
    obtain ⟨R, hRO, hR⟩ := h x O hO hxO
    exact ⟨R, hRO, fun β β' hβ hx hπ => hR β β' (X.lemma_7_4_20 R hβ hx hπ).2 hπ⟩
  · intro h x O hO hxO
    obtain ⟨R, hRO, hR⟩ := h x O hO hxO
    refine ⟨R, hRO, fun β β' hβ hπ => ?_⟩
    have himg : β '' R.U = R.U := Subset.antisymm (image_subset_iff.2 hβ.mapsTo)
      fun y hy => ⟨β' y, hβ.mapsTo_inv hy, hβ.right_inv y hy⟩
    refine hR β β' (by rw [himg]; exact hβ) ?_ hπ
    exact R.eq_self_of_π_eq (hβ.mapsTo R.mem_U) (hπ x R.mem_U)

end EpGroupoid

/-- **2021 Definition 7.4.23, p. 339 (new in the 2021 edition)**: the strong local regularity
property (SLR), (LR) for every `Xⁱ`. -/
def EP.IsSLR (A : EP.{u}) : Prop := ∀ i, (A.lift i).X.IsLR

/-! ### Witnesses for the hypotheses of Lemma 7.4.4, Proposition 7.4.8 and Corollary 7.6.8 -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **Witness**: `HasLevelOneConnectedDenseReps` holds when there is at most one object, and it is
smooth. -/
theorem hasLevelOneConnectedDenseReps_of_subsingleton [Subsingleton Obj]
    (hs : X.PObj.smoothSet = univ) : X.HasLevelOneConnectedDenseReps := fun x => by
  obtain ⟨R, -⟩ := X.theorem_7_1_13 x isOpen_univ (mem_univ _)
  refine ⟨R, Set.Subsingleton.isPreconnected fun _ _ _ _ =>
    MPolyfold.level_ext (Subsingleton.elim _ _), ?_⟩
  have h1 : X.PObj.levelSet 1 = univ := eq_univ_of_forall fun y =>
    MPolyfold.smoothSet_subset_levelSet 1 (by rw [hs]; exact mem_univ y)
  rw [h1, inter_univ]
  exact subset_closure

namespace Examples

/-- **Witness** for the hypotheses of `lemma_7_4_4`: all lifts of the point ep-groupoid. -/
theorem hasLevelOneConnectedDenseReps_lift_pointEP (i : ℕ) :
    (pointEP.lift i).X.HasLevelOneConnectedDenseReps := by
  obtain ⟨h1, -, h3⟩ := lift_pointEP i
  exact (pointEP.lift i).X.hasLevelOneConnectedDenseReps_of_subsingleton h3

/-- The hypotheses of `lemma_7_4_4` are satisfiable. -/
theorem lemma_7_4_4_pointEP (i : ℕ) : pointEP.X.IsLUC ∧ ∀ k ≤ i, (pointEP.lift k).X.IsLUC :=
  lemma_7_4_4 pointEP i (fun k _ => hasLevelOneConnectedDenseReps_lift_pointEP k)
    (isSLUC_pointEP i)

end Examples

end EpGroupoid

end Polyfold
