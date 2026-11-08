import Polyfold.Chapter2.TangentLift
import Polyfold.Chapter4.VectorFieldsGlobal

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §2.3
"M-Polyfolds and Sub-M-Polyfolds": **Proposition 2.3.17** (p. 42, new in the 2021 edition) for
every `i`, with the discussion before it (pp. 40–42); and, from §4.4 "Sc-Differential Forms",
**Lemma 4.4.4** (p. 196, new in the 2021 edition) for every `i`.  Numbers and pages are the 2021
text's.  The cases `i = 1` (and `i = 2` of Proposition 2.3.17) are in
`Polyfold/Chapter2/TangentLift.lean` and `Polyfold/Chapter4/VectorFieldsGlobal.lean`.

# The tangent of the lifts: `T(Xⁱ) ≡ (TX)ⁱ` for every `i`

## The text, paraphrased

(pp. 40–42) The sc-smooth inclusions `X^{i+1} → X^i` induce inclusions `T(X^{i+1}) → T(X^i)`
covering `X^{i+2} → X^{i+1}`; the lifts of `TX` give `(TX)^{i+1} → (TX)^i` over the same maps.
The two towers are the same up to natural identifications: in a local model `(TO)^i = T(O^i)`,
compatibly with the tangent charts.  (Proposition 2.3.17) There is a natural identification of
`(TX)^i` with `T(X^i)`, and of the M-polyfold bundles `(TX)^i → (X¹)^i` and `T(X^i) → (X^i)¹`,
covering the natural identification `(X¹)^i ≡ (X^i)¹`.

(Lemma 4.4.4, p. 196) By this identification the index of an sc-smooth vector field `A` (a section
of `TX → X¹`) can be raised by any `i ≥ 0`: `A^(i)` is an sc-smooth vector field of `X^i`, a
section of `T(X^i) → X^{i+1}`.

## What is formalized

* `MPolyfold.ScEquiv` (an sc-diffeomorphism as an equivalence sc-smooth in both directions;
  `refl`, `symm`, `trans`, `isScDiffeoOn`, and `ScEquiv.shift`, the index raise of
  `levelOneEquiv`), `MPolyfold.ScMap` (an sc-smooth map, `ScMap.shift`),
  `MPolyfold.tangentShiftScEquiv` (`Φ : T(X¹) ≃ (TX)¹` of Proposition 2.3.17 for `i = 1`) and
  `MPolyfold.tangentProjScMap` (`p : TX → X¹`).
* `MPolyfold.tangentLower_tangentMap`: **the inclusion `T(X¹) → TX` is natural**, i.e.
  `ι ∘ T(f¹) = Tf ∘ ι` for an sc-smooth `f : X → Y` (a chart computation through
  `toBase_retractTangentMap_shift`).
* `BundledMPolyfold` (an M-polyfold with its space), `BundledMPolyfold.lift` (`X^i`, by iterating
  `shift`), `BundledMPolyfold.tangent` (`TX`), the inclusions `incl : X^i → X` (injective,
  `incl_injective`) and `tangentIncl : T(X^i) → TX` (the composite of the inclusions
  `T(X^{k+1}) → T(X^k)`, `MPolyfold.tangentLower`), `liftMap` (`f^i`), `tangentProjLift` (`p^i`).
* `BundledMPolyfold.tangentLiftEquiv` (`Φ_i : T(X^i) ≃ (TX)^i`, an `ScEquiv`, by recursion:
  `Φ_{i+1} = (Φ_i)¹ ∘ Φ`), `BundledMPolyfold.shiftLiftEquiv` (`J_i : (X¹)^i ≃ (X^i)¹`), and
  `levelVal_tangentLiftEquiv_succ`, `incl_tangentLiftEquiv`, `incl_shiftLiftEquiv`,
  `tangentProjLift_tangentLiftEquiv`, `tangentLiftEquiv_unique`, `tangentLiftEquiv_one`,
  `tangentIncl_tangentMap`, `tangentLiftEquiv_natural`.
* **`proposition_2_3_17_all_2021`** (Proposition 2.3.17 for every `i`).
* `BundledMPolyfold.raiseIndexAll` (`A^(i)`, by recursion: `A^(i+1) = (A^(i))^(1)`,
  `MPolyfold.raiseIndex`), `tangentIncl_raiseIndexAll`, `tangentLiftEquiv_raiseIndexAll`, and
  **`lemma_4_4_4_all_2021`** (Lemma 4.4.4 for every `i`).
* Witnesses: `BundledMPolyfold.nonempty` (a bundled M-polyfold exists: the half-line
  `MPolyfold.quadrantPolyfold 1 W`), `lemma_4_4_4_all_2021_zero` (the zero vector field; with
  `MPolyfold.isScVectorField_zero` the hypothesis of Lemma 4.4.4 is satisfiable).  `ScEquiv` and
  `ScMap` have the witnesses `ScEquiv.refl`, `tangentShiftScEquiv`, `tangentProjScMap`.

## What the text leaves implicit, and the choices made

* `X^i` is the iterate `(X¹)¹⋯` of `MPolyfold.shift`; to have one statement for all `i` the
  M-polyfolds are bundled with their spaces (`BundledMPolyfold`, as `EP` bundles ep-groupoids),
  so that `X^i` is a function of `i`.  `BundledMPolyfold.of P` bundles a given `P`.
* "Natural identification" is read as: an sc-diffeomorphism `Φ_i : T(X^i) → (TX)^i` (part (1))
  which commutes with the inclusions of the two towers of the text (part (5): the inclusion
  `(TX)^{i+1} → (TX)^i` after `Φ_{i+1}` is `Φ_i` after `T(X^{i+1}) → T(X^i)`), hence with their
  composites into `TX` (part (4)); this determines `Φ_i` (part (7)).  `Φ_1` is the map of
  `TangentLift.lean` (`tangentLiftEquiv_one`), which in the charts `T(φ¹)`, `(Tφ)¹` is the identity
  of `T(O¹) = (TO)¹` (`proposition_2_3_17_2021` (5)); `Φ_i` is a composite of index raises of such
  maps.  It is natural in `X` as well: `Φ_i ∘ T(f^i) = (Tf)^i ∘ Φ_i` (`tangentLiftEquiv_natural`).
* `(X¹)^i ≡ (X^i)¹` is the sc-diffeomorphism `J_i`, the identity on the points of `X`
  (`incl_shiftLiftEquiv`).  "Covering" is `J_i ∘ p^i ∘ Φ_i = p_{X^i}` (part (3)), where
  `p^i : (TX)^i → (X¹)^i` is the `i`-th index raise of `p : TX → X¹`; both projections are
  sc-smooth (part (2)).  The linear structure of the fibres is not part of the statement (the
  project has no linear structure on `T_xX`).
* Lemma 4.4.4: `A^(i)` is defined by iterating the case `i = 1` (`raiseIndex` on `X^i`); "it is
  `A`" is read as: its image under `T(X^i) → TX` at `x ∈ X^{i+1}` is `A(x)`, and, through the
  identifications, `Φ_i ∘ A^(i) ∘ J_i` is the `i`-th index raise of `A : X¹ → TX` (the diagram
  printed before the lemma).
-/

open Set Function

noncomputable section

namespace Polyfold

universe u v w

namespace MPolyfold

/-! ### sc-diffeomorphisms and sc-smooth maps, bundled -/

section ScEquivSec

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}

variable (P Q) in
/-- An sc-diffeomorphism `X ≃ Y` of M-polyfolds: an equivalence which is sc-smooth in both
directions.  Witnesses: `ScEquiv.refl`, `tangentShiftScEquiv`. -/
structure ScEquiv extends X ≃ Y where
  isScSmoothMap_toFun : P.IsScSmoothMap Q toFun
  isScSmoothMap_invFun : Q.IsScSmoothMap P invFun

variable (P Q) in
/-- An sc-smooth map `X → Y`, bundled.  Witness: `tangentProjScMap`. -/
structure ScMap where
  toFun : X → Y
  isScSmoothMap : P.IsScSmoothMap Q toFun

namespace ScEquiv

instance : CoeFun (ScEquiv P Q) (fun _ => X → Y) := ⟨fun e => e.toFun⟩

variable (P) in
/-- The identity. -/
def refl : ScEquiv P P := ⟨Equiv.refl X, isScSmoothMap_id, isScSmoothMap_id⟩

/-- The inverse. -/
def symm (e : ScEquiv P Q) : ScEquiv Q P :=
  ⟨e.toEquiv.symm, e.isScSmoothMap_invFun, e.isScSmoothMap_toFun⟩

/-- The composite. -/
def trans (e : ScEquiv P Q) (e' : ScEquiv Q S) : ScEquiv P S where
  toEquiv := e.toEquiv.trans e'.toEquiv
  isScSmoothMap_toFun := IsScSmoothMap.comp (f := e.toFun) (g := e'.toFun) e'.isScSmoothMap_toFun
    e.isScSmoothMap_toFun
  isScSmoothMap_invFun := IsScSmoothMap.comp (f := e'.invFun) (g := e.invFun)
    e.isScSmoothMap_invFun e'.isScSmoothMap_invFun

@[simp] lemma refl_apply (x : X) : ScEquiv.refl P x = x := rfl

@[simp] lemma trans_apply (e : ScEquiv P Q) (e' : ScEquiv Q S) (x : X) :
    e.trans e' x = e' (e x) := rfl

/-- An `ScEquiv` is an sc-diffeomorphism. -/
theorem isScDiffeoOn (e : ScEquiv P Q) : P.IsScDiffeoOn Q e e.invFun univ univ :=
  ⟨e.isScSmoothMap_toFun, e.isScSmoothMap_invFun, mapsTo_univ _ _, mapsTo_univ _ _,
    fun x _ => e.left_inv x, fun y _ => e.right_inv y⟩

/-- **Raising the index of an sc-diffeomorphism**: `e¹ : X¹ ≃ Y¹` (`levelOneEquiv`). -/
def shift (e : ScEquiv P Q) : ScEquiv P.shift Q.shift :=
  ⟨levelOneEquiv e.toEquiv e.isScSmoothMap_toFun e.isScSmoothMap_invFun,
    IsScSmoothMap.levelOne e.isScSmoothMap_toFun fun _ => rfl,
    IsScSmoothMap.levelOne e.isScSmoothMap_invFun fun _ => rfl⟩

@[simp] lemma levelVal_shift (e : ScEquiv P Q) (y : P.Level 1) :
    Q.levelVal 1 (e.shift y) = e (P.levelVal 1 y) := rfl

end ScEquiv

namespace ScMap

instance : CoeFun (ScMap P Q) (fun _ => X → Y) := ⟨fun f => f.toFun⟩

/-- **Raising the index of an sc-smooth map**: `f¹ : X¹ → Y¹`. -/
def shift (f : ScMap P Q) : ScMap P.shift Q.shift :=
  ⟨fun x => Q.levelMk 1 (f (P.levelVal 1 x)) (f.isScSmoothMap.mapsTo_levelSet 1 (P.levelVal_mem x)),
    IsScSmoothMap.levelOne f.isScSmoothMap fun _ => rfl⟩

@[simp] lemma levelVal_shift (f : ScMap P Q) (y : P.Level 1) :
    Q.levelVal 1 (f.shift y) = f (P.levelVal 1 y) := rfl

end ScMap

variable (P) in
/-- `Φ : T(X¹) ≃ (TX)¹` (2021 Proposition 2.3.17 for `i = 1`, `tangentShiftEquiv`) as an
`ScEquiv`. -/
def tangentShiftScEquiv : ScEquiv P.shift.tangentPolyfold P.tangentPolyfold.shift :=
  ⟨tangentShiftEquiv, tangentShiftMap_isScSmooth, tangentShiftEquiv_symm_isScSmooth⟩

variable (P) in
/-- The tangent projection `p : TX → X¹` as an `ScMap`. -/
def tangentProjScMap : ScMap P.tangentPolyfold P.shift :=
  ⟨P.tangentProj, P.tangentProj_isScSmooth⟩

end ScEquivSec

/-! ### Naturality of the inclusion `T(X¹) → TX` -/

section Naturality

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {f : X → Y} {f₁ : P.Level 1 → Q.Level 1}

/-- **The inclusion `ι : T(X¹) → TX` is natural** (2021 p. 41, the inclusions of the tangent
spaces): for an sc-smooth `f : X → Y` and its index raise `f¹ : X¹ → Y¹`, `ι ∘ T(f¹) = Tf ∘ ι`.
In charts this is `T(g¹) = (Tg)¹` for `g = ψ ∘ f ∘ φ⁻¹` (`toBase_retractTangentMap_shift`). -/
theorem tangentLower_tangentMap (hf : P.IsScSmoothMap Q f)
    (hf₁ : ∀ x, Q.levelVal 1 (f₁ x) = f (P.levelVal 1 x)) (α : P.shift.TangentSpace) :
    tangentLower (tangentMap (IsScSmoothMap.levelOne hf hf₁) α) =
      tangentMap hf (tangentLower α) := by
  have hf1s : P.shift.IsScSmoothMap Q.shift f₁ := IsScSmoothMap.levelOne hf hf₁
  set x₀ : P.Level 1 := P.shift.levelVal 1 (P.shift.tangentProj α) with hx₀
  obtain ⟨φ, hφ, hx⟩ := P.exists_isChart_mem_source (P.levelVal 1 x₀)
  obtain ⟨ψ, hψ, hfx⟩ := Q.exists_isChart_mem_source (f (P.levelVal 1 x₀))
  set V := TangentPre.fdom φ f ψ with hVdef
  have hVo : IsOpen V := TangentPre.isOpen_fdom hf φ ψ
  have hVφ : V ⊆ φ.source := inter_subset_left
  have hxV : P.levelVal 1 x₀ ∈ V := ⟨hx, hfx⟩
  have hg := TangentPre.isScSmoothRetractMap_coord hf hφ hψ subset_rfl hVo
  have hO := φ.isScRetract_image hVφ hVo
  set χ := levelChart hφ x₀ with hχdef
  have hχ : P.shift.IsChart χ := P.shift_isChart hφ x₀
  set ω := levelChart hψ (f₁ x₀) with hωdef
  have hω : Q.shift.IsChart ω := Q.shift_isChart hψ (f₁ x₀)
  have hbase : shiftBase (tangentMap hf1s α) = f (P.levelVal 1 x₀) := by
    change Q.levelVal 1 (Q.shift.levelVal 1 (Q.shift.tangentProj (tangentMap hf1s α))) = _
    rw [levelVal_tangentProj_tangentMap hf1s α, hf₁]
  have hαχ : α ∈ tangentChartSet (P := P.shift) χ := hx
  have hTαω : f₁ (P.shift.levelVal 1 (P.shift.tangentProj α)) ∈ ω.source := by
    change Q.levelVal 1 (f₁ x₀) ∈ ψ.source
    rw [hf₁]; exact hfx
  have hLα : tangentLower α ∈ tangentChartSet (P := P) φ := tangentLower_mem_tangentChartSet hx
  have hfLα : f (P.levelVal 1 (P.tangentProj (tangentLower α))) ∈ ψ.source := by
    rw [tangentProj_tangentLower]; exact hfx
  have hRψ : tangentMap hf (tangentLower α) ∈ tangentChartSet (P := Q) ψ := by
    change Q.levelVal 1 (Q.tangentProj (tangentMap hf (tangentLower α))) ∈ ψ.source
    rw [levelVal_tangentProj_tangentMap]; exact hfLα
  have hbψ : shiftBase (tangentMap hf1s α) ∈ ψ.source := by rw [hbase]; exact hfx
  have hLψ : tangentLower (tangentMap hf1s α) ∈ tangentChartSet (P := Q) ψ :=
    tangentLower_mem_tangentChartSet hbψ
  refine tangentChartMap_injOn hψ hLψ hRψ ?_
  rw [tangentChartMap_tangentLower _ hψ hbψ (f₁ x₀),
    tangentChartMap_tangentMap hf1s hχ hω hαχ hTαω,
    tangentChartMap_tangentMap hf hφ hψ hLα hfLα, tangentChartMap_tangentLower α hφ hx x₀]
  have hfdom : TangentPre.fdom χ f₁ ω = {x : P.Level 1 | P.levelVal 1 x ∈ V} := by
    ext x
    change P.levelVal 1 x ∈ φ.source ∧ Q.levelVal 1 (f₁ x) ∈ ψ.source ↔
      P.levelVal 1 x ∈ φ.source ∧ f (P.levelVal 1 x) ∈ ψ.source
    rw [hf₁]
  have hset : χ '' TangentPre.fdom χ f₁ ω = φ.model.E.lvlSet (φ '' V) 1 := by
    rw [hfdom]; exact levelChart_image_preimage hφ x₀ hVφ
  have haS : tangentChartMap hχ α ∈ retractTangent φ.model.E.shift
      (φ.model.E.lvlSet φ.model.C 1) (φ.model.E.lvlSet (φ '' V) 1) := by
    rw [← levelChart_image_preimage hφ x₀ hVφ]
    refine (TangentPre.mem_retractTangent_image_iff (φ := χ) (fun x hx => hVφ hx)
      ((continuous_levelVal 1).isOpen_preimage _ hVo) ?_).2 (tangentChartMap_mem hχ hαχ)
    rw [tangentChartMap_fst hχ hαχ, P.shift.toBase_levelLift hχ hαχ (P.shift.levelVal_mem _)]
    exact ⟨_, hxV, rfl⟩
  have heq : EqOn (levelMap (ψ ∘ f ∘ φ.symm) 1) (ω ∘ f₁ ∘ χ.symm)
      (φ.model.E.lvlSet (φ '' V) 1) := by
    intro z hz
    have hzO : φ.model.E.toBase 1 z ∈ φ.model.O := φ.image_subset_model hVφ hz
    have hx' : P.levelVal 1 (χ.symm z) ∈ V := by
      rw [levelChart_symm_apply hφ x₀ hzO]
      obtain ⟨v, hv, hvz⟩ := hz
      rw [← hvz, φ.symm_apply_apply (hVφ hv)]
      exact hv
    have e := levelChart_apply_levelOne hf₁ hφ hψ x₀ (f₁ x₀) hx'.1 hx'.2
    rw [χ.apply_symm_apply (z := z) hzO] at e
    exact e.symm
  have h1 := retractTangentMap_congr (hg.shift hO) hO.shift heq haS
  have h2 := toBase_retractTangentMap_shift hg hO haS
  rw [h1] at h2
  rw [hset]
  exact h2

end Naturality

end MPolyfold

open MPolyfold

/-! ### The towers `X^i`, `T(X^i)`, `(TX)^i` -/

/-- An M-polyfold bundled with its underlying space (so that the lifts `X^i` form a family indexed
by `i`).  Witness: `BundledMPolyfold.nonempty`. -/
structure BundledMPolyfold : Type (u + 1) where
  /-- The underlying space. -/
  carrier : Type u
  [instTop : TopologicalSpace carrier]
  [instT2 : T2Space carrier]
  [instPara : ParacompactSpace carrier]
  /-- The M-polyfold structure. -/
  P : MPolyfold carrier

attribute [instance] BundledMPolyfold.instTop BundledMPolyfold.instT2 BundledMPolyfold.instPara

namespace BundledMPolyfold

/-- A given M-polyfold, bundled. -/
def of {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X) :
    BundledMPolyfold.{u} where
  carrier := X
  P := P

/-- **Witness**: a bundled M-polyfold (the half-line `[0, ∞)`). -/
theorem nonempty : Nonempty BundledMPolyfold.{0} :=
  ⟨of (quadrantPolyfold 1 (ScBanach.const (Fin 1 → ℝ)))⟩

/-- The lift `X¹`. -/
def shift (A : BundledMPolyfold.{u}) : BundledMPolyfold.{u} where
  carrier := A.P.Level 1
  P := A.P.shift

/-- The lift `X^i` (2021 p. 37): `X⁰ = X`, `X^{i+1} = (X^i)¹`. -/
def lift (A : BundledMPolyfold.{u}) : ℕ → BundledMPolyfold.{u}
  | 0 => A
  | i + 1 => (A.lift i).shift

/-- The tangent `TX` (2021 Theorem 2.3.16). -/
def tangent (A : BundledMPolyfold.{u}) : BundledMPolyfold.{max u 1} where
  carrier := A.P.TangentSpace
  P := A.P.tangentPolyfold

variable (A : BundledMPolyfold.{u})

/-- **The identification `Φ_i : T(X^i) ≃ (TX)^i`** of 2021 Proposition 2.3.17: `Φ_0 = id`,
`Φ_{i+1} = (Φ_i)¹ ∘ Φ`, with `Φ : T((X^i)¹) ≃ (T(X^i))¹` the case `i = 1` for `X^i`. -/
def tangentLiftEquiv : (i : ℕ) → ScEquiv (A.lift i).tangent.P (A.tangent.lift i).P
  | 0 => ScEquiv.refl _
  | i + 1 => (tangentShiftScEquiv (A.lift i).P).trans (tangentLiftEquiv i).shift

/-- **The identification `J_i : (X¹)^i ≃ (X^i)¹`** (the identity on the points of `X`,
`incl_shiftLiftEquiv`). -/
def shiftLiftEquiv : (i : ℕ) → ScEquiv (A.shift.lift i).P (A.lift i).shift.P
  | 0 => ScEquiv.refl _
  | i + 1 => (shiftLiftEquiv i).shift

/-- The `i`-th index raise `f^i : X^i → Y^i` of an sc-smooth map `f : X → Y`. -/
def liftMap {B : BundledMPolyfold.{v}} (f : ScMap A.P B.P) :
    (i : ℕ) → ScMap (A.lift i).P (B.lift i).P
  | 0 => f
  | i + 1 => (liftMap f i).shift

/-- The projection `p^i : (TX)^i → (X¹)^i`, the `i`-th index raise of `p : TX → X¹`. -/
def tangentProjLift (i : ℕ) : ScMap (A.tangent.lift i).P (A.shift.lift i).P :=
  liftMap A.tangent (B := A.shift) (tangentProjScMap A.P) i

/-- The inclusion `X^i → X`. -/
def incl : (i : ℕ) → (A.lift i).carrier → A.carrier
  | 0 => id
  | i + 1 => fun y => incl i ((A.lift i).P.levelVal 1 y)

/-- The inclusion `T(X^i) → TX`, the composite of the inclusions `T(X^{k+1}) → T(X^k)`
(`MPolyfold.tangentLower`, 2021 p. 41). -/
def tangentIncl : (i : ℕ) → (A.lift i).tangent.carrier → A.tangent.carrier
  | 0 => id
  | i + 1 => fun α => tangentIncl i (tangentLower (P := (A.lift i).P) α)

theorem incl_injective : ∀ i, Injective (A.incl i)
  | 0 => injective_id
  | i + 1 => fun _ _ h => level_ext (incl_injective i h)

/-- **`Φ` commutes with the inclusions of the two towers**: the inclusion `(TX)^{i+1} → (TX)^i`
after `Φ_{i+1}` is `Φ_i` after `T(X^{i+1}) → T(X^i)`. -/
theorem levelVal_tangentLiftEquiv_succ (i : ℕ) (α : (A.lift (i + 1)).tangent.carrier) :
    (A.tangent.lift i).P.levelVal 1 (A.tangentLiftEquiv (i + 1) α) =
      A.tangentLiftEquiv i (tangentLower (P := (A.lift i).P) α) := rfl

/-- `Φ_i` commutes with the inclusions into `TX`. -/
theorem incl_tangentLiftEquiv : ∀ (i : ℕ) (α : (A.lift i).tangent.carrier),
    A.tangent.incl i (A.tangentLiftEquiv i α) = A.tangentIncl i α
  | 0, _ => rfl
  | i + 1, α => incl_tangentLiftEquiv i (tangentLower (P := (A.lift i).P) α)

/-- `J_i` is the identity on the points of `X`. -/
theorem incl_shiftLiftEquiv : ∀ (i : ℕ) (y : (A.shift.lift i).carrier),
    A.incl (i + 1) (A.shiftLiftEquiv i y) = A.P.levelVal 1 (A.shift.incl i y)
  | 0, _ => rfl
  | i + 1, y => incl_shiftLiftEquiv i ((A.shift.lift i).P.levelVal 1 y)

/-- **`Φ_i` covers `J_i`**: `J_i ∘ p^i ∘ Φ_i = p_{X^i}`. -/
theorem tangentProjLift_tangentLiftEquiv : ∀ (i : ℕ) (α : (A.lift i).tangent.carrier),
    A.shiftLiftEquiv i (A.tangentProjLift i (A.tangentLiftEquiv i α)) =
      (A.lift i).P.tangentProj α
  | 0, _ => rfl
  | i + 1, α => level_ext ((tangentProjLift_tangentLiftEquiv i
      (tangentLower (P := (A.lift i).P) α)).trans (tangentProj_tangentLower α))

/-- The `i`-th index raise commutes with the inclusions into `X`, `Y`. -/
theorem incl_liftMap {B : BundledMPolyfold.{v}} (f : ScMap A.P B.P) :
    ∀ (i : ℕ) (y : (A.lift i).carrier), B.incl i (A.liftMap f i y) = f (A.incl i y)
  | 0, _ => rfl
  | i + 1, y => incl_liftMap f i ((A.lift i).P.levelVal 1 y)

/-- `Φ_1` is the map `tangentShiftEquiv` of the case `i = 1`. -/
theorem tangentLiftEquiv_one (α : (A.lift 1).tangent.carrier) :
    A.tangentLiftEquiv 1 α = tangentShiftEquiv (P := A.P) α :=
  MPolyfold.level_ext (P := A.P.tangentPolyfold) rfl

/-- `Φ_i` is the only map `T(X^i) → (TX)^i` compatible with the inclusions into `TX`. -/
theorem tangentLiftEquiv_unique (i : ℕ)
    (Ψ : (A.lift i).tangent.carrier → (A.tangent.lift i).carrier)
    (hΨ : ∀ α, A.tangent.incl i (Ψ α) = A.tangentIncl i α) : Ψ = A.tangentLiftEquiv i :=
  funext fun α => A.tangent.incl_injective i ((hΨ α).trans (A.incl_tangentLiftEquiv i α).symm)

/-- **2021 Proposition 2.3.17, p. 42 (new in the 2021 edition), for every `i`**: the natural
identification `T(X^i) ≡ (TX)^i` as M-polyfold bundles over `(X^i)¹ ≡ (X¹)^i`.
(1) `Φ_i : T(X^i) → (TX)^i` and `J_i : (X¹)^i → (X^i)¹` are sc-diffeomorphisms;
(2) the projections `p^i : (TX)^i → (X¹)^i` and `p : T(X^i) → (X^i)¹` are sc-smooth;
(3) `Φ_i` covers `J_i`: `J_i ∘ p^i ∘ Φ_i = p`;
(4) `Φ_i` commutes with the inclusions `T(X^i) → TX` and `(TX)^i → TX`, (5) and with the
inclusions `T(X^{i+1}) → T(X^i)`, `(TX)^{i+1} → (TX)^i` of the two towers of the text;
(6) `J_i` is the identity on the points of `X`;
(7) `Φ_i` is the only map with (4). -/
theorem _root_.Polyfold.proposition_2_3_17_all_2021 (i : ℕ) :
    (A.lift i).tangent.P.IsScDiffeoOn (A.tangent.lift i).P (A.tangentLiftEquiv i)
        (A.tangentLiftEquiv i).invFun univ univ ∧
      (A.shift.lift i).P.IsScDiffeoOn (A.lift i).shift.P (A.shiftLiftEquiv i)
        (A.shiftLiftEquiv i).invFun univ univ ∧
      ((A.tangent.lift i).P.IsScSmoothMap (A.shift.lift i).P (A.tangentProjLift i) ∧
        (A.lift i).tangent.P.IsScSmoothMap (A.lift i).shift.P (A.lift i).P.tangentProj) ∧
      (∀ α, A.shiftLiftEquiv i (A.tangentProjLift i (A.tangentLiftEquiv i α)) =
        (A.lift i).P.tangentProj α) ∧
      (∀ α, A.tangent.incl i (A.tangentLiftEquiv i α) = A.tangentIncl i α) ∧
      (∀ α : (A.lift (i + 1)).tangent.carrier,
        (A.tangent.lift i).P.levelVal 1 (A.tangentLiftEquiv (i + 1) α) =
          A.tangentLiftEquiv i (tangentLower (P := (A.lift i).P) α)) ∧
      (∀ y, A.incl (i + 1) (A.shiftLiftEquiv i y) = A.P.levelVal 1 (A.shift.incl i y)) ∧
      ∀ Ψ : (A.lift i).tangent.carrier → (A.tangent.lift i).carrier,
        (∀ α, A.tangent.incl i (Ψ α) = A.tangentIncl i α) → Ψ = A.tangentLiftEquiv i :=
  ⟨(A.tangentLiftEquiv i).isScDiffeoOn, (A.shiftLiftEquiv i).isScDiffeoOn,
    ⟨(A.tangentProjLift i).isScSmoothMap, (A.lift i).P.tangentProj_isScSmooth⟩,
    A.tangentProjLift_tangentLiftEquiv i, A.incl_tangentLiftEquiv i,
    A.levelVal_tangentLiftEquiv_succ i, A.incl_shiftLiftEquiv i, A.tangentLiftEquiv_unique i⟩

/-! ### Naturality in `X` -/

variable {A} {B : BundledMPolyfold.{v}}

/-- The tangent map `Tf` of an sc-smooth map, as an `ScMap`. -/
def tangentScMap (f : ScMap A.P B.P) : ScMap A.tangent.P B.tangent.P :=
  ⟨MPolyfold.tangentMap f.isScSmoothMap, tangentMap_isScSmooth f.isScSmoothMap⟩

/-- `ι ∘ T(f^i) = Tf ∘ ι` for the inclusions `T(X^i) → TX`, `T(Y^i) → TY`. -/
theorem tangentIncl_tangentMap (f : ScMap A.P B.P) : ∀ (i : ℕ) (α : (A.lift i).tangent.carrier),
    B.tangentIncl i (MPolyfold.tangentMap (A.liftMap f i).isScSmoothMap α) =
      MPolyfold.tangentMap f.isScSmoothMap (A.tangentIncl i α)
  | 0, _ => rfl
  | i + 1, α => by
    have h := tangentLower_tangentMap (A.liftMap f i).isScSmoothMap (f₁ := (A.liftMap f (i + 1)))
      (fun _ => rfl) α
    exact (congrArg (B.tangentIncl i) h).trans (tangentIncl_tangentMap f i _)

/-- **`Φ_i` is natural in `X`**: `Φ_i ∘ T(f^i) = (Tf)^i ∘ Φ_i` for an sc-smooth `f : X → Y`. -/
theorem tangentLiftEquiv_natural (f : ScMap A.P B.P) (i : ℕ) (α : (A.lift i).tangent.carrier) :
    B.tangentLiftEquiv i (MPolyfold.tangentMap (A.liftMap f i).isScSmoothMap α) =
      A.tangent.liftMap (B := B.tangent) (tangentScMap f) i (A.tangentLiftEquiv i α) := by
  apply B.tangent.incl_injective i
  refine (B.incl_tangentLiftEquiv i _).trans ?_
  refine (tangentIncl_tangentMap f i α).trans ?_
  refine Eq.trans ?_ (A.tangent.incl_liftMap (B := B.tangent) (tangentScMap f) i _).symm
  rw [A.incl_tangentLiftEquiv]
  rfl

/-! ### Lemma 4.4.4 for every `i` -/

/-- **`A^(i)`**, the vector field `A` with the index raised by `i`: `A^(0) = A`,
`A^(i+1) = (A^(i))^(1)` (`MPolyfold.raiseIndex`, through `Φ` for `X^i`). -/
def raiseIndexAll (V : A.P.Level 1 → A.P.TangentSpace) (hV : A.P.IsScVectorField V) :
    (i : ℕ) → {W : (A.lift i).P.Level 1 → (A.lift i).P.TangentSpace //
      (A.lift i).P.IsScVectorField W}
  | 0 => ⟨V, hV⟩
  | i + 1 => ⟨raiseIndex (raiseIndexAll V hV i).2, (lemma_4_4_4_2021 (raiseIndexAll V hV i).2).1⟩

/-- `A^(i)` is `A`: its image in `TX` at `x ∈ X^{i+1}` is `A(x)`. -/
theorem tangentIncl_raiseIndexAll (V : A.P.Level 1 → A.P.TangentSpace)
    (hV : A.P.IsScVectorField V) : ∀ (i : ℕ) (x : (A.lift i).P.Level 1) (y : A.P.Level 1),
      A.P.levelVal 1 y = A.incl (i + 1) x → A.tangentIncl i ((raiseIndexAll V hV i).1 x) = V y
  | 0, x, y, h => by
    have : x = y := level_ext h.symm
    subst this; rfl
  | i + 1, x, y, h => by
    have h1 := (lemma_4_4_4_2021 (raiseIndexAll V hV i).2).2 x
    exact (congrArg (A.tangentIncl i) h1).trans
      (tangentIncl_raiseIndexAll V hV i ((A.lift i).P.shift.levelVal 1 x) y h)

/-- A vector field as an `ScMap X¹ → TX`. -/
def vectorFieldScMap (V : A.P.Level 1 → A.P.TangentSpace) (hV : A.P.IsScVectorField V) :
    ScMap A.shift.P A.tangent.P := ⟨V, hV.1⟩

/-- Through the identifications, `Φ_i ∘ A^(i) ∘ J_i` is the `i`-th index raise of `A : X¹ → TX`
(the diagram before 2021 Lemma 4.4.4). -/
theorem tangentLiftEquiv_raiseIndexAll (V : A.P.Level 1 → A.P.TangentSpace)
    (hV : A.P.IsScVectorField V) (i : ℕ) (y : (A.shift.lift i).carrier) :
    A.tangentLiftEquiv i ((raiseIndexAll V hV i).1 (A.shiftLiftEquiv i y)) =
      liftMap A.shift (B := A.tangent) (vectorFieldScMap V hV) i y := by
  apply A.tangent.incl_injective i
  refine (A.incl_tangentLiftEquiv i _).trans ?_
  refine (tangentIncl_raiseIndexAll V hV i _ _ (A.incl_shiftLiftEquiv i y).symm).trans ?_
  exact (incl_liftMap A.shift (vectorFieldScMap V hV) i y).symm

/-- **2021 Lemma 4.4.4, p. 196 (new in the 2021 edition), for every `i ≥ 0`**: for an sc-smooth
vector field `A` of `X`, `A^(i)` is an sc-smooth vector field of `X^i`, i.e. an sc-smooth section
of `T(X^i) → X^{i+1}`; it is `A` (its image in `TX` at `x ∈ X^{i+1}` is `A(x)`); through the
identifications `Φ_i`, `J_i` of Proposition 2.3.17 it is the `i`-th index raise of `A`; and
`A^(i+1) = (A^(i))^(1)`. -/
theorem _root_.Polyfold.lemma_4_4_4_all_2021 (V : A.P.Level 1 → A.P.TangentSpace)
    (hV : A.P.IsScVectorField V) (i : ℕ) :
    (A.lift i).P.IsScVectorField (raiseIndexAll V hV i).1 ∧
      (∀ (x : (A.lift i).P.Level 1) (y : A.P.Level 1), A.P.levelVal 1 y = A.incl (i + 1) x →
        A.tangentIncl i ((raiseIndexAll V hV i).1 x) = V y) ∧
      (∀ y, A.tangentLiftEquiv i ((raiseIndexAll V hV i).1 (A.shiftLiftEquiv i y)) =
        liftMap A.shift (B := A.tangent) (vectorFieldScMap V hV) i y) ∧
      ∀ x, (raiseIndexAll V hV (i + 1)).1 x = raiseIndex (raiseIndexAll V hV i).2 x :=
  ⟨(raiseIndexAll V hV i).2, tangentIncl_raiseIndexAll V hV i,
    tangentLiftEquiv_raiseIndexAll V hV i, fun _ => rfl⟩

/-- **Witness** for `lemma_4_4_4_all_2021`: the zero vector field (`isScVectorField_zero`). -/
theorem lemma_4_4_4_all_2021_zero (A : BundledMPolyfold.{u}) (i : ℕ) :
    (A.lift i).P.IsScVectorField (raiseIndexAll A.P.zeroVectorField A.P.isScVectorField_zero i).1 :=
  (lemma_4_4_4_all_2021 _ A.P.isScVectorField_zero i).1

end BundledMPolyfold

end Polyfold
