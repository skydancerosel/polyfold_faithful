import Polyfold.Chapter2.Metrizable
import Polyfold.Chapter2.TameBoundary
import Polyfold.Chapter4.VectorFields
import Polyfold.Chapter5.StrongBundleShift

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §2.3
"M-Polyfolds and Sub-M-Polyfolds": **Theorem 2.3.16** (p. 40; 2017: the running text after
Proposition 2.5; preprint: the paragraph after Proposition 2.19), **Proposition 2.3.17** (p. 42,
new in the 2021 edition), the bundle notions of **Definition 2.1.16** (p. 29; 2017:
Definition 2.5; preprint: Definition 2.9), and the levels `X_m` as charted spaces (the paragraph
after **Definition 2.3.8**, p. 37; preprint: after Definition 2.14) for the lift `X¹`; and, from
§2.4 "The Degeneracy Index and Boundary Geometry", the example of **Remark 2.4.2** (pp. 44–45, new
in the 2021 edition).  Numbers and pages are the 2021 text's.

# The tangent of the lift: `T(X¹) ≡ (TX)¹`

## The text, paraphrased

(Definition 2.1.16, p. 29) An sc-smooth bundle retraction of `U ⊕ F` has the form
`R(u, v) = (r(u), ρ(u, v))`, `ρ` linear in `v`, covering the retraction `r`; a bundle map between
bundle retracts has the form `Φ(u, v) = (a(u), φ(u, v))`, `φ` linear in `v`, with `p' ∘ Φ = p`.
(Theorem 2.3.16, p. 40) The models `TO → O¹` are bundle retracts, the transition maps of the
tangent charts are sc-smooth bundle maps, so `p : TX → X¹` is a well defined M-polyfold bundle.

(pp. 40–42) The inclusions `X^{i+1} → X^i` give inclusions `T(X^{i+1}) → T(X^i)`, and the lifts
give `(TX)^{i+1} → (TX)^i`, over `X^{i+2} → X^{i+1}`.  In a local model, with `r : U → U`,
`(TO)^i = T(r^i)((U^i)¹ ⊕ E^i) = T(O^i)`; this is compatible with the tangent charts: for a chart
`φ` of `X`, `T(V^i) = (TV)^i`, and `T(φ^i)`, `(Tφ)^i` agree on it.  (Proposition 2.3.17, p. 42)
There is a natural identification of `(TX)^i` with `T(X^i)`, and of the M-polyfold bundles
`(TX)^i → (X¹)^i` and `T(X^i) → (X^i)¹`, covering `(X¹)^i ≡ (X^i)¹`.  (After Definition 2.3.8,
p. 37) For every `m` the charts `(V_m, φ, (O_m, C_m, E_m))` form an atlas of `X_m`; in particular
the lift `X¹` has the levels `(X¹)_m = X_{m+1}`.

(Remark 2.4.2, pp. 44–45) The half-line `Δ` of the points `(s, s, s)`, `s ≥ 0`, in
`C = [0,∞)³ ⊆ ℝ³` is a smooth retract `(Δ, C, ℝ³)`; for the induced structure `s ↦ (s, s, s)` is a
diffeomorphism from `[0,∞)`.  `d_C(s, s, s)` is `3` at `s = 0` and `0` otherwise, `d_Δ(s, s, s)` is
`1` at `s = 0` and `0` otherwise, and `Δ` has an atlas modelled on relatively open subsets of
`[0,∞)`.

## What is formalized

Local models (`T(f¹) = (Tf)¹`):
* `tangentMap_levelMap_one`, `toBase_tangentMap_levelMap_one`: `T(f¹)` is the level-`1` map of
  `Tf` on `T(U¹) = (TU)¹`; `retractTangent_shift_of_isScRetract` (`T(O¹) = (TO)¹`, from
  `retractTangent_shift` of `VectorFields.lean`); `toBase_retractTangentMap_shift`: the same for
  sc-smooth maps between retracts.
* `ScRetraction.IsBundleRetractionOver`, `IsBundleMapOn` (**Definition 2.1.16**, the shape of the
  maps), with the witnesses `ScRetraction.tangentRetraction_isBundleRetractionOver` (`Tr` covers
  `r¹`) and `IsScSmoothRetractMap.retractTangentMap_isBundleMapOn` (`Tf` covers `f¹`).

M-polyfolds:
* `theorem_2_3_16` (**Theorem 2.3.16**, bundle form): the tangent charts belong to the
  structure of `TX`, `p` is sc-smooth, `p` is the first projection in the tangent charts, the
  models are bundle retracts, and the transition maps of tangent charts are bundle maps covering
  those of the charts `φ¹` of `X¹`.
* `MPolyfold.TangentPre.lower`, `MPolyfold.tangentLower` (well defined by
  `TangentPre.transport_lower`), `MPolyfold.tangentShiftMap`, `MPolyfold.tangentShiftEquiv`
  (`Φ : T(X¹) ≃ (TX)¹`), `MPolyfold.tangentShiftHomeomorph`, `MPolyfold.tangentProjShift`
  (`p¹ : (TX)¹ → (X¹)¹`), `MPolyfold.tangentShiftEquiv_isScDiffeoOn`.
* `proposition_2_3_17` (**Proposition 2.3.17**, `i = 1`): `Φ` is an sc-diffeomorphism of
  M-polyfolds, `p¹ ∘ Φ = p_{X¹}`, `p¹` is sc-smooth, `Φ` is natural (`Tψ ∘ Φ = ι ∘ T(ψ¹)` in
  every chart `ψ`, `MPolyfold.tangentChartMap_tangentLower`) and, in the charts `T(φ¹)`, `(Tφ)¹`,
  the identity of `T(O¹) = (TO)¹` (`MPolyfold.levelChart_tangentShiftMap`).
* `MPolyfold.levelOneEquiv`, `MPolyfold.levelOneEquiv_isScDiffeoOn` (the index raise of an
  sc-diffeomorphism), `MPolyfold.tangentShiftEquivTwo` and `proposition_2_3_17_two`
  (**Proposition 2.3.17**, `i = 2`).
* Gap G.6 of the report: `MPolyfold.levelLift_transition`, `MPolyfold.levelLift_levelChart` (the
  level-`m` lift of the chart `φ¹` of `X¹` is the level-`(m+1)` lift of `φ`),
  `MPolyfold.shiftLevelMap`, `MPolyfold.continuous_shiftLevelMap`,
  `MPolyfold.continuous_shiftLevelInv` (for an arbitrary chart of `X¹`, through the level-`m` maps
  of transition maps), `MPolyfold.shiftLevelHomeomorph` (`(X¹)_m ≅ X_{m+1}`, the identity on the
  points of `X`) and `MPolyfold.shift_level_eq`: the levels of the iterate `(X¹)¹ ⋯` are the
  levels `X_m` of `X`, with their topology and charts.

The diagonal example (Remark 2.4.2):
* `ScOperator.ofConst`, `diagonalAverage`, `diagonalInclusion`, `diagonalFirst` (linear maps of
  `ℝ`, `ℝ³` as sc-operators); `diagonalRetraction` (the average of the coordinates, a retraction of
  `[0,∞)³ ⊕ W` onto `Δ ⊕ W`, `mem_diagonalRetraction_retract_iff`), `diagonalModel`,
  `diagonalPolyfold` (the M-polyfold `Δ ⊕ W`).
* `diagonalEmbed`, `diagonalProject`, `diagonalEmbed_isScDiffeoOn` (`s ↦ (s, s, s)` is an
  sc-diffeomorphism from the half-line M-polyfold `MPolyfold.quadrantPolyfold 1 W`).
* `degIndex_diagonal_quadrant` (`d_C`), `diagonalPolyfold_degIndex` (`d_Δ`, through
  `proposition_2_4_4`), `diagonalHalfLineChart`, `diagonalHalfLineChart_spec` (one chart on all of
  `Δ`, with model `[0,∞) ⊕ W`, in which the index is `d_Δ`), and `remark_2_4_2` collecting
  these.

## What the text leaves implicit, and the choices made

* "Naturally identified … as bundles" is read as: a bijection `Φ : T(X¹) → (TX)¹` which is an
  sc-diffeomorphism of M-polyfolds, commutes with the projections onto `(X¹)¹`, and is, in the
  charts induced by any chart of `X`, the identity of `T(O¹) = (TO)¹` (so linear on the fibres).
  `Φ` is defined with a chosen chart (`MPolyfold.someChart`) and then shown to be independent of
  it (`tangentChartMap_tangentLower` holds in every chart).
* `X^i` is the iterate `(X¹)¹ ⋯` (`MPolyfold.shift`).  The case `i = 1` is proved; every fixed `i`
  follows by iteration (`i = 2` is written out, with `levelOneEquiv` as the inductive step); the
  statement for all `i` at once is `proposition_2_3_17_all` in `Chapter2/TangentLiftAll.lean`.
* `(X¹)^i ≡ (X^i)¹` is an equality for `i = 1`, and for `i = 2` it is `((X¹)¹)¹ = ((X¹)¹)¹`.
  That the levels of `X¹` carry the topology of the levels of `X` is a separate statement (gap
  G.6), proved here as `shiftLevelHomeomorph`; Proposition 2.3.17 does not use it.
* Definition 2.1.16 is stated for the shape of the maps only (`R` on `U ⊕ F`,
  `R(u, v) = (r(u), ρ(u) v)` with `ρ(u)` a continuous linear map); the sc-smoothness is part of the
  data (`ScRetraction`, `IsScSmoothRetractMap`).
* Remark 2.4.2 is stated for `Δ ⊕ W ⊆ [0,∞)³ ⊕ W` with an arbitrary sc-Banach space `W` (the text's
  `ℝ³` is `W = 0`); "classically smooth" is read as sc-smooth for the constant sc-structure, and
  "the smooth structure on `Δ`" as the M-polyfold of the retract (`LocalModel.toMPolyfold`).  The
  retraction is not given in the text; we take the orthogonal projection onto the diagonal.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

/-! ### `T(f¹) = (Tf)¹` in a local model -/

section Local

variable {E F : ScBanach}

/-- The tangent map of `f¹ : U¹ → F¹` is the level-`1` map of `Tf` on `T(U¹) = (TU)¹`. -/
theorem tangentMap_levelMap_one {U : Set (E 0)} {f : E 0 → F 0} (hU : IsScDomain E U)
    (hf : IsSc1 U f) {p : E.shift.tangent 0} (hp : p ∈ E.shift.tangentSet (E.lvlSet U 1)) :
    tangentMap (E := E.shift) (F := F.shift) (E.lvlSet U 1) (levelMap f 1) p =
      levelMap (E := E.tangent) (F := F.tangent) (tangentMap U f) 1 p := by
  have h1 := hf.isSc1With_scDeriv.shift hU
  have hp' : p ∈ E.tangent.lvlSet (E.tangentSet U) 1 := by rw [E.shift_tangentSet]; exact hp
  simp only [tangentMap]
  rw [hf.isSc1With_scDeriv.levelMap_tangentMapWith hp']
  change ((levelMap (E := E.shift) (F := F.shift) (levelMap f 1) 1 p.1,
      scDeriv (E := E.shift) (F := F.shift) (E.lvlSet U 1) (levelMap f 1) p.1 p.2) :
      F.shift.tangent 0) = ((levelMap f 2 p.1, levelDeriv (scDeriv U f) 1 p.1 p.2) : F.tangent 1)
  rw [hf.isSc0.levelMap_shift (E.mem_lvlSet_tangentSet.1 hp'),
    IsSc1.scDeriv_eqOn h1 (hU.shift.uniqueDiffWithinAt 1) hp]

/-- `ι(T(f¹)(p)) = Tf(ι p)` on `T(U¹)`. -/
theorem toBase_tangentMap_levelMap_one {U : Set (E 0)} {f : E 0 → F 0} (hU : IsScDomain E U)
    (hf : IsSc1 U f) {p : E.shift.tangent 0} (hp : p ∈ E.shift.tangentSet (E.lvlSet U 1)) :
    F.tangent.toBase 1 (tangentMap (E := E.shift) (F := F.shift) (E.lvlSet U 1) (levelMap f 1) p) =
      tangentMap U f (E.tangent.toBase 1 p) := by
  rw [tangentMap_levelMap_one hU hf hp]
  have hp' : p ∈ E.tangent.lvlSet (E.tangentSet U) 1 := by rw [E.shift_tangentSet]; exact hp
  exact hf.isSc1With_scDeriv.tangent_isSc0.toBase_levelMap hp'

variable {C O : Set (E 0)}

/-- `T(O¹) = (TO)¹` for any sc-smooth retract (`retractTangent_shift` with the retraction
eliminated). -/
theorem retractTangent_shift_of_isScRetract (hO : IsScRetract E C O) :
    retractTangent E.shift (E.lvlSet C 1) (E.lvlSet O 1) =
      E.tangent.lvlSet (retractTangent E C O) 1 := by
  obtain ⟨R, rfl⟩ := hO
  exact retractTangent_shift R

variable {C' O' : Set (F 0)} {f : E 0 → F 0}

/-- **`T(f¹) = (Tf)¹` for sc-smooth maps between retracts**: for `f : (O, C, E) → (O', C', F)`
sc-smooth and `a ∈ T(O¹)`, `ι(T(f¹)(a)) = Tf(ι a)`. -/
theorem toBase_retractTangentMap_shift (hf : IsScSmoothRetractMap E C O F C' O' f)
    (hO : IsScRetract E C O) {a : E.shift.tangent 0}
    (ha : a ∈ retractTangent E.shift (E.lvlSet C 1) (E.lvlSet O 1)) :
    F.tangent.toBase 1
        (retractTangentMap E.shift (E.lvlSet C 1) (E.lvlSet O 1) (E' := F.shift)
          (levelMap f 1) a) =
      retractTangentMap E C O f (E.tangent.toBase 1 a) := by
  have hf1 := hf.shift hO
  have hf0 := hf.isSc0 hO
  have ha0 : E.tangent.toBase 1 a ∈ retractTangent E C O := by
    rw [retractTangent_shift_of_isScRetract hO] at ha; exact ha
  obtain ⟨R, rfl⟩ := hO
  have hR1 : R.shift.retract = E.lvlSet R.retract 1 := R.shift_retract
  rw [retractTangentMap_eqOn hf1 R.shift hR1 ha, retractTangentMap_eqOn hf R rfl ha0]
  have hfR := hf.comp_isScSmooth R rfl
  have haU : a ∈ E.shift.tangentSet R.shift.U := by
    rw [← hR1, retractTangent_eq] at ha
    exact R.shift.tangent_subset ha
  have hcongr : EqOn (levelMap (f ∘ R) 1) (levelMap f 1 ∘ R.shift) R.shift.U := fun x hx =>
    hf0.levelMap_comp R.isSc1.isSc0 R.mapsTo_retract hx
  have h2 := ((hfR.shift R.isScDomain).isSc1.tangentMap_congr R.shift.isScDomain hcongr) haU
  rw [← h2]
  exact toBase_tangentMap_levelMap_one R.isScDomain hfR.isSc1 haU

end Local

/-! ### Definition 2.1.16: bundle retractions and bundle maps -/

section BundleForm

variable {E F : ScBanach}

/-- **2021 Definition 2.1.16, p. 30** (sc-smooth bundle retraction), for a retraction `R` of
`E ⊕ F`: `R` is defined on `U ⊕ F` and has the form `R(u, v) = (r(u), ρ(u) v)` with `ρ(u)` linear,
covering the retraction `r`. -/
def ScRetraction.IsBundleRetractionOver {C : Set (E 0)} {D : Set ((E.prod F) 0)}
    (R : ScRetraction (E.prod F) D) (r : ScRetraction E C) : Prop :=
  R.U = {p | p.1 ∈ r.U} ∧ ∃ ρ : E 0 → F 0 →L[ℝ] F 0, ∀ p ∈ R.U, R p = (r p.1, ρ p.1 p.2)

/-- The tangent retraction `Tr(x, h) = (r(x), Dr(x) h)` is an sc-smooth bundle retraction covering
`r¹ : U¹ → U¹` (2021 Theorem 2.3.16, p. 40: the models of `TX` are bundle retracts). -/
theorem ScRetraction.tangentRetraction_isBundleRetractionOver {C : Set (E 0)}
    (R : ScRetraction E C) :
    ScRetraction.IsBundleRetractionOver (E := E.shift) (F := E) R.tangentRetraction R.shift :=
  ⟨rfl, scDeriv R.U R, fun _ _ => rfl⟩

variable {E' F' : ScBanach}

/-- **2021 Definition 2.1.16, p. 30** (sc-smooth bundle map), on a set `B ⊆ E ⊕ F`: `Φ` has the
form `Φ(u, v) = (a(u), φ(u) v)` with `φ(u)` linear, so that `p' ∘ Φ = a ∘ p`. -/
def IsBundleMapOn (Φ : (E.prod F) 0 → (E'.prod F') 0) (B : Set ((E.prod F) 0))
    (a : E 0 → E' 0) : Prop :=
  ∃ φ : E 0 → F 0 →L[ℝ] F' 0, ∀ p ∈ B, Φ p = (a p.1, φ p.1 p.2)

/-- A bundle map covers `a`: `p' ∘ Φ = a ∘ p` on `B`. -/
theorem IsBundleMapOn.fst_eq {Φ : (E.prod F) 0 → (E'.prod F') 0} {B : Set ((E.prod F) 0)}
    {a : E 0 → E' 0} (h : IsBundleMapOn Φ B a) {p : (E.prod F) 0} (hp : p ∈ B) :
    (Φ p).1 = a p.1 := by
  obtain ⟨φ, hφ⟩ := h
  rw [hφ p hp]

variable {C O : Set (E 0)} {C' O' : Set (E' 0)} {f : E 0 → E' 0}

/-- The tangent map `Tf : TO → TO'` of an sc-smooth map between retracts is a bundle map covering
`f¹ : O¹ → O'¹`: `Tf(x, h) = (f(x), Df(x) h)`. -/
theorem IsScSmoothRetractMap.retractTangentMap_isBundleMapOn
    (hf : IsScSmoothRetractMap E C O E' C' O' f) (hO : IsScRetract E C O) :
    IsBundleMapOn (E := E.shift) (F := E) (E' := E'.shift) (F' := E')
      (retractTangentMap E C O f) (retractTangent E C O) (levelMap f 1) := by
  have hf0 := hf.isSc0 hO
  obtain ⟨R, rfl⟩ := hO
  refine ⟨scDeriv R.U (f ∘ R), fun p hp => ?_⟩
  rw [retractTangentMap_apply hf R rfl hp]
  have hp1 : p.1 ∈ E.lvlSet R.retract 1 := retractTangent_fst_mem ⟨R, rfl⟩ hp
  have hU : p.1 ∈ R.shift.U := E.lvlSet_mono R.retract_subset 1 hp1
  have h1 : levelMap (f ∘ R) 1 p.1 = levelMap f 1 (R.shift p.1) :=
    hf0.levelMap_comp R.isSc1.isSc0 R.mapsTo_retract hU
  have h2 : R.shift p.1 = p.1 :=
    R.shift.apply_eq_self_of_mem_retract (by rw [R.shift_retract]; exact hp1)
  rw [h1, h2]

end BundleForm

/-! ### The identification `T(X¹) ≅ (TX)¹` -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

variable (P) in
/-- A chosen chart of the structure around `x`. -/
def someChart (x : X) : MChart X := (P.exists_isChart_mem_source x).choose

lemma someChart_isChart (x : X) : P.IsChart (P.someChart x) :=
  (P.exists_isChart_mem_source x).choose_spec.1

lemma mem_someChart_source (x : X) : x ∈ (P.someChart x).source :=
  (P.exists_isChart_mem_source x).choose_spec.2

namespace TangentPre

variable (q : P.shift.TangentPre)

/-- The vector `q ∈ T(X¹)` read in the level chart `φ¹` lies in `T(O¹)`, and its inclusion lies in
`TO`. -/
lemma toBase_transport_levelChart_mem {φ : MChart X} (hφ : P.IsChart φ) (x₀ : P.Level 1)
    (hx : P.levelVal 1 q.x ∈ φ.source) :
    φ.model.E.tangent.toBase 1 (q.transport (levelChart hφ x₀)) ∈
      retractTangent φ.model.E φ.model.C φ.model.O := by
  have h : q.transport (levelChart hφ x₀) ∈ retractTangent φ.model.E.shift
      (φ.model.E.lvlSet φ.model.C 1) (φ.model.E.lvlSet φ.model.O 1) :=
    q.transport_mem (P.shift_isChart hφ x₀) hx
  rw [retractTangent_shift_of_isScRetract φ.model.isScRetract] at h
  exact h

/-- The base point of `q` read in `φ¹` is `φ(x)` on level `1`. -/
lemma toBase_transport_levelChart_fst {φ : MChart X} (hφ : P.IsChart φ) (x₀ : P.Level 1)
    (hx : P.levelVal 1 q.x ∈ φ.source) :
    φ.model.E.shift.toBase 1 (q.transport (levelChart hφ x₀)).1 =
      levelLift φ 1 (P.levelVal 1 q.x) := by
  rw [q.transport_fst (P.shift_isChart hφ x₀) hx]
  exact P.shift.toBase_levelLift (P.shift_isChart hφ x₀) hx q.mem_level

/-- `ι(T(φ¹)(q)) = (φ(x), ι h')` on level `1`. -/
lemma toBase_transport_levelChart_eq {φ : MChart X} (hφ : P.IsChart φ) (x₀ : P.Level 1)
    (hx : P.levelVal 1 q.x ∈ φ.source) :
    φ.model.E.tangent.toBase 1 (q.transport (levelChart hφ x₀)) =
      ((levelLift φ 1 (P.levelVal 1 q.x), φ.model.E.toBase 1 (q.transport (levelChart hφ x₀)).2) :
        φ.model.E.tangent 0) :=
  (ScBanach.tangent_toBase φ.model.E 1 _).trans
    (Prod.ext (q.toBase_transport_levelChart_fst hφ x₀ hx) rfl)

/-- **The lowered tuple**: `q = [(x, χ, h)] ∈ T(X¹)` read in the level chart `φ¹` of a chosen chart
`φ` of `X` around `x` is `(φ¹(x), h')` with `h' ∈ E₁`; the tuple `(x, φ, ι h')` of `TX`. -/
def lower : P.TangentPre where
  x := P.levelVal 1 q.x
  φ := P.someChart (P.levelVal 1 q.x)
  h := (P.someChart (P.levelVal 1 q.x)).model.E.toBase 1
    (q.transport (levelChart (P.someChart_isChart (P.levelVal 1 q.x)) q.x)).2
  isChart := P.someChart_isChart _
  mem_source := P.mem_someChart_source _
  mem_level := P.levelVal_mem q.x
  mem_tangent := by
    have h := q.toBase_transport_levelChart_mem (P.someChart_isChart (P.levelVal 1 q.x)) q.x
      (P.mem_someChart_source _)
    rw [q.toBase_transport_levelChart_eq (P.someChart_isChart (P.levelVal 1 q.x)) q.x
      (P.mem_someChart_source _)] at h
    exact h

lemma lower_vec : q.lower.vec = (P.someChart (P.levelVal 1 q.x)).model.E.tangent.toBase 1
    (q.transport (levelChart (P.someChart_isChart (P.levelVal 1 q.x)) q.x)) :=
  (q.toBase_transport_levelChart_eq (P.someChart_isChart (P.levelVal 1 q.x)) q.x
    (P.mem_someChart_source _)).symm

/-- **The key identity**: the lowered tuple read in any chart `ψ` of `X` is the inclusion of `q`
read in the level chart `ψ¹`: `Tψ[q.lower] = ι(T(ψ¹)(q))`.  (`T(ψ ∘ φ⁻¹)` on `(TO)¹` is the
tangent of `(ψ ∘ φ⁻¹)¹`, by `toBase_retractTangentMap_shift`.) -/
theorem transport_lower {ψ : MChart X} (hψ : P.IsChart ψ) (hx : P.levelVal 1 q.x ∈ ψ.source)
    (y₀ : P.Level 1) :
    q.lower.transport ψ = ψ.model.E.tangent.toBase 1 (q.transport (levelChart hψ y₀)) := by
  have hφ : P.IsChart (P.someChart (P.levelVal 1 q.x)) := P.someChart_isChart _
  have hxφ : P.levelVal 1 q.x ∈ (P.someChart (P.levelVal 1 q.x)).source := P.mem_someChart_source _
  set φ := P.someChart (P.levelVal 1 q.x) with hφdef
  have hχ : P.shift.IsChart (levelChart hφ q.x) := P.shift_isChart hφ q.x
  have hχ' : P.shift.IsChart (levelChart hψ y₀) := P.shift_isChart hψ y₀
  have hov := levelChart_overlap hφ q.x hψ y₀
  -- the vector `a = T(φ¹)(q)` lies in `T(φ¹(V¹ ∩ V'¹))`
  have ha : q.transport (levelChart hφ q.x) ∈ retractTangent (levelChart hφ q.x).model.E
      (levelChart hφ q.x).model.C ((levelChart hφ q.x).overlap (levelChart hψ y₀)) := by
    refine (TangentPre.mem_retractTangent_image_iff inter_subset_left
      ((levelChart hφ q.x).isOpen_source.inter (levelChart hψ y₀).isOpen_source) ?_).2
      (q.transport_mem hχ hxφ)
    rw [q.transport_fst hχ hxφ, P.shift.toBase_levelLift hχ hxφ q.mem_level]
    exact ⟨q.x, ⟨hxφ, hx⟩, rfl⟩
  rw [hov] at ha
  have hT := toBase_retractTangentMap_shift (hφ.compatible hψ (P := P)).1
    (φ.isScRetract_overlap ψ) ha
  change retractTangentMap φ.model.E φ.model.C (φ.overlap ψ) (φ.transition ψ) q.lower.vec = _
  rw [q.lower_vec, ← hT]
  congr 1
  rw [← q.transport_transport hχ hχ' hxφ hx, hov]
  exact retractTangentMap_congr ((hφ.compatible hψ (P := P)).1.shift (φ.isScRetract_overlap ψ))
    (φ.isScRetract_overlap ψ).shift
    (fun z hz => (levelChart_transition hφ q.x hψ y₀ (φ.overlap_subset ψ hz)).symm) ha

end TangentPre

/-- The map `T(X¹) → TX`, `[q] ↦ [q.lower]` (well defined by `transport_lower`). -/
def tangentLower : P.shift.TangentSpace → P.TangentSpace :=
  TangentSpace.lift (fun q => TangentSpace.mk q.lower) fun q q' h => by
    have hφ := P.someChart_isChart (P.levelVal 1 q.x)
    have hx : P.levelVal 1 q.x ∈ (P.someChart (P.levelVal 1 q.x)).source := P.mem_someChart_source _
    have hx' : P.levelVal 1 q'.x ∈ (P.someChart (P.levelVal 1 q.x)).source := by
      rw [← h.1]; exact hx
    apply tangentChartMap_injOn hφ (show q.lower.x ∈ _ from hx) (show q'.lower.x ∈ _ from hx')
    rw [tangentChartMap_mk hφ (show q.lower.x ∈ _ from hx),
      tangentChartMap_mk hφ (show q'.lower.x ∈ _ from hx'), q.transport_lower hφ hx q.x,
      q'.transport_lower hφ hx' q.x, h.transport (P.shift_isChart hφ q.x) hx]

lemma tangentLower_mk (q : P.shift.TangentPre) :
    tangentLower (TangentSpace.mk q) = TangentSpace.mk q.lower := rfl

/-- The base point of `α ∈ T(X¹)` as a point of `X`. -/
abbrev shiftBase (α : P.shift.TangentSpace) : X :=
  P.levelVal 1 (P.shift.levelVal 1 (P.shift.tangentProj α))

/-- `p ∘ tangentLower = p_{X¹}` (as points of `X¹`). -/
theorem tangentProj_tangentLower (α : P.shift.TangentSpace) :
    P.tangentProj (tangentLower α) = P.shift.levelVal 1 (P.shift.tangentProj α) := by
  obtain ⟨q, rfl⟩ := TangentSpace.exists_rep α
  exact level_ext rfl

/-- **`Tψ ∘ tangentLower = ι ∘ T(ψ¹)`**: in a chart `ψ` of `X` and its level chart `ψ¹`. -/
theorem tangentChartMap_tangentLower (α : P.shift.TangentSpace) {ψ : MChart X} (hψ : P.IsChart ψ)
    (hx : shiftBase α ∈ ψ.source) (y₀ : P.Level 1) :
    tangentChartMap hψ (tangentLower α) =
      ψ.model.E.tangent.toBase 1 (tangentChartMap (P.shift_isChart hψ y₀) α) := by
  obtain ⟨q, rfl⟩ := TangentSpace.exists_rep α
  rw [tangentLower_mk, tangentChartMap_mk hψ (show q.lower.x ∈ _ from hx),
    tangentChartMap_mk (P.shift_isChart hψ y₀) (show q.x ∈ (levelChart hψ y₀).source from hx)]
  exact q.transport_lower hψ hx y₀

lemma tangentLower_mem_tangentChartSet {α : P.shift.TangentSpace} {ψ : MChart X}
    (hx : shiftBase α ∈ ψ.source) : tangentLower α ∈ tangentChartSet (P := P) ψ := by
  change P.levelVal 1 (P.tangentProj (tangentLower α)) ∈ ψ.source
  rw [tangentProj_tangentLower]; exact hx

/-- `tangentLower` maps `T(X¹)` into the level `(TX)₁`. -/
theorem tangentLower_mem_levelSet (α : P.shift.TangentSpace) :
    tangentLower α ∈ P.tangentPolyfold.levelSet 1 := by
  have hφ := P.someChart_isChart (shiftBase α)
  have hx := P.mem_someChart_source (shiftBase α)
  rw [P.tangentPolyfold.mem_levelSet_iff (P.tangentPolyfold_isChart hφ (tangentLower α))
    (tangentLower_mem_tangentChartSet hx), tangentChart_apply,
    tangentChartMap_tangentLower α hφ hx (P.shift.levelVal 1 (P.shift.tangentProj α))]
  exact ⟨_, rfl⟩

/-- **The natural map `T(X¹) → (TX)¹`** of Proposition 2.3.17. -/
def tangentShiftMap (α : P.shift.TangentSpace) : P.tangentPolyfold.Level 1 :=
  P.tangentPolyfold.levelMk 1 (tangentLower α) (tangentLower_mem_levelSet α)

@[simp] lemma levelVal_tangentShiftMap (α : P.shift.TangentSpace) :
    P.tangentPolyfold.levelVal 1 (tangentShiftMap α) = tangentLower α := rfl

theorem tangentLower_injective : Injective (tangentLower (P := P)) := by
  intro α β h
  have hp : P.shift.tangentProj α = P.shift.tangentProj β := by
    apply level_ext
    rw [← tangentProj_tangentLower, h, tangentProj_tangentLower]
  have hφ := P.someChart_isChart (shiftBase α)
  have hx := P.mem_someChart_source (shiftBase α)
  have hx' : shiftBase β ∈ (P.someChart (shiftBase α)).source := by
    simp only [shiftBase, ← hp]; exact hx
  set y := P.shift.levelVal 1 (P.shift.tangentProj α)
  have hχ := P.shift_isChart hφ y
  refine tangentChartMap_injOn hχ (show shiftBase α ∈ _ from hx) (show shiftBase β ∈ _ from hx') ?_
  apply (P.someChart (shiftBase α)).model.E.tangent.toBase_injective 1
  rw [← tangentChartMap_tangentLower α hφ hx y, ← tangentChartMap_tangentLower β hφ hx' y, h]

theorem tangentShiftMap_injective : Injective (tangentShiftMap (P := P)) := fun _ _ h =>
  tangentLower_injective (congrArg (P.tangentPolyfold.levelVal 1) h)

theorem tangentShiftMap_surjective : Surjective (tangentShiftMap (P := P)) := by
  intro β
  set α' := P.tangentPolyfold.levelVal 1 β with hα'def
  set y := P.tangentProj α' with hydef
  have hφ := P.someChart_isChart (P.levelVal 1 y)
  have hx := P.mem_someChart_source (P.levelVal 1 y)
  set φ := P.someChart (P.levelVal 1 y) with hφdef
  have hα' : α' ∈ tangentChartSet (P := P) φ := hx
  obtain ⟨a, ha⟩ := (P.tangentPolyfold.mem_levelSet_iff (P.tangentPolyfold_isChart hφ α') hα').1
    (P.tangentPolyfold.levelVal_mem β)
  have haT : a ∈ retractTangent (levelChart hφ y).model.E (levelChart hφ y).model.C
      (levelChart hφ y).model.O := by
    change a ∈ retractTangent φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1)
      (φ.model.E.lvlSet φ.model.O 1)
    rw [retractTangent_shift_of_isScRetract φ.model.isScRetract]
    change φ.model.E.tangent.toBase 1 a ∈ retractTangent φ.model.E φ.model.C φ.model.O
    have ha' : φ.model.E.tangent.toBase 1 a = tangentChartMap hφ α' := ha
    rw [ha']; exact tangentChartMap_mem hφ hα'
  have hχ := P.shift_isChart hφ y
  set q := TangentPre.ofVec hχ haT with hqdef
  refine ⟨TangentSpace.mk q, level_ext ?_⟩
  change tangentLower (TangentSpace.mk q) = α'
  have hq : shiftBase (TangentSpace.mk q) ∈ φ.source := q.mem_source
  refine tangentChartMap_injOn hφ (tangentLower_mem_tangentChartSet hq) hα' ?_
  rw [tangentChartMap_tangentLower _ hφ hq y, tangentChartMap_mk_ofVec hχ haT]
  exact ha

/-- **Proposition 2.3.17, the identification `T(X¹) ≡ (TX)¹`** as a bijection. -/
def tangentShiftEquiv : P.shift.TangentSpace ≃ P.tangentPolyfold.Level 1 :=
  Equiv.ofBijective tangentShiftMap ⟨tangentShiftMap_injective, tangentShiftMap_surjective⟩

@[simp] lemma tangentShiftEquiv_apply (α : P.shift.TangentSpace) :
    tangentShiftEquiv α = tangentShiftMap α := rfl

lemma tangentShiftMap_symm (β : P.tangentPolyfold.Level 1) :
    tangentShiftMap (tangentShiftEquiv.symm β) = β := tangentShiftEquiv.apply_symm_apply β

/-- The base point of `Φ⁻¹(β)` is that of `β`. -/
lemma shiftBase_symm (β : P.tangentPolyfold.Level 1) :
    shiftBase (tangentShiftEquiv.symm β) =
      P.levelVal 1 (P.tangentProj (P.tangentPolyfold.levelVal 1 β)) := by
  rw [shiftBase, ← tangentProj_tangentLower, ← levelVal_tangentShiftMap, tangentShiftMap_symm]

/-! ### The identification in charts; sc-smoothness -/

/-- `id : T(O¹) → (TO)¹` is sc-smooth between the local models `T(O¹, C¹, E¹)` and
`(TO, TC, TE)¹` (`E¹ ⊕ E` shifted is `E² ⊕ E¹`, `T(C¹) = (TC)¹`, `T(O¹) = (TO)¹`). -/
theorem _root_.Polyfold.LocalModel.isScSmoothRetractMap_shift_tangent_id (M : LocalModel) :
    IsScSmoothRetractMap M.shift.tangent.E M.shift.tangent.C M.shift.tangent.O M.tangent.shift.E
      M.tangent.shift.C M.tangent.shift.O id :=
  ⟨fun a ha => by
    change a ∈ M.E.tangent.lvlSet (retractTangent M.E M.C M.O) 1
    rw [← retractTangent_shift_of_isScRetract M.isScRetract]; exact ha,
   fun R _ => R.isScSmooth⟩

/-- `id : (TO)¹ → T(O¹)` is sc-smooth. -/
theorem _root_.Polyfold.LocalModel.isScSmoothRetractMap_tangent_shift_id (M : LocalModel) :
    IsScSmoothRetractMap M.tangent.shift.E M.tangent.shift.C M.tangent.shift.O M.shift.tangent.E
      M.shift.tangent.C M.shift.tangent.O id :=
  ⟨fun a ha => by
    change a ∈ retractTangent M.E.shift (M.E.lvlSet M.C 1) (M.E.lvlSet M.O 1)
    rw [retractTangent_shift_of_isScRetract M.isScRetract]; exact ha,
   fun R _ => R.isScSmooth⟩

section Smooth

variable {φ : MChart X} (hφ : P.IsChart φ)

/-- **The identification is the identity in charts**: in the chart `T(φ¹)` of `T(X¹)` and the
level chart `(Tφ)¹` of `(TX)¹`, `Φ` is the identity of `T(O¹) = (TO)¹`. -/
theorem levelChart_tangentShiftMap (α₀ : P.TangentSpace) (β₀ : P.tangentPolyfold.Level 1)
    (y₀ : P.Level 1) {α : P.shift.TangentSpace}
    (hα : α ∈ tangentChartSet (P := P.shift) (levelChart hφ y₀)) :
    levelChart (P.tangentPolyfold_isChart hφ α₀) β₀ (tangentShiftMap α) =
      tangentChartMap (P.shift_isChart hφ y₀) α := by
  have hx : shiftBase α ∈ φ.source := hα
  rw [levelChart_apply]
  apply φ.model.E.tangent.toBase_injective 1
  refine (P.tangentPolyfold.toBase_levelLift (P.tangentPolyfold_isChart hφ α₀)
    (tangentLower_mem_tangentChartSet hx) (tangentLower_mem_levelSet α)).trans ?_
  rw [tangentChart_apply, tangentChartMap_tangentLower α hφ hx y₀]

lemma mapsTo_tangentChart_shift_model (y₀ : P.Level 1) (α₀ : P.shift.TangentSpace)
    (β₀ : P.tangentPolyfold.Level 1) (α₁ : P.TangentSpace) :
    MapsTo (tangentChart (P.shift_isChart hφ y₀) α₀)
      (tangentChart (P.shift_isChart hφ y₀) α₀).source
      (levelChart (P.tangentPolyfold_isChart hφ α₁) β₀).model.O := fun β hβ => by
  have := (tangentChart (P.shift_isChart hφ y₀) α₀).mapsTo_model β hβ
  change _ ∈ φ.model.E.tangent.lvlSet (retractTangent φ.model.E φ.model.C φ.model.O) 1
  rw [← retractTangent_shift_of_isScRetract φ.model.isScRetract]; exact this

lemma mapsTo_levelChart_tangent_model (y₀ : P.Level 1) (α₀ : P.shift.TangentSpace)
    (β₀ : P.tangentPolyfold.Level 1) (α₁ : P.TangentSpace) :
    MapsTo (levelChart (P.tangentPolyfold_isChart hφ α₁) β₀)
      (levelChart (P.tangentPolyfold_isChart hφ α₁) β₀).source
      (tangentChart (P.shift_isChart hφ y₀) α₀).model.O := fun β hβ => by
  have := (levelChart (P.tangentPolyfold_isChart hφ α₁) β₀).mapsTo_model β hβ
  change _ ∈ retractTangent φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1)
    (φ.model.E.lvlSet φ.model.O 1)
  rw [retractTangent_shift_of_isScRetract φ.model.isScRetract]; exact this

/-- On the chart domain, `Φ⁻¹ = T(φ¹)⁻¹ ∘ (Tφ)¹`. -/
lemma tangentShiftEquiv_symm_mem_source (y₀ : P.Level 1) (α₀ : P.shift.TangentSpace)
    (β₀ : P.tangentPolyfold.Level 1) (α₁ : P.TangentSpace) {γ : P.tangentPolyfold.Level 1}
    (hγ : γ ∈ (levelChart (P.tangentPolyfold_isChart hφ α₁) β₀).source) :
    tangentShiftEquiv.symm γ ∈ (tangentChart (P.shift_isChart hφ y₀) α₀).source := by
  change shiftBase _ ∈ φ.source
  rw [shiftBase_symm]; exact hγ

end Smooth

/-- `Φ : T(X¹) → (TX)¹` is continuous. -/
theorem continuous_tangentShiftMap : Continuous (tangentShiftMap (P := P)) := by
  refine continuous_iff_continuousAt.2 fun α => ?_
  have hφ := P.someChart_isChart (shiftBase α)
  have hx := P.mem_someChart_source (shiftBase α)
  set y := P.shift.levelVal 1 (P.shift.tangentProj α)
  have hχ := P.shift_isChart hφ y
  set Tχ := tangentChart hχ α with hTχ
  set Ξ := levelChart (P.tangentPolyfold_isChart hφ (tangentLower α)) (tangentShiftMap α) with hΞ
  have hα : α ∈ Tχ.source := hx
  have heq : EqOn tangentShiftMap (Ξ.symm ∘ Tχ) Tχ.source := fun β hβ => by
    change tangentShiftMap β = Ξ.symm (tangentChartMap hχ β)
    rw [← levelChart_tangentShiftMap hφ (tangentLower α) (tangentShiftMap α) y hβ]
    exact (Ξ.symm_apply_apply (tangentLower_mem_tangentChartSet (P := P) hβ)).symm
  have hcont : ContinuousOn (Ξ.symm ∘ Tχ) Tχ.source :=
    Ξ.continuousOn_invFun.comp Tχ.continuousOn_toFun
      (mapsTo_tangentChart_shift_model hφ y α (tangentShiftMap α) (tangentLower α))
  exact (hcont.congr heq).continuousAt (Tχ.isOpen_source.mem_nhds hα)

/-- `Φ⁻¹ : (TX)¹ → T(X¹)` is continuous. -/
theorem continuous_tangentShiftEquiv_symm : Continuous (tangentShiftEquiv (P := P)).symm := by
  refine continuous_iff_continuousAt.2 fun β => ?_
  set α := tangentShiftEquiv.symm β with hαdef
  have hφ := P.someChart_isChart (shiftBase α)
  have hx := P.mem_someChart_source (shiftBase α)
  set y := P.shift.levelVal 1 (P.shift.tangentProj α)
  have hχ := P.shift_isChart hφ y
  set Tχ := tangentChart hχ α with hTχ
  set Ξ := levelChart (P.tangentPolyfold_isChart hφ (tangentLower α)) β with hΞ
  have hβ : β ∈ Ξ.source := by
    have h1 : P.tangentPolyfold.levelVal 1 β = tangentLower α :=
      (congrArg (P.tangentPolyfold.levelVal 1) (tangentShiftMap_symm β)).symm
    change P.tangentPolyfold.levelVal 1 β ∈ tangentChartSet (P := P) (P.someChart (shiftBase α))
    rw [h1]; exact tangentLower_mem_tangentChartSet (P := P) hx
  have heq : EqOn tangentShiftEquiv.symm (Tχ.symm ∘ Ξ) Ξ.source := fun γ hγ => by
    have hs := tangentShiftEquiv_symm_mem_source hφ y α β (tangentLower α) hγ
    have h2 := levelChart_tangentShiftMap hφ (tangentLower α) β y hs
    rw [tangentShiftMap_symm] at h2
    change tangentShiftEquiv.symm γ = Tχ.symm (Ξ γ)
    rw [h2]
    exact (Tχ.symm_apply_apply hs).symm
  have hcont : ContinuousOn (Tχ.symm ∘ Ξ) Ξ.source :=
    Tχ.continuousOn_invFun.comp Ξ.continuousOn_toFun
      (mapsTo_levelChart_tangent_model hφ y α β (tangentLower α))
  exact (hcont.congr heq).continuousAt (Ξ.isOpen_source.mem_nhds hβ)

/-- **Proposition 2.3.17, the homeomorphism `T(X¹) ≅ (TX)¹`.** -/
def tangentShiftHomeomorph : P.shift.TangentSpace ≃ₜ P.tangentPolyfold.Level 1 where
  toEquiv := tangentShiftEquiv
  continuous_toFun := continuous_tangentShiftMap
  continuous_invFun := continuous_tangentShiftEquiv_symm

/-- `Φ : T(X¹) → (TX)¹` is sc-smooth (the identity in the charts `T(φ¹)`, `(Tφ)¹`). -/
theorem tangentShiftMap_isScSmooth :
    P.shift.tangentPolyfold.IsScSmoothMap P.tangentPolyfold.shift tangentShiftMap := by
  refine IsScSmoothOn.of_exists_charts isOpen_univ continuous_tangentShiftMap.continuousOn
    fun α _ => ?_
  have hφ := P.someChart_isChart (shiftBase α)
  have hx := P.mem_someChart_source (shiftBase α)
  set y := P.shift.levelVal 1 (P.shift.tangentProj α)
  have hχ := P.shift_isChart hφ y
  refine ⟨tangentChart hχ α,
    levelChart (P.tangentPolyfold_isChart hφ (tangentLower α)) (tangentShiftMap α),
    tangentChartSet (P := P.shift) (levelChart hφ y), P.shift.tangentPolyfold_isChart hχ α,
    P.tangentPolyfold.shift_isChart (P.tangentPolyfold_isChart hφ _) _,
    isOpen_tangentChartSet hχ, hx, fun β hβ => ⟨mem_univ _, hβ⟩,
    fun β hβ => tangentLower_mem_tangentChartSet (P := P) hβ, ?_⟩
  have himg : tangentChart hχ α '' tangentChartSet (P := P.shift) (levelChart hφ y) =
      (tangentChart hχ α).model.O := (tangentChart hχ α).image_source
  rw [himg]
  refine (LocalModel.isScSmoothRetractMap_shift_tangent_id
    (P.someChart (shiftBase α)).model).congr fun a ha => ?_
  have ha' : a ∈ (tangentChart hχ α).model.O := ha
  have hs := (tangentChart hχ α).symm_mapsTo ha'
  have h1 := levelChart_tangentShiftMap hφ (tangentLower α) (tangentShiftMap α) y hs
  have h2 : tangentChartMap hχ ((tangentChart hχ α).symm a) = a :=
    (tangentChart hχ α).apply_symm_apply ha'
  exact (h1.trans h2).symm

/-- `Φ⁻¹ : (TX)¹ → T(X¹)` is sc-smooth. -/
theorem tangentShiftEquiv_symm_isScSmooth :
    P.tangentPolyfold.shift.IsScSmoothMap P.shift.tangentPolyfold tangentShiftEquiv.symm := by
  refine IsScSmoothOn.of_exists_charts isOpen_univ
    continuous_tangentShiftEquiv_symm.continuousOn fun β _ => ?_
  set α := tangentShiftEquiv.symm β with hαdef
  have hφ := P.someChart_isChart (shiftBase α)
  have hx := P.mem_someChart_source (shiftBase α)
  set y := P.shift.levelVal 1 (P.shift.tangentProj α)
  have hχ := P.shift_isChart hφ y
  set Ξ := levelChart (P.tangentPolyfold_isChart hφ (tangentLower α)) β with hΞ
  have hβ : β ∈ Ξ.source := by
    have h1 : P.tangentPolyfold.levelVal 1 β = tangentLower α :=
      (congrArg (P.tangentPolyfold.levelVal 1) (tangentShiftMap_symm β)).symm
    change P.tangentPolyfold.levelVal 1 β ∈ tangentChartSet (P := P) (P.someChart (shiftBase α))
    rw [h1]; exact tangentLower_mem_tangentChartSet (P := P) hx
  refine ⟨Ξ, tangentChart hχ α, Ξ.source,
    P.tangentPolyfold.shift_isChart (P.tangentPolyfold_isChart hφ _) _,
    P.shift.tangentPolyfold_isChart hχ α, Ξ.isOpen_source, hβ, fun γ hγ => ⟨mem_univ _, hγ⟩,
    fun γ hγ => tangentShiftEquiv_symm_mem_source hφ y α β (tangentLower α) hγ, ?_⟩
  rw [Ξ.image_source]
  refine (LocalModel.isScSmoothRetractMap_tangent_shift_id
    (P.someChart (shiftBase α)).model).congr fun b hb => ?_
  have hb' : b ∈ Ξ.model.O := hb
  have hs := Ξ.symm_mapsTo hb'
  have hs' := tangentShiftEquiv_symm_mem_source hφ y α β (tangentLower α) hs
  have h2 := levelChart_tangentShiftMap hφ (tangentLower α) β y hs'
  rw [tangentShiftMap_symm, Ξ.apply_symm_apply hb'] at h2
  exact h2

/-- The projection `p¹ : (TX)¹ → (X¹)¹`, the level-`1` map of `p : TX → X¹`. -/
def tangentProjShift (β : P.tangentPolyfold.Level 1) : P.shift.Level 1 :=
  P.shift.levelMk 1 (P.tangentProj (P.tangentPolyfold.levelVal 1 β))
    (P.tangentProj_isScSmooth.mapsTo_levelSet 1 (P.tangentPolyfold.levelVal_mem β))

/-- `p¹ : (TX)¹ → (X¹)¹` is sc-smooth (raising the index of `p`). -/
theorem tangentProjShift_isScSmooth :
    P.tangentPolyfold.shift.IsScSmoothMap P.shift.shift tangentProjShift :=
  IsScSmoothMap.levelOne P.tangentProj_isScSmooth fun _ => rfl

/-- `p¹ ∘ Φ = p_{X¹}`: the identification covers the identity of `(X¹)¹`. -/
theorem tangentProjShift_tangentShiftMap (α : P.shift.TangentSpace) :
    tangentProjShift (tangentShiftMap α) = P.shift.tangentProj α :=
  level_ext (tangentProj_tangentLower α)

/-- `Φ : T(X¹) → (TX)¹` is an sc-diffeomorphism. -/
theorem tangentShiftEquiv_isScDiffeoOn :
    P.shift.tangentPolyfold.IsScDiffeoOn P.tangentPolyfold.shift tangentShiftEquiv
      tangentShiftEquiv.symm univ univ :=
  ⟨tangentShiftMap_isScSmooth, tangentShiftEquiv_symm_isScSmooth, mapsTo_univ _ _,
    mapsTo_univ _ _, fun α _ => tangentShiftEquiv.symm_apply_apply α,
    fun β _ => tangentShiftEquiv.apply_symm_apply β⟩

/-- **2021 Proposition 2.3.17, p. 42 (new in the 2021 edition)**, for `i = 1`: the natural
identification `T(X¹) ≡ (TX)¹`.
(1) `Φ : T(X¹) → (TX)¹` is a bijection which is an sc-diffeomorphism between the M-polyfolds
`T(X¹)` and `(TX)¹` (in particular a homeomorphism, `tangentShiftHomeomorph`);
(2) it covers the identity of `(X¹)¹`: `p¹ ∘ Φ = p_{X¹}`, where `p¹ : (TX)¹ → (X¹)¹` is the
level-`1` map of `p : TX → X¹`, (3) itself sc-smooth;
(4) it is natural: in every chart `ψ` of `X` around the base point, `Tψ(Φ α) = ι(T(ψ¹) α)`, so
`Φ` does not depend on the charts used to define it;
(5) as a map of bundles it is, in the charts `T(φ¹)` and `(Tφ)¹`, the identity of
`T(O¹) = (TO)¹` (in particular linear on the fibres). -/
theorem _root_.Polyfold.proposition_2_3_17 :
    P.shift.tangentPolyfold.IsScDiffeoOn P.tangentPolyfold.shift tangentShiftEquiv
      tangentShiftEquiv.symm univ univ ∧
    (∀ α : P.shift.TangentSpace, tangentProjShift (tangentShiftEquiv α) = P.shift.tangentProj α) ∧
    P.tangentPolyfold.shift.IsScSmoothMap P.shift.shift tangentProjShift ∧
    (∀ (α : P.shift.TangentSpace) {ψ : MChart X} (hψ : P.IsChart ψ), shiftBase α ∈ ψ.source →
      ∀ y₀ : P.Level 1, tangentChartMap hψ (P.tangentPolyfold.levelVal 1 (tangentShiftEquiv α)) =
        ψ.model.E.tangent.toBase 1 (tangentChartMap (P.shift_isChart hψ y₀) α)) ∧
    (∀ {φ : MChart X} (hφ : P.IsChart φ) (α₀ : P.TangentSpace) (β₀ : P.tangentPolyfold.Level 1)
      (y₀ : P.Level 1) (α : P.shift.TangentSpace),
      α ∈ tangentChartSet (P := P.shift) (levelChart hφ y₀) →
      levelChart (P.tangentPolyfold_isChart hφ α₀) β₀ (tangentShiftEquiv α) =
        tangentChartMap (P.shift_isChart hφ y₀) α) :=
  ⟨tangentShiftEquiv_isScDiffeoOn, tangentProjShift_tangentShiftMap, tangentProjShift_isScSmooth,
    fun α _ hψ hx y₀ => tangentChartMap_tangentLower α hψ hx y₀,
    fun hφ α₀ β₀ y₀ _ hα => levelChart_tangentShiftMap hφ α₀ β₀ y₀ hα⟩

/-! ### Raising the index of an sc-diffeomorphism; `i = 2` -/

section LevelOneEquiv

universe v w

variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}

/-- The level-`1` map `Y¹ ≃ Z¹` of a bijection `e : Y ≃ Z` which is sc-smooth in both
directions. -/
def levelOneEquiv (e : Y ≃ Z) (he : Q.IsScSmoothMap S e) (he' : S.IsScSmoothMap Q e.symm) :
    Q.Level 1 ≃ S.Level 1 where
  toFun y := S.levelMk 1 (e (Q.levelVal 1 y)) (he.mapsTo_levelSet 1 (Q.levelVal_mem y))
  invFun z := Q.levelMk 1 (e.symm (S.levelVal 1 z)) (he'.mapsTo_levelSet 1 (S.levelVal_mem z))
  left_inv _ := level_ext (e.symm_apply_apply _)
  right_inv _ := level_ext (e.apply_symm_apply _)

variable (e : Y ≃ Z) (he : Q.IsScSmoothMap S e) (he' : S.IsScSmoothMap Q e.symm)

@[simp] lemma levelVal_levelOneEquiv (y : Q.Level 1) :
    S.levelVal 1 (levelOneEquiv e he he' y) = e (Q.levelVal 1 y) := rfl

@[simp] lemma levelVal_levelOneEquiv_symm (z : S.Level 1) :
    Q.levelVal 1 ((levelOneEquiv e he he').symm z) = e.symm (S.levelVal 1 z) := rfl

/-- **Raising the index of an sc-diffeomorphism**: `e¹ : Y¹ → Z¹` is an sc-diffeomorphism. -/
theorem levelOneEquiv_isScDiffeoOn :
    Q.shift.IsScDiffeoOn S.shift (levelOneEquiv e he he') (levelOneEquiv e he he').symm
      univ univ :=
  ⟨IsScSmoothMap.levelOne he fun _ => rfl, IsScSmoothMap.levelOne he' fun _ => rfl,
    mapsTo_univ _ _, mapsTo_univ _ _, fun y _ => (levelOneEquiv e he he').symm_apply_apply y,
    fun z _ => (levelOneEquiv e he he').apply_symm_apply z⟩

end LevelOneEquiv

/-- The identification `T(X²) ≡ (TX)²` (`X² = (X¹)¹`, `(TX)² = ((TX)¹)¹`): `Φ` for `X¹`, then the
index raise of `Φ⁻¹` for `X`. -/
def tangentShiftEquivTwo : P.shift.shift.TangentSpace ≃ P.tangentPolyfold.shift.Level 1 :=
  ((levelOneEquiv tangentShiftEquiv.symm tangentShiftEquiv_symm_isScSmooth
    tangentShiftMap_isScSmooth).trans (tangentShiftEquiv (P := P.shift)).symm).symm

/-- The projection `p² : (TX)² → (X¹)²`. -/
def tangentProjShiftTwo (γ : P.tangentPolyfold.shift.Level 1) : P.shift.shift.Level 1 :=
  P.shift.shift.levelMk 1 (tangentProjShift (P.tangentPolyfold.shift.levelVal 1 γ))
    (tangentProjShift_isScSmooth.mapsTo_levelSet 1 (P.tangentPolyfold.shift.levelVal_mem γ))

/-- **2021 Proposition 2.3.17, p. 42, for `i = 2`** (iterating the case `i = 1`; every fixed `i`
is obtained in the same way): `T(X²) ≡ (TX)²` is an sc-diffeomorphism covering the identity of
`(X¹)² = (X²)¹`. -/
theorem _root_.Polyfold.proposition_2_3_17_two :
    P.shift.shift.tangentPolyfold.IsScDiffeoOn P.tangentPolyfold.shift.shift tangentShiftEquivTwo
      tangentShiftEquivTwo.symm univ univ ∧
    ∀ α : P.shift.shift.TangentSpace,
      tangentProjShiftTwo (tangentShiftEquivTwo α) = P.shift.shift.tangentProj α := by
  have h1 := levelOneEquiv_isScDiffeoOn (tangentShiftEquiv (P := P)).symm
    tangentShiftEquiv_symm_isScSmooth tangentShiftMap_isScSmooth
  have h2 := tangentShiftEquiv_isScDiffeoOn (P := P.shift)
  refine ⟨⟨?_, ?_, mapsTo_univ _ _, mapsTo_univ _ _,
    fun α _ => tangentShiftEquivTwo.symm_apply_apply α,
    fun γ _ => tangentShiftEquivTwo.apply_symm_apply γ⟩, fun α => ?_⟩
  · have := IsScSmoothMap.comp h1.isScSmoothOn_inv h2.isScSmoothOn
    exact this
  · have := IsScSmoothMap.comp h2.isScSmoothOn_inv h1.isScSmoothOn
    exact this
  · apply level_ext
    change tangentProjShift (tangentShiftMap (tangentShiftMap α).1) = _
    rw [tangentProjShift_tangentShiftMap]
    exact tangentProj_tangentLower (P := P.shift) α

/-! ### Theorem 2.3.16 as a bundle statement -/

/-- **2021 Theorem 2.3.16, p. 40** (2017: Theorem 2.3; preprint: Theorem 2.16), as a bundle
statement: `TX` is an M-polyfold with the tangent charts `Tφ` of the charts `φ` of `X`;
`p : TX → X¹` is sc-smooth; in a tangent chart `p` is the first projection onto the level chart
`φ¹` of `X¹`; the models `(TO, TC, TE)` are bundle retracts (`Tr` covers `r¹`); and the transition
maps of tangent charts are bundle maps covering the transition maps of the charts `φ¹`. -/
theorem _root_.Polyfold.theorem_2_3_16 [ParacompactSpace P.TangentSpace]
    [ParacompactSpace (P.Level 1)] :
    (∀ {φ : MChart X} (hφ : P.IsChart φ) (α₀ : P.TangentSpace),
      P.tangentPolyfold.IsChart (tangentChart hφ α₀)) ∧
    P.tangentPolyfold.IsScSmoothMap P.shift P.tangentProj ∧
    (∀ {φ : MChart X} (hφ : P.IsChart φ) (x₀ : P.Level 1) {α : P.TangentSpace},
      α ∈ tangentChartSet φ →
        (tangentChartMap hφ α).1 = levelChart hφ x₀ (P.tangentProj α)) ∧
    (∀ (φ : MChart X) (R : ScRetraction φ.model.E φ.model.C), R.retract = φ.model.O →
      ScRetraction.IsBundleRetractionOver (E := φ.model.E.shift) (F := φ.model.E)
        R.tangentRetraction R.shift) ∧
    (∀ {φ ψ : MChart X} (hφ : P.IsChart φ) (hψ : P.IsChart ψ) (α₀ β₀ : P.TangentSpace),
      IsBundleMapOn (E := φ.model.E.shift) (F := φ.model.E) (E' := ψ.model.E.shift)
        (F' := ψ.model.E) ((tangentChart hφ α₀).transition (tangentChart hψ β₀))
        (retractTangent φ.model.E φ.model.C (φ.overlap ψ)) (levelMap (φ.transition ψ) 1)) := by
  refine ⟨fun hφ α₀ => P.tangentPolyfold_isChart hφ α₀, P.tangentProj_isScSmooth,
    fun hφ x₀ α hα => ?_, fun φ R _ => R.tangentRetraction_isBundleRetractionOver,
    fun {φ ψ} hφ hψ α₀ β₀ => ?_⟩
  · rw [tangentChartMap_fst hφ hα, levelChart_apply]
  · obtain ⟨ρ, hρ⟩ := ((hφ.compatible hψ (P := P)).1).retractTangentMap_isBundleMapOn
      (φ.isScRetract_overlap ψ)
    exact ⟨ρ, fun p hp => (tangentChart_transition hφ α₀ hψ β₀ hp).trans (hρ p hp)⟩

/-! ### The levels of `X¹`: `(X¹)_m ≅ X_{m+1}` (gap G.6) -/

section ShiftLevel

/-- In a chart, the level-`m` lift is transported by the level-`m` map of the transition map. -/
theorem levelLift_transition {φ ψ : MChart X} (hφ : P.IsChart φ) (hψ : P.IsChart ψ) {m : ℕ}
    {x : X} (hxφ : x ∈ φ.source) (hxψ : x ∈ ψ.source) (hxm : x ∈ P.levelSet m) :
    levelLift ψ m x = levelMap (φ.transition ψ) m (levelLift φ m x) := by
  symm
  apply levelMap_eq_of_toBase_eq
  rw [P.toBase_levelLift hψ hxψ hxm, P.toBase_levelLift hφ hxφ hxm, φ.transition_apply ψ hxφ]

/-- **The charts of `(X¹)_m` are those of `X_{m+1}`**: the level-`m` lift of the level chart `φ¹`
is the level-`(m+1)` lift of `φ` (`E¹_m = E_{m+1}`). -/
theorem levelLift_levelChart {φ : MChart X} (hφ : P.IsChart φ) (x₀ : P.Level 1) {m : ℕ}
    {x : P.Level 1} (hx : P.levelVal 1 x ∈ φ.source) (hxm : x ∈ P.shift.levelSet m) :
    levelLift (levelChart hφ x₀) m x = levelLift φ (m + 1) (P.levelVal 1 x) := by
  have hxm' : P.levelVal 1 x ∈ P.levelSet (m + 1) := (mem_shift_levelSet_iff x).1 hxm
  apply φ.model.E.toBase_injective (m + 1)
  rw [P.toBase_levelLift hφ hx hxm']
  have h := P.shift.toBase_levelLift (P.shift_isChart hφ x₀) (x := x) hx hxm
  refine (ScBanach.shift_toBase φ.model.E m (levelLift (levelChart hφ x₀) m x)).trans ?_
  change φ.model.E.toBase 1 ((levelChart hφ x₀).model.E.toBase m
    (levelLift (levelChart hφ x₀) m x)) = _
  rw [h, levelChart_apply, P.toBase_levelLift hφ hx (P.levelVal_mem x)]

variable (P) in
/-- The map `(X¹)_m → X_{m+1}` (the identity of the underlying points of `X`). -/
def shiftLevelMap (m : ℕ) (x : P.shift.Level m) : P.Level (m + 1) :=
  P.levelMk (m + 1) (P.levelVal 1 (P.shift.levelVal m x))
    ((mem_shift_levelSet_iff _).1 (P.shift.levelVal_mem x))

variable (P) in
/-- The map `X_{m+1} → (X¹)_m`. -/
def shiftLevelInv (m : ℕ) (y : P.Level (m + 1)) : P.shift.Level m :=
  P.shift.levelMk m (P.levelMk 1 (P.levelVal (m + 1) y)
    (P.levelSet_antitone (by omega : 1 ≤ m + 1) (P.levelVal_mem y)))
    ((mem_shift_levelSet_iff _).2 (P.levelVal_mem y))

/-- `(X¹)_m → X_{m+1}` is continuous. -/
theorem continuous_shiftLevelMap (m : ℕ) : Continuous (P.shiftLevelMap m) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨φ, hφ, W, hW, rfl⟩
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  set x₀ := P.shift.levelVal m x
  refine ⟨{x' : P.shift.Level m | P.shift.levelVal m x' ∈ (levelChart hφ x₀).source ∧
      levelLift (levelChart hφ x₀) m (P.shift.levelVal m x') ∈ W}, ?_,
    P.shift.isOpen_level_basic (P.shift_isChart hφ x₀) (m := m) hW, ?_⟩
  · rintro x' ⟨hx'φ, hx'W⟩
    refine ⟨hx'φ, ?_⟩
    rw [levelLift_levelChart hφ x₀ hx'φ (P.shift.levelVal_mem x')] at hx'W
    exact hx'W
  · refine ⟨hx.1, ?_⟩
    rw [levelLift_levelChart hφ x₀ hx.1 (P.shift.levelVal_mem x)]
    exact hx.2

/-- `X_{m+1} → (X¹)_m` is continuous: a basic open set of `(X¹)_m` for an arbitrary chart `ψ'` of
`X¹` is open in `X_{m+1}`, through the continuity of the level-`m` map of the transition map from
a level chart `φ¹` to `ψ'`. -/
theorem continuous_shiftLevelInv (m : ℕ) : Continuous (P.shiftLevelInv m) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨ψ', hψ', W', hW', rfl⟩
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  set x₁ : P.Level 1 := P.shift.levelVal m (P.shiftLevelInv m y) with hx₁
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source (P.levelVal (m + 1) y)
  set χ := levelChart hφ x₁ with hχdef
  have hχ : P.shift.IsChart χ := P.shift_isChart hφ x₁
  have hcomp := (hχ.compatible hψ' (P := P.shift)).1
  have hcont := hcomp.continuousOn_levelMap (χ.isScRetract_overlap ψ') m
  obtain ⟨G, hG, hGeq⟩ := (continuousOn_iff'.1 hcont) W' hW'
  obtain ⟨W₀, hW₀, hW₀eq⟩ := χ.exists_isOpen_image_eq (s := χ.source ∩ ψ'.source)
    inter_subset_left (χ.isOpen_source.inter ψ'.isOpen_source)
  -- the transition formula on the overlap
  have key : ∀ x' : P.shift.Level m, P.shift.levelVal m x' ∈ χ.source →
      P.shift.levelVal m x' ∈ ψ'.source →
      levelLift (levelChart hφ x₁) m (P.shift.levelVal m x') ∈
          χ.model.E.lvlSet (χ.overlap ψ') m ∧
        levelLift ψ' m (P.shift.levelVal m x') =
          levelMap (χ.transition ψ') m (levelLift χ m (P.shift.levelVal m x')) := by
    intro x' h1 h2
    refine ⟨?_, P.shift.levelLift_transition hχ hψ' h1 h2 (P.shift.levelVal_mem x')⟩
    rw [ScBanach.mem_lvlSet, P.shift.toBase_levelLift hχ h1 (P.shift.levelVal_mem x')]
    exact ⟨_, ⟨h1, h2⟩, rfl⟩
  refine ⟨{y' : P.Level (m + 1) | P.levelVal (m + 1) y' ∈ φ.source ∧
      levelLift φ (m + 1) (P.levelVal (m + 1) y') ∈ G ∩ φ.model.E.shift.lvlSet W₀ m}, ?_,
    P.isOpen_level_basic hφ (hG.inter (φ.model.E.shift.isOpen_lvlSet hW₀ m)), ?_⟩
  · rintro y' ⟨hy'φ, hy'G, hy'W₀⟩
    set x' := P.shiftLevelInv m y'
    have hx'χ : P.shift.levelVal m x' ∈ χ.source := hy'φ
    have hL := levelLift_levelChart hφ x₁ hx'χ (P.shift.levelVal_mem x')
    have hψx' : P.shift.levelVal m x' ∈ ψ'.source := by
      have hO : χ (P.shift.levelVal m x') ∈ χ.model.O ∩ W₀ := by
        refine ⟨χ.mapsTo_model _ hx'χ, ?_⟩
        rw [← P.shift.toBase_levelLift hχ hx'χ (P.shift.levelVal_mem x'), hL]
        exact hy'W₀
      rw [← hW₀eq] at hO
      obtain ⟨w, hw, hwx⟩ := hO
      rw [← χ.toPartialEquiv.injOn hw.1 hx'χ hwx]
      exact hw.2
    obtain ⟨hmem, htr⟩ := key x' hx'χ hψx'
    refine ⟨hψx', ?_⟩
    change levelLift ψ' m (P.shift.levelVal m x') ∈ W'
    rw [htr]
    have : levelLift χ m (P.shift.levelVal m x') ∈ G ∩ χ.model.E.lvlSet (χ.overlap ψ') m :=
      ⟨by rw [hL]; exact hy'G, hmem⟩
    rw [← hGeq] at this
    exact this.1
  · have hxχ : x₁ ∈ χ.source := hyφ
    obtain ⟨hmem, htr⟩ := key _ hxχ hy.1
    have hL := levelLift_levelChart hφ x₁ hxχ (P.shift.levelVal_mem (P.shiftLevelInv m y))
    have hW'mem : levelLift χ m x₁ ∈ levelMap (χ.transition ψ') m ⁻¹' W' ∩
        χ.model.E.lvlSet (χ.overlap ψ') m := ⟨by
          change levelMap (χ.transition ψ') m (levelLift χ m x₁) ∈ W'
          rw [← htr]; exact hy.2, hmem⟩
    rw [hGeq] at hW'mem
    refine ⟨hyφ, ?_, ?_⟩
    · have := hW'mem.1
      rw [hL] at this
      exact this
    · have hov := hmem
      rw [ScBanach.mem_lvlSet, hL] at hov
      have h3 : χ.model.E.toBase m (levelLift φ (m + 1) (P.levelVal 1 x₁)) ∈ χ.model.O ∩ W₀ := by
        rw [← hW₀eq]; exact hov
      change χ.model.E.toBase m (levelLift φ (m + 1) (P.levelVal 1 x₁)) ∈ W₀
      exact h3.2

variable (P) in
/-- **Gap G.6: the levels of `X¹` are those of `X`** (2021: the paragraph after Definition 2.3.8,
p. 37; preprint: after Definition 2.14): `(X¹)_m` and `X_{m+1}` are homeomorphic through the
identity of the underlying points. -/
def shiftLevelHomeomorph (m : ℕ) : P.shift.Level m ≃ₜ P.Level (m + 1) where
  toFun := P.shiftLevelMap m
  invFun := P.shiftLevelInv m
  left_inv _ := P.shift.level_ext (P.level_ext rfl)
  right_inv _ := P.level_ext rfl
  continuous_toFun := continuous_shiftLevelMap m
  continuous_invFun := continuous_shiftLevelInv m

/-- **Gap G.6** (2021: the paragraph after Definition 2.3.8, p. 37): for every `m`, the level
`(X¹)_m` of the M-polyfold `X¹` is the level `X_{m+1}` of `X`, with its topology (the homeomorphism
`shiftLevelHomeomorph` is the identity on points of `X`) and its charts (the level-`m` lift of the
chart `φ¹` of `X¹` is the level-`(m+1)` lift of `φ`). -/
theorem shift_level_eq (m : ℕ) :
    (∀ x : P.shift.Level m, P.levelVal (m + 1) (P.shiftLevelHomeomorph m x) =
      P.levelVal 1 (P.shift.levelVal m x)) ∧
    (∀ {φ : MChart X} (hφ : P.IsChart φ) (x₀ : P.Level 1) (x : P.shift.Level m),
      P.levelVal 1 (P.shift.levelVal m x) ∈ φ.source →
        levelLift (levelChart hφ x₀) m (P.shift.levelVal m x) =
          levelLift φ (m + 1) (P.levelVal 1 (P.shift.levelVal m x))) :=
  ⟨fun _ => rfl, fun hφ x₀ x hx => levelLift_levelChart hφ x₀ hx (P.shift.levelVal_mem x)⟩

end ShiftLevel

end MPolyfold

/-! ### 2021 Remark 2.4.2: the diagonal half-line in `[0,∞)³` -/

section DiagonalExample

/-- The sc-operator `const V → const V'` given by a linear map of finite-dimensional spaces. -/
def ScOperator.ofConst {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V']
    (L : V →L[ℝ] V') : ScOperator (ScBanach.const V) (ScBanach.const V') where
  lvl _ := L
  incl_comm _ _ := rfl

/-- The averaging map `x ↦ ((x₀ + x₁ + x₂)/3, …)` on `ℝ³`. -/
def diagonalAverage : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x _ => (x 0 + x 1 + x 2) / 3
      map_add' := fun x y => by ext; simp only [Pi.add_apply]; ring
      map_smul' := fun c x => by
        ext; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

/-- The diagonal embedding `ℝ → ℝ³`, `t ↦ (t, t, t)`. -/
def diagonalInclusion : (Fin 1 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun t _ => t 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The first coordinate `ℝ³ → ℝ`. -/
def diagonalFirst : (Fin 3 → ℝ) →L[ℝ] (Fin 1 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x _ => x 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

variable (W : ScBanach)

lemma diagonalAverage_apply (x : Fin 3 → ℝ) (i : Fin 3) :
    diagonalAverage x i = (x 0 + x 1 + x 2) / 3 := rfl

/-- The retraction `r(x, w) = ((x₀ + x₁ + x₂)/3 · (1, 1, 1), w)` of `C = [0,∞)³ ⊕ W` onto the
diagonal `Δ ⊕ W`. -/
def diagonalRetraction : ScRetraction ((ScBanach.const (Fin 3 → ℝ)).prod W) (quadrant 3 W 0) where
  U := quadrant 3 W 0
  toFun := (ScOperator.ofConst diagonalAverage).prodMap (ScOperator.id W) 0
  relOpen := MPolyfold.isRelOpenInQuadrant_quadrant 3 W
  mapsTo p hp i := by
    change 0 ≤ (p.1 0 + p.1 1 + p.1 2) / 3
    have := hp 0; have := hp 1; have := hp 2
    positivity
  isScSmooth := ((ScOperator.ofConst diagonalAverage).prodMap (ScOperator.id W)).isScSmooth
    (MPolyfold.isRelOpenInQuadrant_quadrant 3 W).isScDomain
  idem p _ := by
    refine Prod.ext (funext fun i => ?_) rfl
    change ((p.1 0 + p.1 1 + p.1 2) / 3 + (p.1 0 + p.1 1 + p.1 2) / 3 +
      (p.1 0 + p.1 1 + p.1 2) / 3) / 3 = (p.1 0 + p.1 1 + p.1 2) / 3
    ring

lemma mem_diagonalRetraction_retract_iff (p : ((ScBanach.const (Fin 3 → ℝ)).prod W) 0) :
    p ∈ (diagonalRetraction W).retract ↔ 0 ≤ p.1 0 ∧ ∀ i, p.1 i = p.1 0 := by
  rw [ScRetraction.mem_retract_iff]
  constructor
  · rintro ⟨hU, hp⟩
    refine ⟨hU 0, fun i => ?_⟩
    have h := congrArg (fun q : ((ScBanach.const (Fin 3 → ℝ)).prod W) 0 => q.1) hp
    have hi := congrFun h i
    have h0 := congrFun h 0
    change (p.1 0 + p.1 1 + p.1 2) / 3 = p.1 i at hi
    change (p.1 0 + p.1 1 + p.1 2) / 3 = p.1 0 at h0
    rw [← hi, h0]
  · rintro ⟨h0, hi⟩
    refine ⟨fun i => by rw [hi i]; exact h0, Prod.ext (funext fun j => ?_) rfl⟩
    change (p.1 0 + p.1 1 + p.1 2) / 3 = p.1 j
    rw [hi 1, hi 2, hi j]
    ring

lemma diagonalPoint_mem {s : ℝ} (hs : 0 ≤ s) (w : W 0) :
    (((fun _ => s : Fin 3 → ℝ), w) : ((ScBanach.const (Fin 3 → ℝ)).prod W) 0) ∈
      (diagonalRetraction W).retract :=
  (mem_diagonalRetraction_retract_iff W _).2 ⟨hs, fun _ => rfl⟩

/-- The local model `(Δ ⊕ W, [0,∞)³ ⊕ W, ℝ³ ⊕ W)` of 2021 Remark 2.4.2. -/
def diagonalModel : LocalModel :=
  ⟨(ScBanach.const (Fin 3 → ℝ)).prod W, quadrant 3 W 0, (diagonalRetraction W).retract,
    ⟨diagonalRetraction W, rfl⟩⟩

lemma diagonalModel_nonempty : (diagonalModel W).O.Nonempty :=
  ⟨_, diagonalPoint_mem W le_rfl 0⟩

/-- The half-line `Δ = {(s, s, s) | s ≥ 0}` (times `W`) with the M-polyfold structure of its
retract presentation `(Δ, [0,∞)³, ℝ³)` (2021 Remark 2.4.2, p. 44). -/
def diagonalPolyfold : MPolyfold (diagonalModel W).O :=
  (diagonalModel W).toMPolyfold (diagonalModel_nonempty W)

/-- The map `[0,∞) ⊕ W → Δ ⊕ W`, `(s, w) ↦ ((s, s, s), w)`. -/
def diagonalEmbed (x : quadrant 1 W 0) : (diagonalModel W).O :=
  ⟨(ScOperator.ofConst diagonalInclusion).prodMap (ScOperator.id W) 0 x.1,
    diagonalPoint_mem W (x.2 0) x.1.2⟩

/-- The inverse `Δ ⊕ W → [0,∞) ⊕ W`, `((s, s, s), w) ↦ (s, w)`. -/
def diagonalProject (y : (diagonalModel W).O) : quadrant 1 W 0 :=
  ⟨(ScOperator.ofConst diagonalFirst).prodMap (ScOperator.id W) 0 y.1,
    fun _ => ((mem_diagonalRetraction_retract_iff W _).1 y.2).1⟩

lemma isChart_diagonal_selfChart :
    (diagonalPolyfold W).IsChart ((diagonalModel W).selfChart (diagonalModel_nonempty W)) :=
  (diagonalPolyfold W).isChart_of_mem (mem_singleton _)

lemma isChart_quadrant_selfChart :
    (MPolyfold.quadrantPolyfold 1 W).IsChart
      ((LocalModel.ofRelOpen (MPolyfold.isRelOpenInQuadrant_quadrant 1 W)).selfChart
        (MPolyfold.quadrant_nonempty 1 W)) :=
  (MPolyfold.isRelOpenInQuadrant_quadrant 1 W).selfChart_isChart (MPolyfold.quadrant_nonempty 1 W)

/-- The map `s ↦ (s, s, s)` is an sc-diffeomorphism `[0,∞) ⊕ W → Δ ⊕ W` (2021 Remark 2.4.2,
p. 44). -/
theorem diagonalEmbed_isScDiffeoOn :
    (MPolyfold.quadrantPolyfold 1 W).IsScDiffeoOn (diagonalPolyfold W) (diagonalEmbed W)
      (diagonalProject W) univ univ := by
  have hφ := isChart_quadrant_selfChart W
  have hψ := isChart_diagonal_selfChart W
  set φ : MChart (quadrant 1 W 0) :=
    (LocalModel.ofRelOpen (MPolyfold.isRelOpenInQuadrant_quadrant 1 W)).selfChart
      (MPolyfold.quadrant_nonempty 1 W) with hφdef
  set ψ : MChart (diagonalModel W).O :=
    (diagonalModel W).selfChart (diagonalModel_nonempty W) with hψdef
  refine ⟨?_, ?_, mapsTo_univ _ _, mapsTo_univ _ _, fun x _ => ?_, fun y _ => ?_⟩
  · refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ ?_ fun x _ =>
      ⟨φ, ψ, univ, hφ, hψ, isOpen_univ, mem_univ x, fun z _ => ⟨mem_univ z, mem_univ z⟩,
        mapsTo_univ _ _, ?_⟩
    · exact (((ScOperator.ofConst diagonalInclusion).prodMap (ScOperator.id W) 0).continuous.comp
        continuous_subtype_val).subtype_mk _ |>.continuousOn
    · have hO : IsScRetract φ.model.E φ.model.C (φ '' univ) := by
        rw [show φ '' univ = φ.model.O from φ.image_source]; exact φ.model.isScRetract
      refine (((ScOperator.ofConst diagonalInclusion).prodMap
        (ScOperator.id W)).isScSmoothRetractMap (O₁ := (diagonalRetraction W).retract) hO ?_).congr
        ?_
      · rintro _ ⟨z, -, rfl⟩
        exact diagonalPoint_mem W (z.2 0) z.1.2
      · rintro _ ⟨z, -, rfl⟩
        have h : (φ.symm (φ z) : quadrant 1 W 0) = z := φ.symm_apply_apply (mem_univ z)
        exact (congrArg (fun y : quadrant 1 W 0 => (ψ (diagonalEmbed W y) :
          ((ScBanach.const (Fin 3 → ℝ)).prod W) 0)) h).symm
  · refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ ?_ fun y _ =>
      ⟨ψ, φ, univ, hψ, hφ, isOpen_univ, mem_univ y, fun z _ => ⟨mem_univ z, mem_univ z⟩,
        mapsTo_univ _ _, ?_⟩
    · exact (((ScOperator.ofConst diagonalFirst).prodMap (ScOperator.id W) 0).continuous.comp
        continuous_subtype_val).subtype_mk _ |>.continuousOn
    · have hO : IsScRetract ψ.model.E ψ.model.C (ψ '' univ) := by
        rw [show ψ '' univ = ψ.model.O from ψ.image_source]; exact ψ.model.isScRetract
      refine (((ScOperator.ofConst diagonalFirst).prodMap
        (ScOperator.id W)).isScSmoothRetractMap (O₁ := quadrant 1 W 0) hO ?_).congr ?_
      · rintro _ ⟨z, -, rfl⟩ _
        exact ((mem_diagonalRetraction_retract_iff W _).1 z.2).1
      · rintro _ ⟨z, -, rfl⟩
        have h : (ψ.symm (ψ z) : (diagonalModel W).O) = z := ψ.symm_apply_apply (mem_univ z)
        exact (congrArg (fun y : (diagonalModel W).O => (φ (diagonalProject W y) :
          ((ScBanach.const (Fin 1 → ℝ)).prod W) 0)) h).symm
  · refine Subtype.ext (Prod.ext (funext fun i => ?_) rfl)
    rw [Fin.fin_one_eq_zero i]
    rfl
  · obtain ⟨-, hi⟩ := (mem_diagonalRetraction_retract_iff W _).1 y.2
    refine Subtype.ext (Prod.ext (funext fun i => ?_) rfl)
    exact (hi i).symm

/-- `d_C(s, s, s) = 3` for `s = 0` and `0` otherwise, for the corner structure of
`C = [0,∞)³ ⊕ W` (2021 Remark 2.4.2, p. 44). -/
theorem degIndex_diagonal_quadrant {s : ℝ} (hs : 0 ≤ s) (w : W 0) :
    degIndex ((ScBanach.const (Fin 3 → ℝ)).prod W) (quadrant 3 W 0) ((fun _ => s), w) =
      if s = 0 then 3 else 0 := by
  rw [degIndex_quadrant (fun _ => hs)]
  unfold quadrantDeg
  split_ifs with h <;> simp [h]

/-- The point `(s, w)` of `[0,∞) ⊕ W`. -/
lemma halfLinePoint_mem {s : ℝ} (hs : 0 ≤ s) (w : W 0) :
    (((fun _ => s : Fin 1 → ℝ), w) : ((ScBanach.const (Fin 1 → ℝ)).prod W) 0) ∈
      quadrant 1 W 0 :=
  fun _ => hs

lemma degIndex_halfLinePoint {s : ℝ} (hs : 0 ≤ s) (w : W 0) :
    (MPolyfold.quadrantPolyfold 1 W).degIndex ⟨_, halfLinePoint_mem W hs w⟩ =
      if s = 0 then 1 else 0 := by
  rw [MPolyfold.quadrantPolyfold, corollary_2_4_13 (MPolyfold.isRelOpenInQuadrant_quadrant 1 W)
    (MPolyfold.quadrant_nonempty 1 W), degIndex_quadrant (halfLinePoint_mem W hs w)]
  unfold quadrantDeg
  split_ifs with h <;> simp [h]

/-- `d_Δ(s, s, s) = 1` for `s = 0` and `0` otherwise (2021 Remark 2.4.2, p. 45), by
Proposition 2.24 (2021 Proposition 2.4.4) applied to `s ↦ (s, s, s)`. -/
theorem diagonalPolyfold_degIndex {s : ℝ} (hs : 0 ≤ s) (w : W 0) :
    (diagonalPolyfold W).degIndex ⟨((fun _ => s), w), diagonalPoint_mem W hs w⟩ =
      if s = 0 then 1 else 0 := by
  rw [← degIndex_halfLinePoint W hs w]
  exact (proposition_2_4_4 (diagonalEmbed_isScDiffeoOn W)
    (mem_univ (⟨_, halfLinePoint_mem W hs w⟩ : quadrant 1 W 0))).symm

/-- The chart `Δ → [0,∞) ⊕ W`, `((s, s, s), w) ↦ (s, w)`, transported from the identity chart of
the half-line by the sc-diffeomorphism `diagonalProject`. -/
def diagonalHalfLineChart : MChart (diagonalModel W).O :=
  MPolyfold.transportChart (diagonalEmbed_isScDiffeoOn W).symm
    ((LocalModel.ofRelOpen (MPolyfold.isRelOpenInQuadrant_quadrant 1 W)).selfChart
      (MPolyfold.quadrant_nonempty 1 W))

theorem diagonalHalfLineChart_spec :
    (diagonalPolyfold W).IsChart (diagonalHalfLineChart W) ∧
      (diagonalHalfLineChart W).source = univ ∧
      (diagonalHalfLineChart W).model =
        LocalModel.ofRelOpen (MPolyfold.isRelOpenInQuadrant_quadrant 1 W) ∧
      ∀ x, MPolyfold.chartDegIndex (diagonalHalfLineChart W) x =
        (diagonalPolyfold W).degIndex x := by
  refine ⟨MPolyfold.transportChart_isChart _ (isChart_quadrant_selfChart W),
    univ_inter _, ?_, fun x => ?_⟩
  · change LocalModel.mk _ _ _ _ = LocalModel.mk _ _ _ _
    congr 1
    rw [univ_inter]
    exact MChart.image_source _
  · rw [proposition_2_4_4 (diagonalEmbed_isScDiffeoOn W).symm (mem_univ x),
      MPolyfold.quadrantPolyfold, corollary_2_4_13 (MPolyfold.isRelOpenInQuadrant_quadrant 1 W)
      (MPolyfold.quadrant_nonempty 1 W)]
    rfl

/-- **2021 Remark 2.4.2, pp. 44–45** (new in the 2021 edition): the half-line
`Δ = {(s, s, s) | s ≥ 0}` in `C = [0,∞)³`, here `Δ ⊕ W ⊆ [0,∞)³ ⊕ W` for an arbitrary `W`
(`W = 0` is the text's `ℝ³`).  `Δ` is a retract of `C` (`diagonalRetraction`, the average of the
coordinates), and with the resulting M-polyfold structure
1. `s ↦ (s, s, s)` is an sc-diffeomorphism `[0,∞) → Δ`;
2. `d_C(s, s, s) = 3` for `s = 0` and `0` otherwise, while `d_Δ(s, s, s) = 1` for `s = 0` and `0`
   otherwise; in the defining chart (the identity of the retract) the index is `d_C`;
3. `Δ` has an atlas whose local model is the relatively open subset `[0,∞)` (`⊕ W`) of a
   partial quadrant of `ℝ` (`⊕ W`): one chart, defined on all of `Δ`, in which the index is
   `d_Δ`. -/
theorem remark_2_4_2 :
    (MPolyfold.quadrantPolyfold 1 W).IsScDiffeoOn (diagonalPolyfold W) (diagonalEmbed W)
      (diagonalProject W) univ univ ∧
    (∀ {s : ℝ} (hs : 0 ≤ s) (w : W 0),
      degIndex ((ScBanach.const (Fin 3 → ℝ)).prod W) (quadrant 3 W 0) ((fun _ => s), w) =
        (if s = 0 then 3 else 0) ∧
      (diagonalPolyfold W).degIndex ⟨((fun _ => s), w), diagonalPoint_mem W hs w⟩ =
        (if s = 0 then 1 else 0)) ∧
    (∀ x, MPolyfold.chartDegIndex ((diagonalModel W).selfChart (diagonalModel_nonempty W)) x =
      degIndex ((ScBanach.const (Fin 3 → ℝ)).prod W) (quadrant 3 W 0) x.1) ∧
    ((diagonalPolyfold W).IsChart (diagonalHalfLineChart W) ∧
      (diagonalHalfLineChart W).source = univ ∧
      (diagonalHalfLineChart W).model =
        LocalModel.ofRelOpen (MPolyfold.isRelOpenInQuadrant_quadrant 1 W) ∧
      ∀ x, MPolyfold.chartDegIndex (diagonalHalfLineChart W) x =
        (diagonalPolyfold W).degIndex x) :=
  ⟨diagonalEmbed_isScDiffeoOn W, fun hs w =>
    ⟨degIndex_diagonal_quadrant W hs w, diagonalPolyfold_degIndex W hs w⟩, fun _ => rfl,
    diagonalHalfLineChart_spec W⟩

end DiagonalExample

end Polyfold
