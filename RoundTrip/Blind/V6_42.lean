import Polyfold
/-! Blind formalization of V6_42 (the text's §6.5, Lemma 6.30 and the bundle `L` after it,
pp. 222–223).

Text: along the path the kernels `L_t = ker F_t'(φ(t), 0)`, tangent spaces of the solution manifold
`S_t` of Lemma 6.30, form the smooth vector bundle `L` over `[0, 1]`.

Choices:
- Setting (as in `RoundTrip/Blind/V5_*.lean`): `X Y : Type` (universe 0); `PX : MPolyfold X`,
  `P : Y → X` with the fibrewise linear structure as instances, `B : StrongBundle PX P`; `X` tame
  (`PX.IsTame`: the §6 setting is a strong bundle over a tame M-polyfold, and general position,
  Definition 5.17, is defined there); `f` sc-Fredholm (`B.IsScFredholmSection f`).
- Paths: the text's sc-smooth `φ : [0, 1] → X` is an sc-smooth `γ : ℝ¹ → X`
  (`(rnPolyfold 1).IsScSmoothMap PX γ`; the vocabulary has no M-polyfold `[0, 1]`, and its paths
  `ScPath` are of this form); only `t ∈ J = [0, 1] ⊆ ℝ¹` matters.
- Sections `s(y, t)`, `sᵢ(y, t)` "on `X × [0, 1]`": sc⁺-sections of the pull-back `π*P` over
  `ℝ¹ × X` (Proposition 2.54, `B.pullback`, on the product M-polyfold `(rnPolyfold 1).prod PX`),
  parameter written first, with slices `pullbackSlice s t : X → Y`.  Forming `π*P` needs that
  `Prod.snd : ℝⁿ × X → X` is sc-smooth: taken as a hypothesis `hπ : SndSmooth PX` (it is true; I
  may not look up the project's lemma); the paracompactness of `ℝⁿ × X` and of `π*Y` are instance
  hypotheses, as in the vocabulary's `IsPush`.  `f − s(·, t)` is
  `subSec f s_t = sectionAdd P f (sectionSmul P (−1) s_t)`.
- (P) ("for every fixed `t`, `F_t` is at `(φ(t), 0)` in general position to the boundary of
  `X × ℝᵏ`"): `F_t(λ, y) = f(y) − s(y, t) + Σ λᵢ sᵢ(y, t)`, a section of the pull-back over
  `ℝᵏ × X` (`Fgen`, computed in the fibre `Y_y` via `fv`), is in general position at `(0, φ(t))`
  for every `t ∈ [0, 1]`, with the project's `IsGeneralPositionGerm` (Definition 5.17, audited as
  V5_31) for the bundle `B.pullback (hπ k)`.
- Reading in a chart: `DET(f, x)` and its orientations exist in the vocabulary only read in a
  chart point (`ChartPoint.linSet` = `Lin(f, x)`, Definition 6.1; `ChartPoint.Or` = `Or^f_x`,
  Definition 6.27; `orEquivRay`: `o ↦ o(L)`).  So everything is read in a strong bundle chart `c`
  of `B` (`B.IsChart c`) whose domain contains `φ([0, 1])` (the text's `U` lies in one chart, and
  it assumes `X = U`), with level-`1` lifts `z_t` of `φ(γ(t))` (unique; quantified over).
  `T_t = (f − s(·, t))'(φ(t))` is `linAt` of the principal part of `f − s_t` on `T_zO`, with
  values in `K_z`, and `φ_t(λ) = Σ λᵢ ŝᵢ(t)(φ(γ t))` (structure `Reading`, the two maps given with
  their defining equations; they are unique).  `F_t'(φ(t), 0)(v, λ) = T_t v + φ_t λ` (the text's
  (96) is written with this), so `L_t = ker(T_t ⊕ φ_t) ⊆ T_zO × ℝᵏ ⊆ E₀ × ℝᵏ` (`Reading.L`).
- Structure `Facts`: `T_t` Fredholm, `T_t ⊕ φ_t` onto, a continuous family `Λ` (`SubspaceFamily`
  over `J`) with `Λ_t = L_t`, `T_0 ∈ Lin(f, φ(0))`, `T_1 ∈ Lin(f, φ(1))` — what the construction
  uses; they follow from (P) by the text's Lemmas 6.29–6.31 (claimed in V6_39, V6_42).
- The push-forward `Facts.push` is the text's: `o₀ ↦ o₀(T_0)`, then the project's `propagate`
  (`stabRayEquiv` = `stabIota`, the text's `Φ_E` of the stabilization sequence followed by `ψ` of
  (94) — trusted from its docstring and `#print`; then `det(T ⊕ φ) ≅ λ(ker)`; then the
  continuation `contEquiv` of `λ(Λ)` over `J`; then the inverse at `t = 1`), then the orientation
  through the ray at `T_1`.  No sign `(−1)^{dim coker T}` is inserted: the text has none (the
  project's `IsStabKernels.push` inserts `stabSign` twice).
- B: for choices `s, s₁, …, s_k` with (P), read in any chart, there is a continuous family `Λ`
  (`SubspaceFamily` over `J`, local continuous frames) with `Λ_t = L_t` for all `t ∈ [0, 1]`,
  and it is smooth: near every `t₀` it has a frame `e₁, …, e_n` (`n = dim L_t`) of maps
  `ℝ¹ → E₀ × ℝᵏ` that are `C^∞` on (the relevant piece of) `[0, 1]` (`ContDiffOn ℝ ∞`).
- "smooth vector bundle": I check smoothness on level `0` of the chart only (`E₀ × ℝᵏ`), not on
  the higher levels `E_m × ℝᵏ` (where the `L_t ⊆ E_∞ × ℝᵏ` also lie); frames of a continuous
  family are only required on open subsets of `J`, smoothness on their image in `ℝ¹`.
- "tangent spaces of the solution manifold `S_t`": not formalized (that is Lemma 6.30 itself,
  V6_34); `L_t` is defined directly as `ker F_t'(φ(t), 0)`.
- Nothing looks false to me.
-/
namespace RoundTrip.V6_42
open Polyfold

/-- The parameter interval `[0, 1] ⊆ ℝ¹` (the project's paths are maps `ℝ¹ → X`). -/
abbrev J : Type := Set.Icc (0 : Fin 1 → ℝ) 1

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

open Classical in
/-- The value `g(y)` as a point of the fibre `Y_y` (junk `0` if `g(y) ∉ Y_y`). -/
noncomputable def fv (g : X → Y) (y : X) : P ⁻¹' {y} :=
  if h : P (g y) = y then ⟨g y, h⟩ else 0

/-- `−s`, fibrewise. -/
noncomputable def negSec (s : X → Y) : X → Y := sectionSmul P (fun _ => -1) s

/-- `f − s`, fibrewise. -/
noncomputable def subSec (f s : X → Y) : X → Y := sectionAdd P f (negSec (P := P) s)

/-- `G(λ, y) = g(y) + Σ λᵢ σᵢ(y)`, a section of `π*P → ℝᵏ × X`. -/
noncomputable def Fgen {k : ℕ} (g : X → Y) (σ : Fin k → X → Y) :
    (Fin k → ℝ) × X → pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X) :=
  fun w => ⟨(w, ((fv (P := P) g w.2 + ∑ i, w.1 i • fv (P := P) (σ i) w.2 : P ⁻¹' {w.2}) : Y)),
    Set.mem_singleton_iff.mp (fv (P := P) g w.2 + ∑ i, w.1 i • fv (P := P) (σ i) w.2).2⟩

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- `Prod.snd : ℝⁿ × X → X` is sc-smooth (needed to form the pull-back `π*P`). -/
abbrev SndSmooth (PX : MPolyfold X) : Prop :=
  ∀ n : ℕ, ((rnPolyfold n).prod PX).IsScSmoothMap PX (Prod.snd : (Fin n → ℝ) × X → X)

/-- The choices of pp. 221–222 along `φ = γ`: an sc⁺-section `s(y, t)` with
`s(φ(t), t) = f(φ(t))` and sc⁺-sections `s₁, …, s_k`, all over `ℝ × X`. -/
structure Choices (B : StrongBundle PX P) (hπ : SndSmooth PX) (f : X → Y)
    (γ : (Fin 1 → ℝ) → X) (k : ℕ) where
  s : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)
  s_plus : (B.pullback (hπ 1)).IsScPlusSection s
  s_eq : ∀ t : J, pullbackSlice s t (γ t) = f (γ t)
  σ : Fin k → (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)
  σ_plus : ∀ i, (B.pullback (hπ 1)).IsScPlusSection (σ i)

variable {B : StrongBundle PX P} {hπ : SndSmooth PX} {f : X → Y} {γ : (Fin 1 → ℝ) → X} {k : ℕ}

/-- `F_t(y, λ) = f(y) − s(y, t) + Σ λᵢ sᵢ(y, t)` on `ℝᵏ × X`. -/
noncomputable def Choices.Ft (D : Choices B hπ f γ k) (t : Fin 1 → ℝ) :
    (Fin k → ℝ) × X → pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X) :=
  Fgen (subSec (P := P) f (pullbackSlice D.s t)) (fun i => pullbackSlice (D.σ i) t)

/-- Property (P): for every `t ∈ [0, 1]`, `F_t` is at `(φ(t), 0)` in general position
(Definition 5.17, the project's `IsGeneralPositionGerm`) for the bundle over `ℝᵏ × X`. -/
def Choices.HasP (D : Choices B hπ f γ k) : Prop :=
  ∀ t : J, (B.pullback (hπ k)).IsGeneralPositionGerm (D.Ft t) (0, γ t)

variable (c : StrongBundleChart PX P) (hc : B.IsChart c) (hγ : ∀ t : J, γ t ∈ c.φ.source)
  (z : J → c.φ.model.E.lvl 1) (hz : ∀ t, c.φ.model.E.toBase 1 (z t) = c.φ.toPartialEquiv (γ t))

/-- The chart point of `c` at `φ(t)`, with the level-`1` lift `z t`. -/
abbrev cp (t : J) : ChartPoint B (γ t) := chartPt c hc (hγ t) (z t) (hz t)

/-- The linearizations read in the chart: `T_t = (f − s(·, t))'(φ(t)) : T_{φ(t)}X → Y_{φ(t)}`
and `φ_t(λ) = Σ λᵢ sᵢ(φ(t), t)` (both determined by their defining equations). -/
structure Reading (D : Choices B hπ f γ k) where
  T : ∀ t : J, (cp c hc hγ z hz t).T →L[ℝ] (cp c hc hγ z hz t).K
  hT : ∀ t v, ((T t v : (cp c hc hγ z hz t).K) : c.F.lvl 0) =
    linAt c.U c.R (c.principal (subSec (P := P) f (pullbackSlice D.s t))) (z t) v
  Φ : ∀ t : J, (Fin k → ℝ) →L[ℝ] (cp c hc hγ z hz t).K
  hΦ : ∀ t μ, ((Φ t μ : (cp c hc hγ z hz t).K) : c.F.lvl 0) =
    ∑ i, μ i • c.principal (pullbackSlice (D.σ i) t) (c.φ.toPartialEquiv (γ t))

variable {c hc hγ z hz} in
/-- `L_t = ker F_t'(φ(t), 0) = ker(T_t ⊕ φ_t)`, as a subspace of `E₀ × ℝᵏ`. -/
noncomputable abbrev Reading.L {D : Choices B hπ f γ k} (R : Reading c hc hγ z hz D) (t : J) :
    Submodule ℝ (c.φ.model.E.lvl 0 × (Fin k → ℝ)) :=
  Submodule.map
    ((cp c hc hγ z hz t).T.subtypeL.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ))).toLinearMap
      (LinearMap.ker ((R.T t).coprod (R.Φ t)).toLinearMap)

/-- The facts the construction uses (Lemmas 6.29–6.31): `T_t` Fredholm, `T_t ⊕ φ_t =
F_t'(φ(t), 0)` onto, the kernels `L_t` as a continuous family `Λ` in `E₀ × ℝᵏ`, and
`T_0 ∈ Lin(f, φ(0))`, `T_1 ∈ Lin(f, φ(1))`. -/
structure Facts {D : Choices B hπ f γ k} (R : Reading c hc hγ z hz D) where
  fred : ∀ t, (R.T t).IsFredholm
  surj : ∀ t, Function.Surjective ((R.T t).coprod (R.Φ t))
  Λ : SubspaceFamily J (c.φ.model.E.lvl 0 × (Fin k → ℝ))
  hΛ : ∀ t, Λ.L t = R.L t
  lin0 : R.T iccZero ∈ ChartPoint.linSet f (cp c hc hγ z hz iccZero)
  lin1 : R.T iccOne ∈ ChartPoint.linSet f (cp c hc hγ z hz iccOne)

variable {c hc hγ z hz}

/-- **The text's push-forward** `o₀ ↦ o₁ = φ_*o₀` (p. 224): `o₀ ↦ o₀(T_0)`, then `Φ_{E_0}`,
continuation in `λ(L)`, `(Φ_{E_1})⁻¹` (the project's `propagate`, whose docstring is exactly
this), then the orientation of `DET(f, φ(1))` through the ray at `T_1`.  No sign is inserted. -/
noncomputable def Facts.push {D : Choices B hπ f γ k} {R : Reading c hc hγ z hz D}
    (F : Facts c hc hγ z hz R) (hf : B.IsScFredholmSection f) :
    ChartPoint.Or f (cp c hc hγ z hz iccZero) hf ≃ ChartPoint.Or f (cp c hc hγ z hz iccOne) hf :=
  ((cp c hc hγ z hz iccZero).orEquivRay hf F.lin0).trans
    ((propagate F.Λ iccZero iccOne (F.fred _) (F.surj _)
        (kerEquivMap (cp c hc hγ z hz iccZero).T.subtypeL Subtype.val_injective (F.hΛ _))
        (F.fred _) (F.surj _)
        (kerEquivMap (cp c hc hγ z hz iccOne).T.subtypeL Subtype.val_injective (F.hΛ _))).trans
      ((cp c hc hγ z hz iccOne).orEquivRay hf F.lin1).symm)

end

/-- The stabilized kernels `L_t` form a smooth (in particular continuous) family over `[0, 1]`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    (B : StrongBundle PX P) (hπ : SndSmooth PX), PX.IsTame →
  ∀ f : X → Y, B.IsScFredholmSection f →
  ∀ (γ : (Fin 1 → ℝ) → X), (rnPolyfold 1).IsScSmoothMap PX γ →
  ∀ (c : StrongBundleChart PX P) (hc : B.IsChart c) (hγ : ∀ t : J, γ t ∈ c.φ.source)
    (z : J → c.φ.model.E.lvl 1)
    (hz : ∀ t, c.φ.model.E.toBase 1 (z t) = c.φ.toPartialEquiv (γ t)),
  ∀ (k : ℕ) (D : Choices B hπ f γ k), D.HasP → ∀ R : Reading c hc hγ z hz D,
    ∃ Λ : SubspaceFamily J (c.φ.model.E.lvl 0 × (Fin k → ℝ)), (∀ t, Λ.L t = R.L t) ∧
      ∀ t₀ : J, ∃ U : Set J, IsOpen U ∧ t₀ ∈ U ∧
        ∃ e : Fin Λ.n → (Fin 1 → ℝ) → c.φ.model.E.lvl 0 × (Fin k → ℝ),
          (∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e i) (Subtype.val '' U)) ∧
          ∀ t ∈ U, (∀ i, e i t ∈ Λ.L t) ∧ LinearIndependent ℝ (fun i => e i t)

end RoundTrip.V6_42
