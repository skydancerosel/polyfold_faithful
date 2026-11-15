import Polyfold.Chapter6.OrientationMainClean
import Polyfold.Chapter6.SmoothPathComponents2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 6, §6.6 "Local
Orientation Propagation": **Theorem 6.6.17**, p. 275, and the orientation space defined just
before it (pp. 274–275), for an arbitrary family of fibres with local transport data.

# The orientation space of local transport data

## The text, paraphrased

(pp. 274–275) For an sc-Fredholm section `f` of a strong bundle over a tame M-polyfold `X`, the
orientation space `O_f` consists of the pairs `(x, o)` with `x ∈ X_∞` and `o` an orientation of
`DET(f, x)`; `π_f : O_f → X_∞` is `(x, o) ↦ x`.

(Theorem 6.6.17, p. 275) There is a uniquely defined Hausdorff topology on `O_f` characterized by:
(1) `π_f` is a local homeomorphism; (2) every `x ∈ X_∞` has an open neighbourhood `U` in `X` such
that `O_f` has precisely two continuous sections over `U ∩ X_∞`; (3) a continuous section
`t ↦ (φ(t), o_t)` of the pull-back of `O_f` along an sc-smooth path `φ` has, for `t` close to
`t₀`, `o_t` equal to the local propagation of `o_{t₀}`.  The proof is left to the reader, in view
of Proposition 6.6.3 and Theorem 6.6.11.

## What is formalized

The theorem and its proof use only the following structure of the orientations: sets `O x`
indexed by the smooth points, open sets covering `X_∞` (the orientable neighbourhoods) and
push-forwards `O x₀ ≃ O x₁` along the sc-smooth paths in such a set, compatible with composition
and with change of the set.  This is `LocalTransport PX O` (`PathTransport.lean`).  For every
family `O` and every `L : LocalTransport PX O`:

* `LocalTransport.Total` (the pairs `(x, o)`, `x ∈ X_∞`, `o ∈ O x`), `proj`, `Pullback`, and the
  properties `IsContSectionOver`, `HasTwoContSections` (2), `IsPropagationContinuous` (3) of a
  topology on the total space; `IsOrientationTopology` collects them with `T2Space` and (1).
* `IsContOn L U o` (a section `o` carried along by the transport along every sc-smooth path in
  the open set `U`), `sec`, `basic`, and the topology `L.topology`: `W` is open iff
  `{y ∈ U_∞ | (y, o_y) ∈ W}` is open in `X_∞` for all such `U`, `o`.
* `isOpen_basic`, `continuousOn_sec`, `continuous_proj`, `exists_isContOn`, `chartHomeo`,
  `isLocalHomeomorph_proj` (1), `t2Space_topology`, `hasTwoContSections_topology` (2, when
  every `O x` has exactly two elements), `isPropagationContinuous_topology` (3).
* `eq_topology_of` (a topology with (1) and (3) is `L.topology`), `existsUnique_topology`, and
  `existsUnique_isOrientationTopology`: **Theorem 6.6.17** for `L`, when every `O x` has
  exactly two elements.
* Sections: `IsContOn.mono`, `IsContOn.congr`, `IsContOn.eq_of_eq` (two sections carried along
  over a connected open set agree if they agree at a point), `exists_other` and
  `IsContOn.of_other` (the other element of a two-element fibre), `isContOn_of_local`
  (`IsContOn` is a local property), `isOpen_setOf_sec_eq`, and
  `isContOn_univ_iff_continuous_sec`: `y ↦ (y, o_y)` is continuous for `L.topology` iff `o` is
  carried along by the transport along every sc-smooth path.

## Choices

* Paths are sc-smooth maps `ℝ → X` restricted to `[0, 1]`; "local propagation" in (3) is the
  push-forward `L.push` in a good set `L.Good U` containing the segment of the path.
* Sc-smooth paths in an open set are those of `MPolyfold.exists_nhds_scJoinedIn`; connected
  smooth parts of small neighbourhoods are `MPolyfold.hasConnectedSmoothNbhds`.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {O : ∀ x : X, x ∈ PX.smoothSet → Type v}

namespace LocalTransport

/-! ### The total space and the properties of a topology on it -/

/-- **The total space** of the family `O` over `X_∞`: the pairs `(x, o)` of a smooth point `x`
and `o ∈ O x` (for `O x = Or_x^f` the orientation space `O_f`, 2021, pp. 274–275). -/
abbrev Total (_L : LocalTransport PX O) : Type _ :=
  Σ x : PX.SmoothLevel, O (PX.smoothVal x) (PX.smoothVal_mem x)

variable (L : LocalTransport PX O)

/-- **The projection** `(x, o) ↦ x` of the total space to `X_∞`. -/
def proj : L.Total → PX.SmoothLevel := Sigma.fst

/-- **The pull-back of the total space** along a path `φ`: the pairs `(t, p)`, `t ∈ [0, 1]`,
with `φ(t)` the base point of `p`. -/
def Pullback (φ : (Fin 1 → ℝ) → X) : Set (unitInterval × L.Total) :=
  {q | φ (pt1 (q.1 : ℝ)) = PX.smoothVal q.2.1}

/-- A **continuous section over `U ∩ X_∞`** for a topology `t` on the total space. -/
def IsContSectionOver (t : TopologicalSpace L.Total) (U : Set X)
    (σ : PX.smoothVal ⁻¹' U → L.Total) : Prop :=
  @Continuous _ _ _ t σ ∧ ∀ y, (σ y).1 = y

/-- **Property (3)** of 2021 Theorem 6.6.17 for a topology `t` on the total space: for an
sc-smooth path `φ` and a continuous section `α(t) = (t, (φ(t), o_t))` of the pull-back, for `t`
near `t₀` the element `o_t` is the push-forward of `o_{t₀}` along `φ|[t₀, t]` in a good set. -/
def IsPropagationContinuous (t : TopologicalSpace L.Total) : Prop :=
  letI := t
  ∀ (φ : (Fin 1 → ℝ) → X) (hφ : (rnPolyfold 1).IsScSmoothMap PX φ)
    (α : unitInterval → L.Pullback φ), Continuous α → (∀ s, (α s).1.1 = s) →
    ∀ t₀ : unitInterval, ∀ᶠ t : unitInterval in 𝓝 t₀, ∃ (U : Set X)
      (hU : L.Good U) (hseg : ∀ s ∈ Icc (0 : ℝ) 1, segPath φ t₀ t (pt1 s) ∈ U)
      (h₀ : segPath φ t₀ t (pt1 0) = PX.smoothVal (α t₀).1.2.1)
      (h₁ : segPath φ t₀ t (pt1 1) = PX.smoothVal (α t).1.2.1),
      L.push hU (segPath φ t₀ t) (isScSmoothMap_segPath hφ t₀ t) hseg h₀ h₁
        (PX.smoothVal_mem _) (PX.smoothVal_mem _) (α t₀).1.2.2 = (α t).1.2.2

/-- **Property (2)** of 2021 Theorem 6.6.17 for a topology `t` on the total space: every
`x ∈ X_∞` has an open neighbourhood `U` in `X` over whose smooth part there are precisely two
continuous sections. -/
def HasTwoContSections (t : TopologicalSpace L.Total) : Prop :=
  ∀ x : PX.SmoothLevel, ∃ U : Set X, IsOpen U ∧ PX.smoothVal x ∈ U ∧
    ∃ σ₁ σ₂ : PX.smoothVal ⁻¹' U → L.Total, L.IsContSectionOver t U σ₁ ∧
      L.IsContSectionOver t U σ₂ ∧ σ₁ ≠ σ₂ ∧
      ∀ σ, L.IsContSectionOver t U σ → σ = σ₁ ∨ σ = σ₂

/-- **The properties of 2021 Theorem 6.6.17** of a topology on the total space: Hausdorff, (1)
the projection is a local homeomorphism, (2) and (3). -/
structure IsOrientationTopology (t : TopologicalSpace L.Total) : Prop where
  t2Space : @T2Space _ t
  isLocalHomeomorph : @IsLocalHomeomorph _ _ t _ L.proj
  twoSections : L.HasTwoContSections t
  propagation : L.IsPropagationContinuous t

/-! ### The topology -/

/-- A **continuous section over an open set `U`**: `o` carried along by the transport along
every sc-smooth path in `U`. -/
def IsContOn (U : Set X) (o : ∀ y (hy : y ∈ PX.smoothSet), O y hy) : Prop :=
  IsOpen U ∧ ∀ (γ : (Fin 1 → ℝ) → X) (hγ : (rnPolyfold 1).IsScSmoothMap PX γ),
    (∀ s ∈ Icc (0 : ℝ) 1, γ (pt1 s) ∈ U) → ∀ {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
      (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet),
      L.transport γ hγ h₀ h₁ hs₀ hs₁ (o x₀ hs₀) = o x₁ hs₁

/-- The section `y ↦ (y, o_y)`. -/
def sec (o : ∀ y (hy : y ∈ PX.smoothSet), O y hy) (y : PX.SmoothLevel) : L.Total :=
  ⟨y, o (PX.smoothVal y) (PX.smoothVal_mem y)⟩

/-- The image `{(y, o_y) | y ∈ U_∞}` of a section. -/
def basic (U : Set X) (o : ∀ y (hy : y ∈ PX.smoothSet), O y hy) : Set L.Total :=
  {p | PX.smoothVal p.1 ∈ U ∧ p.2 = o (PX.smoothVal p.1) (PX.smoothVal_mem p.1)}

/-- **The topology of the total space**: `W` is open iff `{y ∈ U_∞ | (y, o_y) ∈ W}` is open in
`X_∞` for every continuous section `o` over an open `U`. -/
@[instance_reducible] def topology : TopologicalSpace L.Total where
  IsOpen W := ∀ U o, L.IsContOn U o →
    IsOpen {y : PX.SmoothLevel | PX.smoothVal y ∈ U ∧ L.sec o y ∈ W}
  isOpen_univ U o h := by
    simp only [mem_univ, and_true]
    exact h.1.preimage PX.continuous_smoothVal
  isOpen_inter W₁ W₂ h₁ h₂ U o h := by
    convert (h₁ U o h).inter (h₂ U o h) using 1
    ext y
    exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, a, c⟩, fun ⟨⟨a, b⟩, _, c⟩ => ⟨a, b, c⟩⟩
  isOpen_sUnion S hS U o h := by
    have : {y : PX.SmoothLevel | PX.smoothVal y ∈ U ∧ L.sec o y ∈ ⋃₀ S} =
        ⋃ W ∈ S, {y | PX.smoothVal y ∈ U ∧ L.sec o y ∈ W} := by
      ext y
      simp only [mem_iUnion, exists_prop]
      exact ⟨fun ⟨a, W, hW, b⟩ => ⟨W, hW, a, b⟩, fun ⟨W, hW, a, b⟩ => ⟨a, W, hW, b⟩⟩
    rw [this]
    exact isOpen_biUnion fun W hW => hS W hW U o h

variable {L}

/-! ### Restriction, congruence, connected sets -/

/-- A continuous section over `U` is one over every open `V ⊆ U`. -/
theorem IsContOn.mono {U V : Set X} {o : ∀ y (hy : y ∈ PX.smoothSet), O y hy}
    (h : L.IsContOn U o) (hV : IsOpen V) (hVU : V ⊆ U) : L.IsContOn V o :=
  ⟨hV, fun γ hγ hγV => h.2 γ hγ fun s hs => hVU (hγV s hs)⟩

/-- A section agreeing over `U` with a continuous section over `U` is one. -/
theorem IsContOn.congr {U : Set X} {o o' : ∀ y (hy : y ∈ PX.smoothSet), O y hy}
    (h : L.IsContOn U o) (heq : ∀ y ∈ U, ∀ hs : y ∈ PX.smoothSet, o y hs = o' y hs) :
    L.IsContOn U o' := by
  refine ⟨h.1, fun γ hγ hγU x₀ x₁ h₀ h₁ hs₀ hs₁ => ?_⟩
  rw [← heq x₀ (h₀ ▸ hγU 0 ⟨le_rfl, zero_le_one⟩) hs₀,
    ← heq x₁ (h₁ ▸ hγU 1 ⟨zero_le_one, le_rfl⟩) hs₁]
  exact h.2 γ hγ hγU h₀ h₁ hs₀ hs₁

/-- **Two continuous sections over a connected open set which agree at one smooth point agree
at every smooth point** (smooth points of a connected open set are joined by sc-smooth paths in
it, `MPolyfold.scJoinedIn_of_isConnected`). -/
theorem IsContOn.eq_of_eq {U : Set X} {o o' : ∀ y (hy : y ∈ PX.smoothSet), O y hy}
    (h : L.IsContOn U o) (h' : L.IsContOn U o') (hc : IsPreconnected U) {x : X} (hx : x ∈ U)
    (hxs : x ∈ PX.smoothSet) (e : o x hxs = o' x hxs) {y : X} (hy : y ∈ U)
    (hys : y ∈ PX.smoothSet) : o y hys = o' y hys := by
  obtain ⟨γ, hγ, h₀, h₁, hγU⟩ := PX.scJoinedIn_of_isConnected h.1 ⟨⟨x, hx⟩, hc⟩ hx hy hxs hys
  rw [← h.2 γ hγ (fun s _ => hγU _) h₀ h₁ hxs hys, ← h'.2 γ hγ (fun s _ => hγU _) h₀ h₁ hxs hys,
    e]

/-- **In two-element fibres every section has the other section**: a section `o'` with
`o'_y ≠ o_y`, and every element different from `o_y` is `o'_y`. -/
theorem exists_other
    (htwo : ∀ y (hy : y ∈ PX.smoothSet), ∃ a b : O y hy, a ≠ b ∧ ∀ c, c = a ∨ c = b)
    (o : ∀ y (hy : y ∈ PX.smoothSet), O y hy) :
    ∃ o' : ∀ y (hy : y ∈ PX.smoothSet), O y hy, (∀ y hy, o' y hy ≠ o y hy) ∧
      ∀ y hy (c : O y hy), c ≠ o y hy → c = o' y hy := by
  classical
  have hne : ∀ y (hy : y ∈ PX.smoothSet), ∃ c : O y hy, c ≠ o y hy := fun y hy =>
    let ⟨a₁, a₂, ha, _⟩ := htwo y hy
    if h : o y hy = a₁ then ⟨a₂, h ▸ ha.symm⟩ else ⟨a₁, Ne.symm h⟩
  choose o' ho' using hne
  exact ⟨o', ho', fun y hy c hc =>
    let ⟨_, _, _, hall⟩ := htwo y hy
    eq_of_ne_of_ne_of_two hall hc (ho' y hy)⟩

/-- **The other section of a continuous section is continuous** (the transports are
bijections). -/
theorem IsContOn.of_other {U : Set X} {o o' : ∀ y (hy : y ∈ PX.smoothSet), O y hy}
    (h : L.IsContOn U o) (hne : ∀ y hy, o' y hy ≠ o y hy)
    (hother : ∀ y hy (c : O y hy), c ≠ o y hy → c = o' y hy) : L.IsContOn U o' :=
  ⟨h.1, fun γ hγ hγU x₀ _ h₀ h₁ hs₀ hs₁ =>
    hother _ _ _ fun e => hne x₀ hs₀ ((L.transport γ hγ h₀ h₁ hs₀ hs₁).injective
      (e.trans (h.2 γ hγ hγU h₀ h₁ hs₀ hs₁).symm))⟩

/-- **Two continuous sections agree near a point iff they agree at it.** -/
theorem IsContOn.eventually_iff {U U' : Set X} {o o' : ∀ y (hy : y ∈ PX.smoothSet), O y hy}
    (h : L.IsContOn U o) (h' : L.IsContOn U' o') {x : PX.SmoothLevel}
    (hx : PX.smoothVal x ∈ U) (hx' : PX.smoothVal x ∈ U') :
    ∀ᶠ y in 𝓝 x, PX.smoothVal y ∈ U ∧ PX.smoothVal y ∈ U' ∧
      (o (PX.smoothVal y) (PX.smoothVal_mem y) = o' (PX.smoothVal y) (PX.smoothVal_mem y) ↔
        o (PX.smoothVal x) (PX.smoothVal_mem x) = o' (PX.smoothVal x) (PX.smoothVal_mem x)) := by
  obtain ⟨V, hVo, hxV, hVW, hpath⟩ := PX.exists_nhds_scJoinedIn (h.1.inter h'.1) ⟨hx, hx'⟩
  filter_upwards [(hVo.preimage PX.continuous_smoothVal).mem_nhds hxV] with y hy
  obtain ⟨γ, hγ, h₀, h₁, hγW⟩ := hpath _ hxV _ hy (PX.smoothVal_mem x) (PX.smoothVal_mem y)
  refine ⟨(hVW hy).1, (hVW hy).2, ?_⟩
  rw [← h.2 γ hγ (fun s _ => (hγW _).1) h₀ h₁ (PX.smoothVal_mem x) (PX.smoothVal_mem y),
    ← h'.2 γ hγ (fun s _ => (hγW _).2) h₀ h₁ (PX.smoothVal_mem x) (PX.smoothVal_mem y)]
  exact (L.transport γ hγ h₀ h₁ _ _).apply_eq_iff_eq

/-! ### The local description -/

/-- The sets `{(y, o_y) | y ∈ U_∞}` of continuous sections are open. -/
theorem isOpen_basic {U : Set X} {o : ∀ y (hy : y ∈ PX.smoothSet), O y hy}
    (h : L.IsContOn U o) : IsOpen[L.topology] (L.basic U o) := by
  intro U' o' h'
  refine isOpen_iff_mem_nhds.2 fun y hy => ?_
  filter_upwards [h'.eventually_iff h hy.1 hy.2.1] with z hz
  exact ⟨hz.1, hz.2.1, hz.2.2.2 hy.2.2⟩

/-- A continuous section is continuous over `U_∞` for the topology of the total space. -/
theorem continuousOn_sec {U : Set X} {o : ∀ y (hy : y ∈ PX.smoothSet), O y hy}
    (h : L.IsContOn U o) :
    @ContinuousOn _ _ _ L.topology (L.sec o) (PX.smoothVal ⁻¹' U) := by
  let := L.topology
  exact (continuousOn_open_iff (h.1.preimage PX.continuous_smoothVal)).2 fun W hW => hW U o h

variable (L) in
/-- The projection is continuous. -/
theorem continuous_proj : @Continuous _ _ L.topology _ L.proj := by
  let := L.topology
  exact continuous_def.2 fun G hG U o h => (h.1.preimage PX.continuous_smoothVal).inter hG

/-- A point of `{(y, o_y) | y ∈ U_∞}` is `(x, o_x)` for its base point `x`. -/
theorem eq_sec_of_mem_basic {U : Set X} {o : ∀ y (hy : y ∈ PX.smoothSet), O y hy}
    {p : L.Total} (hp : p ∈ L.basic U o) : p = L.sec o p.1 :=
  Sigma.ext rfl (heq_of_eq hp.2)

/-- `(y, o_y) ∈ {(y, o_y) | y ∈ U_∞}` for `y ∈ U`. -/
theorem sec_mem_basic {U : Set X} {o : ∀ y (hy : y ∈ PX.smoothSet), O y hy}
    {y : PX.SmoothLevel} (hy : PX.smoothVal y ∈ U) : L.sec o y ∈ L.basic U o :=
  ⟨hy, rfl⟩

/-- `(y, o_y) = (y, o'_y)` iff `o_y = o'_y`. -/
theorem sec_eq_sec_iff {o o' : ∀ y (hy : y ∈ PX.smoothSet), O y hy} (y : PX.SmoothLevel) :
    L.sec o y = L.sec o' y ↔
      o (PX.smoothVal y) (PX.smoothVal_mem y) = o' (PX.smoothVal y) (PX.smoothVal_mem y) :=
  ⟨fun h => eq_of_heq (Sigma.mk.inj_iff.1 h).2, fun h => by unfold sec; rw [h]⟩

/-- `p = (y, o_y)` iff the second component of `p` is `o` at its base point, for `p` over `y`. -/
theorem eq_sec_iff {o : ∀ y (hy : y ∈ PX.smoothSet), O y hy} {p : L.Total}
    {y : PX.SmoothLevel} (hp : p.1 = y) :
    p = L.sec o y ↔ p.2 = o (PX.smoothVal p.1) (PX.smoothVal_mem p.1) := by
  obtain ⟨z, c⟩ := p
  dsimp only at hp ⊢
  subst hp
  exact ⟨fun h => eq_of_heq (Sigma.mk.inj_iff.1 h).2, fun h => by rw [h]; rfl⟩

variable (L) in
/-- **Every section of the projection is `y ↦ (y, o_y)`** for the map `o_y = σ(y)`. -/
theorem exists_eq_sec (σ : PX.SmoothLevel → L.Total) (hσ : ∀ y, (σ y).1 = y) :
    ∃ o : ∀ y (hy : y ∈ PX.smoothSet), O y hy, σ = L.sec o := by
  refine ⟨fun y hy => cast (congrArg (fun z : PX.SmoothLevel =>
    O (PX.smoothVal z) (PX.smoothVal_mem z)) (hσ (PX.smoothMk y hy)))
      (σ (PX.smoothMk y hy)).2,
    funext fun y => Sigma.ext (hσ y) ?_⟩
  exact (cast_heq _ _).symm

variable (L) in
/-- **Every point of the total space lies on a continuous section** over an open set contained
in a good set of `L` (sc-smooth paths from the point, and push-forwards along them). -/
theorem exists_isContOn (p : L.Total) :
    ∃ (U : Set X) (o : ∀ y (hy : y ∈ PX.smoothSet), O y hy), L.IsContOn U o ∧
      (∃ U', L.Good U' ∧ U ⊆ U') ∧ p ∈ L.basic U o := by
  classical
  obtain ⟨x, a⟩ := p
  obtain ⟨U', hU', hxU'⟩ := L.exists_good _ (PX.smoothVal_mem x)
  obtain ⟨V, hVo, hxV, hVU', hpath⟩ := PX.exists_nhds_scJoinedIn (L.isOpen hU') hxU'
  choose γ hγs hγ0 hγ1 hγU using fun y (hy : y ∈ V) (hys : y ∈ PX.smoothSet) =>
    (hpath _ hxV y hy (PX.smoothVal_mem x) hys : ∃ γ : (Fin 1 → ℝ) → X,
      (rnPolyfold 1).IsScSmoothMap PX γ ∧ γ (pt1 0) = PX.smoothVal x ∧ γ (pt1 1) = y ∧
        ∀ t, γ t ∈ U')
  let o : ∀ y (hy : y ∈ PX.smoothSet), O y hy := fun y hys =>
    if hy : y ∈ V then
      L.push hU' (γ y hy hys) (hγs y hy hys) (fun s _ => hγU y hy hys _) (hγ0 y hy hys)
        (hγ1 y hy hys) (PX.smoothVal_mem x) hys a
    else (L.nonempty _ (PX.smoothVal_mem x) y hys).some a
  have ho : ∀ y (hy : y ∈ V) (hys : y ∈ PX.smoothSet), o y hys =
      L.push hU' (γ y hy hys) (hγs y hy hys) (fun s _ => hγU y hy hys _) (hγ0 y hy hys)
        (hγ1 y hy hys) (PX.smoothVal_mem x) hys a := fun y hy hys => dif_pos hy
  refine ⟨V, o, ⟨hVo, fun δ hδ hδV x₀ x₁ h₀ h₁ hs₀ hs₁ => ?_⟩, ⟨U', hU', hVU'⟩, hxV, ?_⟩
  · have hx₀ : x₀ ∈ V := h₀ ▸ hδV 0 ⟨le_rfl, zero_le_one⟩
    have hx₁ : x₁ ∈ V := h₁ ▸ hδV 1 ⟨zero_le_one, le_rfl⟩
    rw [L.transport_eq_push hU' hδ (fun s hs => hVU' (hδV s hs)) h₀ h₁ hs₀ hs₁, ho _ hx₀,
      ho _ hx₁, L.push_trans hU' (hγs x₁ hx₁ hs₁) (hγs x₀ hx₀ hs₀) hδ (fun s _ => hγU _ _ _ _)
        (fun s _ => hγU _ _ _ _) (fun s hs => hVU' (hδV s hs)) (hγ0 _ _ _) (hγ1 _ _ _)
        (hγ0 _ _ _) (hγ1 _ _ _) h₀ h₁ (PX.smoothVal_mem x) hs₀ hs₁, Equiv.trans_apply]
  · change a = o _ _
    rw [ho _ hxV, L.push_eq_refl hU' _ _ (hγ0 _ _ _) (hγ1 _ _ _)]
    rfl

/-- **The local homeomorphism** of a continuous section: the projection restricted to
`{(y, o_y) | y ∈ U_∞}`, with inverse `y ↦ (y, o_y)` on `U_∞`. -/
def chartHomeo {U : Set X} {o : ∀ y (hy : y ∈ PX.smoothSet), O y hy}
    (h : L.IsContOn U o) :
    @OpenPartialHomeomorph L.Total PX.SmoothLevel L.topology _ :=
  let := L.topology
  { toFun := L.proj
    invFun := L.sec o
    source := L.basic U o
    target := PX.smoothVal ⁻¹' U
    map_source' := fun _ hp => hp.1
    map_target' := fun _ hy => ⟨hy, rfl⟩
    left_inv' := fun _ hp => (eq_sec_of_mem_basic hp).symm
    right_inv' := fun _ _ => rfl
    open_source := isOpen_basic h
    open_target := h.1.preimage PX.continuous_smoothVal
    continuousOn_toFun := (continuous_proj L).continuousOn
    continuousOn_invFun := continuousOn_sec h }

variable (L) in
/-- **Property (1)** (2021 Theorem 6.6.17): the projection is a local homeomorphism. -/
theorem isLocalHomeomorph_proj : @IsLocalHomeomorph _ _ L.topology _ L.proj :=
  fun p =>
    let ⟨_, _, h, _, hp⟩ := exists_isContOn L p
    ⟨chartHomeo h, hp, rfl⟩

variable (L) in
/-- **The topology of the total space is Hausdorff.** -/
theorem t2Space_topology : @T2Space _ L.topology := by
  let := L.topology
  have := PX.metrizableSpace_smoothLevel
  refine ⟨fun p q hpq => ?_⟩
  by_cases h : p.1 = q.1
  · obtain ⟨U, o, ho, -, hp⟩ := exists_isContOn L p
    obtain ⟨U', o', ho', -, hq⟩ := exists_isContOn L q
    obtain ⟨x, a⟩ := p
    obtain ⟨x', b⟩ := q
    dsimp only at h
    subst h
    have hab : a ≠ b := fun e => hpq (by rw [e])
    obtain ⟨N, hN, hNo, hxN⟩ := mem_nhds_iff.1 (ho.eventually_iff ho' hp.1 hq.1)
    refine ⟨L.basic U o ∩ L.proj ⁻¹' N, L.basic U' o' ∩ L.proj ⁻¹' N,
      (isOpen_basic ho).inter (hNo.preimage (continuous_proj L)),
      (isOpen_basic ho').inter (hNo.preimage (continuous_proj L)), ⟨hp, hxN⟩, ⟨hq, hxN⟩, ?_⟩
    rw [Set.disjoint_left]
    rintro r ⟨hr, hrN⟩ ⟨hr', -⟩
    exact hab (hp.2.trans (((hN hrN).2.2.1 (hr.2.symm.trans hr'.2)).trans hq.2.symm))
  · obtain ⟨G₁, G₂, h₁, h₂, hp, hq, hG⟩ := t2_separation h
    exact ⟨_, _, h₁.preimage (continuous_proj L), h₂.preimage (continuous_proj L), hp, hq,
      hG.preimage _⟩

/-- A point over `y` is `(y, o_y)` or `(y, o'_y)` when `o'_y` is the other element. -/
theorem eq_sec_or_eq_sec {o o' : ∀ y (hy : y ∈ PX.smoothSet), O y hy}
    (hother : ∀ y hy (c : O y hy), c ≠ o y hy → c = o' y hy) {p : L.Total}
    {y : PX.SmoothLevel} (hp : p.1 = y) : p = L.sec o y ∨ p = L.sec o' y := by
  obtain ⟨z, c⟩ := p
  dsimp only at hp
  subst hp
  by_cases hc : c = o (PX.smoothVal z) (PX.smoothVal_mem z)
  · left
    rw [hc]
    rfl
  · right
    rw [hother _ _ _ hc]
    rfl

/-! ### Property (2) -/

variable (L) in
/-- **Property (2)** (2021 Theorem 6.6.17) for the topology of the total space, when every fibre
has exactly two elements (every smooth point has small open neighbourhoods with connected
smooth part, `MPolyfold.hasConnectedSmoothNbhds`). -/
theorem hasTwoContSections_topology
    (htwo : ∀ y (hy : y ∈ PX.smoothSet), ∃ a b : O y hy, a ≠ b ∧ ∀ c, c = a ∨ c = b) :
    L.HasTwoContSections L.topology := by
  classical
  let := L.topology
  intro x
  obtain ⟨a, -, -, -⟩ := htwo _ (PX.smoothVal_mem x)
  obtain ⟨V, o, ho, -, hp⟩ := exists_isContOn L ⟨x, a⟩
  obtain ⟨U, hUo, hxU, hUV, hconn⟩ := PX.hasConnectedSmoothNbhds x V ho.1 hp.1
  obtain ⟨o', ho', hother⟩ := exists_other htwo o
  have hco' : L.IsContOn V o' := ho.of_other ho' hother
  have hUV' : PX.smoothVal ⁻¹' U ⊆ PX.smoothVal ⁻¹' V := fun y hy => hUV hy
  have hcont : ∀ {o'' : ∀ y (hy : y ∈ PX.smoothSet), O y hy}, L.IsContOn V o'' →
      Continuous fun y : PX.smoothVal ⁻¹' U => L.sec o'' (y : PX.SmoothLevel) := fun h =>
    continuousOn_iff_continuous_domRestrict.1 ((continuousOn_sec h).mono hUV')
  have hoo' : ∀ y : PX.SmoothLevel, L.sec o y ≠ L.sec o' y := fun y e =>
    ho' _ _ (eq_of_heq (Sigma.mk.inj_iff.1 e).2).symm
  refine ⟨U, hUo, hxU, fun y => L.sec o y, fun y => L.sec o' y, ⟨hcont ho, fun _ => rfl⟩,
    ⟨hcont hco', fun _ => rfl⟩, fun e => hoo' x (congrFun e ⟨x, hxU⟩), ?_⟩
  rintro σ ⟨hσc, hσ⟩
  -- the set where `σ` is the first section is open and closed
  have hev : ∀ {o'' : ∀ y (hy : y ∈ PX.smoothSet), O y hy}, L.IsContOn V o'' →
      IsOpen {y : PX.smoothVal ⁻¹' U | σ y = L.sec o'' y} := fun {o''} h =>
    isOpen_iff_mem_nhds.2 fun y hy => by
      have hmem : σ y ∈ L.basic V o'' := by
        rw [show σ y = L.sec o'' y from hy]
        exact sec_mem_basic (hUV y.2)
      filter_upwards [hσc.continuousAt.preimage_mem_nhds ((isOpen_basic h).mem_nhds hmem)]
        with z hz
      exact (eq_sec_of_mem_basic hz).trans (by rw [hσ z])
  have hA : IsClopen {y : PX.smoothVal ⁻¹' U | σ y = L.sec o y} := by
    refine ⟨isOpen_compl_iff.1 ?_, hev ho⟩
    convert hev hco' using 1
    ext y
    change ¬ (σ y = L.sec o y) ↔ σ y = L.sec o' y
    rcases eq_sec_or_eq_sec hother (hσ y) with h | h
    · rw [h]
      exact ⟨fun h' => (h' rfl).elim, fun e => (hoo' _ e).elim⟩
    · rw [h]
      exact ⟨fun _ => rfl, fun _ e => hoo' _ e.symm⟩
  have : PreconnectedSpace (PX.smoothVal ⁻¹' U) := Subtype.preconnectedSpace hconn
  rcases isClopen_iff.1 hA with h | h
  · right
    funext y
    have hy : y ∉ {y : PX.smoothVal ⁻¹' U | σ y = L.sec o y} := by rw [h]; exact fun e => e
    exact (eq_sec_or_eq_sec hother (hσ y)).resolve_left hy
  · left
    funext y
    have hy : y ∈ {y : PX.smoothVal ⁻¹' U | σ y = L.sec o y} := by rw [h]; exact mem_univ y
    exact hy

/-! ### Property (3), uniqueness and the theorem -/

variable (L) in
/-- **Property (3)** (2021 Theorem 6.6.17) for the topology of the total space: near `t₀`, a
continuous section of the pull-back stays in one set `{(y, o_y)}` of a continuous section `o`,
which is carried along the segments of `φ` by the transport. -/
theorem isPropagationContinuous_topology : L.IsPropagationContinuous L.topology := by
  let _ : TopologicalSpace L.Total := L.topology
  intro φ hφ α hα hαs t₀
  obtain ⟨U, o, ho, ⟨U', hU', hUU'⟩, hp⟩ := exists_isContOn L (α t₀).1.2
  have hφc : Continuous φ := continuousOn_univ.1 hφ.continuousOn
  have hev1 : ∀ᶠ t in 𝓝 t₀, (α t).1.2 ∈ L.basic U o :=
    (continuous_snd.comp (continuous_subtype_val.comp hα)).continuousAt
      ((isOpen_basic ho).mem_nhds hp)
  have hαφ : ∀ t : unitInterval, φ (pt1 (t : ℝ)) = PX.smoothVal (α t).1.2.1 := fun t => by
    have := (α t).2
    change φ (pt1 (((α t).1.1 : unitInterval) : ℝ)) = PX.smoothVal (α t).1.2.1 at this
    rw [hαs] at this
    exact this
  have hφt₀ : φ (pt1 (t₀ : ℝ)) ∈ U := by rw [hαφ]; exact hp.1
  filter_upwards [hev1, eventually_segPath_mem hφc ho.1 hφt₀] with t ht hseg
  have h₀ : segPath φ t₀ t (pt1 0) = PX.smoothVal (α t₀).1.2.1 := by rw [segPath_zero, hαφ]
  have h₁ : segPath φ t₀ t (pt1 1) = PX.smoothVal (α t).1.2.1 := by rw [segPath_one, hαφ]
  refine ⟨U', hU', fun s hs => hUU' (hseg s hs), h₀, h₁, ?_⟩
  have hT := ho.2 _ (isScSmoothMap_segPath hφ t₀ t) hseg h₀ h₁ (PX.smoothVal_mem _)
    (PX.smoothVal_mem _)
  rw [← L.transport_eq_push hU' (isScSmoothMap_segPath hφ t₀ t) (fun s hs => hUU' (hseg s hs)),
    hp.2, hT, ← ht.2]

/-- **Continuous local sections are the continuous sections of `IsContOn`** (the core of
uniqueness): for a topology with property (3), a continuous section `s` over an open `N ⊆ X_∞`
which agrees with a continuous section `o` at `y₀` agrees with it near `y₀` (paths of
`eventually_exists_scPath_smoothLevel`, `continuous_smoothMk_comp`, and connectedness of
`[0, 1]`). -/
theorem eventually_eq_sec_of_continuousOn {t : TopologicalSpace L.Total}
    (h3 : L.IsPropagationContinuous t) {U : Set X}
    {o : ∀ y (hy : y ∈ PX.smoothSet), O y hy} (ho : L.IsContOn U o) {N : Set PX.SmoothLevel}
    (hNo : IsOpen N) {s : PX.SmoothLevel → L.Total}
    (hs : @ContinuousOn _ _ _ t s N) (hs1 : ∀ y ∈ N, (s y).1 = y) {y₀ : PX.SmoothLevel}
    (hy₀ : y₀ ∈ N) (hy₀U : PX.smoothVal y₀ ∈ U) (hsy₀ : s y₀ = L.sec o y₀) :
    ∀ᶠ y in 𝓝 y₀, s y = L.sec o y := by
  let := t
  have hN : N ∩ PX.smoothVal ⁻¹' U ∈ 𝓝 y₀ :=
    (hNo.inter (ho.1.preimage PX.continuous_smoothVal)).mem_nhds ⟨hy₀, hy₀U⟩
  filter_upwards [eventually_exists_scPath_smoothLevel y₀ hN] with y ⟨γ, hγ, hγ0, hγ1, hγN⟩
  set γ' : unitInterval → PX.SmoothLevel := fun τ =>
    PX.smoothMk (γ (pt1 (τ : ℝ))) (mem_smoothSet_of_isScSmoothMap hγ _) with hγ'def
  have hγ'c : Continuous γ' :=
    (continuous_smoothMk_comp hγ).comp (continuous_pt1.comp continuous_subtype_val)
  have hγ'N : ∀ τ, γ' τ ∈ N ∩ PX.smoothVal ⁻¹' U := fun τ => hγN _
  let α : unitInterval → L.Pullback γ := fun τ =>
    ⟨(τ, s (γ' τ)), by
      change γ (pt1 (τ : ℝ)) = PX.smoothVal (s (γ' τ)).1
      rw [hs1 _ (hγ'N τ).1]
      rfl⟩
  have hαc : Continuous α :=
    (continuous_id.prodMk (hs.comp_continuous hγ'c fun τ => (hγ'N τ).1)).subtype_mk _
  have h3' := h3 γ hγ α hαc fun _ => rfl
  have hQiff : ∀ τ, s (γ' τ) = L.sec o (γ' τ) ↔ (α τ).1.2.2 =
      o (PX.smoothVal (α τ).1.2.1) (PX.smoothVal_mem _) := fun τ =>
    eq_sec_iff (hs1 _ (hγ'N τ).1)
  have hQ : ∀ τ₀, ∀ᶠ τ in 𝓝 τ₀,
      (s (γ' τ) = L.sec o (γ' τ) ↔ s (γ' τ₀) = L.sec o (γ' τ₀)) := by
    intro τ₀
    filter_upwards [h3' τ₀] with τ ⟨U'', hU'', hseg, h₀, h₁, hpush⟩
    have hsegU : ∀ r ∈ Icc (0 : ℝ) 1, segPath γ τ₀ τ (pt1 r) ∈ U := fun r _ => (hγN _).2
    have hT := ho.2 _ (isScSmoothMap_segPath hγ τ₀ τ) hsegU h₀ h₁ (PX.smoothVal_mem _)
      (PX.smoothVal_mem _)
    have hP : L.transport _ (isScSmoothMap_segPath hγ τ₀ τ) h₀ h₁ (PX.smoothVal_mem _)
        (PX.smoothVal_mem _) (α τ₀).1.2.2 = (α τ).1.2.2 := by
      rw [L.transport_eq_push hU'' _ hseg]
      exact hpush
    rw [hQiff τ, hQiff τ₀, ← hP, ← hT]
    exact (L.transport _ _ h₀ h₁ _ _).apply_eq_iff_eq
  have hopen : IsOpen {τ | s (γ' τ) = L.sec o (γ' τ)} :=
    isOpen_iff_mem_nhds.2 fun τ₀ hτ₀ => (hQ τ₀).mono fun τ h => h.2 hτ₀
  have hclosed : IsOpen {τ | s (γ' τ) = L.sec o (γ' τ)}ᶜ :=
    isOpen_iff_mem_nhds.2 fun τ₀ hτ₀ => (hQ τ₀).mono fun τ h hτ => hτ₀ (h.1 hτ)
  have hγ'0 : γ' 0 = y₀ := MPolyfold.smoothMk_eq hγ0
  have hγ'1 : γ' 1 = y := MPolyfold.smoothMk_eq hγ1
  have h0 : (0 : unitInterval) ∈ {τ | s (γ' τ) = L.sec o (γ' τ)} := by
    change s (γ' 0) = L.sec o (γ' 0)
    rw [hγ'0]; exact hsy₀
  rcases isClopen_iff.1 ⟨isOpen_compl_iff.1 hclosed, hopen⟩ with h | h
  · exact absurd (h ▸ h0) (notMem_empty _)
  · have h1 : (1 : unitInterval) ∈ {τ | s (γ' τ) = L.sec o (γ' τ)} := by rw [h]; exact mem_univ _
    change s (γ' 1) = L.sec o (γ' 1) at h1
    rwa [hγ'1] at h1

/-- **Uniqueness in 2021 Theorem 6.6.17**: a topology on the total space with properties (1)
and (3) is `L.topology` (Hausdorffness and property (2) are not needed). -/
theorem eq_topology_of {t : TopologicalSpace L.Total}
    (h1 : @IsLocalHomeomorph _ _ t _ L.proj) (h3 : L.IsPropagationContinuous t) :
    t = L.topology := by
  have hsec' : ∀ (e : @OpenPartialHomeomorph _ _ t _), L.proj = e →
      ∀ z ∈ e.target, (e.symm z).1 = z := fun e he z hz =>
    (congrFun he (e.symm z)).trans (e.right_inv hz)
  refine TopologicalSpace.ext (funext fun G => propext ⟨fun hG => ?_, fun hG => ?_⟩)
  · -- `t`-open sets are open
    intro U o ho
    refine isOpen_iff_mem_nhds.2 fun y hy => ?_
    obtain ⟨e, hpe, he⟩ := h1 (L.sec o y)
    have hey : e (L.sec o y) = y := (congrFun he _).symm
    have hyt : y ∈ e.target := hey ▸ e.map_source hpe
    have hsy : e.symm y = L.sec o y := by
      conv_lhs => rw [← hey]
      exact e.left_inv hpe
    have hev := eventually_eq_sec_of_continuousOn h3 ho e.open_target
      e.continuousOn_symm (hsec' e he) hyt hy.1 hsy
    have hev2 : ∀ᶠ z in 𝓝 y, e.symm z ∈ G :=
      (e.continuousOn_symm.continuousAt (e.open_target.mem_nhds hyt))
        (@IsOpen.mem_nhds _ t _ _ hG (hsy ▸ hy.2))
    filter_upwards [hev, hev2, (ho.1.preimage PX.continuous_smoothVal).mem_nhds hy.1]
      with z hz1 hz2 hz3
    exact ⟨hz3, hz1 ▸ hz2⟩
  · -- open sets are `t`-open
    let := t
    refine isOpen_iff_mem_nhds.2 fun p hp => ?_
    obtain ⟨e, hpe, he⟩ := h1 p
    obtain ⟨U, o, ho, -, hpo⟩ := exists_isContOn L p
    have hep : e p = p.1 := (congrFun he p).symm
    have hp1 : p.1 ∈ e.target := hep ▸ e.map_source hpe
    have hsp : e.symm p.1 = L.sec o p.1 := by
      conv_lhs => rw [← hep]
      exact (e.left_inv hpe).trans (eq_sec_of_mem_basic hpo)
    have hev := eventually_eq_sec_of_continuousOn h3 ho e.open_target
      e.continuousOn_symm (hsec' e he) hp1 hpo.1 hsp
    have hmem : p.1 ∈ {y : PX.SmoothLevel | PX.smoothVal y ∈ U ∧ L.sec o y ∈ G} :=
      ⟨hpo.1, (eq_sec_of_mem_basic hpo) ▸ hp⟩
    obtain ⟨M, hMsub, hMo, hpM⟩ := mem_nhds_iff.1
      ((hev.and ((hG U o ho).mem_nhds hmem)).and (e.open_target.mem_nhds hp1))
    refine mem_nhds_iff.2 ⟨e.source ∩ e ⁻¹' M, fun q ⟨hq, hqM⟩ => ?_,
      e.isOpen_inter_preimage hMo, hpe, show e p ∈ M by rw [hep]; exact hpM⟩
    have h := hMsub hqM
    rw [← e.left_inv hq, h.1.1]
    exact h.1.2.2

variable (L) in
/-- **2021 Theorem 6.6.17 without property (2)**: there is exactly one Hausdorff topology on the
total space with properties (1) and (3) (by `eq_topology_of`, even exactly one with (1) and
(3)). -/
theorem existsUnique_topology :
    ∃! t : TopologicalSpace L.Total, @T2Space _ t ∧ @IsLocalHomeomorph _ _ t _ L.proj ∧
      L.IsPropagationContinuous t :=
  ⟨L.topology, ⟨t2Space_topology L, isLocalHomeomorph_proj L, isPropagationContinuous_topology L⟩,
    fun _ ht => eq_topology_of ht.2.1 ht.2.2⟩

variable (L) in
/-- **2021 Theorem 6.6.17**, p. 275, for local transport data `L` on a family with two-element
fibres: there is exactly one topology on the total space which is Hausdorff and has properties
(1), (2) and (3). -/
theorem existsUnique_isOrientationTopology
    (htwo : ∀ y (hy : y ∈ PX.smoothSet), ∃ a b : O y hy, a ≠ b ∧ ∀ c, c = a ∨ c = b) :
    ∃! t : TopologicalSpace L.Total, L.IsOrientationTopology t :=
  ⟨L.topology,
    ⟨t2Space_topology L, isLocalHomeomorph_proj L, hasTwoContSections_topology L htwo,
      isPropagationContinuous_topology L⟩,
    fun _ ht => eq_topology_of ht.isLocalHomeomorph ht.propagation⟩

/-! ### Locality of continuity, and continuous global sections -/

/-- **Induction along the dyadic pieces of an sc-smooth path**: let `Q` be a property of paths
inherited by both halves, and `R` a property which a path with `Q` has when its halves have it.
If every point `γ(t)` of a path with `Q` has an open neighbourhood `V` such that every path
with `Q` whose `[0, 1]` lies in `V` has `R`, then every sc-smooth path with `Q` has `R`. -/
theorem scPath_induction (Q R : ((Fin 1 → ℝ) → X) → Prop)
    (hQl : ∀ γ, (rnPolyfold 1).IsScSmoothMap PX γ → Q γ → Q (leftHalf γ))
    (hQr : ∀ γ, (rnPolyfold 1).IsScSmoothMap PX γ → Q γ → Q (rightHalf γ))
    (hR : ∀ γ, (rnPolyfold 1).IsScSmoothMap PX γ → Q γ → R (leftHalf γ) → R (rightHalf γ) →
      R γ)
    (hloc : ∀ γ, (rnPolyfold 1).IsScSmoothMap PX γ → Q γ → ∀ t ∈ Icc (0 : ℝ) 1,
      ∃ V : Set X, IsOpen V ∧ γ (pt1 t) ∈ V ∧ ∀ γ', (rnPolyfold 1).IsScSmoothMap PX γ' →
        Q γ' → (∀ s ∈ Icc (0 : ℝ) 1, γ' (pt1 s) ∈ V) → R γ')
    {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hQ : Q γ) : R γ := by
  let G : Set X → Prop := fun V => ∀ γ', (rnPolyfold 1).IsScSmoothMap PX γ' → Q γ' →
    (∀ s ∈ Icc (0 : ℝ) 1, γ' (pt1 s) ∈ V) → R γ'
  let Leb : ℝ → ((Fin 1 → ℝ) → X) → Prop := fun δ γ' => ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    b - a < δ → ∃ V, G V ∧ ∀ t ∈ Icc a b, γ' (pt1 t) ∈ V
  have key : ∀ N : ℕ, ∀ δ : ℝ, ∀ γ', (rnPolyfold 1).IsScSmoothMap PX γ' → Q γ' → Leb δ γ' →
      1 < 2 ^ N * δ → R γ' := by
    intro N
    induction N with
    | zero =>
      intro δ γ' hγ' hQ' hL hN
      rw [pow_zero, one_mul] at hN
      obtain ⟨V, hV, hγV⟩ := hL 0 1 le_rfl zero_le_one le_rfl (by linarith)
      exact hV γ' hγ' hQ' hγV
    | succ N ih =>
      intro δ γ' hγ' hQ' hL hN
      have hN' : 1 < 2 ^ N * (2 * δ) := by rw [pow_succ, mul_assoc] at hN; exact hN
      refine hR γ' hγ' hQ' (ih (2 * δ) _ (isScSmoothMap_leftHalf hγ') (hQl γ' hγ' hQ') ?_ hN')
        (ih (2 * δ) _ (isScSmoothMap_rightHalf hγ') (hQr γ' hγ' hQ') ?_ hN')
      · intro a b ha hab hb hba
        obtain ⟨V, hV, hγV⟩ := hL (a / 2) (b / 2) (by linarith) (by linarith) (by linarith)
          (by linarith)
        exact ⟨V, hV, fun t ht => hγV (t / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
      · intro a b ha hab hb hba
        obtain ⟨V, hV, hγV⟩ := hL ((1 + a) / 2) ((1 + b) / 2) (by linarith) (by linarith)
          (by linarith) (by linarith)
        exact ⟨V, hV, fun t ht => hγV ((1 + t) / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hc : Continuous fun t : ℝ => γ (pt1 t) :=
    (continuousOn_univ.1 hγ.continuousOn).comp (continuous_pi fun _ => continuous_id)
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    (c := fun V : {V : Set X // IsOpen V ∧ G V} => (fun t : ℝ => γ (pt1 t)) ⁻¹' V.1)
    isCompact_Icc (fun V => V.2.1.preimage hc) (fun t ht => by
      obtain ⟨V, hVo, htV, hV⟩ := hloc γ hγ hQ t ht
      exact mem_iUnion.2 ⟨⟨V, hVo, hV⟩, htV⟩)
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (1 / δ) (one_lt_two : (1 : ℝ) < 2)
  refine key N δ γ hγ hQ (fun a b ha hab hb hba => ?_) ((div_lt_iff₀ hδ).1 hN)
  obtain ⟨i, hsub⟩ := hball a ⟨ha, hab.trans hb⟩
  refine ⟨i.1, i.2.2, fun t ht => @hsub t ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [ht.1, ht.2]

/-- **Continuity of a section is local**: a section which is a continuous section over an open
neighbourhood of every smooth point of an open `U` is one over `U`.  The transport along a path
in `U` is the composite of the transports along small dyadic pieces (`scPath_induction`,
`transport_halves`). -/
theorem isContOn_of_local {U : Set X} (hU : IsOpen U)
    {o : ∀ y (hy : y ∈ PX.smoothSet), O y hy}
    (h : ∀ x ∈ U, x ∈ PX.smoothSet → ∃ V : Set X, x ∈ V ∧ L.IsContOn V o) :
    L.IsContOn U o := by
  let R : ((Fin 1 → ℝ) → X) → Prop := fun γ => ∀ (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet), L.transport γ hγ h₀ h₁ hs₀ hs₁ (o x₀ hs₀) = o x₁ hs₁
  have key : ∀ γ, (rnPolyfold 1).IsScSmoothMap PX γ → (∀ q, γ q ∈ U) → R γ := by
    intro γ hγ hQ
    refine scPath_induction (fun γ => ∀ q, γ q ∈ U) R (fun γ _ hQ q => hQ _)
      (fun γ _ hQ q => hQ _) ?_ ?_ hγ hQ
    · intro γ _ _ hl hr hγ x₀ x₁ h₀ h₁ hs₀ hs₁
      have hsm := mem_smoothSet_of_isScSmoothMap hγ (pt1 (1 / 2))
      rw [L.transport_halves hγ h₀ h₁ rfl hs₀ hs₁ hsm, Equiv.trans_apply,
        hl (isScSmoothMap_leftHalf hγ) (leftHalf_zero.trans h₀) (leftHalf_one.trans rfl) hs₀ hsm,
        hr (isScSmoothMap_rightHalf hγ) (rightHalf_zero.trans rfl) (rightHalf_one.trans h₁) hsm
          hs₁]
    · intro γ hγ hQ t _
      obtain ⟨V, hxV, hV⟩ := h _ (hQ _) (mem_smoothSet_of_isScSmoothMap hγ (pt1 t))
      exact ⟨V, hV.1, hxV, fun γ' _ _ hγ'V hγ'' x₀ x₁ h₀ h₁ hs₀ hs₁ =>
        hV.2 γ' hγ'' hγ'V h₀ h₁ hs₀ hs₁⟩
  refine ⟨hU, fun γ hγ hγU x₀ x₁ h₀ h₁ hs₀ hs₁ => ?_⟩
  rw [← L.transport_reparam hγ Real.smoothTransition.contDiff Real.smoothTransition.zero
    Real.smoothTransition.one h₀ h₁ hs₀ hs₁]
  exact key (fun s => γ (pt1 (Real.smoothTransition (s 0))))
    (isScSmoothMap_reparam hγ Real.smoothTransition.contDiff)
    (fun q => hγU _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩) _ _ _ _ _

/-- The set where a section `o` with `y ↦ (y, o_y)` continuous agrees with a continuous section
`o''` over `V ⊇ U` is open in `U ∩ X_∞`. -/
theorem isOpen_setOf_sec_eq {o o'' : ∀ y (hy : y ∈ PX.smoothSet), O y hy}
    (ho : @Continuous _ _ _ L.topology (L.sec o)) {U V : Set X} (hUV : U ⊆ V)
    (h : L.IsContOn V o'') :
    IsOpen {y : PX.smoothVal ⁻¹' U | L.sec o (y : PX.SmoothLevel) = L.sec o'' y} := by
  let := L.topology
  have hσc : Continuous fun y : PX.smoothVal ⁻¹' U => L.sec o (y : PX.SmoothLevel) :=
    ho.comp continuous_subtype_val
  refine isOpen_iff_mem_nhds.2 fun y hy => ?_
  have hmem : L.sec o (y : PX.SmoothLevel) ∈ L.basic V o'' := by
    rw [show L.sec o (y : PX.SmoothLevel) = L.sec o'' y from hy]
    exact sec_mem_basic (hUV y.2)
  filter_upwards [hσc.continuousAt.preimage_mem_nhds ((isOpen_basic h).mem_nhds hmem)]
    with z hz
  exact eq_sec_of_mem_basic hz

/-- A continuous section over all of `X` gives a continuous map `y ↦ (y, o_y)`. -/
theorem IsContOn.continuous_sec {o : ∀ y (hy : y ∈ PX.smoothSet), O y hy}
    (h : L.IsContOn univ o) : @Continuous _ _ _ L.topology (L.sec o) := by
  let := L.topology
  have h' := continuousOn_sec h
  rw [preimage_univ] at h'
  exact continuousOn_univ.1 h'

/-- **A section `o` with `y ↦ (y, o_y)` continuous for `L.topology` is a continuous section over
all of `X`**, when every fibre has exactly two elements: near a smooth `x` there is a continuous
section `o₁` with `o₁(x) = o(x)`; on a neighbourhood with connected smooth part the set where
`o = o₁` is open and closed; then `isContOn_of_local`. -/
theorem isContOn_univ_of_continuous_sec
    (htwo : ∀ y (hy : y ∈ PX.smoothSet), ∃ a b : O y hy, a ≠ b ∧ ∀ c, c = a ∨ c = b)
    {o : ∀ y (hy : y ∈ PX.smoothSet), O y hy}
    (ho : @Continuous _ _ _ L.topology (L.sec o)) : L.IsContOn univ o := by
  classical
  refine isContOn_of_local isOpen_univ fun x _ hxs => ?_
  set xs : PX.SmoothLevel := ⟨x, hxs⟩
  obtain ⟨V, o₁, ho₁, -, hp⟩ := exists_isContOn L ⟨xs, o x hxs⟩
  obtain ⟨U, hUo, hxU, hUV, hconn⟩ := PX.hasConnectedSmoothNbhds xs V ho₁.1 hp.1
  obtain ⟨o₁', ho₁', hother⟩ := exists_other htwo o₁
  have hco' : L.IsContOn V o₁' := ho₁.of_other ho₁' hother
  have hoo' : ∀ y : PX.SmoothLevel, L.sec o₁ y ≠ L.sec o₁' y := fun y e =>
    ho₁' _ _ (eq_of_heq (Sigma.mk.inj_iff.1 e).2).symm
  set S := {y : PX.smoothVal ⁻¹' U | L.sec o (y : PX.SmoothLevel) = L.sec o₁ y}
  have hA : IsClopen S := by
    refine ⟨isOpen_compl_iff.1 ?_, isOpen_setOf_sec_eq ho hUV ho₁⟩
    convert isOpen_setOf_sec_eq ho hUV hco' using 1
    ext y
    change ¬ (L.sec o (y : PX.SmoothLevel) = L.sec o₁ y) ↔
      L.sec o (y : PX.SmoothLevel) = L.sec o₁' y
    rcases eq_sec_or_eq_sec hother (p := L.sec o (y : PX.SmoothLevel)) rfl with h | h
    · rw [h]
      exact ⟨fun h' => (h' rfl).elim, fun e => (hoo' _ e).elim⟩
    · rw [h]
      exact ⟨fun _ => rfl, fun _ e => hoo' _ e.symm⟩
  have : PreconnectedSpace (PX.smoothVal ⁻¹' U) := Subtype.preconnectedSpace hconn
  have hxS : (⟨xs, hxU⟩ : PX.smoothVal ⁻¹' U) ∈ S := by
    change L.sec o xs = L.sec o₁ xs
    exact eq_sec_of_mem_basic hp
  have hS : S = univ := (isClopen_iff.1 hA).resolve_left (Set.nonempty_iff_ne_empty.1 ⟨_, hxS⟩)
  refine ⟨U, hxU, (ho₁.mono hUo hUV).congr fun y hyU hys => ?_⟩
  have hy : (⟨⟨y, hys⟩, hyU⟩ : PX.smoothVal ⁻¹' U) ∈ S := hS ▸ mem_univ _
  exact (eq_of_heq (Sigma.mk.inj_iff.1 hy).2).symm

variable (L) in
/-- **Continuous global sections are the sections carried along by the transport**: when every
fibre has exactly two elements, `y ↦ (y, o_y)` is continuous for `L.topology` iff the transport
along every sc-smooth path takes `o` at its start to `o` at its end. -/
theorem isContOn_univ_iff_continuous_sec
    (htwo : ∀ y (hy : y ∈ PX.smoothSet), ∃ a b : O y hy, a ≠ b ∧ ∀ c, c = a ∨ c = b)
    {o : ∀ y (hy : y ∈ PX.smoothSet), O y hy} :
    @Continuous _ _ _ L.topology (L.sec o) ↔ L.IsContOn univ o :=
  ⟨isContOn_univ_of_continuous_sec htwo, IsContOn.continuous_sec⟩

end LocalTransport

end Polyfold
