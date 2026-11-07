import Polyfold
/-! Blind formalization of V6_34 (the text's §6.5, Lemma 6.30, p. 222).

Text: the solution set `S` of `F = 0` near `(t, φ(t), 0)` is a smooth manifold with boundary
with corners containing `{(t, φ(t), 0)}`; by (P) the projection `π : S → [0, 1]` is a
submersion, and its fibres `S_t` are manifolds with boundary with corners.
`L_t = T_{(φ(t),0)}S_t = ker F_t'(φ(t), 0)`, and `L` is a smooth vector bundle over `[0, 1]`.

Choices:
- Setting, context and encodings as in `RoundTrip/Blind/V6_33.lean` (Lemma 6.29; prelude of
  `RoundTrip/Blind/V6_32.lean`), whose definitions `Ft`, `Ffam` (`F`) and `PropP` ((P)) are
  copied.  Hypotheses: the context of Lemma 6.29 (with its added tameness and `IsSection P f`) and
  sc⁺-sections `s₁, …, s_k` over `[0, 1] × U` with (P), as the lemma's "by (P)" requires.
- `[0, 1]` is replaced by `ℝ¹` (as in V6_33): `S` lives in `ℝ¹ × (ℝᵏ × X)` (factors in the
  project's order; the text's `(t, φ(t), 0)` is `(t, (0, φ(t)))`).  DOUBT: the boundary of
  `[0, 1]` at `t ∈ {0, 1}` is lost; near `t = 0, 1` the set `S` is a two-sided piece of the
  solution set in `ℝ¹ × ℝᵏ × X` (true by openness of general position, but not the text's
  `S ⊆ [0, 1] × X × ℝᵏ`).
- "the solution set near `(t, φ(t), 0)`": `S = N ∩ F⁻¹(0)` for some open `N` containing the whole
  curve `{(t, (0, φ(t))) | t ∈ [0, 1]}` (B asserts `∃ N`); `F = 0` is `IsZeroAt`.
- "smooth manifold with boundary with corners": a smooth finite-dimensional submanifold
  (Definition 4.13, `IsSmoothSubmanifold`) whose induced structure (`subPolyfold`, for some proof
  of `IsSubMPolyfold`) is a manifold with boundary with corners (`IsManifoldWithCornersLoc`, of
  locally constant dimension).  Same reading for the fibres `S_t = {w | (t, w) ∈ S} ⊆ ℝᵏ × X`,
  `t ∈ [0, 1]`.
- "`π : S → [0, 1]` is a submersion": `π(t, λ, y) = t` is sc-smooth on the M-polyfold `S`, and
  its tangent map (`MPolyfold.tangentMap`) maps the tangent space at every point `q` onto the
  tangent space of `ℝ¹` at `π(q)` (fibres of `tangentProj`).
- `T_{(φ(t),0)}S_t` is read in the product chart of `π*P` built from a chart point `p` at `φ(t)`
  (`PullbackChartData.ofProd p.c 0`, as in `RoundTrip/Blind/V6_37.lean`), as the linear span of
  the tangent cone (Mathlib's `tangentConeAt`, in `ℝᵏ × E` on level `0`) of the chart image of
  `S_t` at `(0, φ(φ(t)))`; the span, so that corners are covered.  `L_t = ker F_t'(φ(t), 0)` is
  the kernel of the project's `linAt` of `F_t` in the product chart at `(0, z)`, included into
  `ℝᵏ × E` (`kerProd`).  B quantifies over all chart points (both sides are chart-dependent the
  same way) and over the junk value `q₀`.
- "`L` is a smooth vector bundle over `[0, 1]`": in every chart point `p` at `φ(t₀)`, there are an
  open `J ∋ t₀`, the lifts `z_t` of `φ(φ(t))` for `t ∈ J ∩ [0, 1]`, and `C^∞` maps
  `e₁, …, e_d : J → ℝᵏ × E` (level `0`) forming a basis of `L_t` (read at `z_t`) for every
  `t ∈ J ∩ [0, 1]`: smooth local frames.  Smoothness into the higher levels is not asked.
- Technical hypotheses as in V6_33, plus paracompactness of all subsets of `ℝⁿ × X` and of
  `ℝ¹ × (ℝⁿ × X)` (instance hypotheses; true, M-polyfolds are metrizable).
- Nothing else looks doubtful to me.
-/
namespace RoundTrip.V6_34
open Polyfold

/-- `[0, 1] ⊆ ℝ¹`. -/
def I1 : Set (Fin 1 → ℝ) := Set.Icc 0 1

section
variable {X : Type} {Y : Type} {P : Y → X}

/-- The slice `s(·, t)` of a section of `π*P → ℝⁿ × X` is a section of `P`. -/
theorem isSection_slice {n : ℕ}
    (s : (Fin n → ℝ) × X → ↥(pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)))
    (hs : IsSection (pullbackProj P Prod.snd) s) (t : Fin n → ℝ) :
    IsSection P (pullbackSlice s t) := by
  intro y
  have h1 : P (s (t, y)).1.2 = (s (t, y)).1.1.2 := (s (t, y)).2
  have h2 : (s (t, y)).1.1 = (t, y) := hs (t, y)
  change P (s (t, y)).1.2 = y
  rw [h1, h2]

/-- `f − g` is a section if `f` and `g` are. -/
theorem isSection_sectionDiff [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    {f g : X → Y} (hf : IsSection P f) (hg : IsSection P g) :
    IsSection P (sectionDiff P f g) := by
  intro y
  have hg' : P (sectionSmul P (fun _ => (-1 : ℝ)) g y) = y := by
    unfold sectionSmul
    rw [dif_pos (hg y)]
    exact ((-1 : ℝ) • (⟨g y, hg y⟩ : ↥(P ⁻¹' {y}))).2
  unfold sectionDiff sectionAdd
  rw [dif_pos (And.intro (hf y) hg')]
  exact ((⟨f y, hf y⟩ : ↥(P ⁻¹' {y})) + ⟨_, hg'⟩).2

end

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace ↥(pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  [∀ W : Set ((Fin 1 → ℝ) × X), ParacompactSpace ↥W]
  [∀ W : Set ((Fin 1 → ℝ) × X), ParacompactSpace
    ↥(pullbackSpace (pullbackProj P (Prod.snd : (Fin 1 → ℝ) × X → X))
      (Subtype.val : W → (Fin 1 → ℝ) × X))]
  [∀ n : ℕ, ParacompactSpace ((Fin 1 → ℝ) × ((Fin n → ℝ) × X))]
  [∀ n : ℕ, ParacompactSpace ↥(pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin 1 → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]

/-- A (set-theoretic) section candidate of `π*P → ℝ¹ × X`. -/
abbrev Sec1 (P : Y → X) : Type :=
  (Fin 1 → ℝ) × X → ↥(pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))

/-- `s` is a section of `π*P` which is an sc⁺-section over the open set `W ⊆ ℝ¹ × X`. -/
def IsScPlusOn (Bd : StrongBundle PX P)
    (hπ : ((rnPolyfold 1).prod PX).IsScSmoothMap PX Prod.snd) (W : Set ((Fin 1 → ℝ) × X))
    (s : Sec1 P) : Prop :=
  ∃ (hW : IsOpen W) (hne : Nonempty ↥W) (hs : IsSection (pullbackProj P Prod.snd) s),
    letI := hne
    ((Bd.pullback hπ).restrictOpen hW).IsScPlusSection
      (restrictSection (pullbackProj P Prod.snd) W s hs)

/-- `s` is an sc⁺-section over (an open neighbourhood of) `A ⊆ ℝ¹ × X`. -/
def IsScPlusNear (Bd : StrongBundle PX P)
    (hπ : ((rnPolyfold 1).prod PX).IsScSmoothMap PX Prod.snd) (A : Set ((Fin 1 → ℝ) × X))
    (s : Sec1 P) : Prop :=
  ∃ W, A ⊆ W ∧ IsScPlusOn Bd hπ W s

/-- `φ : ℝ¹ → X` is an sc-smooth path on `[0, 1]`. -/
def IsScPathOn (PX : MPolyfold X) (φ : (Fin 1 → ℝ) → X) : Prop :=
  ∃ V, I1 ⊆ V ∧ (rnPolyfold 1).IsScSmoothOn PX φ V

/-- (1) `U` is sc-smoothly contractible. -/
def IsScContractible (PX : MPolyfold X) (U : Set X) : Prop :=
  ∃ (H : (Fin 1 → ℝ) × X → X) (y₀ : X),
    (∃ W, I1 ×ˢ U ⊆ W ∧ ((rnPolyfold 1).prod PX).IsScSmoothOn PX H W) ∧
    (∀ t ∈ I1, ∀ y ∈ U, H (t, y) ∈ U) ∧ (∀ y ∈ U, H (pt1 1, y) = y) ∧
    (∀ y ∈ U, H (pt1 0, y) = y₀)

/-- (3) along every sc-smooth path in `U` there is an sc⁺-section `s` with
`s(φ(t), t) = f(φ(t))`. -/
def HasPathSections (Bd : StrongBundle PX P)
    (hπ : ((rnPolyfold 1).prod PX).IsScSmoothMap PX Prod.snd) (f : X → Y) (U : Set X) : Prop :=
  ∀ φ : (Fin 1 → ℝ) → X, IsScPathOn PX φ → (∀ t ∈ I1, φ t ∈ U) →
    ∃ s : Sec1 P, IsScPlusNear Bd hπ (I1 ×ˢ U) s ∧ ∀ t ∈ I1, pullbackSlice s t (φ t) = f (φ t)

/-- (4) sc⁺-sections over `[0, 1] × U` through every smooth fibre point over `[0, 1] × U_∞`. -/
def HasPointSections (Bd : StrongBundle PX P)
    (hπ : ((rnPolyfold 1).prod PX).IsScSmoothMap PX Prod.snd) (U : Set X) : Prop :=
  ∀ t₀ ∈ I1, ∀ y₀ ∈ U ∩ PX.smoothSet, ∀ e₀ ∈ Bd.toMPolyfold0.smoothSet, P e₀ = y₀ →
    ∃ q : Sec1 P, IsScPlusNear Bd hπ (I1 ×ˢ U) q ∧ pullbackSlice q t₀ y₀ = e₀

/-- The properties (1)–(4) of Proposition 6.28 for the open neighbourhood `U` of `x`. -/
def IsNbhd628 (Bd : StrongBundle PX P)
    (hπ : ((rnPolyfold 1).prod PX).IsScSmoothMap PX Prod.snd) (f : X → Y) (x : X)
    (U : Set X) : Prop :=
  IsOpen U ∧ x ∈ U ∧ IsScContractible PX U ∧
    IsCompact {y | y ∈ closure U ∧ IsZeroAt P f y} ∧
    HasPathSections Bd hπ f U ∧ HasPointSections Bd hπ U

/-- `F_t(λ, y) = f(y) − s(y, t) + Σ λᵢ sᵢ(y, t)`, a section of `π*P → ℝᵏ × X`. -/
noncomputable def Ft {k : ℕ} (f : X → Y) (hf : IsSection P f) (s : Sec1 P)
    (hs : IsSection (pullbackProj P Prod.snd) s) (σ : Fin k → Sec1 P)
    (hσ : ∀ i, IsSection (pullbackProj P Prod.snd) (σ i)) (t : Fin 1 → ℝ) :
    (Fin k → ℝ) × X → ↥(pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X)) :=
  paramSection (sectionDiff P f (pullbackSlice s t))
    (isSection_sectionDiff hf (isSection_slice s hs t))
    (fun i => pullbackSlice (σ i) t) (fun i => isSection_slice (σ i) (hσ i) t)

/-- `F(t, λ, y) = F_t(λ, y)`, a section of the pull-back of `π*P → ℝᵏ × X` to
`ℝ¹ × (ℝᵏ × X)` along the projection. -/
noncomputable def Ffam {k : ℕ} (f : X → Y) (hf : IsSection P f) (s : Sec1 P)
    (hs : IsSection (pullbackProj P Prod.snd) s) (σ : Fin k → Sec1 P)
    (hσ : ∀ i, IsSection (pullbackProj P Prod.snd) (σ i)) :
    (Fin 1 → ℝ) × ((Fin k → ℝ) × X) →
      ↥(pullbackSpace (pullbackProj P (Prod.snd : (Fin k → ℝ) × X → X))
        (Prod.snd : (Fin 1 → ℝ) × ((Fin k → ℝ) × X) → (Fin k → ℝ) × X)) :=
  fun q => ⟨(q, Ft f hf s hs σ hσ q.1 q.2), rfl⟩

/-- Property (P): for every `t ∈ [0, 1]`, `F_t` is in general position at `(0, φ(t))`. -/
def PropP (Bd : StrongBundle PX P)
    (hπ : ∀ n : ℕ, ((rnPolyfold n).prod PX).IsScSmoothMap PX Prod.snd)
    (f : X → Y) (hf : IsSection P f) (s : Sec1 P) (hs : IsSection (pullbackProj P Prod.snd) s)
    {k : ℕ} (σ : Fin k → Sec1 P) (hσ : ∀ i, IsSection (pullbackProj P Prod.snd) (σ i))
    (φ : (Fin 1 → ℝ) → X) : Prop :=
  ∀ t ∈ I1, (Bd.pullback (hπ k)).IsGeneralPositionGerm (Ft f hf s hs σ hσ t) (0, φ t)

/-- The product chart `(λ, y) ↦ (λ, φ(y))` of `π*P → ℝᵏ × X` built from the strong bundle chart
`c` (the project's `PullbackChartData.ofProd` centred at `r₀ = 0`; `q₀` is the junk value of its
inverse). -/
noncomputable abbrev prodChart (c : StrongBundleChart PX P) (k : ℕ)
    (q₀ : ↥(pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))) :
    StrongBundleChart ((rnPolyfold k).prod PX) (pullbackProj P Prod.snd) :=
  (PullbackChartData.ofProd (n := k) c 0).toChart q₀

/-- The level-`1` point `(0, z)` of the product chart. -/
def zProd (c : StrongBundleChart PX P) (k : ℕ)
    (q₀ : ↥(pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))) (z : c.φ.model.E.lvl 1) :
    (prodChart c k q₀).φ.model.E.lvl 1 :=
  show (Fin k → ℝ) × c.φ.model.E.lvl 1 from ((0 : Fin k → ℝ), z)

/-- The tangent space `T_{(0,z)}(ℝᵏ × O)` of the product chart. -/
noncomputable abbrev TProd (c : StrongBundleChart PX P) (k : ℕ)
    (q₀ : ↥(pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))) (z : c.φ.model.E.lvl 1) :
    Submodule ℝ ((prodChart c k q₀).φ.model.E.lvl 0) :=
  rangeS (scDeriv (prodChart c k q₀).U (StrongRetr.r (prodChart c k q₀).R) (zProd c k q₀ z))

/-- `ker G'(0, z) ⊆ ℝᵏ × E` for a section `G` of `π*P`, read in the product chart (for
`G = F_t` and `z` over `φ(t)` this is `L_t = ker F_t'(φ(t), 0)`). -/
noncomputable def kerProd (c : StrongBundleChart PX P) (k : ℕ)
    (q₀ : ↥(pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))) (z : c.φ.model.E.lvl 1)
    (G : (Fin k → ℝ) × X → ↥(pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))) :
    Submodule ℝ ((prodChart c k q₀).φ.model.E.lvl 0) :=
  (LinearMap.ker ((linAt (prodChart c k q₀).U (prodChart c k q₀).R
    ((prodChart c k q₀).principal G) (zProd c k q₀ z) :
      ↥(TProd c k q₀ z) →L[ℝ] (prodChart c k q₀).F.lvl 0) :
        ↥(TProd c k q₀ z) →ₗ[ℝ] (prodChart c k q₀).F.lvl 0)).map (TProd c k q₀ z).subtype

end

/-- Lemma 6.30: near the curve `t ↦ (t, φ(t), 0)` the solution set `S` of `F = 0` is a smooth
manifold with boundary with corners, `π : S → [0, 1]` is a submersion, the fibres `S_t` are
manifolds with boundary with corners, `L_t = T_{(φ(t),0)}S_t = ker F_t'(φ(t), 0)`, and `L` is a
smooth vector bundle over `[0, 1]`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace ↥(pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    [∀ W : Set ((Fin 1 → ℝ) × X), ParacompactSpace ↥W]
    [∀ W : Set ((Fin 1 → ℝ) × X), ParacompactSpace
      ↥(pullbackSpace (pullbackProj P (Prod.snd : (Fin 1 → ℝ) × X → X))
        (Subtype.val : W → (Fin 1 → ℝ) × X))]
    [∀ n : ℕ, ParacompactSpace ((Fin 1 → ℝ) × ((Fin n → ℝ) × X))]
    [∀ n : ℕ, ParacompactSpace ↥(pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin 1 → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]
    [∀ (n : ℕ) (A : Set ((Fin n → ℝ) × X)), ParacompactSpace ↥A]
    [∀ (n : ℕ) (A : Set ((Fin 1 → ℝ) × ((Fin n → ℝ) × X))), ParacompactSpace ↥A]
    (Bd : StrongBundle PX P),
    -- the strong bundle is tame (as in V6_33)
    (∀ y : X, ∃ c : StrongBundleChart PX P, Bd.IsTameChart c ∧ y ∈ c.φ.source) →
    ∀ (f : X → Y) (hf : IsSection P f), Bd.IsScFredholmSection f →
    ∀ (hπ : ∀ n : ℕ, ((rnPolyfold n).prod PX).IsScSmoothMap PX Prod.snd),
    -- `U` as in Proposition 6.28, `φ` an sc-smooth path in `U`, `s` as in (3)
    ∀ (x : X) (U : Set X), x ∈ PX.smoothSet → IsNbhd628 Bd (hπ 1) f x U →
    ∀ φ : (Fin 1 → ℝ) → X, IsScPathOn PX φ → (∀ t ∈ I1, φ t ∈ U) →
    ∀ (s : Sec1 P) (hs : IsSection (pullbackProj P Prod.snd) s),
      IsScPlusNear Bd (hπ 1) (I1 ×ˢ U) s → (∀ t ∈ I1, pullbackSlice s t (φ t) = f (φ t)) →
    -- sc⁺-sections `s₁, …, s_k` over `[0, 1] × U` with (P) (Lemma 6.29)
    ∀ (k : ℕ) (σ : Fin k → Sec1 P) (hσ : ∀ i, IsSection (pullbackProj P Prod.snd) (σ i)),
      (∀ i, IsScPlusNear Bd (hπ 1) (I1 ×ˢ U) (σ i)) → PropP Bd hπ f hf s hs σ hσ φ →
    ∃ N : Set ((Fin 1 → ℝ) × ((Fin k → ℝ) × X)), IsOpen N ∧
      let Z := (rnPolyfold 1).prod ((rnPolyfold k).prod PX)
      let S : Set ((Fin 1 → ℝ) × ((Fin k → ℝ) × X)) :=
        {q | q ∈ N ∧ IsZeroAt (pullbackProj (pullbackProj P Prod.snd) Prod.snd)
          (Ffam f hf s hs σ hσ) q}
      let St : (Fin 1 → ℝ) → Set ((Fin k → ℝ) × X) := fun t => {w | (t, w) ∈ S}
      -- `S` contains the curve `t ↦ (t, φ(t), 0)`
      (∀ t ∈ I1, (t, ((0 : Fin k → ℝ), φ t)) ∈ S) ∧
      -- `S` is a smooth manifold with boundary with corners and `π : S → [0, 1]` a submersion
      (Z.IsSmoothSubmanifold S ∧ ∃ hS : Z.IsSubMPolyfold S,
        (Z.subPolyfold hS).IsManifoldWithCornersLoc ∧
        ∃ hsm : (Z.subPolyfold hS).IsScSmoothMap (rnPolyfold 1)
            (fun q : ↥S => (q : (Fin 1 → ℝ) × ((Fin k → ℝ) × X)).1),
          ∀ (ξ : (Z.subPolyfold hS).TangentSpace) (η : (rnPolyfold 1).TangentSpace),
            (rnPolyfold 1).tangentProj η = (rnPolyfold 1).tangentProj (MPolyfold.tangentMap hsm ξ) →
            ∃ ξ' : (Z.subPolyfold hS).TangentSpace,
              (Z.subPolyfold hS).tangentProj ξ' = (Z.subPolyfold hS).tangentProj ξ ∧
              MPolyfold.tangentMap hsm ξ' = η) ∧
      -- the fibres `S_t` are manifolds with boundary with corners
      (∀ t ∈ I1, ((rnPolyfold k).prod PX).IsSmoothSubmanifold (St t) ∧
        ∃ h : ((rnPolyfold k).prod PX).IsSubMPolyfold (St t),
          (((rnPolyfold k).prod PX).subPolyfold h).IsManifoldWithCornersLoc) ∧
      -- `L_t = T_{(φ(t),0)} S_t`: the span of the tangent cone of `S_t`, in the product chart
      (∀ t ∈ I1, ∀ (p : ChartPoint Bd (φ t))
        (q₀ : ↥(pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))),
        kerProd p.c k q₀ p.z (Ft f hf s hs σ hσ t) =
          Submodule.span ℝ (tangentConeAt ℝ
            ((prodChart p.c k q₀).φ.toPartialEquiv '' (St t ∩ (prodChart p.c k q₀).φ.source))
            ((prodChart p.c k q₀).φ.toPartialEquiv ((0 : Fin k → ℝ), φ t)))) ∧
      -- `L` is a smooth vector bundle over `[0, 1]`: smooth local frames in every chart
      (∀ t₀ ∈ I1, ∀ (p : ChartPoint Bd (φ t₀))
        (q₀ : ↥(pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))),
        ∃ J : Set (Fin 1 → ℝ), IsOpen J ∧ t₀ ∈ J ∧
        ∃ zf : (Fin 1 → ℝ) → p.c.φ.model.E.lvl 1,
          (∀ t ∈ J ∩ I1, φ t ∈ p.c.φ.source ∧
            p.c.φ.model.E.toBase 1 (zf t) = p.c.φ.toPartialEquiv (φ t)) ∧
          ∃ (d : ℕ) (e : Fin d → (Fin 1 → ℝ) → (prodChart p.c k q₀).φ.model.E.lvl 0),
            (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (e j) J) ∧
            ∀ t ∈ J ∩ I1, LinearIndependent ℝ (fun j => e j t) ∧
              Submodule.span ℝ (Set.range fun j => e j t) =
                kerProd p.c k q₀ (zf t) (Ft f hf s hs σ hσ t))

end RoundTrip.V6_34
