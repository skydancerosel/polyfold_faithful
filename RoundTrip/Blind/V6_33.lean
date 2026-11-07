import Polyfold
/-! Blind formalization of V6_33 (the text's §6.5, the section `F`, p. 221; Lemma 6.29, p. 222).

Text: with `s(φ(t), t) = f(φ(t))` and `F(t, y, λ) = f(y) − s(y, t) + Σ λᵢ sᵢ(y, t)` on
`[0, 1] × X × ℝᵏ`, there are finitely many sc⁺-sections `s₁, …, s_k` with (P): for every fixed
`t`, `F_t` is at `(φ(t), 0)` in general position to the boundary of `X × ℝᵏ`.  (P) implies that
`F` is in general position at all `(t, φ(t), 0)`.

Choices:
- Setting and encodings as in `RoundTrip/Blind/V6_32.lean` (Proposition 6.28), whose prelude is
  copied: `X Y : Type`, `Bd : StrongBundle PX P`, `f` sc-Fredholm; `[0, 1] = Set.Icc 0 1 ⊆ ℝ¹`;
  "sc⁺-section over `[0, 1] × U`" = a section of `π*P → ℝ¹ × X` which is sc⁺ on an open set
  containing `[0, 1] × U` (`IsScPlusNear`); `s(y, t)` is `pullbackSlice s t y`.
- Context (the text's §6.5): `x` smooth, `U` an open neighbourhood of `x` with (1)–(4) of
  Proposition 6.28 (`IsNbhd628`), `φ` an sc-smooth path in `U` on `[0, 1]`, `s` the sc⁺-section
  of (3) with `s(φ(t), t) = f(φ(t))` for `t ∈ [0, 1]`.  The `sᵢ` are sc⁺-sections over
  `[0, 1] × U` in the same sense ("finitely many": some `k : ℕ`).
- Added hypotheses: `f` is a section (`IsSection P f`; `F` is built from fibrewise sums, which
  need it), and the strong bundle is tame: every point lies in a tame strong bundle chart
  (`StrongBundle.IsTameChart`).  General position (Definition 5.17, the project's
  `IsGeneralPositionGerm`) is defined in a tame chart, so the text presupposes tameness; without
  it the existence claim could fail vacuously.
- `F_t(λ, y) = (f − s(·, t))(y) + Σ λᵢ sᵢ(y, t)`: the project's `paramSection` of
  `sectionDiff P f (s(·, t))` and the slices `sᵢ(·, t)`, a section of `π*P → ℝᵏ × X`
  (factors in the project's order `ℝᵏ × X`; the text's point `(φ(t), 0)` is `(0, φ(t))`).  The
  section property of the slices and of `f − s(·, t)` is proved below.
- (P): `∀ t ∈ [0, 1]`, `(Bd.pullback hπ).IsGeneralPositionGerm F_t (0, φ(t))` ("general position
  to the boundary of `X × ℝᵏ`" is general position in the M-polyfold `ℝᵏ × X`).
- `F` on `[0, 1] × X × ℝᵏ`: a section of the pull-back of `π*P → ℝᵏ × X` along
  `ℝ¹ × (ℝᵏ × X) → ℝᵏ × X` (a second `StrongBundle.pullback`), `F(t, λ, y) = F_t(λ, y)`.  "In
  general position at `(t, φ(t), 0)`" is `IsGeneralPositionGerm` of this bundle at
  `(t, (0, φ(t)))`.  DOUBT: `[0, 1]` is replaced by the boundaryless `ℝ¹`, so the boundary of
  `[0, 1]` at `t ∈ {0, 1}` is not seen by the general position of `F` (the vocabulary has no
  M-polyfold `[0, 1]`).
- The implication "(P) ⇒ `F` in general position" is stated for every family of sc⁺-sections
  `s₁, …, s_k` over `[0, 1] × U` (it is not specific to the chosen ones).
- Technical hypotheses: the sc-smoothness of the projections `ℝⁿ × X → X` and
  `ℝ¹ × (ℝⁿ × X) → ℝⁿ × X` is quantified over (true; the pull-back bundles need it);
  paracompactness of the products, subsets and pulled-back total spaces are instance hypotheses
  (true: M-polyfolds are metrizable).  The section property of `s`, `sᵢ` (implied by
  `IsScPlusNear`) is named as a binder because `F` needs it.
- Nothing looks false to me (apart from the `[0, 1]` boundary point above).
-/
namespace RoundTrip.V6_33
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

/-- `F` is in general position at every `(t, 0, φ(t))`, `t ∈ [0, 1]`. -/
def FamGP (Bd : StrongBundle PX P)
    (hπ : ∀ n : ℕ, ((rnPolyfold n).prod PX).IsScSmoothMap PX Prod.snd)
    (hπ' : ∀ n : ℕ, ((rnPolyfold 1).prod ((rnPolyfold n).prod PX)).IsScSmoothMap
      ((rnPolyfold n).prod PX) Prod.snd)
    (f : X → Y) (hf : IsSection P f) (s : Sec1 P) (hs : IsSection (pullbackProj P Prod.snd) s)
    {k : ℕ} (σ : Fin k → Sec1 P) (hσ : ∀ i, IsSection (pullbackProj P Prod.snd) (σ i))
    (φ : (Fin 1 → ℝ) → X) : Prop :=
  ∀ t ∈ I1, ((Bd.pullback (hπ k)).pullback (hπ' k)).IsGeneralPositionGerm
    (Ffam f hf s hs σ hσ) (t, (0, φ t))

end

/-- Lemma 6.29: there are finitely many sc⁺-sections `s₁, …, s_k` over `[0, 1] × U` with (P);
and (P) implies that `F` is in general position at all `(t, φ(t), 0)`. -/
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
    (Bd : StrongBundle PX P),
    -- the strong bundle is tame (general position is defined in tame charts)
    (∀ y : X, ∃ c : StrongBundleChart PX P, Bd.IsTameChart c ∧ y ∈ c.φ.source) →
    ∀ (f : X → Y) (hf : IsSection P f), Bd.IsScFredholmSection f →
    ∀ (hπ : ∀ n : ℕ, ((rnPolyfold n).prod PX).IsScSmoothMap PX Prod.snd)
      (hπ' : ∀ n : ℕ, ((rnPolyfold 1).prod ((rnPolyfold n).prod PX)).IsScSmoothMap
        ((rnPolyfold n).prod PX) Prod.snd),
    -- `U` as in Proposition 6.28, `φ` an sc-smooth path in `U`, `s` as in (3)
    ∀ (x : X) (U : Set X), x ∈ PX.smoothSet → IsNbhd628 Bd (hπ 1) f x U →
    ∀ φ : (Fin 1 → ℝ) → X, IsScPathOn PX φ → (∀ t ∈ I1, φ t ∈ U) →
    ∀ (s : Sec1 P) (hs : IsSection (pullbackProj P Prod.snd) s),
      IsScPlusNear Bd (hπ 1) (I1 ×ˢ U) s → (∀ t ∈ I1, pullbackSlice s t (φ t) = f (φ t)) →
      -- the sections `s₁, …, s_k` with (P)
      (∃ (k : ℕ) (σ : Fin k → Sec1 P) (hσ : ∀ i, IsSection (pullbackProj P Prod.snd) (σ i)),
        (∀ i, IsScPlusNear Bd (hπ 1) (I1 ×ˢ U) (σ i)) ∧ PropP Bd hπ f hf s hs σ hσ φ) ∧
      -- (P) implies that `F` is in general position along `t ↦ (t, φ(t), 0)`
      (∀ (k : ℕ) (σ : Fin k → Sec1 P) (hσ : ∀ i, IsSection (pullbackProj P Prod.snd) (σ i)),
        (∀ i, IsScPlusNear Bd (hπ 1) (I1 ×ˢ U) (σ i)) → PropP Bd hπ f hf s hs σ hσ φ →
        FamGP Bd hπ hπ' f hf s hs σ hσ φ)

end RoundTrip.V6_33
