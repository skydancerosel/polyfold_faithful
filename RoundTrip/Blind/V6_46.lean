import Polyfold
/-! Blind formalization of V6_46 (the text's §6.5, pp. 224–226; and the proof of Theorem 5.18,
p. 178).

Text: the added sections `s̄ⱼ(y, t)` of Lemma 6.33 (p. 224) and the sections `s(y, τ, t)`,
`sᵢ(y, τ, t)` over a square (p. 226) are used as sc⁺-sections over the products, and adding
sections is taken to keep the general position (said in the proof of Theorem 5.18, p. 178).

Choices:
- Setting: `X Y : Type` (universe 0); `PX : MPolyfold X`, `P : Y → X` with the fibrewise linear
  structure as instances, `B : StrongBundle PX P`; for (4) `X` tame (general position,
  Definition 5.17, is defined for tame `X`).
- "Sections over the products" `X × [0, 1]`, `X × [0, 1]²`, `X × [0, 1] × ℝᵐ`: sections of the
  pull-back `π*P` over `ℝⁿ × X` (Proposition 2.54, `B.pullback`, on `(rnPolyfold n).prod PX`;
  parameters written first, `[0, 1]` and the square inside `ℝ¹`, `ℝ²`, as the project's paths).
  Forming `π*P` needs `Prod.snd : ℝⁿ × X → X` sc-smooth: a hypothesis `hπ : SndSmooth PX` (true;
  I may not look up the project's lemma); paracompactness of `ℝⁿ × X`, `π*Y` as instances.
- Reading: the text uses, without comment, that the following constructions give sc⁺-sections
  over the products, and that adding sections keeps general position.  B is the conjunction of
  (1) reparametrizing the parameter linearly keeps sc⁺: for `S` sc⁺ over `ℝⁿ × X` and a linear
      `g : ℝᵐ → ℝⁿ`, `(q, y) ↦ S(g(q), y)` is sc⁺ over `ℝᵐ × X` (this covers `s̄ⱼ(y, t)` and
      `s(y, t)` used over the square or over `[0, 1] × ℝᵐ`, e.g. `g(τ, t) = t`);
  (2) slices of sc⁺-sections are sc⁺: `y ↦ S(q, y)` is an sc⁺-section of `P` (used whenever
      `f − s(·, t)`, `sᵢ(·, t)` are treated as sections of `P`);
  (3) the convex combination over the square, `s(y, τ, t) = τ s¹(y, t) + (1 − τ) s⁰(y, t)`
      (Lemma 6.34), is sc⁺ over `ℝ² × X` when `s⁰`, `s¹` are sc⁺ over `ℝ¹ × X`;
  (4) adding sections keeps general position (Theorem 5.18's "adding more sections, the
      properties will still hold", applied to (P)): if `G(λ, y) = g(y) + Σ λᵢ σᵢ(y)` over
      `ℝᵏ × X` is in general position (the project's `IsGeneralPositionGerm`, Definition 5.17,
      audited as V5_31) at `(0, x)`, `g(x) = 0`, then so is
      `(λ, μ, y) ↦ g(y) + Σ λᵢ σᵢ(y) + Σ μⱼ s̄ⱼ(y)` over `ℝ^{k+l} × X` (`Fin.append`), for `g`
      sc-Fredholm and `σᵢ`, `s̄ⱼ` sc⁺ (in (P), `g = f − s(·, t)` and the slices at `t`).
- Combinations are computed in the fibre `Y_y` (`fv`: the value as a fibre point, junk `0` when
  it is not in `Y_y`, which does not happen for sections).  The `sᵢ(y, τ, t)` of p. 226 are chosen
  as sc⁺-sections over the square; that is a hypothesis of Lemma 6.34 (V6_47), not a claim.
- Nothing looks false to me.
-/
namespace RoundTrip.V6_46
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

open Classical in
/-- The value `g(y)` as a point of the fibre `Y_y` (junk `0` if `g(y) ∉ Y_y`). -/
noncomputable def fv (g : X → Y) (y : X) : P ⁻¹' {y} :=
  if h : P (g y) = y then ⟨g y, h⟩ else 0

/-- `G(λ, y) = g(y) + Σ λᵢ σᵢ(y)`, a section of `π*P → ℝᵏ × X`. -/
noncomputable def Fgen {k : ℕ} (g : X → Y) (σ : Fin k → X → Y) :
    (Fin k → ℝ) × X → pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X) :=
  fun w => ⟨(w, ((fv (P := P) g w.2 + ∑ i, w.1 i • fv (P := P) (σ i) w.2 : P ⁻¹' {w.2}) : Y)),
    Set.mem_singleton_iff.mp (fv (P := P) g w.2 + ∑ i, w.1 i • fv (P := P) (σ i) w.2).2⟩

/-- `(q, y) ↦ S(g(q), y)`: the section `S` over `ℝⁿ × X` reparametrized along `g : ℝᵐ → ℝⁿ`. -/
noncomputable def reparam {m n : ℕ} (g : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ))
    (S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) :
    (Fin m → ℝ) × X → pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X) :=
  fun w => ⟨(w, ((fv (P := P) (pullbackSlice S (g w.1)) w.2 : P ⁻¹' {w.2}) : Y)),
    Set.mem_singleton_iff.mp (fv (P := P) (pullbackSlice S (g w.1)) w.2).2⟩

/-- `s(y, τ, t) = τ s¹(y, t) + (1 − τ) s⁰(y, t)` over the square (`w.1 = (τ, t)`). -/
noncomputable def convSq
    (s₀ s₁ : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)) :
    (Fin 2 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 2 → ℝ) × X → X) :=
  fun w => ⟨(w, ((w.1 0 • fv (P := P) (pullbackSlice s₁ (pt1 (w.1 1))) w.2 +
      (1 - w.1 0) • fv (P := P) (pullbackSlice s₀ (pt1 (w.1 1))) w.2 : P ⁻¹' {w.2}) : Y)),
    Set.mem_singleton_iff.mp (w.1 0 • fv (P := P) (pullbackSlice s₁ (pt1 (w.1 1))) w.2 +
      (1 - w.1 0) • fv (P := P) (pullbackSlice s₀ (pt1 (w.1 1))) w.2).2⟩

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- `Prod.snd : ℝⁿ × X → X` is sc-smooth (needed to form the pull-back `π*P`). -/
abbrev SndSmooth (PX : MPolyfold X) : Prop :=
  ∀ n : ℕ, ((rnPolyfold n).prod PX).IsScSmoothMap PX (Prod.snd : (Fin n → ℝ) × X → X)

end

/-- Sections over parameter families: linear reparametrizations, slices and the convex
combination over the square are sc⁺, and adding sections keeps general position. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    (B : StrongBundle PX P) (hπ : SndSmooth PX),
    -- (1) linear reparametrization of the parameter
    (∀ (m n : ℕ) (g : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ))
      (S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)),
      (B.pullback (hπ n)).IsScPlusSection S →
        (B.pullback (hπ m)).IsScPlusSection (reparam g S)) ∧
    -- (2) slices
    (∀ (n : ℕ) (S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
      (q : Fin n → ℝ),
      (B.pullback (hπ n)).IsScPlusSection S → B.IsScPlusSection (pullbackSlice S q)) ∧
    -- (3) the convex combination over the square
    (∀ s₀ s₁ : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X),
      (B.pullback (hπ 1)).IsScPlusSection s₀ → (B.pullback (hπ 1)).IsScPlusSection s₁ →
        (B.pullback (hπ 2)).IsScPlusSection (convSq s₀ s₁)) ∧
    -- (4) adding sections keeps general position
    (PX.IsTame → ∀ (k l : ℕ) (g : X → Y) (σ : Fin k → X → Y) (sb : Fin l → X → Y) (x : X),
      B.IsScFredholmSection g → (∀ i, B.IsScPlusSection (σ i)) →
      (∀ j, B.IsScPlusSection (sb j)) → IsZeroAt P g x →
      (B.pullback (hπ k)).IsGeneralPositionGerm (Fgen g σ) (0, x) →
        (B.pullback (hπ (k + l))).IsGeneralPositionGerm (Fgen g (Fin.append σ sb)) (0, x))

end RoundTrip.V6_46
