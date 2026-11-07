import Polyfold
/-! Blind formalization of V6_1 (the text's §6.1, Definition 6.1, p. 201, with pp. 200–201 and the
convexity remark of §6.5, p. 219: the space `Lin(f, x)` of linearizations).  Choices:
- Setting: `X Y : Type` (universe 0, as in the other blind files), `PX : MPolyfold X`,
  `P : Y → X` with the fibrewise linear structure as instances, `Bd : StrongBundle PX P`,
  `f : X → Y` an sc-Fredholm section (`StrongBundle.IsScFredholmSection`, Definition 3.14, germ
  reading; no tameness — the md attaches none), `x` a smooth point (`IsSmoothPt`:
  `x ∈ X_∞ = ⋂ X_m`, `MPolyfold.levelSet`).
- `T_xX → Y_x` is read in a strong bundle chart around `x`: the project's `ChartPoint Bd x` (a
  chart `c` of `Bd` with `x` in its domain and the level-1 point `z` over `φ(x)`; fields read with
  `#print`), with `p.T = T_zO = Dr(z)E` and `p.K = K_z = ρ(z)F` (the project's, matching their
  docstrings).  `Lin(f, x)` is a set of bounded operators `T_zO → K_z` (level `0`); my `LinB p f`.
- "A local sc⁺-section `s` with `s(x) = f(x)`" (`IsLocScPlusSec p W ŝ`): an open `W ⊆ E₀`
  containing `z₀ = φ(x)`, and a principal part `ŝ` on `O ∩ W` with `(y, ŝ y) ∈ K`, such that
  `ŝ ∘ r` lifts to an sc-smooth map `U ∩ r⁻¹(W) → F¹` (Definition 2.49 in the chart: sc-smooth
  into `K[1]`); `s(x) = f(x)` is `ŝ(z₀) = f̂(z₀)` (`f̂` = `c.principal f`).
- `(f − s)'(x)` (`IsLinOfDiff`): the operator `L₀ : T_zO → K_z` with
  `L₀ v = D((f̂ − ŝ) ∘ r)(z) v` (`scDeriv` on `U ∩ r⁻¹(W)`, the set where `ŝ ∘ r` lives).
- "sc⁺-operator `a : T_xX → Y_x`" (`IsScPlusOpB`): `T_zO`, `K_z` are sc-subspaces and `a` is level
  `0` of an sc⁺-operator `T_zO → K_z` (project's `ScPlus` = sc-operator into the shift) for the
  induced sc-structures.  "sc-Fredholm of index `i`" (`IsScFredholmOfIndex`): `L` is level `0` of
  an sc-operator `T_zO → K_z` which is sc-Fredholm (`IsScFredholm`, Definition 1.8) with
  `scIndex = i`.
- `Lin(f, x) = {(f − s)'(x) + a}`: my `LinB` takes `s` existentially; the text's construction
  `s(y) = R(y, f(x))` and the independence of `s` are claims (2), (3) below.
- `B` is the conjunction, for every such `f`, `x`, of: for every chart point `p`,
  (1) the project's `ChartPoint.linSet f p` equals `LinB p f` (the definition);
  (2) the text's section, `ŝ(y) = (R(y, f̂(z₀)))₂` in the chart (`R` the strong bundle
      retraction of `c`; on `O` this is `s(y) = R(y, f(x))`), is a local sc⁺-section (with
      `W = E₀`) with `s(x) = f(x)`; and `Lin(f, x)` is nonempty;
  (3) for EVERY local sc⁺-section `s` with `s(x) = f(x)`, `(f − s)'(x)` maps `T_zO` into `K_z` and
      `Lin(f, x) = {(f − s)'(x) + a | a sc⁺}` (no dependence on `s`);
  (4) members differ by sc⁺-operators;
  (5) `Lin(f, x)` is convex (§6.5, p. 219);
  and (6) all members, in all charts around `x`, are sc-Fredholm of one index `i = ind(f, x)`.
- Doubts: (1) is the only clause about the project's `linSet`; it compares with LOCAL sections in
  the chart, as the md says.  A `#print` of `ChartPoint.linSet` (a definition) showed me that it
  is built from GLOBAL sc⁺-sections of `Bd` (with `f + s` vanishing at `x`); so (1) needs a
  global sc⁺-section through `f(x)`, which the text's local reading does not presuppose (it holds
  when such sections exist, by (3)).  If Chapter 6 presupposes tame bundles (Definition 3.51),
  the hypothesis `IsScFredholmSection` is weaker than the text's.  Nothing in the statement looks
  false to me.
-/
namespace RoundTrip.V6_1
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {Bd : StrongBundle PX P} {x : X}

/-- `x` is a smooth point: `x ∈ X_∞ = ⋂ X_m`. -/
def IsSmoothPt (PX : MPolyfold X) (x : X) : Prop := ∀ m : ℕ, x ∈ PX.levelSet m

/-- A local sc⁺-section near `z₀ = φ(x)` in the chart of `p`: an open `W ∋ z₀` and a principal
part `ŝ` on `O ∩ W` with values in the fibres of `K`, `ŝ ∘ r` sc-smooth into `F¹` on
`U ∩ r⁻¹(W)`. -/
def IsLocScPlusSec (p : ChartPoint Bd x) (W : Set (p.c.φ.model.E.lvl 0))
    (ŝ : p.c.φ.model.E.lvl 0 → p.c.F.lvl 0) : Prop :=
  IsOpen W ∧ p.c.φ.model.E.toBase 1 p.z ∈ W ∧
  (∀ y ∈ p.c.φ.model.O ∩ W, (y, ŝ y) ∈ p.c.K) ∧
  ∃ σ : p.c.φ.model.E.lvl 0 → p.c.F.shift.lvl 0,
    IsScSmooth (p.c.U ∩ StrongRetr.r p.c.R ⁻¹' W) σ ∧
    ∀ u ∈ p.c.U ∩ StrongRetr.r p.c.R ⁻¹' W,
      p.c.F.shiftIncl.lvl 0 (σ u) = ŝ (StrongRetr.r p.c.R u)

/-- `L₀ = (f − s)'(x)` in the chart: `L₀ v = D((f̂ − ŝ) ∘ r)(z) v` for `v ∈ T_zO`. -/
def IsLinOfDiff (p : ChartPoint Bd x) (f : X → Y) (W : Set (p.c.φ.model.E.lvl 0))
    (ŝ : p.c.φ.model.E.lvl 0 → p.c.F.lvl 0) (L₀ : ↥p.T →L[ℝ] ↥p.K) : Prop :=
  ∀ v : ↥p.T, (L₀ v : p.c.F.lvl 0) =
    scDeriv (p.c.U ∩ StrongRetr.r p.c.R ⁻¹' W)
      (fun u => p.c.principal f (StrongRetr.r p.c.R u) - ŝ (StrongRetr.r p.c.R u)) p.z
      (v : p.c.φ.model.E.lvl 0)

/-- `a : T_zO → K_z` is an sc⁺-operator: `T_zO`, `K_z` are sc-subspaces and `a` is level `0` of an
sc⁺-operator between them. -/
def IsScPlusOpB (p : ChartPoint Bd x) (a : ↥p.T →L[ℝ] ↥p.K) : Prop :=
  ∃ (hT : p.c.φ.model.E.IsScSubspace p.T) (hK : p.c.F.IsScSubspace p.K)
    (S : ScPlus (p.c.φ.model.E.ofSubspace hT) (p.c.F.ofSubspace hK)),
    ∀ (v : ↥p.T) (w : ↥(p.c.φ.model.E.levelSub p.T 0)),
      (w : p.c.φ.model.E.lvl 0) = (v : p.c.φ.model.E.lvl 0) →
        (Subtype.val : ↥(p.c.F.levelSub p.K 0) → p.c.F.lvl 0) (S.toScOperator.lvl 0 w) =
          (a v : p.c.F.lvl 0)

/-- `L : T_zO → K_z` is sc-Fredholm of index `i`: level `0` of an sc-operator between the
sc-subspaces `T_zO`, `K_z` which is sc-Fredholm with index `i`. -/
def IsScFredholmOfIndex (p : ChartPoint Bd x) (L : ↥p.T →L[ℝ] ↥p.K) (i : ℤ) : Prop :=
  ∃ (hT : p.c.φ.model.E.IsScSubspace p.T) (hK : p.c.F.IsScSubspace p.K)
    (L₀ : ↥(p.c.φ.model.E.levelSub p.T 0) →L[ℝ] ↥(p.c.F.levelSub p.K 0)),
    (∀ (v : ↥p.T) (w : ↥(p.c.φ.model.E.levelSub p.T 0)),
      (w : p.c.φ.model.E.lvl 0) = (v : p.c.φ.model.E.lvl 0) →
        (L₀ w : p.c.F.lvl 0) = (L v : p.c.F.lvl 0)) ∧
    ∃ hL : @IsScOperator (p.c.φ.model.E.ofSubspace hT) (p.c.F.ofSubspace hK) L₀,
      IsScFredholm hL.toScOperator ∧ scIndex hL.toScOperator = i

/-- **Definition 6.1** in the chart of `p`: `Lin(f, x) = {(f − s)'(x) + a}` for a local
sc⁺-section `s` with `s(x) = f(x)` and an sc⁺-operator `a`. -/
def LinB (p : ChartPoint Bd x) (f : X → Y) : Set (↥p.T →L[ℝ] ↥p.K) :=
  {L | ∃ (W : Set (p.c.φ.model.E.lvl 0)) (ŝ : p.c.φ.model.E.lvl 0 → p.c.F.lvl 0),
    IsLocScPlusSec p W ŝ ∧
    ŝ (p.c.φ.model.E.toBase 1 p.z) = p.c.principal f (p.c.φ.model.E.toBase 1 p.z) ∧
    ∃ (L₀ a : ↥p.T →L[ℝ] ↥p.K), IsLinOfDiff p f W ŝ L₀ ∧ IsScPlusOpB p a ∧ L = L₀ + a}

end

/-- Definition 6.1: `Lin(f, x)` is the project's `linSet`; it is nonempty, does not depend on
the section `s`, its members differ by sc⁺-operators, it is convex, and all its members are
sc-Fredholm of one index `ind(f, x)`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    Bd.IsScFredholmSection f → IsSmoothPt PX x →
      (∀ p : ChartPoint Bd x,
        -- (1) the definition
        ChartPoint.linSet f p = LinB p f ∧
        -- (2) the text's section `s(y) = R(y, f(x))` is a local sc⁺-section with `s(x) = f(x)`,
        -- and `Lin(f, x)` is nonempty
        (IsLocScPlusSec p Set.univ
            (fun y => (p.c.R (y, p.c.principal f (p.c.φ.model.E.toBase 1 p.z))).2) ∧
          (p.c.R (p.c.φ.model.E.toBase 1 p.z,
            p.c.principal f (p.c.φ.model.E.toBase 1 p.z))).2 =
              p.c.principal f (p.c.φ.model.E.toBase 1 p.z)) ∧
        (LinB p f).Nonempty ∧
        -- (3) independent of the section `s`
        (∀ (W : Set (p.c.φ.model.E.lvl 0)) (ŝ : p.c.φ.model.E.lvl 0 → p.c.F.lvl 0),
          IsLocScPlusSec p W ŝ →
          ŝ (p.c.φ.model.E.toBase 1 p.z) = p.c.principal f (p.c.φ.model.E.toBase 1 p.z) →
            ∃ L₀ : ↥p.T →L[ℝ] ↥p.K, IsLinOfDiff p f W ŝ L₀ ∧
              LinB p f = {L | ∃ a : ↥p.T →L[ℝ] ↥p.K, IsScPlusOpB p a ∧ L = L₀ + a}) ∧
        -- (4) members differ by sc⁺-operators
        (∀ L₁ ∈ LinB p f, ∀ L₂ ∈ LinB p f, IsScPlusOpB p (L₁ - L₂)) ∧
        -- (5) convex
        Convex ℝ (LinB p f)) ∧
      -- (6) one index `ind(f, x)`
      ∃ i : ℤ, ∀ p : ChartPoint Bd x, ∀ L ∈ LinB p f, IsScFredholmOfIndex p L i

end RoundTrip.V6_1
