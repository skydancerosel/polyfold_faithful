import Polyfold
/-! Blind formalization of V7_39 (the 2017 book's Part II, §7.2, Proposition 7.9, p. 242, with
the description of the structure from its proof, pp. 242–243).

Text: the reduced morphism set `𝐗^R` has a natural M-polyfold structure: `𝐗^R` carries the
quotient topology of `π : 𝐗 → 𝐗^R`; for an open `𝐔(φ₀)` on which `s` is an sc-diffeomorphism, the
maps `Ψ_{φ₀} : 𝐔(φ₀) → 𝐔([φ₀])`, `φ ↦ [φ]`, are homeomorphisms between open subsets of `𝐗` and
open subsets of `𝐗^R` with sc-smooth transition maps, and this defines the M-polyfold structure.

Choices:
- Setting: `Obj Mor : Type` (spaces in `Type`; the project's `EpGroupoid` is universe-polymorphic,
  this is `u = 0`), with their topologies, Hausdorff and paracompact, `X : EpGroupoid Obj Mor`
  (the project's Definition 7.3, checked with `#print`; see `RoundTrip/Blind/V7_33.lean`).
- `T_x`, `∼` and `𝐗^R` are mine, as in `RoundTrip/Blind/V7_38.lean` (`NatRepB`, `TxB`, `RelB`;
  `T_x` uses the data of Theorem 7.1 with `U` open and connected, the text's presupposition, see
  `RoundTrip/Blind/V7_35.lean`).  `𝐗^R` is
  `Quot (RelB X)` (`XRB`) with Mathlib's quotient topology (the topology coinduced by `π`); its
  classes are the `∼`-classes since `∼` is an equivalence relation (V7_38).  I do not use the
  project's `ReducedMor`, `reducedPolyfold`, `reducedChart`.
- "open `𝐔(φ₀)` on which `s` is an sc-diffeomorphism" (`IsSrcSheetB`): an open `W ⊆ 𝐗` such that
  `s : W → V` is an sc-diffeomorphism onto some open `V ⊆ X` (the project's `IsScDiffeoOn`, checked
  with `#print`: both maps sc-smooth on the open sets, `MapsTo` both ways, mutually inverse).  The
  claims are made for every such `W` (whatever `φ₀ ∈ W`).
- "`Ψ` is a homeomorphism between open subsets": `π(W)` is open and `φ ↦ [φ]` is a homeomorphism
  `W ≃ₜ π(W)`.
- "sc-smooth transition maps": for two such `W₀, W₁`, the map `Ψ_1⁻¹ ∘ Ψ_0`, defined on
  `D = W₀ ∩ π⁻¹(π(W₁))`, is sc-smooth on `D` (the project's `IsScSmoothOn`, which includes that
  `D` is open); it is stated for every `τ : Mor → Mor` with `τ(φ) ∈ W₁` and `[τ(φ)] = [φ]` on `D`
  (unique on `D`, `Ψ_1` being injective; only values on `D` matter).
- "natural M-polyfold structure": an M-polyfold (Definition 2.13; the project's `MPolyfold`,
  an sc-smooth atlas on a Hausdorff paracompact space) on `𝐗^R` with the quotient topology, so B
  asserts that `𝐗^R` is Hausdorff and paracompact, and a structure `Q` for which every `Ψ` is an
  sc-diffeomorphism `W → π(W)`.  Since the `π(W)` cover `𝐗^R` (`s` is a local sc-diffeomorphism),
  this determines `Q` up to equivalence of atlases.
- Doubtful (formalized literally anyway): I believe the Hausdorff part does not hold as I read it
  when the object space has jumping dimension.  Take Part I's sc-retract
  `O = {(t, 0) | t ≤ 0} ∪ {(t, s γ_t) | t > 0, s ∈ ℝ} ⊆ ℝ × L²` (`r(t, f) = (t, ⟨f, γ_t⟩ γ_t)` for
  `t > 0`, `γ_t` a bump moving off to infinity as `t ↓ 0`), and `ℤ/2 = {1, h}` acting by
  `(t, f) ↦ (t, −f)` (sc-linear, commuting with `r`); the translation groupoid `ℤ/2 ⋉ O` is an
  ep-groupoid.  Then `T_{(t,0)} = ℤ/2` for `t < 0`, but `T_{(0,0)} = 1`, so `[(1, (0,0))] ≠
  [(h, (0,0))]` in `𝐗^R`, while every pair of neighbourhoods of them meets in
  `[(1, (t,0))] = [(h, (t,0))]`, `t < 0` small.  The other conjuncts look true to me.
-/
namespace RoundTrip.V7_39
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- **The natural `G_x`-action on `U`** (the data of Theorem 7.1): a connected open `U ∋ x`, a
homomorphism `Φ : G_x → Diff_sc(U)` and an sc-smooth `Γ : G_x × U → 𝐗` with (1) `Γ(g, x) = g`,
(2) `s Γ(g, y) = y`, `t Γ(g, y) = Φ(g)(y)`, (3) `Γ(·, y)` is a bijection onto the morphisms from
`y` to points of `U`. -/
structure NatRepB (X : EpGroupoid Obj Mor) (x : Obj) where
  /-- The neighbourhood `U = U(x)`. -/
  U : Set Obj
  isOpen_U : IsOpen U
  isConnected_U : IsConnected U
  mem_U : x ∈ U
  /-- The action `Φ : G_x → Diff_sc(U)`. -/
  Φ : X.Isotropy x → Obj → Obj
  /-- The map `Γ : G_x × U → 𝐗`. -/
  Γ : X.Isotropy x → Obj → Mor
  diffeo : ∀ g, ∃ ψ : Obj → Obj, X.PObj.IsScDiffeoOn X.PObj (Φ g) ψ U U
  hom : ∀ g h, ∀ y ∈ U, Φ (g * h) y = Φ g (Φ h y)
  smooth : ∀ g, X.PObj.IsScSmoothOn X.PMor (Γ g) U
  Γ_x : ∀ g, Γ g x = g.val
  src_Γ : ∀ g, ∀ y ∈ U, X.src (Γ g y) = y
  tgt_Γ : ∀ g, ∀ y ∈ U, X.tgt (Γ g y) = Φ g y
  unique : ∀ h : Mor, X.src h ∈ U → X.tgt h ∈ U → ∃! g, Γ g (X.src h) = h

/-- `g ∈ G_x` **acts trivially**: `Φ(g) = 1` on `U(x)` for some `U(x)` with the natural action. -/
def ActsTriviallyB (X : EpGroupoid Obj Mor) {x : Obj} (g : X.Isotropy x) : Prop :=
  ∃ R : NatRepB X x, ∀ y ∈ R.U, R.Φ g y = y

/-- `T_x ⊆ G_x`: the elements acting trivially. -/
def TxB (X : EpGroupoid Obj Mor) (x : Obj) : Set (X.Isotropy x) :=
  {g | ActsTriviallyB X g}

/-- **Definition 7.12**: `φ ∼ φ'`: `s φ = s φ' = x` and `φ = φ' ∘ g` for some `g ∈ T_x`. -/
def RelB (X : EpGroupoid Obj Mor) (φ φ' : Mor) : Prop :=
  X.src φ = X.src φ' ∧ ∃ g : X.Isotropy (X.src φ), g ∈ TxB X (X.src φ) ∧ φ = X.comp φ' g.val

/-- **The reduced morphisms** `𝐗^R`, the `∼`-classes, with the quotient topology. -/
abbrev XRB (X : EpGroupoid Obj Mor) : Type :=
  Quot (RelB X)

/-- The projection `π : 𝐗 → 𝐗^R`, `φ ↦ [φ]`. -/
def πB (X : EpGroupoid Obj Mor) : Mor → XRB X :=
  Quot.mk (RelB X)

/-- `W` is an open set of morphisms on which `s` is an sc-diffeomorphism onto an open set. -/
def IsSrcSheetB (X : EpGroupoid Obj Mor) (W : Set Mor) : Prop :=
  ∃ (σ : Obj → Mor) (V : Set Obj), X.PMor.IsScDiffeoOn X.PObj X.src σ W V

end

/-- Proposition 7.9: with the quotient topology, the maps `Ψ : W → π(W)`, `φ ↦ [φ]`, are
homeomorphisms onto open sets with sc-smooth transition maps, and they make `𝐗^R` an M-polyfold. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    -- `Ψ` is a homeomorphism between open subsets of `𝐗` and of `𝐗^R`
    (∀ W : Set Mor, IsSrcSheetB X W →
      IsOpen (πB X '' W) ∧ ∃ e : W ≃ₜ (πB X '' W), ∀ φ : W, (e φ : XRB X) = πB X φ) ∧
    -- the transition maps `Ψ_1⁻¹ ∘ Ψ_0` are sc-smooth
    (∀ W₀ W₁ : Set Mor, IsSrcSheetB X W₀ → IsSrcSheetB X W₁ → ∀ τ : Mor → Mor,
      (∀ φ ∈ W₀ ∩ πB X ⁻¹' (πB X '' W₁), τ φ ∈ W₁ ∧ πB X (τ φ) = πB X φ) →
      X.PMor.IsScSmoothOn X.PMor τ (W₀ ∩ πB X ⁻¹' (πB X '' W₁))) ∧
    -- the M-polyfold structure for which every `Ψ` is an sc-diffeomorphism
    (∃ (_ : T2Space (XRB X)) (_ : ParacompactSpace (XRB X)) (Q : MPolyfold (XRB X)),
      ∀ W : Set Mor, IsSrcSheetB X W →
        ∃ g : XRB X → Mor, X.PMor.IsScDiffeoOn Q (πB X) g W (πB X '' W))

end RoundTrip.V7_39
