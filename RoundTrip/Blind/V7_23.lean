import Polyfold
/-! Blind formalization of V7_23 (the 2017 book, arXiv 1707.08941, Part II, §7.1, pp. 232–233:
the map `Φ̂ : G_x → Diff_sc(𝐔(x))`).

Text: every `φ ∈ 𝐔(x)` lies in `𝐔(h)` for a unique `h ∈ G_x`, and `φ = Γ(h, s φ)`,
`t φ = Φ(h)(s φ)`; `Φ̂(g)(φ) = Γ(g h g⁻¹, g ∗ s φ)` for `φ ∈ 𝐔(h)` defines a group homomorphism
`Φ̂ : G_x → Diff_sc(𝐔(x))` with `Φ̂(g)(𝐔(h)) = 𝐔(g h g⁻¹)`, `s(Φ̂(g)φ) = Φ(g)(s φ)`,
`t(Φ̂(g)φ) = Φ(g)(t φ)`; to sum up, one can choose a small connected `U(x)` such that `𝐔(x)` is
the disjoint union of the connected open `𝐔(g)` and `Φ̂(g)|𝐔(h) : 𝐔(h) → 𝐔(ghg⁻¹)`,
`s, t : 𝐔(h), 𝐔(ghg⁻¹) → U(x)` are sc-diffeomorphisms with `s ∘ Φ̂(g) = Φ(g) ∘ s`,
`t ∘ Φ̂(g) = Φ(g) ∘ t` on `𝐔(h)`.

Choices:
- Setting as in my `RoundTrip/Blind/V7_21.lean`: `Obj Mor : Type` (universe 0), the project's
  `X : EpGroupoid Obj Mor`, `G_x = X.Isotropy x` (`g * h = g ∘ h`, checked by `rfl`), and "the
  natural `G_x`-action on `U(x)`" my `IsNatAction X x U Φ Γ` (Theorem 7.1's data; `U` open, not
  required connected — the project's `NaturalRep` requires connected `U`, so I did not use it).
- `𝐔(x) = {φ | s φ, t φ ∈ U}` (project's `X.morOn U`, `#print`ed).  `𝐔(h)` is not defined in the
  md; I read it as the sheet `𝐔(h) = Γ({h} × U(x)) = Γ(h, ·)(U)` (`sheetB`).
- `Φ̂` (`PhiHatB`): the text's formula with `h` the index of `φ` (`idxB`, chosen by
  `Classical.choose` among the `h` with `φ ∈ 𝐔(h)`; uniqueness is claim (i); `1` off `𝐔(x)`, a
  junk value — all claims are about `φ ∈ 𝐔(x)`).  `g ∗ z = Φ(g)(z)`.
- Claims (i)–(v) are asserted for EVERY natural action: (i) unique index and the two formulas;
  (ii) every `Φ̂(g)` is an sc-diffeomorphism of the open set `𝐔(x) ⊆ 𝐗` (`IsScDiffeoOn` of the
  morphism M-polyfold, some inverse) — the content of "`Φ̂ : G_x → Diff_sc(𝐔(x))`"; (iii) the
  homomorphism property `Φ̂(g₁g₂) = Φ̂(g₁) ∘ Φ̂(g₂)` on `𝐔(x)` (`Φ̂(1) = id` follows from (ii)
  and (iii)); (iv) `Φ̂(g)(𝐔(h)) = 𝐔(ghg⁻¹)`; (v) the formulas for `s`, `t`.
- "To sum up" (vi): "one can choose a small connected neighbourhood `U(x)`" is read as: inside
  every open `V ∋ x` there is a natural action on a connected `U ⊆ V` with: `𝐔(x) = ⋃_g 𝐔(g)`,
  the `𝐔(g)` pairwise disjoint, open and connected; for all `g, h`: `Φ̂(g)` maps `𝐔(h)`
  sc-diffeomorphically onto `𝐔(ghg⁻¹)`, `s, t : 𝐔(h) → U` are sc-diffeomorphisms (for every `h`,
  hence also for `ghg⁻¹`), and the two squares commute on `𝐔(h)` (`Φ(g)` being an
  sc-diffeomorphism of `U` is part of the natural action).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V7_23
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- The natural `G_x`-action on the open neighbourhood `U` of `x` (the data `Φ`, `Γ` of
Theorem 7.1 with its properties (1)–(3)), as in `RoundTrip/Blind/V7_21.lean`. -/
structure IsNatAction (X : EpGroupoid Obj Mor) (x : Obj) (U : Set Obj)
    (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor) : Prop where
  isOpen : IsOpen U
  mem : x ∈ U
  diffeo : ∀ g, ∃ ψ : Obj → Obj, X.PObj.IsScDiffeoOn X.PObj (Φ g) ψ U U
  hom : ∀ g h, ∀ y ∈ U, Φ (g * h) y = Φ g (Φ h y)
  smooth : ∀ g, X.PObj.IsScSmoothOn X.PMor (Γ g) U
  Γ_x : ∀ g, Γ g x = g.val
  src_tgt : ∀ g, ∀ y ∈ U, X.src (Γ g y) = y ∧ X.tgt (Γ g y) = Φ g y
  unique : ∀ h : Mor, X.src h ∈ U → X.tgt h ∈ U → ∃! g, Γ g (X.src h) = h

/-- The sheet `𝐔(h) = Γ({h} × U)`. -/
def sheetB (X : EpGroupoid Obj Mor) (x : Obj) (U : Set Obj) (Γ : X.Isotropy x → Obj → Mor)
    (h : X.Isotropy x) : Set Mor :=
  Γ h '' U

/-- The index `h` of `φ ∈ 𝐔(x)`: an `h` with `φ ∈ 𝐔(h)` (`1` if there is none). -/
noncomputable def idxB (X : EpGroupoid Obj Mor) (x : Obj) (U : Set Obj)
    (Γ : X.Isotropy x → Obj → Mor) (φ : Mor) : X.Isotropy x := by
  classical
  exact if hφ : ∃ h, φ ∈ sheetB X x U Γ h then hφ.choose else 1

/-- `Φ̂(g)(φ) = Γ(g h g⁻¹, g ∗ s(φ))` for `φ ∈ 𝐔(h)`. -/
noncomputable def PhiHatB (X : EpGroupoid Obj Mor) (x : Obj) (U : Set Obj)
    (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor) (g : X.Isotropy x)
    (φ : Mor) : Mor :=
  Γ (g * idxB X x U Γ φ * g⁻¹) (Φ g (X.src φ))

end

/-- `Φ̂ : G_x → Diff_sc(𝐔(x))` is a well-defined group homomorphism with
`Φ̂(g)(𝐔(h)) = 𝐔(ghg⁻¹)` and `s ∘ Φ̂(g) = Φ(g) ∘ s`, `t ∘ Φ̂(g) = Φ(g) ∘ t`; and for a small
connected `U(x)`, `𝐔(x)` is the disjoint union of the connected open sheets `𝐔(g)`, on which
`Φ̂(g)`, `s`, `t` are sc-diffeomorphisms forming commutative squares. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (x : Obj),
    (∀ (U : Set Obj) (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor),
      IsNatAction X x U Φ Γ →
      -- (i) unique index `h`, `φ = Γ(h, s φ)`, `t φ = Φ(h)(s φ)`
      (∀ φ ∈ X.morOn U, (∃! h, φ ∈ sheetB X x U Γ h) ∧
        ∀ h, φ ∈ sheetB X x U Γ h → φ = Γ h (X.src φ) ∧ X.tgt φ = Φ h (X.src φ)) ∧
      -- (ii) `Φ̂(g) ∈ Diff_sc(𝐔(x))`
      (∀ g, ∃ ψ : Mor → Mor,
        X.PMor.IsScDiffeoOn X.PMor (PhiHatB X x U Φ Γ g) ψ (X.morOn U) (X.morOn U)) ∧
      -- (iii) `Φ̂` is a group homomorphism
      (∀ g₁ g₂, ∀ φ ∈ X.morOn U,
        PhiHatB X x U Φ Γ (g₁ * g₂) φ = PhiHatB X x U Φ Γ g₁ (PhiHatB X x U Φ Γ g₂ φ)) ∧
      -- (iv) `Φ̂(g)(𝐔(h)) = 𝐔(g h g⁻¹)`
      (∀ g h, PhiHatB X x U Φ Γ g '' sheetB X x U Γ h = sheetB X x U Γ (g * h * g⁻¹)) ∧
      -- (v) `s(Φ̂(g)φ) = Φ(g)(s φ)`, `t(Φ̂(g)φ) = Φ(g)(t φ)`
      (∀ g, ∀ φ ∈ X.morOn U, X.src (PhiHatB X x U Φ Γ g φ) = Φ g (X.src φ) ∧
        X.tgt (PhiHatB X x U Φ Γ g φ) = Φ g (X.tgt φ))) ∧
    -- (vi) to sum up: a small connected `U(x)` with the sheet decomposition and the squares
    (∀ V : Set Obj, IsOpen V → x ∈ V →
      ∃ (U : Set Obj) (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor),
        IsNatAction X x U Φ Γ ∧ U ⊆ V ∧ IsConnected U ∧
        X.morOn U = ⋃ g, sheetB X x U Γ g ∧
        Pairwise (fun g h => Disjoint (sheetB X x U Γ g) (sheetB X x U Γ h)) ∧
        (∀ g, IsOpen (sheetB X x U Γ g) ∧ IsConnected (sheetB X x U Γ g)) ∧
        ∀ g h,
          (∃ ψ : Mor → Mor, X.PMor.IsScDiffeoOn X.PMor (PhiHatB X x U Φ Γ g) ψ
            (sheetB X x U Γ h) (sheetB X x U Γ (g * h * g⁻¹))) ∧
          (∃ σ : Obj → Mor, X.PMor.IsScDiffeoOn X.PObj X.src σ (sheetB X x U Γ h) U) ∧
          (∃ τ : Obj → Mor, X.PMor.IsScDiffeoOn X.PObj X.tgt τ (sheetB X x U Γ h) U) ∧
          (∀ φ ∈ sheetB X x U Γ h, X.src (PhiHatB X x U Φ Γ g φ) = Φ g (X.src φ) ∧
            X.tgt (PhiHatB X x U Φ Γ g φ) = Φ g (X.tgt φ)))

end RoundTrip.V7_23
