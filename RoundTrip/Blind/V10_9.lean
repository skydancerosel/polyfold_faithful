import Polyfold
/-! Blind formalization of V10_9 (the text's Part II, §10.1, Remark 10.1.12, p. 472 of the
Springer 2021 book; new in the 2021 edition).

Text: for an equivalence `F` and `ψ : F(x) → y`, `g ↦ ψ ∘ F(g) ∘ ψ⁻¹` is an isomorphism
`G_x → G_y` mapping `T_x` onto `T_y`.

Choices:
- Setting: ep-groupoids `X : EpGroupoid Obj Mor`, `Y : EpGroupoid Obj' Mor'`, all four spaces in
  `Type` (universe 0), Hausdorff and paracompact (`RoundTrip/Blind/V7_3.lean`); `F : X → Y` an
  sc-smooth functor (the project's `EpFunctor`).
- "equivalence": my `IsEquivB` (Definition 10.1.1), copied from `RoundTrip/Blind/V10_1.lean`.
- `x ∈ X`, `y ∈ Y` and `ψ` with `s ψ = F x`, `t ψ = y`, all arbitrary.
- `G_x`: the project's isotropy group `X.Isotropy x` (morphisms `x → x`; checked by `rfl` that
  its product is composition, `(g * h).val = g.val ∘ h.val`, and its unit `1_x`).
- `T_x ⊆ G_x`: the project's `X.trivialSubgroup x`, the `g` acting trivially (`Φ(g) = id` on `U`
  for some natural representation `(U, Φ, Γ)` of Theorem 7.1 with `U` open and connected; read
  with `#print`), the notion of `RoundTrip/Blind/V7_38.lean`.
- "`g ↦ ψ ∘ F(g) ∘ ψ⁻¹` is an isomorphism": there is a group isomorphism `c : G_x ≃* G_y` whose
  underlying morphism is `ψ ∘ F(g) ∘ ψ⁻¹` (project's `comp a b = a ∘ b`, first `b`).  "mapping
  `T_x` onto `T_y`": `c(T_x) = T_y`, stated (`c` being bijective) as `g ∈ T_x ↔ c g ∈ T_y`.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_9
open Polyfold

universe u v

section
variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']

/-- `x ≅ y` in the groupoid `G`: there is a morphism `x → y`. -/
def IsoRelB {O M : Type u} (G : GroupoidStr O M) (x y : O) : Prop :=
  ∃ φ : M, G.src φ = x ∧ G.tgt φ = y

/-- The orbit space `|G|`, the objects modulo `≅`, with the quotient topology. -/
abbrev OrbB {O M : Type u} (G : GroupoidStr O M) : Type u :=
  Quot (IsoRelB G)

/-- `F` is full and faithful: `φ ↦ F φ` is a bijection `mor(x, x') → mor(F x, F x')`. -/
def FullyFaithfulB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F : EpFunctor X Y) :
    Prop :=
  (∀ φ φ' : Mor, X.src φ = X.src φ' → X.tgt φ = X.tgt φ' → F.mor φ = F.mor φ' → φ = φ') ∧
  (∀ (x x' : Obj) (ψ : Mor'), Y.src ψ = F.obj x → Y.tgt ψ = F.obj x' →
    ∃ φ : Mor, X.src φ = x ∧ X.tgt φ = x' ∧ F.mor φ = ψ)

/-- The induced map `|F| : |X| → |Y|`, `|x| ↦ |F x|`, is a homeomorphism. -/
def OrbitHomeoB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F : EpFunctor X Y) :
    Prop :=
  ∃ e : OrbB X.toGroupoidStr ≃ₜ OrbB Y.toGroupoidStr,
    ∀ x : Obj, e (Quot.mk _ x) = Quot.mk _ (F.obj x)

/-- `F` is a local sc-diffeomorphism on objects. -/
def LocalScDiffeoObjB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F : EpFunctor X Y) :
    Prop :=
  ∀ x : Obj, ∃ (U : Set Obj) (V : Set Obj') (g : Obj' → Obj),
    x ∈ U ∧ X.PObj.IsScDiffeoOn Y.PObj F.obj g U V

/-- **Definition 10.1.1**: `F` is an equivalence. -/
def IsEquivB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F : EpFunctor X Y) : Prop :=
  FullyFaithfulB F ∧ OrbitHomeoB F ∧ LocalScDiffeoObjB F

end

/-- Remark 10.1.12: for an equivalence `F` and `ψ : F(x) → y`, conjugation `g ↦ ψ ∘ F(g) ∘ ψ⁻¹`
is an isomorphism `G_x ≅ G_y` mapping `T_x` onto `T_y`. -/
def B : Prop :=
  ∀ (Obj Mor Obj' Mor' : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (F : EpFunctor X Y),
    IsEquivB F →
    ∀ (x : Obj) (y : Obj') (ψ : Mor'), Y.src ψ = F.obj x → Y.tgt ψ = y →
      ∃ c : X.Isotropy x ≃* Y.Isotropy y,
        (∀ g : X.Isotropy x, (c g).val = Y.comp ψ (Y.comp (F.mor g.val) (Y.inv ψ))) ∧
        (∀ g : X.Isotropy x, g ∈ X.trivialSubgroup x ↔ c g ∈ Y.trivialSubgroup y)

end RoundTrip.V10_9
