import GWMemoir.Skeleton

/-!
The groupoid of stable maps of HWZ, *Applications of Polyfold Theory I* (Memoirs AMS 248, no. 1179),
§1.1: objects the stable maps `(S, j, M, D, u)` of class `(k, δ)` into a fixed `(Q, ω)` with `m`
marked points, morphisms the equivalences `φ` with `u' ∘ φ = u` (Memoir Definition 1.4, pp. 3–4).
It is the groupoidal category of the book's Part IV (Definition 19.1.1, 2021 p. 863, which is
Definition 17.1.1 (1)–(3), 2021 p. 744), once the finiteness of the isomorphism sets
(`FiniteIsos'`) is given.

* `NodalSurface.Iso.refl`, `.trans`, `.symm`: identity, composition (chain rule for `mfderiv`),
  inverse (the derivative of `φ⁻¹` is the inverse of the derivative of `φ`).
* `StableMap.Iso.refl`, `.trans`, `.symm`, and the groupoid laws.
* `gwGroupoid om m k δ : GroupoidStr`, the structure maps `s, t, m, u, ι` of Definition 7.1.1.
* `gwCategory hfin : GroupoidalCategory.{1}`, with `hfin : FiniteIsos' m k δ` (for `k = 3` this is
  `FiniteIsos` of `GWMemoir.Skeleton`); `gwCategory_metrizable` plugs it into Skeleton §5.

The topology on `|C|` (the `GCT` of Definition 17.1.1) is not part of the data here: in the
memoir it comes from the good uniformizers (Memoir Theorem 1.6, through Theorem 19.5.3), as
`BasicConstruction.toGCTOfMetrizable` builds it.
-/

set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff
open Set Function

noncomputable section

namespace GWMemoir

open Polyfold

/-! ## Isomorphisms of noded Riemann surfaces -/

namespace NodalSurface

variable {m : ℕ} {X Y Z : NodalSurface m}

@[ext]
theorem Iso.ext {f g : Iso X Y} (h : ∀ x, f.φ x = g.φ x) : f = g := by
  obtain ⟨φ, _, _, _⟩ := f
  obtain ⟨ψ, _, _, _⟩ := g
  obtain rfl : φ = ψ := Diffeomorph.ext h
  rfl

theorem Iso.mdifferentiableAt (f : Iso X Y) (x : X.S) :
    MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E2) f.φ x :=
  f.φ.contMDiffAt.mdifferentiableAt (by simp)

/-- The identity of a noded Riemann surface. -/
def Iso.refl (X : NodalSurface m) : Iso X X where
  φ := Diffeomorph.refl _ _ _
  holo x := by
    rw [Diffeomorph.coe_refl, mfderiv_id]
    rfl
  marked _ := rfl
  nodes := by
    rw [Diffeomorph.coe_refl, Sym2.map_id, Set.image_id]

/-- The holomorphy of an isomorphism, applied to a vector (at a point `y = φ x`). -/
theorem Iso.holo_apply (f : Iso X Y) {x : X.S} {y : Y.S} (h : f.φ x = y) (v : E2) :
    mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) f.φ x (X.j.J x v) =
      Y.j.J y (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) f.φ x v) := by
  subst h
  exact congrArg (fun L => L v) (f.holo x)

/-- The composition `g ∘ f`: by the chain rule `T(g ∘ f) = Tg ∘ Tf`, it is again holomorphic. -/
def Iso.trans (f : Iso X Y) (g : Iso Y Z) : Iso X Z where
  φ := f.φ.trans g.φ
  holo x := by
    rw [Diffeomorph.coe_trans, mfderiv_comp x (g.mdifferentiableAt _) (f.mdifferentiableAt x)]
    refine ContinuousLinearMap.ext fun v => ?_
    show mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) g.φ (f.φ x) (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) f.φ x (X.j.J x v)) =
      Z.j.J (g.φ (f.φ x)) (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) g.φ (f.φ x)
        (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) f.φ x v))
    rw [f.holo_apply rfl]
    exact g.holo_apply rfl _
  marked i := by
    simp only [Diffeomorph.coe_trans, Function.comp_apply, f.marked, g.marked]
  nodes := by
    rw [Diffeomorph.coe_trans, ← g.nodes, ← f.nodes, Set.image_image]
    congr 1
    funext p
    rw [Sym2.map_map]

/-- `T(φ⁻¹)_{φ x} ∘ Tφ_x = id` and `Tφ_x ∘ T(φ⁻¹)_{φ x} = id`. -/
theorem Iso.mfderiv_symm_comp (f : Iso X Y) (x : X.S) (v : E2) :
    mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) f.φ.symm (f.φ x) (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) f.φ x v) = v := by
  have hs : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E2) f.φ.symm (f.φ x) :=
    f.φ.symm.contMDiffAt.mdifferentiableAt (by simp)
  have h := mfderiv_comp x hs (f.mdifferentiableAt x)
  have hid : (f.φ.symm : Y.S → X.S) ∘ f.φ = id := funext f.φ.symm_apply_apply
  rw [hid, mfderiv_id] at h
  exact (congrArg (fun L => L v) h).symm

theorem Iso.mfderiv_symm_comp' (f : Iso X Y) {x : X.S} {y : Y.S} (h : f.φ x = y) (v : E2) :
    mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) f.φ.symm y (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) f.φ x v) = v := by
  subst h
  exact f.mfderiv_symm_comp x v

theorem Iso.mfderiv_comp_symm (f : Iso X Y) (y : Y.S) (v : E2) :
    mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) f.φ (f.φ.symm y) (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) f.φ.symm y v) = v := by
  have hs : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E2) f.φ.symm y :=
    f.φ.symm.contMDiffAt.mdifferentiableAt (by simp)
  have h := mfderiv_comp y (f.mdifferentiableAt (f.φ.symm y)) hs
  have hid : (f.φ : X.S → Y.S) ∘ f.φ.symm = id := funext f.φ.apply_symm_apply
  rw [hid, mfderiv_id] at h
  exact (congrArg (fun L => L v) h).symm

/-- The inverse isomorphism: `T(φ⁻¹) = (Tφ)⁻¹` intertwines `j'` and `j`. -/
def Iso.symm (f : Iso X Y) : Iso Y X where
  φ := f.φ.symm
  holo y := by
    refine ContinuousLinearMap.ext fun v => ?_
    show mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) f.φ.symm y (Y.j.J y v) =
      X.j.J (f.φ.symm y) (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) f.φ.symm y v)
    -- `B (j' v) = B (j' (A (B v))) = B (A (j (B v))) = j (B v)`
    have hy : f.φ (f.φ.symm y) = y := f.φ.apply_symm_apply y
    refine (congrArg (fun w : E2 => mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) f.φ.symm y (Y.j.J y w))
      (f.mfderiv_comp_symm y v).symm).trans ?_
    refine (congrArg (fun w : E2 => mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) f.φ.symm y w)
      (f.holo_apply hy _).symm).trans ?_
    exact f.mfderiv_symm_comp' hy _
  marked i := by
    rw [← f.marked i]
    exact f.φ.symm_apply_apply _
  nodes := by
    rw [← f.nodes, Set.image_image]
    convert Set.image_id X.nodes using 2
    rename_i p _
    rw [Sym2.map_map]
    have hid : (f.φ.symm : Y.S → X.S) ∘ f.φ = id := funext f.φ.symm_apply_apply
    rw [hid, Sym2.map_id]

@[simp] theorem Iso.refl_apply (x : X.S) : (Iso.refl X).φ x = x := rfl
@[simp] theorem Iso.trans_apply (f : Iso X Y) (g : Iso Y Z) (x : X.S) :
    (f.trans g).φ x = g.φ (f.φ x) := rfl
@[simp] theorem Iso.symm_apply_apply (f : Iso X Y) (x : X.S) : f.symm.φ (f.φ x) = x :=
  f.φ.symm_apply_apply x
@[simp] theorem Iso.apply_symm_apply (f : Iso X Y) (y : Y.S) : f.φ (f.symm.φ y) = y :=
  f.φ.apply_symm_apply y

end NodalSurface

/-! ## Isomorphisms of stable maps -/

section StableMaps

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  {om : SymplecticForm E Q} {m k : ℕ} {δ : ℝ}

namespace StableMap

variable {α β γ : StableMap om m k δ}

@[ext]
theorem Iso.ext {f g : Iso α β} (h : ∀ x, f.φ.φ x = g.φ.φ x) : f = g := by
  obtain ⟨φ, _⟩ := f
  obtain ⟨ψ, _⟩ := g
  obtain rfl : φ = ψ := NodalSurface.Iso.ext h
  rfl

/-- The identity of a stable map. -/
def Iso.refl (α : StableMap om m k δ) : Iso α α := ⟨NodalSurface.Iso.refl _, fun _ => rfl⟩

/-- The composition of isomorphisms of stable maps. -/
def Iso.trans (f : Iso α β) (g : Iso β γ) : Iso α γ :=
  ⟨f.φ.trans g.φ, fun x => (g.comm _).trans (f.comm x)⟩

/-- The inverse of an isomorphism of stable maps. -/
def Iso.symm (f : Iso α β) : Iso β α :=
  ⟨f.φ.symm, fun y => by
    rw [← f.comm (f.φ.symm.φ y), NodalSurface.Iso.apply_symm_apply]⟩

@[simp] theorem Iso.trans_refl (f : Iso α β) : f.trans (Iso.refl β) = f := by ext; rfl
@[simp] theorem Iso.refl_trans (f : Iso α β) : (Iso.refl α).trans f = f := by ext; rfl
theorem Iso.trans_assoc {δ' : StableMap om m k δ} (f : Iso α β) (g : Iso β γ) (h : Iso γ δ') :
    (f.trans g).trans h = f.trans (g.trans h) := by ext; rfl
@[simp] theorem Iso.trans_symm (f : Iso α β) : f.trans f.symm = Iso.refl α := by
  ext x; exact f.φ.symm_apply_apply x
@[simp] theorem Iso.symm_trans (f : Iso α β) : f.symm.trans f = Iso.refl β := by
  ext x; exact f.φ.apply_symm_apply x

end StableMap

/-! ## The groupoid and the groupoidal category -/

variable (om) (m k δ)

/-- The morphisms of the groupoid of stable maps: triples `(α, β, f : α → β)`. -/
abbrev GWMor := Σ α β : StableMap om m k δ, StableMap.Iso α β

variable {om m k δ}

/-- Composition of composable triples: `src φ = tgt ψ`. -/
def GWMor.compAux : ∀ (φ ψ : GWMor om m k δ), φ.1 = ψ.2.1 → GWMor om m k δ
  | ⟨_, γ, f⟩, ⟨α, _, g⟩, rfl => ⟨α, γ, g.trans f⟩

open Classical in
/-- The total composition `m(φ, ψ) = φ ∘ ψ`, the first argument off the composable pairs (as for
the full subcategories of Chapter 7). -/
def GWMor.comp (φ ψ : GWMor om m k δ) : GWMor om m k δ :=
  if h : φ.1 = ψ.2.1 then GWMor.compAux φ ψ h else φ

theorem GWMor.comp_mk {α β γ : StableMap om m k δ} (f : StableMap.Iso β γ)
    (g : StableMap.Iso α β) : GWMor.comp ⟨β, γ, f⟩ ⟨α, β, g⟩ = ⟨α, γ, g.trans f⟩ := by
  rw [GWMor.comp, dif_pos rfl]
  rfl

variable (om m k δ)

/-- **Memoir Definition 1.4, p. 4** as a groupoid (Definition 7.1.1, 2021): objects the stable
maps of class `(k, δ)`, morphisms their equivalences; `|C|` is the set of stable curves (for
`(k, δ) = (3, δ₀)`, the space `Z` of Memoir Definition 1.5). -/
def gwGroupoid : GroupoidStr (StableMap om m k δ) (GWMor om m k δ) where
  src φ := φ.1
  tgt φ := φ.2.1
  comp := GWMor.comp
  unit α := ⟨α, α, StableMap.Iso.refl α⟩
  inv φ := ⟨φ.2.1, φ.1, φ.2.2.symm⟩
  src_comp := by
    rintro ⟨β, γ, f⟩ ⟨α, β', g⟩ (h : β = β')
    subst h
    rw [GWMor.comp_mk]
  tgt_comp := by
    rintro ⟨β, γ, f⟩ ⟨α, β', g⟩ (h : β = β')
    subst h
    rw [GWMor.comp_mk]
  comp_assoc := by
    rintro ⟨γ, δ', f⟩ ⟨β, γ', g⟩ ⟨α, β', h⟩ (e1 : γ = γ') (e2 : β = β')
    subst e1 e2
    rw [GWMor.comp_mk, GWMor.comp_mk, GWMor.comp_mk, GWMor.comp_mk,
      StableMap.Iso.trans_assoc]
  src_unit _ := rfl
  tgt_unit _ := rfl
  comp_unit := by
    rintro ⟨α, β, f⟩
    show GWMor.comp ⟨α, β, f⟩ ⟨α, α, StableMap.Iso.refl α⟩ = _
    rw [GWMor.comp_mk, StableMap.Iso.refl_trans]
  unit_comp := by
    rintro ⟨α, β, f⟩
    show GWMor.comp ⟨β, β, StableMap.Iso.refl β⟩ ⟨α, β, f⟩ = _
    rw [GWMor.comp_mk, StableMap.Iso.trans_refl]
  src_inv _ := rfl
  tgt_inv _ := rfl
  comp_inv := by
    rintro ⟨α, β, f⟩
    show GWMor.comp ⟨α, β, f⟩ ⟨β, α, f.symm⟩ = _
    rw [GWMor.comp_mk, StableMap.Iso.symm_trans]
  inv_comp := by
    rintro ⟨α, β, f⟩
    show GWMor.comp ⟨β, α, f.symm⟩ ⟨α, β, f⟩ = _
    rw [GWMor.comp_mk, StableMap.Iso.trans_symm]

/-- `mor(α, β)` of the groupoid is the set of isomorphisms `α → β`. -/
theorem gwGroupoid_mor (α β : StableMap om m k δ) :
    (gwGroupoid om m k δ).mor α β = range fun f : StableMap.Iso α β => (⟨α, β, f⟩ : GWMor om m k δ) := by
  ext ⟨α', β', f⟩
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨f, rfl⟩
  · rintro ⟨g, hg⟩
    cases hg
    exact ⟨rfl, rfl⟩

theorem gwGroupoid_isomorphic_iff (α β : StableMap om m k δ) :
    (gwGroupoid om m k δ).Isomorphic α β ↔ Nonempty (StableMap.Iso α β) := by
  constructor
  · rintro ⟨⟨α', β', f⟩, rfl, rfl⟩
    exact ⟨f⟩
  · rintro ⟨f⟩
    exact ⟨⟨α, β, f⟩, rfl, rfl⟩

variable {om} in
/-- `FiniteIsos` (for all `k`, `δ`): every set of isomorphisms between two stable maps is finite,
the classical input of Definition 19.1.1 (2).  The memoir states it as a consequence of the
stability condition (§3.1, p. 62: the automorphism group of a stable map is finite); for two
isomorphic stable maps `Iso α β` is a torsor under `Iso α α`. -/
def FiniteIsos' (m k : ℕ) (δ : ℝ) : Prop :=
  ∀ α β : StableMap om m k δ, Finite (StableMap.Iso α β)

theorem finiteIsos'_iff (δ₀ : ℝ) : FiniteIsos' (om := om) m 3 δ₀ ↔ FiniteIsos om m δ₀ := Iff.rfl

variable {om m k δ} in
/-- **The groupoidal category of stable maps** (Definition 19.1.1, 2021 p. 863; Definition 17.1.1
(1)–(3), 2021 p. 744): the groupoid `gwGroupoid` with the finiteness of its morphism sets. -/
def gwCategory (hfin : FiniteIsos' (om := om) m k δ) : GroupoidalCategory.{1} where
  Obj := StableMap om m k δ
  Mor := GWMor om m k δ
  toGroupoidStr := gwGroupoid om m k δ
  finite_mor α β := by
    rw [gwGroupoid_mor]
    have := hfin α β
    exact Set.finite_range _

/-- The orbit space `|C|` of `gwCategory` is the set of isomorphism classes of stable maps. -/
theorem gwCategory_π_eq_iff (hfin : FiniteIsos' (om := om) m k δ) (α β : StableMap om m k δ) :
    (gwCategory hfin).π α = (gwCategory hfin).π β ↔ Nonempty (StableMap.Iso α β) :=
  ((gwCategory hfin).π_eq_π_iff).trans (gwGroupoid_isomorphic_iff om m k δ α β)

/-- The category of Skeleton §5 is `gwCategory` for `k = 3`: the reduction of Memoir Theorems 3.22
and 1.6 (second countable) to metrizability (Proposition 19.4.2, Theorem 19.5.3 (1)) applies to
every uniformizer construction on it. -/
theorem gwCategory_metrizable (δ₀ : ℝ) (hfin : FiniteIsos om m δ₀)
    (U : (gwCategory (k := 3) (δ := δ₀) hfin).UniformizerConstruction)
    (T : U.TransitionData) (hB : U.HasClassUniformizers)
    (h322 : Theorem_3_22 U T) (h16 : Theorem_1_6_sc U T hB) :
    @TopologicalSpace.MetrizableSpace (gwCategory (k := 3) (δ := δ₀) hfin).OrbitSpace
      ((basicOf U T).natTop hB) :=
  metrizable_of_theorem_3_22 U T hB h322 h16

end StableMaps

end GWMemoir
