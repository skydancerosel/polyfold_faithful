import Polyfold.Chapter6.TransportOrientationSpace

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 6, §6.6,
**Theorem 6.6.17**, p. 275, and the orientation space `O_f` (pp. 274–275): two descriptions of
the fibres give the same space.

# Fibrewise bijections which commute with the transports

## The text, paraphrased

The orientation space `O_f` consists of the pairs `(x, o)` of a smooth point `x` and an
orientation `o` of `DET(f, x)`; its topology is the one in which the sections carried along by
the propagation of orientations along sc-smooth paths are continuous (Theorem 6.6.17).  The
set `Or_x^f` of orientations of `DET(f, x)` can be described with different families of
linearizations (for instance with sc⁺-sections defined on all of `X` or near `x` only); the
descriptions are identified by canonical bijections.

## What is formalized

For two families of fibres `O`, `O'` over the smooth points of an M-polyfold with local
transport data `L`, `L'` and a family of bijections `ρ_x : O x ≃ O' x` which commutes with the
transports along all sc-smooth paths (`LocalTransport.Intertwines`):

* `Intertwines.isContOn_iff`, `Intertwines.isContOn_symm_iff`: the sections carried along by
  the transports correspond.
* `Intertwines.totalEquiv`, `Intertwines.totalHomeomorph`: **`(x, o) ↦ (x, ρ_x o)` is a
  homeomorphism of the total spaces** for the topologies `L.topology`, `L'.topology`; it
  commutes with the projections to `X_∞` (`proj_totalHomeomorph`) and carries the section of
  `o` to the section of `ρ o` (`totalHomeomorph_sec`).
* `Intertwines.symm`, `Intertwines.refl`, `Intertwines.trans`.
* `isContOrOn_iff_isContOn`, `orTopology_eq_topology`: for `O = Or^f` the notions of
  `OrientationSpace.lean` are those of the total space of the local transport data.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u v v' v''

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {O : ∀ x : X, x ∈ PX.smoothSet → Type v} {O' : ∀ x : X, x ∈ PX.smoothSet → Type v'}
  {O'' : ∀ x : X, x ∈ PX.smoothSet → Type v''}

namespace LocalTransport

/-- **A family of fibrewise bijections commuting with the transports**: for every sc-smooth
path `γ` from `x₀` to `x₁`, `ρ_{x₁} ∘ T_γ = T'_γ ∘ ρ_{x₀}`. -/
def Intertwines (L : LocalTransport PX O) (L' : LocalTransport PX O')
    (ρ : ∀ x (hs : x ∈ PX.smoothSet), O x hs ≃ O' x hs) : Prop :=
  ∀ (γ : (Fin 1 → ℝ) → X) (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) {x₀ x₁ : X}
    (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet) (a : O x₀ hs₀),
    ρ x₁ hs₁ (L.transport γ hγ h₀ h₁ hs₀ hs₁ a) =
      L'.transport γ hγ h₀ h₁ hs₀ hs₁ (ρ x₀ hs₀ a)

namespace Intertwines

variable {L : LocalTransport PX O} {L' : LocalTransport PX O'} {L'' : LocalTransport PX O''}
  {ρ : ∀ x (hs : x ∈ PX.smoothSet), O x hs ≃ O' x hs}

/-- The identity commutes with the transports. -/
theorem refl (L : LocalTransport PX O) : L.Intertwines L fun _ _ => Equiv.refl _ :=
  fun _ _ _ _ _ _ _ _ _ => rfl

/-- The inverse bijections commute with the transports. -/
theorem symm (h : L.Intertwines L' ρ) : L'.Intertwines L fun x hs => (ρ x hs).symm :=
  fun γ hγ _ _ h₀ h₁ hs₀ hs₁ a => by
    have e := h γ hγ h₀ h₁ hs₀ hs₁ ((ρ _ hs₀).symm a)
    rw [Equiv.apply_symm_apply] at e
    exact (Equiv.symm_apply_eq _).2 e.symm

/-- Composites of bijections commuting with the transports commute with the transports. -/
theorem trans {ρ' : ∀ x (hs : x ∈ PX.smoothSet), O' x hs ≃ O'' x hs} (h : L.Intertwines L' ρ)
    (h' : L'.Intertwines L'' ρ') : L.Intertwines L'' fun x hs => (ρ x hs).trans (ρ' x hs) :=
  fun γ hγ _ _ h₀ h₁ hs₀ hs₁ a =>
    (congrArg (ρ' _ hs₁) (h γ hγ h₀ h₁ hs₀ hs₁ a)).trans (h' γ hγ h₀ h₁ hs₀ hs₁ _)

/-- **The sections carried along by the transports correspond**: `o` is carried along by the
transport of `L` along the sc-smooth paths in `U` iff `ρ o` is carried along by that of `L'`. -/
theorem isContOn_iff (h : L.Intertwines L' ρ) (U : Set X)
    (o : ∀ y (hy : y ∈ PX.smoothSet), O y hy) :
    L.IsContOn U o ↔ L'.IsContOn U fun y hy => ρ y hy (o y hy) :=
  ⟨fun ho => ⟨ho.1, fun γ hγ hγU _ _ h₀ h₁ hs₀ hs₁ =>
      (h γ hγ h₀ h₁ hs₀ hs₁ _).symm.trans (congrArg (ρ _ hs₁) (ho.2 γ hγ hγU h₀ h₁ hs₀ hs₁))⟩,
    fun ho => ⟨ho.1, fun γ hγ hγU _ _ h₀ h₁ hs₀ hs₁ =>
      (ρ _ hs₁).injective ((h γ hγ h₀ h₁ hs₀ hs₁ _).trans (ho.2 γ hγ hγU h₀ h₁ hs₀ hs₁))⟩⟩

/-- The same for a section of the second family and its preimage. -/
theorem isContOn_symm_iff (h : L.Intertwines L' ρ) (U : Set X)
    (o' : ∀ y (hy : y ∈ PX.smoothSet), O' y hy) :
    L.IsContOn U (fun y hy => (ρ y hy).symm (o' y hy)) ↔ L'.IsContOn U o' := by
  have e : (fun y hy => ρ y hy ((ρ y hy).symm (o' y hy))) = o' :=
    funext fun y => funext fun hy => (ρ y hy).apply_symm_apply _
  have h1 := h.isContOn_iff U fun y hy => (ρ y hy).symm (o' y hy)
  rw [e] at h1
  exact h1

variable (L L') in
/-- **The bijection of the total spaces** `(x, o) ↦ (x, ρ_x o)`. -/
def totalEquiv (ρ : ∀ x (hs : x ∈ PX.smoothSet), O x hs ≃ O' x hs) : L.Total ≃ L'.Total :=
  Equiv.sigmaCongrRight fun x => ρ (PX.smoothVal x) (PX.smoothVal_mem x)

@[simp] theorem totalEquiv_fst (p : L.Total) : (totalEquiv L L' ρ p).1 = p.1 := rfl

@[simp] theorem totalEquiv_symm_fst (p : L'.Total) : ((totalEquiv L L' ρ).symm p).1 = p.1 :=
  rfl

/-- The bijection of the total spaces commutes with the projections to `X_∞`. -/
theorem proj_totalEquiv (p : L.Total) : L'.proj (totalEquiv L L' ρ p) = L.proj p := rfl

/-- The bijection of the total spaces carries the section of `o` to the section of `ρ o`. -/
theorem totalEquiv_sec (o : ∀ y (hy : y ∈ PX.smoothSet), O y hy) (y : PX.SmoothLevel) :
    totalEquiv L L' ρ (L.sec o y) = L'.sec (fun y hy => ρ y hy (o y hy)) y := rfl

theorem totalEquiv_symm_sec (o' : ∀ y (hy : y ∈ PX.smoothSet), O' y hy) (y : PX.SmoothLevel) :
    (totalEquiv L L' ρ).symm (L'.sec o' y) = L.sec (fun y hy => (ρ y hy).symm (o' y hy)) y :=
  rfl

/-- `(x, o) ↦ (x, ρ_x o)` is continuous for the topologies of the total spaces. -/
theorem continuous_totalEquiv (h : L.Intertwines L' ρ) :
    @Continuous _ _ L.topology L'.topology (totalEquiv L L' ρ) :=
  @Continuous.mk _ _ L.topology L'.topology _ fun _ hW U o ho =>
    hW U _ ((h.isContOn_iff U o).1 ho)

/-- The inverse of `(x, o) ↦ (x, ρ_x o)` is continuous. -/
theorem continuous_totalEquiv_symm (h : L.Intertwines L' ρ) :
    @Continuous _ _ L'.topology L.topology (totalEquiv L L' ρ).symm := by
  refine @Continuous.mk _ _ L'.topology L.topology _ fun W hW U o' ho' => ?_
  exact hW U _ ((h.isContOn_symm_iff U o').2 ho')

/-- **The homeomorphism of the total spaces** `(x, o) ↦ (x, ρ_x o)` for a family of fibrewise
bijections which commutes with the transports. -/
def totalHomeomorph (h : L.Intertwines L' ρ) :
    @Homeomorph L.Total L'.Total L.topology L'.topology :=
  letI := L.topology
  letI := L'.topology
  { toEquiv := totalEquiv L L' ρ
    continuous_toFun := h.continuous_totalEquiv
    continuous_invFun := h.continuous_totalEquiv_symm }

theorem totalHomeomorph_apply (h : L.Intertwines L' ρ) (p : L.Total) :
    h.totalHomeomorph p = ⟨p.1, ρ _ _ p.2⟩ := rfl

/-- The homeomorphism of the total spaces commutes with the projections to `X_∞`. -/
theorem proj_totalHomeomorph (h : L.Intertwines L' ρ) (p : L.Total) :
    L'.proj (h.totalHomeomorph p) = L.proj p := rfl

/-- The homeomorphism of the total spaces carries the section of `o` to the section of
`ρ o`. -/
theorem totalHomeomorph_sec (h : L.Intertwines L' ρ) (o : ∀ y (hy : y ∈ PX.smoothSet), O y hy)
    (y : PX.SmoothLevel) :
    h.totalHomeomorph (L.sec o y) = L'.sec (fun y hy => ρ y hy (o y hy)) y := rfl

end Intertwines

end LocalTransport

/-! ### The orientation space of an sc-Fredholm section as a total space -/

section Orx

variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y} {hf : B.IsScFredholmSection f}
  (L : LocalTransport PX fun x hs => Orx f hf x hs)

/-- A continuous orientation over `U` is a section carried along by the transport over `U`. -/
theorem isContOrOn_iff_isContOn (U : Set X) (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy) :
    IsContOrOn L U o ↔ L.IsContOn U o := Iff.rfl

/-- The topology of `O_f` is the topology of the total space of the local transport data. -/
theorem orTopology_eq_topology : orTopology L = L.topology := rfl

end Orx

end Polyfold
