import Polyfold
/-! Blind formalization of V7_64 (the 2017 book's Part II, §7.5.1, Lemma 7.9, p. 254).

Text: if `U₁` is the open neighbourhood of `x₀` guaranteed by Lemma 7.8, there is an open
neighbourhood `U₂ ⊆ U₁` of `x₀` such that the open neighbourhood
`U := ⋃_{g ∈ G_{x₀}} t_g ∘ s_g⁻¹(U₂)` of `x₀` is contained in `U₁` and invariant under all the
maps `t_g ∘ s_g⁻¹`, `g ∈ G_{x₀}`.

Choices:
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files), with the instances of the
  project's `EpGroupoid`, `X : EpGroupoid Obj Mor` (the project's Definition 7.3, fields read
  with `#print`, as in `RoundTrip/Blind/V7_49.lean`); `G_{x₀}` is the project's `X.Isotropy x₀`.
- The choices of the proof of Theorem 7.5 (`IsChoicesB`, as in `RoundTrip/Blind/V7_63.lean`):
  open `U₀ ∋ x₀`; open `N^s_g, N^t_g ∋ g` on which `s`, resp. `t`, is an sc-diffeomorphism onto
  `U₀`; the `N^s_g ∪ N^t_g` pairwise disjoint.  `N_g := N^s_g ∩ N^t_g`, `s_g = s|N_g`,
  `t_g = t|N_g`.  The contractibility of `N^s_g, N^t_g` in the text's choices is left out, as in
  V7_63 (unused here; keeping it risked a vacuous hypothesis; without it B is stronger).
- "`U₁` guaranteed by Lemma 7.8": any `U₁` with the properties Lemma 7.8 states (open, `x₀ ∈ U₁`,
  `U₁ ⊆ U₀`, every morphism with source and target in `U₁` lies in some `N_g`) — a hypothesis.
- `s_g` is a bijection of `N_g` onto `s(N_g)` (injective as `s|N^s_g` is), so for `A ⊆ s(N_g)`:
  `t_g ∘ s_g⁻¹(A) = t(N_g ∩ s⁻¹(A))`.  This is how I write the images, without naming `s_g⁻¹`.
- Domains: `t_g ∘ s_g⁻¹` is defined on `s(N_g)`.  I read the statement as presupposing
  `U₂ ⊆ s(N_g)` for all `g` (so that `t_g ∘ s_g⁻¹(U₂)` is an image of all of `U₂`), and
  "`U` invariant under `t_g ∘ s_g⁻¹`" as: `U ⊆ s(N_g)` (the map is defined on `U`) and
  `t_g ∘ s_g⁻¹(U) ⊆ U`.
- "the open neighbourhood `U` of `x₀`": I include `IsOpen U` and `x₀ ∈ U` as claims (the text
  presupposes them; they hold).
- Nothing looks false to me.
-/
namespace RoundTrip.V7_64
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- The choices of the proof of Theorem 7.5: `U₀ ∋ x₀` open; open `N^s_g, N^t_g ∋ g` on which
`s`, resp. `t`, is an sc-diffeomorphism onto `U₀`; the `N^s_g ∪ N^t_g` pairwise disjoint. -/
def IsChoicesB (X : EpGroupoid Obj Mor) (x₀ : Obj) (U₀ : Set Obj)
    (Ns Nt : X.Isotropy x₀ → Set Mor) : Prop :=
  IsOpen U₀ ∧ x₀ ∈ U₀ ∧
  (∀ g, IsOpen (Ns g) ∧ IsOpen (Nt g) ∧ g.val ∈ Ns g ∧ g.val ∈ Nt g) ∧
  (∀ g, ∃ σ : Obj → Mor, X.PMor.IsScDiffeoOn X.PObj X.src σ (Ns g) U₀) ∧
  (∀ g, ∃ τ : Obj → Mor, X.PMor.IsScDiffeoOn X.PObj X.tgt τ (Nt g) U₀) ∧
  Pairwise (Function.onFun Disjoint (fun g => Ns g ∪ Nt g))

/-- `U₁` has the properties of Lemma 7.8. -/
def IsLemma78NbhdB (X : EpGroupoid Obj Mor) (x₀ : Obj) (U₀ : Set Obj)
    (Ns Nt : X.Isotropy x₀ → Set Mor) (U₁ : Set Obj) : Prop :=
  IsOpen U₁ ∧ x₀ ∈ U₁ ∧ U₁ ⊆ U₀ ∧
    ∀ h : Mor, X.src h ∈ U₁ → X.tgt h ∈ U₁ → ∃ g, h ∈ Ns g ∩ Nt g

/-- `t_g ∘ s_g⁻¹(A) = t(N_g ∩ s⁻¹(A))`, `N_g = N^s_g ∩ N^t_g`. -/
def hatImage (X : EpGroupoid Obj Mor) {x₀ : Obj} (Ns Nt : X.Isotropy x₀ → Set Mor)
    (g : X.Isotropy x₀) (A : Set Obj) : Set Obj :=
  X.tgt '' (Ns g ∩ Nt g ∩ X.src ⁻¹' A)

end

/-- Lemma 7.9: a small `U₂` whose orbit `U = ⋃_g t_g s_g⁻¹(U₂)` lies in `U₁` and is invariant. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (x₀ : Obj) (U₀ : Set Obj) (Ns Nt : X.Isotropy x₀ → Set Mor) (U₁ : Set Obj),
    IsChoicesB X x₀ U₀ Ns Nt → IsLemma78NbhdB X x₀ U₀ Ns Nt U₁ →
    ∃ U₂ : Set Obj, IsOpen U₂ ∧ x₀ ∈ U₂ ∧ U₂ ⊆ U₁ ∧
      (∀ g, U₂ ⊆ X.src '' (Ns g ∩ Nt g)) ∧
      IsOpen (⋃ g, hatImage X Ns Nt g U₂) ∧ x₀ ∈ (⋃ g, hatImage X Ns Nt g U₂) ∧
      (⋃ g, hatImage X Ns Nt g U₂) ⊆ U₁ ∧
      ∀ g, (⋃ k, hatImage X Ns Nt k U₂) ⊆ X.src '' (Ns g ∩ Nt g) ∧
        hatImage X Ns Nt g (⋃ k, hatImage X Ns Nt k U₂) ⊆ ⋃ k, hatImage X Ns Nt k U₂

end RoundTrip.V7_64
