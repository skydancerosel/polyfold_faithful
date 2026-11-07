import Polyfold
/-! Blind formalization of V7_63 (the 2017 book's Part II, §7.5.1, Lemma 7.8, p. 253).

Text: with the choices made in the proof of Theorem 7.5 (the disjoint open neighbourhoods `N_g`
of the `g ∈ G_{x₀}` and the open neighbourhood `U₀` of `x₀`) there is an open neighbourhood
`U₁ ⊆ U₀` of `x₀` such that every morphism `h` with `s(h), t(h) ∈ U₁` belongs to `N_g` for some
`g ∈ G_{x₀}`.

Choices:
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files), with the instances of the
  project's `EpGroupoid`, `X : EpGroupoid Obj Mor` (the project's Definition 7.3, fields read
  with `#print`, as in `RoundTrip/Blind/V7_49.lean`); `G_{x₀}` is the project's `X.Isotropy x₀`.
- "The choices made above" (`IsChoicesB`), as the proof of Theorem 7.5 makes them (item V7_62):
  an open `U₀ ∋ x₀` and, for every `g`, open neighbourhoods `N^s_g, N^t_g` of `g` in `𝐗` on
  which `s`, resp. `t`, is an sc-diffeomorphism ONTO `U₀` (the project's `IsScDiffeoOn` with
  some inverse, `#print`), and the sets `N^t_g ∪ N^s_g` pairwise disjoint;
  `N_g := N^t_g ∩ N^s_g`.  These are hypotheses on arbitrary such data (the lemma holds for every
  choice).  LEFT OUT: the proof of Theorem 7.5 also takes `N^s_g, N^t_g` contractible (hence
  `U₀` contractible).  It is not used for this conclusion, and I could not convince myself that
  every point of an M-polyfold has a contractible open neighbourhood, so keeping it risked a
  vacuous hypothesis; without it B is stronger (and, I believe, still true).
- "open neighbourhood `U₁ ⊆ U₀` of `x₀`": `IsOpen U₁`, `x₀ ∈ U₁`, `U₁ ⊆ U₀`.
- Nothing looks false to me (the proof uses the properness (3) of Definition 7.3 at `x₀`).
-/
namespace RoundTrip.V7_63
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

end

/-- Lemma 7.8: near `x₀`, every morphism between nearby points lies in some `N_g`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (x₀ : Obj) (U₀ : Set Obj) (Ns Nt : X.Isotropy x₀ → Set Mor),
    IsChoicesB X x₀ U₀ Ns Nt →
    ∃ U₁ : Set Obj, IsOpen U₁ ∧ x₀ ∈ U₁ ∧ U₁ ⊆ U₀ ∧
      ∀ h : Mor, X.src h ∈ U₁ → X.tgt h ∈ U₁ → ∃ g, h ∈ Ns g ∩ Nt g

end RoundTrip.V7_63
