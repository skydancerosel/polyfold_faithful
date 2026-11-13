import Polyfold.Chapter16.BranchedSuborbifold

/-!
# Naturality of the structure on `supp θ` (2021 Proposition 16.4.3, p. 730)

2021 Proposition 16.4.3 (p. 730) says that `supp θ` carries a manifold (orbifold) structure induced
from a representative, independent of the choice. H formalized, for each representative `(X, α, Θ)`,
the homeomorphism `|supp Θ| ≃ₜ supp θ` and the structure of Proposition 9.1.9 on `|supp Θ|`
(`proposition_16_4_3_manifold`). This file gives

* the transition homeomorphism `|supp Θ| ≃ₜ |supp Θ'|` between two representatives of the same
  `θ` (`suppTransition`), its characterization `α' ∘ t = α` and the cocycle identities;
* the predicate `IsInducedSuppStructure` (the conclusion of Proposition 9.1.9 (1));
* the independence claim as a Lean `Prop` (`proposition_16_4_3_naturality_statement`): the
  transition is an sc-diffeomorphism for suitable induced structures. It is not proved here
  (gap text in `narrow/p3w4-SM.md`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace PolyfoldClass

open EpGroupoid MPolyfold

variable {Z : Type u} [TopologicalSpace Z] {c : PolyfoldClass Z}

namespace BranchedSuborbifold

/-- **The transition between two representatives** of one branched suborbifold:
`|supp Θ| ≃ₜ supp θ ≃ₜ |supp Θ'|` (Proposition 16.4.3, p. 730, applied twice). -/
def suppTransition (a a' : BranchedRep c) (h : (⟦a⟧ : BranchedSuborbifold c) = ⟦a'⟧) :
    a.p.X.X.orbitSupp a.Θ ≃ₜ a'.p.X.X.orbitSupp a'.Θ :=
  (proposition_16_4_3_homeomorph a).trans
    ((Homeomorph.setCongr (congrArg supp h)).trans (proposition_16_4_3_homeomorph a').symm)

/-- The transition is characterized by `α' ∘ t = α` on `|supp Θ|`. -/
theorem β_suppTransition (a a' : BranchedRep c) (h : (⟦a⟧ : BranchedSuborbifold c) = ⟦a'⟧)
    (q : a.p.X.X.orbitSupp a.Θ) :
    a'.p.β (suppTransition a a' h q : a'.p.X.X.OrbitSpace) = a.p.β q := by
  rw [← proposition_16_4_3_homeomorph_apply a', suppTransition, Homeomorph.trans_apply,
    Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
  rfl

theorem suppTransition_eq_iff (a a' : BranchedRep c) (h : (⟦a⟧ : BranchedSuborbifold c) = ⟦a'⟧)
    (q : a.p.X.X.orbitSupp a.Θ) (q' : a'.p.X.X.orbitSupp a'.Θ) :
    suppTransition a a' h q = q' ↔ a'.p.β q' = a.p.β q := by
  constructor
  · rintro rfl; exact β_suppTransition a a' h q
  · intro hq
    exact Subtype.ext (a'.p.β.injective ((β_suppTransition a a' h q).trans hq.symm))

/-- The transition of a representative to itself is the identity. -/
theorem suppTransition_self (a : BranchedRep c) (q : a.p.X.X.orbitSupp a.Θ) :
    suppTransition a a rfl q = q :=
  (suppTransition_eq_iff a a rfl q q).2 rfl

/-- The transitions compose (cocycle identity). -/
theorem suppTransition_trans (a a' a'' : BranchedRep c)
    (h : (⟦a⟧ : BranchedSuborbifold c) = ⟦a'⟧) (h' : (⟦a'⟧ : BranchedSuborbifold c) = ⟦a''⟧)
    (q : a.p.X.X.orbitSupp a.Θ) :
    suppTransition a' a'' h' (suppTransition a a' h q) = suppTransition a a'' (h.trans h') q :=
  (suppTransition_eq_iff _ _ _ _ _).2 <| by
    rw [β_suppTransition, β_suppTransition]

/-- The inverse transition. -/
theorem suppTransition_symm (a a' : BranchedRep c) (h : (⟦a⟧ : BranchedSuborbifold c) = ⟦a'⟧)
    (q : a.p.X.X.orbitSupp a.Θ) : suppTransition a' a h.symm (suppTransition a a' h q) = q :=
  (suppTransition_trans a a' a h h.symm q).trans (suppTransition_self a q)

/-- **The structure of Proposition 9.1.9 (1) on `|supp Θ|`** (used in Proposition 16.4.3, p. 730):
`supp Θ` is an ep-subgroupoid and a smooth submanifold of `X`, and `PZ` makes the projection
`supp Θ → |supp Θ|` a local sc-diffeomorphism. -/
def IsInducedSuppStructure (a : BranchedRep c)
    [ParacompactSpace (a.p.X.X.orbitSupp a.Θ)] [T2Space (a.p.X.X.orbitSupp a.Θ)]
    (PZ : MPolyfold (a.p.X.X.orbitSupp a.Θ)) : Prop :=
  ∃ hA : a.p.X.X.IsEpSubgroupoid (EpGroupoid.supp a.Θ),
    a.p.X.X.PObj.IsSmoothSubmanifold (EpGroupoid.supp a.Θ) ∧
    haveI := a.p.X.X.PObj.paracompactSpace_subtype (EpGroupoid.supp a.Θ)
    (subEpGroupoid hA).PObj.IsLocalScDiffeo PZ (a.p.X.X.orbitSuppProj a.Θ)

/-- **2021 Proposition 16.4.3, p. 730, independence of the representative (manifold type)**, as a
Lean statement: for two representatives `a`, `a'` of one manifold-type `θ` there are induced
structures (Proposition 9.1.9 (1)) on `|supp Θ|` and `|supp Θ'|` for which the transition
`|supp Θ| ≃ₜ |supp Θ'|` is an sc-diffeomorphism. -/
def proposition_16_4_3_naturality_statement (c : PolyfoldClass Z) : Prop :=
  ∀ (a a' : BranchedRep c) (h : (⟦a⟧ : BranchedSuborbifold c) = ⟦a'⟧),
    a.p.X.X.IsManifoldType a.Θ → a'.p.X.X.IsManifoldType a'.Θ →
    haveI := a.isBranched.paracompactSpace_orbitSupp
    haveI := a'.isBranched.paracompactSpace_orbitSupp
    ∃ (PZ : MPolyfold (a.p.X.X.orbitSupp a.Θ)) (PZ' : MPolyfold (a'.p.X.X.orbitSupp a'.Θ)),
      IsInducedSuppStructure a PZ ∧ IsInducedSuppStructure a' PZ' ∧
      PZ.IsScDiffeoOn PZ' (suppTransition a a' h) (suppTransition a' a h.symm) univ univ

/-- **The statement for one representative** (`a' = a`): the induced structure of
Proposition 9.1.9 (1) exists and the transition `|supp Θ| → |supp Θ|` is the identity, an
sc-diffeomorphism. -/
theorem proposition_16_4_3_naturality_self (a : BranchedRep c)
    (hm : a.p.X.X.IsManifoldType a.Θ) :
    haveI := a.isBranched.paracompactSpace_orbitSupp
    ∃ PZ : MPolyfold (a.p.X.X.orbitSupp a.Θ), IsInducedSuppStructure a PZ ∧
      PZ.IsScDiffeoOn PZ (suppTransition a a rfl) (suppTransition a a rfl) univ univ := by
  have := a.isBranched.paracompactSpace_orbitSupp
  obtain ⟨hA, hsub, PZ, hPZ⟩ := a.p.X.X.proposition_9_1_9_one a.isBranched hm
  refine ⟨PZ, ⟨hA, hsub, hPZ⟩, ?_⟩
  exact ((MPolyfold.isScDiffeoOn_id isOpen_univ).congr_left
    fun q _ => (suppTransition_self a q).symm).congr_right
    fun q _ => (suppTransition_self a q).symm

end BranchedSuborbifold

end PolyfoldClass

end Polyfold
