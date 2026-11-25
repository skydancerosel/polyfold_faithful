import Polyfold
/-! Blind formalization of V19_77 (the text's §19.7, Proposition 19.7.15, p. 915 of the Springer
2021 book; new in the 2021 edition).

Text: (1) the topology on `M(Ψ̂, Ψ̂')` is natural; (2) `ŝ`, `t̂` are local homeomorphisms;
(3) `ι̂` is a homeomorphism and `û` continuous; (4) `m̂` is a local homeomorphism.

Choices:
- Setting (as in the blind V19_75/V19_76): universe `0`: groupoidal categories `A`, `B`, a
  finite-to-one covering functor `P : A → B` (Definition 19.7.1; vocabulary
  `IsFiniteToOneCovering`) and a basic construction `Bh` for `P` (Definition 19.7.11; vocabulary
  `CoveringBasicConstruction P`).  `Ψ̂, Ψ̂', Ψ̂''` range over `Bh.hatU.Unif`.  No metrizability,
  `HasClassUniformizers` or compatibility hypothesis is assumed (none is quoted).  The vocabulary
  has `IsCompatible` ("every `t̂` is continuous"), documented there as an added hypothesis of the
  project, without which it says (2) does not hold as the project reads it; I do not add it.
- Topology on `M(Ψ̂, Ψ̂')` (vocabulary `MHat`, wrapped in the synonym `MT`): the one of
  Proposition 19.7.13, induced by the canonical bijection `toFib : M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_τ̂ E`,
  `(e, φ̂, e') ↦ (p(e, φ̂, e'), e)` (source description).  `M(Ψ, Ψ')` carries `T_{Ψ,Ψ'}`
  (vocabulary `MB`), `E`, `E'` the topologies of the object spaces of `Ψ̂`, `Ψ̂'`.
- (1) "the topology is natural": the quoted text does not say what "natural" means.  I read it
  as: the topology does not depend on the use of the source in its definition, i.e. the
  target description `(e, φ̂, e') ↦ (p(e, φ̂, e'), e')` is also a homeomorphism onto
  `M(Ψ, Ψ') ₜ×_τ̂' E' = {(h, e') | t(h) = τ̂'(e')}` (subspace of the product).  This reading is
  doubtful.
- (2) `ŝ` = vocabulary `srcHat` (`(e, φ̂, e') ↦ e`), `t̂` = `tgtHat` (`↦ e'`), as maps into
  `E`, `E'`; `IsLocalHomeomorph`.
- (3) `ι̂` = `invHat` (`(e, φ̂, e') ↦ (e', φ̂⁻¹, e)`): there is a homeomorphism
  `M(Ψ̂, Ψ̂') ≃ₜ M(Ψ̂', Ψ̂)` with underlying map `ι̂`; `û` = `unitHat` (`e ↦ (e, 1, e)`) is
  continuous `E → M(Ψ̂, Ψ̂)`.
- (4) `m̂` = `mulHat` on the fibred product `M(Ψ̂', Ψ̂'') ₛ×ₜ M(Ψ̂, Ψ̂')` (pairs with
  `ŝ(first) = t̂(second)`; my own subtype, subspace topology of the product of the topologies
  above), into `M(Ψ̂, Ψ̂'')`; `IsLocalHomeomorph`.
- Nothing else looks doubtful to me.
-/
namespace RoundTrip.V19_77
open Polyfold
open GroupoidalCategory

/-- `M(Ψ̂, Ψ̂')` as a bare type. -/
def MT {A B : GroupoidalCategory.{0}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}
    (Bh : CoveringBasicConstruction P) (x y : Bh.hatU.Unif) : Type :=
  Bh.MHat x y

/-- The topology of Proposition 19.7.13: induced by `M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_τ̂ E`. -/
noncomputable instance {A B : GroupoidalCategory.{0}}
    {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}
    (Bh : CoveringBasicConstruction P) (x y : Bh.hatU.Unif) : TopologicalSpace (MT Bh x y) :=
  TopologicalSpace.induced (Bh.toFib x y) inferInstance

/-- `M(Ψ, Ψ') ₜ×_τ̂' E'`. -/
def TgtFib {A B : GroupoidalCategory.{0}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}
    (Bh : CoveringBasicConstruction P) (x y : Bh.hatU.Unif) : Type :=
  {q : Bh.MB x y × y.Ψh.ObjE // q.1.tgt = y.Ψh.τ.obj q.2}

noncomputable instance {A B : GroupoidalCategory.{0}}
    {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}
    (Bh : CoveringBasicConstruction P) (x y : Bh.hatU.Unif) : TopologicalSpace (TgtFib Bh x y) :=
  instTopologicalSpaceSubtype

/-- The target description `(e, φ̂, e') ↦ (p(e, φ̂, e'), e')`. -/
noncomputable def toTgtFib {A B : GroupoidalCategory.{0}}
    {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}
    (Bh : CoveringBasicConstruction P) (x y : Bh.hatU.Unif) (h : MT Bh x y) : TgtFib Bh x y :=
  ⟨(Bh.pB x y h, Bh.tgtHat x y h), rfl⟩

/-- The fibred product `M(Ψ̂', Ψ̂'') ₛ×ₜ M(Ψ̂, Ψ̂')`. -/
def FP {A B : GroupoidalCategory.{0}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}
    (Bh : CoveringBasicConstruction P) (x y z : Bh.hatU.Unif) : Type :=
  {q : MT Bh y z × MT Bh x y // Bh.srcHat y z q.1 = Bh.tgtHat x y q.2}

noncomputable instance {A B : GroupoidalCategory.{0}}
    {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}
    (Bh : CoveringBasicConstruction P) (x y z : Bh.hatU.Unif) : TopologicalSpace (FP Bh x y z) :=
  instTopologicalSpaceSubtype

/-- `m̂ : M(Ψ̂', Ψ̂'') ₛ×ₜ M(Ψ̂, Ψ̂') → M(Ψ̂, Ψ̂'')`. -/
noncomputable def mT {A B : GroupoidalCategory.{0}}
    {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}
    (Bh : CoveringBasicConstruction P) (x y z : Bh.hatU.Unif) (q : FP Bh x y z) : MT Bh x z :=
  Bh.mulHat x y z ⟨(q.1.1, q.1.2), q.2⟩

/-- Proposition 19.7.15: the structure maps of `M(Ψ̂, Ψ̂')`. -/
def B : Prop :=
  ∀ (A B : GroupoidalCategory.{0}) (P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr),
    IsFiniteToOneCovering P →
    ∀ Bh : CoveringBasicConstruction P,
      -- (1) the topology is natural (the target description gives the same topology)
      (∀ x y : Bh.hatU.Unif, ∃ e : MT Bh x y ≃ₜ TgtFib Bh x y,
        ∀ h : MT Bh x y, e h = toTgtFib Bh x y h) ∧
      -- (2) `ŝ` and `t̂` are local homeomorphisms
      (∀ x y : Bh.hatU.Unif,
        IsLocalHomeomorph (fun h : MT Bh x y => Bh.srcHat x y h) ∧
        IsLocalHomeomorph (fun h : MT Bh x y => Bh.tgtHat x y h)) ∧
      -- (3) `ι̂` is a homeomorphism and `û` is continuous
      (∀ x y : Bh.hatU.Unif, ∃ e : MT Bh x y ≃ₜ MT Bh y x,
        ∀ h : MT Bh x y, e h = Bh.invHat x y h) ∧
      (∀ x : Bh.hatU.Unif, Continuous (fun e : x.Ψh.ObjE => (Bh.unitHat x e : MT Bh x x))) ∧
      -- (4) `m̂` is a local homeomorphism
      (∀ x y z : Bh.hatU.Unif, IsLocalHomeomorph (mT Bh x y z))

end RoundTrip.V19_77
