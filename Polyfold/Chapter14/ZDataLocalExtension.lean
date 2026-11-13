import Polyfold.Chapter14.ZLoopCoherent
import Polyfold.Chapter14.CoherentExtension

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 14,
§14.4, pp. 664–671: the coherent neighbourhood systems of Proposition 14.4.10 feed the local
extension of Proposition 14.4.14.

# From `ZData`/`ZSections` to the data of Proposition 14.4.14

The local extension (agent LX, `CoherentExtension`) takes the data of a fixed `a ∈ A` as
a `LocalExtensionBase` and a coherent neighbourhood system as its `CoherentNbhdSystem`
(Definition 14.4.11 (1), (3), (4), with (2) as `IsEquivariant`).  Here they are built from the
setting of this block:

* `ZSections.toLocalExtensionBase`: `∼_y` is `ZRel a y`, `≈_z` is `ZData.Approx a z`; the faces
  condition of Definition 14.1.3 (1) on `U(a)` is the extra input `hface`.
* `coherentNbhdSystem_hyp`: Proposition 14.4.10 (`proposition_14_4_10_hyp`) gives LX's
  `CoherentNbhdSystem`, and it satisfies (2) (`isEquivariant_coherentNbhdSystem_hyp`).
* `proposition_14_4_14_of_hyp`: hence Proposition 14.4.14 for these data, under
  Proposition 14.4.6 (2) in the form `HasThetaLocalEq`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}} {S : A.X.ZData}

/-- The data of Proposition 14.4.14 at `a ∈ A`, from `ZData` and `ZSections`. -/
def ZSections.toLocalExtensionBase (D : ZSections A S) {a : A.Obj} (ha : a ∈ S.A)
    (hface : ∀ i, IsFaceScPlusSectionOn A (D.s a i) (S.nbhd a).bdry) : LocalExtensionBase A a :=
  LocalExtensionBase.ofZSetup S.toZSetup ha (S.isOpen_V a ha) (D.s a) hface
    (fun g i y hy => D.equivariant a ha g i y hy) (S.Approx a)

/-- **Proposition 14.4.10 gives a coherent neighbourhood system in LX's form**, from
Proposition 14.4.6 (2) in the form `HasThetaLocalEq`. -/
theorem coherentNbhdSystem_hyp (D : ZSections A S) (hP : HasThetaLocalEq D) {a : A.Obj}
    (ha : a ∈ S.A) (hface : ∀ i, IsFaceScPlusSectionOn A (D.s a i) (S.nbhd a).bdry) :
    ∃ C : CoherentNbhdSystem (D.toLocalExtensionBase ha hface), C.IsEquivariant := by
  obtain ⟨O, hO⟩ := proposition_14_4_10_hyp D hP ha
  refine ⟨⟨O, fun z hz => (hO z hz).1, fun z hz => (hO z hz).2.1, fun z hz => (hO z hz).2.2.1,
    fun z hz y hy i i' h => ?_, fun z hz y hy i i' h => ?_⟩, fun z hz g =>
      ⟨(hO z hz).2.2.2.1 g, (hO z hz).2.2.2.2.1 g⟩⟩
  · exact (hO z hz).2.2.2.2.2.1 i' y hy h
  · exact (hO z (closure_mono inter_subset_left hz)).2.2.2.2.2.2 hz i i' h y hy

/-- **Proposition 14.4.14 for the data of this block** (through LX's `proposition_14_4_14`),
under Proposition 14.4.6 (2) in the form `HasThetaLocalEq`: sc⁺-sections `ŝᵃᵢ` on `V̂_a`,
symmetric, equal to `s⁰ᵃᵢ` on `V_a`, and equal for `i ∼_z i'`. -/
theorem proposition_14_4_14_of_hyp
    (hB : ∀ x : A.Obj, ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧ x ∈ c.φ.source)
    (hpu : A.X.PObj.AdmitsScPartitionsOfUnity) (D : ZSections A S) (hP : HasThetaLocalEq D)
    {a : A.Obj} (ha : a ∈ S.A) (hface : ∀ i, IsFaceScPlusSectionOn A (D.s a i) (S.nbhd a).bdry) :
    ∃ sh : S.I a → A.Obj → A.W, (∀ i, IsScPlusSectionOn A (sh i) (S.V a)) ∧
      (∀ (g : A.X.Isotropy a) i, ∀ y ∈ S.V a,
        sh (g • i) ((S.nbhd a).rep.Φ g y) = fibAct ((S.nbhd a).rep.Γ g y) (sh i y)) ∧
      (∀ i, ∀ y ∈ S.V a ∩ A.X.PObj.boundary, sh i y = D.s a i y) ∧
      ∀ y ∈ S.V a, ∀ i i', S.ZRel a y i i' → sh i y = sh i' y := by
  obtain ⟨C, -⟩ := coherentNbhdSystem_hyp D hP ha hface
  exact proposition_14_4_14 hB hpu C

end SBLocalization

end Polyfold
