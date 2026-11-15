import Polyfold.Chapter15.CanonicalOrientationLocal
import Polyfold.Chapter16.CanonicalOrientationWitness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §16.6:
**Definition 16.6.5** (p. 739) with `Lin(f, x)` made with local sc⁺-sections, and its
comparison with the form made with sc⁺-sections over the whole object space.

# Orientations of sc-Fredholm sections of strong polyfold bundles, local form

## The text, paraphrased

(Definition 16.6.5) An orientation of an sc-Fredholm section `f` of a strong polyfold bundle is
the choice of an orientation of `F` for a representative `(W, F)` (Definition 12.5.4).

## What is formalized

* `orTopology_isOrientationTopology` (namespace `Polyfold`): for a tame M-polyfold with sc-smooth
  bump functions and tame germ data, the topology of Theorem 6.6.17 made with sc-smooth bump
  functions has the properties of Theorem 6.6.17 (`IsOrientationTopology`).
* `StrongPolyfoldBundle.OrientationRepLoc`: **Definition 16.6.5 with local sc⁺-sections**: a
  representative `(W, F)` with tame object M-polyfold and tame germ data of `F`, and an
  orientation `o` of `F` in the local orientation sets (`definition_12_5_4_loc`).  The topology
  of `O_F` is the one of Theorem 12.5.3, so it is not part of the data.
* `OrientationRepLoc.toOrientationRep` (with sc-smooth bump functions) and
  `OrientationRep.toLoc` (with a tame object M-polyfold, bump functions and tame germ data):
  the two forms correspond (`toOrientationRep_toLoc_o`, `toLoc_toOrientationRep_o`: the
  orientations go back and forth).
* **`FredholmSection.isOrientable_iff_isOrientableLoc`**: when every representative has a tame
  object M-polyfold with sc-smooth bump functions and tame germ data, `f` is orientable in the
  sense of Definition 16.6.5 iff it is in the local sense.
* `OrientationRepLoc.isSectionOrientation`: the image of a local orientation is an orientation of
  Definition 6.6.16, and invariant under the morphisms (`isOrInvariant`), the inputs of Theorem
  15.4.1 in the model.

## Witnesses (namespace `Polyfold.HalfSpaceBundle`)

On the half space `H = [0, ∞) × ℝᵐ` (`∂H ≠ ∅`, fibres `ℝᵏ`, the graph section of a `C^∞` map):
`halfOrientationRepLoc`, `isOrientableLoc_halfFredholmSection`.  On the half-disc example
(`f(a, y) = ((a, y), a² + y² − 1)`, `Λ = 0`, a boundary point in the support):
`halfDiscOrientationLoc`, `definition_12_5_4_loc_halfDiscOrientationLoc`,
`theorem_15_4_1_loc_halfSEP` (Theorem 15.4.1 with the local orientation as input) and
`orOfLoc_halfDiscOrientationLoc` (its image is `halfOrientation`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

section Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **The topology of Theorem 6.6.17 made with sc-smooth bump functions has the properties of
Theorem 6.6.17**: it is the unique such topology (`theorem_6_6_17`, `eq_orTopology_of`). -/
theorem orTopology_isOrientationTopology (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (hsec : B.HasScPlusSectionsThrough) :
    haveI := paracompactSpace_rn_prod PX
    haveI := paracompactSpace_rn_pullback B
    haveI := paracompactSpace_rn_rn_prod PX
    haveI := paracompactSpace_rn_rn_pullback B
    IsOrientationTopology f hf.toIsScFredholmSection
      (orTopology (orLocalTransport hX hbump hf hsec)) := by
  have := paracompactSpace_rn_prod PX
  have := paracompactSpace_rn_pullback B
  have := paracompactSpace_rn_rn_prod PX
  have := paracompactSpace_rn_rn_pullback B
  obtain ⟨t₀, ht₀⟩ := (theorem_6_6_17 hX hbump hf).exists
  exact eq_orTopology_of hX hbump hf hsec ht₀.isLocalHomeomorph ht₀.propagation ▸ ht₀

end Topology

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure SBLocalization

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- **2021 Definition 16.6.5, p. 739, with local sc⁺-sections**: a representative `(W, F)` of
the sc-Fredholm section with a tame object M-polyfold and tame germ data of `F`, and an
orientation `o` of `F` in the sense of Definition 12.5.4 made with the local orientation sets
`OrxLoc` (continuous for the topology of Theorem 12.5.3, invariant under the morphisms). -/
structure OrientationRepLoc (s : FredholmSection c) : Type (u + 1) where
  /-- The representative `(W, F)`. -/
  a : SectionRep c
  ha : ⟦a⟧ = s.1
  hF : a.S.A.E.IsScFredholmSectionFunctor a.F
  hX : a.S.A.X.PObj.IsTame
  hfT : a.S.A.B.IsScFredholmSectionTame a.F
  /-- The orientation `x ↦ o_x` in the local orientation sets. -/
  o : ∀ x (hs : x ∈ a.S.A.X.PObj.smoothSet), OrxLoc hfT x hs
  isOrientation : a.S.A.E.definition_12_5_4_loc hX hF hfT o

/-- `f` is **orientable in the local sense** (Definition 16.6.5 with local sc⁺-sections). -/
def FredholmSection.IsOrientableLoc (s : FredholmSection c) : Prop :=
  Nonempty (OrientationRepLoc s)

variable {s : FredholmSection c}

/-- **A local orientation is an orientation of Definition 16.6.5**, when the object M-polyfold of
the representative admits sc-smooth bump functions: the orientation `orOfLoc o` with the
topology of Theorem 6.6.17. -/
def OrientationRepLoc.toOrientationRep (R : OrientationRepLoc s)
    (hbump : R.a.S.A.X.PObj.AdmitsBumpFunctions) (hsec : R.a.S.A.B.HasScPlusSectionsThrough) :
    OrientationRep s where
  a := R.a
  ha := R.ha
  hF := R.hF
  hsec := hsec
  t := haveI := paracompactSpace_rn_prod R.a.S.A.X.PObj
    haveI := paracompactSpace_rn_pullback R.a.S.A.B
    haveI := paracompactSpace_rn_rn_prod R.a.S.A.X.PObj
    haveI := paracompactSpace_rn_rn_pullback R.a.S.A.B
    orTopology (orLocalTransport R.hX hbump R.hfT hsec)
  isOrientationTopology := orTopology_isOrientationTopology R.hX hbump R.hfT hsec
  o := orOfLoc R.hF R.hfT hsec R.o
  isOrientation := definition_12_5_4_orOfLoc R.hX hbump R.hF R.hfT hsec R.o R.isOrientation

/-- **An orientation of Definition 16.6.5 is a local orientation**, for a tame object
M-polyfold with sc-smooth bump functions and tame germ data of `F`: the topology `t` is that
of Theorem 6.6.17 (`eq_orTopology_of`), and the image of `o` under `orxLocEquiv` is an
orientation in the local orientation sets (`definition_12_5_4_iff_loc`). -/
def OrientationRep.toLoc (R : OrientationRep s) (hX : R.a.S.A.X.PObj.IsTame)
    (hbump : R.a.S.A.X.PObj.AdmitsBumpFunctions)
    (hft : R.a.S.A.B.IsScFredholmSectionTame R.a.F) : OrientationRepLoc s where
  a := R.a
  ha := R.ha
  hF := R.hF
  hX := hX
  hfT := hft
  o := fun x hs => orxLocEquiv hft R.hsec x hs (R.o x hs)
  isOrientation := by
    have := paracompactSpace_rn_prod R.a.S.A.X.PObj
    have := paracompactSpace_rn_pullback R.a.S.A.B
    have := paracompactSpace_rn_rn_prod R.a.S.A.X.PObj
    have := paracompactSpace_rn_rn_pullback R.a.S.A.B
    have ht : R.t = orTopology (orLocalTransport hX hbump hft R.hsec) :=
      eq_orTopology_of hX hbump hft R.hsec R.isOrientationTopology.isLocalHomeomorph
        R.isOrientationTopology.propagation
    have h := R.isOrientation
    rw [ht] at h
    exact (R.a.S.A.E.definition_12_5_4_iff_loc R.hF hft R.hsec hX hbump R.o).1 h

/-- Back and forth: `toLoc` then `toOrientationRep` gives back the orientation `o`. -/
theorem OrientationRep.toOrientationRep_toLoc_o (R : OrientationRep s)
    (hX : R.a.S.A.X.PObj.IsTame) (hbump : R.a.S.A.X.PObj.AdmitsBumpFunctions)
    (hft : R.a.S.A.B.IsScFredholmSectionTame R.a.F) :
    ((R.toLoc hX hbump hft).toOrientationRep hbump R.hsec).o = R.o :=
  orOfLoc_orxLocEquiv R.hF hft R.hsec R.o

/-- Back and forth: `toOrientationRep` then `toLoc` gives back the local orientation `o`. -/
theorem OrientationRepLoc.toLoc_toOrientationRep_o (R : OrientationRepLoc s)
    (hbump : R.a.S.A.X.PObj.AdmitsBumpFunctions) (hsec : R.a.S.A.B.HasScPlusSectionsThrough) :
    ((R.toOrientationRep hbump hsec).toLoc R.hX hbump R.hfT).o = R.o := by
  funext x hs
  exact orxLocEquiv_orOfLoc R.hF R.hfT hsec R.o x hs

/-- **Definition 16.6.5 and its local form agree**: if every representative of `f` has a tame
object M-polyfold with sc-smooth bump functions and tame germ data, `f` is orientable iff it is
orientable in the local sense. -/
theorem FredholmSection.isOrientable_iff_isOrientableLoc
    (h : ∀ a : SectionRep c, ⟦a⟧ = s.1 →
      a.S.A.X.PObj.IsTame ∧ a.S.A.X.PObj.AdmitsBumpFunctions ∧
        a.S.A.B.IsScFredholmSectionTame a.F) :
    s.IsOrientable ↔ s.IsOrientableLoc := by
  constructor
  · rintro ⟨R⟩
    obtain ⟨hX, hbump, hft⟩ := h R.a R.ha
    exact ⟨R.toLoc hX hbump hft⟩
  · rintro ⟨R⟩
    obtain ⟨-, hbump, -⟩ := h R.a R.ha
    exact ⟨R.toOrientationRep hbump hbump.hasScPlusSectionsThrough⟩

/-- **The inputs of Theorem 15.4.1 in the model of a local orientation**: the image `orOfLoc o`
is an orientation of Definition 6.6.16. -/
theorem OrientationRepLoc.isSectionOrientation (R : OrientationRepLoc s)
    (hbump : R.a.S.A.X.PObj.AdmitsBumpFunctions) (hsec : R.a.S.A.B.HasScPlusSectionsThrough) :
    haveI := paracompactSpace_rn_prod R.a.S.A.X.PObj
    haveI := paracompactSpace_rn_pullback R.a.S.A.B
    IsSectionOrientation R.a.F R.hF.2 (orOfLoc R.hF R.hfT hsec R.o) :=
  isSectionOrientation_orOfLoc R.hX hbump R.hF R.hfT hsec R.o R.isOrientation

/-- The image `orOfLoc o` of a local orientation is invariant under the morphisms. -/
theorem OrientationRepLoc.isOrInvariant (R : OrientationRepLoc s)
    (hbump : R.a.S.A.X.PObj.AdmitsBumpFunctions) (hsec : R.a.S.A.B.HasScPlusSectionsThrough) :
    R.a.S.A.E.IsOrInvariant R.hF hsec (orOfLoc R.hF R.hfT hsec R.o) :=
  isOrInvariant_orOfLoc R.hX hbump R.hF R.hfT hsec R.o R.isOrientation

end StrongPolyfoldBundle

namespace HalfSpaceBundle

open SBLocalization StrongPolyfoldBundle

variable {m k : ℕ} {φ : Pm m → (Fin k → ℝ)}

/-- **A local orientation of the sc-Fredholm section over the half space** (Definition 16.6.5
with local sc⁺-sections), the image of `halfOrientationRep`. -/
def halfOrientationRepLoc (hφ : ContDiff ℝ ∞ φ) : OrientationRepLoc (halfFredholmSection hφ) :=
  (halfOrientationRep hφ).toLoc (isTame_halfSEP m k) (admitsBumpFunctions_halfSEP m k)
    (isScFredholmSectionTame_graphSection_halfSEP hφ)

/-- **The sc-Fredholm section over the half space is orientable in the local sense.** -/
theorem isOrientableLoc_halfFredholmSection (hφ : ContDiff ℝ ∞ φ) :
    (halfFredholmSection (m := m) (k := k) hφ).IsOrientableLoc :=
  ⟨halfOrientationRepLoc hφ⟩

/-- **The local orientation of the half-disc section**: the image of `halfOrientation` in the
local orientation sets. -/
def halfDiscOrientationLoc :
    ∀ y (hy : y ∈ (halfSEP 1 1).X.PObj.smoothSet),
      OrxLoc (isScFredholmSectionTame_graphSection_halfSEP contDiff_halfDiscMap) y hy :=
  fun y hy => orxLocEquiv (isScFredholmSectionTame_graphSection_halfSEP contDiff_halfDiscMap)
    (hasScPlusSectionsThrough_halfSEP 1 1) y hy (halfOrientation contDiff_halfDiscMap y hy)

/-- `halfDiscOrientationLoc` is an orientation in the local orientation sets
(Definition 12.5.4 with local sc⁺-sections). -/
theorem definition_12_5_4_loc_halfDiscOrientationLoc :
    (halfSEP 1 1).E.definition_12_5_4_loc (isTame_halfSEP 1 1)
      (isScFredholmSectionFunctor_graphSection_halfSEP contDiff_halfDiscMap)
      (isScFredholmSectionTame_graphSection_halfSEP contDiff_halfDiscMap)
      halfDiscOrientationLoc := by
  obtain ⟨-, -, -, hX, hbump, hF, hft, -, hsec, hinv, ho, -, -⟩ :=
    theorem_15_4_1_hypotheses_halfSEP
  exact definition_12_5_4_loc_of_orientation hX hbump hF hft hsec _ hinv ho

/-- The image of `halfDiscOrientationLoc` in `Orx` is `halfOrientation`. -/
theorem orOfLoc_halfDiscOrientationLoc :
    orOfLoc (isScFredholmSectionFunctor_graphSection_halfSEP contDiff_halfDiscMap)
      (isScFredholmSectionTame_graphSection_halfSEP contDiff_halfDiscMap)
      (hasScPlusSectionsThrough_halfSEP 1 1) halfDiscOrientationLoc =
      halfOrientation contDiff_halfDiscMap :=
  orOfLoc_orxLocEquiv _ _ _ _

/-- **Theorem 15.4.1 with a local orientation as input, on the half-disc example** (`∂X ≠ ∅`,
fibre `ℝ`, a boundary point `(0, 1)` in `supp(Λ ∘ f)`, sheets of dimension `1`):
`canonicalOrientationLoc` is the canonical orientation of `Θ = Λ ∘ f`. -/
theorem theorem_15_4_1_loc_halfSEP :
    IsCanonicalFor (zeroMultisection (halfSEP 1 1))
      (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap).2
      (hasScPlusSectionsThrough_halfSEP 1 1)
      (orOfLoc (isScFredholmSectionFunctor_graphSection_halfSEP contDiff_halfDiscMap)
        (isScFredholmSectionTame_graphSection_halfSEP contDiff_halfDiscMap)
        (hasScPlusSectionsThrough_halfSEP 1 1) halfDiscOrientationLoc) 1
      (canonicalOrientationLoc
        (isScFredholmSectionFunctor_graphSection_halfSEP contDiff_halfDiscMap)
        (isScFredholmSectionTame_graphSection_halfSEP contDiff_halfDiscMap)
        (hasScPlusSectionsThrough_halfSEP 1 1) halfDiscOrientationLoc
        (zeroMultisection (halfSEP 1 1))) := by
  obtain ⟨-, -, -, hX, hbump, hF, hft, hΛ, hsec, -, -, hgp, hidx⟩ :=
    theorem_15_4_1_hypotheses_halfSEP
  exact theorem_15_4_1_loc hX hbump hF hft hΛ hsec _
    definition_12_5_4_loc_halfDiscOrientationLoc hgp hidx

end HalfSpaceBundle

end Polyfold
