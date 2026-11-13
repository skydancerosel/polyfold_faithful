import Polyfold.Chapter16.P3W4PB_FredholmSections
import Polyfold.Chapter16.P3W5PC_NormLamContinuous

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.3 (p. 729): **the zero section of a strong polyfold bundle** as an sc-smooth section
(Definition 16.3.18), the canonical section `z ↦ 0_z` induced by the zero section functors of the
models.  Numbers and pages are the 2021 text's.

## What is formalized

* `StrongPolyfoldBundle.continuous_zeroAt`: `z ↦ 0_z` is continuous (read through the quotient
  map `|x| ↦ γ(|x|)`, where it is `Γ ∘ |·| ∘ 0`).
* `StrongPolyfoldBundle.zeroRepOf S hS`: the representative `(0, Γ, W, 0_P)` in any structure
  `S ∈ c̄` (`0_P = fiberZero P`, an sc⁺-section functor, Definition 8.3.4).
* `StrongPolyfoldBundle.zeroSection c : ScSection c` (**the zero section**), with
  `toFun_zeroSection` (`f = 0_·`), `zeroSection_eq_mk` (every structure's zero section functor
  gives the same class), `isScPlus_zeroSection`, `zeroPlusSection`.
* `ScSection.eq_zeroSection_iff_F` and `rep_F_eq_fiberZero`: a representative `(f, Γ, W, F)` of
  the zero section has `F = 0_P`, i.e. the zero section is the one induced by the models' zero
  sections, in every model; `solutionSet_zeroSection` (`f⁻¹(0) = Z`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

open EPLocalization SBLocalization StrongPolyfoldBundleStructure

namespace StrongPolyfoldBundle

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- The zero section functor `x ↦ 0_x` of a strong bundle is continuous. -/
theorem continuous_fiberZero_W (S : StrongPolyfoldBundleStructure p) :
    Continuous (fiberZero S.A.P) :=
  continuousOn_univ.1 S.A.E.fiberZero_mem_sectionFunctors.1.2.continuousOn

/-- **`z ↦ 0_z` is continuous.** -/
theorem continuous_zeroAt (c : StrongPolyfoldBundle p) : Continuous c.zeroAt := by
  rw [(StrongPolyfoldBundle.isQuotientMap_γπ c.out).continuous_iff]
  have e : c.zeroAt ∘ (fun x : c.out.A.Obj => c.out.γ (c.out.A.X.π x)) =
      fun x => c.out.Γ (c.out.A.E.toEpGroupoid.π (fiberZero c.out.A.P x)) :=
    funext fun x => c.out.zeroAt_eq rfl
  rw [e]
  exact c.out.Γ.continuous.comp
    (c.out.A.E.toEpGroupoid.continuous_π.comp (continuous_fiberZero_W c.out))

/-- **The representative `(0, Γ, W, 0_P)` of the zero section** in a structure `S ∈ c̄`. -/
def zeroRepOf (S : StrongPolyfoldBundleStructure p) (hS : ⟦S⟧ = c) : SectionRep c where
  S := S
  hS := hS
  F := fiberZero S.A.P
  hF := S.A.E.fiberZero_mem_sectionFunctors
  f := c.zeroAt
  continuous_f := c.continuous_zeroAt
  isSection := c.p_zeroAt
  comm x := by rw [zeroAt_eq_of_mem hS]; exact S.zeroAt_eq rfl

/-- **The zero section `z ↦ 0_z` of `(p, c̄)`** as an sc-smooth section (Definition 16.3.18),
induced by the zero section functor of the model `c̄.out`. -/
def zeroSection (c : StrongPolyfoldBundle p) : ScSection c :=
  ⟦zeroRepOf c.out (Quotient.out_eq c)⟧

@[simp] theorem toFun_zeroSection (c : StrongPolyfoldBundle p) :
    (zeroSection c).toFun = c.zeroAt := rfl

/-- **The zero section does not depend on the model**: the zero section functor of every
structure of `c̄` gives the same class. -/
theorem zeroSection_eq_mk (S : StrongPolyfoldBundleStructure p) (hS : ⟦S⟧ = c) :
    zeroSection c = ⟦zeroRepOf S hS⟧ :=
  ScSection.ext_toFun rfl

/-- **The zero section is sc⁺** (Definition 16.3.19): `0_P ∈ Γ⁺(P, μ)`. -/
theorem isScPlus_zeroSection (c : StrongPolyfoldBundle p) : (zeroSection c).IsScPlus :=
  ⟨_, rfl, (c.out.A.E).fiberZero_mem_plusSectionFunctors⟩

/-- The zero section as an sc⁺-section (Definition 16.3.19). -/
def zeroPlusSection (c : StrongPolyfoldBundle p) : ScPlusSection c :=
  ⟨zeroSection c, isScPlus_zeroSection c⟩

/-- **Every representative of the zero section has `F = 0_P`**: the zero section is the one
induced by the zero section functors, in every model. -/
theorem rep_F_eq_fiberZero (a : SectionRep c) (ha : a.f = c.zeroAt) :
    a.F = fiberZero a.S.A.P := by
  funext x
  have hsec : a.S.A.P (a.F x) = x := a.hF.1.1 x
  have h1 : a.S.Γ (a.S.A.E.toEpGroupoid.π (a.F x)) =
      a.S.zeroAt (p (a.S.Γ (a.S.A.E.toEpGroupoid.π (a.F x)))) := by
    rw [← a.comm x, a.isSection, ha, zeroAt_eq_of_mem a.hS]
  have h2 := (a.S.Γ_π_eq_zeroAt_iff (a.F x)).1 h1
  rw [h2, hsec]

/-- An sc-smooth section is the zero section iff `f = 0_·`, iff one (every) representative has
`F = 0_P`. -/
theorem ScSection.eq_zeroSection_iff (s : ScSection c) :
    s = zeroSection c ↔ s.toFun = c.zeroAt :=
  ⟨fun h => h ▸ rfl, fun h => ScSection.ext_toFun h⟩

theorem ScSection.eq_zeroSection_iff_F (a : SectionRep c) :
    (⟦a⟧ : ScSection c) = zeroSection c ↔ a.F = fiberZero a.S.A.P := by
  rw [ScSection.eq_zeroSection_iff]
  change a.f = c.zeroAt ↔ _
  refine ⟨rep_F_eq_fiberZero a, fun hF => funext fun z => ?_⟩
  obtain ⟨x, rfl⟩ := a.S.surjective_γπ z
  rw [a.comm x, hF, zeroAt_eq_of_mem a.hS, a.S.zeroAt_eq rfl]

/-- The solution set of the zero section is all of `Z`. -/
theorem solutionSet_zeroSection (c : StrongPolyfoldBundle p) :
    (zeroSection c).solutionSet = univ :=
  eq_univ_of_forall fun _ => rfl

end StrongPolyfoldBundle

end Polyfold
