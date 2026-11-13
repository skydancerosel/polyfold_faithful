import Polyfold.Chapter16.P3W3V_PolyfoldSections
import Polyfold.Chapter16.P3W3V_PolyfoldAuxNorm
import Polyfold.Chapter13.P3M_MultisectionSupport

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§§16.5–16.6 (pp. 732–740): **the zero of a fibre of a strong polyfold bundle**, used by
Definition 16.5.2 (`y ≠ 0_z`, as in Definition 13.2.2) and Definitions 16.6.2–16.6.3
(`f(z) = 0`).  Numbers and pages are the 2021 text's.

## What is formalized

* Strong bundle level (namespace `Polyfold.SBLocalization`): the orbit of `0_x` depends only on the
  orbit of `x` (`π_fiberZero_eq_of_π_eq`); the orbit map of a generalized strong bundle map sends
  `|0_x|` to `|0_{x'}|` whenever its base orbit map sends `|x|` to `|x'|`
  (`SDiagram.orbitMap_π_fiberZero`, `GenSBMap.orbitMap_π_fiberZero`); morphisms preserve
  nonzero points (`μ_ne_fiberZero`).
* Strong polyfold bundles: `StrongPolyfoldBundleStructure.zeroAt S z = Γ(|0_x|)` for
  `γ(|x|) = z` (`zeroAt_eq`), the same for equivalent structures (`zeroAt_eq_of_equiv`), hence
  `StrongPolyfoldBundle.zeroAt c` (`zeroAt_eq_of_mem`), with `p (zeroAt z) = z`, and
  `Γ(|w|) = 0_z` iff `w` is the zero of its fibre (`Γ_π_eq_zeroAt_iff`).
* `StrongPolyfoldBundle.normY c n`: `n` read as `0` off `Y_{0,1}` (the text's `n : Y_{0,1} → ℝ⁺`
  on all of `Y`), and `normY_Γ` (`normY n (Γ|w|) = normW (normOf n) w`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

open EPLocalization

namespace SBLocalization

variable {A A' : SEP.{u}}

/-- The orbit of `0_x` depends only on the orbit of `x`: `μ(φ, 0_{s(φ)}) = 0_{t(φ)}`. -/
theorem π_fiberZero_eq_of_π_eq {x y : A.Obj} (h : A.X.π x = A.X.π y) :
    A.E.toEpGroupoid.π (fiberZero A.P x) = A.E.toEpGroupoid.π (fiberZero A.P y) := by
  obtain ⟨φ, rfl, rfl⟩ := (GroupoidStr.π_eq_π_iff _).1 h
  have h0 : A.P (fiberZero A.P (A.X.src φ)) = A.X.src φ := isSection_fiberZero _
  rw [← μ_fiberZero A φ h0, EpStrongBundle.π_μ]

/-- Morphisms map nonzero points to nonzero points. -/
theorem μ_ne_fiberZero (q : pullbackSpace A.P A.X.src)
    (hq : (q : A.Mor × A.W).2 ≠ fiberZero A.P (A.P (q : A.Mor × A.W).2)) :
    A.E.μ q ≠ fiberZero A.P (A.P (A.E.μ q)) := by
  intro h
  apply hq
  have hP : A.P (q : A.Mor × A.W).2 = A.X.src (q : A.Mor × A.W).1 := q.2
  have h0 : A.P (fiberZero A.P (A.X.src (q : A.Mor × A.W).1)) =
      A.X.src (q : A.Mor × A.W).1 := isSection_fiberZero _
  rw [hP]
  refine EpStrongBundle.μ_injective_snd A.E hP h0 ?_
  rw [μ_fiberZero A _ h0]
  have hq' : A.E.μ ⟨((q : A.Mor × A.W).1, (q : A.Mor × A.W).2), hP⟩ = A.E.μ q := rfl
  rw [hq', h, A.E.P_μ]

/-- A zero point is carried to a zero point by a morphism. -/
theorem π_eq_fiberZero_iff {w : A.W} {x : A.Obj}
    (h : A.E.toEpGroupoid.π w = A.E.toEpGroupoid.π (fiberZero A.P x)) :
    w = fiberZero A.P (A.P w) := by
  by_contra hw
  obtain ⟨q, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 h.symm
  have hs' : (q : A.Mor × A.W).2 = fiberZero A.P x := hs
  have ht' : A.E.μ q = w := ht
  have hP : A.P (q : A.Mor × A.W).2 = A.X.src (q : A.Mor × A.W).1 := q.2
  have h0 : A.P (fiberZero A.P x) = x := isSection_fiberZero _
  have hx : x = A.X.src (q : A.Mor × A.W).1 := by rw [← h0, ← hs']; exact hP
  have e : A.E.μ q = fiberZero A.P (A.X.tgt (q : A.Mor × A.W).1) := by
    have hq : q = ⟨((q : A.Mor × A.W).1, fiberZero A.P (A.X.src (q : A.Mor × A.W).1)),
        isSection_fiberZero _⟩ := by
      apply Subtype.ext
      refine Prod.ext rfl ?_
      rw [hs', hx]
    rw [hq, μ_fiberZero]
  apply hw
  rw [← ht', e]
  exact congrArg _ (isSection_fiberZero _).symm

namespace SDiagram

/-- **`|D|(|0_x|) = |0_{x'}|`** whenever `|d|(|x|) = |x'|`. -/
theorem orbitMap_π_fiberZero (D : SDiagram A A') {x : A.Obj} {x' : A'.Obj}
    (h : D.base.orbitMap (A.X.π x) = A'.X.π x') :
    D.orbitMap (A.E.toEpGroupoid.π (fiberZero A.P x)) =
      A'.E.toEpGroupoid.π (fiberZero A'.P x') := by
  obtain ⟨ξ, hξ⟩ := D.hΦ.isEquivalence_base.isHomeomorph_orbitMap.surjective (A.X.π x)
  induction ξ using Quotient.inductionOn with | h x'' => ?_
  have h1 : A.X.π ((SEP.Hom.ϕ D.Φ).obj x'') = A.X.π x := hξ
  have hΦ0 : (SEP.Hom.Φ D.Φ).obj (fiberZero D.B.P x'') =
      fiberZero A.P ((SEP.Hom.ϕ D.Φ).obj x'') :=
    D.Φ.isStrongBundleFunctor.isStrongBundleMap_obj.map_fiberZero x''
  have hΨ0 : (SEP.Hom.Φ D.Ψ).obj (fiberZero D.B.P x'') =
      fiberZero A'.P ((SEP.Hom.ϕ D.Ψ).obj x'') :=
    D.Ψ.isStrongBundleFunctor.isStrongBundleMap_obj.map_fiberZero x''
  have h2 : D.base.orbitMap (A.X.π ((SEP.Hom.ϕ D.Φ).obj x'')) =
      A'.X.π ((SEP.Hom.ϕ D.Ψ).obj x'') :=
    D.base.orbitMap_orbitMap_F (D.B.X.π x'')
  rw [h1, h] at h2
  rw [← π_fiberZero_eq_of_π_eq h1, ← hΦ0, π_fiberZero_eq_of_π_eq h2, ← hΨ0]
  exact D.orbitMap_orbitMap_Φ (D.B.E.toEpGroupoid.π (fiberZero D.B.P x''))

end SDiagram

namespace GenSBMap

/-- **A generalized strong bundle map preserves the zeros of the fibres** on orbit spaces:
`|[D]|(|0_x|) = |0_{x'}|` whenever `|[d]|(|x|) = |x'|`. -/
theorem orbitMap_π_fiberZero (F : GenSBMap A A') {x : A.Obj} {x' : A'.Obj}
    (h : EPLoc.orbitMap F.base (A.X.π x) = A'.X.π x') :
    F.orbitMap (A.E.toEpGroupoid.π (fiberZero A.P x)) =
      A'.E.toEpGroupoid.π (fiberZero A'.P x') := by
  induction F using Quot.inductionOn with | h D => ?_
  exact D.orbitMap_π_fiberZero h

end GenSBMap

end SBLocalization

open SBLocalization

namespace StrongPolyfoldBundleStructure

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}

/-- **The zero of the fibre `p⁻¹(z)`** read in a structure: `Γ(|0_x|)` for a representative
`x` of `γ⁻¹(z)`. -/
def zeroAt (S : StrongPolyfoldBundleStructure p) (z : Z) : Y :=
  S.Γ (S.A.E.toEpGroupoid.π (fiberZero S.A.P (S.γ.symm z).out))

/-- `zeroAt z = Γ(|0_x|)` for every `x` with `γ(|x|) = z`. -/
theorem zeroAt_eq (S : StrongPolyfoldBundleStructure p) {x : S.A.Obj} {z : Z}
    (h : S.γ (S.A.X.π x) = z) :
    S.zeroAt z = S.Γ (S.A.E.toEpGroupoid.π (fiberZero S.A.P x)) := by
  unfold zeroAt
  congr 1
  apply π_fiberZero_eq_of_π_eq
  rw [← h, Homeomorph.symm_apply_apply]
  exact Quotient.out_eq _

theorem p_zeroAt (S : StrongPolyfoldBundleStructure p) (z : Z) : p (S.zeroAt z) = z := by
  obtain ⟨ξ, rfl⟩ := S.γ.surjective z
  induction ξ using Quotient.inductionOn with | h x => ?_
  change p (S.zeroAt (S.γ (S.A.X.π x))) = S.γ (S.A.X.π x)
  rw [S.zeroAt_eq rfl, S.p_Γ]
  change S.γ (S.A.X.π (S.A.P (fiberZero S.A.P x))) = _
  rw [show S.A.P (fiberZero S.A.P x) = x from isSection_fiberZero x]

/-- **The zero does not depend on the structure** within an equivalence class (Definition
16.3.3; zeros are preserved by generalized strong bundle isomorphisms). -/
theorem zeroAt_eq_of_equiv {S S' : StrongPolyfoldBundleStructure p} (h : Equiv S S') :
    S.zeroAt = S'.zeroAt := by
  obtain ⟨F, -, hγ, hΓ⟩ := h
  funext z
  obtain ⟨ξ, rfl⟩ := S.γ.surjective z
  induction ξ using Quotient.inductionOn with | h x => ?_
  change S.zeroAt (S.γ (S.A.X.π x)) = S'.zeroAt (S.γ (S.A.X.π x))
  obtain ⟨ξ', hξ'⟩ := S'.A.X.surjective_π (EPLoc.orbitMap F.base (S.A.X.π x))
  have hz : S'.γ (S'.A.X.π ξ') = S.γ (S.A.X.π x) := by
    rw [hξ']; exact congrFun hγ (S.A.X.π x)
  rw [S.zeroAt_eq rfl, S'.zeroAt_eq hz, ← congrFun hΓ,
    Function.comp_apply, F.orbitMap_π_fiberZero hξ'.symm]

/-- `Γ(|w|)` is the zero of its fibre iff `w` is. -/
theorem Γ_π_eq_zeroAt_iff (S : StrongPolyfoldBundleStructure p) (w : S.A.W) :
    S.Γ (S.A.E.toEpGroupoid.π w) = S.zeroAt (p (S.Γ (S.A.E.toEpGroupoid.π w))) ↔
      w = fiberZero S.A.P (S.A.P w) := by
  have hz : S.γ (S.A.X.π (S.A.P w)) = p (S.Γ (S.A.E.toEpGroupoid.π w)) :=
    (S.p_Γ (S.A.E.toEpGroupoid.π w)).symm
  rw [S.zeroAt_eq hz]
  constructor
  · intro h
    exact π_eq_fiberZero_iff (S.Γ.injective h)
  · intro h
    conv_lhs => rw [h]

end StrongPolyfoldBundleStructure

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}

/-- **The zero `0_z ∈ p⁻¹(z)`** of a strong polyfold bundle (read in any structure of `c̄`,
`zeroAt_eq_of_mem`). -/
def zeroAt (c : StrongPolyfoldBundle p) : Z → Y := c.out.zeroAt

theorem zeroAt_eq_of_mem {c : StrongPolyfoldBundle p} {S : StrongPolyfoldBundleStructure p}
    (hS : ⟦S⟧ = c) : c.zeroAt = S.zeroAt :=
  zeroAt_eq_of_equiv (Quotient.exact (show ⟦c.out⟧ = ⟦S⟧ by rw [Quotient.out_eq, hS]))

theorem p_zeroAt (c : StrongPolyfoldBundle p) (z : Z) : p (c.zeroAt z) = z :=
  c.out.p_zeroAt z

/-- `n : Y_{0,1} → ℝ` read on `Y`, with the value `0` off `Y_{0,1}`. -/
def normY (c : StrongPolyfoldBundle p) (n : Y → ℝ) (y : Y) : ℝ := by
  classical
  exact if y ∈ c.Y01 then n y else 0

/-- **`normY n (Γ(|w|)) = N(w)`** for `N = normOf n` read on `W` (`normW`, `0` off `W_{0,1}`). -/
theorem normY_Γ {c : StrongPolyfoldBundle p} {S : StrongPolyfoldBundleStructure p} (hS : ⟦S⟧ = c)
    (n : Y → ℝ) (w : S.A.W) :
    c.normY n (S.Γ (S.A.E.toEpGroupoid.π w)) = normW (S.normOf n) w := by
  classical
  unfold normY
  rw [c.Y01_eq hS]
  by_cases hw : w ∈ S.A.B.oneSet
  · rw [if_pos ⟨S.A.B.oneMk w hw, rfl⟩, normW_of_mem _ hw]
    rfl
  · rw [normW, dif_neg hw, if_neg]
    rintro ⟨e, he⟩
    apply hw
    have h1 : S.A.E.toEpGroupoid.π (S.A.B.oneVal e) = S.A.E.toEpGroupoid.π w :=
      S.Γ.injective he
    obtain ⟨q, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 h1
    have hs' : (q : S.A.Mor × S.A.W).2 = S.A.B.oneVal e := hs
    have ht' : S.A.E.μ q = w := ht
    rw [← ht']
    exact μ_mem_oneSet S.A q (by rw [hs']; exact S.A.B.oneVal_mem e)

end StrongPolyfoldBundle

end Polyfold
