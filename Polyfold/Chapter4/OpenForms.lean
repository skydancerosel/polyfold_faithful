import Polyfold.Chapter4.ScFormsPullback2021
import Polyfold.Chapter8.TangentLocal

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §4.4, p. 198 (the paragraph
before Theorem 4.4.7, with (4.7)), and Lemma 4.4.8 (p. 199): sc-forms on an **open subset** of an
M-polyfold, their restriction, and "`[ω] = [τ]` on `V`" (part of gaps G.80 and G.92).

# Sc-forms on open subsets

## The text, paraphrased

(p. 198) For `[ω], [τ] ∈ Ωᵏ_∞(X)` and an open `V ⊆ X`, `[ω] = [τ]` on `V` if the pull-backs by
the inclusion `σ : V → X` agree: for representatives `ω ∈ Ωᵏ(Xⁱ)`, `τ ∈ Ωᵏ(Xʲ)` there is
`ℓ ≥ i, j` with `σ^*ω = σ^*τ` on `V^ℓ` (4.7).  (Lemma 4.4.8) Forms on open neighbourhoods
`U(x)`, `V(x)` of a point, and "`d[τ] = [ω]` on `V(x)`".

## What is formalized

* The open subset `U ⊆ X` with Part I's structure `MPolyfold.restrictOpen` (charts of `X` inside
  `U`) is the M-polyfold of the text; its inclusion is sc-smooth (`isScSmoothMap_subtypeVal`,
  `Chapter8/TangentLocal.lean`) and `TU ≅ p⁻¹(U)`.
* `MPolyfold.formRestrict hU ω = ι^*ω` (`formRestrict_apply`: `(ω|U)(x)(α) = ω(x)(Tι α)`),
  `formRestrict_mem_scForms` (`Ωᵏ(X) → Ωᵏ(U)`), `extD_formRestrict` (`d(ω|U) = (dω)|U¹`).
* On the direct limits: `BundledMPolyfold.openSub A hU hne` (the bundled M-polyfold `U`),
  `inclOpen` (the inclusion as an `ScMap`), `formsInftyResOpen : Ωᵏ_∞(X) → Ωᵏ_∞(U)`, with
  `formsInftyD_formsInftyResOpen` (`d` commutes with the restriction);
  `inclOpenOpen`, `formsInftyResOpenOpen` (the restriction `Ωᵏ_∞(U) → Ωᵏ_∞(V)` for `V ⊆ U`) and
  `formsInftyResOpenOpen_comp` (`(ω|U)|V = ω|V`).
* (4.7): `FormsInftyEqOn A hV hne a b` (`[ω] = [τ]` on `V`), and `formsInftyEqOn_of_iff`: for
  representatives on the same level `i`, it holds iff `σ^*ω = σ^*τ` on `V^ℓ` for some `ℓ ≥ i`.

## The reading

* Part I's `restrictOpen` needs a junk point, so the open sets are nonempty (`hne`); its
  paracompactness is `MPolyfold.paracompactSpace_subtype`.
* Representatives on different levels `i`, `j` are first moved to `max i j` by (4.4).
-/

open Set Function

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {U : Set X} (hU : IsOpen U) [Nonempty U] [ParacompactSpace U] {k : ℕ}

/-- The restriction `ω|U = ι^*ω` of a family of alternating forms on `TX` to the open subset `U`. -/
def formRestrict (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) :
    ∀ x : (P.restrictOpen hU).Level 1, (P.restrictOpen hU).tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ :=
  formPullback (isScSmoothMap_subtypeVal hU) ω

variable {hU}

/-- `(ω|U)(x)(α₁, …, α_k) = ω(x)(Tι α₁, …, Tι α_k)`. -/
lemma formRestrict_apply (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ)
    (x : (P.restrictOpen hU).Level 1) (α : Fin k → (P.restrictOpen hU).tangentFiber x) :
    formRestrict hU ω x α = ω (liftLevelOneMap (isScSmoothMap_subtypeVal hU) x)
      fun i => tangentFiberMap (isScSmoothMap_subtypeVal hU) x (α i) := rfl

/-- **Sc-forms restrict to sc-forms on open subsets**: `Ωᵏ(X) → Ωᵏ(U)`. -/
theorem formRestrict_mem_scForms {ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    (hω : ω ∈ P.scForms k) : formRestrict hU ω ∈ (P.restrictOpen hU).scForms k :=
  formPullback_mem_scForms _ hω

/-- `d(ω|U) = (dω)|U¹`, with `U¹ → X¹` the index raise of the inclusion. -/
theorem extD_formRestrict {ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    (hω : ω ∈ P.scForms k) :
    extD (formRestrict hU ω) =
      formPullback (isScSmoothMap_liftLevelOneMap (isScSmoothMap_subtypeVal hU)) (extD ω) :=
  extD_formPullback _ hω

end MPolyfold

namespace BundledMPolyfold

open MPolyfold

variable (A : BundledMPolyfold.{u}) {U V : Set A.carrier}

/-- **An open subset `U ≠ ∅` of an M-polyfold, as a bundled M-polyfold** (Part I's
`restrictOpen`). -/
def openSub (hU : IsOpen U) (hne : U.Nonempty) : BundledMPolyfold.{u} :=
  haveI : Nonempty U := hne.to_subtype
  haveI : ParacompactSpace U := A.P.paracompactSpace_subtype U
  { carrier := U, P := A.P.restrictOpen hU }

/-- The inclusion `U → X`, an `ScMap`. -/
def inclOpen (hU : IsOpen U) (hne : U.Nonempty) : ScMap (A.openSub hU hne).P A.P :=
  haveI : Nonempty U := hne.to_subtype
  haveI : ParacompactSpace U := A.P.paracompactSpace_subtype U
  ⟨Subtype.val, isScSmoothMap_subtypeVal hU⟩

@[simp] lemma inclOpen_apply (hU : IsOpen U) (hne : U.Nonempty) (x : (A.openSub hU hne).carrier) :
    A.inclOpen hU hne x = (x : U).1 := rfl

/-- The inclusion `V → U` of open subsets `V ⊆ U`, an `ScMap`. -/
def inclOpenOpen (hU : IsOpen U) (hne : U.Nonempty) (hV : IsOpen V) (hneV : V.Nonempty)
    (hVU : V ⊆ U) : ScMap (A.openSub hV hneV).P (A.openSub hU hne).P :=
  haveI : Nonempty U := hne.to_subtype
  haveI : ParacompactSpace U := A.P.paracompactSpace_subtype U
  haveI : Nonempty V := hneV.to_subtype
  haveI : ParacompactSpace V := A.P.paracompactSpace_subtype V
  ⟨fun v => ⟨(v : V).1, hVU v.2⟩, IsScSmoothMap.codRestrict_restrictOpen hU
    (isScSmoothMap_subtypeVal hV) fun v => hVU v.2⟩

/-- `ι_U ∘ ι_{VU} = ι_V`. -/
lemma inclOpen_comp_inclOpenOpen (hU : IsOpen U) (hne : U.Nonempty) (hV : IsOpen V)
    (hneV : V.Nonempty) (hVU : V ⊆ U) :
    (A.inclOpen hU hne).comp (A.inclOpenOpen hU hne hV hneV hVU) = A.inclOpen hV hneV := rfl

variable (k : ℕ)

/-- **The restriction `Ωᵏ_∞(X) → Ωᵏ_∞(U)`**, `[ω] ↦ [σ^*ω]` with `σ : U → X` the inclusion. -/
def formsInftyResOpen (hU : IsOpen U) (hne : U.Nonempty) :
    A.formsInfty k →ₗ[ℝ] (A.openSub hU hne).formsInfty k :=
  formsInftyPullback (A.inclOpen hU hne) k

/-- The restriction `Ωᵏ_∞(U) → Ωᵏ_∞(V)` for open `V ⊆ U`. -/
def formsInftyResOpenOpen (hU : IsOpen U) (hne : U.Nonempty) (hV : IsOpen V)
    (hneV : V.Nonempty) (hVU : V ⊆ U) :
    (A.openSub hU hne).formsInfty k →ₗ[ℝ] (A.openSub hV hneV).formsInfty k :=
  formsInftyPullback (A.inclOpenOpen hU hne hV hneV hVU) k

/-- `d` commutes with the restriction to an open subset. -/
theorem formsInftyD_formsInftyResOpen (hU : IsOpen U) (hne : U.Nonempty) (a : A.formsInfty k) :
    (A.openSub hU hne).formsInftyD k (A.formsInftyResOpen k hU hne a) =
      A.formsInftyResOpen (k + 1) hU hne (A.formsInftyD k a) :=
  LinearMap.congr_fun (formsInftyD_comp_formsInftyPullback (A.inclOpen hU hne) k) a

/-- `d` commutes with the restriction `Ωᵏ_∞(U) → Ωᵏ_∞(V)`. -/
theorem formsInftyD_formsInftyResOpenOpen (hU : IsOpen U) (hne : U.Nonempty) (hV : IsOpen V)
    (hneV : V.Nonempty) (hVU : V ⊆ U) (a : (A.openSub hU hne).formsInfty k) :
    (A.openSub hV hneV).formsInftyD k (A.formsInftyResOpenOpen k hU hne hV hneV hVU a) =
      A.formsInftyResOpenOpen (k + 1) hU hne hV hneV hVU ((A.openSub hU hne).formsInftyD k a) :=
  LinearMap.congr_fun (formsInftyD_comp_formsInftyPullback (A.inclOpenOpen hU hne hV hneV hVU) k) a

/-- `(ω|U)|V = ω|V`. -/
theorem formsInftyResOpenOpen_comp (hU : IsOpen U) (hne : U.Nonempty) (hV : IsOpen V)
    (hneV : V.Nonempty) (hVU : V ⊆ U) (a : A.formsInfty k) :
    A.formsInftyResOpenOpen k hU hne hV hneV hVU (A.formsInftyResOpen k hU hne a) =
      A.formsInftyResOpen k hV hneV a := by
  have h := formsInftyPullback_comp (A.inclOpenOpen hU hne hV hneV hVU) k (A.inclOpen hU hne)
  rw [inclOpen_comp_inclOpenOpen] at h
  exact (LinearMap.congr_fun h a).symm

/-- **(4.7), 2021 p. 198**: `[ω] = [τ]` on the open set `V`: their restrictions to `V` agree. -/
def FormsInftyEqOn (hV : IsOpen V) (hne : V.Nonempty) (a b : A.formsInfty k) : Prop :=
  A.formsInftyResOpen k hV hne a = A.formsInftyResOpen k hV hne b

/-- **(4.7)** for representatives on one level `i` (representatives on levels `i`, `j` are moved
to `max i j` by (4.4)): `[ω] = [τ]` on `V` iff `σ^*ω = σ^*τ` on `V^ℓ` for some `ℓ ≥ i`. -/
theorem formsInftyEqOn_of_iff (hV : IsOpen V) (hne : V.Nonempty) {i : ℕ} (ω τ : A.forms k i) :
    A.FormsInftyEqOn k hV hne (A.formsInftyOf k i ω) (A.formsInftyOf k i τ) ↔
      ∃ ℓ, ∃ h : i ≤ ℓ, formsPullback (A.inclOpen hV hne) k ℓ (A.formsMap k i ℓ h ω) =
        formsPullback (A.inclOpen hV hne) k ℓ (A.formsMap k i ℓ h τ) := by
  unfold FormsInftyEqOn formsInftyResOpen
  rw [formsInftyPullback_of, formsInftyPullback_of]
  constructor
  · intro h
    obtain ⟨ℓ, hiℓ, h⟩ := Module.DirectLimit.exists_eq_of_of_eq h
    exact ⟨ℓ, hiℓ, by rw [formsPullback_formsMap, formsPullback_formsMap]; exact h⟩
  · rintro ⟨ℓ, hiℓ, h⟩
    rw [formsPullback_formsMap, formsPullback_formsMap] at h
    rw [← formsInftyOf_formsMap _ _ hiℓ, ← formsInftyOf_formsMap _ _ hiℓ, h]

end BundledMPolyfold

end Polyfold
