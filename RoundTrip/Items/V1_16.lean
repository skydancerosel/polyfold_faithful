import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_16

/-! Round trip for V1_16 (Proposition 1.17: if `f : U → V` is sc^k then `f : U¹ → V¹` is sc^k).

`A` is the conjunction of the types of the theorems in the item's declaration list:
`IsSc0.shift`, `IsSc1With.shift`, `IsSck.shift`, `IsScSmooth.shift`, `IsScDomain.shift`.  None has
universe parameters (`ScBanach` lives in `Type`).

Same notions on both sides: `B`'s `levelTo f 1 1` is `levelMap f 1` by `rfl`, `B`'s `U¹` is
`E.lvlSet U 1` in `E.shift`, and `sc^k` is the project's `IsSck`.

* `A → B`: `IsSck.shift` on the sc-domain `U` (`IsRelOpenInQuadrant.isScDomain`), and
  `IsSc0.levelMap_mapsTo` for `f(U¹) ⊆ V¹`.
* `B → A` fails for a genuine reason: every conjunct of `A` is stated for an arbitrary domain
  (`IsSc0.shift`: any `U ⊆ E₀`; `IsSc1With.shift`, `IsSck.shift`, `IsScSmooth.shift`: any
  `IsScDomain U`, e.g. a closed disc in a finite-dimensional `E`, which is not relatively open in a
  partial quadrant), while `B` only covers relatively open subsets of partial quadrants.  On those
  domains `IsSc0.shift`, `IsSck.shift` and `IsScSmooth.shift` follow from `B`
  (`B_shift_quadrant`, `B_smooth_shift_quadrant`, taking `V = C' = F₀`);
  `IsScDomain.shift` is a fact about the domain class that `B` does not address (re-proved
  outright, `isScDomain_shift'`).  `IsSc1With.shift` additionally names the derivative family
  (`levelDeriv D 1`), which `B` (an `IsSc1` existence statement) does not; on those domains it
  follows too (`B_sc1With_shift_quadrant`: the family given by `B` agrees with `levelDeriv D 1` on
  `U₂` by uniqueness of derivatives and the density of `E₂` in `E₁`).  So the only gap is the
  domain class. -/

namespace RoundTrip.V1_16
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.IsSc0.shift) ∧ (type_of% @Polyfold.IsSc1With.shift) ∧
    (type_of% @Polyfold.IsSck.shift) ∧ (type_of% @Polyfold.IsScSmooth.shift) ∧
    (type_of% @Polyfold.IsScDomain.shift)

theorem A_holds : A :=
  ⟨@Polyfold.IsSc0.shift, @Polyfold.IsSc1With.shift, @Polyfold.IsSck.shift,
    @Polyfold.IsScSmooth.shift, @Polyfold.IsScDomain.shift⟩

/-- The blind `levelTo f 1 1` is the project's `levelMap f 1`. -/
theorem levelTo_eq {E F : ScBanach} (f : E 0 → F 0) : levelTo f 1 1 = levelMap f 1 := rfl

theorem A_to_B : A → B := by
  intro hA E F C U C' V f k hU _ hfV hf
  obtain ⟨-, -, hk, -, -⟩ := hA
  exact ⟨hf.isSc0.levelMap_mapsTo hfV 1, hk hU.isScDomain hf⟩

/-- `F₀` is relatively open in the partial quadrant `F₀`. -/
theorem relOpen_univ (F : ScBanach) : IsRelOpenInQuadrant F univ univ :=
  ⟨isPartialQuadrant_univ F, univ, isOpen_univ, (inter_self _).symm⟩

/-- `B → A`, restricted to relatively open subsets of partial quadrants: the `IsSck.shift`
conjunct (hence `IsSc0.shift` for `k = 0`). -/
theorem B_shift_quadrant (hB : B) {E F : ScBanach} {C U : Set (E 0)}
    (hU : IsRelOpenInQuadrant E C U) {f : E 0 → F 0} {k : ℕ} (hf : IsSck k E F U f) :
    IsSck k E.shift F.shift (E.lvlSet U 1) (levelMap f 1) :=
  (hB E F C U univ univ f k hU (relOpen_univ F) (mapsTo_univ _ _) hf).2

theorem B_sc0_shift_quadrant (hB : B) {E F : ScBanach} {C U : Set (E 0)}
    (hU : IsRelOpenInQuadrant E C U) {f : E 0 → F 0} (hf : IsSc0 E F U f) :
    IsSc0 E.shift F.shift (E.lvlSet U 1) (levelMap f 1) :=
  B_shift_quadrant (k := 0) hB hU hf

/-- `B → A`, restricted: the `IsScSmooth.shift` conjunct. -/
theorem B_smooth_shift_quadrant (hB : B) {E F : ScBanach} {C U : Set (E 0)}
    (hU : IsRelOpenInQuadrant E C U) {f : E 0 → F 0} (hf : IsScSmooth U f) :
    IsScSmooth (E := E.shift) (F := F.shift) (E.lvlSet U 1) (levelMap f 1) :=
  fun k => B_shift_quadrant hB hU (hf k)

/-- `IsScDomain.shift`, re-proved outright (a fact about the domain class, not addressed by `B`). -/
theorem isScDomain_shift' {E : ScBanach} {U : Set (E 0)} (hU : IsScDomain E U) :
    IsScDomain E.shift (E.lvlSet U 1) where
  relOpenConvex m := by rw [E.shift_lvlSet]; exact hU.relOpenConvex (m + 1)
  uniqueDiffWithinAt m x hx := by
    rw [E.shift_lvlSet] at hx ⊢; exact hU.uniqueDiffWithinAt (m + 1) x hx

/-- An sc¹ derivative family can be replaced by one agreeing with it on `U₁`. -/
theorem isSc1With_congr_deriv {E F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0}
    {D D' : E 1 → E 0 →L[ℝ] F 0} (h : IsSc1With U f D) (hD : ∀ x ∈ E.lvlSet U 1, D x = D' x) :
    IsSc1With U f D' where
  isSc0 := h.isSc0
  hasFDerivWithinAt x hx := by rw [← hD x hx]; exact h.hasFDerivWithinAt x hx
  tangent_isSc0 := h.tangent_isSc0.congr fun p hp => by
    change (levelMap f 1 p.1, D p.1 p.2) = (levelMap f 1 p.1, D' p.1 p.2)
    rw [hD p.1 hp]

/-- `B → A` on relatively open subsets of partial quadrants: `IsSc1With.shift`, with its named
derivative family `levelDeriv D 1`.  `B` (with `k = 1`) gives some derivative family `D'` of
`f : U¹ → F¹`; it agrees with `levelDeriv D 1` on `(U¹)₁ = U₂` by the uniqueness of derivatives of
`f : U₂ → F₀` and the density of `E₂` in `E₁`. -/
theorem B_sc1With_shift_quadrant (hB : B) {E F : ScBanach} {C U : Set (E 0)}
    (hUC : IsRelOpenInQuadrant E C U) {f : E 0 → F 0} {D : E 1 → E 0 →L[ℝ] F 0}
    (h : IsSc1With U f D) :
    IsSc1With (E := E.shift) (F := F.shift) (E.lvlSet U 1) (levelMap f 1) (levelDeriv D 1) := by
  have hk : IsSck 1 E F U f := ⟨h.isSc1, h.isSc1.tangentMap_isSc0⟩
  obtain ⟨D', hD'⟩ := (B_shift_quadrant hB hUC hk).1
  refine isSc1With_congr_deriv hD' fun x hx => ?_
  have hx2 : x ∈ E.lvlSet U (1 + 1) := by rw [← E.shift_lvlSet]; exact hx
  set z : E 1 := E.shift.toBase 1 x with hz
  -- the two derivatives of `f : U₂ → F₀` at `x`
  have h1 : HasFDerivWithinAt (f ∘ E.toBase 1 ∘ E.shift.toBase 1)
      ((F.toBase 1).comp ((D' x).comp (E.shift.toBase 1)))
      (E.shift.lvlSet (E.lvlSet U 1) 1) x := by
    have := (F.toBase 1).hasFDerivAt.comp_hasFDerivWithinAt x (hD'.hasFDerivWithinAt x hx)
    refine this.congr (fun y hy => ?_) ?_
    · exact (h.isSc0.toBase_levelMap (m := 1) (x := E.shift.toBase 1 y) hy).symm
    · exact (h.isSc0.toBase_levelMap (m := 1) (x := E.shift.toBase 1 x) hx).symm
  have h2 : HasFDerivWithinAt (f ∘ E.toBase 1 ∘ E.shift.toBase 1)
      (((D z).comp (E.toBase 1)).comp (E.shift.toBase 1))
      (E.shift.lvlSet (E.lvlSet U 1) 1) x :=
    (h.hasFDerivWithinAt z hx).comp x (E.shift.toBase 1).hasFDerivWithinAt fun y hy => hy
  have huniq := (isScDomain_shift' hUC.isScDomain).uniqueDiffWithinAt 1 x hx
  have heq := huniq.eq h1 h2
  have hdense : Dense (Submodule.span ℝ (range (E.shift.toBase 1)) : Set (E 1)) :=
    Dense.mono Submodule.subset_span (E.shift.denseRange_inclK 0 1)
  have h3 : (F.toBase 1).comp (D' x) = (D z).comp (E.toBase 1) := by
    refine ContinuousLinearMap.ext_on hdense ?_
    rintro _ ⟨u, rfl⟩
    exact congrArg (fun L : E.shift 1 →L[ℝ] F 0 => L u) heq
  ext v
  apply F.toBase_injective 1
  rw [h.toBase_levelDeriv (m := 1) hx2 v]
  exact congrArg (fun L : E 1 →L[ℝ] F 0 => L v) h3

#rt_check RoundTrip.V1_16.B_sc1With_shift_quadrant [Polyfold.IsSc0.shift,
  Polyfold.IsSc1With.shift, Polyfold.IsSck.shift, Polyfold.IsScSmooth.shift,
  Polyfold.IsScDomain.shift]
#rt_check RoundTrip.V1_16.A_to_B [Polyfold.IsSc0.shift, Polyfold.IsSc1With.shift,
  Polyfold.IsSck.shift, Polyfold.IsScSmooth.shift, Polyfold.IsScDomain.shift]
#rt_check RoundTrip.V1_16.B_shift_quadrant [Polyfold.IsSc0.shift, Polyfold.IsSc1With.shift,
  Polyfold.IsSck.shift, Polyfold.IsScSmooth.shift, Polyfold.IsScDomain.shift]
#rt_check RoundTrip.V1_16.B_smooth_shift_quadrant [Polyfold.IsSc0.shift, Polyfold.IsSc1With.shift,
  Polyfold.IsSck.shift, Polyfold.IsScSmooth.shift, Polyfold.IsScDomain.shift]
#rt_check RoundTrip.V1_16.isScDomain_shift' [Polyfold.IsSc0.shift, Polyfold.IsSc1With.shift,
  Polyfold.IsSck.shift, Polyfold.IsScSmooth.shift, Polyfold.IsScDomain.shift]

end RoundTrip.V1_16
