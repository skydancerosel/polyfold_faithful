import Polyfold.Chapter16.OrientationNonEffectiveWitness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021): a strong bundle over the
translation groupoid of the trivial action of `ℤ/3`, for any M-polyfold and any strong bundle
over it.  It is used as a base which is not effective in the witnesses of Corollary 15.4.4
(§15.4, p. 703) and Definition 16.6.5 (§16.6).

# The trivial action of `ℤ/3` on a strong bundle

For an M-polyfold `P` on `U` and a strong bundle `B : W → U` over `P`:

* `z3Groupoid P`: the ep-groupoid `ℤ/3 × U ⇉ U` with `s = t = π₂` (Chapter 7's
  `actionEpGroupoid` for the trivial action); `z3EpBundleOf P B`: `B` with `μ((g, x), w) = w`
  (Definition 8.3.1); `z3SEPOf P B`, the object of `SEP`.
* `ne_unit_z3SEPOf`, `not_isEffective_z3SEPOf`: for `U ≠ ∅` there is a morphism which is not a
  unit, and the base is not effective (Definition 7.2.1).
* `hasParacompactOrbitSpace_z3SEPOf` (`U` second countable), `isZhou_z3SEPOf` (every isotropy
  group acts trivially, `T_x = G_x`), `isLRLocal_z3SEPOf` (Definition 8.4.2 read as
  `IsLRLocal`), `injective_π_z3SEPOf` (`|X| = U`).
* `isScFredholmSectionFunctor_z3SEPOf`: an sc-Fredholm section of `B` is an sc-Fredholm section
  functor (the action on the fibres is trivial).
* **`orMor_z3SEPOf`**: every morphism `(g, x)` acts as the identity on `Or^f_x` (its third power
  is `1_x` and `Or^f_x` has two elements); `isOrInvariant_z3SEPOf`: every family of
  orientations is invariant (Definition 12.5.4).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

namespace TrivialIsotropy

open SBLocalization StrongBundle EpGroupoid EpStrongBundle

/-- The trivial action of `ℤ/3 = Multiplicative (ZMod 3)` on a type. -/
scoped instance instMulActionZ3Trivial (U : Type) : MulAction (Multiplicative (ZMod 3)) U where
  smul _ y := y
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem z3_smul_eq_trivial {U : Type} (g : Multiplicative (ZMod 3)) (y : U) : g • y = y := rfl

variable {U : Type} [TopologicalSpace U] [T2Space U] [ParacompactSpace U] (P : MPolyfold U)

/-- **`ℤ/3 × U ⇉ U`**: the translation groupoid of the trivial action of `ℤ/3` on the
M-polyfold `P` (`s = t = π₂`). -/
def z3Groupoid : EpGroupoid U (Multiplicative (ZMod 3) × U) :=
  EpGroupoid.Examples.actionEpGroupoid (K := Multiplicative (ZMod 3)) (P := P)
    fun _ => MPolyfold.isScSmoothMap_id

theorem z3Groupoid_tgt (σ : Multiplicative (ZMod 3) × U) : (z3Groupoid P).tgt σ = σ.2 := rfl

theorem z3Groupoid_src (σ : Multiplicative (ZMod 3) × U) : (z3Groupoid P).src σ = σ.2 := rfl

variable {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {p : W → U}
  [∀ x, AddCommGroup (p ⁻¹' {x})] [∀ x, Module ℝ (p ⁻¹' {x})]

/-- **The strong bundle `B` over `ℤ/3 × U ⇉ U`** (Definition 8.3.1): `μ((g, x), w) = w`. -/
def z3EpBundleOf (B : StrongBundle P p) : EpStrongBundle (z3Groupoid P) B where
  μ := pullbackProj' p (z3Groupoid P).src
  isStrongBundleMap := by
    have := B.paracompactSpace_pullback (z3Groupoid P).PMor (z3Groupoid P).src
    exact B.isStrongBundleMap_pullbackProj' (z3Groupoid P).isScSmoothMap_src
  surjective w := ⟨⟨((1, p w), w), rfl⟩, rfl⟩
  isLocalScDiffeo := by
    have := B.paracompactSpace_pullback (z3Groupoid P).PMor (z3Groupoid P).src
    exact B.isLocalScDiffeo_pullbackProj' (z3Groupoid P).isScSmoothMap_src
      (z3Groupoid P).isLocalScDiffeo_src
  μ_unit _ := rfl
  μ_comp _ _ _ _ _ := rfl

/-- `B` over `ℤ/3 × U ⇉ U` as an object of `SEP`. -/
def z3SEPOf (B : StrongBundle P p) : SEP.{0} :=
  ⟨U, _, z3Groupoid P, W, p, B, z3EpBundleOf P B⟩

variable {P} (B : StrongBundle P p)

theorem z3SEPOf_tgt (σ : (z3SEPOf P B).Mor) : (z3SEPOf P B).X.tgt σ = (z3SEPOf P B).X.src σ :=
  rfl

/-- **A morphism which is not a unit**: `(1, y)` with `1 ≠ 0` in `ℤ/3`. -/
theorem ne_unit_z3SEPOf (y : U) :
    ∃ σ : (z3SEPOf P B).Mor, σ ≠ (z3SEPOf P B).X.unit ((z3SEPOf P B).X.src σ) :=
  ⟨(Multiplicative.ofAdd (1 : ZMod 3), y), fun h => by
    have h1 : Multiplicative.ofAdd (1 : ZMod 3) = 1 := congrArg Prod.fst h
    exact absurd h1 (by decide)⟩

/-- **`ℤ/3 × U ⇉ U` is not effective** (Definition 7.2.1) for `U ≠ ∅`. -/
theorem not_isEffective_z3SEPOf (y : U) : ¬ (z3SEPOf P B).X.IsEffective := by
  intro h
  have hne : Multiplicative.ofAdd (1 : ZMod 3) ≠ 1 := by decide
  obtain ⟨ψ, -, hψ⟩ := h y ⟨(Multiplicative.ofAdd 1, y), rfl, rfl⟩ (fun h1 => hne
    (congrArg (fun g : (z3SEPOf P B).X.Isotropy y => g.val.1) h1)) univ isOpen_univ (mem_univ _)
  exact hψ rfl

/-- `|ℤ/3 × U ⇉ U|` is paracompact for a second countable `U`. -/
theorem hasParacompactOrbitSpace_z3SEPOf [SecondCountableTopology U] :
    (z3SEPOf P B).X.HasParacompactOrbitSpace :=
  EpGroupoid.Examples.hasParacompactOrbitSpace_action (K := Multiplicative (ZMod 3)) (P := P)
    fun _ => MPolyfold.isScSmoothMap_id

/-- `T_x = G_x`: every element of the isotropy group acts trivially. -/
theorem trivialSubgroup_z3SEPOf (x : U) : (z3SEPOf P B).X.trivialSubgroup x = ⊤ :=
  eq_top_iff.2 fun _ _ => (z3SEPOf P B).X.mem_trivialSet_iff_eventually.2
    (Eventually.of_forall fun _ => rfl)

/-- **(ZHOU)** for `ℤ/3 × U ⇉ U`. -/
theorem isZhou_z3SEPOf : (z3SEPOf P B).X.IsZhou :=
  isZhou_of_trivialSubgroup_eq_top _ (trivialSubgroup_z3SEPOf B)

/-- **The local regularity property** (Definition 8.4.2 read as `IsLRLocal`): a strong bundle
isomorphism of `W|U(x)` with `|Φ(w)| = |w|` is the identity, since the orbits are points. -/
theorem isLRLocal_z3SEPOf : (z3SEPOf P B).E.IsLRLocal := by
  intro x O hO hxO
  obtain ⟨R, hRO⟩ := (z3SEPOf P B).X.theorem_7_1_13 x hO hxO
  refine ⟨R, hRO, fun β Φ _ hπ => ⟨1, fun w hw => ?_⟩⟩
  obtain ⟨q, h1, h2⟩ := (GroupoidStr.π_eq_π_iff _).1 (hπ w hw)
  exact h1.symm.trans h2

/-- **`|X| = U`**: the orbits of the trivial action are points. -/
theorem injective_π_z3SEPOf : Function.Injective (z3SEPOf P B).X.π := fun a b h => by
  obtain ⟨σ, h1, h2⟩ := (z3SEPOf P B).X.π_eq_π_iff.1 h
  exact h1.symm.trans h2

/-- **An sc-Fredholm section of `B` is an sc-Fredholm section functor over `ℤ/3 × U ⇉ U`**
(Definition 8.3.4): `f(t(g, x)) = f(x) = μ((g, x), f(x))`. -/
theorem isScFredholmSectionFunctor_z3SEPOf {f : U → W} (hs : B.IsScSmoothSection f)
    (hf : B.IsScFredholmSection f) : (z3SEPOf P B).E.IsScFredholmSectionFunctor f :=
  ⟨⟨hs, fun _ => rfl⟩, hf⟩

/-- **Every morphism `(g, x)` of `ℤ/3 × U ⇉ U` acts as the identity on `Or^f_x`**: its third
power is `1_x`, and `Or^f_x` has two elements. -/
theorem orMor_z3SEPOf {f : U → W} (hF : (z3SEPOf P B).E.IsScFredholmSectionFunctor f)
    (hsec : B.HasScPlusSectionsThrough) (σ : (z3SEPOf P B).Mor)
    (hs : (z3SEPOf P B).X.src σ ∈ (z3SEPOf P B).X.PObj.smoothSet)
    (o : Orx (B := B) f hF.2 ((z3SEPOf P B).X.src σ) hs) :
    (z3SEPOf P B).E.orMor hF hsec σ rfl rfl hs hs o = o := by
  refine equiv_eq_self_of_two_of_cube (exists_two_orx hF.2 hs hsec)
    ((z3SEPOf P B).E.orMor hF hsec σ rfl rfl hs hs) (fun o => ?_) o
  have c₁ := (z3SEPOf P B).E.orMor_comp (hF := hF) (hsec := hsec) (φ := σ) (ψ := σ) rfl rfl rfl
    rfl hs hs hs
  have c₂ := (z3SEPOf P B).E.orMor_comp (hF := hF) (hsec := hsec)
    (φ := (z3SEPOf P B).X.comp σ σ) (ψ := σ) (x := (z3SEPOf P B).X.src σ)
    (y := (z3SEPOf P B).X.src σ) (z := (z3SEPOf P B).X.src σ) rfl rfl rfl rfl hs hs hs
  have hg : ∀ g : Multiplicative (ZMod 3), g * (g * g) = 1 := by decide
  have hu : (z3SEPOf P B).X.comp σ ((z3SEPOf P B).X.comp σ σ) =
      (z3SEPOf P B).X.unit ((z3SEPOf P B).X.src σ) :=
    Prod.ext (hg σ.1) rfl
  have c₃ := (z3SEPOf P B).E.orMor_unit hF hsec hu rfl rfl hs
  have e₁ := DFunLike.congr_fun c₁ o
  have e₂ := DFunLike.congr_fun c₂ o
  have e₃ := DFunLike.congr_fun c₃ o
  rw [Equiv.trans_apply] at e₁ e₂
  exact (congrArg _ e₁).trans (e₂.trans e₃)

/-- **Every family of orientations is invariant under the morphisms** of `ℤ/3 × U ⇉ U`
(Definition 12.5.4). -/
theorem isOrInvariant_z3SEPOf {f : U → W} (hF : (z3SEPOf P B).E.IsScFredholmSectionFunctor f)
    (hsec : B.HasScPlusSectionsThrough)
    (o : ∀ x (hs : x ∈ (z3SEPOf P B).X.PObj.smoothSet), Orx (B := B) f hF.2 x hs) :
    (z3SEPOf P B).E.IsOrInvariant hF hsec o := by
  intro σ x x' hx hx' hs hs'
  obtain rfl : (z3SEPOf P B).X.src σ = x := hx
  obtain rfl : (z3SEPOf P B).X.src σ = x' := hx'
  exact orMor_z3SEPOf B hF hsec σ hs (o _ hs)

end TrivialIsotropy

end Polyfold
