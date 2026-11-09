import Polyfold.Chapter3.GlobalIFT
import Polyfold.Chapter3.FredholmGermIndex

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.4,
**Corollary 3.4.3 (preprint 3.39)** (composition of Theorem 3.38 with a given conjugation to a basic germ), with
the calculus of strong bundle isomorphisms it uses: linear ones from sc-operators, the index
raise of a strong bundle isomorphism, composition, and the composition of push-forwards.

# Corollary 3.4.3 (preprint 3.39)

## The text, paraphrased

(Corollary 3.4.3 (preprint 3.39)) If the sc-germ `g : O(C, 0) → (F, 0)` is equivalent by a strong bundle
isomorphism `Φ` to the basic germ `Φ_* g`, and `s : O(C, 0) → (F, 0)` is an sc⁺-germ, then there
is a strong bundle map `Ψ` such that `((Ψ ∘ Φ)_*(g + s))¹` is a basic germ.  *Proof.* `Φ` covers
an sc-diffeomorphism `ϕ : (U, 0) → (V, 0)` with `Φ_* g = h` basic; `t = Φ_* s` is an sc⁺-section
with `t(0) = 0` and `Φ_*(g + s) = h + t`; Theorem 3.4.2 (preprint 3.38) gives `Ψ` with `(Ψ_*(h + t))¹` basic; take
`Γ = Ψ ∘ Φ`.

## What is formalized

* `Polyfold.ScOperator.prodMap`, `ScOperator.isStrongBundleMap_prodMap`,
  `ScOperator.isStrongBundleIso_prodMap`: a pair of sc-operators `S : E → E'`, `T : F → F'` gives
  the strong bundle map `(u, k) ↦ (Su, Tk)`; with inverse sc-operators (on the base only over `U`)
  a strong bundle isomorphism.  The axioms on `[0]` and `[1]` are the sc-smoothness of the
  sc-operators `S ⊕ T` and `S ⊕ T¹`.
* `Polyfold.strongShift Ψ = Ψ¹` (the level-`1` map) and `IsStrongBundleMap.shift`,
  `IsStrongBundleIso.shift`: **the index raise of a strong bundle map** `U ◁ F → U' ◁ F'` is a
  strong bundle map `U¹ ◁ F¹ → U'¹ ◁ F'¹` (its `[0]` is the shift of `[0]`, its `[1]` the shift
  of `[1]`, Proposition 1.2.2 (preprint 1.17)), with `toBase_strongShift` (`ι Ψ¹ = Ψ ι` on `U₁ ⊕ F₁`).
* `IsStrongBundleMap.comp`, `IsStrongBundleIso.comp` (with `IsStrongBundleMap.base_comp`,
  `shiftFiber_comp`): **the composition** of strong bundle maps/isomorphisms; and
  `IsStrongBundleIso.pushforward_comp`: **`(Λ ∘ Φ)_* = Λ_* ∘ Φ_*`** on the target of `Λ`.
* `Polyfold.StabilityData.linIso` (`Λ = (ψ, Ψ)` of Theorem 3.4.2 (preprint 3.38) on the index-raised
  structures: base `split`, fibre `fiber`), `StabilityData.linIso_isStrongBundleIso`:
  **Theorem 3.4.2 (preprint 3.38)'s coordinate change is a strong bundle isomorphism**
  `U ◁ (ℝᴺ ⊕ W)¹ → ψ(U) ◁ ((ℝᴺ ⊕ Z) ⊕ X¹)` between the shifted structures, for every relatively
  open `U` in the shifted quadrant; `ψ(U) = glue⁻¹(U)` is relatively open in `(C̃ ⊕ C) ⊕ X¹`
  (`StabilityData.isRelOpen_glue_preimage`).  Before the index raise: `StabilityData.linIso₀`
  (`split₀`, `fiber₀`), `linIso₀_isStrongBundleIso`, and `StabilityData.strongShift_linIso₀`
  (`(Λ₀)¹ = Λ`); `IsStrongBundleMap.strongShift_comp` (`(Λ ∘ Φ)¹ = Λ¹ ∘ Φ¹`).
* `Polyfold.ConjugationData.pushPlus` (`t = Φ[1]_* s`), `ConjugationData.absorb`
  (`h' = h + (t_{ℝᴺ}, 0)`), and **`Polyfold.corollary_3_4_3`**: for conjugation data `d` of the
  sc-smooth `g` (`Φ = d.Ψ`) and an sc⁺-germ `s` with `s(0) = 0` there are the data `𝒮` of
  Theorem 3.4.2 (preprint 3.38) for `t_W` such that `Φ_*(g + s) = h + t` near `0`, the composite
  `Γ = Λ ∘ Φ¹` (inverse `Φ'¹ ∘ Λ⁻¹`) is a strong bundle isomorphism
  `U¹ ◁ F¹ → ψ(U'¹) ◁ F'` covering an sc-diffeomorphism with `Γ(0) = 0`,
  `Γ_* = Λ_* ∘ Φ¹_*`, the push-forward `𝒮.pushMap h'` is a basic germ (Theorem 3.4.2 (preprint 3.38)), and
  `(Γ(u, (g + s)¹(u)))₂ = 𝒮.pushMap h'(γ(u))` for `u ∈ U¹` near `0`;
  `Polyfold.corollary_3_4_3_isConjugate`: `(g + s)¹` is conjugated to a basic germ
  (`IsConjugateToBasicGerm` on the shifted structure `E¹`, `F¹`);
  `Polyfold.ConjugationData.compIso_eq_strongShift`: the text's form `Γ = (Ψ ∘ Φ)¹`, i.e.
  `Λ₀ ∘ Φ` is a strong bundle isomorphism on level `0` and its index raise is `Λ ∘ Φ¹`.

## What the text leaves implicit, and the choices made (the findings)

* **"`g` is equivalent by a strong bundle isomorphism `Φ` to the basic germ `Φ_* g`"** is read as
  `IsConjugateToBasicGerm U g` (Definition 3.1.11 (preprint 3.11), second paragraph): `Φ` is a strong bundle
  isomorphism `U ◁ F → U' ◁ (ℝᴺ ⊕ W)` covering `ϕ` with `ϕ(0) = 0` and `(Φ(u, g(u)))₂ = h(ϕ(u))`
  near `0` for a basic germ `h` on a germ inside `U'`.  "Sc-germ" is read as: `g` sc-smooth on `U`
  (needed for `(g + s)¹` to take values on level `1`).  `s(0) = 0` is the text's `(F, 0)`.
* **The index raise.**  `((Ψ ∘ Φ)_*(g + s))¹` is a germ on the shifted spaces; in Lean the
  conclusion is a conjugation of `(g + s)¹ : U¹ → F¹` (the level-`1` map) on the shifted structures
  `E¹ ◁ F¹`, so the strong bundle isomorphism of the conclusion lives there too.  It is
  `Γ = Λ ∘ Φ¹`: the index raise `Φ¹` of the given `Φ` (a strong bundle isomorphism of the shifted
  structures, `IsStrongBundleIso.shift`; the text uses this silently) followed by the linear
  `Λ` of Theorem 3.4.2 (preprint 3.38) on the shifted structures, where the contraction normal form holds.  The
  text's "`Γ = Ψ ∘ Φ`, then raise the index" is the same map: `Λ₀ ∘ Φ` is a strong bundle
  isomorphism on level `0` and `(Λ₀ ∘ Φ)¹ = Λ₀¹ ∘ Φ¹ = Λ ∘ Φ¹` on `U¹ ⊕ F¹`
  (`ConjugationData.compIso_eq_strongShift`).
* **`Φ_*(g + s) = h + t`** holds only near `0` (where the conjugation identity holds), and
  `t = Φ_* s = (u' ↦ Φ[1](ϕ⁻¹u', s(ϕ⁻¹u'))₂)` has an `ℝᴺ`-component, which the data of
  Theorem 3.4.2 (preprint 3.38) do not carry; it is absorbed into the basic germ `h' = h + (t_{ℝᴺ}, 0)`
  (Finding 85, as in `theorem_3_6_8_graph_wholeChart`).  Then `Φ_*(g + s) = 𝒮.fsum h'` near `0`.
* **"There exists a strong bundle map `Ψ`"**: the `Ψ` of Theorem 3.4.2 (preprint 3.38) is a strong bundle
  *isomorphism* (`linIso_isStrongBundleIso`), so the composite is one, which is what
  `IsConjugateToBasicGerm` needs.  The text's `τ : Z → C` is not applied (Finding 60): the new
  target is `(ℝᴺ ⊕ Z) ⊕ X¹`, the new parameter space `ℝⁿ ⊕ C`.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

variable {E F E' F' E'' F'' : ScBanach}

/-! ### Strong bundle isomorphisms from sc-operators -/

/-- The direct sum `S ⊕ T : E ⊕ F → E' ⊕ F'` of two sc-operators. -/
def ScOperator.prodMap (S : ScOperator E E') (T : ScOperator F F') :
    ScOperator (E.prod F) (E'.prod F') where
  lvl m := (S m).prodMap (T m)
  incl_comm m x := Prod.ext (S.incl_comm m x.1) (T.incl_comm m x.2)

@[simp] lemma ScOperator.prodMap_apply (S : ScOperator E E') (T : ScOperator F F') (m : ℕ)
    (p : (E.prod F) m) : S.prodMap T m p = (S m p.1, T m p.2) := rfl

section Linear

variable {C : Set (E 0)} {C' : Set (E' 0)} {U : Set (E 0)} {U' : Set (E' 0)}

/-- **A pair of sc-operators is a strong bundle map**: `(u, k) ↦ (Su, Tk)` on `U ◁ F → U' ◁ F'`
when `S` maps `U` into `U'`; on `[0]` it is the sc-operator `S ⊕ T`, on `[1]` the sc-operator
`S ⊕ T¹`. -/
theorem ScOperator.isStrongBundleMap_prodMap (hU : IsRelOpenInQuadrant E C U)
    (S : ScOperator E E') (T : ScOperator F F') (hSU : MapsTo (S 0) U U') :
    IsStrongBundleMap U U' (fun p : E 0 × F 0 => (S 0 p.1, T 0 p.2)) where
  mapsTo p hp := ⟨hSU hp.1, mem_univ _⟩
  fst_independent _ _ _ _ := rfl
  fiber_linear _ _ := ⟨fun a b => map_add (T 0) a b, fun c a => map_smul (T 0) c a⟩
  preserves_filtration m k _ u _ hum h hh := by
    obtain ⟨um, rfl⟩ := hum
    obtain ⟨hk, rfl⟩ := hh
    exact ⟨⟨S m um, S.toBase_comm m um⟩, ⟨T k hk, T.toBase_comm k hk⟩⟩
  isScSmooth_zero :=
    ((S.prodMap T).isScSmooth (hU.prod_univ F).isScDomain).congr (hU.prod_univ F).isScDomain
      fun _ _ => rfl
  isScSmooth_one := by
    refine ((S.prodMap T.shiftOp).isScSmooth (hU.prod_univ F.shift).isScDomain).congr
      (hU.prod_univ F.shift).isScDomain fun p _ => ?_
    refine Prod.ext rfl ?_
    change T 1 p.2 = Function.invFun (F'.toBase 1) (T 0 (F.toBase 1 p.2))
    rw [← T.toBase_comm]
    exact (Function.leftInverse_invFun (F'.toBase_injective 1) _).symm

/-- **A pair of sc-isomorphisms is a strong bundle isomorphism**: `(u, k) ↦ (Su, Tk)` with
inverse `(u', k') ↦ (S'u', T'k')`, when `S`, `S'` are inverse on `U`, `U'` and `T`, `T'` are
inverse. -/
theorem ScOperator.isStrongBundleIso_prodMap (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsRelOpenInQuadrant E' C' U') (S : ScOperator E E') (S' : ScOperator E' E)
    (T : ScOperator F F') (T' : ScOperator F' F) (hSU : MapsTo (S 0) U U')
    (hS'U : MapsTo (S' 0) U' U) (hS'S : ∀ u ∈ U, S' 0 (S 0 u) = u)
    (hSS' : ∀ u' ∈ U', S 0 (S' 0 u') = u') (hT'T : ∀ k, T' 0 (T 0 k) = k)
    (hTT' : ∀ k', T 0 (T' 0 k') = k') :
    IsStrongBundleIso U U' (fun p : E 0 × F 0 => (S 0 p.1, T 0 p.2))
      (fun p : E' 0 × F' 0 => (S' 0 p.1, T' 0 p.2)) where
  toFun := S.isStrongBundleMap_prodMap hU T hSU
  invFun := S'.isStrongBundleMap_prodMap hU' T' hS'U
  left_inv p hp := Prod.ext (hS'S p.1 hp.1) (hT'T p.2)
  right_inv p hp := Prod.ext (hSS' p.1 hp.1) (hTT' p.2)

end Linear

/-! ### The index raise of a strong bundle map -/

/-- The level-`1` map `Ψ¹ : E₁ ⊕ F₁ → E'₁ ⊕ F'₁` of `Ψ : E₀ ⊕ F₀ → E'₀ ⊕ F'₀` (the text's index
raise `(·)¹`): the map of the shifted structures `E¹ ◁ F¹ → E'¹ ◁ F'¹`. -/
def strongShift (Ψ : E 0 × F 0 → E' 0 × F' 0) : E.shift 0 × F.shift 0 → E'.shift 0 × F'.shift 0 :=
  levelMap (E := E.prod F) (F := E'.prod F') Ψ 1

namespace IsStrongBundleMap

variable {C : Set (E 0)} {U : Set (E 0)} {U' : Set (E' 0)} {Ψ : E 0 × F 0 → E' 0 × F' 0}
  (hΨ : IsStrongBundleMap U U' Ψ)
include hΨ

/-- `ι Ψ¹(p) = Ψ(ι p)` on `U₁ ⊕ F₁`. -/
lemma toBase_strongShift {p : E 1 × F 1} (hp : E.toBase 1 p.1 ∈ U) :
    (E'.prod F').toBase 1 (strongShift Ψ p) = Ψ ((E.prod F).toBase 1 p) := by
  refine toBase_levelMap (E := E.prod F) (F := E'.prod F') (f := Ψ) (m := 1) (x := p) ?_
  rw [ScBanach.prod_toBase]
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ :=
    hΨ.preserves_filtration 1 1 (by norm_num) _ hp ⟨p.1, rfl⟩ _ ⟨p.2, rfl⟩
  exact ⟨((a, b) : (E'.prod F') 1), by rw [ScBanach.prod_toBase]; exact Prod.ext ha hb⟩

lemma toBase_strongShift_fst {u : E 1} (hu : E.toBase 1 u ∈ U) (k : F 1) :
    E'.toBase 1 (strongShift Ψ (u, k)).1 = (Ψ (E.toBase 1 u, F.toBase 1 k)).1 := by
  have := congrArg Prod.fst (hΨ.toBase_strongShift (p := (u, k)) hu)
  rwa [ScBanach.prod_toBase, ScBanach.prod_toBase] at this

lemma toBase_strongShift_snd {u : E 1} (hu : E.toBase 1 u ∈ U) (k : F 1) :
    F'.toBase 1 (strongShift Ψ (u, k)).2 = (Ψ (E.toBase 1 u, F.toBase 1 k)).2 := by
  have := congrArg Prod.snd (hΨ.toBase_strongShift (p := (u, k)) hu)
  rwa [ScBanach.prod_toBase, ScBanach.prod_toBase] at this

/-- The base map of `Ψ¹` is the level-`1` map of the base map of `Ψ`. -/
lemma toBase_base_strongShift {u : E 1} (hu : E.toBase 1 u ∈ U) :
    E'.toBase 1 (base (strongShift Ψ) u) = base Ψ (E.toBase 1 u) := by
  have := hΨ.toBase_strongShift_fst hu 0
  rw [map_zero] at this
  exact this

/-- **The index raise of a strong bundle map is a strong bundle map**: `Ψ¹ : U¹ ◁ F¹ → U'¹ ◁ F'¹`
(the shifted structures `E¹`, `F¹`); `(U¹ ◁ F¹)[0]` is the shift of `(U ◁ F)[0]` and
`(U¹ ◁ F¹)[1]` the shift of `(U ◁ F)[1]`, so both sc-smoothness axioms are Proposition 1.2.2 (preprint 1.17). -/
theorem shift (hU : IsRelOpenInQuadrant E C U) :
    IsStrongBundleMap (E := E.shift) (F := F.shift) (E' := E'.shift) (F' := F'.shift)
      (E.lvlSet U 1) (E'.lvlSet U' 1) (strongShift Ψ) where
  mapsTo p hp := by
    obtain ⟨u, k⟩ := p
    refine ⟨?_, mem_univ _⟩
    change E'.toBase 1 (strongShift Ψ (u, k)).1 ∈ U'
    rw [hΨ.toBase_strongShift_fst hp.1]
    exact (hΨ.mapsTo (show (E.toBase 1 u, F.toBase 1 k) ∈ U ×ˢ univ from
      ⟨hp.1, mem_univ _⟩)).1
  fst_independent u hu h h' := E'.toBase_injective 1 (by
    rw [hΨ.toBase_strongShift_fst hu, hΨ.toBase_strongShift_fst hu]
    exact hΨ.fst_independent _ hu _ _)
  fiber_linear u hu := by
    have hl := hΨ.fiber_linear _ hu
    refine ⟨fun a b => F'.toBase_injective 1 ?_, fun c a => F'.toBase_injective 1 ?_⟩
    · rw [map_add, hΨ.toBase_strongShift_snd hu, hΨ.toBase_strongShift_snd hu,
        hΨ.toBase_strongShift_snd hu, map_add]
      exact hl.map_add _ _
    · rw [map_smul, hΨ.toBase_strongShift_snd hu, hΨ.toBase_strongShift_snd hu, map_smul]
      exact hl.map_smul _ _
  preserves_filtration m k hk u hu hum h hh := by
    obtain ⟨um, rfl⟩ := hum
    obtain ⟨hk', rfl⟩ := hh
    obtain ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ := hΨ.preserves_filtration (m + 1) (k + 1) (by omega) _ hu
      ⟨um, (E.shift_toBase m um)⟩ _ ⟨hk', (F.shift_toBase k hk')⟩
    refine ⟨⟨y, E'.toBase_injective 1 ?_⟩, ⟨z, F'.toBase_injective 1 ?_⟩⟩
    · rw [← E'.shift_toBase, hy, hΨ.toBase_strongShift_fst hu]
    · rw [← F'.shift_toBase, hz, hΨ.toBase_strongShift_snd hu]
  isScSmooth_zero := by
    have h := hΨ.isScSmooth_zero.shift (hU.prod_univ F).isScDomain
    have hset : (E.prod F).lvlSet (U ×ˢ univ) 1 = E.lvlSet U 1 ×ˢ (univ : Set (F 1)) := by
      ext p
      rw [ScBanach.mem_lvlSet, ScBanach.prod_toBase]
      simp [ScBanach.mem_lvlSet]
    rw [hset] at h
    exact h
  isScSmooth_one := by
    have h := hΨ.isScSmooth_one.shift (hU.prod_univ F.shift).isScDomain
    have hset : (E.prod F.shift).lvlSet (U ×ˢ univ) 1 =
        E.lvlSet U 1 ×ˢ (univ : Set (F.shift 1)) := by
      ext p
      rw [ScBanach.mem_lvlSet, ScBanach.prod_toBase]
      simp [ScBanach.mem_lvlSet]
    rw [hset] at h
    have h' : IsScSmooth (E := E.shift.prod F.shift.shift) (F := E'.shift.prod F'.shift.shift)
        (E.lvlSet U 1 ×ˢ univ) (levelMap (E := E.prod F.shift) (F := E'.prod F'.shift)
          (shiftFiber Ψ) 1) := h
    refine h'.congr (hU.shift.prod_univ F.shift.shift).isScDomain fun p hp => ?_
    obtain ⟨u, k₂⟩ := p
    have hu : E.toBase 1 u ∈ U := hp.1
    -- `k₁ = ι k₂ ∈ F₁` and the lift of `(Ψ(ιu, ιk₁))₂` to `F'₂`
    obtain ⟨-, ⟨z, hz⟩⟩ := hΨ.preserves_filtration 1 2 (by norm_num) _ hu ⟨u, rfl⟩
      (F.toBase 1 (F.shift.toBase 1 k₂)) ⟨k₂, F.shift_toBase 1 k₂⟩
    have hsnd : (strongShift Ψ (u, F.shift.toBase 1 k₂)).2 = F'.shift.toBase 1 z :=
      F'.toBase_injective 1 (by rw [hΨ.toBase_strongShift_snd hu, ← F'.shift_toBase, hz])
    apply levelMap_eq_of_toBase_eq
    rw [ScBanach.prod_toBase, ScBanach.prod_toBase]
    refine Prod.ext ?_ ?_
    · exact hΨ.toBase_strongShift_fst hu _
    · change F'.shift.toBase 1 (Function.invFun (F'.shift.toBase 1)
          (strongShift Ψ (u, F.shift.toBase 1 k₂)).2) =
        Function.invFun (F'.toBase 1) (Ψ (E.toBase 1 u, F.toBase 1 (F.shift.toBase 1 k₂))).2
      rw [hsnd, Function.leftInverse_invFun (F'.shift.toBase_injective 1) z,
        ← hΨ.toBase_strongShift_snd hu, hsnd]
      exact (Function.leftInverse_invFun (F'.toBase_injective 1) _).symm

end IsStrongBundleMap

namespace IsStrongBundleIso

variable {C : Set (E 0)} {C' : Set (E' 0)} {U : Set (E 0)} {U' : Set (E' 0)}
  {Ψ : E 0 × F 0 → E' 0 × F' 0} {Ψ' : E' 0 × F' 0 → E 0 × F 0}

/-- **The index raise of a strong bundle isomorphism** `Ψ : U ◁ F → U' ◁ F'` is a strong bundle
isomorphism `Ψ¹ : U¹ ◁ F¹ → U'¹ ◁ F'¹` of the shifted structures, with inverse `Ψ'¹`. -/
theorem shift (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U')
    (hΨ : IsStrongBundleIso U U' Ψ Ψ') :
    IsStrongBundleIso (E := E.shift) (F := F.shift) (E' := E'.shift) (F' := F'.shift)
      (E.lvlSet U 1) (E'.lvlSet U' 1) (strongShift Ψ) (strongShift Ψ') where
  toFun := hΨ.toFun.shift hU
  invFun := hΨ.invFun.shift hU'
  left_inv p hp := by
    have hm := (hΨ.toFun.shift hU).mapsTo hp
    apply (E.prod F).toBase_injective 1
    rw [hΨ.invFun.toBase_strongShift hm.1, hΨ.toFun.toBase_strongShift hp.1]
    refine hΨ.left_inv _ ⟨?_, mem_univ _⟩
    rw [ScBanach.prod_toBase]
    exact hp.1
  right_inv p hp := by
    have hm := (hΨ.invFun.shift hU').mapsTo hp
    apply (E'.prod F').toBase_injective 1
    rw [hΨ.toFun.toBase_strongShift hm.1, hΨ.invFun.toBase_strongShift hp.1]
    refine hΨ.right_inv _ ⟨?_, mem_univ _⟩
    rw [ScBanach.prod_toBase]
    exact hp.1

end IsStrongBundleIso

/-! ### Composition of strong bundle maps and of push-forwards -/

namespace IsStrongBundleMap

variable {C : Set (E 0)} {C' : Set (E' 0)} {U : Set (E 0)} {U' : Set (E' 0)}
  {U'' : Set (E'' 0)} {Φ : E 0 × F 0 → E' 0 × F' 0} {Λ : E' 0 × F' 0 → E'' 0 × F'' 0}

/-- The base map of a composition is the composition of the base maps (on `U`). -/
lemma base_comp (hΦ : IsStrongBundleMap U U' Φ) (hΛ : IsStrongBundleMap U' U'' Λ) {u : E 0}
    (hu : u ∈ U) : base (Λ ∘ Φ) u = base Λ (base Φ u) := by
  change (Λ (Φ (u, 0))).1 = (Λ (base Φ u, 0)).1
  rw [hΦ.apply_eq hu 0]
  exact hΛ.fst_independent _ (hΦ.base_mem hu) _ _

/-- `(Λ ∘ Φ)[1] = Λ[1] ∘ Φ[1]` on `U ⊕ F₁`. -/
lemma shiftFiber_comp (hΦ : IsStrongBundleMap U U' Φ) {p : (E.prod F.shift) 0} (hp : p.1 ∈ U) :
    shiftFiber (Λ ∘ Φ) p = shiftFiber Λ (shiftFiber Φ p) := by
  have h2 : ((shiftFiber Φ p).1, F'.toBase 1 (shiftFiber Φ p).2) = Φ (p.1, F.toBase 1 p.2) :=
    Prod.ext rfl (hΦ.toBase_shiftFiber_snd hp)
  change ((Λ (Φ (p.1, F.toBase 1 p.2))).1,
      Function.invFun (F''.toBase 1) (Λ (Φ (p.1, F.toBase 1 p.2))).2) =
    ((Λ ((shiftFiber Φ p).1, F'.toBase 1 (shiftFiber Φ p).2)).1,
      Function.invFun (F''.toBase 1) (Λ ((shiftFiber Φ p).1, F'.toBase 1 (shiftFiber Φ p).2)).2)
  rw [h2]

/-- **The composition of strong bundle maps is a strong bundle map** (Definition 2.6.1 (preprint 2.47)): on `[0]`
and `[1]` by the chain rule, `(Λ ∘ Φ)[1] = Λ[1] ∘ Φ[1]`. -/
theorem comp (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U')
    (hΦ : IsStrongBundleMap U U' Φ) (hΛ : IsStrongBundleMap U' U'' Λ) :
    IsStrongBundleMap U U'' (Λ ∘ Φ) where
  mapsTo := hΛ.mapsTo.comp hΦ.mapsTo
  fst_independent u hu h h' := by
    change (Λ (Φ (u, h))).1 = (Λ (Φ (u, h'))).1
    rw [hΦ.apply_eq hu h, hΦ.apply_eq hu h']
    exact hΛ.fst_independent _ (hΦ.base_mem hu) _ _
  fiber_linear u hu := by
    have hfun : (fun h => ((Λ ∘ Φ) (u, h)).2) =
        (fun k => (Λ (base Φ u, k)).2) ∘ (fun h => (Φ (u, h)).2) := by
      funext h
      simp only [Function.comp_apply]
      rw [← hΦ.apply_eq hu h]
    rw [hfun]
    exact ((IsLinearMap.mk' _ (hΛ.fiber_linear _ (hΦ.base_mem hu))).comp
      (IsLinearMap.mk' _ (hΦ.fiber_linear u hu))).isLinear
  preserves_filtration m k hk u hu hum h hh := by
    obtain ⟨h1, h2⟩ := hΦ.preserves_filtration m k hk u hu hum h hh
    exact hΛ.preserves_filtration m k hk _ (hΦ.mapsTo ⟨hu, mem_univ h⟩).1 h1 _ h2
  isScSmooth_zero := IsScSmooth.comp (hU.prod_univ F).isScDomain (hU'.prod_univ F').isScDomain
    hΛ.isScSmooth_zero hΦ.isScSmooth_zero hΦ.mapsTo
  isScSmooth_one := by
    have h := IsScSmooth.comp (hU.prod_univ F.shift).isScDomain
      (hU'.prod_univ F'.shift).isScDomain hΛ.isScSmooth_one hΦ.isScSmooth_one
      (fun p hp => ⟨(hΦ.mapsTo (show (p.1, F.toBase 1 p.2) ∈ U ×ˢ univ from
        ⟨hp.1, mem_univ _⟩)).1, mem_univ _⟩)
    exact h.congr (hU.prod_univ F.shift).isScDomain fun p hp =>
      (hΦ.shiftFiber_comp (Λ := Λ) hp.1).symm

end IsStrongBundleMap

namespace IsStrongBundleIso

variable {C : Set (E 0)} {C' : Set (E' 0)} {C'' : Set (E'' 0)} {U : Set (E 0)}
  {U' : Set (E' 0)} {U'' : Set (E'' 0)} {Φ : E 0 × F 0 → E' 0 × F' 0}
  {Φ' : E' 0 × F' 0 → E 0 × F 0} {Λ : E' 0 × F' 0 → E'' 0 × F'' 0}
  {Λ' : E'' 0 × F'' 0 → E' 0 × F' 0}

/-- **The composition of strong bundle isomorphisms is a strong bundle isomorphism**, with inverse
the composition of the inverses in the opposite order. -/
theorem comp (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U')
    (hU'' : IsRelOpenInQuadrant E'' C'' U'') (hΦ : IsStrongBundleIso U U' Φ Φ')
    (hΛ : IsStrongBundleIso U' U'' Λ Λ') : IsStrongBundleIso U U'' (Λ ∘ Φ) (Φ' ∘ Λ') where
  toFun := hΦ.toFun.comp hU hU' hΛ.toFun
  invFun := hΛ.invFun.comp hU'' hU' hΦ.invFun
  left_inv p hp := by
    change Φ' (Λ' (Λ (Φ p))) = p
    rw [hΛ.left_inv _ (hΦ.toFun.mapsTo hp), hΦ.left_inv p hp]
  right_inv p hp := by
    change Λ (Φ (Φ' (Λ' p))) = p
    rw [hΦ.right_inv _ (hΛ.invFun.mapsTo hp), hΛ.right_inv p hp]

/-- **Push-forwards compose**: `(Λ ∘ Φ)_* g = Λ_*(Φ_* g)` on the target `U''` of `Λ`. -/
theorem pushforward_comp (hΦ : IsStrongBundleIso U U' Φ Φ') (hΛ : IsStrongBundleIso U' U'' Λ Λ')
    (g : E 0 → F 0) {u'' : E'' 0} (hu'' : u'' ∈ U'') :
    pushforward (Λ ∘ Φ) (Φ' ∘ Λ') g u'' = pushforward Λ Λ' (pushforward Φ Φ' g) u'' := by
  have hw : IsStrongBundleMap.base Λ' u'' ∈ U' := hΛ.invFun.base_mem hu''
  have hbase : IsStrongBundleMap.base (Φ' ∘ Λ') u'' =
      IsStrongBundleMap.base Φ' (IsStrongBundleMap.base Λ' u'') :=
    hΛ.invFun.base_comp hΦ.invFun hu''
  have hv : IsStrongBundleMap.base Φ (IsStrongBundleMap.base Φ' (IsStrongBundleMap.base Λ' u'')) =
      IsStrongBundleMap.base Λ' u'' := hΦ.base_base' hw
  unfold pushforward
  rw [hbase]
  change (Λ (Φ (IsStrongBundleMap.base Φ' (IsStrongBundleMap.base Λ' u''),
      g (IsStrongBundleMap.base Φ' (IsStrongBundleMap.base Λ' u''))))).2 = _
  rw [hΦ.toFun.apply_eq (hΦ.invFun.base_mem hw), hv]

end IsStrongBundleIso

/-- **The index raise commutes with composition**: `(Λ ∘ Φ)¹ = Λ¹ ∘ Φ¹` on `U₁ ⊕ F₁`. -/
theorem IsStrongBundleMap.strongShift_comp {U : Set (E 0)} {U' : Set (E' 0)} {U'' : Set (E'' 0)}
    {Φ : E 0 × F 0 → E' 0 × F' 0} {Λ : E' 0 × F' 0 → E'' 0 × F'' 0}
    (hΦ : IsStrongBundleMap U U' Φ) (hΛ : IsStrongBundleMap U' U'' Λ) {p : E 1 × F 1}
    (hp : E.toBase 1 p.1 ∈ U) : strongShift (Λ ∘ Φ) p = strongShift Λ (strongShift Φ p) := by
  have hm : E'.toBase 1 (strongShift Φ p).1 ∈ U' := by
    obtain ⟨u, k⟩ := p
    rw [hΦ.toBase_strongShift_fst hp]
    exact (hΦ.mapsTo (show (E.toBase 1 u, F.toBase 1 k) ∈ U ×ˢ univ from ⟨hp, mem_univ _⟩)).1
  apply levelMap_eq_of_toBase_eq
  rw [hΛ.toBase_strongShift hm, hΦ.toBase_strongShift hp]
  rfl

/-! ### Theorem 3.4.2 (preprint 3.38)'s coordinate change as a strong bundle isomorphism -/

namespace StabilityData

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P} (𝒮 : StabilityData Ct W) (Q : Type) [NormedAddCommGroup Q]
  [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

/-- **The coordinate change `Λ = (ψ, Ψ)` of Theorem 3.4.2 (preprint 3.38) on the index-raised structures**:
`Λ((a, w), (q, w')) = (ψ(a, w), Ψ(q, w'))` with the linear `ψ(a, w) = ((a, (1 − P₁)w), P₁w)`
(`split`) and `Ψ(q, w') = ((q, (1 − P₂)w'), L⁻¹P₂w')` (`fiber`), from
`(ℝⁿ ⊕ W)¹ ◁ (ℝᴺ ⊕ W)¹` to `((ℝⁿ ⊕ C) ⊕ X¹) ◁ ((ℝᴺ ⊕ Z) ⊕ X¹)`. -/
def linIso : (ScBanach.paramProd P W).shift 0 × (ScBanach.paramProd Q W).shift 0 →
    𝒮.E' 0 × 𝒮.F' Q 0 :=
  fun p => (𝒮.split 0 p.1, 𝒮.fiber 0 p.2)

/-- The inverse `Λ⁻¹ = (ψ⁻¹, Ψ⁻¹)` (`glue`, `fiberInv`). -/
def linIsoInv : 𝒮.E' 0 × 𝒮.F' Q 0 →
    (ScBanach.paramProd P W).shift 0 × (ScBanach.paramProd Q W).shift 0 :=
  fun p => (𝒮.glue 0 p.1, 𝒮.fiberInv 0 p.2)

lemma linIso_apply (p : (ScBanach.paramProd P W).shift 0 × (ScBanach.paramProd Q W).shift 0) :
    𝒮.linIso Q p = (𝒮.split 0 p.1, 𝒮.fiber 0 p.2) := rfl

variable {Q}

lemma base_linIso (y : (ScBanach.paramProd P W).shift 0) :
    IsStrongBundleMap.base (𝒮.linIso Q) y = 𝒮.split 0 y := rfl

/-- `ψ(U) = (ψ⁻¹)⁻¹(U)` is relatively open in `(C̃ ⊕ C) ⊕ X¹` when `U` is relatively open in the
shifted quadrant `(C̃ ⊕ W)¹`. -/
lemma isRelOpen_glue_preimage (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    {U : Set ((ScBanach.paramProd P W).shift 0)}
    (hU : IsRelOpenInQuadrant (ScBanach.paramProd P W).shift
      ((ScBanach.paramProd P W).lvlSet (Ct ×ˢ univ) 1) U) :
    IsRelOpenInQuadrant 𝒮.E' ((Ct ×ˢ univ) ×ˢ univ) (𝒮.glue 0 ⁻¹' U) := by
  obtain ⟨O, hO, hUO⟩ := hU.relOpen
  refine ⟨(hC.const_prod_univ 𝒮.Cs).prod_univ 𝒮.XB.shift, 𝒮.glue 0 ⁻¹' O,
    hO.preimage (𝒮.glue 0).continuous, ?_⟩
  rw [hUO, ScBanach.paramProd_lvlSet]
  ext y
  change 𝒮.glue 0 y ∈ O ∧ 𝒮.glue 0 y ∈ Ct ×ˢ univ ↔ 𝒮.glue 0 y ∈ O ∧ y ∈ (Ct ×ˢ univ) ×ˢ univ
  rw [glue_apply]
  simp only [mem_prod, mem_univ, and_true]

/-- **Theorem 3.4.2 (preprint 3.38)'s coordinate change is a strong bundle isomorphism** of the index-raised
structures: `Λ = (ψ, Ψ) : U ◁ (ℝᴺ ⊕ W)¹ → ψ(U) ◁ ((ℝᴺ ⊕ Z) ⊕ X¹)` with inverse `(ψ⁻¹, Ψ⁻¹)`, for
every `U` relatively open in `(C̃ ⊕ W)¹`.  Base and fibre maps are the linear sc-isomorphisms
`split`/`glue` and `fiber`/`fiberInv` (`ScOperator.isStrongBundleIso_prodMap`). -/
theorem linIso_isStrongBundleIso (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    {U : Set ((ScBanach.paramProd P W).shift 0)}
    (hU : IsRelOpenInQuadrant (ScBanach.paramProd P W).shift
      ((ScBanach.paramProd P W).lvlSet (Ct ×ˢ univ) 1) U) :
    IsStrongBundleIso U (𝒮.glue 0 ⁻¹' U) (𝒮.linIso Q) (𝒮.linIsoInv Q) :=
  ScOperator.isStrongBundleIso_prodMap hU (𝒮.isRelOpen_glue_preimage hC hU) 𝒮.split 𝒮.glue
    𝒮.fiber 𝒮.fiberInv
    (fun u hu => by
      change 𝒮.glue 0 (𝒮.split 0 u) ∈ U
      rw [𝒮.glue_split]; exact hu)
    (fun _ hu' => hu') (fun u _ => 𝒮.glue_split 0 u) (fun u' _ => 𝒮.split_glue 0 u')
    (fun k => 𝒮.fiberInv_fiber 0 k) (fun k' => 𝒮.fiber_fiberInv 0 k')

variable (Q) in
/-- The coordinate change `Λ₀ = (ψ, Ψ)` of Theorem 3.4.2 (preprint 3.38) **before** the index raise, on
`(ℝⁿ ⊕ W) ◁ (ℝᴺ ⊕ W) → ((ℝⁿ ⊕ C) ⊕ X) ◁ ((ℝᴺ ⊕ Z) ⊕ X)` (`split₀`, `fiber₀`); its index raise is
`linIso` (`strongShift_linIso₀`). -/
def linIso₀ : (ScBanach.paramProd P W) 0 × (ScBanach.paramProd Q W) 0 → 𝒮.E₀' 0 × 𝒮.F₀' Q 0 :=
  fun p => (𝒮.split₀ 0 p.1, 𝒮.fiber₀ 0 p.2)

variable (Q) in
/-- The inverse `Λ₀⁻¹ = (glue₀, fiberInv₀)`. -/
def linIsoInv₀ : 𝒮.E₀' 0 × 𝒮.F₀' Q 0 → (ScBanach.paramProd P W) 0 × (ScBanach.paramProd Q W) 0 :=
  fun p => (𝒮.glue₀ 0 p.1, 𝒮.fiberInv₀ 0 p.2)

/-- `ψ(U) = (ψ⁻¹)⁻¹(U)` is relatively open in `(C̃ ⊕ C) ⊕ X` for `U` relatively open in `C̃ ⊕ W`. -/
lemma isRelOpen_glue₀_preimage (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    {U : Set ((ScBanach.paramProd P W) 0)}
    (hU : IsRelOpenInQuadrant (ScBanach.paramProd P W) (Ct ×ˢ univ) U) :
    IsRelOpenInQuadrant 𝒮.E₀' ((Ct ×ˢ univ) ×ˢ univ) (𝒮.glue₀ 0 ⁻¹' U) := by
  obtain ⟨O, hO, hUO⟩ := hU.relOpen
  refine ⟨(hC.const_prod_univ 𝒮.Cs).prod_univ 𝒮.XB, 𝒮.glue₀ 0 ⁻¹' O,
    hO.preimage (𝒮.glue₀ 0).continuous, ?_⟩
  rw [hUO]
  ext y
  change 𝒮.glue₀ 0 y ∈ O ∧ 𝒮.glue₀ 0 y ∈ Ct ×ˢ univ ↔ 𝒮.glue₀ 0 y ∈ O ∧ y ∈ (Ct ×ˢ univ) ×ˢ univ
  rw [glue₀_apply]
  simp only [mem_prod, mem_univ, and_true]

/-- **Theorem 3.4.2 (preprint 3.38)'s coordinate change before the index raise is a strong bundle isomorphism**
`Λ₀ : U ◁ (ℝᴺ ⊕ W) → ψ(U) ◁ ((ℝᴺ ⊕ Z) ⊕ X)` (the text's `Ψ`, "a strong bundle map covering the
sc-diffeomorphism `ψ`"). -/
theorem linIso₀_isStrongBundleIso (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    {U : Set ((ScBanach.paramProd P W) 0)}
    (hU : IsRelOpenInQuadrant (ScBanach.paramProd P W) (Ct ×ˢ univ) U) :
    IsStrongBundleIso U (𝒮.glue₀ 0 ⁻¹' U) (𝒮.linIso₀ Q) (𝒮.linIsoInv₀ Q) :=
  ScOperator.isStrongBundleIso_prodMap hU (𝒮.isRelOpen_glue₀_preimage hC hU) 𝒮.split₀ 𝒮.glue₀
    𝒮.fiber₀ 𝒮.fiberInv₀
    (fun u hu => by
      change 𝒮.glue₀ 0 (𝒮.split₀ 0 u) ∈ U
      rw [𝒮.glue₀_split₀]; exact hu)
    (fun _ hu' => hu') (fun u _ => 𝒮.glue₀_split₀ 0 u) (fun u' _ => 𝒮.split₀_glue₀ 0 u')
    (fun k => 𝒮.fiberInv₀_fiber₀ 0 k) (fun k' => 𝒮.fiber₀_fiberInv₀ 0 k')

/-- **The index raise of `Λ₀` is `Λ`**: `(Λ₀)¹ = linIso` (`split = split₀` and `fiber = fiber₀` on
levels `m + 1`). -/
theorem strongShift_linIso₀ : strongShift (𝒮.linIso₀ Q) = 𝒮.linIso Q := by
  funext p
  apply levelMap_eq_of_toBase_eq
  rw [ScBanach.prod_toBase, ScBanach.prod_toBase]
  refine Prod.ext ?_ ?_
  · change 𝒮.E₀'.toBase 1 (𝒮.split₀ 1 p.1) = 𝒮.split₀ 0 ((ScBanach.paramProd P W).toBase 1 p.1)
    exact 𝒮.split₀.toBase_comm 1 p.1
  · change (𝒮.F₀' Q).toBase 1 (𝒮.fiber₀ 1 p.2) = 𝒮.fiber₀ 0 ((ScBanach.paramProd Q W).toBase 1 p.2)
    exact 𝒮.fiber₀.toBase_comm 1 p.2

end StabilityData

/-! ### Corollary 3.4.3 (preprint 3.39) -/

namespace ConjugationData

variable {U : Set (E 0)} {g : E 0 → F 0} (d : ConjugationData U g)

/-- `t = Φ[1]_* s : U' → (ℝᴺ ⊕ W)¹`, `t(u') = (Φ[1](ϕ⁻¹u', s(ϕ⁻¹u')))₂`: the push-forward of a
local sc⁺-section `s : U → F¹` by the conjugation `Φ = d.Ψ` (proof of Corollary 3.4.3 (preprint 3.39): "`t = Φ_* s`
defines an sc⁺-section"). -/
def pushPlus (s : E 0 → F 1) :
    (ScBanach.paramProd d.Pn d.W) 0 → (ScBanach.paramProd d.Q d.W).shift 0 :=
  fun u' => (shiftFiber d.Ψ (IsStrongBundleMap.base d.Ψ' u', s (IsStrongBundleMap.base d.Ψ' u'))).2

/-- `h' = h + (t_{ℝᴺ}, 0)`: the basic germ with the `ℝᴺ`-component of `t = Φ_* s` absorbed
(Finding 85). -/
def absorb (s : E 0 → F 1) : d.Pn × d.W 0 → d.Q × d.W 0 :=
  fun x => d.h x + ScBanach.qPartOp d.Q d.W 0 (d.pushPlus s x)

variable (𝒮 : StabilityData d.Ct d.W)

/-- **The composite strong bundle isomorphism `Γ = Λ ∘ Φ¹` of Corollary 3.4.3 (preprint 3.39)**: the index raise
`Φ¹ = strongShift d.Ψ` of the given conjugation followed by the linear coordinate change
`Λ = 𝒮.linIso` of Theorem 3.4.2 (preprint 3.38), on the shifted structures `E¹ ◁ F¹`. -/
def compIso : E.shift 0 × F.shift 0 → 𝒮.E' 0 × 𝒮.F' d.Q 0 :=
  𝒮.linIso d.Q ∘ strongShift d.Ψ

/-- The inverse `Γ⁻¹ = Φ'¹ ∘ Λ⁻¹`. -/
def compIsoInv : 𝒮.E' 0 × 𝒮.F' d.Q 0 → E.shift 0 × F.shift 0 :=
  strongShift d.Ψ' ∘ 𝒮.linIsoInv d.Q

/-- The target `γ(U¹) = ψ(U'¹)` of `Γ` (`ψ = split`). -/
def compDomain : Set (𝒮.E' 0) :=
  𝒮.glue 0 ⁻¹' (ScBanach.paramProd d.Pn d.W).lvlSet d.U' 1

lemma compIso_eq : d.compIso 𝒮 = 𝒮.linIso d.Q ∘ strongShift d.Ψ := rfl

lemma compIsoInv_eq : d.compIsoInv 𝒮 = strongShift d.Ψ' ∘ 𝒮.linIsoInv d.Q := rfl

/-- **The text's form of the composite, `Γ = (Ψ ∘ Φ)¹`**: the composite `Λ₀ ∘ Φ` of the given
conjugation with the coordinate change of Theorem 3.4.2 (preprint 3.38) before the index raise is a strong bundle
isomorphism `U ◁ F → ψ(U') ◁ ((ℝᴺ ⊕ Z) ⊕ X)` (level `0`), and its index raise is `Γ = Λ ∘ Φ¹` on
`U¹ ⊕ F¹`. -/
theorem compIso_eq_strongShift {C : Set (E 0)} (hU : IsRelOpenInQuadrant E C U) :
    IsStrongBundleIso U (𝒮.glue₀ 0 ⁻¹' d.U') (𝒮.linIso₀ d.Q ∘ d.Ψ) (d.Ψ' ∘ 𝒮.linIsoInv₀ d.Q) ∧
      ∀ p ∈ E.lvlSet U 1 ×ˢ (univ : Set (F 1)),
        d.compIso 𝒮 p = strongShift (𝒮.linIso₀ d.Q ∘ d.Ψ) p := by
  have hΛ₀ := 𝒮.linIso₀_isStrongBundleIso (Q := d.Q) d.quadrant d.relOpen
  refine ⟨d.iso.comp hU d.relOpen (𝒮.isRelOpen_glue₀_preimage d.quadrant d.relOpen) hΛ₀,
    fun p hp => ?_⟩
  rw [d.iso.toFun.strongShift_comp hΛ₀.toFun hp.1, 𝒮.strongShift_linIso₀]
  rfl

end ConjugationData

section Cor339

variable {C U : Set (E 0)}

open ConjugationData in
/-- **Corollary 3.4.3 (preprint 3.39)**, with the composite strong bundle isomorphism explicit.  Let `g : U → F` be
sc-smooth and conjugated to a basic germ `h : O(C̃ ⊕ W, 0) → ℝᴺ ⊕ W` by the strong bundle
isomorphism `Φ = d.Ψ : U ◁ F → U' ◁ (ℝᴺ ⊕ W)` covering `ϕ` (the data `d`), and let `s : U → F¹`
be an sc⁺-germ with `s(0) = 0`.  Then, with `t = Φ[1]_* s` (`d.pushPlus s`, `t(0) = 0`) and
`h' = h + (t_{ℝᴺ}, 0)` (`d.absorb s`), there are the data `𝒮` of Theorem 3.4.2 (preprint 3.38) for `t_W` on the
germ of `h` such that:
* `h'` is a basic germ and `Φ_*(g + s) = h + t = 𝒮.fsum h'` near `0` (the text's
  "`Φ_*(g + s) = h + t`");
* `Γ = Λ ∘ Φ¹` (`d.compIso 𝒮`, `Λ = 𝒮.linIso`) is a strong bundle isomorphism
  `U¹ ◁ F¹ → ψ(U'¹) ◁ ((ℝᴺ ⊕ Z) ⊕ X¹)` with inverse `Φ'¹ ∘ Λ⁻¹`, `γ(0) = 0`, onto a relatively
  open subset of `(C̃ ⊕ C) ⊕ X¹` containing the germ of `𝒮.pushMap h'`, and
  `Γ_* = Λ_* ∘ Φ¹_*`;
* `𝒮.pushMap h' = (Λ_*(h + t))¹` is a basic germ (Theorem 3.4.2 (preprint 3.38)), and
  `(Γ(u, (g + s)¹(u)))₂ = 𝒮.pushMap h'(γ(u))` for `u ∈ U¹` near `0`: `((Ψ ∘ Φ)_*(g + s))¹` is
  the basic germ `𝒮.pushMap h'`. -/
theorem corollary_3_4_3 (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E 0) ∈ U)
    {g : E 0 → F 0} (hg : IsScSmooth U g) (d : ConjugationData U g) {s : E 0 → F 1}
    (hs : IsScSmooth (F := F.shift) U s) (hs0 : s 0 = 0) :
    ∃ 𝒮 : StabilityData d.Ct d.W,
      𝒮.G = d.G ∧ 𝒮.s = (fun x => (d.pushPlus s x).2) ∧ d.pushPlus s 0 = 0 ∧
      IsBasicGerm d.Ct 𝒮.G (d.absorb s) d.Bc ∧
      (∀ᶠ u in 𝓝 (0 : E 0), u ∈ U →
        pushforward d.Ψ d.Ψ' (fun v => g v + F.toBase 1 (s v)) (IsStrongBundleMap.base d.Ψ u) =
          𝒮.fsum (d.absorb s) (IsStrongBundleMap.base d.Ψ u)) ∧
      IsRelOpenInQuadrant 𝒮.E' ((d.Ct ×ˢ univ) ×ˢ univ) (d.compDomain 𝒮) ∧
      IsStrongBundleIso (E := E.shift) (F := F.shift) (E.lvlSet U 1) (d.compDomain 𝒮)
        (d.compIso 𝒮) (d.compIsoInv 𝒮) ∧
      IsStrongBundleMap.base (d.compIso 𝒮) 0 = 0 ∧
      (∀ (k : E.shift 0 → F.shift 0), ∀ y ∈ d.compDomain 𝒮,
        pushforward (d.compIso 𝒮) (d.compIsoInv 𝒮) k y =
          pushforward (𝒮.linIso d.Q) (𝒮.linIsoInv d.Q)
            (pushforward (strongShift d.Ψ) (strongShift d.Ψ') k) y) ∧
      𝒮.pushGerm.U 0 ⊆ d.compDomain 𝒮 ∧
      IsBasicGerm (d.Ct ×ˢ univ) 𝒮.pushGerm (𝒮.pushMap (d.absorb s)) (𝒮.pushB d.Bc) ∧
      ∀ᶠ u in 𝓝 (0 : E.shift 0), u ∈ E.lvlSet U 1 →
        (d.compIso 𝒮 (u, levelMap (fun v => g v + F.toBase 1 (s v)) 1 u)).2 =
          𝒮.pushMap (d.absorb s) (IsStrongBundleMap.base (d.compIso 𝒮) u) := by
  classical
  have hU' := d.relOpen
  have hCt := d.quadrant
  have hψψ' : ∀ u ∈ U, IsStrongBundleMap.base d.Ψ' (IsStrongBundleMap.base d.Ψ u) = u :=
    fun u hu => d.iso.base_base hu
  have h0U' : (0 : (ScBanach.paramProd d.Pn d.W) 0) ∈ d.U' :=
    d.base_zero ▸ d.iso.toFun.base_mem h0
  have hψ'0 : IsStrongBundleMap.base d.Ψ' 0 = 0 := d.iso.base_zero' h0 d.base_zero
  have hψsc : IsScSmooth U (IsStrongBundleMap.base d.Ψ) := d.iso.toFun.base_isScSmooth hU
  have hψ'sc : IsScSmooth d.U' (IsStrongBundleMap.base d.Ψ') := d.iso.invFun.base_isScSmooth hU'
  have hC'q : IsQuadrantLike (ScBanach.paramProd d.Pn d.W) (d.Ct ×ˢ univ) :=
    hU'.isPartialQuadrant.isQuadrantLike
  have hU'C : d.U' ⊆ d.Ct ×ˢ univ := by
    obtain ⟨Uo, -, hUo⟩ := hU'.relOpen
    rw [hUo]; exact inter_subset_right
  -- the push-forward sc⁺-germ `t = Φ[1]_* s` on `U'`
  set t := d.pushPlus s with htdef
  have htsc : IsScSmooth (E := ScBanach.paramProd d.Pn d.W)
      (F := (ScBanach.paramProd d.Q d.W).shift) d.U' t := by
    have hpair : IsScSmooth (E := ScBanach.paramProd d.Pn d.W) (F := E.prod F.shift) d.U'
        (scPair (F := E) (G := F.shift) (IsStrongBundleMap.base d.Ψ')
          (fun u' => s (IsStrongBundleMap.base d.Ψ' u'))) := by
      refine hψ'sc.scPair hU'.isScDomain ?_
      exact IsScSmooth.comp hU'.isScDomain hU.isScDomain hs hψ'sc fun u' hu' =>
        d.iso.invFun.base_mem hu'
    have hUF := (hU.prod_univ F.shift).isScDomain
    have hmaps : MapsTo (scPair (F := E) (G := F.shift) (IsStrongBundleMap.base d.Ψ')
        (fun u' => s (IsStrongBundleMap.base d.Ψ' u'))) d.U' (U ×ˢ univ) := fun u' hu' =>
      ⟨d.iso.invFun.base_mem hu', mem_univ _⟩
    have := IsScSmooth.comp hU'.isScDomain hUF d.iso.toFun.isScSmooth_one hpair hmaps
    exact (this.snd hU'.isScDomain).congr hU'.isScDomain fun _ _ => rfl
  have hGsub : ∀ m, d.G.U m ⊆ (ScBanach.paramProd d.Pn d.W).lvlSet d.U' m := fun m z hz =>
    d.germ_subset (d.G.toBase_mem hz)
  have htG : IsScSmoothGerm (E := ScBanach.paramProd d.Pn d.W)
      (F := (ScBanach.paramProd d.Q d.W).shift) d.G t :=
    (htsc.isScSmoothGerm hC'q hU'.relOpen h0U').mono hC'q hGsub
  have ht0 : t 0 = 0 := by
    have e : t 0 = (shiftFiber d.Ψ (((0 : E 0), (0 : F 1)) : (E.prod F.shift) 0)).2 := by
      simp only [htdef, ConjugationData.pushPlus, hψ'0, hs0]
    rw [e]
    unfold shiftFiber
    simp only [map_zero]
    rw [d.iso.toFun.snd_zero h0]
    have := Function.leftInverse_invFun ((ScBanach.paramProd d.Q d.W).toBase_injective 1) 0
    rw [map_zero] at this
    exact this
  -- the basic germ `h' = h + (t_{ℝᴺ}, 0)` and the data of Theorem 3.4.2 (preprint 3.38) with `s = t_W`
  set h' := d.absorb s with hh'def
  have hh' : IsBasicGerm d.Ct d.G h' d.Bc :=
    { isScSmooth := by
        have hq : IsScSmoothGerm (E := ScBanach.paramProd d.Pn d.W)
            (F := ScBanach.paramProd d.Q d.W) d.G (ScBanach.qPartOp d.Q d.W 0 ∘ t) :=
          fun k => IsSckGerm.operator_comp hC'q (ScBanach.qPartOp d.Q d.W) (htG k)
        have hp : IsScSmoothGerm (E := ScBanach.paramProd d.Pn d.W)
            (F := (ScBanach.paramProd d.Q d.W).prod (ScBanach.paramProd d.Q d.W)) d.G
            (pairMap (F := ScBanach.paramProd d.Q d.W) (G := ScBanach.paramProd d.Q d.W) d.h
              (ScBanach.qPartOp d.Q d.W 0 ∘ t)) :=
          IsScSmoothGerm.pair (F := ScBanach.paramProd d.Q d.W) (G := ScBanach.paramProd d.Q d.W)
            hC'q d.basic.isScSmooth hq
        intro k
        exact (IsSckGerm.operator_comp hC'q (ScBanach.paramProd d.Q d.W).addOp (hp k)).congr hC'q
          fun x _ => rfl
      f_zero := by
        change d.h 0 + ScBanach.qPartOp d.Q d.W 0 (t 0) = 0
        rw [d.basic.f_zero, ht0, map_zero, add_zero]
      snd_eq := fun x hx => by
        change (d.h x + ScBanach.qPartOp d.Q d.W 0 (t x)).2 = x.2 - d.Bc x
        rw [Prod.snd_add, d.basic.snd_eq x hx, ScBanach.qPartOp_apply, add_zero]
      contraction := d.basic.contraction }
  have hsW : IsScSmoothGerm (E := ScBanach.paramProd d.Pn d.W) (F := d.W.shift) d.G
      (fun x => (t x).2) := fun k =>
    (IsSckGerm.operator_comp hC'q (ScBanach.wPartOp d.Q d.W) (htG k)).congr hC'q fun _ _ => rfl
  have hsW0 : ((t 0).2 : d.W 1) = 0 := by rw [ht0]; rfl
  obtain ⟨𝒮, h𝒮G, h𝒮s⟩ := StabilityData.exists_of_scPlus hsW hsW0
  have hh'𝒮 : IsBasicGerm d.Ct 𝒮.G h' d.Bc := by rw [h𝒮G]; exact hh'
  have hfsum : ∀ x, 𝒮.fsum h' x = d.h x + (ScBanach.paramProd d.Q d.W).toBase 1 (t x) := fun x => by
    rw [StabilityData.fsum_apply, h𝒮s, ScBanach.paramProd_toBase]
    change d.h x + ((t x).1, (0 : d.W 0)) + ((0 : d.Q), d.W.toBase 1 (t x).2) =
      d.h x + ((t x).1, d.W.toBase 1 (t x).2)
    rw [add_assoc]
    congr 1
    ext <;> simp
  -- (1) `Φ_*(g + s) = h + t = 𝒮.fsum h'` where the conjugation identity holds
  set k := fun v => g v + F.toBase 1 (s v) with hkdef
  have hksc : IsScSmooth U k := hg.add hU.isScDomain (hs.toBase_shift hU.isScDomain)
  have hpush : ∀ u ∈ U, pushforward d.Ψ d.Ψ' k (IsStrongBundleMap.base d.Ψ u) =
      (d.Ψ (u, k u)).2 := fun u hu => by
    unfold pushforward
    rw [hψψ' u hu]
  have hkey : ∀ u ∈ U, (d.Ψ (u, g u)).2 = d.h (IsStrongBundleMap.base d.Ψ u) →
      (d.Ψ (u, k u)).2 = 𝒮.fsum h' (IsStrongBundleMap.base d.Ψ u) := by
    intro u hu hconj
    have e1 : t (IsStrongBundleMap.base d.Ψ u) = (shiftFiber d.Ψ (u, s u)).2 := by
      simp only [htdef, ConjugationData.pushPlus]; rw [hψψ' u hu]
    have e2 : (ScBanach.paramProd d.Q d.W).toBase 1 (shiftFiber d.Ψ (u, s u)).2 =
        (d.Ψ (u, F.toBase 1 (s u))).2 :=
      d.iso.toFun.toBase_shiftFiber_snd (p := (u, s u)) hu
    rw [hfsum, e1, e2, ← hconj]
    exact (d.iso.toFun.fiber_linear u hu).map_add _ _
  -- the composite strong bundle isomorphism
  have hΦ1 := d.iso.shift hU hU'
  have hΛ := 𝒮.linIso_isStrongBundleIso (Q := d.Q) hCt hU'.shift
  have hrel := 𝒮.isRelOpen_glue_preimage hCt hU'.shift
  have hΓ := hΦ1.comp hU.shift hU'.shift hrel hΛ
  have h01 : E.toBase 1 (0 : E 1) ∈ U := by rw [map_zero]; exact h0
  have hb1 : ∀ u : E 1, E.toBase 1 u ∈ U →
      IsStrongBundleMap.base (strongShift d.Ψ) u = levelMap (IsStrongBundleMap.base d.Ψ) 1 u :=
    fun u hu => (levelMap_eq_of_toBase_eq (d.iso.toFun.toBase_base_strongShift hu)).symm
  have hbase : ∀ u : E 1, E.toBase 1 u ∈ U → IsStrongBundleMap.base (d.compIso 𝒮) u =
      𝒮.split 0 (levelMap (IsStrongBundleMap.base d.Ψ) 1 u) := fun u hu => by
    rw [compIso_eq, (d.iso.toFun.shift hU).base_comp hΛ.toFun hu, hb1 u hu]
    rfl
  have hlev0 : levelMap (IsStrongBundleMap.base d.Ψ) 1 (0 : E 1) = 0 :=
    levelMap_eq_of_toBase_eq (by rw [map_zero, map_zero, d.base_zero])
  refine ⟨𝒮, h𝒮G, h𝒮s, ht0, hh'𝒮, ?_, hrel, hΓ, ?_, fun k y hy => hΦ1.pushforward_comp hΛ k hy,
    ?_, theorem_3_4_2 𝒮 hCt.isQuadrantLike hh'𝒮, ?_⟩
  · filter_upwards [d.conj] with u hu huU
    rw [hpush u huU]
    exact hkey u huU (hu huU)
  · rw [hbase 0 h01, hlev0, map_zero]
  · intro y hy
    have hy' : 𝒮.glue 0 y ∈ 𝒮.G.U 1 := hy
    rw [h𝒮G] at hy'
    change (ScBanach.paramProd d.Pn d.W).toBase 1 (𝒮.glue 0 y) ∈ d.U'
    exact d.germ_subset (d.G.toBase_mem hy')
  -- (4) the conjugation identity on level `1`
  have hT : Tendsto (E.toBase 1) (𝓝 (0 : E 1)) (𝓝 (0 : E 0)) := by
    have := (E.toBase 1).continuous.tendsto (0 : E 1)
    rwa [map_zero] at this
  have hev2 := hT.eventually d.conj
  obtain ⟨O₁, hO₁, hG1⟩ := d.G.relOpen 1
  have h01' : (0 : E 1) ∈ E.lvlSet U 1 := h01
  have h0O₁ : (0 : (ScBanach.paramProd d.Pn d.W) 1) ∈ O₁ := by
    have := d.G.zero_mem 1
    rw [hG1] at this
    exact this.1
  have hev3 : ∀ᶠ u in 𝓝 (0 : E 1), u ∈ E.lvlSet U 1 →
      levelMap (IsStrongBundleMap.base d.Ψ) 1 u ∈ O₁ := by
    have hcw := hψsc.isSc1.isSc0.continuousOn 1 0 h01'
    rw [ContinuousWithinAt, hlev0] at hcw
    exact eventually_nhdsWithin_iff.1 (hcw (hO₁.mem_nhds h0O₁))
  have hfs0 : IsSc0Germ (E := ScBanach.paramProd d.Pn d.W) (F := ScBanach.paramProd d.Q d.W) 𝒮.G
      (𝒮.fsum h') := 𝒮.fsum_isScSmoothGerm hCt.isQuadrantLike hh'𝒮.isScSmooth 0
  filter_upwards [hev2, hev3] with u hu2 hu3 hu
  have hιu : E.toBase 1 u ∈ U := hu
  have hconj : (d.Ψ (E.toBase 1 u, g (E.toBase 1 u))).2 =
      d.h (IsStrongBundleMap.base d.Ψ (E.toBase 1 u)) := hu2 hιu
  have hy1 : levelMap (IsStrongBundleMap.base d.Ψ) 1 u ∈ 𝒮.G.U 1 := by
    rw [h𝒮G, hG1]
    refine ⟨hu3 hu, ?_⟩
    rw [ScBanach.mem_lvlSet, hψsc.isSc1.isSc0.toBase_levelMap hu]
    exact hU'C (d.iso.toFun.base_mem hιu)
  rw [hbase u hιu]
  change 𝒮.fiber 0 (strongShift d.Ψ (u, levelMap k 1 u)).2 =
    𝒮.fiber 0 (levelMap (E := ScBanach.paramProd d.Pn d.W) (F := ScBanach.paramProd d.Q d.W)
      (𝒮.fsum h') 1 (𝒮.glue 0 (𝒮.split 0 (levelMap (IsStrongBundleMap.base d.Ψ) 1 u))))
  rw [𝒮.glue_split]
  congr 1
  apply (ScBanach.paramProd d.Q d.W).toBase_injective 1
  rw [d.iso.toFun.toBase_strongShift_snd hιu, hfs0.toBase_levelMap hy1,
    hψsc.isSc1.isSc0.toBase_levelMap hu, hksc.isSc1.isSc0.toBase_levelMap hu]
  exact hkey _ hιu hconj

/-- **Corollary 3.4.3 (preprint 3.39)**: if the sc-smooth `g : U → F` is conjugated to a basic germ and `s` is an
sc⁺-germ with `s(0) = 0`, then the index-raised germ `(g + s)¹ : U¹ → F¹` is conjugated to a basic
germ (on the shifted structures `E¹`, `F¹`); the conjugation is `Γ = Λ ∘ Φ¹` of
`corollary_3_4_3`, with `Λ` the coordinate change of Theorem 3.4.2 (preprint 3.38). -/
theorem corollary_3_4_3_isConjugate (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E 0) ∈ U)
    {g : E 0 → F 0} (hg : IsScSmooth U g) (hconj : IsConjugateToBasicGerm U g) {s : E 0 → F 1}
    (hs : IsScSmooth (F := F.shift) U s) (hs0 : s 0 = 0) :
    IsConjugateToBasicGerm (E := E.shift) (F := F.shift) (E.lvlSet U 1)
      (levelMap (fun v => g v + F.toBase 1 (s v)) 1) := by
  obtain ⟨d⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj
  obtain ⟨𝒮, -, -, -, -, -, hrel, hΓ, hb0, -, hsub, hbasic, hev⟩ :=
    corollary_3_4_3 hU h0 hg d hs hs0
  exact ⟨d.Pn × 𝒮.Cs, d.Q × 𝒮.Zs, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 𝒮.XB.shift, d.Ct ×ˢ univ, d.compDomain 𝒮, d.compIso 𝒮,
    d.compIsoInv 𝒮, 𝒮.pushGerm, 𝒮.pushMap (d.absorb s), 𝒮.pushB d.Bc,
    d.quadrant.const_prod_univ 𝒮.Cs, hrel, hΓ, hb0, hsub, hbasic, hev⟩

end Cor339

end Polyfold
