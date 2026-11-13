import Polyfold.Chapter16.PolyfoldMaps

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.2, pp. 720–721: the **pull-back part of Theorem 16.2.6** (2017: Theorem 16.2).  Numbers and
pages are the 2021 text's.

# Pull-back of sc-differential forms by sc-smooth maps of polyfolds

## The text, paraphrased

(p. 720) For an sc-smooth map `f̂ : (Z, c) → (Z', c')` with a representative
`(f, 𝔣) : (X, α) → (X', α')`, `f̂^*[(ω', (X', α'))] = [(𝔣^*ω', (X, α))]`, and
`d_Z ∘ f̂^* = f̂^* ∘ d_{Z'}`.  (Theorem 16.2.6, second part) An sc-smooth map induces the
co-chain map `f̂^* : Ω*_sc(Z', c') → Ω*_sc(Z, c)`.

## What is formalized

* `MapRep.pullback a k : Ωᵏ_sc(Z', c') →ₗ Ωᵏ_sc(Z, c)`, `ω ↦ [(𝔣^* ω_{X'}, (X, α))]` for a
  representative `a = (f, 𝔣)`; **`MapRep.pullback_eq_of_equiv`: it depends only on the class of
  `a` (Definition 16.1.6)**: for `(h, Id) ≫ (f', 𝔣') = (f, 𝔣) ≫ (k, Id)`,
  `h_* ∘ 𝔣^* = 𝔣'^* ∘ k_*` (Theorem 11.2.1 (3), `h_* = (h⁻¹)^*`).
* **`ScMap.pullback F k`, the pull-back `f̂^*`** (linear), with `ScMap.pullback_mk` (the text's
  formula, for every representative and every representative of the form),
  **`ScMap.d_comp_pullback`** (`d_Z ∘ f̂^* = f̂^* ∘ d_{Z'}`, Theorem 11.2.1 (2)),
  `ScMap.pullback_id` (`1^* = 1`), `ScMap.pullback_mk_comp` (`(ĝ ∘ f̂)^* = f̂^* ∘ ĝ^*` on
  representatives with a common middle structure) and `ScMap.pullback_comp` (for effective middle
  polyfolds, where Definition 16.1.10 is well defined); **`theorem_16_2_6_pullback`**.
* The pull-back needs no effectiveness: it is well defined on every class of Definition 16.1.6,
  although the composition of Definition 16.1.10 need not be (`not_definition_16_1_10`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

open EPLocalization EPLocalization.EPLoc

variable {Z W V : Type u} [TopologicalSpace Z] [TopologicalSpace W] [TopologicalSpace V]

namespace PolyfoldClass

variable {c : PolyfoldClass Z} {d : PolyfoldClass W} {e : PolyfoldClass V} {k : ℕ}

namespace MapRep

/-- **The pull-back by a representative** `(f, 𝔣) : (X, α) → (Y, β)`:
`ω ↦ [(𝔣^* ω_Y, (X, α))]`, `ω_Y` the representative of `ω` on `(Y, β)`. -/
def pullback (a : MapRep c d) (k : ℕ) : ScForm d k →ₗ[ℝ] ScForm c k :=
  (ScForm.equivStructureₗ a.p a.hp).symm.toLinearMap ∘ₗ
    (formsPullback a.φ.gen k ∘ₗ ScForm.toStructureₗ a.q a.hq)

theorem pullback_apply (a : MapRep c d) (k : ℕ) (ω : ScForm d k) :
    a.pullback k ω =
      ScForm.mk a.p a.hp (formsPullback a.φ.gen k (ScForm.toStructure a.q a.hq ω)) :=
  rfl

/-- **The pull-back depends only on the class of the representative** (Definition 16.1.6). -/
theorem pullback_eq_of_equiv {a b : MapRep c d} (hab : a ≈ b) (k : ℕ) :
    a.pullback k = b.pullback k := by
  obtain ⟨h, kk, hh, hk, he⟩ := hab
  have hg : h.gen ≫ b.φ.gen = a.φ.gen ≫ kk.gen := congrArg PSHom.gen he
  have key : hh.2.choose ≫ a.φ.gen = b.φ.gen ≫ hk.2.choose := by
    have e1 : hh.2.choose ≫ h.gen = 𝟙 _ := hh.2.choose_spec.2
    have e2 : kk.gen ≫ hk.2.choose = 𝟙 _ := hk.2.choose_spec.1
    calc hh.2.choose ≫ a.φ.gen = hh.2.choose ≫ a.φ.gen ≫ kk.gen ≫ hk.2.choose := by
          rw [e2, Category.comp_id]
      _ = hh.2.choose ≫ (h.gen ≫ b.φ.gen) ≫ hk.2.choose := by
          rw [hg, Category.assoc]
      _ = b.φ.gen ≫ hk.2.choose := by
          rw [← Category.assoc, ← Category.assoc, e1, Category.id_comp]
  refine LinearMap.ext fun ω => ?_
  rw [pullback_apply, pullback_apply,
    ScForm.mk_eq_mk_formsPush a.hp b.hp _ hh.2 hh.β_eq]
  congr 1
  have hω : ScForm.toStructure b.q b.hq ω =
      formsPush kk.gen hk.2 k (ScForm.toStructure a.q a.hq ω) := by
    conv_lhs => rw [← ScForm.mk_toStructure a.q a.hq ω]
    exact ScForm.toStructure_mk_of a.hq b.hq _ hk.2 hk.β_eq
  rw [hω]
  change formsPullback hh.2.choose k (formsPullback a.φ.gen k _) =
    formsPullback b.φ.gen k (formsPullback hk.2.choose k _)
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← formsPullback_comp,
    ← formsPullback_comp, key]

end MapRep

namespace ScMap

/-- **The pull-back `f̂^* : Ωᵏ_sc(W, d) → Ωᵏ_sc(Z, c)`** of an sc-smooth map (2021 p. 721). -/
def pullback (F : ScMap c d) (k : ℕ) : ScForm d k →ₗ[ℝ] ScForm c k :=
  Quotient.lift (fun a : MapRep c d => a.pullback k)
    (fun _ _ h => MapRep.pullback_eq_of_equiv h k) F

/-- **The text's formula** (2021 p. 721): `f̂^*[(ω', (Y, β))] = [(𝔣^* ω', (X, α))]` for every
representative `(f, 𝔣) : (X, α) → (Y, β)` and every `ω'` on `Y`. -/
theorem pullback_mk (p : PolyfoldStructure Z) (hp : (⟦p⟧ : PolyfoldClass Z) = c)
    (q : PolyfoldStructure W) (hq : (⟦q⟧ : PolyfoldClass W) = d) (φ : PSHom p q)
    (ω : q.X.epFormsInfty k) :
    pullback (mk p hp q hq φ) k (ScForm.mk q hq ω) = ScForm.mk p hp (formsPullback φ.gen k ω) := by
  change ScForm.mk p hp (formsPullback φ.gen k (ScForm.toStructure q hq (ScForm.mk q hq ω))) = _
  rw [ScForm.toStructure_mk]

/-- **`d_Z ∘ f̂^* = f̂^* ∘ d_W`** (2021 p. 721). -/
theorem d_comp_pullback (F : ScMap c d) (k : ℕ) :
    ScForm.d.comp (pullback F k) = (pullback F (k + 1)).comp ScForm.d := by
  obtain ⟨p, hp⟩ := Quotient.exists_rep c
  obtain ⟨q, hq⟩ := Quotient.exists_rep d
  obtain ⟨φ, rfl⟩ := exists_rep F p hp q hq
  refine LinearMap.ext fun ω => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← ScForm.mk_toStructure q hq ω, ScForm.d_mk,
    pullback_mk, pullback_mk, ScForm.d_mk]
  congr 1
  exact (LinearMap.congr_fun (theorem_11_2_1_two φ.gen k) _)

/-- **`1^* = 1`.** -/
theorem pullback_id (c : PolyfoldClass Z) (k : ℕ) : pullback (id c) k = LinearMap.id := by
  refine LinearMap.ext fun ω => ?_
  rw [LinearMap.id_apply, ← ScForm.mk_toStructure c.out (Quotient.out_eq c) ω]
  change pullback (mk _ _ _ _ (PSHom.id _)) k _ = _
  rw [pullback_mk]
  change ScForm.mk _ _ (formsPullback (𝟙 _) k _) = _
  rw [formsPullback_id]
  rfl

/-- **`(ĝ ∘ f̂)^* = f̂^* ∘ ĝ^*`** on representatives with a common middle structure. -/
theorem pullback_mk_comp (p : PolyfoldStructure Z) (hp : (⟦p⟧ : PolyfoldClass Z) = c)
    (q : PolyfoldStructure W) (hq : (⟦q⟧ : PolyfoldClass W) = d) (r : PolyfoldStructure V)
    (hr : (⟦r⟧ : PolyfoldClass V) = e) (a : PSHom p q) (b : PSHom q r) (k : ℕ) :
    pullback (mk p hp r hr (a.comp b)) k =
      (pullback (mk p hp q hq a) k).comp (pullback (mk q hq r hr b) k) := by
  refine LinearMap.ext fun ω => ?_
  rw [← ScForm.mk_toStructure r hr ω, LinearMap.comp_apply, pullback_mk, pullback_mk,
    pullback_mk, PSHom.comp_gen, formsPullback_comp, LinearMap.comp_apply]

/-- **`(ĝ ∘ f̂)^* = f̂^* ∘ ĝ^*`** for an effective middle polyfold (Definition 16.1.10). -/
theorem pullback_comp (hd : d.IsEffective) (F : ScMap c d) (G : ScMap d e) (k : ℕ) :
    pullback (comp hd F G) k = (pullback F k).comp (pullback G k) := by
  obtain ⟨p, hp⟩ := Quotient.exists_rep c
  obtain ⟨q, hq⟩ := Quotient.exists_rep d
  obtain ⟨r, hr⟩ := Quotient.exists_rep e
  obtain ⟨a, rfl⟩ := exists_rep F p hp q hq
  obtain ⟨b, rfl⟩ := exists_rep G q hq r hr
  rw [comp_mk hd, pullback_mk_comp]

end ScMap

/-- **2021 Theorem 16.2.6, p. 721 (2017: Theorem 16.2), the pull-back part**: an sc-smooth map
`f̂ : (Z, c) → (W, d)` of polyfolds induces linear maps `f̂^* : Ωᵏ_sc(W, d) → Ωᵏ_sc(Z, c)` with
`d_Z ∘ f̂^* = f̂^* ∘ d_W`, given on every representative by `[(ω', (Y, β))] ↦ [(𝔣^*ω', (X, α))]`;
`1^* = 1` and `(ĝ ∘ f̂)^* = f̂^* ∘ ĝ^*` on representatives with a common middle structure.  (The
de Rham complex itself is `theorem_16_2_6_complex`.) -/
theorem theorem_16_2_6_pullback (F : ScMap c d) (k : ℕ) :
    ScForm.d.comp (F.pullback k) = (F.pullback (k + 1)).comp ScForm.d ∧
    (∀ (p : PolyfoldStructure Z) (hp : (⟦p⟧ : PolyfoldClass Z) = c)
      (q : PolyfoldStructure W) (hq : (⟦q⟧ : PolyfoldClass W) = d) (φ : PSHom p q),
      F = ScMap.mk p hp q hq φ → ∀ ω : q.X.epFormsInfty k,
        F.pullback k (ScForm.mk q hq ω) = ScForm.mk p hp (formsPullback φ.gen k ω)) ∧
    (ScMap.id c).pullback k = LinearMap.id :=
  ⟨ScMap.d_comp_pullback F k, fun p hp q hq φ h ω => by rw [h, ScMap.pullback_mk],
    ScMap.pullback_id c k⟩

end PolyfoldClass

end Polyfold
