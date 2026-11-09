import Polyfold.Chapter3.LocalCompactness
import Polyfold.Chapter1.FredholmIndex
import Polyfold.Chapter3.StrongBundleSections

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.4,
**Theorem 3.4.2 (preprint 3.38)** (weak stability of basic germs under sc⁺-perturbations) with its index statement,
in the germ setting of Definitions 3.1.7 and 3.4.1 (preprint 3.7 and 3.37).

# Stability of basic germs

## The text, paraphrased

(Definition 3.4.1 (preprint 3.37)) The basic class `C_basic` consists of the basic germs
`f : O([0,∞)ᵏ ⊕ ℝⁿ⁻ᵏ ⊕ W, 0) → (ℝᴺ ⊕ W, 0)` (Definition 3.1.7 (preprint 3.7)).  (Theorem 3.4.2 (preprint 3.38)) Let `f` be a basic
germ and `s` the principal part of an sc⁺-section with `s(0) = 0`.  Then there is a strong bundle
isomorphism `Φ : U ◁ (ℝᴺ ⊕ W) → U' ◁ (ℝᴺ' ⊕ W')` covering an sc-diffeomorphism `ϕ : (U, 0) → (V, 0)`
such that `(Φ_*(f + s))¹` (the levels raised by one) is a basic germ; `n − N = n' − N'`.  *Proof.*
`P ∘ f(a, w) = w − B(a, w)`; `A := P ∘ D₂s(0) : W → W` is an sc⁺-operator, so `1 + A` is
sc-Fredholm of index `0` (Proposition 1.1.11 (preprint 1.10)) with sc-splittings `W = C ⊕ X = R ⊕ Z`,
`C = ker(1 + A)`, `R = range(1 + A)`, `dim C = dim Z`.  Write `P ∘ s(a, w) = Aw + S(a, w)` with
`D₂S(0) = 0`; `S` is an arbitrarily small contraction in `w` on every level `m ≥ 1`.  Then
`P ∘ (f + s)(a, w) = (1 + A)w − B̄(a, w)`, `B̄ = B − S`, and with `P₁ : W → X`, `P₂ : W → R` the
projections and `L = (1 + A)|_X : X → R`, `L⁻¹P₂ ∘ P ∘ (f + s)(a, c + x) = x − B̂((a, c), x)`,
`B̂((a, c), x) = L⁻¹P₂B̄(a, c + x)`, which is the contraction normal form in the new parameter
`(a, c) ∈ V ⊕ C` and the new fibre variable `x ∈ X` on all levels `m ≥ 1`.  The coordinate change
is `ψ(a, w) = (a, (1 − P₁)w, P₁w)`, `Ψ(δa ⊕ δw) = δa ⊕ L⁻¹P₂δw ⊕ τ(1 − P₂)δw`.
(Corollary 3.4.3 (preprint 3.39)) If `g` is conjugate to a basic germ by `Φ` and `s` is sc⁺, then
`((Ψ ∘ Φ)_*(g + s))¹` is a basic germ for some `Ψ`.

## What is formalized

* The sc-operators attached to an sc-splitting `E = A ⊕ B` (`ScBanach.IsScSplitting.proj`,
  `projOp`, `IsScSubspace.inclOp`), the lift `A → E_m` of a finite-dimensional `A ⊆ E_∞`
  (`ScBanach.finLift`), and `isScFredholm_id`, `scIndex_id` (the identity is sc-Fredholm of
  index `0`, the trivial splitting).
* `Polyfold.scPlusOfDeriv` (the sc⁺-operator `A = D₂s(0)` of an sc⁺-germ, from the level
  operators of Proposition 1.2.1 (preprint 1.16) at `0`), `Polyfold.scPlusRemainder` (`S = s − A`) and
  **`Polyfold.scPlusRemainder_contraction`** (the contraction estimate for `S` on level `m + 1`,
  by the mean value inequality and the continuity of the derivative).
* `Polyfold.StabilityData` (the data: the germ, the sc⁺-germ `s` with `s(0) = 0`, and an
  sc-Fredholm splitting `W = C ⊕ X = R ⊕ Z` of `1 + A`; `StabilityData.exists_of_scPlus` by
  Proposition 1.1.11 (preprint 1.10)), with the sc-isomorphism `L : X_m ≃ R_m` (`StabilityData.Lequiv`, inverse
  continuous by the open mapping theorem), the sc-operators `L⁻¹P₂` (`LinvPOp`), the base change
  `ψ` (`split`) and its inverse `ψ⁻¹` (`glue`), the fibre change `Ψ` (`fiber`) and its inverse
  (`fiberInv`), all on the index-raised structures, with `split_glue`, `glue_split`,
  `fiber_fiberInv`, `fiberInv_fiber`.
* `StabilityData.pushGerm` (the germ `ψ(U_{m+1})`), `StabilityData.pushMap f`
  (`(Φ_*(f + s))¹ = Ψ ∘ (f + s)¹ ∘ ψ⁻¹`), `StabilityData.pushB B` (`B̂`), and
  **`Polyfold.theorem_3_4_2`**: `pushMap f` is a basic germ with contraction map `pushB B`
  (`pushMap_isScSmoothGerm`, `snd_pushMap`, `pushB_isSc0ContractionGerm`).
* `StabilityData.pushMap_eq_zero_iff` (the solution sets correspond under `ψ`),
  `StabilityData.finrank_Cs_eq_finrank_Zs` (**the index statement** `dim C = dim Z`, i.e.
  `n − N = n' − N'`).

## What the text leaves implicit, and the choices made (the findings)

* **The coordinate change of Theorem 3.4.2 (preprint 3.38) is linear**: `ψ(a, w) = ((a, (1 − P₁)w), P₁w)` and
  `Ψ` are sc-isomorphisms (sc-operators with sc-operator inverses), so no general strong bundle
  isomorphism is needed here; the push-forward is written with these operators.  The text's
  `τ : Z → C` (to make the new finite-dimensional target `ℝᴺ ⊕ C`) is not applied: the new
  target is `(Q ⊕ Z) ⊕ X¹` (`StabilityData.F'`), the new source `(P ⊕ C) ⊕ X¹` (`E'`).
* **The index raise is a change of sc-structure**: the new germ lives on the shifted spaces
  `X¹` (levels `X_{m+1}`), and its germ of neighbourhoods is `ψ(U_{m+1})`; "the levels are
  raised by `1`" is `IsSckGerm.shift` (Proposition 1.2.2 (preprint 1.17) for germs) for `(f + s)¹`.
* **"`S` is an arbitrarily small contraction on every level `m ≥ 1`"** needs Proposition 1.2.1 (preprint 1.16)
  for the sc⁺-germ `s` at level `m + 1` (`s : U_{m+1} → W_{m+1}` is `C¹` with derivative
  continuous in the operator norm, `continuousOn_levelDeriv_clm`) and the mean value inequality
  on a ball in `W_{m+1}` for fixed `a`; only the partial derivative `D₂S(0) = 0` vanishes
  (`scPlusRemainder_contraction`).
* **Hypotheses actually used**: of the sc⁺-section `s` only its `W`-component enters the
  contraction (it must be sc-smooth into `W¹` for the push-forward to be sc-smooth); of the basic
  germ, `B` is used only through Definition 3.1.7 (preprint 3.7) (sc⁰ with the contraction estimates); `1 + A` is
  sc-Fredholm by Proposition 1.1.11 (preprint 1.10) applied to the identity (`isScFredholm_id`), and
  `dim C = dim Z` is `ind(1 + A) = ind(1) = 0` (`proposition_1_1_11_index`, `scIndex_id`).
* The sum `f + s` of the text is `fsum f = f + ι ∘ s` (`StabilityData.fsum`), sc-smooth by the
  pairing and operator rules of the germ calculus; its `W`-component at a level-`1` point is
  `(1 + A)w − B̄(a, w)` (`snd_levelMap_fsum`).
* Corollary 3.4.3 (preprint 3.39) (the composition with a given conjugation to a basic germ) is not formalized
  here; it is the composition of a strong bundle isomorphism with the linear change of this file.
-/

open Set Filter Topology Function Asymptotics Metric

noncomputable section

namespace Polyfold

/-! ### Sc-splittings: the level-wise projections as sc-operators -/

namespace ScBanach

variable (E : ScBanach)

/-- For a subspace `A ⊆ E_∞`, the level-`m` part `A_m` is isomorphic to `A` through `ι_m`. -/
def smoothLevelEquiv {A : Submodule ℝ (E 0)} (hA : A ≤ E.smooth) (m : ℕ) :
    E.levelSub A m ≃ₗ[ℝ] A :=
  LinearEquiv.ofBijective ((E.toBase m : E m →ₗ[ℝ] E 0).restrict (p := E.levelSub A m) (q := A)
    fun _ hx => hx) (by
    refine ⟨fun x y hxy => Subtype.ext (E.toBase_injective m (congrArg Subtype.val hxy)),
      fun y => ?_⟩
    obtain ⟨x, hx⟩ := (ScScale.mem_smooth_iff E.toScScale).1 (hA y.2) m
    exact ⟨⟨x, by rw [mem_levelSub, hx]; exact y.2⟩, Subtype.ext hx⟩)

@[simp] lemma coe_smoothLevelEquiv {A : Submodule ℝ (E 0)} (hA : A ≤ E.smooth) (m : ℕ)
    (x : E.levelSub A m) : (E.smoothLevelEquiv hA m x : E 0) = E.toBase m x := rfl

lemma toBase_smoothLevelEquiv_symm {A : Submodule ℝ (E 0)} (hA : A ≤ E.smooth) (m : ℕ) (a : A) :
    E.toBase m ((E.smoothLevelEquiv hA m).symm a : E m) = a := by
  have := congrArg Subtype.val ((E.smoothLevelEquiv hA m).apply_symm_apply a)
  rwa [coe_smoothLevelEquiv] at this

/-- The lift `A → E_m` of a subspace `A ⊆ E_∞` (`ι_m ∘ lift = id`); continuous linear when `A` is
finite-dimensional. -/
def finLift {A : Submodule ℝ (E 0)} [FiniteDimensional ℝ A] (hA : A ≤ E.smooth) (m : ℕ) :
    A →L[ℝ] E m :=
  LinearMap.toContinuousLinearMap
    ((E.levelSub A m).subtype ∘ₗ (E.smoothLevelEquiv hA m).symm.toLinearMap)

lemma toBase_finLift {A : Submodule ℝ (E 0)} [FiniteDimensional ℝ A] (hA : A ≤ E.smooth)
    (m : ℕ) (a : A) : E.toBase m (E.finLift hA m a) = a :=
  E.toBase_smoothLevelEquiv_symm hA m a

lemma finLift_mem {A : Submodule ℝ (E 0)} [FiniteDimensional ℝ A] (hA : A ≤ E.smooth)
    (m : ℕ) (a : A) : E.finLift hA m a ∈ E.levelSub A m := by
  rw [mem_levelSub, toBase_finLift]; exact a.2

lemma incl_finLift {A : Submodule ℝ (E 0)} [FiniteDimensional ℝ A] (hA : A ≤ E.smooth)
    (m : ℕ) (a : A) : E.incl m (E.finLift hA (m + 1) a) = E.finLift hA m a := by
  apply E.toBase_injective m
  rw [← ScScale.toBase_succ, toBase_finLift, toBase_finLift]

@[simp] lemma finLift_zero_apply {A : Submodule ℝ (E 0)} [FiniteDimensional ℝ A]
    (hA : A ≤ E.smooth) (a : A) : E.finLift hA 0 a = a := by
  have := E.toBase_finLift hA 0 a
  simpa using this

lemma finLift_eq_of_toBase {A : Submodule ℝ (E 0)} [FiniteDimensional ℝ A] (hA : A ≤ E.smooth)
    {m : ℕ} {x : E m} (hx : x ∈ E.levelSub A m) :
    E.finLift hA m ⟨E.toBase m x, hx⟩ = x := by
  apply E.toBase_injective m
  rw [toBase_finLift]

/-- `ι_m` restricted to `A_m → A`, as a continuous linear map. -/
def levelToSub (A : Submodule ℝ (E 0)) (m : ℕ) : E.levelSub A m →L[ℝ] A :=
  ((E.toBase m : E m →ₗ[ℝ] E 0).restrict (p := E.levelSub A m) (q := A) fun _ hx => hx).mkContinuous
    ‖E.toBase m‖ fun x => (E.toBase m).le_opNorm x

@[simp] lemma coe_levelToSub (A : Submodule ℝ (E 0)) (m : ℕ) (x : E.levelSub A m) :
    (E.levelToSub A m x : E 0) = E.toBase m x := rfl

variable {E}

/-- The level-`m` projection `E_m → A_m` along `B_m` of an sc-splitting `E = A ⊕ B`. -/
def IsScSplitting.proj {A B : Submodule ℝ (E 0)} (h : E.IsScSplitting A B) (m : ℕ) :
    E m →L[ℝ] E.levelSub A m :=
  (E.levelSub A m).projectionOntoL (E.levelSub B m) (h.isTopCompl m)

lemma IsScSplitting.proj_add {A B : Submodule ℝ (E 0)} (h : E.IsScSplitting A B) (m : ℕ)
    {a b : E m} (ha : a ∈ E.levelSub A m) (hb : b ∈ E.levelSub B m) :
    h.proj m (a + b) = ⟨a, ha⟩ := by
  unfold proj
  rw [map_add, Submodule.projectionOntoL_apply_right _ ⟨b, hb⟩, add_zero]
  exact Submodule.projectionOntoL_apply_left (h.isTopCompl m) ⟨a, ha⟩

lemma IsScSplitting.proj_apply_left {A B : Submodule ℝ (E 0)} (h : E.IsScSplitting A B) (m : ℕ)
    {a : E m} (ha : a ∈ E.levelSub A m) : h.proj m a = ⟨a, ha⟩ :=
  Submodule.projectionOntoL_apply_left (h.isTopCompl m) ⟨a, ha⟩

lemma IsScSplitting.proj_apply_right {A B : Submodule ℝ (E 0)} (h : E.IsScSplitting A B) (m : ℕ)
    {b : E m} (hb : b ∈ E.levelSub B m) : h.proj m b = 0 :=
  Submodule.projectionOntoL_apply_right (h.isTopCompl m) ⟨b, hb⟩

lemma IsScSplitting.exists_add {A B : Submodule ℝ (E 0)} (h : E.IsScSplitting A B) (m : ℕ)
    (x : E m) : ∃ a ∈ E.levelSub A m, ∃ b ∈ E.levelSub B m, x = a + b := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1
    ((h.2.2 m).sup_eq_top ▸ Submodule.mem_top (x := x))
  exact ⟨a, ha, b, hb, hab.symm⟩

lemma IsScSplitting.sub_proj_mem {A B : Submodule ℝ (E 0)} (h : E.IsScSplitting A B) (m : ℕ)
    (x : E m) : x - h.proj m x ∈ E.levelSub B m := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_add m x
  rw [h.proj_add m ha hb]
  simpa using hb

/-- The projections of an sc-splitting commute with the inclusions. -/
lemma IsScSplitting.incl_proj {A B : Submodule ℝ (E 0)} (h : E.IsScSplitting A B) (m : ℕ)
    (x : E (m + 1)) : E.incl m (h.proj (m + 1) x : E (m + 1)) = h.proj m (E.incl m x) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_add (m + 1) x
  rw [h.proj_add (m + 1) ha hb, map_add, h.proj_add m (E.incl_mem_levelSub ha) (E.incl_mem_levelSub hb)]

lemma IsScSplitting.toBase_proj {A B : Submodule ℝ (E 0)} (h : E.IsScSplitting A B) (m : ℕ)
    (x : E m) : E.toBase m (h.proj m x : E m) = h.proj 0 (E.toBase m x) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ScScale.toBase_succ, h.incl_proj, ih]; rfl

/-- The sc-Banach space `A` of an sc-splitting `E = A ⊕ B` (the induced structure). -/
abbrev IsScSplitting.left {A B : Submodule ℝ (E 0)} (h : E.IsScSplitting A B) : ScBanach :=
  E.ofSubspace h.1

/-- The projection `E → A` of an sc-splitting, as an sc-operator. -/
def IsScSplitting.projOp {A B : Submodule ℝ (E 0)} (h : E.IsScSplitting A B) :
    ScOperator E h.left where
  lvl m := h.proj m
  incl_comm m x := Subtype.ext (h.incl_proj m x)

@[simp] lemma IsScSplitting.projOp_apply {A B : Submodule ℝ (E 0)} (h : E.IsScSplitting A B)
    (m : ℕ) (x : E m) : h.projOp m x = h.proj m x := rfl

/-- The inclusion `A → E` of an sc-subspace, as an sc-operator. -/
def IsScSubspace.inclOp {A : Submodule ℝ (E 0)} (h : E.IsScSubspace A) :
    ScOperator (E.ofSubspace h) E where
  lvl m := (E.levelSub A m).subtypeL
  incl_comm _ _ := rfl

@[simp] lemma IsScSubspace.inclOp_apply {A : Submodule ℝ (E 0)} (h : E.IsScSubspace A) (m : ℕ)
    (x : E.levelSub A m) : h.inclOp m x = (x : E m) := rfl

lemma ofSubspace_toBase_coe {A : Submodule ℝ (E 0)} (h : E.IsScSubspace A) (m : ℕ)
    (x : (E.ofSubspace h) m) : ((E.ofSubspace h).toBase m x).1 = E.toBase m x.1 :=
  E.ofSubspaceScale_coe_toBase h.isClosed m x

lemma ofSubspace_incl_coe {A : Submodule ℝ (E 0)} (h : E.IsScSubspace A) (m : ℕ)
    (x : (E.ofSubspace h) (m + 1)) : ((E.ofSubspace h).incl m x).1 = E.incl m x.1 :=
  rfl

end ScBanach

/-! ### The identity is sc-Fredholm -/

lemma ScBanach.isScSubspace_bot (E : ScBanach) : E.IsScSubspace ⊥ := by
  refine ⟨by simp, fun m x hx => ?_⟩
  have hx0 : x = 0 := by
    rw [SetLike.mem_coe, ScBanach.mem_levelSub, Submodule.mem_bot] at hx
    exact E.toBase_injective m (by rw [hx, map_zero])
  rw [hx0]
  exact subset_closure ⟨by simp, by
    simp only [ScScale.smoothLvl, mem_preimage, map_zero, SetLike.mem_coe]; exact zero_mem _⟩

lemma ScBanach.isScSubspace_top (E : ScBanach) : E.IsScSubspace ⊤ := by
  refine ⟨by simp, fun m x _ => ?_⟩
  have : (E.levelSub ⊤ m : Set (E m)) ∩ E.smoothLvl m = E.smoothLvl m := by
    ext y
    simp only [mem_inter_iff, SetLike.mem_coe, ScBanach.mem_levelSub, Submodule.mem_top, true_and]
  rw [this, (E.dense_smooth m).closure_eq]; exact mem_univ _

lemma ScBanach.levelSub_bot (E : ScBanach) (m : ℕ) : E.levelSub ⊥ m = ⊥ := by
  ext x
  rw [ScBanach.mem_levelSub, Submodule.mem_bot, Submodule.mem_bot]
  exact ⟨fun h => E.toBase_injective m (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

lemma ScBanach.levelSub_top (E : ScBanach) (m : ℕ) : E.levelSub ⊤ m = ⊤ := by
  ext x; simp [ScBanach.mem_levelSub]

lemma ScBanach.isScSplitting_bot_top (E : ScBanach) : E.IsScSplitting ⊥ ⊤ :=
  ⟨E.isScSubspace_bot, E.isScSubspace_top, fun m => by
    rw [E.levelSub_bot, E.levelSub_top]; exact isCompl_bot_top⟩

/-- The identity `E → E` is sc-Fredholm (of index `0`). -/
def ScOperator.idSplitting (E : ScBanach) : ScFredholmSplitting (ScOperator.id E) where
  K := ⊥
  X := ⊤
  C := ⊥
  Y := ⊤
  splitE := E.isScSplitting_bot_top
  splitF := E.isScSplitting_bot_top
  ker_eq := by ext x; simp [ScOperator.id]
  finite_K := inferInstance
  finite_C := inferInstance
  range_eq := by ext x; simp [ScOperator.id]
  bijOn m := by
    rw [E.levelSub_top]
    exact bijOn_id _

theorem isScFredholm_id (E : ScBanach) : IsScFredholm (ScOperator.id E) :=
  ⟨ScOperator.idSplitting E⟩

theorem scIndex_id (E : ScBanach) : scIndex (ScOperator.id E) = 0 := by
  rw [← (ScOperator.idSplitting E).index_eq]
  simp only [ScFredholmSplitting.index, ScOperator.idSplitting]
  exact sub_self _


/-! ### The linearization `A = P ∘ D₂s(0)` of an sc⁺-germ -/

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P}

section Linearization

variable {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)} {s : P × W 0 → W 1}
  {Ds : (ScBanach.paramProd P W) 1 → (ScBanach.paramProd P W) 0 →L[ℝ] W 1}

/-- The sc⁺-operator `A = D₂s(0) : W → W¹` of an sc¹-germ `s : O(C̃ ⊕ W, 0) → W¹` (proof of
Theorem 3.4.2 (preprint 3.38): "since `s` is an sc⁺-section and `0` is a smooth point, `A` is an sc⁺-operator");
its level-`m` map is the level operator of Proposition 1.2.1 (preprint 1.16) at `0 ∈ U_{m+1}`. -/
def scPlusOfDeriv (hs : IsSc1GermWith (E := ScBanach.paramProd P W) (F := W.shift) G s Ds) :
    ScPlus W W where
  lvl m := (levelDeriv (E := ScBanach.paramProd P W) (F := W.shift) Ds m 0).comp
    (ContinuousLinearMap.inr ℝ P (W m))
  incl_comm m x := by
    apply W.shift.toBase_injective m
    rw [← ScScale.toBase_succ]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    rw [hs.toBase_levelDeriv (G.zero_mem _), hs.toBase_levelDeriv (G.zero_mem _)]
    simp only [map_zero]
    rfl

lemma scPlusOfDeriv_apply (hs : IsSc1GermWith (E := ScBanach.paramProd P W) (F := W.shift) G s Ds)
    (m : ℕ) (w : W m) :
    scPlusOfDeriv hs m w =
      levelDeriv (E := ScBanach.paramProd P W) (F := W.shift) Ds m 0 ((0 : P), w) := rfl

lemma scPlusOfDeriv_zero_apply
    (hs : IsSc1GermWith (E := ScBanach.paramProd P W) (F := W.shift) G s Ds) (w : W 0) :
    scPlusOfDeriv hs 0 w = Ds 0 ((0 : P), w) := by
  rw [scPlusOfDeriv_apply, levelDeriv_zero]

/-- The remainder `S(a, w) = s(a, w) − A w` on level `m + 1` (proof of Theorem 3.4.2 (preprint 3.38):
`P ∘ s(a, w) = Aw + S(a, w)`, `D₂S(0, 0) = 0`). -/
def scPlusRemainder (hs : IsSc1GermWith (E := ScBanach.paramProd P W) (F := W.shift) G s Ds)
    (m : ℕ) (x : P × W (m + 1)) : W (m + 1) :=
  levelMap (E := ScBanach.paramProd P W) (F := W.shift) s m ((ScBanach.paramProd P W).incl m x) -
    scPlusOfDeriv hs m (W.incl m x.2)

/-- **The contraction estimate for the remainder** (proof of Theorem 3.4.2 (preprint 3.38): "`S` is, with respect to
the second variable `w`, an arbitrary small contraction on every level `m ≥ 1`, if `a` and `w` are
sufficiently small depending on the level `m` and the contraction constant"): since `D₂S(0) = 0`
on level `m + 1` and the derivative is continuous there (Proposition 1.2.1 (preprint 1.16)), the mean value
inequality gives `|S(a, w) − S(a, w')|_{m+1} ≤ ε|w − w'|_{m+1}` near `0`. -/
theorem scPlusRemainder_contraction (hC : IsQuadrantLike (ScBanach.const P) Ct)
    (hs : IsSc1GermWith (E := ScBanach.paramProd P W) (F := W.shift) G s Ds) (m : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ r > 0, ∀ a ∈ Ct, ‖a‖ < r → ∀ w w' : W (m + 1), ‖w‖ < r → ‖w'‖ < r →
      ((a, w) : (ScBanach.paramProd P W) (m + 1)) ∈ G.U (m + 1) ∧
        ‖scPlusRemainder hs m (a, w) - scPlusRemainder hs m (a, w')‖ ≤ ε * ‖w - w'‖ := by
  set E := ScBanach.paramProd P W with hE
  -- the ball in `U_{m+1}`
  obtain ⟨O, hO, hUO⟩ := G.relOpen (m + 1)
  have h0O : (0 : E (m + 1)) ∈ O := by
    have := G.zero_mem (m + 1); rw [hUO] at this; exact this.1
  obtain ⟨r₀, hr₀, hr₀O⟩ := Metric.isOpen_iff.1 hO 0 h0O
  -- continuity of the derivative at `0`
  have hcont := hs.continuousOn_levelDeriv_clm m 0 (G.zero_mem (m + 1))
  rw [Metric.continuousWithinAt_iff] at hcont
  obtain ⟨r₁, hr₁, hr₁'⟩ := hcont ε hε
  set r := min r₀ r₁ with hr
  have hrpos : 0 < r := lt_min hr₀ hr₁
  have hmem : ∀ a ∈ Ct, ‖a‖ < r → ∀ w : W (m + 1), ‖w‖ < r → ((a, w) : E (m + 1)) ∈ G.U (m + 1) := by
    intro a ha ha' w hw
    rw [hUO]
    refine ⟨hr₀O ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, Prod.norm_mk]
      exact max_lt (ha'.trans_le (min_le_left _ _)) (hw.trans_le (min_le_left _ _))
    · rw [ScBanach.paramProd_lvlSet]; exact ⟨ha, mem_univ _⟩
  refine ⟨r, hrpos, fun a ha ha' w w' hw hw' => ⟨hmem a ha ha' w hw, ?_⟩⟩
  -- the derivative of `w ↦ S(a, w)` on the ball
  set K : Set (W (m + 1)) := Metric.ball 0 r with hK
  set Dφ : W (m + 1) → W (m + 1) →L[ℝ] W (m + 1) := fun w =>
    ((levelDeriv (E := E) (F := W.shift) Ds m ((a, w) : E (m + 1))).comp (E.incl m)).comp
      (ContinuousLinearMap.inr ℝ P (W (m + 1))) -
      (scPlusOfDeriv hs m).comp (W.incl m) with hDφ
  have hderiv : ∀ w ∈ K, HasFDerivWithinAt (fun w => scPlusRemainder hs m (a, w)) (Dφ w) K w := by
    intro w hw
    have hwK : ‖w‖ < r := by rwa [hK, Metric.mem_ball, dist_zero_right] at hw
    have h1 : HasFDerivWithinAt (levelMap (E := E) (F := W.shift) s m ∘ E.incl m)
        ((levelDeriv (E := E) (F := W.shift) Ds m ((a, w) : E (m + 1))).comp (E.incl m))
        (G.U (m + 1)) ((a, w) : E (m + 1)) :=
      hs.hasFDerivWithinAt_level (hC.paramProd W) (hmem a ha ha' w hwK)
    have h2 : HasFDerivWithinAt (fun w : W (m + 1) => ((a, w) : E (m + 1)))
        (ContinuousLinearMap.inr ℝ P (W (m + 1))) K w :=
      ((hasFDerivAt_const a w).prodMk (hasFDerivAt_id w)).hasFDerivWithinAt
    have h3 : MapsTo (fun w : W (m + 1) => ((a, w) : E (m + 1))) K (G.U (m + 1)) := fun w hw =>
      hmem a ha ha' w (by rwa [hK, Metric.mem_ball, dist_zero_right] at hw)
    have h4 := h1.comp w h2 h3
    have h5 : HasFDerivWithinAt (fun w : W (m + 1) => scPlusOfDeriv hs m (W.incl m w))
        ((scPlusOfDeriv hs m).comp (W.incl m)) K w :=
      ((scPlusOfDeriv hs m).comp (W.incl m)).hasFDerivWithinAt
    exact h4.sub h5
  have hbound : ∀ w ∈ K, ‖Dφ w‖ ≤ ε := by
    intro w hw
    have hwK : ‖w‖ < r := by rwa [hK, Metric.mem_ball, dist_zero_right] at hw
    refine ContinuousLinearMap.opNorm_le_bound _ hε.le fun ζ => ?_
    have hmemw := hmem a ha ha' w hwK
    have hdist : dist ((a, w) : E (m + 1)) 0 < r₁ := by
      rw [dist_zero_right, Prod.norm_mk]
      exact max_lt (ha'.trans_le (min_le_right _ _)) (hwK.trans_le (min_le_right _ _))
    have hε' := hr₁' hmemw hdist
    rw [dist_eq_norm] at hε'
    have heq : Dφ w ζ = ((levelDeriv (E := E) (F := W.shift) Ds m ((a, w) : E (m + 1))).comp
        (E.incl m) - (levelDeriv (E := E) (F := W.shift) Ds m 0).comp (E.incl m))
        (((0 : P), ζ) : E (m + 1)) := by
      simp only [hDφ, sub_apply, ContinuousLinearMap.comp_apply]
      rfl
    rw [heq]
    calc ‖_‖ ≤ ‖(levelDeriv (E := E) (F := W.shift) Ds m ((a, w) : E (m + 1))).comp (E.incl m) -
          (levelDeriv (E := E) (F := W.shift) Ds m 0).comp (E.incl m)‖ *
          ‖(((0 : P), ζ) : E (m + 1))‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * ‖ζ‖ := by
          rw [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)]
          exact mul_le_mul_of_nonneg_right hε'.le (norm_nonneg _)
  have hwK : w ∈ K := by rw [hK, Metric.mem_ball, dist_zero_right]; exact hw
  have hw'K : w' ∈ K := by rw [hK, Metric.mem_ball, dist_zero_right]; exact hw'
  have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound (convex_ball 0 r) hw'K hwK
  exact this

end Linearization

/-! ### Theorem 3.4.2 (preprint 3.38): the data of the coordinate change -/

/-- **The data of Theorem 3.4.2 (preprint 3.38)**: the germ of neighbourhoods `G = O(C̃ ⊕ W, 0)`, an sc⁺-germ
`s : O(C̃ ⊕ W, 0) → W¹` (the `W`-component of the sc⁺-section) with `s(0) = 0`, and an
sc-Fredholm splitting (Definition 1.1.9 (preprint 1.8)) `W = C ⊕ X = R ⊕ Z` of `1 + A`, `A = D₂s(0)`
(Proposition 1.1.11 (preprint 1.10); `C = ker(1 + A)`, `R = range(1 + A)`). -/
structure StabilityData (Ct : Set P) (W : ScBanach) where
  /-- The germ of neighbourhoods. -/
  G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)
  /-- The sc⁺-germ (its `W`-component). -/
  s : P × W 0 → W 1
  isScSmooth : IsScSmoothGerm (E := ScBanach.paramProd P W) (F := W.shift) G s
  s_zero : s 0 = 0
  /-- The sc-Fredholm splitting of `1 + D₂s(0)`. -/
  sp : ScFredholmSplitting (ScOperator.id W +
    (scPlusOfDeriv ((isScSmooth 1).1.isSc1GermWith_scDerivGerm)).toScOperator)

namespace StabilityData

variable (𝒮 : StabilityData Ct W)

/-- The sc¹ structure of `s` with the chosen derivative. -/
lemma hs : IsSc1GermWith (E := ScBanach.paramProd P W) (F := W.shift) 𝒮.G 𝒮.s
    (scDerivGerm 𝒮.G 𝒮.s) := (𝒮.isScSmooth 1).1.isSc1GermWith_scDerivGerm

/-- The sc⁺-operator `A = D₂s(0)`. -/
abbrev A : ScPlus W W := scPlusOfDeriv 𝒮.hs

/-- The sc-Fredholm operator `T = 1 + A`. -/
abbrev T : ScOperator W W := ScOperator.id W + 𝒮.A.toScOperator

lemma T_apply (m : ℕ) (w : W m) : 𝒮.T m w = w + W.incl m (𝒮.A m w) := rfl

/-- `C = ker(1 + A)`. -/
abbrev Cs : Submodule ℝ (W 0) := 𝒮.sp.K
/-- `X`, the sc-complement of `C`. -/
abbrev Xs : Submodule ℝ (W 0) := 𝒮.sp.X
/-- `Z`, the finite-dimensional complement of the range. -/
abbrev Zs : Submodule ℝ (W 0) := 𝒮.sp.C
/-- `R = range(1 + A)`. -/
abbrev Rs : Submodule ℝ (W 0) := 𝒮.sp.Y

instance : FiniteDimensional ℝ 𝒮.Cs := 𝒮.sp.finite_K
instance : FiniteDimensional ℝ 𝒮.Zs := 𝒮.sp.finite_C

lemma Cs_le_smooth : 𝒮.Cs ≤ W.smooth := 𝒮.sp.K_le_smooth
lemma Zs_le_smooth : 𝒮.Zs ≤ W.smooth := 𝒮.sp.C_le_smooth

/-- The splitting `W = X ⊕ C`. -/
lemma splitX : W.IsScSplitting 𝒮.Xs 𝒮.Cs := 𝒮.sp.splitE.symm
/-- The splitting `W = C ⊕ X`. -/
lemma splitC : W.IsScSplitting 𝒮.Cs 𝒮.Xs := 𝒮.sp.splitE
/-- The splitting `W = R ⊕ Z`. -/
lemma splitR : W.IsScSplitting 𝒮.Rs 𝒮.Zs := 𝒮.sp.splitF.symm
/-- The splitting `W = Z ⊕ R`. -/
lemma splitZ : W.IsScSplitting 𝒮.Zs 𝒮.Rs := 𝒮.sp.splitF

/-- The sc-Banach space `X` (the new fibre, before the index raise). -/
abbrev XB : ScBanach := W.ofSubspace 𝒮.splitX.1

lemma XB_lvl (m : ℕ) : 𝒮.XB m = W.levelSub 𝒮.Xs m := rfl

/-- The projection `P₁ : W_m → X_m` along `C_m`. -/
abbrev projX (m : ℕ) : W m →L[ℝ] W.levelSub 𝒮.Xs m := 𝒮.splitX.proj m
/-- The projection `W_m → C_m` along `X_m`. -/
abbrev projC (m : ℕ) : W m →L[ℝ] W.levelSub 𝒮.Cs m := 𝒮.splitC.proj m
/-- The projection `P₂ : W_m → R_m` along `Z_m`. -/
abbrev projR (m : ℕ) : W m →L[ℝ] W.levelSub 𝒮.Rs m := 𝒮.splitR.proj m
/-- The projection `W_m → Z_m` along `R_m`. -/
abbrev projZ (m : ℕ) : W m →L[ℝ] W.levelSub 𝒮.Zs m := 𝒮.splitZ.proj m

lemma projX_add_projC (m : ℕ) (w : W m) : (𝒮.projX m w : W m) + 𝒮.projC m w = w := by
  obtain ⟨x, hx, c, hc, rfl⟩ := 𝒮.splitX.exists_add m w
  rw [ScBanach.IsScSplitting.proj_add _ m hx hc, add_comm x c,
    ScBanach.IsScSplitting.proj_add _ m hc hx, add_comm]

lemma projC_add_projX (m : ℕ) (w : W m) : (𝒮.projC m w : W m) + 𝒮.projX m w = w := by
  rw [add_comm (𝒮.projC m w : W m), 𝒮.projX_add_projC]

lemma projR_add_projZ (m : ℕ) (w : W m) : (𝒮.projR m w : W m) + 𝒮.projZ m w = w := by
  obtain ⟨x, hx, c, hc, rfl⟩ := 𝒮.splitR.exists_add m w
  rw [ScBanach.IsScSplitting.proj_add _ m hx hc, add_comm x c,
    ScBanach.IsScSplitting.proj_add _ m hc hx, add_comm]

lemma T_eq_zero_of_mem {m : ℕ} {c : W m} (hc : c ∈ W.levelSub 𝒮.Cs m) : 𝒮.T m c = 0 := by
  have : c ∈ LinearMap.ker (𝒮.T m : W m →ₗ[ℝ] W m) := by rw [𝒮.sp.ker_lvl]; exact hc
  exact this

lemma T_mem_Rs (m : ℕ) (w : W m) : 𝒮.T m w ∈ W.levelSub 𝒮.Rs m := by
  rw [← 𝒮.sp.range_lvl]; exact LinearMap.mem_range_self _ _

lemma projR_T (m : ℕ) (w : W m) : 𝒮.projR m (𝒮.T m w) = ⟨𝒮.T m w, 𝒮.T_mem_Rs m w⟩ :=
  ScBanach.IsScSplitting.proj_apply_left _ m _

/-- `L = (1 + A)|_X : X_m → R_m`. -/
def Lm (m : ℕ) : W.levelSub 𝒮.Xs m →L[ℝ] W.levelSub 𝒮.Rs m :=
  ((𝒮.T m).comp (W.levelSub 𝒮.Xs m).subtypeL).codRestrict (W.levelSub 𝒮.Rs m)
    fun x => 𝒮.T_mem_Rs m x

@[simp] lemma coe_Lm (m : ℕ) (x : W.levelSub 𝒮.Xs m) : (𝒮.Lm m x : W m) = 𝒮.T m x := rfl

lemma Lm_bijective (m : ℕ) : Bijective (𝒮.Lm m) := by
  refine ⟨fun x y hxy => Subtype.ext ((𝒮.sp.bijOn m).injOn x.2 y.2 (congrArg Subtype.val hxy)),
    fun y => ?_⟩
  obtain ⟨x, hx, hxy⟩ := (𝒮.sp.bijOn m).surjOn y.2
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- `L : X_m ≃ R_m` as a continuous linear equivalence (the inverse is continuous by the open
mapping theorem; the text: "`L := (1 + A)|X : X → R` is an sc-isomorphism"). -/
def Lequiv (m : ℕ) : W.levelSub 𝒮.Xs m ≃L[ℝ] W.levelSub 𝒮.Rs m :=
  haveI : CompleteSpace (W.levelSub 𝒮.Xs m) :=
    (W.isClosed_levelSub 𝒮.splitX.1.isClosed m).completeSpace_coe
  haveI : CompleteSpace (W.levelSub 𝒮.Rs m) :=
    (W.isClosed_levelSub 𝒮.splitR.1.isClosed m).completeSpace_coe
  (LinearEquiv.ofBijective (𝒮.Lm m : W.levelSub 𝒮.Xs m →ₗ[ℝ] W.levelSub 𝒮.Rs m)
    (𝒮.Lm_bijective m)).toContinuousLinearEquivOfContinuous (𝒮.Lm m).continuous

lemma Lequiv_apply (m : ℕ) (x : W.levelSub 𝒮.Xs m) : 𝒮.Lequiv m x = 𝒮.Lm m x := rfl

/-- `L⁻¹ ∘ P₂ : W_m → X_m`. -/
def LinvP (m : ℕ) : W m →L[ℝ] W.levelSub 𝒮.Xs m :=
  ((𝒮.Lequiv m).symm : W.levelSub 𝒮.Rs m →L[ℝ] W.levelSub 𝒮.Xs m).comp (𝒮.projR m)

lemma LinvP_apply (m : ℕ) (w : W m) : 𝒮.LinvP m w = (𝒮.Lequiv m).symm (𝒮.projR m w) := rfl

/-- `L⁻¹P₂ w = x` iff `x ∈ X_m` and `(1 + A)x = P₂ w`. -/
lemma LinvP_eq_of {m : ℕ} {w : W m} {x : W m} (hx : x ∈ W.levelSub 𝒮.Xs m)
    (h : 𝒮.T m x = 𝒮.projR m w) : (𝒮.LinvP m w : W m) = x := by
  rw [LinvP_apply]
  have : 𝒮.Lequiv m ⟨x, hx⟩ = 𝒮.projR m w := Subtype.ext (by rw [Lequiv_apply, coe_Lm]; exact h)
  rw [← this, ContinuousLinearEquiv.symm_apply_apply]

lemma LinvP_T {m : ℕ} {x : W m} (hx : x ∈ W.levelSub 𝒮.Xs m) : (𝒮.LinvP m (𝒮.T m x) : W m) = x :=
  𝒮.LinvP_eq_of hx (by rw [projR_T])

lemma T_LinvP (m : ℕ) (w : W m) : 𝒮.T m (𝒮.LinvP m w) = 𝒮.projR m w := by
  have := congrArg Subtype.val ((𝒮.Lequiv m).apply_symm_apply (𝒮.projR m w))
  rw [Lequiv_apply, coe_Lm] at this
  exact this

lemma incl_LinvP (m : ℕ) (w : W (m + 1)) :
    W.incl m (𝒮.LinvP (m + 1) w : W (m + 1)) = 𝒮.LinvP m (W.incl m w) := by
  symm
  refine 𝒮.LinvP_eq_of (W.incl_mem_levelSub (𝒮.LinvP (m + 1) w).2) ?_
  rw [← 𝒮.T.incl_comm, 𝒮.T_LinvP, ScBanach.IsScSplitting.incl_proj]

/-- `L⁻¹ ∘ P₂ : W → X` as an sc-operator. -/
def LinvPOp : ScOperator W 𝒮.XB where
  lvl m := 𝒮.LinvP m
  incl_comm m w := Subtype.ext (𝒮.incl_LinvP m w)

@[simp] lemma LinvPOp_apply (m : ℕ) (w : W m) : 𝒮.LinvPOp m w = 𝒮.LinvP m w := rfl

/-- The lift `C → W_m` of the smooth finite-dimensional subspace `C`. -/
abbrev liftC (m : ℕ) : 𝒮.Cs →L[ℝ] W m := W.finLift 𝒮.Cs_le_smooth m
/-- The lift `Z → W_m`. -/
abbrev liftZ (m : ℕ) : 𝒮.Zs →L[ℝ] W m := W.finLift 𝒮.Zs_le_smooth m
/-- The `C`-component `W_m → C` (projection along `X_m`, then `ι_m`). -/
abbrev toC (m : ℕ) : W m →L[ℝ] 𝒮.Cs := (W.levelToSub 𝒮.Cs m).comp (𝒮.projC m)
/-- The `Z`-component `W_m → Z` (projection along `R_m`, then `ι_m`). -/
abbrev toZ (m : ℕ) : W m →L[ℝ] 𝒮.Zs := (W.levelToSub 𝒮.Zs m).comp (𝒮.projZ m)

lemma liftC_toC (m : ℕ) (w : W m) : 𝒮.liftC m (𝒮.toC m w) = 𝒮.projC m w := by
  change W.finLift _ m ⟨W.toBase m (𝒮.projC m w : W m), _⟩ = _
  exact W.finLift_eq_of_toBase _ (𝒮.projC m w).2

lemma liftZ_toZ (m : ℕ) (w : W m) : 𝒮.liftZ m (𝒮.toZ m w) = 𝒮.projZ m w := by
  change W.finLift _ m ⟨W.toBase m (𝒮.projZ m w : W m), _⟩ = _
  exact W.finLift_eq_of_toBase _ (𝒮.projZ m w).2

lemma toC_liftC (m : ℕ) (c : 𝒮.Cs) : 𝒮.toC m (𝒮.liftC m c) = c := by
  apply Subtype.ext
  change W.toBase m (𝒮.projC m (𝒮.liftC m c) : W m) = c
  rw [ScBanach.IsScSplitting.proj_apply_left _ m (W.finLift_mem _ m c), W.toBase_finLift]

lemma toZ_liftZ (m : ℕ) (z : 𝒮.Zs) : 𝒮.toZ m (𝒮.liftZ m z) = z := by
  apply Subtype.ext
  change W.toBase m (𝒮.projZ m (𝒮.liftZ m z) : W m) = z
  rw [ScBanach.IsScSplitting.proj_apply_left _ m (W.finLift_mem _ m z), W.toBase_finLift]

lemma toC_coe_Xs (m : ℕ) (x : W.levelSub 𝒮.Xs m) : 𝒮.toC m x = 0 := by
  apply Subtype.ext
  change W.toBase m (𝒮.projC m x : W m) = 0
  rw [ScBanach.IsScSplitting.proj_apply_right _ m x.2]; simp

lemma toZ_T (m : ℕ) (w : W m) : 𝒮.toZ m (𝒮.T m w) = 0 := by
  apply Subtype.ext
  change W.toBase m (𝒮.projZ m (𝒮.T m w) : W m) = 0
  rw [ScBanach.IsScSplitting.proj_apply_right _ m (𝒮.T_mem_Rs m w)]; simp

lemma projR_liftZ (m : ℕ) (z : 𝒮.Zs) : 𝒮.projR m (𝒮.liftZ m z) = 0 :=
  ScBanach.IsScSplitting.proj_apply_right _ m (W.finLift_mem _ m z)

lemma projX_liftC (m : ℕ) (c : 𝒮.Cs) : 𝒮.projX m (𝒮.liftC m c) = 0 :=
  ScBanach.IsScSplitting.proj_apply_right _ m (W.finLift_mem _ m c)

lemma T_liftC (m : ℕ) (c : 𝒮.Cs) : 𝒮.T m (𝒮.liftC m c) = 0 :=
  𝒮.T_eq_zero_of_mem (W.finLift_mem _ m c)

lemma toC_incl (m : ℕ) (w : W (m + 1)) : 𝒮.toC (m + 1) w = 𝒮.toC m (W.incl m w) := by
  apply Subtype.ext
  change W.toBase (m + 1) (𝒮.projC (m + 1) w : W (m + 1)) = W.toBase m (𝒮.projC m (W.incl m w) : W m)
  rw [ScScale.toBase_succ, ScBanach.IsScSplitting.incl_proj]

lemma toZ_incl (m : ℕ) (w : W (m + 1)) : 𝒮.toZ (m + 1) w = 𝒮.toZ m (W.incl m w) := by
  apply Subtype.ext
  change W.toBase (m + 1) (𝒮.projZ (m + 1) w : W (m + 1)) = W.toBase m (𝒮.projZ m (W.incl m w) : W m)
  rw [ScScale.toBase_succ, ScBanach.IsScSplitting.incl_proj]

/-! #### The new spaces and the coordinate changes -/

/-- The new parameter space `P ⊕ C` and the new fibre `X¹`: `E' = (P ⊕ C) ⊕ X¹` (the text's
`V ⊕ C ⊕ X` with the levels raised by one). -/
abbrev E' : ScBanach := ScBanach.paramProd (P × 𝒮.Cs) 𝒮.XB.shift

/-- The new target `(Q ⊕ Z) ⊕ X¹` (the text's `ℝᴺ ⊕ C ⊕ X` with `τ : Z ≅ C` not applied). -/
abbrev F' (Q : Type) [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] : ScBanach :=
  ScBanach.paramProd (Q × 𝒮.Zs) 𝒮.XB.shift

/-- The inverse base change `ψ⁻¹ : (P ⊕ C) ⊕ X¹ → (P ⊕ W)¹`, `((a, c), x) ↦ (a, c + x)`. -/
def glue : ScOperator 𝒮.E' (ScBanach.paramProd P W).shift where
  lvl m := ((ContinuousLinearMap.fst ℝ P 𝒮.Cs).comp
      (ContinuousLinearMap.fst ℝ (P × 𝒮.Cs) (W.levelSub 𝒮.Xs (m + 1)))).prod
    (((𝒮.liftC (m + 1)).comp ((ContinuousLinearMap.snd ℝ P 𝒮.Cs).comp
      (ContinuousLinearMap.fst ℝ (P × 𝒮.Cs) (W.levelSub 𝒮.Xs (m + 1))))) +
      (W.levelSub 𝒮.Xs (m + 1)).subtypeL.comp
        (ContinuousLinearMap.snd ℝ (P × 𝒮.Cs) (W.levelSub 𝒮.Xs (m + 1))))
  incl_comm m y := by
    refine Prod.ext rfl ?_
    change W.incl (m + 1) (𝒮.liftC (m + 2) y.1.2 + y.2.val) =
      𝒮.liftC (m + 1) y.1.2 + W.incl (m + 1) y.2.val
    rw [map_add, W.incl_finLift]

lemma glue_apply (m : ℕ) (y : 𝒮.E' m) :
    𝒮.glue m y = ((y.1.1, 𝒮.liftC (m + 1) y.1.2 + y.2.val) : P × W (m + 1)) := rfl

/-- The base change `ψ : (P ⊕ W)¹ → (P ⊕ C) ⊕ X¹`, `(a, w) ↦ ((a, (1 − P₁)w), P₁w)`. -/
def split : ScOperator (ScBanach.paramProd P W).shift 𝒮.E' where
  lvl m := ((ContinuousLinearMap.fst ℝ P (W (m + 1))).prod
      ((𝒮.toC (m + 1)).comp (ContinuousLinearMap.snd ℝ P (W (m + 1))))).prod
    ((𝒮.projX (m + 1)).comp (ContinuousLinearMap.snd ℝ P (W (m + 1))))
  incl_comm m y := by
    refine Prod.ext (Prod.ext rfl ?_) ?_
    · exact 𝒮.toC_incl (m + 1) y.2
    · exact Subtype.ext (ScBanach.IsScSplitting.incl_proj 𝒮.splitX (m + 1) y.2)

lemma split_apply (m : ℕ) (y : (ScBanach.paramProd P W) (m + 1)) :
    𝒮.split m y = (((y.1, 𝒮.toC (m + 1) y.2), 𝒮.projX (m + 1) y.2) : 𝒮.E' m) := rfl

lemma glue_split (m : ℕ) (y : (ScBanach.paramProd P W) (m + 1)) : 𝒮.glue m (𝒮.split m y) = y := by
  refine Prod.ext rfl ?_
  change 𝒮.liftC (m + 1) (𝒮.toC (m + 1) y.2) + (𝒮.projX (m + 1) y.2 : W (m + 1)) = y.2
  rw [𝒮.liftC_toC, 𝒮.projC_add_projX]

lemma split_glue (m : ℕ) (y : 𝒮.E' m) : 𝒮.split m (𝒮.glue m y) = y := by
  obtain ⟨⟨a, c⟩, x⟩ := y
  have hx : x.val ∈ W.levelSub 𝒮.Xs (m + 1) := x.2
  refine Prod.ext (Prod.ext rfl ?_) ?_
  · change 𝒮.toC (m + 1) (𝒮.liftC (m + 1) c + x.val) = c
    have h1 : 𝒮.toC (m + 1) x.val = 0 := 𝒮.toC_coe_Xs (m + 1) ⟨x.val, hx⟩
    rw [map_add, 𝒮.toC_liftC, h1, add_zero]
  · change 𝒮.projX (m + 1) (𝒮.liftC (m + 1) c + x.val) = x
    rw [map_add, 𝒮.projX_liftC, zero_add]
    exact ScBanach.IsScSplitting.proj_apply_left _ _ hx

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

/-- The fibre change `Ψ : (Q ⊕ W)¹ → (Q ⊕ Z) ⊕ X¹`, `(q, w) ↦ ((q, (1 − P₂)w), L⁻¹P₂w)`. -/
def fiber : ScOperator (ScBanach.paramProd Q W).shift (𝒮.F' Q) where
  lvl m := ((ContinuousLinearMap.fst ℝ Q (W (m + 1))).prod
      ((𝒮.toZ (m + 1)).comp (ContinuousLinearMap.snd ℝ Q (W (m + 1))))).prod
    ((𝒮.LinvP (m + 1)).comp (ContinuousLinearMap.snd ℝ Q (W (m + 1))))
  incl_comm m y := by
    refine Prod.ext (Prod.ext rfl ?_) ?_
    · exact 𝒮.toZ_incl (m + 1) y.2
    · exact Subtype.ext (𝒮.incl_LinvP (m + 1) y.2)

lemma fiber_apply (m : ℕ) (y : (ScBanach.paramProd Q W) (m + 1)) :
    𝒮.fiber (Q := Q) m y = (((y.1, 𝒮.toZ (m + 1) y.2), 𝒮.LinvP (m + 1) y.2) : 𝒮.F' Q m) := rfl

/-- The inverse fibre change `Ψ⁻¹ : (Q ⊕ Z) ⊕ X¹ → (Q ⊕ W)¹`, `((q, z), x) ↦ (q, z + (1 + A)x)`. -/
def fiberInv : ScOperator (𝒮.F' Q) (ScBanach.paramProd Q W).shift where
  lvl m := ((ContinuousLinearMap.fst ℝ Q 𝒮.Zs).comp
      (ContinuousLinearMap.fst ℝ (Q × 𝒮.Zs) (W.levelSub 𝒮.Xs (m + 1)))).prod
    (((𝒮.liftZ (m + 1)).comp ((ContinuousLinearMap.snd ℝ Q 𝒮.Zs).comp
      (ContinuousLinearMap.fst ℝ (Q × 𝒮.Zs) (W.levelSub 𝒮.Xs (m + 1))))) +
      (𝒮.T (m + 1)).comp ((W.levelSub 𝒮.Xs (m + 1)).subtypeL.comp
        (ContinuousLinearMap.snd ℝ (Q × 𝒮.Zs) (W.levelSub 𝒮.Xs (m + 1)))))
  incl_comm m y := by
    refine Prod.ext rfl ?_
    change W.incl (m + 1) (𝒮.liftZ (m + 2) y.1.2 + 𝒮.T (m + 2) y.2.val) =
      𝒮.liftZ (m + 1) y.1.2 + 𝒮.T (m + 1) (W.incl (m + 1) y.2.val)
    rw [map_add, W.incl_finLift, 𝒮.T.incl_comm]

lemma fiberInv_apply (m : ℕ) (y : 𝒮.F' Q m) :
    𝒮.fiberInv m y = ((y.1.1, 𝒮.liftZ (m + 1) y.1.2 + 𝒮.T (m + 1) y.2.val) : Q × W (m + 1)) :=
  rfl

lemma fiber_fiberInv (m : ℕ) (y : 𝒮.F' Q m) : 𝒮.fiber m (𝒮.fiberInv m y) = y := by
  obtain ⟨⟨q, z⟩, x⟩ := y
  have hx : x.val ∈ W.levelSub 𝒮.Xs (m + 1) := x.2
  refine Prod.ext (Prod.ext rfl ?_) ?_
  · change 𝒮.toZ (m + 1) (𝒮.liftZ (m + 1) z + 𝒮.T (m + 1) x.val) = z
    rw [map_add, 𝒮.toZ_liftZ, 𝒮.toZ_T, add_zero]
  · change 𝒮.LinvP (m + 1) (𝒮.liftZ (m + 1) z + 𝒮.T (m + 1) x.val) = x
    have h1 : 𝒮.LinvP (m + 1) (𝒮.liftZ (m + 1) z) = 0 := by
      rw [LinvP_apply, 𝒮.projR_liftZ, map_zero]
    rw [map_add, h1, zero_add]
    exact Subtype.ext (𝒮.LinvP_T hx)

lemma fiberInv_fiber (m : ℕ) (y : (ScBanach.paramProd Q W) (m + 1)) :
    𝒮.fiberInv m (𝒮.fiber m y) = y := by
  refine Prod.ext rfl ?_
  change 𝒮.liftZ (m + 1) (𝒮.toZ (m + 1) y.2) + 𝒮.T (m + 1) (𝒮.LinvP (m + 1) y.2 : W (m + 1)) = y.2
  rw [𝒮.liftZ_toZ, 𝒮.T_LinvP, add_comm (𝒮.projZ (m + 1) y.2 : W (m + 1)), 𝒮.projR_add_projZ]

lemma fiber_eq_zero_iff (m : ℕ) (y : (ScBanach.paramProd Q W) (m + 1)) :
    𝒮.fiber m y = 0 ↔ y = 0 :=
  ⟨fun h => by rw [← 𝒮.fiberInv_fiber m y, h, map_zero], fun h => by rw [h, map_zero]⟩

/-! #### The pushed-forward germ -/

/-- The level shift of an sc-operator, `T : E¹ → F¹`. -/
def _root_.Polyfold.ScOperator.shiftOp {E F : ScBanach} (T : ScOperator E F) :
    ScOperator E.shift F.shift where
  lvl m := T (m + 1)
  incl_comm m x := T.incl_comm (m + 1) x

@[simp] lemma _root_.Polyfold.ScOperator.shiftOp_apply {E F : ScBanach} (T : ScOperator E F) (m : ℕ)
    (x : E (m + 1)) : T.shiftOp m x = T (m + 1) x := rfl

/-- The inclusion `W → Q ⊕ W`, `w ↦ (0, w)`, as an sc-operator. -/
def _root_.Polyfold.ScBanach.inrOp (Q : Type) [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [FiniteDimensional ℝ Q] (W : ScBanach) : ScOperator W (ScBanach.paramProd Q W) where
  lvl m := ContinuousLinearMap.inr ℝ Q (W m)
  incl_comm _ _ := rfl

/-- The perturbed germ `f + s : O(C̃ ⊕ W, 0) → Q ⊕ W` (the text's `f + s`, with
`s : U → ℝᴺ ⊕ W¹` replaced by its `W`-component). -/
def fsum (f : P × W 0 → Q × W 0) : P × W 0 → Q × W 0 :=
  (ScBanach.paramProd Q W).addOp 0 ∘
    pairMap (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) (G := ScBanach.paramProd Q W)
      f (((ScBanach.inrOp Q W).comp W.shiftIncl) 0 ∘ 𝒮.s)

lemma fsum_apply (f : P × W 0 → Q × W 0) (x : P × W 0) :
    𝒮.fsum f x = f x + ((0 : Q), W.toBase 1 (𝒮.s x)) := rfl

/-- `B̄ = B − S` with `S(a, w) = s(a, w) − Aw` (proof of Theorem 3.4.2 (preprint 3.38), "we have abbreviated
`B̄(a, w) = B(a, w) − S(a, w)`"), as a germ on `O(C̃ ⊕ W, 0)`. -/
def Bbar (B : P × W 0 → W 0) : P × W 0 → W 0 :=
  W.addOp 0 ∘ pairMap (E := ScBanach.paramProd P W) (F := W) (G := W) B ((W.negOp.comp W.shiftIncl) 0 ∘
    (W.shift.addOp 0 ∘ pairMap (E := ScBanach.paramProd P W) (F := W.shift) (G := W.shift) 𝒮.s
      ((W.shift.negOp.comp (𝒮.A.comp (ScBanach.sndOp (ScBanach.const P) W))) 0)))

lemma Bbar_apply (B : P × W 0 → W 0) (x : P × W 0) :
    𝒮.Bbar B x = B x - (W.toBase 1 (𝒮.s x) - W.toBase 1 (𝒮.A 0 x.2)) := by
  change B x + -(W.incl 0 (𝒮.s x + -(𝒮.A 0 x.2))) = _
  rw [map_add, map_neg, sub_eq_add_neg, sub_eq_add_neg]; rfl

lemma Bbar_zero {B : P × W 0 → W 0} (hB0 : B (0, 0) = 0) : 𝒮.Bbar B 0 = 0 := by
  rw [Bbar_apply]
  change B (0, 0) - (W.toBase 1 (𝒮.s 0) - W.toBase 1 (𝒮.A 0 0)) = 0
  rw [hB0, 𝒮.s_zero]; simp

/-- The germ of neighbourhoods of the pushed-forward germ: `U'_m = ψ(U_{m+1})`, the
preimage of `U_{m+1}` under `ψ⁻¹`. -/
def pushGerm : ScNbhdGerm 𝒮.E' ((Ct ×ˢ univ) ×ˢ univ) where
  U m := 𝒮.glue m ⁻¹' 𝒮.G.U (m + 1)
  nested m y hy := by
    show 𝒮.glue m (𝒮.E'.incl m y) ∈ 𝒮.G.U (m + 1)
    rw [← 𝒮.glue.incl_comm]
    exact 𝒮.G.nested (m + 1) _ hy
  zero_mem m := by
    show 𝒮.glue m 0 ∈ 𝒮.G.U (m + 1)
    rw [map_zero]; exact 𝒮.G.zero_mem _
  relOpen m := by
    obtain ⟨O, hO, hU⟩ := 𝒮.G.relOpen (m + 1)
    refine ⟨𝒮.glue m ⁻¹' O, hO.preimage (𝒮.glue m).continuous, ?_⟩
    ext y
    rw [ScBanach.paramProd_lvlSet]
    change 𝒮.glue m y ∈ 𝒮.G.U (m + 1) ↔ 𝒮.glue m y ∈ O ∧ y ∈ (Ct ×ˢ univ) ×ˢ univ
    rw [hU, ScBanach.paramProd_lvlSet, mem_inter_iff, glue_apply]
    simp only [mem_prod, mem_univ, and_true]

lemma mem_pushGerm_U {m : ℕ} {y : 𝒮.E' m} : y ∈ 𝒮.pushGerm.U m ↔ 𝒮.glue m y ∈ 𝒮.G.U (m + 1) :=
  Iff.rfl

lemma glue_mapsToGerm : 𝒮.pushGerm.MapsToGerm 𝒮.G.shift (𝒮.glue 0) := by
  intro m y hy
  rw [ScOperator.levelMap_eq]
  exact hy

/-- **The pushed-forward germ `Φ_*(f + s)` of Theorem 3.4.2 (preprint 3.38)** (on level `1`):
`Ψ ∘ (f + s) ∘ ψ⁻¹ : (P ⊕ C) ⊕ X¹ → (Q ⊕ Z) ⊕ X¹`. -/
def pushMap (f : P × W 0 → Q × W 0) : 𝒮.E' 0 → 𝒮.F' Q 0 :=
  𝒮.fiber 0 ∘ levelMap (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) (𝒮.fsum f) 1 ∘
    𝒮.glue 0

/-- **The contraction map `B̂` of Theorem 3.4.2 (preprint 3.38)**: `B̂((a, c), x) = L⁻¹P₂ B̄(a, c + x)`. -/
def pushB (B : P × W 0 → W 0) : 𝒮.E' 0 → 𝒮.XB.shift 0 :=
  𝒮.LinvPOp.shiftOp 0 ∘ levelMap (E := ScBanach.paramProd P W) (F := W) (𝒮.Bbar B) 1 ∘ 𝒮.glue 0

variable (hC : IsQuadrantLike (ScBanach.const P) Ct)
include hC

lemma isQuadrantLike_E' : IsQuadrantLike 𝒮.E' ((Ct ×ˢ univ) ×ˢ univ) :=
  (hC.prod_univ_const (Q := 𝒮.Cs)).paramProd _

/-- `f + s` is sc-smooth (the sum rule). -/
lemma fsum_isScSmoothGerm {f : P × W 0 → Q × W 0}
    (hf : IsScSmoothGerm (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) 𝒮.G f) :
    IsScSmoothGerm (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) 𝒮.G (𝒮.fsum f) :=
  fun k =>
  ((hf k).pair (hC.paramProd W) ((𝒮.isScSmooth k).operator_comp (hC.paramProd W) _)).operator_comp
    (hC.paramProd W) _

omit hC in
lemma Bbar_isSc0Germ {B : P × W 0 → W 0} (hB : IsSc0Germ 𝒮.G B) : IsSc0Germ 𝒮.G (𝒮.Bbar B) := by
  refine ((W.addOp.isSc0Germ _).comp ?_ (𝒮.G.mapsToGerm_full _))
  refine hB.pair (((W.negOp.comp W.shiftIncl).isSc0Germ _).comp ?_ (𝒮.G.mapsToGerm_full _))
  refine ((W.shift.addOp.isSc0Germ _).comp ?_ (𝒮.G.mapsToGerm_full _))
  exact IsSc0Germ.pair (𝒮.isScSmooth 0)
    (((W.shift.negOp.comp (𝒮.A.comp (ScBanach.sndOp (ScBanach.const P) W))).isSc0Germ _))

/-- The pushed-forward germ is sc-smooth: it is `Ψ ∘ (f + s)¹ ∘ ψ⁻¹` with `Ψ`, `ψ⁻¹`
sc-operators and `(f + s)¹` sc-smooth on the shifted germ (Proposition 1.2.2 (preprint 1.17)). -/
theorem pushMap_isScSmoothGerm {f : P × W 0 → Q × W 0}
    (hf : IsScSmoothGerm (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) 𝒮.G f) :
    IsScSmoothGerm 𝒮.pushGerm (𝒮.pushMap f) := by
  intro k
  have hE' := 𝒮.isQuadrantLike_E' hC
  refine IsSckGerm.operator_comp hE' _ ?_
  exact IsSckGerm.comp hE' (hC.paramProd W).shift ((𝒮.fsum_isScSmoothGerm hC hf k).shift (hC.paramProd W))
    (𝒮.glue.isSckGerm k _ hE') 𝒮.glue_mapsToGerm

omit hC in
/-- The `W`-component of `(f + s)¹` at a level-`1` point: `(1 + A)w − B̄(a, w)`. -/
lemma snd_levelMap_fsum {f : P × W 0 → Q × W 0} {B : P × W 0 → W 0} (hf : IsBasicGerm Ct 𝒮.G f B)
    {x : (ScBanach.paramProd P W) 1} (hx : x ∈ 𝒮.G.U 1) :
    (levelMap (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) (𝒮.fsum f) 1 x).2 =
      𝒮.T 1 x.2 - levelMap (E := ScBanach.paramProd P W) (F := W) (𝒮.Bbar B) 1 x := by
  have hfs : IsSc0Germ (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) 𝒮.G (𝒮.fsum f) := by
    refine (((ScBanach.paramProd Q W).addOp.isSc0Germ _).comp ?_ (𝒮.G.mapsToGerm_full _))
    exact IsSc0Germ.pair (hf.isScSmooth 0)
      ((((ScBanach.inrOp Q W).comp W.shiftIncl).isSc0Germ _).comp (𝒮.isScSmooth 0)
        (𝒮.G.mapsToGerm_full _))
  have hBb : IsSc0Germ 𝒮.G (𝒮.Bbar B) := 𝒮.Bbar_isSc0Germ hf.contraction.isSc0
  apply W.toBase_injective 1
  have h1 := congrArg Prod.snd (hfs.toBase_levelMap hx)
  rw [ScBanach.paramProd_toBase] at h1
  change W.toBase 1 (levelMap (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W)
    (𝒮.fsum f) 1 x).2 = (𝒮.fsum f ((ScBanach.paramProd P W).toBase 1 x)).2 at h1
  have hA : W.toBase 1 (W.incl 1 (𝒮.A 1 x.2)) = W.toBase 1 (𝒮.A 0 (W.toBase 1 x.2)) := by
    rw [← ScScale.toBase_succ, W.shift_toBase 1, 𝒮.A.toBase_comm 1]
  rw [h1, fsum_apply, Prod.snd_add, hf.snd_eq _ (𝒮.G.toBase_mem hx), map_sub,
    hBb.toBase_levelMap hx, Bbar_apply, T_apply, map_add, hA, ScBanach.paramProd_toBase]
  dsimp only
  abel

omit hC in
/-- The identity `P ∘ Ψ ∘ (f + s) ∘ ψ⁻¹(a, c, x) = x − B̂(a, c, x)` (the "desired formula" of the
proof of Theorem 3.4.2 (preprint 3.38)). -/
theorem snd_pushMap {f : P × W 0 → Q × W 0} {B : P × W 0 → W 0} (hf : IsBasicGerm Ct 𝒮.G f B)
    {y : 𝒮.E' 0} (hy : y ∈ 𝒮.pushGerm.U 0) : (𝒮.pushMap f y).2 = y.2 - 𝒮.pushB B y := by
  obtain ⟨⟨a, c⟩, x⟩ := y
  have hx : x.val ∈ W.levelSub 𝒮.Xs 1 := x.2
  unfold pushMap pushB
  simp only [Function.comp_apply]
  rw [fiber_apply]
  simp only
  rw [𝒮.snd_levelMap_fsum hf hy, map_sub, ScOperator.shiftOp_apply, LinvPOp_apply]
  congr 1
  rw [glue_apply]
  show 𝒮.LinvP 1 (𝒮.T 1 (𝒮.liftC 1 c + x.val)) = x
  rw [map_add, 𝒮.T_liftC, zero_add]
  exact Subtype.ext (𝒮.LinvP_T hx)

omit hC in
lemma pushMap_zero {f : P × W 0 → Q × W 0} (hf0 : f 0 = 0) : 𝒮.pushMap f 0 = 0 := by
  have : levelMap (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) (𝒮.fsum f) 1 0 = 0 := by
    apply levelMap_eq_of_toBase_eq
    rw [map_zero, map_zero, fsum_apply, hf0, 𝒮.s_zero, map_zero]
    simp only [zero_add, Prod.mk_zero_zero]
  unfold pushMap
  simp only [Function.comp_apply, map_zero, this]

omit hC in
lemma pushB_zero {B : P × W 0 → W 0} (hB0 : B (0, 0) = 0) : 𝒮.pushB B 0 = 0 := by
  have : levelMap (E := ScBanach.paramProd P W) (F := W) (𝒮.Bbar B) 1 0 = 0 := by
    apply levelMap_eq_of_toBase_eq
    rw [map_zero, map_zero, 𝒮.Bbar_zero hB0]
  unfold pushB
  simp only [Function.comp_apply, map_zero, this]

omit hC in
/-- `B̄_{m+1} = B_{m+1} − S_m` on `U_{m+1}`. -/
lemma levelMap_Bbar {B : P × W 0 → W 0} (hB : IsSc0Germ 𝒮.G B) {m : ℕ}
    {x : (ScBanach.paramProd P W) (m + 1)} (hx : x ∈ 𝒮.G.U (m + 1)) :
    levelMap (E := ScBanach.paramProd P W) (F := W) (𝒮.Bbar B) (m + 1) x =
      levelB B (m + 1) x - scPlusRemainder 𝒮.hs m x := by
  apply levelMap_eq_of_toBase_eq
  rw [map_sub, hB.toBase_levelMap hx, Bbar_apply, scPlusRemainder, map_sub, W.shift_toBase m,
    𝒮.hs.isSc0.toBase_levelMap (𝒮.G.nested m x hx), ← ScScale.toBase_succ, W.shift_toBase m,
    𝒮.A.toBase_comm m, ← ScScale.toBase_succ, ScBanach.paramProd_toBase]

omit hC in
lemma levelMap_pushB {B : P × W 0 → W 0} (hB : IsSc0Germ 𝒮.G B) {m : ℕ} {y : 𝒮.E' m}
    (hy : y ∈ 𝒮.pushGerm.U m) :
    levelMap (E := 𝒮.E') (F := 𝒮.XB.shift) (𝒮.pushB B) m y =
      𝒮.LinvP (m + 1) (levelMap (E := ScBanach.paramProd P W) (F := W) (𝒮.Bbar B) (m + 1)
        (𝒮.glue m y)) := by
  have hBb : IsSc0Germ 𝒮.G (𝒮.Bbar B) := 𝒮.Bbar_isSc0Germ hB
  have hinner : IsSc0Germ (E := 𝒮.E') (F := W.shift) 𝒮.pushGerm
      (levelMap (E := ScBanach.paramProd P W) (F := W) (𝒮.Bbar B) 1 ∘ 𝒮.glue 0) :=
    hBb.shift.comp (𝒮.glue.isSc0Germ _) 𝒮.glue_mapsToGerm
  unfold pushB
  rw [IsSc0Germ.levelMap_comp (𝒮.LinvPOp.shiftOp.isSc0Germ _) hinner (𝒮.pushGerm.mapsToGerm_full _) hy,
    ScOperator.levelMap_eq, IsSc0Germ.levelMap_comp hBb.shift (𝒮.glue.isSc0Germ _)
      𝒮.glue_mapsToGerm hy, ScOperator.levelMap_eq, hBb.levelMap_shift hy]
  rfl

/-- **`B̂` is an sc⁰-contraction germ on the index-raised structure** (the core of Theorem 3.4.2 (preprint 3.38)):
on level `m` of `(P ⊕ C) ⊕ X¹`, i.e. level `m + 1` of `W`, `B̂ = L⁻¹P₂(B − S)` is a contraction in
`x` with arbitrarily small constant near `0`, since `B` is (Definition 3.1.7 (preprint 3.7)) and `S` is
(`scPlusRemainder_contraction`). -/
theorem pushB_isSc0ContractionGerm {f : P × W 0 → Q × W 0} {B : P × W 0 → W 0}
    (hf : IsBasicGerm Ct 𝒮.G f B) : IsSc0ContractionGerm (Ct ×ˢ univ) 𝒮.pushGerm (𝒮.pushB B) where
  isSc0 :=
    (𝒮.LinvPOp.shiftOp.isSc0Germ _).comp
      ((𝒮.Bbar_isSc0Germ hf.contraction.isSc0).shift.comp (𝒮.glue.isSc0Germ _) 𝒮.glue_mapsToGerm)
      (𝒮.pushGerm.mapsToGerm_full _)
  B_zero := 𝒮.pushB_zero hf.contraction.B_zero
  contraction := by
    intro ε hε m
    set Λ : ℝ := ‖𝒮.LinvP (m + 1)‖ with hΛ
    set ε' : ℝ := ε / (2 * (Λ + 1)) with hε'
    have hε'pos : 0 < ε' := by positivity
    obtain ⟨rB, hrB, hB⟩ := hf.contraction.contraction ε' hε'pos (m + 1)
    obtain ⟨rS, hrS, hS⟩ := scPlusRemainder_contraction hC 𝒮.hs m hε'pos
    set K : ℝ := ‖𝒮.liftC (m + 1)‖ with hK
    set r : ℝ := min rB rS / (K + 2) with hr
    have hrpos : 0 < r := by positivity
    have hrK : r * (K + 2) = min rB rS := by
      rw [hr]; exact div_mul_cancel₀ _ (by positivity)
    have hrmin : r ≤ min rB rS := by
      rw [hr]; exact div_le_self (le_min hrB.le hrS.le) (by linarith [norm_nonneg (𝒮.liftC (m + 1))])
    have hrB' : r ≤ rB := hrmin.trans (min_le_left _ _)
    have hrS' : r ≤ rS := hrmin.trans (min_le_right _ _)
    refine ⟨r, hrpos, fun ac hac hac' x x' hx hx' => ?_⟩
    obtain ⟨a, c⟩ := ac
    have ha : a ∈ Ct := hac.1
    have ha' : ‖a‖ < rB := lt_of_le_of_lt (norm_fst_le (a, c)) (hac'.trans_le hrB')
    have haS : ‖a‖ < rS := lt_of_le_of_lt (norm_fst_le (a, c)) (hac'.trans_le hrS')
    have hc' : ‖c‖ < r := lt_of_le_of_lt (norm_snd_le (a, c)) hac'
    -- the points `w = c + x`, `w' = c + x'` on level `m + 1`
    set w : W (m + 1) := 𝒮.liftC (m + 1) c + x.val with hw
    set w' : W (m + 1) := 𝒮.liftC (m + 1) c + x'.val with hw'
    have hwbound : ∀ z : 𝒮.XB.shift m, ‖z‖ < r → ‖𝒮.liftC (m + 1) c + z.val‖ < min rB rS := by
      intro z hz
      have hz' : ‖z.val‖ = ‖z‖ := rfl
      calc ‖𝒮.liftC (m + 1) c + z.val‖ ≤ ‖𝒮.liftC (m + 1) c‖ + ‖z.val‖ := norm_add_le _ _
        _ ≤ K * ‖c‖ + ‖z‖ := by rw [hz']; gcongr; exact (𝒮.liftC (m + 1)).le_opNorm c
        _ < K * r + r := by
            have : K * ‖c‖ ≤ K * r := mul_le_mul_of_nonneg_left hc'.le (norm_nonneg _)
            linarith
        _ ≤ min rB rS := by rw [← hrK]; nlinarith [hrpos.le, norm_nonneg (𝒮.liftC (m + 1))]
    have hwB : ‖w‖ < rB := (hwbound x hx).trans_le (min_le_left _ _)
    have hw'B : ‖w'‖ < rB := (hwbound x' hx').trans_le (min_le_left _ _)
    have hwS : ‖w‖ < rS := (hwbound x hx).trans_le (min_le_right _ _)
    have hw'S : ‖w'‖ < rS := (hwbound x' hx').trans_le (min_le_right _ _)
    have hmemU : ((a, w) : (ScBanach.paramProd P W) (m + 1)) ∈ 𝒮.G.U (m + 1) := (hB a ha ha' w w hwB hwB).1
    have hmem : (((a, c), x) : 𝒮.E' m) ∈ 𝒮.pushGerm.U m := by
      rw [mem_pushGerm_U, glue_apply]; exact hmemU
    refine ⟨hmem, ?_⟩
    have hmem' : (((a, c), x') : 𝒮.E' m) ∈ 𝒮.pushGerm.U m := by
      rw [mem_pushGerm_U, glue_apply]; exact (hB a ha ha' w' w' hw'B hw'B).1
    have hB0 := hf.contraction.isSc0
    unfold levelB
    rw [𝒮.levelMap_pushB hB0 hmem, 𝒮.levelMap_pushB hB0 hmem', glue_apply, glue_apply]
    simp only
    have e1 : levelMap (E := ScBanach.paramProd P W) (F := W) (𝒮.Bbar B) (m + 1) (a, 𝒮.liftC (m + 1) c + x.val) =
        levelB B (m + 1) (a, w) - scPlusRemainder 𝒮.hs m (a, w) := 𝒮.levelMap_Bbar hB0 hmemU
    have e2 : levelMap (E := ScBanach.paramProd P W) (F := W) (𝒮.Bbar B) (m + 1) (a, 𝒮.liftC (m + 1) c + x'.val) =
        levelB B (m + 1) (a, w') - scPlusRemainder 𝒮.hs m (a, w') :=
      𝒮.levelMap_Bbar hB0 (hB a ha ha' w' w' hw'B hw'B).1
    rw [e1, e2]
    have hdiff : w - w' = x.val - x'.val := by rw [hw, hw']; abel
    have hnorm : ‖x - x'‖ = ‖w - w'‖ := by rw [hdiff]; rfl
    have h1 := (hB a ha ha' w w' hwB hw'B).2
    have h2 := (hS a ha haS w w' hwS hw'S).2
    have key : ‖𝒮.LinvP (m + 1) (levelB B (m + 1) (a, w) - scPlusRemainder 𝒮.hs m (a, w)) -
        𝒮.LinvP (m + 1) (levelB B (m + 1) (a, w') - scPlusRemainder 𝒮.hs m (a, w'))‖ ≤
        ε * ‖w - w'‖ := by
      rw [← map_sub]
      calc ‖𝒮.LinvP (m + 1) ((levelB B (m + 1) (a, w) - scPlusRemainder 𝒮.hs m (a, w)) -
            (levelB B (m + 1) (a, w') - scPlusRemainder 𝒮.hs m (a, w')))‖
          ≤ Λ * ‖(levelB B (m + 1) (a, w) - scPlusRemainder 𝒮.hs m (a, w)) -
            (levelB B (m + 1) (a, w') - scPlusRemainder 𝒮.hs m (a, w'))‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = Λ * ‖(levelB B (m + 1) (a, w) - levelB B (m + 1) (a, w')) -
            (scPlusRemainder 𝒮.hs m (a, w) - scPlusRemainder 𝒮.hs m (a, w'))‖ := by
            congr 2; abel
        _ ≤ Λ * (‖levelB B (m + 1) (a, w) - levelB B (m + 1) (a, w')‖ +
            ‖scPlusRemainder 𝒮.hs m (a, w) - scPlusRemainder 𝒮.hs m (a, w')‖) := by
            gcongr; exact norm_sub_le _ _
        _ ≤ Λ * (ε' * ‖w - w'‖ + ε' * ‖w - w'‖) := by gcongr
        _ = (2 * ε' * Λ) * ‖w - w'‖ := by ring
        _ ≤ ε * ‖w - w'‖ := by
            gcongr
            rw [hε']
            have : 2 * (ε / (2 * (Λ + 1))) * Λ = ε * (Λ / (Λ + 1)) := by field_simp
            rw [this]
            exact mul_le_of_le_one_right hε.le
              ((div_le_one (by positivity)).2 (by linarith))
    rw [hnorm]
    exact key

/-- **Theorem 3.4.2 (preprint 3.38) (weak stability of basic germs)**: let `f : O(C̃ ⊕ W, 0) → Q ⊕ W` be a basic
germ and `s` an sc⁺-germ with `s(0) = 0` (the `W`-component of the sc⁺-section; its
`Q`-component does not enter).  With the sc-Fredholm splitting `W = C ⊕ X = R ⊕ Z` of
`1 + D₂s(0)` (Proposition 1.1.11 (preprint 1.10)), the strong bundle isomorphism `Φ = (ψ, Ψ)` with the **linear**
base change `ψ(a, w) = ((a, (1 − P₁)w), P₁w)` (`StabilityData.split`, inverse `glue`) and fibre
change `Ψ(q, w) = ((q, (1 − P₂)w), L⁻¹P₂w)` (`fiber`, inverse `fiberInv`) carries `f + s` to the
germ `(Φ_*(f + s))¹ = pushMap f` on `O((C̃ ⊕ C) ⊕ X¹, 0)` (levels raised by one), which is a
basic germ with contraction map `B̂ = pushB B`. -/
theorem _root_.Polyfold.theorem_3_4_2 {f : P × W 0 → Q × W 0} {B : P × W 0 → W 0}
    (hf : IsBasicGerm Ct 𝒮.G f B) :
    IsBasicGerm (Ct ×ˢ univ) 𝒮.pushGerm (𝒮.pushMap f) (𝒮.pushB B) where
  isScSmooth := 𝒮.pushMap_isScSmoothGerm hC hf.isScSmooth
  f_zero := 𝒮.pushMap_zero hf.f_zero
  snd_eq _ hy := 𝒮.snd_pushMap hf hy
  contraction := 𝒮.pushB_isSc0ContractionGerm hC hf

omit hC in
/-- The solution sets correspond: for `y ∈ U'_0`, `Φ_*(f + s)(y) = 0` iff `(f + s)(ψ⁻¹ y) = 0`
(the fibre change `Ψ` is a linear isomorphism). -/
theorem pushMap_eq_zero_iff {f : P × W 0 → Q × W 0}
    (hf : IsScSmoothGerm (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) 𝒮.G f)
    {y : 𝒮.E' 0} (hy : y ∈ 𝒮.pushGerm.U 0) :
    𝒮.pushMap f y = 0 ↔ 𝒮.fsum f ((ScBanach.paramProd P W).toBase 1 (𝒮.glue 0 y)) = 0 := by
  have hfs : IsSc0Germ (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) 𝒮.G (𝒮.fsum f) := by
    refine (((ScBanach.paramProd Q W).addOp.isSc0Germ _).comp ?_ (𝒮.G.mapsToGerm_full _))
    exact IsSc0Germ.pair (hf 0)
      ((((ScBanach.inrOp Q W).comp W.shiftIncl).isSc0Germ _).comp (𝒮.isScSmooth 0)
        (𝒮.G.mapsToGerm_full _))
  unfold pushMap
  rw [Function.comp_apply, Function.comp_apply, 𝒮.fiber_eq_zero_iff, ← hfs.toBase_levelMap hy]
  constructor
  · intro h; rw [h, map_zero]
  · intro h; exact (ScBanach.paramProd Q W).toBase_injective 1 (by rw [h, map_zero])

omit hC in
/-- **Theorem 3.4.2 (preprint 3.38), the index**: `dim C = dim Z` ("because the Fredholm index is invariant under
strong bundle isomorphisms": `ind(1 + A) = ind(1) = 0` by Proposition 1.1.11 (preprint 1.10)), so that
`n − N = n' − N'` with `n' = n + dim C`, `N' = N + dim Z`. -/
theorem finrank_Cs_eq_finrank_Zs : Module.finrank ℝ 𝒮.Cs = Module.finrank ℝ 𝒮.Zs := by
  have h1 := 𝒮.sp.index_eq
  have h2 : scIndex 𝒮.T = 0 := by
    rw [proposition_1_1_11_index (isScFredholm_id W) 𝒮.A, scIndex_id]
  rw [h2] at h1
  unfold ScFredholmSplitting.index at h1
  change (Module.finrank ℝ 𝒮.sp.K : ℤ) - Module.finrank ℝ 𝒮.sp.C = 0 at h1
  show Module.finrank ℝ 𝒮.sp.K = Module.finrank ℝ 𝒮.sp.C
  omega


/-! #### The coordinate changes on level `0` (the sc-isomorphisms `ψ`, `Ψ` themselves) -/

omit hC

/-- The new structure before the index raise, `E'₀ = (P ⊕ C) ⊕ X`. -/
abbrev E₀' : ScBanach := ScBanach.paramProd (P × 𝒮.Cs) 𝒮.XB

/-- The new target before the index raise, `(Q ⊕ Z) ⊕ X`. -/
abbrev F₀' (Q : Type) [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] : ScBanach :=
  ScBanach.paramProd (Q × 𝒮.Zs) 𝒮.XB

/-- `ψ⁻¹ : (P ⊕ C) ⊕ X → P ⊕ W`, `((a, c), x) ↦ (a, c + x)`, on every level (`glue` is its
level shift). -/
def glue₀ : ScOperator 𝒮.E₀' (ScBanach.paramProd P W) where
  lvl m := ((ContinuousLinearMap.fst ℝ P 𝒮.Cs).comp
      (ContinuousLinearMap.fst ℝ (P × 𝒮.Cs) (W.levelSub 𝒮.Xs m))).prod
    (((𝒮.liftC m).comp ((ContinuousLinearMap.snd ℝ P 𝒮.Cs).comp
      (ContinuousLinearMap.fst ℝ (P × 𝒮.Cs) (W.levelSub 𝒮.Xs m)))) +
      (W.levelSub 𝒮.Xs m).subtypeL.comp
        (ContinuousLinearMap.snd ℝ (P × 𝒮.Cs) (W.levelSub 𝒮.Xs m)))
  incl_comm m y := by
    refine Prod.ext rfl ?_
    change W.incl m (𝒮.liftC (m + 1) y.1.2 + y.2.val) = 𝒮.liftC m y.1.2 + W.incl m y.2.val
    rw [map_add, W.incl_finLift]

lemma glue₀_apply (m : ℕ) (y : 𝒮.E₀' m) :
    𝒮.glue₀ m y = ((y.1.1, 𝒮.liftC m y.1.2 + y.2.val) : P × W m) := rfl

lemma glue_eq_glue₀ (m : ℕ) (y : 𝒮.E' m) : 𝒮.glue m y = 𝒮.glue₀ (m + 1) y := rfl

/-- `ψ : P ⊕ W → (P ⊕ C) ⊕ X`, `(a, w) ↦ ((a, (1 − P₁)w), P₁w)`, on every level. -/
def split₀ : ScOperator (ScBanach.paramProd P W) 𝒮.E₀' where
  lvl m := ((ContinuousLinearMap.fst ℝ P (W m)).prod
      ((𝒮.toC m).comp (ContinuousLinearMap.snd ℝ P (W m)))).prod
    ((𝒮.projX m).comp (ContinuousLinearMap.snd ℝ P (W m)))
  incl_comm m y := by
    refine Prod.ext (Prod.ext rfl ?_) ?_
    · exact 𝒮.toC_incl m y.2
    · exact Subtype.ext (ScBanach.IsScSplitting.incl_proj 𝒮.splitX m y.2)

lemma split₀_apply (m : ℕ) (y : (ScBanach.paramProd P W) m) :
    𝒮.split₀ m y = (((y.1, 𝒮.toC m y.2), 𝒮.projX m y.2) : 𝒮.E₀' m) := rfl

lemma split_eq_split₀ (m : ℕ) (y : (ScBanach.paramProd P W) (m + 1)) :
    𝒮.split m y = 𝒮.split₀ (m + 1) y := rfl

lemma glue₀_split₀ (m : ℕ) (y : (ScBanach.paramProd P W) m) : 𝒮.glue₀ m (𝒮.split₀ m y) = y := by
  refine Prod.ext rfl ?_
  change 𝒮.liftC m (𝒮.toC m y.2) + (𝒮.projX m y.2 : W m) = y.2
  rw [𝒮.liftC_toC, 𝒮.projC_add_projX]

lemma split₀_glue₀ (m : ℕ) (y : 𝒮.E₀' m) : 𝒮.split₀ m (𝒮.glue₀ m y) = y := by
  obtain ⟨⟨a, c⟩, x⟩ := y
  have hx : x.val ∈ W.levelSub 𝒮.Xs m := x.2
  refine Prod.ext (Prod.ext rfl ?_) ?_
  · change 𝒮.toC m (𝒮.liftC m c + x.val) = c
    have h1 : 𝒮.toC m x.val = 0 := 𝒮.toC_coe_Xs m ⟨x.val, hx⟩
    rw [map_add, 𝒮.toC_liftC, h1, add_zero]
  · change 𝒮.projX m (𝒮.liftC m c + x.val) = x
    rw [map_add, 𝒮.projX_liftC, zero_add]
    exact ScBanach.IsScSplitting.proj_apply_left _ _ hx

/-- `Ψ : Q ⊕ W → (Q ⊕ Z) ⊕ X`, `(q, w) ↦ ((q, (1 − P₂)w), L⁻¹P₂w)`, on every level. -/
def fiber₀ : ScOperator (ScBanach.paramProd Q W) (𝒮.F₀' Q) where
  lvl m := ((ContinuousLinearMap.fst ℝ Q (W m)).prod
      ((𝒮.toZ m).comp (ContinuousLinearMap.snd ℝ Q (W m)))).prod
    ((𝒮.LinvP m).comp (ContinuousLinearMap.snd ℝ Q (W m)))
  incl_comm m y := by
    refine Prod.ext (Prod.ext rfl ?_) ?_
    · exact 𝒮.toZ_incl m y.2
    · exact Subtype.ext (𝒮.incl_LinvP m y.2)

lemma fiber₀_apply (m : ℕ) (y : (ScBanach.paramProd Q W) m) :
    𝒮.fiber₀ (Q := Q) m y = (((y.1, 𝒮.toZ m y.2), 𝒮.LinvP m y.2) : 𝒮.F₀' Q m) := rfl

lemma fiber_eq_fiber₀ (m : ℕ) (y : (ScBanach.paramProd Q W) (m + 1)) :
    𝒮.fiber (Q := Q) m y = 𝒮.fiber₀ (m + 1) y := rfl

/-- `Ψ⁻¹ : (Q ⊕ Z) ⊕ X → Q ⊕ W`, `((q, z), x) ↦ (q, z + (1 + A)x)`, on every level. -/
def fiberInv₀ : ScOperator (𝒮.F₀' Q) (ScBanach.paramProd Q W) where
  lvl m := ((ContinuousLinearMap.fst ℝ Q 𝒮.Zs).comp
      (ContinuousLinearMap.fst ℝ (Q × 𝒮.Zs) (W.levelSub 𝒮.Xs m))).prod
    (((𝒮.liftZ m).comp ((ContinuousLinearMap.snd ℝ Q 𝒮.Zs).comp
      (ContinuousLinearMap.fst ℝ (Q × 𝒮.Zs) (W.levelSub 𝒮.Xs m)))) +
      (𝒮.T m).comp ((W.levelSub 𝒮.Xs m).subtypeL.comp
        (ContinuousLinearMap.snd ℝ (Q × 𝒮.Zs) (W.levelSub 𝒮.Xs m))))
  incl_comm m y := by
    refine Prod.ext rfl ?_
    change W.incl m (𝒮.liftZ (m + 1) y.1.2 + 𝒮.T (m + 1) y.2.val) =
      𝒮.liftZ m y.1.2 + 𝒮.T m (W.incl m y.2.val)
    rw [map_add, W.incl_finLift, 𝒮.T.incl_comm]

lemma fiberInv₀_apply (m : ℕ) (y : 𝒮.F₀' Q m) :
    𝒮.fiberInv₀ m y = ((y.1.1, 𝒮.liftZ m y.1.2 + 𝒮.T m y.2.val) : Q × W m) := rfl

lemma fiber₀_fiberInv₀ (m : ℕ) (y : 𝒮.F₀' Q m) : 𝒮.fiber₀ m (𝒮.fiberInv₀ m y) = y := by
  obtain ⟨⟨q, z⟩, x⟩ := y
  have hx : x.val ∈ W.levelSub 𝒮.Xs m := x.2
  refine Prod.ext (Prod.ext rfl ?_) ?_
  · change 𝒮.toZ m (𝒮.liftZ m z + 𝒮.T m x.val) = z
    rw [map_add, 𝒮.toZ_liftZ, 𝒮.toZ_T, add_zero]
  · change 𝒮.LinvP m (𝒮.liftZ m z + 𝒮.T m x.val) = x
    have h1 : 𝒮.LinvP m (𝒮.liftZ m z) = 0 := by
      rw [LinvP_apply, 𝒮.projR_liftZ, map_zero]
    rw [map_add, h1, zero_add]
    exact Subtype.ext (𝒮.LinvP_T hx)

lemma fiberInv₀_fiber₀ (m : ℕ) (y : (ScBanach.paramProd Q W) m) :
    𝒮.fiberInv₀ m (𝒮.fiber₀ m y) = y := by
  refine Prod.ext rfl ?_
  change 𝒮.liftZ m (𝒮.toZ m y.2) + 𝒮.T m (𝒮.LinvP m y.2 : W m) = y.2
  rw [𝒮.liftZ_toZ, 𝒮.T_LinvP, add_comm (𝒮.projZ m y.2 : W m), 𝒮.projR_add_projZ]

lemma fiber₀_eq_zero_iff (m : ℕ) (y : (ScBanach.paramProd Q W) m) :
    𝒮.fiber₀ m y = 0 ↔ y = 0 :=
  ⟨fun h => by rw [← 𝒮.fiberInv₀_fiber₀ m y, h, map_zero], fun h => by rw [h, map_zero]⟩

/-- The germ of neighbourhoods `ψ(U_m)` on level `0` (its level shift is `pushGerm`). -/
def pushGerm₀ : ScNbhdGerm 𝒮.E₀' ((Ct ×ˢ univ) ×ˢ univ) where
  U m := 𝒮.glue₀ m ⁻¹' 𝒮.G.U m
  nested m y hy := by
    show 𝒮.glue₀ m (𝒮.E₀'.incl m y) ∈ 𝒮.G.U m
    rw [← 𝒮.glue₀.incl_comm]
    exact 𝒮.G.nested m _ hy
  zero_mem m := by
    show 𝒮.glue₀ m 0 ∈ 𝒮.G.U m
    rw [map_zero]; exact 𝒮.G.zero_mem _
  relOpen m := by
    obtain ⟨O, hO, hU⟩ := 𝒮.G.relOpen m
    refine ⟨𝒮.glue₀ m ⁻¹' O, hO.preimage (𝒮.glue₀ m).continuous, ?_⟩
    ext y
    rw [ScBanach.paramProd_lvlSet]
    change 𝒮.glue₀ m y ∈ 𝒮.G.U m ↔ 𝒮.glue₀ m y ∈ O ∧ y ∈ (Ct ×ˢ univ) ×ˢ univ
    rw [hU, ScBanach.paramProd_lvlSet, mem_inter_iff, glue₀_apply]
    simp only [mem_prod, mem_univ, and_true]

lemma mem_pushGerm₀_U {m : ℕ} {y : 𝒮.E₀' m} : y ∈ 𝒮.pushGerm₀.U m ↔ 𝒮.glue₀ m y ∈ 𝒮.G.U m :=
  Iff.rfl

lemma pushGerm_U_eq (m : ℕ) : 𝒮.pushGerm.U m = 𝒮.pushGerm₀.U (m + 1) := rfl

lemma glue₀_mapsToGerm : 𝒮.pushGerm₀.MapsToGerm 𝒮.G (𝒮.glue₀ 0) := by
  intro m y hy
  rw [ScOperator.levelMap_eq]
  exact hy

/-- The push-forward `Φ_*(f + s) = Ψ ∘ (f + s) ∘ ψ⁻¹` on level `0` (not yet index-raised). -/
def pushMap₀ (f : P × W 0 → Q × W 0) : 𝒮.E₀' 0 → 𝒮.F₀' Q 0 :=
  𝒮.fiber₀ 0 ∘ 𝒮.fsum f ∘ 𝒮.glue₀ 0

include hC in
/-- `Φ_*(f + s)` is an sc-smooth germ on `ψ(U)`. -/
theorem pushMap₀_isScSmoothGerm {f : P × W 0 → Q × W 0}
    (hf : IsScSmoothGerm (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) 𝒮.G f) :
    IsScSmoothGerm 𝒮.pushGerm₀ (𝒮.pushMap₀ f) := by
  intro k
  have hE' : IsQuadrantLike 𝒮.E₀' ((Ct ×ˢ univ) ×ˢ univ) :=
    (hC.prod_univ_const (Q := 𝒮.Cs)).paramProd _
  refine IsSckGerm.operator_comp hE' _ ?_
  exact IsSckGerm.comp hE' (hC.paramProd W) (𝒮.fsum_isScSmoothGerm hC hf k)
    (𝒮.glue₀.isSckGerm k _ hE') 𝒮.glue₀_mapsToGerm

lemma pushMap₀_zero {f : P × W 0 → Q × W 0} (hf0 : f 0 = 0) : 𝒮.pushMap₀ f 0 = 0 := by
  unfold pushMap₀
  simp only [Function.comp_apply, map_zero, fsum_apply, hf0, 𝒮.s_zero, zero_add,
    Prod.mk_zero_zero]

/-- The index-raised push-forward is the level-`1` map of the level-`0` push-forward. -/
theorem pushMap_eq_levelMap_pushMap₀ {f : P × W 0 → Q × W 0}
    (hf : IsScSmoothGerm (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) 𝒮.G f)
    {x : 𝒮.E' 0} (hx : x ∈ 𝒮.pushGerm.U 0) :
    𝒮.pushMap f x = levelMap (E := 𝒮.E₀') (F := 𝒮.F₀' Q) (𝒮.pushMap₀ f) 1 x := by
  have hfs : IsSc0Germ (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) 𝒮.G (𝒮.fsum f) := by
    refine (((ScBanach.paramProd Q W).addOp.isSc0Germ _).comp ?_ (𝒮.G.mapsToGerm_full _))
    exact IsSc0Germ.pair (hf 0)
      ((((ScBanach.inrOp Q W).comp W.shiftIncl).isSc0Germ _).comp (𝒮.isScSmooth 0)
        (𝒮.G.mapsToGerm_full _))
  symm
  apply levelMap_eq_of_toBase_eq
  unfold pushMap pushMap₀
  simp only [Function.comp_apply]
  rw [fiber_eq_fiber₀, 𝒮.fiber₀.toBase_comm, hfs.toBase_levelMap hx, glue_eq_glue₀,
    𝒮.glue₀.toBase_comm]

end StabilityData

/-- The data of Theorem 3.4.2 (preprint 3.38) exist for every sc-smooth sc⁺-germ `s` with `s(0) = 0`:
`1 + D₂s(0)` is sc-Fredholm by Proposition 1.1.11 (preprint 1.10). -/
theorem StabilityData.exists_of_scPlus {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)}
    {s : P × W 0 → W 1} (hs : IsScSmoothGerm (E := ScBanach.paramProd P W) (F := W.shift) G s)
    (hs0 : s 0 = 0) : ∃ 𝒮 : StabilityData Ct W, 𝒮.G = G ∧ 𝒮.s = s := by
  have h := proposition_1_1_11_preprint (isScFredholm_id W) (scPlusOfDeriv ((hs 1).1.isSc1GermWith_scDerivGerm))
  exact ⟨⟨G, s, hs, hs0, Classical.choice h⟩, rfl, rfl⟩



end Polyfold
