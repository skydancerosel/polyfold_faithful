import Polyfold.Chapter6.OrientationSpace

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, **the remarks after
Theorem 6.6.17** (p. 275; new in the 2021 edition): the orientation bundle `π_f : O_f → X_∞`,
orientability and global continuous sections, the `ℤ₂`-action and `det_f`.  Gap G.91.

# The orientation bundle

## The text, paraphrased

With the topology of Theorem 6.6.17, `π_f : O_f → X_∞` is the orientation bundle of `f`; `f` is
orientable iff `π_f` has a global continuous section; `ℤ₂` acts continuously on `O_f` by
`(x, o_x) ↦ (x, −o_x)`; and `det_f = ℝ ⊗_{ℤ₂} O_f → X_∞` is the determinant bundle of `f`.

## What is formalized

For local transport data `L` whose fibres have exactly two elements (`IsTwoPointed`), and the
topology `orTopology L` of `O_f`:

* `continuous_orSec_iff`: a map `y ↦ o_y` gives a continuous section `y ↦ (y, o_y)` of `π_f`
  iff the transport along every sc-smooth path carries `o` along (`IsContOrOn L univ o`).
  `exists_eq_orSec`: every section of `π_f` is of this form.
* `orNeg` (`(x, o) ↦ (x, −o)`, the other orientation): a homeomorphism (`orNegHomeomorph`), an
  involution without fixed points over `π_f` (`orNeg_orNeg`, `orNeg_ne`, `orProj_orNeg`);
  `orUnitsAct`, the corresponding action of `ℤˣ ≅ ℤ₂` (`orUnitsAct_one`, `orUnitsAct_mul`).
* `detCore`: **`det_f`** as a Mathlib vector bundle core with fibre `ℝ` over `X_∞` (hence a
  topological line bundle, `detCore.TotalSpace`), built on the continuous orientations
  `(U, o)`: the coordinate changes are `±1` according as two continuous orientations agree.
  `detMk x r a` is the class of `r ⊗ a`, and `detMk_eq_iff`, `detMk_surjective` and
  `detMk_neg` say that the fibre over `x` is `ℝ ⊗_{ℤ₂} Or_x`: `(r, a)` and `(r', a')` have the
  same class iff `(r', a') = (r, a)` or `(r', a') = (−r, −a)`.

With `L = orLocalTransport` (the data of `Γ_f`, Theorem 6.6.13):

* `isSectionOrientation_iff_continuous`: `y ↦ o_y` is an orientation of `f` (Definition 6.6.16)
  iff `y ↦ (y, o_y)` is continuous for the topology of Theorem 6.6.17.
* **`isOrientableSection_iff_exists_continuous_section`**: `f` is orientable (Definition 6.6.14,
  equivalently 6.6.15) iff `π_f` has a global continuous section.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

section Generic

variable {hf : B.IsScFredholmSection f}

variable (f hf) in
/-- Every `Or_x^f` has exactly two elements (`exists_two_orx`, from sc⁺-sections through every
point). -/
def IsTwoPointed : Prop :=
  ∀ x (hs : x ∈ PX.smoothSet), ∃ a b : Orx f hf x hs, a ≠ b ∧ ∀ c, c = a ∨ c = b

/-! ### The other orientation -/

open Classical in
/-- **The other orientation** `−a` of `a ∈ Or_x^f` (the element different from `a`). -/
def orOther {x : X} {hs : x ∈ PX.smoothSet} (a : Orx f hf x hs) : Orx f hf x hs :=
  if h : ∃ b, b ≠ a then h.choose else a

theorem orOther_ne (h2 : IsTwoPointed f hf) {x : X} {hs : x ∈ PX.smoothSet}
    (a : Orx f hf x hs) : orOther a ≠ a := by
  have h : ∃ b, b ≠ a := by
    obtain ⟨b₁, b₂, hne, -⟩ := h2 x hs
    by_cases hb : b₁ = a
    · exact ⟨b₂, fun e => hne (hb.trans e.symm)⟩
    · exact ⟨b₁, hb⟩
  unfold orOther
  rw [dif_pos h]
  exact h.choose_spec

/-- In a two-element set, two elements different from a third are equal. -/
theorem eq_of_ne_of_ne_orx (h2 : IsTwoPointed f hf) {x : X} {hs : x ∈ PX.smoothSet}
    {u v w : Orx f hf x hs} (hu : u ≠ w) (hv : v ≠ w) : u = v :=
  let ⟨_, _, _, hall⟩ := h2 x hs
  eq_of_ne_of_ne_of_two hall hu hv

theorem eq_orOther_iff (h2 : IsTwoPointed f hf) {x : X} {hs : x ∈ PX.smoothSet}
    (a c : Orx f hf x hs) : c = orOther a ↔ c ≠ a :=
  ⟨fun h => h ▸ orOther_ne h2 a, fun h => eq_of_ne_of_ne_orx h2 h (orOther_ne h2 a)⟩

@[simp] theorem orOther_orOther (h2 : IsTwoPointed f hf) {x : X} {hs : x ∈ PX.smoothSet}
    (a : Orx f hf x hs) : orOther (orOther a) = a :=
  (eq_of_ne_of_ne_orx h2 (orOther_ne h2 (orOther a)) (orOther_ne h2 a).symm)

/-- **Every bijection of orientation sets commutes with `a ↦ −a`.** -/
theorem equiv_orOther (h2 : IsTwoPointed f hf) {x y : X} {hx : x ∈ PX.smoothSet}
    {hy : y ∈ PX.smoothSet} (e : Orx f hf x hx ≃ Orx f hf y hy) (a : Orx f hf x hx) :
    e (orOther a) = orOther (e a) :=
  ((eq_orOther_iff h2 _ _).2 fun h => orOther_ne h2 a (e.injective h))

/-! ### Continuous sections and continuous orientations -/

variable (L : LocalTransport PX fun x hs => Orx f hf x hs)

/-- `(y, o_y) = (y, o'_y)` iff `o_y = o'_y`. -/
theorem orSec_eq_orSec_iff {o o' : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy}
    (y : PX.SmoothLevel) :
    orSec o y = orSec o' y ↔
      o (PX.smoothVal y) (PX.smoothVal_mem y) = o' (PX.smoothVal y) (PX.smoothVal_mem y) :=
  ⟨fun h => eq_of_heq (Sigma.mk.inj_iff.1 h).2, fun h => by unfold orSec; rw [h]⟩

/-- **Every section of `π_f` is `y ↦ (y, o_y)`** for the map `o_y = σ(y)`. -/
theorem exists_eq_orSec (σ : PX.SmoothLevel → OrSpace f hf) (hσ : ∀ y, (σ y).1 = y) :
    ∃ o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy, σ = orSec o := by
  refine ⟨fun y hy => cast (congrArg (fun z : PX.SmoothLevel =>
    Orx f hf (PX.smoothVal z) (PX.smoothVal_mem z)) (hσ (PX.smoothMk y hy)))
      (σ (PX.smoothMk y hy)).2,
    funext fun y => Sigma.ext (hσ y) ?_⟩
  exact (cast_heq _ _).symm

/-- **A continuous section is carried along every path in the domain of a continuous
orientation**: if `y ↦ (y, o_y)` is continuous and `o'` is a continuous orientation over `V`, the
transport along an sc-smooth path in `V` takes `o` at its start to `o` at its end.  *Proof*: along
the path, the set where `o = o'` is open (the sets `{(y, o'_y)}` are open) and closed (`O_f` is
Hausdorff), so `o = o'` or `o = −o'` along the whole path, and both are carried along. -/
theorem transport_apply_eq_of_continuous (h2 : IsTwoPointed f hf)
    {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy}
    (hc : @Continuous _ _ _ (orTopology L) (orSec o)) {V : Set X}
    {o' : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy} (ho' : IsContOrOn L V o')
    (γ : (Fin 1 → ℝ) → X) (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγV : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ V) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
    (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    L.transport γ hγ h₀ h₁ hs₀ hs₁ (o x₀ hs₀) = o x₁ hs₁ := by
  let _ : TopologicalSpace (OrSpace f hf) := orTopology L
  have _ := t2Space_orTopology L
  set γ' : unitInterval → PX.SmoothLevel := fun τ =>
    PX.smoothMk (γ (pt1 (τ : ℝ))) (mem_smoothSet_of_isScSmoothMap hγ _) with hγ'def
  have hγ'c : Continuous γ' :=
    (continuous_smoothMk_comp hγ).comp (continuous_pt1.comp continuous_subtype_val)
  have hγ'V : ∀ τ, PX.smoothVal (γ' τ) ∈ V := fun τ => hγV _ τ.2
  have hF : Continuous fun τ => orSec o (γ' τ) := hc.comp hγ'c
  have hG : Continuous fun τ => orSec o' (γ' τ) :=
    (continuousOn_orSec ho').comp_continuous hγ'c hγ'V
  set A := {τ : unitInterval | orSec o (γ' τ) = orSec o' (γ' τ)} with hA
  have hAc : IsClosed A := isClosed_eq hF hG
  have hAo : IsOpen A := by
    refine isOpen_iff_mem_nhds.2 fun τ₀ hτ₀ => ?_
    have hmem : orSec o (γ' τ₀) ∈ orBasic V o' := by
      rw [show orSec o (γ' τ₀) = orSec o' (γ' τ₀) from hτ₀]
      exact orSec_mem_orBasic (hγ'V τ₀)
    filter_upwards [hF.continuousAt ((isOpen_orBasic ho').mem_nhds hmem)] with τ hτ
    exact eq_orSec_of_mem_orBasic hτ
  have hiff : ∀ τ, τ ∈ A ↔ o (PX.smoothVal (γ' τ)) (PX.smoothVal_mem _) =
      o' (PX.smoothVal (γ' τ)) (PX.smoothVal_mem _) := fun τ => orSec_eq_orSec_iff _
  subst h₀ h₁
  have hT := ho'.2 γ hγ hγV rfl rfl hs₀ hs₁
  rcases isClopen_iff.1 ⟨hAc, hAo⟩ with hA0 | hA1
  · -- `o = −o'` along the path
    have n0 : o (γ (pt1 0)) hs₀ ≠ o' (γ (pt1 0)) hs₀ := fun h =>
      (show (0 : unitInterval) ∉ A from hA0 ▸ notMem_empty _) ((hiff 0).2 h)
    have n1 : o (γ (pt1 1)) hs₁ ≠ o' (γ (pt1 1)) hs₁ := fun h =>
      (show (1 : unitInterval) ∉ A from hA0 ▸ notMem_empty _) ((hiff 1).2 h)
    refine eq_of_ne_of_ne_orx h2 (w := o' (γ (pt1 1)) hs₁) ?_ n1
    rw [← hT]
    exact fun h => n0 ((L.transport γ hγ rfl rfl hs₀ hs₁).injective h)
  · -- `o = o'` along the path
    have e0 : o (γ (pt1 0)) hs₀ = o' (γ (pt1 0)) hs₀ := (hiff 0).1 (hA1 ▸ mem_univ _)
    have e1 : o (γ (pt1 1)) hs₁ = o' (γ (pt1 1)) hs₁ := (hiff 1).1 (hA1 ▸ mem_univ _)
    rw [e0, e1, hT]

/-- **Continuous sections of `π_f` are the maps carried along by the transport**: `y ↦ (y, o_y)`
is continuous for the topology `orTopology L` iff the transport along every sc-smooth path takes
`o` at its start to `o` at its end (`IsContOrOn L univ o`). -/
theorem continuous_orSec_iff (h2 : IsTwoPointed f hf)
    (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy) :
    @Continuous _ _ _ (orTopology L) (orSec o) ↔ IsContOrOn L univ o := by
  constructor
  · intro hc
    refine ⟨isOpen_univ, fun γ hγ _ x₀ x₁ h₀ h₁ hs₀ hs₁ => ?_⟩
    refine L.transport_apply_eq_of_local o
      (fun V => ∃ o', IsContOrOn L V o' ∧ ∃ U', L.Good U' ∧ V ⊆ U')
      (fun ⟨_, h, _⟩ => h.1) (fun x hx => ?_) (fun ⟨_, _, h⟩ => h) ?_ hγ h₀ h₁ hs₀ hs₁
    · obtain ⟨U, o', ho', hU', hp⟩ := exists_isContOrOn L (orSec o (PX.smoothMk x hx))
      exact ⟨U, ⟨o', ho', hU'⟩, hp.1⟩
    · rintro V ⟨o', ho', -⟩ δ hδ hδV y₀ y₁ e₀ e₁ t₀ t₁
      exact transport_apply_eq_of_continuous L h2 hc ho' δ hδ hδV e₀ e₁ t₀ t₁
  · intro h
    have hc := continuousOn_orSec h
    rw [preimage_univ] at hc
    let := orTopology L
    exact continuousOn_univ.1 hc

/-! ### The `ℤ₂`-action -/

/-- **`(x, o) ↦ (x, −o)`** on `O_f`. -/
def orNeg (p : OrSpace f hf) : OrSpace f hf := ⟨p.1, orOther p.2⟩

@[simp] theorem orProj_orNeg (p : OrSpace f hf) : orProj f hf (orNeg p) = orProj f hf p := rfl

theorem orNeg_orNeg (h2 : IsTwoPointed f hf) (p : OrSpace f hf) : orNeg (orNeg p) = p :=
  Sigma.ext rfl (heq_of_eq (orOther_orOther h2 p.2))

theorem orNeg_ne (h2 : IsTwoPointed f hf) (p : OrSpace f hf) : orNeg p ≠ p := by
  obtain ⟨x, a⟩ := p
  exact fun h => orOther_ne h2 a (eq_of_heq (Sigma.mk.inj_iff.1 h).2)

/-- `−o` is a continuous orientation over `U` if `o` is. -/
theorem IsContOrOn.other (h2 : IsTwoPointed f hf) {U : Set X}
    {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy} (h : IsContOrOn L U o) :
    IsContOrOn L U fun y hy => orOther (o y hy) :=
  ⟨h.1, fun γ hγ hγU _ _ h₀ h₁ hs₀ hs₁ => by
    rw [equiv_orOther h2, h.2 γ hγ hγU h₀ h₁ hs₀ hs₁]⟩

/-- **The `ℤ₂`-action is continuous**: `(x, o) ↦ (x, −o)` is continuous for `orTopology L`. -/
theorem continuous_orNeg (h2 : IsTwoPointed f hf) :
    @Continuous _ _ (orTopology L) (orTopology L) (orNeg (hf := hf)) := by
  let := orTopology L
  exact continuous_def.2 fun W hW U o h => hW U _ (h.other L h2)

/-- `(x, o) ↦ (x, −o)` as a homeomorphism of `O_f`. -/
def orNegHomeomorph (h2 : IsTwoPointed f hf) :
    @Homeomorph (OrSpace f hf) (OrSpace f hf) (orTopology L) (orTopology L) :=
  let := orTopology L
  { toFun := orNeg
    invFun := orNeg
    left_inv := orNeg_orNeg h2
    right_inv := orNeg_orNeg h2
    continuous_toFun := continuous_orNeg L h2
    continuous_invFun := continuous_orNeg L h2 }

open Classical in
/-- **The action of `ℤˣ = {±1} ≅ ℤ₂` on `O_f`**: `1` acts trivially, `−1` by `(x, o) ↦ (x, −o)`. -/
def orUnitsAct (u : ℤˣ) (p : OrSpace f hf) : OrSpace f hf := if u = 1 then p else orNeg p

@[simp] theorem orUnitsAct_one (p : OrSpace f hf) : orUnitsAct 1 p = p := if_pos rfl

theorem orUnitsAct_neg_one (p : OrSpace f hf) : orUnitsAct (-1) p = orNeg p :=
  if_neg (by decide)

theorem orUnitsAct_mul (h2 : IsTwoPointed f hf) (u v : ℤˣ) (p : OrSpace f hf) :
    orUnitsAct (u * v) p = orUnitsAct u (orUnitsAct v p) := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
    simp [orUnitsAct_neg_one, orNeg_orNeg h2]

/-- **`ℤˣ ≅ ℤ₂` acts on `O_f`** (the remarks after Theorem 6.6.17). -/
@[instance_reducible] def orMulAction (h2 : IsTwoPointed f hf) : MulAction ℤˣ (OrSpace f hf) where
  smul := orUnitsAct
  one_smul := orUnitsAct_one
  mul_smul := orUnitsAct_mul h2

theorem continuous_orUnitsAct (h2 : IsTwoPointed f hf) (u : ℤˣ) :
    @Continuous _ _ (orTopology L) (orTopology L) (orUnitsAct (hf := hf) u) := by
  let := orTopology L
  rcases Int.units_eq_one_or u with rfl | rfl
  · rw [show orUnitsAct (hf := hf) 1 = id from funext orUnitsAct_one]
    exact continuous_id
  · rw [show orUnitsAct (hf := hf) (-1) = orNeg from funext orUnitsAct_neg_one]
    exact continuous_orNeg L h2

/-- The action is over `π_f` and free: `π_f(u • p) = π_f(p)`, and `(−1) • p ≠ p`. -/
theorem orProj_orUnitsAct (u : ℤˣ) (p : OrSpace f hf) :
    orProj f hf (orUnitsAct u p) = orProj f hf p := by
  unfold orUnitsAct; split_ifs <;> rfl

/-! ### The determinant bundle `det_f` -/

open Classical in
/-- `+1` where two orientations agree at `x`, `−1` where they differ. -/
def orAgreeSign (o o' : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy) (x : PX.SmoothLevel) : ℝ :=
  if o (PX.smoothVal x) (PX.smoothVal_mem x) = o' (PX.smoothVal x) (PX.smoothVal_mem x) then 1
  else -1

theorem orAgreeSign_self (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy) (x : PX.SmoothLevel) :
    orAgreeSign o o x = 1 := if_pos rfl

theorem orAgreeSign_mul (h2 : IsTwoPointed f hf)
    (o o' o'' : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy)
    (x : PX.SmoothLevel) : orAgreeSign o' o'' x * orAgreeSign o o' x = orAgreeSign o o'' x := by
  unfold orAgreeSign
  by_cases a : o (PX.smoothVal x) (PX.smoothVal_mem x) = o' (PX.smoothVal x) (PX.smoothVal_mem x)
  · by_cases b : o' (PX.smoothVal x) (PX.smoothVal_mem x) =
        o'' (PX.smoothVal x) (PX.smoothVal_mem x)
    · rw [if_pos a, if_pos b, if_pos (a.trans b)]; norm_num
    · rw [if_pos a, if_neg b, if_neg fun c => b (a.symm.trans c)]; norm_num
  · by_cases b : o' (PX.smoothVal x) (PX.smoothVal_mem x) =
        o'' (PX.smoothVal x) (PX.smoothVal_mem x)
    · rw [if_neg a, if_pos b, if_neg fun c => a (c.trans b.symm)]; norm_num
    · rw [if_neg a, if_neg b, if_pos (eq_of_ne_of_ne_orx h2 a fun c => b c.symm)]; norm_num

/-- `orAgreeSign o o'` is locally constant where `o` and `o'` are continuous orientations. -/
theorem orAgreeSign_eventuallyEq {U U' : Set X} {o o' : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy}
    (h : IsContOrOn L U o) (h' : IsContOrOn L U' o') {x : PX.SmoothLevel}
    (hx : PX.smoothVal x ∈ U) (hx' : PX.smoothVal x ∈ U') :
    orAgreeSign o o' =ᶠ[𝓝 x] fun _ => orAgreeSign o o' x := by
  filter_upwards [h.eventually_iff h' hx hx'] with y hy
  unfold orAgreeSign
  by_cases c : o (PX.smoothVal x) (PX.smoothVal_mem x) = o' (PX.smoothVal x) (PX.smoothVal_mem x)
  · rw [if_pos c, if_pos (hy.2.2.2 c)]
  · rw [if_neg c, if_neg fun e => c (hy.2.2.1 e)]

/-- The index set of `det_f`: continuous orientations `(U, o)`. -/
def DetIndex : Type _ :=
  {i : Set X × (∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy) // IsContOrOn L i.1 i.2}

/-- **`det_f` (the remarks after Theorem 6.6.17)**: the real line bundle over `X_∞` with
trivializations over the continuous orientations `(U, o)` and coordinate changes `±1` according
as two continuous orientations agree; its fibre over `x` is `ℝ ⊗_{ℤ₂} Or_x^f` (`detMk_eq_iff`). -/
def detCore (h2 : IsTwoPointed f hf) : VectorBundleCore ℝ PX.SmoothLevel ℝ (DetIndex L) where
  baseSet i := PX.smoothVal ⁻¹' i.1.1
  isOpen_baseSet i := i.2.1.preimage PX.continuous_smoothVal
  indexAt x :=
    let h := exists_isContOrOn L ⟨x, (h2 (PX.smoothVal x) (PX.smoothVal_mem x)).choose⟩
    ⟨(h.choose, h.choose_spec.choose), h.choose_spec.choose_spec.1⟩
  mem_baseSet_at x :=
    (exists_isContOrOn L ⟨x, (h2 (PX.smoothVal x) (PX.smoothVal_mem x)).choose⟩
      ).choose_spec.choose_spec.2.2.1
  coordChange i j x := orAgreeSign i.1.2 j.1.2 x • ContinuousLinearMap.id ℝ ℝ
  coordChange_self i x _ v := by simp [orAgreeSign_self]
  continuousOn_coordChange i j x hx := by
    have he : (fun y => orAgreeSign i.1.2 j.1.2 y • ContinuousLinearMap.id ℝ ℝ) =ᶠ[𝓝 x]
        fun _ => orAgreeSign i.1.2 j.1.2 x • ContinuousLinearMap.id ℝ ℝ :=
      (orAgreeSign_eventuallyEq L i.2 j.2 hx.1 hx.2).mono fun y hy =>
        congrArg (fun c : ℝ => c • ContinuousLinearMap.id ℝ ℝ) hy
    exact (continuousAt_const.congr he.symm).continuousWithinAt
  coordChange_comp i j k x _ v := by
    change orAgreeSign j.1.2 k.1.2 x • (orAgreeSign i.1.2 j.1.2 x • v) =
      orAgreeSign i.1.2 k.1.2 x • v
    rw [smul_smul, orAgreeSign_mul h2]

open Classical in
/-- **The class of `r ⊗ a` in `det_f`** over `x`, for `r ∈ ℝ`, `a ∈ Or_x^f`: in the standard
trivialization at `x`, `r` if `a` is the orientation of that trivialization and `−r` if not. -/
def detMk (h2 : IsTwoPointed f hf) (x : PX.SmoothLevel) (r : ℝ)
    (a : Orx f hf (PX.smoothVal x) (PX.smoothVal_mem x)) : (detCore L h2).Fiber x :=
  (if a = ((detCore L h2).indexAt x).1.2 (PX.smoothVal x) (PX.smoothVal_mem x) then r else -r : ℝ)

open Classical in
/-- **`detMk` does not depend on the trivialization**: in the trivialization of any continuous
orientation `(U, o)` with `x ∈ U`, `r ⊗ a` has coordinate `r` if `a = o_x` and `−r` if not. -/
theorem localTriv_detMk (h2 : IsTwoPointed f hf) (i : DetIndex L) {x : PX.SmoothLevel}
    (r : ℝ) (a : Orx f hf (PX.smoothVal x) (PX.smoothVal_mem x)) :
    ((detCore L h2).localTriv i ⟨x, detMk L h2 x r a⟩).2 =
      if a = i.1.2 (PX.smoothVal x) (PX.smoothVal_mem x) then r else -r := by
  rw [VectorBundleCore.localTriv_apply]
  change orAgreeSign _ _ x * (if a = _ then r else -r) = _
  unfold orAgreeSign
  set o₀ := ((detCore L h2).indexAt x).1.2 (PX.smoothVal x) (PX.smoothVal_mem x)
  set oi := i.1.2 (PX.smoothVal x) (PX.smoothVal_mem x)
  by_cases h0 : a = o₀ <;> by_cases hi : o₀ = oi
  · rw [if_pos hi, if_pos h0, if_pos (h0.trans hi)]; ring
  · rw [if_neg hi, if_pos h0, if_neg fun e => hi (h0.symm.trans e)]; ring
  · rw [if_pos hi, if_neg h0, if_neg fun e => h0 (e.trans hi.symm)]; ring
  · rw [if_neg hi, if_neg h0, if_pos (eq_of_ne_of_ne_orx h2 h0 fun e => hi e.symm)]; ring

open Classical in
/-- **The fibre of `det_f` over `x` is `ℝ ⊗_{ℤ₂} Or_x^f`**: `r ⊗ a = r' ⊗ a'` iff
`(r', a') = (r, a)` or `(r', a') = (−r, −a)`. -/
theorem detMk_eq_iff (h2 : IsTwoPointed f hf) (x : PX.SmoothLevel) (r r' : ℝ)
    (a a' : Orx f hf (PX.smoothVal x) (PX.smoothVal_mem x)) :
    detMk L h2 x r a = detMk L h2 x r' a' ↔ (r' = r ∧ a' = a) ∨ (r' = -r ∧ a' = orOther a) := by
  rw [eq_orOther_iff h2]
  unfold detMk
  set o₀ := ((detCore L h2).indexAt x).1.2 (PX.smoothVal x) (PX.smoothVal_mem x)
  change (if a = o₀ then r else -r) = (if a' = o₀ then r' else -r') ↔ _
  by_cases h : a = o₀ <;> by_cases h' : a' = o₀
  · rw [if_pos h, if_pos h']
    have : a' = a := h'.trans h.symm
    simp only [this, ne_eq, not_true_eq_false, and_true, and_false, or_false]
    constructor <;> intro e <;> linarith
  · rw [if_pos h, if_neg h']
    have : a' ≠ a := fun e => h' (e.trans h)
    simp only [this, ne_eq, not_false_eq_true, and_true, and_false, false_or]
    constructor <;> intro e <;> linarith
  · rw [if_neg h, if_pos h']
    have : a' ≠ a := fun e => h (e.symm.trans h')
    simp only [this, ne_eq, not_false_eq_true, and_true, and_false, false_or]
    constructor <;> intro e <;> linarith
  · rw [if_neg h, if_neg h']
    have : a' = a := eq_of_ne_of_ne_orx h2 h' h
    simp only [this, ne_eq, not_true_eq_false, and_true, and_false, or_false]
    constructor <;> intro e <;> linarith

/-- `(−r) ⊗ (−a) = r ⊗ a`. -/
theorem detMk_neg (h2 : IsTwoPointed f hf) (x : PX.SmoothLevel) (r : ℝ)
    (a : Orx f hf (PX.smoothVal x) (PX.smoothVal_mem x)) :
    detMk L h2 x (-r) (orOther a) = detMk L h2 x r a :=
  ((detMk_eq_iff L h2 x r (-r) a (orOther a)).2 (Or.inr ⟨rfl, rfl⟩)).symm

/-- Every element of the fibre of `det_f` over `x` is some `r ⊗ a`. -/
theorem detMk_surjective (h2 : IsTwoPointed f hf) (x : PX.SmoothLevel)
    (v : (detCore L h2).Fiber x) : ∃ r a, detMk L h2 x r a = v :=
  ⟨v, _, if_pos rfl⟩

end Generic

/-! ### The orientation bundle of `f` -/

section Bundle

variable (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) (hf : B.IsScFredholmSectionTame f)
  (hsec : B.HasScPlusSectionsThrough)

include hsec in
/-- With sc⁺-sections through every point, every `Or_x^f` has two elements (`exists_two_orx`). -/
theorem isTwoPointed_of_hasScPlusSectionsThrough :
    IsTwoPointed f hf.toIsScFredholmSection :=
  fun _ hs => exists_two_orx hf.toIsScFredholmSection hs hsec

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]

include hX hbump hsec

/-- **An orientation of `f` is a continuous section of `π_f`** (the remarks after Theorem
6.6.17): `y ↦ o_y` is an orientation of `f` (Definition 6.6.16) iff `y ↦ (y, o_y)` is continuous
for the topology of `O_f` of Theorem 6.6.17. -/
theorem isSectionOrientation_iff_continuous
    (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy) :
    IsSectionOrientation f hf.toIsScFredholmSection o ↔
      @Continuous _ _ _ (orTopology (orLocalTransport hX hbump hf hsec)) (orSec o) := by
  rw [continuous_orSec_iff _ (isTwoPointed_of_hasScPlusSectionsThrough hf hsec),
    isSectionOrientation_iff hX hbump hf hsec]
  constructor
  · intro h
    refine ⟨isOpen_univ, fun γ hγ _ x₀ x₁ h₀ h₁ hs₀ hs₁ => ?_⟩
    have := h ⟨x₀, hs₀⟩ ⟨x₁, hs₁⟩ (PathCat.homMk ⟨γ, hγ, h₀, h₁⟩)
    rwa [orFunctorMap_mk] at this
  · intro h x y a
    obtain ⟨φ, rfl⟩ := PathCat.exists_eq_mk a
    rw [orFunctorMap_mk]
    exact h.2 φ.toFun φ.isScSmoothMap (fun _ _ => mem_univ _) φ.source φ.target _ _

/-- **`f` is orientable iff `π_f` has a global continuous section** (the remarks after Theorem
6.6.17): `f` is orientable (Definition 6.6.14) iff there is a continuous `σ : X_∞ → O_f` with
`π_f ∘ σ = id`. -/
theorem isOrientableSection_iff_exists_continuous_section :
    IsOrientableSection hX hbump hf hsec ↔
      ∃ σ : PX.SmoothLevel → OrSpace f hf.toIsScFredholmSection,
        @Continuous _ _ _ (orTopology (orLocalTransport hX hbump hf hsec)) σ ∧
          ∀ y, orProj f hf.toIsScFredholmSection (σ y) = y := by
  rw [← exists_isSectionOrientation_iff hX hbump hf hsec]
  constructor
  · rintro ⟨o, ho⟩
    exact ⟨orSec o, (isSectionOrientation_iff_continuous hX hbump hf hsec o).1 ho, fun _ => rfl⟩
  · rintro ⟨σ, hσ, hσp⟩
    obtain ⟨o, rfl⟩ := exists_eq_orSec σ hσp
    exact ⟨o, (isSectionOrientation_iff_continuous hX hbump hf hsec o).2 hσ⟩

omit hX hbump in
/-- **`det_f` (the remarks after Theorem 6.6.17)**: the determinant line bundle of `f` over `X_∞`,
`ℝ ⊗_{ℤ₂} O_f`, as a Mathlib vector bundle core (`detCore`) for the transport of `Γ_f`. -/
abbrev detBundleCore :
    VectorBundleCore ℝ PX.SmoothLevel ℝ (DetIndex (orLocalTransport hX hbump hf hsec)) :=
  detCore _ (isTwoPointed_of_hasScPlusSectionsThrough hf hsec)

end Bundle

end Polyfold
