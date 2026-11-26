import Polyfold.Chapter18.MultisectionConstructions

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, §18.4: **the
functor `Λ` of the construction of p. 854**, defined in one strong bundle uniformizer, and its
elementary properties.  Proposition 18.4.3 (2021 p. 855) for this `Λ` is
`MultisectionConstructionText.lean`.

## The text, paraphrased

For a strong bundle uniformizer `Ψ̄ : G ⋉ K → E` over `Ψ : G ⋉ O → C` and an sc⁺-section `s₁` of
`p : K → O`, the translates are `s_g(g ∗ q) = g ∗ s₁(q)`, and
`Λ(Ψ̄(h)) = |G|⁻¹·#{g ∈ G | s_g(p(h)) = h}`.  For `(β, e)` with a morphism `φ : β → Ψ(q)`,
`Λ(β, e) = Λ(Ψ̄(h₀))` where `Ψ̄(h₀) = (Ψ(q), φ̂(e))`; this does not depend on `φ`.  Otherwise
`Λ(β, e) = 1` for `e = 0` and `0` for `e ≠ 0`.

## What is formalized (namespace `Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction`)

* `textTranslate` (`s_g(q) = g ∗ s₁(g⁻¹ ∗ q)`), `textLamK` (`|G|⁻¹·#{g | s_g(p(h)) = h}`),
  `TextReach`, `textLift`, `textValue`, **`textLam`** (the functor `Λ : E → ℚ⁺`).
* **`textValue_indep`**: the value attached to `(q, φ)` does not depend on the choice.
* `textLam_obj` (`Λ(Ψ̄(h)) = |G|⁻¹·#{g | s_g(p(h)) = h}`), `isMorInvariant_textLam` (`Λ` is a
  functor), `textLam_pos` (`Λ(Ψ̄(s₁(q))) > 0`).
* Zero vectors and translates: `obj_fiberZero`, `smul_fiberZero`, `textTranslate_of_notMem`,
  `textLamK_of_notMem` (`Λ = 1_{h = 0}` where all translates vanish),
  `isScPlusSection_textTranslate`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace GCT.VectorBundle.StrongPolyfoldBundleConstruction

open GroupoidalCategory GroupoidalCategory.BanachFunctor SBLocalization StrongBundle
  StrongBundleUniformizerConstruction StrongBundleUniformizerData PolyfoldConstruction

variable {C : GCT.{u}} {V : C.VectorBundle}

/-! ### The construction of p. 854 -/

section Construction

variable (Ψb : V.StrongBundleUniformizer) (s₁ : Ψb.base.O → Ψb.K)

/-- **The translates** `s_g(g ∗ q) = g ∗ s₁(q)`, i.e. `s_g(q) = g ∗ s₁(g⁻¹ ∗ q)` (p. 854). -/
def textTranslate (g : Ψb.base.G) (q : Ψb.base.O) : Ψb.K := g • s₁ (g⁻¹ • q)

/-- **`Λ(Ψ̄(h)) = |G|⁻¹·#{g ∈ G | s_g(p(h)) = h}`** (p. 854), as a function of `h ∈ K`. -/
def textLamK (h : Ψb.K) : ℚ≥0 :=
  (Nat.card Ψb.base.G : ℚ≥0)⁻¹ * (Nat.card {g : Ψb.base.G // textTranslate Ψb s₁ g (Ψb.p h) = h})

/-- `(q, φ)` with `φ : P(e) → Ψ(q)`: a morphism from the base of `e` into `Ψ(O)`. -/
def TextReach (e : V.EObj) (r : Ψb.base.O × C.Mor) : Prop :=
  C.toGroupoidStr.src r.2 = V.base e ∧ C.toGroupoidStr.tgt r.2 = Ψb.base.obj r.1

/-- `h₀ ∈ K` with `Ψ̄(h₀) = (t(φ), φ̂(e))` (p. 854). -/
def textLift (e : V.EObj) (r : Ψb.base.O × C.Mor) (hr : TextReach Ψb e r) : Ψb.K :=
  Ψb.lift r.1 (V.act r.2 e hr.1.symm) hr.2

/-- The value `Λ(Ψ̄(h₀))` attached to a choice of `(q, φ)`. -/
def textValue (e : V.EObj) (r : Ψb.base.O × C.Mor) (hr : TextReach Ψb e r) : ℚ≥0 :=
  textLamK Ψb s₁ (textLift Ψb e r hr)

open Classical in
/-- **The functor `Λ : E → ℚ⁺` of p. 854**: `Λ(β, e) = Λ(Ψ̄(h₀))` with `Ψ̄(h₀) = (t(φ), φ̂(e))`
for a morphism `φ : β → t(φ) ∈ Ψ(O)`, and `Λ(β, e) = 1` for `e = 0`, `0` otherwise, when there is
no such morphism. -/
def textLam (e : V.EObj) : ℚ≥0 :=
  if h : ∃ r, TextReach Ψb e r then textValue Ψb s₁ e h.choose h.choose_spec
  else if e.2 = 0 then 1 else 0

variable {Ψb s₁}

theorem p_textLift (e : V.EObj) (r : Ψb.base.O × C.Mor) (hr : TextReach Ψb e r) :
    Ψb.p (textLift Ψb e r hr) = r.1 := Ψb.p_lift _ _ _

theorem obj_textLift (e : V.EObj) (r : Ψb.base.O × C.Mor) (hr : TextReach Ψb e r) :
    Ψb.obj (textLift Ψb e r hr) = V.act r.2 e hr.1.symm := Ψb.obj_lift _ _ _

/-- `s_g(g' ∗ q) = g' ∗ s_{g'⁻¹ g}(q)`. -/
theorem textTranslate_smul (g g' : Ψb.base.G) (q : Ψb.base.O) :
    textTranslate Ψb s₁ g (g' • q) = g' • textTranslate Ψb s₁ (g'⁻¹ * g) q := by
  unfold textTranslate
  rw [← mul_smul g' (g'⁻¹ * g), ← mul_assoc, mul_inv_cancel, one_mul, mul_inv_rev, inv_inv,
    mul_smul]

/-- `s_1 = s₁`. -/
theorem textTranslate_one (q : Ψb.base.O) : textTranslate Ψb s₁ 1 q = s₁ q := by
  unfold textTranslate; rw [inv_one, one_smul, one_smul]

/-- **`Λ(Ψ̄(g' ∗ h)) = Λ(Ψ̄(h))`**: `g ↦ g'⁻¹ g` matches the two counts. -/
theorem textLamK_smul (g' : Ψb.base.G) (h : Ψb.K) :
    textLamK Ψb s₁ (g' • h) = textLamK Ψb s₁ h := by
  unfold textLamK
  congr 2
  refine Nat.card_congr ((Equiv.mulLeft g'⁻¹).subtypeEquiv fun g => ?_)
  rw [Ψb.p_smul, textTranslate_smul]
  exact smul_left_cancel_iff g'

/-- **The value does not depend on the choice of `(q, φ)`** (p. 854): two choices differ by a
morphism `Ψ(q) → Ψ(q')`, which is `Ψ(g, q)` (fullness), and `h₀' = g ∗ h₀`. -/
theorem textValue_indep (e : V.EObj) (r r' : Ψb.base.O × C.Mor) (hr : TextReach Ψb e r)
    (hr' : TextReach Ψb e r') : textValue Ψb s₁ e r hr = textValue Ψb s₁ e r' hr' := by
  set ψ := C.toGroupoidStr.comp r'.2 (C.toGroupoidStr.inv r.2)
  have hc : C.toGroupoidStr.src r'.2 = C.toGroupoidStr.tgt (C.toGroupoidStr.inv r.2) := by
    rw [C.toGroupoidStr.tgt_inv, hr.1, hr'.1]
  have hψs : C.toGroupoidStr.src ψ = Ψb.base.obj r.1 := by
    rw [C.toGroupoidStr.src_comp _ _ hc, C.toGroupoidStr.src_inv, hr.2]
  have hψt : C.toGroupoidStr.tgt ψ = Ψb.base.obj r'.1 := by
    rw [C.toGroupoidStr.tgt_comp _ _ hc, hr'.2]
  obtain ⟨g, -, hg⟩ := Ψb.base.toUniformizer.exists_smul_eq_mor hψs hψt
  have key : textLift Ψb e r' hr' = g • textLift Ψb e r hr := by
    apply Ψb.obj_injective
    refine (obj_textLift e r' hr').trans ?_
    refine Eq.trans ?_ (Ψb.obj_smul' g _)
    have hp := p_textLift e r hr
    have h1 : V.base e = C.toGroupoidStr.src (C.toGroupoidStr.comp ψ r.2) := by
      rw [C.toGroupoidStr.src_comp _ _ (by rw [hψs, hr.2])]; exact hr.1.symm
    have hcomp : C.toGroupoidStr.comp ψ r.2 = r'.2 := by
      change C.toGroupoidStr.comp (C.toGroupoidStr.comp r'.2 (C.toGroupoidStr.inv r.2)) r.2 = _
      rw [GroupoidStr.comp_assoc _ _ _ _ hc (by rw [C.toGroupoidStr.src_inv]),
        C.toGroupoidStr.inv_comp, GroupoidStr.comp_unit_of_eq (hr'.1.trans hr.1.symm)]
    refine (act_congr hcomp.symm rfl _ h1).trans ?_
    refine (act_comp' ψ r.2 (by rw [hψs, hr.2]) e h1).trans ?_
    exact act_congr (by rw [hp, hg]) (obj_textLift e r hr).symm _ _
  unfold textValue
  rw [key, textLamK_smul]

theorem textLam_eq_textValue (e : V.EObj) (r : Ψb.base.O × C.Mor) (hr : TextReach Ψb e r) :
    textLam Ψb s₁ e = textValue Ψb s₁ e r hr := by
  have h : ∃ r, TextReach Ψb e r := ⟨r, hr⟩
  unfold textLam
  rw [dif_pos h]
  exact textValue_indep _ _ _ _ _

open Classical in
theorem textLam_of_not_reach (e : V.EObj) (h : ¬ ∃ r, TextReach Ψb e r) :
    textLam Ψb s₁ e = if e.2 = 0 then 1 else 0 := by
  unfold textLam; rw [dif_neg h]

/-- **`Λ(Ψ̄(h)) = |G|⁻¹·#{g | s_g(p(h)) = h}`** (p. 854). -/
theorem textLam_obj (h : Ψb.K) : textLam Ψb s₁ (Ψb.obj h) = textLamK Ψb s₁ h := by
  have hr : TextReach Ψb (Ψb.obj h) (Ψb.p h, C.toGroupoidStr.unit (Ψb.base.obj (Ψb.p h))) :=
    ⟨C.toGroupoidStr.src_unit _, C.toGroupoidStr.tgt_unit _⟩
  rw [textLam_eq_textValue _ _ hr]
  unfold textValue
  congr 1
  exact (Ψb.lift_eq_iff _ _).2 (act_unit' _ _).symm

theorem textReach_act {e : V.EObj} (a : V.EMor) (ha : a.e = e) {r : Ψb.base.O × C.Mor}
    (hr : TextReach Ψb e r) :
    TextReach Ψb (V.act a.φ a.e a.2) (r.1, C.toGroupoidStr.comp r.2 (C.toGroupoidStr.inv a.φ)) := by
  have hc : C.toGroupoidStr.src r.2 = C.toGroupoidStr.tgt (C.toGroupoidStr.inv a.φ) := by
    rw [C.toGroupoidStr.tgt_inv, hr.1, ← ha]; exact a.2
  exact ⟨by rw [C.toGroupoidStr.src_comp _ _ hc, C.toGroupoidStr.src_inv]; rfl,
    by rw [C.toGroupoidStr.tgt_comp _ _ hc, hr.2]⟩

theorem textReach_of_act {e : V.EObj} (a : V.EMor) (ha : a.e = e) {r : Ψb.base.O × C.Mor}
    (hr : TextReach Ψb (V.act a.φ a.e a.2) r) :
    TextReach Ψb e (r.1, C.toGroupoidStr.comp r.2 a.φ) := by
  have hc : C.toGroupoidStr.src r.2 = C.toGroupoidStr.tgt a.φ := hr.1
  exact ⟨by rw [C.toGroupoidStr.src_comp _ _ hc]; exact a.2.symm.trans (congrArg V.base ha),
    by rw [C.toGroupoidStr.tgt_comp _ _ hc, hr.2]⟩

/-- `μ(φ) e = 0` iff `e = 0`. -/
theorem text_act_eq_objMk_zero_iff (φ : C.Mor) (e : V.EObj)
    (h : V.base e = C.toGroupoidStr.src φ) :
    V.act φ e h = V.objMk (C.toGroupoidStr.tgt φ) 0 ↔ e = V.objMk (V.base e) 0 := by
  have hz : V.act φ (V.objMk (V.base e) 0) h = V.objMk (C.toGroupoidStr.tgt φ) 0 :=
    act_objMk_zero h.symm h
  constructor
  · intro he
    exact act_injective h h (he.trans hz.symm)
  · intro he
    exact (act_congr rfl he h h).trans hz

theorem objMk_zero_iff (e : V.EObj) : e = V.objMk (V.base e) 0 ↔ e.2 = 0 := by
  obtain ⟨α, v⟩ := e
  exact objMk_eq_iff

/-- **`Λ` is a functor `E → ℚ⁺`** (constant along the morphisms of `E`). -/
theorem isMorInvariant_textLam : IsMorInvariant (textLam Ψb s₁) := by
  intro a
  change textLam Ψb s₁ (V.act a.φ a.e a.2) = textLam Ψb s₁ a.e
  by_cases h : ∃ r, TextReach Ψb a.e r
  · obtain ⟨r, hr⟩ := h
    have hr' := textReach_act (Ψb := Ψb) a rfl hr
    rw [textLam_eq_textValue _ _ hr', textLam_eq_textValue _ _ hr]
    unfold textValue textLift
    congr 2
    have hc : C.toGroupoidStr.src r.2 = C.toGroupoidStr.tgt (C.toGroupoidStr.inv a.φ) := by
      rw [C.toGroupoidStr.tgt_inv, hr.1]; exact a.2
    refine (act_comp' _ _ hc _ _).trans (act_congr rfl (act_inv_act _ _ _) _ _)
  · have h' : ¬ ∃ r, TextReach Ψb (V.act a.φ a.e a.2) r := fun ⟨r, hr⟩ =>
      h ⟨_, textReach_of_act (Ψb := Ψb) a rfl hr⟩
    rw [textLam_of_not_reach _ h, textLam_of_not_reach _ h']
    have e1 : (V.act a.φ a.e a.2).2 = 0 ↔ a.e.2 = 0 := by
      rw [← objMk_zero_iff, ← objMk_zero_iff]
      exact text_act_eq_objMk_zero_iff a.φ a.e a.2
    by_cases h0 : a.e.2 = 0
    · rw [if_pos (e1.2 h0), if_pos h0]
    · rw [if_neg (fun h => h0 (e1.1 h)), if_neg h0]

/-- **`Λ(Ψ̄(s₁(q̄))) > 0`**: the index `g = 1` is counted. -/
theorem textLam_pos (hs : ∀ q, Ψb.p (s₁ q) = q) (q : Ψb.base.O) :
    0 < textLam Ψb s₁ (Ψb.obj (s₁ q)) := by
  rw [textLam_obj]
  unfold textLamK
  have : Nonempty {g : Ψb.base.G // textTranslate Ψb s₁ g (Ψb.p (s₁ q)) = s₁ q} :=
    ⟨⟨1, by rw [textTranslate_one, hs]⟩⟩
  have : Finite {g : Ψb.base.G // textTranslate Ψb s₁ g (Ψb.p (s₁ q)) = s₁ q} :=
    Subtype.finite
  exact mul_pos (inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)) (Nat.cast_pos.2 Nat.card_pos)

end Construction

section Zero
variable {Ψb : V.StrongBundleUniformizer} {s₁ : Ψb.base.O → Ψb.K}

theorem obj_fiberZero (q : Ψb.base.O) :
    Ψb.obj (fiberZero Ψb.p q) = V.objMk (Ψb.base.obj q) 0 := by
  rw [Ψb.obj_of_eq (proj_fiberZero Ψb.p q)]
  exact congrArg (V.objMk _) (Ψb.fiber q).map_zero

theorem obj_eq_zero_iff (h : Ψb.K) :
    Ψb.obj h = V.objMk (Ψb.base.obj (Ψb.p h)) 0 ↔ h = fiberZero Ψb.p (Ψb.p h) := by
  constructor
  · intro e
    exact Ψb.obj_injective (e.trans (obj_fiberZero _).symm)
  · intro e
    have := obj_fiberZero (Ψb := Ψb) (Ψb.p h)
    rw [← e] at this
    exact this

theorem smul_fiberZero (g : Ψb.base.G) (q : Ψb.base.O) :
    g • fiberZero Ψb.p q = fiberZero Ψb.p (g • q) := by
  apply Ψb.obj_injective
  have h' : V.base (V.objMk (Ψb.base.obj q) 0) =
      C.toGroupoidStr.src (Ψb.base.mor (g, Ψb.p (fiberZero Ψb.p q))) :=
    ((Ψb.base.functor.src_mor (g, _)).trans
      (congrArg Ψb.base.obj (proj_fiberZero Ψb.p q))).symm
  refine (Ψb.obj_smul' g _).symm.trans ?_
  refine (act_congr rfl (obj_fiberZero q) _ h').trans ?_
  refine (act_objMk_zero h'.symm h').trans ?_
  rw [obj_fiberZero, Ψb.base.functor.tgt_mor]
  change V.objMk (Ψb.base.obj (g • Ψb.p (fiberZero Ψb.p q))) 0 = _
  rw [proj_fiberZero Ψb.p q]

/-- `s_g(q) = 0` if `s₁` vanishes at `g⁻¹ ∗ q`. -/
theorem textTranslate_of_notMem {Vt : Set Ψb.base.O}
    (hvan : ∀ q ∉ Vt, s₁ q = fiberZero Ψb.p q) {g : Ψb.base.G} {q : Ψb.base.O}
    (hq : g⁻¹ • q ∉ Vt) : textTranslate Ψb s₁ g q = fiberZero Ψb.p q := by
  unfold textTranslate
  rw [hvan _ hq, smul_fiberZero, smul_inv_smul]

/-- `s_g` vanishes off `Vt` for `g` in the stabilizer of a set `Vt` off which `s₁` vanishes. -/
theorem textTranslate_of_notMem' {Vt : Set Ψb.base.O}
    (hvan : ∀ q ∉ Vt, s₁ q = fiberZero Ψb.p q) {g : Ψb.base.G} (hg : MapsTo (g • ·) Vt Vt)
    {q : Ψb.base.O} (hq : q ∉ Vt) : textTranslate Ψb s₁ g q = fiberZero Ψb.p q := by
  refine textTranslate_of_notMem hvan fun h => hq ?_
  have := hg h
  simp only [smul_inv_smul] at this
  exact this

open Classical in
theorem textLamK_of_notMem {Vt : Set Ψb.base.O}
    (hvan : ∀ q ∉ Vt, s₁ q = fiberZero Ψb.p q) {h : Ψb.K} (hq : ∀ g : Ψb.base.G, g⁻¹ • Ψb.p h ∉ Vt) :
    textLamK Ψb s₁ h = if h = fiberZero Ψb.p (Ψb.p h) then 1 else 0 := by
  unfold textLamK
  simp_rw [textTranslate_of_notMem hvan (hq _)]
  by_cases h0 : h = fiberZero Ψb.p (Ψb.p h)
  · rw [if_pos h0]
    have : Nat.card {g : Ψb.base.G // fiberZero Ψb.p (Ψb.p h) = h} = Nat.card Ψb.base.G :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => h0.symm)
    rw [this]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  · rw [if_neg h0]
    have : IsEmpty {g : Ψb.base.G // fiberZero Ψb.p (Ψb.p h) = h} :=
      ⟨fun g => h0 g.2.symm⟩
    rw [show Nat.card {g : Ψb.base.G // fiberZero Ψb.p (Ψb.p h) = h} = 0 from
      Nat.card_of_isEmpty]
    simp

/-- `g' ∗ s_g(q) = s_{g' g}(g' ∗ q)`. -/
theorem smul_textTranslate (g' g : Ψb.base.G) (q : Ψb.base.O) :
    g' • textTranslate Ψb s₁ g q = textTranslate Ψb s₁ (g' * g) (g' • q) := by
  rw [textTranslate_smul, inv_mul_cancel_left]

theorem text_act_eq_objMk_zero_iff' (φ : C.Mor) (e : V.EObj)
    (h : V.base e = C.toGroupoidStr.src φ) {α : C.Obj} (hα : C.toGroupoidStr.tgt φ = α) :
    V.act φ e h = V.objMk α 0 ↔ e = V.objMk (V.base e) 0 := by
  subst hα
  exact text_act_eq_objMk_zero_iff φ e h

theorem isScPlusSection_textTranslate (hs : Ψb.B.IsScPlusSection s₁) (g : Ψb.base.G) :
    Ψb.B.IsScPlusSection (textTranslate Ψb s₁ g) := by
  obtain ⟨hsec, G', hGf, hG⟩ := (Ψb.B.isScPlusSection_iff s₁).1 hs
  refine (Ψb.B.isScPlusSection_iff _).2 ⟨fun y => ?_,
    StrongBundle.oneRestrict Ψb.B Ψb.B (fun k : Ψb.K => g • k)
      (Ψb.isStrongBundleMap_smul g).mapsTo_oneSet ∘ G' ∘ fun y => g⁻¹ • y, ?_, ?_⟩
  · change Ψb.p (g • s₁ (g⁻¹ • y)) = y
    rw [Ψb.p_smul, hsec, smul_inv_smul]
  · funext y
    simp only [comp_apply, StrongBundle.oneVal_oneRestrict]
    change g • Ψb.B.oneVal (G' (g⁻¹ • y)) = g • s₁ (g⁻¹ • y)
    rw [← congrFun hGf (g⁻¹ • y)]
    rfl
  · exact (Ψb.isStrongBundleMap_smul g).isScSmoothMap_one.comp
      (hG.comp (Ψb.base.smooth_smul g⁻¹))

end Zero

end GCT.VectorBundle.StrongPolyfoldBundleConstruction

end Polyfold
