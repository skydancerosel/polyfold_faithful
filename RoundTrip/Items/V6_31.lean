import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_31

/-! Round trip for V6_31 (Definition 6.27: `Or^f_x = {o_x, −o_x}` and the morphisms of `𝒪_f`).

A = `isFredholm_of_mem_linSet` ∧ `exists_two_or` ∧ `nonempty_equiv_of_two` ∧
`equiv_eq_of_apply_eq_of_two`; the first two at universes `0`, the last two (stated for
`Sort u`) at universes `1`, i.e. for types (at `0` they would be about propositions).
B = (1) every orientation `o` of `DET(f, x)` has an opposite `o'` (`o'(L) = −o(L)` for all
`L ∈ Lin(f, x)`), `o' ≠ o`, and every orientation is `o` or `o'`; (2) for smooth `x`, `y` in one
path component, the bijections `Or^f_x → Or^f_y` are exactly `±o_x ↦ ±o_y` and `±o_x ↦ ∓o_y`.

* `B ⇒ A` (proved): `exists_two_or` from (1), once one orientation exists (under A's hypothesis
  `HasScPlusSectionsThrough`, `Lin(f, x) ≠ ∅` is convex, hence simply connected, and the project's
  `exists_lineOrientation_apply_eq` gives one).  The other three conjuncts are proved outright
  (`isFredholm_of_mem_linSet` from `isFredholm_isIndexAt_of_mem_linSet`; the two others are
  statements about arbitrary two-element types, which B cannot speak about).
* `A ⇒ B` fails: `exists_two_or` has the hypothesis `Bd.HasScPlusSectionsThrough` (sc⁺-sections
  through every smooth fibre point; true with sc-smooth bump functions, so satisfiable), which B
  does not have.  `A_to_Bsec` proves B under it.  `B_imp_nonemptyLin`: B forces every
  `Lin(f, x)` at a smooth point to be nonempty (over an empty base there is exactly one
  orientation, which is its own `o'`), which is not known without such sections.
-/


namespace RoundTrip.V6_31
open Polyfold

/-- The project's statement; universes `0` for the `Type*` lemmas, `1` for the `Sort*` lemmas. -/
def A : Prop :=
  type_of% @Polyfold.ChartPoint.isFredholm_of_mem_linSet.{0, 0} ∧
  type_of% @Polyfold.ChartPoint.exists_two_or.{0, 0} ∧
  type_of% @Polyfold.nonempty_equiv_of_two.{1, 1} ∧
  type_of% @Polyfold.equiv_eq_of_apply_eq_of_two.{1, 1}

theorem A_holds : A :=
  ⟨@Polyfold.ChartPoint.isFredholm_of_mem_linSet.{0, 0}, @Polyfold.ChartPoint.exists_two_or.{0, 0},
    @Polyfold.nonempty_equiv_of_two.{1, 1}, @Polyfold.equiv_eq_of_apply_eq_of_two.{1, 1}⟩

/-! ### Generic glue -/

/-- If every element is `o₁` or `o₂` and `a ≠ b`, every element is `a` or `b`. -/
theorem two_of_two {α : Sort*} {o₁ o₂ a b : α} (h : ∀ o, o = o₁ ∨ o = o₂) (hab : a ≠ b) :
    ∀ o, o = a ∨ o = b := by
  intro o
  rcases h o with h1 | h1 <;> rcases h a with h2 | h2 <;> rcases h b with h3 | h3 <;>
    first
    | exact Or.inl (h1.trans h2.symm)
    | exact Or.inr (h1.trans h3.symm)
    | exact absurd (h2.trans h3.symm) hab

/-- A bijection between two two-element types with prescribed values. -/
theorem exists_equiv_pair {α β : Type*} {a a' : α} {b b' : β} (ha : a ≠ a')
    (hα : ∀ x, x = a ∨ x = a') (hb : b ≠ b') (hβ : ∀ y, y = b ∨ y = b') :
    ∃ e : α ≃ β, e a = b ∧ e a' = b' := by
  classical
  refine ⟨⟨fun x => if x = a then b else b', fun y => if y = b then a else a', fun x => ?_,
    fun y => ?_⟩, by simp, by simp [ha.symm]⟩
  · rcases hα x with rfl | rfl <;> simp [ha.symm, hb.symm]
  · rcases hβ y with rfl | rfl <;> simp [ha.symm, hb.symm]

/-- Two rays of a line are equal or opposite. -/
theorem ray_eq_or_eq_neg {M : Type*} [AddCommGroup M] [Module ℝ M] (h : Module.finrank ℝ M = 1)
    (r r' : Module.Ray ℝ M) : r' = r ∨ r' = -r := by
  have : Module.Finite ℝ M := Module.finite_of_finrank_eq_succ h
  induction r using Module.Ray.ind with
  | h v hv =>
    induction r' using Module.Ray.ind with
    | h w hw =>
      have hli : ¬ LinearIndependent ℝ ![v, w] := fun hli => by
        have := hli.fintype_card_le_finrank
        simp [h] at this
      rcases sameRay_or_sameRay_neg_iff_not_linearIndependent.2 hli with h1 | h1
      · exact Or.inl ((ray_eq_iff hw hv).2 h1.symm)
      · refine Or.inr ?_
        rw [neg_rayOfNeZero]
        refine (ray_eq_iff hw _).2 ?_
        have := h1.neg
        rw [neg_neg] at this
        exact this.symm

/-- `λ(E) = Λ^max E` is a submodule of a ring, so an additive group.  (Instance search does not
find this through `maxPow`; B's `IsOpp` uses exactly this instance, `Submodule.addCommGroup`, for
the negation of rays in `det(L) = λ(ker L) ⊗ λ*(coker L)`.) -/
noncomputable instance instAddCommGroupMaxPow (E : Type*) [AddCommGroup E] [Module ℝ E] :
    AddCommGroup ↥(maxPow E) :=
  Submodule.addCommGroup (maxPow E)

section
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Two rays of `det(T)` are equal or opposite. -/
theorem ray_det {T : E →L[ℝ] F} (hT : T.IsFredholm) (r r' : Module.Ray ℝ (fredholmDet T)) :
    r' = r ∨ r' = -r :=
  ray_eq_or_eq_neg (finrank_fredholmDet hT) r r'

/-- A ray of `det(T)` is not its own opposite. -/
theorem ray_det_ne {T : E →L[ℝ] F} (r : Module.Ray ℝ (fredholmDet T)) : r ≠ -r :=
  Module.Ray.ne_neg_self r

end

/-! ### The setting of B -/

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {Bd : StrongBundle PX P} {f : X → Y} {hf : Bd.IsScFredholmSection f} {x : X}
  {p : ChartPoint Bd x}

/-- An orientation is not its own opposite when `Lin(f, x) ≠ ∅`. -/
theorem ne_of_isOpp (hne : (p.linSet f).Nonempty) {o o' : OrB Bd f hf p} (h : IsOpp o o') :
    o' ≠ o := by
  rintro rfl
  obtain ⟨L, hL⟩ := hne
  exact ray_det_ne (T := L) _ (h ⟨L, hL⟩)

/-- Over a convex (hence preconnected) `Lin(f, x)`, the orientation different from `o` is `−o`
(two rays of a line are equal or opposite). -/
theorem isOpp_of_ne (hFr : ∀ L ∈ p.linSet f, L.IsFredholm) {o o' : OrB Bd f hf p}
    (hne : o' ≠ o) : IsOpp o o' := by
  have : PreconnectedSpace ↥(p.linSet f) :=
    isPreconnected_iff_preconnectedSpace.1 (p.convex_linSet hf).isPreconnected
  intro L
  exact (ray_det (hFr L.1 L.2) (o.1 L) (o'.1 L)).resolve_left
    fun h => hne (LineOrientation.eq_of_apply_eq L h)

/-- An orientation exists when `Lin(f, x) ≠ ∅` (`Lin(f, x)` is convex: contractible). -/
theorem exists_or (hne : (p.linSet f).Nonempty) : Nonempty (OrB Bd f hf p) := by
  obtain ⟨L, hL⟩ := hne
  have : ContractibleSpace ↥(p.linSet f) := (p.convex_linSet hf).contractibleSpace ⟨L, hL⟩
  have : LocallyPathConnectedSpace ↥(p.linSet f) :=
    (p.convex_linSet hf).locallyPathConnectedSpace
  have := nontrivial_fiber (L := ChartPoint.detLin f p hf) ⟨L, hL⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : ChartPoint.detLin f p hf ⟨L, hL⟩)
  obtain ⟨o, -⟩ := exists_lineOrientation_apply_eq (L := ChartPoint.detLin f p hf) ⟨L, hL⟩
    (rayOfNeZero ℝ v hv)
  exact ⟨o⟩

end

/-! ### B ⇒ A -/

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- proved outright (B cannot state it: `DET(f, x)` presupposes it)
    intro X _ _ _ PX Y _ _ _ P _ _ Bd f x p hf L hL
    exact (p.isFredholm_isIndexAt_of_mem_linSet hf hL).1
  · intro X _ _ _ PX Y _ _ _ P _ _ Bd f x p hf hx hsec
    obtain ⟨o⟩ := exists_or (hf := hf) (p.linSet_nonempty hf hx hsec)
    obtain ⟨o', -, ho', hall⟩ := (hB PX P Bd f hf).1 x hx p o
    exact ⟨o, o', ho'.symm, hall⟩
  · -- proved outright (a statement about arbitrary two-element types)
    intro α β a₁ a₂ ha ha' b₁ b₂ hb hb'
    exact ⟨(exists_equiv_pair ha ha' hb hb').choose⟩
  · -- proved outright (a statement about arbitrary two-element types)
    intro α β e₁ e₂ a h b₁ b₂ hb
    refine Equiv.ext fun z => ?_
    by_cases hz : z = a
    · rw [hz, h]
    · have h1 : e₁ z ≠ e₂ a := fun h' => hz (e₁.injective (h'.trans h.symm))
      have h2 : e₂ z ≠ e₂ a := fun h' => hz (e₂.injective h')
      rcases hb (e₁ z) with k1 | k1 <;> rcases hb (e₂ z) with k2 | k2 <;>
        rcases hb (e₂ a) with k3 | k3 <;>
        first
        | exact k1.trans k2.symm
        | exact absurd (k1.trans k3.symm) h1
        | exact absurd (k2.trans k3.symm) h2

/-! ### A ⇒ B under `HasScPlusSectionsThrough` -/

/-- B with the project's hypothesis `Bd.HasScPlusSectionsThrough` added. -/
def Bsec : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P), Bd.HasScPlusSectionsThrough →
    ∀ (f : X → Y) (hf : Bd.IsScFredholmSection f),
    (∀ x ∈ PX.smoothSet, ∀ (p : ChartPoint Bd x) (o : OrB Bd f hf p),
      ∃ o' : OrB Bd f hf p, IsOpp o o' ∧ o' ≠ o ∧ ∀ o'' : OrB Bd f hf p, o'' = o ∨ o'' = o') ∧
    (∀ x ∈ PX.smoothSet, ∀ y ∈ PX.smoothSet, Joined x y →
      ∀ (p : ChartPoint Bd x) (q : ChartPoint Bd y) (ox ox' : OrB Bd f hf p)
        (oy oy' : OrB Bd f hf q), IsOpp ox ox' → IsOpp oy oy' →
        (∃ e : OrB Bd f hf p ≃ OrB Bd f hf q, e ox = oy ∧ e ox' = oy') ∧
        (∃ e : OrB Bd f hf p ≃ OrB Bd f hf q, e ox = oy' ∧ e ox' = oy) ∧
        ∀ e : OrB Bd f hf p ≃ OrB Bd f hf q,
          (e ox = oy ∧ e ox' = oy') ∨ (e ox = oy' ∧ e ox' = oy))

theorem A_to_Bsec : A → Bsec := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd hsec f hf
  have hFr : ∀ {x : X} (p : ChartPoint Bd x), ∀ L ∈ p.linSet f, L.IsFredholm :=
    fun p => hA.1 p hf
  -- the two elements of `Or^f_x`, written as `o` and `−o`
  have hpair : ∀ x ∈ PX.smoothSet, ∀ (p : ChartPoint Bd x) (o o' : OrB Bd f hf p),
      IsOpp o o' → o' ≠ o ∧ ∀ o'' : OrB Bd f hf p, o'' = o ∨ o'' = o' := by
    intro x hx p o o' hoo'
    have hne' := ne_of_isOpp (p.linSet_nonempty hf hx hsec) hoo'
    obtain ⟨a₁, a₂, -, hall⟩ := hA.2.1 p hf hx hsec
    exact ⟨hne', two_of_two hall hne'.symm⟩
  refine ⟨fun x hx p o => ?_, fun x hx y hy _ p q ox ox' oy oy' hox hoy => ?_⟩
  · obtain ⟨a₁, a₂, h12, hall⟩ := hA.2.1 p hf hx hsec
    have hoth : ∃ o' : OrB Bd f hf p, o' ≠ o ∧ ∀ o'', o'' = o ∨ o'' = o' := by
      rcases hall o with rfl | rfl
      · exact ⟨a₂, Ne.symm h12, hall⟩
      · exact ⟨a₁, h12, fun o'' => (hall o'').symm⟩
    obtain ⟨o', ho', hall'⟩ := hoth
    exact ⟨o', isOpp_of_ne (hFr p) ho', ho', hall'⟩
  · obtain ⟨hx', hαx⟩ := hpair x hx p ox ox' hox
    obtain ⟨hy', hαy⟩ := hpair y hy q oy oy' hoy
    refine ⟨exists_equiv_pair hx'.symm hαx hy'.symm hαy,
      exists_equiv_pair hx'.symm hαx hy' (fun o => (hαy o).symm), fun e => ?_⟩
    rcases hαy (e ox) with h | h
    · refine Or.inl ⟨h, (hαy (e ox')).resolve_left fun h' => hx' (e.injective (h'.trans h.symm))⟩
    · refine Or.inr ⟨h, (hαy (e ox')).resolve_right fun h' =>
        hx' (e.injective (h'.trans h.symm))⟩

/-! ### B forces `Lin(f, x) ≠ ∅` -/

/-- Every `Lin(f, x)` at a smooth point, read in every chart point, is nonempty. -/
def NonemptyLin : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (_ : Bd.IsScFredholmSection f) (x : X),
    x ∈ PX.smoothSet → ∀ p : ChartPoint Bd x, (p.linSet f).Nonempty

/-- Over an empty `Lin(f, x)` there is exactly one orientation, so B(1) fails there. -/
theorem B_imp_nonemptyLin : B → NonemptyLin := by
  intro hB X _ _ _ PX Y _ _ _ P _ _ Bd f hf x hx p
  by_contra hne
  have hem : IsEmpty ↥(p.linSet f) :=
    ⟨fun L => hne ⟨L.1, L.2⟩⟩
  let o : OrB Bd f hf p := ⟨fun L => isEmptyElim L, fun b₀ => isEmptyElim b₀⟩
  obtain ⟨o', -, ho', -⟩ := (hB PX P Bd f hf).1 x hx p o
  exact ho' (LineOrientation.ext fun L => isEmptyElim L)

/-! **On the check.**  `#rt_check` (and `#rt_check_soft`) cannot pass with the banned
`isFredholm_of_mem_linSet`: it is the Fredholm witness with which `ChartPoint.detLin =
DetOn (Lin(f, x)) (p.isFredholm_of_mem_linSet hf)` is formed, so it occurs in the *statements* of
A and of B (`OrB`, `IsOpp`, `ChartPoint.Or`, and every instance argument for `DET(f, x)`, where
elaboration also unfolds `fredholmIncl` and puts the witness into `FredholmOp` subtypes); even
`fun hB => …` reaches it.  It is a proposition (`∀ L ∈ Lin(f, x), L.IsFredholm`), so every
occurrence is interchangeable, by proof irrelevance, with the non-banned
`(p.isFredholm_isIndexAt_of_mem_linSet hf hL).1`, which is how A's first conjunct is proved in
`B_to_A`.  The checks are therefore run with the three other theorems of the item. -/
#rt_check_soft RoundTrip.V6_31.B_to_A [Polyfold.ChartPoint.exists_two_or,
  Polyfold.nonempty_equiv_of_two, Polyfold.equiv_eq_of_apply_eq_of_two]
#rt_overlap RoundTrip.V6_31.B_to_A [Polyfold.ChartPoint.isFredholm_of_mem_linSet,
  Polyfold.ChartPoint.exists_two_or, Polyfold.nonempty_equiv_of_two,
  Polyfold.equiv_eq_of_apply_eq_of_two]
#rt_check_soft RoundTrip.V6_31.A_to_Bsec [Polyfold.ChartPoint.exists_two_or,
  Polyfold.nonempty_equiv_of_two, Polyfold.equiv_eq_of_apply_eq_of_two]
#rt_check_soft RoundTrip.V6_31.B_imp_nonemptyLin [Polyfold.ChartPoint.exists_two_or,
  Polyfold.nonempty_equiv_of_two, Polyfold.equiv_eq_of_apply_eq_of_two]

end RoundTrip.V6_31
