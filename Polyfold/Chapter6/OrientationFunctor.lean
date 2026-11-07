import Polyfold.Chapter6.SectionOrientation
import Polyfold.Chapter6.PushTransfer
import Polyfold.Chapter6.PathTransport
import Polyfold.Chapter6.PathCategory

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5,
pp. 227–229: **Theorem 6.37** (the functor `Γ_f`) and **Definitions 6.38–6.40** (orientability
and orientations of sc-Fredholm sections) *(book 2017: Theorem 6.2, Definitions 6.11–6.13; see
`BookConcordance.md`)*.

# The orientation functor `Γ_f`

## The text, paraphrased

(Theorem 6.37) For a strong bundle `P : Y → X` over a tame M-polyfold `X` and an sc-Fredholm
section `f` there is a uniquely determined functor `Γ_f : PX → O_f`, `x ↦ Or_x^f`, taking the
class `[φ] : x → y` to a morphism `Γ_f([φ]) : Or_x^f → Or_y^f`, with the property (∗): for a
smooth point `x`, an sc-smoothly contractible open neighbourhood `U = U(x)` on which `f` has the
local propagation property and an sc-smooth path `φ : [0, 1] → U`, the local propagation
`φ_* : Or_{φ(0)}^f → Or_{φ(1)}^f` and `Γ_f([φ])` coincide.  (Definition 6.38) `f` is orientable if
for every pair of smooth points `x`, `y` in the same path component, `Γ_f([φ])` does not depend on
the homotopy class `[φ] : x → y`.  An equivalent version is Definition 6.39: there is a map
`y ↦ o_y` such that every smooth point has an orientable neighbourhood over which `y ↦ o_y` is
one of the two continuous orientations.  (Definition 6.40) An orientation of `f` is a map
`y ↦ o_y` such that for every smooth point `x` and every orientable neighbourhood `U(x)` the
restriction to `U(x)_∞` is one of the two continuous orientations.

## What is formalized

* `IsPropagationNbhd f hf U`: `U` open with the local propagation property in some chart;
  `orPush`, the push-forward along a path in such a `U`, read in the chosen charts by
  `toChartOr`; `orPush_eq` (it is every push-forward along the path, in every chart `c` in which
  the path lies in a set with the local propagation property: `HasLocalPropagation.push_compat`
  and `toChartOr_trans`), `orPush_trans`, `orPush_compat`.
* `orLocalTransport`: the local transport data of `f` (`LocalTransport`, with the good sets
  `IsPropagationNbhd`, Theorem 6.35), and `orLocalTransport_transport_eq`, property (∗) for the
  transport along a path.
* **Theorem 6.37**: `orFunctorMap a` (the text's `Γ_f([φ])`: the transport along `φ`, well defined
  on classes by its homotopy invariance), `orFunctorMap_mk`, `orFunctorMap_id`,
  `orFunctorMap_comp`, the functor `orFunctor : PathCat PX ⥤ Type`, `x ↦ Or_x^f`;
  `IsStarProperty f hf G` (property (∗) for a family `G` of maps on the morphisms of `PX`, on all
  open sets; `IsStarPropertyOn f hf W G` on the members of a family `W`),
  `orFunctorMap_isStarProperty`, the uniqueness `orFunctorMap_unique` and
  `orFunctorMap_unique_of_cover` ((∗) asked only on a family of open sets with the local
  propagation property covering `X_∞`), and `theorem_6_37`.
* **Definition 6.38**: `IsOrientableSection`.  `isOrientableSection_iff_exists`: `f` is orientable
  iff there is a map `y ↦ o_y` with `Γ_f([φ]) o_x = o_y` for all `[φ] : x → y`
  (`exists_apply_eq_of_isOrientableSection`, `isOrientableSection_of_apply_eq`);
  `isOrientableSection'_iff_exists`: the same for Definition 6.39
  (`orFunctorMap_apply_eq_of_local`, `isContinuousOrientation_of_apply_eq`); **6.38 ⇔ 6.39**:
  `isOrientableSection_iff`.
* **Definition 6.40**: `isSectionOrientation_iff` (an orientation is a map `y ↦ o_y` with
  `Γ_f([φ]) o_x = o_y` for all `[φ]`), `exists_isSectionOrientation_iff` (`f` has an orientation
  iff it is orientable), `IsSectionOrientation.apply_eq_iff` (two orientations which agree at a
  point agree on its path component) and `IsSectionOrientation.exists_two` (on the path component
  of a point there are exactly two orientations).
* The tools: `LocalTransport.restrict`, `LocalTransport.transport_apply_eq_of_local` (elements
  carried into each other by the transport along the paths in the members of an open covering are
  carried into each other along every path); `scPathSetoid` (smooth points joined by an sc-smooth
  path); `exists_two_orx`, `toChartOr_trans`, `forall_mem_of_forall_pt1_mem`; regroupings of
  bijections (`equiv_conj_transfer_aux`, `equiv_conj_trans_aux`, `equiv_conj_apply_eq_iff`) and
  facts on two-element types (`nonempty_equiv_of_two`, `eq_of_ne_of_ne_of_two`,
  `equiv_eq_of_apply_eq_of_two`).

## Reading

`Or_x^f` is read as the orientations in the chosen chart `orChart B x` (`Orx`), and a
push-forward `e` along `φ` in a chart `c` is compared with them by `toChartOr`
(`ChartPoint.orTransfer`); so (∗) reads `Γ_f([φ]) = toChartOr_{φ(1)}⁻¹ ∘ e ∘ toChartOr_{φ(0)}` for
every chart `c`, every open `U` with the local propagation property in `c`, every sc-smooth path
`φ` in `U` with smooth end points and every push-forward `e` along `φ` in `c` (`IsPush`); by
`orFunctorMap_isStarProperty` this property is satisfiable.  The point `x ∈ U` plays no role.  The
sc-smooth contractibility of `U` is not asked: Proposition 6.28 gives (1′) rather than the
contractibility of its neighbourhoods (see `OrientableNbhd.lean`), and `Γ_f` has (∗) on every open
`U` with the local propagation property.  For the uniqueness, (∗) on fewer sets suffices:
`orFunctorMap_unique_of_cover` asks it only on the members of a family of such open sets covering
`X_∞` (for instance the sc-smoothly contractible ones, wherever they cover `X_∞`).  The category
`O_f` is read as the category of types: `orFunctor` takes `x` to `Or_x^f` and `[φ]` to the
bijection `Γ_f([φ])`; "uniquely determined" is read for the maps on morphisms (on objects there is
no choice), and the uniqueness uses only the composition rule and (∗) (the identities and the
homotopy invariance follow).  Theorem 6.37 uses the standing hypotheses of Theorem 6.35
(tameness, bump functions, a tame sc-Fredholm section) and sc⁺-sections through every point
(`HasScPlusSectionsThrough`, so that every `Or_x^f` has two elements).

"For every pair of smooth points `x` and `y` in the same path component" is read as: for any two
morphisms `x → y` of `PX`, i.e. for points joined by an sc-smooth path; for points not so joined
there is nothing to check.  "An equivalent version" is `isOrientableSection_iff`.  From 6.39 to
6.38: the transport along a path carries `o_{φ(0)}` to `o_{φ(1)}` (on a dyadic piece in an
orientable neighbourhood this is (∗) and the continuity, `transport_apply_eq_of_local`), and a
bijection between two-element sets is determined by one value.  From 6.38 to 6.39: a base point
is chosen in each class of smooth points joined by sc-smooth paths (`Quotient.out` for
`scPathSetoid`), an orientation `o_b` there, and `o_y = Γ_f([φ_y]) o_b` for a path `φ_y` from the
base point to `y`.  As in `SectionOrientation.lean`, an orientable neighbourhood is a pair
`V ⊆ U` (`IsOrientableNbhd`).  "Exactly two orientations" on a path component is read as
`IsSectionOrientation.exists_two`: the second one is the first one changed on that component.
-/

open Set CategoryTheory

noncomputable section

namespace Polyfold

universe u v

/-! ### Regrouping bijections -/

section Regroup

/-- **A push-forward conjugated into a second chart**: `(A₀ T₀) (T₁ (T₀⁻¹ e) (A₁ T₁)⁻¹) =
A₀ e A₁⁻¹` (composition read from left to right). -/
theorem equiv_conj_transfer_aux {α β γ δ ε ζ : Sort*} (A₀ : α ≃ β) (A₁ : γ ≃ δ) (T₀ : β ≃ ε)
    (T₁ : δ ≃ ζ) (e : β ≃ δ) :
    (A₀.trans T₀).trans (((T₀.symm.trans e).trans T₁).trans (A₁.trans T₁).symm) =
      A₀.trans (e.trans A₁.symm) := by
  ext a
  simp only [Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_apply_apply]

/-- **Composites of conjugated push-forwards**: `A₀ (e₁ e₂) A₂⁻¹ = (A₀ e₁ A₁⁻¹) (A₁ e₂ A₂⁻¹)`. -/
theorem equiv_conj_trans_aux {α β γ δ ε ζ : Sort*} (A₀ : α ≃ β) (A₁ : γ ≃ δ) (A₂ : ε ≃ ζ)
    (e₁ : β ≃ δ) (e₂ : δ ≃ ζ) :
    A₀.trans ((e₁.trans e₂).trans A₂.symm) =
      (A₀.trans (e₁.trans A₁.symm)).trans (A₁.trans (e₂.trans A₂.symm)) := by
  ext a
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]

/-- The value of a conjugated bijection: `(A₀ e A₁⁻¹)(a) = b` iff `e (A₀ a) = A₁ b`. -/
theorem equiv_conj_apply_eq_iff {α β γ δ : Sort*} (A₀ : α ≃ β) (A₁ : γ ≃ δ) (e : β ≃ δ) (a : α)
    (b : γ) : (A₀.trans (e.trans A₁.symm)) a = b ↔ e (A₀ a) = A₁ b := by
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_eq]

/-- **Two sets with exactly two elements are in bijection.** -/
theorem nonempty_equiv_of_two {α β : Sort*} {a₁ a₂ : α} (ha : a₁ ≠ a₂)
    (ha' : ∀ a, a = a₁ ∨ a = a₂) {b₁ b₂ : β} (hb : b₁ ≠ b₂) (hb' : ∀ b, b = b₁ ∨ b = b₂) :
    Nonempty (α ≃ β) := by
  classical
  refine ⟨⟨fun a => if a = a₁ then b₁ else b₂, fun b => if b = b₁ then a₁ else a₂,
    fun a => ?_, fun b => ?_⟩⟩
  · rcases ha' a with rfl | rfl <;> simp [ha.symm, hb.symm]
  · rcases hb' b with rfl | rfl <;> simp [ha.symm, hb.symm]

/-- In a set with (at most) two elements, two elements different from a third one agree. -/
theorem eq_of_ne_of_ne_of_two {β : Sort*} {b₁ b₂ : β} (hb : ∀ b, b = b₁ ∨ b = b₂) {u v w : β}
    (hu : u ≠ w) (hv : v ≠ w) : u = v := by
  rcases hb u with h₁ | h₁ <;> rcases hb v with h₂ | h₂ <;> rcases hb w with h₃ | h₃ <;>
    first
    | exact h₁.trans h₂.symm
    | exact absurd (h₁.trans h₃.symm) hu
    | exact absurd (h₂.trans h₃.symm) hv

/-- **A bijection onto a two-element set is determined by one value.** -/
theorem equiv_eq_of_apply_eq_of_two {α β : Sort*} {e₁ e₂ : α ≃ β} {a : α} (h : e₁ a = e₂ a)
    {b₁ b₂ : β} (hb : ∀ b, b = b₁ ∨ b = b₂) : e₁ = e₂ := by
  ext p
  by_cases hp : p = a
  · rw [hp, h]
  · exact eq_of_ne_of_ne_of_two hb (e₁.injective.ne hp)
      (fun h' => e₂.injective.ne hp (h'.trans h))

end Regroup

/-! ### Paths in a set -/

section Paths

variable {X : Type u}

/-- A path with `γ([0, 1]) ⊆ U`, in the form `∀ q ∈ [0, 1]¹, γ q ∈ U` of `HasLocalPropagation`. -/
theorem forall_mem_of_forall_pt1_mem {γ : (Fin 1 → ℝ) → X} {U : Set X}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U) : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ U :=
  fun q hq => pt1_apply_zero q ▸ h (q 0) ⟨hq.1 0, hq.2 0⟩

end Paths

/-! ### Elements carried along by a local transport -/

namespace LocalTransport

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {O : ∀ x : X, x ∈ PX.smoothSet → Type v} (L : LocalTransport PX O)

/-- **Local transport data on a smaller family of good sets**: the sets `V` with `W V`, open,
covering `X_∞` and each contained in a good set of `L`, with the push-forwards of `L` (in a chosen
good set containing `V`). -/
def restrict (W : Set X → Prop) (hWo : ∀ {V}, W V → IsOpen V)
    (hWc : ∀ x ∈ PX.smoothSet, ∃ V, W V ∧ x ∈ V) (hWs : ∀ {V}, W V → ∃ U, L.Good U ∧ V ⊆ U) :
    LocalTransport PX O where
  Good := W
  isOpen := hWo
  exists_good := hWc
  nonempty := L.nonempty
  push hV γ hγ hγV _ _ h₀ h₁ hs₀ hs₁ :=
    L.push (hWs hV).choose_spec.1 γ hγ (fun t ht => (hWs hV).choose_spec.2 (hγV t ht)) h₀ h₁ hs₀
      hs₁
  push_trans hV _ _ _ hγ hγ₁ hγ₂ _ _ _ _ _ _ h₀ h₂ h₁₀ h₁₁ h₂₀ h₂₁ hs₀ hs₁ hs₂ :=
    L.push_trans (hWs hV).choose_spec.1 hγ hγ₁ hγ₂ _ _ _ h₀ h₂ h₁₀ h₁₁ h₂₀ h₂₁ hs₀ hs₁ hs₂
  push_compat hV hV' _ hγ _ _ _ _ h₀ h₁ hs₀ hs₁ :=
    L.push_compat (hWs hV).choose_spec.1 (hWs hV').choose_spec.1 hγ _ _ h₀ h₁ hs₀ hs₁

/-- **Elements carried into each other along every path**: if `s x ∈ O x` and the transport
along every sc-smooth path in a member `V` of an open covering of `X_∞` (each member in a good set)
takes `s` at the starting point to `s` at the end point, then so does the transport along every
sc-smooth path (Lebesgue number of the covering, dyadic pieces and `transport_halves`). -/
theorem transport_apply_eq_of_local (s : ∀ x (hx : x ∈ PX.smoothSet), O x hx)
    (W : Set X → Prop) (hWo : ∀ {V}, W V → IsOpen V)
    (hWc : ∀ x ∈ PX.smoothSet, ∃ V, W V ∧ x ∈ V) (hWs : ∀ {V}, W V → ∃ U, L.Good U ∧ V ⊆ U)
    (hW : ∀ {V}, W V → ∀ (γ : (Fin 1 → ℝ) → X) (hγ : (rnPolyfold 1).IsScSmoothMap PX γ),
      (∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ V) → ∀ {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
        (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet),
        L.transport γ hγ h₀ h₁ hs₀ hs₁ (s x₀ hs₀) = s x₁ hs₁)
    {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) {x₀ x₁ : X}
    (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet) : L.transport γ hγ h₀ h₁ hs₀ hs₁ (s x₀ hs₀) = s x₁ hs₁ := by
  let L' := L.restrict W hWo hWc hWs
  have key : ∀ N : ℕ, ∀ {γ : (Fin 1 → ℝ) → X}, L'.IsFine N γ →
      ∀ (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
        (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet),
        L.transport γ hγ h₀ h₁ hs₀ hs₁ (s x₀ hs₀) = s x₁ hs₁ := by
    intro N
    induction N with
    | zero =>
      intro γ hF hγ x₀ x₁ h₀ h₁ hs₀ hs₁
      obtain ⟨V, hV, hγV⟩ := hF
      exact hW (hV : W V) γ hγ hγV h₀ h₁ hs₀ hs₁
    | succ N ih =>
      intro γ hF hγ x₀ x₁ h₀ h₁ hs₀ hs₁
      have hsm := mem_smoothSet_of_isScSmoothMap hγ (pt1 (1 / 2))
      rw [L.transport_halves hγ h₀ h₁ rfl hs₀ hs₁ hsm, Equiv.trans_apply, ih hF.1, ih hF.2]
  obtain ⟨N, δ, hδ, hN⟩ := L'.exists_level hγ
  exact key N (L'.isFine_of_isLebesgueNumber N hδ hN) hγ h₀ h₁ hs₀ hs₁

end LocalTransport

section PathSetoid

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

variable (PX : MPolyfold X) in
/-- **The relation "joined by an sc-smooth path"** on the smooth points: `x ≈ y` iff `PX` has a
morphism `x ⟶ y` (an equivalence relation by the identities, the inverses and the composition of
the groupoid `PX`). -/
def scPathSetoid : Setoid (PathCat PX) where
  r x y := Nonempty (x ⟶ y)
  iseqv := ⟨fun x => ⟨𝟙 x⟩, fun ⟨a⟩ => ⟨Groupoid.inv a⟩, fun ⟨a⟩ ⟨b⟩ => ⟨a ≫ b⟩⟩

end PathSetoid

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-! ### The orientation sets -/

/-- **`Or_x^f` has exactly two elements** (`ChartPoint.exists_two_or`). -/
theorem exists_two_orx (hf : B.IsScFredholmSection f) {x : X} (hs : x ∈ PX.smoothSet)
    (hsec : B.HasScPlusSectionsThrough) :
    ∃ o₁ o₂ : Orx f hf x hs, o₁ ≠ o₂ ∧ ∀ o, o = o₁ ∨ o = o₂ :=
  ChartPoint.exists_two_or _ hf hs hsec

/-- **`toChartOr` followed by `orTransfer` is `toChartOr`** (`ChartPoint.orTransfer_trans`). -/
theorem toChartOr_trans (hf : B.IsScFredholmSection f) {x : X} (hs : x ∈ PX.smoothSet)
    {c c' : StrongBundleChart PX P} (hc : B.IsChart c) (hc' : B.IsChart c')
    (hx : x ∈ c.φ.source) (hx' : x ∈ c'.φ.source) :
    (toChartOr hf hs c hc hx).trans
        ((chartPtOf c hc hx hs).orTransfer (chartPtOf c' hc' hx' hs) hf hs) =
      toChartOr hf hs c' hc' hx' :=
  ChartPoint.orTransfer_trans _ _ _ hf hs

/-! ### The push-forward in a neighbourhood with the local propagation property -/

section Push

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

variable (f) in
/-- **The good sets of Theorem 6.37**: open sets with the local propagation property
(`HasLocalPropagation`) in some chart. -/
def IsPropagationNbhd (hf : B.IsScFredholmSection f) (U : Set X) : Prop :=
  ∃ (c : StrongBundleChart PX P) (hc : B.IsChart c), IsOpen U ∧ HasLocalPropagation f hf c hc U

/-- **The push-forward along a path in a good set** `U`, read in `Or^f`: a chosen push-forward
`e` (`HasLocalPropagation.exists_isPush`) in the chosen chart `c` of `U`, conjugated by
`toChartOr` at the end points. -/
def orPush {hf : B.IsScFredholmSection f} {U : Set X} (hU : IsPropagationNbhd f hf U)
    (γ : (Fin 1 → ℝ) → X) (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
    (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    Orx f hf x₀ hs₀ ≃ Orx f hf x₁ hs₁ :=
  have hLP := hU.choose_spec.choose_spec.2
  have hγ := forall_mem_of_forall_pt1_mem hγU
  have hx₀ : x₀ ∈ hU.choose.φ.source :=
    hLP.subset (h₀ ▸ hγ _ (pt1_mem_Icc ⟨le_rfl, zero_le_one⟩))
  have hx₁ : x₁ ∈ hU.choose.φ.source :=
    hLP.subset (h₁ ▸ hγ _ (pt1_mem_Icc ⟨zero_le_one, le_rfl⟩))
  (toChartOr hf hs₀ hU.choose hU.choose_spec.choose hx₀).trans
    ((hLP.exists_isPush γ hγs hγ h₀ h₁ hx₀ hx₁ hs₀ hs₁).choose.trans
      (toChartOr hf hs₁ hU.choose hU.choose_spec.choose hx₁).symm)

/-- **The push-forward in a good set is every push-forward along the path** (the chart-free form
of (∗)): for every chart `c`, every `U'` with the local propagation property in `c` containing
the path and every push-forward `e` along it in `c`, `orPush = toChartOr⁻¹ ∘ e ∘ toChartOr`
(`HasLocalPropagation.push_compat` and `toChartOr_trans`). -/
theorem orPush_eq {hf : B.IsScFredholmSection f} {U : Set X} (hU : IsPropagationNbhd f hf U)
    {γ : (Fin 1 → ℝ) → X} (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
    (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet)
    {c : StrongBundleChart PX P} {hc : B.IsChart c} {U' : Set X}
    (hU' : HasLocalPropagation f hf c hc U') (hγU' : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ U')
    (hx₀ : x₀ ∈ c.φ.source) (hx₁ : x₁ ∈ c.φ.source)
    {e : (chartPtOf c hc hx₀ hs₀).Or f hf ≃ (chartPtOf c hc hx₁ hs₁).Or f hf}
    (he : IsPush f hf c hc γ (fun q hq => hU'.subset (hγU' q hq)) h₀ h₁ hx₀ hx₁ hs₀ hs₁ e) :
    orPush hU γ hγs hγU h₀ h₁ hs₀ hs₁ =
      (toChartOr hf hs₀ c hc hx₀).trans (e.trans (toChartOr hf hs₁ c hc hx₁).symm) := by
  have hLP := hU.choose_spec.choose_spec.2
  have hγ := forall_mem_of_forall_pt1_mem hγU
  have hx₀' : x₀ ∈ hU.choose.φ.source :=
    hLP.subset (h₀ ▸ hγ _ (pt1_mem_Icc ⟨le_rfl, zero_le_one⟩))
  have hx₁' : x₁ ∈ hU.choose.φ.source :=
    hLP.subset (h₁ ▸ hγ _ (pt1_mem_Icc ⟨zero_le_one, le_rfl⟩))
  have hpush := (hLP.exists_isPush γ hγs hγ h₀ h₁ hx₀' hx₁' hs₀ hs₁).choose_spec
  have hee := HasLocalPropagation.push_compat hLP hU' hγs hγ hγU' h₀ h₁ hx₀' hx₁' hx₀ hx₁ hs₀ hs₁
    hpush he
  subst hee
  rw [← toChartOr_trans hf hs₀ hU.choose_spec.choose hc hx₀' hx₀,
    ← toChartOr_trans hf hs₁ hU.choose_spec.choose hc hx₁' hx₁]
  exact (equiv_conj_transfer_aux _ _ _ _ _).symm

/-- **The push-forward does not depend on the good set** containing the path. -/
theorem orPush_compat {hf : B.IsScFredholmSection f} {U U' : Set X}
    (hU : IsPropagationNbhd f hf U) (hU' : IsPropagationNbhd f hf U') {γ : (Fin 1 → ℝ) → X}
    (hγs : (rnPolyfold 1).IsScSmoothMap PX γ) (hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U)
    (hγU' : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U') {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
    (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet) :
    orPush hU γ hγs hγU h₀ h₁ hs₀ hs₁ = orPush hU' γ hγs hγU' h₀ h₁ hs₀ hs₁ := by
  have hLP := hU'.choose_spec.choose_spec.2
  have hγ := forall_mem_of_forall_pt1_mem hγU'
  have hx₀ : x₀ ∈ hU'.choose.φ.source :=
    hLP.subset (h₀ ▸ hγ _ (pt1_mem_Icc ⟨le_rfl, zero_le_one⟩))
  have hx₁ : x₁ ∈ hU'.choose.φ.source :=
    hLP.subset (h₁ ▸ hγ _ (pt1_mem_Icc ⟨zero_le_one, le_rfl⟩))
  exact orPush_eq hU hγs hγU h₀ h₁ hs₀ hs₁ hLP hγ hx₀ hx₁
    (hLP.exists_isPush γ hγs hγ h₀ h₁ hx₀ hx₁ hs₀ hs₁).choose_spec

/-- **Push-forwards in a good set compose** (`HasLocalPropagation.eq_trans`). -/
theorem orPush_trans {hf : B.IsScFredholmSection f} {U : Set X} (hU : IsPropagationNbhd f hf U)
    {γ γ₁ γ₂ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγ₁ : (rnPolyfold 1).IsScSmoothMap PX γ₁) (hγ₂ : (rnPolyfold 1).IsScSmoothMap PX γ₂)
    (hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U) (hγ₁U : ∀ t ∈ Icc (0 : ℝ) 1, γ₁ (pt1 t) ∈ U)
    (hγ₂U : ∀ t ∈ Icc (0 : ℝ) 1, γ₂ (pt1 t) ∈ U) {x₀ x₁ x₂ : X} (h₀ : γ (pt1 0) = x₀)
    (h₂ : γ (pt1 1) = x₂) (h₁₀ : γ₁ (pt1 0) = x₀) (h₁₁ : γ₁ (pt1 1) = x₁)
    (h₂₀ : γ₂ (pt1 0) = x₁) (h₂₁ : γ₂ (pt1 1) = x₂) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet) (hs₂ : x₂ ∈ PX.smoothSet) :
    orPush hU γ hγ hγU h₀ h₂ hs₀ hs₂ =
      (orPush hU γ₁ hγ₁ hγ₁U h₁₀ h₁₁ hs₀ hs₁).trans (orPush hU γ₂ hγ₂ hγ₂U h₂₀ h₂₁ hs₁ hs₂) := by
  obtain ⟨c, hc, -, hLP⟩ := id hU
  have hγ' := forall_mem_of_forall_pt1_mem hγU
  have hγ₁' := forall_mem_of_forall_pt1_mem hγ₁U
  have hγ₂' := forall_mem_of_forall_pt1_mem hγ₂U
  have hx₀ : x₀ ∈ c.φ.source := hLP.subset (h₀ ▸ hγ' _ (pt1_mem_Icc ⟨le_rfl, zero_le_one⟩))
  have hx₁ : x₁ ∈ c.φ.source := hLP.subset (h₁₁ ▸ hγ₁' _ (pt1_mem_Icc ⟨zero_le_one, le_rfl⟩))
  have hx₂ : x₂ ∈ c.φ.source := hLP.subset (h₂ ▸ hγ' _ (pt1_mem_Icc ⟨zero_le_one, le_rfl⟩))
  obtain ⟨e, he⟩ := hLP.exists_isPush γ hγ hγ' h₀ h₂ hx₀ hx₂ hs₀ hs₂
  obtain ⟨e₁, he₁⟩ := hLP.exists_isPush γ₁ hγ₁ hγ₁' h₁₀ h₁₁ hx₀ hx₁ hs₀ hs₁
  obtain ⟨e₂, he₂⟩ := hLP.exists_isPush γ₂ hγ₂ hγ₂' h₂₀ h₂₁ hx₁ hx₂ hs₁ hs₂
  rw [orPush_eq hU hγ hγU h₀ h₂ hs₀ hs₂ hLP hγ' hx₀ hx₂ he,
    orPush_eq hU hγ₁ hγ₁U h₁₀ h₁₁ hs₀ hs₁ hLP hγ₁' hx₀ hx₁ he₁,
    orPush_eq hU hγ₂ hγ₂U h₂₀ h₂₁ hs₁ hs₂ hLP hγ₂' hx₁ hx₂ he₂,
    hLP.eq_trans hγ hγ₁ hγ₂ hγ' hγ₁' hγ₂' h₀ h₂ h₁₀ h₁₁ h₂₀ h₂₁ hx₀ hx₁ hx₂ hs₀ hs₁ hs₂ he he₁ he₂]
  exact equiv_conj_trans_aux _ _ _ _ _

variable (f) in
/-- **Property (∗) of Theorem 6.37 on a family `W` of sets**, for a family `G` of maps
`Or_x^f ≃ Or_y^f` on the morphisms `x ⟶ y` of `PX`: for every chart `c`, every `U` with `W U` and
the local propagation property in `c`, every sc-smooth path `φ` in `U` between smooth points `x`,
`y` and every push-forward `e` along `φ` in `c` (`IsPush`), `G([φ])` is `e` read in the chosen
charts, `toChartOr_y⁻¹ ∘ e ∘ toChartOr_x`. -/
def IsStarPropertyOn (hf : B.IsScFredholmSection f) (W : Set X → Prop)
    (G : ∀ x y : PathCat PX, (x ⟶ y) → (Orx f hf x.pt x.smooth ≃ Orx f hf y.pt y.smooth)) :
    Prop :=
  ∀ (c : StrongBundleChart PX P) (hc : B.IsChart c) (U : Set X), W U →
    ∀ (hU : HasLocalPropagation f hf c hc U) (x y : PathCat PX) (φ : ScPath PX x.pt y.pt)
      (hφ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, φ.toFun q ∈ U) (hx : x.pt ∈ c.φ.source)
      (hy : y.pt ∈ c.φ.source)
      (e : (chartPtOf c hc hx x.smooth).Or f hf ≃ (chartPtOf c hc hy y.smooth).Or f hf),
      IsPush f hf c hc φ.toFun (fun q hq => hU.subset (hφ q hq)) φ.source φ.target hx hy
        x.smooth y.smooth e →
      G x y (PathCat.homMk φ) =
        (toChartOr hf x.smooth c hc hx).trans (e.trans (toChartOr hf y.smooth c hc hy).symm)

variable (f) in
/-- **Property (∗) of Theorem 6.37**: `IsStarPropertyOn` for all open sets, i.e. for every open
`U` with the local propagation property in a chart `c` and every push-forward `e` in `c` along an
sc-smooth path in `U`, `G([φ]) = toChartOr⁻¹ ∘ e ∘ toChartOr`. -/
abbrev IsStarProperty (hf : B.IsScFredholmSection f)
    (G : ∀ x y : PathCat PX, (x ⟶ y) → (Orx f hf x.pt x.smooth ≃ Orx f hf y.pt y.smooth)) :
    Prop :=
  IsStarPropertyOn f hf IsOpen G

/-! ### The local transport data and the functor `Γ_f` (Theorem 6.37) -/

section Transport

variable [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]

variable (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) (hf : B.IsScFredholmSectionTame f)
  (hsec : B.HasScPlusSectionsThrough)

include hX hbump hf hsec

/-- **The local transport data of `f`** (the proof of Theorem 6.37): the good sets are the open
sets with the local propagation property in some chart (they cover `X_∞` by Theorem 6.35), the
push-forwards are `orPush`; any two `Or_x^f` are in bijection (two elements each). -/
def orLocalTransport :
    LocalTransport PX (fun x hs => Orx f hf.toIsScFredholmSection x hs) where
  Good := IsPropagationNbhd f hf.toIsScFredholmSection
  isOpen hU := hU.choose_spec.choose_spec.1
  exists_good _ hx :=
    let ⟨c, hc, U, hUo, hxU, hU⟩ := theorem_6_35 hX hbump hf hx
    ⟨U, ⟨c, hc, hUo, hU⟩, hxU⟩
  nonempty _ hs₀ _ hs₁ :=
    let ⟨_, _, ha, ha'⟩ := exists_two_orx hf.toIsScFredholmSection hs₀ hsec
    let ⟨_, _, hb, hb'⟩ := exists_two_orx hf.toIsScFredholmSection hs₁ hsec
    nonempty_equiv_of_two ha ha' hb hb'
  push hU γ hγs hγU _ _ h₀ h₁ hs₀ hs₁ := orPush hU γ hγs hγU h₀ h₁ hs₀ hs₁
  push_trans hU _ _ _ hγ hγ₁ hγ₂ hγU hγ₁U hγ₂U _ _ _ h₀ h₂ h₁₀ h₁₁ h₂₀ h₂₁ hs₀ hs₁ hs₂ :=
    orPush_trans hU hγ hγ₁ hγ₂ hγU hγ₁U hγ₂U h₀ h₂ h₁₀ h₁₁ h₂₀ h₂₁ hs₀ hs₁ hs₂
  push_compat hU hU' _ hγ hγU hγU' _ _ h₀ h₁ hs₀ hs₁ :=
    orPush_compat hU hU' hγ hγU hγU' h₀ h₁ hs₀ hs₁

/-- **Property (∗) for the transport along a path**: on an sc-smooth path in an open `U` with the
local propagation property in a chart `c`, the transport is every push-forward `e` along the path
in `c`, read in the chosen charts. -/
theorem orLocalTransport_transport_eq {c : StrongBundleChart PX P} {hc : B.IsChart c}
    {U : Set X} (hU : HasLocalPropagation f hf.toIsScFredholmSection c hc U) (hUo : IsOpen U)
    {γ : (Fin 1 → ℝ) → X} (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγU : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ U) {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀)
    (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet)
    (hx₀ : x₀ ∈ c.φ.source) (hx₁ : x₁ ∈ c.φ.source)
    {e : (chartPtOf c hc hx₀ hs₀).Or f hf.toIsScFredholmSection ≃
      (chartPtOf c hc hx₁ hs₁).Or f hf.toIsScFredholmSection}
    (he : IsPush f hf.toIsScFredholmSection c hc γ (fun q hq => hU.subset (hγU q hq)) h₀ h₁ hx₀
      hx₁ hs₀ hs₁ e) :
    (orLocalTransport hX hbump hf hsec).transport γ hγs h₀ h₁ hs₀ hs₁ =
      (toChartOr hf.toIsScFredholmSection hs₀ c hc hx₀).trans
        (e.trans (toChartOr hf.toIsScFredholmSection hs₁ c hc hx₁).symm) :=
  ((orLocalTransport hX hbump hf hsec).transport_eq_push (U := U) ⟨c, hc, hUo, hU⟩ hγs
    (fun _ ht => hγU _ (pt1_mem_Icc ht)) h₀ h₁ hs₀ hs₁).trans
    (orPush_eq _ hγs (fun _ ht => hγU _ (pt1_mem_Icc ht)) h₀ h₁ hs₀ hs₁ hU hγU hx₀ hx₁ he)

/-- **The functor `Γ_f` on morphisms** (Theorem 6.37): `Γ_f([φ]) : Or_x^f ≃ Or_y^f` is the
transport along `φ` (`LocalTransport.transport`), which depends only on the class `[φ]`
(`transport_eq_of_isScHomotopyRel`). -/
def orFunctorMap {x y : PathCat PX} (a : x ⟶ y) :
    Orx f hf.toIsScFredholmSection x.pt x.smooth ≃ Orx f hf.toIsScFredholmSection y.pt y.smooth :=
  Quotient.lift (s := ScPath.setoid PX x.pt y.pt)
    (fun φ => (orLocalTransport hX hbump hf hsec).transport φ.toFun φ.isScSmoothMap φ.source
      φ.target x.smooth y.smooth)
    (fun φ ψ h => by
      obtain ⟨Φ, hΦ⟩ := h
      exact (orLocalTransport hX hbump hf hsec).transport_eq_of_isScHomotopyRel hΦ
        φ.isScSmoothMap ψ.isScSmoothMap φ.source φ.target x.smooth y.smooth)
    a

/-- `Γ_f([φ])` is the transport along `φ`. -/
theorem orFunctorMap_mk {x y : PathCat PX} (φ : ScPath PX x.pt y.pt) :
    orFunctorMap hX hbump hf hsec (PathCat.homMk φ) =
      (orLocalTransport hX hbump hf hsec).transport φ.toFun φ.isScSmoothMap φ.source φ.target
        x.smooth y.smooth :=
  rfl

/-- **`Γ_f` takes identities to identities** (`transport_const`). -/
theorem orFunctorMap_id (x : PathCat PX) :
    orFunctorMap hX hbump hf hsec (𝟙 x) = Equiv.refl _ :=
  (orLocalTransport hX hbump hf hsec).transport_const _ (fun _ _ => rfl) _ _ x.smooth

/-- **`Γ_f` takes compositions to composites** (`transport_concatPath`). -/
theorem orFunctorMap_comp {x y z : PathCat PX} (a : x ⟶ y) (b : y ⟶ z) :
    orFunctorMap hX hbump hf hsec (a ≫ b) =
      (orFunctorMap hX hbump hf hsec a).trans (orFunctorMap hX hbump hf hsec b) := by
  obtain ⟨φ, rfl⟩ := PathCat.exists_eq_mk a
  obtain ⟨ψ, rfl⟩ := PathCat.exists_eq_mk b
  exact (orLocalTransport hX hbump hf hsec).transport_concatPath φ.isScSmoothMap ψ.isScSmoothMap
    φ.source φ.target ψ.source ψ.target x.smooth y.smooth z.smooth

/-- **The functor `Γ_f : PX → O_f`** (Theorem 6.37) into the category of types: `x ↦ Or_x^f`,
`[φ] ↦ Γ_f([φ])`. -/
def orFunctor : PathCat PX ⥤ Type where
  obj x := Orx f hf.toIsScFredholmSection x.pt x.smooth
  map a := ↾(orFunctorMap hX hbump hf hsec a)
  map_id x := by
    rw [orFunctorMap_id]
    rfl
  map_comp a b := by
    rw [orFunctorMap_comp]
    rfl

/-- The functor `Γ_f` on objects: `x ↦ Or_x^f`. -/
theorem orFunctor_obj (x : PathCat PX) :
    (orFunctor hX hbump hf hsec).obj x = Orx f hf.toIsScFredholmSection x.pt x.smooth :=
  rfl

/-- The functor `Γ_f` on morphisms is `orFunctorMap`. -/
theorem orFunctor_map_apply {x y : PathCat PX} (a : x ⟶ y)
    (o : Orx f hf.toIsScFredholmSection x.pt x.smooth) :
    (orFunctor hX hbump hf hsec).map a o = orFunctorMap hX hbump hf hsec a o :=
  rfl

/-- **`Γ_f` has property (∗)** (`orLocalTransport_transport_eq`). -/
theorem orFunctorMap_isStarProperty :
    IsStarProperty f hf.toIsScFredholmSection fun _ _ a => orFunctorMap hX hbump hf hsec a :=
  fun _ _ _ hUo hU x y φ hφ hx hy _ he =>
    orLocalTransport_transport_eq hX hbump hf hsec hU hUo φ.isScSmoothMap hφ φ.source φ.target
      x.smooth y.smooth hx hy he

/-- **Uniqueness of `Γ_f`, for (∗) on a covering**: a family of maps on the morphisms of `PX`
taking compositions to composites and with property (∗) on the members of a family `W` of open
sets with the local propagation property covering `X_∞` is `Γ_f` (`transport_unique` for the
local transport data restricted to `W`, which both the family and the transport of
`orLocalTransport` satisfy; homotopy invariance holds on classes). -/
theorem orFunctorMap_unique_of_cover (W : Set X → Prop) (hWo : ∀ {U}, W U → IsOpen U)
    (hWc : ∀ x ∈ PX.smoothSet, ∃ U, W U ∧ x ∈ U ∧ ∃ (c : StrongBundleChart PX P)
      (hc : B.IsChart c), HasLocalPropagation f hf.toIsScFredholmSection c hc U)
    (G : ∀ x y : PathCat PX, (x ⟶ y) →
      (Orx f hf.toIsScFredholmSection x.pt x.smooth ≃ Orx f hf.toIsScFredholmSection y.pt y.smooth))
    (hG_comp : ∀ (x y z : PathCat PX) (a : x ⟶ y) (b : y ⟶ z),
      G x z (a ≫ b) = (G x y a).trans (G y z b))
    (hG : IsStarPropertyOn f hf.toIsScFredholmSection W G) :
    G = fun _ _ a => orFunctorMap hX hbump hf hsec a := by
  let L := orLocalTransport hX hbump hf hsec
  let W' : Set X → Prop := fun U => W U ∧ ∃ (c : StrongBundleChart PX P) (hc : B.IsChart c),
    HasLocalPropagation f hf.toIsScFredholmSection c hc U
  have hWs : ∀ {U}, W' U → ∃ U', L.Good U' ∧ U ⊆ U' := fun {_} ⟨hU, c, hc, hLP⟩ =>
    ⟨_, ⟨c, hc, hWo hU, hLP⟩, subset_rfl⟩
  let L' := L.restrict W' (fun hU => hWo hU.1)
    (fun x hx =>
      let ⟨U, hU, hxU, hLP⟩ := hWc x hx
      ⟨U, ⟨hU, hLP⟩, hxU⟩) hWs
  -- on a path in a member of `W'`, the push-forward of `L'` is every push-forward in its chart
  have hpush : ∀ {U : Set X} (hU : L'.Good U) {γ : (Fin 1 → ℝ) → X}
      (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ U)
      {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
      (hs₁ : x₁ ∈ PX.smoothSet) {c : StrongBundleChart PX P} {hc : B.IsChart c}
      (hLP : HasLocalPropagation f hf.toIsScFredholmSection c hc U) (hx₀ : x₀ ∈ c.φ.source)
      (hx₁ : x₁ ∈ c.φ.source)
      {e : (chartPtOf c hc hx₀ hs₀).Or f hf.toIsScFredholmSection ≃
        (chartPtOf c hc hx₁ hs₁).Or f hf.toIsScFredholmSection},
      IsPush f hf.toIsScFredholmSection c hc γ
        (fun q hq => hLP.subset (forall_mem_of_forall_pt1_mem hγU q hq)) h₀ h₁ hx₀ hx₁ hs₀ hs₁ e →
      L'.push hU γ hγ hγU h₀ h₁ hs₀ hs₁ =
        (toChartOr hf.toIsScFredholmSection hs₀ c hc hx₀).trans
          (e.trans (toChartOr hf.toIsScFredholmSection hs₁ c hc hx₁).symm) :=
    fun {_} hU {_} hγ hγU {_ _} h₀ h₁ hs₀ hs₁ {_ _} hLP hx₀ hx₁ {_} he =>
      orPush_eq (hWs hU).choose_spec.1 hγ (fun t ht => (hWs hU).choose_spec.2 (hγU t ht)) h₀ h₁
        hs₀ hs₁ hLP (forall_mem_of_forall_pt1_mem hγU) hx₀ hx₁ he
  funext x y a
  obtain ⟨φ, rfl⟩ := PathCat.exists_eq_mk a
  refine (L'.transport_unique
    (fun γ hγ {x₀ x₁} h₀ h₁ hs₀ hs₁ => G ⟨x₀, hs₀⟩ ⟨x₁, hs₁⟩ (PathCat.homMk ⟨γ, hγ, h₀, h₁⟩))
    ?_ ?_ ?_ φ.isScSmoothMap φ.source φ.target x.smooth y.smooth).trans
    (L'.transport_unique L.transport ?_ ?_ ?_ φ.isScSmoothMap φ.source φ.target x.smooth
      y.smooth).symm
  · intro _ _ _ hΦ _ _ _ _ _ _ _ _
    exact congrArg (G _ _) (PathCat.mk_eq_mk_iff.2 ⟨_, hΦ⟩)
  · intro _ _ hγ₁ hγ₂ _ _ _ h₁₀ h₁₁ h₂₀ h₂₁ hs₀ hs₁ hs₂
    exact hG_comp ⟨_, hs₀⟩ ⟨_, hs₁⟩ ⟨_, hs₂⟩ (PathCat.homMk ⟨_, hγ₁, h₁₀, h₁₁⟩)
      (PathCat.homMk ⟨_, hγ₂, h₂₀, h₂₁⟩)
  · intro U hU γ hγ hγU x₀ x₁ h₀ h₁ hs₀ hs₁
    obtain ⟨hWU, c, hc, hLP⟩ := id hU
    have hγ' := forall_mem_of_forall_pt1_mem hγU
    have hx₀ : x₀ ∈ c.φ.source := hLP.subset (h₀ ▸ hγ' _ (pt1_mem_Icc ⟨le_rfl, zero_le_one⟩))
    have hx₁ : x₁ ∈ c.φ.source := hLP.subset (h₁ ▸ hγ' _ (pt1_mem_Icc ⟨zero_le_one, le_rfl⟩))
    obtain ⟨e, he⟩ := hLP.exists_isPush γ hγ hγ' h₀ h₁ hx₀ hx₁ hs₀ hs₁
    exact (hG c hc U hWU hLP ⟨x₀, hs₀⟩ ⟨x₁, hs₁⟩ ⟨γ, hγ, h₀, h₁⟩ hγ' hx₀ hx₁ e he).trans
      (hpush hU hγ hγU h₀ h₁ hs₀ hs₁ hLP hx₀ hx₁ he).symm
  · intro _ _ _ hΦ hγ₀ hγ₁ _ _ h₀ h₁ hs₀ hs₁
    exact L.transport_eq_of_isScHomotopyRel hΦ hγ₀ hγ₁ h₀ h₁ hs₀ hs₁
  · intro _ _ hγ₁ hγ₂ _ _ _ h₁₀ h₁₁ h₂₀ h₂₁ hs₀ hs₁ hs₂
    exact L.transport_concatPath hγ₁ hγ₂ h₁₀ h₁₁ h₂₀ h₂₁ hs₀ hs₁ hs₂
  · intro U hU γ hγ hγU x₀ x₁ h₀ h₁ hs₀ hs₁
    obtain ⟨hWU, c, hc, hLP⟩ := id hU
    have hγ' := forall_mem_of_forall_pt1_mem hγU
    have hx₀ : x₀ ∈ c.φ.source := hLP.subset (h₀ ▸ hγ' _ (pt1_mem_Icc ⟨le_rfl, zero_le_one⟩))
    have hx₁ : x₁ ∈ c.φ.source := hLP.subset (h₁ ▸ hγ' _ (pt1_mem_Icc ⟨zero_le_one, le_rfl⟩))
    obtain ⟨e, he⟩ := hLP.exists_isPush γ hγ hγ' h₀ h₁ hx₀ hx₁ hs₀ hs₁
    exact (orLocalTransport_transport_eq hX hbump hf hsec hLP (hWo hWU) hγ hγ' h₀ h₁ hs₀ hs₁ hx₀
      hx₁ he).trans (hpush hU hγ hγU h₀ h₁ hs₀ hs₁ hLP hx₀ hx₁ he).symm

/-- **Uniqueness of `Γ_f`** ("it is obvious that `Γ_f` is unique"): a family of maps on the
morphisms of `PX` taking compositions to composites and with property (∗) is `Γ_f`
(`orFunctorMap_unique_of_cover` for the open sets, which cover `X_∞` by Theorem 6.35). -/
theorem orFunctorMap_unique
    (G : ∀ x y : PathCat PX, (x ⟶ y) →
      (Orx f hf.toIsScFredholmSection x.pt x.smooth ≃ Orx f hf.toIsScFredholmSection y.pt y.smooth))
    (hG_comp : ∀ (x y z : PathCat PX) (a : x ⟶ y) (b : y ⟶ z),
      G x z (a ≫ b) = (G x y a).trans (G y z b))
    (hG : IsStarProperty f hf.toIsScFredholmSection G) :
    G = fun _ _ a => orFunctorMap hX hbump hf hsec a :=
  orFunctorMap_unique_of_cover hX hbump hf hsec IsOpen id
    (fun _ hx =>
      let ⟨c, hc, U, hUo, hxU, hU⟩ := theorem_6_35 hX hbump hf hx
      ⟨U, hUo, hxU, c, hc, hU⟩) G hG_comp hG

/-- **Theorem 6.37**: there is a unique family of maps `Γ_f([φ]) : Or_x^f ≃ Or_y^f` on the
morphisms `[φ] : x ⟶ y` of `PX` which is a functor (identities to identities, compositions to
composites) and has property (∗); it is `orFunctorMap` (packaged as `orFunctor`). -/
theorem theorem_6_37 :
    ∃! G : ∀ x y : PathCat PX, (x ⟶ y) →
        (Orx f hf.toIsScFredholmSection x.pt x.smooth ≃
          Orx f hf.toIsScFredholmSection y.pt y.smooth),
      (∀ x, G x x (𝟙 x) = Equiv.refl _) ∧
      (∀ (x y z : PathCat PX) (a : x ⟶ y) (b : y ⟶ z),
        G x z (a ≫ b) = (G x y a).trans (G y z b)) ∧
      IsStarProperty f hf.toIsScFredholmSection G :=
  ⟨fun _ _ a => orFunctorMap hX hbump hf hsec a,
    ⟨orFunctorMap_id hX hbump hf hsec, fun _ _ _ => orFunctorMap_comp hX hbump hf hsec,
      orFunctorMap_isStarProperty hX hbump hf hsec⟩,
    fun G ⟨_, hG_comp, hG⟩ => orFunctorMap_unique hX hbump hf hsec G hG_comp hG⟩

/-! ### Orientability (Definitions 6.38 and 6.39) and orientations (Definition 6.40) -/

/-- **Definition 6.38, orientability**: for every pair of smooth points `x`, `y` and any two
morphisms `[φ], [ψ] : x ⟶ y` of `PX` (classes of sc-smooth paths from `x` to `y`),
`Γ_f([φ]) = Γ_f([ψ])`. -/
def IsOrientableSection : Prop :=
  ∀ (x y : PathCat PX) (a b : x ⟶ y),
    orFunctorMap hX hbump hf hsec a = orFunctorMap hX hbump hf hsec b

/-- **A map `y ↦ o_y` which is a continuous orientation over an orientable neighbourhood of every
smooth point is carried along by `Γ_f`**: `Γ_f([φ]) o_x = o_y` for every `[φ] : x ⟶ y`
(`transport_apply_eq_of_local` for the covering by the sets `V` of these orientable
neighbourhoods; on a path in `V`, (∗) and the continuity). -/
theorem orFunctorMap_apply_eq_of_local
    (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy)
    (ho : ∀ x ∈ PX.smoothSet, ∃ (c : StrongBundleChart PX P) (hc : B.IsChart c) (U V : Set X)
      (hN : IsOrientableNbhd f hf.toIsScFredholmSection c hc U V x),
      IsContinuousOrientation f hf.toIsScFredholmSection c hc hN.hasLocalPropagation.subset
        hN.subset (restrictOr o hN))
    {x y : PathCat PX} (a : x ⟶ y) :
    orFunctorMap hX hbump hf hsec a (o x.pt x.smooth) = o y.pt y.smooth := by
  obtain ⟨φ, rfl⟩ := PathCat.exists_eq_mk a
  rw [orFunctorMap_mk]
  refine (orLocalTransport hX hbump hf hsec).transport_apply_eq_of_local o
    (fun V => ∃ (c : StrongBundleChart PX P) (hc : B.IsChart c) (U : Set X) (x : X)
      (hN : IsOrientableNbhd f hf.toIsScFredholmSection c hc U V x),
      IsContinuousOrientation f hf.toIsScFredholmSection c hc hN.hasLocalPropagation.subset
        hN.subset (restrictOr o hN))
    (fun ⟨_, _, _, _, hN, _⟩ => hN.isOpen_V)
    (fun x hx =>
      let ⟨c, hc, U, V, hN, hcont⟩ := ho x hx
      ⟨V, ⟨c, hc, U, x, hN, hcont⟩, hN.mem⟩)
    (fun ⟨c, hc, U, _, hN, _⟩ => ⟨U, ⟨c, hc, hN.isOpen_U, hN.hasLocalPropagation⟩, hN.subset⟩)
    ?_ φ.isScSmoothMap φ.source φ.target x.smooth y.smooth
  rintro V ⟨c, hc, U, x', hN, hcont⟩ γ hγ hγV x₀ x₁ h₀ h₁ hs₀ hs₁
  have hγU := forall_mem_of_forall_pt1_mem fun t ht => hN.subset (hγV t ht)
  have hx₀ : x₀ ∈ V := h₀ ▸ hγV 0 ⟨le_rfl, zero_le_one⟩
  have hx₁ : x₁ ∈ V := h₁ ▸ hγV 1 ⟨zero_le_one, le_rfl⟩
  have hUc := hN.hasLocalPropagation.subset
  obtain ⟨e, he⟩ := hN.hasLocalPropagation.exists_isPush γ hγ hγU h₀ h₁ (hUc (hN.subset hx₀))
    (hUc (hN.subset hx₁)) hs₀ hs₁
  rw [orLocalTransport_transport_eq hX hbump hf hsec hN.hasLocalPropagation hN.isOpen_U hγ hγU h₀
    h₁ hs₀ hs₁ _ _ he]
  exact (equiv_conj_apply_eq_iff _ _ _ _ _).2 (hcont γ hγ hγU hx₀ hx₁ hs₀ hs₁ h₀ h₁ e he)

/-- **A map `y ↦ o_y` carried along by `Γ_f` is a continuous orientation over every orientable
neighbourhood** ((∗) for the paths in `U`). -/
theorem isContinuousOrientation_of_apply_eq
    (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy)
    (ho : ∀ (x y : PathCat PX) (a : x ⟶ y),
      orFunctorMap hX hbump hf hsec a (o x.pt x.smooth) = o y.pt y.smooth)
    {c : StrongBundleChart PX P} {hc : B.IsChart c} {U V : Set X} {x : X}
    (hN : IsOrientableNbhd f hf.toIsScFredholmSection c hc U V x) :
    IsContinuousOrientation f hf.toIsScFredholmSection c hc hN.hasLocalPropagation.subset
      hN.subset (restrictOr o hN) := by
  intro γ hγs hγ y₁ y₂ _ _ hs₁ hs₂ h₀ h₁ e he
  have h := ho ⟨y₁, hs₁⟩ ⟨y₂, hs₂⟩ (PathCat.homMk ⟨γ, hγs, h₀, h₁⟩)
  rw [orFunctorMap_mk, orLocalTransport_transport_eq hX hbump hf hsec hN.hasLocalPropagation
    hN.isOpen_U hγs hγ h₀ h₁ hs₁ hs₂ _ _ he] at h
  exact (equiv_conj_apply_eq_iff _ _ _ _ _).1 h

/-- **From Definition 6.38 to a map `y ↦ o_y` carried along by `Γ_f`**: in each class of smooth
points joined by sc-smooth paths a base point `b` (`Quotient.out` for `scPathSetoid`) and an
orientation `o_b` are chosen, and `o_y = Γ_f([φ_y]) o_b` for a path `φ_y` from `b` to `y`. -/
theorem exists_apply_eq_of_isOrientableSection (h : IsOrientableSection hX hbump hf hsec) :
    ∃ o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy,
      ∀ (x y : PathCat PX) (a : x ⟶ y),
        orFunctorMap hX hbump hf hsec a (o x.pt x.smooth) = o y.pt y.smooth := by
  let base : PathCat PX → PathCat PX := fun y => (Quotient.mk (scPathSetoid PX) y).out
  have hbase : ∀ y, Nonempty (base y ⟶ y) := fun y => Quotient.mk_out (s := scPathSetoid PX) y
  let ob : ∀ z : PathCat PX, Orx f hf.toIsScFredholmSection z.pt z.smooth := fun z =>
    (exists_two_orx hf.toIsScFredholmSection z.smooth hsec).choose
  refine ⟨fun y hy => orFunctorMap hX hbump hf hsec (hbase ⟨y, hy⟩).some (ob (base ⟨y, hy⟩)),
    fun x y a => ?_⟩
  have hb : base x = base y := congrArg Quotient.out (Quotient.sound (s := scPathSetoid PX) ⟨a⟩)
  have key : ∀ b₁ b₂ : PathCat PX, b₁ = b₂ → ∀ (p₁ : b₁ ⟶ x) (p₂ : b₂ ⟶ y),
      orFunctorMap hX hbump hf hsec a (orFunctorMap hX hbump hf hsec p₁ (ob b₁)) =
        orFunctorMap hX hbump hf hsec p₂ (ob b₂) := by
    rintro b _ rfl p₁ p₂
    rw [← Equiv.trans_apply, ← orFunctorMap_comp, h _ _ (p₁ ≫ a) p₂]
  exact key _ _ hb _ _

/-- **From a map `y ↦ o_y` carried along by `Γ_f` to Definition 6.38**: `Γ_f([φ])` and
`Γ_f([ψ])` agree at `o_x`, and a bijection onto the two-element set `Or_y^f` is determined by
one value. -/
theorem isOrientableSection_of_apply_eq
    (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy)
    (ho : ∀ (x y : PathCat PX) (a : x ⟶ y),
      orFunctorMap hX hbump hf hsec a (o x.pt x.smooth) = o y.pt y.smooth) :
    IsOrientableSection hX hbump hf hsec := fun x y a b =>
  let ⟨_, _, _, hall⟩ := exists_two_orx hf.toIsScFredholmSection y.smooth hsec
  equiv_eq_of_apply_eq_of_two ((ho x y a).trans (ho x y b).symm) hall

/-- **Definition 6.38 in terms of maps `y ↦ o_y`**: `f` is orientable iff there is a map
`y ↦ o_y ∈ Or_y^f` on the smooth points with `Γ_f([φ]) o_x = o_y` for every `[φ] : x ⟶ y`. -/
theorem isOrientableSection_iff_exists :
    IsOrientableSection hX hbump hf hsec ↔
      ∃ o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy,
        ∀ (x y : PathCat PX) (a : x ⟶ y),
          orFunctorMap hX hbump hf hsec a (o x.pt x.smooth) = o y.pt y.smooth :=
  ⟨exists_apply_eq_of_isOrientableSection hX hbump hf hsec,
    fun ⟨o, ho⟩ => isOrientableSection_of_apply_eq hX hbump hf hsec o ho⟩

/-- **Definition 6.39 in terms of maps `y ↦ o_y`**: there is a map `y ↦ o_y` which is a continuous
orientation over an orientable neighbourhood of every smooth point iff there is one with
`Γ_f([φ]) o_x = o_y` for every `[φ] : x ⟶ y` (orientable neighbourhoods exist,
`exists_isOrientableNbhd`). -/
theorem isOrientableSection'_iff_exists :
    IsOrientableSection' f hf.toIsScFredholmSection ↔
      ∃ o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy,
        ∀ (x y : PathCat PX) (a : x ⟶ y),
          orFunctorMap hX hbump hf hsec a (o x.pt x.smooth) = o y.pt y.smooth :=
  ⟨fun ⟨o, ho⟩ => ⟨o, fun _ _ a => orFunctorMap_apply_eq_of_local hX hbump hf hsec o ho a⟩,
    fun ⟨o, ho⟩ => ⟨o, fun _ hx =>
      let ⟨c, hc, U, V, hN⟩ := exists_isOrientableNbhd hX hbump hf hx
      ⟨c, hc, U, V, hN, isContinuousOrientation_of_apply_eq hX hbump hf hsec o ho hN⟩⟩⟩

/-- **Definitions 6.38 and 6.39 are equivalent** ("an equivalent version"). -/
theorem isOrientableSection_iff :
    IsOrientableSection hX hbump hf hsec ↔ IsOrientableSection' f hf.toIsScFredholmSection :=
  (isOrientableSection_iff_exists hX hbump hf hsec).trans
    (isOrientableSection'_iff_exists hX hbump hf hsec).symm

/-- **Definition 6.40 in terms of `Γ_f`**: `y ↦ o_y` is an orientation of `f` iff
`Γ_f([φ]) o_x = o_y` for every morphism `[φ] : x ⟶ y` of `PX`. -/
theorem isSectionOrientation_iff
    (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy) :
    IsSectionOrientation f hf.toIsScFredholmSection o ↔
      ∀ (x y : PathCat PX) (a : x ⟶ y),
        orFunctorMap hX hbump hf hsec a (o x.pt x.smooth) = o y.pt y.smooth :=
  ⟨fun h _ _ a => orFunctorMap_apply_eq_of_local hX hbump hf hsec o (fun _ hx =>
      let ⟨c, hc, U, V, hN⟩ := exists_isOrientableNbhd hX hbump hf hx
      ⟨c, hc, U, V, hN, h _ hx c hc U V hN⟩) a,
    fun ho _ _ _ _ _ _ hN => isContinuousOrientation_of_apply_eq hX hbump hf hsec o ho hN⟩

/-- **`f` has an orientation (Definition 6.40) iff it is orientable (Definition 6.38).** -/
theorem exists_isSectionOrientation_iff :
    (∃ o, IsSectionOrientation f hf.toIsScFredholmSection o) ↔
      IsOrientableSection hX hbump hf hsec :=
  (exists_congr (isSectionOrientation_iff hX hbump hf hsec)).trans
    (isOrientableSection_iff_exists hX hbump hf hsec).symm

/-- **Two orientations which agree at a point agree on its path component**: for a morphism
`[φ] : x ⟶ y`, `o_x = o'_x` iff `o_y = o'_y`. -/
theorem IsSectionOrientation.apply_eq_iff
    {o o' : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy}
    (ho : IsSectionOrientation f hf.toIsScFredholmSection o)
    (ho' : IsSectionOrientation f hf.toIsScFredholmSection o') {x y : PathCat PX} (a : x ⟶ y) :
    o x.pt x.smooth = o' x.pt x.smooth ↔ o y.pt y.smooth = o' y.pt y.smooth := by
  rw [← (isSectionOrientation_iff hX hbump hf hsec o).1 ho x y a,
    ← (isSectionOrientation_iff hX hbump hf hsec o').1 ho' x y a]
  exact (orFunctorMap hX hbump hf hsec a).apply_eq_iff_eq.symm

/-- **On the path component of a point there are exactly two orientations**: for an orientation
`o` and a smooth point `x` there is an orientation `o'` which differs from `o` at every point
joined to `x` by an sc-smooth path and agrees with `o` at the other points, and on the path
component of `x` every orientation agrees with `o` or with `o'`. -/
theorem IsSectionOrientation.exists_two
    {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy}
    (ho : IsSectionOrientation f hf.toIsScFredholmSection o) (x : PathCat PX) :
    ∃ o' : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy,
      IsSectionOrientation f hf.toIsScFredholmSection o' ∧
      (∀ y : PathCat PX, Nonempty (x ⟶ y) → o' y.pt y.smooth ≠ o y.pt y.smooth) ∧
      (∀ y : PathCat PX, IsEmpty (x ⟶ y) → o' y.pt y.smooth = o y.pt y.smooth) ∧
      ∀ o'' : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy,
        IsSectionOrientation f hf.toIsScFredholmSection o'' →
        (∀ y : PathCat PX, Nonempty (x ⟶ y) → o'' y.pt y.smooth = o y.pt y.smooth) ∨
        (∀ y : PathCat PX, Nonempty (x ⟶ y) → o'' y.pt y.smooth = o' y.pt y.smooth) := by
  classical
  have htwo := fun (y : X) (hy : y ∈ PX.smoothSet) =>
    exists_two_orx hf.toIsScFredholmSection hy hsec
  -- the other orientation at `y`
  have hne : ∀ y (hy : y ∈ PX.smoothSet) (p : Orx f hf.toIsScFredholmSection y hy), ∃ q, q ≠ p :=
    fun y hy p =>
      let ⟨a₁, a₂, ha, _⟩ := htwo y hy
      if hp : p = a₁ then ⟨a₂, hp ▸ ha.symm⟩ else ⟨a₁, Ne.symm hp⟩
  let flip : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy →
      Orx f hf.toIsScFredholmSection y hy := fun y hy p => (hne y hy p).choose
  have hflip : ∀ y hy p, flip y hy p ≠ p := fun y hy p => (hne y hy p).choose_spec
  have hother : ∀ y hy (p q : Orx f hf.toIsScFredholmSection y hy), q ≠ p → q = flip y hy p :=
    fun y hy p q hq =>
      let ⟨_, _, _, hall⟩ := htwo y hy
      eq_of_ne_of_ne_of_two hall hq (hflip y hy p)
  have hΓ := (isSectionOrientation_iff hX hbump hf hsec o).1 ho
  let o' : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy := fun y hy =>
    if Nonempty (x ⟶ ⟨y, hy⟩) then flip y hy (o y hy) else o y hy
  have e₁ : ∀ y : PathCat PX, Nonempty (x ⟶ y) →
      o' y.pt y.smooth = flip y.pt y.smooth (o y.pt y.smooth) := fun _ h => if_pos h
  have e₂ : ∀ y : PathCat PX, IsEmpty (x ⟶ y) → o' y.pt y.smooth = o y.pt y.smooth :=
    fun _ h => if_neg (not_nonempty_iff.2 h)
  have ho' : IsSectionOrientation f hf.toIsScFredholmSection o' := by
    refine (isSectionOrientation_iff hX hbump hf hsec o').2 fun y z a => ?_
    by_cases hy : Nonempty (x ⟶ y)
    · rw [e₁ y hy, e₁ z ⟨hy.some ≫ a⟩]
      refine hother _ _ _ _ fun h => hflip _ _ (o y.pt y.smooth) ?_
      exact (orFunctorMap hX hbump hf hsec a).injective (h.trans (hΓ y z a).symm)
    · have hz : IsEmpty (x ⟶ z) := not_nonempty_iff.1 fun ⟨b⟩ => hy ⟨b ≫ Groupoid.inv a⟩
      rw [e₂ y (not_nonempty_iff.1 hy), e₂ z hz]
      exact hΓ y z a
  refine ⟨o', ho', fun y hy => (e₁ y hy).symm ▸ hflip _ _ _, e₂, fun o'' ho'' => ?_⟩
  by_cases hx : o'' x.pt x.smooth = o x.pt x.smooth
  · exact Or.inl fun y ⟨a⟩ => (ho''.apply_eq_iff hX hbump hf hsec ho a).1 hx
  · have hx' : o'' x.pt x.smooth = o' x.pt x.smooth :=
      (hother _ _ _ _ hx).trans (e₁ x ⟨𝟙 x⟩).symm
    exact Or.inr fun y ⟨a⟩ => (ho''.apply_eq_iff hX hbump hf hsec ho' a).1 hx'

end Transport

end Push

end Polyfold
