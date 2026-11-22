import Polyfold.Chapter17.WhitneySumStructure

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.6 (pp. 817–819): the **category `⊕ᵏ TC`** of **Proposition 17.6.1**, its projection
`⊕ᵏ P : ⊕ᵏ TC → C¹`, and the **functors `⊕ᵏ TΨ : G ⋉ ⊕ᵏ TO → ⊕ᵏ TC` on morphisms**.  Numbers and
pages are the 2021 text's.

# The category `⊕ᵏ TC` and the functors `⊕ᵏ TΨ`

## The text, paraphrased

(pp. 817–818) "On the categorical level we can build the `k`-fold Whitney sum `⊕ᵏ TC → C¹`."
(Proposition 17.6.1, proof) The functors `⊕ᵏ TΨ : G ⋉ ⊕ᵏ TO → ⊕ᵏ TC` are
`(⊕ᵏ TΨ)(h₁, …, h_k) = (TΨ(h₁), …, TΨ(h_k))` on objects, `hᵢ ∈ T_qO`, and on the morphism
`(g, (h₁, …, h_k)) : (h₁, …, h_k) → (g ∗ h₁, …, g ∗ h_k)`
`(⊕ᵏ TΨ)(g, (h₁, …, h_k)) = ((TΨ(h₁), Ψ(g, x), T(Ψ(g, x))(TΨ(h₁))), …,
(TΨ(h_k), Ψ(g, x), T(Ψ(g, x))(TΨ(h_k))))`; they cover `Ψ¹`, `⊕ᵏ P ∘ ⊕ᵏ TΨ = Ψ¹ ∘ ⊕ᵏ p`.
"Clearly, `⊕ᵏ TC` is a GCT."

## What is formalized

* General (namespace `Polyfold.GroupoidFunctor`), for a functor `P : G → H` of groupoids: the
  **`k`-fold fibred power `⊕ᵏ_P G`** over `H`, `WhitneyObj` (`(β, x₁, …, x_k)` with
  `P(xᵢ) = β`), `WhitneyMor` (`(ψ, φ₁, …, φ_k)` with `P(φᵢ) = ψ`), the groupoid
  `whitneyGroupoid` (componentwise structure maps), `finite_whitneyMor`, the projection
  `whitneyProjFunctor` (`⊕ᵏ P`), the components `whitneyComponent i`, and **`whitneyLift`** (the
  functor into `⊕ᵏ_P G` of a functor `F` into `H` and `k` functors `Tᵢ` into `G` over `F`);
  `bijective_whitneyProj_zero` (`⊕⁰_P G = H`) and `bijective_whitneyComponent_one`
  (`⊕¹_P G = G`).
* For a polyfold construction `S` of `C` (namespace `Polyfold.GCT.PolyfoldConstruction`):
  **`whitneyCatGroupoid k`**, **`whitneyCategory k`** (`⊕ᵏ TC`, the fibred power of
  `P : TC → C¹`, a groupoidal category), `whitneyCatProj` (`⊕ᵏ P : ⊕ᵏ TC → C¹`),
  `whitneyCatProj_zero_bijective`, `whitneyComponent_one_bijective`; `whitneyTranslation Ψ k`
  (`G ⋉ ⊕ᵏ TO`), `whitneyVecFunctor` (`(g, v) ↦ (g, vᵢ)`), `whitneyBaseFunctor` (`Ψ¹ ∘ ⊕ᵏ p`),
  **`whitneyUnifFunctor`** (`⊕ᵏ TΨ`, a functor for continuous `Ψ̂`), its values
  `whitneyUnifFunctor_obj_vec`, `whitneyUnifFunctor_mor_vec`, `whitneyUnifFunctor_mor_base`,
  the square `whitneyCatProj_comp_whitneyUnifFunctor`, the target formula
  `whitneyUnifFunctor_tgt`, and **`proposition_17_6_1_functor`**.
* Witness, `k = 2` on the reflection `ℤ/2 ⋉ ℝ`: **`reflection_whitneyUnif_nondegenerate`**:
  `⊕² TΨ₀(−1, (e, e))` is a morphism of `⊕² TC` whose source and target differ.

## Readings

* `⊕ᵏ TC` is read as the `k`-fold fibred product of `P : TC → C¹` over `C¹`: an object is an
  object `α` of `C¹` with `k` tangent vectors at `α`, a morphism is a morphism `φ` of `C¹` with
  `k` morphisms of `TC` over `φ` (the reading of `WTrM` for the transition sets).  For `k = 0`
  it is `C¹`, for `k = 1` it is `TC`.
* "`G ⋉ ⊕ᵏ TO`" is the translation groupoid of `ULift G` acting through
  `g ∗ (h₁, …, h_k) = (T(g ∗ ·)h₁, …, T(g ∗ ·)h_k)`, as `G ⋉ TO` for `TC`.
* On morphisms `⊕ᵏ TΨ` is built from `TΨ(g, h)`, a functor when `Ψ̂` is continuous
  (`lemma_17_2_10_of_continuous`; without continuity `not_lemma_17_2_10`); so `⊕ᵏ TΨ` carries
  the hypothesis `hc : Continuous (S.hat Ψ)`, as `tangentUnifFunctor` does (the reading of
  Lemma 17.1.9, `lemma_17_1_9_of_continuous`).  The reflection witness has continuous `Ψ̂`.
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u v w

/-! ### The fibred power of a functor of groupoids -/

namespace GroupoidFunctor

variable {Obj Mor : Type u} {Obj' Mor' : Type v} {G : GroupoidStr Obj Mor}
  {H : GroupoidStr Obj' Mor'} (P : GroupoidFunctor G H) (k : ℕ)

/-- **An object of `⊕ᵏ_P G`**: an object `β` of `H` and `k` objects `xᵢ` of `G` over it. -/
structure WhitneyObj : Type (max u v) where
  /-- The object `β` of `H`. -/
  base : Obj'
  /-- The objects `x₁, …, x_k` of `G`. -/
  vec : Fin k → Obj
  obj_vec : ∀ i, P.obj (vec i) = base

/-- **A morphism of `⊕ᵏ_P G`**: a morphism `ψ` of `H` and `k` morphisms `φᵢ` of `G` over it. -/
structure WhitneyMor : Type (max u v) where
  /-- The morphism `ψ` of `H`. -/
  base : Mor'
  /-- The morphisms `φ₁, …, φ_k` of `G`. -/
  vec : Fin k → Mor
  mor_vec : ∀ i, P.mor (vec i) = base

variable {P k}

theorem WhitneyObj.ext' {x y : P.WhitneyObj k} (h₁ : x.base = y.base) (h₂ : x.vec = y.vec) :
    x = y := by
  cases x; cases y; cases h₁; cases h₂; rfl

theorem WhitneyMor.ext' {Φ Ψ : P.WhitneyMor k} (h₁ : Φ.base = Ψ.base) (h₂ : Φ.vec = Ψ.vec) :
    Φ = Ψ := by
  cases Φ; cases Ψ; cases h₁; cases h₂; rfl

variable (P k)

/-- The source `(s(ψ), s(φ₁), …, s(φ_k))`. -/
def whitneySrc (Φ : P.WhitneyMor k) : P.WhitneyObj k :=
  ⟨H.src Φ.base, fun i => G.src (Φ.vec i), fun i => by rw [← P.src_mor, Φ.mor_vec]⟩

/-- The target `(t(ψ), t(φ₁), …, t(φ_k))`. -/
def whitneyTgt (Φ : P.WhitneyMor k) : P.WhitneyObj k :=
  ⟨H.tgt Φ.base, fun i => G.tgt (Φ.vec i), fun i => by rw [← P.tgt_mor, Φ.mor_vec]⟩

/-- The unit `(1_β, 1_{x₁}, …, 1_{x_k})`. -/
def whitneyUnit (x : P.WhitneyObj k) : P.WhitneyMor k :=
  ⟨H.unit x.base, fun i => G.unit (x.vec i), fun i => by rw [P.mor_unit, x.obj_vec]⟩

/-- The inverse `(ψ⁻¹, φ₁⁻¹, …, φ_k⁻¹)`. -/
def whitneyInv (Φ : P.WhitneyMor k) : P.WhitneyMor k :=
  ⟨H.inv Φ.base, fun i => G.inv (Φ.vec i), fun i => by rw [P.mor_inv, Φ.mor_vec]⟩

variable {P k}

theorem base_composable {Φ Ψ : P.WhitneyMor k} (h : P.whitneySrc k Φ = P.whitneyTgt k Ψ) :
    H.src Φ.base = H.tgt Ψ.base :=
  congrArg WhitneyObj.base h

theorem vec_composable {Φ Ψ : P.WhitneyMor k} (h : P.whitneySrc k Φ = P.whitneyTgt k Ψ)
    (i : Fin k) : G.src (Φ.vec i) = G.tgt (Ψ.vec i) :=
  congrFun (congrArg WhitneyObj.vec h) i

variable (P k)

open scoped Classical in
/-- The composite `(ψ ∘ ψ', φ₁ ∘ φ₁', …, φ_k ∘ φ_k')` (meant for composable pairs). -/
def whitneyComp (Φ Ψ : P.WhitneyMor k) : P.WhitneyMor k :=
  if h : P.whitneySrc k Φ = P.whitneyTgt k Ψ then
    ⟨H.comp Φ.base Ψ.base, fun i => G.comp (Φ.vec i) (Ψ.vec i), fun i => by
      rw [P.mor_comp _ _ (vec_composable h i), Φ.mor_vec, Ψ.mor_vec]⟩
  else Ψ

variable {P k}

theorem whitneyComp_base {Φ Ψ : P.WhitneyMor k} (h : P.whitneySrc k Φ = P.whitneyTgt k Ψ) :
    (P.whitneyComp k Φ Ψ).base = H.comp Φ.base Ψ.base := by
  rw [whitneyComp, dif_pos h]

theorem whitneyComp_vec {Φ Ψ : P.WhitneyMor k} (h : P.whitneySrc k Φ = P.whitneyTgt k Ψ)
    (i : Fin k) : (P.whitneyComp k Φ Ψ).vec i = G.comp (Φ.vec i) (Ψ.vec i) := by
  rw [whitneyComp, dif_pos h]

theorem whitneySrc_comp {Φ Ψ : P.WhitneyMor k} (h : P.whitneySrc k Φ = P.whitneyTgt k Ψ) :
    P.whitneySrc k (P.whitneyComp k Φ Ψ) = P.whitneySrc k Ψ := by
  refine WhitneyObj.ext' ?_ (funext fun i => ?_)
  · change H.src (P.whitneyComp k Φ Ψ).base = H.src Ψ.base
    rw [whitneyComp_base h]
    exact H.src_comp _ _ (base_composable h)
  · change G.src ((P.whitneyComp k Φ Ψ).vec i) = G.src (Ψ.vec i)
    rw [whitneyComp_vec h]
    exact G.src_comp _ _ (vec_composable h i)

theorem whitneyTgt_comp {Φ Ψ : P.WhitneyMor k} (h : P.whitneySrc k Φ = P.whitneyTgt k Ψ) :
    P.whitneyTgt k (P.whitneyComp k Φ Ψ) = P.whitneyTgt k Φ := by
  refine WhitneyObj.ext' ?_ (funext fun i => ?_)
  · change H.tgt (P.whitneyComp k Φ Ψ).base = H.tgt Φ.base
    rw [whitneyComp_base h]
    exact H.tgt_comp _ _ (base_composable h)
  · change G.tgt ((P.whitneyComp k Φ Ψ).vec i) = G.tgt (Φ.vec i)
    rw [whitneyComp_vec h]
    exact G.tgt_comp _ _ (vec_composable h i)

theorem whitneySrc_unit (x : P.WhitneyObj k) : P.whitneySrc k (P.whitneyUnit k x) = x :=
  WhitneyObj.ext' (H.src_unit _) (funext fun _ => G.src_unit _)

theorem whitneyTgt_unit (x : P.WhitneyObj k) : P.whitneyTgt k (P.whitneyUnit k x) = x :=
  WhitneyObj.ext' (H.tgt_unit _) (funext fun _ => G.tgt_unit _)

theorem whitneySrc_inv (Φ : P.WhitneyMor k) :
    P.whitneySrc k (P.whitneyInv k Φ) = P.whitneyTgt k Φ :=
  WhitneyObj.ext' (H.src_inv _) (funext fun _ => G.src_inv _)

theorem whitneyTgt_inv (Φ : P.WhitneyMor k) :
    P.whitneyTgt k (P.whitneyInv k Φ) = P.whitneySrc k Φ :=
  WhitneyObj.ext' (H.tgt_inv _) (funext fun _ => G.tgt_inv _)

variable (P k)

/-- **The groupoid `⊕ᵏ_P G`**, the `k`-fold fibred power of `P : G → H` over `H`, with the
componentwise structure maps. -/
def whitneyGroupoid : GroupoidStr (P.WhitneyObj k) (P.WhitneyMor k) where
  src := P.whitneySrc k
  tgt := P.whitneyTgt k
  comp := P.whitneyComp k
  unit := P.whitneyUnit k
  inv := P.whitneyInv k
  src_comp _ _ h := whitneySrc_comp h
  tgt_comp _ _ h := whitneyTgt_comp h
  comp_assoc Φ Ψ X h₁ h₂ := by
    have h₃ : P.whitneySrc k (P.whitneyComp k Φ Ψ) = P.whitneyTgt k X :=
      (whitneySrc_comp h₁).trans h₂
    have h₄ : P.whitneySrc k Φ = P.whitneyTgt k (P.whitneyComp k Ψ X) :=
      h₁.trans (whitneyTgt_comp h₂).symm
    refine WhitneyMor.ext' ?_ (funext fun i => ?_)
    · rw [whitneyComp_base h₃, whitneyComp_base h₁, whitneyComp_base h₄, whitneyComp_base h₂]
      exact H.comp_assoc _ _ _ (base_composable h₁) (base_composable h₂)
    · rw [whitneyComp_vec h₃, whitneyComp_vec h₁, whitneyComp_vec h₄, whitneyComp_vec h₂]
      exact G.comp_assoc _ _ _ (vec_composable h₁ i) (vec_composable h₂ i)
  src_unit := whitneySrc_unit
  tgt_unit := whitneyTgt_unit
  comp_unit Φ := by
    have h : P.whitneySrc k Φ = P.whitneyTgt k (P.whitneyUnit k (P.whitneySrc k Φ)) :=
      (whitneyTgt_unit _).symm
    refine WhitneyMor.ext' ?_ (funext fun i => ?_)
    · rw [whitneyComp_base h]
      exact H.comp_unit _
    · rw [whitneyComp_vec h]
      exact G.comp_unit _
  unit_comp Φ := by
    have h : P.whitneySrc k (P.whitneyUnit k (P.whitneyTgt k Φ)) = P.whitneyTgt k Φ :=
      whitneySrc_unit _
    refine WhitneyMor.ext' ?_ (funext fun i => ?_)
    · rw [whitneyComp_base h]
      exact H.unit_comp _
    · rw [whitneyComp_vec h]
      exact G.unit_comp _
  src_inv := whitneySrc_inv
  tgt_inv := whitneyTgt_inv
  comp_inv Φ := by
    have h : P.whitneySrc k Φ = P.whitneyTgt k (P.whitneyInv k Φ) := (whitneyTgt_inv _).symm
    refine WhitneyMor.ext' ?_ (funext fun i => ?_)
    · rw [whitneyComp_base h]
      exact H.comp_inv _
    · rw [whitneyComp_vec h]
      exact G.comp_inv _
  inv_comp Φ := by
    have h : P.whitneySrc k (P.whitneyInv k Φ) = P.whitneyTgt k Φ := whitneySrc_inv _
    refine WhitneyMor.ext' ?_ (funext fun i => ?_)
    · rw [whitneyComp_base h]
      exact H.inv_comp _
    · rw [whitneyComp_vec h]
      exact G.inv_comp _

variable {P k}

/-- **Finitely many morphisms between two objects** of `⊕ᵏ_P G` if `G` and `H` have this
property. -/
theorem finite_whitneyMor (hG : ∀ x y, (G.mor x y).Finite) (hH : ∀ x y, (H.mor x y).Finite)
    (x y : P.WhitneyObj k) : ((P.whitneyGroupoid k).mor x y).Finite := by
  refine Set.Finite.of_finite_image (f := fun Φ : P.WhitneyMor k => (Φ.base, Φ.vec))
    (((hH x.base y.base).prod (Set.Finite.pi fun i => hG (x.vec i) (y.vec i))).subset ?_) ?_
  · rintro _ ⟨Φ, ⟨hs, ht⟩, rfl⟩
    refine ⟨⟨congrArg WhitneyObj.base hs, congrArg WhitneyObj.base ht⟩, fun i _ => ?_⟩
    exact ⟨congrFun (congrArg WhitneyObj.vec hs) i, congrFun (congrArg WhitneyObj.vec ht) i⟩
  · intro Φ _ Ψ _ h
    exact WhitneyMor.ext' (congrArg Prod.fst h) (congrArg Prod.snd h)

variable (P k)

/-- **The projection `⊕ᵏ P : ⊕ᵏ_P G → H`**, `(β, x₁, …, x_k) ↦ β`. -/
def whitneyProjFunctor : GroupoidFunctor (P.whitneyGroupoid k) H where
  obj x := x.base
  mor Φ := Φ.base
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ h := whitneyComp_base h
  mor_unit _ := rfl

/-- **The `i`-th component `⊕ᵏ_P G → G`**. -/
def whitneyComponent (i : Fin k) : GroupoidFunctor (P.whitneyGroupoid k) G where
  obj x := x.vec i
  mor Φ := Φ.vec i
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ h := whitneyComp_vec h i
  mor_unit _ := rfl

/-- `P ∘ (i-th component) = ⊕ᵏ P`. -/
theorem comp_whitneyComponent (i : Fin k) :
    P.comp (P.whitneyComponent k i) = P.whitneyProjFunctor k :=
  GroupoidFunctor.ext (funext fun x => x.obj_vec i) (funext fun Φ => Φ.mor_vec i)

variable {P k}

/-- **The functor into `⊕ᵏ_P G`** of a functor `F : D → H` and `k` functors `Tᵢ : D → G` with
`P ∘ Tᵢ = F`: `d ↦ (F(d), T₁(d), …, T_k(d))`. -/
def whitneyLift {ObjD MorD : Type w} {D : GroupoidStr ObjD MorD} (F : GroupoidFunctor D H)
    (T : Fin k → GroupoidFunctor D G) (hobj : ∀ i x, P.obj ((T i).obj x) = F.obj x)
    (hmor : ∀ i φ, P.mor ((T i).mor φ) = F.mor φ) : GroupoidFunctor D (P.whitneyGroupoid k) where
  obj x := ⟨F.obj x, fun i => (T i).obj x, fun i => hobj i x⟩
  mor φ := ⟨F.mor φ, fun i => (T i).mor φ, fun i => hmor i φ⟩
  src_mor φ := WhitneyObj.ext' (F.src_mor φ) (funext fun i => (T i).src_mor φ)
  tgt_mor φ := WhitneyObj.ext' (F.tgt_mor φ) (funext fun i => (T i).tgt_mor φ)
  mor_comp φ ψ h := by
    have hc : P.whitneySrc k ⟨F.mor φ, fun i => (T i).mor φ, fun i => hmor i φ⟩ =
        P.whitneyTgt k ⟨F.mor ψ, fun i => (T i).mor ψ, fun i => hmor i ψ⟩ := by
      refine WhitneyObj.ext' ?_ (funext fun i => ?_)
      · change H.src (F.mor φ) = H.tgt (F.mor ψ)
        rw [F.src_mor, F.tgt_mor, h]
      · change G.src ((T i).mor φ) = G.tgt ((T i).mor ψ)
        rw [(T i).src_mor, (T i).tgt_mor, h]
    refine WhitneyMor.ext' ?_ (funext fun i => ?_)
    · change F.mor (D.comp φ ψ) = (P.whitneyComp k _ _).base
      rw [whitneyComp_base hc]
      exact F.mor_comp φ ψ h
    · change (T i).mor (D.comp φ ψ) = (P.whitneyComp k _ _).vec i
      rw [whitneyComp_vec hc]
      exact (T i).mor_comp φ ψ h
  mor_unit x := WhitneyMor.ext' (F.mor_unit x) (funext fun i => (T i).mor_unit x)

theorem whitneyProjFunctor_comp_whitneyLift {ObjD MorD : Type w} {D : GroupoidStr ObjD MorD}
    (F : GroupoidFunctor D H) (T : Fin k → GroupoidFunctor D G)
    (hobj : ∀ i x, P.obj ((T i).obj x) = F.obj x) (hmor : ∀ i φ, P.mor ((T i).mor φ) = F.mor φ) :
    (P.whitneyProjFunctor k).comp (whitneyLift F T hobj hmor) = F := rfl

theorem whitneyComponent_comp_whitneyLift {ObjD MorD : Type w} {D : GroupoidStr ObjD MorD}
    (F : GroupoidFunctor D H) (T : Fin k → GroupoidFunctor D G)
    (hobj : ∀ i x, P.obj ((T i).obj x) = F.obj x) (hmor : ∀ i φ, P.mor ((T i).mor φ) = F.mor φ)
    (i : Fin k) : (P.whitneyComponent k i).comp (whitneyLift F T hobj hmor) = T i := rfl

variable (P)

/-- **`⊕⁰_P G = H`**: the projection of the `0`-fold power is bijective on objects and on
morphisms. -/
theorem bijective_whitneyProj_zero :
    Bijective (P.whitneyProjFunctor 0).obj ∧ Bijective (P.whitneyProjFunctor 0).mor :=
  ⟨⟨fun _ _ h => WhitneyObj.ext' h (funext fun i => i.elim0),
      fun β => ⟨⟨β, fun i => i.elim0, fun i => i.elim0⟩, rfl⟩⟩,
    ⟨fun _ _ h => WhitneyMor.ext' h (funext fun i => i.elim0),
      fun ψ => ⟨⟨ψ, fun i => i.elim0, fun i => i.elim0⟩, rfl⟩⟩⟩

/-- **`⊕¹_P G = G`**: the component of the `1`-fold power is bijective on objects and on
morphisms. -/
theorem bijective_whitneyComponent_one :
    Bijective (P.whitneyComponent 1 0).obj ∧ Bijective (P.whitneyComponent 1 0).mor := by
  refine ⟨⟨fun x y h => ?_, fun e => ⟨⟨P.obj e, fun _ => e, fun _ => rfl⟩, rfl⟩⟩,
    ⟨fun Φ Ψ h => ?_, fun φ => ⟨⟨P.mor φ, fun _ => φ, fun _ => rfl⟩, rfl⟩⟩⟩
  · have hv : x.vec = y.vec := funext fun i => by
      rw [Subsingleton.elim i 0]; exact h
    refine WhitneyObj.ext' ?_ hv
    rw [← x.obj_vec 0, ← y.obj_vec 0, hv]
  · have hv : Φ.vec = Ψ.vec := funext fun i => by
      rw [Subsingleton.elim i 0]; exact h
    refine WhitneyMor.ext' ?_ hv
    rw [← Φ.mor_vec 0, ← Ψ.mor_vec 0, hv]

end GroupoidFunctor

/-! ### The category `⊕ᵏ TC` -/

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} (S : C.PolyfoldConstruction)

/-- **The groupoid `⊕ᵏ TC`** (2021 pp. 817–818): the `k`-fold fibred power of the projection
`P : TC → C¹` over `C¹`. -/
abbrev whitneyCatGroupoid (k : ℕ) :
    GroupoidStr (S.tangentCatProj.WhitneyObj k) (S.tangentCatProj.WhitneyMor k) :=
  S.tangentCatProj.whitneyGroupoid k

/-- `C¹` has finitely many morphisms between two objects. -/
theorem finite_regSubMor (x y : S.regSet 1) : ((S.regSub 1).mor x y).Finite := by
  refine Set.Finite.of_finite_image ((C.finite_mor x.1 y.1).subset ?_)
    Subtype.val_injective.injOn
  rintro _ ⟨φ, ⟨hs, ht⟩, rfl⟩
  exact ⟨congrArg Subtype.val hs, congrArg Subtype.val ht⟩

/-- **The category `⊕ᵏ TC`** (2021 p. 819, "clearly, `⊕ᵏ TC` is a GCT"): a groupoidal category
(finitely many morphisms between two objects), in the universe `max u 1` of `TC`. -/
def whitneyCategory (k : ℕ) : GroupoidalCategory.{max u 1} where
  Obj := S.tangentCatProj.WhitneyObj k
  Mor := S.tangentCatProj.WhitneyMor k
  toGroupoidStr := S.whitneyCatGroupoid k
  finite_mor := GroupoidFunctor.finite_whitneyMor S.finite_tangentCatMor S.finite_regSubMor

/-- **The projection `⊕ᵏ P : ⊕ᵏ TC → C¹`** (2021 p. 818). -/
abbrev whitneyCatProj (k : ℕ) : GroupoidFunctor (S.whitneyCatGroupoid k) (S.regSub 1) :=
  S.tangentCatProj.whitneyProjFunctor k

/-- **`⊕⁰ TC = C¹`**: `⊕⁰ P` is bijective on objects and morphisms. -/
theorem whitneyCatProj_zero_bijective :
    Bijective (S.whitneyCatProj 0).obj ∧ Bijective (S.whitneyCatProj 0).mor :=
  S.tangentCatProj.bijective_whitneyProj_zero

/-- **`⊕¹ TC = TC`**: the component `⊕¹ TC → TC` is bijective on objects and morphisms. -/
theorem whitneyComponent_one_bijective :
    Bijective (S.tangentCatProj.whitneyComponent 1 0).obj ∧
      Bijective (S.tangentCatProj.whitneyComponent 1 0).mor :=
  S.tangentCatProj.bijective_whitneyComponent_one

/-! ### The functors `⊕ᵏ TΨ` -/

/-- **`G ⋉ ⊕ᵏ TO`** (2021 p. 818): the translation groupoid of `G` acting on `⊕ᵏ TO` by
`g ∗ (h₁, …, h_k) = (T(g ∗ ·)h₁, …, T(g ∗ ·)h_k)` (through `ULift G`, which only matches
universes). -/
abbrev whitneyTranslation (Ψ : S.Unif) (k : ℕ) :
    GroupoidStr (Ψ.1.P.WhitneySum k) (ULift.{1} Ψ.1.G × Ψ.1.P.WhitneySum k) :=
  GroupoidStr.translation (ULift.{1} Ψ.1.G) (Ψ.1.P.WhitneySum k)

/-- The `i`-th vector `G ⋉ ⊕ᵏ TO → G ⋉ TO`, `(g, (h₁, …, h_k)) ↦ (g, hᵢ)`. -/
def whitneyVecFunctor (Ψ : S.Unif) (k : ℕ) (i : Fin k) :
    GroupoidFunctor (S.whitneyTranslation Ψ k) (S.tangentTranslation Ψ) where
  obj v := MPolyfold.whitneyVec v i
  mor p := (p.1, MPolyfold.whitneyVec p.2 i)
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ _ := rfl
  mor_unit _ := rfl

/-- `Ψ(x) ∈ C¹` for `x ∈ O¹`. -/
theorem obj_levelVal_mem (Ψ : S.Unif) (x : Ψ.1.P.Level 1) :
    Ψ.1.obj (Ψ.1.P.levelVal 1 x) ∈ S.regSet 1 :=
  ⟨Ψ, _, C.toGroupoidStr.isomorphic_refl _, MPolyfold.levelVal_mem _⟩

/-- **`Ψ¹ ∘ ⊕ᵏ p : G ⋉ ⊕ᵏ TO → C¹`**, `(g, (h₁, …, h_k)) ↦ Ψ(g, x)`, `x` the base point. -/
def whitneyBaseFunctor (Ψ : S.Unif) (k : ℕ) :
    GroupoidFunctor (S.whitneyTranslation Ψ k) (S.regSub 1) where
  obj v := ⟨Ψ.1.obj (Ψ.1.P.levelVal 1 (MPolyfold.whitneyProj v)), S.obj_levelVal_mem Ψ _⟩
  mor p := ⟨Ψ.1.mor (p.1.down, Ψ.1.P.levelVal 1 (MPolyfold.whitneyProj p.2)), by
      rw [Ψ.1.src_mor]; exact S.obj_levelVal_mem Ψ _, by
      rw [Ψ.1.tgt_mor]
      exact S.obj_levelVal_mem Ψ (MPolyfold.whitneyProj (p.1 • p.2))⟩
  src_mor p := Subtype.ext (Ψ.1.src_mor _)
  tgt_mor p := Subtype.ext (Ψ.1.tgt_mor _)
  mor_comp p p' h := by
    have hq : Ψ.1.P.levelVal 1 (MPolyfold.whitneyProj p.2) =
        p'.1.down • Ψ.1.P.levelVal 1 (MPolyfold.whitneyProj p'.2) := by
      rw [show p.2 = p'.1 • p'.2 from h]
      rfl
    have hm : C.toGroupoidStr.src (Ψ.1.mor (p.1.down, Ψ.1.P.levelVal 1
        (MPolyfold.whitneyProj p.2))) = C.toGroupoidStr.tgt (Ψ.1.mor (p'.1.down,
          Ψ.1.P.levelVal 1 (MPolyfold.whitneyProj p'.2))) := by
      rw [Ψ.1.src_mor, Ψ.1.tgt_mor]; exact congrArg Ψ.1.obj hq
    refine Subtype.ext ?_
    change Ψ.1.mor ((p.1 * p'.1).down, Ψ.1.P.levelVal 1 (MPolyfold.whitneyProj p'.2)) =
      ((C.toGroupoidStr.fullSub (S.regSet 1)).comp _ _).1
    simp only [GroupoidStr.fullSub, dif_pos hm]
    rw [hq]
    exact Ψ.1.functor.mor_comp (p.1.down, p'.1.down • Ψ.1.P.levelVal 1
      (MPolyfold.whitneyProj p'.2)) (p'.1.down, Ψ.1.P.levelVal 1 (MPolyfold.whitneyProj p'.2)) rfl
  mor_unit v := Subtype.ext (Ψ.1.functor.mor_unit _)

/-- `P ∘ TΨ ∘ (i-th vector) = Ψ¹ ∘ ⊕ᵏ p` on objects. -/
theorem tangentCatProj_whitneyUnif_obj (hU : S.HasUniformizers) (Ψ : S.Unif)
    (hc : Continuous (S.hat Ψ)) (k : ℕ) (i : Fin k) (v : Ψ.1.P.WhitneySum k) :
    S.tangentCatProj.obj (((S.tangentUnifFunctor hU Ψ hc).comp (S.whitneyVecFunctor Ψ k i)).obj v) =
      (S.whitneyBaseFunctor Ψ k).obj v :=
  Subtype.ext (congrArg (fun y => Ψ.1.obj (Ψ.1.P.levelVal 1 y))
    (MPolyfold.tangentProj_whitneyVec v i))

/-- `P ∘ TΨ ∘ (i-th vector) = Ψ¹ ∘ ⊕ᵏ p` on morphisms. -/
theorem tangentCatProj_whitneyUnif_mor (hU : S.HasUniformizers) (Ψ : S.Unif)
    (hc : Continuous (S.hat Ψ)) (k : ℕ) (i : Fin k)
    (p : ULift.{1} Ψ.1.G × Ψ.1.P.WhitneySum k) :
    S.tangentCatProj.mor (((S.tangentUnifFunctor hU Ψ hc).comp (S.whitneyVecFunctor Ψ k i)).mor p) =
      (S.whitneyBaseFunctor Ψ k).mor p :=
  Subtype.ext (congrArg (fun y => Ψ.1.mor (p.1.down, Ψ.1.P.levelVal 1 y))
    (MPolyfold.tangentProj_whitneyVec p.2 i))

/-- **The functor `⊕ᵏ TΨ : G ⋉ ⊕ᵏ TO → ⊕ᵏ TC`** (2021 p. 818, proof of Proposition 17.6.1), for
continuous `Ψ̂`: `(h₁, …, h_k) ↦ (TΨ(h₁), …, TΨ(h_k))` over `Ψ(x)`, and
`(g, (h₁, …, h_k)) ↦ ((TΨ(h₁), Ψ(g, x), ·), …, (TΨ(h_k), Ψ(g, x), ·))` over `Ψ(g, x)`. -/
def whitneyUnifFunctor (hU : S.HasUniformizers) (Ψ : S.Unif) (hc : Continuous (S.hat Ψ))
    (k : ℕ) : GroupoidFunctor (S.whitneyTranslation Ψ k) (S.whitneyCatGroupoid k) :=
  GroupoidFunctor.whitneyLift (S.whitneyBaseFunctor Ψ k)
    (fun i => (S.tangentUnifFunctor hU Ψ hc).comp (S.whitneyVecFunctor Ψ k i))
    (S.tangentCatProj_whitneyUnif_obj hU Ψ hc k) (S.tangentCatProj_whitneyUnif_mor hU Ψ hc k)

variable (hU : S.HasUniformizers) (Ψ : S.Unif) (hc : Continuous (S.hat Ψ)) {k : ℕ}

/-- `(⊕ᵏ TΨ)(h₁, …, h_k)ᵢ = TΨ(hᵢ)`. -/
theorem whitneyUnifFunctor_obj_vec (v : Ψ.1.P.WhitneySum k) (i : Fin k) :
    ((S.whitneyUnifFunctor hU Ψ hc k).obj v).vec i =
      S.tangentUnifObj hU Ψ (MPolyfold.whitneyVec v i) := rfl

/-- `(⊕ᵏ TΨ)(h₁, …, h_k)` lies over `Ψ(x)`. -/
theorem whitneyUnifFunctor_obj_base (v : Ψ.1.P.WhitneySum k) :
    ((S.whitneyUnifFunctor hU Ψ hc k).obj v).base.1 =
      Ψ.1.obj (Ψ.1.P.levelVal 1 (MPolyfold.whitneyProj v)) := rfl

/-- `(⊕ᵏ TΨ)(g, (h₁, …, h_k))ᵢ = (TΨ(hᵢ), Ψ(g, x), T(Ψ(g, x))(TΨ(hᵢ)))`. -/
theorem whitneyUnifFunctor_mor_vec (p : ULift.{1} Ψ.1.G × Ψ.1.P.WhitneySum k) (i : Fin k) :
    ((S.whitneyUnifFunctor hU Ψ hc k).mor p).vec i =
      S.tangentUnifMor hU Ψ (p.1, MPolyfold.whitneyVec p.2 i) := rfl

/-- `(⊕ᵏ TΨ)(g, (h₁, …, h_k))` lies over `Ψ(g, x)`. -/
theorem whitneyUnifFunctor_mor_base (p : ULift.{1} Ψ.1.G × Ψ.1.P.WhitneySum k) :
    ((S.whitneyUnifFunctor hU Ψ hc k).mor p).base.1 =
      Ψ.1.mor (p.1.down, Ψ.1.P.levelVal 1 (MPolyfold.whitneyProj p.2)) := rfl

/-- **The square of Proposition 17.6.1**: `⊕ᵏ P ∘ ⊕ᵏ TΨ = Ψ¹ ∘ ⊕ᵏ p`. -/
theorem whitneyCatProj_comp_whitneyUnifFunctor :
    (S.whitneyCatProj k).comp (S.whitneyUnifFunctor hU Ψ hc k) = S.whitneyBaseFunctor Ψ k := rfl

/-- The components of `⊕ᵏ TΨ` are `TΨ ∘ (i-th vector)`. -/
theorem whitneyComponent_comp_whitneyUnifFunctor (i : Fin k) :
    (S.tangentCatProj.whitneyComponent k i).comp (S.whitneyUnifFunctor hU Ψ hc k) =
      (S.tangentUnifFunctor hU Ψ hc).comp (S.whitneyVecFunctor Ψ k i) := rfl

/-- **`(g, (h₁, …, h_k)) : (h₁, …, h_k) → (g ∗ h₁, …, g ∗ h_k)` goes to a morphism from
`⊕ᵏ TΨ(h₁, …, h_k)` to `⊕ᵏ TΨ(g ∗ h₁, …, g ∗ h_k)`** (from (17.40) for each `hᵢ`). -/
theorem whitneyUnifFunctor_tgt (p : ULift.{1} Ψ.1.G × Ψ.1.P.WhitneySum k) :
    (S.whitneyCatGroupoid k).src ((S.whitneyUnifFunctor hU Ψ hc k).mor p) =
        (S.whitneyUnifFunctor hU Ψ hc k).obj p.2 ∧
      (S.whitneyCatGroupoid k).tgt ((S.whitneyUnifFunctor hU Ψ hc k).mor p) =
        (S.whitneyUnifFunctor hU Ψ hc k).obj (p.1 • p.2) :=
  ⟨(S.whitneyUnifFunctor hU Ψ hc k).src_mor p, (S.whitneyUnifFunctor hU Ψ hc k).tgt_mor p⟩

/-- **Proposition 17.6.1, the category `⊕ᵏ TC` and the functors `⊕ᵏ TΨ`** (2021 pp. 818–819), for
continuous `Ψ̂`: `⊕ᵏ TC` is a groupoidal category; `⊕ᵏ TΨ : G ⋉ ⊕ᵏ TO → ⊕ᵏ TC` is a functor with
`(⊕ᵏ TΨ)(h₁, …, h_k) = (TΨ(h₁), …, TΨ(h_k))` and
`(⊕ᵏ TΨ)(g, (h₁, …, h_k))ᵢ = (TΨ(hᵢ), Ψ(g, x), T(Ψ(g, x))(TΨ(hᵢ)))`; it maps
`(g, (h₁, …, h_k))` to a morphism ending at `⊕ᵏ TΨ(g ∗ h₁, …, g ∗ h_k)`; and it covers `Ψ¹`:
`⊕ᵏ P ∘ ⊕ᵏ TΨ = Ψ¹ ∘ ⊕ᵏ p`. -/
theorem proposition_17_6_1_functor :
    (S.whitneyCategory k).toGroupoidStr = S.whitneyCatGroupoid k ∧
      (∀ x y : (S.whitneyCategory k).Obj, ((S.whitneyCategory k).toGroupoidStr.mor x y).Finite) ∧
      (∀ v i, ((S.whitneyUnifFunctor hU Ψ hc k).obj v).vec i =
        S.tangentUnifObj hU Ψ (MPolyfold.whitneyVec v i)) ∧
      (∀ p i, ((S.whitneyUnifFunctor hU Ψ hc k).mor p).vec i =
        S.tangentUnifMor hU Ψ (p.1, MPolyfold.whitneyVec p.2 i)) ∧
      (∀ p, (S.whitneyCatGroupoid k).tgt ((S.whitneyUnifFunctor hU Ψ hc k).mor p) =
        (S.whitneyUnifFunctor hU Ψ hc k).obj (p.1 • p.2)) ∧
      (S.whitneyCatProj k).comp (S.whitneyUnifFunctor hU Ψ hc k) = S.whitneyBaseFunctor Ψ k :=
  ⟨rfl, (S.whitneyCategory k).finite_mor, fun _ _ => rfl, fun _ _ => rfl,
    fun p => (S.whitneyUnifFunctor_tgt hU Ψ hc p).2, rfl⟩

end GCT.PolyfoldConstruction

/-! ### The witness: `k = 2` on the reflection -/

section Reflection

open GCT GCT.PolyfoldConstruction EpGroupoid.Examples MPolyfold

/-- **The witness of `whitneyUnifFunctor`**: on the reflection `ℤ/2 ⋉ ℝ` (continuous `Ψ̂`),
`⊕² TΨ₀(−1, (e, e))` is a morphism of `⊕² TC` from `⊕² TΨ₀(e, e)` to `⊕² TΨ₀(−e, −e)`, and these
two objects differ. -/
theorem reflection_whitneyUnif_nondegenerate :
    let F := reflectionConstruction.whitneyUnifFunctor reflectionConstruction_hasUniformizers
      reflectionUnif reflection_continuous_hat 2
    (reflectionConstruction.whitneyCatGroupoid 2).src (F.mor (ULift.up reflNegOne, reflWhitneyVec))
      ≠ (reflectionConstruction.whitneyCatGroupoid 2).tgt
        (F.mor (ULift.up reflNegOne, reflWhitneyVec)) := by
  intro F h
  rw [F.src_mor, F.tgt_mor] at h
  apply reflection_whitney_smul_ne
  have hv : ∀ i, whitneyVec (whitneyMapOf (reflectionUnif.1.smooth_smul reflNegOne)
      reflWhitneyVec) i = whitneyVec reflWhitneyVec i := fun i =>
    (injective_tangentUnifObj reflectionConstruction_hasUniformizers reflectionUnif
      (congrFun (congrArg GroupoidFunctor.WhitneyObj.vec h) i)).symm
  refine whitneySum_ext ?_ hv
  rw [← tangentProj_whitneyVec _ 0, ← tangentProj_whitneyVec _ 0, hv 0]

end Reflection

end Polyfold
