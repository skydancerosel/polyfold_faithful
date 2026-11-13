import Polyfold.Chapter13.P3D_Tight

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.3, tools for **Proposition 13.3.19** (p. 620; 2017: Proposition 13.5).

# Products of families of correspondences

The proof of Proposition 13.3.19 takes, for a locally finite family `(Λ_l)_{l ∈ L}`, the index
sets `K_x = ∏_{l ∈ L} K^l_x` and the correspondences `τ_{x,x'} = ∏_{l ∈ L} τ^l_{x,x'}`, where all
but finitely many factors are one-point sets (and the unit diagram `{∗} ← {∗} → {∗}`).  The text
leaves the check that this product is well defined to the reader.  Here:

* `IndexDiagram.pi`: the product `∏_l I^l_x ← ∏_l I^l → ∏_l I^l_{x'}` of a family of diagrams with
  finite product of middle sets (`card_fiber_pi`: the fibres of a product map have equal size).
* `IndexCorr.pi`: the product of a family of correspondences, through representatives;
  `pi_eq_mk` (any family of representatives gives the same class), `pi_congr`, `sat_pi`,
  `swap_pi`, `biact_pi`, `pi_ofPerm`.
* `finite_pi_of_subsingleton`: a product of finite types which are one-point outside a finite set
  is finite; `subsingleton_out_I`.
* `SymmetricStructureOn.reindex`: a symmetric structure relabelled along an equivariant bijection
  of index sets.
* `fibAct_sum`: `μ(ψ, ∑ vₗ) = ∑ μ(ψ, vₗ)` on fibres.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

/-! ### Finiteness of products -/

/-- A product of finite types which are subsingletons outside a finite set `S` is finite. -/
theorem finite_pi_of_subsingleton {L : Type*} {F : L → Type*} (S : Finset L)
    [∀ l, Finite (F l)] (h : ∀ l ∉ S, Subsingleton (F l)) : Finite (∀ l, F l) := by
  refine Finite.of_injective (fun k (l : S) => k l) fun k k' e => funext fun l => ?_
  by_cases hl : l ∈ S
  · exact congrFun e ⟨l, hl⟩
  · exact (h l hl).elim _ _

namespace IndexDiagram

variable {L : Type u} {α β : L → Type u}

/-- The fibres of a product map have equal size if the fibres of every factor do. -/
theorem card_fiber_pi {γ : L → Type u} {I : L → Type u} [∀ l, Finite (I l)]
    (f : ∀ l, I l → γ l) (hf : ∀ l i i', Nat.card {k // f l k = i} = Nat.card {k // f l k = i'})
    (i i' : ∀ l, γ l) :
    Nat.card {k : ∀ l, I l // (fun l => f l (k l)) = i} =
      Nat.card {k : ∀ l, I l // (fun l => f l (k l)) = i'} := by
  have e : ∀ i : ∀ l, γ l,
      {k : ∀ l, I l // (fun l => f l (k l)) = i} ≃ ∀ l, {k // f l k = i l} := fun i =>
    (_root_.Equiv.subtypeEquivRight fun _ => funext_iff).trans
      (_root_.Equiv.subtypePiEquivPi (p := fun l k => f l k = i l))
  rw [Nat.card_congr (e i), Nat.card_congr (e i')]
  exact Nat.card_congr (_root_.Equiv.piCongrRight fun l =>
    (Finite.card_eq.1 (hf l (i l) (i' l))).some)

/-- **The product of a family of diagrams** `∏_l I^l_x ← ∏_l I^l → ∏_l I^l_{x'}` (proof of
Proposition 13.3.19), for a family whose product of middle sets is finite. -/
def pi (d : ∀ l, IndexDiagram (α l) (β l)) (h : Finite (∀ l, (d l).I)) :
    IndexDiagram (∀ l, α l) (∀ l, β l) where
  I := ∀ l, (d l).I
  fintype := haveI := h; Fintype.ofFinite _
  a k l := (d l).a (k l)
  b k l := (d l).b (k l)
  surjective_a i := ⟨fun l => ((d l).surjective_a (i l)).choose,
    funext fun l => ((d l).surjective_a (i l)).choose_spec⟩
  surjective_b j := ⟨fun l => ((d l).surjective_b (j l)).choose,
    funext fun l => ((d l).surjective_b (j l)).choose_spec⟩
  uniform_a i i' := card_fiber_pi (fun l => (d l).a) (fun l => (d l).uniform_a) i i'
  uniform_b j j' := card_fiber_pi (fun l => (d l).b) (fun l => (d l).uniform_b) j j'

end IndexDiagram

namespace IndexCorr

variable {L : Type u} {α β : L → Type u}

/-- A representative of a correspondence. -/
def out {α' β' : Type u} (τ : IndexCorr α' β') : IndexDiagram α' β' := Quotient.out τ

theorem mk_out {α' β' : Type u} (τ : IndexCorr α' β') : mk τ.out = τ := Quotient.out_eq τ

/-- The middle set of any representative of the class of a diagram with one-point middle set is
a subsingleton. -/
theorem subsingleton_out_I {α' β' : Type u} {τ : IndexCorr α' β'} (d : IndexDiagram α' β')
    (hd : mk d = τ) [Subsingleton d.I] : Subsingleton τ.out.I := by
  obtain ⟨c, -⟩ := mk_eq_mk.1 ((mk_out τ).trans hd.symm)
  exact c.subsingleton

/-- **The product of a family of correspondences** `∏_l τ^l` (proof of Proposition 13.3.19),
through representatives, for a family whose middle sets have a finite product. -/
def pi (τ : ∀ l, IndexCorr (α l) (β l)) (h : Finite (∀ l, (τ l).out.I)) :
    IndexCorr (∀ l, α l) (∀ l, β l) :=
  mk (IndexDiagram.pi (fun l => (τ l).out) h)

/-- **The product does not depend on the representatives.** -/
theorem pi_eq_mk (τ : ∀ l, IndexCorr (α l) (β l)) (h : Finite (∀ l, (τ l).out.I))
    (d : ∀ l, IndexDiagram (α l) (β l)) (hd : ∀ l, mk (d l) = τ l)
    (h' : Finite (∀ l, (d l).I)) : pi τ h = mk (IndexDiagram.pi d h') := by
  have hc : ∀ l, (τ l).out ≈ d l := fun l => mk_eq_mk.1 ((mk_out _).trans (hd l).symm)
  refine mk_eq_mk.2 ⟨_root_.Equiv.piCongrRight fun l => (hc l).choose, fun k => ⟨?_, ?_⟩⟩
  · exact funext fun l => ((hc l).choose_spec (k l)).1
  · exact funext fun l => ((hc l).choose_spec (k l)).2

theorem pi_congr {τ τ' : ∀ l, IndexCorr (α l) (β l)} (hτ : ∀ l, τ l = τ' l)
    (h : Finite (∀ l, (τ l).out.I)) (h' : Finite (∀ l, (τ' l).out.I)) : pi τ h = pi τ' h' := by
  obtain rfl : τ = τ' := funext hτ
  rfl

/-- A condition on the pairs `(a(k), b(k))` holds for the product if the factor conditions do. -/
theorem sat_pi {τ : ∀ l, IndexCorr (α l) (β l)} (h : Finite (∀ l, (τ l).out.I))
    {R : (∀ l, α l) → (∀ l, β l) → Prop} (Rl : ∀ l, α l → β l → Prop)
    (hR : ∀ i j, (∀ l, Rl l (i l) (j l)) → R i j) (hτ : ∀ l, (τ l).Sat (Rl l)) :
    (pi τ h).Sat R :=
  fun k => hR _ _ fun l => (sat_iff _ _).1 (hτ l) _ (mk_out _) (k l)

/-- **The pseudo-inverse of a product** is the product of the pseudo-inverses. -/
theorem swap_pi (τ : ∀ l, IndexCorr (α l) (β l)) (h : Finite (∀ l, (τ l).out.I))
    (h' : Finite (∀ l, ((τ l).swap).out.I)) :
    (pi τ h).swap = pi (fun l => (τ l).swap) h' := by
  refine Eq.trans ?_ (pi_eq_mk _ h' (fun l => (τ l).out.swap)
    (fun l => (congrArg swap (mk_out (τ l)) :)) h).symm
  exact mk_eq_mk.2 ⟨_root_.Equiv.refl _, fun _ => ⟨rfl, rfl⟩⟩

/-- **The bi-action on a product** (with the componentwise actions) is the product of the
bi-actions. -/
theorem biact_pi {G G' : Type*} [Group G] [Group G'] [∀ l, MulAction G (α l)]
    [∀ l, MulAction G' (β l)] (g' : G') (g : G) (τ : ∀ l, IndexCorr (α l) (β l))
    (h : Finite (∀ l, (τ l).out.I)) (h' : Finite (∀ l, (biact g' (τ l) g).out.I)) :
    biact g' (pi τ h) g = pi (fun l => biact g' (τ l) g) h' := by
  refine Eq.trans ?_ (pi_eq_mk _ h'
    (fun l => (τ l).out.map (MulAction.toPerm g⁻¹) (MulAction.toPerm g'))
    (fun l => (congrArg (map (MulAction.toPerm g⁻¹) (MulAction.toPerm g')) (mk_out (τ l)) :))
    h).symm
  exact mk_eq_mk.2 ⟨_root_.Equiv.refl _, fun _ => ⟨rfl, rfl⟩⟩

/-- **A product of `[I ←id I →g I]`** is `[∏ I ←id ∏ I →g ∏ I]` (componentwise action). -/
theorem pi_ofPerm {G : Type*} [Group G] [∀ l, Fintype (α l)] [∀ l, MulAction G (α l)]
    [Fintype (∀ l, α l)] (g : G) (τ : ∀ l, IndexCorr (α l) (α l))
    (hτ : ∀ l, τ l = ofPerm g) (h : Finite (∀ l, (τ l).out.I)) :
    pi τ h = (ofPerm g : IndexCorr (∀ l, α l) (∀ l, α l)) := by
  have hfin : Finite (∀ l, (IndexDiagram.ofEquiv (MulAction.toPerm (α := G) (β := α l) g)).I) :=
    inferInstanceAs (Finite (∀ l, α l))
  refine (pi_eq_mk τ h _ (fun l => (hτ l).symm) hfin).trans ?_
  exact mk_eq_mk.2 ⟨_root_.Equiv.refl _, fun _ => ⟨rfl, rfl⟩⟩

end IndexCorr

variable {A : SEP.{u}}

/-! ### Relabelling a symmetric structure -/

namespace SymmetricStructureOn

variable {Λ : A.W → ℚ≥0} {x : A.Obj} {N : A.X.NatNbhd x}

/-- **Relabelling** a symmetric structure along a `G_x`-equivariant bijection `e : I' ≃ I`:
the sections `s'_κ = s_{e(κ)}`. -/
def reindex (S : SymmetricStructureOn A Λ N) (I' : Type u) [Fintype I']
    [MulAction (A.X.Isotropy x) I'] (e : I' ≃ S.I)
    (he : ∀ (g : A.X.Isotropy x) κ, e (g • κ) = g • e κ) : SymmetricStructureOn A Λ N where
  I := I'
  s κ := S.s (e κ)
  isScPlusSectionOn κ := S.isScPlusSectionOn (e κ)
  equivariant g κ y hy := by
    rw [he]
    exact S.equivariant g (e κ) y hy
  rep w hw := (S.rep w hw).trans (count_reindex e (fun _ => rfl) w).symm

@[simp] theorem reindex_s (S : SymmetricStructureOn A Λ N) (I' : Type u) [Fintype I']
    [MulAction (A.X.Isotropy x) I'] (e : I' ≃ S.I)
    (he : ∀ (g : A.X.Isotropy x) κ, e (g • κ) = g • e κ) (κ : I') :
    (S.reindex I' e he).s κ = S.s (e κ) := rfl

end SymmetricStructureOn

/-! ### `μ(ψ, ·)` on finite sums -/

/-- `μ(ψ, ∑ₗ vₗ) = ∑ₗ μ(ψ, vₗ)` over the fibre of `s(ψ)`. -/
theorem fibAct_sum {ι : Type*} (T : Finset ι) {ψ : A.Mor} {y y' : A.Obj} (hy : A.X.src ψ = y)
    (hy' : A.X.tgt ψ = y') (v : ι → A.P ⁻¹' {y}) :
    fibAct ψ ((∑ l ∈ T, v l : A.P ⁻¹' {y}) : A.W) =
      ((∑ l ∈ T, ⟨fibAct ψ (v l), (P_fibAct ((v l).2.trans hy.symm)).trans hy'⟩ :
        A.P ⁻¹' {y'}) : A.W) := by
  subst hy hy'
  rw [fibAct_of ((∑ l ∈ T, v l : A.P ⁻¹' {A.X.src ψ})).2]
  have e := A.E.fiberMor_apply ψ (∑ l ∈ T, v l)
  rw [map_sum] at e
  refine e.symm.trans ?_
  congr 1
  refine Finset.sum_congr rfl fun l _ => Subtype.ext ?_
  rw [A.E.fiberMor_apply]
  exact (fibAct_of (v l).2).symm

end SBLocalization

end Polyfold
