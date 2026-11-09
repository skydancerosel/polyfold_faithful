import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_54

/-! Round trip for V10_54 (2021 §10.5, p. 505: the homomorphism `γ : G_x → G'_{x'}`, the
equivariant germ `q` and its lift `Q` (10.25)).

The item lists the definition `Diagram.isotropyHom` (`γ`, vocabulary) and three theorems; `A` is
the conjunction of their types, universes at `0`, all for an arbitrary diagram
`d : X ←φ X'' →ψ X'` of ep-groupoids (`X Y : EP`):
`isotropyHom_spec` (`γ(g) = b ∘ ψ(k) ∘ b⁻¹` for the `k` with `φ(k) = a⁻¹ ∘ g ∘ a`),
`bijective_isotropyHom` (`γ` is bijective if `ψ` is an equivalence) and `exists_isotropyData`
(if `|[d]|(|x|) = |x'|` there are `x''`, `a`, `b`).

`B` is stated for the diagram of bases of a diagram `D` of strong bundles and has three parts:
(i) the data `x''`, `a`, `b` exist; (ii) for each choice, `φ : G_{x''} → G_{φ(x'')}` is bijective
and there is a homomorphism `γ` with B's formula; (iii) natural representations `R`, `R'`, an
open `O ∋ x` and an equivariant germ `q` (sc-smooth, representing `|[d]|`) with a lift `Q`, a
strong bundle map over `O` representing `|[D]|` and equivariant for the natural lifts.

* `A → B` is **not proved**.  `A` has nothing on (iii): the project lists the germ `q` and its
  lift `Q` as not formalized (module docstring of `StrongBundleLocalization.lean`).  We prove
  exactly the rest: `Bii` is `B` with (iii) dropped, and `A_to_Bii : A → Bii` (from
  `exists_isotropyData` and `isotropyHom_spec`; the uniqueness of `k` from the injectivity of
  `φ` on isotropy groups, `EpFunctor.IsEquivalence.bijective_isotropyHom`, not an item theorem;
  B's `a⁻¹ ∘ (g ∘ a)` and `b ∘ (ψ(k) ∘ b⁻¹)` versus the project's left-bracketed forms by
  `comp_assoc`).  `B_to_Bii` shows `Bii` is a weakening of `B`.  Constructing `q` and `Q`
  (local inverses of `φ`, `Φ`, translation by the sheets through `a`, `b`, uniqueness of
  morphisms near `γ(g)` for the equivariance, and the strong bundle structure maps for `Q`) is
  new mathematics, not glue.
* `B → A` is proved only **outright** (`uses_hypothesis = false`): `A` concerns arbitrary
  diagrams of ep-groupoids and the project's specific `isotropyHom`, while `B` only speaks of
  base diagrams of strong bundle diagrams and of some `γ`; there is no construction in the
  project turning an ep-groupoid into a strong bundle over it (e.g. the zero bundle) through
  which `B` could be applied.  The three conjuncts are elementary and are re-proved from
  non-item project lemmas (the project's proofs, copied). -/

namespace RoundTrip.V10_54
open Polyfold CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EPLocalization.Diagram.isotropyHom_spec.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.bijective_isotropyHom.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.exists_isotropyData.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EPLocalization.Diagram.isotropyHom_spec.{0},
    @Polyfold.EPLocalization.Diagram.bijective_isotropyHom.{0},
    @Polyfold.EPLocalization.Diagram.exists_isotropyData.{0}⟩

/-- `B` without (iii), the germ `q` and its lift `Q`. -/
def Bii : Prop :=
  ∀ (A A' : SEP.{0}) (D : SBLocalization.SDiagram A A') (x : A.Obj) (x' : A'.Obj),
    (baseDiagB D).orbitMap (A.X.π x) = A'.X.π x' →
    (∃ (x'' : D.B.Obj) (a : A.Mor) (b : A'.Mor),
      A.X.src a = D.Φ.ϕ.obj x'' ∧ A.X.tgt a = x ∧
      A'.X.src b = D.Ψ.ϕ.obj x'' ∧ A'.X.tgt b = x') ∧
    ∀ (x'' : D.B.Obj) (a : A.Mor) (b : A'.Mor),
      A.X.src a = D.Φ.ϕ.obj x'' → A.X.tgt a = x →
      A'.X.src b = D.Ψ.ϕ.obj x'' → A'.X.tgt b = x' →
      Function.Bijective (D.Φ.ϕ.isotropyHom x'') ∧
      ∃ γ : A.X.Isotropy x →* A'.X.Isotropy x',
        ∀ (g : A.X.Isotropy x) (k : D.B.X.Isotropy x''),
          D.Φ.ϕ.mor k.val = A.X.comp (A.X.inv a) (A.X.comp g.val a) →
          (γ g).val = A'.X.comp b (A'.X.comp (D.Ψ.ϕ.mor k.val) (A'.X.inv b))

theorem B_to_Bii : B → Bii := by
  intro hB A A' D x x' h
  refine ⟨(hB A A' D x x' h).1, fun x'' a b ha ha' hb hb' => ?_⟩
  obtain ⟨h1, γ, hγ, -⟩ := (hB A A' D x x' h).2 x'' a b ha ha' hb hb'
  exact ⟨h1, γ, hγ⟩

theorem A_to_Bii : A → Bii := by
  rintro ⟨hspec, -, hex⟩ A A' D x x' h
  refine ⟨hex (baseDiagB D) h, fun x'' a b ha ha' hb hb' => ?_⟩
  have hbij : Function.Bijective (D.Φ.ϕ.isotropyHom x'') :=
    (baseDiagB D).isEquivalence_F.bijective_isotropyHom x''
  refine ⟨hbij, (baseDiagB D).isotropyHom a ha ha' b hb hb', fun g k hk => ?_⟩
  obtain ⟨k₀, hk₀, hγ⟩ := hspec (baseDiagB D) a ha ha' b hb hb' g
  have e₁ : A.X.src (A.X.inv a) = A.X.tgt g.val := by
    rw [GroupoidStr.src_inv, ha', g.tgt_val]
  have e₂ : A.X.src g.val = A.X.tgt a := by rw [g.src_val, ha']
  have hkk : k = k₀ := by
    refine hbij.1 (GroupoidStr.Isotropy.ext ?_)
    change D.Φ.ϕ.mor k.val = D.Φ.ϕ.mor k₀.val
    rw [hk]
    exact ((A.X.comp_assoc _ _ _ e₁ e₂).symm.trans hk₀.symm)
  subst hkk
  have f₁ : A'.X.src b = A'.X.tgt (D.Ψ.ϕ.mor k.val) := by
    rw [hb, GroupoidFunctor.tgt_mor, k.tgt_val]
  have f₂ : A'.X.src (D.Ψ.ϕ.mor k.val) = A'.X.tgt (A'.X.inv b) := by
    rw [GroupoidFunctor.src_mor, k.src_val, GroupoidStr.tgt_inv, hb]
  exact hγ.trans (A'.X.comp_assoc _ _ _ f₁ f₂)

/-! ### `B → A`, outright (the hypothesis is not used) -/

theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, ?_, ?_⟩
  · intro X Y d x x' x'' a ha ha' b hb hb' g
    set e := MulEquiv.ofBijective _ (d.isEquivalence_F.bijective_isotropyHom x'')
    set c := X.X.isotropyConj (X.X.inv a) (by rw [GroupoidStr.src_inv, ha'])
      (by rw [GroupoidStr.tgt_inv, ha]) g
    refine ⟨e.symm c, ?_, rfl⟩
    have h1 : d.F.isotropyHom x'' (e.symm c) = c := e.apply_symm_apply c
    have h2 := congrArg GroupoidStr.Isotropy.val h1
    rw [EpFunctor.isotropyHom_val] at h2
    rw [h2, GroupoidStr.isotropyConj_val, GroupoidStr.inv_inv]
  · intro X Y d hΦ x x' x'' a ha ha' b hb hb'
    exact (Y.X.isotropyConj b hb hb').bijective.comp ((hΦ.bijective_isotropyHom x'').comp
      ((MulEquiv.ofBijective _ (d.isEquivalence_F.bijective_isotropyHom x'')).symm.bijective.comp
        (X.X.isotropyConj (X.X.inv a) _ _).bijective))
  · intro X Y d x x' h
    obtain ⟨x'', a, ha, ha'⟩ := d.isEquivalence_F.exists_iso x
    have hq : d.F.orbitMap (d.A.X.π x'') = X.X.π x := by
      rw [GroupoidFunctor.orbitMap_π]
      exact X.X.π_eq_π_iff.2 ⟨a, ha, ha'⟩
    have h' := (EPLocalization.Diagram.orbitMap_eq_of hq).symm.trans h
    rw [GroupoidFunctor.orbitMap_π] at h'
    obtain ⟨b, hb, hb'⟩ := Y.X.π_eq_π_iff.1 h'
    exact ⟨x'', a, b, ha, ha', hb, hb'⟩

#rt_check RoundTrip.V10_54.B_to_A [Polyfold.EPLocalization.Diagram.isotropyHom_spec,
  Polyfold.EPLocalization.Diagram.bijective_isotropyHom,
  Polyfold.EPLocalization.Diagram.exists_isotropyData]
#rt_check RoundTrip.V10_54.A_to_Bii [Polyfold.EPLocalization.Diagram.isotropyHom_spec,
  Polyfold.EPLocalization.Diagram.bijective_isotropyHom,
  Polyfold.EPLocalization.Diagram.exists_isotropyData]
#rt_check RoundTrip.V10_54.B_to_Bii [Polyfold.EPLocalization.Diagram.isotropyHom_spec,
  Polyfold.EPLocalization.Diagram.bijective_isotropyHom,
  Polyfold.EPLocalization.Diagram.exists_isotropyData]
#rt_overlap RoundTrip.V10_54.B_to_A [Polyfold.EPLocalization.Diagram.isotropyHom_spec,
  Polyfold.EPLocalization.Diagram.bijective_isotropyHom,
  Polyfold.EPLocalization.Diagram.exists_isotropyData]

end RoundTrip.V10_54
