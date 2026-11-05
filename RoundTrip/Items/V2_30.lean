import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_30

/-! Round trip for V2_30 (Lemma 2.26: `d_A ≤ d_X` on a sub-M-polyfold).

`A` is the type of `Polyfold.lemma_2_26` (universe `0`): for the project's structure
`subPolyfold hA` on `A` (Proposition 2.21), `d_A(a) ≤ d_X(a)`.

B states the inequality for EVERY M-polyfold structure `Q` on `A` with properties (1), (2) of
Proposition 2.21.

* `A → B`: such a `Q` and `subPolyfold hA` are sc-diffeomorphic by the identity near `a`: on
  `V ∩ A` (`(V, r)` the sub-M-polyfold data at `a`) `id = i⁻¹ ∘ r ∘ i`, which is sc-smooth
  `Q → subPolyfold` by (1) for `Q` and Proposition 2.21 (2) for `subPolyfold`, and
  `subPolyfold → Q` by Proposition 2.21 (1) and (2) for `Q`.  Proposition 2.24 (a project
  lemma, not an item theorem) gives `d_Q(a) = d_{subPolyfold}(a)`, and A concludes.
* `B → A`: `subPolyfold hA` has properties (1), (2) (`subPolyfold_inclusion_isScSmooth`,
  `subPolyfold_retraction_isScSmooth`, with `i⁻¹ ∘ r` replaced by any `g` agreeing with `r`). -/

namespace RoundTrip.V2_30
open Polyfold Set

/-- The project's statement (universe `0`). -/
def A : Prop := type_of% @Polyfold.lemma_2_26.{0}

theorem A_holds : A := @Polyfold.lemma_2_26.{0}

/-- `A → B`. -/
theorem A_to_B : A → B := by
  intro hA' X _ _ _ P A hA _ Q hQ a
  set S := MPolyfold.subPolyfold hA
  set d := hA.data a.2
  set UA : Set A := Subtype.val ⁻¹' d.V
  have hUA : IsOpen UA := d.isOpen.preimage continuous_subtype_val
  have haUA : a ∈ UA := hA.mem_data_V a.2
  set g := d.retractInto a
  have hg_id : ∀ z ∈ UA, g z.1 = z := fun z hz =>
    Subtype.ext (by rw [d.retractInto_val a hz]; exact d.apply_eq_self ⟨z.2, hz⟩)
  -- `Q → subPolyfold`: `id = (i⁻¹ ∘ r) ∘ i` on `V ∩ A`
  have h1 : Q.IsScSmoothOn S id UA := by
    have := (MPolyfold.subPolyfold_retraction_isScSmooth hA d a).comp
      (hQ.1.1.mono hUA (subset_univ _)) (fun z hz => hz)
    exact this.congr fun z hz => hg_id z hz
  -- `subPolyfold → Q`: `id = (i⁻¹ ∘ r) ∘ i` on `V ∩ A`, with (2) for `Q`
  have h2 : S.IsScSmoothOn Q id UA := by
    have hgQ : P.IsScSmoothOn Q g d.V :=
      hQ.2 d.V d.r d.isOpen d.mapsTo d.isScSmoothOn d.idem d.image g
        (fun x hx => d.retractInto_val a hx)
    have := hgQ.comp ((MPolyfold.subPolyfold_inclusion_isScSmooth hA).mono hUA (subset_univ _))
      (fun z hz => hz)
    exact this.congr fun z hz => hg_id z hz
  have hdiffeo : Q.IsScDiffeoOn S id id UA UA :=
    ⟨h1, h2, mapsTo_id _, mapsTo_id _, fun _ _ => rfl, fun _ _ => rfl⟩
  rw [proposition_2_24 hdiffeo haUA]
  exact hA' hA a

/-- `B → A`. -/
theorem B_to_A : B → A := by
  intro hB X _ _ _ P A hA _ a
  refine hB X P A hA (MPolyfold.subPolyfold hA)
    ⟨⟨MPolyfold.subPolyfold_inclusion_isScSmooth hA, Topology.IsEmbedding.subtypeVal⟩, ?_⟩ a
  intro V r hV hr hrs hidem himg g hg
  let d : P.SubData A := ⟨V, r, hV, hr, hrs, hidem, himg⟩
  refine (MPolyfold.subPolyfold_retraction_isScSmooth hA d a).congr fun x hx => Subtype.ext ?_
  rw [d.retractInto_val a hx]
  exact (hg x hx).symm

#rt_check RoundTrip.V2_30.A_to_B [Polyfold.lemma_2_26]
#rt_check RoundTrip.V2_30.B_to_A [Polyfold.lemma_2_26]
#rt_overlap RoundTrip.V2_30.B_to_A [Polyfold.lemma_2_26]

end RoundTrip.V2_30
