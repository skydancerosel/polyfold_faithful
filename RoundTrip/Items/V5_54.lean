import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_54

/-!
Round trip for V5_54 (Definition 5.36: the sc-smooth approximation property).

The only listed declaration, `Polyfold.LocalModel.HasApproxProperty`, is a definition, so
`A = True`; the content of the audit is the comparison of the project's notion with B's, which is
B itself, proved outright here (`B_holds`).

The two definitions differ only in how the open set `V ⊆ O` is presented:

* project: an open `W ⊆ E₀` with `cl_E(O ∩ W) ⊆ O`; supports `cl(O ∩ {f ≠ 0}) ∩ O ⊆ W`;
* B: `V ⊆ O` with `V = O ∩ W'` for an open `W'`, `cl_C(V) = cl_E(V) ∩ C ⊆ O`; supports `⊆ V`.

With `V = O ∩ W` these agree: a support taken in `O` lies in `W` iff it lies in `O ∩ W`, and
`cl_E(V) ∩ C = cl_E(V)` because `V ⊆ O ⊆ C` and the partial quadrant `C` is closed
(`LocalModel.O_subset_C`, `LocalModel.isPartialQuadrant`).  Everything else (continuity of `f` on
`O`, `[0, 1]` values on `O`, `IsScSmoothRetractMap … realSc univ univ g`, `|f − g| ≤ ε` on `O`, all
`ε > 0`) is literally the same.
-/

namespace RoundTrip.V5_54
open Polyfold Set Function

/-- Only definitions are listed: `A = True`. -/
def A : Prop := True

theorem A_holds : A := trivial

/-- `cl_E(V) ∩ C = cl_E(V)` for `V ⊆ O`. -/
lemma closure_subset_C (M : LocalModel) {V : Set (M.E 0)} (hV : V ⊆ M.O) :
    closure V ⊆ M.C :=
  M.isPartialQuadrant.isClosed.closure_subset_iff.2 (hV.trans M.O_subset_C)

/-- The project's Definition 5.36 is B's. -/
theorem B_holds : B := by
  intro M
  constructor
  · rintro h V hVO ⟨W, hW, rfl⟩ hcl f hf hf01 hfsupp ε hε
    have hcl' : closure (M.O ∩ W) ⊆ M.O := fun z hz =>
      hcl ⟨hz, closure_subset_C M hVO hz⟩
    obtain ⟨g, hg, hg01, hgsupp, hgf⟩ :=
      h W hW hcl' f hf hf01 (hfsupp.trans inter_subset_right) ε hε
    exact ⟨g, hg, hg01, fun z hz => ⟨hz.2, hgsupp hz⟩, hgf⟩
  · intro h W hW hcl f hf hf01 hfsupp ε hε
    obtain ⟨g, hg, hg01, hgsupp, hgf⟩ :=
      h (M.O ∩ W) inter_subset_left ⟨W, hW, rfl⟩ (inter_subset_left.trans hcl) f hf hf01
        (fun z hz => ⟨hz.2, hfsupp hz⟩) ε hε
    exact ⟨g, hg, hg01, hgsupp.trans inter_subset_right, hgf⟩

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := fun _ => trivial

#rt_check RoundTrip.V5_54.A_to_B []
#rt_check RoundTrip.V5_54.B_to_A []
#rt_overlap RoundTrip.V5_54.B_to_A []
#rt_overlap RoundTrip.V5_54.A_to_B [Polyfold.LocalModel.HasApproxProperty]

end RoundTrip.V5_54
