import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Order.Monotone
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace FCAppendix.Exclusive.Narrow.OrderedGraph
open Set MeasureTheory

def Ordered (R : ℝ → ℝ → Prop) : Prop :=
  ∀ ⦃v w b d : ℝ⦄, R v b → R w d → v < w → b ≤ d

def branching (R : ℝ → ℝ → Prop) : Set ℝ :=
  {v | ∃ b d, R v b ∧ R v d ∧ b < d}

theorem branching_countable {R : ℝ → ℝ → Prop} (hR : Ordered R) :
    (branching R).Countable := by
  classical
  have hp : ∀ v : branching R, ∃ b d, R v.val b ∧ R v.val d ∧ b < d :=
    fun v => v.property
  choose b d hb hd hbd using hp
  choose q hqb hqd using (fun v : branching R => exists_rat_btwn (hbd v))
  have hinj : Function.Injective q := by
    intro v w he
    apply Subtype.ext
    by_contra hne
    have heR : (q v : ℝ) = (q w : ℝ) := congrArg (fun t : ℚ => (t : ℝ)) he
    rcases lt_or_gt_of_ne hne with hvw | hwv
    · have ho := hR (hd v) (hb w) hvw
      linarith [hqd v, hqb w]
    · have ho := hR (hd w) (hb v) hwv
      linarith [hqd w, hqb v]
  exact hinj.countable

theorem eq_of_not_branching {R : ℝ → ℝ → Prop} {v b d : ℝ}
    (hv : v ∉ branching R) (hb : R v b) (hd : R v d) : b = d := by
  rcases lt_trichotomy b d with h | h | h
  · exact False.elim (hv ⟨b, d, hb, hd, h⟩)
  · exact h
  · exact False.elim (hv ⟨d, b, hd, hb, h⟩)

def lowerImage (R : ℝ → ℝ → Prop) (a v : ℝ) : Set ℝ :=
  insert a {b | ∃ w, w ≤ v ∧ R w b}

noncomputable def representative (R : ℝ → ℝ → Prop) (a v : ℝ) : ℝ :=
  sSup (lowerImage R a v)

private theorem lowerImage_nonempty (R : ℝ → ℝ → Prop) (a v : ℝ) :
    (lowerImage R a v).Nonempty := ⟨a, Or.inl rfl⟩

private theorem lowerImage_bddAbove {R : ℝ → ℝ → Prop} {a B : ℝ}
    (haB : a ≤ B) (hB : ∀ ⦃v b⦄, R v b → b ≤ B) (v : ℝ) :
    BddAbove (lowerImage R a v) := by
  refine ⟨B, ?_⟩
  rintro b (rfl | ⟨w, _, hwb⟩)
  · exact haB
  · exact hB hwb

theorem representative_mem {R : ℝ → ℝ → Prop} {a B : ℝ}
    (haB : a ≤ B) (hB : ∀ ⦃v b⦄, R v b → b ≤ B) (v : ℝ) :
    representative R a v ∈ Icc a B := by
  constructor
  · exact le_csSup (lowerImage_bddAbove haB hB v) (Or.inl rfl)
  · apply csSup_le (lowerImage_nonempty R a v)
    rintro b (rfl | ⟨w, _, hwb⟩)
    · exact haB
    · exact hB hwb

theorem representative_monotone {R : ℝ → ℝ → Prop} {a B : ℝ}
    (haB : a ≤ B) (hB : ∀ ⦃v b⦄, R v b → b ≤ B) :
    Monotone (representative R a) := by
  intro v w hvw
  apply csSup_le (lowerImage_nonempty R a v)
  intro b hb
  apply le_csSup (lowerImage_bddAbove haB hB w)
  rcases hb with rfl | ⟨u, huv, hub⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨u, huv.trans hvw, hub⟩

theorem representative_eq {R : ℝ → ℝ → Prop} {a B v b : ℝ}
    (haB : a ≤ B) (ha : ∀ ⦃v b⦄, R v b → a ≤ b)
    (hB : ∀ ⦃v b⦄, R v b → b ≤ B) (hR : Ordered R)
    (hv : v ∉ branching R) (hb : R v b) : representative R a v = b := by
  apply le_antisymm
  · apply csSup_le (lowerImage_nonempty R a v)
    rintro d (rfl | ⟨w, hwv, hwd⟩)
    · exact ha hb
    · rcases lt_or_eq_of_le hwv with hlt | he
      · exact hR hwd hb hlt
      · subst w
        exact (eq_of_not_branching hv hwd hb).le
  · exact le_csSup (lowerImage_bddAbove haB hB v) (Or.inr ⟨v, le_rfl, hb⟩)

theorem ae_singleton_fiber (μ : Measure ℝ) [NullSingletonClass μ]
    {R : ℝ → ℝ → Prop} (hR : Ordered R) :
    ∀ᵐ v ∂μ, ∀ b d, R v b → R v d → b = d := by
  filter_upwards [(branching_countable hR).ae_notMem μ] with v hv b d hb hd
  exact eq_of_not_branching hv hb hd

theorem ae_all_singleton_fibers (μ : Measure ℝ) [NullSingletonClass μ]
    {ι : Type*} [Countable ι] (R : ι → ℝ → ℝ → Prop)
    (hR : ∀ i, Ordered (R i)) :
    ∀ᵐ v ∂μ, ∀ i b d, R i v b → R i v d → b = d := by
  exact ae_all_iff.mpr (fun i => ae_singleton_fiber μ (hR i))

theorem strictMonoOn_of_positive_derivative {A A' : ℝ → ℝ} {a B : ℝ}
    (hA : ∀ b ∈ Ioo a B, HasDerivAt A (A' b) b)
    (hpos : ∀ b ∈ Ioo a B, 0 < A' b) : StrictMonoOn A (Ioo a B) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo a B)
    (fun b hb => (hA b hb).continuousAt.continuousWithinAt)
  intro b hb
  have hb' : b ∈ Ioo a B := interior_subset hb
  rw [(hA b hb').deriv]
  exact hpos b hb'

end FCAppendix.Exclusive.Narrow.OrderedGraph
