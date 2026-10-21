import FCAppendix.Affine.UniformFinite.PhysicalLaw
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Sequences

noncomputable section
namespace FCAppendix.Affine.Uniform05
open Set MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace

theorem isClosed_restrictedPair (i : Row) : IsClosed {p : ℝ × Bid i | RestrictedPair i p} := by
  unfold RestrictedPair
  exact (isClosed_Icc.preimage continuous_fst).inter
    ((isClosed_le ((continuous_floor i).comp continuous_fst) continuous_snd.subtype_val).inter
      (isClosed_le continuous_snd.subtype_val continuous_fst))

theorem isClosed_restrictedSupport (i : Row) :
    IsClosed {G : ProbabilityMeasure (ℝ × Bid i) |
      ∀ᵐ p ∂(G : Measure (ℝ × Bid i)), RestrictedPair i p} := by
  apply IsSeqClosed.isClosed
  intro G G₀ hG ht
  let S : Set (ℝ × Bid i) := {p | RestrictedPair i p}
  have hs : IsClosed S := isClosed_restrictedPair i
  have hn (n : ℕ) : (G n : Measure (ℝ × Bid i)) Sᶜ = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    simpa only [S, mem_compl_iff, mem_setOf_eq, not_not] using hG n
  have hh := ProbabilityMeasure.le_liminf_measure_open_of_tendsto ht hs.isOpen_compl
  simp only [hn, liminf_const] at hh
  have hz : (G₀ : Measure (ℝ × Bid i)) Sᶜ = 0 := le_antisymm hh bot_le
  have ha := measure_eq_zero_iff_ae_notMem.mp hz
  simpa only [S, mem_compl_iff, mem_setOf_eq, not_not] using ha

instance restrictedLawCompact (i : Row) : CompactSpace (RestrictedLaw i) := by
  have hc := isCompact_fixedFstMarginal (A := Bid i) (lowerValueMeasure i)
  have hs := (isClosed_fixedFstMarginal (A := Bid i) (lowerValueMeasure i)).inter
    (isClosed_restrictedSupport i)
  have hk : IsCompact {G : ProbabilityMeasure (ℝ × Bid i) |
      (G : Measure (ℝ × Bid i)).map Prod.fst = lowerValueMeasure i ∧
      ∀ᵐ p ∂(G : Measure (ℝ × Bid i)), RestrictedPair i p} :=
    hc.of_isClosed_subset hs (fun _ h => h.1)
  exact isCompact_iff_compactSpace.mp hk

end FCAppendix.Affine.Uniform05
