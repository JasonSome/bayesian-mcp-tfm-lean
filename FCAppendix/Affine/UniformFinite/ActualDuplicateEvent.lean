import FCAppendix.Affine.UniformFinite.ActualAtomCrossing
import FCAppendix.Affine.UniformFinite.AtomCountEvents

noncomputable section
namespace FCAppendix.Affine.UniformFinite.ActualAtoms
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped BigOperators

theorem residual_balance_of_duplicate {M : ℕ} (row : Source.CountRow M)
    (hM : 2*Uniform07.capacity M≤ M) (κ : ℝ) (b : Fin M→ℝ) (a : Fin M)
    (hdup : LowBody.focalCopy ((Source.lowerTemplate row).selection κ b) a=2) :
    row.lower.card + 2*Uniform07.capacity M =
      M + Source.residual row 0 + Source.residual row 1 := by
  have hf := (Source.lowerTemplate row).selection_feasible κ b
  have ha := (LowBody.focalCopy_eq_two_iff _ _).mp hdup
  have hp0 : 0<((Source.lowerTemplate row).selection κ b).1.card :=
    Finset.card_pos.mpr ⟨a,(Finset.mem_inter.mp ha).1⟩
  have hp1 : 0<((Source.lowerTemplate row).selection κ b).2.card :=
    Finset.card_pos.mpr ⟨a,(Finset.mem_inter.mp ha).2⟩
  have hd0 : 0< Source.residual row 0 := hp0.trans_le hf.1
  have hd1 : 0< Source.residual row 1 := hp1.trans_le hf.2.2.1
  have h0 : Source.residual row 0=min row.lower.card (Uniform07.capacity M-row.upper0) := by
    simp [Source.residual, Source.upperCount]
  have h1 : Source.residual row 1=min row.lower.card (Uniform07.capacity M-row.upper1) := by
    simp [Source.residual, Source.upperCount]
  have hp := row.partition
  rw [h0] at hd0
  rw [h1] at hd1
  rw [h0, h1]
  omega

theorem harmful_duplicate_original_value_count {M : ℕ}
    (i : Uniform07.Row) (row : Source.CountRow M) (hM : 2*Uniform07.capacity M≤ M)
    (b value : Fin M→ℝ) (hb : ∀k∈row.lower,0≤ b k)
    (hfloor : ∀k∈row.lower,Uniform05.floorBid i (value k)≤ b k)
    (focal : Fin M) (hf : focal∈row.lower) (hpos : 0< b focal)
    (target : ℝ) (hraise : b focal< target) (hcap : target≤ Uniform05.cap i)
    (hnot : LowBody.focalCopy ((Source.lowerTemplate row).selection (Uniform05.kappa i)
      (Source.lowerBids row b)) focal≠2)
    (hdup : LowBody.focalCopy ((Source.lowerTemplate row).selection (Uniform05.kappa i)
      (Source.lowerBids row (Function.update b focal target))) focal=2) :
    ∃rival : Fin M, rival∈row.lower ∧ rival≠focal ∧
      (b rival∈Icc (b focal) target ∨
        b rival∈Icc (Uniform05.kappa i*b focal) (Uniform05.kappa i*target)) ∧
      M-2*Uniform07.capacity M ≤
        ((row.lower.filter (fun k => k≠focal ∧ value k≤ Uniform05.zc i)).erase rival).card := by
  have hb' : ∀k,0≤ Source.lowerBids row b k := by
    intro k
    by_cases hk : k∈row.lower
    · simpa only [Source.lowerBids_of_mem row b hk] using hb k hk
    · simp [Source.lowerBids, hk]
  rw [lowerBids_update row b focal hf] at hdup
  obtain ⟨rival, hr, hrf, hc, hcount⟩ :=
    PureAtoms.duplicate_acquisition_small_count (Source.lowerTemplate row)
      (Uniform05.kappa_range i).1 (Source.lowerBids row b) hb'
      (fun k hk => Source.lowerBids_of_not_mem row b hk) focal hf
      (by simpa only [Source.lowerBids_of_mem row b hf] using hpos) target
      (by simpa only [Source.lowerBids_of_mem row b hf] using hraise) hnot hdup
  have hbalance := residual_balance_of_duplicate row hM (Uniform05.kappa i)
    (Function.update (Source.lowerBids row b) focal target) focal hdup
  have hsub :
      ((row.lower.filter (fun k => k≠focal ∧ Source.lowerBids row b k≤ Uniform05.kappa i*target)).erase rival) ⊆
      ((row.lower.filter (fun k => k≠focal ∧ value k≤ Uniform05.zc i)).erase rival) := by
    intro k hk
    obtain ⟨hkr,hk⟩ := Finset.mem_erase.mp hk
    obtain ⟨hkl,hkf,hkb⟩ := Finset.mem_filter.mp hk
    apply Finset.mem_erase.mpr
    refine ⟨hkr, Finset.mem_filter.mpr ⟨hkl,hkf,?_⟩⟩
    have hkb' : b k≤ Uniform05.kappa i*Uniform05.cap i := by
      rw [Source.lowerBids_of_mem row b hkl] at hkb
      exact hkb.trans (mul_le_mul_of_nonneg_left hcap (Uniform05.kappa_range i).1.le)
    exact Uniform05.low_category_imp_value_le i (Uniform05.t_pos i)
      (Uniform05.zc_receipt_guard i) (hfloor k hkl) hkb'
  have hcards := Finset.card_le_card hsub
  refine ⟨rival,hr,hrf,?_,?_⟩
  · simpa only [Source.lowerBids_of_mem row b hr, Source.lowerBids_of_mem row b hf] using hc
  · change row.lower.card≤
        ((row.lower.filter (fun k => k≠focal ∧ Source.lowerBids row b k≤ Uniform05.kappa i*target)).erase rival).card+
          Source.residual row 0+Source.residual row 1 at hcount
    omega

end FCAppendix.Affine.UniformFinite.ActualAtoms
