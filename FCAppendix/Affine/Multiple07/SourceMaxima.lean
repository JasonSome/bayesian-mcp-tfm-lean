import FCAppendix.Affine.Multiple07.SourceGuards

noncomputable section
namespace FCAppendix.Affine.Multiple07
open Set

def sourceOneMaximum (r : Partition) (v : ℝ) : ℝ :=
  sSup (Hybrid.one xi 0 v (multiplier r) '' Icc (0 : ℝ) 1)

def sourceTwoMaximum (r : Partition) (v : ℝ) : ℝ :=
  sSup (Hybrid.two xi 0 v (multiplier r) '' Icc (0 : ℝ) 1)

theorem sourceOneMaximum_attained (r : Partition) (v : ℝ) :
    ∃ q ∈ Icc (0 : ℝ) 1,
      sourceOneMaximum r v = Hybrid.one xi 0 v (multiplier r) q := by
  obtain ⟨q, hq, hmax⟩ := source_one_maximum_attained r v
  have hbound : BddAbove (Hybrid.one xi 0 v (multiplier r) '' Icc (0 : ℝ) 1) := by
    refine ⟨Hybrid.one xi 0 v (multiplier r) q, ?_⟩
    rintro y ⟨q', hq', rfl⟩
    exact hmax q' hq'
  refine ⟨q, hq, le_antisymm ?_ ?_⟩
  · change sSup (Hybrid.one xi 0 v (multiplier r) '' Icc (0:ℝ) 1) ≤ _
    refine csSup_le (s:=Hybrid.one xi 0 v (multiplier r) '' Icc (0:ℝ) 1)
      ⟨Hybrid.one xi 0 v (multiplier r) q,⟨q,hq,rfl⟩⟩ ?_
    rintro y ⟨q', hq', rfl⟩
    exact hmax q' hq'
  · exact le_csSup hbound ⟨q, hq, rfl⟩

theorem sourceTwoMaximum_eq_outsideTwo (r : Partition) {v : ℝ}
    (hv : activeLower r ≤ v) :
    sourceTwoMaximum r v = Hybrid.outsideTwo v (multiplier r) := by
  obtain ⟨hp, he, hmax⟩ := source_two_zero_optimizer r hv
  have hbound : BddAbove (Hybrid.two xi 0 v (multiplier r) '' Icc (0 : ℝ) 1) := by
    refine ⟨Hybrid.outsideTwo v (multiplier r), ?_⟩
    rintro y ⟨q, hq, rfl⟩
    exact hmax q
  apply le_antisymm
  · apply csSup_le
    · exact ⟨Hybrid.two xi 0 v (multiplier r) (exposure r v),
        exposure r v, ⟨hp.1.le, hp.2.le⟩, rfl⟩
    · rintro y ⟨q, hq, rfl⟩
      exact hmax q
  · rw [← he]
    exact le_csSup hbound ⟨exposure r v, ⟨hp.1.le, hp.2.le⟩, rfl⟩

theorem literal_active_maximum_guards (r : Partition) {v : ℝ}
    (hv : v ∈ Icc (activeLower r) (activeUpper r)) :
    sourceOneMaximum r v < sourceTwoMaximum r v ∧
      v - upperFloor r < sourceTwoMaximum r v ∧
      sourceTwoMaximum r v = Hybrid.outsideTwo v (multiplier r) := by
  obtain ⟨q, hq, hmax⟩ := sourceOneMaximum_attained r v
  rw [sourceTwoMaximum_eq_outsideTwo r hv.1, hmax]
  exact ⟨active_two_gt_every_one r hv hq, active_two_gt_upper_price r hv, rfl⟩

theorem literal_upper_maximum_guards (r : Partition) {v : ℝ}
    (hv : upperLower r ≤ v) :
    sourceTwoMaximum r v < v - upperFloor r ∧
      sourceOneMaximum r v < v - upperFloor r ∧
      Hybrid.outsideTwo v (multiplier r) < v - upperFloor r := by
  have hvA : activeLower r ≤ v := by
    have h : activeLower r ≤ upperLower r := by
      cases r <;> norm_num [activeLower, upperLower]
    exact h.trans hv
  obtain ⟨q, hq, hmax⟩ := sourceOneMaximum_attained r v
  rw [sourceTwoMaximum_eq_outsideTwo r hvA, hmax]
  exact ⟨upper_price_gt_outsideTwo r hv,
    upper_price_gt_every_one r hv hq, upper_price_gt_outsideTwo r hv⟩

end FCAppendix.Affine.Multiple07
