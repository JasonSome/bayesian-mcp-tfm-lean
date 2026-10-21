import FCAppendix.Existence.R01PayOnceImprovement

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open Set Filter Topology MeasureTheory ProbabilityTheory

theorem positive_bid_bestResponse_strict_surplus {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (w : Value W) (b : PositiveBid W)
    (hIC : ∀a : FloorAction 0 W,positivePayoff N n c π (w,a)≤
      positivePayoff N n c π (w,positiveAction b))
    (hQ : 0<positiveQ N n c π (positiveAction b)) :
    b.1<w.1 ∧ 0<positivePayoff N n c π (w,positiveAction b) := by
  have hnonneg : 0≤positivePayoff N n c π (w,positiveAction b) := by
    simpa only [positivePayoff_inactive N n c hn π] using hIC (.inl ())
  have hbw : b.1≤w.1 := by
    change 0≤(w.1-b.1)*positiveQ N n c π (positiveAction b) at hnonneg
    by_contra hh
    have hp := mul_neg_of_neg_of_pos (sub_neg.mpr (lt_of_not_ge hh)) hQ
    linarith
  have hstrict : b.1<w.1 := by
    by_contra hh
    have heq : w.1=b.1 := le_antisymm (le_of_not_gt hh) hbw
    let step : ℕ→ℝ := fun k=>b.1/(k+2)
    have hstep : ∀k,0<step k ∧ step k<b.1 := by
      intro k
      refine ⟨div_pos b.2.1 (by positivity),?_⟩
      apply (div_lt_iff₀ (by positivity : (0:ℝ)<k+2)).mpr
      nlinarith [show (0:ℝ)≤k from Nat.cast_nonneg k,b.2.1]
    let lower : ℕ→PositiveBid W := fun k=>
      ⟨b.1-step k,sub_pos.mpr (hstep k).2,(sub_le_self _ (hstep k).1.le).trans b.2.2⟩
    have hstep0 : Tendsto step atTop (𝓝 0) := by
      convert (tendsto_const_div_atTop_nhds_zero_nat b.1).comp (tendsto_add_atTop_nat 2) using 1
      funext k
      simp only [Function.comp_apply,Nat.cast_add,Nat.cast_ofNat]
      rfl
    have hlower : Tendsto lower atTop (𝓝 b) := by
      apply tendsto_subtype_rng.mpr
      convert tendsto_const_nhds.sub hstep0 using 1
      simp
    have hqseq := (continuous_positiveQ_own N n c hn π).continuousAt.tendsto.comp hlower
    have hevent : ∀ᶠk in atTop,0<positiveQ N n c π (positiveAction (lower k)) :=
      hqseq.eventually (Ioi_mem_nhds hQ)
    obtain ⟨k,hk⟩ := hevent.exists
    have hdev : 0<positivePayoff N n c π (w,positiveAction (lower k)) := by
      change 0<(w.1-(b.1-step k))*positiveQ N n c π (positiveAction (lower k))
      rw [heq]
      apply mul_pos _ hk
      linarith [(hstep k).1]
    have hplayed : positivePayoff N n c π (w,positiveAction b)=0 := by
      change (w.1-b.1)*positiveQ N n c π (positiveAction b)=0
      rw [heq,sub_self,zero_mul]
    have hd := hIC (positiveAction (lower k))
    rw [hplayed] at hd
    linarith
  exact ⟨hstrict,mul_pos (sub_pos.mpr hstrict) hQ⟩

end FCAppendix.Existence.PayOnceBounded
