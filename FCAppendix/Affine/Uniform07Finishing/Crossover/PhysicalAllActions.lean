import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalLimitOptimizer

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Topology
namespace Physical
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem BroadcastLaw05.actual_marginal_continuousOn_positive
    {Γ : FiniteGame m 2 c Seed} {t U eta : ℝ}
    (P : BroadcastLaw05 Γ t U) (i : Fin m)
    (heta : eta∈Ioc (0:ℝ) 1)
    (hA : Γ.A=Schedule.affine 2 eta heta.1.le heta.2) (hg : Γ.g=0)
    {s : ℝ} (hs : 0< s) : ContinuousOn (q Γ i) (Icc s U) := by
  let B : Icc s U → Icc (0:ℝ) U := fun b => ⟨b.1,⟨hs.le.trans b.2.1,b.2.2⟩⟩
  have hB : Continuous B := by fun_prop
  let f0 : Icc s U → ℝ := fun b =>
    (problem Γ i).payoff 0 (sourceLowerBroadcastAction U (B b))
  let f1 : Icc s U → ℝ := fun b =>
    (problem Γ i).payoff 1 (sourceLowerBroadcastAction U (B b))
  have hf0 : Continuous f0 := by
    apply continuous_iff_continuousAt.mpr
    intro b
    have hinput : ContinuousAt (fun z : Icc s U => ((0:ℝ),B z)) b :=
      (continuous_const.prodMk hB).continuousAt
    exact ContinuousAt.comp' (f := fun z : Icc s U => ((0:ℝ),B z)) (x := b)
      (P.payoffContinuous i (0,B b) (hs.trans_le b.2.1)) hinput
  have hf1 : Continuous f1 := by
    apply continuous_iff_continuousAt.mpr
    intro b
    have hinput : ContinuousAt (fun z : Icc s U => ((1:ℝ),B z)) b :=
      (continuous_const.prodMk hB).continuousAt
    exact ContinuousAt.comp' (f := fun z : Icc s U => ((1:ℝ),B z)) (x := b)
      (P.payoffContinuous i (1,B b) (hs.trans_le b.2.1)) hinput
  have hid (b : Icc s U) : q Γ i b.1=
      ((eta-1)*(f1 b-f0 b)-f0 b/b.1)/(2*eta) := by
    have hb : 0≤ b.1 := hs.le.trans b.2.1
    have hb0 : b.1≠0 := (hs.trans_le b.2.1).ne'
    have h0 : f0 b=utilityTwo eta 0 b.1 (q Γ i b.1) (duplicate Γ i b.1) := by
      dsimp [f0]
      rw [sourceLowerBroadcastAction_eq_two]
      exact two_payoff Γ heta.1.le heta.2 hA hg i 0 hb
    have h1 : f1 b=utilityTwo eta 1 b.1 (q Γ i b.1) (duplicate Γ i b.1) := by
      dsimp [f1]
      rw [sourceLowerBroadcastAction_eq_two]
      exact two_payoff Γ heta.1.le heta.2 hA hg i 1 hb
    rw [h0,h1]
    unfold utilityTwo
    field_simp [hb0,heta.1.ne']
    ring
  rw [continuousOn_iff_continuous_restrict]
  have hc : Continuous (fun b : Icc s U =>
      ((eta-1)*(f1 b-f0 b)-f0 b/b.1)/(2*eta)) :=
    (((hf1.sub hf0).const_mul (eta-1)).sub
      (hf0.div continuous_subtype_val (fun b => (hs.trans_le b.2.1).ne'))).div_const (2*eta)
  exact hc.congr (fun b => (hid b).symm)

theorem every_low_singleton_action_loses
    (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    {eta v ell lowTop U : ℝ} (heta : eta∈Icc (0:ℝ) 1)
    (hA : Γ.A=Schedule.affine 2 eta heta.1 heta.2) (hg : Γ.g=0)
    (hv : 0< v) (hell : 0< ell) (hhalfU : v/2≤ U) (hhalfLow : v/2≤ lowTop)
    (hqhalf : ell≤ q Γ i (v/2))
    (hdup : ∀ b∈Icc (0:ℝ) lowTop, duplicate Γ i b≤ ell/8)
    (a : JointAction 2) (ha : a.routeCount=1) (hab : a.bid≤ U) (halow : a.bid≤ lowTop) :
    ∃ z∈Icc (0:ℝ) (min v U),
      (problem Γ i).payoff v a<(problem Γ i).payoff v (two z) := by
  have hhalf0 : 0≤ v/2 := by positivity
  have hDhalf := hdup (v/2) ⟨hhalf0,hhalfLow⟩
  have hhalf := half_value_broadcast_payoff_lower Γ i heta hA hg hv.le hell.le
    hqhalf (hDhalf.trans (by linarith))
  have hone : (problem Γ i).payoff v a=utilityOne v a.bid (q Γ i a.bid) := by
    rw [singleton_payoff Γ (by norm_num : 0<2) i a ha,hg]
    simp only [sub_zero,q,utilityOne]
  by_cases hu : v*ell/4≤ utilityOne v a.bid (q Γ i a.bid)
  · have hpositive : 0< utilityOne v a.bid (q Γ i a.bid) :=
      (by positivity : 0< v*ell/4).trans_le hu
    have hbv : a.bid< v := positive_singleton_utility_implies_underbid
      (q_nonneg Γ i a.bid) hpositive
    refine ⟨a.bid,⟨a.bid_nonneg,le_min hbv.le hab⟩,?_⟩
    have hD := hdup a.bid ⟨a.bid_nonneg,halow⟩
    have hsmall : duplicate Γ i a.bid<(ell/2)/2 := by linarith
    have hgain := (low_optimizer_strict_route_gap hv a.bid_nonneg hbv.le heta.1 heta.2
      (duplicate_nonneg Γ i a.bid) (by convert hu using 1; ring) hsmall).2
    rw [hone,two_payoff Γ heta.1 heta.2 hA hg i v a.bid_nonneg]
    exact hgain
  · refine ⟨v/2,⟨hhalf0,le_min (by linarith) hhalfU⟩,?_⟩
    rw [hone]
    exact (lt_of_not_ge hu).trans_le ((by nlinarith [mul_pos hv hell] : v*ell/4≤ v*ell/2).trans hhalf)

theorem every_lower_singleton_action_of_optimizer_exclusion
    (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    {eta v ell lowTop U : ℝ} (heta : eta∈Ioc (0:ℝ) 1)
    (hA : Γ.A=Schedule.affine 2 eta heta.1.le heta.2) (hg : Γ.g=0)
    (hv : 0< v) (hell : 0< ell) (hlow : 0< lowTop)
    (hhalfU : v/2≤ U) (hhalfLow : v/2≤ lowTop)
    (hqhalf : ell≤ q Γ i (v/2))
    (hdup : ∀ b∈Icc (0:ℝ) lowTop, duplicate Γ i b≤ ell/8)
    (hcont : ContinuousOn (q Γ i) (Icc (lowTop/2) U))
    (hoptimizers : ∀ a : JointAction 2, a.routeCount=1 → a.bid∈Icc (0:ℝ) (min v U) →
      (∀ a' : JointAction 2, a'.routeCount=1 → a'.bid≤ U →
        (problem Γ i).payoff v a'≤(problem Γ i).payoff v a) →
      ∃ z∈Icc (0:ℝ) U, (problem Γ i).payoff v a<(problem Γ i).payoff v (two z)) :
    ∀ a : JointAction 2, a.routeCount=1 → a.bid≤ U →
      ∃ z∈Icc (0:ℝ) U, (problem Γ i).payoff v a<(problem Γ i).payoff v (two z) := by
  classical
  have lowWin : ∀ a : JointAction 2, a.routeCount=1 → a.bid≤ U → a.bid≤ lowTop →
      ∃ z∈Icc (0:ℝ) U, (problem Γ i).payoff v a<(problem Γ i).payoff v (two z) := by
    intro a ha hab halow
    obtain ⟨z,hz,hgain⟩ := every_low_singleton_action_loses Γ i ⟨heta.1.le,heta.2⟩
      hA hg hv hell hhalfU hhalfLow hqhalf hdup a ha hab halow
    exact ⟨z,⟨hz.1,hz.2.trans (min_le_right v U)⟩,hgain⟩
  have scalar (a : JointAction 2) (ha : a.routeCount=1) :
      (problem Γ i).payoff v a=utilityOne v a.bid (q Γ i a.bid) := by
    rw [singleton_payoff Γ (by norm_num : 0<2) i a ha,hg]
    simp only [sub_zero,q,utilityOne]
  intro a ha hab
  by_cases halow : a.bid≤ lowTop
  · exact lowWin a ha hab halow
  have hhigh : lowTop< a.bid := lt_of_not_ge halow
  by_cases hnonpos : (problem Γ i).payoff v a≤ 0
  · have hDhalf := hdup (v/2) ⟨by positivity,hhalfLow⟩
    have hhalf := half_value_broadcast_payoff_lower Γ i ⟨heta.1.le,heta.2⟩ hA hg hv.le hell.le
      hqhalf (hDhalf.trans (by linarith))
    exact ⟨v/2,⟨by positivity,hhalfU⟩,
      hnonpos.trans_lt ((by positivity : 0< v*ell/2).trans_le hhalf)⟩
  have hpos : 0<(problem Γ i).payoff v a := lt_of_not_ge hnonpos
  have hav : a.bid< v := positive_singleton_utility_implies_underbid (q_nonneg Γ i a.bid)
    (by simpa only [scalar a ha] using hpos)
  have hcap : a.bid≤ min v U := le_min hav.le hab
  have hinterval : lowTop/2≤ min v U := (by linarith : lowTop/2≤ a.bid).trans hcap
  have hnonempty : (Icc (lowTop/2) (min v U)).Nonempty := ⟨a.bid,⟨by linarith,hcap⟩⟩
  have hc : ContinuousOn (fun b => utilityOne v b (q Γ i b)) (Icc (lowTop/2) (min v U)) := by
    unfold utilityOne
    exact (continuousOn_const.sub continuousOn_id).mul
      (hcont.mono (fun b hb => ⟨hb.1,hb.2.trans (min_le_right v U)⟩))
  obtain ⟨b,hb,hmax⟩ := isCompact_Icc.exists_isMaxOn hnonempty hc
  have hb0 : 0≤ b := (by positivity : 0≤ lowTop/2).trans hb.1
  have hbU : b≤ U := hb.2.trans (min_le_right v U)
  have habmax : (problem Γ i).payoff v a≤(problem Γ i).payoff v (one b) := by
    rw [scalar a ha,one_payoff Γ hg i v hb0]
    exact hmax ⟨by linarith,hcap⟩
  have hbPos : 0<(problem Γ i).payoff v (one b) := hpos.trans_le habmax
  by_cases hglobal : ∀ a' : JointAction 2, a'.routeCount=1 → a'.bid≤ U →
      (problem Γ i).payoff v a'≤(problem Γ i).payoff v (one b)
  · obtain ⟨z,hz,hgain⟩ := hoptimizers (one b) (one_routes b)
      (by simpa only [one_bid hb0] using (show b∈Icc (0:ℝ) (min v U) from ⟨hb0,hb.2⟩)) hglobal
    exact ⟨z,hz,habmax.trans_lt hgain⟩
  · push Not at hglobal
    obtain ⟨a',ha',ha'U,hbetter⟩ := hglobal
    have ha'Pos : 0<(problem Γ i).payoff v a' := hbPos.trans hbetter
    have ha'v : a'.bid< v := positive_singleton_utility_implies_underbid (q_nonneg Γ i a'.bid)
      (by simpa only [scalar a' ha'] using ha'Pos)
    have ha'low : a'.bid< lowTop/2 := by
      by_contra h
      have ha'I : a'.bid∈Icc (lowTop/2) (min v U) :=
        ⟨le_of_not_gt h,le_min ha'v.le ha'U⟩
      have hbad := hmax ha'I
      rw [scalar a' ha',one_payoff Γ hg i v hb0] at hbetter
      exact (not_lt_of_ge hbad) hbetter
    obtain ⟨z,hz,hgain⟩ := lowWin a' ha' ha'U (ha'low.le.trans (by linarith))
    exact ⟨z,hz,(habmax.trans_lt hbetter).trans hgain⟩

end Physical
end FCAppendix.Affine.Uniform07Finishing.Crossover
