import FCAppendix.Affine.Hybrid.Tail03.FiniteInterface

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology

structure SourceTailOutcomes {F : ProbabilityMeasure ℝ} {eta1 eta2 : ℝ}
    (M : ℝ) (f : ActualTwoCoefficientFamilies F eta1 eta2) where
  index : ℕ→ f.Market
  increasing : StrictMono (fun k=>(index k).1)
  lowerLaw : ℝ→ CountLaw 2
  upperLaw : ℝ→ CountLaw 2
  measurable_lower : ∀r,Measurable (fun v=>(lowerLaw v).mass r)
  measurable_upper : ∀r,Measurable (fun v=>(upperLaw v).mass r)
  ae_count_limits : ∀ᵐv ∂(F : Measure ℝ),∀r,
    Tendsto (fun k=>((f.lowerAt (index k)).conditionalCount v).mass r) atTop
      (𝓝 ((lowerLaw v).mass r)) ∧
    Tendsto (fun k=>((f.upperAt (index k)).conditionalCount v).mass r) atTop
      (𝓝 ((upperLaw v).mass r))
  fixed_tail_count_limits : ∀v,M≤ v → ∀r,
    Tendsto (fun k=>((f.lowerAt (index k)).conditionalCount v).mass r) atTop
      (𝓝 ((lowerLaw v).mass r)) ∧
    Tendsto (fun k=>((f.upperAt (index k)).conditionalCount v).mass r) atTop
      (𝓝 ((upperLaw v).mass r))
  lower_tail : ∀v,M≤ v → lowerLaw v=FiniteLaw.dirac (1 : Fin 3)
  tail_reversal : ∀v,M≤ v →
    (lowerLaw v).success=1 ∧ (lowerLaw v).load=1 ∧
    (lowerLaw v).load/(lowerLaw v).success=1 ∧
    0<(upperLaw v).success ∧ (upperLaw v).success<1 ∧
    1<(upperLaw v).load ∧ 1<(upperLaw v).load/(upperLaw v).success
  Q1 : ℝ
  Q2 : ℝ
  Q1_eq : Q1=∫v,(lowerLaw v).success ∂(F : Measure ℝ)
  Q2_eq : Q2=∫v,(upperLaw v).success ∂(F : Measure ℝ)
  Q1_pos : 0< Q1
  Q2_pos : 0< Q2
  coverage_lower : Tendsto (fun k=> Bayes.finiteCoverage (f.lowerAt (index k)).game)
    atTop (𝓝 Q1)
  coverage_upper : Tendsto (fun k=> Bayes.finiteCoverage (f.upperAt (index k)).game)
    atTop (𝓝 Q2)
  load_lower : Tendsto (fun k=> Bayes.finiteLoad (f.lowerAt (index k)).game)
    atTop (𝓝 (99/100:ℝ))
  load_upper : Tendsto (fun k=> Bayes.finiteLoad (f.upperAt (index k)).game)
    atTop (𝓝 (99/100:ℝ))
  multiplicity_lower : Tendsto (fun k=>
    Bayes.finiteLoad (f.lowerAt (index k)).game /
      Bayes.finiteCoverage (f.lowerAt (index k)).game)
    atTop (𝓝 ((99/100)/Q1))
  multiplicity_upper : Tendsto (fun k=>
    Bayes.finiteLoad (f.upperAt (index k)).game /
      Bayes.finiteCoverage (f.upperAt (index k)).game)
    atTop (𝓝 ((99/100)/Q2))
  aggregate_reversal : Q2< Q1 ∧ (99/100)/Q1<(99/100)/Q2

namespace SourceTailOutcomes

theorem eventually_positive_coverage {F eta1 eta2 M}
    {f : ActualTwoCoefficientFamilies F eta1 eta2}
    (o : SourceTailOutcomes M f) :
    ∀ᶠ k in atTop,
      0< Bayes.finiteCoverage (f.lowerAt (o.index k)).game ∧
      0< Bayes.finiteCoverage (f.upperAt (o.index k)).game :=
  (o.coverage_lower.eventually (Ioi_mem_nhds o.Q1_pos)).and
    (o.coverage_upper.eventually (Ioi_mem_nhds o.Q2_pos))

theorem eventually_aggregate_reversal {F eta1 eta2 M}
    {f : ActualTwoCoefficientFamilies F eta1 eta2}
    (o : SourceTailOutcomes M f) :
    ∀ᶠ k in atTop,
      0< Bayes.finiteCoverage (f.lowerAt (o.index k)).game ∧
      0< Bayes.finiteCoverage (f.upperAt (o.index k)).game ∧
      Bayes.finiteCoverage (f.upperAt (o.index k)).game <
        Bayes.finiteCoverage (f.lowerAt (o.index k)).game ∧
      Bayes.finiteLoad (f.lowerAt (o.index k)).game /
          Bayes.finiteCoverage (f.lowerAt (o.index k)).game <
        Bayes.finiteLoad (f.upperAt (o.index k)).game /
          Bayes.finiteCoverage (f.upperAt (o.index k)).game := by
  have hQ := o.coverage_upper.eventually_lt o.coverage_lower o.aggregate_reversal.1
  have hmu := o.multiplicity_lower.eventually_lt o.multiplicity_upper
    o.aggregate_reversal.2
  filter_upwards [o.eventually_positive_coverage,hQ,hmu] with k hk hQk hmuk
  exact ⟨hk.1,hk.2,hQk,hmuk⟩

theorem fixed_tail_statistics {F eta1 eta2 M}
    {f : ActualTwoCoefficientFamilies F eta1 eta2}
    (o : SourceTailOutcomes M f) (v : ℝ) (hv : M≤ v) :
    Tendsto (fun k=>((f.lowerAt (o.index k)).conditionalCount v).success) atTop (𝓝 1) ∧
    Tendsto (fun k=>((f.lowerAt (o.index k)).conditionalCount v).load) atTop (𝓝 1) ∧
    Tendsto (fun k=>((f.lowerAt (o.index k)).conditionalCount v).load /
      ((f.lowerAt (o.index k)).conditionalCount v).success) atTop (𝓝 1) ∧
    Tendsto (fun k=>((f.upperAt (o.index k)).conditionalCount v).success) atTop
      (𝓝 ((o.upperLaw v).success)) ∧
    Tendsto (fun k=>((f.upperAt (o.index k)).conditionalCount v).load) atTop
      (𝓝 ((o.upperLaw v).load)) ∧
    Tendsto (fun k=>((f.upperAt (o.index k)).conditionalCount v).load /
      ((f.upperAt (o.index k)).conditionalCount v).success) atTop
      (𝓝 ((o.upperLaw v).load/(o.upperLaw v).success)) ∧
    (∀ᶠk in atTop,0<((f.lowerAt (o.index k)).conditionalCount v).success ∧
      0<((f.upperAt (o.index k)).conditionalCount v).success) := by
  have hc := o.fixed_tail_count_limits v hv
  have hl := count_two_statistics_tendsto
    (fun k=>(f.lowerAt (o.index k)).conditionalCount v) (o.lowerLaw v)
    (hc 0).1 (hc 2).1
  have hu := count_two_statistics_tendsto
    (fun k=>(f.upperAt (o.index k)).conditionalCount v) (o.upperLaw v)
    (hc 0).2 (hc 2).2
  have hr := o.tail_reversal v hv
  rw [hr.1,hr.2.1] at hl
  have hml := hl.2.div hl.1 (by norm_num : (1:ℝ)≠0)
  have hmu := hu.2.div hu.1 (ne_of_gt hr.2.2.2.1)
  refine ⟨hl.1,hl.2,by simpa using! hml,hu.1,hu.2,hmu,?_⟩
  exact (hl.1.eventually (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))).and
    (hu.1.eventually (Ioi_mem_nhds hr.2.2.2.1))

theorem fixed_tail_eventually_reversal {F eta1 eta2 M}
    {f : ActualTwoCoefficientFamilies F eta1 eta2}
    (o : SourceTailOutcomes M f) (v : ℝ) (hv : M≤ v) :
    ∀ᶠk in atTop,
      0<((f.lowerAt (o.index k)).conditionalCount v).success ∧
      0<((f.upperAt (o.index k)).conditionalCount v).success ∧
      ((f.upperAt (o.index k)).conditionalCount v).success <
        ((f.lowerAt (o.index k)).conditionalCount v).success ∧
      ((f.lowerAt (o.index k)).conditionalCount v).load <
        ((f.upperAt (o.index k)).conditionalCount v).load ∧
      ((f.lowerAt (o.index k)).conditionalCount v).load /
          ((f.lowerAt (o.index k)).conditionalCount v).success <
        ((f.upperAt (o.index k)).conditionalCount v).load /
          ((f.upperAt (o.index k)).conditionalCount v).success := by
  obtain ⟨hS1,hL1,hmu1,hS2,hL2,hmu2,hpos⟩ := o.fixed_tail_statistics v hv
  obtain ⟨_,_,_,_,hS,hL,hmu⟩ := o.tail_reversal v hv
  have hSfinite := hS2.eventually_lt hS1 hS
  have hLfinite := hL1.eventually_lt hL2 hL
  have hmufinite := hmu1.eventually_lt hmu2 hmu
  filter_upwards [hpos,hSfinite,hLfinite,hmufinite] with k hk hSk hLk hmuk
  exact ⟨hk.1,hk.2,hSk,hLk,hmuk⟩

theorem common_conull_IC_and_counts {F eta1 eta2 M}
    {f : ActualTwoCoefficientFamilies F eta1 eta2}
    (o : SourceTailOutcomes M f) :
    ∀ᵐv ∂(F : Measure ℝ),
      (∀m : f.Market,∀i : Fin m.1,
        (∀ᵐa ∂(f.lowerAt m).game.σ v,∀raw : JointAction 2,
          (Bayes.problem (f.lowerAt m).game i).payoff v raw ≤
            (Bayes.problem (f.lowerAt m).game i).payoff v a) ∧
        (∀ᵐa ∂(f.upperAt m).game.σ v,∀raw : JointAction 2,
          (Bayes.problem (f.upperAt m).game i).payoff v raw ≤
            (Bayes.problem (f.upperAt m).game i).payoff v a)) ∧
      (∀r,
        Tendsto (fun k=>((f.lowerAt (o.index k)).conditionalCount v).mass r) atTop
          (𝓝 ((o.lowerLaw v).mass r)) ∧
        Tendsto (fun k=>((f.upperAt (o.index k)).conditionalCount v).mass r) atTop
          (𝓝 ((o.upperLaw v).mass r))) :=
  f.common_conull_all_actions.and o.ae_count_limits

end SourceTailOutcomes

theorem load_limit_of_underfill {F eta1 eta2}
    {f : ActualTwoCoefficientFamilies F eta1 eta2}
    (index : ℕ→ f.Market) (hi : StrictMono (fun k=>(index k).1))
    (load : ℕ→ℝ)
    (hu : Tendsto (fun k=>2*(sourceCapacity (index k).1 : ℝ)/(index k).1-load k)
      atTop (𝓝 0)) : Tendsto load atTop (𝓝 (99/100:ℝ)) := by
  have hratio := sourceCapacity_ratio_tendsto.comp hi.tendsto_atTop
  have hcap : Tendsto (fun k=>2*(sourceCapacity (index k).1 : ℝ)/(index k).1)
      atTop (𝓝 (99/100:ℝ)) := by
    simpa only [Function.comp_apply,mul_div_assoc,
      show (2:ℝ)*(99/200)=99/100 by norm_num] using hratio.const_mul (2:ℝ)
  have hh := hcap.sub hu
  simpa only [sub_sub_cancel,sub_zero] using hh

theorem source_outcomes_of_finite_output {eta1 eta2 : ℝ}
    (p : Parameters eta1 eta2) (out : BothOriginalFiniteFamiliesAndLimits p) :
    Nonempty (SourceTailOutcomes p.tailFloor out.families) := by
  let f := out.families
  let l := out.limits
  have hlim1 : ∀ᵐv ∂(commonLaw p : Measure ℝ),∀r,
      Tendsto (fun k=>((f.lowerAt (l.index k)).conditionalCount v).mass r) atTop
        (𝓝 ((l.lowerLaw v).mass r)) := by
    filter_upwards [l.ae_count_limits] with v hv
    exact fun r=>(hv r).1
  have hlim2 : ∀ᵐv ∂(commonLaw p : Measure ℝ),∀r,
      Tendsto (fun k=>((f.upperAt (l.index k)).conditionalCount v).mass r) atTop
        (𝓝 ((l.upperLaw v).mass r)) := by
    filter_upwards [l.ae_count_limits] with v hv
    exact fun r=>(hv r).2
  have hagg1 := bounded_count_aggregate_passage (commonLaw p)
    (fun k=>(f.lowerAt (l.index k)).conditionalCount) l.lowerLaw
    (fun k r=>(f.lowerAt (l.index k)).measurable_conditionalCount_mass r) hlim1
  have hagg2 := bounded_count_aggregate_passage (commonLaw p)
    (fun k=>(f.upperAt (l.index k)).conditionalCount) l.upperLaw
    (fun k r=>(f.upperAt (l.index k)).measurable_conditionalCount_mass r) hlim2
  let Q1 := ∫v,(l.lowerLaw v).success ∂(commonLaw p : Measure ℝ)
  let Q2 := ∫v,(l.upperLaw v).success ∂(commonLaw p : Measure ℝ)
  have hQ1 : Tendsto (fun k=> Bayes.finiteCoverage (f.lowerAt (l.index k)).game)
      atTop (𝓝 Q1) := by
    simpa only [Q1,NativeFinite.coverage_eq_original_integral] using hagg1.1
  have hQ2 : Tendsto (fun k=> Bayes.finiteCoverage (f.upperAt (l.index k)).game)
      atTop (𝓝 Q2) := by
    simpa only [Q2,NativeFinite.coverage_eq_original_integral] using hagg2.1
  have hL1 : Tendsto (fun k=> Bayes.finiteLoad (f.lowerAt (l.index k)).game)
      atTop (𝓝 (99/100:ℝ)) :=
    load_limit_of_underfill l.index l.increasing _ l.underfill_lower
  have hL2 : Tendsto (fun k=> Bayes.finiteLoad (f.upperAt (l.index k)).game)
      atTop (𝓝 (99/100:ℝ)) :=
    load_limit_of_underfill l.index l.increasing _ l.underfill_upper
  have hintL1 : (∫v,(l.lowerLaw v).load ∂(commonLaw p : Measure ℝ))=99/100 := by
    have hh : Tendsto (fun k=> Bayes.finiteLoad (f.lowerAt (l.index k)).game)
        atTop (𝓝 (∫v,(l.lowerLaw v).load ∂(commonLaw p : Measure ℝ))) := by
      simpa only [NativeFinite.load_eq_original_integral] using hagg1.2
    exact tendsto_nhds_unique hh hL1
  have hintL2 : (∫v,(l.upperLaw v).load ∂(commonLaw p : Measure ℝ))=99/100 := by
    have hh : Tendsto (fun k=> Bayes.finiteLoad (f.upperAt (l.index k)).game)
        atTop (𝓝 (∫v,(l.upperLaw v).load ∂(commonLaw p : Measure ℝ))) := by
      simpa only [NativeFinite.load_eq_original_integral] using hagg2.2
    exact tendsto_nhds_unique hh hL2
  have hQ1pos : 0< Q1 := positive_coverage_from_load (commonLaw p)
    l.lowerLaw l.measurable_lower hintL1
  have hQ2pos : 0< Q2 := positive_coverage_from_load (commonLaw p)
    l.upperLaw l.measurable_upper hintL2
  have hgap : partialMass p.center*(p.center.theta-oneMixedMass p.center)≤ Q1-Q2 :=
    aggregate_coverage_gap p.lawInput p.center.theta (oneMixedMass p.center)
      l.lowerLaw l.upperLaw
      (measurable_count_success _ l.measurable_lower)
      (measurable_count_success _ l.measurable_upper)
      l.low_lower l.low_upper l.partial_lower l.partial_upper l.fixed_upper_lower
  have hQlt : Q2< Q1 := by linarith [p.aggregate_margin]
  have hmu := strict_inverse_coverage hQ1pos hQ2pos hQlt
    (by norm_num : (0:ℝ)<99/100)
  refine ⟨{
    index := l.index
    increasing := l.increasing
    lowerLaw := l.lowerLaw
    upperLaw := l.upperLaw
    measurable_lower := l.measurable_lower
    measurable_upper := l.measurable_upper
    ae_count_limits := l.ae_count_limits
    fixed_tail_count_limits := l.fixed_tail_count_limits
    lower_tail := l.lower_tail
    tail_reversal := ?_
    Q1 := Q1
    Q2 := Q2
    Q1_eq := rfl
    Q2_eq := rfl
    Q1_pos := hQ1pos
    Q2_pos := hQ2pos
    coverage_lower := hQ1
    coverage_upper := hQ2
    load_lower := hL1
    load_upper := hL2
    multiplicity_lower := hL1.div hQ1 (ne_of_gt hQ1pos)
    multiplicity_upper := hL2.div hQ2 (ne_of_gt hQ2pos)
    aggregate_reversal := ⟨hQlt,hmu⟩ }⟩
  intro v hv
  have hb := p.boundary.response_mem l.multiplier l.multiplier_mem v
    (p.tail_above_boundary.le.trans hv)
  have hu := transfer_strict_outcomes p.center p.rect p.analytic.receipt
    l.multiplier l.multiplier_mem (p.boundary.response l.multiplier v) hb
    (l.upperLaw v) (l.upper_tail_failure v hv) (l.upper_tail_duplicates v hv)
  have hs : (l.lowerLaw v).success=1 := by
    rw [l.lower_tail v hv]
    norm_num [CountLaw.success,successIndicator]
  have hl : (l.lowerLaw v).load=1 := by
    rw [l.lower_tail v hv]
    norm_num [CountLaw.load]
  exact ⟨hs,hl,by rw [hs,hl]; norm_num,hu⟩

def SourceAffinePartII (eta1 eta2 : ℝ) : Prop :=
  ∃F : ProbabilityMeasure ℝ,NullSingletonClass (F : Measure ℝ) ∧
    ∃f : ActualTwoCoefficientFamilies F eta1 eta2,∃index : ℕ→ f.Market,
      StrictMono (fun k=>(index k).1) ∧
      ∃Q1 Q2 : ℝ,0< Q1 ∧ 0< Q2 ∧ Q2< Q1 ∧ (99/100)/Q1<(99/100)/Q2 ∧
        Tendsto (fun k=> Bayes.finiteCoverage (f.lowerAt (index k)).game) atTop (𝓝 Q1) ∧
        Tendsto (fun k=> Bayes.finiteCoverage (f.upperAt (index k)).game) atTop (𝓝 Q2) ∧
        Tendsto (fun k=> Bayes.finiteLoad (f.lowerAt (index k)).game) atTop (𝓝 (99/100:ℝ)) ∧
        Tendsto (fun k=> Bayes.finiteLoad (f.upperAt (index k)).game) atTop (𝓝 (99/100:ℝ)) ∧
        Tendsto (fun k=> Bayes.finiteLoad (f.lowerAt (index k)).game /
          Bayes.finiteCoverage (f.lowerAt (index k)).game) atTop (𝓝 ((99/100)/Q1)) ∧
        Tendsto (fun k=> Bayes.finiteLoad (f.upperAt (index k)).game /
          Bayes.finiteCoverage (f.upperAt (index k)).game) atTop (𝓝 ((99/100)/Q2))

theorem affine_part_ii_of_outcomes {F : ProbabilityMeasure ℝ} {eta1 eta2 M : ℝ}
    (hF : NullSingletonClass (F : Measure ℝ))
    {f : ActualTwoCoefficientFamilies F eta1 eta2} (o : SourceTailOutcomes M f) :
    SourceAffinePartII eta1 eta2 :=
  ⟨F,hF,f,o.index,o.increasing,o.Q1,o.Q2,o.Q1_pos,o.Q2_pos,
    o.aggregate_reversal.1,o.aggregate_reversal.2,o.coverage_lower,o.coverage_upper,
    o.load_lower,o.load_upper,o.multiplicity_lower,o.multiplicity_upper⟩

end FCAppendix.Affine.Hybrid.Tail03
