import FCAppendix.Affine.Uniform06.LiteralLowDuplicate
import FCAppendix.Affine.LowBody.ExpectedPayoffContinuity
import FCAppendix.Affine.LowBody.NoisyExpectedLoss

noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralPrefixContinuity

open MeasureTheory Set Filter Topology LowBody
open LiteralExperiment LiteralKernelMeasurable LiteralPrefixStieltjes
open LiteralLowDuplicate SourceGuardGeometry PureRankCounts EqualCanonicalRegularity
open FCAppendix.Affine.Uniform07
open scoped BigOperators

def boundedBid (U : ℝ) (hU : 0 ≤ U) (b : ℝ) : LowValue U :=
  ⟨max 0 (min b U), le_max_left _ _, max_le hU (min_le_right _ _)⟩

theorem measurable_boundedBid (U : ℝ) (hU : 0 ≤ U) :
    Measurable (boundedBid U hU) := by
  apply Measurable.subtype_mk
  fun_prop

theorem boundedBid_eq {U : ℝ} (hU : 0 ≤ U) {b : ℝ}
    (hb : b ∈ Icc (0:ℝ) U) : (boundedBid U hU b).1=b := by
  simp only [boundedBid,min_eq_left hb.2,max_eq_right hb.1]

theorem compact_representation (G : Measure ℝ) [IsProbabilityMeasure G]
    {U : ℝ} (hU : 0 ≤ U) (hbound : ∀ᵐ b ∂G, b ∈ Icc (0:ℝ) U)
    (hatom : ∀ b : ℝ, G {b}=0) :
    let μ := G.map (boundedBid U hU)
    realLowLaw μ=G ∧ NullSingletonClass μ := by
  dsimp only
  let μ := G.map (boundedBid U hU)
  have he : realLowLaw μ=G := by
    unfold realLowLaw
    rw [Measure.map_map measurable_subtype_coe (measurable_boundedBid U hU)]
    calc
      _=G.map id := Measure.map_congr (hbound.mono fun b hb => boundedBid_eq hU hb)
      _=G := Measure.map_id
  refine ⟨he,⟨fun b => ?_⟩⟩
  have hs : (Subtype.val : LowValue U → ℝ) ⁻¹' {b.1}={b} := by
    ext a
    simp only [mem_preimage,mem_singleton_iff]
    exact ⟨Subtype.ext,congrArg Subtype.val⟩
  have hh := congrArg (fun ν : Measure ℝ => ν {b.1}) he
  rw [realLowLaw,Measure.map_apply measurable_subtype_coe (measurableSet_singleton _),hs] at hh
  exact hh.trans (hatom b.1)

variable {N : ℕ}

def literalExpectedPayoff (t ξ : ℝ) (G : Measure ℝ) (c N : ℕ)
    (w b : ℝ) : ℝ :=
  ∫ ω : Fin N → RowRival, literalRowPayoff ξ c w (b,ω)
    ∂Measure.pi (fun _ : Fin N => sourceRivalLaw t G)

theorem rowBids_lowRowPoint {U : ℝ} (kind : Fin N → Fin 4)
    (b : ℝ) (r : Fin N → LowValue U) :
    rowBids b (fun j => lowRowPoint (kind j,r j))=actualPatternBids kind U b r := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · rfl
  · by_cases hk : kind k=0 <;>
      simp [rowBids,lowRowPoint,actualPatternBids,hk]

theorem literal_expected_eq_exact {t ξ U : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (μ : ProbabilityMeasure (LowValue U))
    (c N : ℕ) (w b : ℝ) :
    literalExpectedPayoff t ξ (realLowLaw (μ : Measure (LowValue U))) c N w b=
      exactExpectedPayoff N U ξ c
        (categoryLaw t 0 (1-t) ht.1 (by norm_num) (sub_nonneg.mpr ht.2)
          (by ring) (realLowLaw (μ : Measure (LowValue U)))) μ (w,b) := by
  have hh := integral_lowRowProfile t 0 (1-t) ht.1 (by norm_num)
    (sub_nonneg.mpr ht.2) (by ring) (μ : Measure (LowValue U)) N
    (fun ω => literalRowPayoff ξ c w (b,ω))
    ((measurable_literalRowPayoff hξ hξ1 c w).comp
      (measurable_const.prodMk measurable_id))
    (|w|+(3+2*|1-ξ|)*|b|) (abs_literalRowPayoff_le hξ hξ1 c w b)
  change literalExpectedPayoff t ξ (realLowLaw (μ : Measure (LowValue U))) c N w b=_ at hh
  rw [hh]
  unfold FiniteLaw.expect exactExpectedPayoff patternExpectedPayoff
  apply Finset.sum_congr rfl
  intro kind _
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun r => by
    change patternPayoff ξ c kind w (rowBids b (fun j => lowRowPoint (kind j,r j)))=_
    rw [rowBids_lowRowPoint]
    rfl

theorem continuousAt_literalExpectedPayoff
    {t ξ U b : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 ≤ U)
    (G : Measure ℝ) [IsProbabilityMeasure G]
    (hbound : ∀ᵐ z ∂G, z ∈ Icc (0:ℝ) U) (hatom : ∀ z : ℝ, G {z}=0)
    (c N : ℕ) (w : ℝ) (hb : 0 < b) :
    ContinuousAt (fun p : ℝ × ℝ => literalExpectedPayoff t ξ G c N p.1 p.2) (w,b) := by
  let μ₀ := G.map (boundedBid U hU)
  letI : IsProbabilityMeasure μ₀ :=
    Measure.isProbabilityMeasure_map (measurable_boundedBid U hU).aemeasurable
  obtain ⟨he,ha⟩ := compact_representation G hU hbound hatom
  letI : NullSingletonClass μ₀ := ha
  let μ : ProbabilityMeasure (LowValue U) := ⟨μ₀,inferInstance⟩
  letI : NullSingletonClass (μ : Measure (LowValue U)) := ha
  have heq : (fun p : ℝ × ℝ => literalExpectedPayoff t ξ G c N p.1 p.2)=
      exactExpectedPayoff N U ξ c
        (categoryLaw t 0 (1-t) ht.1 (by norm_num) (sub_nonneg.mpr ht.2)
          (by ring) (realLowLaw μ₀)) μ := by
    funext p
    rw [← he]
    exact literal_expected_eq_exact ht hξ hξ1 μ c N p.1 p.2
  rw [heq]
  exact continuousAt_exactExpectedPayoff (N := N) hξ hξ1 c _ μ (w,b) hb

def extendedSuccess (t ξ : ℝ) (G : Measure ℝ) (c N : ℕ) (b : ℝ) : ℝ :=
  literalExpectedPayoff t ξ G c N 1 b-literalExpectedPayoff t ξ G c N 0 b

def extendedDuplicate (t ξ : ℝ) (G : Measure ℝ) (c N : ℕ) (b : ℝ) : ℝ :=
  (-literalExpectedPayoff t ξ G c N 0 b-b*extendedSuccess t ξ G c N b)/((1-2*ξ)*b)

theorem extensions_continuous_positive {t ξ U : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hη : 1-2*ξ ≠ 0)
    (hU : 0 ≤ U) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hbound : ∀ᵐ z ∂G, z ∈ Icc (0:ℝ) U) (hatom : ∀ z : ℝ, G {z}=0)
    (c N : ℕ) :
    ContinuousOn (extendedSuccess t ξ G c N) (Ioi 0) ∧
      ContinuousOn (extendedDuplicate t ξ G c N) (Ioi 0) := by
  have hF (w b : ℝ) (hb : 0 < b) :
      ContinuousAt (literalExpectedPayoff t ξ G c N w) b :=
    (continuousAt_literalExpectedPayoff ht hξ hξ1 hU G hbound hatom c N w hb).comp
      (f := fun x : ℝ => (w,x)) (x := b) (by fun_prop)
  have hS (b : ℝ) (hb : 0 < b) : ContinuousAt (extendedSuccess t ξ G c N) b :=
    (hF 1 b hb).sub (hF 0 b hb)
  refine ⟨fun b hb => (hS b hb).continuousWithinAt,?_⟩
  intro b hb
  exact (((hF 0 b hb).neg.sub (continuousAt_id.mul (hS b hb))).div
    (continuousAt_const.mul continuousAt_id) (mul_ne_zero hη hb.ne')).continuousWithinAt

theorem first_eq_pureServed {ι : Type*} [DecidableEq ι]
    (P : Finset ι × Finset ι) (j : ι) : first j P=pureServed P j := by
  simp only [first_eq_indicator,pureServed,Finset.mem_union]

theorem row_low_payoff_eq {ξ B : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B)
    (hB : B ≤ g.multiplier-g.radius) (margin : (Fin N → Fin 4) → ℝ)
    (w b : ℝ) (hb : b ∈ Icc (0:ℝ) B) (ω : Fin N → RowRival) :
    Rank.payoff (1-2*ξ) w b
      ((rowLaw ξ (1-ξ) c g margin b ω).expect (first 0))
      ((rowLaw ξ (1-ξ) c g margin b ω).expect (duplicate 0))=
        literalRowPayoff ξ c w (b,ω) := by
  rw [literalRowPayoff,patternPayoff_outcomes]
  change Rank.payoff (1-2*ξ) w b _ _=(w-b)*
    patternServed ξ c (fun j => (ω j).1) (rowBids b ω)-
      (1-2*ξ)*b*patternDuplicate ξ c (fun j => (ω j).1) (rowBids b ω)
  by_cases he : rowResidual c 0 ω=rowResidual c 1 ω
  · have heT : (patternTemplate c (fun j => (ω j).1)).residual₀=
      (patternTemplate c (fun j => (ω j).1)).residual₁ := he
    simp only [rowLaw,continuationLaw,empty_completion_first hξ hξ1,
      empty_completion_duplicate hξ hξ1,row_complement_eq_equal ξ c b ω he,
      patternServed,patternDuplicate,if_pos heT,Rank.payoff,equalMarginal]
    rfl
  · have heT : ¬(patternTemplate c (fun j => (ω j).1)).residual₀=
      (patternTemplate c (fun j => (ω j).1)).residual₁ := he
    have hh := unequal_low_full_eq_pure hξ hξ1 (by linarith : 1-ξ ≤ 1)
      {g with countMargin := margin (fun j => (ω j).1)}
      (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)
      hg.margin_pos hg.population_pos hg.radius_nonneg hg.requiredDemand_pos
      hg.rejectionScale_pos hg.lower_pos (rowBids_outside c b ω) 0
      (by simpa only [rowBids,Fin.cons_zero] using hb.1)
      (by simpa only [rowBids,Fin.cons_zero] using hb.2.trans hB)
      (by simpa only [rowBids,Fin.cons_zero] using hb.2.trans hg.rejection) he
    simpa only [rowLaw,patternServed,patternDuplicate,if_neg heT,Rank.payoff,
      first_eq_pureServed,literal_duplicate_eq_pureDuplicate] using
      congrArg₂ (fun s d => (w-b)*s-(1-2*ξ)*b*d) hh.1 hh.2

theorem actual_low_payoff_eq {t ξ B : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (G : Measure ℝ) [IsProbabilityMeasure G]
    (c N : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B)
    (hB : B ≤ g.multiplier-g.radius) (margin : (Fin N → Fin 4) → ℝ)
    (w b : ℝ) (hb : b ∈ Icc (0:ℝ) B) :
    Rank.payoff (1-2*ξ) w b (actualSuccess t ξ (1-ξ) G c N g margin b)
      (actualDuplicate t ξ (1-ξ) G c N g margin b)=
        literalExpectedPayoff t ξ G c N w b := by
  letI := sourceRivalLaw_probability ht G
  let P := Measure.pi fun _ : Fin N => sourceRivalLaw t G
  have hS := integrable_row_first hξ hξ1 (1-ξ) c g margin b P
  have hD := integrable_row_duplicate hξ hξ1 (1-ξ) c g margin b P
  unfold Rank.payoff actualSuccess actualDuplicate literalExpectedPayoff
  change (w-b)*(∫ ω, (rowLaw ξ (1-ξ) c g margin b ω).expect (first 0) ∂P)-
    (1-2*ξ)*b*(∫ ω, (rowLaw ξ (1-ξ) c g margin b ω).expect (duplicate 0) ∂P)=
      ∫ ω, literalRowPayoff ξ c w (b,ω) ∂P
  rw [← integral_const_mul,← integral_const_mul,
    ← integral_sub (hS.const_mul (w-b)) (hD.const_mul ((1-2*ξ)*b))]
  exact integral_congr_ae (Eventually.of_forall fun ω => row_low_payoff_eq hξ hξ1
    c g hg hB margin w b hb ω)

theorem actual_eq_extensions_on_low_prefix {t ξ B : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hη : 1-2*ξ ≠ 0)
    (G : Measure ℝ) [IsProbabilityMeasure G] (c N : ℕ)
    (g : GuardData) (hg : PrefixConditions ξ g B) (hB : B ≤ g.multiplier-g.radius)
    (margin : (Fin N → Fin 4) → ℝ) {b : ℝ} (hb : 0 < b) (hbB : b ≤ B) :
    actualSuccess t ξ (1-ξ) G c N g margin b=extendedSuccess t ξ G c N b ∧
      actualDuplicate t ξ (1-ξ) G c N g margin b=extendedDuplicate t ξ G c N b := by
  have h0 := actual_low_payoff_eq ht hξ hξ1 G c N g hg hB margin 0 b ⟨hb.le,hbB⟩
  have h1 := actual_low_payoff_eq ht hξ hξ1 G c N g hg hB margin 1 b ⟨hb.le,hbB⟩
  unfold Rank.payoff at h0 h1
  have hs : actualSuccess t ξ (1-ξ) G c N g margin b=extendedSuccess t ξ G c N b := by
    unfold extendedSuccess
    linarith
  refine ⟨hs,?_⟩
  unfold extendedDuplicate
  apply (eq_div_iff (mul_ne_zero hη hb.ne')).mpr
  rw [← hs]
  nlinarith

theorem actual_low_payoff_eq_extension {t ξ B : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hη : 1-2*ξ ≠ 0)
    (G : Measure ℝ) [IsProbabilityMeasure G] (c N : ℕ)
    (g : GuardData) (hg : PrefixConditions ξ g B) (hB : B ≤ g.multiplier-g.radius)
    (margin : (Fin N → Fin 4) → ℝ) (w : ℝ) {b : ℝ} (hb : b ∈ Icc (0:ℝ) B) :
    Rank.payoff (1-2*ξ) w b (actualSuccess t ξ (1-ξ) G c N g margin b)
      (actualDuplicate t ξ (1-ξ) G c N g margin b)=
        Rank.payoff (1-2*ξ) w b (extendedSuccess t ξ G c N b)
          (extendedDuplicate t ξ G c N b) := by
  by_cases hz : b=0
  · subst b
    have h0 := actual_low_payoff_eq ht hξ hξ1 G c N g hg hB margin 0 0 hb
    have h1 := actual_low_payoff_eq ht hξ hξ1 G c N g hg hB margin 1 0 hb
    have hs : actualSuccess t ξ (1-ξ) G c N g margin 0=extendedSuccess t ξ G c N 0 := by
      unfold Rank.payoff at h0 h1
      unfold extendedSuccess
      nlinarith
    simp only [Rank.payoff,hs,sub_zero,mul_zero,zero_mul]
  · have hp : 0 < b := lt_of_le_of_ne hb.1 (Ne.symm hz)
    obtain ⟨hs,hd⟩ := actual_eq_extensions_on_low_prefix ht hξ hξ1 hη G c N g hg hB margin hp hb.2
    rw [hs,hd]

theorem actual_continuousOn_low_prefix {t ξ B U : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hη : 1-2*ξ ≠ 0)
    (hU : 0 ≤ U) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hbound : ∀ᵐ z ∂G, z ∈ Icc (0:ℝ) U) (hatom : ∀ z : ℝ, G {z}=0)
    (c N : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B)
    (hB : B ≤ g.multiplier-g.radius) (margin : (Fin N → Fin 4) → ℝ) :
    ContinuousOn (actualSuccess t ξ (1-ξ) G c N g margin) (Ioc 0 B) ∧
      ContinuousOn (actualDuplicate t ξ (1-ξ) G c N g margin) (Ioc 0 B) := by
  have hc := extensions_continuous_positive ht hξ hξ1 hη hU G hbound hatom c N
  constructor
  · apply (hc.1.mono (fun _ h => h.1)).congr
    intro b hb
    exact (actual_eq_extensions_on_low_prefix ht hξ hξ1 hη G c N g hg hB margin hb.1 hb.2).1
  · apply (hc.2.mono (fun _ h => h.1)).congr
    intro b hb
    exact (actual_eq_extensions_on_low_prefix ht hξ hξ1 hη G c N g hg hB margin hb.1 hb.2).2

end FCAppendix.Affine.Uniform06.LiteralPrefixContinuity
