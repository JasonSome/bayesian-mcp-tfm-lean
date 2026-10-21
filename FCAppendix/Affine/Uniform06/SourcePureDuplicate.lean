import FCAppendix.Affine.Uniform06.PureDuplicateRare
import FCAppendix.Affine.Uniform06.CapacityFloor

noncomputable section
namespace FCAppendix.Affine.Uniform06.PureDuplicateRare

open MeasureTheory ProbabilityTheory Set Filter
open LowBody PureRankSelector PureDuplicateIntervals PureRankCounts
open FCAppendix.Affine.Uniform07 EqualCanonicalRegularity
open scoped BigOperators

section Interval
variable {N : ℕ}

def rareCluster (c : ℕ) (κ y : ℝ) (B : Set ℝ) : Set (Fin (N+1) → RowRival) :=
  {ω | (∃ i, ω i ∈ lowCluster B) ∧
    N+3-2*c ≤ lowBelowCount (κ*y) ω}

theorem measurableSet_rareCluster (c : ℕ) (κ y : ℝ)
    (B : Set ℝ) (hB : MeasurableSet B) :
    MeasurableSet (rareCluster (N := N) c κ y B) := by
  have h₁ : MeasurableSet {ω : Fin (N+1) → RowRival | ∃ i, ω i ∈ lowCluster B} := by
    simp only [setOf_exists]
    exact MeasurableSet.iUnion fun i =>
      (measurable_pi_apply i) (measurableSet_lowCluster B hB)
  exact h₁.inter ((PiBinomial.measurable_count (lowCluster (Iic (κ*y)))
    (measurableSet_lowCluster _ measurableSet_Iic) Finset.univ) measurableSet_Ici)

theorem pure_increment_le_rareCluster
    (c : ℕ) {κ x y : ℝ} (hκ : 0 < κ) (hκ1 : κ < 1)
    (hx : 0 < x) (hxy : x < y) (ω : Fin (N+1) → RowRival)
    (hω : ∀ j, (ω j).1=0 → 0 ≤ (ω j).2)
    (hno : ∀ j, (ω j).1 ≠ 1) :
    rowPureDuplicate κ c y ω-rowPureDuplicate κ c x ω ≤
      (rareCluster c κ y (Icc x y ∪ Icc (κ*x) (κ*y))).indicator (fun _ => (1:ℝ)) ω := by
  classical
  by_cases hA : ω ∈ rareCluster c κ y (Icc x y ∪ Icc (κ*x) (κ*y))
  · rw [Set.indicator_of_mem hA]
    linarith [(rowPureDuplicate_bounds κ c y ω).2,(rowPureDuplicate_bounds κ c x ω).1]
  · rw [Set.indicator_of_notMem hA]
    by_cases hx0 : rowPureDuplicate κ c x ω=0
    · have hy0 : rowPureDuplicate κ c y ω=0 := by
        by_contra hy0
        have hy1 : rowPureDuplicate κ c y ω=1 := by
          unfold rowPureDuplicate pureDuplicate at *
          split_ifs at * <;> simp_all
        have hc := row_duplicate_acquisition_in_harmfulCluster c hκ hx hxy ω hω hx0 hy1
        exact hA ⟨hc.2,duplicate_requires_many_scaled_low c hκ.le hκ1
          (hx.trans hxy) ω hno hy1⟩
      rw [hx0,hy0]
      norm_num
    · have hx1 : rowPureDuplicate κ c x ω=1 := by
        unfold rowPureDuplicate pureDuplicate at *
        split_ifs at * <;> simp_all
      rw [hx1]
      linarith [(rowPureDuplicate_bounds κ c y ω).2]

theorem original_pure_duplicate_rare_increment
    {t κ x y : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hx : 0 < x) (hxy : x < y)
    (G : Measure ℝ) [IsProbabilityMeasure G] (hG : ∀ᵐ b ∂G, 0 ≤ b)
    (hatom : ∀ b : ℝ, G {b}=0) (c : ℕ) (hcap : 2*c ≤ N+2) :
    expectedPureDuplicate (N := N+1) t 0 (1-t) κ G c y-
      expectedPureDuplicate (N := N+1) t 0 (1-t) κ G c x ≤
      (N+1:ℕ)*(t*G.real (Ioc x y)+t*G.real (Ioc (κ*x) (κ*y)))*
        (Measure.pi fun _ : Fin N => sourceRivalLaw t G).real
          {ω | N+2-2*c ≤ lowBelowCount (κ*y) ω} := by
  let μ := sourceRivalLaw t G
  letI : IsProbabilityMeasure μ := sourceRivalLaw_probability ⟨ht,ht1⟩ G
  let P := Measure.pi fun _ : Fin (N+1) => μ
  let B := Icc x y ∪ Icc (κ*x) (κ*y)
  let E := lowCluster (Iic (κ*y))
  let A := rareCluster (N := N) c κ y B
  have hBm : MeasurableSet B := measurableSet_Icc.union measurableSet_Icc
  have hEm : MeasurableSet E := measurableSet_lowCluster _ measurableSet_Iic
  have hAm : MeasurableSet A := measurableSet_rareCluster c κ y B hBm
  have hno : ∀ᵐ ω ∂P, ∀ j, (ω j).1 ≠ 1 := source_iid_row_no_active ⟨ht,ht1⟩ G
  have hnon : ∀ᵐ ω ∂P, ∀ j, 0 ≤ (ω j).2 :=
    iid_rows_ae_bid_nonnegative μ (rivalLaw_ae_bid_nonnegative t 0 (1-t) G hG)
  have hi := integral_mono_ae
    ((integrable_rowPureDuplicate κ c y P).sub (integrable_rowPureDuplicate κ c x P))
    ((integrable_const (1:ℝ)).indicator hAm) (by
      filter_upwards [hno,hnon] with ω hω hn
      exact pure_increment_le_rareCluster c hκ hκ1 hx hxy ω (fun j _ => hn j) hω)
  simp only [Pi.sub_apply] at hi
  rw [integral_sub (integrable_rowPureDuplicate κ c y P)
    (integrable_rowPureDuplicate κ c x P),integral_indicator_const 1 hAm,smul_eq_mul,mul_one] at hi
  have hk : N+3-2*c=(N+2-2*c)+1 := by omega
  have hprob : P.real A ≤ (N+1:ℕ)*(t*G.real B)*
      (Measure.pi fun _ : Fin N => μ).real
        {ω | N+2-2*c ≤ lowBelowCount (κ*y) ω} := by
    have hh := cluster_and_many_probability (N := N) μ (lowCluster B) E
      (measurableSet_lowCluster B hBm) hEm (N+2-2*c)
    have hμ : μ.real (lowCluster B) = t*G.real B := by
      exact lowCluster_probability t 0 (1-t) ht G B hBm
    rw [hμ] at hh
    simpa only [A,rareCluster,hk,E,lowBelowCount] using hh
  have hmass : t*G.real B ≤ t*G.real (Ioc x y)+t*G.real (Ioc (κ*x) (κ*y)) := by
    have hh := mul_le_mul_of_nonneg_left
      (measureReal_union_le (μ := G) (Icc x y) (Icc (κ*x) (κ*y))) ht
    rw [real_Icc_eq_Ioc_of_atomless G hatom,
      real_Icc_eq_Ioc_of_atomless G hatom] at hh
    simpa only [B,mul_add] using hh
  have htail0 : 0 ≤ (Measure.pi fun _ : Fin N => μ).real
      {ω | N+2-2*c ≤ lowBelowCount (κ*y) ω} := measureReal_nonneg
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg (N+1))) htail0
  exact (hi.trans hprob).trans hm

end Interval

section PrimitiveSource

theorem source_pure_duplicate_exponential (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hfloor : ∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2)
    {m : ℕ} (hm : 4 ≤ m) :
    ∀ b : ℝ, 0 < b → b ≤ RankCutoff.Mstar i →
      expectedPureDuplicate (N := m-1) (cutoff i) 0 (1-cutoff i) (kappa i)
        (G.map Prod.snd) (capacity m) b ≤ Real.exp (-(9/1000000:ℝ)*m) := by
  let Gb := G.map Prod.snd
  letI : IsProbabilityMeasure Gb := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let μ := sourceRivalLaw (cutoff i) Gb
  letI : IsProbabilityMeasure μ := sourceRivalLaw_probability
    ⟨(cutoff_pos i).le,(cutoff_lt_one i).le⟩ Gb
  let P := Measure.pi fun _ : Fin (m-1) => μ
  have hc := PhysicalRates.capacity_positive (show 3 ≤ m by omega)
  have hcR := (PhysicalRates.capacity_floor_bounds m).2
  have hcm : 2*capacity m ≤ m := by
    have hR : (2*capacity m:ℝ) ≤ m := by
      norm_num only [rho] at hcR
      nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ (m:ℝ))]
    exact_mod_cast hR
  have hκ : 0 < kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hκ1 : kappa i < 1 := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hno : ∀ᵐ ω ∂P, ∀ j, (ω j).1 ≠ 1 :=
    source_iid_row_no_active ⟨(cutoff_pos i).le,(cutoff_lt_one i).le⟩ Gb
  intro b hb hbM
  let E := lowCluster (Iic (kappa i*b))
  let A : Set (Fin (m-1) → RowRival) :=
    {ω | m-2*capacity m ≤ PiBinomial.count E Finset.univ ω}
  have hEm : MeasurableSet E := measurableSet_lowCluster _ measurableSet_Iic
  have hAm : MeasurableSet A :=
    (PiBinomial.measurable_count E hEm Finset.univ) measurableSet_Ici
  have hpoint : ∀ᵐ ω ∂P, rowPureDuplicate (kappa i) (capacity m) b ω ≤
      A.indicator (fun _ => (1:ℝ)) ω := by
    filter_upwards [hno] with ω hω
    by_cases hA : ω ∈ A
    · rw [Set.indicator_of_mem hA]
      exact (rowPureDuplicate_bounds (kappa i) (capacity m) b ω).2
    · rw [Set.indicator_of_notMem hA]
      have hzero : rowPureDuplicate (kappa i) (capacity m) b ω=0 := by
        by_contra hn
        have hdup : rowPureDuplicate (kappa i) (capacity m) b ω=1 := by
          unfold rowPureDuplicate pureDuplicate at *
          split_ifs at * <;> simp_all
        have hc' := duplicate_requires_many_scaled_low (capacity m) hκ.le hκ1 hb ω hω hdup
        apply hA
        change m-2*capacity m ≤ lowBelowCount (kappa i*b) ω
        omega
      rw [hzero]
  have hi := integral_mono_ae
    (integrable_rowPureDuplicate (kappa i) (capacity m) b P)
    ((integrable_const (1:ℝ)).indicator hAm) hpoint
  change (∫ ω, rowPureDuplicate (kappa i) (capacity m) b ω ∂P) ≤
    (∫ ω, A.indicator (fun _ => (1:ℝ)) ω ∂P) at hi
  rw [integral_indicator_const 1 hAm,smul_eq_mul,mul_one] at hi
  have hmass : μ.real E ≤ (17/20000:ℝ) := by
    dsimp only [μ,E,sourceRivalLaw]
    rw [lowCluster_probability (cutoff i) 0 (1-cutoff i) (cutoff_pos i).le Gb
      (Iic (kappa i*b)) measurableSet_Iic]
    exact (original_floor_low_rank_bound i G hvalue hfloor
      (source_scaled_prefix_receipt i hbM)).trans (RankCutoff.Mstar_bounds i).2.le
  have ht := source_low_count_upper_remaining μ E hEm hmass m (capacity m) (m-1)
    hcm (Nat.sub_le _ _) (by omega) hcR
  exact hi.trans ht

theorem source_pure_duplicate_stieltjes_interval (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hfloor : ∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2)
    (hatom : ∀ b : ℝ, (G.map Prod.snd) {b}=0)
    {m : ℕ} (hm : 4 ≤ m) :
    ∀ x y : ℝ, 0 < x → x < y → y ≤ RankCutoff.Mstar i →
      expectedPureDuplicate (N := m-1) (cutoff i) 0 (1-cutoff i) (kappa i)
        (G.map Prod.snd) (capacity m) y-
      expectedPureDuplicate (N := m-1) (cutoff i) 0 (1-cutoff i) (kappa i)
        (G.map Prod.snd) (capacity m) x ≤
        (m-1:ℕ)*((cutoff i)*(G.map Prod.snd).real (Ioc x y)+
          (cutoff i)*(G.map Prod.snd).real (Ioc (kappa i*x) (kappa i*y)))*
            Real.exp (-(9/1000000:ℝ)*m) := by
  let Gb := G.map Prod.snd
  letI : IsProbabilityMeasure Gb := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let μ := sourceRivalLaw (cutoff i) Gb
  letI : IsProbabilityMeasure μ := sourceRivalLaw_probability
    ⟨(cutoff_pos i).le,(cutoff_lt_one i).le⟩ Gb
  have hc := PhysicalRates.capacity_positive (show 3 ≤ m by omega)
  have hcR := (PhysicalRates.capacity_floor_bounds m).2
  have hcm : 2*capacity m ≤ m := by
    have hR : (2*capacity m:ℝ) ≤ m := by
      norm_num only [rho] at hcR
      nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ (m:ℝ))]
    exact_mod_cast hR
  have hκ : 0 < kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hκ1 : kappa i < 1 := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  intro x y hx hxy hy
  have hn₁ : m-2+1=m-1 := by omega
  have hn₂ : m-2+2=m := by omega
  have hinc := original_pure_duplicate_rare_increment (N := m-2)
    (cutoff_pos i).le (cutoff_lt_one i).le hκ hκ1 hx hxy Gb
    (source_floor_bid_nonnegative i G hfloor) hatom (capacity m) (by omega)
  rw [hn₁,hn₂] at hinc
  let E := lowCluster (Iic (kappa i*y))
  have hEm : MeasurableSet E := measurableSet_lowCluster _ measurableSet_Iic
  have hmass : μ.real E ≤ (17/20000:ℝ) := by
    dsimp only [μ,E,sourceRivalLaw]
    rw [lowCluster_probability (cutoff i) 0 (1-cutoff i) (cutoff_pos i).le Gb
      (Iic (kappa i*y)) measurableSet_Iic]
    exact (original_floor_low_rank_bound i G hvalue hfloor
      (source_scaled_prefix_receipt i hy)).trans (RankCutoff.Mstar_bounds i).2.le
  have ht := source_low_count_upper_remaining μ E hEm hmass m (capacity m) (m-2)
    hcm (Nat.sub_le _ _) (by omega) hcR
  apply hinc.trans
  exact mul_le_mul_of_nonneg_left ht
    (mul_nonneg (Nat.cast_nonneg (m-1))
      (add_nonneg (mul_nonneg (cutoff_pos i).le measureReal_nonneg)
        (mul_nonneg (cutoff_pos i).le measureReal_nonneg)))

end PrimitiveSource

end FCAppendix.Affine.Uniform06.PureDuplicateRare
