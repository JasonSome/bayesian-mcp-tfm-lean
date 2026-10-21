import FCAppendix.Affine.Uniform06.LiteralGuardRare
import FCAppendix.Affine.Uniform06.EntryThresholdNull

noncomputable section
namespace FCAppendix.Affine.Uniform06.GuardCornerNull

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
open LowBody Uniform07 LiteralExperiment
open FCAppendix.Affine.ClippedResidual

section PositiveSum
variable {Ω : Type*} [MeasurableSpace Ω]

theorem positive_sum_level_null (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f)
    (hnull : ∀ a : ℝ,0 < a → ∀ᵐ x ∂μ,f x ≠ a)
    (N : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin N => μ),(∑ j,f (ω j)) ≠ d := by
  have hj (j : Fin N) : ∀ᵐ ω ∂Measure.pi (fun _ : Fin N => μ),
      0 < f (ω j) → (∑ q,f (ω q)) ≠ d := by
    let A := fun ω : Fin N → Ω => ∑ q ∈ Finset.univ.erase j,f (ω q)
    let P := fun (u : Ω) (ω : Fin N → Ω) => 0 < f u → f u+A ω ≠ d
    have hA : Measurable A := Finset.measurable_sum _ fun q _ =>
      hf.comp (measurable_pi_apply q)
    have hPm : MeasurableSet {p : Ω × (Fin N → Ω) | P p.1 p.2} := by
      dsimp [P]
      measurability
    have hAu (u : Ω) (ω : Fin N → Ω) : A (Function.update ω j u)=A ω := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hq)]
    have hPi : ∀ u ω u',P u (Function.update ω j u') ↔ P u ω := by
      intro u ω u'
      simp only [P,hAu]
    have hfixed (ω : Fin N → Ω) : ∀ᵐ u ∂μ,P u ω := by
      by_cases hpos : 0 < d-A ω
      · filter_upwards [hnull (d-A ω) hpos] with u hu hfu he
        exact hu (by linarith)
      · exact ae_of_all _ fun u hfu he => hpos (by linarith)
    have hAE : ∀ᵐ u ∂μ,∀ᵐ ω ∂Measure.pi (fun _ : Fin N => μ),P u ω := by
      exact (Measure.ae_ae_comm hPm).mpr (ae_of_all _ hfixed)
    have hh := FCAppendix.Resample.ae_resample μ j P hPm hPi hAE
    filter_upwards [hh] with ω hω hpos he
    apply hω hpos
    have heq : (∑ q,f (ω q))=f (ω j)+A ω := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    rwa [← heq]
  filter_upwards [ae_all_iff.mpr hj] with ω hω he
  have hex : ∃ j,0 < f (ω j) := by
    by_contra hn
    push Not at hn
    have hs : (∑ j,f (ω j)) ≤ 0 := Finset.sum_nonpos (fun j _ => hn j)
    linarith
  obtain ⟨j,hj⟩ := hex
  exact hω j hj he

theorem countable_positive_sum_levels (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f)
    (hnull : ∀ a : ℝ,0 < a → ∀ᵐ x ∂μ,f x ≠ a)
    (N : ℕ) (d : ℕ → ℝ) (hd : ∀ c,0 < d c) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin N => μ),∀ c : ℕ,(∑ j,f (ω j)) ≠ d c :=
  ae_all_iff.mpr fun c => positive_sum_level_null μ hf hnull N (hd c)

end PositiveSum

theorem lowerTest_positive_atom_null (μ : Measure RowRival)
    (hnull : ∀ B : ℝ,∀ᵐ r ∂μ,r.1=0 → r.2 ≠ B)
    (F : ℝ → ℝ) {U : ℝ}
    (hcap : ∀ᵐ r ∂μ,r.1=0 → r.2 ≤ U)
    (hinj : ∀ {B C : ℝ},B ≤ U → C ≤ U → 0 < F B → 0 < F C → F B=F C → B=C)
    {a : ℝ} (ha : 0 < a) :
    ∀ᵐ r ∂μ,RivalGood.lowerTest F r ≠ a := by
  by_cases hex : ∃ B : ℝ,B ≤ U ∧ F B=a
  · obtain ⟨B,hBU,hBa⟩ := hex
    filter_upwards [hnull B,hcap] with r hr hc he
    by_cases ht : r.1=0
    · have hFa : F r.2=a := by simpa only [RivalGood.lowerTest,if_pos ht] using he
      exact hr ht (hinj (hc ht) hBU (by linarith) (by linarith) (hFa.trans hBa.symm))
    · have hz : (0:ℝ)=a := by simpa only [RivalGood.lowerTest,if_neg ht] using he
      linarith
  · filter_upwards [hcap] with r hc he
    by_cases ht : r.1=0
    · exact hex ⟨r.2,hc ht,by simpa only [RivalGood.lowerTest,if_pos ht] using he⟩
    · have hz : (0:ℝ)=a := by simpa only [RivalGood.lowerTest,if_neg ht] using he
      linarith

theorem exposure_positive_injective {ξ z U : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hz : 0 < z) (hcap : (1-ξ)*U ≤ z)
    {B C : ℝ} (hBU : B ≤ U) (hCU : C ≤ U)
    (hB : 0 < exposure ξ z B) (hC : 0 < exposure ξ z C)
    (he : exposure ξ z B=exposure ξ z C) : B=C := by
  have hzB : z < B := by
    by_contra hn
    have he0 := exposure_zero (ξ:=ξ) (le_of_not_gt hn)
    rw [he0] at hB
    exact (lt_irrefl 0) hB
  have hzC : z < C := by
    by_contra hn
    have he0 := exposure_zero (ξ:=ξ) (le_of_not_gt hn)
    rw [he0] at hC
    exact (lt_irrefl 0) hC
  exact EntryThresholdNull.exposure_bid_injective hξ hz hzB hzC
    ((mul_le_mul_of_nonneg_left hBU (sub_nonneg.mpr hξ1.le)).trans hcap)
    ((mul_le_mul_of_nonneg_left hCU (sub_nonneg.mpr hξ1.le)).trans hcap) he

theorem psi_positive_injective {d z B C : ℝ} (hd : 0 < d)
    (hB : 0 < PrefixRoot.psi d z B) (hC : 0 < PrefixRoot.psi d z C)
    (he : PrefixRoot.psi d z B=PrefixRoot.psi d z C) : B=C := by
  have hzB : z < B := by
    by_contra hn
    simp only [PrefixRoot.psi,max_eq_left (sub_nonpos.mpr (le_of_not_gt hn)),zero_div] at hB
    exact (lt_irrefl 0) hB
  have hzC : z < C := by
    by_contra hn
    simp only [PrefixRoot.psi,max_eq_left (sub_nonpos.mpr (le_of_not_gt hn)),zero_div] at hC
    exact (lt_irrefl 0) hC
  rw [PrefixRoot.psi,PrefixRoot.psi,max_eq_right (sub_pos.mpr hzB).le,
    max_eq_right (sub_pos.mpr hzC).le] at he
  have hdenB : 0 < d+(B-z) := add_pos hd (sub_pos.mpr hzB)
  have hdenC : 0 < d+(C-z) := add_pos hd (sub_pos.mpr hzC)
  have hc := (div_eq_div_iff hdenB.ne' hdenC.ne').mp he
  nlinarith

theorem original_guard_ramp_corners (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G]
    (hnull : ∀ a : ℝ,(G.map Prod.snd) {a}=0)
    {U : ℝ} (hcap : ∀ᵐ p ∂G,p.2 ≤ U) (N : ℕ) (g : GuardData)
    (hlo : 0 < g.multiplier-g.radius)
    (hclip : (1-xi i)*U ≤ g.multiplier-g.radius)
    (hd : 0 < g.rejectionScale) (hεM : 1 < g.margin*g.population) (b : ℝ) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin N => RawMixedSource.source i G),
      ∀ (c : ℕ) (k : Fin 2),
        exposure (xi i) (g.multiplier-g.radius) b+
          (∑ j,RivalGood.lowerTest (exposure (xi i) (g.multiplier-g.radius)) (ω j)) ≠
            (c:ℝ)+((k.val+1:ℕ):ℝ)*g.margin*g.population ∧
        PrefixRoot.psi g.rejectionScale g.rejectionRoot b+
          (∑ j,RivalGood.lowerTest (PrefixRoot.psi g.rejectionScale g.rejectionRoot) (ω j)) ≠
            (c:ℝ)+((k.val+1:ℕ):ℝ)*g.margin*g.population := by
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hraw := SourceCoarseIntegral.original_retained_bid_cap i G hcap
  have hf0 : Measurable (RivalGood.lowerTest (exposure (xi i) (g.multiplier-g.radius))) :=
    RivalGood.measurable_lowerTest (continuous_exposure (xi_pos i) hlo).measurable
  have hf1 : Measurable (RivalGood.lowerTest (PrefixRoot.psi g.rejectionScale g.rejectionRoot)) := by
    apply RivalGood.measurable_lowerTest
    unfold PrefixRoot.psi
    fun_prop
  have hn0 (a : ℝ) (ha : 0 < a) : ∀ᵐ r ∂ RawMixedSource.source i G,
      RivalGood.lowerTest (exposure (xi i) (g.multiplier-g.radius)) r ≠ a :=
    lowerTest_positive_atom_null (RawMixedSource.source i G)
      (EntryThresholdNull.raw_lower_bid_ne i G hnull) (exposure (xi i) (g.multiplier-g.radius))
      hraw (fun hB hC hpB hpC he => exposure_positive_injective (xi_pos i) hξ1 hlo hclip hB hC hpB hpC he) ha
  have hn1 (a : ℝ) (ha : 0 < a) : ∀ᵐ r ∂ RawMixedSource.source i G,
      RivalGood.lowerTest (PrefixRoot.psi g.rejectionScale g.rejectionRoot) r ≠ a :=
    lowerTest_positive_atom_null (RawMixedSource.source i G)
      (EntryThresholdNull.raw_lower_bid_ne i G hnull) (PrefixRoot.psi g.rejectionScale g.rejectionRoot)
      hraw (fun _ _ hpB hpC he => psi_positive_injective hd hpB hpC he) ha
  have hlevels (c : ℕ) (k : Fin 2) :
      0 < (c:ℝ)+((k.val+1:ℕ):ℝ)*g.margin*g.population-
        exposure (xi i) (g.multiplier-g.radius) b ∧
      0 < (c:ℝ)+((k.val+1:ℕ):ℝ)*g.margin*g.population-
        PrefixRoot.psi g.rejectionScale g.rejectionRoot b := by
    have hc : 0 ≤ (c:ℝ) := Nat.cast_nonneg _
    have hk : (1:ℝ) ≤ ((k.val+1:ℕ):ℝ) := by exact_mod_cast (by omega : 1 ≤ k.val+1)
    have hmult : g.margin*g.population ≤ ((k.val+1:ℕ):ℝ)*g.margin*g.population := by
      have hh := mul_le_mul_of_nonneg_right hk (by linarith : 0 ≤ g.margin*g.population)
      nlinarith
    constructor <;> linarith [exposure_le_one (xi i) (g.multiplier-g.radius) b,
      (PrefixRoot.psi_bounds hd (z:=g.rejectionRoot) (b:=b)).2]
  have h0 := ae_all_iff.mpr fun c => ae_all_iff.mpr fun k =>
    positive_sum_level_null (RawMixedSource.source i G) hf0 hn0 N (hlevels c k).1
  have h1 := ae_all_iff.mpr fun c => ae_all_iff.mpr fun k =>
    positive_sum_level_null (RawMixedSource.source i G) hf1 hn1 N (hlevels c k).2
  filter_upwards [h0,h1] with ω hω0 hω1 c k
  constructor
  · intro he
    exact hω0 c k (by linarith)
  · intro he
    exact hω1 c k (by linarith)

end FCAppendix.Affine.Uniform06.GuardCornerNull
