import FCAppendix.PayOnce.ActivePairCovariance

namespace FCAppendix.PayOnce.CovarianceConcentration
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators

theorem weighted_sum_distance_le_pair_gap {ι : Type*} [Fintype ι]
    (s p : ι → ℝ) (hs : ∀ i, 0 ≤ s i) (r : ℝ) :
    (∑ i, s i)*(∑ i, s i*|p i-r|) ≤
      (∑ i, ∑ j, s i*s j*|p i-p j|)+(∑ i, s i)*|∑ i, s i*p i-r*(∑ i, s i)| := by
  have hS : 0 ≤ ∑ i, s i := Finset.sum_nonneg fun i _ => hs i
  have hpoint (i : ι) : (∑ j, s j)*|p i-r| ≤
      (∑ j, s j*|p i-p j|)+|∑ j, s j*p j-r*(∑ j, s j)| := by
    have he : (∑ j, s j)*(p i-r) = (∑ j, s j*(p i-p j))+(∑ j, s j*p j-r*(∑ j, s j)) := by
      simp_rw [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul]
      ring
    calc
      _ = |(∑ j, s j)*(p i-r)| := by rw [abs_mul,abs_of_nonneg hS]
      _ ≤ |∑ j, s j*(p i-p j)|+|∑ j, s j*p j-r*(∑ j, s j)| := by rw [he]; exact abs_add_le _ _
      _ ≤ (∑ j, s j*|p i-p j|)+|∑ j, s j*p j-r*(∑ j, s j)| := by
        apply add_le_add _ le_rfl
        calc
          _ ≤ ∑ j, |s j*(p i-p j)| := Finset.abs_sum_le_sum_abs _ _
          _ = _ := by simp_rw [abs_mul,abs_of_nonneg (hs _)]
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (hs i))
  have hleft : (∑ i, s i)*(∑ i, s i*|p i-r|) = ∑ i, s i*((∑ j, s j)*|p i-r|) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hright : (∑ i, ∑ j, s i*s j*|p i-p j|)+(∑ i, s i)*|∑ i, s i*p i-r*(∑ i, s i)| =
      ∑ i, s i*((∑ j, s j*|p i-p j|)+|∑ j, s j*p j-r*(∑ j, s j)|) := by
    simp_rw [mul_add,Finset.sum_add_distrib,Finset.mul_sum,← Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hleft,hright]
  exact hh

theorem active_mean_distance_bound {ι : Type*} [Fintype ι]
    (hm : 0 < Fintype.card ι) (s p : ι → ℝ)
    (hs : ∀ i, s i ∈ Icc (0:ℝ) 1) (hp : ∀ i, p i ∈ Icc (0:ℝ) 1)
    {π ρ : ℝ} (hπ : 0 < π) (hr : ρ/π ∈ Icc (0:ℝ) 1) :
    populationMean (fun i => s i*|p i-ρ/π|) ≤
      (populationPairMean (fun i j => s i*s j*|p i-p j|)+
        |populationMean (fun i => s i*p i)-ρ|+(1+ρ/π)*|populationMean s-π|)/π := by
  let a := populationMean s
  let D := populationMean (fun i => s i*|p i-ρ/π|)
  let q := populationMean (fun i => s i*p i)
  let E := populationPairMean (fun i j => s i*s j*|p i-p j|)
  have hmR : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr hm
  have ha : a ∈ Icc (0:ℝ) 1 := by
    refine ⟨div_nonneg (Finset.sum_nonneg fun i _ => (hs i).1) hmR.le,?_⟩
    apply (div_le_one hmR).mpr
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using
      Finset.sum_le_sum (s := (Finset.univ : Finset ι)) (fun i _ => (hs i).2)
  have hgap i : |p i-ρ/π| ≤ 1 := abs_le.mpr
    ⟨by linarith [(hp i).1,hr.2],by linarith [(hp i).2,hr.1]⟩
  have hD : D ∈ Icc (0:ℝ) 1 := by
    refine ⟨div_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (hs i).1 (abs_nonneg _)) hmR.le,?_⟩
    apply (div_le_one hmR).mpr
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using
      Finset.sum_le_sum (s := (Finset.univ : Finset ι)) (fun i _ =>
        mul_le_one₀ (hs i).2 (abs_nonneg _) (hgap i))
  have hweighted : a*D ≤ E+a*|q-ρ/π*a| := by
    have hh := div_le_div_of_nonneg_right (weighted_sum_distance_le_pair_gap s p (fun i => (hs i).1) (ρ/π))
      (sq_pos_of_pos hmR).le
    have hleft : a*D = ((∑ i, s i)*(∑ i, s i*|p i-ρ/π|))/(Fintype.card ι:ℝ)^2 := by
      dsimp only [a,D,populationMean]
      ring
    have hright : E+a*|q-ρ/π*a| =
        ((∑ i, ∑ j, s i*s j*|p i-p j|)+(∑ i, s i)*|∑ i, s i*p i-ρ/π*(∑ i, s i)|)/(Fintype.card ι:ℝ)^2 := by
      dsimp only [a,q,E,populationMean,populationPairMean]
      rw [show (∑ i, s i*p i)/(Fintype.card ι:ℝ)-ρ/π*((∑ i, s i)/(Fintype.card ι:ℝ)) =
        ((∑ i, s i*p i)-ρ/π*(∑ i, s i))/(Fintype.card ι:ℝ) by ring]
      rw [abs_div,abs_of_pos hmR]
      ring
    rw [hleft,hright]
    exact hh
  have h1 : π*D ≤ E+|q-ρ/π*a|+|a-π| := by
    have hmean := mul_le_mul_of_nonneg_right (le_abs_self (π-a)) hD.1
    have habs : |π-a| * D ≤ |a-π| := by
      rw [abs_sub_comm]
      exact mul_le_of_le_one_right (abs_nonneg _) hD.2
    have haerr := mul_le_of_le_one_left (abs_nonneg (q-ρ/π*a)) ha.2
    nlinarith
  have h2 : |q-ρ/π*a| ≤ |q-ρ|+(ρ/π)*|a-π| := by
    have hid : q-ρ/π*a = (q-ρ)-(ρ/π)*(a-π) := by field_simp; ring
    rw [hid]
    have hh := abs_sub (q-ρ) ((ρ/π)*(a-π))
    simpa only [abs_mul,abs_of_nonneg hr.1] using hh
  apply (le_div_iff₀ hπ).mpr
  change D*π ≤ E+|q-ρ|+(1+ρ/π)*|a-π|
  nlinarith

theorem integral_active_distance_tendsto_zero
    {Ω ι : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)] [∀ t, Fintype (ι t)]
    (P : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (P t)]
    (hm : ∀ t, 0 < Fintype.card (ι t)) (s p : ∀ t, Ω t → ι t → ℝ)
    (hs : ∀ t i, Measurable (fun ω => s t ω i))
    (hp : ∀ t i, Measurable (fun ω => p t ω i))
    (hsb : ∀ t ω i, s t ω i ∈ Icc (0:ℝ) 1)
    (hpb : ∀ t ω i, p t ω i ∈ Icc (0:ℝ) 1)
    {π ρ : ℝ} (hπ : 0 < π) (hr : ρ/π ∈ Icc (0:ℝ) 1)
    (hactive : Tendsto (fun t => ∫ ω, |populationMean (s t ω)-π| ∂P t) atTop (𝓝 0))
    (hload : Tendsto (fun t => ∫ ω, |populationMean (fun i => s t ω i*p t ω i)-ρ| ∂P t) atTop (𝓝 0))
    (hpair : Tendsto (fun t => ∫ ω, populationPairMean (fun i j => s t ω i*s t ω j*|p t ω i-p t ω j|) ∂P t)
      atTop (𝓝 0)) :
    Tendsto (fun t => ∫ ω, populationMean (fun i => s t ω i*|p t ω i-ρ/π|) ∂P t) atTop (𝓝 0) := by
  have hsI t i := UnitInterval.integrable (P t) _ (hs t i) (fun ω => (hsb t ω i).1) (fun ω => (hsb t ω i).2)
  have hspI t i := UnitInterval.integrable (P t) _ ((hs t i).mul (hp t i))
    (fun ω => mul_nonneg (hsb t ω i).1 (hpb t ω i).1)
    (fun ω => mul_le_one₀ (hsb t ω i).2 (hpb t ω i).1 (hpb t ω i).2)
  have haI t : Integrable (fun ω => |populationMean (s t ω)-π|) (P t) :=
    (((integrable_finsetSum _ (fun i _ => hsI t i)).div_const _).sub (integrable_const π)).abs
  have hqI t : Integrable (fun ω => |populationMean (fun i => s t ω i*p t ω i)-ρ|) (P t) :=
    (((integrable_finsetSum _ (fun i _ => hspI t i)).div_const _).sub (integrable_const ρ)).abs
  have hpairI t : Integrable (fun ω => populationPairMean
      (fun i j => s t ω i*s t ω j*|p t ω i-p t ω j|)) (P t) := by
    apply integrable_populationPairMean
    intro i j
    apply UnitInterval.integrable (P t) _ (((hs t i).mul (hs t j)).mul ((hp t i).sub (hp t j)).abs)
    · intro ω
      exact mul_nonneg (mul_nonneg (hsb t ω i).1 (hsb t ω j).1) (abs_nonneg _)
    · intro ω
      apply mul_le_one₀ (mul_le_one₀ (hsb t ω i).2 (hsb t ω j).1 (hsb t ω j).2) (abs_nonneg _)
      dsimp only [Pi.sub_apply]
      exact abs_le.mpr ⟨by linarith [(hpb t ω i).1,(hpb t ω j).2],by linarith [(hpb t ω i).2,(hpb t ω j).1]⟩
  have hDI t : Integrable (fun ω => populationMean (fun i => s t ω i*|p t ω i-ρ/π|)) (P t) := by
    apply Integrable.div_const
    apply integrable_finsetSum
    intro i _
    apply UnitInterval.integrable (P t) _ ((hs t i).mul ((hp t i).sub_const (ρ/π)).abs)
    · intro ω
      exact mul_nonneg (hsb t ω i).1 (abs_nonneg _)
    · intro ω
      apply mul_le_one₀ (hsb t ω i).2 (abs_nonneg _)
      exact abs_le.mpr ⟨by linarith [(hpb t ω i).1,hr.2],by linarith [(hpb t ω i).2,hr.1]⟩
  have hupper : Tendsto (fun t => ((∫ ω, populationPairMean
      (fun i j => s t ω i*s t ω j*|p t ω i-p t ω j|) ∂P t)+
      (∫ ω, |populationMean (fun i => s t ω i*p t ω i)-ρ| ∂P t)+
      (1+ρ/π)*(∫ ω, |populationMean (s t ω)-π| ∂P t))/π) atTop (𝓝 0) := by
    simpa only [add_zero,mul_zero,zero_div] using ((hpair.add hload).add (hactive.const_mul (1+ρ/π))).div_const π
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
  · intro t
    exact integral_nonneg fun ω => div_nonneg
      (Finset.sum_nonneg fun i _ => mul_nonneg (hsb t ω i).1 (abs_nonneg _)) (Nat.cast_nonneg _)
  · intro t
    have hh := integral_mono (hDI t) ((((hpairI t).add (hqI t)).add ((haI t).const_mul (1+ρ/π))).div_const π)
      (fun ω => active_mean_distance_bound (hm t) (s t ω) (p t ω) (hsb t ω) (hpb t ω) hπ hr)
    simp only [Pi.add_apply] at hh
    rw [integral_div,integral_add
      (show Integrable (fun ω => populationPairMean (fun i j => s t ω i*s t ω j*|p t ω i-p t ω j|)+
        |populationMean (fun i => s t ω i*p t ω i)-ρ|) (P t) from (hpairI t).add (hqI t))
      ((haI t).const_mul (1+ρ/π)),integral_add (hpairI t) (hqI t),integral_const_mul] at hh
    exact hh

end FCAppendix.PayOnce.CovarianceConcentration
