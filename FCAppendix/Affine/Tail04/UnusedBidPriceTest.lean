import FCAppendix.Affine.Tail04.UnusedBidAntiConcentration

noncomputable section
namespace FCAppendix.Affine.Tail04.WeightedFlagBound
open Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def meanMixedPrice (xi : ℝ) (c ell : ℕ) (privateMean : ℝ)
    (I : Finset ι) (b : ι → ℝ) : ℝ :=
  ((I.card : ℝ)-xi*((c:ℝ)-privateMean-ell))/mixedReciprocalSum I b

theorem weighted_unused_sum (xi bid : ℝ) (b : ι → ℝ) (flags : ι → Bool) :
    weightedSum (unusedCoefficient xi bid b) flags =
      bid * mixedReciprocalSum (flaggedMixedSet flags) b -
        (1-xi/2)*(flaggedMixedSet flags).card := by
  rw [weightedSum_eq_setWeight]
  have he : boolSetEquiv flags = flaggedMixedSet flags := rfl
  rw [he]
  unfold setWeight unusedCoefficient
  rw [Finset.sum_sub_distrib]
  unfold mixedReciprocalSum
  rw [Finset.mul_sum]
  simp only [Finset.sum_const, nsmul_eq_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · ring

theorem unused_price_weighted_identity (xi bid : ℝ) (c ell N : ℕ)
    (ownMean otherMean balanceError : ℝ) (b : ι → ℝ) (flags : ι → Bool)
    (hW : mixedReciprocalSum (flaggedMixedSet flags) b ≠ 0)
    (hbalance : (ell:ℝ) =
      ((N:ℝ)-(flaggedMixedSet flags).card+otherMean-ownMean)/2+balanceError) :
    mixedReciprocalSum (flaggedMixedSet flags) b *
      (bid-meanMixedPrice xi c ell ownMean (flaggedMixedSet flags) b) =
      weightedSum (unusedCoefficient xi bid b) flags +
        xi*((c:ℝ)-(N:ℝ)/2-(ownMean+otherMean)/2-balanceError) := by
  rw [weighted_unused_sum]
  unfold meanMixedPrice
  rw [hbalance]
  field_simp [hW]
  ring

omit [Fintype ι] [DecidableEq ι] in

theorem balanced_price_difference (xi : ℝ) (c ell1 ell2 N : ℕ)
    (mean1 mean2 err1 err2 : ℝ) (I : Finset ι) (b : ι → ℝ)
    (hW : 0 < mixedReciprocalSum I b) (hxi : 0 ≤ xi)
    (hbalance1 : (ell1:ℝ) = ((N:ℝ)-I.card+mean2-mean1)/2+err1)
    (hbalance2 : (ell2:ℝ) = ((N:ℝ)-I.card+mean1-mean2)/2+err2)
    (he1 : |err1| ≤ 1/2) (he2 : |err2| ≤ 1/2) :
    |meanMixedPrice xi c ell1 mean1 I b-meanMixedPrice xi c ell2 mean2 I b| ≤
      xi/mixedReciprocalSum I b := by
  have heq : meanMixedPrice xi c ell1 mean1 I b-meanMixedPrice xi c ell2 mean2 I b =
      (xi/mixedReciprocalSum I b)*(err1-err2) := by
    unfold meanMixedPrice
    rw [hbalance1,hbalance2]
    ring
  have herr : |err1-err2| ≤ 1 := by
    have hh := abs_sub err1 err2
    linarith
  rw [heq,abs_mul,abs_of_nonneg (div_nonneg hxi hW.le)]
  simpa using mul_le_mul_of_nonneg_left herr (div_nonneg hxi hW.le)

theorem bulk_flag_bounds {beta B u epsilon bi : ℝ}
    (hbeta : 0 ≤ beta) (hB : 1 < B) (hu : u < B-1)
    (hbi : bi ∈ Icc 1 (1+u))
    (hlower : epsilon ≤ beta*((B-1-u)/(B-1))^2)
    (hupper : beta ≤ 1-epsilon) :
    epsilon ≤ mixedFlagProbability beta B bi ∧
      mixedFlagProbability beta B bi ≤ 1-epsilon := by
  have hd : 0 < B-1 := by linarith
  have hbiB : bi ≤ B := by linarith [hbi.2]
  have hl0 : 0 ≤ (B-1-u)/(B-1) := div_nonneg (by linarith) hd.le
  have hq : (B-1-u)/(B-1) ≤ (B-bi)/(B-1) :=
    (div_le_div_iff_of_pos_right hd).mpr (by linarith [hbi.2])
  have hq0 : 0 ≤ (B-bi)/(B-1) := hl0.trans hq
  have hs : ((B-1-u)/(B-1))^2 ≤ ((B-bi)/(B-1))^2 :=
    (sq_le_sq₀ hl0 hq0).mpr hq
  refine ⟨hlower.trans (mul_le_mul_of_nonneg_left hs hbeta), ?_⟩
  exact (mixedFlagProbability_le_base hbeta hB ⟨hbi.1,hbiB⟩).trans hupper

theorem weighted_error_sqrt_rate {epsilon N : ℝ} (heps : 0 < epsilon)
    (hN : 1 ≤ N) (r : ℕ) :
    2/(epsilon*N)+(r:ℝ)*Real.sqrt (2/(epsilon*N+1)) ≤
      (2/epsilon+(r:ℝ)*Real.sqrt (2/epsilon))/Real.sqrt N := by
  have hN0 : 0 < N := by linarith
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hs2 : (Real.sqrt N)^2=N := Real.sq_sqrt hN0.le
  have hsN : Real.sqrt N ≤ N := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg N) hN0.le).mp
    rw [hs2]
    have hh := mul_le_mul_of_nonneg_right hN hN0.le
    simpa only [one_mul,pow_two] using hh
  have hfirst : 2/(epsilon*N) ≤ (2/epsilon)/Real.sqrt N := by
    calc
      _ = (2/epsilon)/N := by field_simp [ne_of_gt heps,ne_of_gt hN0]
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hs0 hsN
  have hratio : 2/(epsilon*N+1) ≤ (2/epsilon)/N := by
    calc
      _ ≤ 2/(epsilon*N) := div_le_div_of_nonneg_left (by norm_num)
        (mul_pos heps hN0) (by linarith)
      _ = _ := by field_simp [ne_of_gt heps,ne_of_gt hN0]
  have hroot : Real.sqrt (2/(epsilon*N+1)) ≤ Real.sqrt (2/epsilon)/Real.sqrt N := by
    apply (le_div_iff₀ hs0).mpr
    have hleft0 : 0 ≤ Real.sqrt (2/(epsilon*N+1))*Real.sqrt N := by positivity
    apply (sq_le_sq₀ hleft0 (Real.sqrt_nonneg (2/epsilon))).mp
    rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 2/(epsilon*N+1)),hs2,
      Real.sq_sqrt (by positivity : 0 ≤ 2/epsilon)]
    calc
      _ ≤ ((2/epsilon)/N)*N := mul_le_mul_of_nonneg_right hratio hN0.le
      _ = _ := div_mul_cancel₀ _ (ne_of_gt hN0)
  calc
    _ ≤ (2/epsilon)/Real.sqrt N+(r:ℝ)*(Real.sqrt (2/epsilon)/Real.sqrt N) :=
      add_le_add hfirst (mul_le_mul_of_nonneg_left hroot (Nat.cast_nonneg r))
    _ = _ := by ring

end FCAppendix.Affine.Tail04.WeightedFlagBound
