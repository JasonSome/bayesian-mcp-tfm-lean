import FCAppendix.Affine.Hybrid.FavoredFiniteCrossing
import FCAppendix.Affine.Hybrid.SourceMenuNeighborhood

noncomputable section
namespace FCAppendix.Affine.Hybrid
variable {ι : Type*} [Fintype ι]

lemma one_sub_fillFraction_ge_owner_complement {K : ℕ}
    (hN : 2≤ Fintype.card ι) (hK : K≤ Fintype.card ι) :
    1-(K:ℝ)/(Fintype.card ι:ℝ)≤1-fillFraction (ι:=ι) K := by
  have hn : (1:ℝ)<Fintype.card ι := by exact_mod_cast (show 1<Fintype.card ι by omega)
  have hn0 : (Fintype.card ι:ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hnm : (Fintype.card ι:ℝ)-1 ≠ 0 := ne_of_gt (by linarith)
  have hk : (K:ℝ)≤ Fintype.card ι := by exact_mod_cast hK
  have he1 : 1-(K:ℝ)/(Fintype.card ι:ℝ)=((Fintype.card ι:ℝ)-(K:ℝ))/(Fintype.card ι:ℝ) := by
    field_simp [hn0]
  have he2 : 1-fillFraction (ι:=ι) K=((Fintype.card ι:ℝ)-(K:ℝ))/((Fintype.card ι:ℝ)-1) := by
    unfold fillFraction
    field_simp [hnm]
    ring
  rw [he1,he2]
  apply (div_le_div_iff₀ (show 0<(Fintype.card ι:ℝ) by linarith)
    (show 0<(Fintype.card ι:ℝ)-1 by linarith)).mpr
  nlinarith

lemma rankDenominator_le_population_sq {M : ℕ} (hcard : Fintype.card ι≤ M) :
    rankDenominator ι≤(M:ℝ)^2 := by
  have hc : (Fintype.card ι:ℝ)≤ M := by exact_mod_cast hcard
  have hc0 : (0:ℝ)≤ Fintype.card ι := Nat.cast_nonneg _
  have hM : (0:ℝ)≤ M := Nat.cast_nonneg _
  by_cases hzero : Fintype.card ι=0
  · simp only [rankDenominator,hzero,Nat.cast_zero,zero_mul,zero_div]
    positivity
  · have hc1 : (1:ℝ)≤ Fintype.card ι := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hzero)
    unfold rankDenominator
    nlinarith [sq_le_sq₀ hc0 hM |>.mpr hc]

theorem favored_crossing_coefficient_lower {K M : ℕ} {z gain : ℝ}
    (hN : 2≤ Fintype.card ι) (hK : K≤ Fintype.card ι) (hcard : Fintype.card ι≤ M)
    (hz : z<1) (hgain : 0≤ gain)
    (hshare : (K:ℝ)/(Fintype.card ι:ℝ)≤(1+z)/2) :
    (1-z)*gain/(16*(M:ℝ)^2)≤
      ((1-fillFraction (ι:=ι) K)*(gain/2))/(4*rankDenominator ι) := by
  have hM : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hn : 0<(Fintype.card ι:ℝ) := by exact_mod_cast (show 0<Fintype.card ι by omega)
  have hf : (1-z)/2≤1-fillFraction (ι:=ι) K := by
    have hh:=one_sub_fillFraction_ge_owner_complement hN hK
    linarith
  have hd : 0<rankDenominator ι := by unfold rankDenominator;positivity
  have hdM:=rankDenominator_le_population_sq hcard
  apply (div_le_div_iff₀ (by positivity : 0<16*(M:ℝ)^2) (by positivity : 0<4*rankDenominator ι)).mpr
  have hpos : 0≤(1-z)*gain:=mul_nonneg (sub_nonneg.mpr hz.le) hgain
  have h1:=mul_le_mul_of_nonneg_right hf (show 0≤ gain/2 by positivity)
  have h2:=mul_le_mul_of_nonneg_left hdM hpos
  have h3:=mul_le_mul_of_nonneg_left h1 (show 0≤16*(M:ℝ)^2 by positivity)
  nlinarith

theorem favored_crossing_coefficient_cubic {K M : ℕ} {gain : ℝ}
    (hN : 2≤ Fintype.card ι) (hK : 1≤ K) (hKN : K<Fintype.card ι)
    (hcard : Fintype.card ι≤ M) (hgain : 0≤ gain) :
    gain/(8*(M:ℝ)^3) ≤
      ((1-fillFraction (ι:=ι) K)*(gain/2))/(4*rankDenominator ι) := by
  have hn : (1:ℝ)<Fintype.card ι := by exact_mod_cast (show 1<Fintype.card ι by omega)
  have hm : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hnM : (Fintype.card ι:ℝ)≤ M := by exact_mod_cast hcard
  have hnK : (1:ℝ)≤(Fintype.card ι:ℝ)-(K:ℝ) := by
    have hk : (K:ℝ)+1≤(Fintype.card ι:ℝ) := by
      exact_mod_cast (show K+1≤ Fintype.card ι by omega)
    linarith
  have he : 1-fillFraction (ι:=ι) K=
      ((Fintype.card ι:ℝ)-(K:ℝ))/((Fintype.card ι:ℝ)-1) := by
    unfold fillFraction
    field_simp [ne_of_gt (show 0<(Fintype.card ι:ℝ)-1 by linarith)]
    ring
  have hf : 1/(M:ℝ)≤1-fillFraction (ι:=ι) K := by
    rw [he]
    exact (one_div_le_one_div_of_le (by linarith) (by linarith)).trans
      (div_le_div_of_nonneg_right hnK (by linarith))
  have hf0 : 0≤1-fillFraction (ι:=ι) K :=
    (by positivity : 0≤1/(M:ℝ)).trans hf
  have hd : 0<rankDenominator ι := by unfold rankDenominator;positivity
  have hdM := rankDenominator_le_population_sq hcard
  calc
    gain/(8*(M:ℝ)^3) = ((1/(M:ℝ))*(gain/2))/(4*(M:ℝ)^2) := by
      field_simp [hm.ne']
      ring
    _ ≤ ((1-fillFraction (ι:=ι) K)*(gain/2))/(4*(M:ℝ)^2) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hf (by positivity)) (by positivity)
    _ ≤ ((1-fillFraction (ι:=ι) K)*(gain/2))/(4*rankDenominator ι) :=
      div_le_div_of_nonneg_left (mul_nonneg hf0 (by positivity)) (by positivity)
        (mul_le_mul_of_nonneg_left hdM (by norm_num))

end FCAppendix.Affine.Hybrid
