import FCAppendix.PayOnce.PriceGoodEvent

namespace FCAppendix.PayOnce.PriceConcentration
open MeasureTheory ProbabilityTheory Set Filter Topology CommonList KernelTailEvent
open Probability PriceInteriorBounds
open scoped BigOperators

theorem goodEvent_price_gap_le {n N c : ℕ} (hn : 2 ≤ n) (hN : 0 < N)
    (μ : Measure ℝ) {ℓ u a z q b R T : ℝ}
    (hℓ : 0 < ℓ) (hT : T ∈ Icc ℓ u) (ha : u < a) (haz : a < z)
    (hz : z < (n:ℝ)*ℓ) (hq : 0 < q)
    {r : Fin N → ℝ} (hr : r ∈ goodEvent n N c ℓ u a z q)
    (hR : 0 < R)
    (hcap : kernel n b R+∑ j, kernel n (r j) R =
      (min c (Fintype.card (DummyKernel.Active r)+1):ℕ))
    (hbias : |(∫ b, kernel n b T ∂μ)-(c:ℝ)/(N:ℝ)| ≤ 1/(N:ℝ)) :
    |R-T| ≤ ((n:ℝ)*z/q)*
      (|(∑ j, kernel n (r j) T)/(N:ℝ)-(∫ b, kernel n b T ∂μ)|+2/(N:ℝ)) := by
  classical
  have hu : 0 < u := (hℓ.trans_le hT.1).trans_le hT.2
  have hzpos : 0 < z := (hu.trans ha).trans haz
  have hc := goodEvent_capacity_le_active hn hℓ hr
  rw [Nat.min_eq_left (hc.trans (Nat.le_succ _))] at hcap
  have hRI := goodEvent_root_mem_Icc hn hℓ hu hr hR hcap
  let J := Finset.univ.filter fun j => r j ∈ Ioo a z
  have hJ : ∀ j ∈ J, r j ∈ Ioo a z := fun j hj => (Finset.mem_filter.mp hj).2
  have hcount : q*(N:ℝ) ≤ (J.card:ℝ) := by simpa [J,sampleCount] using hr.2.2
  have hh := price_gap_le_capacity_error hn hN r hℓ hRI hT ha haz hz J hJ hq hcount hcap
  have he := (abs_sub_le ((∑ j, kernel n (r j) T)/(N:ℝ))
    (∫ b, kernel n b T ∂μ) ((c:ℝ)/(N:ℝ))).trans (add_le_add le_rfl hbias)
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have htwo : 1/(N:ℝ)+1/(N:ℝ)=2/(N:ℝ) := by ring
  linarith only [he,htwo]

theorem price_tail_le_bad_add_hoeffding {n N c : ℕ} (hn : 2 ≤ n) (hN : 0 < N)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {ℓ u a z q T ε : ℝ} (hℓ : 0 < ℓ) (hT : T ∈ Icc ℓ u)
    (ha : u < a) (haz : a < z) (hz : z < (n:ℝ)*ℓ) (hq : 0 < q)
    (b R : (Fin N → ℝ) → ℝ) (hR : ∀ r, 0 < R r)
    (hcap : ∀ r, kernel n (b r) (R r)+∑ j, kernel n (r j) (R r) =
      (min c (Fintype.card (DummyKernel.Active r)+1):ℕ))
    (hbias : |(∫ b, kernel n b T ∂μ)-(c:ℝ)/(N:ℝ)| ≤ 1/(N:ℝ))
    (hε : 4*((n:ℝ)*z/q)/(N:ℝ) ≤ ε) :
    (Measure.pi (fun _ : Fin N => μ)).real {r | ε ≤ |R r-T|} ≤
      (Measure.pi (fun _ : Fin N => μ)).real (goodEvent n N c ℓ u a z q)ᶜ+
        2*Real.exp (-(N:ℝ)*ε^2/(2*((n:ℝ)*z/q)^2)) := by
  let K := (n:ℝ)*z/q
  let P := Measure.pi (fun _ : Fin N => μ)
  let E := {r : Fin N → ℝ |
    ε/(2*K) ≤ |(∑ j, kernel n (r j) T)/(N:ℝ)-(∫ b, kernel n b T ∂μ)|}
  have hTpos : 0 < T := hℓ.trans_le hT.1
  have hzpos : 0 < z := ((hTpos.trans_le hT.2).trans ha).trans haz
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hK : 0 < K := by dsimp only [K]; positivity
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hεpos : 0 < ε := lt_of_lt_of_le (by dsimp only [K] at hK; positivity) hε
  have hsub : {r : Fin N → ℝ | ε ≤ |R r-T|} ⊆
      (goodEvent n N c ℓ u a z q)ᶜ ∪ E := by
    intro r hr
    by_cases hg : r ∈ goodEvent n N c ℓ u a z q
    · right
      have hgap := goodEvent_price_gap_le hn hN μ hℓ hT ha haz hz hq hg (hR r) (hcap r) hbias
      change ε/(2*K) ≤ _
      by_contra he
      have he' := (lt_div_iff₀ (by positivity : 0 < 2*K)).mp (lt_of_not_ge he)
      have hshift : K*(4/(N:ℝ)) ≤ ε := by
        calc
          K*(4/(N:ℝ)) = 4*((n:ℝ)*z/q)/(N:ℝ) := by dsimp only [K]; ring
          _ ≤ ε := hε
      have hgap' : |R r-T| ≤ K*
          (|(∑ j, kernel n (r j) T)/(N:ℝ)-(∫ b, kernel n b T ∂μ)|+2/(N:ℝ)) := hgap
      dsimp only [mem_setOf_eq] at hr
      have hid : K*(4/(N:ℝ)) = 2*(K*(2/(N:ℝ))) := by ring
      nlinarith
    · exact Or.inl hg
  have hE := iid_empiricalMean_two_sided_le μ
    (continuous_kernel_bid hn hTpos).measurable.aemeasurable
    (Eventually.of_forall fun b => kernel_bounds hn hTpos b) N hN
    (show 0 ≤ ε/(2*K) by positivity)
  have hexp : -2*(N:ℝ)*(ε/(2*K))^2 = -(N:ℝ)*ε^2/(2*K^2) := by
    field_simp
  rw [hexp] at hE
  exact (measureReal_mono hsub).trans
    ((measureReal_union_le (μ := P) _ E).trans (add_le_add le_rfl hE))

theorem price_tail_le {n N c : ℕ} (hn : 2 ≤ n) (hN : 0 < N)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {ℓ u a z q δlo δhi d T ε : ℝ} (hℓ : 0 < ℓ) (hT : T ∈ Icc ℓ u)
    (ha : u < a) (haz : a < z) (hz : z < (n:ℝ)*ℓ)
    (hq : 0 < q) (hδlo : 0 ≤ δlo) (hδhi : 0 ≤ δhi)
    (hlo : (c:ℝ)/(N:ℝ) ≤ (∫ b, kernel n b ℓ ∂μ)-δlo)
    (hhi : (∫ b, kernel n b u ∂μ)+δhi ≤ ((c:ℝ)-1)/(N:ℝ))
    (hmass : 2*q ≤ μ.real (Ioo a z))
    (hdlo : d ≤ 2*δlo^2) (hdhi : d ≤ 2*δhi^2) (hdq : d ≤ 2*q^2)
    (b R : (Fin N → ℝ) → ℝ) (hR : ∀ r, 0 < R r)
    (hcap : ∀ r, kernel n (b r) (R r)+∑ j, kernel n (r j) (R r) =
      (min c (Fintype.card (DummyKernel.Active r)+1):ℕ))
    (hbias : |(∫ b, kernel n b T ∂μ)-(c:ℝ)/(N:ℝ)| ≤ 1/(N:ℝ))
    (hε : 4*((n:ℝ)*z/q)/(N:ℝ) ≤ ε) :
    (Measure.pi (fun _ : Fin N => μ)).real {r | ε ≤ |R r-T|} ≤
      3*Real.exp (-d*(N:ℝ))+2*Real.exp (-(N:ℝ)*ε^2/(2*((n:ℝ)*z/q)^2)) := by
  have hu : 0 < u := (hℓ.trans_le hT.1).trans_le hT.2
  exact (price_tail_le_bad_add_hoeffding hn hN μ hℓ hT ha haz hz hq b R hR hcap hbias hε).trans
    (add_le_add
      (goodEvent_compl_le_exponential hn hN μ hℓ hu hq.le hδlo hδhi hlo hhi hmass hdlo hdhi hdq) le_rfl)

theorem goodEvent_focal_price_gap_le {n N c : ℕ} (hn : 2 ≤ n) (hN : 0 < N)
    {ℓ u a z q b d R S : ℝ} (hℓ : 0 < ℓ) (hu : 0 < u)
    (ha : u < a) (haz : a < z) (hz : z < (n:ℝ)*ℓ) (hq : 0 < q)
    {r : Fin N → ℝ} (hr : r ∈ goodEvent n N c ℓ u a z q)
    (hR : 0 < R) (hS : 0 < S)
    (hcapR : kernel n b R+∑ j, kernel n (r j) R =
      (min c (Fintype.card (DummyKernel.Active r)+1):ℕ))
    (hcapS : kernel n d S+∑ j, kernel n (r j) S =
      (min c (Fintype.card (DummyKernel.Active r)+1):ℕ)) :
    |R-S| ≤ (n:ℝ)*z/(q*N) := by
  classical
  have hc := goodEvent_capacity_le_active hn hℓ hr
  rw [Nat.min_eq_left (hc.trans (Nat.le_succ _))] at hcapR hcapS
  have hRI := goodEvent_root_mem_Icc hn hℓ hu hr hR hcapR
  have hSI := goodEvent_root_mem_Icc hn hℓ hu hr hS hcapS
  let J := Finset.univ.filter fun j => r j ∈ Ioo a z
  have hJ : ∀ j ∈ J, r j ∈ Ioo a z := fun j hj => (Finset.mem_filter.mp hj).2
  have hcount : q*(N:ℝ) ≤ (J.card:ℝ) := by simpa [J,sampleCount] using hr.2.2
  exact focal_price_gap_le hn hN r hℓ hRI hSI ha haz hz J hJ hq hcount hcapR hcapS

theorem fullPopulation_reference_bias_le {N c : ℕ} (hN : 0 < N)
    (hc : c ≤ N+1) {m : ℝ} (hm : m = (c:ℝ)/((N:ℝ)+1)) :
    |m-(c:ℝ)/(N:ℝ)| ≤ 1/(N:ℝ) := by
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hcR : (c:ℝ) ≤ (N:ℝ)+1 := by exact_mod_cast hc
  have he : m-(c:ℝ)/(N:ℝ) = -(c:ℝ)/((N:ℝ)*((N:ℝ)+1)) := by
    rw [hm]
    field_simp
    ring
  rw [he,abs_div,abs_neg,abs_of_nonneg (Nat.cast_nonneg c),abs_of_pos (by positivity)]
  apply (div_le_iff₀ (by positivity : 0 < (N:ℝ)*((N:ℝ)+1))).mpr
  calc
    (c:ℝ) ≤ (N:ℝ)+1 := hcR
    _ = (1/(N:ℝ))*((N:ℝ)*((N:ℝ)+1)) := by field_simp

theorem price_tail_le_bad_add_gaussian {n N c : ℕ} (hn : 2 ≤ n) (hN : 0 < N)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {ℓ u a z q T ε : ℝ} (hℓ : 0 < ℓ) (hT : T ∈ Icc ℓ u)
    (ha : u < a) (haz : a < z) (hz : z < (n:ℝ)*ℓ) (hq : 0 < q)
    (b R : (Fin N → ℝ) → ℝ) (hR : ∀ r, 0 < R r)
    (hcap : ∀ r, kernel n (b r) (R r)+∑ j, kernel n (r j) (R r) =
      (min c (Fintype.card (DummyKernel.Active r)+1):ℕ))
    (hbias : |(∫ b, kernel n b T ∂μ)-(c:ℝ)/(N:ℝ)| ≤ 1/(N:ℝ))
    (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin N => μ)).real {r | ε ≤ |R r-T|} ≤
      (Measure.pi (fun _ : Fin N => μ)).real (goodEvent n N c ℓ u a z q)ᶜ+
        (2*Real.exp 8)*Real.exp (-(N:ℝ)*ε^2/(2*((n:ℝ)*z/q)^2)) := by
  let K := (n:ℝ)*z/q
  have hTpos : 0 < T := hℓ.trans_le hT.1
  have hzpos : 0 < z := ((hTpos.trans_le hT.2).trans ha).trans haz
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hK : 0 < K := by dsimp only [K]; positivity
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hexp8 : 1 ≤ Real.exp 8 := Real.one_le_exp_iff.mpr (by norm_num)
  by_cases hcut : 4*K/(N:ℝ) ≤ ε
  · have hh := price_tail_le_bad_add_hoeffding hn hN μ hℓ hT ha haz hz hq b R hR hcap hbias hcut
    have hm := mul_le_mul_of_nonneg_right hexp8
      (Real.exp_pos (-(N:ℝ)*ε^2/(2*K^2))).le
    dsimp only [K] at hm
    nlinarith
  · have hεN : ε*(N:ℝ) ≤ 4*K := (le_div_iff₀ hNR).mp (le_of_lt (lt_of_not_ge hcut))
    have hs : (ε*(N:ℝ))^2 ≤ (4*K)^2 :=
      (sq_le_sq₀ (mul_nonneg hε hNR.le) (by positivity)).mpr hεN
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
    have hNN : (N:ℝ) ≤ (N:ℝ)^2 := by nlinarith
    have hsqN := mul_le_mul_of_nonneg_left hNN (sq_nonneg ε)
    have hnum : (N:ℝ)*ε^2 ≤ 16*K^2 := by nlinarith
    have hsmall : (N:ℝ)*ε^2/(2*K^2) ≤ 8 :=
      (div_le_iff₀ (by positivity : 0 < 2*K^2)).mpr (by nlinarith)
    have hprod : 1 ≤ Real.exp 8*Real.exp (-(N:ℝ)*ε^2/(2*K^2)) := by
      rw [← Real.exp_add,← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      rw [neg_mul,neg_div]
      linarith
    have hp : (Measure.pi (fun _ : Fin N => μ)).real {r | ε ≤ |R r-T|} ≤ 1 := measureReal_le_one
    have hbad : 0 ≤ (Measure.pi (fun _ : Fin N => μ)).real (goodEvent n N c ℓ u a z q)ᶜ :=
      measureReal_nonneg
    dsimp only [K] at hprod
    nlinarith

theorem price_tail_le_gaussian {n N c : ℕ} (hn : 2 ≤ n) (hN : 0 < N)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {ℓ u a z q δlo δhi d T ε : ℝ} (hℓ : 0 < ℓ) (hT : T ∈ Icc ℓ u)
    (ha : u < a) (haz : a < z) (hz : z < (n:ℝ)*ℓ)
    (hq : 0 < q) (hδlo : 0 ≤ δlo) (hδhi : 0 ≤ δhi)
    (hlo : (c:ℝ)/(N:ℝ) ≤ (∫ b, kernel n b ℓ ∂μ)-δlo)
    (hhi : (∫ b, kernel n b u ∂μ)+δhi ≤ ((c:ℝ)-1)/(N:ℝ))
    (hmass : 2*q ≤ μ.real (Ioo a z))
    (hdlo : d ≤ 2*δlo^2) (hdhi : d ≤ 2*δhi^2) (hdq : d ≤ 2*q^2)
    (b R : (Fin N → ℝ) → ℝ) (hR : ∀ r, 0 < R r)
    (hcap : ∀ r, kernel n (b r) (R r)+∑ j, kernel n (r j) (R r) =
      (min c (Fintype.card (DummyKernel.Active r)+1):ℕ))
    (hbias : |(∫ b, kernel n b T ∂μ)-(c:ℝ)/(N:ℝ)| ≤ 1/(N:ℝ))
    (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin N => μ)).real {r | ε ≤ |R r-T|} ≤
      3*Real.exp (-d*(N:ℝ))+(2*Real.exp 8)*Real.exp (-(N:ℝ)*ε^2/(2*((n:ℝ)*z/q)^2)) := by
  have hu : 0 < u := (hℓ.trans_le hT.1).trans_le hT.2
  exact (price_tail_le_bad_add_gaussian hn hN μ hℓ hT ha haz hz hq b R hR hcap hbias hε).trans
    (add_le_add
      (goodEvent_compl_le_exponential hn hN μ hℓ hu hq.le hδlo hδhi hlo hhi hmass hdlo hdhi hdq) le_rfl)

end FCAppendix.PayOnce.PriceConcentration
