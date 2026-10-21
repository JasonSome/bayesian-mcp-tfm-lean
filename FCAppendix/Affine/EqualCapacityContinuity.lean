import FCAppendix.Affine.EqualCapacity

noncomputable section
namespace FCAppendix.Affine.EqualCapacity
open Set MeasureTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

theorem kernel_cross (ξ : ℝ) (c : ℕ) (b b' p q : ι→ℝ)
    (hp : IsKernel ξ c b p) (hq : IsKernel ξ c b' q) :
    ∑i,(q i-p i)*(b i*(1-ξ*p i)-b' i*(1-ξ*q i))≤0 := by
  obtain ⟨hp0,hp1,hps,z,hz,hpt⟩ := hp
  obtain ⟨hq0,hq1,hqs,z',hz',hqt⟩ := hq
  have h₁ := Proposer.threshold_linear_optimal p (fun i=>b i*(1-ξ*p i)) z _
    hp0 hp1 hps hz hpt q hq0 hq1 hqs.le
  have h₂ := Proposer.threshold_linear_optimal q (fun i=>b' i*(1-ξ*q i)) z' _
    hq0 hq1 hqs hz' hqt p hp0 hp1 hps.le
  have he : (∑i,(q i-p i)*(b i*(1-ξ*p i)-b' i*(1-ξ*q i)))=
      ((∑i,q i*(b i*(1-ξ*p i)))-(∑i,p i*(b i*(1-ξ*p i))))+
      ((∑i,p i*(b' i*(1-ξ*q i)))-(∑i,q i*(b' i*(1-ξ*q i)))) := by
    rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  linarith

theorem kernel_perturbation {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (b b' p q : ι→ℝ) (hb : ∀i,0<b i)
    (hp : IsKernel ξ c b p) (hq : IsKernel ξ c b' q) (i : ι) :
    ξ*b i*(q i-p i)^2≤∑j,|b' j-b j| := by
  have hx := kernel_cross ξ c b b' p q hp hq
  have he : (∑j,(q j-p j)*(b j*(1-ξ*p j)-b' j*(1-ξ*q j)))=
      (∑j,ξ*b j*(q j-p j)^2)-(∑j,(q j-p j)*(b' j-b j)*(1-ξ*q j)) := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at hx
  have hs := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun j=>ξ*b j*(q j-p j)^2)
    (fun j _=>mul_nonneg (mul_nonneg hξ.le (hb j).le) (sq_nonneg _)) (Finset.mem_univ i)
  have hr : (∑j,(q j-p j)*(b' j-b j)*(1-ξ*q j))≤∑j,|b' j-b j| := by
    apply Finset.sum_le_sum
    intro j _
    have hp0 := hp.1 j
    have hp1 := hp.2.1 j
    have hq0 := hq.1 j
    have hq1 := hq.2.1 j
    have hd : |q j-p j|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
    have hh : |1-ξ*q j|≤1 := abs_le.mpr ⟨by nlinarith,by nlinarith [mul_nonneg hξ.le hq0]⟩
    calc
      (q j-p j)*(b' j-b j)*(1-ξ*q j)≤|(q j-p j)*(b' j-b j)*(1-ξ*q j)| := le_abs_self _
      _ = |q j-p j| * |b' j-b j| * |1-ξ*q j| := by rw [abs_mul,abs_mul]
      _ ≤ 1* |b' j-b j| * 1 := by gcongr
      _ = |b' j-b j| := by ring
  linarith

theorem continuousOn_kernelMarginal {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ) :
    ContinuousOn (kernelMarginal (ι:=ι) ξ c) {b | ∀i,0<b i} := by
  rw [continuousOn_pi]
  intro i
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  set N : ℝ := (Fintype.card ι:ℝ) with hNdef
  have hN : 0≤N := Nat.cast_nonneg _
  have hbi := hb i
  refine ⟨ε^2*(ξ*b i)/(N+1),by positivity,?_⟩
  intro b' hb' hdist
  have hh := kernel_perturbation hξ hξ1 c b b' (kernelMarginal ξ c b)
    (kernelMarginal ξ c b') hb (kernelMarginal_spec hξ hξ1 c b hb)
    (kernelMarginal_spec hξ hξ1 c b' hb') i
  have hs : (∑j,|b' j-b j|)≤N*dist b' b := by
    calc
      (∑j,|b' j-b j|)≤∑_j : ι,dist b' b := by
        apply Finset.sum_le_sum
        intro j _
        rw [←Real.dist_eq]
        exact dist_le_pi_dist b' b j
      _ = N*dist b' b := by simp [hNdef]
  have hsum := hh.trans hs
  have hd : (kernelMarginal ξ c b' i-kernelMarginal ξ c b i)^2<ε^2 := by
    have hδ : N*dist b' b≤N*(ε^2*(ξ*b i)/(N+1)) :=
      mul_le_mul_of_nonneg_left hdist.le hN
    have hfrac : N/(N+1)<1 := (div_lt_one (by linarith)).2 (by linarith)
    have hε2 : 0<ε^2 := sq_pos_of_pos hε
    have hcoef : 0<ξ*b i := mul_pos hξ hbi
    have he : N*(ε^2*(ξ*b i)/(N+1))=(N/(N+1)*ε^2)*(ξ*b i) := by ring
    rw [he] at hδ
    have hbound : (kernelMarginal ξ c b' i-kernelMarginal ξ c b i)^2≤N/(N+1)*ε^2 :=
      le_of_mul_le_mul_right (by nlinarith) hcoef
    nlinarith
  rw [Real.dist_eq]
  exact abs_lt_of_sq_lt_sq hd hε.le

theorem continuousAt_kernelMarginal {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (b : ι→ℝ) (hb : ∀i,0<b i) : ContinuousAt (kernelMarginal ξ c) b :=
  (continuousOn_kernelMarginal hξ hξ1 c).continuousAt (CommonList.isOpen_positive.mem_nhds hb)
end FCAppendix.Affine.EqualCapacity
