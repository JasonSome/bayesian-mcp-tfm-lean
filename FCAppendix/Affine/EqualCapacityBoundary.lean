import FCAppendix.Affine.EqualCapacityLottery

noncomputable section
namespace FCAppendix.Affine.EqualCapacity
open Set MeasureTheory Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positiveMarginal_linear_optimal {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (b q : ι→ℝ) (hq0 : ∀i,0≤q i) (hq1 : ∀i,q i≤1)
    (hqsum : (∑i,q i)≤(c:ℝ)) :
    (∑i,q i*(b i*(1-ξ*positiveMarginal ξ c b i)))≤
      ∑i,positiveMarginal ξ c b i*(b i*(1-ξ*positiveMarginal ξ c b i)) := by
  have hp := positiveMarginal_spec ξ c hξ hξ1 b
  obtain ⟨z,hz,ht,hslack⟩ := positiveMarginal_threshold hξ hξ1 c b
  let p := positiveMarginal ξ c b
  let r := fun i=>b i*(1-ξ*p i)
  have hcoord : ∑i,(q i-p i)*(r i-z)≤0 :=
    Finset.sum_nonpos (fun i _=>Proposer.coordinate_threshold p r z hp.1 hp.2.1 ht i
      (q i) (hq0 i) (hq1 i))
  have he : (∑i,(q i-p i)*(r i-z))=
      (∑i,q i*r i)-(∑i,p i*r i)-z*((∑i,q i)-(∑i,p i)) := by
    simp only [sub_mul,mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul]
    ring
  have hg : z*((∑i,q i)-(∑i,p i))≤0 := by
    have hh := mul_le_mul_of_nonneg_left (sub_le_sub_right hqsum (∑i,p i)) hz
    exact hh.trans (le_of_eq hslack)
  change (∑i,q i*r i)≤∑i,p i*r i
  linarith

theorem positive_kernel_cross {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (b b' : ι→ℝ) :
    let p := positiveMarginal ξ c b
    let q := positiveMarginal ξ c b'
    ∑i,(q i-p i)*(b i*(1-ξ*p i)-b' i*(1-ξ*q i))≤0 := by
  let p := positiveMarginal ξ c b
  let q := positiveMarginal ξ c b'
  have hp := positiveMarginal_spec ξ c hξ hξ1 b
  have hq := positiveMarginal_spec ξ c hξ hξ1 b'
  have hps : (∑i,p i)≤(c:ℝ) := hp.2.2.le.trans (Nat.cast_le.mpr (min_le_left _ _))
  have hqs : (∑i,q i)≤(c:ℝ) := hq.2.2.le.trans (Nat.cast_le.mpr (min_le_left _ _))
  have h₁ := positiveMarginal_linear_optimal hξ hξ1 c b q hq.1 hq.2.1 hqs
  have h₂ := positiveMarginal_linear_optimal hξ hξ1 c b' p hp.1 hp.2.1 hps
  have he : (∑i,(q i-p i)*(b i*(1-ξ*p i)-b' i*(1-ξ*q i)))=
      ((∑i,q i*(b i*(1-ξ*p i)))-(∑i,p i*(b i*(1-ξ*p i))))+
      ((∑i,p i*(b' i*(1-ξ*q i)))-(∑i,q i*(b' i*(1-ξ*q i)))) := by
    rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change (∑i,(q i-p i)*(b i*(1-ξ*p i)-b' i*(1-ξ*q i)))≤0
  rw [he]
  linarith

theorem positive_kernel_perturbation {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (b b' : ι→ℝ) (hb : ∀i,0≤b i) (i : ι) :
    ξ*b i*(positiveMarginal ξ c b' i-positiveMarginal ξ c b i)^2≤∑j,|b' j-b j| := by
  let p := positiveMarginal ξ c b
  let q := positiveMarginal ξ c b'
  have hp := positiveMarginal_spec ξ c hξ hξ1 b
  have hq := positiveMarginal_spec ξ c hξ hξ1 b'
  have hx := positive_kernel_cross hξ hξ1 c b b'
  change (∑j,(q j-p j)*(b j*(1-ξ*p j)-b' j*(1-ξ*q j)))≤0 at hx
  have he : (∑j,(q j-p j)*(b j*(1-ξ*p j)-b' j*(1-ξ*q j)))=
      (∑j,ξ*b j*(q j-p j)^2)-(∑j,(q j-p j)*(b' j-b j)*(1-ξ*q j)) := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at hx
  have hs := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun j=>ξ*b j*(q j-p j)^2)
    (fun j _=>mul_nonneg (mul_nonneg hξ.le (hb j)) (sq_nonneg _)) (Finset.mem_univ i)
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

theorem continuousAt_positiveMarginal_focal {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (b : ι→ℝ) (hb : ∀j,0≤b j) (i : ι) (hbi : 0<b i) :
    ContinuousAt (fun b' : ι→ℝ=>positiveMarginal ξ c b' i) b := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  set N : ℝ := (Fintype.card ι:ℝ) with hNdef
  have hN : 0≤N := Nat.cast_nonneg _
  refine ⟨ε^2*(ξ*b i)/(N+1),by positivity,?_⟩
  intro b' hdist
  have hh := positive_kernel_perturbation hξ hξ1 c b b' hb i
  have hs : (∑j,|b' j-b j|)≤N*dist b' b := by
    calc
      (∑j,|b' j-b j|)≤∑_j : ι,dist b' b := by
        apply Finset.sum_le_sum
        intro j _
        rw [←Real.dist_eq]
        exact dist_le_pi_dist b' b j
      _ = N*dist b' b := by simp [hNdef]
  have hsum := hh.trans hs
  have hd : (positiveMarginal ξ c b' i-positiveMarginal ξ c b i)^2<ε^2 := by
    have hδ : N*dist b' b≤N*(ε^2*(ξ*b i)/(N+1)) :=
      mul_le_mul_of_nonneg_left hdist.le hN
    have hfrac : N/(N+1)<1 := (div_lt_one (by linarith)).2 (by linarith)
    have hε2 : 0<ε^2 := sq_pos_of_pos hε
    have hcoef : 0<ξ*b i := mul_pos hξ hbi
    have he : N*(ε^2*(ξ*b i)/(N+1))=(N/(N+1)*ε^2)*(ξ*b i) := by ring
    rw [he] at hδ
    have hbound : (positiveMarginal ξ c b' i-positiveMarginal ξ c b i)^2≤N/(N+1)*ε^2 :=
      le_of_mul_le_mul_right (by nlinarith) hcoef
    nlinarith
  rw [Real.dist_eq]
  exact abs_lt_of_sq_lt_sq hd hε.le
end FCAppendix.Affine.EqualCapacity
