import FCAppendix.Existence.NarrowPayOnceSmoothInterior

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology
open PayOnce PayOnce.OwnImpact CommonList
open scoped BigOperators ContDiff

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def priceDerivative (n : ℕ) (b p h : ι → ℝ) : ℝ :=
  (∑ j, sensitivity n (b j) (p j)*H n (p j)*h j)/(∑ j, sensitivity n (b j) (p j))

theorem linearized_kernel_solution {n : ℕ} (hn : 2 ≤ n) (b p h u : ι → ℝ)
    (hb : ∀ i, 0<b i) (hp : ∀ i, p i ∈ Icc (0:ℝ) 1)
    (heq : equationLinearAt n b p (h,u)=0) (i : ι) :
    u i=sensitivity n (b i) (p i)*(H n (p i)*h i-priceDerivative n b p h) := by
  let r := receiptLinearAt n b p (h,u)
  have hrel : r-meanProjection ι r+meanProjection ι u=0 := heq
  have hPu : meanProjection ι u=0 := by
    have hh := congrArg (meanProjection ι) hrel
    simpa only [map_add,map_sub,meanProjection_idempotent,sub_self,zero_add,map_zero] using hh
  have hr : r=meanProjection ι r := by
    rw [hPu,add_zero] at hrel
    exact sub_eq_zero.mp hrel
  let L := (∑ j, r j)/(Fintype.card ι:ℝ)
  have hrL (j : ι) : H n (p j)*h j-(b j*Hslope n (p j))*u j=L := by
    have hh := congrFun hr j
    simpa [r,receiptLinearAt,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
      multiplyMap_apply,meanProjection_apply,L,sub_eq_add_neg] using hh
  have hsol (j : ι) : u j=sensitivity n (b j) (p j)*(H n (p j)*h j-L) := by
    have hden : b j*Hslope n (p j)≠0 := (mul_pos (hb j) (Hslope_pos hn (hp j))).ne'
    calc
      _ = (H n (p j)*h j-L)/(b j*Hslope n (p j)) := (eq_div_iff hden).mpr (by linarith [hrL j])
      _ = _ := by simp [sensitivity,mul_comm,div_eq_mul_inv]
  have hsumu : (∑ j, u j)=0 := by
    have hh := congrFun hPu i
    rw [meanProjection_apply,Pi.zero_apply] at hh
    simpa only [zero_mul] using (div_eq_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).mp hh
  have hsumrel : (∑ j, u j)=(∑ j, sensitivity n (b j) (p j)*H n (p j)*h j)-
      L*(∑ j, sensitivity n (b j) (p j)) := by
    calc
      _ = ∑ j, sensitivity n (b j) (p j)*(H n (p j)*h j-L) := Finset.sum_congr rfl fun j _ => hsol j
      _ = _ := by simp only [mul_sub,mul_assoc,Finset.sum_sub_distrib,← Finset.sum_mul]; ring
  have hT : 0<∑ j, sensitivity n (b j) (p j) :=
    Finset.sum_pos (fun j _ => sensitivity_pos hn (hb j) (hp j)) Finset.univ_nonempty
  have hL : L=priceDerivative n b p h := by
    apply (eq_div_iff hT.ne').mpr
    linarith
  rw [hsol i,hL]

theorem fderiv_kernelMarginal_interior {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι)
    (b : ι → ℝ) (hb : ∀ i, 0<b i)
    (hp : ∀ i, kernelMarginal n c b i ∈ Ioo (0:ℝ) 1) (h : ι → ℝ) (i : ι) :
    fderiv ℝ (kernelMarginal n c) b h i=
      sensitivity n (b i) (kernelMarginal n c b i)*
        (H n (kernelMarginal n c b i)*h i-priceDerivative n b (kernelMarginal n c b) h) := by
  let K := kernelMarginal (ι:=ι) n c
  let p := K b
  let rho : ℝ := (c:ℝ)/(Fintype.card ι:ℝ)
  have hcap : (Fintype.card ι:ℝ)*rho=c := by dsimp [rho]; field_simp
  have hK := contDiffAt_kernelMarginal_interior hn hc b hb hp
  have hdiff : DifferentiableAt ℝ K b := hK.differentiableAt (by simp)
  have hcont := hdiff.continuousAt
  have hpositive : ∀ᶠ a in 𝓝 b, ∀ j, 0<a j := isOpen_positive.mem_nhds hb
  have hinterior : ∀ᶠ a in 𝓝 b, ∀ j, K a j ∈ Ioo (0:ℝ) 1 :=
    Filter.eventually_all.mpr fun j => ((continuous_apply j).continuousAt.comp hcont)
      (isOpen_Ioo.mem_nhds (hp j))
  have hzero : (fun a => kernelEquation n rho (a,K a)) =ᶠ[𝓝 b] fun _ => (0:ι → ℝ) := by
    filter_upwards [hpositive,hinterior] with a ha hi
    exact kernelEquation_actual hn hc hcap a ha hi
  have hd : HasFDerivAt (fun a => kernelEquation n rho (a,K a))
      ((equationLinearAt n b p).comp
        ((ContinuousLinearMap.id ℝ (ι → ℝ)).prod (fderiv ℝ K b))) b :=
    by
      have hh := HasFDerivAt.comp (𝕜:=ℝ) b (hasFDerivAt_kernelEquationAt n rho b p)
        ((hasFDerivAt_id b).prodMk hdiff.hasFDerivAt)
      simpa only [Function.comp_def,id_eq] using hh
  have hd0 : HasFDerivAt (𝕜:=ℝ) (fun a => kernelEquation n rho (a,K a)) 0 b :=
    (hasFDerivAt_const (𝕜:=ℝ) (0:ι → ℝ) b).congr_of_eventuallyEq hzero
  have hlin := hd.unique hd0
  have heq : equationLinearAt n b p (h,fderiv ℝ K b h)=0 := by
    have hh := congrArg (fun J => J h) hlin
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply,zero_apply] using hh
  exact linearized_kernel_solution hn b p h _ hb (fun j => ⟨(hp j).1.le,(hp j).2.le⟩) heq i

theorem priceDerivative_constant {n : ℕ} (hn : 2 ≤ n) {B rho : ℝ}
    (hB : 0<B) (hrho : rho ∈ Ioo (0:ℝ) 1) (h : ι → ℝ) :
    priceDerivative n (fun _ => B) (fun _ => rho) h=
      H n rho*(∑ j, h j)/(Fintype.card ι:ℝ) := by
  have hden : B*Hslope n rho≠0 := (mul_pos hB (Hslope_pos hn ⟨hrho.1.le,hrho.2.le⟩)).ne'
  have hN : (Fintype.card ι:ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold priceDerivative
  rw [← Finset.mul_sum]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,sensitivity]
  field_simp [hB.ne',(Hslope_pos hn ⟨hrho.1.le,hrho.2.le⟩).ne',hN]

theorem fderiv_kernelMarginal_constant {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι)
    {B rho : ℝ} (hB : 0<B) (hrho : rho ∈ Ioo (0:ℝ) 1)
    (hcap : (Fintype.card ι:ℝ)*rho=c) :
    fderiv ℝ (kernelMarginal (ι:=ι) n c) (fun _ => B)=
      (H n rho/(B*Hslope n rho)) • (ContinuousLinearMap.id ℝ (ι → ℝ)-meanProjection ι) := by
  have hbase := kernelMarginal_constant hn hc hB hrho hcap
  have hp (i : ι) : kernelMarginal n c (fun _ : ι => B) i ∈ Ioo (0:ℝ) 1 := by
    rw [hbase]
    exact hrho
  apply ContinuousLinearMap.ext
  intro h
  funext i
  rw [fderiv_kernelMarginal_interior hn hc (fun _ => B) (fun _ => hB) hp h i,hbase,
    priceDerivative_constant hn hB hrho h]
  simp only [smul_apply,sub_apply,ContinuousLinearMap.id_apply,Pi.smul_apply,Pi.sub_apply,
    smul_eq_mul,meanProjection_apply,sensitivity]
  have hden : B*Hslope n rho≠0 := (mul_pos hB (Hslope_pos hn ⟨hrho.1.le,hrho.2.le⟩)).ne'
  have hN : (Fintype.card ι:ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp [hB.ne',(Hslope_pos hn ⟨hrho.1.le,hrho.2.le⟩).ne',hN]

theorem weighted_average_abs_le (s x : ι → ℝ) (hs : ∀ i, 0<s i) {C : ℝ}
    (hx : ∀ i, |x i| ≤ C) : |(∑ i, s i*x i)/(∑ i, s i)| ≤ C := by
  have hT : 0<∑ i, s i := Finset.sum_pos (fun i _ => hs i) Finset.univ_nonempty
  rw [abs_div,abs_of_pos hT]
  apply (div_le_iff₀ hT).mpr
  calc
    _ ≤ ∑ i, |s i*x i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, s i*|x i| := by simp only [abs_mul,abs_of_pos (hs _)]
    _ ≤ ∑ i, s i*C := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i) (hs i).le
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem priceDerivative_abs_le_norm {n : ℕ} (hn : 2 ≤ n) (b p h : ι → ℝ)
    (hb : ∀ i, 0<b i) (hp : ∀ i, p i ∈ Icc (0:ℝ) 1) :
    |priceDerivative n b p h| ≤ ‖h‖ := by
  unfold priceDerivative
  simp_rw [mul_assoc]
  apply weighted_average_abs_le (fun i => sensitivity n (b i) (p i)) (fun i => H n (p i)*h i)
    (fun i => sensitivity_pos hn (hb i) (hp i))
  intro i
  rw [abs_mul,abs_of_pos (H_pos n (by omega) _ (hp i).1 (hp i).2)]
  have hh : |h i| ≤ ‖h‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm h i
  exact (mul_le_mul_of_nonneg_right (H_bounds n (by omega) _ (hp i).1 (hp i).2).2
    (abs_nonneg _)).trans (by simpa only [one_mul] using hh)

theorem sensitivity_uniform_upper {n : ℕ} (hn : 2 ≤ n) {b p lower : ℝ}
    (hlower : 0<lower) (hb : lower ≤ b) (hp : p ∈ Icc (0:ℝ) 1) :
    sensitivity n b p ≤ (n:ℝ)/lower := by
  have hb0 := hlower.trans_le hb
  have hden := mul_pos hb0 (Hslope_pos hn hp)
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hs := (div_le_iff₀ hnR).mp (Hslope_bounds hn hp).1
  change 1/(b*Hslope n p) ≤ (n:ℝ)/lower
  apply (div_le_div_iff₀ hden hlower).mpr
  have hh := mul_le_mul_of_nonneg_left hs hb0.le
  nlinarith

theorem norm_fderiv_kernelMarginal_le {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι)
    {lower : ℝ} (hlower : 0<lower) (b : ι → ℝ) (hb : ∀ i, lower ≤ b i)
    (hp : ∀ i, kernelMarginal n c b i ∈ Ioo (0:ℝ) 1) :
    ‖fderiv ℝ (kernelMarginal n c) b‖ ≤ 2*(n:ℝ)/lower := by
  have hb0 (i : ι) : 0<b i := hlower.trans_le (hb i)
  have hp' (i : ι) : kernelMarginal n c b i ∈ Icc (0:ℝ) 1 := ⟨(hp i).1.le,(hp i).2.le⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs,fderiv_kernelMarginal_interior hn hc b hb0 hp h i,abs_mul,
    abs_of_pos (sensitivity_pos hn (hb0 i) (hp' i))]
  have hprice := priceDerivative_abs_le_norm hn b (kernelMarginal n c b) h hb0 hp'
  have hgain : |H n (kernelMarginal n c b i)*h i| ≤ ‖h‖ := by
    rw [abs_mul,abs_of_pos (H_pos n (by omega) _ (hp' i).1 (hp' i).2)]
    have hh : |h i| ≤ ‖h‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm h i
    exact (mul_le_mul_of_nonneg_right (H_bounds n (by omega) _ (hp' i).1 (hp' i).2).2
      (abs_nonneg _)).trans (by simpa only [one_mul] using hh)
  have hdiff := (abs_sub _ _).trans (add_le_add hgain hprice)
  have hs := sensitivity_uniform_upper hn hlower (hb i) (hp' i)
  calc
    _ ≤ ((n:ℝ)/lower)*(‖h‖+‖h‖) := mul_le_mul hs hdiff (abs_nonneg _) (by positivity)
    _ = _ := by ring

end FCAppendix.Existence.NarrowPayOnce
