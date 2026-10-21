import FCAppendix.Existence.NarrowPayOnceProfileDerivative
import FCAppendix.Existence.NarrowPayOnceReceiptCurvature

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology
open PayOnce PayOnce.OwnImpact CommonList
open scoped BigOperators ContDiff

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem actual_linearized_equation {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι)
    (b : ι → ℝ) (hb : ∀ i, 0<b i)
    (hp : ∀ i, kernelMarginal n c b i ∈ Ioo (0:ℝ) 1) (h : ι → ℝ) :
    equationLinearAt n b (kernelMarginal n c b) (h,fderiv ℝ (kernelMarginal n c) b h)=0 := by
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
        ((ContinuousLinearMap.id ℝ (ι → ℝ)).prod (fderiv ℝ K b))) b := by
    have hh := HasFDerivAt.comp (𝕜:=ℝ) b (hasFDerivAt_kernelEquationAt n rho b p)
      ((hasFDerivAt_id b).prodMk hdiff.hasFDerivAt)
    simpa only [Function.comp_def,id_eq] using hh
  have hd0 : HasFDerivAt (𝕜:=ℝ) (fun a => kernelEquation n rho (a,K a)) 0 b :=
    (hasFDerivAt_const (𝕜:=ℝ) (0:ι → ℝ) b).congr_of_eventuallyEq hzero
  have hh := congrArg (fun J => J h) (hd.unique hd0)
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,zero_apply] using hh

def secondReceiptForcing (n : ℕ) (b p h k uh uk : ι → ℝ) : ι → ℝ := fun i =>
  -Hslope n (p i)*(h i*uk i+k i*uh i)+b i*Hcurvature n (p i)*uh i*uk i

theorem actual_second_linearized_equation {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι)
    (b : ι → ℝ) (hb : ∀ i, 0<b i)
    (hp : ∀ i, kernelMarginal n c b i ∈ Ioo (0:ℝ) 1) (h k : ι → ℝ) :
    let K := kernelMarginal (ι:=ι) n c
    let p := K b
    let uh := fderiv ℝ K b h
    let uk := fderiv ℝ K b k
    let v := secondReceiptForcing n b p h k uh uk
    let u2 := fderiv ℝ (fun a => fderiv ℝ K a h) b k
    equationLinearAt n b p ((fun i => v i/H n (p i)),u2)=0 := by
  let K := kernelMarginal (ι:=ι) n c
  let p := K b
  let uh := fderiv ℝ K b h
  let uk := fderiv ℝ K b k
  let v := secondReceiptForcing n b p h k uh uk
  let u := fun a => fderiv ℝ K a h
  let u2 := fderiv ℝ u b k
  change equationLinearAt n b p ((fun i => v i/H n (p i)),u2)=0
  have hK := contDiffAt_kernelMarginal_interior hn hc b hb hp
  have hdiff : DifferentiableAt ℝ K b := hK.differentiableAt (by simp)
  have hU : ContDiffAt ℝ 1 u b :=
    (hK.fderiv_right (m:=1) (WithTop.coe_le_coe.mpr le_top)).clm_apply contDiffAt_const
  have hdu : DifferentiableAt ℝ u b := hU.differentiableAt (by norm_num)
  let curve := fun t : ℝ => b+t • k
  have hcurve : HasDerivAt curve k 0 := by
    simpa [curve] using (((hasDerivAt_id (0:ℝ)).smul_const k).const_add b)
  have hcb : curve 0=b := by simp [curve]
  have hpc : HasDerivAt (fun t => K (curve t)) uk 0 := by
    have hh := HasFDerivAt.comp_hasDerivAt_of_eq (𝕜:=ℝ) (x:=(0:ℝ)) hdiff.hasFDerivAt hcurve hcb.symm
    simpa only [Function.comp_def] using hh
  have huc : HasDerivAt (fun t => u (curve t)) u2 0 := by
    have hh := HasFDerivAt.comp_hasDerivAt_of_eq (𝕜:=ℝ) (x:=(0:ℝ)) hdu.hasFDerivAt hcurve hcb.symm
    simpa only [Function.comp_def] using hh
  let R := fun t => receiptLinearAt n (curve t) (K (curve t)) (h,u (curve t))
  have hRi (i : ι) : HasDerivAt (fun t => R t i)
      (v i-b i*Hslope n (p i)*u2 i) 0 := by
    have hpi : HasDerivAt (fun t => K (curve t) i) (uk i) 0 := by
      exact hasDerivAt_pi.mp hpc i
    have hui : HasDerivAt (fun t => u (curve t) i) (u2 i) 0 := by
      exact hasDerivAt_pi.mp huc i
    have hbi : HasDerivAt (fun t => curve t i) (k i) 0 := by
      exact hasDerivAt_pi.mp hcurve i
    have hH : HasDerivAt (fun t => H n (K (curve t) i)) (-Hslope n (p i)*uk i) 0 := by
      have hh := (PayOnce.OwnImpact.hasDerivAt_H n (p i)).comp_of_eq (0:ℝ) hpi (by rw [hcb])
      simpa only [Function.comp_def] using hh
    have hsl : HasDerivAt (fun t => Hslope n (K (curve t) i)) (-Hcurvature n (p i)*uk i) 0 := by
      have hh := (hasDerivAt_Hslope n (p i)).comp_of_eq (0:ℝ) hpi (by rw [hcb])
      simpa only [Function.comp_def] using hh
    have hh := (hH.mul_const (h i)).sub ((hbi.mul hsl).mul hui)
    have he : (fun t => R t i)=(fun t => H n (K (curve t) i)*h i-
        curve t i*Hslope n (K (curve t) i)*u (curve t) i) := by
      funext t
      simp [R,receiptLinearAt,multiplyMap_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
      ring
    rw [he]
    convert hh using 1 <;> first | rfl | (simp only [hcb]; dsimp [v,secondReceiptForcing,uh,p,u]; rw [hcb]; ring)
  have hR : HasDerivAt R (v-multiplyMap (fun i => b i*Hslope n (p i)) u2) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    exact hRi i
  have hPR := (meanProjection ι).hasFDerivAt.comp_hasDerivAt (0:ℝ) hR
  have hPU := (meanProjection ι).hasFDerivAt.comp_hasDerivAt (0:ℝ) huc
  have hF := (hR.sub hPR).add hPU
  have hpos : ∀ᶠ t in 𝓝 (0:ℝ), ∀ i, 0<curve t i :=
    hcurve.continuousAt (by rw [hcb]; exact isOpen_positive.mem_nhds hb)
  have hint : ∀ᶠ t in 𝓝 (0:ℝ), ∀ i, K (curve t) i ∈ Ioo (0:ℝ) 1 := by
    apply Filter.eventually_all.mpr
    intro i
    exact ((continuous_apply i).continuousAt.comp hpc.continuousAt)
      (by change Ioo 0 1 ∈ 𝓝 (K (curve 0) i); rw [hcb]; exact isOpen_Ioo.mem_nhds (hp i))
  have hzero : (fun t => R t-meanProjection ι (R t)+meanProjection ι (u (curve t))) =ᶠ[𝓝 0]
      fun _ => (0:ι → ℝ) := by
    filter_upwards [hpos,hint] with t ht hi
    exact actual_linearized_equation hn hc (curve t) ht hi h
  have h0 : HasDerivAt (fun t => R t-meanProjection ι (R t)+meanProjection ι (u (curve t))) 0 (0:ℝ) :=
    (hasDerivAt_const (0:ℝ) (0:ι → ℝ)).congr_of_eventuallyEq hzero
  have hz := hF.unique h0
  have hrec : receiptLinearAt n b p ((fun i => v i/H n (p i)),u2)=
      v-multiplyMap (fun i => b i*Hslope n (p i)) u2 := by
    funext i
    have hHi : H n (p i)≠0 := (H_pos n (by omega) _ (hp i).1.le (hp i).2.le).ne'
    change H n (p i)*(v i/H n (p i))+(-(b i*Hslope n (p i)))*u2 i =
      v i-b i*Hslope n (p i)*u2 i
    field_simp
    ring
  change receiptLinearAt n b p ((fun i => v i/H n (p i)),u2)-
    meanProjection ι (receiptLinearAt n b p ((fun i => v i/H n (p i)),u2))+meanProjection ι u2=0
  rw [hrec]
  exact hz

theorem fderiv_fderiv_kernelMarginal_interior {n c : ℕ} (hn : 2 ≤ n)
    (hc : c ≤ Fintype.card ι) (b : ι → ℝ) (hb : ∀ i, 0<b i)
    (hp : ∀ i, kernelMarginal n c b i ∈ Ioo (0:ℝ) 1) (h k : ι → ℝ) (i : ι) :
    let K := kernelMarginal (ι:=ι) n c
    let p := K b
    let v := secondReceiptForcing n b p h k (fderiv ℝ K b h) (fderiv ℝ K b k)
    fderiv ℝ (fun a => fderiv ℝ K a h) b k i =
      sensitivity n (b i) (p i)*(v i-
        (∑ j, sensitivity n (b j) (p j)*v j)/(∑ j, sensitivity n (b j) (p j))) := by
  let K := kernelMarginal (ι:=ι) n c
  let p := K b
  let v := secondReceiptForcing n b p h k (fderiv ℝ K b h) (fderiv ℝ K b k)
  have heq := actual_second_linearized_equation hn hc b hb hp h k
  have hsol := linearized_kernel_solution hn b p (fun j => v j/H n (p j))
    (fderiv ℝ (fun a => fderiv ℝ K a h) b k) hb
    (fun j => ⟨(hp j).1.le,(hp j).2.le⟩) heq i
  have hH (j : ι) : H n (p j)≠0 := (H_pos n (by omega) _ (hp j).1.le (hp j).2.le).ne'
  have hcanc (j : ι) : H n (p j)*(v j/H n (p j))=v j := by field_simp [hH j]
  change _=sensitivity n (b i) (p i)*(v i-_)
  rw [hsol,hcanc]
  congr 2
  unfold priceDerivative
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc,hcanc]

omit [Nonempty ι] in
theorem secondReceiptForcing_abs_le {n : ℕ} (hn : 2 ≤ n)
    {upper A : ℝ} (hA : 0≤A) (b p h k uh uk : ι → ℝ)
    (hb : ∀ i, 0<b i ∧ b i≤upper) (hp : ∀ i, p i∈Icc (0:ℝ) 1)
    (huh : ∀ i, |uh i|≤A*‖h‖) (huk : ∀ i, |uk i|≤A*‖k‖) (i : ι) :
    |secondReceiptForcing n b p h k uh uk i|≤
      (2*(n:ℝ)*A+upper*(n:ℝ)^2*A^2)*‖h‖*‖k‖ := by
  have hupper : 0≤upper := (hb i).1.le.trans (hb i).2
  have hh : |h i|≤‖h‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm h i
  have hk : |k i|≤‖k‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm k i
  have hs : 0≤Hslope n (p i) := (Hslope_pos hn (hp i)).le
  have hcurv : 0≤Hcurvature n (p i) := Hcurvature_nonneg n (hp i).2
  have hsum : |h i*uk i+k i*uh i|≤|h i| * |uk i|+|k i| * |uh i| := by
    simpa only [abs_mul] using abs_add_le (h i*uk i) (k i*uh i)
  calc
    _ ≤ Hslope n (p i)*(|h i| * |uk i|+|k i| * |uh i|)+
        b i*Hcurvature n (p i)*|uh i| * |uk i| := by
      unfold secondReceiptForcing
      calc
        _ ≤ |-Hslope n (p i)*(h i*uk i+k i*uh i)|+
          |b i*Hcurvature n (p i)*uh i*uk i| := abs_add_le _ _
        _ ≤ _ := by
          simp only [abs_neg,abs_mul,abs_of_nonneg hs,abs_of_pos (hb i).1,
            abs_of_nonneg hcurv]
          exact add_le_add (mul_le_mul_of_nonneg_left hsum hs) le_rfl
    _ ≤ (n:ℝ)*(‖h‖*(A*‖k‖)+‖k‖*(A*‖h‖))+
        upper*(n:ℝ)^2*(A*‖h‖)*(A*‖k‖) := by
      gcongr
      · exact (Hslope_bounds hn (hp i)).2
      · exact huk i
      · exact huh i
      · exact (hb i).2
      · exact Hcurvature_upper (show 0<n by omega) (hp i)
      · exact huh i
      · exact huk i
    _ = _ := by ring

theorem norm_fderiv_fderiv_kernelMarginal_le {n c : ℕ} (hn : 2 ≤ n)
    (hc : c ≤ Fintype.card ι) {lower upper : ℝ} (hlower : 0<lower)
    (b : ι → ℝ) (hb : ∀ i, lower≤b i ∧ b i≤upper)
    (hp : ∀ i, kernelMarginal n c b i∈Ioo (0:ℝ) 1) (h k : ι → ℝ) :
    ‖fderiv ℝ (fun a => fderiv ℝ (kernelMarginal n c) a h) b k‖≤
      (2*(n:ℝ)/lower)*(2*(n:ℝ)*(2*(n:ℝ)/lower)+
        upper*(n:ℝ)^2*(2*(n:ℝ)/lower)^2)*‖h‖*‖k‖ := by
  let K := kernelMarginal (ι:=ι) n c
  let p := K b
  let A := 2*(n:ℝ)/lower
  let C := 2*(n:ℝ)*A+upper*(n:ℝ)^2*A^2
  let v := secondReceiptForcing n b p h k (fderiv ℝ K b h) (fderiv ℝ K b k)
  have hb0 (i : ι) : 0<b i := hlower.trans_le (hb i).1
  have hp' (i : ι) : p i∈Icc (0:ℝ) 1 := ⟨(hp i).1.le,(hp i).2.le⟩
  have hupper : 0≤upper := (hb0 (Classical.choice inferInstance)).le.trans
    (hb (Classical.choice inferInstance)).2
  have hA : 0≤A := by dsimp [A]; positivity
  have hC : 0≤C := by dsimp [C]; positivity
  have hnorm : ‖fderiv ℝ K b‖≤A := norm_fderiv_kernelMarginal_le hn hc hlower b
    (fun i => (hb i).1) hp
  have hvalue (l : ι → ℝ) (i : ι) : |fderiv ℝ K b l i|≤A*‖l‖ := by
    have hi : |fderiv ℝ K b l i|≤‖fderiv ℝ K b l‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fderiv ℝ K b l) i
    exact hi.trans
      (((fderiv ℝ K b).le_opNorm l).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)))
  have hv (i : ι) : |v i|≤C*‖h‖*‖k‖ :=
    secondReceiptForcing_abs_le hn hA b p h k _ _
      (fun j => ⟨hb0 j,(hb j).2⟩) hp' (hvalue h) (hvalue k) i
  have havg := weighted_average_abs_le (fun i => sensitivity n (b i) (p i)) v
    (fun i => sensitivity_pos hn (hb0 i) (hp' i)) hv
  change _≤A*C*‖h‖*‖k‖
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs,fderiv_fderiv_kernelMarginal_interior hn hc b hb0 hp h k i,
    abs_mul,abs_of_pos (sensitivity_pos hn (hb0 i) (hp' i))]
  have hdiff := (abs_sub _ _).trans (add_le_add (hv i) havg)
  have hs := sensitivity_uniform_upper hn hlower (hb i).1 (hp' i)
  calc
    _ ≤ ((n:ℝ)/lower)*(C*‖h‖*‖k‖+C*‖h‖*‖k‖) :=
      mul_le_mul hs hdiff (abs_nonneg _) (by positivity)
    _ = _ := by dsimp [A]; ring

end FCAppendix.Existence.NarrowPayOnce
