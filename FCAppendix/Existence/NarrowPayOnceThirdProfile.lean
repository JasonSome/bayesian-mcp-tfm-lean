import FCAppendix.Existence.NarrowPayOnceSecondProfile

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology
open PayOnce PayOnce.OwnImpact CommonList
open scoped BigOperators ContDiff

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem actual_second_residual_equation {n c : ℕ} (hn : 2 ≤ n)
    (hc : c ≤ Fintype.card ι) (b : ι → ℝ) (hb : ∀ i, 0<b i)
    (hp : ∀ i, kernelMarginal n c b i ∈ Ioo (0:ℝ) 1) (h k : ι → ℝ) :
    let K := kernelMarginal (ι:=ι) n c
    let p := K b
    let v := secondReceiptForcing n b p h k (fderiv ℝ K b h) (fderiv ℝ K b k)
    let u := fderiv ℝ (fun a => fderiv ℝ K a h) b k
    let r := v-multiplyMap (fun i => b i*Hslope n (p i)) u
    r-meanProjection ι r+meanProjection ι u=0 := by
  let K := kernelMarginal (ι:=ι) n c
  let p := K b
  let v := secondReceiptForcing n b p h k (fderiv ℝ K b h) (fderiv ℝ K b k)
  let u := fderiv ℝ (fun a => fderiv ℝ K a h) b k
  have heq := actual_second_linearized_equation hn hc b hb hp h k
  have hr : receiptLinearAt n b p ((fun i => v i/H n (p i)),u)=
      v-multiplyMap (fun i => b i*Hslope n (p i)) u := by
    funext i
    have hH : H n (p i)≠0 := (H_pos n (by omega) _ (hp i).1.le (hp i).2.le).ne'
    change H n (p i)*(v i/H n (p i))+(-(b i*Hslope n (p i)))*u i =
      v i-b i*Hslope n (p i)*u i
    field_simp
    ring
  change receiptLinearAt n b p ((fun i => v i/H n (p i)),u)-
    meanProjection ι (receiptLinearAt n b p ((fun i => v i/H n (p i)),u))+
      meanProjection ι u=0 at heq
  rw [hr] at heq
  exact heq

def thirdReceiptForcing (n : ℕ) (b p h k l uh uk ul uhk uhl ukl : ι → ℝ) : ι → ℝ := fun i =>
  Hcurvature n (p i)*(ul i*(h i*uk i+k i*uh i)+l i*uh i*uk i)-
  Hslope n (p i)*(h i*ukl i+k i*uhl i+l i*uhk i)+
  b i*Hcurvature n (p i)*(uhl i*uk i+uh i*ukl i+ul i*uhk i)-
  b i*Hthird n (p i)*ul i*uh i*uk i

theorem actual_third_linearized_equation {n c : ℕ} (hn : 2 ≤ n)
    (hc : c ≤ Fintype.card ι) (b : ι → ℝ) (hb : ∀ i, 0<b i)
    (hp : ∀ i, kernelMarginal n c b i ∈ Ioo (0:ℝ) 1) (h k l : ι → ℝ) :
    let K := kernelMarginal (ι:=ι) n c
    let p := K b
    let u1 := fun h a => fderiv ℝ K a h
    let u2 := fun h k a => fderiv ℝ (u1 h) a k
    let v := thirdReceiptForcing n b p h k l (u1 h b) (u1 k b) (u1 l b)
      (u2 h k b) (u2 h l b) (u2 k l b)
    let u3 := fderiv ℝ (u2 h k) b l
    equationLinearAt n b p ((fun i => v i/H n (p i)),u3)=0 := by
  let K := kernelMarginal (ι:=ι) n c
  let p := K b
  let u1 := fun h a => fderiv ℝ K a h
  let u2 := fun h k a => fderiv ℝ (u1 h) a k
  let v := thirdReceiptForcing n b p h k l (u1 h b) (u1 k b) (u1 l b)
      (u2 h k b) (u2 h l b) (u2 k l b)
  let u3 := fderiv ℝ (u2 h k) b l
  change equationLinearAt n b p ((fun i => v i/H n (p i)),u3)=0
  have hK := contDiffAt_kernelMarginal_interior hn hc b hb hp
  have hdK : DifferentiableAt ℝ K b := hK.differentiableAt (by simp)
  have hU (z : ι → ℝ) : ContDiffAt ℝ 2 (u1 z) b :=
    (hK.fderiv_right (m:=2) (WithTop.coe_le_coe.mpr le_top)).clm_apply contDiffAt_const
  have hdU (z : ι → ℝ) : DifferentiableAt ℝ (u1 z) b :=
    (hU z).differentiableAt (by norm_num)
  have hU2 : ContDiffAt ℝ 1 (u2 h k) b :=
    ((hU h).fderiv_right (m:=1) (by norm_num)).clm_apply contDiffAt_const
  have hdU2 : DifferentiableAt ℝ (u2 h k) b := hU2.differentiableAt (by norm_num)
  let curve := fun t : ℝ => b+t • l
  have hcurve : HasDerivAt curve l 0 := by
    simpa [curve] using (((hasDerivAt_id (0:ℝ)).smul_const l).const_add b)
  have hcb : curve 0=b := by simp [curve]
  have hpc : HasDerivAt (fun t => K (curve t)) (u1 l b) 0 := by
    have hh := HasFDerivAt.comp_hasDerivAt_of_eq (𝕜:=ℝ) (x:=(0:ℝ)) hdK.hasFDerivAt hcurve hcb.symm
    simpa only [Function.comp_def] using hh
  have huc (z : ι → ℝ) : HasDerivAt (fun t => u1 z (curve t)) (u2 z l b) 0 := by
    have hh := HasFDerivAt.comp_hasDerivAt_of_eq (𝕜:=ℝ) (x:=(0:ℝ))
      (hdU z).hasFDerivAt hcurve hcb.symm
    simpa only [Function.comp_def] using hh
  have hvc : HasDerivAt (fun t => u2 h k (curve t)) u3 0 := by
    have hh := HasFDerivAt.comp_hasDerivAt_of_eq (𝕜:=ℝ) (x:=(0:ℝ))
      hdU2.hasFDerivAt hcurve hcb.symm
    simpa only [Function.comp_def] using hh
  let R := fun t => secondReceiptForcing n (curve t) (K (curve t)) h k
      (u1 h (curve t)) (u1 k (curve t))-
    multiplyMap (fun i => curve t i*Hslope n (K (curve t) i)) (u2 h k (curve t))
  have hRi (i : ι) : HasDerivAt (fun t => R t i)
      (v i-b i*Hslope n (p i)*u3 i) 0 := by
    have hpi := hasDerivAt_pi.mp hpc i
    have hui := hasDerivAt_pi.mp (huc h) i
    have hki := hasDerivAt_pi.mp (huc k) i
    have hu2i := hasDerivAt_pi.mp hvc i
    have hbi := hasDerivAt_pi.mp hcurve i
    have hsl : HasDerivAt (fun t => Hslope n (K (curve t) i))
        (-Hcurvature n (p i)*u1 l b i) 0 := by
      have hh := (hasDerivAt_Hslope n (p i)).comp_of_eq (0:ℝ) hpi (by rw [hcb])
      simpa only [Function.comp_def] using hh
    have hcurv : HasDerivAt (fun t => Hcurvature n (K (curve t) i))
        (-Hthird n (p i)*u1 l b i) 0 := by
      have hh := (hasDerivAt_Hcurvature n (p i)).comp_of_eq (0:ℝ) hpi (by rw [hcb])
      simpa only [Function.comp_def] using hh
    have hsum := (hki.const_mul (h i)).add (hui.const_mul (k i))
    have hfirst := hsl.neg.mul hsum
    have hsecond := ((hbi.mul hcurv).mul hui).mul hki
    have hthird := (hbi.mul hsl).mul hu2i
    have hh := (hfirst.add hsecond).sub hthird
    have he : (fun t => R t i)=(fun t =>
        -Hslope n (K (curve t) i)*(h i*u1 k (curve t) i+k i*u1 h (curve t) i)+
        curve t i*Hcurvature n (K (curve t) i)*u1 h (curve t) i*u1 k (curve t) i-
        curve t i*Hslope n (K (curve t) i)*u2 h k (curve t) i) := by
      funext t
      rfl
    rw [he]
    convert hh using 1 <;> first | rfl |
      (simp only [hcb]; dsimp [v,thirdReceiptForcing,p]; rw [hcb]; ring)
  have hR : HasDerivAt R (v-multiplyMap (fun i => b i*Hslope n (p i)) u3) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    exact hRi i
  have hPR := (meanProjection ι).hasFDerivAt.comp_hasDerivAt (0:ℝ) hR
  have hPU := (meanProjection ι).hasFDerivAt.comp_hasDerivAt (0:ℝ) hvc
  have hF := (hR.sub hPR).add hPU
  have hpos : ∀ᶠ t in 𝓝 (0:ℝ), ∀ i, 0<curve t i :=
    hcurve.continuousAt (by rw [hcb]; exact isOpen_positive.mem_nhds hb)
  have hint : ∀ᶠ t in 𝓝 (0:ℝ), ∀ i, K (curve t) i ∈ Ioo (0:ℝ) 1 := by
    apply Filter.eventually_all.mpr
    intro i
    exact ((continuous_apply i).continuousAt.comp hpc.continuousAt)
      (by change Ioo 0 1 ∈ 𝓝 (K (curve 0) i); rw [hcb]; exact isOpen_Ioo.mem_nhds (hp i))
  have hzero : (fun t => R t-meanProjection ι (R t)+meanProjection ι (u2 h k (curve t))) =ᶠ[𝓝 0]
      fun _ => (0:ι → ℝ) := by
    filter_upwards [hpos,hint] with t ht hi
    exact actual_second_residual_equation hn hc (curve t) ht hi h k
  have h0 : HasDerivAt (fun t => R t-meanProjection ι (R t)+meanProjection ι (u2 h k (curve t)))
      0 (0:ℝ) := (hasDerivAt_const (0:ℝ) (0:ι → ℝ)).congr_of_eventuallyEq hzero
  have hz := hF.unique h0
  have hrec : receiptLinearAt n b p ((fun i => v i/H n (p i)),u3)=
      v-multiplyMap (fun i => b i*Hslope n (p i)) u3 := by
    funext i
    have hH : H n (p i)≠0 := (H_pos n (by omega) _ (hp i).1.le (hp i).2.le).ne'
    change H n (p i)*(v i/H n (p i))+(-(b i*Hslope n (p i)))*u3 i =
      v i-b i*Hslope n (p i)*u3 i
    field_simp
    ring
  change receiptLinearAt n b p ((fun i => v i/H n (p i)),u3)-
    meanProjection ι (receiptLinearAt n b p ((fun i => v i/H n (p i)),u3))+meanProjection ι u3=0
  rw [hrec]
  exact hz

theorem fderiv_fderiv_fderiv_kernelMarginal_interior {n c : ℕ} (hn : 2 ≤ n)
    (hc : c ≤ Fintype.card ι) (b : ι → ℝ) (hb : ∀ i, 0<b i)
    (hp : ∀ i, kernelMarginal n c b i ∈ Ioo (0:ℝ) 1) (h k l : ι → ℝ) (i : ι) :
    let K := kernelMarginal (ι:=ι) n c
    let p := K b
    let u1 := fun h a => fderiv ℝ K a h
    let u2 := fun h k a => fderiv ℝ (u1 h) a k
    let v := thirdReceiptForcing n b p h k l (u1 h b) (u1 k b) (u1 l b)
      (u2 h k b) (u2 h l b) (u2 k l b)
    fderiv ℝ (u2 h k) b l i = sensitivity n (b i) (p i)*(v i-
      (∑ j, sensitivity n (b j) (p j)*v j)/(∑ j, sensitivity n (b j) (p j))) := by
  let K := kernelMarginal (ι:=ι) n c
  let p := K b
  let u1 := fun h a => fderiv ℝ K a h
  let u2 := fun h k a => fderiv ℝ (u1 h) a k
  let v := thirdReceiptForcing n b p h k l (u1 h b) (u1 k b) (u1 l b)
      (u2 h k b) (u2 h l b) (u2 k l b)
  have heq := actual_third_linearized_equation hn hc b hb hp h k l
  have hsol := linearized_kernel_solution hn b p (fun j => v j/H n (p j))
    (fderiv ℝ (u2 h k) b l) hb
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
theorem thirdReceiptForcing_abs_le {n : ℕ} (hn : 2 ≤ n)
    {upper A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (b p h k l uh uk ul uhk uhl ukl : ι → ℝ)
    (hb : ∀ i, 0<b i ∧ b i≤upper) (hp : ∀ i, p i∈Icc (0:ℝ) 1)
    (huh : ∀ i, |uh i|≤A*‖h‖) (huk : ∀ i, |uk i|≤A*‖k‖)
    (hul : ∀ i, |ul i|≤A*‖l‖)
    (huhk : ∀ i, |uhk i|≤B*‖h‖*‖k‖)
    (huhl : ∀ i, |uhl i|≤B*‖h‖*‖l‖)
    (hukl : ∀ i, |ukl i|≤B*‖k‖*‖l‖) (i : ι) :
    |thirdReceiptForcing n b p h k l uh uk ul uhk uhl ukl i|≤
      (3*(n:ℝ)^2*A^2+3*(n:ℝ)*B+3*upper*(n:ℝ)^2*A*B+
        upper*(n:ℝ)^3*A^3)*‖h‖*‖k‖*‖l‖ := by
  have hupper : 0≤upper := (hb i).1.le.trans (hb i).2
  have hh : |h i|≤‖h‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm h i
  have hk : |k i|≤‖k‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm k i
  have hl : |l i|≤‖l‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm l i
  have hs : 0≤Hslope n (p i) := (Hslope_pos hn (hp i)).le
  have hq : 0≤Hcurvature n (p i) := Hcurvature_nonneg n (hp i).2
  have ht : 0≤Hthird n (p i) := Hthird_nonneg n (hp i).2
  have habs (a b c d : ℝ) : |a-b+c-d|≤|a|+|b|+|c|+|d| := by
    exact (abs_sub _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)) le_rfl)
  have hsum2 (a b c d : ℝ) : |a*b+c*d|≤|a| * |b|+|c| * |d| := by
    simpa only [abs_mul] using abs_add_le (a*b) (c*d)
  have hsum3 (a b c d e f : ℝ) : |a*b+c*d+e*f|≤|a| * |b|+|c| * |d|+|e| * |f| := by
    exact (abs_add_le _ _).trans (add_le_add (hsum2 a b c d) (by rw [abs_mul]))
  have hX : |ul i*(h i*uk i+k i*uh i)+l i*uh i*uk i|≤
      |ul i| * (|h i| * |uk i|+|k i| * |uh i|)+|l i| * |uh i| * |uk i| := by
    refine (abs_add_le _ _).trans ?_
    simp only [abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (hsum2 _ _ _ _) (abs_nonneg _)) le_rfl
  calc
    _ ≤ Hcurvature n (p i)*(|ul i| * (|h i| * |uk i|+|k i| * |uh i|)+
          |l i| * |uh i| * |uk i|)+
        Hslope n (p i)*(|h i| * |ukl i|+|k i| * |uhl i|+|l i| * |uhk i|)+
        b i*Hcurvature n (p i)*(|uhl i| * |uk i|+|uh i| * |ukl i|+|ul i| * |uhk i|)+
        b i*Hthird n (p i)*|ul i| * |uh i| * |uk i| := by
      unfold thirdReceiptForcing
      refine (habs _ _ _ _).trans ?_
      simp only [abs_mul,abs_of_nonneg hq,abs_of_nonneg hs,abs_of_nonneg ht,
        abs_of_pos (hb i).1]
      exact add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hX hq)
        (mul_le_mul_of_nonneg_left (hsum3 _ _ _ _ _ _) hs))
        (mul_le_mul_of_nonneg_left (hsum3 _ _ _ _ _ _) (mul_nonneg (hb i).1.le hq))) le_rfl
    _ ≤ (n:ℝ)^2*((A*‖l‖)*(‖h‖*(A*‖k‖)+‖k‖*(A*‖h‖))+
          ‖l‖*(A*‖h‖)*(A*‖k‖))+
        (n:ℝ)*(‖h‖*(B*‖k‖*‖l‖)+‖k‖*(B*‖h‖*‖l‖)+‖l‖*(B*‖h‖*‖k‖))+
        upper*(n:ℝ)^2*((B*‖h‖*‖l‖)*(A*‖k‖)+(A*‖h‖)*(B*‖k‖*‖l‖)+
          (A*‖l‖)*(B*‖h‖*‖k‖))+
        upper*(n:ℝ)^3*(A*‖l‖)*(A*‖h‖)*(A*‖k‖) := by
      gcongr <;> first
        | exact Hcurvature_upper (show 0<n by omega) (hp i)
        | exact (Hslope_bounds hn (hp i)).2
        | exact Hthird_upper (show 0<n by omega) (hp i)
        | exact (hb i).2
        | exact huh i
        | exact huk i
        | exact hul i
        | exact huhk i
        | exact huhl i
        | exact hukl i
    _ = _ := by ring

def firstJetBound (n : ℕ) (lower : ℝ) : ℝ := 2*(n:ℝ)/lower
def secondJetBound (n : ℕ) (lower upper : ℝ) : ℝ :=
  firstJetBound n lower*(2*(n:ℝ)*firstJetBound n lower+
    upper*(n:ℝ)^2*(firstJetBound n lower)^2)
def thirdJetBound (n : ℕ) (lower upper : ℝ) : ℝ :=
  let A := firstJetBound n lower
  let B := secondJetBound n lower upper
  A*(3*(n:ℝ)^2*A^2+3*(n:ℝ)*B+3*upper*(n:ℝ)^2*A*B+upper*(n:ℝ)^3*A^3)

theorem norm_fderiv_fderiv_fderiv_kernelMarginal_le {n c : ℕ} (hn : 2 ≤ n)
    (hc : c ≤ Fintype.card ι) {lower upper : ℝ} (hlower : 0<lower)
    (b : ι → ℝ) (hb : ∀ i, lower≤b i ∧ b i≤upper)
    (hp : ∀ i, kernelMarginal n c b i∈Ioo (0:ℝ) 1) (h k l : ι → ℝ) :
    ‖fderiv ℝ (fun a => fderiv ℝ (fun d => fderiv ℝ (kernelMarginal n c) d h) a k) b l‖≤
      thirdJetBound n lower upper*‖h‖*‖k‖*‖l‖ := by
  let K := kernelMarginal (ι:=ι) n c
  let p := K b
  let u1 := fun h a => fderiv ℝ K a h
  let u2 := fun h k a => fderiv ℝ (u1 h) a k
  let A := firstJetBound n lower
  let B := secondJetBound n lower upper
  let C := 3*(n:ℝ)^2*A^2+3*(n:ℝ)*B+3*upper*(n:ℝ)^2*A*B+upper*(n:ℝ)^3*A^3
  let v := thirdReceiptForcing n b p h k l (u1 h b) (u1 k b) (u1 l b)
      (u2 h k b) (u2 h l b) (u2 k l b)
  have hb0 (i : ι) : 0<b i := hlower.trans_le (hb i).1
  have hp' (i : ι) : p i∈Icc (0:ℝ) 1 := ⟨(hp i).1.le,(hp i).2.le⟩
  have hupper : 0≤upper := (hb0 (Classical.choice inferInstance)).le.trans
    (hb (Classical.choice inferInstance)).2
  have hA : 0≤A := by dsimp [A,firstJetBound]; positivity
  have hB : 0≤B := by dsimp [B,secondJetBound]; positivity
  have hC : 0≤C := by dsimp [C]; positivity
  have hnorm : ‖fderiv ℝ K b‖≤A := norm_fderiv_kernelMarginal_le hn hc hlower b
    (fun i => (hb i).1) hp
  have hvalue (z : ι → ℝ) (i : ι) : |u1 z b i|≤A*‖z‖ := by
    have hi : |u1 z b i|≤‖u1 z b‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (u1 z b) i
    exact hi.trans (((fderiv ℝ K b).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)))
  have hvalue2 (z y : ι → ℝ) (i : ι) : |u2 z y b i|≤B*‖z‖*‖y‖ := by
    have hi : |u2 z y b i|≤‖u2 z y b‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (u2 z y b) i
    exact hi.trans (norm_fderiv_fderiv_kernelMarginal_le hn hc hlower b hb hp z y)
  have hv (i : ι) : |v i|≤C*‖h‖*‖k‖*‖l‖ :=
    thirdReceiptForcing_abs_le hn hA hB b p h k l _ _ _ _ _ _
      (fun j => ⟨hb0 j,(hb j).2⟩) hp' (hvalue h) (hvalue k) (hvalue l)
      (hvalue2 h k) (hvalue2 h l) (hvalue2 k l) i
  have havg := weighted_average_abs_le (fun i => sensitivity n (b i) (p i)) v
    (fun i => sensitivity_pos hn (hb0 i) (hp' i)) hv
  change _≤A*C*‖h‖*‖k‖*‖l‖
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs,fderiv_fderiv_fderiv_kernelMarginal_interior hn hc b hb0 hp h k l i,
    abs_mul,abs_of_pos (sensitivity_pos hn (hb0 i) (hp' i))]
  have hdiff := (abs_sub _ _).trans (add_le_add (hv i) havg)
  have hs := sensitivity_uniform_upper hn hlower (hb i).1 (hp' i)
  calc
    _ ≤ ((n:ℝ)/lower)*(C*‖h‖*‖k‖*‖l‖+C*‖h‖*‖k‖*‖l‖) :=
      mul_le_mul hs hdiff (abs_nonneg _) (by positivity)
    _ = _ := by dsimp [A,firstJetBound]; ring

def bidBox (lower upper : ℝ) : Set (ι → ℝ) := {b | ∀ i, lower≤b i ∧ b i≤upper}

omit [Fintype ι] [Nonempty ι] in
theorem bidBox_convex (lower upper : ℝ) : Convex ℝ (bidBox (ι:=ι) lower upper) := by
  have he : bidBox (ι:=ι) lower upper=Set.pi univ (fun _ : ι => Icc lower upper) := by
    ext b
    simp [bidBox,Pi.le_def,forall_and]
  rw [he]
  exact convex_pi fun _ _ => convex_Icc lower upper

theorem first_kernel_jet_lipschitz {n c : ℕ} (hn : 2≤n) (hc : c≤Fintype.card ι)
    {lower upper : ℝ} (hlower : 0<lower)
    (hinterior : ∀ b∈bidBox (ι:=ι) lower upper, ∀ i, kernelMarginal n c b i∈Ioo (0:ℝ) 1)
    (a b : ι → ℝ) (ha : a∈bidBox lower upper) (hb : b∈bidBox lower upper) (h : ι → ℝ) :
    ‖fderiv ℝ (kernelMarginal n c) b h-fderiv ℝ (kernelMarginal n c) a h‖≤
      secondJetBound n lower upper*‖h‖*‖b-a‖ := by
  let K := kernelMarginal (ι:=ι) n c
  have hupper : 0≤upper := (hlower.trans_le (ha (Classical.choice inferInstance)).1).le.trans
    (ha (Classical.choice inferInstance)).2
  have hC : 0 ≤ secondJetBound n lower upper := by
    unfold secondJetBound firstJetBound
    positivity
  apply Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ)
    (s:=bidBox lower upper) (f:=fun d => fderiv ℝ K d h) ?_ ?_
    (bidBox_convex lower upper) ha hb
  · intro d hd
    have hK := contDiffAt_kernelMarginal_interior hn hc d
      (fun i => hlower.trans_le (hd i).1) (hinterior d hd)
    exact (((hK.fderiv_right (m:=1) (WithTop.coe_le_coe.mpr le_top)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num))
  · intro d hd
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg h))
    intro k
    exact norm_fderiv_fderiv_kernelMarginal_le hn hc hlower d hd (hinterior d hd) h k

theorem second_kernel_jet_lipschitz {n c : ℕ} (hn : 2≤n) (hc : c≤Fintype.card ι)
    {lower upper : ℝ} (hlower : 0<lower)
    (hinterior : ∀ b∈bidBox (ι:=ι) lower upper, ∀ i, kernelMarginal n c b i∈Ioo (0:ℝ) 1)
    (a b : ι → ℝ) (ha : a∈bidBox lower upper) (hb : b∈bidBox lower upper) (h k : ι → ℝ) :
    ‖fderiv ℝ (fun d => fderiv ℝ (kernelMarginal n c) d h) b k-
      fderiv ℝ (fun d => fderiv ℝ (kernelMarginal n c) d h) a k‖≤
      thirdJetBound n lower upper*‖h‖*‖k‖*‖b-a‖ := by
  let K := kernelMarginal (ι:=ι) n c
  have hupper : 0≤upper := (hlower.trans_le (ha (Classical.choice inferInstance)).1).le.trans
    (ha (Classical.choice inferInstance)).2
  have hC : 0≤thirdJetBound n lower upper := by
    unfold thirdJetBound secondJetBound firstJetBound
    positivity
  apply Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ)
    (s:=bidBox lower upper) (f:=fun d => fderiv ℝ (fun e => fderiv ℝ K e h) d k) ?_ ?_
    (bidBox_convex lower upper) ha hb
  · intro d hd
    have hK := contDiffAt_kernelMarginal_interior hn hc d
      (fun i => hlower.trans_le (hd i).1) (hinterior d hd)
    have hU : ContDiffAt ℝ 2 (fun e => fderiv ℝ K e h) d :=
      (hK.fderiv_right (m:=2) (WithTop.coe_le_coe.mpr le_top)).clm_apply contDiffAt_const
    exact (((hU.fderiv_right (m:=1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num))
  · intro d hd
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro l
    exact norm_fderiv_fderiv_fderiv_kernelMarginal_le hn hc hlower d hd (hinterior d hd) h k l

end FCAppendix.Existence.NarrowPayOnce
