import FCAppendix.Affine.LowBody.PhysicalWeakPayoff

noncomputable section
namespace FCAppendix.Affine.LowBody
open Set Filter Topology MeasureTheory ProbabilityTheory

def zeroUnitInterval : unitInterval := ⟨0,by norm_num⟩

def basePhysicalPoint (d ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/2)
    (x : LowValue d×unitInterval) : LowValue d×LowValue d :=
  (x.1,noisyBid d ε hε hsmall (x,zeroUnitInterval))

def noisyPhysicalPoint (d ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/2)
    (x : (LowValue d×unitInterval)×unitInterval) : LowValue d×LowValue d :=
  (x.1.1,noisyBid d ε hε hsmall x)

theorem dist_noisyPhysicalPoint_base_le {d ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/2)
    (x : (LowValue d×unitInterval)×unitInterval) :
    dist (noisyPhysicalPoint d ε hε hsmall x) (basePhysicalPoint d ε hε hsmall x.1)≤|d| * ε := by
  have hbase0 : 0≤x.1.1.1*bidRatio ε x.1.2 :=
    mul_nonneg x.1.1.property.1 (hε.le.trans (bidRatio_bounds hε hsmall x.1.2).1)
  have hbased : x.1.1.1*bidRatio ε x.1.2≤d := by
    have hh:=(noisyBid d ε hε hsmall (x.1,zeroUnitInterval)).property.2
    simpa only [noisyBid,zeroUnitInterval,mul_zero,add_zero,mul_one] using hh
  have hd : 0≤|d| * ε := mul_nonneg (abs_nonneg d) hε.le
  rw [Prod.dist_eq]
  simp only [noisyPhysicalPoint,basePhysicalPoint,dist_self]
  apply max_le hd
  change |x.1.1.1*bidRatio ε x.1.2*(1+ε*x.2.1)-x.1.1.1*bidRatio ε x.1.2*(1+ε*0)|≤|d| * ε
  have he : x.1.1.1*bidRatio ε x.1.2*(1+ε*x.2.1)-x.1.1.1*bidRatio ε x.1.2*(1+ε*0)=
      (x.1.1.1*bidRatio ε x.1.2)*ε*x.2.1 := by ring
  rw [he,abs_of_nonneg (mul_nonneg (mul_nonneg hbase0 hε.le) x.2.property.1)]
  calc
    _≤(x.1.1.1*bidRatio ε x.1.2)*ε:=mul_le_of_le_one_right (mul_nonneg hbase0 hε.le) x.2.property.2
    _≤|d| * ε:=mul_le_mul_of_nonneg_right (hbased.trans (le_abs_self d)) hε.le

theorem eventually_noisy_test_close {d : ℝ}
    (h : C(LowValue d×LowValue d,ℝ))
    (eps : ℕ→ℝ) (heps : ∀j,0<eps j) (hsmall : ∀j,eps j≤1/2)
    (ht : Tendsto eps atTop (𝓝 0)) {eta : ℝ} (heta : 0<eta) :
    ∀ᶠj in atTop,∀x : (LowValue d×unitInterval)×unitInterval,
      |h (noisyPhysicalPoint d (eps j) (heps j) (hsmall j) x)-
        h (basePhysicalPoint d (eps j) (heps j) (hsmall j) x.1)| < eta := by
  obtain ⟨r,hr,hmod⟩:=Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous h.continuous) eta heta
  have hv : Tendsto (fun j=>|d| * eps j) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul ht
  filter_upwards [hv.eventually (Iio_mem_nhds hr)] with j hj x
  simpa only [Real.dist_eq] using
    hmod ((dist_noisyPhysicalPoint_base_le (heps j) (hsmall j) x).trans_lt hj)

end FCAppendix.Affine.LowBody
