import FCAppendix.Existence.NarrowPayOnceProfileDerivative
import Mathlib.Analysis.Calculus.ParametricIntegral
import FCAppendix.PayOnce.RareSuccessSlope
import FCAppendix.Existence.R01Distributional

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open MeasureTheory ProbabilityTheory Set Filter Topology
open PayOnce PayOnce.OwnImpact CommonList
open scoped BigOperators

variable {R : ℕ} {V : Type*}

def rowBids (beta : V→ℝ) (z : ℝ) (omega : Fin R→V) : Fin (R+1)→ℝ :=
  Fin.cons z (fun j=>beta (omega j))

def finiteRowMarginal (n c : ℕ) (beta : V→ℝ) (z : ℝ) (omega : Fin R→V) : ℝ :=
  kernelMarginal n c (rowBids beta z omega) 0

def finiteRowVelocity (n c : ℕ) (beta : V→ℝ) (z : ℝ) (omega : Fin R→V) : ℝ :=
  let b:=rowBids beta z omega
  let p:=kernelMarginal n c b
  let s:=fun i=>sensitivity n (b i) (p i)
  s 0*H n (p 0)*(1-s 0/(∑i,s i))

def finiteRowUtility (n c : ℕ) (beta : V→ℝ) (w z : ℝ) (omega : Fin R→V) : ℝ :=
  (w-z)*PayOnce.success n (finiteRowMarginal n c beta z omega)

def finiteRowScore (n c : ℕ) (beta : V→ℝ) (w z : ℝ) (omega : Fin R→V) : ℝ :=
  (w-z)*(n:ℝ)*(1-finiteRowMarginal n c beta z omega)^(n-1)*
    finiteRowVelocity n c beta z omega-PayOnce.success n (finiteRowMarginal n c beta z omega)

def finiteExpectedUtility [MeasurableSpace V] (n c : ℕ) (nu : Measure V)
    (beta : V→ℝ) (w z : ℝ) : ℝ :=
  ∫omega : Fin R→V,finiteRowUtility n c beta w z omega ∂Measure.pi (fun _=>nu)

def finiteExpectedScore [MeasurableSpace V] (n c : ℕ) (nu : Measure V)
    (beta : V→ℝ) (w z : ℝ) : ℝ :=
  ∫omega : Fin R→V,finiteRowScore n c beta w z omega ∂Measure.pi (fun _=>nu)

private theorem hasDerivAt_rowBids (beta : V→ℝ) (omega : Fin R→V) (z : ℝ) :
    HasDerivAt (fun x=>rowBids beta x omega) (Fin.cons 1 (fun _=>0)) z := by
  apply hasDerivAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · exact hasDerivAt_id z
  · exact hasDerivAt_const z (beta (omega j))

theorem hasDerivAt_finiteRowMarginal {n c : ℕ} (hn : 2≤n) (hc : c≤R+1)
    (beta : V→ℝ) (z : ℝ) (omega : Fin R→V) (hz : 0<z)
    (hbeta : ∀v,0<beta v)
    (hp : ∀i,kernelMarginal n c (rowBids beta z omega) i∈Ioo (0:ℝ) 1) :
    HasDerivAt (fun x=>finiteRowMarginal n c beta x omega)
      (finiteRowVelocity n c beta z omega) z := by
  let b:=rowBids beta z omega
  let p:=kernelMarginal n c b
  let h : Fin (R+1)→ℝ:=Fin.cons 1 (fun _=>0)
  have hb : ∀i,0<b i := by
    intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact hz
    · exact hbeta (omega j)
  have hK : DifferentiableAt ℝ (kernelMarginal (ι:=Fin (R+1)) n c) b :=
    (contDiffAt_kernelMarginal_interior hn (by simpa using hc) b hb hp).differentiableAt (by simp)
  have hd := hK.hasFDerivAt.comp_hasDerivAt z (hasDerivAt_rowBids beta omega z)
  have hd0 := (ContinuousLinearMap.proj (0:Fin (R+1)) : (Fin (R+1)→ℝ)→L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt z hd
  have hprice : priceDerivative n b p h=
      sensitivity n (b 0) (p 0)*H n (p 0)/(∑i,sensitivity n (b i) (p i)) := by
    unfold priceDerivative
    rw [Fin.sum_univ_succ]
    simp [h]
  have he := fderiv_kernelMarginal_interior hn (by simpa using hc) b hb hp h 0
  rw [hprice] at he
  have he' : fderiv ℝ (kernelMarginal (ι:=Fin (R+1)) n c) b h 0=
      finiteRowVelocity n c beta z omega := by
    rw [he]
    dsimp [finiteRowVelocity,b,p,h]
    simp only [Fin.cons_zero]
    ring
  change HasDerivAt (fun x=>finiteRowMarginal n c beta x omega)
    (fderiv ℝ (kernelMarginal (ι:=Fin (R+1)) n c) b h 0) z at hd0
  rwa [he'] at hd0

theorem hasDerivAt_finiteRowUtility {n c : ℕ} (hn : 2≤n) (hc : c≤R+1)
    (beta : V→ℝ) (w z : ℝ) (omega : Fin R→V) (hz : 0<z)
    (hbeta : ∀v,0<beta v)
    (hp : ∀i,kernelMarginal n c (rowBids beta z omega) i∈Ioo (0:ℝ) 1) :
    HasDerivAt (fun x=>finiteRowUtility n c beta w x omega)
      (finiteRowScore n c beta w z omega) z := by
  have hq:=hasDerivAt_finiteRowMarginal hn hc beta z omega hz hbeta hp
  have hs := (hasDerivAt_const z (1:ℝ)).sub
    (((hasDerivAt_const z (1:ℝ)).sub hq).pow n)
  have hu := ((hasDerivAt_const z w).sub (hasDerivAt_id z)).mul hs
  convert hu using 1 <;> first | rfl | (dsimp [finiteRowUtility,finiteRowScore,PayOnce.success]; ring)

section Continuity
variable [TopologicalSpace V]

theorem continuous_rowBids_joint (beta : V→ℝ) (hbeta : Continuous beta) :
    Continuous (fun t : ℝ×(Fin R→V)=>rowBids beta t.1 t.2) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · exact continuous_fst
  · exact hbeta.comp ((continuous_apply j).comp continuous_snd)

theorem continuousAt_rowKernel_joint {n c : ℕ} (hn : 2≤n)
    (beta : V→ℝ) (hbeta : Continuous beta) (hpos : ∀v,0<beta v)
    (t : ℝ×(Fin R→V)) (ht : 0<t.1) :
    ContinuousAt (fun x : ℝ×(Fin R→V)=>kernelMarginal n c (rowBids beta x.1 x.2)) t := by
  have hb : ∀i,0<rowBids beta t.1 t.2 i := by
    intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact ht
    · exact hpos (t.2 j)
  have hk : ContinuousAt (kernelMarginal (ι:=Fin (R+1)) n c) (rowBids beta t.1 t.2) :=
    continuousAt_kernelMarginal n hn c _ hb
  have hr : ContinuousAt (fun x : ℝ×(Fin R→V)=>rowBids beta x.1 x.2) t :=
    (continuous_rowBids_joint (R:=R) beta hbeta).continuousAt
  exact hk.comp (f:=fun x : ℝ×(Fin R→V)=>rowBids beta x.1 x.2) (x:=t) hr

theorem continuousAt_finiteRowVelocity_joint {n c : ℕ} (hn : 2≤n)
    (beta : V→ℝ) (hbeta : Continuous beta) (hpos : ∀v,0<beta v)
    (t : ℝ×(Fin R→V)) (ht : 0<t.1) :
    ContinuousAt (fun x : ℝ×(Fin R→V)=>finiteRowVelocity n c beta x.1 x.2) t := by
  let b:=fun x : ℝ×(Fin R→V)=>rowBids beta x.1 x.2
  let p:=fun x : ℝ×(Fin R→V)=>kernelMarginal n c (b x)
  let s:=fun x i=>sensitivity n (b x i) (p x i)
  have hb : ∀i,0<b t i := by
    intro i; refine Fin.cases ?_ (fun j=>?_) i
    · exact ht
    · exact hpos (t.2 j)
  have hspec:=kernelMarginal_spec n hn c (b t) hb
  have hbc:=continuous_rowBids_joint (R:=R) beta hbeta
  have hpc:=continuousAt_rowKernel_joint (c:=c) hn beta hbeta hpos t ht
  have hs : ∀i,ContinuousAt (fun x=>s x i) t := by
    intro i
    have hbi : ContinuousAt (fun x=>b x i) t :=
      ((continuous_apply i).comp hbc).continuousAt
    have hpi : ContinuousAt (fun x=>p x i) t :=
      (continuous_apply i).continuousAt.comp (f:=p) (x:=t) hpc
    exact continuousAt_const.div
      (hbi.mul ((PayOnce.RareSuccessSlope.continuous_Hslope n).continuousAt.comp hpi))
      (mul_pos (hb i) (Hslope_pos hn ⟨hspec.1 i,hspec.2.1 i⟩)).ne'
  have hsum : ContinuousAt (fun x=>∑i,s x i) t :=
    tendsto_finsetSum Finset.univ (fun i _=>hs i)
  have hsumpos : 0<∑i,s t i := Finset.sum_pos
    (fun i _=>sensitivity_pos hn (hb i) ⟨hspec.1 i,hspec.2.1 i⟩) Finset.univ_nonempty
  exact ((hs 0).mul ((continuous_H n).continuousAt.comp
    ((continuous_apply 0).continuousAt.comp hpc))).mul
    (continuousAt_const.sub ((hs 0).div hsum hsumpos.ne'))

theorem continuousAt_finiteRowScore_joint {n c : ℕ} (hn : 2≤n)
    (beta : V→ℝ) (hbeta : Continuous beta) (hpos : ∀v,0<beta v) (w : ℝ)
    (t : ℝ×(Fin R→V)) (ht : 0<t.1) :
    ContinuousAt (fun x : ℝ×(Fin R→V)=>finiteRowScore n c beta w x.1 x.2) t := by
  have hp := (continuous_apply 0).continuousAt.comp
    (continuousAt_rowKernel_joint (c:=c) hn beta hbeta hpos t ht)
  exact (((((continuousAt_const.sub continuous_fst.continuousAt).mul continuousAt_const).mul
    ((continuousAt_const.sub hp).pow (n-1))).mul
    (continuousAt_finiteRowVelocity_joint (c:=c) hn beta hbeta hpos t ht))).sub
    ((PayOnce.continuous_success n).continuousAt.comp hp)

theorem continuousAt_finiteRowUtility_joint {n c : ℕ} (hn : 2≤n)
    (beta : V→ℝ) (hbeta : Continuous beta) (hpos : ∀v,0<beta v) (w : ℝ)
    (t : ℝ×(Fin R→V)) (ht : 0<t.1) :
    ContinuousAt (fun x : ℝ×(Fin R→V)=>finiteRowUtility n c beta w x.1 x.2) t :=
  (continuousAt_const.sub continuous_fst.continuousAt).mul
    ((PayOnce.continuous_success n).continuousAt.comp
      ((continuous_apply 0).continuousAt.comp (continuousAt_rowKernel_joint (c:=c) hn beta hbeta hpos t ht)))

theorem continuous_finiteRowScore {n c : ℕ} (hn : 2≤n)
    (beta : V→ℝ) (hbeta : Continuous beta) (hpos : ∀v,0<beta v)
    (w z : ℝ) (hz : 0<z) : Continuous (finiteRowScore (R:=R) n c beta w z) := by
  rw [continuous_iff_continuousAt]
  intro omega
  exact (continuousAt_finiteRowScore_joint hn beta hbeta hpos w (z,omega) hz).comp
    (f:=fun omega : Fin R→V=>(z,omega)) (x:=omega)
    (continuous_const.prodMk continuous_id).continuousAt

theorem continuous_finiteRowUtility {n c : ℕ} (hn : 2≤n)
    (beta : V→ℝ) (hbeta : Continuous beta) (hpos : ∀v,0<beta v)
    (w z : ℝ) (hz : 0<z) : Continuous (finiteRowUtility (R:=R) n c beta w z) := by
  rw [continuous_iff_continuousAt]
  intro omega
  exact (continuousAt_finiteRowUtility_joint hn beta hbeta hpos w (z,omega) hz).comp
    (f:=fun omega : Fin R→V=>(z,omega)) (x:=omega)
    (continuous_const.prodMk continuous_id).continuousAt

end Continuity

section Expected
variable [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace.MetrizableSpace V] [CompactSpace V]

theorem continuous_finiteExpectedScore_positive {n c : ℕ} (hn : 2≤n)
    (nu : Measure V) [IsProbabilityMeasure nu]
    (beta : V→ℝ) (hbeta : Continuous beta) (hpos : ∀v,0<beta v) (w : ℝ) :
    Continuous (fun z : Ioi (0:ℝ)=>finiteExpectedScore (R:=R) n c nu beta w z.1) := by
  let P : ProbabilityMeasure (Fin R→V):=⟨Measure.pi (fun _=>nu),inferInstance⟩
  let f : Ioi (0:ℝ)×(Fin R→V)→ℝ:=fun t=>finiteRowScore n c beta w t.1.1 t.2
  have hf : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro t
    have hh : ContinuousAt (fun x : ℝ×(Fin R→V)=>finiteRowScore n c beta w x.1 x.2) (t.1.1,t.2) :=
      continuousAt_finiteRowScore_joint hn beta hbeta hpos w (t.1.1,t.2) t.1.2
    have hr : ContinuousAt (fun x : Ioi (0:ℝ)×(Fin R→V)=>(x.1.1,x.2)) t :=
      (continuous_fst.subtype_val.prodMk continuous_snd).continuousAt
    exact hh.comp (f:=fun x : Ioi (0:ℝ)×(Fin R→V)=>(x.1.1,x.2)) (x:=t) hr
  exact (Distributional.continuous_law_integral f hf).comp
    (continuous_id.prodMk (continuous_const (y:=P)))

theorem hasDerivAt_finiteExpectedUtility {n c : ℕ} (hn : 2≤n) (hc : c≤R+1)
    (nu : Measure V) [IsProbabilityMeasure nu]
    (beta : V→ℝ) (hbeta : Continuous beta) (hpos : ∀v,0<beta v)
    (w lo hi z : ℝ) (hlo : 0<lo) (hz : z∈Ioo lo hi)
    (hp : ∀x∈Ioo lo hi,∀omega : Fin R→V,
      ∀i,kernelMarginal n c (rowBids beta x omega) i∈Ioo (0:ℝ) 1) :
    HasDerivAt (finiteExpectedUtility (R:=R) n c nu beta w)
      (finiteExpectedScore (R:=R) n c nu beta w z) z := by
  let score : ℝ×(Fin R→V)→ℝ:=fun t=>finiteRowScore n c beta w t.1 t.2
  have hscore : ContinuousOn score (Icc lo hi ×ˢ Set.univ) := by
    intro t ht
    exact (continuousAt_finiteRowScore_joint hn beta hbeta hpos w t
      (lt_of_lt_of_le hlo ht.1.1)).continuousWithinAt
  obtain ⟨B,hB⟩ := (isCompact_Icc.prod (isCompact_univ : IsCompact (Set.univ : Set (Fin R→V)))).bddAbove_image hscore.abs
  have hu (x : ℝ) (hx : 0<x) :=
    continuous_finiteRowUtility (R:=R) (c:=c) hn beta hbeta hpos w x hx
  have hs (x : ℝ) (hx : 0<x) :=
    continuous_finiteRowScore (R:=R) (c:=c) hn beta hbeta hpos w x hx
  have hzpos : 0<z := hlo.trans hz.1
  have hint : Integrable (finiteRowUtility n c beta w z) (Measure.pi (fun _ : Fin R=>nu)) :=
    (ContinuousMap.equivBoundedOfCompact _ _ ⟨_,hu z hzpos⟩).integrable _
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=Measure.pi (fun _ : Fin R=>nu))
    (F:=fun x omega=>finiteRowUtility n c beta w x omega)
    (F':=fun x omega=>finiteRowScore n c beta w x omega)
    (s:=Ioo lo hi) (bound:=fun _ : Fin R→V=>B)
    (Ioo_mem_nhds hz.1 hz.2)
    (by
      filter_upwards [Ioi_mem_nhds hzpos] with x hx
      exact (hu x hx).measurable.aestronglyMeasurable)
    hint (hs z hzpos).measurable.aestronglyMeasurable
    (by
      filter_upwards [] with omega x hx
      simpa only [Real.norm_eq_abs] using
        hB ⟨(x,omega),⟨⟨hx.1.le,hx.2.le⟩,Set.mem_univ _⟩,rfl⟩)
    (integrable_const B)
    (by
      filter_upwards [] with omega x hx
      exact hasDerivAt_finiteRowUtility hn hc beta w x omega
        (hlo.trans hx.1) hpos (hp x hx omega))
  exact hderiv.2

end Expected
end FCAppendix.Existence.NarrowPayOnce
