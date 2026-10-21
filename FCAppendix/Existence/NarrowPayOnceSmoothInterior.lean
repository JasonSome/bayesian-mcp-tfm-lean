import FCAppendix.Existence.NarrowPayOnceSmoothKernel
import FCAppendix.Existence.NarrowPayOnceUniformBand
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology
open PayOnce PayOnce.OwnImpact CommonList
open scoped BigOperators ContDiff

variable {ι : Type*} [Fintype ι]

def multiplyMap (d : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i => d i • ContinuousLinearMap.proj i

omit [Fintype ι] in
theorem multiplyMap_apply (d x : ι → ℝ) (i : ι) : multiplyMap d x i=d i*x i := rfl

def weightedMap (d : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  multiplyMap d-(meanProjection ι).comp (multiplyMap d)+meanProjection ι

theorem weightedMap_apply (d x : ι → ℝ) : weightedMap d x=
    multiplyMap d x-meanProjection ι (multiplyMap d x)+meanProjection ι x := rfl

variable [Nonempty ι]

theorem projection_weightedMap (d x : ι → ℝ) :
    meanProjection ι (weightedMap d x)=meanProjection ι x := by
  rw [weightedMap_apply,map_add,map_sub,meanProjection_idempotent,sub_self,zero_add,
    meanProjection_idempotent]

theorem weightedMap_injective (d : ι → ℝ) (hd : ∀ i, d i<0) : Function.Injective (weightedMap d) := by
  classical
  apply (injective_iff_map_eq_zero (weightedMap d)).mpr
  intro x hx
  have hPx : meanProjection ι x=0 := by
    have hh := congrArg (meanProjection ι) hx
    rwa [projection_weightedMap,map_zero] at hh
  have hDx : multiplyMap d x=meanProjection ι (multiplyMap d x) := by
    rw [weightedMap_apply,hPx,add_zero] at hx
    exact sub_eq_zero.mp hx
  let t := (∑ j, d j*x j)/(Fintype.card ι:ℝ)
  have heq (i : ι) : d i*x i=t := by
    have hh := congrFun hDx i
    simpa only [meanProjection_apply,multiplyMap_apply] using hh
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have hsum : (∑ j, x j)=0 := by
    have hh := congrFun hPx i
    rw [meanProjection_apply,Pi.zero_apply] at hh
    simpa only [zero_mul] using (div_eq_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).mp hh
  obtain ⟨j,hj⟩ := exists_coordinate_le_average x 0 (by simpa only [mul_zero] using hsum)
  obtain ⟨k,hk⟩ := exists_coordinate_ge_average x 0 (by simpa only [mul_zero] using hsum)
  have ht0 : 0 ≤ t := by rw [← heq j]; exact mul_nonneg_of_nonpos_of_nonpos (hd j).le hj
  have ht1 : t ≤ 0 := by rw [← heq k]; exact mul_nonpos_of_nonpos_of_nonneg (hd k).le hk
  have ht : t=0 := le_antisymm ht1 ht0
  ext j
  have hh := heq j
  rw [ht] at hh
  exact (mul_eq_zero.mp hh).resolve_left (hd j).ne

theorem weightedMap_isInvertible (d : ι → ℝ) (hd : ∀ i, d i<0) : (weightedMap d).IsInvertible := by
  have hinj := weightedMap_injective d hd
  have hsurj := LinearMap.surjective_of_injective (f:=(weightedMap d).toLinearMap) hinj
  let e := ContinuousLinearEquiv.ofBijective (weightedMap d)
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
  refine ⟨e,?_⟩
  apply ContinuousLinearMap.ext
  intro x
  rfl

omit [Nonempty ι] in
def receiptLinearAt (n : ℕ) (b p : ι → ℝ) :
    ((ι → ℝ) × (ι → ℝ)) →L[ℝ] (ι → ℝ) :=
  (multiplyMap (fun i => H n (p i))).comp (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))+
    (multiplyMap (fun i => -(b i*Hslope n (p i)))).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))

omit [Nonempty ι] in
theorem hasFDerivAt_receiptVectorAt (n : ℕ) (b p : ι → ℝ) :
    HasFDerivAt (receiptVector (ι:=ι) n) (receiptLinearAt n b p) (b,p) := by
  apply hasFDerivAt_pi''
  intro i
  have hb : HasFDerivAt (fun z : (ι → ℝ) × (ι → ℝ) => z.1 i)
      ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))) (b,p) :=
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp _ hasFDerivAt_fst
  have hp : HasFDerivAt (fun z : (ι → ℝ) × (ι → ℝ) => z.2 i)
      ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))) (b,p) :=
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp _ hasFDerivAt_snd
  have he : (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).comp (receiptLinearAt n b p)=
      b i • ((-Hslope n (p i)) • ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))))+
      H n (p i) • ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))) := by
    apply ContinuousLinearMap.ext
    intro z
    simp [receiptLinearAt,multiplyMap_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
    ring
  rw [he]
  have hH : HasDerivAt (H n) (-Hslope n (p i)) (p i) := PayOnce.OwnImpact.hasDerivAt_H n (p i)
  have hcomp : HasFDerivAt (fun z : (ι → ℝ) × (ι → ℝ) => H n (z.2 i))
      ((-Hslope n (p i)) • ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)))) (b,p) :=
    HasDerivAt.comp_hasFDerivAt_of_eq (𝕜:=ℝ) (𝕜':=ℝ) (b,p) hH hp rfl
  exact hb.mul hcomp

omit [Nonempty ι] in
def equationLinearAt (n : ℕ) (b p : ι → ℝ) :
    ((ι → ℝ) × (ι → ℝ)) →L[ℝ] (ι → ℝ) :=
  receiptLinearAt n b p-(meanProjection ι).comp (receiptLinearAt n b p)+
    (meanProjection ι).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))

omit [Nonempty ι] in
theorem hasFDerivAt_kernelEquationAt (n : ℕ) (rho : ℝ) (b p : ι → ℝ) :
    HasFDerivAt (kernelEquation (ι:=ι) n rho) (equationLinearAt n b p) (b,p) := by
  have hd := hasFDerivAt_receiptVectorAt (ι:=ι) n b p
  have hp := (meanProjection ι).hasFDerivAt (x:=receiptVector n (b,p))
  exact ((hd.sub (hp.comp _ hd)).add
    ((meanProjection ι).hasFDerivAt.comp _ hasFDerivAt_snd)).sub_const (fun _ => rho)

omit [Nonempty ι] in
theorem equationLinearAt_partial (n : ℕ) (b p : ι → ℝ) :
    (equationLinearAt n b p).comp (ContinuousLinearMap.inr ℝ (ι → ℝ) (ι → ℝ))=
      weightedMap (fun i => -(b i*Hslope n (p i))) := by
  apply ContinuousLinearMap.ext
  intro x
  simp [equationLinearAt,receiptLinearAt,weightedMap,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']

theorem contDiffAt_kernelMarginal_interior {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι)
    (b0 : ι → ℝ) (hb0 : ∀ i, 0<b0 i)
    (hi0 : ∀ i, kernelMarginal n c b0 i ∈ Ioo (0:ℝ) 1) :
    ContDiffAt ℝ ∞ (kernelMarginal (ι:=ι) n c) b0 := by
  let rho : ℝ := (c:ℝ)/(Fintype.card ι:ℝ)
  have hcap : (Fintype.card ι:ℝ)*rho=c := by dsimp [rho]; field_simp
  let K := kernelMarginal (ι:=ι) n c
  let p0 := K b0
  let F := kernelEquation (ι:=ι) n rho
  have hzero : F (b0,p0)=0 := kernelEquation_actual hn hc hcap b0 hb0 hi0
  have hF : ContDiffAt ℝ ∞ F (b0,p0) := (contDiff_kernelEquation n rho).contDiffAt
  have hinv : (fderiv ℝ F (b0,p0) ∘L ContinuousLinearMap.inr ℝ (ι → ℝ) (ι → ℝ)).IsInvertible := by
    rw [(hasFDerivAt_kernelEquationAt n rho b0 p0).fderiv,equationLinearAt_partial]
    exact weightedMap_isInvertible _ fun i => neg_neg_of_pos
      (mul_pos (hb0 i) (Hslope_pos hn ⟨(hi0 i).1.le,(hi0 i).2.le⟩))
  let psi := hF.implicitFunction (by simp) hinv
  have hpsi : ContDiffAt ℝ ∞ psi b0 := hF.contDiffAt_implicitFunction (by simp) hinv
  have heq : ∀ᶠ z in 𝓝 (b0,p0), F z=F (b0,p0) ↔ psi z.1=z.2 :=
    hF.eventually_apply_eq_iff_implicitFunction (by simp) hinv
  have hK : ContinuousAt K b0 :=
    (continuousOn_kernelMarginal n hn c b0 hb0).continuousAt (isOpen_positive.mem_nhds hb0)
  have hpair : Tendsto (fun b => (b,K b)) (𝓝 b0) (𝓝 (b0,p0)) := continuousAt_id.prodMk hK
  have hpositive : ∀ᶠ b in 𝓝 b0, ∀ i, 0<b i := isOpen_positive.mem_nhds hb0
  have hinterior : ∀ᶠ b in 𝓝 b0, ∀ i, K b i ∈ Ioo (0:ℝ) 1 :=
    Filter.eventually_all.mpr fun i => ((continuous_apply i).continuousAt.comp hK)
      (isOpen_Ioo.mem_nhds (hi0 i))
  apply hpsi.congr_of_eventuallyEq
  filter_upwards [hpair.eventually heq,hpositive,hinterior] with b hbe hb hi
  exact (hbe.mp (by rw [hzero]; exact kernelEquation_actual hn hc hcap b hb hi)).symm

theorem exists_uniform_smooth_kernel_radius {n : ℕ} (hn : 2 ≤ n)
    {B rhoLo rhoHi : ℝ} (hB : 0<B) (hlo : 0<rhoLo) (hhi : rhoHi<1) :
    ∃ eps : ℝ, 0<eps ∧ eps<B ∧
      ∀ (κ : Type*) [Fintype κ] [Nonempty κ] (c : ℕ) (rho : ℝ),
      rho ∈ Icc rhoLo rhoHi → c ≤ Fintype.card κ → (Fintype.card κ:ℝ)*rho=c →
      ∀ b : κ → ℝ, (∀ i, |b i-B| ≤ eps) →
      (∀ i, kernelMarginal n c b i ∈ Ioo (0:ℝ) 1) ∧
      ContDiffAt ℝ ∞ (kernelMarginal n c) b := by
  let eta := min rhoLo (1-rhoHi)
  have heta : 0<eta := lt_min hlo (sub_pos.mpr hhi)
  obtain ⟨eps,heps,hepsB,hbound⟩ := exists_uniform_kernel_radius hn hB heta
  refine ⟨eps,heps,hepsB,?_⟩
  intro κ _ _ c rho hrho hc hcap b hb
  have hri : rho ∈ Ioo (0:ℝ) 1 := ⟨hlo.trans_le hrho.1,hrho.2.trans_lt hhi⟩
  have hinside (i : κ) : kernelMarginal n c b i ∈ Ioo (0:ℝ) 1 := by
    have hh := abs_lt.mp (hbound κ c rho hri hc hcap b hb i)
    have hleft : eta ≤ rhoLo := min_le_left _ _
    have hright : eta ≤ 1-rhoHi := min_le_right _ _
    constructor <;> linarith [hrho.1,hrho.2]
  refine ⟨hinside,contDiffAt_kernelMarginal_interior hn hc b ?_ hinside⟩
  intro i
  have hh := (abs_le.mp (hb i)).1
  linarith

end FCAppendix.Existence.NarrowPayOnce
