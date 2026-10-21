import FCAppendix.Existence.NarrowPayOnceProjection
import FCAppendix.Existence.Potential
import FCAppendix.PayOnce.OwnImpact

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology
open PayOnce PayOnce.OwnImpact CommonList
open scoped BigOperators ContDiff

variable {ι : Type*} [Fintype ι]

def receiptVector (n : ℕ) (z : (ι → ℝ) × (ι → ℝ)) : ι → ℝ :=
  fun i => z.1 i*H n (z.2 i)

def kernelEquation (n : ℕ) (rho : ℝ) (z : (ι → ℝ) × (ι → ℝ)) : ι → ℝ :=
  receiptVector n z-meanProjection ι (receiptVector n z)+meanProjection ι z.2-(fun _ => rho)

theorem contDiff_receiptVector (n : ℕ) : ContDiff ℝ ∞ (receiptVector (ι:=ι) n) := by
  unfold receiptVector H
  fun_prop

theorem contDiff_kernelEquation (n : ℕ) (rho : ℝ) : ContDiff ℝ ∞ (kernelEquation (ι:=ι) n rho) := by
  have hp : ContDiff ℝ ∞ (meanProjection ι) := (meanProjection ι).contDiff
  unfold kernelEquation
  exact (((contDiff_receiptVector n).sub (hp.comp (contDiff_receiptVector n))).add
    (hp.comp contDiff_snd)).sub contDiff_const

def receiptLinear (n : ℕ) (B rho : ℝ) :
    ((ι → ℝ) × (ι → ℝ)) →L[ℝ] (ι → ℝ) :=
  H n rho • ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)+
    (-(B*Hslope n rho)) • ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)

theorem hasFDerivAt_receiptVector (n : ℕ) (B rho : ℝ) :
    HasFDerivAt (receiptVector (ι:=ι) n) (receiptLinear n B rho) ((fun _ => B),(fun _ => rho)) := by
  apply hasFDerivAt_pi''
  intro i
  have hb : HasFDerivAt (fun z : (ι → ℝ) × (ι → ℝ) => z.1 i)
      ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))) ((fun _ => B),(fun _ => rho)) :=
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp _ hasFDerivAt_fst
  have hp : HasFDerivAt (fun z : (ι → ℝ) × (ι → ℝ) => z.2 i)
      ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))) ((fun _ => B),(fun _ => rho)) :=
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp _ hasFDerivAt_snd
  have he : (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).comp (receiptLinear n B rho)=
      B • ((-Hslope n rho) • ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))))+
      H n rho • ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))) := by
    apply ContinuousLinearMap.ext
    intro z
    simp [receiptLinear,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
    ring
  rw [he]
  have hH : HasDerivAt (H n) (-Hslope n rho) rho := PayOnce.OwnImpact.hasDerivAt_H n rho
  have hcomp : HasFDerivAt (fun z : (ι → ℝ) × (ι → ℝ) => H n (z.2 i))
      ((-Hslope n rho) • ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)))) ((fun _ => B),(fun _ => rho)) :=
    HasDerivAt.comp_hasFDerivAt_of_eq (𝕜:=ℝ) (𝕜':=ℝ)
      ((fun _ : ι => B),(fun _ => rho)) hH hp rfl
  exact hb.mul hcomp

def equationLinear (n : ℕ) (B rho : ℝ) :
    ((ι → ℝ) × (ι → ℝ)) →L[ℝ] (ι → ℝ) :=
  receiptLinear n B rho-(meanProjection ι).comp (receiptLinear n B rho)+
    (meanProjection ι).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))

theorem hasFDerivAt_kernelEquation (n : ℕ) (B rho : ℝ) :
    HasFDerivAt (kernelEquation (ι:=ι) n rho) (equationLinear n B rho)
      ((fun _ => B),(fun _ => rho)) := by
  have hd := hasFDerivAt_receiptVector (ι:=ι) n B rho
  have hp := (meanProjection ι).hasFDerivAt (x:=receiptVector n ((fun _ : ι => B),(fun _ => rho)))
  exact ((hd.sub (hp.comp _ hd)).add
    ((meanProjection ι).hasFDerivAt.comp _ hasFDerivAt_snd)).sub_const (fun _ => rho)

theorem equationLinear_partial (n : ℕ) (B rho : ℝ) :
    (equationLinear (ι:=ι) n B rho).comp (ContinuousLinearMap.inr ℝ (ι → ℝ) (ι → ℝ))=
      splitMap (meanProjection ι) (-(B*Hslope n rho)) 1 := by
  ext z i
  simp [equationLinear,receiptLinear,splitMap_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
  ring

variable [Nonempty ι]

theorem kernelEquation_partial_invertible {n : ℕ} (hn : 2 ≤ n) {B rho : ℝ}
    (hB : 0<B) (hrho : rho ∈ Ioo (0:ℝ) 1) :
    (fderiv ℝ (kernelEquation (ι:=ι) n rho) ((fun _ => B),(fun _ => rho)) ∘L
      ContinuousLinearMap.inr ℝ (ι → ℝ) (ι → ℝ)).IsInvertible := by
  rw [(hasFDerivAt_kernelEquation n B rho).fderiv,equationLinear_partial]
  exact splitMap_isInvertible (meanProjection ι) meanProjection_idempotent
    (neg_ne_zero.mpr (mul_pos hB (Hslope_pos hn ⟨hrho.1.le,hrho.2.le⟩)).ne') one_ne_zero

theorem meanProjection_const (a : ℝ) : meanProjection ι (fun _ => a)=(fun _ => a) := by
  ext i
  rw [meanProjection_apply]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact mul_div_cancel_left₀ a (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

omit [Nonempty ι] in
theorem kernelMarginal_constant {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι)
    {B rho : ℝ} (hB : 0<B) (hrho : rho ∈ Ioo (0:ℝ) 1)
    (hcap : (Fintype.card ι:ℝ)*rho=c) :
    kernelMarginal (ι:=ι) n c (fun _ => B)=(fun _ => rho) := by
  symm
  apply eq_kernelMarginal n hn c _ (fun _ => hB)
  refine ⟨fun _ => hrho.1.le,fun _ => hrho.2.le,?_,B*H n rho,?_,?_,?_,?_⟩
  · simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.min_eq_left hc] using hcap
  · exact (mul_pos hB (H_pos n (by omega) _ hrho.1.le hrho.2.le)).le
  · intro _ _; exact le_rfl
  · intro _ _; exact le_rfl
  · intro _ _ _; rfl

theorem kernelEquation_constant (n : ℕ) (B rho : ℝ) :
    kernelEquation (ι:=ι) n rho ((fun _ => B),(fun _ => rho))=0 := by
  change ((fun _ : ι => B*H n rho)-meanProjection ι (fun _ => B*H n rho)+
    meanProjection ι (fun _ => rho)-(fun _ => rho))=0
  rw [meanProjection_const,meanProjection_const,sub_self,zero_add,sub_self]

theorem kernelEquation_actual {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι)
    {rho : ℝ} (hcap : (Fintype.card ι:ℝ)*rho=c) (b : ι → ℝ) (hb : ∀ i, 0<b i)
    (hi : ∀ i, kernelMarginal n c b i ∈ Ioo (0:ℝ) 1) :
    kernelEquation n rho (b,kernelMarginal n c b)=0 := by
  obtain ⟨_h0,_h1,hsum,L,_hL,ht⟩ := kernelMarginal_spec n hn c b hb
  have hr : receiptVector n (b,kernelMarginal n c b)=(fun _ => L) := by
    funext i
    exact ht.2.2 i (hi i).1 (hi i).2
  have hp : meanProjection ι (kernelMarginal n c b)=(fun _ => rho) := by
    ext i
    rw [meanProjection_apply,hsum,Nat.min_eq_left hc]
    apply (div_eq_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).mpr
    exact hcap.symm.trans (mul_comm _ _)
  unfold kernelEquation
  rw [hr,meanProjection_const,sub_self,zero_add,hp,sub_self]

theorem contDiffAt_kernelMarginal_constant {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι)
    {B rho : ℝ} (hB : 0<B) (hrho : rho ∈ Ioo (0:ℝ) 1)
    (hcap : (Fintype.card ι:ℝ)*rho=c) :
    ContDiffAt ℝ ∞ (kernelMarginal (ι:=ι) n c) (fun _ => B) := by
  let b0 : ι → ℝ := fun _ => B
  let p0 : ι → ℝ := fun _ => rho
  let K := kernelMarginal (ι:=ι) n c
  let F := kernelEquation (ι:=ι) n rho
  have hzero : F (b0,p0)=0 := kernelEquation_constant n B rho
  have hbase : K b0=p0 := kernelMarginal_constant hn hc hB hrho hcap
  have hF : ContDiffAt ℝ ∞ F (b0,p0) := (contDiff_kernelEquation n rho).contDiffAt
  have hinv : (fderiv ℝ F (b0,p0) ∘L ContinuousLinearMap.inr ℝ (ι → ℝ) (ι → ℝ)).IsInvertible :=
    kernelEquation_partial_invertible hn hB hrho
  let psi := hF.implicitFunction (by simp) hinv
  have hpsi : ContDiffAt ℝ ∞ psi b0 := hF.contDiffAt_implicitFunction (by simp) hinv
  have heq : ∀ᶠ z in 𝓝 (b0,p0), F z=F (b0,p0) ↔ psi z.1=z.2 :=
    hF.eventually_apply_eq_iff_implicitFunction (by simp) hinv
  have hK : ContinuousAt K b0 :=
    (continuousOn_kernelMarginal n hn c b0 (fun _ => hB)).continuousAt
      (isOpen_positive.mem_nhds (fun _ => hB))
  have hpair : Tendsto (fun b => (b,K b)) (𝓝 b0) (𝓝 (b0,p0)) := by
    rw [← hbase]
    exact continuousAt_id.prodMk hK
  have hpositive : ∀ᶠ b in 𝓝 b0, ∀ i, 0<b i :=
    isOpen_positive.mem_nhds (fun _ => hB)
  have hinterior : ∀ᶠ b in 𝓝 b0, ∀ i, K b i ∈ Ioo (0:ℝ) 1 := by
    apply Filter.eventually_all.mpr
    intro i
    have hi : ContinuousAt (fun b => K b i) b0 := (continuous_apply i).continuousAt.comp hK
    have hival : K b0 i=rho := congrFun hbase i
    apply hi
    change Ioo 0 1 ∈ 𝓝 (K b0 i)
    rw [hival]
    exact isOpen_Ioo.mem_nhds hrho
  apply hpsi.congr_of_eventuallyEq
  filter_upwards [hpair.eventually heq,hpositive,hinterior] with b hbe hb hi
  exact (hbe.mp (by rw [hzero]; exact kernelEquation_actual hn hc hcap b hb hi)).symm

end FCAppendix.Existence.NarrowPayOnce
