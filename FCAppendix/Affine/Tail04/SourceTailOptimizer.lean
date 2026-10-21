import FCAppendix.Affine.Tail04.CompactMenuChoice
import FCAppendix.Affine.Tail04.SourceBulkAnalyticAdapter
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceTailOptimizer
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open OriginalValues SourceMenuIdentity

variable (P : ValueParameters) (ξ : ℝ)

def DerivativeGeometry (Λ : Set (ℝ×ℝ)) : Prop :=
  ∀lam∈Λ,
    (∀b∈Ico (1:ℝ) (Central.B ξ),0< deriv (served P ξ lam.1 lam.2) b) ∧
    (∀b∈Ioo (1:ℝ) (Central.B ξ),
      0< deriv (deriv (payment P ξ lam.1 lam.2)) b*deriv (served P ξ lam.1 lam.2) b-
        deriv (payment P ξ lam.1 lam.2) b*deriv (deriv (served P ξ lam.1 lam.2)) b) ∧
    deriv (payment P ξ lam.1 lam.2) 1< P.M*deriv (served P ξ lam.1 lam.2) 1

def ExposureRectangle (Λ : Set (ℝ×ℝ)) : Prop :=
  ∀lam∈Λ,(1-ξ)*Central.B ξ< lam.1 ∧ lam.1<1-ξ/2 ∧
    (1-ξ)*Central.B ξ< lam.2 ∧ lam.2<1-ξ/2

lemma smooth_served (lamA lamR b : ℝ) (hb : b≠0) :
    ContDiffAt ℝ 2 (served P ξ lamA lamR) b := by
  unfold served mixedProbability exposure
  fun_prop (disch := exact hb)

lemma smooth_payment (lamA lamR b : ℝ) (hb : b≠0) :
    ContDiffAt ℝ 2 (payment P ξ lamA lamR) b := by
  unfold payment served duplicates mixedProbability exposure
  fun_prop (disch := exact hb)

lemma differentiable_served_deriv (lamA lamR b : ℝ) (hb : b≠0) :
    DifferentiableAt ℝ (deriv (served P ξ lamA lamR)) b :=
  ((smooth_served P ξ lamA lamR b hb).derivWithin
    (by norm_num : (1:WithTop ℕ∞)+1≤2)).differentiableAt (by norm_num)

lemma differentiable_payment_deriv (lamA lamR b : ℝ) (hb : b≠0) :
    DifferentiableAt ℝ (deriv (payment P ξ lamA lamR)) b :=
  ((smooth_payment P ξ lamA lamR b hb).derivWithin
    (by norm_num : (1:WithTop ℕ∞)+1≤2)).differentiableAt (by norm_num)

lemma hasDerivAt_menu (lamA lamR v b : ℝ) (hb : b≠0) :
    HasDerivAt (menuUtility P ξ lamA lamR v)
      (v*deriv (served P ξ lamA lamR) b-deriv (payment P ξ lamA lamR) b) b :=
  (((smooth_served P ξ lamA lamR b hb).differentiableAt (by norm_num)).hasDerivAt.const_mul v).sub (((smooth_payment P ξ lamA lamR b hb).differentiableAt (by norm_num)).hasDerivAt)

lemma flag_endpoint (reg : Bool) : mixedProbability P ξ reg (Central.B ξ)=0 := by
  simp only [mixedProbability,sub_self,zero_div,zero_pow (by omega : (2:ℕ)≠0),mul_zero]

lemma hasDerivAt_flag_endpoint (reg : Bool) :
    HasDerivAt (mixedProbability P ξ reg) 0 (Central.B ξ) := by
  unfold mixedProbability
  convert! ((((hasDerivAt_const (Central.B ξ) (Central.B ξ)).sub
    (hasDerivAt_id (Central.B ξ))).div_const (Central.B ξ-1)).pow 2).const_mul (SourceMenuPopulation.baseFlag P reg) using 1
  simp

theorem endpoint_derivatives (hξ : 0< ξ) (lamA lamR : ℝ) :
    deriv (served P ξ lamA lamR) (Central.B ξ)=0 ∧
      deriv (payment P ξ lamA lamR) (Central.B ξ)=1 := by
  let B:=Central.B ξ
  have hB : B≠0 := by dsimp [B,Central.B];linarith
  have hq (lam : ℝ) : DifferentiableAt ℝ (exposure ξ lam) B := by
    unfold exposure
    fun_prop (disch := exact hB)
  have hS : HasDerivAt (served P ξ lamA lamR) 0 B := by
    let hA:= (hasDerivAt_flag_endpoint P ξ false).mul
      (((hasDerivAt_const B 1).sub (hq lamA).hasDerivAt).pow 2)
    let hR:= (hasDerivAt_flag_endpoint P ξ true).mul
      (((hasDerivAt_const B 1).sub (hq lamR).hasDerivAt).pow 2)
    convert! (hasDerivAt_const B 1).sub ((hA.const_mul (1-P.theta)).add (hR.const_mul P.theta)) using 1
    · funext x
      simp only [served,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply]
      ring
    · simp only [B,flag_endpoint,zero_mul,mul_zero,add_zero,sub_zero]
  have hD : HasDerivAt (duplicates P ξ lamA lamR) 0 B := by
    let hA:=(hasDerivAt_flag_endpoint P ξ false).mul ((hq lamA).hasDerivAt.pow 2)
    let hR:=(hasDerivAt_flag_endpoint P ξ true).mul ((hq lamR).hasDerivAt.pow 2)
    convert! (hA.const_mul (1-P.theta)).add (hR.const_mul P.theta) using 1
    · funext x
      simp only [duplicates,Pi.add_apply,Pi.mul_apply,Pi.pow_apply]
      ring
    · simp only [B,flag_endpoint,zero_mul,mul_zero,add_zero]
  have hSv : served P ξ lamA lamR B=1 := by
    simp only [served,B,flag_endpoint,mul_zero,zero_mul,add_zero,sub_zero]
  have hDv : duplicates P ξ lamA lamR B=0 := by
    simp only [duplicates,B,flag_endpoint,mul_zero,zero_mul,add_zero]
  have hT : HasDerivAt (payment P ξ lamA lamR) 1 B := by
    convert! (hasDerivAt_id B).mul (hS.add (hD.const_mul (1-2*ξ))) using 1
    simp only [Pi.add_apply,id_eq,hSv,hDv,mul_zero,add_zero,mul_one]
  exact ⟨hS.deriv,hT.deriv⟩

def ratio (lam : ℝ×ℝ) (b : ℝ) : ℝ :=
  deriv (payment P ξ lam.1 lam.2) b/deriv (served P ξ lam.1 lam.2) b

theorem ratio_strictMono (_hξ : 0< ξ) {Λ : Set (ℝ×ℝ)}
    (hgeom : DerivativeGeometry P ξ Λ) (lam : ℝ×ℝ) (hlam : lam∈Λ) :
    StrictMonoOn (ratio P ξ lam) (Ico (1:ℝ) (Central.B ξ)) := by
  have hg := hgeom lam hlam
  apply strictMonoOn_of_deriv_pos (convex_Ico 1 (Central.B ξ))
  · intro b hb
    exact ((differentiable_payment_deriv P ξ lam.1 lam.2 b (by linarith [hb.1])).continuousAt.div
      (differentiable_served_deriv P ξ lam.1 lam.2 b (by linarith [hb.1])).continuousAt
      (hg.1 b hb).ne').continuousWithinAt
  · intro b hb
    rw [interior_Ico] at hb
    have hs := hg.1 b ⟨hb.1.le,hb.2⟩
    have hd := ((differentiable_payment_deriv P ξ lam.1 lam.2 b (by linarith [hb.1])).hasDerivAt).div ((differentiable_served_deriv P ξ lam.1 lam.2 b (by linarith [hb.1])).hasDerivAt) hs.ne'
    change 0 < deriv (deriv (payment P ξ lam.1 lam.2) / deriv (served P ξ lam.1 lam.2)) b
    rw [hd.deriv]
    exact div_pos (hg.2.1 b hb) (sq_pos_of_pos hs)

theorem exists_stationary (hξ : 0< ξ) {Λ : Set (ℝ×ℝ)}
    (hgeom : DerivativeGeometry P ξ Λ) (lam : ℝ×ℝ) (hlam : lam∈Λ)
    (v : ℝ) (hv : P.M≤ v) :
    ∃b∈Ioo (1:ℝ) (Central.B ξ),v=ratio P ξ lam b := by
  let f := fun b=> v*deriv (served P ξ lam.1 lam.2) b-deriv (payment P ξ lam.1 lam.2) b
  have hB : 1< Central.B ξ := by unfold Central.B;linarith
  have hs:=hgeom lam hlam
  have hleft : 0< f 1 := by
    have hh:=mul_le_mul_of_nonneg_right hv (hs.1 1 ⟨le_rfl,hB⟩).le
    dsimp only [f]
    linarith [hs.2.2]
  have hend := endpoint_derivatives P ξ hξ lam.1 lam.2
  have hright : f (Central.B ξ)<0 := by dsimp only [f];rw [hend.1,hend.2];norm_num
  have hc : ContinuousOn f (Icc (1:ℝ) (Central.B ξ)) := by
    intro b hb
    exact (((differentiable_served_deriv P ξ lam.1 lam.2 b (by linarith [hb.1])).continuousAt.const_mul v).sub (differentiable_payment_deriv P ξ lam.1 lam.2 b (by linarith [hb.1])).continuousAt).continuousWithinAt
  obtain ⟨b,hb,hzero⟩ := intermediate_value_Icc' hB.le hc ⟨hright.le,hleft.le⟩
  have hlo : 1< b := by
    by_contra hn
    have he : b=1 := le_antisymm (not_lt.mp hn) hb.1
    subst b
    linarith
  have hhi : b< Central.B ξ := by
    by_contra hn
    have he : b=Central.B ξ := le_antisymm hb.2 (not_lt.mp hn)
    subst b
    linarith
  refine ⟨b,⟨hlo,hhi⟩,?_⟩
  unfold ratio
  exact (eq_div_iff (hs.1 b ⟨hlo.le,hhi⟩).ne').mpr (sub_eq_zero.mp hzero)

theorem stationary_strict_max (hξ : 0< ξ) {Λ : Set (ℝ×ℝ)}
    (hgeom : DerivativeGeometry P ξ Λ) (lam : ℝ×ℝ) (hlam : lam∈Λ)
    (v b : ℝ) (hb : b∈Ioo (1:ℝ) (Central.B ξ)) (hroot : v=ratio P ξ lam b)
    (a : ℝ) (ha : a∈Icc (1:ℝ) (Central.B ξ)) (hab : a≠b) :
    menuUtility P ξ lam.1 lam.2 v a< menuUtility P ξ lam.1 lam.2 v b := by
  have hr := ratio_strictMono P ξ hξ hgeom lam hlam
  have hs := (hgeom lam hlam).1
  have hc : ContinuousOn (menuUtility P ξ lam.1 lam.2 v) (Icc (1:ℝ) (Central.B ξ)) :=
    fun a ha=>(hasDerivAt_menu P ξ lam.1 lam.2 v a (by linarith [ha.1])).continuousAt.continuousWithinAt
  have hd (x : ℝ) (hx : x∈Ico (1:ℝ) (Central.B ξ)) :
      deriv (menuUtility P ξ lam.1 lam.2 v) x=
        deriv (served P ξ lam.1 lam.2) x*(v-ratio P ξ lam x) := by
    rw [(hasDerivAt_menu P ξ lam.1 lam.2 v x (by linarith [hx.1])).deriv]
    unfold ratio
    field_simp [(hs x hx).ne']
  have hl : StrictMonoOn (menuUtility P ξ lam.1 lam.2 v) (Icc (1:ℝ) b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 1 b)
    · exact hc.mono (Icc_subset_Icc_right hb.2.le)
    · intro x hx
      rw [interior_Icc] at hx
      have hxB : x∈Ico (1:ℝ) (Central.B ξ) := ⟨hx.1.le,hx.2.trans hb.2⟩
      rw [hd x hxB,hroot]
      exact mul_pos (hs x hxB) (sub_pos.mpr (hr hxB ⟨hb.1.le,hb.2⟩ hx.2))
  have hu : StrictAntiOn (menuUtility P ξ lam.1 lam.2 v) (Icc b (Central.B ξ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc b (Central.B ξ))
    · exact hc.mono (Icc_subset_Icc_left hb.1.le)
    · intro x hx
      rw [interior_Icc] at hx
      have hxB : x∈Ico (1:ℝ) (Central.B ξ) := ⟨hb.1.le.trans hx.1.le,hx.2⟩
      rw [hd x hxB,hroot]
      exact mul_neg_of_pos_of_neg (hs x hxB) (sub_neg.mpr (hr ⟨hb.1.le,hb.2⟩ hxB hx.1))
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact hl ⟨ha.1,hab.le⟩ ⟨hb.1.le,le_rfl⟩ hab
  · exact hu ⟨le_rfl,hb.2.le⟩ ⟨hba.le,ha.2⟩ hba

def beta (hξ : 0< ξ) (lam : ℝ×ℝ) (v : ℝ) : Icc (1:ℝ) (Central.B ξ) :=
  CompactMenuChoice.choice P ξ (Central.B ξ) (by unfold Central.B;linarith) (lam,v)

theorem beta_spec (hξ : 0< ξ) {Λ : Set (ℝ×ℝ)}
    (hgeom : DerivativeGeometry P ξ Λ) (lam : ℝ×ℝ) (hlam : lam∈Λ)
    (v : ℝ) (hv : P.M≤ v) :
    (beta P ξ hξ lam v:ℝ)∈Ioo (1:ℝ) (Central.B ξ) ∧
      v=ratio P ξ lam (beta P ξ hξ lam v) ∧
      ∀a : Icc (1:ℝ) (Central.B ξ),a≠beta P ξ hξ lam v→
        menuUtility P ξ lam.1 lam.2 v a< menuUtility P ξ lam.1 lam.2 v (beta P ξ hξ lam v) := by
  obtain ⟨b,hb,hroot⟩ := exists_stationary P ξ hξ hgeom lam hlam v hv
  have he : (beta P ξ hξ lam v:ℝ)=b := by
    by_contra hn
    have hh := stationary_strict_max P ξ hξ hgeom lam hlam v b hb hroot
      (beta P ξ hξ lam v) (beta P ξ hξ lam v).2 hn
    have hm := CompactMenuChoice.choice_max P ξ (Central.B ξ)
      (by unfold Central.B;linarith) (lam,v) ⟨b,hb.1.le,hb.2.le⟩
    change menuUtility P ξ lam.1 lam.2 v b≤
      menuUtility P ξ lam.1 lam.2 v (beta P ξ hξ lam v) at hm
    exact (not_lt_of_ge hm) hh
  refine ⟨he.symm ▸ hb,he.symm ▸ hroot,?_⟩
  intro a ha
  apply stationary_strict_max P ξ hξ hgeom lam hlam v _ (he.symm ▸ hb) (he.symm ▸ hroot) a a.2
  exact fun hh=> ha (Subtype.ext hh)

lemma measurable_beta (hξ : 0< ξ) : Measurable (fun p : (ℝ×ℝ)×ℝ=> beta P ξ hξ p.1 p.2) :=
  CompactMenuChoice.measurable_choice P ξ (Central.B ξ) (by unfold Central.B;linarith)

theorem beta_exposures (hξ : 0< ξ) (hξh : ξ<1/2) {Λ : Set (ℝ×ℝ)}
    (hgeom : DerivativeGeometry P ξ Λ) (hrect : ExposureRectangle ξ Λ)
    (lam : ℝ×ℝ) (hlam : lam∈Λ) (v : ℝ) (hv : P.M≤ v) :
    (∀z∈({lam.1,lam.2}:Set ℝ),1/2< exposure ξ z (beta P ξ hξ lam v) ∧
      exposure ξ z (beta P ξ hξ lam v)<1) := by
  have hb := (beta_spec P ξ hξ hgeom lam hlam v hv).1
  have hB : 0< Central.B ξ := by unfold Central.B;linarith
  have hκ : 0<1-ξ := by linarith
  intro z hz
  have hz0 : (1-ξ)*Central.B ξ< z ∧ z<1-ξ/2 := by
    rcases hz with rfl | hz
    · exact ⟨(hrect lam hlam).1,(hrect lam hlam).2.1⟩
    · rcases hz with rfl
      exact ⟨(hrect lam hlam).2.2.1,(hrect lam hlam).2.2.2⟩
  have hb0 : 0<(beta P ξ hξ lam v:ℝ) := by linarith [hb.1]
  have hzpos : 0< z := (mul_pos hκ hB).trans hz0.1
  have hdiv : z/(beta P ξ hξ lam v:ℝ)<1-ξ/2 := by
    apply (div_lt_iff₀ hb0).mpr
    have hc : 0<1-ξ/2 := by linarith
    nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hb.1.le)]
  have hdiv' : 1-ξ< z/(beta P ξ hξ lam v:ℝ) := by
    apply (lt_div_iff₀ hb0).mpr
    exact (mul_lt_mul_of_pos_left hb.2 hκ).trans hz0.1
  unfold exposure
  constructor
  · apply (lt_div_iff₀ hξ).mpr
    linarith
  · apply (div_lt_one hξ).mpr
    linarith

end FCAppendix.Affine.Tail04.SourceTailOptimizer
