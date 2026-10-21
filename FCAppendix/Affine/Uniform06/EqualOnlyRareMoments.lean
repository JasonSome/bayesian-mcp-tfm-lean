import FCAppendix.Affine.Uniform06.LiteralGuardVelocity
import FCAppendix.Affine.Uniform06.StrictLaplaceLLT
import FCAppendix.Affine.Uniform06.PhysicalSourceMoments

noncomputable section
namespace FCAppendix.Affine.Uniform06.EqualOnlyRareMoments

open Set MeasureTheory Filter LowBody
open scoped Topology BigOperators
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource RawMarkedLaplace
open LiteralCoarsePath LiteralKernelIdentity RawMomentPartition RawDeficitGeometry
open LiteralGuardVelocity LiteralDerivativeMoments GlobalDerivativeReplacement
open FixedPriceCanonicalRows FixedPriceRawDerivative PhysicalSourceMoments
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open FiniteMarkedExchangeability MixedIntervalLLT DeficitOrientation StrictLaplaceLLT

variable {N : ℕ} [Nonempty (Fin N)]

def emptyMoment (i : Row) (c : ℕ) (b θ : ℝ) (q : ℕ)
    (ω : Fin N → RowRival) : ℝ :=
  if imbalanceSum ω=0 then Real.exp (-θ*deficit i b c ω)*strictPower q (deficit i b c ω) else 0

omit [Nonempty (Fin N)] in
lemma emptyMoment_eq_laplace (i : Row) (c : ℕ) (b θ : ℝ) (q : ℕ)
    (ω : Fin N → RowRival) :
    emptyMoment i c b θ q ω=FiniteMarkedExchangeability.laplace (demand (xi i) b) integerSign c θ 0 q ω := by
  simp only [emptyMoment,FiniteMarkedExchangeability.laplace,strictPower,deficit,FCAppendix.ExponentialTilt.iidSum,
    sumX,show sumY integerSign ω=imbalanceSum ω from rfl]
  split_ifs <;> simp_all

omit [Nonempty (Fin N)] in
theorem measurable_emptyMoment (i : Row) (c : ℕ) (b θ : ℝ) (q : ℕ) :
    Measurable (emptyMoment (N:=N) i c b θ q) := by
  have hD : Measurable (deficit (N:=N) i b c) := by
    unfold deficit FCAppendix.ExponentialTilt.iidSum
    apply measurable_const.sub
    exact Finset.measurable_sum _ (fun j _ =>
      (measurable_demand (xi i) b).comp (measurable_pi_apply j))
  unfold emptyMoment
  exact Measurable.ite (measurableSet_eq_fun measurable_imbalanceSum measurable_const)
    (((hD.const_mul (-θ)).exp).mul ((measurable_strictPower q).comp hD)) measurable_const

omit [Nonempty (Fin N)] in
theorem emptyMoment_polynomial (i : Row) (c : ℕ) {b θ : ℝ}
    (hb : 0< b) (hθ : 0≤θ) (hc : (c:ℝ)≤ N) (q : ℕ) (ω : Fin N → RowRival) :
    emptyMoment i c b θ q ω∈Icc (0:ℝ) ((N:ℝ)^q) := by
  have hD : deficit i b c ω≤(N:ℝ) := by
    have hx : 0≤ sumX (demand (xi i) b) ω :=
      Finset.sum_nonneg (fun j _ => (demand_bounds (xi_pos i) hb (ω j)).1)
    change (c:ℝ)-sumX (demand (xi i) b) ω≤(N:ℝ)
    linarith
  unfold emptyMoment strictPower
  split_ifs with hy hp
  · have he : Real.exp (-θ*deficit i b c ω)≤1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hθ hp.le])
    refine ⟨mul_nonneg (Real.exp_pos _).le (pow_nonneg hp.le q),?_⟩
    exact (mul_le_mul_of_nonneg_right he (pow_nonneg hp.le q)).trans
      (by simpa only [one_mul] using pow_le_pow_left₀ hp.le hD q)
  · simp only [mul_zero]
    exact ⟨le_rfl,by positivity⟩
  · exact ⟨le_rfl,by positivity⟩

omit [Nonempty (Fin N)] in

theorem unequal_literal_zero (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b : ℝ} (hb : 0< b) (hbL : b≤ g.multiplier)
    (hlo : 0< g.multiplier-g.radius) (hbl : b≤ g.multiplier-g.radius)
    (hε : 0< g.margin) (hM : 0< g.population) (hr : 0< g.requiredDemand)
    (θ : ℝ) (q : ℕ) (ω : Fin N → RowRival)
    (hne : (patternTemplate c (fun j => (ω j).1)).residual₀≠
      (patternTemplate c (fun j => (ω j).1)).residual₁) :
    literalMoment i c g cm b θ q ω=0 := by
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  let g' := {g with countMargin:=cm (fun j => (ω j).1)}
  let P := pathLaw (weights (xi i) g' T B) (imbalance T) ∅
  have hξ1 : xi i<1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  by_cases hα : guardAlpha (xi i) g' T B=0
  · change Real.exp (-θ*deficit i b c ω)*branchWeight (xi i) g' T B*P.expect _=0
    rw [branchWeight,if_neg (show T.residual₀≠T.residual₁ from hne),hα,mul_zero,zero_mul]
  have hαp : 0< guardAlpha (xi i) g' T B :=
    lt_of_le_of_ne (guardAlpha_bounds (xi i) g' T B).1 (Ne.symm hα)
  have ha : 0< branchWeight (xi i) g' T B := by
    simpa only [branchWeight,if_neg (show T.residual₀≠T.residual₁ from hne)] using hαp
  have hpoint : P.expect (fun p => strictPower q
      (focalDeficit (xi i) T B (finalSet (imbalance T) ∅ p) 0))=0 := by
    apply expect_zero_of_support
    intro p hp
    let E := finalSet (imbalance T) ∅ p
    let B' := maskedBids T B E
    have he := branch_path_geometry g' T B 0 hε hM hr
      (by simpa only [B,rowBids,Fin.cons_zero] using hbL) ha p hp
    have hB0 : B' 0=b := by
      have hm : (0 : Fin (N+1)) ∈ T.support := focal_mem c ω
      have hn : (0 : Fin (N+1)) ∉ E := he.2
      simp only [B',maskedBids,if_pos (Finset.mem_sdiff.mpr ⟨hm,hn⟩)]
      rfl
    have hp0 := SourceGuardGeometry.complement_rejects_below_lower_guard (xi_pos i) hξ1
      g' T B hε hM hlo (rowBids_outside c b ω) hαp E he.1.le 0
      (by simpa only [B,rowBids,Fin.cons_zero] using hbl)
    have heq := actual_positive_iff_deficit (xi_pos i) hξ1 (small T) B' 0
      (by simpa only [hB0] using hb)
    have hD : ¬0< focalDeficit (xi i) T B E 0 := by
      intro hpos
      have hp' : 0< EqualCapacity.positiveMarginal (xi i) (small T) B' 0 := heq.mpr (by
        rw [hB0,masked_demand_eq T B E 0 hb (rowBids_outside c b ω)]
        exact hpos)
      change 0< complementMarginal (xi i) T B E 0 at hp'
      rw [hp0] at hp'
      exact lt_irrefl 0 hp'
    change strictPower q (focalDeficit (xi i) T B E 0)=0
    simp only [strictPower,if_neg hD]
  change Real.exp (-θ*deficit i b c ω)*branchWeight (xi i) g' T B*P.expect _=0
  rw [hpoint,mul_zero]

theorem literal_eq_empty_on_valid_counts (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b : ℝ} (hb : 0< b) (hbL : b≤ g.multiplier)
    (hlo : 0< g.multiplier-g.radius) (hbl : b≤ g.multiplier-g.radius)
    (hε : 0< g.margin) (hM : 0< g.population) (hr : 0< g.requiredDemand)
    (θ : ℝ) (q : ℕ) (ω : Fin N → RowRival) (hc : RawPathAdapter.ValidCounts c ω) :
    literalMoment i c g cm b θ q ω=emptyMoment i c b θ q ω := by
  by_cases hy : imbalanceSum ω=0
  · rw [literalMoment_eq_reducedMoment i c g cm hb hbL θ q hε hM hr ω hc,
      reducedMoment,if_pos hy,emptyMoment,if_pos hy]
    simp only [FiniteSampledLaplace.sampledRow,pathLaw,
      FCAppendix.FiniteLaw.expect_dirac,FiniteSampledLaplace.tupleTest,
      show sumY integerSign ω=imbalanceSum ω from rfl,hy,
      Fin.sum_univ_zero,sub_zero,true_and,strictPower,deficit,
      FCAppendix.ExponentialTilt.iidSum,sumX]
    split_ifs <;> simp_all
  · have hn := mt (imbalance_zero_iff_equal c ω hc).mpr hy
    rw [unequal_literal_zero i c g cm hb hbL hlo hbl hε hM hr θ q ω hn,
      emptyMoment,if_neg hy]

omit [Nonempty (Fin N)] in

theorem low_literal_polynomial (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b θ : ℝ} (hb : 0< b) (hbL : b≤ g.multiplier)
    (hlo : 0< g.multiplier-g.radius) (hbl : b≤ g.multiplier-g.radius)
    (hε : 0< g.margin) (hM : 0< g.population) (hr : 0< g.requiredDemand)
    (hθ : 0≤θ) (hc : (c:ℝ)≤ N) (q : ℕ) (ω : Fin N → RowRival) :
    literalMoment i c g cm b θ q ω∈Icc (0:ℝ) ((N:ℝ)^q) := by
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  let D := focalDeficit (xi i) T B ∅ 0
  by_cases he : T.residual₀=T.residual₁
  · have hk : imbalance T=0 := by simp [imbalance,small,he]
    have hid : literalMoment i c g cm b θ q ω=
        Real.exp (-θ*deficit i b c ω)*strictPower q D := by
      change Real.exp (-θ*deficit i b c ω)*branchWeight (xi i)
        {g with countMargin:=cm (fun j => (ω j).1)} T B*
        (pathLaw (weights (xi i) {g with countMargin:=cm (fun j => (ω j).1)} T B)
          (imbalance T) ∅).expect
          (fun p => strictPower q (focalDeficit (xi i) T B (finalSet (imbalance T) ∅ p) 0))=_
      simp only [branchWeight,if_pos he,mul_one]
      rw [hk]
      simp only [pathLaw,finalSet,FCAppendix.FiniteLaw.expect_dirac]
      rfl
    rw [hid]
    by_cases hD : 0< D
    · have hsmall : 0< small T := by
        have hdem : 0≤ remainingDemand (xi i) B {0} b := by
          unfold remainingDemand
          apply Finset.sum_nonneg
          intro j _
          split_ifs
          · rfl
          · exact exposure_nonneg (xi_pos i) hb
        have hcast : (0:ℝ)< small T := by
          change 0<(small T:ℝ)-remainingDemand (xi i) B (insert 0 ∅) (B 0) at hD
          rw [show B 0=b from rfl] at hD
          simp only [Finset.insert_empty] at hD
          linarith
        exact_mod_cast hcast
      have hDW : D≤ deficit i b c ω := by
        have h := template_deficit_le_raw_of_positive_small i c hb ω hsmall
        change (small T:ℝ)+(imbalance T:ℝ)/2-remainingDemand (xi i) B {0} (B 0)≤_ at h
        rw [hk] at h
        simpa only [Nat.cast_zero,zero_div,add_zero,D,focalDeficit,Finset.insert_empty] using h
      have hW : 0< deficit i b c ω := hD.trans_le hDW
      have hWN : deficit i b c ω≤(N:ℝ) := by
        have hx : 0≤ sumX (demand (xi i) b) ω :=
          Finset.sum_nonneg (fun j _ => (demand_bounds (xi_pos i) hb (ω j)).1)
        change (c:ℝ)-sumX (demand (xi i) b) ω≤(N:ℝ)
        linarith
      have hexp : Real.exp (-θ*deficit i b c ω)≤1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hθ hW.le])
      rw [strictPower,if_pos hD]
      exact ⟨mul_nonneg (Real.exp_pos _).le (pow_nonneg hD.le q),
        (mul_le_mul_of_nonneg_right hexp (pow_nonneg hD.le q)).trans
          (by simpa only [one_mul] using pow_le_pow_left₀ hD.le (hDW.trans hWN) q)⟩
    · simp only [strictPower,if_neg hD,mul_zero]
      exact ⟨le_rfl,by positivity⟩
  · rw [unequal_literal_zero i c g cm hb hbL hlo hbl hε hM hr θ q ω he]
    exact ⟨le_rfl,by positivity⟩

omit [Nonempty (Fin N)] in
theorem low_physical_bounded (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b θ : ℝ} (hb : 0< b) (hbL : b≤ g.multiplier)
    (hlo : 0< g.multiplier-g.radius) (hbl : b≤ g.multiplier-g.radius)
    (hε : 0< g.margin) (hM : 0< g.population) (hr : 0< g.requiredDemand)
    (hθ : 0≤θ) (hc : (c:ℝ)≤ N) (q : ℕ) (hq : 0< q) (ω : Fin N → RowRival) :
    physicalMoment i c g cm b θ q ω∈Icc (0:ℝ) 1 := by
  have hp := physicalMoment_le_strict_zero i c g cm hb θ q hq ω
  have hz := low_literal_polynomial i c g cm hb hbL hlo hbl hε hM hr hθ hc 0 ω
  simp only [pow_zero] at hz
  exact ⟨hp.1,hp.2.trans hz.2⟩

theorem original_empty_moments (i : Row) (A : CenteredArray RowRival)
    [∀ n,Nonempty (Fin (A.N n))] (hgap : A.CompactGap)
    (b θ r : ℕ → ℝ) (c : ℕ → ℕ) (hY : ∀ n,A.Y n=integerSign)
    (hcenter : ∀ n,∀ᵐ x ∂A.law n,A.X n x=demand (xi i) (b n) x-r n)
    (hmatch : ∀ᶠ n in atTop,(c n:ℝ)=(A.N n:ℝ)*r n)
    {θ₀ lo hi : ℝ} (hlo : 0< lo) (hθ : ∀ n,lo≤θ n ∧ θ n≤ hi)
    (hθlim : Tendsto θ atTop (𝓝 θ₀)) (hθ₀ : 0<θ₀) :
    ∀ q : Fin 3,Tendsto (fun n => (A.N n:ℝ)*
      ∫ ω : Fin (A.N n) → RowRival,emptyMoment i (c n) (b n) (θ n) q.val ω
        ∂Measure.pi (fun _ : Fin (A.N n) => A.law n))
      atTop (𝓝 (density A.vX A.vY*(q.val.factorial:ℝ)/θ₀^(q.val+1))) := by
  let shift := fun n => (c n:ℝ)-(A.N n:ℝ)*r n
  have hs : Tendsto (fun n => (reflectX A).d n*shift n) atTop (𝓝 0) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0)).congr'
    filter_upwards [hmatch] with n hn
    simp only [shift,hn,sub_self,mul_zero]
  have hy : Tendsto (fun n => (reflectX A).d n*((0-0:ℤ):ℝ)) atTop (𝓝 0) := by simp
  have ht := strict_moments (reflectX A) (reflectX_compactGap A hgap) shift
    (fun _ => 0) (fun _ => 0) hs hy θ hlo hθ hθlim hθ₀
  have hid (n q : ℕ) :
      (∫ ω : Fin (A.N n) → RowRival,emptyMoment i (c n) (b n) (θ n) q ω
        ∂Measure.pi (fun _ : Fin (A.N n) => A.law n))=
      ∫ w,strictTest q (θ n) w ∂(reflectX A).cell shift (fun _ => 0) (fun _ => 0) n := by
    simp_rw [emptyMoment_eq_laplace,← hY n]
    exact integral_laplace_eq_reflected_cell A (fun n => demand (xi i) (b n))
      (fun n => measurable_demand _ _) r (fun n => (c n:ℝ)) hcenter n q (θ n) 0
  intro q
  fin_cases q
  · simpa only [hid,reflectX,Nat.factorial_zero,Nat.cast_one,pow_one,mul_one,
      Nat.reduceAdd] using ht.1
  · simpa only [hid,reflectX,Nat.factorial_one,Nat.cast_one,mul_one,
      Nat.reduceAdd] using ht.2.1
  · convert! ht.2.2 using 1
    · funext n
      rw [hid]
      rfl
    · norm_num [reflectX]
      ring

end FCAppendix.Affine.Uniform06.EqualOnlyRareMoments
