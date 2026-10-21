import FCAppendix.Affine.Uniform06.RelativeIntegralWindow
import FCAppendix.Affine.Uniform06.LiteralMomentBounds
import FCAppendix.Affine.Uniform06.LiteralRootGood
import FCAppendix.Affine.Uniform06.RareSourceReciprocal

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.PhysicalRootTransfer

open MeasureTheory Set Filter LowBody
open scoped Topology BigOperators
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource RawMarkedLaplace
open PhysicalSourceMoments LiteralRootWindow RawMomentPartition RawPathAdapter
open RareEmpiricalReplacement RelativeIntegralWindow FullReciprocalMean
open FCAppendix.Affine.WeightedSampling

theorem constructed_response_replacement (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 (FullJointLaw.law i)))
    (N c : ℕ → ℕ) [∀ n,Nonempty (Fin (N n))]
    (hN : Tendsto N atTop atTop) (hNp : ∀ n,0< N n)
    (b θ : ℕ → ℝ) (g : ℕ → GuardData)
    (cm : ∀ n,(Fin (N n) → Fin 4) → ℝ)
    (E : ∀ n,Set (Fin (N n) → RowRival)) (hE : ∀ n,MeasurableSet (E n))
    {lo blo bhi U Θ t0 b0 θ0 γ ε B : ℝ}
    (hlo : 0< lo) (hloBlo : lo< blo) (hU : 0< U)
    (hb : ∀ n,b n ∈ Icc blo bhi) (hbiU : bhi≤ U)
    (hbL : ∀ n,b n≤(g n).multiplier) (hr : ∀ n,0<(g n).requiredDemand)
    (hclip : (1-xi i)*U≤ lo)
    (hbox : ∀ n,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p ∈ EarlyJointCompactness.box (cutoff i) U)
    (ht0 : 0< t0) (hθ : ∀ n,t0≤θ n ∧ θ n≤Θ)
    (hblim : Tendsto b atTop (𝓝 b0)) (hθlim : Tendsto θ atTop (𝓝 θ0))
    (hb0L : b0< entry i) (hγ : 0<γ) (hγν : γ≤ nu i b0 θ0)
    (hε : 0<ε) (hB : 0< B)
    (hpoly : ∀ n,∀ᵐ ω ∂Measure.pi (fun _ : Fin (N n) =>
        tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n)),
      (∀ q : Fin 3,literalMoment i (c n) (g n) (cm n) (b n) (θ n) q.val ω
          ∈ Icc (0:ℝ) ((N n:ℝ)^q.val) ∧
        literalMoment i (c n) (g n) (cm n) (b n) (θ n/2) q.val ω
          ∈ Icc (0:ℝ) ((N n:ℝ)^q.val)) ∧
      ∀ q : Fin 2,physicalMoment i (c n) (g n) (cm n) (b n) (θ n) (q.val+1) ω
        ∈ Icc (0:ℝ) 1)
    (hmom : ∀ᶠ n in atTop,
      (∀ q : Fin 3,(N n:ℝ)*∫ ω : Fin (N n) → RowRival,
        literalMoment i (c n) (g n) (cm n) (b n) (θ n) q.val ω
          ∂Measure.pi (fun _ : Fin (N n) => tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))≤ B ∧
        (N n:ℝ)*∫ ω : Fin (N n) → RowRival,
          literalMoment i (c n) (g n) (cm n) (b n) (θ n/2) q.val ω
            ∂Measure.pi (fun _ : Fin (N n) => tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))≤ B) ∧
      (N n:ℝ)*∫ ω : Fin (N n) → RowRival,
        ((imbalanceSum ω).natAbs:ℝ)*literalMoment i (c n) (g n) (cm n) (b n) (θ n) 0 ω
          ∂Measure.pi (fun _ : Fin (N n) => tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))≤ B)
    (hbad : ∀ᶠ n in atTop,(Measure.pi (fun _ : Fin (N n) =>
        tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))).real (E n)ᶜ≤
      10*Real.exp (-(2*ε^2)*(N n:ℝ)))
    (hrows : ∀ᶠ n in atTop,∀ᵐ ω ∂Measure.pi (fun _ : Fin (N n) =>
        tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n)),ω ∈ E n →
      (∀ q : Fin 2,
        physicalMoment i (c n) (g n) (cm n) (b n) (θ n) (q.val+1) ω=0 ∧
        literalMoment i (c n) (g n) (cm n) (b n) (θ n) (q.val+1) ω=0) ∨
      (ValidCounts (c n) ω ∧ (∀ j,(ω j).1=0 → (ω j).2≤ U) ∧
      (imbalanceSum ω=0 ∨ ∀ j,0≤ rawH (xi i) (b n) (ω j)) ∧
      ((imbalanceSum ω).natAbs:ℝ)<
        totalWeight (FiniteSampledLaplace.rowWeights (rawWeight (xi i) (g n))
          (rawWeight_bounds (xi i) (g n)) ω) ∧
      γ+((imbalanceSum ω).natAbs:ℝ)/(lo*(N n:ℝ))≤
        empirical (FullReciprocalMean.reciprocal (b n)) (N n) ω))
    (q : Fin 2) :
    Tendsto (fun n => (N n:ℝ)^(q.val+2)*tiltedPhysical i (G n:Measure (ℝ × ℝ))
        (N n) (c n) (g n) (cm n) (b n) (θ n) (q.val+1)-
      (1/(b0*nu i b0 θ0))^(q.val+1)*(N n:ℝ)*∫ ω : Fin (N n) → RowRival,
        literalMoment i (c n) (g n) (cm n) (b n) (θ n) (q.val+1) ω
          ∂Measure.pi (fun _ : Fin (N n) => tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n)))
      atTop (𝓝 0) := by
  let ν := nu i b0 θ0
  let μ := fun n => tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n)
  let P := fun n => Measure.pi (fun _ : Fin (N n) => μ n)
  let T := fun n => literalMoment i (c n) (g n) (cm n) (b n) (θ n) 0
  let degree : Fin 3 := ⟨q.val+1,by omega⟩
  have hblo : 0< blo := hlo.trans hloBlo
  have hbp : ∀ n,0< b n := fun n => hblo.trans_le (hb n).1
  have hb0 := isClosed_Icc.mem_of_tendsto hblim (Eventually.of_forall hb)
  have hb0p : 0< b0 := hblo.trans_le hb0.1
  have hlo0 : lo< b0 := hloBlo.trans_le hb0.1
  have hν : 0<ν := nu_pos i hb0p hb0L θ0
  letI : ∀ n,IsProbabilityMeasure (μ n) := fun n => tiltedSource_probability i _ (hbp n) _
  have hNr (n : ℕ) : 0<(N n:ℝ) := Nat.cast_pos.mpr (hNp n)
  have hNreal : Tendsto (fun n => (N n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hinv : Tendsto (fun n => 1/(N n:ℝ)) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp hNreal
  have hbb (n : ℕ) : b n ∈ Icc lo bhi := ⟨hloBlo.le.trans (hb n).1,(hb n).2⟩
  have hθbox (n : ℕ) : θ n ∈ Icc (-Θ) Θ := by
    have hp := ht0.trans_le (hθ n).1
    exact ⟨by linarith [(hθ n).2],(hθ n).2⟩
  have hTpoly (n : ℕ) : ∀ᵐ ω ∂P n,0≤ T n ω ∧ T n ω≤1*(N n:ℝ)^0 := by
    simpa only [T,P,μ,Set.mem_Icc,Fin.val_zero,pow_zero,mul_one] using
      (hpoly n).mono fun _ hx => (hx.1 0).1
  have hTbound : ∀ᶠ n in atTop,(N n:ℝ)*∫ ω,T n ω ∂P n≤ B :=
    hmom.mono fun _ hn => (hn.1 0).1
  have hrec := (RareSourceReciprocal.original_bounded_rare_reciprocal_and_window i G hG
    hlo hU.le hbox b b θ hbb hbb hθbox hblim hblim hθlim N hNp hN T
    (fun n => measurable_literalMoment _ _ _ _ _ _ _) 0 (by norm_num : (0:ℝ)≤1) hB hTpoly hTbound).1
  let aa := fun n => 1/(b n*ν)
  let kk := fun n => xi i/((b n-lo)*γ)
  let a0 := 1/(b0*ν)
  let k0 := xi i/((b0-lo)*γ)
  have haalim : Tendsto aa atTop (𝓝 a0) :=
    tendsto_const_nhds.div (hblim.mul_const ν) (mul_pos hb0p hν).ne'
  have hkklim : Tendsto kk atTop (𝓝 k0) :=
    tendsto_const_nhds.div ((hblim.sub_const lo).mul_const γ) (mul_pos (sub_pos.mpr hlo0) hγ).ne'
  let C := k0^(q.val+1)+a0^(q.val+1)+1
  have hC : 0< C := by dsimp [C,k0,a0]; have hξ:=xi_pos i; positivity
  have hcoef : ∀ᶠ n in atTop,kk n^(q.val+1)+aa n^(q.val+1)≤ C :=
    (((hkklim.pow _).add (haalim.pow _)).eventually
      (Iio_mem_nhds (by dsimp [C]; linarith))).mono fun _ hn => hn.le
  let f := fun n => (N n:ℝ)^(q.val+2)*tiltedPhysical i (G n:Measure (ℝ × ℝ))
      (N n) (c n) (g n) (cm n) (b n) (θ n) (q.val+1)-
    a0^(q.val+1)*(N n:ℝ)*∫ ω,literalMoment i (c n) (g n) (cm n) (b n) (θ n) (q.val+1) ω ∂P n
  apply tendsto_zero_of_windows (f:=f) (B:=C*B) (a:=t0/2)
    (mul_nonneg hC.le hB.le) (half_pos ht0)
  intro H hH
  let z := fun n => max lo (b n-xi i*H/(γ*(N n:ℝ)))
  have hrawlim : Tendsto (fun n => b n-xi i*H/(γ*(N n:ℝ))) atTop (𝓝 b0) := by
    have he (n : ℕ) : xi i*H/(γ*(N n:ℝ))=(xi i*H/γ)*(1/(N n:ℝ)) := by ring
    simpa only [he,mul_zero,sub_zero] using hblim.sub (hinv.const_mul (xi i*H/γ))
  have hzlim : Tendsto z atTop (𝓝 b0) := by
    simpa only [max_eq_right hlo0.le] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => lo) atTop (𝓝 lo)).max hrawlim
  have hzb (n : ℕ) : z n ∈ Icc lo bhi := by
    refine ⟨le_max_left _ _,max_le ((hbb n).1.trans (hb n).2) ?_⟩
    have hp : 0≤ xi i*H/(γ*(N n:ℝ)) := by have hξ:=xi_pos i; positivity
    exact (sub_le_self _ hp).trans (hb n).2
  have hzpos (n : ℕ) : 0< z n := hlo.trans_le (hzb n).1
  have hzraw : ∀ᶠ n in atTop,z n=b n-xi i*H/(γ*(N n:ℝ)) :=
    (hrawlim.eventually (Ioi_mem_nhds hlo0)).mono fun n hn => max_eq_right hn.le
  have hsmall : ∀ᶠ n in atTop,H*(xi i)^2*b n<(b n-lo)^2*γ*(N n:ℝ) := by
    have hlim : Tendsto (fun n => (b n-lo)^2*γ-H*(xi i)^2*b n/(N n:ℝ))
        atTop (𝓝 ((b0-lo)^2*γ)) := by
      simpa only [mul_zero,sub_zero] using
        (((hblim.sub_const lo).pow 2).mul_const γ).sub
          (((hblim.const_mul (H*(xi i)^2)).mul hinv).congr fun n => by ring)
    have hp : 0<(b0-lo)^2*γ := mul_pos (sq_pos_of_pos (sub_pos.mpr hlo0)) hγ
    filter_upwards [hlim.eventually (Ioi_mem_nhds hp)] with n hn
    have hh : H*(xi i)^2*b n/(N n:ℝ)<(b n-lo)^2*γ := by linarith
    exact (div_lt_iff₀ (hNr n)).mp hh
  have hwin := (RareSourceReciprocal.original_bounded_rare_reciprocal_and_window i G hG
    hlo hU.le hbox b z θ hbb hzb hθbox hblim hzlim hθlim N hNp hN T
    (fun n => measurable_literalMoment _ _ _ _ _ _ _) 0 (by norm_num : (0:ℝ)≤1) hB hTpoly hTbound).2
  let er := fun n => (N n:ℝ)*∫ ω,T n ω*
    |empirical (FullReciprocalMean.reciprocal (b n)) (N n) ω-ν| ∂P n
  let ew := fun n => (N n:ℝ)*∫ ω,T n ω*
    empirical (FullReciprocalMean.window (z n) (b n)) (N n) ω ∂P n
  let A := fun n => (if q.val=0 then 1 else 2*(H/(b n*γ)))*H/(b n^2*γ^2)
  let A0 := (if q.val=0 then 1 else 2*(H/(b0*γ)))*H/(b0^2*γ^2)
  have hAlim : Tendsto A atTop (𝓝 A0) := by
    have hfac : Tendsto (fun n => if q.val=0 then (1:ℝ) else 2*(H/(b n*γ))) atTop
        (𝓝 (if q.val=0 then 1 else 2*(H/(b0*γ)))) := by
      split_ifs
      · exact tendsto_const_nhds
      · exact (tendsto_const_nhds.div (hblim.mul_const γ) (mul_pos hb0p hγ).ne').const_mul 2
    exact (hfac.mul_const H).div ((hblim.pow 2).mul_const (γ^2)) (by positivity)
  let e := fun n => A n*(B/(N n:ℝ)+b n*(er n+B/(lo*(N n:ℝ))+ew n/z n))+
    (1+aa n^(q.val+1))*10*((N n:ℝ)^(q.val+2)*Real.exp (-(2*ε^2)*(N n:ℝ)))+
    B*|aa n^(q.val+1)-a0^(q.val+1)|
  have helim : Tendsto e atTop (𝓝 0) := by
    have hbn : Tendsto (fun n => B/(N n:ℝ)) atTop (𝓝 0) := by
      simpa only [mul_zero,div_eq_mul_inv,one_div,one_mul] using hinv.const_mul B
    have hbln : Tendsto (fun n => B/(lo*(N n:ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero,div_eq_mul_inv,one_div,mul_inv,mul_assoc,one_mul] using hinv.const_mul (B/lo)
    have hmain := hAlim.mul (hbn.add (hblim.mul ((hrec.add hbln).add (hwin.div hzlim hb0p.ne'))))
    have hbadlim := (((haalim.pow (q.val+1)).const_add 1).mul_const 10).mul
      (polynomial_exp_tendsto N hN (q.val+2) (by positivity : 0<2*ε^2))
    have hparam := ((haalim.pow (q.val+1)).sub_const (a0^(q.val+1))).abs.const_mul B
    simpa only [e,er,ew,A,aa,ν,a0,P,μ,Pi.div_apply,sub_self,abs_zero,mul_zero,zero_div,add_zero,zero_add]
      using (hmain.add hbadlim).add hparam
  refine ⟨e,helim,?_⟩
  filter_upwards [hmom,hbad,hrows,hcoef,hsmall,hzraw] with n hm hbade hrow hco hs hzr
  let Q := physicalMoment i (c n) (g n) (cm n) (b n) (θ n) (q.val+1)
  let F := literalMoment i (c n) (g n) (cm n) (b n) (θ n) (q.val+1)
  let HH := literalMoment i (c n) (g n) (cm n) (b n) (θ n/2) (q.val+1)
  let X := fun ω : Fin (N n) → RowRival =>
    |empirical (FullReciprocalMean.reciprocal (b n)) (N n) ω-ν|
  let Y := fun ω : Fin (N n) → RowRival => ((imbalanceSum ω).natAbs:ℝ)
  let Z := empirical (FullReciprocalMean.window (z n) (b n)) (N n)
  let tail := (kk n^(q.val+1)+aa n^(q.val+1))*Real.exp (-θ n*H/2)
  have hXmeas : Measurable X := ((measurable_empirical (measurable_reciprocal (b n)) _).sub_const ν).abs
  have hYmeas : Measurable Y :=
    (measurable_of_countable (fun y : ℤ => (y.natAbs:ℝ))).comp measurable_imbalanceSum
  have hZmeas : Measurable Z := measurable_empirical (measurable_window (z n) (b n)) _
  have hXb : ∀ᵐ ω ∂P n,X ω ∈ Icc (0:ℝ) (1/lo+ν) := by
    apply ae_of_all
    intro ω
    have hrb := fun r => reciprocal_bounds hlo (hbb n).1 r
    have he0 : 0≤ empirical (reciprocal (b n)) (N n) ω :=
      div_nonneg (Finset.sum_nonneg (fun j _ => (hrb (ω j)).1)) (hNr n).le
    have he1 : empirical (reciprocal (b n)) (N n) ω≤1/lo := by
      have he := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => (hrb (ω j)).2)
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at he
      unfold empirical
      apply (div_le_iff₀ (hNr n)).mpr
      simpa only [one_div,mul_comm] using he
    refine ⟨abs_nonneg _,?_⟩
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg he0,abs_of_pos hν]; linarith)
  have hYb : ∀ᵐ ω ∂P n,Y ω ∈ Icc (0:ℝ) (N n:ℝ) := by
    apply ae_of_all
    intro ω
    refine ⟨Nat.cast_nonneg _,?_⟩
    change ((imbalanceSum ω).natAbs:ℝ)≤ (N n:ℝ)
    exact_mod_cast (show (imbalanceSum ω).natAbs≤ N n by rw [← draws_eq_natAbs]; exact draws_le ω)
  have hZb : ∀ᵐ ω ∂P n,Z ω ∈ Icc (0:ℝ) 1 :=
    empirical_unit_bounds (μ n) (ae_of_all _ (window_bounds (z n) (b n))) (hNp n)
  have hpp := (hpoly n).mono fun _ hx => hx.2 q
  have htp := (hpoly n).mono fun _ hx => by simpa only [Fin.val_zero,pow_zero] using (hx.1 0).1
  have hfp := (hpoly n).mono fun _ hx => (hx.1 degree).1
  have hhp := (hpoly n).mono fun _ hx => (hx.1 degree).2
  have hbnp : 0< b n := hbp n
  have hNrn : 0< (N n:ℝ) := hNr n
  have hzn : 0< z n := hzpos n
  have hbnlo : 0< b n-lo := sub_pos.mpr (hloBlo.trans_le (hb n).1)
  have hA : 0≤ A n := by dsimp [A]; split_ifs <;> positivity
  have haa : 0≤ aa n := by dsimp [aa]; positivity
  have htail : 0≤ tail := by dsimp [tail,kk,aa]; have hξ:=xi_pos i; positivity
  have hwb : ∀ᵐ ω ∂P n,ω ∈ E n →
      |(N n:ℝ)^(q.val+1)*Q ω-aa n^(q.val+1)*F ω|≤
        A n*(1/(N n:ℝ)+b n*(X ω+Y ω/(lo*(N n:ℝ))+Z ω/z n))*T n ω+tail*HH ω := by
    filter_upwards [hrow,htp,hhp,hXb,hYb,hZb] with ω hω ht hhh hx hy hz' he
    rcases hω he with hzero | hregular
    · have hp0 : Q ω=0 := (hzero q).1
      have hf0 : F ω=0 := (hzero q).2
      rw [hp0,hf0,mul_zero,mul_zero,sub_self,abs_zero]
      have ht0 := ht.1
      have hhh0 := hhh.1
      have hx0 := hx.1
      have hy0 := hy.1
      have hz0 := hz'.1
      positivity
    · obtain ⟨hv,hcap,hraw,hW,hrecip⟩ := hregular
      have hh' := actual_literal_window i (c n) (g n) (cm n) hlo hU
        (hloBlo.trans_le (hb n).1) ((hb n).2.trans hbiU) hclip hγ hγν
        (hzpos n) hH (hNp n) (ht0.le.trans (hθ n).1) (hbL n) (hr n)
        ω hv hcap hraw hW hrecip hs (le_of_eq hzr) q
      convert! hh' using 1; dsimp only [A,Q,F,HH,T,X,Y,Z,aa,kk,tail,ν]; ring
  have hi := finite_integral_bound (P n) Q (T n) F HH X Y Z (E n) (hE n)
    (measurable_physicalMoment _ _ _ _ _ _ _) (measurable_literalMoment _ _ _ _ _ _ _)
    (measurable_literalMoment _ _ _ _ _ _ _) (measurable_literalMoment _ _ _ _ _ _ _)
    hXmeas hYmeas hZmeas (hNr n) haa hA htail (hbp n).le hlo (hzpos n)
    (q.val+1) hpp htp hfp hhp hXb hYb hZb hwb
  have hmass0 : (∫ ω,T n ω ∂P n)≤ B/(N n:ℝ) := by
    apply (le_div_iff₀ (hNr n)).mpr
    have hh := (hm.1 0).1
    change (N n:ℝ)*(∫ ω,T n ω ∂P n)≤ B at hh
    nlinarith only [hh]
  have hmass1 : (∫ ω,T n ω*Y ω ∂P n)/lo≤ B/(lo*(N n:ℝ)) := by
    have hh' : (∫ ω,T n ω*Y ω ∂P n)≤ B/(N n:ℝ) :=
      (le_div_iff₀ (hNr n)).mpr (by simpa only [Y,T,mul_comm] using hm.2)
    have he := div_le_div_of_nonneg_right hh' hlo.le
    convert! he using 1; ring
  have htailbound : tail*B≤ C*B*Real.exp (-(t0/2)*H) := by
    have he := Real.exp_le_exp.mpr (show -θ n*H/2≤-(t0/2)*H by
      nlinarith [mul_le_mul_of_nonneg_right (hθ n).1 hH])
    have hc' := mul_le_mul hco he (Real.exp_pos _).le hC.le
    have h := mul_le_mul_of_nonneg_right hc' hB.le
    dsimp only [tail]
    convert! h using 1; ring
  have hmain : |(N n:ℝ)^(q.val+2)*tiltedPhysical i (G n:Measure (ℝ × ℝ))
      (N n) (c n) (g n) (cm n) (b n) (θ n) (q.val+1)-
        aa n^(q.val+1)*(N n:ℝ)*∫ ω,F ω ∂P n|≤
      A n*(B/(N n:ℝ)+b n*(er n+B/(lo*(N n:ℝ))+ew n/z n))+
        (1+aa n^(q.val+1))*10*((N n:ℝ)^(q.val+2)*Real.exp (-(2*ε^2)*(N n:ℝ)))+
          C*B*Real.exp (-(t0/2)*H) := by
    refine hi.trans ?_
    have ht' := (hm.1 degree).2
    change (N n:ℝ)*(∫ ω,HH ω ∂P n)≤ B at ht'
    have hinside : (∫ ω,T n ω ∂P n)+
        b n*(er n+(∫ ω,T n ω*Y ω ∂P n)/lo+ew n/z n)≤
        B/(N n:ℝ)+b n*(er n+B/(lo*(N n:ℝ))+ew n/z n) :=
      add_le_add hmass0 (mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add le_rfl hmass1) le_rfl) hbnp.le)
    have hh' := add_le_add (mul_le_mul_of_nonneg_left
      hinside hA)
      (mul_le_mul_of_nonneg_left ht' htail)
    have hbad' := mul_le_mul_of_nonneg_left hbade
      (show 0≤(1+aa n^(q.val+1))*(N n:ℝ)^(q.val+2) by positivity)
    dsimp only [er,ew,Y,T,F,Q,HH,P,μ,tiltedPhysical] at hh' hbad' htailbound ⊢
    nlinarith only [hh',hbad',htailbound]
  have hFi : Integrable F (P n) := Integrable.of_mem_Icc 0 ((N n:ℝ)^(q.val+1))
    (measurable_literalMoment _ _ _ _ _ _ _).aemeasurable hfp
  have hFn : 0≤(N n:ℝ)*∫ ω,F ω ∂P n :=
    mul_nonneg (hNr n).le (integral_nonneg_of_ae (hfp.mono fun _ hx => hx.1))
  have hFb : (N n:ℝ)*∫ ω,F ω ∂P n≤ B := (hm.1 degree).1
  have hpchange : |(aa n^(q.val+1)-a0^(q.val+1))*((N n:ℝ)*∫ ω,F ω ∂P n)|≤
      B*|aa n^(q.val+1)-a0^(q.val+1)| := by
    rw [abs_mul,abs_of_nonneg hFn]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hFb (abs_nonneg _)
  have hid : f n=
      ((N n:ℝ)^(q.val+2)*tiltedPhysical i (G n:Measure (ℝ × ℝ))
        (N n) (c n) (g n) (cm n) (b n) (θ n) (q.val+1)-
        aa n^(q.val+1)*(N n:ℝ)*∫ ω,F ω ∂P n)+
      (aa n^(q.val+1)-a0^(q.val+1))*((N n:ℝ)*∫ ω,F ω ∂P n) := by
    dsimp only [f,F]
    ring
  rw [hid]
  have hh' := (abs_add_le _ _).trans (add_le_add hmain hpchange)
  convert! hh' using 1; dsimp only [e]; ring

end FCAppendix.Affine.Uniform06.PhysicalRootTransfer
