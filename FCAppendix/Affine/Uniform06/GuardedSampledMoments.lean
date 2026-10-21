import FCAppendix.Affine.Uniform06.RawSamplingBounds
import FCAppendix.Affine.Uniform06.LiteralGuardRare
import FCAppendix.Affine.Uniform06.SharedGamma

noncomputable section
namespace FCAppendix.Affine.Uniform06.GuardedSampledMoments

open Set MeasureTheory Filter
open scoped Topology BigOperators
open LowBody Uniform07 RawMixedSource RawTiltedSource RawMarkedLaplace
open LiteralExperiment SamplingPopulation MixedIntervalLLT
open FiniteSampledLaplace SampledCellDomination SampledSafeLimit
open LiteralGuardRare SharedGamma RareEmpiricalReplacement RawSamplingBounds

section FiniteError
variable {Ω : Type*} [MeasurableSpace Ω]

lemma integral_guard_error_bound (μ : Measure Ω) [IsFiniteMeasure μ]
    {T a : Ω → ℝ} (hT : Measurable T) (ha : Measurable a)
    {D α : ℝ} (hTb : ∀ᵐ ω ∂μ,T ω ∈ Icc (0:ℝ) D)
    (hab : ∀ᵐ ω ∂μ,a ω ∈ Icc (0:ℝ) 1) (_hα : α ∈ Icc (0:ℝ) 1) :
    |(∫ ω,a ω*T ω ∂μ)-α*(∫ ω,T ω ∂μ)| ≤ ∫ ω,T ω*|a ω-α| ∂μ := by
  have hTi : Integrable T μ := Integrable.of_mem_Icc 0 D hT.aemeasurable hTb
  have hai : Integrable (fun ω => a ω*T ω) μ := by
    apply Integrable.of_mem_Icc 0 D (ha.mul hT).aemeasurable
    filter_upwards [hTb,hab] with ω ht haω
    exact ⟨mul_nonneg haω.1 ht.1,
      (mul_le_mul_of_nonneg_right haω.2 ht.1).trans (by simpa only [one_mul] using ht.2)⟩
  rw [← integral_const_mul,← integral_sub hai (hTi.const_mul α)]
  have hh : |∫ ω,a ω*T ω-α*T ω ∂μ| ≤ ∫ ω,|a ω*T ω-α*T ω| ∂μ := by
    simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
      (f:=fun ω => a ω*T ω-α*T ω) (μ:=μ))
  refine hh.trans_eq (integral_congr_ae ?_)
  filter_upwards [hTb] with ω ht
  rw [← sub_mul,abs_mul,abs_of_nonneg ht.1,mul_comm]

end FiniteError

def ratio (i : Row) (G : Measure (ℝ × ℝ)) (b θ : ℝ) (g : GuardData) : ℝ :=
  selectedMean i G b θ g/weightMean i G b θ g

def sourceGamma (i : Row) (G : Measure (ℝ × ℝ)) (N c : ℕ)
    (b θ : ℝ) (g : GuardData) (cm : ℝ) : ℝ :=
  gamma (currentCoefficient (tiltedSource i G b θ) N (xi i) g c cm) (ratio i G b θ g)

def safeCell (i : Row) (μ : Measure RowRival) (N c : ℕ) [Nonempty (Fin N)]
    (g : GuardData) (cm : (Fin N → Fin 4) → ℝ) (b θ : ℝ)
    (y : ℤ) (k q : ℕ) : ℝ :=
  (N:ℝ)*∫ ω : Fin N → RowRival,rawGuard (xi i) g c cm b ω*
    safeRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
      (rawWeight_bounds (xi i) g) c θ y q k ω ∂Measure.pi (fun _ : Fin N => μ)

def zeroCell (i : Row) (μ : Measure RowRival) (N c : ℕ) [Nonempty (Fin N)]
    (g : GuardData) (b θ : ℝ) (q : ℕ) : ℝ :=
  (N:ℝ)*∫ ω : Fin N → RowRival,
    sampledRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
      (rawWeight_bounds (xi i) g) c θ 0 q 0 ω ∂Measure.pi (fun _ : Fin N => μ)

theorem original_current_gamma_moments (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 (FullJointLaw.law i)))
    (hvalue : ∀ n,(G n:Measure (ℝ × ℝ)).map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hbelow : ∀ n,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p.2 ≤ p.1)
    (A : CenteredArray RowRival) [∀ n,Nonempty (Fin (A.N n))] (hgap : A.CompactGap)
    (b θ r : ℕ → ℝ) (c : ℕ → ℕ) (g : ℕ → GuardData) (g₀ : GuardData)
    (cm : (n : ℕ) → (Fin (A.N n) → Fin 4) → ℝ) (cmbar : ℕ → ℝ)
    (hlaw : ∀ n,A.law n=tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))
    (hY : ∀ n,A.Y n=integerSign)
    (hcenter : ∀ n,∀ᵐ x ∂A.law n,A.X n x=demand (xi i) (b n) x-r n)
    (hr : ∀ n,r n ∈ Icc (0:ℝ) 1)
    (hmatch : ∀ᶠ n in atTop,(c n:ℝ)=(A.N n:ℝ)*r n)
    (hcap : ∀ n,(c n:ℝ) ≤ (A.N n:ℝ))
    {b₀ θ₀ lo hi U e ε K s : ℝ}
    (hb : ∀ n,0 < b n) (hb₀ : 0 < b₀) (hblim : Tendsto b atTop (𝓝 b₀))
    (hθlim : Tendsto θ atTop (𝓝 θ₀)) (hθ₀ : 0 < θ₀) (hlo : 0 < lo)
    (hθ : ∀ n,lo ≤ θ n ∧ θ n ≤ hi)
    (hU : 0 < U) (hcapG : ∀ n,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p.2 ≤ U)
    (hbU : ∀ n,b n ≤ U) (he : 0 < e)
    (hreceipt : ∀ n,(1-xi i/2)*U+e ≤ b n)
    (hLlim : Tendsto (fun n => (g n).multiplier) atTop (𝓝 (entry i)))
    (hL₀ : g₀.multiplier=entry i)
    (hreq₀ : g₀.requiredDemand=PrefixRoot.requiredDemand i)
    (hreq : ∀ n,(g n).requiredDemand=g₀.requiredDemand)
    (hM : ∀ n,0 < (g n).population) (hNM : ∀ n,(A.N n:ℝ) ≤ (g n).population)
    (hε : 0 < ε) (hgε : ∀ n,ε ≤ (g n).margin) (hK : 0 ≤ K)
    (hgl : ∀ n,0 < (g n).multiplier-(g n).radius)
    (hgu : ∀ n,0 < (g n).multiplier+(g n).radius)
    (hd : ∀ n,0 < (g n).rejectionScale)
    (hs : 0 < s) (hst : s ≤ cutoff i) (hgseed : ∀ n,(g n).seedCutoff=s)
    (hcm : ∀ n,∀ᵐ ω ∂Measure.pi (fun _ : Fin (A.N n) => A.law n),
      |cm n (fun j => (ω j).1)/(g n).population-cmbar n| ≤
        K*(deviationSum (A.law n) (xi i) (g n) ω+(g n).population⁻¹)) :
    (∃ Γmax > (0:ℝ),∀ᶠ n in atTop,
      sourceGamma i (G n:Measure (ℝ × ℝ)) (A.N n) (c n) (b n) (θ n) (g n) (cmbar n)
        ∈ Icc (1:ℝ) Γmax) ∧
    ∀ q : Fin 3,Tendsto (fun n =>
      zeroCell i (A.law n) (A.N n) (c n) (g n) (b n) (θ n) q.val+
        (∑' k : ℕ,(safeCell i (A.law n) (A.N n) (c n) (g n) (cm n) (b n) (θ n)
          ((k+1:ℕ):ℤ) (k+1) q.val+
          safeCell i (A.law n) (A.N n) (c n) (g n) (cm n) (b n) (θ n)
            (-((k+1:ℕ):ℤ)) (k+1) q.val))-
        (density A.vX A.vY*(q.val.factorial:ℝ)/θ₀^(q.val+1))*
          sourceGamma i (G n:Measure (ℝ × ℝ)) (A.N n) (c n)
            (b n) (θ n) (g n) (cmbar n)) atTop (𝓝 0) := by
  let X := fun n => demand (xi i) (b n)
  let H := fun n => rawH (xi i) (b n)
  let W := fun n => rawWeight (xi i) (g n)
  let cap := fun n => (c n:ℝ)
  let η := e/(xi i*U)
  let Q := Real.exp (-lo*η)
  let a := selectedMean i (FullJointLaw.law i:Measure (ℝ × ℝ)) b₀ θ₀ g₀
  let z := weightMean i (FullJointLaw.law i:Measure (ℝ × ℝ)) b₀ θ₀ g₀
  let α := fun n => currentCoefficient (A.law n) (A.N n) (xi i) (g n) (c n) (cmbar n)
  let qn := fun n => ratio i (G n:Measure (ℝ × ℝ)) (b n) (θ n) (g n)
  have hη : 0 < η := div_pos he (mul_pos (xi_pos i) hU)
  have hQ0 : 0 < Q := Real.exp_pos _
  have hQ1 : Q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hlo hη])
  have hdenQ : 0 < 1-Q := sub_pos.mpr hQ1
  have haz := full_sampling_means_positive i hb₀ θ₀ g₀ hL₀ hreq₀
  have hz : 0 < z := haz.1
  have ha : 0 < a := haz.2
  have hLpos (n : ℕ) : 0 < (g n).multiplier := by linarith [hgl n,hgu n]
  have hL0pos : 0 < g₀.multiplier := by rw [hL₀]; exact EarlyMean.entry_pos i
  have hr0pos : 0 < g₀.requiredDemand := by
    rw [hreq₀]
    exact (EntryEarlySourceLimits.requiredDemand_bounds i).1
  have hmeans := actual_one_user_means_tendsto i G (FullJointLaw.law i) hG b θ g g₀
    hb hb₀ hLpos hL0pos hr0pos hreq hblim hθlim
      (by simpa only [hL₀] using hLlim)
  have hwmean : Tendsto (fun n => ∫ x,W n x ∂A.law n) atTop (𝓝 z) := by
    simpa only [W,z,weightMean,hlaw] using! hmeans.1
  have hamean : Tendsto (fun n => ∫ x,W n x*Real.exp (-θ n*H n x) ∂A.law n)
      atTop (𝓝 a) := by simpa only [W,H,a,selectedMean,hlaw] using! hmeans.2
  have hqlim : Tendsto qn atTop (𝓝 (a/z)) := hmeans.2.div hmeans.1 hz.ne'
  have hwpos := hmeans.1.eventually (Ioi_mem_nhds hz)
  have hqb : ∀ᶠ n in atTop,qn n ∈ Icc (0:ℝ) Q := by
    filter_upwards [hwpos] with n hn
    have hh := original_sampling_ratio_bounds i (G n:Measure (ℝ × ℝ)) hU (hb n)
      (hbU n) he (hcapG n) (hreceipt n) hlo (hθ n).1 (g n) hn
    exact ⟨hh.1.le,hh.2.1⟩
  have hα : ∀ n,α n ∈ Icc (0:ℝ) 1 := fun n => currentCoefficient_bounds _ _ _ _ _ _
  have hΓ : ∀ᶠ n in atTop,sourceGamma i (G n:Measure (ℝ × ℝ)) (A.N n) (c n)
      (b n) (θ n) (g n) (cmbar n) ∈ Icc (1:ℝ) (1+2*Q/(1-Q)) := by
    filter_upwards [hqb] with n hn
    simpa only [sourceGamma,← hlaw,α,qn,Set.mem_Icc] using! gamma_bounds (hα n) hn hQ1
  refine ⟨⟨1+2*Q/(1-Q),by positivity,hΓ⟩,?_⟩
  have hHp (n : ℕ) : ∀ᵐ x ∂A.law n,0 ≤ H n x ∧ (0 < W n x → η ≤ H n x) := by
    rw [hlaw]
    exact original_receipt_h_bounds i (G n:Measure (ℝ × ℝ)) hU (hb n) (hbU n)
      he (hcapG n) (hreceipt n) (θ n) (g n)
  have hbal (n : ℕ) (x : RowRival) (hx : W n x ≠ 0) :
      X n x+H n x=1/2 ∧ A.Y n x=0 := by
    simpa only [hY] using raw_support (xi i) (b n) (g n) x hx
  have hX := fun n => measurable_demand (xi i) (b n)
  have hH := fun n => measurable_rawH (xi i) (b n)
  have hW := fun n => measurable_rawWeight (xi i) (g n)
  have hWX := fun n x => rawWeight_bounds (xi i) (g n) x
  have hXX := fun n x => demand_bounds (xi_pos i) (hb n) x
  have hHH := fun n x => rawH_abs_le i (hb n) x
  have hpositive (n : ℕ) : ∀ᵐ x ∂A.law n,0 ≤ X n x ∧ 0 ≤ H n x :=
    (hHp n).mono fun x hx => ⟨(hXX n x).1,hx.1⟩
  obtain ⟨C,hC,hcells⟩ := eventual_sampled_cell_bounds A hgap X H W r cap θ hX hH hW
    hWX hXX (fun n => (hHp n).mono fun _ hx => hx.1) hcenter hcap hlo hθ hη
    (fun n => (hHp n).mono fun _ hx => hx.2)
  have hseed : ∀ᶠ n in atTop,(Measure.pi (fun _ : Fin (A.N n) => A.law n)).real
      (LiteralSeedRare.noRivalSeed (g n).seedCutoff) ≤
        1*Real.exp (-(2*(Real.exp (-2*hi)*s)^2)*(A.N n:ℝ)) := by
    apply Eventually.of_forall
    intro n
    rw [hlaw,hgseed,one_mul]
    exact LiteralSeedRare.source_noRivalSeed_probability i (G n:Measure (ℝ × ℝ))
      (hvalue n) (hbelow n) hs hst (hb n) (hlo.le.trans (hθ n).1) (hθ n).2
      (A.N n) (Nat.cast_pos.mp (A.N_pos n))
  intro q
  let L := density A.vX A.vY*(q.val.factorial:ℝ)/θ₀^(q.val+1)
  have hsamp (k : ℕ) (y : ℤ) := fixed_imbalance_sampled_moments A hgap X H W r cap θ
    hX hH hW hXX hHH hWX hbal (fun n => (hHp n).mono fun _ hx => hx.1)
    hr hcenter hmatch hcap k y hlo hθ hθlim hθ₀ hz hwmean hamean q
  have hsafe (k : ℕ) (y : ℤ) := fixed_imbalance_safe_moments A hgap X H W r cap θ
    hX hH hW hXX hHH hWX hbal (fun n => (hHp n).mono fun _ hx => hx.1)
    hr hcenter hmatch hcap k y hlo hθ hθlim hθ₀ hz hwmean hamean q
  have hzero : Tendsto (fun n => zeroCell i (A.law n) (A.N n) (c n) (g n)
      (b n) (θ n) q.val-L) atTop (𝓝 0) := by
    have hh := (hsamp 0 0).sub_const L
    simpa only [zeroCell,hY,X,H,W,cap,pow_zero,one_mul,div_one,L,sub_self] using hh
  have hfixed (k : ℕ) (y : ℤ) : Tendsto (fun n =>
      safeCell i (A.law n) (A.N n) (c n) (g n) (cm n) (b n) (θ n) y k q.val-
        α n*L*(qn n)^k) atTop (𝓝 0) := by
    let T : (n : ℕ) → (Fin (A.N n) → RowRival) → ℝ := fun n => safeRow (X n) (H n) (W n) (A.Y n) (hWX n) (cap n) (θ n) y q.val k
    have hT (n : ℕ) : Measurable (T n) := measurable_safeRow (hX n) (hH n) (hW n)
      (A.measurable_Y n) _ _ _ _ _ _
    have hTb (n : ℕ) : ∀ᵐ ω ∂Measure.pi (fun _ : Fin (A.N n) => A.law n),
        0 ≤ T n ω ∧ T n ω ≤ 1*(A.N n:ℝ)^q.val := by
      simpa only [one_mul,T,cap,Set.mem_Icc] using! (polynomial_sampled_ae (A.law n)
        (Nat.cast_pos.mp (A.N_pos n)) (X n) (H n) (W n) (A.Y n) (hWX n)
          (hpositive n) (hcap n) (hlo.le.trans (hθ n).1) y q.val k).mono fun _ hx => hx.2
    let R := |(a/z)^k*L|+1
    have hR : 0 < R := by dsimp [R]; positivity
    have hrare : ∀ᶠ n in atTop,(A.N n:ℝ)*∫ ω,T n ω
        ∂Measure.pi (fun _ : Fin (A.N n) => A.law n) ≤ R := by
      exact ((hsafe k y).eventually (Iio_mem_nhds
        (show (a/z)^k*L < R by dsimp [R]; linarith [le_abs_self ((a/z)^k*L)]))).mono
          fun _ hn => hn.le
    have hrep := relative_current_guard A.law A.N (fun n => Nat.cast_pos.mp (A.N_pos n))
      A.market (xi i) (xi_pos i) g c cm cmbar b hM hNM hε hgε hK
      (by norm_num : (0:ℝ) ≤ 1) hR (by norm_num : (0:ℝ) ≤ 1)
      (by positivity : 0 < 2*(Real.exp (-2*hi)*s)^2) hgl hgu hd T hT q.val hTb hrare hcm hseed
    have he0 : Tendsto (fun n => safeCell i (A.law n) (A.N n) (c n) (g n) (cm n)
        (b n) (θ n) y k q.val-α n*((A.N n:ℝ)*∫ ω,T n ω
          ∂Measure.pi (fun _ : Fin (A.N n) => A.law n))) atTop (𝓝 0) := by
      apply squeeze_zero_norm' _ hrep
      apply Eventually.of_forall
      intro n
      have hh := integral_guard_error_bound (Measure.pi (fun _ : Fin (A.N n) => A.law n))
        (hT n) (measurable_rawGuard (xi i) (g n) (c n) (cm n) (b n))
        (by simpa only [one_mul,Set.mem_Icc] using! hTb n)
        (ae_of_all _ (rawGuard_bounds (xi i) (g n) (c n) (cm n) (b n))) (hα n)
      have hh' := mul_le_mul_of_nonneg_left hh (A.N_pos n).le
      have hscale (u v : ℝ) :
          |(A.N n:ℝ)*u-α n*((A.N n:ℝ)*v)|=(A.N n:ℝ)*|u-α n*v| := by
        rw [show (A.N n:ℝ)*u-α n*((A.N n:ℝ)*v)=(A.N n:ℝ)*(u-α n*v) by ring,
          abs_mul,abs_of_nonneg (A.N_pos n).le]
      simpa only [safeCell,hY,X,H,W,cap,T,α,Real.norm_eq_abs,hscale] using! hh'
    have he1 := guarded_cell_error
      (F:=fun n => (A.N n:ℝ)*∫ ω,T n ω ∂Measure.pi (fun _ : Fin (A.N n) => A.law n))
      k hα (by simpa only [mul_comm] using hsafe k y) hqlim
    have hsum := he0.add he1
    rw [zero_add] at hsum
    apply hsum.congr
    intro n
    dsimp only [L]
    ring
  have hbound : ∀ᶠ n in atTop,∀ k : ℕ,
      ‖safeCell i (A.law n) (A.N n) (c n) (g n) (cm n) (b n) (θ n)
        ((k+1:ℕ):ℤ) (k+1) q.val‖ ≤ C*Q^(k+1) ∧
      ‖safeCell i (A.law n) (A.N n) (c n) (g n) (cm n) (b n) (θ n)
        (-((k+1:ℕ):ℤ)) (k+1) q.val‖ ≤ C*Q^(k+1) := by
    filter_upwards [hcells] with n hn k
    have hone (y : ℤ) : ‖safeCell i (A.law n) (A.N n) (c n) (g n) (cm n)
        (b n) (θ n) y (k+1) q.val‖ ≤ C*Q^(k+1) := by
      let T : (Fin (A.N n) → RowRival) → ℝ := safeRow (X n) (H n) (W n) (A.Y n) (hWX n) (cap n) (θ n) y q.val (k+1)
      have hbT := (polynomial_sampled_ae (A.law n) (Nat.cast_pos.mp (A.N_pos n))
        (X n) (H n) (W n) (A.Y n) (hWX n) (hpositive n) (hcap n)
          (hlo.le.trans (hθ n).1) y q.val (k+1)).mono fun _ hx => hx.2
      have hTi : Integrable T (Measure.pi (fun _ : Fin (A.N n) => A.law n)) :=
        Integrable.of_mem_Icc 0 _ (measurable_safeRow (hX n) (hH n) (hW n)
          (A.measurable_Y n) _ _ _ _ _ _).aemeasurable hbT
      have hpoint : ∀ ω,0 ≤ rawGuard (xi i) (g n) (c n) (cm n) (b n) ω*T ω ∧
          rawGuard (xi i) (g n) (c n) (cm n) (b n) ω*T ω ≤ T ω := by
        intro ω
        have hg := rawGuard_bounds (xi i) (g n) (c n) (cm n) (b n) ω
        have ht := safeRow_nonneg (X n) (H n) (W n) (A.Y n) (hWX n)
          (cap n) (θ n) y q.val (k+1) ω
        exact ⟨mul_nonneg hg.1 ht, by
          simpa only [one_mul] using (mul_le_mul_of_nonneg_right hg.2 ht)⟩
      have hGi : Integrable (fun ω => rawGuard (xi i) (g n) (c n) (cm n) (b n) ω*T ω)
          (Measure.pi (fun _ : Fin (A.N n) => A.law n)) := by
        apply Integrable.of_mem_Icc 0 _
          ((measurable_rawGuard _ _ _ _ _).mul (measurable_safeRow (hX n) (hH n) (hW n)
            (A.measurable_Y n) _ _ _ _ _ _)).aemeasurable
        exact hbT.mono fun ω ht => ⟨(hpoint ω).1,(hpoint ω).2.trans ht.2⟩
      have hh := mul_le_mul_of_nonneg_left (integral_mono hGi hTi (fun ω => (hpoint ω).2))
        (A.N_pos n).le
      have hnonneg : 0 ≤ (A.N n:ℝ)*(∫ ω,rawGuard (xi i) (g n) (c n) (cm n) (b n) ω*T ω
          ∂Measure.pi (fun _ : Fin (A.N n) => A.law n)) :=
        mul_nonneg (A.N_pos n).le (integral_nonneg (fun ω => (hpoint ω).1))
      have hc := hh.trans (hn y (k+1) q)
      simp only [T,X,H,W,cap,hY] at hnonneg hc
      simpa only [safeCell,Q,η,Real.norm_of_nonneg hnonneg] using! hc
    exact ⟨hone _,hone _⟩
  have ht := moving_gamma_from_cell_errors
    (fun n => zeroCell i (A.law n) (A.N n) (c n) (g n) (b n) (θ n) q.val) α qn
    (fun n k => safeCell i (A.law n) (A.N n) (c n) (g n) (cm n) (b n) (θ n)
      ((k+1:ℕ):ℤ) (k+1) q.val)
    (fun n k => safeCell i (A.law n) (A.N n) (c n) (g n) (cm n) (b n) (θ n)
      (-((k+1:ℕ):ℤ)) (k+1) q.val)
    L hα hQ0.le hQ1 hC.le hqb hbound hzero (fun k => hfixed (k+1) _)
      (fun k => hfixed (k+1) _)
  simpa only [L,sourceGamma,← hlaw,α,qn,ratio] using ht

end FCAppendix.Affine.Uniform06.GuardedSampledMoments
