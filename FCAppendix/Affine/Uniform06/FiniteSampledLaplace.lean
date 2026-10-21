import FCAppendix.Affine.Uniform06.SamplerDenominatorLimit

noncomputable section
namespace FCAppendix.Affine.Uniform06.FiniteSampledLaplace

open MeasureTheory Set Filter
open scoped Topology BigOperators
open FCAppendix.Affine.WeightedSampling
open PathNumerator FiniteMarkedExchangeability SelectedLaplaceLimit
open SamplerDenominatorLimit RareEmpiricalReplacement

variable {Ω : Type*} [MeasurableSpace Ω]

def rowWeights {N : ℕ} (w : Ω → ℝ) (hw : ∀ x,w x ∈ Icc (0:ℝ) 1)
    (ω : Fin N → Ω) : Weights (Fin N) := ⟨fun j => w (ω j),fun j => hw (ω j)⟩

def tupleTest (X h : Ω → ℝ) (Y : Ω → ℤ) (cap θ : ℝ) (y : ℤ) (r : ℕ)
    {N k : ℕ} (ω : Fin N → Ω) (v : Fin k → Fin N) : ℝ :=
  if sumY Y ω=y ∧ 0 < cap-sumX X ω-∑ j,h (ω (v j)) then
    Real.exp (-θ*(cap-sumX X ω))*(cap-sumX X ω-∑ j,h (ω (v j)))^r else 0

def sampledRow {N : ℕ} [Nonempty (Fin N)] (X h w : Ω → ℝ) (Y : Ω → ℤ)
    (hw : ∀ x,w x ∈ Icc (0:ℝ) 1) (cap θ : ℝ) (y : ℤ) (r k : ℕ)
    (ω : Fin N → Ω) : ℝ :=
  (pathLaw (rowWeights w hw ω) k ∅).expect (fun p => tupleTest X h Y cap θ y r ω (tuple k p))

def numeratorRow {N : ℕ} [Nonempty (Fin N)] (X h w : Ω → ℝ) (Y : Ω → ℤ)
    (hw : ∀ x,w x ∈ Icc (0:ℝ) 1) (cap θ : ℝ) (y : ℤ) (r k : ℕ)
    (ω : Fin N → Ω) : ℝ :=
  numeratorSum (rowWeights w hw ω) k ∅
    (fun p => tupleTest X h Y cap θ y r ω (tuple k p))/(N:ℝ)^k

lemma measurable_tupleTest {X h : Ω → ℝ} {Y : Ω → ℤ}
    (hX : Measurable X) (hh : Measurable h) (hY : Measurable Y)
    (cap θ : ℝ) (y : ℤ) (r : ℕ) {N k : ℕ} (v : Fin k → Fin N) :
    Measurable (fun ω : Fin N → Ω => tupleTest X h Y cap θ y r ω v) := by
  have hx : Measurable (fun ω : Fin N → Ω => ∑ j, X (ω j)) := Finset.measurable_sum Finset.univ (fun j _ => hX.comp (measurable_pi_apply j))
  have hy : Measurable (fun ω : Fin N → Ω => ∑ j, Y (ω j)) := Finset.measurable_sum Finset.univ (fun j _ => hY.comp (measurable_pi_apply j))
  have hh' : Measurable (fun ω : Fin N → Ω => ∑ j, h (ω (v j))) := Finset.measurable_sum Finset.univ
    (fun j _ => hh.comp (measurable_pi_apply (v j)))
  unfold tupleTest sumX sumY
  exact Measurable.ite ((measurableSet_eq_fun hy measurable_const).inter
    (measurableSet_lt measurable_const ((measurable_const.sub hx).sub hh')))
    (((measurable_const.sub hx).const_mul (-θ)).exp.mul
      (((measurable_const.sub hx).sub hh').pow_const r)) measurable_const

omit [MeasurableSpace Ω] in
lemma tupleTest_nonneg (X h : Ω → ℝ) (Y : Ω → ℤ)
    (cap θ : ℝ) (y : ℤ) (r : ℕ) {N k : ℕ} (ω : Fin N → Ω) (v : Fin k → Fin N) :
    0 ≤ tupleTest X h Y cap θ y r ω v := by
  unfold tupleTest
  split_ifs with hp
  · exact mul_nonneg (Real.exp_pos _).le (pow_nonneg hp.2.le _)
  · rfl

omit [MeasurableSpace Ω] in
lemma tupleTest_polynomial {X h : Ω → ℝ} {Y : Ω → ℤ} {cap θ : ℝ}
    {N k : ℕ} (ω : Fin N → Ω) (v : Fin k → Fin N)
    (hX : ∀ j,0 ≤ X (ω j)) (hh : ∀ j,0 ≤ h (ω j))
    (hcap : cap ≤ (N:ℝ)) (hθ : 0 ≤ θ) (y : ℤ) (r : ℕ) :
    tupleTest X h Y cap θ y r ω v ≤ (N:ℝ)^r := by
  have hx : 0 ≤ sumX X ω := Finset.sum_nonneg (fun j _ => hX j)
  have hs : 0 ≤ ∑ j,h (ω (v j)) := Finset.sum_nonneg (fun j _ => hh (v j))
  unfold tupleTest
  split_ifs with hp
  · have hW : 0 ≤ cap-sumX X ω := by linarith [hp.2]
    have hD : cap-sumX X ω-∑ j,h (ω (v j)) ≤ (N:ℝ) := by linarith
    have he : Real.exp (-θ*(cap-sumX X ω)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ) hW)
    exact (mul_le_mul_of_nonneg_right he (pow_nonneg hp.2.le r)).trans
      (by simpa using pow_le_pow_left₀ hp.2.le hD r)
  · positivity

lemma measurable_sampledRow {N : ℕ} [Nonempty (Fin N)]
    {X h w : Ω → ℝ} {Y : Ω → ℤ}
    (hX : Measurable X) (hh : Measurable h) (hw : Measurable w) (hY : Measurable Y)
    (hbw : ∀ x,w x ∈ Icc (0:ℝ) 1) (cap θ : ℝ) (y : ℤ) (r k : ℕ) :
    Measurable (sampledRow X h w Y hbw cap θ y r k : (Fin N → Ω) → ℝ) := by
  unfold sampledRow FCAppendix.FiniteLaw.expect
  apply Finset.measurable_sum
  intro p _
  exact (LiteralCoarseMeasurable.measurable_path_mass (fun ω => rowWeights w hbw ω)
    (fun j => hw.comp (measurable_pi_apply j)) k ∅ p).mul
      (measurable_tupleTest hX hh hY cap θ y r (tuple k p))

omit [MeasurableSpace Ω] in
theorem numeratorRow_eq_embeddings {N : ℕ} [Nonempty (Fin N)]
    (X h w : Ω → ℝ) (Y : Ω → ℤ) (hw : ∀ x,w x ∈ Icc (0:ℝ) 1)
    (cap θ : ℝ) (y : ℤ) (r k : ℕ) (ω : Fin N → Ω) :
    numeratorRow X h w Y hw cap θ y r k ω=
      (∑ f : Fin k ↪ Fin N,markedFunctional X h w Y cap θ y r ω
        (fun j => ω (f j)))/(N:ℝ)^k := by
  rw [numeratorRow,numeratorSum_eq_embeddings]
  rfl

lemma measurable_numeratorRow {N : ℕ} [Nonempty (Fin N)]
    {X h w : Ω → ℝ} {Y : Ω → ℤ}
    (hX : Measurable X) (hh : Measurable h) (hw : Measurable w) (hY : Measurable Y)
    (hbw : ∀ x,w x ∈ Icc (0:ℝ) 1) (cap θ : ℝ) (y : ℤ) (r k : ℕ) :
    Measurable (numeratorRow X h w Y hbw cap θ y r k : (Fin N → Ω) → ℝ) := by
  change Measurable (fun ω : Fin N → Ω => numeratorRow X h w Y hbw cap θ y r k ω)
  simp_rw [numeratorRow_eq_embeddings]
  apply Measurable.div_const
  exact Finset.measurable_sum _ fun f _ =>
    RawMarkedLaplace.measurable_markedFunctional hX hh hw hY cap θ y r f

theorem integral_numeratorRow {N : ℕ} [Nonempty (Fin N)] (μ : Measure Ω)
    (X h w : Ω → ℝ) (Y : Ω → ℤ) (hw : ∀ x,w x ∈ Icc (0:ℝ) 1)
    (cap θ : ℝ) (y : ℤ) (r k : ℕ) :
    (∫ ω : Fin N → Ω,numeratorRow X h w Y hw cap θ y r k ω
      ∂Measure.pi (fun _ : Fin N => μ))=
        numeratorMoment μ X h w Y N cap θ y r k := by
  simp_rw [numeratorRow_eq_embeddings]
  rw [integral_div]
  rfl

omit [MeasurableSpace Ω] in

theorem row_polynomial_bounds {N : ℕ} [Nonempty (Fin N)]
    (X h w : Ω → ℝ) (Y : Ω → ℤ) (hw : ∀ x,w x ∈ Icc (0:ℝ) 1)
    (cap θ : ℝ) (y : ℤ) (r k : ℕ) (ω : Fin N → Ω)
    (hN : 0 < N) (hX : ∀ j,0 ≤ X (ω j)) (hh : ∀ j,0 ≤ h (ω j))
    (hcap : cap ≤ (N:ℝ)) (hθ : 0 ≤ θ) :
    (0 ≤ sampledRow X h w Y hw cap θ y r k ω ∧
      sampledRow X h w Y hw cap θ y r k ω ≤ (N:ℝ)^r) ∧
    (0 ≤ numeratorRow X h w Y hw cap θ y r k ω ∧
      numeratorRow X h w Y hw cap θ y r k ω ≤ (N:ℝ)^r) := by
  have hNr : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have hF (v : Fin k → Fin N) := tupleTest_nonneg X h Y cap θ y r ω v
  have hFb (v : Fin k → Fin N) := tupleTest_polynomial (Y := Y) ω v hX hh hcap hθ y r
  have hnum (f : Fin k ↪ Fin N) :
      markedFunctional X h w Y cap θ y r ω (fun j => ω (f j)) ∈ Icc (0:ℝ) ((N:ℝ)^r) := by
    have hp0 : 0 ≤ ∏ j,w (ω (f j)) := Finset.prod_nonneg (fun j _ => (hw _).1)
    have hp1 : (∏ j,w (ω (f j))) ≤ 1 :=
      Finset.prod_le_one (fun j _ => (hw _).1) (fun j _ => (hw _).2)
    change (∏ j,w (ω (f j)))*tupleTest X h Y cap θ y r ω f ∈ _
    exact ⟨mul_nonneg hp0 (hF f),(mul_le_mul_of_nonneg_left (hFb f) hp0).trans
      (by simpa using mul_le_mul_of_nonneg_right hp1 (pow_nonneg hNr.le r))⟩
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · exact expect_nonneg _ _ (fun p => hF (tuple k p))
  · exact expect_le_const _ _ _ (fun p _ => hFb (tuple k p))
  · rw [numeratorRow_eq_embeddings]
    exact div_nonneg (Finset.sum_nonneg (fun f _ => (hnum f).1)) (pow_pos hNr k).le
  · rw [numeratorRow_eq_embeddings]
    apply (div_le_iff₀ (pow_pos hNr k)).mpr
    calc
      _ ≤ ∑ _f : Fin k ↪ Fin N,(N:ℝ)^r := Finset.sum_le_sum (fun f _ => (hnum f).2)
      _ = ((N.descFactorial k:ℕ):ℝ)*(N:ℝ)^r := by simp [Fintype.card_embedding_eq]
      _ ≤ (N:ℝ)^k*(N:ℝ)^r := mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.descFactorial_le_pow N k) (pow_nonneg hNr.le r)
      _ = _ := by ring

omit [MeasurableSpace Ω] in
theorem actual_pointwise_denominator {N : ℕ} [Nonempty (Fin N)]
    (X h w : Ω → ℝ) (Y : Ω → ℤ) (hw : ∀ x,w x ∈ Icc (0:ℝ) 1)
    (cap θ : ℝ) (y : ℤ) (r k : ℕ) (ω : Fin N → Ω)
    (hN : 0 < N) {c z : ℝ} (hc : 0 < c) (hz : c ≤ z)
    (hguard : c ≤ empirical w N ω-(k:ℝ)/(N:ℝ)) :
    |sampledRow X h w Y hw cap θ y r k ω-
      numeratorRow X h w Y hw cap θ y r k ω/z^k| ≤
      ((k:ℝ)*(c⁻¹)^(k-1)/c^2)*numeratorRow X h w Y hw cap θ y r k ω*
        (|empirical w N ω-z|+(k:ℝ)/(N:ℝ)) := by
  exact actual_denominator_error (rowWeights w hw ω) k
    (fun p => tupleTest X h Y cap θ y r ω (tuple k p))
    (fun p => tupleTest_nonneg X h Y cap θ y r ω (tuple k p))
    (Nat.cast_pos.mpr hN) hc hguard hz

theorem sampled_limit_from_numerator
    (μ : ℕ → Measure Ω) [∀ n,IsProbabilityMeasure (μ n)]
    (N : ℕ → ℕ) [∀ n,Nonempty (Fin (N n))]
    (hNpos : ∀ n,0 < N n) (hN : Tendsto N atTop atTop)
    (X h w : ℕ → Ω → ℝ) (Y : ℕ → Ω → ℤ)
    (hX : ∀ n,Measurable (X n)) (hh : ∀ n,Measurable (h n))
    (hw : ∀ n,Measurable (w n)) (hY : ∀ n,Measurable (Y n))
    (hbw : ∀ n x,w n x ∈ Icc (0:ℝ) 1)
    (hpositive : ∀ n,∀ᵐ x ∂μ n,0 ≤ X n x ∧ 0 ≤ h n x)
    (cap θn : ℕ → ℝ) (hcap : ∀ n,cap n ≤ (N n:ℝ))
    (hθ : ∀ n,0 ≤ θn n) (y : ℤ) (r k : ℕ)
    {z L : ℝ} (hz : 0 < z)
    (hmean : Tendsto (fun n => ∫ x,w n x ∂μ n) atTop (𝓝 z))
    (hnum : Tendsto (fun n => (N n:ℝ)*numeratorMoment (μ n) (X n) (h n) (w n)
      (Y n) (N n) (cap n) (θn n) y r k) atTop (𝓝 L)) :
    Tendsto (fun n => (N n:ℝ)*∫ ω : Fin (N n) → Ω,
      sampledRow (X n) (h n) (w n) (Y n) (hbw n) (cap n) (θn n) y r k ω
        ∂Measure.pi (fun _ : Fin (N n) => μ n)) atTop (𝓝 (L/z^k)) := by
  let Q := fun n => Measure.pi (fun _ : Fin (N n) => μ n)
  let P : (n : ℕ) → (Fin (N n) → Ω) → ℝ := fun n => sampledRow (X n) (h n) (w n) (Y n) (hbw n) (cap n) (θn n) y r k
  let T : (n : ℕ) → (Fin (N n) → Ω) → ℝ := fun n => numeratorRow (X n) (h n) (w n) (Y n) (hbw n) (cap n) (θn n) y r k
  have hPm (n : ℕ) : Measurable (P n) :=
    measurable_sampledRow (hX n) (hh n) (hw n) (hY n) (hbw n) _ _ _ _ _
  have hTm (n : ℕ) : Measurable (T n) :=
    measurable_numeratorRow (hX n) (hh n) (hw n) (hY n) (hbw n) _ _ _ _ _
  have hboth (n : ℕ) : ∀ᵐ ω ∂Q n,
      (0 ≤ P n ω ∧ P n ω ≤ (N n:ℝ)^r) ∧ (0 ≤ T n ω ∧ T n ω ≤ (N n:ℝ)^r) := by
    have hall (j : Fin (N n)) :=
      (measurePreserving_eval (fun _ : Fin (N n) => μ n) j).quasiMeasurePreserving.ae
        (hpositive n)
    filter_upwards [ae_all_iff.mpr hall] with ω hω
    exact row_polynomial_bounds (X n) (h n) (w n) (Y n) (hbw n) _ _ _ _ _ ω
      (hNpos n) (fun j => (hω j).1) (fun j => (hω j).2) (hcap n) (hθ n)
  have hPb (n : ℕ) : ∀ᵐ ω ∂Q n,0 ≤ P n ω ∧ P n ω ≤ 1*(N n:ℝ)^r := by
    simpa only [one_mul] using (hboth n).mono fun _ h => h.1
  have hTb (n : ℕ) : ∀ᵐ ω ∂Q n,0 ≤ T n ω ∧ T n ω ≤ 1*(N n:ℝ)^r := by
    simpa only [one_mul] using (hboth n).mono fun _ h => h.2
  have hrare : Tendsto (fun n => (N n:ℝ)*∫ ω,T n ω ∂Q n) atTop (𝓝 L) := by
    simpa only [T,Q,integral_numeratorRow] using hnum
  have herr := relative_denominator_replacement μ N hNpos hN w hw
    (fun n => ae_of_all _ (hbw n)) P T hPm hTm k r (by norm_num : (0:ℝ) ≤ 1)
    hz hPb hTb hrare hmean (fun n => ae_of_all _ fun ω hg =>
      actual_pointwise_denominator (X n) (h n) (w n) (Y n) (hbw n) _ _ _ _ _ ω
        (hNpos n) (by positivity : 0 < z/4) (by linarith : z/4 ≤ z) hg)
  have hPi (n : ℕ) : Integrable (P n) (Q n) :=
    Integrable.of_mem_Icc 0 _ (hPm n).aemeasurable (hPb n)
  have hTi (n : ℕ) : Integrable (T n) (Q n) :=
    Integrable.of_mem_Icc 0 _ (hTm n).aemeasurable (hTb n)
  have hbound (n : ℕ) :
      |(N n:ℝ)*(∫ ω,P n ω ∂Q n)-(N n:ℝ)*(∫ ω,T n ω ∂Q n)/z^k| ≤
        (N n:ℝ)*∫ ω,|P n ω-T n ω/z^k| ∂Q n := by
    have hid : (N n:ℝ)*(∫ ω,P n ω ∂Q n)-(N n:ℝ)*(∫ ω,T n ω ∂Q n)/z^k=
        (N n:ℝ)*∫ ω,P n ω-T n ω/z^k ∂Q n := by
      rw [integral_sub (hPi n) ((hTi n).div_const _),integral_div]
      ring
    rw [hid,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (fun ω => P n ω-T n ω/z^k)
  have hdiff : Tendsto (fun n => (N n:ℝ)*(∫ ω,P n ω ∂Q n)-
      (N n:ℝ)*(∫ ω,T n ω ∂Q n)/z^k) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    exact squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
      (Eventually.of_forall hbound) herr
  have hh := hdiff.add (hrare.div_const (z^k))
  simpa only [sub_add_cancel,zero_add] using hh

theorem fixed_imbalance_sampled_moments (A : MixedIntervalLLT.CenteredArray Ω)
    [∀ n,Nonempty (Fin (A.N n))] (hgap : A.CompactGap)
    (U h w : ℕ → Ω → ℝ) (r cap θn : ℕ → ℝ)
    (hU : ∀ n,Measurable (U n)) (hh : ∀ n,Measurable (h n))
    (hw : ∀ n,Measurable (w n))
    (hbU : ∀ n x,U n x ∈ Icc (0:ℝ) 1)
    (hbh : ∀ n x,|h n x| ≤ 1) (hbw : ∀ n x,w n x ∈ Icc (0:ℝ) 1)
    (hbal : ∀ n x,w n x ≠ 0 → U n x+h n x=1/2 ∧ A.Y n x=0)
    (hhpos : ∀ n,∀ᵐ x ∂A.law n,0 ≤ h n x)
    (hr : ∀ n,r n ∈ Icc (0:ℝ) 1)
    (hcenter : ∀ n,∀ᵐ x ∂A.law n,A.X n x=U n x-r n)
    (hmatch : ∀ᶠ n in atTop,cap n=(A.N n:ℝ)*r n)
    (hcap : ∀ n,cap n ≤ (A.N n:ℝ))
    (k : ℕ) (y : ℤ) {θ lo hi a z : ℝ} (hlo : 0 < lo)
    (hbracket : ∀ n,lo ≤ θn n ∧ θn n ≤ hi)
    (hθn : Tendsto θn atTop (𝓝 θ)) (hθ : 0 < θ) (hz : 0 < z)
    (hwmean : Tendsto (fun n => ∫ x,w n x ∂A.law n) atTop (𝓝 z))
    (hmean : Tendsto (fun n => ∫ x,w n x*Real.exp (-θn n*h n x) ∂A.law n)
      atTop (𝓝 a)) :
    ∀ q : Fin 3,Tendsto (fun n => (A.N n:ℝ)*∫ ω : Fin (A.N n) → Ω,
      sampledRow (U n) (h n) (w n) (A.Y n) (hbw n) (cap n) (θn n) y q.val k ω
        ∂Measure.pi (fun _ : Fin (A.N n) => A.law n)) atTop
      (𝓝 ((a^k*(MixedIntervalLLT.density A.vX A.vY*
        (q.val.factorial:ℝ)/θ^(q.val+1)))/z^k)) := by
  have ht := distinct_numerator_moments A hgap U h w r cap θn hU hh hw hbU hbh hbw
    hbal hr hcenter hmatch k y hlo hbracket hθn hθ hmean
  intro q
  have hnum : Tendsto (fun n => (A.N n:ℝ)*numeratorMoment (A.law n) (U n) (h n) (w n)
      (A.Y n) (A.N n) (cap n) (θn n) y q.val k) atTop
      (𝓝 (a^k*(MixedIntervalLLT.density A.vX A.vY*(q.val.factorial:ℝ)/θ^(q.val+1)))) := by
    fin_cases q
    · simpa using ht.1
    · simpa using ht.2.1
    · simpa only [Fin.val_mk, Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_one, mul_one, Nat.reduceAdd, mul_div_assoc] using ht.2.2
  apply sampled_limit_from_numerator A.law A.N
    (fun n => Nat.cast_pos.mp (A.N_pos n)) A.market U h w A.Y hU hh hw A.measurable_Y hbw
    _ cap θn hcap (fun n => hlo.le.trans (hbracket n).1) y q.val k hz hwmean hnum
  intro n
  filter_upwards [hhpos n] with x hx
  exact ⟨(hbU n x).1,hx⟩

end FCAppendix.Affine.Uniform06.FiniteSampledLaplace
