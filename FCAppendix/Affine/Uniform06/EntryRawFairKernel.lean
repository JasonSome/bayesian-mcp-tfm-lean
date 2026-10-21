import FCAppendix.Affine.Uniform06.EntryModerateAveraging
import FCAppendix.Affine.Uniform06.EntryLiteralResponseMoments

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryRawFairKernel
open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07 FCAppendix.ExponentialTilt
open FCAppendix.Affine.WeightedSampling
open EntryEarlySourceLimits EntryRawSignMoments EntrySignFiber EntryParityRenewal
open EntryUntilting EntryLaplace EntryModerateAveraging EntryRawTiltedFiber
open scoped BigOperators

variable {N : ℕ}

def upper (r : RowRival) : ℝ := if r.1=0 then 0 else 1

def upperCount (r : Fin N → RowRival) : ℕ := ∑ j,if (r j).1=0 then 0 else 1

lemma upper_bounds (r : RowRival) : upper r∈Icc (0:ℝ) 1 := by
  unfold upper
  split_ifs <;> norm_num

lemma measurable_upper : Measurable upper :=
  (measurable_of_countable (fun j : Fin 4 => if j=0 then (0:ℝ) else 1)).comp measurable_fst

lemma measurable_upperCount : Measurable (upperCount (N := N)) := by
  unfold upperCount
  exact Finset.measurable_sum _ fun j _ =>
    (measurable_of_countable (fun t : Fin 4 => if t=0 then (0:ℕ) else 1)).comp
      (measurable_fst.comp (measurable_pi_apply j))

lemma upperCount_cast (r : Fin N → RowRival) : (upperCount r:ℝ)=∑ j,upper (r j) := by
  simp [upperCount,upper,Nat.cast_sum,Nat.cast_ite]

lemma upperCount_le (r : Fin N → RowRival) : upperCount r ≤ N := by
  have hh : upperCount r ≤ ∑ _ : Fin N,1 := by
    apply Finset.sum_le_sum
    intro j _
    split_ifs <;> omega
  simpa using hh

lemma upperCount_row (low sign : Fin N → Bool) (B : Fin N → ℝ) :
    upperCount (row low sign B)=(EntrySignFiber.upperSet low).card := by
  unfold upperCount EntrySignFiber.upperSet
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _
  cases hL : low j <;> cases hS : sign j <;>
    simp [row,rawRowPoint,tag,hL,hS]

def kernel (i : Row) (C : ℕ) (b l : ℝ) (k : ℕ) (r : Fin N → RowRival) : ℝ :=
  fairMoment (weights i b l r) (hs i b r) (upperCount r) k (balanced i C b r)

def weightedKernel (i : Row) (C : ℕ) (b l θ : ℝ) (k : ℕ) (r : Fin N → RowRival) : ℝ :=
  Real.exp (-θ*balanced i C b r)*kernel i C b l k r

lemma measurable_kernel (i : Row) (C : ℕ) (b l : ℝ) (k : ℕ) :
    Measurable (kernel (N := N) i C b l k) :=
  measurable_fairMoment _ _ _ _ (measurable_weights i b l) (measurable_hs i b)
    measurable_upperCount (measurable_balanced i C b) k

lemma measurable_weightedKernel (i : Row) (C : ℕ) (b l θ : ℝ) (k : ℕ) :
    Measurable (weightedKernel (N := N) i C b l θ k) :=
  ((measurable_balanced i C b).const_mul (-θ)).exp.mul (measurable_kernel i C b l k)

lemma hs_nonneg (i : Row) {b : ℝ} (hb : 0 < b) (r : Fin N → RowRival) :
    ∀ j,0 ≤ hs i b r j := fun j => Fin.cases (by norm_num [hs, EntryProfileMean.profileH])
      (fun j => (rawH_bounds i hb (r j)).1) j

lemma kernel_nonneg (i : Row) (C : ℕ) (b l : ℝ) (k : ℕ) (r : Fin N → RowRival) :
    0 ≤ kernel i C b l k r := fairMoment_nonneg _ _ _ _ _

lemma kernel_le_initial (i : Row) (C : ℕ) {b : ℝ} (hb : 0 < b) (l : ℝ)
    (k : ℕ) (r : Fin N → RowRival) : kernel i C b l k r ≤ deficitMoment k (balanced i C b r) :=
  fairMoment_le_initial _ _ (hs_nonneg i hb r) _ _ _

lemma kernel_bound (i : Row) (C : ℕ) {b : ℝ} (hb : 0 < b) (l : ℝ)
    (k : ℕ) (r : Fin N → RowRival) : |kernel i C b l k r| ≤ ((C:ℝ)+1)^k := by
  rw [abs_of_nonneg (kernel_nonneg _ _ _ _ _ _)]
  exact (kernel_le_initial i C hb l k r).trans
    (moment_le (Nat.cast_nonneg C) (balanced_le_capacity i C hb r) k)

lemma weightedKernel_nonneg (i : Row) (C : ℕ) (b l θ : ℝ) (k : ℕ) (r : Fin N → RowRival) :
    0 ≤ weightedKernel i C b l θ k r := mul_nonneg (Real.exp_pos _).le (kernel_nonneg _ _ _ _ _ _)

lemma weightedKernel_bound (i : Row) (C : ℕ) {b θ : ℝ} (hb : 0 < b) (hθ : 0 ≤ θ) (l : ℝ)
    (k : ℕ) (r : Fin N → RowRival) : |weightedKernel i C b l θ k r| ≤ ((C:ℝ)+1)^k := by
  by_cases hW : 0 < balanced i C b r
  · have hexp : Real.exp (-θ*balanced i C b r) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    rw [weightedKernel,abs_mul,abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (kernel_bound i C hb l k r) (Real.exp_pos _).le).trans
      (by nlinarith [pow_nonneg (show 0 ≤ (C:ℝ)+1 by positivity) k])
  · have hz : kernel i C b l k r=0 :=
      fairMoment_eq_zero_of_nonpos _ _ (hs_nonneg i hb r) _ _ (le_of_not_gt hW)
    simp [weightedKernel,hz]
    positivity

lemma kernel_row (i : Row) (C : ℕ) (b l : ℝ) (k : ℕ)
    (low sign : Fin N → Bool) (B : Fin N → ℝ) :
    kernel i C b l k (row low sign B)=
      fairMoment (maskWeights i b l (low,B)) (maskH i b (low,B))
        (EntrySignFiber.upperSet low).card k (maskW i C b (low,B)) := by
  rw [kernel,weights_row,hs_row,upperCount_row,balanced_row]

theorem tilted_moment_eq_raw_kernel
    (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (C : ℕ) {b θ : ℝ} (hb : 0 < b) (hθ : 0 ≤ θ) (l : ℝ) (k N : ℕ) :
    (∫ r : Fin N → RowRival,Real.exp (-θ*balanced i C b r)*conditionalMoment i C b l k r
      ∂Measure.pi (fun _ : Fin N => rawTilt i G b (-θ)))=
    (∫ r : Fin N → RowRival,weightedKernel i C b l θ k r
      ∂Measure.pi (fun _ : Fin N => rawTilt i G b (-θ))) := by
  rw [original_tilted_fair_moment i G C hb hθ l k N]
  have hh := (original_moderate_sign_fiber (θ := θ) i G hb N (weightedKernel i C b l θ k)
    (measurable_weightedKernel i C b l θ k) (weightedKernel_bound i C hb hθ l k)).2.2
  rw [hh]
  apply FiniteLaw.expect_congr
  intro low
  symm
  calc
    _ = (CommonList.iid fairSign N).expect (fun _ : Fin N → Bool =>
        ∫ B : Fin N → ℝ, Real.exp (-θ*maskW i C b (low,B))*
          fairMoment (maskWeights i b l (low,B)) (maskH i b (low,B))
            (EntrySignFiber.upperSet low).card k (maskW i C b (low,B))
          ∂Measure.pi (fun _ : Fin N => lowerTilt i G b (-θ))) := by
      apply FiniteLaw.expect_congr
      intro sign
      apply integral_congr_ae
      exact ae_of_all _ fun B => by
        change weightedKernel i C b l θ k (row low sign B)=_
        rw [weightedKernel,balanced_row,kernel_row]
    _ = _ := FiniteLaw.expect_const _ _

theorem untilted_moment_eq_raw_kernel
    (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (C : ℕ) {b θ : ℝ} (hb : 0 < b) (hθ : 0 ≤ θ) (l : ℝ) (k N : ℕ) :
    (∫ x : EntryIIDCentral.Row (Ω := RowRival) N,
      deficitMoment k (sampleDeficit i C b l x) ∂EntryIIDCentral.rowLaw (RawMixedSource.source i G) N)=
      Real.exp ((N:ℝ)*cgf (RawMixedSource.demand (xi i) b) (RawMixedSource.source i G) (-θ)+θ*C)*
        (∫ r : Fin N → RowRival,weightedKernel i C b l θ k r
          ∂Measure.pi (fun _ : Fin N => rawTilt i G b (-θ))) := by
  rw [original_untilted_moment i G C hb hθ l k N]
  congr 1
  rw [← tilted_moment_eq_raw_kernel i G C hb hθ l k N,
    original_tilted_fair_moment i G C hb hθ l k N]

theorem original_upper_mean (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G] :
    (∫ r,upper r ∂ RawMixedSource.source i G)=1-cutoff i := by
  letI : IsProbabilityMeasure (G.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  rw [RawMixedSource.source,integral_rivalLaw (cutoff i) (cutoff_pos i).le
    (cutoff_lt_one i).le (G.map Prod.snd) upper measurable_upper]
  · have h2 : upper ((2:Fin 4),(0:ℝ))=1 := by
      simp only [upper,show (2:Fin 4)≠0 by decide,if_false]
    have h3 : upper ((3:Fin 4),(0:ℝ))=1 := by
      simp only [upper,show (3:Fin 4)≠0 by decide,if_false]
    rw [h2,h3]
    simp only [upper,ite_true,integral_zero,mul_zero,mul_one,zero_add]
    ring
  · simp [upper]

end FCAppendix.Affine.Uniform06.EntryRawFairKernel
