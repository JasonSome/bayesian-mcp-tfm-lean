import FCAppendix.Affine.Uniform06.EntryRawModerate
import FCAppendix.Affine.Uniform06.EntryLiteralDeficit

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryRawSignMoments

open MeasureTheory ProbabilityTheory Set LowBody
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.ClippedResidual
open FCAppendix.Affine.WeightedSampling FCAppendix.ExponentialTilt
open EntrySamplingLaw EntryEarlySourceLimits EntryRawCentral EntryProfileMean
open EntrySignFiber EntryParityRenewal EntryUntilting EntryRawTiltedFiber
open scoped BigOperators

variable {N : ℕ}

abbrev Mask (N : ℕ) := (Fin N → Bool) × (Fin N → ℝ)

def row (low sign : Fin N → Bool) (B : Fin N → ℝ) : Fin N → RowRival :=
  fun j => rawRowPoint (tag (low j,sign j),B j)

def weights (i : Row) (b l : ℝ) : (Fin N → RowRival) → Weights (Fin (N+1)) :=
  profileWeights (focalWeight i b l) (rawWeight i l)
    (focalWeight_bounds i b l) (rawWeight_bounds i l)

def hs (i : Row) (b : ℝ) : (Fin N → RowRival) → Fin (N+1) → ℝ :=
  profileH (1/2) (rawH i b)

def balanced (i : Row) (C : ℕ) (b : ℝ) (r : Fin N → RowRival) : ℝ :=
  (C:ℝ)-iidSum (RawMixedSource.demand (xi i) b) N r

def sampleDeficit (i : Row) (C : ℕ) (b l : ℝ)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) : ℝ :=
  balanced i C b x.1-sampled (weights i b l) (hs i b) RawMixedSource.draws x

def maskWeights (i : Row) (b l : ℝ) (x : Mask N) : Weights (Fin (N+1)) :=
  weights i b l (row x.1 (fun _ => false) x.2)

def maskH (i : Row) (b : ℝ) (x : Mask N) : Fin (N+1) → ℝ :=
  hs i b (row x.1 (fun _ => false) x.2)

def maskW (i : Row) (C : ℕ) (b : ℝ) (x : Mask N) : ℝ :=
  balanced i C b (row x.1 (fun _ => false) x.2)

lemma row_weight (i : Row) (l : ℝ) (low sign : Fin N → Bool) (B : Fin N → ℝ) (j : Fin N) :
    rawWeight i l (row low sign B j)=rawWeight i l (row low (fun _ => false) B j) := by
  cases hL : low j <;> cases hS : sign j <;>
    simp [row,rawWeight,RivalGood.lowerTest,rawRowPoint,tag,hL,hS]

lemma row_h (i : Row) (b : ℝ) (low sign : Fin N → Bool) (B : Fin N → ℝ) (j : Fin N) :
    rawH i b (row low sign B j)=rawH i b (row low (fun _ => false) B j) := by
  cases hL : low j <;> cases hS : sign j <;>
    simp [row,rawH,rawRowPoint,tag,hL,hS]

lemma row_demand (i : Row) (b : ℝ) (low sign : Fin N → Bool) (B : Fin N → ℝ) (j : Fin N) :
    RawMixedSource.demand (xi i) b (row low sign B j)=
      RawMixedSource.demand (xi i) b (row low (fun _ => false) B j) := by
  cases hL : low j <;> cases hS : sign j <;>
    simp [row,RawMixedSource.demand,rawRowPoint,tag,hL,hS]

lemma weights_row (i : Row) (b l : ℝ) (low sign : Fin N → Bool) (B : Fin N → ℝ) :
    weights i b l (row low sign B)=maskWeights i b l (low,B) := by
  apply Subtype.ext
  funext j
  refine Fin.cases rfl (fun j => ?_) j
  exact row_weight i l low sign B j

lemma hs_row (i : Row) (b : ℝ) (low sign : Fin N → Bool) (B : Fin N → ℝ) :
    hs i b (row low sign B)=maskH i b (low,B) := by
  funext j
  refine Fin.cases rfl (fun j => ?_) j
  exact row_h i b low sign B j

lemma balanced_row (i : Row) (C : ℕ) (b : ℝ) (low sign : Fin N → Bool) (B : Fin N → ℝ) :
    balanced i C b (row low sign B)=maskW i C b (low,B) := by
  unfold balanced maskW balanced iidSum
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact row_demand i b low sign B j

lemma classCount_row (k : Fin 4) (low sign : Fin N → Bool) (B : Fin N → ℝ) :
    classCount k (row low sign B)=classCount k (patternRow (fun j => tag (low j,sign j))) := by
  unfold classCount
  apply Finset.sum_congr rfl
  intro j _
  change (if tag (low j,sign j)=k then (1:ℕ) else 0)=
    (if tag (low j,sign j)=k then (1:ℕ) else 0)
  rfl

lemma draws_row (low sign : Fin N → Bool) (B : Fin N → ℝ) :
    RawMixedSource.draws (row low sign B)=
      EntryParityRenewal.imbalance (upperSet low).card (positiveCount low sign) := by
  unfold RawMixedSource.draws
  simp only [classCount_row,classCount_two,classCount_three]
  have hr : positiveCount low sign ≤ (upperSet low).card := PiBinomial.count_le _ _ _
  unfold EntryParityRenewal.imbalance
  split_ifs <;> omega

lemma measurable_weights (i : Row) (b l : ℝ) : Measurable (weights (N := N) i b l) :=
  measurable_profileWeights _ _ _ _ (measurable_rawWeight i l) N

lemma measurable_hs (i : Row) (b : ℝ) : Measurable (hs (N := N) i b) :=
  measurable_profileH _ (measurable_rawH i b) N

lemma measurable_balanced (i : Row) (C : ℕ) (b : ℝ) : Measurable (balanced (N := N) i C b) :=
  measurable_const.sub (measurable_iidSum (RawMixedSource.measurable_demand _ _) N)

lemma measurable_sampleDeficit (i : Row) (C : ℕ) (b l : ℝ) :
    Measurable (sampleDeficit (N := N) i C b l) :=
  ((measurable_balanced i C b).comp measurable_fst).sub
    (measurable_sampled _ _ _ (measurable_weights i b l) (measurable_hs i b)
      (RawMixedSource.measurable_draws N))

lemma measurable_deficitMoment {Ξ : Type*} [MeasurableSpace Ξ]
    {D : Ξ → ℝ} (hD : Measurable D) (k : ℕ) : Measurable (fun x => deficitMoment k (D x)) := by
  by_cases hk : k=0
  · simp only [hk,deficitMoment_zero]
    exact Measurable.ite (measurableSet_lt measurable_const hD) measurable_const measurable_const
  · simp only [deficitMoment,if_neg hk]
    exact (hD.max measurable_const).pow_const k

lemma sample_nonneg (i : Row) {b : ℝ} (hb : 0 < b) (l : ℝ)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    0 ≤ sampled (weights i b l) (hs i b) RawMixedSource.draws x := by
  apply EntryIIDCentral.selectedSum_nonneg (hs i b x.1) ?_
  intro j
  change 0 ≤ profileH (1/2) (rawH i b) x.1 j
  refine Fin.cases (by change (0:ℝ) ≤ 1/2; norm_num)
    (fun j => (rawH_bounds i hb (x.1 j)).1) j

lemma balanced_le_capacity (i : Row) (C : ℕ) {b : ℝ} (hb : 0 < b) (r : Fin N → RowRival) :
    balanced i C b r ≤ C := by
  have hh : 0 ≤ iidSum (RawMixedSource.demand (xi i) b) N r :=
    Finset.sum_nonneg fun j _ => (RawMixedSource.demand_bounds (xi_pos i) hb _).1
  dsimp only [balanced]
  linarith

lemma moment_le {D C : ℝ} (hC : 0 ≤ C) (hD : D ≤ C) (k : ℕ) :
    deficitMoment k D ≤ (C+1)^k := by
  by_cases hk : k=0
  · simp only [hk,deficitMoment_zero,pow_zero]
    split_ifs <;> norm_num
  · rw [deficitMoment,if_neg hk]
    exact pow_le_pow_left₀ (le_max_right _ _) (max_le (by linarith) (by linarith)) k

lemma sampleDeficit_moment_bound (i : Row) (C : ℕ) {b : ℝ} (hb : 0 < b) (l : ℝ)
    (k : ℕ) (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    |deficitMoment k (sampleDeficit i C b l x)| ≤ ((C:ℝ)+1)^k := by
  rw [abs_of_nonneg (deficitMoment_nonneg _ _)]
  exact moment_le (Nat.cast_nonneg C) (by
    have := balanced_le_capacity i C hb x.1
    have := sample_nonneg i hb l x
    dsimp only [sampleDeficit]
    linarith) k

def conditionalMoment (i : Row) (C : ℕ) (b l : ℝ) (k : ℕ) (r : Fin N → RowRival) : ℝ :=
  ∫ u : unitInterval,deficitMoment k (sampleDeficit i C b l (r,u))

lemma measurable_conditionalMoment (i : Row) (C : ℕ) (b l : ℝ) (k : ℕ) :
    Measurable (conditionalMoment (N := N) i C b l k) :=
  ((measurable_deficitMoment (measurable_sampleDeficit i C b l) k).stronglyMeasurable.integral_prod_right').measurable

lemma conditionalMoment_nonneg (i : Row) (C : ℕ) (b l : ℝ) (k : ℕ) (r : Fin N → RowRival) :
    0 ≤ conditionalMoment i C b l k r := integral_nonneg fun _ => deficitMoment_nonneg _ _

lemma conditionalMoment_bound (i : Row) (C : ℕ) {b : ℝ} (hb : 0 < b) (l : ℝ)
    (k : ℕ) (r : Fin N → RowRival) : |conditionalMoment i C b l k r| ≤ ((C:ℝ)+1)^k := by
  rw [abs_of_nonneg (conditionalMoment_nonneg _ _ _ _ _ _)]
  have hi : Integrable (fun u : unitInterval => deficitMoment k (sampleDeficit i C b l (r,u))) volume :=
    Integrable.of_bound ((measurable_deficitMoment (measurable_sampleDeficit i C b l) k).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable _
      (ae_of_all _ fun u => by simpa only [Real.norm_eq_abs] using sampleDeficit_moment_bound i C hb l k (r,u))
  have hh := integral_mono hi (integrable_const (((C:ℝ)+1)^k))
    (fun u => (le_abs_self _).trans (sampleDeficit_moment_bound i C hb l k (r,u)))
  simpa only [conditionalMoment,integral_const,probReal_univ,one_smul] using hh

theorem conditional_fair_sign_moment (i : Row) (C : ℕ) (b l : ℝ) (k : ℕ)
    (low : Fin N → Bool) (B : Fin N → ℝ) :
    (CommonList.iid fairSign N).expect (fun sign => conditionalMoment i C b l k (row low sign B))=
      fairMoment (maskWeights i b l (low,B)) (maskH i b (low,B))
        (upperSet low).card k (maskW i C b (low,B)) := by
  have he (sign : Fin N → Bool) : conditionalMoment i C b l k (row low sign B)=
      (pathLaw (maskWeights i b l (low,B))
        (EntryParityRenewal.imbalance (upperSet low).card (positiveCount low sign)) ∅).expect
        (fun p => deficitMoment k (maskW i C b (low,B)-
          selectedSum (maskH i b (low,B))
            (EntryParityRenewal.imbalance (upperSet low).card (positiveCount low sign)) p)) := by
    unfold conditionalMoment sampleDeficit sampled
    dsimp only
    rw [weights_row,hs_row,balanced_row,draws_row]
    exact integral_sampler_test (maskWeights i b l (low,B))
      (EntryParityRenewal.imbalance (upperSet low).card (positiveCount low sign))
      (fun p => deficitMoment k (maskW i C b (low,B)-selectedSum (maskH i b (low,B))
        (EntryParityRenewal.imbalance (upperSet low).card (positiveCount low sign)) p))
  simp_rw [he]
  exact actual_sign_fiber_moment low _ _ k _

theorem conditional_fair_weighted_moment (i : Row) (C : ℕ) (b l θ : ℝ) (k : ℕ)
    (low : Fin N → Bool) (B : Fin N → ℝ) :
    (CommonList.iid fairSign N).expect (fun sign =>
      Real.exp (-θ*balanced i C b (row low sign B))*conditionalMoment i C b l k (row low sign B))=
      Real.exp (-θ*maskW i C b (low,B))*
        fairMoment (maskWeights i b l (low,B)) (maskH i b (low,B))
          (upperSet low).card k (maskW i C b (low,B)) := by
  simp_rw [balanced_row]
  rw [FiniteLaw.expect_const_mul,conditional_fair_sign_moment]

lemma weighted_conditional_bound (i : Row) (C : ℕ) {b θ : ℝ} (hb : 0 < b) (hθ : 0 ≤ θ)
    (l : ℝ) (k : ℕ) (r : Fin N → RowRival) :
    |Real.exp (-θ*balanced i C b r)*conditionalMoment i C b l k r| ≤ ((C:ℝ)+1)^k := by
  by_cases hW : 0 < balanced i C b r
  · rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-θ*balanced i C b r) ≤ 1 := by
      simpa using Real.exp_le_exp.mpr (show -θ*balanced i C b r ≤ 0 by nlinarith)
    exact (mul_le_mul_of_nonneg_left (conditionalMoment_bound i C hb l k r) (Real.exp_pos _).le).trans
      (by nlinarith [pow_nonneg (show 0 ≤ (C:ℝ)+1 by positivity) k])
  · have hz : conditionalMoment i C b l k r=0 := by
      apply integral_eq_zero_of_ae
      exact ae_of_all _ fun u => deficitMoment_eq_zero_of_nonpos _ (by
        have hh := sample_nonneg i hb l (r,u)
        dsimp only [sampleDeficit]
        linarith [le_of_not_gt hW])
    simp [hz]
    positivity

section IntegratingSigns

lemma finite_expect_integral {α Ξ : Type*} [Fintype α] [MeasurableSpace Ξ]
    (Q : FiniteLaw α) (μ : Measure Ξ) (F : α → Ξ → ℝ)
    (hF : ∀ a,Integrable (F a) μ) :
    Q.expect (fun a => ∫ x, F a x ∂μ)=∫ x, Q.expect (fun a => F a x) ∂μ := by
  unfold FiniteLaw.expect
  rw [integral_finsetSum _ (fun a _ => (hF a).const_mul (Q.mass a))]
  simp only [integral_const_mul]

theorem original_tilted_fair_moment
    (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (C : ℕ) {b θ : ℝ} (hb : 0 < b) (hθ : 0 ≤ θ) (l : ℝ) (k N : ℕ) :
    (∫ r : Fin N → RowRival,
      Real.exp (-θ*balanced i C b r)*conditionalMoment i C b l k r
      ∂Measure.pi (fun _ => rawTilt i G b (-θ)))=
      (CommonList.iid (IndependentCounts.bernoulli (lowerMass i G b (-θ))
        (mass_bounds i G hb (-θ)).1.le (mass_bounds i G hb (-θ)).2.1.le) N).expect (fun low =>
        ∫ B : Fin N → ℝ,Real.exp (-θ*maskW i C b (low,B))*
          fairMoment (maskWeights i b l (low,B)) (maskH i b (low,B))
            (upperSet low).card k (maskW i C b (low,B))
            ∂Measure.pi (fun _ : Fin N => lowerTilt i G b (-θ))) := by
  let F : (Fin N → RowRival) → ℝ := fun r =>
    Real.exp (-θ*balanced i C b r)*conditionalMoment i C b l k r
  have hF : Measurable F := ((measurable_balanced i C b).const_mul (-θ)).exp.mul
    (measurable_conditionalMoment i C b l k)
  have hbound : ∀ r,|F r| ≤ ((C:ℝ)+1)^k := weighted_conditional_bound i C hb hθ l k
  have hh := (original_moderate_sign_fiber i G (θ := θ) hb N F hF hbound).2.2
  rw [hh]
  apply FiniteLaw.expect_congr
  intro low
  let ν := Measure.pi (fun _ : Fin N => lowerTilt i G b (-θ))
  letI := lowerTilt_probability i G hb (-θ)
  have hm (sign : Fin N → Bool) : Measurable (fun B : Fin N → ℝ => row low sign B) :=
    measurable_pi_lambda _ fun j => measurable_rawRowPoint.comp
      (measurable_const.prodMk (measurable_pi_apply j))
  have hi (sign : Fin N → Bool) : Integrable (fun B : Fin N → ℝ => F (row low sign B)) ν :=
    Integrable.of_bound (hF.comp (hm sign)).aestronglyMeasurable (((C:ℝ)+1)^k)
      (ae_of_all _ fun B => by simpa only [Real.norm_eq_abs] using hbound (row low sign B))
  change ((CommonList.iid fairSign N).expect (fun sign =>
    ∫ B, F (row low sign B) ∂ν))=_
  rw [finite_expect_integral _ ν _ hi]
  apply integral_congr_ae
  exact ae_of_all _ fun B => conditional_fair_weighted_moment i C b l θ k low B

theorem original_untilted_moment
    (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (C : ℕ) {b θ : ℝ} (hb : 0 < b) (hθ : 0 ≤ θ) (l : ℝ) (k N : ℕ) :
    (∫ x : EntryIIDCentral.Row (Ω := RowRival) N,
      deficitMoment k (sampleDeficit i C b l x)
      ∂EntryIIDCentral.rowLaw (RawMixedSource.source i G) N)=
      Real.exp ((N:ℝ)*cgf (RawMixedSource.demand (xi i) b) (RawMixedSource.source i G) (-θ)+θ*C)*
      (CommonList.iid (IndependentCounts.bernoulli (lowerMass i G b (-θ))
        (mass_bounds i G hb (-θ)).1.le (mass_bounds i G hb (-θ)).2.1.le) N).expect (fun low =>
        ∫ B : Fin N → ℝ,Real.exp (-θ*maskW i C b (low,B))*
          fairMoment (maskWeights i b l (low,B)) (maskH i b (low,B))
            (upperSet low).card k (maskW i C b (low,B))
            ∂Measure.pi (fun _ : Fin N => lowerTilt i G b (-θ))) := by
  have hi : Integrable (fun x : EntryIIDCentral.Row (Ω := RowRival) N =>
      deficitMoment k (sampleDeficit i C b l x))
      (EntryIIDCentral.rowLaw (RawMixedSource.source i G) N) :=
    Integrable.of_bound (measurable_deficitMoment (measurable_sampleDeficit i C b l) k).aestronglyMeasurable _
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using sampleDeficit_moment_bound i C hb l k x)
  rw [EntryIIDCentral.rowLaw,integral_prod _ hi]
  have hh := exact_reverse_iid_moment (RawMixedSource.source i G)
    (RawMixedSource.demand (xi i) b) N (conditionalMoment i C b l k) θ (C:ℝ)
    (RawMixedSource.measurable_demand _ _)
    (ae_of_all _ (RawMixedSource.demand_bounds (xi_pos i) hb))
  change (∫ r, conditionalMoment i C b l k r ∂Measure.pi (fun _ : Fin N => RawMixedSource.source i G))=_
  rw [hh]
  congr 1
  exact original_tilted_fair_moment i G C hb hθ l k N

end IntegratingSigns
end FCAppendix.Affine.Uniform06.EntryRawSignMoments
