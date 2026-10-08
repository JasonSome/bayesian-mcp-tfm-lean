import FCAppendix.Exclusive.CompletionActualAdapters
import FCAppendix.Exclusive.InverseBidConcentration
import FCAppendix.Exclusive.BroadcastCapacity
import FCAppendix.Probability.EmpiricalMean

noncomputable section
namespace FCAppendix.Completion.Exclusive
open MeasureTheory ProbabilityTheory Filter Topology Set
open FCAppendix Game Bayes Exclusive Exclusive.Narrow Exclusive.Narrow.Finite
open Bayes.ExclusiveNarrow
open scoped BigOperators ProbabilityTheory

section FiniteAverages
variable {α : Type*} {m : ℕ}

def sampleMean (f : α → ℝ) (z : Fin m → α) : ℝ := (∑ j, f (z j)) / m

def forcedMean (f : α → ℝ) (i : Fin m) (a : ℝ) (z : Fin m → α) : ℝ :=
  (a + ∑ j ∈ Finset.univ.erase i, f (z j)) / m

theorem forcedMean_sub_sampleMean (f : α → ℝ) (i : Fin m) (a : ℝ)
    (z : Fin m → α) : forcedMean f i a z - sampleMean f z = (a-f (z i))/m := by
  classical
  have hs := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin m)))
    (f := fun j => f (z j)) (Finset.mem_univ i)
  unfold forcedMean sampleMean
  rw [← hs]
  ring

theorem forcedMean_replacement_bound (hm : 0 < m) {B a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) B) (f : α → ℝ) (hf : ∀ x, f x ∈ Icc (0 : ℝ) B)
    (i : Fin m) (z : Fin m → α) :
    |forcedMean f i a z - sampleMean f z| ≤ B/m := by
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  rw [forcedMean_sub_sampleMean, abs_div, abs_of_pos hmR]
  apply div_le_div_of_nonneg_right _ hmR.le
  exact abs_le.mpr ⟨by linarith [ha.1, (hf (z i)).2], by linarith [ha.2, (hf (z i)).1]⟩

theorem sampleMean_mem (hm : 0 < m) {B : ℝ} (f : α → ℝ)
    (hf : ∀ x, f x ∈ Icc (0 : ℝ) B) (z : Fin m → α) :
    sampleMean f z ∈ Icc (0 : ℝ) B := by
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  change (∑ j, f (z j)) / (m : ℝ) ∈ Icc (0 : ℝ) B
  refine ⟨div_nonneg (Finset.sum_nonneg fun j _ => (hf (z j)).1) hmR.le, ?_⟩
  apply (div_le_iff₀ hmR).mpr
  calc
    (∑ j, f (z j)) ≤ ∑ _j : Fin m, B := Finset.sum_le_sum fun j _ => (hf (z j)).2
    _ = B * m := by simp [mul_comm]

theorem forcedMean_mem (hm : 0 < m) {B a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) B) (f : α → ℝ)
    (hf : ∀ x, f x ∈ Icc (0 : ℝ) B) (i : Fin m) (z : Fin m → α) :
    forcedMean f i a z ∈ Icc (0 : ℝ) B := by
  classical
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hm1 : 1 ≤ m := hm
  have hs : (∑ j ∈ Finset.univ.erase i, f (z j)) ≤ ((m : ℝ)-1)*B := by
    calc
      _ ≤ ∑ _j ∈ Finset.univ.erase i, B :=
        Finset.sum_le_sum fun j _ => (hf (z j)).2
      _ = ((m : ℝ)-1)*B := by
        simp [Finset.card_erase_of_mem (Finset.mem_univ i), Nat.cast_sub hm1]
  change (a + ∑ j ∈ Finset.univ.erase i, f (z j)) / (m : ℝ) ∈ Icc (0 : ℝ) B
  refine ⟨div_nonneg (add_nonneg ha.1
    (Finset.sum_nonneg fun j _ => (hf (z j)).1)) hmR.le, ?_⟩
  apply (div_le_iff₀ hmR).mpr
  nlinarith [ha.2]

theorem abs_sub_bound_of_mem {x B y : ℝ} (hx : x ∈ Icc (0 : ℝ) B) :
    |x-y| ≤ B+|y| := by
  calc
    |x-y| ≤ |x|+|y| := by simpa using (abs_sub_le x 0 y)
    _ ≤ B+|y| := add_le_add (by simpa [abs_of_nonneg hx.1] using hx.2) le_rfl

end FiniteAverages

section MeasurableAverages
variable {α : Type*} [MeasurableSpace α] {m : ℕ}

theorem measurable_sampleMean (f : α → ℝ) (hf : Measurable f) :
    Measurable (sampleMean (m := m) f) := by
  exact (Finset.measurable_sum _ (fun j _ => hf.comp (measurable_pi_apply j))).div_const m

theorem measurable_forcedMean (f : α → ℝ) (hf : Measurable f)
    (i : Fin m) (a : ℝ) : Measurable (forcedMean f i a) := by
  classical
  exact (measurable_const.add
    (Finset.measurable_sum _ (fun j _ => hf.comp (measurable_pi_apply j)))).div_const m

theorem integrable_abs_forcedMean_sub (μ : Measure (Fin m → α)) [IsFiniteMeasure μ]
    (hm : 0 < m) (f : α → ℝ) (hf : Measurable f) {B a : ℝ}
    (hb : ∀ x, f x ∈ Icc (0 : ℝ) B) (ha : a ∈ Icc (0 : ℝ) B)
    (i : Fin m) (r : ℝ) :
    Integrable (fun z => |forcedMean f i a z-r|) μ := by
  apply Integrable.of_bound
    ((measurable_forcedMean f hf i a).sub_const r).abs.aestronglyMeasurable (B+|r|)
  exact Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_abs]
    exact abs_sub_bound_of_mem (forcedMean_mem hm ha f hb i z)

theorem forcedMean_L1 (μ : Measure α) [IsProbabilityMeasure μ]
    (hm : 0 < m) (f : α → ℝ) (hf : Measurable f) {B a : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, f x ∈ Icc (0 : ℝ) B) (ha : a ∈ Icc (0 : ℝ) B) (i : Fin m) :
    (∫ z : Fin m → α, |forcedMean f i a z - ∫ x, f x ∂μ|
      ∂Measure.pi (fun _ : Fin m => μ)) ≤ B/Real.sqrt m + B/m := by
  let ν : Measure (Fin m → α) := Measure.pi (fun _ : Fin m => μ)
  letI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  let F : ℝ := ∫ x, f x ∂μ
  have hi : Integrable (fun z : Fin m → α => |sampleMean f z-F|) ν := by
    apply Integrable.of_bound
      ((measurable_sampleMean f hf).sub_const F).abs.aestronglyMeasurable (B+|F|)
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_abs]
      exact abs_sub_bound_of_mem (sampleMean_mem hm f hb z)
  have hforced := integrable_abs_forcedMean_sub ν hm f hf hb ha i F
  have hLLN : (∫ z, |sampleMean f z-F| ∂ν) ≤ B/Real.sqrt m := by
    simpa only [sampleMean, ν, F] using
      Probability.iid_empiricalMean_L1_le μ hf.aestronglyMeasurable B hB
        (Eventually.of_forall fun x => by
          rw [abs_of_nonneg (hb x).1]
          exact (hb x).2) m hm
  have hconst : Integrable (fun _ : Fin m → α => B/(m : ℝ)) ν := integrable_const _
  calc
    _ ≤ ∫ z, |sampleMean f z-F| + B/m ∂ν := by
      apply integral_mono_ae hforced (hi.add hconst)
      exact Eventually.of_forall fun z => by
        change |forcedMean f i a z-F| ≤ |sampleMean f z-F|+B/(m : ℝ)
        have ht := abs_sub_le (forcedMean f i a z) (sampleMean f z) F
        have hr := forcedMean_replacement_bound hm ha f hb i z
        linarith
    _ = (∫ z, |sampleMean f z-F| ∂ν) + B/m := by
      rw [integral_add hi hconst]
      simp
    _ ≤ B/Real.sqrt m+B/m := add_le_add hLLN le_rfl

end MeasurableAverages

def allocationOfMeans (w x y : ℝ) : ℝ := unitClamp (1-max x 0*w/y)
def shareOfMeans (m : ℕ) (w y : ℝ) : ℝ := unitClamp (w/((m : ℝ)*y))

theorem allocation_ratio_error {w U x y delta mean ell : ℝ}
    (hU : 0 ≤ U) (hw : w ∈ Icc (0 : ℝ) U) (hy : 0 < y)
    (hell : 0 < ell) (hmean : ell ≤ mean) (hd : delta ∈ Icc (0 : ℝ) 1)
    (href : 1-delta*w/mean ∈ Icc (0 : ℝ) 1) :
    |allocationOfMeans w x y - (1-delta*w/mean)| ≤
      (2*U/ell)*|x-delta| + (2*U/ell^2+2/ell)*|y-mean| := by
  have hm : 0 < mean := hell.trans_le hmean
  have hcoef0 : 0 ≤ 2/ell := div_nonneg (by norm_num) hell.le
  by_cases hgood : ell/2 ≤ y
  · have hmax : |max x 0-delta| ≤ |x-delta| := by
      by_cases hx : 0 ≤ x
      · rw [max_eq_left hx]
      · have hx0 : x ≤ 0 := le_of_not_ge hx
        have hxd : x-delta ≤ 0 := by linarith [hd.1]
        rw [max_eq_right hx0, zero_sub, abs_neg,
          abs_of_nonneg hd.1, abs_of_nonpos hxd]
        linarith
    have hinv : 1/y ≤ 2/ell := by
      apply (div_le_div_iff₀ hy hell).mpr
      nlinarith
    have hprod : ell/2*ell ≤ y*mean :=
      mul_le_mul hgood hmean hell.le hy.le
    have hinv2 : delta/(y*mean) ≤ 2/ell^2 := by
      apply (div_le_div_iff₀ (mul_pos hy hm) (sq_pos_of_pos hell)).mpr
      have hδ := mul_le_mul_of_nonneg_right hd.2 (sq_nonneg ell)
      nlinarith
    have hdiv : |max x 0/y-delta/mean| ≤
        (2/ell)*|x-delta|+(2/ell^2)*|y-mean| := by
      have he : max x 0/y-delta/mean =
          (max x 0-delta)/y + delta*(mean-y)/(y*mean) := by
        field_simp [hy.ne', hm.ne']
        ring
      calc
        _ = |(max x 0-delta)/y + delta*(mean-y)/(y*mean)| := congrArg abs he
        _ ≤ |(max x 0-delta)/y| + |delta*(mean-y)/(y*mean)| := abs_add_le _ _
        _ = |max x 0-delta|/y + (delta/(y*mean))*|y-mean| := by
          rw [abs_div, abs_div, abs_mul, abs_of_pos hy,
            abs_of_pos (mul_pos hy hm), abs_of_nonneg hd.1, abs_sub_comm mean y]
          ring
        _ ≤ (2/ell)*|x-delta|+(2/ell^2)*|y-mean| := by
          apply add_le_add
          · calc
              _ ≤ |x-delta|/y := div_le_div_of_nonneg_right hmax hy.le
              _ = (1/y)*|x-delta| := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_right hinv (abs_nonneg _)
          · exact mul_le_mul_of_nonneg_right hinv2 (abs_nonneg _)
    calc
      _ = |unitClamp (1-max x 0*w/y)-unitClamp (1-delta*w/mean)| := by
        rw [unitClamp_eq href]
        rfl
      _ ≤ |(1-max x 0*w/y)-(1-delta*w/mean)| := unitClamp_nonexpansive _ _
      _ = w*|max x 0/y-delta/mean| := by
        have he : (1-max x 0*w/y)-(1-delta*w/mean) =
            -(w*(max x 0/y-delta/mean)) := by ring
        rw [he, abs_neg, abs_mul, abs_of_nonneg hw.1]
      _ ≤ U*((2/ell)*|x-delta|+(2/ell^2)*|y-mean|) :=
        mul_le_mul hw.2 hdiv (abs_nonneg _) hU
      _ = (2*U/ell)*|x-delta|+(2*U/ell^2)*|y-mean| := by ring
      _ ≤ _ := by
        have he : 0 ≤ (2/ell)*|y-mean| := mul_nonneg hcoef0 (abs_nonneg _)
        nlinarith
  · have hdist : ell/2 ≤ |y-mean| := by
      rw [abs_of_nonpos (show y-mean ≤ 0 by linarith)]
      linarith
    have hunit : |allocationOfMeans w x y-(1-delta*w/mean)| ≤ 1 := by
      have hb := unitClamp_mem (1-max x 0*w/y)
      change |unitClamp (1-max x 0*w/y)-(1-delta*w/mean)| ≤ 1
      exact abs_le.mpr ⟨by linarith [hb.1, href.2], by linarith [hb.2, href.1]⟩
    have hbad : 1 ≤ (2/ell)*|y-mean| := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hell).mpr
      nlinarith
    have hn1 : 0 ≤ (2*U/ell)*|x-delta| := by positivity
    have hn2 : 0 ≤ (2*U/ell^2)*|y-mean| := by positivity
    exact hunit.trans (by nlinarith)

theorem share_ratio_error {m : ℕ} {w U y mean ell : ℝ} (hm : 0 < m)
    (hw : w ∈ Icc (0 : ℝ) U) (hy : 0 < y) (hell : 0 < ell) (hmean : ell ≤ mean) :
    shareOfMeans m w y ≤ 2*U/((m : ℝ)*ell)+(2/ell)*|y-mean| := by
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hU : 0 ≤ U := hw.1.trans hw.2
  by_cases hgood : ell/2 ≤ y
  · have hraw : shareOfMeans m w y ≤ w/((m : ℝ)*y) :=
      max_le (div_nonneg hw.1 (mul_pos hmR hy).le) (min_le_right _ _)
    have hratio : w/((m : ℝ)*y) ≤ 2*U/((m : ℝ)*ell) := by
      apply (div_le_div_iff₀ (mul_pos hmR hy) (mul_pos hmR hell)).mpr
      calc
        w*((m : ℝ)*ell) ≤ U*((m : ℝ)*ell) :=
          mul_le_mul_of_nonneg_right hw.2 (mul_pos hmR hell).le
        _ = (U*(m : ℝ))*ell := by ring
        _ ≤ (U*(m : ℝ))*(2*y) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hU hmR.le)
        _ = (2*U)*((m : ℝ)*y) := by ring
    exact hraw.trans (hratio.trans (le_add_of_nonneg_right (by positivity)))
  · have hdist : ell/2 ≤ |y-mean| := by
      rw [abs_of_nonpos (show y-mean ≤ 0 by linarith)]
      linarith
    have hbad : 1 ≤ (2/ell)*|y-mean| := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hell).mpr
      nlinarith
    have hfirst : 0 ≤ 2*U/((m : ℝ)*ell) := by positivity
    exact (unitClamp_mem _).2.trans (hbad.trans (by linarith))

def concentrationRate (m : ℕ) (U ell : ℝ) : ℝ :=
  (2*U/ell)*(1/Real.sqrt m+1/m) +
    (2*U/ell^2+4/ell)*(U/Real.sqrt m+U/m) + 2*U/((m : ℝ)*ell)

theorem concentrationRate_tendsto {M : ℕ → ℕ} (hM : Tendsto M atTop atTop)
    (U ell : ℝ) : Tendsto (fun t => concentrationRate (M t) U ell) atTop (𝓝 0) := by
  have hm : Tendsto (fun t => (M t : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hM
  have hinv : Tendsto (fun t => (M t : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hm
  have hsqrt : Tendsto (fun t => (Real.sqrt (M t : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hm)
  have h := (((hsqrt.add hinv).const_mul (2*U/ell)).add
    (((hsqrt.const_mul U).add (hinv.const_mul U)).const_mul (2*U/ell^2+4/ell))).add
      (hinv.const_mul (2*U/ell))
  convert h using 1
  · funext t
    simp only [concentrationRate, div_eq_mul_inv, mul_inv_rev]
    ring
  · ring

section ActualGames
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def activeDraw (u : UserDraw n) : ℝ := if u.1.2.routeCount = 0 then 0 else 1

theorem activeDraw_bounds (u : UserDraw n) : activeDraw u ∈ Icc (0 : ℝ) 1 := by
  unfold activeDraw
  split_ifs <;> norm_num

theorem activeDraw_measurable : Measurable (activeDraw (n := n)) := by
  exact Measurable.ite
    (measurableSet_eq_fun ((measurable_routeCount n).comp (measurable_snd.comp measurable_fst))
      measurable_const) measurable_const measurable_const

def inverseMean (Γ : FiniteGame m n c Seed) (lo hi : ℝ) : ℝ :=
  ∫ u, clippedInverseDraw n lo hi u ∂userLaw Γ

def forcedActive (i : Fin m) (z : UserProfile m n) : ℝ := forcedMean activeDraw i 1 z
def forcedWeight (lo hi b : ℝ) (i : Fin m) (z : UserProfile m n) : ℝ :=
  forcedMean (clippedInverseDraw n lo hi) i (inverseBid n b) z

theorem integral_userLaw_value_bounded (Γ : FiniteGame m n c Seed)
    (f : ℝ → ℝ) (hf : Measurable f) (K : ℝ) (hK : ∀ v, |f v| ≤ K) :
    (∫ u, f u.1.1 ∂userLaw Γ) = ∫ v, f v ∂Γ.F := by
  letI : IsMarkovKernel Γ.σ := Γ.hσ
  have hi : Integrable (fun x : ℝ × JointAction n => f x.1) (Γ.F ⊗ₘ Γ.σ) := by
    apply Integrable.of_bound (hf.comp measurable_fst).aestronglyMeasurable K
    exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, Function.comp_def] using hK x.1
  change (∫ u, f u.1.1 ∂(Γ.F ⊗ₘ Γ.σ).prod (permLaw n)) = _
  rw [integral_fun_fst (fun x : ℝ × JointAction n => f x.1)]
  simp only [probReal_univ, one_smul]
  rw [Measure.integral_compProd hi]
  simp

theorem inverseMean_lower (Γ : FiniteGame m n c Seed) (hn : 2 ≤ n)
    {lo hi h : ℝ} (hlo : 0 < lo) (hband : lo ≤ hi)
    (hmass : ∫ u, activeDraw u ∂userLaw Γ = h) :
    h * inverseBid n hi ≤ inverseMean Γ lo hi := by
  have hpoint (u : UserDraw n) : inverseBid n hi*activeDraw u ≤ clippedInverseDraw n lo hi u := by
    by_cases hz : u.1.2.routeCount = 0
    · simp [activeDraw, clippedInverseDraw, hz]
    · simp only [activeDraw, clippedInverseDraw, if_neg hz, mul_one]
      exact inverseBid_antitone n hn
        (hlo.trans_le (le_max_left _ _)) (max_le hband (min_le_left _ _))
  have ha : Integrable (activeDraw (n := n)) (userLaw Γ) := by
    apply Integrable.of_bound activeDraw_measurable.aestronglyMeasurable 1
    exact Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (activeDraw_bounds u).1]
      exact (activeDraw_bounds u).2
  have hw : Integrable (clippedInverseDraw n lo hi) (userLaw Γ) := by
    apply Integrable.of_bound (measurable_clippedInverseDraw n lo hi).aestronglyMeasurable
      (inverseBid n lo)
    exact Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (clippedInverseDraw_bounds n hn hlo u).1]
      exact (clippedInverseDraw_bounds n hn hlo u).2
  have hi := integral_mono (ha.const_mul _) hw hpoint
  simpa only [integral_const_mul, hmass, inverseMean, mul_comm] using hi

theorem activeMean_eq (Γ : FiniteGame m n c Seed) (hn : 0 < n)
    (E : Set ℝ) (hE : MeasurableSet E) (hclass : ExclusiveBroadcastOn Γ E) :
    (∫ u, activeDraw u ∂userLaw Γ) = Γ.F.real E := by
  have hc : ∀ᵐ u ∂userLaw Γ,
      (u.1.1 ∈ E → 0 < u.1.2.bid ∧ u.1.2.routeCount = n) ∧
      (u.1.1 ∉ E → u.1.2.routeCount = 0) :=
    Measure.quasiMeasurePreserving_fst.ae hclass
  have he : ∀ᵐ u ∂userLaw Γ,
      activeDraw u = E.indicator (fun _ => (1 : ℝ)) u.1.1 := by
    filter_upwards [hc] with u hu
    by_cases hv : u.1.1 ∈ E
    · simp [activeDraw, (hu.1 hv).2, hn.ne', hv]
    · simp [activeDraw, hu.2 hv, hv]
  rw [integral_congr_ae he]
  have hbound (v : ℝ) : |E.indicator (fun _ => (1 : ℝ)) v| ≤ 1 := by
    by_cases hv : v ∈ E <;> simp [hv]
  rw [integral_userLaw_value_bounded Γ _ (measurable_const.indicator hE) 1 hbound]
  exact integral_indicator_one hE

theorem forced_statistics_row (Γ : FiniteGame m (n+1) c Seed)
    (P : Corridor (n+1) m c) (hplay : CorridorPlay Γ P) (i : Fin m)
    {b : ℝ} (hb : b ∈ Icc P.lower P.upper) :
    ∀ᵐ z ∂userProfileLaw Γ,
      forcedActive i z = (rivalCount i z : ℝ)/m ∧
      forcedWeight P.lower P.upper b i z = (rivalWeight i z+inverseBid (n+1) b)/m ∧
      boundedP Γ P hplay i b z = allocationOfMeans (inverseBid (n+1) b)
        (forcedActive i z-(c:ℝ)/m) (forcedWeight P.lower P.upper b i z) ∧
      boundedShare Γ P hplay i b z = shareOfMeans m (inverseBid (n+1) b)
        (forcedWeight P.lower P.upper b i z) := by
  classical
  filter_upwards [ae_goodProfile Γ P hplay] with z hz
  have hsumA : (∑ j ∈ Finset.univ.erase i, activeDraw (z j)) =
      ((activeRivals i z).card : ℝ) := by
    simp [activeRivals, activeDraw, Finset.card_filter]
  have hsumW : (∑ j ∈ Finset.univ.erase i,
      clippedInverseDraw (n+1) P.lower P.upper (z j)) = rivalWeight i z := by
    unfold rivalWeight activeRivals
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    rcases hz j with hjz | ⟨hjr,hjb⟩
    · simp [clippedInverseDraw, hjz]
    · have hjn : (z j).1.2.routeCount ≠ 0 := by rw [hjr]; omega
      simp [clippedInverseDraw_eq (n+1) (z j) hjn hjb, hjn]
  have hA : forcedActive i z = (rivalCount i z : ℝ)/m := by
    simp [forcedActive, forcedMean, hsumA, rivalCount, Nat.cast_add, add_comm]
  have hW : forcedWeight P.lower P.upper b i z =
      (rivalWeight i z+inverseBid (n+1) b)/m := by
    simp [forcedWeight, forcedMean, hsumW, add_comm]
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr P.population
  have hden : 0 < rivalWeight i z+inverseBid (n+1) b :=
    add_pos_of_nonneg_of_pos (P.rival_nonneg (rival_bounds P i z hz))
      (inverseBid_pos (n+1) (P.lower_pos.trans_le hb.1))
  have hnat : (((rivalCount i z-c : ℕ) : ℝ)/m) =
      max ((rivalCount i z : ℝ)/m-(c:ℝ)/m) 0 := by
    by_cases hc : c ≤ rivalCount i z
    · have hcR : (c : ℝ) ≤ (rivalCount i z : ℝ) := by exact_mod_cast hc
      have hq : (0 : ℝ) ≤ (rivalCount i z : ℝ)/m-(c : ℝ)/m :=
        sub_nonneg.mpr (div_le_div_of_nonneg_right hcR hmR.le)
      rw [Nat.cast_sub hc, sub_div, max_eq_left hq]
    · have hcN : rivalCount i z ≤ c := (by omega)
      have hcR : (rivalCount i z : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcN
      have hq : (rivalCount i z : ℝ)/m-(c : ℝ)/m ≤ 0 :=
        sub_nonpos.mpr (div_le_div_of_nonneg_right hcR hmR.le)
      rw [Nat.sub_eq_zero_of_le hcN, Nat.cast_zero, zero_div, max_eq_right hq]
  refine ⟨hA,hW,?_,?_⟩
  · rw [hA,hW]
    unfold boundedP allocationOfMeans
    rw [corridorClamp_eq P hb]
    apply congrArg unitClamp
    change 1-((rivalCount i z-c : ℕ) : ℝ)*inverseBid (n+1) b /
        (rivalWeight i z+inverseBid (n+1) b) = _
    rw [← hnat]
    field_simp [hmR.ne', hden.ne']
  · rw [hW]
    unfold boundedShare shareOfMeans
    rw [corridorClamp_eq P hb]
    apply congrArg unitClamp
    change inverseBid (n+1) b/(rivalWeight i z+inverseBid (n+1) b) = _
    field_simp [hmR.ne', hden.ne']

end ActualGames
end FCAppendix.Completion.Exclusive
