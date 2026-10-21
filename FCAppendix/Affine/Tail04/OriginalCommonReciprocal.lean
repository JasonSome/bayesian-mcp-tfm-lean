import FCAppendix.Affine.Tail04.NativeFlagTransport
import FCAppendix.Affine.Tail04.NativeActiveCompressedLaw

noncomputable section
namespace FCAppendix.Affine.Tail04.OriginalCommonReciprocal
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional OriginalValues FiniteTailNoisyGame
open SourceTailNoisyFixedPoint NativeNoisySource LatentNoisyPopulation
open NativeActiveCompressedLaw OriginalActiveCompression
open scoped BigOperators

section Iid
variable {X : Type*} [MeasurableSpace X]

theorem iid_reciprocal (μ : Measure X) [IsProbabilityMeasure μ]
    (E : Set X) (hE : MeasurableSet E) (N : ℕ) (hN : 0< N)
    {s : ℝ} (hs : 0< s) (hmass : s≤ (μ).real E) :
    (∫ row : Fin N→ X,1/((Probability.sampleCount E row+1:ℕ):ℝ)
      ∂Measure.pi (fun _ : Fin N=> μ))≤
      2/(s*(N:ℝ))+Real.exp (-(N:ℝ)*s^2/2) := by
  let ν := Measure.pi (fun _ : Fin N=> μ)
  let bad : Set (Fin N→ X) :=
    {row | (Probability.sampleCount E row:ℝ)< s*(N:ℝ)/2}
  let r : (Fin N→ X)→ℝ :=
    fun row=>1/((Probability.sampleCount E row+1:ℕ):ℝ)
  have hn : (0:ℝ)< N := Nat.cast_pos.mpr hN
  have hm : Measurable (fun row : Fin N→ X=>(Probability.sampleCount E row:ℝ)) :=
    (measurable_of_countable (fun n : ℕ=>(n:ℝ))).comp
      (Probability.measurable_sampleCount E hE N)
  have hbad : MeasurableSet bad := measurableSet_lt hm measurable_const
  have hmr : Measurable r := by
    simpa only [r,Nat.cast_add,Nat.cast_one] using!
      measurable_const.div (hm.add_const 1)
  have hr (row : Fin N→ X) : r row∈Icc (0:ℝ) 1 := by
    have hc : (0:ℝ)≤ Probability.sampleCount E row := Nat.cast_nonneg _
    dsimp only [r]
    push_cast
    exact ⟨by positivity,(div_le_one (by positivity)).mpr (by linarith)⟩
  have hir : Integrable r ν := Integrable.of_bound hmr.aestronglyMeasurable 1
    (ae_of_all _ fun row=> by rw [Real.norm_eq_abs,abs_of_nonneg (hr row).1];exact (hr row).2)
  have hib : Integrable (bad.indicator (fun _ : Fin N→ X=>(1:ℝ))) ν :=
    (integrable_const 1).indicator hbad
  have hK : 0≤2/(s*(N:ℝ)) := by positivity
  have hpoint (row : Fin N→ X) :
      r row≤2/(s*(N:ℝ))+bad.indicator (fun _=>(1:ℝ)) row := by
    by_cases hb : row∈bad
    · simpa only [Set.indicator_of_mem hb] using (hr row).2.trans (by linarith : (1:ℝ)≤2/(s*(N:ℝ))+1)
    · have hc : s*(N:ℝ)/2≤(Probability.sampleCount E row:ℝ) := le_of_not_gt hb
      have hd : 0< s*(N:ℝ)/2 := by positivity
      have hden : s*(N:ℝ)/2≤((Probability.sampleCount E row+1:ℕ):ℝ) := by
        push_cast
        linarith
      have hh := one_div_le_one_div_of_le hd hden
      have he : 1/(s*(N:ℝ)/2)=2/(s*(N:ℝ)) := by ring
      rw [he] at hh
      simpa only [r,Set.indicator_of_notMem hb,add_zero] using hh
  have hi := integral_mono hir ((integrable_const _).add hib) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_add (integrable_const _) hib,integral_indicator_const (1:ℝ) hbad] at hi
  simp only [integral_const,probReal_univ,smul_eq_mul,mul_one,one_mul] at hi
  have hp := NativeFlag.iid_bulk_count_lower_tail μ E hE N hN hs hmass
  exact hi.trans (by simpa only [ν,bad,add_comm] using add_le_add_left hp (2/(s*(N:ℝ))))

end Iid

section Source
variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)
  (hfloor : ∀ v,t< v→ H≤ upperBid v) (N : ℕ)
  (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)

local notation "μ" => drawLaw D P t ht πL π upperBid hupperBid
local notation "tag" => latentTag D P hdR H hBH
local notation "Ds" => installOriginal D P t ht

include hfloor hrare t ht πL π upperBid hupperBid N in
theorem original_common_mass_ge_bulk : P.bulkWeight≤ (μ).real (tag ⁻¹' {1}) := by
  have hm := original_category_mass D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare 1
  rw [measureReal_def,hm,ENNReal.toReal_ofReal ((Ds).categories.nonneg 1)]
  change P.bulkWeight≤ P.bulkWeight+P.truncatedTailWeight t
  exact le_add_of_nonneg_right (P.truncatedTailWeight_pos t ht).le

include hfloor hrare in
theorem original_common_reciprocal (hN : 0< N) :
    (∫ row : Fin N→ Draw,1/(((Ds).count (tags tag row) 1+1:ℕ):ℝ)
      ∂Measure.pi (fun _ : Fin N=> μ))≤
      2/(P.bulkWeight*(N:ℝ))+Real.exp (-(N:ℝ)*P.bulkWeight^2/2) := by
  have hh := iid_reciprocal μ (tag ⁻¹' {1})
    ((measurable_latentTag D P hdR H hBH) (measurableSet_singleton 1)) N hN
    P.bulkWeight_pos
    (original_common_mass_ge_bulk D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare)
  simpa only [Data.count,tags,Probability.sampleCount,Function.comp_apply,
    Set.mem_preimage,Set.mem_singleton_iff] using hh

end Source
end FCAppendix.Affine.Tail04.OriginalCommonReciprocal
