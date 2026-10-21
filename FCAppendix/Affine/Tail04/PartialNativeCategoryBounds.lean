import FCAppendix.Affine.Tail04.PartialNativeEvents
import FCAppendix.Affine.Tail04.NativeCountGuards
import FCAppendix.Affine.Tail04.OriginalLowRow
import FCAppendix.Affine.Tail04.OriginalMenuMoments

noncomputable section
namespace FCAppendix.Affine.Tail04.PartialNativeCategoryBounds
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativeMenuReports NativePartialReports PartialNativeCoordinates
open PartialNativeEvents NativeCountGuards OriginalPopulation OriginalValues Hybrid
open Existence.Distributional MenuError
open scoped BigOperators

variable {N c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def backgroundRivals (i : Fin (N+1)) (ω : Background (N+1) 2 Seed) : Fin N→ UserDraw 2 :=
  NativeFlag.deletedUsers i ω.1

lemma backgroundRivals_preserving (Γ : FiniteGame (N+1) 2 c Seed) (i : Fin (N+1)) :
    MeasurePreserving (backgroundRivals (Seed:=Seed) i) (backgroundLaw Γ)
      (Measure.pi (fun _ : Fin N => userLaw Γ)) :=
  (NativeFlag.deletedUsers_measurePreserving Γ i).comp measurePreserving_fst

lemma background_category_event (Γ : FiniteGame (N+1) 2 c Seed) (E : Observable.Regions)
    (i : Fin (N+1)) (P : (Fin N→ Fin 4)→ Prop) :
    (backgroundLaw Γ).real {ω | P (rivalKinds E i ω)}=
      (Measure.pi (fun _ : Fin N => userLaw Γ)).real
        {row | P (fun r => E.coarseTag (row r))} := by
  have ht : Measurable (fun row : Fin N→ UserDraw 2 => fun r => E.coarseTag (row r)) :=
    measurable_pi_lambda _ (fun r => E.measurable_coarseTag.comp (measurable_pi_apply r))
  have hP : MeasurableSet {row : Fin N→ UserDraw 2 | P (fun r => E.coarseTag (row r))} :=
    ((Set.to_countable {k : Fin N→ Fin 4 | P k}).measurableSet).preimage ht
  have h := congrArg (fun μ : Measure (Fin N→ UserDraw 2) =>
      μ {row | P (fun r => E.coarseTag (row r))})
    (backgroundRivals_preserving Γ i).map_eq
  rw [Measure.map_apply (backgroundRivals_preserving Γ i).measurable hP] at h
  exact congrArg ENNReal.toReal h

lemma original_menu_rivals (Γ : FiniteGame (N+1) 2 c Seed) (E : Observable.Regions)
    (i : Fin (N+1)) (hmenu : ∀ᵐ x ∂Γ.F⊗ₘΓ.σ,MenuAction E x.2) :
    ∀ᵐ ω ∂backgroundLaw Γ,∀ r : Fin N,MenuAction E (ω.1 (i.succAbove r)).1.2 := by
  have hu : ∀ᵐ x ∂userLaw Γ,MenuAction E x.1.2 :=
    (measurePreserving_fst (μ:=Γ.F⊗ₘΓ.σ) (ν:=permLaw 2)).quasiMeasurePreserving.ae hmenu
  have hp : ∀ᵐ row ∂Measure.pi (fun _ : Fin N => userLaw Γ),∀ r,MenuAction E (row r).1.2 :=
    ae_all_iff.mpr (fun r =>
      (measurePreserving_eval (fun _ : Fin N => userLaw Γ) r).quasiMeasurePreserving.ae hu)
  exact (backgroundRivals_preserving Γ i).quasiMeasurePreserving.ae hp

def noLow (E : Observable.Regions) (i : Fin (N+1)) : Set (Background (N+1) 2 Seed) :=
  {ω | ∀ r : Fin N,rivalKinds E i ω r≠0}

lemma measurableSet_noLow (E : Observable.Regions) (i : Fin (N+1)) :
    MeasurableSet (noLow E (Seed:=Seed) i) := by
  exact ((Set.to_countable {kind : Fin N→Fin 4 | ∀r,kind r≠0}).measurableSet).preimage
    (measurable_rivalKinds E i)

theorem native_noLow_bound (Γ : FiniteGame (N+1) 2 c Seed) (E : Observable.Regions)
    (i : Fin (N+1)) (hN : 0< N) (s : ℝ) (hs : 0< s)
    (hsmass : s≤(userLaw Γ).real (E.coarseTag ⁻¹' {0})) :
    (backgroundLaw Γ).real (noLow E i)≤ Real.exp (-(N:ℝ)*s^2/2) := by
  rw [noLow,background_category_event Γ E i (fun kind=>∀r,kind r≠0)]
  have hprob := NativeFlag.iid_bulk_count_lower_tail (userLaw Γ)
    (E.coarseTag ⁻¹' {0}) (E.measurable_coarseTag (measurableSet_singleton _)) N hN hs hsmass
  apply (measureReal_mono (μ:=Measure.pi (fun _ : Fin N => userLaw Γ)) ?_).trans hprob
  intro row hrow
  have hc : Probability.sampleCount (E.coarseTag ⁻¹' {0}) row=0 := by
    unfold Probability.sampleCount
    have he : (Finset.univ.filter fun r => row r∈E.coarseTag ⁻¹' {0})=∅ := by
      ext r
      simp [hrow r]
    rw [he,Finset.card_empty]
  change (Probability.sampleCount (E.coarseTag ⁻¹' {0}) row : ℝ)<s*(N:ℝ)/2
  rw [hc,Nat.cast_zero]
  positivity

section Source
variable (Γ : FiniteGame (N+1) 2 c NativeLocalPolicy.Seed)
  (D : Data (N+1) c) (P : ValueParameters) (hd : D.E.d=P.d0)
  (t : ℝ) (ht : P.M≤ t)
local instance : IsProbabilityMeasure (P.originalMovingActiveLaw t ht) :=
  P.originalMovingActiveLaw_probability t ht
variable (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (πP : Law (A:=Icc D.E.R D.E.Rp) P.originalPartialLaw)
  (πA : Law (A:=Icc (1:ℝ) D.E.U) (P.originalMovingActiveLaw t ht))
  (upperBid : ℝ→ℝ) (hupper : Measurable upperBid)
  (hfloor : ∀ v,t< v → D.E.H≤ upperBid v)
local notation "z" => activeMass P.theta*P.zeta*powerTail P.M 10 t
variable (hjoint : Γ.F⊗ₘΓ.σ=(originalJoint P t ht D.E.R D.E.Rp D.E.U
  (D.E.d_nonneg.trans D.E.d_lt_R.le) πL πP πA upperBid hupper : Measure (ℝ×JointAction 2)))

include P hd t ht πL πP πA upperBid hupper hfloor hjoint in
theorem source_menu_rivals (i : Fin (N+1)) :
    ∀ᵐ ω ∂backgroundLaw Γ,∀ r : Fin N,MenuAction D.E (ω.1 (i.succAbove r)).1.2 := by
  apply original_menu_rivals Γ D.E i
  rw [hjoint]
  exact (originalJoint_sourceBands P D.E hd t ht πL πP πA upperBid hupper hfloor).mono
    fun x hx => source_menu D.E P t x hx

include hd t ht πL πP πA upperBid hupper hfloor hjoint in
theorem source_low_mass : (userLaw Γ).real (D.E.coarseTag ⁻¹' {0})=lowMass P.theta := by
  have hz := P.tailMass_nonneg t ht
  have ha := P.movingActiveMass_positive t ht
  have hsum : lowMass P.theta+(activeMass P.theta-z)+(partialMass+z)=1 := by
    have hh := mass_sum P.theta
    linarith
  have hrow := native_original_exact_low_row D.E P hd t ht πL πP πA upperBid hupper hfloor Γ hjoint
  have h := original_category_mean Γ D.E (lowMass P.theta) (activeMass P.theta-z) (partialMass+z)
    P.low_mass_pos.le ha.le (by norm_num [partialMass];linarith)
    hsum (LowBody.realLowBidLaw πL.1 : Measure ℝ) hrow 0
  simp only [categoryFlag_indicator,Matrix.cons_val_zero] at h
  have hi : (∫ x,if D.E.coarseTag x=0 then (1:ℝ) else 0 ∂userLaw Γ)=
      (userLaw Γ).real (D.E.coarseTag ⁻¹' {0}) := by
    simpa only [Set.indicator,Set.mem_preimage,Set.mem_singleton_iff,Pi.one_apply] using
      integral_indicator_one (μ:=userLaw Γ) (D.E.measurable_coarseTag (measurableSet_singleton 0))
  exact hi.symm.trans h

include P hd t ht πL πP πA upperBid hupper hfloor hjoint in
theorem source_tie_bound (i : Fin (N+1)) (hN : 0< N) (side : Fin 2) :
    (backgroundLaw Γ).real (tieEvent D i side)≤(75/4:ℝ)/Real.sqrt N := by
  let fixed : Fin 1→ Fin 4 := fun _ => NativeContinuation.upperTag side
  have he : (tieEvent D i side)=ᵐ[backgroundLaw Γ]
      {ω | fullCategoryCount fixed (rivalKinds D.E i ω) 2=
        fullCategoryCount fixed (rivalKinds D.E i ω) 3} := by
    filter_upwards [source_menu_rivals Γ D P hd t ht πL πP πA upperBid hupper hfloor hjoint i] with ω hω
    have hh := partial_private_tie_iff D.E i ω hω D rfl
      (⟨D.E.R,le_rfl,D.E.R_le_Rp⟩ : Icc D.E.R D.E.Rp) side
    apply propext
    change ((LocalCoordinates.ids D.E 2 (presentList ω i D.E.R side)).card=
      (LocalCoordinates.ids D.E 3 (presentList ω i D.E.R side)).card) ↔
      fullCategoryCount fixed (rivalKinds D.E i ω) 2=
        fullCategoryCount fixed (rivalKinds D.E i ω) 3
    rw [hh]
    have hf2 : categoryCount 2 fixed=MenuError.partialOffset side 0 := by
      fin_cases side <;> norm_num [fixed,NativeContinuation.upperTag,MenuError.partialOffset,
        categoryCount,LowBody.hitCount,Fin.sum_univ_one,Fin.ext_iff]
    have hf3 : categoryCount 3 fixed=MenuError.partialOffset side 1 := by
      fin_cases side <;> norm_num [fixed,NativeContinuation.upperTag,MenuError.partialOffset,
        categoryCount,LowBody.hitCount,Fin.sum_univ_one,Fin.ext_iff]
    simp only [fullCategoryCount,hf2,hf3]
    omega
  rw [measureReal_def,measure_congr he]
  change (backgroundLaw Γ).real {ω | fullCategoryCount fixed (rivalKinds D.E i ω) 2=
    fullCategoryCount fixed (rivalKinds D.E i ω) 3}≤_
  rw [background_category_event Γ D.E i
    (fun kind=>fullCategoryCount fixed kind 2=fullCategoryCount fixed kind 3)]
  have hz := P.tailMass_nonneg t ht
  have ha := P.movingActiveMass_positive t ht
  have hsum : lowMass P.theta+(activeMass P.theta-z)+(partialMass+z)=1 := by
    have hh := mass_sum P.theta
    linarith
  have hh1 : partialMass+z≤1 := by linarith [P.low_mass_pos]
  have hrow := native_original_exact_low_row D.E P hd t ht πL πP πA upperBid hupper hfloor Γ hjoint
  have h := original_equal_private_prefix_uniform Γ D.E
    (lowMass P.theta) (activeMass P.theta-z) (partialMass+z) P.low_mass_pos.le ha.le
    (by norm_num [partialMass];linarith) hsum (LowBody.realLowBidLaw πL.1 : Measure ℝ)
    hrow fixed N hN partialMass (by norm_num [partialMass]) (by linarith) hh1
  norm_num [partialMass] at h
  exact h

include hd t ht πL πP πA upperBid hupper hfloor hjoint in
theorem source_noLow_bound (i : Fin (N+1)) (hN : 0< N) :
    (backgroundLaw Γ).real (noLow D.E i)≤
      Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2) :=
  native_noLow_bound Γ D.E i hN (lowMass P.theta) P.low_mass_pos
    (source_low_mass Γ D P hd t ht πL πP πA upperBid hupper hfloor hjoint).ge

end Source
end FCAppendix.Affine.Tail04.PartialNativeCategoryBounds
