import FCAppendix.Existence.R01PayOnceSmallBid
import FCAppendix.Existence.R01PayOnceRowIntegration
import FCAppendix.Existence.R01PayOnceRelabel
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators
open FCAppendix.Existence.Distributional
attribute [local instance] Classical.propDecidable

def profilePayoff {ε W : ℝ} (m n c : ℕ)
    (x : Fin m → Value W × FloorAction ε W) (i : Fin m) : ℝ :=
  ((x i).1.1 - bid (x i).2) * success n c (fun j => (x j).2) i

theorem continuous_profilePayoff {ε W : ℝ} (m n c : ℕ) (hn : 2 ≤ n)
    (hε : 0 < ε) (i : Fin m) : Continuous
      (fun x : Fin m → Value W × FloorAction ε W => profilePayoff m n c x i) := by
  have hs : Continuous (fun x : Fin m → Value W × FloorAction ε W =>
      success n c (fun j => (x j).2) i) :=
    (PayOnce.continuous_success n).comp ((continuous_apply i).comp
      ((continuous_marginal n c hn hε).comp
        (continuous_pi (fun j => (continuous_apply j).snd))))
  exact (((continuous_apply i).fst.subtype_val).sub
    (continuous_bid.comp (continuous_apply i).snd)).mul hs

def raiseProfile {ε W : ℝ} (m : ℕ) (B : Icc ε W)
    (x : Fin m → Value W × FloorAction ε W) (i : Fin m) :
    Fin m → Value W × FloorAction ε W :=
  Function.update x i ((x i).1, .inr B)

theorem continuous_raiseProfile {ε W : ℝ} (m : ℕ) (B : Icc ε W) (i : Fin m) :
    Continuous (fun x : Fin m → Value W × FloorAction ε W => raiseProfile m B x i) := by
  apply continuous_pi
  intro j
  by_cases h : j=i
  · subst j
    simpa [raiseProfile] using (continuous_apply i).fst.prodMk
      (continuous_const : Continuous (fun _ : Fin m → Value W × FloorAction ε W =>
        (Sum.inr B : FloorAction ε W)))
  · simpa [raiseProfile, Function.update_of_ne h] using
      (continuous_apply j : Continuous (fun x : Fin m → Value W × FloorAction ε W => x j))

theorem classGain_eq_indicator {ε W : ℝ} (m n c : ℕ) (a t : ℝ) (B : Icc ε W)
    (x : Fin m → Value W × FloorAction ε W) (i : Fin m) :
    classGain m n c a t B x i =
      {y : Fin m → Value W × FloorAction ε W | smallClass a t (y i)}.indicator
        (fun y => profilePayoff m n c (raiseProfile m B y i) i - profilePayoff m n c y i) x := by
  have he : (fun j => (raiseProfile m B x i j).2) =
      Function.update (fun j => (x j).2) i (.inr B) := by
    funext j
    by_cases h : j=i
    · subst j; simp [raiseProfile]
    · simp [raiseProfile, Function.update_of_ne h]
  by_cases hC : smallClass a t (x i)
  · simp only [classGain, Set.indicator, mem_setOf_eq, hC]
    dsimp only [profilePayoff]
    rw [he]
    simp [raiseProfile, bid]
  · simp [classGain, hC, Set.indicator]

theorem integrable_classGain {ε W : ℝ} (m n c : ℕ) (hn : 2 ≤ n) (hε : 0 < ε)
    (a t : ℝ) (B : Icc ε W) (π : ProbabilityMeasure (Value W × FloorAction ε W))
    (i : Fin m) : Integrable (fun x => classGain m n c a t B x i)
      (rowLaw m π : Measure (Fin m → Value W × FloorAction ε W)) := by
  have hf := ((continuous_profilePayoff m n c hn hε i).comp
    (continuous_raiseProfile m B i)).sub (continuous_profilePayoff m n c hn hε i)
  have hi := (ContinuousMap.equivBoundedOfCompact _ _ ⟨_, hf⟩).integrable
    (rowLaw m π : Measure (Fin m → Value W × FloorAction ε W))
  convert hi.indicator ((measurableSet_smallClass a t).preimage (measurable_pi_apply i)) using 1
  all_goals first | rfl | (funext x; exact classGain_eq_indicator m n c a t B x i)

theorem integral_classGain_head_inner {ε W : ℝ} (N n c : ℕ) (hn : 2 ≤ n)
    (hε : 0 < ε) {μ : Measure (Value W)} (π : FloorLaw ε W μ)
    (a t : ℝ) (B : Icc ε W) (z : Value W × FloorAction ε W) :
    (∫ r, classGain (N+1) n c a t B (Fin.cons z r) 0
      ∂(rowLaw N π.1 : Measure (Fin N → Value W × FloorAction ε W))) =
    if smallClass a t z then
      floorPayoff N n c (π, (z.1, .inr B)) - floorPayoff N n c (π, z) else 0 := by
  have hf (b : FloorAction ε W) : Integrable
      (fun r : Fin N → Value W × FloorAction ε W => success n c (insertFocal N b r) 0)
      (rowLaw N π.1 : Measure (Fin N → Value W × FloorAction ε W)) := by
    have hc : Continuous (fun r : Fin N → Value W × FloorAction ε W =>
        success n c (insertFocal N b r) 0) := (PayOnce.continuous_success n).comp
      ((continuous_apply (0 : Fin (N+1))).comp ((continuous_marginal n c hn hε).comp
        ((continuous_insertFocal N).comp (continuous_const.prodMk continuous_id))))
    exact (ContinuousMap.equivBoundedOfCompact _ _ ⟨_, hc⟩).integrable _
  have he (r : Fin N → Value W × FloorAction ε W) :
      Function.update (fun j => ((Fin.cons (α := fun _ : Fin (N+1) => Value W × FloorAction ε W) z r) j).2) 0 (.inr B) = insertFocal N (.inr B) r := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [insertFocal]
    · simp [insertFocal]
  have he0 (r : Fin N → Value W × FloorAction ε W) :
      (fun j => ((Fin.cons (α := fun _ : Fin (N+1) => Value W × FloorAction ε W) z r) j).2) =
        insertFocal N z.2 r := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> simp [insertFocal]
  by_cases hC : smallClass a t z
  · simp only [classGain, Fin.cons_zero, if_pos hC]
    simp_rw [he, he0]
    change (∫ r, (z.1.1-B.1)*success n c (insertFocal N (.inr B) r) 0 -
      (z.1.1-bid z.2)*success n c (insertFocal N z.2 r) 0 ∂_) = _
    rw [integral_sub ((hf (.inr B)).const_mul _) ((hf z.2).const_mul _),
      integral_const_mul, integral_const_mul]
    rfl
  · simp only [classGain, Fin.cons_zero, if_neg hC, integral_zero]

theorem integral_classGain_head_nonpos {ε W : ℝ} (N n c : ℕ) (hn : 2 ≤ n)
    (hε : 0 < ε) {μ : Measure (Value W)} (π : FloorLaw ε W μ)
    (hIC : AllActionOptimal π (fun z => floorPayoff N n c (π,z)))
    (a t : ℝ) (B : Icc ε W) :
    (∫ x, classGain (N+1) n c a t B x 0
      ∂(rowLaw (N+1) π.1 : Measure (Fin (N+1) → Value W × FloorAction ε W))) ≤ 0 := by
  let f := fun x : Fin (N+1) → Value W × FloorAction ε W => classGain (N+1) n c a t B x 0
  let cons := fun p : (Value W × FloorAction ε W) ×
      (Fin N → Value W × FloorAction ε W) => Fin.cons (α := fun _ : Fin (N+1) => Value W × FloorAction ε W) p.1 p.2
  have hc : Continuous cons := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_fst
    · exact (continuous_apply j).comp continuous_snd
  have hfm : AEStronglyMeasurable f (rowLaw (N+1) π.1 : Measure _) :=
    (integrable_classGain (N+1) n c hn hε a t B π.1 0).aestronglyMeasurable
  have hint : Integrable (f ∘ cons)
      ((π.1 : Measure (Value W × FloorAction ε W)).prod (rowLaw N π.1 : Measure _)) := by
    exact (integrable_map_measure hfm hc.measurable.aemeasurable).mp
      (integrable_classGain (N+1) n c hn hε a t B π.1 0)
  have hm : (∫ x, f x ∂(rowLaw (N+1) π.1 : Measure _)) =
      ∫ z, ∫ r, f (Fin.cons z r) ∂(rowLaw N π.1 : Measure _) ∂(π.1 : Measure _) := by
    change (∫ x, f x ∂Measure.map cons ((π.1 : Measure _).prod (rowLaw N π.1 : Measure _))) = _
    calc
      _ = ∫ p, f (cons p) ∂((π.1 : Measure _).prod (rowLaw N π.1 : Measure _)) :=
        integral_map hc.measurable.aemeasurable hfm
      _ = _ := integral_prod _ hint
  rw [hm]
  apply integral_nonpos_of_ae
  filter_upwards [hIC] with z hz
  rw [show (∫ r, f (Fin.cons z r) ∂(rowLaw N π.1 : Measure _)) = _ from
    integral_classGain_head_inner N n c hn hε π a t B z]
  split_ifs
  · exact sub_nonpos.mpr (hz (.inr B))
  · exact le_rfl

theorem classGain_relabel {ε W : ℝ} (m n c : ℕ) (hn : 2 ≤ n) (hε : 0 < ε)
    (e : Equiv.Perm (Fin m)) (a t : ℝ) (B : Icc ε W)
    (x : Fin m → Value W × FloorAction ε W) (i : Fin m) :
    classGain m n c a t B (x ∘ e) i = classGain m n c a t B x (e i) := by
  have he : Function.update (fun j => (x (e j)).2) i (.inr B) =
      (Function.update (fun j => (x j).2) (e i) (.inr B)) ∘ e := by
    funext j
    by_cases h : j=i
    · subst j; simp
    · have h' : e j ≠ e i := fun h' => h (e.injective h')
      simp [Function.update_of_ne h, Function.update_of_ne h']
  have hs := success_relabel e n c hn hε (fun j => (x j).2) i
  have hs' := success_relabel e n c hn hε
    (Function.update (fun j => (x j).2) (e i) (.inr B)) i
  change success n c (fun j => (x (e j)).2) i = _ at hs
  simp only [classGain, Function.comp_apply]
  rw [he, hs', hs]

theorem integral_classGain_eq_head {ε W : ℝ} (N n c : ℕ) (hn : 2 ≤ n) (hε : 0 < ε)
    (a t : ℝ) (B : Icc ε W) (π : ProbabilityMeasure (Value W × FloorAction ε W))
    (i : Fin (N+1)) :
    (∫ x, classGain (N+1) n c a t B x i ∂(rowLaw (N+1) π : Measure _)) =
      ∫ x, classGain (N+1) n c a t B x 0 ∂(rowLaw (N+1) π : Measure _) := by
  let e : Equiv.Perm (Fin (N+1)) := Equiv.swap 0 i
  let E := MeasurableEquiv.piCongrLeft (fun _ : Fin (N+1) => Value W × FloorAction ε W) e
  have hmp : MeasurePreserving E (rowLaw (N+1) π : Measure _) (rowLaw (N+1) π : Measure _) := by
    rw [rowLaw_eq_pi]
    exact measurePreserving_piCongrLeft
      (α := fun _ : Fin (N+1) => Value W × FloorAction ε W)
      (fun _ : Fin (N+1) => (π : Measure (Value W × FloorAction ε W))) e
  have he (x : Fin (N+1) → Value W × FloorAction ε W) : E x = x ∘ e := by
    funext j
    simp [E, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, e]
  have hh := hmp.integral_comp' (fun x => classGain (N+1) n c a t B x 0)
  convert hh using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [he, classGain_relabel (N+1) n c hn hε e a t B x 0]
    simp [e])

theorem integral_sum_classGain_nonpos {ε W : ℝ} (N n c : ℕ) (hn : 2 ≤ n)
    (hε : 0 < ε) {μ : Measure (Value W)} (π : FloorLaw ε W μ)
    (hIC : AllActionOptimal π (fun z => floorPayoff N n c (π,z)))
    (a t : ℝ) (B : Icc ε W) :
    (∫ x, ∑ i : Fin (N+1), classGain (N+1) n c a t B x i
      ∂(rowLaw (N+1) π.1 : Measure _)) ≤ 0 := by
  rw [integral_finsetSum _ (fun i _ => integrable_classGain (N+1) n c hn hε a t B π.1 i)]
  apply Finset.sum_nonpos
  intro i _
  rw [integral_classGain_eq_head N n c hn hε a t B π.1 i]
  exact integral_classGain_head_nonpos N n c hn hε π hIC a t B

theorem floor_equilibrium_small_bid_estimate {ε W : ℝ} (N n c : ℕ)
    (hn : 2 ≤ n) (hc1 : 1 ≤ c) (hcm : c < N+1) (hε : 0 < ε)
    {μ : Measure (Value W)} (π : FloorLaw ε W μ)
    (hIC : AllActionOptimal π (fun z => floorPayoff N n c (π,z)))
    (a t : ℝ) (ha : 0 ≤ a) (ht : 0 < t) (B : Icc ε W) (hB : B.1=2*n*t) :
    let q := (π.1 : Measure (Value W × FloorAction ε W)).real {z | smallClass a t z}
    a*q^(N+1)*(1-PayOnce.success n ((c:ℝ)/(N+1))) ≤ 2*n*t*q := by
  simpa only [Nat.cast_add, Nat.cast_one] using source_small_bid_estimate (N+1) n c (Nat.succ_pos _) hn hc1 hcm hε
    a t ha ht B hB π.1
    (integrable_finsetSum _ (fun i _ => integrable_classGain (N+1) n c hn hε a t B π.1 i))
    (integral_sum_classGain_nonpos N n c hn hε π hIC a t B)

theorem floor_equilibrium_small_bid_power {ε W : ℝ} (N n c : ℕ)
    (hN : 0 < N) (hn : 2 ≤ n) (hc1 : 1 ≤ c) (hcm : c < N+1) (hε : 0 < ε)
    {μ : Measure (Value W)} (π : FloorLaw ε W μ)
    (hIC : AllActionOptimal π (fun z => floorPayoff N n c (π,z)))
    (a t : ℝ) (ha : 0 < a) (ht : 0 < t) (B : Icc ε W) (hB : B.1=2*n*t) :
    let q := (π.1 : Measure (Value W × FloorAction ε W)).real {z | smallClass a t z}
    q^N ≤ (2*n*t)/(a*(1-PayOnce.success n ((c:ℝ)/(N+1)))) := by
  let q := (π.1 : Measure (Value W × FloorAction ε W)).real {z | smallClass a t z}
  have hq : 0 ≤ q := ENNReal.toReal_nonneg
  have hgap : 0 < 1-PayOnce.success n ((c:ℝ)/(N+1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      capacity_success_gap_pos n (N+1) c (Nat.succ_pos _) hcm
  change q^N ≤ _
  rcases eq_or_lt_of_le hq with hzero | hpos
  · rw [← hzero, zero_pow (Nat.ne_of_gt hN)]
    positivity
  · have hh := small_bid_bound_divide (N+1) (Nat.succ_le_succ (Nat.zero_le _))
      a (1-PayOnce.success n ((c:ℝ)/(N+1))) n t q ha hgap hpos
      (floor_equilibrium_small_bid_estimate N n c hn hc1 hcm hε π hIC a t ha.le ht B hB)
    simpa only [Nat.add_sub_cancel] using hh

end FCAppendix.Existence.PayOnceBounded
