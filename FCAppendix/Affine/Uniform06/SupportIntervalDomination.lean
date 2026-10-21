import FCAppendix.Ample.RankMeasureTools
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Tactic

noncomputable section

namespace FCAppendix.Affine.Uniform06.SupportIntervalDomination

open MeasureTheory Set Filter Topology

def cumulative (μ : Measure ℝ) (x : ℝ) : ℝ := μ.real univ-μ.real (Ioi x)

theorem cumulative_increment (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b : ℝ} (hab : a ≤ b) :
    cumulative μ b-cumulative μ a = μ.real (Ioc a b) := by
  unfold cumulative
  have h := Ample.RankMeasureTools.strict_tail_sub (μ := μ) hab
  linarith

theorem continuous_cumulative (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hatom : ∀ x : ℝ, μ {x} = 0) : Continuous (cumulative μ) :=
  continuous_const.sub (Ample.RankMeasureTools.continuous_strict_tail μ hatom)

theorem measure_le_of_Ioc_real_le
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμatom : ∀ x : ℝ, μ {x} = 0) (hνatom : ∀ x : ℝ, ν {x} = 0)
    (hI : ∀ a b : ℝ, a ≤ b → μ.real (Ioc a b) ≤ ν.real (Ioc a b)) : μ ≤ ν := by
  let F : ℝ → ℝ := fun x => cumulative ν x-cumulative μ x
  have hinc {a b : ℝ} (hab : a ≤ b) :
      F b-F a = ν.real (Ioc a b)-μ.real (Ioc a b) := by
    have hν := cumulative_increment ν hab
    have hμ := cumulative_increment μ hab
    dsimp [F]
    linarith
  have hmono : Monotone F := by
    intro a b hab
    have h := hI a b hab
    have he := hinc hab
    linarith
  have hcont : Continuous F :=
    (continuous_cumulative ν hνatom).sub (continuous_cumulative μ hμatom)
  let G : StieltjesFunction ℝ :=
    { toFun := F
      mono' := hmono
      right_continuous' := fun x => hcont.continuousAt.continuousWithinAt }
  have hdecomp : ν = μ+G.measure := by
    apply Measure.ext_of_Ioc ν (μ+G.measure)
    intro a b hab
    have hnonneg : 0 ≤ F b-F a := sub_nonneg.mpr (hmono hab.le)
    have hGfinite : G.measure (Ioc a b) ≠ ⊤ := by
      rw [G.measure_Ioc]
      exact ENNReal.ofReal_ne_top
    have haddfinite : (μ+G.measure) (Ioc a b) ≠ ⊤ := by
      rw [Measure.add_apply]
      exact ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _,hGfinite⟩
    apply (measureReal_eq_measureReal_iff (measure_ne_top ν _) haddfinite).mp
    rw [measureReal_add_apply (measure_ne_top μ _) hGfinite]
    have hGreal : G.measure.real (Ioc a b) = F b-F a := by
      unfold Measure.real
      rw [G.measure_Ioc,ENNReal.toReal_ofReal hnonneg]
    rw [hGreal,hinc hab.le]
    ring
  rw [hdecomp]
  exact le_add_of_nonneg_right (show (0 : Measure ℝ) ≤ G.measure from bot_le)

theorem extend_short_interval_from_support
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {S : Set ℝ} (hS : IsClosed S) (hfull : ∀ᵐ x ∂μ, x ∈ S)
    (hatom : ∀ x : ℝ, μ {x} = 0)
    {lo hi δ : ℝ}
    (hanchor : ∀ a ∈ S, ∀ b : ℝ,
      a ∈ Icc lo hi → b ∈ Icc lo hi → a ≤ b → b-a ≤ δ →
      μ.real (Ioc a b) ≤ ν.real (Ioc a b))
    {u v : ℝ} (hu : u ∈ Icc lo hi) (hv : v ∈ Icc lo hi)
    (_huv : u ≤ v) (hsmall : v-u ≤ δ) :
    μ.real (Ioc u v) ≤ ν.real (Ioc u v) := by
  classical
  let K : Set ℝ := Icc u v ∩ S
  by_cases hne : K.Nonempty
  · have hcompact : IsCompact K := isCompact_Icc.inter_right hS
    obtain ⟨a,ha⟩ := hcompact.exists_isLeast hne
    have hau : u ≤ a := ha.1.1.1
    have hav : a ≤ v := ha.1.1.2
    have han : ∀ᵐ x ∂μ, x ≠ a := by
      rw [ae_iff]
      simpa using hatom a
    have he : μ.real (Ioc u v) = μ.real (Ioc a v) := by
      apply measureReal_congr
      filter_upwards [hfull,han] with x hx hxa
      change (u < x ∧ x ≤ v) = (a < x ∧ x ≤ v)
      apply propext
      constructor
      · rintro ⟨hux,hxv⟩
        have hax := ha.2 (show x ∈ K from ⟨⟨hux.le,hxv⟩,hx⟩)
        exact ⟨lt_of_le_of_ne hax (Ne.symm hxa),hxv⟩
      · rintro ⟨hax,hxv⟩
        exact ⟨hau.trans_lt hax,hxv⟩
    rw [he]
    exact (hanchor a ha.1.2 v ⟨hu.1.trans hau,hav.trans hv.2⟩ hv hav
      (by linarith)).trans (measureReal_mono (fun _ hx =>
        ⟨hau.trans_lt hx.1,hx.2⟩))
  · have hzero : μ.real (Ioc u v) = 0 := by
      have he : μ.real (Ioc u v) = μ.real (∅ : Set ℝ) := by
        apply measureReal_congr
        filter_upwards [hfull] with x hx
        change (u < x ∧ x ≤ v) = False
        apply propext
        constructor
        · rintro ⟨hux,hxv⟩
          exact hne ⟨x,⟨hux.le,hxv⟩,hx⟩
        · intro h
          exact h.elim
      simpa using he
    rw [hzero]
    exact measureReal_nonneg

theorem monotoneOn_of_uniform_short_steps
    {F : ℝ → ℝ} {lo hi δ : ℝ} (hδ : 0 < δ)
    (hstep : ∀ a ∈ Icc lo hi, ∀ b ∈ Icc lo hi,
      a ≤ b → b-a ≤ δ → F a ≤ F b) : MonotoneOn F (Icc lo hi) := by
  intro a ha b hb hab
  obtain ⟨n,hn⟩ := exists_nat_gt ((b-a)/δ)
  let N : ℕ := n+1
  have hN : 0 < (N : ℝ) := by dsimp [N]; positivity
  let d : ℝ := (b-a)/N
  have hd0 : 0 ≤ d := div_nonneg (sub_nonneg.mpr hab) hN.le
  have hdδ : d ≤ δ := by
    apply (div_le_iff₀ hN).mpr
    have hn' := (div_lt_iff₀ hδ).mp hn
    dsimp [N]
    push_cast
    nlinarith
  have hNd : (N : ℝ)*d = b-a := by
    dsimp [d]
    field_simp [hN.ne']
  have hmem (j : ℕ) (hj : j ≤ N) : a+j*d ∈ Icc lo hi := by
    have hjN : (j : ℝ) ≤ N := by exact_mod_cast hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    constructor
    · nlinarith [ha.1,mul_nonneg hj0 hd0]
    · nlinarith [hb.2,mul_le_mul_of_nonneg_right hjN hd0]
  have hchain (j : ℕ) (hj : j ≤ N) : F a ≤ F (a+j*d) := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hj' : j ≤ N := by omega
      have hprev := ih hj'
      have hnext : F (a+j*d) ≤ F (a+(j+1 : ℕ)*d) := by
        apply hstep _ (hmem j hj') _ (hmem (j+1) hj)
        · push_cast
          linarith
        · push_cast
          linarith
      exact hprev.trans hnext
  have h := hchain N le_rfl
  have he : a+(N : ℝ)*d = b := by linarith
  simpa only [he] using h

theorem all_intervals_from_local_support_bounds
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {S : Set ℝ} (hS : IsClosed S) (hfull : ∀ᵐ x ∂μ, x ∈ S)
    (hatom : ∀ x : ℝ, μ {x} = 0)
    {lo hi δ : ℝ} (hδ : 0 < δ)
    (hanchor : ∀ a ∈ S, ∀ b : ℝ,
      a ∈ Icc lo hi → b ∈ Icc lo hi → a ≤ b → b-a ≤ δ →
      μ.real (Ioc a b) ≤ ν.real (Ioc a b)) :
    ∀ a ∈ Icc lo hi, ∀ b ∈ Icc lo hi, a ≤ b →
      μ.real (Ioc a b) ≤ ν.real (Ioc a b) := by
  let F : ℝ → ℝ := fun x => cumulative ν x-cumulative μ x
  have hinc {a b : ℝ} (hab : a ≤ b) :
      F b-F a = ν.real (Ioc a b)-μ.real (Ioc a b) := by
    have hν := cumulative_increment ν hab
    have hμ := cumulative_increment μ hab
    dsimp [F]
    linarith
  have hmono : MonotoneOn F (Icc lo hi) := by
    apply monotoneOn_of_uniform_short_steps hδ
    intro a ha b hb hab hsmall
    have h := extend_short_interval_from_support μ ν hS hfull hatom
      hanchor ha hb hab hsmall
    have he := hinc hab
    linarith
  intro a ha b hb hab
  have h := hmono ha hb hab
  have he := hinc hab
  linarith

theorem restricted_singleton_null
    (μ : Measure ℝ) (hatom : ∀ x : ℝ, μ {x} = 0) (J : Set ℝ) (x : ℝ) :
    (μ.restrict J) {x} = 0 := by
  rw [Measure.restrict_apply (measurableSet_singleton x)]
  exact measure_mono_null inter_subset_left (hatom x)

theorem measure_restrict_le_of_Ioc_real_le
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμatom : ∀ x : ℝ, μ {x} = 0) (hνatom : ∀ x : ℝ, ν {x} = 0)
    {lo hi : ℝ}
    (hI : ∀ a ∈ Icc lo hi, ∀ b ∈ Icc lo hi, a ≤ b →
      μ.real (Ioc a b) ≤ ν.real (Ioc a b)) :
    μ.restrict (Ioc lo hi) ≤ ν.restrict (Ioc lo hi) := by
  apply measure_le_of_Ioc_real_le
    (μ.restrict (Ioc lo hi)) (ν.restrict (Ioc lo hi))
    (restricted_singleton_null μ hμatom _) (restricted_singleton_null ν hνatom _)
  intro u v _huv
  rw [measureReal_restrict_apply measurableSet_Ioc,
    measureReal_restrict_apply measurableSet_Ioc]
  have he : Ioc u v ∩ Ioc lo hi = Ioc (max u lo) (min v hi) := by
    ext x
    simp only [mem_inter_iff,mem_Ioc,max_lt_iff,le_min_iff]
    tauto
  rw [he]
  by_cases hab : max u lo ≤ min v hi
  · apply hI _ ⟨le_max_right u lo,hab.trans (min_le_right v hi)⟩
      _ ⟨(le_max_right u lo).trans hab,min_le_right v hi⟩ hab
  · rw [Ioc_eq_empty_of_le (lt_of_not_ge hab).le,measureReal_empty]
    simp

theorem measure_restrict_le_of_local_support_bounds
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {S : Set ℝ} (hS : IsClosed S) (hfull : ∀ᵐ x ∂μ, x ∈ S)
    (hμatom : ∀ x : ℝ, μ {x} = 0) (hνatom : ∀ x : ℝ, ν {x} = 0)
    {lo hi δ : ℝ} (hδ : 0 < δ)
    (hanchor : ∀ a ∈ S, ∀ b : ℝ,
      a ∈ Icc lo hi → b ∈ Icc lo hi → a ≤ b → b-a ≤ δ →
      μ.real (Ioc a b) ≤ ν.real (Ioc a b)) :
    μ.restrict (Ioc lo hi) ≤ ν.restrict (Ioc lo hi) := by
  apply measure_restrict_le_of_Ioc_real_le μ ν hμatom hνatom
  exact all_intervals_from_local_support_bounds μ ν hS hfull hμatom hδ hanchor

end FCAppendix.Affine.Uniform06.SupportIntervalDomination
