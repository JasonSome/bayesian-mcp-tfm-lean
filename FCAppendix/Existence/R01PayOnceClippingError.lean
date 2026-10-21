import FCAppendix.Existence.R01PayOnceClipping

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped BigOperators
open FCAppendix.Existence.Distributional
attribute [local instance] Classical.propDecidable

theorem abs_net_payoff_le (W w b s : ℝ) (hw : w∈Icc 0 W) (hb : b∈Icc 0 W)
    (hs : s∈Icc 0 1) : |(w-b)*s|≤W := by
  have hW : 0≤W := hw.1.trans hw.2
  have hab : |w-b|≤W := abs_le.mpr ⟨by linarith [hw.1,hb.2],by linarith [hw.2,hb.1]⟩
  rw [abs_mul,abs_of_nonneg hs.1]
  exact (mul_le_mul_of_nonneg_right hab hs.1).trans
    (by simpa using mul_le_mul_of_nonneg_left hs.2 hW)

theorem floor_bid_bounds {ε W : ℝ} (hε : 0≤ε) (hW : 0≤W) (a : FloorAction ε W) :
    bid a∈Icc 0 W := by
  cases a with
  | inl u => exact ⟨le_rfl,hW⟩
  | inr b => exact ⟨hε.trans b.2.1,b.2.2⟩

def positiveProfilePayoff {W : ℝ} (m n c : ℕ)
    (x : Fin m→Value W × FloorAction 0 W) (i : Fin m) : ℝ :=
  ((x i).1.1-bid (x i).2)*positiveSuccess n c (fun j=>(x j).2) i

def clippedProfilePayoff {W : ℝ} (m n c : ℕ) (δ : ℝ) (hδW : δ≤W)
    (x : Fin m→Value W × FloorAction 0 W) (i : Fin m) : ℝ :=
  ((x i).1.1-bid (clipToFloor δ hδW (x i).2))*
    success n c (fun j=>clipToFloor δ hδW (x j).2) i

theorem positiveProfilePayoff_abs_le {W : ℝ} (m n c : ℕ) (hn : 2≤n) (hW : 0≤W)
    (x : Fin m→Value W × FloorAction 0 W) (i : Fin m) :
    |positiveProfilePayoff m n c x i|≤W :=
  abs_net_payoff_le W _ _ _ (x i).1.2 (floor_bid_bounds le_rfl hW _)
    (positiveSuccess_bounds n c hn _ _)

theorem clippedProfilePayoff_abs_le {W : ℝ} (m n c : ℕ) (hn : 2≤n)
    (δ : ℝ) (hδ : 0<δ) (hδW : δ≤W)
    (x : Fin m→Value W × FloorAction 0 W) (i : Fin m) :
    |clippedProfilePayoff m n c δ hδW x i|≤W :=
  abs_net_payoff_le W _ _ _ (x i).1.2 (floor_bid_bounds hδ.le (hδ.le.trans hδW) _)
    (success_bounds n c hn hδ _ _)

theorem clippedProfilePayoff_eq_of_safe {W : ℝ} (m n c : ℕ)
    (δ : ℝ) (hδ : 0<δ) (hδW : δ≤W)
    (x : Fin m→Value W × FloorAction 0 W)
    (hx : ∀j,x j∉smallActive δ) (i : Fin m) :
    clippedProfilePayoff m n c δ hδW x i=positiveProfilePayoff m n c x i := by
  have hh : ∀j,present (x j).2=true→δ≤bid (x j).2 := by
    intro j hp
    have hb : ¬bid (x j).2≤δ := fun hb=>hx j ⟨hp,hb⟩
    exact (lt_of_not_ge hb).le
  rw [clippedProfilePayoff,bid_clipToFloor_eq δ hδW _ (hh i),
    clipped_success_eq n c δ hδ hδW _ hh]
  rfl

theorem profile_clipping_error_bound {W : ℝ} (m n c : ℕ) (hn : 2≤n)
    (δ : ℝ) (hδ : 0<δ) (hδW : δ≤W)
    (x : Fin m→Value W × FloorAction 0 W) (i : Fin m) :
    |clippedProfilePayoff m n c δ hδW x i-positiveProfilePayoff m n c x i| ≤
      (2*W)*(∑j:Fin m,if x j∈smallActive δ then (1:ℝ) else 0) := by
  have hW : 0≤W := hδ.le.trans hδW
  by_cases hx : ∀j,x j∉smallActive δ
  · rw [clippedProfilePayoff_eq_of_safe m n c δ hδ hδW x hx i,sub_self,abs_zero]
    positivity
  · have hex : ∃j,x j∈smallActive δ := by simpa only [not_forall,not_not] using hx
    obtain ⟨j,hj⟩ := hex
    have hcount : (1:ℝ)≤∑k:Fin m,if x k∈smallActive δ then 1 else 0 := by
      calc
        (1:ℝ)=(if x j∈smallActive δ then 1 else 0) := by rw [if_pos hj]
        _≤_ := Finset.single_le_sum
          (f:=fun k:Fin m=>if x k∈smallActive δ then (1:ℝ) else 0)
          (fun k _=>by split_ifs <;> norm_num) (Finset.mem_univ j)
    have habs : |clippedProfilePayoff m n c δ hδW x i-positiveProfilePayoff m n c x i| ≤
        |clippedProfilePayoff m n c δ hδW x i|+|positiveProfilePayoff m n c x i| := by
      simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le
        (clippedProfilePayoff m n c δ hδW x i) 0 (positiveProfilePayoff m n c x i)
    have herr := habs.trans (add_le_add (clippedProfilePayoff_abs_le m n c hn δ hδ hδW x i)
        (positiveProfilePayoff_abs_le m n c hn hW x i))
    exact herr.trans (by nlinarith)

theorem measurable_positiveProfilePayoff {W : ℝ} (m n c : ℕ) (hn : 2≤n) (i : Fin m) :
    Measurable (fun x : Fin m→Value W × FloorAction 0 W=>positiveProfilePayoff m n c x i) :=
  (((measurable_pi_apply i).fst.subtype_val).sub
    (continuous_bid.measurable.comp (measurable_pi_apply i).snd)).mul
    ((measurable_positiveSuccess n c hn i).comp
      (measurable_pi_iff.mpr (fun j=>(measurable_pi_apply j).snd)))

theorem continuous_clippedProfilePayoff {W : ℝ} (m n c : ℕ) (hn : 2≤n)
    (δ : ℝ) (hδ : 0<δ) (hδW : δ≤W) (i : Fin m) :
    Continuous (fun x : Fin m→Value W × FloorAction 0 W=>clippedProfilePayoff m n c δ hδW x i) := by
  have hs : Continuous (fun x : Fin m→Value W × FloorAction 0 W=>
      success n c (fun j=>clipToFloor δ hδW (x j).2) i) :=
    (PayOnce.continuous_success n).comp ((continuous_apply i).comp
      ((continuous_marginal n c hn hδ).comp
        (continuous_pi (fun j=>(continuous_clipToFloor δ hδW).comp (continuous_apply j).snd))))
  exact (((continuous_apply i).fst.subtype_val).sub
    (continuous_bid.comp ((continuous_clipToFloor δ hδW).comp (continuous_apply i).snd))).mul hs

theorem integral_profile_clipping_error_bound {W : ℝ} (m n c : ℕ) (hn : 2≤n)
    (δ : ℝ) (hδ : 0<δ) (hδW : δ≤W)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (i : Fin m) :
    (∫x,|clippedProfilePayoff m n c δ hδW x i-positiveProfilePayoff m n c x i|
      ∂(rowLaw m π : Measure _)) ≤ (2*W)*m*(π : Measure (Value W × FloorAction 0 W)).real (smallActive δ) := by
  let ν : Measure (Fin m→Value W × FloorAction 0 W) := rowLaw m π
  have hiP : Integrable (fun x=>positiveProfilePayoff m n c x i) ν := by
    apply Integrable.of_bound (measurable_positiveProfilePayoff (W:=W) m n c hn i).aestronglyMeasurable W
    exact Filter.Eventually.of_forall (fun x=>by
      simpa only [Real.norm_eq_abs] using
        (positiveProfilePayoff_abs_le m n c hn (hδ.le.trans hδW) x i))
  have hiC := (ContinuousMap.equivBoundedOfCompact _ _
    ⟨_,continuous_clippedProfilePayoff m n c hn δ hδ hδW i⟩).integrable ν
  have hcls := (isClosed_smallActive (W:=W) δ).measurableSet
  have hiCount : Integrable (fun x : Fin m→Value W × FloorAction 0 W=>
      ∑j:Fin m,if x j∈smallActive δ then (1:ℝ) else 0) ν := by
    apply integrable_finsetSum
    intro j _
    convert (integrable_const (1:ℝ)).indicator (μ:=ν)
      (hcls.preimage (measurable_pi_apply j)) using 1
    all_goals rfl
  have hh := integral_mono ((hiC.sub hiP).abs) (hiCount.const_mul (2*W))
    (profile_clipping_error_bound m n c hn δ hδ hδW · i)
  rw [integral_const_mul] at hh
  have hcount : (∫x,∑j:Fin m,if x j∈smallActive δ then (1:ℝ) else 0 ∂ν)=
      (m:ℝ)*(π : Measure (Value W × FloorAction 0 W)).real (smallActive δ) := by
    exact integral_row_class_count m π (smallActive δ) hcls
  rw [hcount] at hh
  convert hh using 1 <;> first | rfl | ring

end FCAppendix.Existence.PayOnceBounded
