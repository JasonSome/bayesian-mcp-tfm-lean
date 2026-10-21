import FCAppendix.Affine.Tail04.EqualPrivateSignal
import FCAppendix.Affine.Hybrid.FavoredNoisyPayoff

noncomputable section
namespace FCAppendix.Affine.Tail04.PrivatePayoffContinuity
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open scoped BigOperators
open EqualPrivateSignal

local instance (N H : ℕ) : TopologicalSpace (Finset (Target N H)) := ⊥
local instance (N H : ℕ) : DiscreteTopology (Finset (Target N H)) := ⟨rfl⟩
local instance (N H : ℕ) : MeasurableSpace (Finset (Target N H)) := ⊤
local instance (N H : ℕ) : BorelSpace (Finset (Target N H)) := ⟨borel_eq_top_of_discrete.symm⟩

abbrev Input (N H : ℕ) (R Rp : ℝ) :=
  (Fin N → ℝ) × (Fin N → ℝ) × Signal H R Rp

def inputScore {N H c : ℕ} {R Rp : ℝ} (ξ : ℝ)
    (z : Input N H R Rp) (a : Action N H c) : ℝ :=
  revenue z.1 z.2.1 ξ z.2.2 (selected z.2.2 a)

lemma continuous_inputScore {N H c : ℕ} {R Rp : ℝ} (ξ : ℝ) :
    Continuous (fun z : Input N H R Rp × Action N H c => inputScore ξ z.1 z.2) := by
  have hsa : Continuous (fun z : Input N H R Rp × Action N H c => (z.1.2.2,z.2)) :=
    (continuous_snd.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd
  simp only [inputScore,← score_eq_revenue,EqualPrivateFrontier.score,
    ContinuousMap.add_apply,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
  apply ((privateReceipt N H c R Rp).continuous.comp hsa).add
  apply continuous_finsetSum
  intro i _
  exact (((continuous_apply i).comp (continuous_fst.comp continuous_fst)).mul
    (continuous_const.sub (continuous_const.mul
      ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_fst)))))).mul
    ((activeIndicator N H c R Rp i).continuous.comp hsa)

def Best {N H c : ℕ} {R Rp : ℝ} (ξ : ℝ) (z : Input N H R Rp)
    (a : Action N H c) : Prop :=
  ∀ a' : Action N H c, inputScore ξ z a' ≤ inputScore ξ z a

lemma isClosed_best {N H c : ℕ} {R Rp : ℝ} (ξ : ℝ) :
    IsClosed {z : Input N H R Rp × Action N H c | Best ξ z.1 z.2} := by
  simp only [Best,setOf_forall]
  exact isClosed_iInter fun a' => isClosed_le
    ((continuous_inputScore ξ).comp (continuous_fst.prodMk continuous_const))
    (continuous_inputScore ξ)

def chosen {N H c : ℕ} {R Rp : ℝ} (ξ : ℝ) (z : Input N H R Rp) : Action N H c :=
  FiniteSelector.select (inputScore ξ z)

lemma chosen_best {N H c : ℕ} {R Rp : ℝ} (ξ : ℝ) (z : Input N H R Rp) :
    Best (c := c) ξ z (chosen (c := c) ξ z) :=
  FiniteSelector.select_max (inputScore (c := c) ξ z)

lemma measurable_chosen {N H c : ℕ} {R Rp : ℝ} (ξ : ℝ) :
    Measurable (chosen (N := N) (H := H) (c := c) (R := R) (Rp := Rp) ξ) :=
by
  apply FiniteSelector.measurable_select
  intro a
  simpa only [Function.comp_def] using
    ((continuous_inputScore (c := c) ξ).comp
      (show Continuous (fun z : Input N H R Rp => (z,a)) from
        continuous_id.prodMk continuous_const)).measurable

lemma residualOptimal_of_best {N H c : ℕ} {R Rp : ℝ} (ξ : ℝ)
    (z : Input N H R Rp) (a : Action N H c) (ha : Best ξ z a) :
    ∀ S, Feasible N H c (marks z.2.2) S →
      revenue z.1 z.2.1 ξ z.2.2 S ≤ revenue z.1 z.2.1 ξ z.2.2 (selected z.2.2 a) := by
  intro S hS
  have hh := ha (actionFor N H c (marks z.2.2) S hS)
  simpa only [inputScore,selected_actionFor] using hh

def Regular {N H : ℕ} {R Rp : ℝ} (ξ : ℝ) (j : Fin H) : Set (Input N H R Rp) :=
  {z | 0 < partialBid (z.2.2 j) ∧ ∀ i : Target N H, i ≠ Sum.inr j →
    itemReceipt z.1 z.2.1 ξ z.2.2 i ≠ partialBid (z.2.2 j)}

lemma continuous_inputReceipt {N H : ℕ} {R Rp : ℝ} (ξ : ℝ) (i : Target N H) :
    Continuous (fun z : Input N H R Rp => itemReceipt z.1 z.2.1 ξ z.2.2 i) := by
  cases i with
  | inl i =>
    exact ((continuous_apply i).comp continuous_fst).mul
      (continuous_const.sub (continuous_const.mul
        ((continuous_apply i).comp (continuous_fst.comp continuous_snd))))
  | inr i =>
    exact continuous_partialBid.comp
      ((continuous_apply i).comp (continuous_snd.comp continuous_snd))

lemma isOpen_regular {N H : ℕ} {R Rp : ℝ} (ξ : ℝ) (j : Fin H) :
    IsOpen (Regular (N := N) (R := R) (Rp := Rp) ξ j) := by
  have hj : Continuous (fun z : Input N H R Rp => partialBid (z.2.2 j)) :=
    continuous_partialBid.comp ((continuous_apply j).comp (continuous_snd.comp continuous_snd))
  have he : Regular (N := N) (R := R) (Rp := Rp) ξ j =
      {z | 0 < partialBid (z.2.2 j)} ∩
        ⋂ i : Target N H, {z | i ≠ Sum.inr j →
          itemReceipt z.1 z.2.1 ξ z.2.2 i ≠ partialBid (z.2.2 j)} := by
    ext z
    simp [Regular]
  rw [he]
  apply (isOpen_lt continuous_const hj).inter
  apply isOpen_iInter_of_finite
  intro i
  by_cases hij : i = Sum.inr j
  · simp only [hij,ne_eq,not_true_eq_false,false_implies,setOf_true]
    exact isOpen_univ
  · simpa only [ne_eq,hij,not_false_eq_true,true_implies,Set.compl_setOf] using
      (isClosed_eq (continuous_inputReceipt ξ i) hj).isOpen_compl

lemma privateIndicator_unique {N H c : ℕ} {R Rp : ℝ} (ξ : ℝ) (j : Fin H)
    (z : Input N H R Rp) (hz : z ∈ Regular ξ j) (a a' : Action N H c)
    (ha : Best ξ z a) (ha' : Best ξ z a') :
    privateIndicator N H c R Rp j (z.2.2,a) =
      privateIndicator N H c R Rp j (z.2.2,a') := by
  have hh := private_membership_unique z.1 z.2.1 ξ z.2.2
    (selected z.2.2 a) (selected z.2.2 a') j
    (selected_feasible _ _) (selected_feasible _ _)
    (residualOptimal_of_best ξ z a ha) (residualOptimal_of_best ξ z a' ha') hz.1 hz.2
  change (if Sum.inr j ∈ selected z.2.2 a then (1:ℝ) else 0) =
    (if Sum.inr j ∈ selected z.2.2 a' then (1:ℝ) else 0)
  simp only [hh]

def privateValue {N H c : ℕ} {R Rp : ℝ} (ξ : ℝ) (j : Fin H)
    (z : Input N H R Rp) : ℝ := privateIndicator N H c R Rp j (z.2.2,chosen ξ z)

lemma privateValue_bounds {N H c : ℕ} {R Rp : ℝ} (ξ : ℝ) (j : Fin H)
    (z : Input N H R Rp) : 0 ≤ privateValue (c := c) ξ j z ∧ privateValue (c := c) ξ j z ≤ 1 := by
  dsimp [privateValue,privateIndicator]
  split <;> norm_num

lemma measurable_privateValue {N H c : ℕ} {R Rp : ℝ} (ξ : ℝ) (j : Fin H) :
    Measurable (privateValue (N := N) (c := c) (R := R) (Rp := Rp) ξ j) :=
  (privateIndicator N H c R Rp j).continuous.measurable.comp
    ((measurable_snd.comp measurable_snd).prodMk (measurable_chosen ξ))

theorem continuousAt_privateValue {N H c : ℕ} {R Rp : ℝ} (ξ : ℝ) (j : Fin H)
    (z : Input N H R Rp) (hz : z ∈ Regular ξ j) :
    ContinuousAt (privateValue (c := c) ξ j) z := by
  let P := ↥(Regular (N := N) (R := R) (Rp := Rp) ξ j)
  let G : Set (P × Action N H c) := {w | Best ξ w.1.1 w.2}
  have hG : IsClosed G := (isClosed_best (c := c) (R := R) (Rp := Rp) ξ).preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hcont : Continuous (fun p : P => privateValue (c := c) ξ j p.1) := by
    apply EqualPrivateContinuity.continuous_unique_compact_response G hG
      (fun w : P × Action N H c => privateIndicator N H c R Rp j (w.1.1.2.2,w.2))
      ((privateIndicator N H c R Rp j).continuous.comp
        ((continuous_snd.comp (continuous_snd.comp
          (continuous_subtype_val.comp continuous_fst))).prodMk continuous_snd))
    · intro p
      exact ⟨chosen ξ p.1,chosen_best ξ p.1⟩
    · intro p a ha
      exact privateIndicator_unique ξ j p.1 p.2 a (chosen ξ p.1) ha (chosen_best ξ p.1)
  have hOn : ContinuousOn (privateValue (c := c) ξ j) (Regular ξ j) :=
    continuousOn_iff_continuous_restrict.mpr hcont
  exact hOn.continuousAt ((isOpen_regular ξ j).mem_nhds hz)

abbrev FocalInput (N H : ℕ) (R U eps : ℝ) :=
  (Fin N → ℝ) × (Fin N → ℝ) × Icc R U × Signal H R (U*(1+eps))

def noisyInput {N H : ℕ} {R U eps : ℝ} (hR : 0 < R) (heps : 0 ≤ eps)
    (j : Fin H) (p : FocalInput N H R U eps) (u : unitInterval) :
    Input N H R (U*(1+eps)) :=
  (p.1,p.2.1,Function.update p.2.2.2 j (Sum.inr
    ⟨Hybrid.activeNoisyRealBid eps p.2.2.1 u,
      Hybrid.activeNoisyRealBid_mem hR heps p.2.2.1 u⟩))

lemma continuous_noisyInput {N H : ℕ} {R U eps : ℝ} (hR : 0 < R) (heps : 0 ≤ eps)
    (j : Fin H) : Continuous
      (fun z : FocalInput N H R U eps × unitInterval => noisyInput hR heps j z.1 z.2) := by
  have hb : Continuous (fun z : FocalInput N H R U eps × unitInterval => z.1.1) :=
    continuous_fst.comp continuous_fst
  have hq : Continuous (fun z : FocalInput N H R U eps × unitInterval => z.1.2.1) :=
    continuous_fst.comp (continuous_snd.comp continuous_fst)
  have hs : Continuous (fun z : FocalInput N H R U eps × unitInterval => z.1.2.2.2) :=
    continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_fst))
  have hB : Continuous (fun z : FocalInput N H R U eps × unitInterval => (z.1.2.2.1 : ℝ)) :=
    continuous_subtype_val.comp
      (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_fst)))
  have hv : Continuous (fun z : FocalInput N H R U eps × unitInterval =>
      (⟨Hybrid.activeNoisyRealBid eps z.1.2.2.1 z.2,
        Hybrid.activeNoisyRealBid_mem hR heps z.1.2.2.1 z.2⟩ : Icc R (U*(1+eps)))) :=
    (hB.mul (continuous_const.add (continuous_const.mul
      (continuous_subtype_val.comp continuous_snd)))).subtype_mk _
  exact hb.prodMk (hq.prodMk (hs.update j (continuous_inr.comp hv)))

theorem ae_noisyInput_regular {N H : ℕ} {R U eps : ℝ}
    (hR : 0 < R) (heps : 0 < eps) (ξ : ℝ) (j : Fin H)
    (p : FocalInput N H R U eps) :
    ∀ᵐ u : unitInterval ∂volume, noisyInput hR heps.le j p u ∈ Regular ξ j := by
  have hB : (p.2.2.1 : ℝ) ≠ 0 := (hR.trans_le p.2.2.1.2.1).ne'
  have hi (i : Target N H) : ∀ᵐ u : unitInterval ∂volume,
      i ≠ Sum.inr j →
      itemReceipt (noisyInput hR heps.le j p u).1 (noisyInput hR heps.le j p u).2.1 ξ
        (noisyInput hR heps.le j p u).2.2 i ≠
      partialBid ((noisyInput hR heps.le j p u).2.2 j) := by
    cases i with
    | inl i =>
      filter_upwards [Hybrid.ae_activeNoisyRealBid_ne eps p.2.2.1
        (p.1 i*(1-ξ*p.2.1 i)) heps.ne' hB] with u hu _
      simpa only [noisyInput,itemReceipt,Function.update_self,partialBid] using hu.symm
    | inr i =>
      by_cases hij : i=j
      · subst i
        exact ae_of_all _ fun u h => (h rfl).elim
      · filter_upwards [Hybrid.ae_activeNoisyRealBid_ne eps p.2.2.1
          (partialBid (p.2.2.2 i)) heps.ne' hB] with u hu _
        simpa only [noisyInput,itemReceipt,Function.update_self,
          Function.update_of_ne hij,partialBid] using hu.symm
  filter_upwards [ae_all_iff.mpr hi] with u hu
  refine ⟨?_,hu⟩
  have hh := (Hybrid.activeNoisyRealBid_mem hR heps.le p.2.2.1 u).1
  simpa only [noisyInput,Function.update_self,partialBid] using hR.trans_le hh

def smoothedInclusion {N H c : ℕ} {R U eps : ℝ}
    (hR : 0 < R) (heps : 0 ≤ eps) (ξ : ℝ) (j : Fin H)
    (p : FocalInput N H R U eps) : ℝ :=
  ∫ u : unitInterval, privateValue (c := c) ξ j (noisyInput hR heps j p u)

theorem continuous_smoothedInclusion {N H c : ℕ} {R U eps : ℝ}
    (hR : 0 < R) (heps : 0 < eps) (ξ : ℝ) (j : Fin H) :
    Continuous (smoothedInclusion (N := N) (c := c) (U := U) hR heps.le ξ j) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply MeasureTheory.continuousAt_of_dominated
    (F := fun p u => privateValue (c := c) ξ j (noisyInput hR heps.le j p u))
    (bound := fun _ => (1:ℝ))
  · exact Eventually.of_forall fun p => ((measurable_privateValue ξ j).comp
      (((continuous_noisyInput hR heps.le j).comp
        (continuous_const.prodMk continuous_id)).measurable)).aestronglyMeasurable
  · exact Eventually.of_forall fun p => ae_of_all _ fun u => by
      rw [Real.norm_eq_abs,abs_of_nonneg (privateValue_bounds (c := c) ξ j _).1]
      exact (privateValue_bounds (c := c) ξ j _).2
  · exact integrable_const 1
  · filter_upwards [ae_noisyInput_regular hR heps ξ j p] with u hu
    have hn : ContinuousAt (fun z : FocalInput N H R U eps => noisyInput hR heps.le j z u) p := by
      simpa only [Function.comp_def, id_eq] using
        (((continuous_noisyInput hR heps.le j).comp
          (show Continuous (fun z : FocalInput N H R U eps => (z,u)) from
            continuous_id.prodMk continuous_const)).continuousAt (x := p))
    simpa only [Function.comp_def] using
      (continuousAt_privateValue (c := c) ξ j _ hu).comp
        (f := fun z : FocalInput N H R U eps => noisyInput hR heps.le j z u) hn

def smoothedPayment {N H c : ℕ} {R U eps : ℝ}
    (hR : 0 < R) (heps : 0 ≤ eps) (ξ : ℝ) (j : Fin H)
    (p : FocalInput N H R U eps) : ℝ :=
  ∫ u : unitInterval, Hybrid.activeNoisyRealBid eps p.2.2.1 u *
    privateValue (c := c) ξ j (noisyInput hR heps j p u)

lemma continuous_focalPrice {N H : ℕ} {R U eps : ℝ} :
    Continuous (fun z : FocalInput N H R U eps × unitInterval =>
      Hybrid.activeNoisyRealBid eps z.1.2.2.1 z.2) := by
  unfold Hybrid.activeNoisyRealBid
  fun_prop

theorem continuous_smoothedPayment {N H c : ℕ} {R U eps : ℝ}
    (hR : 0 < R) (heps : 0 < eps) (ξ : ℝ) (j : Fin H) :
    Continuous (smoothedPayment (N := N) (c := c) (U := U) hR heps.le ξ j) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply MeasureTheory.continuousAt_of_dominated
    (F := fun p u => Hybrid.activeNoisyRealBid eps p.2.2.1 u *
      privateValue (c := c) ξ j (noisyInput hR heps.le j p u))
    (bound := fun _ => |U*(1+eps)|)
  · exact Eventually.of_forall fun p =>
      (((continuous_focalPrice.comp (continuous_const.prodMk continuous_id)).measurable).mul
        ((measurable_privateValue ξ j).comp (((continuous_noisyInput hR heps.le j).comp
          (continuous_const.prodMk continuous_id)).measurable))).aestronglyMeasurable
  · exact Eventually.of_forall fun p => ae_of_all _ fun u => by
      have hbid := Hybrid.activeNoisyRealBid_mem hR heps.le p.2.2.1 u
      have hpos : 0 ≤ Hybrid.activeNoisyRealBid eps p.2.2.1 u := hR.le.trans hbid.1
      have hval := privateValue_bounds (c := c) ξ j (noisyInput hR heps.le j p u)
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hpos hval.1)]
      exact (mul_le_of_le_one_right hpos hval.2).trans (hbid.2.trans (le_abs_self _))
  · exact integrable_const _
  · filter_upwards [ae_noisyInput_regular hR heps ξ j p] with u hu
    exact ((continuous_focalPrice.comp (continuous_id.prodMk continuous_const)).continuousAt).mul
      (by
        have hn : ContinuousAt (fun z : FocalInput N H R U eps => noisyInput hR heps.le j z u) p := by
          simpa only [Function.comp_def, id_eq] using
            (((continuous_noisyInput hR heps.le j).comp
              (show Continuous (fun z : FocalInput N H R U eps => (z,u)) from
                continuous_id.prodMk continuous_const)).continuousAt (x := p))
        simpa only [Function.comp_def] using
          (continuousAt_privateValue (c := c) ξ j _ hu).comp
            (f := fun z : FocalInput N H R U eps => noisyInput hR heps.le j z u) hn)

abbrev AveragingInput (N H : ℕ) (R U eps : ℝ) :=
  ((Fin N → ℝ) × (Fin N → ℝ) × Icc R U) ×
    ProbabilityMeasure (Signal H R (U*(1+eps)))

def averagedInclusion {N H c : ℕ} {R U eps : ℝ}
    (hR : 0 < R) (heps : 0 ≤ eps) (ξ : ℝ) (j : Fin H)
    (p : AveragingInput N H R U eps) : ℝ :=
  ∫ s, smoothedInclusion (c := c) hR heps ξ j (p.1.1,p.1.2.1,p.1.2.2,s)
    ∂(p.2 : Measure (Signal H R (U*(1+eps))))

def averagedPayment {N H c : ℕ} {R U eps : ℝ}
    (hR : 0 < R) (heps : 0 ≤ eps) (ξ : ℝ) (j : Fin H)
    (p : AveragingInput N H R U eps) : ℝ :=
  ∫ s, smoothedPayment (c := c) hR heps ξ j (p.1.1,p.1.2.1,p.1.2.2,s)
    ∂(p.2 : Measure (Signal H R (U*(1+eps))))

theorem continuous_averagedInclusion {N H c : ℕ} {R U eps : ℝ}
    (hR : 0 < R) (heps : 0 < eps) (ξ : ℝ) (j : Fin H) :
    Continuous (averagedInclusion (N := N) (c := c) (U := U) hR heps.le ξ j) := by
  have hh : Continuous (fun z :
      ((Fin N → ℝ) × (Fin N → ℝ) × Icc R U) × Signal H R (U*(1+eps)) =>
      smoothedInclusion (c := c) hR heps.le ξ j (z.1.1,z.1.2.1,z.1.2.2,z.2)) :=
    (continuous_smoothedInclusion hR heps ξ j).comp
      ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_fst.comp (continuous_snd.comp continuous_fst)).prodMk
          ((continuous_snd.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd)))
  change Continuous (fun p : AveragingInput N H R U eps =>
    ∫ s : Signal H R (U*(1+eps)),
      smoothedInclusion (c := c) hR heps.le ξ j (p.1.1,p.1.2.1,p.1.2.2,s)
      ∂(p.2 : Measure (Signal H R (U*(1+eps)))))
  exact Existence.Distributional.continuous_law_integral _ hh

theorem continuous_averagedPayment {N H c : ℕ} {R U eps : ℝ}
    (hR : 0 < R) (heps : 0 < eps) (ξ : ℝ) (j : Fin H) :
    Continuous (averagedPayment (N := N) (c := c) (U := U) hR heps.le ξ j) := by
  have hh : Continuous (fun z :
      ((Fin N → ℝ) × (Fin N → ℝ) × Icc R U) × Signal H R (U*(1+eps)) =>
      smoothedPayment (c := c) hR heps.le ξ j (z.1.1,z.1.2.1,z.1.2.2,z.2)) :=
    (continuous_smoothedPayment hR heps ξ j).comp
      ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_fst.comp (continuous_snd.comp continuous_fst)).prodMk
          ((continuous_snd.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd)))
  change Continuous (fun p : AveragingInput N H R U eps =>
    ∫ s : Signal H R (U*(1+eps)),
      smoothedPayment (c := c) hR heps.le ξ j (p.1.1,p.1.2.1,p.1.2.2,s)
      ∂(p.2 : Measure (Signal H R (U*(1+eps)))))
  exact Existence.Distributional.continuous_law_integral _ hh

theorem continuous_averagedUtility {N H c : ℕ} {R U eps : ℝ}
    (hR : 0 < R) (heps : 0 < eps) (ξ : ℝ) (j : Fin H) :
    Continuous (fun z : ℝ × AveragingInput N H R U eps =>
      z.1 * averagedInclusion (c := c) hR heps.le ξ j z.2 -
        averagedPayment (c := c) hR heps.le ξ j z.2) :=
  (continuous_fst.mul ((continuous_averagedInclusion hR heps ξ j).comp continuous_snd)).sub
    ((continuous_averagedPayment hR heps ξ j).comp continuous_snd)

def policyInput {N H c : ℕ} {R Rp ξ lo hi : ℝ}
    (p : PolicyParameters N H R Rp lo hi) (s : Signal H R Rp) : Input N H R Rp :=
  (EqualPrivateMeasurable.bids p,policyMean N H c R Rp ξ lo hi p,s)

lemma residualKernel_best {N H c : ℕ} {R Rp ξ lo hi : ℝ}
    (p : PolicyParameters N H R Rp lo hi) (s : Signal H R Rp) :
    ∀ᵐ a ∂residualKernel N H c R Rp ξ lo hi (p,s),
      Best ξ (policyInput (c := c) (ξ := ξ) p s) a := by
  have hh := EqualPrivateMeasurable.policyKernel_best (activeIndicator N H c R Rp)
    (privateReceipt N H c R Rp) ξ lo hi (p,s)
  filter_upwards [hh] with a ha
  intro a'
  have h := ha a'
  simpa only [EqualPrivateMeasurable.localUtility,score_eq_revenue,
    inputScore,policyInput,policyMean] using h

theorem residualKernel_privateValue {N H c : ℕ} {R Rp ξ lo hi : ℝ}
    (p : PolicyParameters N H R Rp lo hi) (s : Signal H R Rp) (j : Fin H)
    (hs : policyInput (c := c) (ξ := ξ) p s ∈ Regular ξ j) :
    ∀ᵐ a ∂residualKernel N H c R Rp ξ lo hi (p,s),
      privateIndicator N H c R Rp j (s,a) =
        privateValue (c := c) ξ j (policyInput (c := c) (ξ := ξ) p s) := by
  filter_upwards [residualKernel_best (c := c) (ξ := ξ) p s] with a ha
  exact privateIndicator_unique ξ j _ hs a (chosen ξ _) ha (chosen_best ξ _)

def focalPolicyInput {N H c : ℕ} {R U eps ξ lo hi : ℝ}
    (p : PolicyParameters N H R (U*(1+eps)) lo hi) (B : Icc R U)
    (s : Signal H R (U*(1+eps))) : FocalInput N H R U eps :=
  (EqualPrivateMeasurable.bids p,policyMean N H c R (U*(1+eps)) ξ lo hi p,B,s)

def actualSmoothedInclusion {N H c : ℕ} {R U eps ξ lo hi : ℝ}
    (hR : 0 < R) (heps : 0 ≤ eps) (j : Fin H)
    (p : PolicyParameters N H R (U*(1+eps)) lo hi) (B : Icc R U)
    (s : Signal H R (U*(1+eps))) : ℝ :=
  ∫ u : unitInterval,
    let t := (noisyInput hR heps j (focalPolicyInput (c := c) (ξ := ξ) p B s) u).2.2
    ∫ a, privateIndicator N H c R (U*(1+eps)) j (t,a)
      ∂residualKernel N H c R (U*(1+eps)) ξ lo hi (p,t)

def actualSmoothedPayment {N H c : ℕ} {R U eps ξ lo hi : ℝ}
    (hR : 0 < R) (heps : 0 ≤ eps) (j : Fin H)
    (p : PolicyParameters N H R (U*(1+eps)) lo hi) (B : Icc R U)
    (s : Signal H R (U*(1+eps))) : ℝ :=
  ∫ u : unitInterval,
    let t := (noisyInput hR heps j (focalPolicyInput (c := c) (ξ := ξ) p B s) u).2.2
    ∫ a, Hybrid.activeNoisyRealBid eps B u * privateIndicator N H c R (U*(1+eps)) j (t,a)
      ∂residualKernel N H c R (U*(1+eps)) ξ lo hi (p,t)

theorem actualSmoothedInclusion_eq {N H c : ℕ} {R U eps ξ lo hi : ℝ}
    (hR : 0 < R) (heps : 0 < eps) (j : Fin H)
    (p : PolicyParameters N H R (U*(1+eps)) lo hi) (B : Icc R U)
    (s : Signal H R (U*(1+eps))) :
    actualSmoothedInclusion (c := c) (ξ := ξ) hR heps.le j p B s =
      smoothedInclusion (c := c) hR heps.le ξ j (focalPolicyInput (c := c) (ξ := ξ) p B s) := by
  apply integral_congr_ae
  filter_upwards [ae_noisyInput_regular hR heps ξ j
    (focalPolicyInput (c := c) (ξ := ξ) p B s)] with u hu
  let t := (noisyInput hR heps.le j (focalPolicyInput (c := c) (ξ := ξ) p B s) u).2.2
  have hh := residualKernel_privateValue (c := c) (ξ := ξ) p t j hu
  calc
    (∫ a, privateIndicator N H c R (U*(1+eps)) j (t,a)
      ∂residualKernel N H c R (U*(1+eps)) ξ lo hi (p,t)) =
      ∫ a, privateValue (c := c) ξ j (policyInput (c := c) (ξ := ξ) p t)
        ∂residualKernel N H c R (U*(1+eps)) ξ lo hi (p,t) := integral_congr_ae hh
    _ = _ := by
      simp
      rfl

theorem actualSmoothedPayment_eq {N H c : ℕ} {R U eps ξ lo hi : ℝ}
    (hR : 0 < R) (heps : 0 < eps) (j : Fin H)
    (p : PolicyParameters N H R (U*(1+eps)) lo hi) (B : Icc R U)
    (s : Signal H R (U*(1+eps))) :
    actualSmoothedPayment (c := c) (ξ := ξ) hR heps.le j p B s =
      smoothedPayment (c := c) hR heps.le ξ j (focalPolicyInput (c := c) (ξ := ξ) p B s) := by
  apply integral_congr_ae
  filter_upwards [ae_noisyInput_regular hR heps ξ j
    (focalPolicyInput (c := c) (ξ := ξ) p B s)] with u hu
  let t := (noisyInput hR heps.le j (focalPolicyInput (c := c) (ξ := ξ) p B s) u).2.2
  have hh := residualKernel_privateValue (c := c) (ξ := ξ) p t j hu
  calc
    (∫ a, Hybrid.activeNoisyRealBid eps B u * privateIndicator N H c R (U*(1+eps)) j (t,a)
      ∂residualKernel N H c R (U*(1+eps)) ξ lo hi (p,t)) =
      ∫ a, Hybrid.activeNoisyRealBid eps B u *
        privateValue (c := c) ξ j (policyInput (c := c) (ξ := ξ) p t)
        ∂residualKernel N H c R (U*(1+eps)) ξ lo hi (p,t) :=
      integral_congr_ae (hh.mono fun a ha => congrArg (fun v => Hybrid.activeNoisyRealBid eps B u*v) ha)
    _ = _ := by
      simp
      rfl

abbrev EndogenousInput (N H : ℕ) (R U eps lo hi : ℝ) :=
  PolicyParameters N H R (U*(1+eps)) lo hi × Icc R U ×
    ProbabilityMeasure (Signal H R (U*(1+eps)))

instance (N H : ℕ) (R U eps lo hi : ℝ) :
    TopologicalSpace (EndogenousInput N H R U eps lo hi) := by
  letI : TopologicalSpace (PolicyParameters N H R (U*(1+eps)) lo hi) := inferInstance
  letI : TopologicalSpace (ProbabilityMeasure (Signal H R (U*(1+eps)))) := inferInstance
  infer_instance

def averagingInput {N H c : ℕ} {R U eps ξ lo hi : ℝ}
    (p : EndogenousInput N H R U eps lo hi) : AveragingInput N H R U eps :=
  ((EqualPrivateMeasurable.bids p.1,policyMean N H c R (U*(1+eps)) ξ lo hi p.1,p.2.1),p.2.2)

lemma continuous_averagingInput {N H c : ℕ} {R U eps ξ lo hi : ℝ}
    (hξ : 0 < ξ) (hlo : 0 < lo) :
    Continuous (averagingInput (N := N) (H := H) (c := c) (R := R) (U := U)
      (eps := eps) (ξ := ξ) (lo := lo) (hi := hi)) :=
  ((EqualPrivateMeasurable.continuous_bids.comp continuous_fst).prodMk
    (((continuous_policyMean N H c R (U*(1+eps)) ξ lo hi hξ hlo).comp continuous_fst).prodMk
      (continuous_fst.comp continuous_snd))).prodMk (continuous_snd.comp continuous_snd)

theorem continuous_endogenousFocalUtility {N H c : ℕ} {R U eps ξ lo hi : ℝ}
    (hR : 0 < R) (heps : 0 < eps) (hξ : 0 < ξ) (hlo : 0 < lo) (j : Fin H) :
    Continuous (fun z : ℝ × EndogenousInput N H R U eps lo hi =>
      z.1 * averagedInclusion (c := c) hR heps.le ξ j (averagingInput (c := c) (ξ := ξ) z.2) -
        averagedPayment (c := c) hR heps.le ξ j (averagingInput (c := c) (ξ := ξ) z.2)) :=
  (continuous_averagedUtility hR heps ξ j).comp
    (continuous_fst.prodMk ((continuous_averagingInput (c := c) hξ hlo).comp continuous_snd))

end FCAppendix.Affine.Tail04.PrivatePayoffContinuity
