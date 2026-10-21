import FCAppendix.Affine.Hybrid.FavoredAtomGain
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory Set Filter Topology
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def focalBoxBids {L U : ℝ} (B : Icc L U) (i : ι) (x : ι→Icc L U) : ι→ℝ :=
  Function.update (fun j=>(x j:ℝ)) i B

omit [Fintype ι] in
lemma continuous_focalBoxBids {L U : ℝ} (B : Icc L U) (i : ι) :
    Continuous (focalBoxBids B i) := by
  apply continuous_pi
  intro j
  by_cases hj : j=i
  · simpa only [focalBoxBids,Function.update_self,hj] using
      (continuous_const : Continuous (fun _ : ι→Icc L U=>(B:ℝ)))
  · simp only [focalBoxBids,Function.update_of_ne hj]
    exact continuous_subtype_val.comp (continuous_apply j)

omit [Fintype ι] in
lemma focalBoxBids_mem {L U : ℝ} (B : Icc L U) (i : ι) (x : ι→Icc L U) (j : ι) :
    focalBoxBids B i x j∈Icc L U := by
  by_cases hj : j=i
  · subst j; simpa only [focalBoxBids,Function.update_self] using B.property
  · simpa only [focalBoxBids,Function.update_of_ne hj] using (x j).property

lemma continuous_favoredTargetPayoff_box {L U : ℝ} (hL : 0<L) (B : Icc L U)
    (xi eta v : ℝ) (r K : ℕ) (i t : ι) (hN : 2≤Fintype.card ι)
    (hK : 1≤K) (hKN : K<Fintype.card ι) :
    Continuous (fun x : ι→Icc L U=>favoredTargetPayoff xi eta v (focalBoxBids B i x) r K i t) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (continuousAt_favoredTargetPayoff xi eta v _ r K i t hN hK hKN
    (fun j=>hL.trans_le (focalBoxBids_mem B i x j).1)).comp
      (continuous_focalBoxBids B i).continuousAt

lemma integrable_sourceOwnerJump_box [Nonempty ι] {L U : ℝ} (hL : 0<L) (B : Icc L U)
    (xi eta v : ℝ) (r K : ℕ) (i : ι) (hN : 2≤Fintype.card ι)
    (hK : 1≤K) (hKN : K<Fintype.card ι)
    (mu : Measure (ι→Icc L U)) [IsFiniteMeasure mu] :
    Integrable (fun x=>sourceOwnerJump xi eta v (focalBoxBids B i x) r K i) mu := by
  have hterm (j : ι) : Integrable (fun x : ι→Icc L U=>
      if j≠i ∧ (x j:ℝ)=(B:ℝ) then
        favoredTargetPayoff xi eta v (focalBoxBids B i x) r K i i-
        favoredTargetPayoff xi eta v (focalBoxBids B i x) r K i j else 0) mu := by
    have hc := (continuous_favoredTargetPayoff_box hL B xi eta v r K i i hN hK hKN).sub
      (continuous_favoredTargetPayoff_box hL B xi eta v r K i j hN hK hKN)
    have hm : MeasurableSet {x : ι→Icc L U | j≠i ∧ (x j:ℝ)=(B:ℝ)} :=
      (MeasurableSet.const (j≠i)).inter (measurableSet_eq_fun
        (continuous_subtype_val.comp (continuous_apply j)).measurable measurable_const)
    apply ((hc.integrable_of_hasCompactSupport (μ:=mu)
      (HasCompactSupport.of_compactSpace _)).indicator hm).congr
    filter_upwards [] with x
    simp only [Set.indicator,Set.mem_setOf_eq,Pi.sub_apply]
  have hi := (integrable_finsetSum Finset.univ (fun j _=>hterm j)).div_const (2*rankDenominator ι)
  apply hi.congr
  filter_upwards [] with x
  unfold sourceOwnerJump tiedRivals
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j=i
  · subst j
    simp
  · simp [focalBoxBids,hj]

theorem expected_sourceOwnerJump_lower_atom [Nonempty ι] {xi eta v L U vmin : ℝ}
    (hL : 0<L) (B : Icc L U) (r K : ℕ) (i j : ι) (hij : i≠j)
    (hN : 2≤Fintype.card ι) (hK : 1≤K) (hKN : K<Fintype.card ι)
    (heta : 0<eta) (hUv : U<vmin) (hvv : vmin≤v)
    (mu : Measure (ι→Icc L U)) [IsProbabilityMeasure mu] :
    (1-fillFraction (ι:=ι) K)*(min (vmin-U) (eta*L)/2)/
        ((Fintype.card ι:ℝ)*((Fintype.card ι:ℝ)+1))*mu.real {x | (x j:ℝ)=(B:ℝ)}≤
      ∫x,sourceOwnerJump xi eta v (focalBoxBids B i x) r K i ∂mu := by
  let C:=(1-fillFraction (ι:=ι) K)*(min (vmin-U) (eta*L)/2)/
    ((Fintype.card ι:ℝ)*((Fintype.card ι:ℝ)+1))
  have hC : 0≤C := by
    have hf:=fillFraction_bounds hN hK hKN.le
    have hm : 0 ≤ min (vmin-U) (eta*L) := le_min (sub_pos.mpr hUv).le (mul_pos heta hL).le
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr hf.2) (div_nonneg hm (by norm_num))) (by positivity)
  let E:Set (ι→Icc L U):={x | (x j:ℝ)=(B:ℝ)}
  have hE : MeasurableSet E := measurableSet_eq_fun
    (continuous_subtype_val.comp (continuous_apply j)).measurable measurable_const
  have hpoint (x : ι→Icc L U) : E.indicator (fun _=>C) x≤
      sourceOwnerJump xi eta v (focalBoxBids B i x) r K i := by
    have hbL : L≤focalBoxBids B i x i := (focalBoxBids_mem B i x i).1
    have hbU : focalBoxBids B i x i≤U := (focalBoxBids_mem B i x i).2
    by_cases hx : x∈E
    · rw [Set.indicator_of_mem hx]
      apply sourceOwnerJump_lower_one_tie _ r K i j hij _ hN hK hKN heta hL hbL hbU hUv hvv
      simpa only [E,Set.mem_setOf_eq,focalBoxBids,Function.update_self,
        Function.update_of_ne hij.symm] using hx.symm
    · rw [Set.indicator_of_notMem hx]
      have hh:=sourceOwnerJump_lower (xi:=xi) _ r K i hN hK hKN.le heta hL hbL hbU hUv hvv
      exact le_trans (by
        have hf:=fillFraction_bounds hN hK hKN.le
        have hm : 0 ≤ min (vmin-U) (eta*L) := le_min (sub_pos.mpr hUv).le (mul_pos heta hL).le
        exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hf.2))
          (div_nonneg hm (by norm_num))) (mul_nonneg (by norm_num) rankDenominator_pos.le)) hh
  have hh:=integral_mono ((integrable_const C).indicator hE)
    (integrable_sourceOwnerJump_box hL B xi eta v r K i hN hK hKN mu) hpoint
  rw [integral_indicator_const C hE] at hh
  simpa only [smul_eq_mul,mul_comm,C,E] using hh

theorem iid_expected_sourceOwnerJump_lower_atom [Nonempty ι] {xi eta v L U vmin : ℝ}
    (hL : 0<L) (B : Icc L U) (r K : ℕ) (i j : ι) (hij : i≠j)
    (hN : 2≤Fintype.card ι) (hK : 1≤K) (hKN : K<Fintype.card ι)
    (heta : 0<eta) (hUv : U<vmin) (hvv : vmin≤v)
    (nu : Measure (Icc L U)) [IsProbabilityMeasure nu] :
    (1-fillFraction (ι:=ι) K)*(min (vmin-U) (eta*L)/2)/
        ((Fintype.card ι:ℝ)*((Fintype.card ι:ℝ)+1))*nu.real {B}≤
      ∫x,sourceOwnerJump xi eta v (focalBoxBids B i x) r K i
        ∂Measure.pi (fun _ : ι=>nu) := by
  have hh:=expected_sourceOwnerJump_lower_atom (xi:=xi) hL B r K i j hij hN hK hKN heta hUv hvv
    (Measure.pi (fun _ : ι=>nu))
  have he : (Measure.pi (fun _ : ι=>nu)).real {x | (x j:ℝ)=(B:ℝ)}=nu.real {B} := by
    have hm:= (measurePreserving_eval (μ:=fun _ : ι=>nu) j).map_eq
    have hset : {x : ι→Icc L U | (x j:ℝ)=(B:ℝ)}=
        (Function.eval j : (ι→Icc L U)→Icc L U)⁻¹' ({B}:Set (Icc L U)) := by
      ext x
      simp only [mem_setOf_eq,mem_preimage,mem_singleton_iff]
      exact Subtype.coe_inj
    have hmeasure:=congrArg (fun m : Measure (Icc L U)=>m {B}) hm
    rw [Measure.map_apply (measurable_pi_apply j) (measurableSet_singleton B)] at hmeasure
    simpa only [hset,measureReal_def] using congrArg ENNReal.toReal hmeasure

  rwa [he] at hh

end FCAppendix.Affine.Hybrid
