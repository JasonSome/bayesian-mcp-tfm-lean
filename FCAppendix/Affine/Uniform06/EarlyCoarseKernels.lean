import FCAppendix.Affine.Uniform06.EarlyCoarseMargins

noncomputable section
namespace FCAppendix.Affine.Uniform06.EarlyCoarseKernels

open MeasureTheory Set Filter LowBody
open scoped Topology
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource MixedIntervalLLT
open SourceCoarseAsymptotics EarlyCoarseMargins

theorem source_coarse_from_early_joint_limit (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ)) (G0 : ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 G0))
    (hvalue : ∀ n,(G n:Measure (ℝ × ℝ)).map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hvalue0 : (G0:Measure (ℝ × ℝ)).map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hbelow0 : ∀ᵐ p ∂(G0:Measure (ℝ × ℝ)),p.2 ≤ p.1)
    (hactive0 : ∀ᵐ p ∂(G0:Measure (ℝ × ℝ)),p.1 ∈ Ioc (entry i) (cutoff i) →
      p.2=ActiveGraphComponent.activeBid i p.1)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (b θ : ℕ → ℝ)
    (g : ℕ → GuardData) (cm : (n : ℕ) → (Fin (m n-1) → Fin 4) → ℝ)
    {hi z : ℝ} (hhi : hi < entry i) (hz : z ∈ Ico (1/2:ℝ) (x i))
    (hband : ∀ n,b n ∈ Icc (cutoff i/2) hi)
    (hblim : Tendsto b atTop (𝓝 (z*cutoff i)))
    (hcap : ∀ᶠ n in atTop,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p.2 ≤ ReceiptGap.cap i)
    (hactive : ∀ᶠ n in atTop,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),
      p.1 ∈ Ioc (EarlyRankCeiling.ceilingValue i) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ cutoff i/10000)
    (hmatch : ∀ᶠ n in atTop,
      SubentryTilt.mean (MixedLaw.law i (MixedLaw.physicalLowerLaw i (b n)
        (G n:Measure (ℝ × ℝ)))) Prod.fst (θ n)=
          (capacity (m n):ℝ)/((m n-1:ℕ):ℝ))
    (hL : Tendsto (fun n => (g n).multiplier) atTop (𝓝 (entry i)))
    (hR : ∀ᶠ n in atTop,(g n).radius ≤ cutoff i/100)
    (hg : ∀ᶠ n in atTop,0 < (g n).margin ∧ 0 < (g n).population ∧ 0 < (g n).requiredDemand) :
    ∃ cC UC UR : ℝ,0 < cC ∧ 0 < UC ∧ 0 < UR ∧ ∀ᶠ n in atTop,
      let I := ExactUntilting.cost (source i (G n:Measure (ℝ × ℝ)))
        (demand (xi i) (b n)) (θ n) (capacity (m n)) (m n-1)
      let C := sourceCanonicalMarginal i (m n) (G n:Measure (ℝ × ℝ)) (g n) (cm n) (b n)
      let R := sourceCanonicalDuplicate i (m n) (G n:Measure (ℝ × ℝ)) (g n) (cm n) (b n)
      cC*Real.exp (-I)/((m n-1:ℕ):ℝ)^2 ≤ C ∧
      C ≤ UC*Real.exp (-I)/((m n-1:ℕ):ℝ)^2 ∧
      R ≤ UR*Real.exp (-I)/((m n-1:ℕ):ℝ)^3 ∧
      0 < C ∧ 0 ≤ R/C ∧ R/C ≤ (UR/cC)/((m n-1:ℕ):ℝ) := by
  have hb (n : ℕ) : 0 < b n := (half_pos (cutoff_pos i)).trans_le (hband n).1
  obtain ⟨θ0,hθ0,hθ,n0,A,hAN,hAlaw,hAX,hAY,hgap⟩ :=
    RawCenteredArray.exists_raw_array_from_early_joint_limit i G G0 hG hvalue0 hbelow0 hactive0
      b θ hb hz hblim m hm hmatch
  let Θ := θ0+1
  have hΘ : 0 < Θ := by dsimp [Θ]; linarith
  have hθbounds : ∀ᶠ n in atTop,0 < θ n ∧ θ n ≤ Θ := by
    have hl := hθ.eventually (Ioi_mem_nhds hθ0)
    have hu := hθ.eventually (Iio_mem_nhds (show θ0 < Θ by dsimp [Θ]; linarith))
    filter_upwards [hl,hu] with n hln hun
    exact ⟨hln,hun.le⟩
  have hrawMatch : ∀ᶠ n in atTop,
      (∫ r,demand (xi i) (b n) r ∂tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))=
        (capacity (m n):ℝ)/((m n-1:ℕ):ℝ) := by
    filter_upwards [hmatch] with n hn
    have hp := tilted_point_preserving i (G n:Measure (ℝ × ℝ)) (hb n) (θ n)
    have hh := integral_map (μ := tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n)) (f := Prod.fst) hp.measurable.aemeasurable measurable_fst.aestronglyMeasurable
    rw [hp.map_eq] at hh
    have hh := hh.symm
    change (∫ r,demand (xi i) (b n) r ∂tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))=_ at hh
    exact hh.trans hn
  obtain ⟨lo,ε,q,a,d,hlo,hε,hq,ha,hd,hscalar⟩ := eventual_source_margins i G m b θ g hm hhi hΘ
    hband hvalue hcap hactive hθbounds hrawMatch hL hR hg
  let G' := fun n => G (n+n0)
  let m' := fun n => m (n+n0)
  let b' := fun n => b (n+n0)
  let θ' := fun n => θ (n+n0)
  let g' := fun n => g (n+n0)
  let cm' := fun n => cm (n+n0)
  let r := fun n => LiteralCenteredArray.mean i
    (PhysicalExposureLimit.lowerProbability i (G (n+n0)) (b (n+n0)) (hb _)) (-θ (n+n0))
  have htail : Tendsto (fun n : ℕ => n+n0) atTop atTop := by
    apply tendsto_atTop.mpr
    intro K
    exact eventually_atTop.mpr ⟨K,fun n hn => by omega⟩
  have hN (n : ℕ) : A.N n=m' n-1 := congrFun hAN n
  have hlaw (n : ℕ) : A.law n=tiltedSource i (G' n:Measure (ℝ × ℝ)) (b' n) (θ' n) := congrFun hAlaw n
  have hY (n : ℕ) : A.Y n=RawTiltedSource.integerSign := congrFun hAY n
  have hcenter (n : ℕ) : ∀ᵐ x ∂A.law n,A.X n x=demand (xi i) (b' n) x-r n := by
    exact ae_of_all _ fun x => congrFun (congrFun hAX n) x
  have hrmean (n : ℕ) : r n=∫ x,demand (xi i) (b' n) x ∂A.law n := by
    have hi : Integrable (demand (xi i) (b' n)) (A.law n) :=
      Integrable.of_mem_Icc 0 1 (measurable_demand _ _).aemeasurable
        (ae_of_all _ fun x => demand_bounds (xi_pos i) (hb _) x)
    have hh := integral_congr_ae (hcenter n)
    rw [A.mean_X n,integral_sub hi (integrable_const _),integral_const] at hh
    simp only [probReal_univ,smul_eq_mul,one_mul] at hh
    linarith
  have hzshift : ∀ᶠ n in atTop,(capacity (m' n):ℝ)-(A.N n:ℝ)*r n=0 := by
    filter_upwards [htail.eventually hrawMatch] with n hn
    rw [hrmean n,hlaw n,hn,← hN n]
    field_simp [(A.N_pos n).ne']
    simp only [m',sub_self]
  have hshift : Tendsto (fun n => A.d n*((capacity (m' n):ℝ)-(A.N n:ℝ)*r n)) atTop (𝓝 0) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0)).congr'
    filter_upwards [hzshift] with n hn
    rw [hn,mul_zero]
  obtain ⟨cC,UC,UR,hcC,hUC,hUR,hout⟩ := source_coarse_from_actual_array i A hgap G' m' b' θ' r g' cm'
    hN hlaw hY hcenter hshift (hθ.comp htail) hθ0 hlo hε hq ha hd
      (htail.eventually hscalar)
  refine ⟨cC,UC,UR,hcC,hUC,hUR,?_⟩
  let P : ℕ → Prop := fun n =>
    let I := ExactUntilting.cost (source i (G n:Measure (ℝ × ℝ)))
      (demand (xi i) (b n)) (θ n) (capacity (m n)) (m n-1)
    let C := sourceCanonicalMarginal i (m n) (G n:Measure (ℝ × ℝ)) (g n) (cm n) (b n)
    let R := sourceCanonicalDuplicate i (m n) (G n:Measure (ℝ × ℝ)) (g n) (cm n) (b n)
    cC*Real.exp (-I)/((m n-1:ℕ):ℝ)^2 ≤ C ∧ C ≤ UC*Real.exp (-I)/((m n-1:ℕ):ℝ)^2 ∧
    R ≤ UR*Real.exp (-I)/((m n-1:ℕ):ℝ)^3 ∧ 0 < C ∧ 0 ≤ R/C ∧ R/C ≤ (UR/cC)/((m n-1:ℕ):ℝ)
  have houtP : ∀ᶠ n in atTop, P (n+n0) := by exact hout
  obtain ⟨M,hM⟩ := eventually_atTop.mp houtP
  refine eventually_atTop.mpr ⟨M+n0,?_⟩
  intro n hn
  have hsmall : n0 ≤ n := by omega
  have he : n-n0+n0=n := Nat.sub_add_cancel hsmall
  have hh : P (n-n0+n0) := hM (n-n0) (by omega)
  exact (congrArg P he).mp hh

end FCAppendix.Affine.Uniform06.EarlyCoarseKernels
