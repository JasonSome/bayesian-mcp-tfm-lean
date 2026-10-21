import FCAppendix.Affine.Uniform06.EarlyCoarseKernels
import FCAppendix.Affine.Uniform06.FiniteMean

noncomputable section
namespace FCAppendix.Affine.Uniform06.EarlyCoarseTiltConstructor

open MeasureTheory Set Filter LowBody
open scoped Topology BigOperators
open Uniform07 LiteralExperiment RawMixedSource

theorem eventually_on_market_fibers (m : ℕ → ℕ) {P : ℕ → Prop}
    (hP : ∀ᶠ n in atTop,P n) :
    ∀ᶠ M in atTop,∀ n,m n=M → P n := by
  obtain ⟨n0,hn0⟩ := eventually_atTop.mp hP
  let K := (Finset.range n0).sum m+1
  refine eventually_atTop.mpr ⟨K,?_⟩
  intro M hM n hn
  by_cases hlarge : n0 ≤ n
  · exact hn0 n hlarge
  · have hmem : n ∈ Finset.range n0 := Finset.mem_range.mpr (by omega)
    have hbound : m n ≤ (Finset.range n0).sum m :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) hmem
    dsimp [K] at hM
    omega

theorem construct_sequence_tilts (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ)) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) (z : ℕ → ℝ) {d : ℝ}
    (hd : 0 < d) (hdmax : d ≤ x i-1/2)
    (hz : ∀ n,z n ∈ Icc (1/2:ℝ) (x i-d))
    (hvalue : ∀ n,(G n:Measure (ℝ × ℝ)).map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hbid : ∀ n,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p.2 ≤ p.1)
    (hactive : ∀ a > (0:ℝ),∀ e > (0:ℝ),∀ᶠ n in atTop,
      ∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p.1 ∈ Ioc (entry i+a) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ e) :
    ∃ θ : ℕ → ℝ,∃ θlo θhi vlo vhi : ℝ,
      0 < θlo ∧ 0 < θhi ∧ 0 < vlo ∧ 0 < vhi ∧
      ∀ᶠ n in atTop,θ n ∈ Icc θlo θhi ∧
        SubentryTilt.mean (MixedLaw.law i
          (MixedLaw.physicalLowerLaw i (z n*cutoff i) (G n:Measure (ℝ × ℝ))))
            Prod.fst (θ n)=(capacity (m n):ℝ)/((m n-1:ℕ):ℝ) ∧
        ProbabilityTheory.variance Prod.fst ((MixedLaw.law i
          (MixedLaw.physicalLowerLaw i (z n*cutoff i) (G n:Measure (ℝ × ℝ)))).tilted
            (fun p => -θ n*p.1)) ∈ Icc vlo vhi := by
  classical
  let C := fun M : ℕ => {n : ℕ // m n=M}
  let F := fun M (E : C M) => (G E.val:Measure (ℝ × ℝ))
  have hprobF : ∀ M (E : C M),IsProbabilityMeasure (F M E) := fun _ _ => inferInstance
  have hvalueF : ∀ M (E : C M),(F M E).map Prod.fst=LowChernoff.conditionalValueLaw i :=
    fun _ E => hvalue E.val
  have hbidF : ∀ M (E : C M),∀ᵐ p ∂F M E,p.2 ≤ p.1 := fun _ E => hbid E.val
  have hactiveF : ∀ a > (0:ℝ),∀ e > (0:ℝ),∀ᶠ M in atTop,∀ E : C M,
      ∀ᵐ p ∂F M E,p.1 ∈ Ioc (entry i+a) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ e := by
    intro a ha e he
    filter_upwards [eventually_on_market_fibers m (hactive a ha e he)] with M hM E
    exact hM E.val E.property
  obtain ⟨θlo,θhi,vlo,vhi,hlo,hhi,hvlo,hvhi,hall⟩ :=
    FiniteMean.eventual_uniform_source_tilts C F i hd hdmax hprobF hvalueF hbidF hactiveF
  let P := fun n θ => θ ∈ Icc θlo θhi ∧
    SubentryTilt.mean (MixedLaw.law i
      (MixedLaw.physicalLowerLaw i (z n*cutoff i) (G n:Measure (ℝ × ℝ))))
        Prod.fst θ=(capacity (m n):ℝ)/((m n-1:ℕ):ℝ) ∧
    ProbabilityTheory.variance Prod.fst ((MixedLaw.law i
      (MixedLaw.physicalLowerLaw i (z n*cutoff i) (G n:Measure (ℝ × ℝ)))).tilted
        (fun p => -θ*p.1)) ∈ Icc vlo vhi
  have hex : ∀ᶠ n in atTop,∃ θ,P n θ := by
    filter_upwards [hm.eventually hall] with n hn
    exact hn ⟨n,rfl⟩ (z n) (hz n)
  let θ := fun n => if h : ∃ t,P n t then Classical.choose h else 0
  refine ⟨θ,θlo,θhi,vlo,vhi,hlo,hhi,hvlo,hvhi,?_⟩
  filter_upwards [hex] with n hn
  dsimp only [θ]
  rw [dif_pos hn]
  exact Classical.choose_spec hn

theorem primitive_sequential_coarse (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ)) (G0 : ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 G0))
    (hvalue : ∀ n,(G n:Measure (ℝ × ℝ)).map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hvalue0 : (G0:Measure (ℝ × ℝ)).map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hbid : ∀ n,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p.2 ≤ p.1)
    (hbelow0 : ∀ᵐ p ∂(G0:Measure (ℝ × ℝ)),p.2 ≤ p.1)
    (hactive0 : ∀ᵐ p ∂(G0:Measure (ℝ × ℝ)),p.1 ∈ Ioc (entry i) (cutoff i) →
      p.2=ActiveGraphComponent.activeBid i p.1)
    (hactive : ∀ a > (0:ℝ),∀ e > (0:ℝ),∀ᶠ n in atTop,
      ∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p.1 ∈ Ioc (entry i+a) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ e)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (z : ℕ → ℝ)
    {d z0 : ℝ} (hd : 0 < d) (hdmax : d ≤ x i-1/2)
    (hz : ∀ n,z n ∈ Icc (1/2:ℝ) (x i-d))
    (hz0 : z0 ∈ Ico (1/2:ℝ) (x i)) (hzlim : Tendsto z atTop (𝓝 z0))
    (hcap : ∀ᶠ n in atTop,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p.2 ≤ ReceiptGap.cap i)
    (g : ℕ → GuardData) (cm : (n : ℕ) → (Fin (m n-1) → Fin 4) → ℝ)
    (hL : Tendsto (fun n => (g n).multiplier) atTop (𝓝 (entry i)))
    (hR : ∀ᶠ n in atTop,(g n).radius ≤ cutoff i/100)
    (hg : ∀ᶠ n in atTop,0 < (g n).margin ∧ 0 < (g n).population ∧ 0 < (g n).requiredDemand) :
    ∃ θ : ℕ → ℝ,∃ cC UC UR : ℝ,0 < cC ∧ 0 < UC ∧ 0 < UR ∧
      (∀ᶠ n in atTop,SubentryTilt.mean (MixedLaw.law i
        (MixedLaw.physicalLowerLaw i (z n*cutoff i) (G n:Measure (ℝ × ℝ)))) Prod.fst (θ n)=
          (capacity (m n):ℝ)/((m n-1:ℕ):ℝ)) ∧
      ∀ᶠ n in atTop,
        let b := z n*cutoff i
        let I := ExactUntilting.cost (source i (G n:Measure (ℝ × ℝ)))
          (demand (xi i) b) (θ n) (capacity (m n)) (m n-1)
        let C := sourceCanonicalMarginal i (m n) (G n:Measure (ℝ × ℝ)) (g n) (cm n) b
        let R := sourceCanonicalDuplicate i (m n) (G n:Measure (ℝ × ℝ)) (g n) (cm n) b
        cC*Real.exp (-I)/((m n-1:ℕ):ℝ)^2 ≤ C ∧
        C ≤ UC*Real.exp (-I)/((m n-1:ℕ):ℝ)^2 ∧
        R ≤ UR*Real.exp (-I)/((m n-1:ℕ):ℝ)^3 ∧
        0 < C ∧ 0 ≤ R/C ∧ R/C ≤ (UR/cC)/((m n-1:ℕ):ℝ) := by
  obtain ⟨θ,θlo,θhi,vlo,vhi,hθlo,hθhi,hvlo,hvhi,hθ⟩ :=
    construct_sequence_tilts i G m hm z hd hdmax hz hvalue hbid hactive
  have hmatch := hθ.mono fun n hn => hn.2.1
  have hstrip : ∀ᶠ n in atTop,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),
      p.1 ∈ Ioc (EarlyRankCeiling.ceilingValue i) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ cutoff i/10000 := by
    have ha : 0 < EarlyRankCeiling.ceilingValue i-entry i :=
      sub_pos.mpr (EarlyRankCeiling.ceilingValue_bounds i).1.1
    have he : entry i+(EarlyRankCeiling.ceilingValue i-entry i)=EarlyRankCeiling.ceilingValue i := by ring
    simpa only [he] using hactive
      (EarlyRankCeiling.ceilingValue i-entry i) ha (cutoff i/10000) (div_pos (cutoff_pos i) (by norm_num))
  have hband : ∀ n,z n*cutoff i ∈ Icc (cutoff i/2) ((x i-d)*cutoff i) := by
    intro n
    constructor
    · nlinarith [(hz n).1,cutoff_pos i]
    · exact mul_le_mul_of_nonneg_right (hz n).2 (cutoff_pos i).le
  have hhi : (x i-d)*cutoff i < entry i := by
    unfold entry
    nlinarith [mul_pos hd (cutoff_pos i)]
  obtain ⟨cC,UC,UR,hcC,hUC,hUR,hout⟩ :=
    EarlyCoarseKernels.source_coarse_from_early_joint_limit i G G0 hG hvalue hvalue0
      hbelow0 hactive0 m hm (fun n => z n*cutoff i) θ g cm hhi hz0 hband
      (hzlim.mul_const (cutoff i)) hcap hstrip hmatch hL hR hg
  exact ⟨θ,cC,UC,UR,hcC,hUC,hUR,hmatch,hout⟩

end FCAppendix.Affine.Uniform06.EarlyCoarseTiltConstructor
