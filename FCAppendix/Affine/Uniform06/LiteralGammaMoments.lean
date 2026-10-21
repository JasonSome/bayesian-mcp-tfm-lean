import FCAppendix.Affine.Uniform06.GuardedSampledMoments
import FCAppendix.Affine.Uniform06.LiteralBadCountTransfer

noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralGammaMoments

open Set MeasureTheory Filter LowBody
open scoped Topology BigOperators
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource RawMarkedLaplace
open RawMomentPartition GuardedSampledMoments MixedIntervalLLT LiteralGuardRare
open SamplingPopulation RareEmpiricalReplacement RawSamplingBounds ClampedMomentBounds

theorem original_current_gamma_literal_moments (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 (FullJointLaw.law i)))
    (hvalue : ∀ n,(G n:Measure (ℝ × ℝ)).map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hbelow : ∀ n,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p.2 ≤ p.1)
    (A : CenteredArray RowRival) [∀ n,Nonempty (Fin (A.N n))] (hgap : A.CompactGap)
    (b θ r : ℕ → ℝ) (c : ℕ → ℕ) (g : ℕ → GuardData) (g₀ : GuardData)
    (cm : (n : ℕ) → (Fin (A.N n) → Fin 4) → ℝ) (cmbar : ℕ → ℝ)
    (hlaw : ∀ n,A.law n=tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))
    (hY : ∀ n,A.Y n=integerSign)
    (hcenter : ∀ n,∀ᵐ x ∂A.law n,A.X n x=demand (xi i) (b n) x-r n)
    (hr : ∀ n,r n ∈ Icc (0:ℝ) 1)
    (hmatch : ∀ᶠ n in atTop,(c n:ℝ)=(A.N n:ℝ)*r n)
    (hcap : ∀ n,(c n:ℝ) ≤ (A.N n:ℝ))
    {b₀ θ₀ lo hi U e ε K s : ℝ}
    (hb : ∀ n,0 < b n) (hb₀ : 0 < b₀) (hblim : Tendsto b atTop (𝓝 b₀))
    (hθlim : Tendsto θ atTop (𝓝 θ₀)) (hθ₀ : 0 < θ₀) (hlo : 0 < lo)
    (hθ : ∀ n,lo ≤ θ n ∧ θ n ≤ hi)
    (hU : 0 < U) (hcapG : ∀ n,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p.2 ≤ U)
    (hbU : ∀ n,b n ≤ U) (he : 0 < e)
    (hreceipt : ∀ n,(1-xi i/2)*U+e ≤ b n)
    (hLlim : Tendsto (fun n => (g n).multiplier) atTop (𝓝 (entry i)))
    (hL₀ : g₀.multiplier=entry i)
    (hreq₀ : g₀.requiredDemand=PrefixRoot.requiredDemand i)
    (hreq : ∀ n,(g n).requiredDemand=g₀.requiredDemand)
    (hM : ∀ n,0 < (g n).population) (hNM : ∀ n,(A.N n:ℝ) ≤ (g n).population)
    (hε : 0 < ε) (hgε : ∀ n,ε ≤ (g n).margin) (hK : 0 ≤ K)
    (hgl : ∀ n,0 < (g n).multiplier-(g n).radius)
    (hgu : ∀ n,0 < (g n).multiplier+(g n).radius)
    (hd : ∀ n,0 < (g n).rejectionScale)
    (hs : 0 < s) (hst : s ≤ cutoff i) (hgseed : ∀ n,(g n).seedCutoff=s)
    (hcm : ∀ n,∀ᵐ ω ∂Measure.pi (fun _ : Fin (A.N n) => A.law n),
      |cm n (fun j => (ω j).1)/(g n).population-cmbar n| ≤
        K*(deviationSum (A.law n) (xi i) (g n) ω+(g n).population⁻¹))
    (hbL : ∀ n,b n≤(g n).multiplier)
    {εc : ℝ} (hεc : 0<εc)
    (hfinite : ∀ᶠ n in atTop,LiteralBadCountTransfer.countMargins i
      (G n:Measure (ℝ × ℝ)) (A.N n) (c n) (b n) (θ n) εc) :
    (∃ Γmax > (0:ℝ),∀ᶠ n in atTop,
      sourceGamma i (G n:Measure (ℝ × ℝ)) (A.N n) (c n) (b n) (θ n) (g n) (cmbar n)
        ∈ Icc (1:ℝ) Γmax) ∧
    ∀ q : Fin 3,Tendsto (fun n =>
      (A.N n:ℝ)*∫ ω : Fin (A.N n) → RowRival,
        literalMoment i (c n) (g n) (cm n) (b n) (θ n) q.val ω
          ∂Measure.pi (fun _ : Fin (A.N n) => A.law n)-
        (density A.vX A.vY*(q.val.factorial:ℝ)/θ₀^(q.val+1))*
          sourceGamma i (G n:Measure (ℝ × ℝ)) (A.N n) (c n)
            (b n) (θ n) (g n) (cmbar n)) atTop (𝓝 0) := by
  have hcells := original_current_gamma_moments i G hG hvalue hbelow A hgap b θ r c g g₀
    cm cmbar hlaw hY hcenter hr hmatch hcap hb hb₀ hblim hθlim hθ₀ hlo hθ
    hU hcapG hbU he hreceipt hLlim hL₀ hreq₀ hreq hM hNM hε hgε hK
    hgl hgu hd hs hst hgseed hcm
  have hreqpos (n : ℕ) : 0<(g n).requiredDemand := by
    rw [hreq n,hreq₀]
    exact (EntryEarlySourceLimits.requiredDemand_bounds i).1
  have hg (n : ℕ) : 0<(g n).margin ∧ 0<(g n).population ∧ 0<(g n).requiredDemand :=
    ⟨hε.trans_le (hgε n),hM n,hreqpos n⟩
  have hh (n : ℕ) : ∀ᵐ x ∂tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n),
      0≤ rawH (xi i) (b n) x :=
    (original_receipt_h_bounds i (G n:Measure (ℝ × ℝ)) hU (hb n) (hbU n)
      he (hcapG n) (hreceipt n) (θ n) (g n)).mono fun _ hx => hx.1
  refine ⟨hcells.1,?_⟩
  intro q
  have hbad := LiteralBadCountTransfer.original_literal_cell_replacement i G A.N c
    A.market (fun n => Nat.cast_pos.mp (A.N_pos n)) b θ θ g cm hb hbL
    (fun n => hlo.le.trans (hθ n).1) hcap hg hh hεc s U hfinite q.val 0
  have hbad' : Tendsto (fun n => (A.N n:ℝ)*∫ ω : Fin (A.N n) → RowRival,
      |literalMoment i (c n) (g n) (cm n) (b n) (θ n) q.val ω-
        cellSum i (c n) (g n) (cm n) (b n) (θ n) q.val ω|
        ∂Measure.pi (fun _ : Fin (A.N n) => A.law n)) atTop (𝓝 0) := by
    simpa only [hlaw,pow_zero,one_mul] using hbad
  let L := density A.vX A.vY*(q.val.factorial:ℝ)/θ₀^(q.val+1)
  let Γ := fun n => sourceGamma i (G n:Measure (ℝ × ℝ)) (A.N n) (c n)
    (b n) (θ n) (g n) (cmbar n)
  have hrow (n : ℕ) : ∀ᵐ ω ∂Measure.pi (fun _ : Fin (A.N n) => A.law n),
      (literalMoment i (c n) (g n) (cm n) (b n) (θ n) q.val ω∈Icc (0:ℝ) ((A.N n:ℝ)^q.val)) ∧
      (cellSum i (c n) (g n) (cm n) (b n) (θ n) q.val ω∈Icc (0:ℝ) ((A.N n:ℝ)^q.val)) := by
    have hhr : ∀ᵐ x ∂A.law n,0≤ rawH (xi i) (b n) x := by rw [hlaw]; exact hh n
    have heval (j : Fin (A.N n)) :=
      (measurePreserving_eval (fun _ : Fin (A.N n) => A.law n) j).quasiMeasurePreserving.ae hhr
    filter_upwards [ae_all_iff.mpr heval] with ω hω
    exact ⟨literalMoment_polynomial i (c n) (g n) (cm n) (hb n) (hbL n)
      (hlo.le.trans (hθ n).1) q.val (hcap n) (hg n).1 (hg n).2.1 (hg n).2.2 ω hω,
      cellSum_polynomial i (c n) (g n) (cm n) (hb n) (hlo.le.trans (hθ n).1)
        q.val (Nat.cast_pos.mp (A.N_pos n)) (hcap n) ω hω⟩
  have hdelta : Tendsto (fun n =>
      (A.N n:ℝ)*(∫ ω : Fin (A.N n) → RowRival,
        literalMoment i (c n) (g n) (cm n) (b n) (θ n) q.val ω
          ∂Measure.pi (fun _ : Fin (A.N n) => A.law n))-
      (A.N n:ℝ)*(∫ ω : Fin (A.N n) → RowRival,
        cellSum i (c n) (g n) (cm n) (b n) (θ n) q.val ω
          ∂Measure.pi (fun _ : Fin (A.N n) => A.law n))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hbad'
    apply Eventually.of_forall
    intro n
    have h1 := Integrable.of_mem_Icc 0 ((A.N n:ℝ)^q.val)
      (measurable_literalMoment i _ _ _ _ _ _).aemeasurable
      ((hrow n).mono fun _ h => h.1)
    have h2 := Integrable.of_mem_Icc 0 ((A.N n:ℝ)^q.val)
      (measurable_cellSum i _ _ _ _ _ _).aemeasurable
      ((hrow n).mono fun _ h => h.2)
    rw [← mul_sub,Real.norm_eq_abs,abs_mul,abs_of_pos (A.N_pos n),← integral_sub h1 h2]
    apply mul_le_mul_of_nonneg_left _ (A.N_pos n).le
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (f:=fun ω =>
        literalMoment i (c n) (g n) (cm n) (b n) (θ n) q.val ω-
          cellSum i (c n) (g n) (cm n) (b n) (θ n) q.val ω)
        (μ:=Measure.pi (fun _ : Fin (A.N n) => A.law n)))
  have hcell : Tendsto (fun n =>
      (A.N n:ℝ)*∫ ω : Fin (A.N n) → RowRival,
        cellSum i (c n) (g n) (cm n) (b n) (θ n) q.val ω
          ∂Measure.pi (fun _ : Fin (A.N n) => A.law n)-L*Γ n) atTop (𝓝 0) := by
    have heq (n : ℕ) := normalized_integral_cellSum i (A.law n) (c n) (g n) (cm n)
      (hb n) (hlo.le.trans (hθ n).1) q.val (Nat.cast_pos.mp (A.N_pos n))
      (hcap n) (by rw [hlaw]; exact hh n)
    simpa only [heq,L,Γ] using hcells.2 q
  have h := hdelta.add hcell
  convert! h using 1
  · funext n
    dsimp only [L,Γ]
    ring
  · simp

end FCAppendix.Affine.Uniform06.LiteralGammaMoments
