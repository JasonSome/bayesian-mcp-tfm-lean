import FCAppendix.Affine.Tail04.OrderedAtomFiniteGain
import FCAppendix.Affine.Tail04.OrderedOriginalNoisySequence

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomNoiseRadius
open MeasureTheory ProbabilityTheory Set Classical
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedAtomFiniteGain
open AllCountActiveFiniteGain ActiveGainUniformModulus ActualActiveFiniteGain
open ActualFallbackPromotion EqualPrivateSignal ActivePhysicalPayoff

private lemma value_eq_physicalUtility (D : Data) (A H0 H1 : ℕ)
    (μP : ProbabilityMeasure (Icc D.R D.Up)) (v : ℝ) (reg low : Bool)
    (b : Fin (A+1)→Icc (1:ℝ) D.B) (hξh : D.ξ≤1/2) (hη : D.eta=1-2*D.ξ) :
    ActivePhysicalPayoff.value D A H0 H1 μP v reg low b=
      physicalUtility H0 H1 D.c D.ξ D.B D.R D.V D.width (D.e0 reg) D.F
        (by linarith) (by linarith [D.hξ]) reg low
        (D.marksLaw H0) (D.marksLaw H1) (D.privateBayes H0 μP) v b 0 := by
  unfold ActivePhysicalPayoff.value physicalUtility
  simp only [hη]

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
local notation "Ds" => installOriginal D P t ht

include P t ht in
theorem exists_uniform_noise_gain_radius (N : ℕ) {C vhi e : ℝ}
    (hξh : D.ξ≤1/2) (hη : D.eta=1-2*D.ξ)
    (hC : 1≤ C) (hBC : D.B≤ C) (hCF : C≤ D.F) (hvhi : 0≤ vhi) (he : 0< e) :
    ∃ δ : ℝ,0< δ ∧ ∀ eps : ℝ,∀ heps : 0< eps,∀ hsmall : eps< D.eps,
      let Dn := atNoise D eps heps hsmall
      let Dns := installOriginal Dn P t ht
      ∀ kind : Fin N→ Fin 4,∀ μP : ProbabilityMeasure (Icc D.R D.Up),
      ∀ v∈Icc (0:ℝ) vhi,∀ b : Fin (Dns.count kind 1+1)→ Icc (1:ℝ) Dn.B,
      (∀ i j,i≠j→(b i:ℝ)≠(b j:ℝ)) → (b 0:ℝ)≤ v →
      ∀ y : Icc (1:ℝ) Dn.B,(b 0:ℝ)< y → (y:ℝ)-(b 0:ℝ)< δ →
        populationCoefficient (N+1) D.ξ D.width (minFlag D) D.F C*
          (if Dns.count kind 2=Dns.count kind 3 then 0 else
            AtypicalFittingFiniteLoss.crossingCount (fun j => (b j:ℝ)) 0 y)-
          (vhi+2*C+1)*meanBeta Dn P t ht N kind b y*
            AtypicalFittingFiniteLoss.crossingCount (fun j => (b j:ℝ)) 0 y-
          2*e-smoothCoefficient D.ξ C vhi*((y:ℝ)-(b 0:ℝ))≤
        regimeValue Dns (Dns.count kind 1) (min (Dns.count kind 2) (Dns.count kind 3)) (max (Dns.count kind 2) (Dns.count kind 3)) μP v
          (decide (0< Dns.count kind 0)) (Function.update b 0 y)-
        regimeValue Dns (Dns.count kind 1) (min (Dns.count kind 2) (Dns.count kind 3)) (max (Dns.count kind 2) (Dns.count kind 3)) μP v
          (decide (0< Dns.count kind 0)) b := by
  have hex (q : (Fin N→ Fin 4)×Bool) :=
    AllCountActiveFiniteGain.exists_finite_gain_radius
      (R:=D.R) (vlo:=0)
      (min ((Ds).count q.1 2) ((Ds).count q.1 3)) (max ((Ds).count q.1 2) ((Ds).count q.1 3)) D.c (N+1)
      (Nat.add_le_add_right (OrderedAtomFiniteGain.count_le Ds q.1 1) 1)
      D.hξ hξh D.hw
      (show 0≤ D.e0 q.2 by
        cases q.2
        · exact D.heA0
        · exact D.heR0)
      (show D.e0 q.2≤1 by
        cases q.2
        · exact D.heA1
        · exact D.heR1)
      D.hF hCF hC hvhi q.2 (decide (0< (Ds).count q.1 0))
      ((Ds).marksLaw _) ((Ds).marksLaw _) (0 : Fin ((Ds).count q.1 1+1)) he
  choose r hr hp using hex
  obtain ⟨δ,hδ,hδr⟩ := IntegratedActiveFiniteGain.finite_common_radius r hr
  refine ⟨δ,hδ,?_⟩
  intro eps heps hsmall
  let Dn := atNoise D eps heps hsmall
  let Dns := installOriginal Dn P t ht
  change ∀ kind : Fin N→ Fin 4,∀ μP : ProbabilityMeasure (Icc D.R D.Up),
    ∀ v∈Icc (0:ℝ) vhi,∀ b : Fin (Dns.count kind 1+1)→ Icc (1:ℝ) Dn.B,
    (∀ i j,i≠j→(b i:ℝ)≠(b j:ℝ)) → (b 0:ℝ)≤ v →
    ∀ y : Icc (1:ℝ) Dn.B,(b 0:ℝ)< y → (y:ℝ)-(b 0:ℝ)< δ → _
  intro kind μP v hv b hno hval y hy hdist
  have hBn : Dn.B≤ D.B :=
    mul_le_mul_of_nonneg_left (by dsimp [Dn,atNoise];linarith)
      ((by norm_num : (0:ℝ)≤1).trans D.hU)
  have hB0 : 1≤ Dn.B := by
    change 1≤ D.U*(1+eps)
    nlinarith [D.hU,mul_nonneg ((by norm_num : (0:ℝ)≤1).trans D.hU) heps.le]
  have hV0 : 0≤ Dn.V := by
    change 0≤ D.Up*(1+eps)
    exact mul_nonneg (D.hR.le.trans D.hRUp) (by linarith)
  have hsep : (1-D.ξ)*Dn.B<1 := Dn.hgap.trans
    ((D.hRUp.trans (by
      change D.Up≤ D.Up*(1+eps)
      nlinarith [mul_nonneg (D.hR.le.trans D.hRUp) heps.le])).trans_lt Dn.hRp)
  have hh (reg : Bool) := hp (kind,reg) Dn.B ⟨hB0,hBn.trans hBC⟩
    Dn.V ⟨hV0,Dn.hRp.le⟩ v hv hsep
    (Dns.privateBayes (min (Dns.count kind 2) (Dns.count kind 3)) μP) b hno hval y hy
    (hdist.trans_le (hδr (kind,reg)))
  have hv (reg : Bool) (r : Fin (Dns.count kind 1+1)→Icc (1:ℝ) Dn.B) :=
    value_eq_physicalUtility Dns (Dns.count kind 1)
      (min (Dns.count kind 2) (Dns.count kind 3)) (max (Dns.count kind 2) (Dns.count kind 3))
      μP v reg (decide (0< Dns.count kind 0)) r hξh hη
  have hh' (reg : Bool) :
      populationCoefficient (N+1) D.ξ D.width (D.e0 reg) D.F C*
          (if Dns.count kind 2=Dns.count kind 3 then 0 else
            AtypicalFittingFiniteLoss.crossingCount (fun j => (b j:ℝ)) 0 y)-
        (vhi+2*C+1)*OrderedAtomFiniteGain.beta Dn P t ht N kind reg b y*
          AtypicalFittingFiniteLoss.crossingCount (fun j => (b j:ℝ)) 0 y-
        2*e-smoothCoefficient D.ξ C vhi*((y:ℝ)-(b 0:ℝ))≤
      ActivePhysicalPayoff.value Dns (Dns.count kind 1)
        (min (Dns.count kind 2) (Dns.count kind 3)) (max (Dns.count kind 2) (Dns.count kind 3))
        μP v reg (decide (0< Dns.count kind 0)) (Function.update b 0 y)-
      ActivePhysicalPayoff.value Dns (Dns.count kind 1)
        (min (Dns.count kind 2) (Dns.count kind 3)) (max (Dns.count kind 2) (Dns.count kind 3))
        μP v reg (decide (0< Dns.count kind 0)) b := by
    have hreg := hh reg
    dsimp only at hreg
    simp only [ordered_counts_equal_iff] at hreg
    exact hreg.trans_eq (congrArg₂ (fun x y : ℝ => x-y)
      (hv reg (Function.update b 0 y)).symm (hv reg b).symm)
  have hm (reg : Bool) := populationCoefficient_mono_flag
    (m:=N+1) (width:=D.width) (F:=D.F) (C:=C)
    hξh (minFlag_nonneg D) (minFlag_le D reg)
  have hc : 0≤(if Dns.count kind 2=Dns.count kind 3 then 0 else
      AtypicalFittingFiniteLoss.crossingCount (fun j => (b j:ℝ)) 0 y) := by
    split_ifs
    · exact le_rfl
    · exact AtypicalFittingFiniteLoss.crossingCount_nonneg _ _ _
  have hg (reg : Bool) := mul_le_mul_of_nonneg_right (hm reg) hc
  have h0 := mul_le_mul_of_nonneg_left (hh' false) (sub_nonneg.mpr D.regimeShare.2.2)
  have h1 := mul_le_mul_of_nonneg_left (hh' true) D.regimeShare.2.1
  have h0' := mul_le_mul_of_nonneg_left (hg false) (sub_nonneg.mpr D.regimeShare.2.2)
  have h1' := mul_le_mul_of_nonneg_left (hg true) D.regimeShare.2.1
  change _≤(1-(D.regimeShare:ℝ))*ActivePhysicalPayoff.value Dns (Dns.count kind 1)
      (min (Dns.count kind 2) (Dns.count kind 3)) (max (Dns.count kind 2) (Dns.count kind 3))
      μP v false (decide (0< Dns.count kind 0)) (Function.update b 0 y)+
    (D.regimeShare:ℝ)*ActivePhysicalPayoff.value Dns (Dns.count kind 1)
      (min (Dns.count kind 2) (Dns.count kind 3)) (max (Dns.count kind 2) (Dns.count kind 3))
      μP v true (decide (0< Dns.count kind 0)) (Function.update b 0 y)-
    ((1-(D.regimeShare:ℝ))*ActivePhysicalPayoff.value Dns (Dns.count kind 1)
      (min (Dns.count kind 2) (Dns.count kind 3)) (max (Dns.count kind 2) (Dns.count kind 3))
      μP v false (decide (0< Dns.count kind 0)) b+
    (D.regimeShare:ℝ)*ActivePhysicalPayoff.value Dns (Dns.count kind 1)
      (min (Dns.count kind 2) (Dns.count kind 3)) (max (Dns.count kind 2) (Dns.count kind 3))
      μP v true (decide (0< Dns.count kind 0)) b)
  dsimp only [meanBeta,Dns,Dn,installOriginal,atNoise] at h0 h1 h0' h1' ⊢
  split_ifs at h0 h1 h0' h1' ⊢ <;> nlinarith only [h0,h1,h0',h1']

end FCAppendix.Affine.Tail04.OrderedAtomNoiseRadius
