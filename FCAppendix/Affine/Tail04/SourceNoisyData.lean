import FCAppendix.Affine.Tail04.SourceTailNoisyFixedPoint
import FCAppendix.Affine.Tail04.CentralMargins

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceNoisyData
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional OriginalValues

def eA (P : ValueParameters) : ℝ := 10*P.theta^2/(9*activeMass P.theta)
def eR (P : ValueParameters) : ℝ := 5*(partialMass+P.theta^2)/(4*activeMass P.theta)

lemma theta_square_lt (P : ValueParameters) : P.theta^2<1/100 := by
  nlinarith [P.theta_pos,P.theta_small]

lemma eA_bounds (P : ValueParameters) : eA P∈Ioo (0:ℝ) 1 := by
  have ha := P.active_mass_pos
  have htheta := P.theta_pos
  have ht := theta_square_lt P
  constructor
  · exact div_pos (by positivity) (by positivity)
  · apply (div_lt_one (by positivity : 0<9*activeMass P.theta)).mpr
    unfold activeMass delta
    nlinarith

lemma eR_bounds (P : ValueParameters) : eR P∈Ioo (0:ℝ) 1 := by
  have ha := P.active_mass_pos
  have htheta := P.theta_pos
  have ht := theta_square_lt P
  constructor
  · apply div_pos
    · dsimp [partialMass]
      nlinarith [sq_nonneg P.theta]
    · positivity
  · apply (div_lt_one (by positivity : 0<4*activeMass P.theta)).mpr
    unfold activeMass partialMass delta
    nlinarith

def budget (ξ R Up U B0 : ℝ) : ℝ :=
  min (1/2) (min ((1-Up)/(2*Up))
    (min ((R-(1-ξ)*U)/(2*((1-ξ)*U))) ((B0-U)/(2*U))))

lemma budget_bounds {ξ R Up U B0 : ℝ}
    (hξ : ξ<1) (hUp : 0< Up) (hUp1 : Up<1) (hU : 0< U)
    (hgap : (1-ξ)*U< R) (hUB : U< B0) :
    0< budget ξ R Up U B0 ∧ budget ξ R Up U B0≤1 ∧
      Up*(1+budget ξ R Up U B0)<1 ∧
      (1-ξ)*(U*(1+budget ξ R Up U B0))< R ∧
      U*(1+budget ξ R Up U B0)< B0 := by
  have hκ : 0<1-ξ := sub_pos.mpr hξ
  have hκU : 0<(1-ξ)*U := mul_pos hκ hU
  have hp : 0<(1-Up)/(2*Up) := div_pos (sub_pos.mpr hUp1) (by positivity)
  have hg : 0<(R-(1-ξ)*U)/(2*((1-ξ)*U)) := div_pos (sub_pos.mpr hgap) (by positivity)
  have hu : 0<(B0-U)/(2*U) := div_pos (sub_pos.mpr hUB) (by positivity)
  have he : 0< budget ξ R Up U B0 := by
    unfold budget
    exact lt_min (by norm_num) (lt_min hp (lt_min hg hu))
  have hhalf : budget ξ R Up U B0≤1/2 := min_le_left _ _
  have hP : budget ξ R Up U B0≤(1-Up)/(2*Up) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hG : budget ξ R Up U B0≤(R-(1-ξ)*U)/(2*((1-ξ)*U)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hU' : budget ξ R Up U B0≤(B0-U)/(2*U) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hPm := (le_div_iff₀ (by positivity : 0<2*Up)).mp hP
  have hGm := (le_div_iff₀ (by positivity : 0<2*((1-ξ)*U))).mp hG
  have hUm := (le_div_iff₀ (by positivity : 0<2*U)).mp hU'
  exact ⟨he,by linarith,by nlinarith,by nlinarith,by nlinarith⟩

lemma source_receipt_gap {ξ U : ℝ} (hξ : 0< ξ) (hξh : ξ<1/2)
    (hUB : U< Central.B ξ) : (1-ξ)*U< Central.R ξ := by
  have hκ : 0<1-ξ := by linarith
  have hcentral : (1-ξ)*Central.B ξ< Central.R ξ := by
    unfold Central.B Central.R
    nlinarith [sq_nonneg ξ]
  exact (mul_lt_mul_of_pos_left hUB hκ).trans hcentral

variable (P : ValueParameters) (ξ u Up U width : ℝ) (c : ℕ)
    (hξ : 0< ξ) (hξh : ξ<1/2) (hu : 0≤ u) (huU : 1+u≤ U)
    (hRUp : Central.R ξ≤ Up) (hUp : Up<1) (hUB : U< Central.B ξ) (hw : 0< width)

def data : FiniteTailNoisyGame.Data := by
  have hR : 0< Central.R ξ := by unfold Central.R;nlinarith
  have hU : 0< U := by linarith
  have hUp0 : 0< Up := hR.trans_le hRUp
  have hgap := source_receipt_gap hξ hξh hUB
  have he := budget_bounds (by linarith : ξ<1) hUp0 hUp hU hgap hUB
  exact {
    c:=c
    R:=Central.R ξ
    Up:=Up
    U:=U
    u:=u
    F:=Central.B ξ
    ξ:=ξ
    eps:=budget ξ (Central.R ξ) Up U (Central.B ξ)
    eta:=1-2*ξ
    eA:=eA P
    eR:=eR P
    width:=width
    hR:=hR
    hRUp:=hRUp
    hU:=by linarith
    hu:=hu
    huU:=huU
    heps:=he.1
    hRp:=he.2.2.1
    hξ:=hξ
    hξ1:=by linarith
    hgap:=he.2.2.2.1
    hF:=by unfold Central.B;linarith
    hUF:=he.2.2.2.2.le
    heA0:=(eA_bounds P).1.le
    heA1:=(eA_bounds P).2.le
    heR0:=(eR_bounds P).1.le
    heR1:=(eR_bounds P).2.le
    hw:=hw
    heta0:=by linarith
    heta1:=by linarith
    regimeShare:=⟨P.theta,P.theta_pos.le,by linarith [P.theta_small]⟩
    bulkShare:=0
    upperShare:=0
    categories:=FiniteLaw.dirac 0 }

local notation "D" => data P ξ u Up U width c hξ hξh hu huU hRUp hUp hUB hw

lemma data_budget_le_one : (D).eps≤1 := by
  have hR : 0< Central.R ξ := by unfold Central.R;nlinarith
  exact (budget_bounds (by linarith : ξ<1) (hR.trans_le hRUp) hUp
    (by linarith : 0< U) (source_receipt_gap hξ hξh hUB) hUB).2.1

@[simp] lemma data_source_tariff : (D).eta=1-2*(D).ξ := rfl
@[simp] lemma data_source_regime : ((D).regimeShare:ℝ)=P.theta := rfl
@[simp] lemma data_source_flags : (D).eA=10*P.theta^2/(9*activeMass P.theta) ∧
    (D).eR=5*(partialMass+P.theta^2)/(4*activeMass P.theta) := ⟨rfl,rfl⟩
@[simp] lemma data_flag_endpoint : (D).F=1+ξ/50 := rfl

theorem exists_source_noisy_law (t : ℝ) (ht : P.M< t) (N : ℕ) :
    ∃ (π : SourceTailNoisyFixedPoint.JointProfile D P t ht)
      (σ : ∀ i : Fin 3,Kernel
        (Hybrid.ActiveValue (SourceTailNoisyFixedPoint.valueLo P i) (SourceTailNoisyFixedPoint.valueHi P t i))
        (Hybrid.ActiveBaseBid (SourceTailNoisyFixedPoint.bidLo D i) (SourceTailNoisyFixedPoint.bidHi D i))),
      (∀ i,IsMarkovKernel (σ i)) ∧
      (∀ i,SourceTailNoisyFixedPoint.originalValueLaw P t ht i ⊗ₘ σ i=((π i).1 : Measure _)) ∧
      (∀ i,AllActionOptimal (π i) (fun x => SourceTailNoisyFixedPoint.payoff D P t ht N i (π,x))) ∧
      (∀ i,∀ᵐ v ∂SourceTailNoisyFixedPoint.originalValueLaw P t ht i,∀ᵐ b ∂σ i v,
        ∀ b' : Hybrid.ActiveBaseBid (SourceTailNoisyFixedPoint.bidLo D i) (SourceTailNoisyFixedPoint.bidHi D i),
          SourceTailNoisyFixedPoint.payoff D P t ht N i (π,(v,b'))≤
            SourceTailNoisyFixedPoint.payoff D P t ht N i (π,(v,b))) :=
  SourceTailNoisyFixedPoint.exists_original_joint_noisy_law D P t ht N

end FCAppendix.Affine.Tail04.SourceNoisyData
