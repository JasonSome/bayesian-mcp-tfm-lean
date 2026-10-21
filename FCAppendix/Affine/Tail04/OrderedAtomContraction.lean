import FCAppendix.Affine.Tail04.OrderedAtomRestoredBeta
import FCAppendix.Affine.Tail04.AtomPassage

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomContraction
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional OriginalValues FiniteTailNoisyGame SourceTailNoisyFixedPoint
open OrderedOriginalNoisySequence LatentNoisyPopulation LatentSpeciesCalculus
open OrderedAtomActiveGeometry OrderedAtomClusterBound OrderedAtomClusterLaws
open OrderedAtomUniformCluster OriginalActiveCrossingCarrier OrderedAtomFiniteGain
open ActiveGainUniformModulus ActualActiveFiniteGain AllCountActiveFiniteGain

section Radii

def shrinking (g : ℕ→ℝ) : ℕ→ℝ
  | 0 => min (g 0) 1
  | n+1 => min (shrinking g n) (min (g (n+1)) (1/(n+2:ℝ)))

lemma shrinking_pos (g : ℕ→ℝ) (hg : ∀ n,0< g n) (n : ℕ) : 0< shrinking g n := by
  induction n with
  | zero => exact lt_min (hg 0) (by norm_num)
  | succ n ih => exact lt_min ih (lt_min (hg (n+1)) (by positivity))

lemma shrinking_le (g : ℕ→ℝ) (n : ℕ) : shrinking g n≤ g n := by
  cases n with
  | zero => exact min_le_left _ _
  | succ n => exact (min_le_right _ _).trans (min_le_left _ _)

lemma shrinking_le_inverse (g : ℕ→ℝ) (n : ℕ) : shrinking g n≤1/(n+1:ℝ) := by
  cases n with
  | zero => simpa only [shrinking,Nat.cast_zero,zero_add,div_one] using (min_le_right (g 0) (1:ℝ))
  | succ n =>
      convert! (min_le_right (shrinking g n) (min (g (n+1)) (1/(n+2:ℝ)))).trans
        (min_le_right (g (n+1)) (1/(n+2:ℝ))) using 1
      push_cast
      ring

lemma shrinking_antitone (g : ℕ→ℝ) : Antitone (shrinking g) := by
  intro n m hnm
  induction m,hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hnm ih => exact (min_le_left _ _).trans ih

lemma shrinking_tendsto (g : ℕ→ℝ) (hg : ∀ n,0< g n) :
    Tendsto (shrinking g) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
      (fun n => (shrinking_pos g hg n).le) (shrinking_le_inverse g)

end Radii

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H) (N : ℕ)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v→ H≤ upperBid v)
  (S : Sequence D P t ht (N+1))

def ConditionalBetaControl (Q : ℝ) : Prop :=
  ∀ e : ℝ,0< e → ∃ δ : ℝ,0< δ ∧ ∀ j : ℕ,∀ b r : ℝ,0< r → 6*r< δ →
    (S.eps j:ℝ)*D.U≤ r → ∀ y : Icc (1:ℝ) D.U,(y:ℝ)=b+2*r →
    ∀ i : Fin (N+1),∀ x∈cluster D P t (Ioo (b-r) (b+r)),
    ∀ w∈physicalCarrier (S.data j) P hdR H ((S.physical_cap_le j).trans_lt hBH) b r,
      (∫ row,carrierBeta (S.data j) P t ht hdR H ((S.physical_cap_le j).trans_lt hBH)
        (N+1) y (x,restore i w row)
          ∂Measure.pi (fun _ : Fin N =>
            originalLaw D P t ht N πL upperBid hupperBid S j))≤2*Q+e

def legalRadius (bulkCut b : ℝ) : ℝ :=
  if b<1+D.u then (1+D.u-b)/4 else min ((D.U-b)/4) ((b-bulkCut)/2)

lemma legalRadius_pos (bulkCut b : ℝ) (hcut : bulkCut<1+D.u) (hb : b< D.U) :
    0< legalRadius D bulkCut b := by
  unfold legalRadius
  split_ifs with h
  · linarith
  · exact lt_min (by linarith) (by linarith)

def comparison (bulkCut b : ℝ) (hb1 : 1≤ b) (_hb : b< D.U)
    (_hcut : bulkCut<1+D.u) (r : ℝ) (hr : 0< r) (hrl : r≤ legalRadius D bulkCut b) :
    Icc (1:ℝ) D.U :=
  ⟨b+2*r,by
    constructor
    · linarith
    · unfold legalRadius at hrl
      split_ifs at hrl with h
      · linarith [D.huU]
      · have hh := hrl.trans (min_le_left _ _)
        linarith⟩

lemma comparison_legal (bulkCut b : ℝ) (hb1 : 1≤ b) (hb : b< D.U)
    (hcut : bulkCut<1+D.u) (r : ℝ) (hr : 0< r) (hrl : r≤ legalRadius D bulkCut b)
    (j : ℕ) (hstrip : (ProbabilityMeasure.toMeasure (S.law j 0).1)
      {x | bulkCut<(x.2:ℝ)}=0) :
    ((comparison D bulkCut b hb1 hb hcut r hr hrl:ℝ)≤1+D.u ∨
      (∀ x∈Ioo (b-r) (b+r),1+D.u< x) ∨
      (ProbabilityMeasure.toMeasure (S.law j 0).1) (typedCluster D P t 0 (Ioo (b-r) (b+r)))=0) := by
  by_cases hbB : b<1+D.u
  · left
    have hh : r≤(1+D.u-b)/4 := by simpa only [legalRadius,if_pos hbB] using hrl
    change b+2*r≤1+D.u
    linarith
  · right
    right
    have hh : r≤(b-bulkCut)/2 := by
      have h := hrl
      rw [legalRadius,if_neg hbB] at h
      exact h.trans (min_le_right _ _)
    have hs : typedCluster D P t 0 (Ioo (b-r) (b+r))⊆
        {x | bulkCut<(x.2:ℝ)} := by
      intro x hx
      change b-r<(x.2:ℝ) ∧ (x.2:ℝ)< b+r at hx
      change bulkCut<(x.2:ℝ)
      linarith
    exact le_antisymm ((measure_mono hs).trans_eq hstrip) bot_le

include hfloor in
theorem active_atom_zero (hN : 0< N) {C Q bulkCut : ℝ}
    (hξh : D.ξ<1/2) (hη : D.eta=1-2*D.ξ) (heps : D.eps≤1)
    (hC : 1≤ C) (hBC : D.B≤ C) (hCF : C< D.F) (hFtwo : D.F≤2)
    (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+2:ℕ)*
      (tailMass P t/(partialMass+tailMass P t)))≤ D.R)
    (hQ : 0≤ Q)
    (hstrict : 2*(t+2*C+1)*Q<
      populationCoefficient (N+2) D.ξ D.width (minFlag D) D.F C*
        (1/2-(75/4:ℝ)/Real.sqrt N))
    (hbeta : ConditionalBetaControl D P t ht hdR H hBH N πL upperBid hupperBid S Q)
    (hcut : bulkCut<1+D.u)
    (hstrip : ∀ j,(ProbabilityMeasure.toMeasure (S.law j 0).1) {x | bulkCut<(x.2:ℝ)}=0)
    (b : ℝ) (hb1 : 1≤ b) (hb : b< D.U) :
    (baseRealLaw D P t ht S.limit : Measure ℝ) {b}=0 := by
  let A := populationCoefficient (N+2) D.ξ D.width (minFlag D) D.F C*
    (1/2-(75/4:ℝ)/Real.sqrt N)
  let K := t+2*C+1
  let a := activeWeight P t
  let L := smoothCoefficient D.ξ C t
  let e : ℕ→ℝ := fun n => 1/(n+1:ℝ)
  have he (n : ℕ) : 0< e n := by dsimp [e];positivity
  have ht0 := P.M_pos.trans ht
  have hK : 0≤ K := by dsimp [K];linarith
  have hL : 0≤ L := (by norm_num : (0:ℝ)≤2).trans
    (smoothCoefficient_ge_two D.hξ (by linarith) ht0.le)
  have ha : 0< a := activeWeight_pos P t ht
  have hn : (0:ℝ)<(N+1:ℕ) := by positivity
  have hA : 0< A := (mul_nonneg (by dsimp [K];linarith : 0≤2*K) hQ).trans_lt hstrict
  have hex (n : ℕ) := exists_sequence_cluster_radius D P t ht hdR H hBH N πL
    upperBid hupperBid hfloor S hN hξh hη heps hC hBC hCF hFtwo (he n) hrare
  choose dg hdg hg using hex
  choose db hdb hbctrl using fun n => hbeta (e n) (he n)
  let g : ℕ→ℝ := fun n => min (dg n/12) (min (db n/12) (legalRadius D bulkCut b))
  have hgpos : ∀ n,0< g n := fun n =>
    lt_min (by linarith [hdg n])
      (lt_min (by linarith [hdb n]) (legalRadius_pos D bulkCut b hcut hb))
  let r : ℕ→ℝ := shrinking g
  have hr : ∀ n,0< r n := shrinking_pos g hgpos
  have hrg (n : ℕ) : 6*r n< dg n := by
    have hh := (shrinking_le g n).trans (min_le_left _ _)
    change r n≤ dg n/12 at hh
    linarith [hdg n]
  have hrb (n : ℕ) : 6*r n< db n := by
    have hh := (shrinking_le g n).trans ((min_le_right _ _).trans (min_le_left _ _))
    change r n≤ db n/12 at hh
    linarith [hdb n]
  have hrl (n : ℕ) : r n≤ legalRadius D bulkCut b :=
    (shrinking_le g n).trans ((min_le_right _ _).trans (min_le_right _ _))
  let err : ℕ→ℝ := fun n => (2*e n+6*L*r n)/((N+1:ℕ)*a)+K*e n
  have herr : ∀ n,0≤ err n := fun n => by
    dsimp [err]
    exact add_nonneg (div_nonneg
      (add_nonneg (mul_nonneg (by norm_num) (he n).le)
        (mul_nonneg (mul_nonneg (by norm_num) hL) (hr n).le)) (mul_nonneg hn.le ha.le))
      (mul_nonneg hK (he n).le)
  have hrt : Tendsto r atTop (𝓝 0) := shrinking_tendsto g hgpos
  have het : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have herrt : Tendsto err atTop (𝓝 0) := by
    have hh := (((het.const_mul 2).add (hrt.const_mul (6*L))).div_const ((N+1:ℕ)*a)).add
      (het.const_mul K)
    simpa only [err,mul_zero,zero_add,zero_div,mul_assoc] using hh
  obtain ⟨hH,hG⟩ := original_common_laws_tendsto D P t ht S.eps S.noise_positive S.noise_small
    S.law S.limit S.noise_tendsto S.law_tendsto
  apply atom_zero_of_ordinary_cluster_estimates
    (fun j => baseRealLaw D P t ht (S.law j))
    (fun j => physicalRealLaw (S.data j) P t ht (S.law j))
    (baseRealLaw D P t ht S.limit) hH hG b A (2*K*Q) hA (by positivity) hstrict
      r err hr (shrinking_antitone g) hrt herr herrt
  intro n
  have hnoise : ∀ᶠ j in atTop,(S.eps j:ℝ)*D.U≤ r n :=
    ((S.noise_real_tendsto.mul_const D.U).eventually_lt_const
      (by simpa only [zero_mul] using hr n)).mono fun _ h => h.le
  filter_upwards [hnoise] with j hj
  let y := comparison D bulkCut b hb1 hb hcut (r n) (hr n) (hrl n)
  have hfinite := hg n j b (r n) (hr n) (hrg n) hj y rfl
    (comparison_legal D P t ht N S bulkCut b hb1 hb hcut (r n) (hr n) (hrl n) j (hstrip j))
      (2*Q+e n) (hbctrl n j b (r n) (hr n) (hrb n) hj y rfl)
  have hmopen := original_open_mass (S.data j) P t ht πL (S.law j) upperBid hupperBid
    (Ioo (b-r n) (b+r n)) measurableSet_Ioo
  have hmclosed := original_physical_mass (S.data j) P t ht πL (S.law j) upperBid hupperBid
    hdR H ((S.physical_cap_le j).trans_lt hBH) hfloor (N+1) (S.rare_guard hrare j) b (r n)
  change (originalLaw D P t ht N πL upperBid hupperBid S j).real
    (cluster D P t (Ioo (b-r n) (b+r n)))=
      a*(baseRealLaw D P t ht (S.law j) : Measure ℝ).real (Ioo (b-r n) (b+r n)) at hmopen
  change (originalLaw D P t ht N πL upperBid hupperBid S j).real
    (physicalCarrier (S.data j) P hdR H ((S.physical_cap_le j).trans_lt hBH) b (r n))=
      a*(physicalRealLaw (S.data j) P t ht (S.law j) : Measure ℝ).real
        (Icc (b-3*r n) (b+3*r n)) at hmclosed
  simp only [Sequence.data,atNoise] at hfinite hmclosed
  rw [hmopen,hmclosed] at hfinite
  have hnrm := normalize_cluster_bound ha hn (A:=A) (K:=K) (q:=2*Q+e n)
    (h:=(baseRealLaw D P t ht (S.law j) : Measure ℝ).real (Ioo (b-r n) (b+r n)))
    (g:=(physicalRealLaw (S.data j) P t ht (S.law j) : Measure ℝ).real
      (Icc (b-3*r n) (b+3*r n))) (err:=2*e n+6*L*r n) (by
        convert! hfinite using 1
        dsimp [A,K,L,a]
        ring)
  exact separate_vanishing_flag_error measureReal_nonneg measureReal_le_one hK (he n).le hnrm

end FCAppendix.Affine.Tail04.OrderedAtomContraction
