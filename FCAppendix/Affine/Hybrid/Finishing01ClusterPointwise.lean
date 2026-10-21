import FCAppendix.Affine.Hybrid.Finishing01ClusterCounts
import FCAppendix.Affine.Hybrid.FavoredIntegratedCrossing

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finish01.Primitives
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open scoped BigOperators
variable (P : Primitives)

abbrev ClusterBox (N : ℕ) := P.Value×P.Bid×((Fin N→ P.Low)×(Fin N→ P.Bid))

def clusterBoxPhysical {N : ℕ} (t : P.ClusterBox N) : ActivePhysicalData N :=
  (t.1,t.2.1,(fun j => (t.2.2.1 j:ℝ)),fun j => (t.2.2.2 j:ℝ))

def clusterBoxRaise {N : ℕ} (t : P.ClusterBox N) (y : P.Bid) : P.ClusterBox N :=
  (t.1,y,t.2.2)

def clusterBoxGain {N : ℕ} (c : ℕ) (kind : Fin N→ Fin 4)
    (t : P.ClusterBox N) (y : P.Bid) : ℝ :=
  activePhysicalPatternPayoff P.xi P.z P.L P.U c kind
    (P.clusterBoxPhysical (P.clusterBoxRaise t y))-
  activePhysicalPatternPayoff P.xi P.z P.L P.U c kind (P.clusterBoxPhysical t)

def clusterBoxBids {N : ℕ} (kind : Fin N→ Fin 4) (t : P.ClusterBox N) : Fin (N+1)→ℝ :=
  activePhysicalBids kind (P.clusterBoxPhysical t)

def clusterActiveSet (_P : Primitives) {N : ℕ} (kind : Fin N→ Fin 4) : Finset (Fin (N+1)) :=
  Finset.univ.filter (activePatternPred kind)

def clusterCrossingCount {N : ℕ} (kind : Fin N→ Fin 4)
    (t : P.ClusterBox N) (y : P.Bid) : ℝ :=
  ∑j : Fin N,if kind j=1 ∧ (t.2.2.2 j:ℝ)∈ Icc (t.2.1:ℝ) (y:ℝ) then 1 else 0

lemma continuous_clusterBoxPhysical {N : ℕ} : Continuous (P.clusterBoxPhysical (N:=N)) := by
  unfold clusterBoxPhysical
  fun_prop

lemma continuous_clusterBoxBids {N : ℕ} (kind : Fin N→ Fin 4) :
    Continuous (P.clusterBoxBids kind) :=
  (continuous_activePhysicalBids kind).comp P.continuous_clusterBoxPhysical

lemma clusterBoxBids_nonneg {N : ℕ} (kind : Fin N→ Fin 4) (t : P.ClusterBox N) :
    ∀ j,0≤ P.clusterBoxBids kind t j := by
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · exact (P.bid_pos t.2.1).le
  · by_cases h0 : kind k=0
    · simpa [clusterBoxBids,clusterBoxPhysical,activePhysicalBids,h0] using
        (t.2.2.1 k).property.1
    · by_cases h1 : kind k=1
      · simpa [clusterBoxBids,clusterBoxPhysical,activePhysicalBids,h1] using
          (P.bid_pos (t.2.2.2 k)).le
      · simp [clusterBoxBids,clusterBoxPhysical,activePhysicalBids,h0,h1]

lemma clusterBoxBids_zero_off_support {N : ℕ} (c : ℕ) (kind : Fin N→ Fin 4)
    (t : P.ClusterBox N) : ∀ j,j∉(activePatternTemplate c kind).support→
      P.clusterBoxBids kind t j=0 := by
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [activePatternTemplate,lowerPatternPred]
  · intro hj
    have h0 : kind k≠0 := by
      intro h
      exact hj (by simp [activePatternTemplate,lowerPatternPred,h])
    have h1 : kind k≠1 := by
      intro h
      exact hj (by simp [activePatternTemplate,lowerPatternPred,h])
    simp [clusterBoxBids,clusterBoxPhysical,activePhysicalBids,h0,h1]

lemma clusterBoxBids_active_lower {N : ℕ} (kind : Fin N→ Fin 4) (t : P.ClusterBox N) :
    ∀ j,j∈ P.clusterActiveSet kind→ P.L≤ P.clusterBoxBids kind t j := by
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · intro _
    exact t.2.1.property.1
  · intro hj
    have h1 : kind k=1 := by simpa [clusterActiveSet,activePatternPred] using hj
    have h0 : kind k≠0 := by rw [h1];decide
    simpa [clusterBoxBids,clusterBoxPhysical,activePhysicalBids,h1] using
      (t.2.2.2 k).property.1

lemma clusterBoxBids_small_inactive {N : ℕ} (c : ℕ) (kind : Fin N→ Fin 4)
    (t : P.ClusterBox N) : ∀ j,j∈(activePatternTemplate c kind).support→
      j∉P.clusterActiveSet kind→ j≠0→ P.clusterBoxBids kind t j≤ P.d := by
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp
  · intro hj ha _
    have h01 : kind k=0 ∨ kind k=1 := by
      simpa [activePatternTemplate,lowerPatternPred] using hj
    have hnot1 : kind k≠1 := by
      intro h1
      exact ha (by simp [clusterActiveSet,activePatternPred,h1])
    have h0 := h01.resolve_right hnot1
    simpa [clusterBoxBids,clusterBoxPhysical,activePhysicalBids,h0] using
      (t.2.2.1 k).property.2

lemma clusterBoxBids_raise {N : ℕ} (kind : Fin N→ Fin 4) (t : P.ClusterBox N)
    (y : P.Bid) : P.clusterBoxBids kind (P.clusterBoxRaise t y)=
      Function.update (P.clusterBoxBids kind t) 0 (y:ℝ) := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j <;>
    simp [clusterBoxBids,clusterBoxPhysical,clusterBoxRaise,activePhysicalBids]

lemma clusterBoxBids_crossing_sum {N : ℕ} (kind : Fin N→ Fin 4)
    (t : P.ClusterBox N) (y : P.Bid) :
    (∑j : Fin (N+1),if j∈ P.clusterActiveSet kind ∧ j≠0 ∧
        P.clusterBoxBids kind t j∈ Icc (P.clusterBoxBids kind t 0) (y:ℝ)
      then (1:ℝ) else 0)=P.clusterCrossingCount kind t y := by
  rw [Fin.sum_univ_succ, if_neg (by simp), zero_add]
  unfold clusterCrossingCount
  apply Finset.sum_congr rfl
  intro j _
  by_cases h1 : kind j=1
  · have h0 : kind j≠0 := by rw [h1];decide
    simp [clusterActiveSet,activePatternPred,clusterBoxBids,clusterBoxPhysical,
      activePhysicalBids,h1]
  · simp [clusterActiveSet,activePatternPred,h1]

theorem cluster_pure_gain {N : ℕ} (c : ℕ) (kind : Fin N→ Fin 4)
    (hpure : activePatternPure P.xi P.L P.U c P.z kind)
    (t : P.ClusterBox N) (y : P.Bid) (hup : (t.2.1:ℝ)< y) :
    -P.eta*P.U*P.clusterCrossingCount kind t y-2*P.kappa*((y:ℝ)-(t.2.1:ℝ)) ≤
      P.clusterBoxGain c kind t y := by
  have h := pure_finite_loss_active (κ:=P.kappa) (d:=P.d) (L:=P.L) (U:=P.U)
    (by dsimp [kappa];linarith [P.xi_half])
    (by dsimp [kappa];linarith [P.xi_pos]) P.low_receipt P.kappa_U_lt_L P.U_pos.le
    (activePatternTemplate c kind) (P.clusterActiveSet kind) (P.clusterBoxBids kind t)
    (P.clusterBoxBids_nonneg kind t) (P.clusterBoxBids_zero_off_support c kind t) 0
    (by simp [activePatternTemplate,lowerPatternPred]) (P.bid_pos t.2.1)
    t.2.1.property.1 (t.2.1.property.2.trans (P.value_surplus.le.trans t.1.property.1))
    (y:ℝ) hup y.property.2 (P.clusterBoxBids_active_lower kind t)
    (P.clusterBoxBids_small_inactive c kind t)
  rw [P.clusterBoxBids_crossing_sum kind t y] at h
  have hfront : P.clusterBoxBids kind t 0=(t.2.1:ℝ) := rfl
  rw [hfront] at h
  unfold clusterBoxGain activePhysicalPatternPayoff
  simp only [if_neg hpure.1,if_neg hpure.2]
  change _ ≤ LowBody.purePayoff P.kappa t.1 (P.clusterBoxBids kind (P.clusterBoxRaise t y))
      ((activePatternTemplate c kind).selection P.kappa
        (P.clusterBoxBids kind (P.clusterBoxRaise t y))) 0-
    LowBody.purePayoff P.kappa t.1 (P.clusterBoxBids kind t)
      ((activePatternTemplate c kind).selection P.kappa (P.clusterBoxBids kind t)) 0
  rw [P.clusterBoxBids_raise kind t y]
  have heta : 2*P.kappa-1=P.eta := by dsimp [kappa,eta];ring
  rw [heta] at h
  linarith

def clusterEqualPayoff {N : ℕ} (c : ℕ) (kind : Fin N→ Fin 4)
    (t : P.ClusterBox N) : ℝ :=
  LowBody.equalPayoff P.xi (activePatternTemplate c kind).residual₀ 0 t.1
    (P.clusterBoxBids kind t)

lemma continuous_clusterEqualPayoff {N : ℕ} (c : ℕ) (kind : Fin N→ Fin 4) :
    Continuous (P.clusterEqualPayoff c kind) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hb := (P.continuous_clusterBoxBids kind).continuousAt (x:=t)
  have hp := (EqualCapacity.continuousAt_positiveMarginal_focal P.xi_pos P.xi_lt_one
    (activePatternTemplate c kind).residual₀ (P.clusterBoxBids kind t)
    (P.clusterBoxBids_nonneg kind t) 0 (P.bid_pos t.2.1)).comp hb
  have hi := (continuous_apply (0:Fin (N+1))).continuousAt.comp hb
  unfold clusterEqualPayoff LowBody.equalPayoff
  exact (continuous_fst.subtype_val.continuousAt.mul
    ((continuousAt_const.mul hp).sub (hp.pow 2))).sub
      (hi.mul ((continuousAt_const.mul hp).sub (continuousAt_const.mul (hp.pow 2))))

theorem cluster_equal_modulus {N : ℕ} (c : ℕ) (kind : Fin N→ Fin 4)
    (hng : ¬activePatternGuarded P.xi P.L P.U c P.z kind)
    (hequal : (activePatternTemplate c kind).residual₀=
      (activePatternTemplate c kind).residual₁) {err : ℝ} (herr : 0< err) :
    ∃delta : ℝ,0< delta ∧ ∀ t : P.ClusterBox N,∀ y : P.Bid,
      (t.2.1:ℝ)< y→(y:ℝ)-(t.2.1:ℝ)< delta→
        -err≤ P.clusterBoxGain c kind t y := by
  obtain ⟨delta,hd,hm⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous (P.continuous_clusterEqualPayoff c kind)) err herr
  refine ⟨delta,hd,?_⟩
  intro t y hup hstep
  have hdist : dist t (P.clusterBoxRaise t y)< delta := by
    simpa [clusterBoxRaise,Prod.dist_eq,
      Subtype.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hup.le),neg_sub] using ⟨hstep,hd⟩
  have hh := hm hdist
  rw [Real.dist_eq] at hh
  unfold clusterBoxGain activePhysicalPatternPayoff
  simp only [if_neg hng,if_pos hequal]
  change -err≤ P.clusterEqualPayoff c kind (P.clusterBoxRaise t y)-P.clusterEqualPayoff c kind t
  linarith [(abs_lt.mp hh).2]

lemma exists_active_rival_of_guarded {N : ℕ} (c : ℕ) (kind : Fin N→ Fin 4)
    (hg : activePatternGuarded P.xi P.L P.U c P.z kind) :
    ∃j : Fin N,kind j=1 := by
  by_contra hn
  have hnot : ∀ j : Fin N,kind j≠1 := by simpa using hn
  have hz : categoryCount 1 kind=0 := by
    simp [categoryCount,LowBody.hitCount,hnot]
  have hcard := hg.1
  rw [activePatternIndex_card,hz] at hcard
  omega

def clusterRankGain : ℝ := min (P.vlo-P.U) (P.eta*P.L)

lemma clusterRankGain_pos : 0< P.clusterRankGain :=
  lt_min (sub_pos.mpr P.value_surplus) (mul_pos P.eta_pos P.L_pos)

theorem cluster_guarded_modulus {N : ℕ} (c : ℕ) (kind : Fin N→ Fin 4)
    (hg : activePatternGuarded P.xi P.L P.U c P.z kind)
    (j : Fin N) (hj : kind j=1) {err : ℝ} (herr : 0< err) :
    ∃delta : ℝ,0< delta ∧ ∀ t : P.ClusterBox N,∀ y : P.Bid,
      (t.2.1:ℝ)< y→(y:ℝ)-(t.2.1:ℝ)< delta→
        P.clusterRankGain/(8*((N+1:ℕ):ℝ)^3)*
          (if (t.2.2.2 j:ℝ)∈ Icc (t.2.1:ℝ) (y:ℝ) then 1 else 0)-err ≤
            P.clusterBoxGain c kind t y := by
  let i := activePatternFocal kind
  let k : ActivePatternIndex kind := ⟨j.succ,by simp [activePatternPred,hj]⟩
  have hki : k≠i := by
    intro hh
    have hv := congrArg Subtype.val hh
    exact Fin.succ_ne_zero j hv
  let K0 := activePatternOwner c P.z kind 0
  let K1 := activePatternOwner c P.z kind 1
  let r := activePatternResidual c P.z kind
  obtain ⟨delta,hd,hcross⟩ := exists_sourceOwnerPayoff_finite_crossing
    (xi:=P.xi) (vhi:=P.vhi) P.L_pos P.eta_pos P.value_surplus r K0 K1 i
    hg.1 hg.2.2.1 hg.2.2.2.1 herr
  have hcard : Fintype.card (ActivePatternIndex kind)≤ N+1 := by
    simpa only [Fintype.card_fin] using
      (Fintype.card_le_of_injective (Subtype.val : ActivePatternIndex kind→ Fin (N+1))
        Subtype.val_injective)
  have hcoef := favored_crossing_coefficient_cubic (ι:=ActivePatternIndex kind)
    hg.1 hg.2.2.1 hg.2.2.2.1 hcard P.clusterRankGain_pos.le
  let G := (1-fillFraction (ι:=ActivePatternIndex kind) (K0+K1))*(P.clusterRankGain/2)
  have hG : 0≤ G := by
    have hf := fillFraction_bounds (ι:=ActivePatternIndex kind) hg.1 hg.2.2.1
      hg.2.2.2.1.le
    exact mul_nonneg (sub_nonneg.mpr hf.2) (div_nonneg P.clusterRankGain_pos.le (by norm_num))
  refine ⟨delta,hd,?_⟩
  intro t y hup hstep
  let x : FavoredBoxInput (ActivePatternIndex kind) P.vlo P.vhi P.L P.U :=
    (t.1,fun i => Fin.cases t.2.1 (fun j => t.2.2.2 j) i.val)
  have hfull := hcross x y hup hstep
  have hsum : (if (t.2.2.2 j:ℝ)∈ Icc (t.2.1:ℝ) (y:ℝ) then G/4 else 0) ≤
      ∑j' : ActivePatternIndex kind,
        if j'≠i ∧ (x.2 j':ℝ)∈ Icc (x.2 i:ℝ) (y:ℝ) then G/4 else 0 := by
    have hh := Finset.single_le_sum (s:=Finset.univ)
      (f:=fun j' : ActivePatternIndex kind =>
        if j'≠i ∧ (x.2 j':ℝ)∈ Icc (x.2 i:ℝ) (y:ℝ) then G/4 else 0)
      (fun j' _ => by split_ifs <;> positivity) (Finset.mem_univ k)
    simpa [x,k,i,activePatternFocal,hki] using hh
  have hlower := div_le_div_of_nonneg_right hsum (rankDenominator_pos (ι:=ActivePatternIndex kind)).le
  have hscalar : P.clusterRankGain/(8*((N+1:ℕ):ℝ)^3)*
      (if (t.2.2.2 j:ℝ)∈ Icc (t.2.1:ℝ) (y:ℝ) then 1 else 0) ≤
      (if (t.2.2.2 j:ℝ)∈ Icc (t.2.1:ℝ) (y:ℝ) then G/4 else 0)/
        rankDenominator (ActivePatternIndex kind) := by
    split_ifs
    · simpa only [G,mul_one,div_div] using hcoef
    · simp
  have hreal : (fun j => (x.2 j:ℝ))=
      activePhysicalActiveBids kind (P.clusterBoxPhysical t) := by
    funext j'
    change (Fin.cases t.2.1 (fun j => t.2.2.2 j) j'.val : P.Bid).val=
      Fin.cases (t.2.1:ℝ) (fun j => (t.2.2.2 j:ℝ)) j'.val
    exact Fin.cases rfl (fun _ => rfl) j'.val
  have hraise : Function.update (fun j => (x.2 j:ℝ)) i (y:ℝ)=
      activePhysicalActiveBids kind (P.clusterBoxPhysical (P.clusterBoxRaise t y)) := by
    ext j'
    by_cases he : j'=i
    · subst j'
      simp [i,activePatternFocal,clusterBoxPhysical,clusterBoxRaise,activePhysicalActiveBids]
    · simp only [Function.update_of_ne he]
      rw [congrFun hreal j']
      have haux (q : Fin (N+1)) (hq : q≠0) :
          Fin.cases (motive:=fun _ : Fin (N+1) => ℝ) (t.2.1:ℝ)
            (fun j => (t.2.2.2 j:ℝ)) q=
            Fin.cases (motive:=fun _ : Fin (N+1) => ℝ) (y:ℝ)
              (fun j => (t.2.2.2 j:ℝ)) q := by
        obtain ⟨k,hk⟩ := Fin.eq_succ_of_ne_zero hq
        rw [hk]
        rfl
      exact haux j'.val (fun hh => he (Subtype.ext hh))
  rw [hraise,hreal] at hfull
  unfold clusterBoxGain activePhysicalPatternPayoff
  simp only [if_pos hg]
  change _ ≤ sourceOwnerPayoff P.xi P.eta t.1 _ r K0 K1 i-
    sourceOwnerPayoff P.xi P.eta t.1 _ r K0 K1 i
  change (∑ j', if j'≠i ∧ (x.2 j':ℝ)∈Icc (x.2 i:ℝ) (y:ℝ)
      then G/4 else 0)/rankDenominator (ActivePatternIndex kind)-err ≤ _ at hfull
  exact (sub_le_sub_right (hscalar.trans hlower) err).trans hfull

theorem all_pattern_cluster_modulus (N c : ℕ) {err : ℝ} (herr : 0< err) :
    ∃delta : ℝ,0< delta ∧ ∀ kind : Fin N→ Fin 4,
      (activePatternGuarded P.xi P.L P.U c P.z kind →
        ∃j : Fin N,kind j=1 ∧ ∀ t : P.ClusterBox N,∀ y : P.Bid,
          (t.2.1:ℝ)< y→(y:ℝ)-(t.2.1:ℝ)< delta→
            P.clusterRankGain/(8*((N+1:ℕ):ℝ)^3)*
              (if (t.2.2.2 j:ℝ)∈ Icc (t.2.1:ℝ) (y:ℝ) then 1 else 0)-err ≤
                P.clusterBoxGain c kind t y) ∧
      (¬activePatternGuarded P.xi P.L P.U c P.z kind →
        (activePatternTemplate c kind).residual₀=(activePatternTemplate c kind).residual₁ →
        ∀ t : P.ClusterBox N,∀ y : P.Bid,
          (t.2.1:ℝ)< y→(y:ℝ)-(t.2.1:ℝ)< delta→
            -err≤ P.clusterBoxGain c kind t y) := by
  let C := fun (kind : Fin N→ Fin 4) (delta : ℝ) =>
    (activePatternGuarded P.xi P.L P.U c P.z kind →
      ∃j : Fin N,kind j=1 ∧ ∀ t : P.ClusterBox N,∀ y : P.Bid,
        (t.2.1:ℝ)< y→(y:ℝ)-(t.2.1:ℝ)< delta→
          P.clusterRankGain/(8*((N+1:ℕ):ℝ)^3)*
            (if (t.2.2.2 j:ℝ)∈ Icc (t.2.1:ℝ) (y:ℝ) then 1 else 0)-err ≤
              P.clusterBoxGain c kind t y) ∧
    (¬activePatternGuarded P.xi P.L P.U c P.z kind →
      (activePatternTemplate c kind).residual₀=(activePatternTemplate c kind).residual₁ →
      ∀ t : P.ClusterBox N,∀ y : P.Bid,
        (t.2.1:ℝ)< y→(y:ℝ)-(t.2.1:ℝ)< delta→-err≤ P.clusterBoxGain c kind t y)
  have hlocal (kind : Fin N→ Fin 4) : ∃d : ℝ,0< d ∧ C kind d := by
    by_cases hg : activePatternGuarded P.xi P.L P.U c P.z kind
    · obtain ⟨j,hj⟩ := P.exists_active_rival_of_guarded c kind hg
      obtain ⟨d,hd,hm⟩ := P.cluster_guarded_modulus c kind hg j hj herr
      exact ⟨d,hd,fun _ => ⟨j,hj,hm⟩,fun hn => False.elim (hn hg)⟩
    · by_cases he : (activePatternTemplate c kind).residual₀=
          (activePatternTemplate c kind).residual₁
      · obtain ⟨d,hd,hm⟩ := P.cluster_equal_modulus c kind hg he herr
        exact ⟨d,hd,fun hh => False.elim (hg hh),fun _ _ => hm⟩
      · exact ⟨1,by norm_num,fun hh => False.elim (hg hh),fun _ hh => False.elim (he hh)⟩
  choose d hd hcontrol using hlocal
  have hmin : ∀ s : Finset (Fin N→ Fin 4),∃delta : ℝ,0< delta ∧ ∀ kind∈ s,delta≤ d kind := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert kind s hnot ih =>
      obtain ⟨delta,hdelta,hall⟩ := ih
      refine ⟨min delta (d kind),lt_min hdelta (hd kind),?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with he|hs
      · subst k
        exact min_le_right _ _
      · exact (min_le_left _ _).trans (hall k hs)
  obtain ⟨delta,hdelta,hall⟩ := hmin Finset.univ
  refine ⟨delta,hdelta,?_⟩
  intro kind
  have hle := hall kind (Finset.mem_univ kind)
  constructor
  · intro hg
    obtain ⟨j,hj,hm⟩ := (hcontrol kind).1 hg
    exact ⟨j,hj,fun t y hup hstep => hm t y hup (hstep.trans_le hle)⟩
  · intro hg he t y hup hstep
    exact (hcontrol kind).2 hg he t y hup (hstep.trans_le hle)

end FCAppendix.Affine.Hybrid.Finish01.Primitives
