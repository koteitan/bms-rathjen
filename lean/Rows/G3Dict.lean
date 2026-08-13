import Rows.Selected

open TM Term BMS Trans Rows Rows.Selected

namespace Rows.Selected.G3Dict

def rep0 : Nat → Trans.Dict.BT
  | 0 => .zero
  | k+1 => .D 0 (rep0 k)

theorem tower_lt_Z (n : Nat) :
    lt (Evidence.WF.tower n) (Z zero) = true := by
  exact Evidence.WF.lt_trans_inT
    (Evidence.WF.inT_of_cnv _ (Evidence.WF.cnv_tower n))
    (Evidence.WF.inT_of_cnv _ Evidence.WF.cnv_eps0T)
    (by decide) (Evidence.WF.lt_tower_eps0 n) (by decide)

theorem collapse_zero_tower (n : Nat) :
    Trans.Dict.collapse 0 (Evidence.WF.tower n) = Evidence.WF.tower (n+1) := by
  cases n with
  | zero => rfl
  | succ n =>
    have hw : Trans.Dict.wcnf (Z zero) [Evidence.WF.tower (n+1)] =
        ([], Evidence.WF.tower (n+1)) := by
      rw [Trans.Dict.wcnf, if_pos (tower_lt_Z (n+1))]
      rfl
    unfold Trans.Dict.collapse
    simp only [Trans.Dict.reg, TM.Term.ofNat]
    rw [show (Evidence.WF.tower (n+1)).toList =
        [Evidence.WF.tower (n+1)] from rfl, hw]
    simp only [List.foldl_nil, Option.getD_none]
    unfold Evidence.WF.tower
    change TM.Term.omegaNF (phi zero (Evidence.WF.tower n)) =
      phi zero (phi zero (Evidence.WF.tower n))
    exact Evidence.StageA.omegaNF_of_compPhi0
      (Evidence.StageA.compPhi0_phi0 (Evidence.WF.tower n))

theorem dict_rep0 (n : Nat) :
    Trans.Dict.dict (rep0 (n+1)) = Evidence.WF.tower n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep0, Trans.Dict.dict_D, ih]
    exact collapse_zero_tower n

theorem tower_lt_Z1 (n : Nat) : lt (Evidence.WF.tower n) (Z one) = true := by
  exact Evidence.WF.lt_trans_inT
    (Evidence.WF.inT_of_cnv _ (Evidence.WF.cnv_tower n))
    (by decide) (by decide) (tower_lt_Z n) (by decide)

theorem plus_Z_tower (n : Nat) :
    plus (Z zero) (Evidence.WF.tower n) =
      add (Z zero) (Evidence.WF.tower n) := by
  unfold plus
  rw [show (Evidence.WF.tower n).toList = [Evidence.WF.tower n] from by
      cases n <;> rfl]
  rw [show (Z zero).toList = [Z zero] from rfl]
  simp only [List.filter_cons, List.filter_nil,
    show le (Evidence.WF.tower n) (Z zero) = true from
      Evidence.WF.le_of_lt (tower_lt_Z n), if_true]
  rfl

def Q : Nat → Term
  | 0 => Z zero
  | n+1 => add (Z zero) (Evidence.WF.tower (n+1))

def X (n : Nat) : Term := phi zero (Q n)
def Y (n : Nat) : Term := phi zero (X n)

theorem collapse_one_tower (n : Nat) :
    Trans.Dict.collapse 1 (Evidence.WF.tower n) = X n := by
  have hw : Trans.Dict.wcnf (Z one) [Evidence.WF.tower n] =
      ([], Evidence.WF.tower n) := by
    rw [Trans.Dict.wcnf, if_pos (tower_lt_Z1 n)]
    rfl
  unfold Trans.Dict.collapse
  simp only [Trans.Dict.reg, TM.Term.ofNat]
  rw [show plus zero one = one from rfl]
  rw [show (Evidence.WF.tower n).toList = [Evidence.WF.tower n] from by
      cases n <;> rfl, hw]
  simp only [List.foldl_nil, Option.getD_none]
  cases n with
  | zero => rfl
  | succ n =>
    unfold X Q
    rw [Rows.ProofsB.plus_zero_left (by cases n <;> rfl), plus_Z_tower]
    change omegaNF (add (Z zero) (Evidence.WF.tower (n+1))) = _
    unfold omegaNF
    simp only [show lt M (add (Z zero) (Evidence.WF.tower (n+1))) = false from by
        rfl,
      Bool.false_eq_true, if_false,
      show ((add (Z zero) (Evidence.WF.tower (n+1)) == M)) = false from rfl]
    unfold phiNF
    simp only [isSC, Bool.false_and, Bool.false_eq_true, if_false]
    unfold phiNFsucc
    rw [show splitFin (add (Z zero) (Evidence.WF.tower (n+1))) =
        (add (Z zero) (Evidence.WF.tower (n+1)), 0) from by
      unfold splitFin
      rw [show (add (Z zero) (Evidence.WF.tower (n+1))).toList =
          [Z zero, Evidence.WF.tower (n+1)] from by
        cases n <;> rfl]
      change
        (ofList ([Z zero, Evidence.WF.tower (n+1)].take
            (2 - ([Evidence.WF.tower (n+1), Z zero].takeWhile (fun x => x == one)).length)),
          ([Evidence.WF.tower (n+1), Z zero].takeWhile (fun x => x == one)).length) = _
      simp only [List.takeWhile,
        show (Evidence.WF.tower (n+1) == one) = false from by cases n <;> rfl,
        Bool.false_eq_true, if_false]
      rfl]
    rfl

theorem Q_lt_Z1 (n : Nat) : lt (Q n) (Z one) = true := by
  cases n <;> rfl

theorem X_lt_Z1 (n : Nat) : lt (X n) (Z one) = true := by
  show lt (phi zero (Q n)) (Z one) = true
  unfold lt
  cases h : fuelOf (phi zero (Q n)) (Z one) with
  | zero =>
    simp [fuelOf] at h
  | succ f =>
    rw [Evidence.WF.ltF_succ_phi_Z]
    simp only [Bool.and_eq_true]
    have hq := Evidence.WF.deg_pos (Q n)
    have hz := Evidence.WF.deg_pos (Z one)
    have hf : (Q n).deg + (Z one).deg ≤ f := by
      change (Q n).deg + (1 + one.deg) ≤ f
      simp only [fuelOf, Term.deg] at h
      omega
    constructor
    · exact Evidence.WF.ltF_left_zero (by omega) (by simp)
    · rw [← Evidence.WF.lt_eq_ltF (Q n) (Z one) f hf]
      exact Q_lt_Z1 n

theorem plus_Z_X (n : Nat) : plus (Z zero) (X n) = X n := by
  unfold plus X
  rw [show (phi zero (Q n)).toList = [phi zero (Q n)] from rfl]
  rw [show (Z zero).toList = [Z zero] from rfl]
  simp only [List.filter_cons, List.filter_nil]
  rw [show le (phi zero (Q n)) (Z zero) = false from by
    unfold le
    rw [show ((phi zero (Q n) == Z zero)) = false from rfl]
    simp only [Bool.false_or]
    cases n <;> rfl]
  rfl

theorem collapse_one_X (n : Nat) :
    Trans.Dict.collapse 1 (X n) = Y n := by
  have hw : Trans.Dict.wcnf (Z one) [X n] = ([], X n) := by
    rw [Trans.Dict.wcnf, if_pos (X_lt_Z1 n)]
    rfl
  unfold Trans.Dict.collapse
  simp only [Trans.Dict.reg, TM.Term.ofNat]
  rw [show plus zero one = one from rfl]
  rw [show (X n).toList = [X n] from rfl, hw]
  simp only [List.foldl_nil, Option.getD_none]
  rw [Rows.ProofsB.plus_zero_left rfl, plus_Z_X]
  unfold Y X
  exact Evidence.StageA.omegaNF_of_compPhi0
    (Evidence.StageA.compPhi0_phi0 (Q n))

theorem logOm_Y (n : Nat) : Trans.Dict.logOm (Y n) = X n := by
  cases n <;> rfl

theorem logOm_X_succ (n : Nat) :
    Trans.Dict.logOm (X (n+1)) = Q (n+1) := by
  unfold Trans.Dict.logOm X
  change (if phiShifted zero (Q (n+1)) then plus (Q (n+1)) one else Q (n+1)) = _
  rw [show phiShifted zero (Q (n+1)) = false from by cases n <;> rfl]
  rfl

theorem divAP_Z_X (n : Nat) :
    Trans.Dict.divAP (Z zero) (X n) = Evidence.WF.tower (n+1) := by
  cases n with
  | zero => rfl
  | succ n =>
    unfold Trans.Dict.divAP
    rw [logOm_X_succ]
    unfold Trans.Dict.subAP Q
    rw [show (add (Z zero) (Evidence.WF.tower (n+1))).toList =
        [Z zero, Evidence.WF.tower (n+1)] from by cases n <;> rfl]
    simp only [show ((Z zero == Z zero)) = true from rfl, if_true]
    unfold Evidence.WF.tower
    exact Evidence.StageA.omegaNF_of_compPhi0
      (Evidence.StageA.compPhi0_phi0 (Evidence.WF.tower n))

theorem X_not_lt_Z (n : Nat) : lt (X n) (Z zero) = false := by
  cases n <;> rfl

theorem Y_not_lt_Z (n : Nat) : lt (Y n) (Z zero) = false := by
  cases n <;> rfl

theorem wcnf_Y (n : Nat) :
    Trans.Dict.wcnf (Z zero) [Y n] =
      ([(Evidence.WF.tower (n+1), one)], zero) := by
  rw [Trans.Dict.wcnf, if_neg (by
    rw [Y_not_lt_Z n]
    exact Bool.noConfusion)]
  rw [logOm_Y]
  dsimp only
  rw [show (X n).toList = [X n] from rfl]
  simp only [X_not_lt_Z, Bool.not_false, if_true, List.filter_cons, List.filter_nil,
    List.map_cons, List.map_nil, divAP_Z_X, ofList]
  rw [Trans.Dict.wcnf]
  rfl

theorem collapse_zero_Y (n : Nat) :
    Trans.Dict.collapse 0 (Y n) = phi (Evidence.WF.tower (n+1)) zero := by
  unfold Trans.Dict.collapse
  simp only [Trans.Dict.reg, TM.Term.ofNat]
  rw [show (Y n).toList = [Y n] from rfl, wcnf_Y]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [show le (Z zero) (Evidence.WF.tower (n+1)) = false from by
    unfold le
    rw [show ((Z zero == Evidence.WF.tower (n+1))) = false from by cases n <;> rfl]
    simp only [Bool.false_or]
    exact Evidence.WF.lt_asymm_inT
      (Evidence.WF.inT_of_cnv _ (Evidence.WF.cnv_tower (n+1))) (by decide)
      (tower_lt_Z (n+1))]
  simp only [Bool.false_eq_true, if_false]
  rw [show Trans.Dict.sub1 one = zero from rfl]
  simp only [show ((0:Nat) == 0) = true from rfl, if_true, Option.getD_some,
    TM.Term.plus_zero]
  rw [Rows.ProofsB.plus_zero_left (Rows.ProofsB.isAP_phiNF _ _)]
  rw [show phiNF (Evidence.WF.tower (n+1)) zero =
      phi (Evidence.WF.tower (n+1)) zero from by
    exact Rows.ProofsB.phiNF_zero_arg (by cases n <;> rfl)]
  change omegaNF (phi (Evidence.WF.tower (n+1)) zero) = _
  exact Rows.ProofsB.omegaNF_phi_ne_zero (Evidence.WF.tower_ne_zero (n+1))

theorem dict_LBT (n : Nat) :
    Trans.Dict.dict (.D 0 (.D 1 (.D 1 (rep0 (n+1))))) =
      phi (Evidence.WF.tower (n+1)) zero := by
  rw [Trans.Dict.dict_D, Trans.Dict.dict_D, Trans.Dict.dict_D, dict_rep0,
    collapse_one_tower, collapse_one_X, collapse_zero_Y]

theorem iterT_tower : ∀ n,
    Rows.ProofsB.iterT zero (n+1) = Evidence.WF.tower n
  | 0 => rfl
  | n+1 => by
    rw [Rows.ProofsB.iterT_succ (a := zero) rfl, iterT_tower n]
    rfl

theorem fsN_t (n : Nat) :
    fsN (phi (phi one zero) zero) (n+2) =
      phi (Evidence.WF.tower (n+1)) zero := by
  rw [fsN]
  change phiNF (fsN Rows.Selected.e0 (n+2)) zero = _
  rw [Rows.Selected.fsN_e0]
  show phiNF (Rows.ProofsB.iterT zero (n+2)) zero = _
  rw [iterT_tower (n+1)]
  exact Rows.ProofsB.phiNF_zero_arg (by cases n <;> rfl)

theorem dict_LBT_fsN (n : Nat) :
    Trans.Dict.dict (.D 0 (.D 1 (.D 1 (rep0 (n+1))))) =
      fsN (phi (phi one zero) zero) (n+2) := by
  rw [dict_LBT, fsN_t]

end Rows.Selected.G3Dict
