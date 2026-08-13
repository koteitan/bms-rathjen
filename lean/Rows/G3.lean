import Rows.G3Dict

open TM Term BMS Trans Rows Rows.Selected

namespace Rows.Selected
namespace G3

def M : BMS.Matrix := [[0,0],[1,1],[2,1],[3,0],[4,1]]
def t : Term := phi (phi (phi zero zero) zero) zero
def A (a m : Nat) : Trans.Recal.PS :=
  (List.range m).map (fun k => (((k + a : Nat) : Int), (0 : Int)))
def C (a m : Nat) : Trans.Recal.PS := (0,0) :: A a m
def E (a m : Nat) : Trans.Recal.PS := (((a:Nat):Int),(1:Int)) :: A (a+1) m
def L (m : Nat) : Trans.Recal.PS :=
  (0,0) :: (1,1) :: (2,1) :: A 3 m
def R (m : Nat) : Trans.Recal.PS := (2,1) :: A 3 m
def S (m : Nat) : Trans.Recal.PS := (0,0) :: (3,1) :: A 4 m
def B (m : Nat) : Trans.Recal.PS := (0,0) :: (1,1) :: A 2 m
def rep0 : Nat → Trans.Dict.BT
  | 0 => .zero
  | k+1 => .D 0 (rep0 k)
def LBT (m : Nat) : Trans.Dict.BT := .D 0 (.D 1 (.D 1 (rep0 m)))

theorem rep0_eq_G3Dict : ∀ n, rep0 n = G3Dict.rep0 n
  | 0 => rfl
  | n+1 => by rw [rep0, G3Dict.rep0, rep0_eq_G3Dict n]

/-! Structural lemmas for the ascending row-zero ladder. -/

theorem A_zero (a : Nat) : A a 0 = [] := rfl

theorem A_succ (a m : Nat) :
    A a (m+1) = (((a : Nat) : Int), (0 : Int)) :: A (a+1) m := by
  unfold A
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro k _
    apply Prod.ext <;> simp
    push_cast
    omega

theorem length_A (a m : Nat) : (A a m).length = m := by
  simp [A]

theorem A_succ_last (a m : Nat) :
    A a (m+1) = A a m ++ [((((a+m : Nat) : Int), (0 : Int)))] := by
  unfold A
  rw [List.range_succ, List.map_append]
  simp [Nat.add_comm]

theorem incrFirst_A (a d m : Nat) :
    Trans.Recal.incrFirst (A a m) (d : Int) = A (a+d) m := by
  unfold Trans.Recal.incrFirst A
  rw [List.map_map]
  apply List.map_congr_left
  intro k _
  apply Prod.ext <;> simp
  push_cast
  omega

theorem derp_A (a m : Nat) : Trans.Recal.derp (A a (m+1)) = A (a+1) m := by
  rw [A_succ]
  rfl

theorem L_succ (m : Nat) : L (m+1) = L m ++ [((((m+3 : Nat) : Int), (0 : Int)))] := by
  unfold L
  rw [A_succ_last]
  simp [Nat.add_comm]

theorem length_L (m : Nat) : (L m).length = m+3 := by
  simp [L, length_A]

theorem predP_L (m : Nat) : Trans.Recal.predP (L (m+1)) = L m := by
  rw [L_succ]
  simp [Trans.Recal.predP, length_L]

theorem getD_A (a m i : Nat) (h : i < m) :
    (A a m).getD i (0,0) = ((((i+a : Nat) : Int), (0 : Int))) := by
  unfold A
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

theorem lenI_A (a m : Nat) : Trans.Recal.lenI (A a m) = (m : Int) := by
  unfold Trans.Recal.lenI
  rw [length_A]

theorem gp0_A (a m : Nat) (j : Int) (h0 : 0 ≤ j) (h1 : j < (m : Int)) :
    Trans.Recal.gp0 (A a m) j = (a : Int) + j := by
  show (if j < 0 then 0 else ((A a m).getD j.toNat (0,0)).1) = _
  rw [if_neg (by omega), getD_A a m j.toNat (by omega)]
  push_cast
  omega

theorem gp1_A (a m : Nat) (j : Int) (h0 : 0 ≤ j) (h1 : j < (m : Int)) :
    Trans.Recal.gp1 (A a m) j = 0 := by
  show (if j < 0 then 0 else ((A a m).getD j.toNat (0,0)).2) = 0
  rw [if_neg (by omega), getD_A a m j.toNat (by omega)]

theorem fpar0_A_zero (a m : Nat) (hm : 1 ≤ m) :
    Trans.Recal.fpar0 (A a m) 0 0 = -1 := by
  show (if (0 : Int) < 0 ∨ (0 : Int) ≥ Trans.Recal.lenI (A a m) then -1
        else Trans.Recal.fpar0Aux ((A a m).length + 1) (A a m)
          (Trans.Recal.gp0 (A a m) 0) (-1) 0) = -1
  rw [if_neg (by rw [lenI_A]; omega), length_A]
  cases m with
  | zero => omega
  | succ p =>
    simp only [Trans.Recal.fpar0Aux]
    rw [if_pos (by omega)]

theorem fpar_A (a m k : Nat) (hk0 : 0 < k) (hk : k < m) :
    Trans.Recal.fpar (A a m) 0 (k : Int) 0 = ((k-1 : Nat) : Int) := by
  show (if (k : Int) < 0 ∨ (k : Int) ≥ Trans.Recal.lenI (A a m) then -1
        else if (0 : Nat) == 0 then
          Trans.Recal.fpar0Aux ((A a m).length + 1) (A a m)
            (Trans.Recal.gp0 (A a m) (k : Int)) ((k : Int) - 1) 0
        else _) = _
  rw [if_neg (by rw [lenI_A]; omega)]
  simp only [show ((0 : Nat) == 0) = true from rfl, if_true]
  rw [gp0_A a m (k : Int) (by omega) (by omega), length_A]
  cases m with
  | zero => omega
  | succ p =>
    simp only [Trans.Recal.fpar0Aux]
    rw [if_neg (by omega), gp0_A a (p+1) ((k : Int)-1) (by omega) (by omega), if_pos (by omega)]
    omega

theorem fpar_A_zero (a m : Nat) (hm : 1 ≤ m) :
    Trans.Recal.fpar (A a m) 0 0 0 = -1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_A]; omega), if_pos (by rfl)]
  have h := fpar0_A_zero a m hm
  unfold Trans.Recal.fpar0 at h
  rw [if_neg (by rw [lenI_A]; omega)] at h
  exact h

theorem fpar1_A_one (a m : Nat) (hm : 2 ≤ m) :
    Trans.Recal.fpar (A a m) 1 1 0 = -1 := by
  show (if (1 : Int) < 0 ∨ (1 : Int) ≥ Trans.Recal.lenI (A a m) then -1
        else if (1 : Nat) == 0 then _
        else Trans.Recal.fpar1Aux ((A a m).length + 1) (A a m)
          (Trans.Recal.gp1 (A a m) 1) 1 0) = -1
  rw [if_neg (by rw [lenI_A]; omega)]
  simp only [show ((1 : Nat) == 0) = false from rfl, Bool.false_eq_true, if_false]
  rw [gp1_A a m 1 (by omega) (by omega), length_A]
  cases m with
  | zero => omega
  | succ p =>
    simp only [Trans.Recal.fpar1Aux]
    rw [show Trans.Recal.fpar0 (A a (p+1)) 1 0 = 0 from by
          have h := fpar_A a (p+1) 1 (by omega) (by omega)
          simpa using h,
        if_neg (by omega), gp1_A a (p+1) 0 (by omega) (by omega), if_neg (by omega)]
    cases p with
    | zero => omega
    | succ q =>
      simp only [Trans.Recal.fpar1Aux]
      rw [fpar0_A_zero a (q+2) (by omega), if_pos (by omega)]

theorem isParentP_A_one (a m : Nat) (hm : 2 ≤ m) :
    Trans.Recal.isParentP (A a m) 1 1 0 = false := by
  unfold Trans.Recal.isParentP
  rw [fpar1_A_one a m hm, lenI_A]
  simp

theorem trMax_A (a m : Nat) (hm : 1 ≤ m) : Trans.Recal.trMax (A a m) = 0 := by
  show Trans.Recal.trMaxAux ((A a m).length + 1) (A a m) 0 = 0
  rw [length_A]
  cases m with
  | zero => omega
  | succ p =>
    simp only [Trans.Recal.trMaxAux]
    rw [if_neg (by rw [lenI_A]; omega)]
    cases p with
    | zero =>
      rw [if_pos (by rfl)]
    | succ q =>
      rw [show Trans.Recal.isParentP (A a (q+1+1)) 1 (0+1) 0 = false from
        isParentP_A_one a (q+1+1) (by omega), if_pos (by rfl)]

theorem isAncAux_A (a m k : Nat) : ∀ f : Nat, k < m → k < f →
    Trans.Recal.isAncAux f (A a m) 0 (k : Int) 0 = true := by
  refine Nat.strongRecOn (motive := fun k => ∀ f : Nat, k < m → k < f →
    Trans.Recal.isAncAux f (A a m) 0 (k : Int) 0 = true) k ?_
  intro k ih f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0 : k = 0
    · subst k; rw [if_pos (by rfl)]
    · rw [show ((0:Int) == (k:Int)) = false from
          beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true, if_false]
      rw [fpar_A a m k (by omega) hkm]
      rw [show ((((k-1 : Nat) : Int)) == (-1:Int)) = false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true, if_false]
      exact ih (k-1) (by omega) f (by omega) (by omega)

theorem isAnc_A (a m k : Nat) (hk : k < m) :
    Trans.Recal.isAnc (A a m) 0 (k : Int) 0 = true := by
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_A]; omega)]
  rw [length_A]
  exact isAncAux_A a m k (m+1) hk (by omega)

theorem isPrincipalP_A (a m : Nat) (hm : 2 ≤ m) :
    Trans.Recal.isPrincipalP (A a m) = true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (A a m) = false from by
        unfold Trans.Recal.isZeroP
        rw [length_A]
        rw [show (m == 1) = false from by simp [show m ≠ 1 from by omega]]
        rfl,
      lenI_A]
  have h := isAnc_A a m (m-1) (by omega)
  rw [show (m:Int)-1 = ((m-1:Nat):Int) by omega, h]
  rfl

theorem fAncAux_A_last (a m k : Nat) : ∀ (f : Nat) (acc : List Int),
    k < m → k < f → acc.getLast? = some (k : Int) →
    (Trans.Recal.fAncAux f (A a m) 0 (k : Int) 0 acc).getLast? = some 0 := by
  refine Nat.strongRecOn (motive := fun k => ∀ (f : Nat) (acc : List Int),
    k < m → k < f → acc.getLast? = some (k : Int) →
    (Trans.Recal.fAncAux f (A a m) 0 (k : Int) 0 acc).getLast? = some 0) k ?_
  intro k ih f acc hkm hkf hlast
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.fAncAux]
    by_cases hk0 : k = 0
    · subst k
      rw [show Trans.Recal.fpar (A a m) 0 ((0:Nat):Int) 0 = -1 from by
        simpa using fpar_A_zero a m (by omega), if_neg (by omega)]
      exact hlast
    · rw [fpar_A a m k (by omega) hkm, if_pos (by omega)]
      exact ih (k-1) (by omega) f (acc ++ [((k-1:Nat):Int)])
        (by omega) (by omega) (by simp)

theorem fAnc_A_last (a m : Nat) (hm : 1 ≤ m) :
    (Trans.Recal.fAnc (A a m) 0 ((m-1:Nat):Int) 0).getLast? = some 0 := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by rw [lenI_A]; omega), length_A]
  exact fAncAux_A_last a m (m-1) (m+1) [((m-1:Nat):Int)]
    (by omega) (by omega) (by simp)

theorem slice_A_full (a m : Nat) :
    Trans.Recal.slice (A a m) 0 (m : Int) = A a m := by
  unfold Trans.Recal.slice
  simp only [Int.toNat_zero, List.drop_zero]
  rw [show ((m:Int)-0).toNat = m by omega]
  simpa only [length_A] using (List.take_length : (A a m).take (A a m).length = A a m)

theorem ppairAux_neg (f : Nat) (P : Trans.Recal.PS) (acc : List Trans.Recal.PS) :
    Trans.Recal.ppairAux f P (-1) acc = acc := by
  cases f <;> rfl

theorem ppair_A (a m : Nat) (hm : 1 ≤ m) :
    Trans.Recal.ppair (A a m) = [A a m] := by
  cases m with
  | zero => omega
  | succ p =>
    unfold Trans.Recal.ppair
    rw [length_A, lenI_A]
    simp only [Trans.Recal.ppairAux]
    rw [if_neg (by omega), show ((p+1:Nat):Int)-1 = (p:Int) by omega]
    have hlast := fAnc_A_last a (p+1) (by omega)
    rw [show p+1-1 = p by omega] at hlast
    rw [hlast]
    simp only [Option.getD_some]
    rw [show (p:Int)+1 = ((p+1:Nat):Int) by omega, slice_A_full]
    rw [if_pos (by omega)]

theorem incrFirst_A_neg (a m : Nat) :
    Trans.Recal.incrFirst (A (a+1) m) (-1) = A a m := by
  unfold Trans.Recal.incrFirst A
  rw [List.map_map]
  apply List.map_congr_left
  intro k _
  apply Prod.ext <;> simp
  push_cast
  omega

theorem drop_A (a m : Nat) : (A a (m+1)).drop 1 = A (a+1) m := by
  rw [A_succ]
  rfl

theorem brF_A0 (m : Nat) :
    Trans.Recal.brF (A 0 (m+2)) = [A 1 (m+1)] := by
  unfold Trans.Recal.brF
  rw [trMax_A 0 (m+2) (by omega)]
  show Trans.Recal.ppair ((A 0 (m+2)).drop 1) = _
  rw [show m+2 = (m+1)+1 by omega, drop_A]
  exact ppair_A 1 (m+1) (by omega)

theorem firstNodes_A0 (m : Nat) :
    Trans.Recal.firstNodes (A 0 (m+2)) = [1, ((m+2:Nat):Int)] := by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [brF_A0, trMax_A 0 (m+2) (by omega)]
  simp [length_A]
  omega

theorem joints_A0 (m : Nat) : Trans.Recal.joints (A 0 (m+2)) = [0] := by
  unfold Trans.Recal.joints
  rw [firstNodes_A0]
  change [Trans.Recal.fpar (A 0 (m+2)) 0 1 0] = [0]
  rw [show Trans.Recal.fpar (A 0 (m+2)) 0 1 0 = 0 from by
    have h := fpar_A 0 (m+2) 1 (by omega) (by omega)
    simpa using h]

theorem cons_derp_A (a m : Nat) :
    ((((a:Nat):Int), (0:Int))) :: Trans.Recal.derp (A a (m+1)) = A a (m+1) := by
  rw [derp_A, A_succ]

theorem red_A0_one : ∀ f : Nat, Trans.Recal.red f (A 0 1) = A 0 1
  | 0 => rfl
  | f+1 => by
    rw [Trans.Recal.red]
    rfl

theorem red_A1 (f m : Nat) :
    Trans.Recal.red (f+1) (A 1 (m+1)) = Trans.Recal.red f (A 0 (m+1)) := by
  cases m with
  | zero =>
    rw [red_A0_one]
    rw [Trans.Recal.red]
    rfl
  | succ p =>
    conv => lhs; rw [Trans.Recal.red]
    rw [show Trans.Recal.isZeroP (A 1 (p+2)) = false from by
          unfold Trans.Recal.isZeroP
          rw [length_A]
          simp,
        isPrincipalP_A 1 (p+2) (by omega)]
    simp only [Bool.false_eq_true, if_false, if_true]
    rw [show (Trans.Recal.gp0 (A 1 (p+2)) 0 == 0
        && Trans.Recal.gp1 (A 1 (p+2)) 0 == 0) = false from by
          rw [gp0_A 1 (p+2) 0 (by omega) (by omega),
            gp1_A 1 (p+2) 0 (by omega) (by omega)]
          rfl]
    simp only [Bool.false_eq_true, if_false]
    rw [show (Trans.Recal.gp1 (A 1 (p+2)) 0 == 0) = true from by
          rw [gp1_A 1 (p+2) 0 (by omega) (by omega)]
          rfl]
    simp only [if_true]
    rw [show -(Trans.Recal.gp0 (A 1 (p+2)) 0) = (-1:Int) from by
          rw [gp0_A 1 (p+2) 0 (by omega) (by omega)]
          omega,
        incrFirst_A_neg]

theorem red_A0_step (f m : Nat) :
    Trans.Recal.red (f+2) (A 0 (m+2)) =
      (((0:Int),(0:Int))) :: Trans.Recal.incrFirst (Trans.Recal.red f (A 0 (m+1))) 1 := by
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (A 0 (m+2)) = false from by
        unfold Trans.Recal.isZeroP
        rw [length_A]
        simp,
      isPrincipalP_A 0 (m+2) (by omega)]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [show (Trans.Recal.gp0 (A 0 (m+2)) 0 == 0
      && Trans.Recal.gp1 (A 0 (m+2)) 0 == 0) = true from by
        rw [gp0_A 0 (m+2) 0 (by omega) (by omega),
          gp1_A 0 (m+2) 0 (by omega) (by omega)]
        rfl]
  simp only [if_true]
  rw [trMax_A 0 (m+2) (by omega), lenI_A]
  rw [show ((0:Int) == ((m+2:Nat):Int)-1) = false from
    beq_eq_false_iff_ne.mpr (by omega)]
  simp only [Bool.false_eq_true, if_false, brF_A0, firstNodes_A0, joints_A0,
    List.length_cons, List.length_nil]
  rw [show List.range 1 = [0] by rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [show ([A 1 (m+1)] : List Trans.Recal.PS).getD 0 [] = A 1 (m+1) from rfl,
      show ([1, ((m+2:Nat):Int)] : List Int).getD 0 0 = 1 from rfl,
      show ([0] : List Int).getD 0 0 = 0 from rfl]
  rw [show Trans.Recal.gp1 (A 1 (m+1)) 0 = 0 from gp1_A 1 (m+1) 0 (by omega) (by omega)]
  simp only [show ((0 : Int) == 0) = true from rfl, if_true]
  change Trans.Recal.jjSeq 0 0 ++ Trans.Recal.incrFirst
    (Trans.Recal.red (f+1) (((0:Int)+1, (-1:Int)+1) :: Trans.Recal.derp (A 1 (m+1))))
      ((0:Int)-(-1:Int)) = _
  rw [show (((0:Int)+1, (-1:Int)+1) :: Trans.Recal.derp (A 1 (m+1))) = A 1 (m+1) from by
        simpa using cons_derp_A 1 m,
      show ((0:Int)-(-1:Int)) = 1 by omega]
  rw [red_A1]
  rfl

theorem red_A0 : ∀ (m f : Nat),
    Trans.Recal.red (2*m+f) (A 0 m) = A 0 m
  | 0, f => by cases f <;> rfl
  | 1, f => by cases f <;> rfl
  | m+2, f => by
    rw [show 2*(m+2)+f = (2*(m+1)+f)+2 by omega, red_A0_step,
      red_A0 (m+1) f]
    rw [show Trans.Recal.incrFirst (A 0 (m+1)) (1:Int) = A 1 (m+1) from by
      simpa using incrFirst_A 0 1 (m+1)]
    rw [show A 0 (m+2) = ((0:Int),(0:Int)) :: A 1 (m+1) from by
      rw [show m+2=(m+1)+1 by omega, A_succ]
      simp]

theorem length_C (a m : Nat) : (C a m).length = m+1 := by
  simp [C, length_A]

theorem lenI_C (a m : Nat) : Trans.Recal.lenI (C a m) = (m:Int)+1 := by
  unfold Trans.Recal.lenI
  rw [length_C]
  omega

theorem gp0_C_zero (a m : Nat) : Trans.Recal.gp0 (C a m) 0 = 0 := rfl
theorem gp1_C_zero (a m : Nat) : Trans.Recal.gp1 (C a m) 0 = 0 := rfl

theorem gp0_C_pos (a m k : Nat) (hk : k < m) :
    Trans.Recal.gp0 (C a m) ((k+1:Nat):Int) = (a:Int)+(k:Int) := by
  show (if ((k+1:Nat):Int) < 0 then 0
    else ((C a m).getD ((k+1:Nat):Int).toNat (0,0)).1) = _
  rw [if_neg (by omega)]
  show ((A a m).getD k (0,0)).1 = _
  rw [getD_A a m k hk]
  push_cast
  omega

theorem gp1_C_pos (a m k : Nat) (hk : k < m) :
    Trans.Recal.gp1 (C a m) ((k+1:Nat):Int) = 0 := by
  show (if ((k+1:Nat):Int) < 0 then 0
    else ((C a m).getD ((k+1:Nat):Int).toNat (0,0)).2) = 0
  rw [if_neg (by omega)]
  show ((A a m).getD k (0,0)).2 = 0
  rw [getD_A a m k hk]

theorem fpar0_C_zero (a m : Nat) : Trans.Recal.fpar0 (C a m) 0 0 = -1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_C]; omega), length_C]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_pos (by omega)]

theorem fpar_C_zero (a m : Nat) : Trans.Recal.fpar (C a m) 0 0 0 = -1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_C]; omega), if_pos (by rfl)]
  have h := fpar0_C_zero a m
  unfold Trans.Recal.fpar0 at h
  rw [if_neg (by rw [lenI_C]; omega)] at h
  exact h

theorem fpar_C (a m k : Nat) (ha : 1 ≤ a) (hk0 : 0 < k) (hk : k < m+1) :
    Trans.Recal.fpar (C a m) 0 (k:Int) 0 = ((k-1:Nat):Int) := by
  show (if (k:Int) < 0 ∨ (k:Int) ≥ Trans.Recal.lenI (C a m) then -1
    else if (0:Nat) == 0 then
      Trans.Recal.fpar0Aux ((C a m).length+1) (C a m)
        (Trans.Recal.gp0 (C a m) (k:Int)) ((k:Int)-1) 0
    else _) = _
  rw [if_neg (by rw [lenI_C]; omega)]
  simp only [show ((0:Nat)==0)=true from rfl, if_true, length_C]
  obtain ⟨q, rfl⟩ : ∃ q : Nat, k = q+1 := ⟨k-1, by omega⟩
  rw [gp0_C_pos a m q (by omega)]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega)]
  cases q with
  | zero =>
    rw [show (((0+1:Nat):Int)-1) = 0 by omega, gp0_C_zero,
      if_pos (by push_cast; omega)]
    omega
  | succ q =>
    rw [show ((q+1+1:Nat):Int)-1 = ((q+1:Nat):Int) by omega,
      gp0_C_pos a m q (by omega), if_pos (by push_cast; omega)]
    omega

theorem fpar1_C_one (a m : Nat) (ha : 1 ≤ a) (hm : 1 ≤ m) :
    Trans.Recal.fpar (C a m) 1 1 0 = -1 := by
  show (if (1:Int)<0 ∨ (1:Int)≥Trans.Recal.lenI (C a m) then -1
    else if (1:Nat)==0 then _ else
      Trans.Recal.fpar1Aux ((C a m).length+1) (C a m)
        (Trans.Recal.gp1 (C a m) 1) 1 0) = -1
  rw [if_neg (by rw [lenI_C]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl, Bool.false_eq_true, if_false]
  rw [show Trans.Recal.gp1 (C a m) 1 = 0 from by
        simpa using gp1_C_pos a m 0 (by omega), length_C]
  simp only [Trans.Recal.fpar1Aux]
  rw [show Trans.Recal.fpar0 (C a m) 1 0 = 0 from by
        have h := fpar_C a m 1 ha (by omega) (by omega)
        simpa using h,
      if_neg (by omega), gp1_C_zero, if_neg (by omega)]
  cases m with
  | zero => omega
  | succ p =>
    simp only [Trans.Recal.fpar1Aux]
    rw [fpar0_C_zero, if_pos (by omega)]

theorem isParentP_C_one (a m : Nat) (ha : 1 ≤ a) (hm : 1 ≤ m) :
    Trans.Recal.isParentP (C a m) 1 1 0 = false := by
  unfold Trans.Recal.isParentP
  rw [fpar1_C_one a m ha hm, lenI_C]
  simp

theorem trMax_C (a m : Nat) (ha : 1 ≤ a) : Trans.Recal.trMax (C a m) = 0 := by
  show Trans.Recal.trMaxAux ((C a m).length+1) (C a m) 0 = 0
  rw [length_C]
  simp only [Trans.Recal.trMaxAux]
  rw [if_neg (by rw [lenI_C]; omega)]
  cases m with
  | zero => rw [if_pos (by rfl)]
  | succ p =>
    rw [show Trans.Recal.isParentP (C a (p+1)) 1 (0+1) 0 = false from by
      simpa using isParentP_C_one a (p+1) ha (by omega), if_pos (by rfl)]

theorem isAncAux_C (a m k : Nat) (ha : 1 ≤ a) : ∀ f : Nat,
    k < m+1 → k < f → Trans.Recal.isAncAux f (C a m) 0 (k:Int) 0 = true := by
  refine Nat.strongRecOn (motive := fun k => ∀ f : Nat,
    k < m+1 → k < f → Trans.Recal.isAncAux f (C a m) 0 (k:Int) 0 = true) k ?_
  intro k ih f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0 : k=0
    · subst k; rw [if_pos (by rfl)]
    · rw [show ((0:Int)==(k:Int))=false from beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true, if_false]
      rw [fpar_C a m k ha (by omega) hkm]
      rw [show (((k-1:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true, if_false]
      exact ih (k-1) (by omega) f (by omega) (by omega)

theorem isAnc_C_last (a m : Nat) (ha : 1 ≤ a) :
    Trans.Recal.isAnc (C a m) 0 (m:Int) 0 = true := by
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_C]; omega), length_C]
  exact isAncAux_C a m m ha (m+2) (by omega) (by omega)

theorem isPrincipalP_C_succ (a m : Nat) (ha : 1 ≤ a) :
    Trans.Recal.isPrincipalP (C a (m+1)) = true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (C a (m+1)) = false from by
        unfold Trans.Recal.isZeroP
        rw [length_C]
        simp,
      lenI_C,
      show ((m+1:Nat):Int)+1-1 = ((m+1:Nat):Int) by omega,
      isAnc_C_last a (m+1) ha]
  rfl

theorem brF_C_succ (a m : Nat) (ha : 1 ≤ a) :
    Trans.Recal.brF (C a (m+1)) = [A a (m+1)] := by
  unfold Trans.Recal.brF
  rw [trMax_C a (m+1) ha]
  show Trans.Recal.ppair ((C a (m+1)).drop 1) = _
  show Trans.Recal.ppair (A a (m+1)) = _
  exact ppair_A a (m+1) (by omega)

theorem firstNodes_C_succ (a m : Nat) (ha : 1 ≤ a) :
    Trans.Recal.firstNodes (C a (m+1)) = [1, ((m+2:Nat):Int)] := by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [brF_C_succ a m ha, trMax_C a (m+1) ha]
  simp [length_A]
  omega

theorem joints_C_succ (a m : Nat) (ha : 1 ≤ a) :
    Trans.Recal.joints (C a (m+1)) = [0] := by
  unfold Trans.Recal.joints
  rw [firstNodes_C_succ a m ha]
  change [Trans.Recal.fpar (C a (m+1)) 0 1 0] = [0]
  rw [show Trans.Recal.fpar (C a (m+1)) 0 1 0 = 0 from by
    have h := fpar_C a (m+1) 1 ha (by omega) (by omega)
    simpa using h]

theorem incrFirst_C (a d m : Nat) :
    Trans.Recal.incrFirst (C a m) (d:Int) =
      ((((d:Nat):Int),(0:Int))) :: A (a+d) m := by
  show (((0:Int)+(d:Int), (0:Int))) :: Trans.Recal.incrFirst (A a m) (d:Int) = _
  rw [show Trans.Recal.incrFirst (A a m) (d:Int) = A (a+d) m from by
    simpa using incrFirst_A a d m]
  simp

theorem incrFirst_C_neg (a d m : Nat) :
    Trans.Recal.incrFirst
      (((((d:Nat):Int),(0:Int))) :: A (a+d) m) (-((d:Nat):Int)) = C a m := by
  unfold Trans.Recal.incrFirst C A
  rw [List.map_cons, List.map_map]
  congr 1
  · apply Prod.ext
    · simp
      omega
    · simp
  · apply List.map_congr_left
    intro k _
    apply Prod.ext <;> simp
    push_cast
    omega

theorem fpar_shift_C (a d m k : Nat) (ha : 1 ≤ a) (hk0 : 0 < k) (hk : k < m+1) :
    Trans.Recal.fpar (Trans.Recal.incrFirst (C a m) (d:Int)) 0 (k:Int) 0 =
      ((k-1:Nat):Int) := by
  rw [Evidence.Cert.fpar_row0_incrFirst (C a m) (d:Int) (k:Int) 0
    (by omega) (by omega) (by rw [lenI_C]; omega)]
  exact fpar_C a m k ha hk0 hk

theorem isAncAux_shift_C (a d m k : Nat) (ha : 1 ≤ a) : ∀ f : Nat,
    k < m+1 → k < f →
      Trans.Recal.isAncAux f (Trans.Recal.incrFirst (C a m) (d:Int)) 0 (k:Int) 0 = true := by
  refine Nat.strongRecOn (motive := fun k => ∀ f : Nat, k < m+1 → k < f →
    Trans.Recal.isAncAux f (Trans.Recal.incrFirst (C a m) (d:Int)) 0 (k:Int) 0 = true) k ?_
  intro k ih f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0 : k=0
    · subst k; rw [if_pos (by rfl)]
    · rw [show ((0:Int)==(k:Int))=false from beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true, if_false]
      rw [fpar_shift_C a d m k ha (by omega) hkm]
      rw [show (((k-1:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true, if_false]
      exact ih (k-1) (by omega) f (by omega) (by omega)

theorem isAnc_shift_C_last (a d m : Nat) (ha : 1 ≤ a) :
    Trans.Recal.isAnc (Trans.Recal.incrFirst (C a m) (d:Int)) 0 (m:Int) 0 = true := by
  unfold Trans.Recal.isAnc
  rw [if_neg (by
    show ¬((0:Int)<0 ∨ (0:Int)≥Trans.Recal.lenI (Trans.Recal.incrFirst (C a m) (d:Int)))
    simp [Trans.Recal.lenI, Trans.Recal.incrFirst, length_C])]
  rw [show (Trans.Recal.incrFirst (C a m) (d:Int)).length = m+1 by
    simp [Trans.Recal.incrFirst, length_C]]
  exact isAncAux_shift_C a d m m ha (m+2) (by omega) (by omega)

theorem isPrincipalP_shift_C_succ (a d m : Nat) (ha : 1 ≤ a) :
    Trans.Recal.isPrincipalP (Trans.Recal.incrFirst (C a (m+1)) (d:Int)) = true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (Trans.Recal.incrFirst (C a (m+1)) (d:Int)) = false from by
        unfold Trans.Recal.isZeroP
        simp [Trans.Recal.incrFirst, length_C],
      show Trans.Recal.lenI (Trans.Recal.incrFirst (C a (m+1)) (d:Int))-1 =
          ((m+1:Nat):Int) by
        simp [Trans.Recal.lenI, Trans.Recal.incrFirst, length_C],
      isAnc_shift_C_last a d (m+1) ha]
  rfl

theorem red_C_zero (a f : Nat) : Trans.Recal.red f (C a 0) = C a 0 := by
  simpa [C, A] using red_A0_one f

theorem red_shift_C (a d m f : Nat) (ha : 1 ≤ a) (hd : 1 ≤ d) :
    Trans.Recal.red (f+1) (((((d:Nat):Int),(0:Int))) :: A (a+d) m) =
      Trans.Recal.red f (C a m) := by
  cases m with
  | zero =>
    rw [show (((((d:Nat):Int),(0:Int))) :: A (a+d) 0) =
        [((((d:Nat):Int),(0:Int)))] from rfl]
    conv => lhs; rw [Trans.Recal.red]
    rw [show Trans.Recal.isZeroP [((((d:Nat):Int),(0:Int)))] = true from by rfl]
    simp only [if_true]
    exact (red_C_zero a f).symm
  | succ p =>
    let P : Trans.Recal.PS := (((((d:Nat):Int),(0:Int))) :: A (a+d) (p+1))
    conv => lhs; rw [Trans.Recal.red]
    rw [show Trans.Recal.isZeroP P = false from by
          unfold Trans.Recal.isZeroP P
          simp [length_A],
        show Trans.Recal.isPrincipalP P = true from by
          rw [show P = Trans.Recal.incrFirst (C a (p+1)) (d:Int) from by
            rw [incrFirst_C]]
          exact isPrincipalP_shift_C_succ a d p ha]
    simp only [Bool.false_eq_true, if_false, if_true]
    rw [show (Trans.Recal.gp0 P 0 == 0 && Trans.Recal.gp1 P 0 == 0) = false from by
          show (((d:Nat):Int)==0 && ((0:Int)==0)) = false
          rw [show (((d:Nat):Int)==0) = false from
            beq_eq_false_iff_ne.mpr (by omega)]
          rfl,
        show (Trans.Recal.gp1 P 0 == 0) = true from by rfl]
    simp only [Bool.false_eq_true, if_false, if_true]
    rw [show -(Trans.Recal.gp0 P 0) = (-((d:Nat):Int)) from by rfl,
      incrFirst_C_neg]

theorem red_C_step (a m f : Nat) (ha : 1 ≤ a) :
    Trans.Recal.red (f+2) (C a (m+1)) =
      ((0:Int),(0:Int)) :: Trans.Recal.incrFirst (Trans.Recal.red f (C a m)) 1 := by
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (C a (m+1)) = false from by
        unfold Trans.Recal.isZeroP
        rw [length_C]
        simp,
      isPrincipalP_C_succ a m ha]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [show (Trans.Recal.gp0 (C a (m+1)) 0 == 0
      && Trans.Recal.gp1 (C a (m+1)) 0 == 0) = true from by rfl]
  simp only [if_true]
  rw [trMax_C a (m+1) ha, lenI_C]
  rw [show ((0:Int) == ((m+1:Nat):Int)+1-1) = false from
    beq_eq_false_iff_ne.mpr (by omega)]
  simp only [Bool.false_eq_true, if_false]
  rw [brF_C_succ a m ha, firstNodes_C_succ a m ha, joints_C_succ a m ha]
  simp only [List.length_cons, List.length_nil]
  rw [show List.range 1 = [0] by rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [show ([A a (m+1)] : List Trans.Recal.PS).getD 0 [] = A a (m+1) from rfl,
      show ([1, ((m+2:Nat):Int)] : List Int).getD 0 0 = 1 from rfl,
      show ([0] : List Int).getD 0 0 = 0 from rfl]
  rw [show Trans.Recal.gp1 (A a (m+1)) 0 = 0 from
    gp1_A a (m+1) 0 (by omega) (by omega)]
  simp only [show ((0 : Int) == 0) = true from rfl, if_true]
  change Trans.Recal.jjSeq 0 0 ++ Trans.Recal.incrFirst
    (Trans.Recal.red (f+1)
      (((1:Int),(0:Int)) :: Trans.Recal.derp (A a (m+1)))) 1 = _
  rw [derp_A]
  rw [show (((1:Int),(0:Int)) :: A (a+1) m) =
      (((((1:Nat):Int),(0:Int))) :: A (a+1) m) from rfl,
    red_shift_C a 1 m f ha (by omega)]
  rfl

theorem red_C (a : Nat) (ha : 1 ≤ a) : ∀ (m f : Nat),
    Trans.Recal.red (2*m+f) (C a m) = A 0 (m+1)
  | 0, f => by
    rw [red_C_zero]
    rfl
  | m+1, f => by
    rw [show 2*(m+1)+f = (2*m+f)+2 by omega, red_C_step a m (2*m+f) ha,
      red_C a ha m f]
    rw [show Trans.Recal.incrFirst (A 0 (m+1)) (1:Int) = A 1 (m+1) from by
      simpa using incrFirst_A 0 1 (m+1)]
    rw [show A 0 (m+2) = ((0:Int),(0:Int)) :: A 1 (m+1) from by
      rw [show m+2=(m+1)+1 by omega, A_succ]
      simp]

theorem length_B (m : Nat) : (B m).length = m+2 := by
  simp [B, length_A]

theorem lenI_B (m : Nat) : Trans.Recal.lenI (B m) = (m:Int)+2 := by
  unfold Trans.Recal.lenI
  rw [length_B]
  omega

theorem gp0_B (m k : Nat) (hk : k < m+2) :
    Trans.Recal.gp0 (B m) (k:Int) = (k:Int) := by
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ q =>
      show (if ((q+2:Nat):Int)<0 then 0 else ((B m).getD (q+2) (0,0)).1) = _
      rw [if_neg (by omega)]
      show ((A 2 m).getD q (0,0)).1 = _
      rw [getD_A 2 m q (by omega)]

theorem fpar0_B_one (m : Nat) : Trans.Recal.fpar0 (B m) 1 0 = 0 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_B]; omega), length_B]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega), show (1:Int)-1=0 by omega,
    show Trans.Recal.gp0 (B m) 1 = 1 from gp0_B m 1 (by omega),
    show Trans.Recal.gp0 (B m) 0 = 0 from gp0_B m 0 (by omega), if_pos (by omega)]

theorem fpar0_B_two (m : Nat) (hm : 1 ≤ m) : Trans.Recal.fpar0 (B m) 2 1 = 1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_B]; omega), length_B]
  rw [show Trans.Recal.gp0 (B m) 2 = 2 from gp0_B m 2 (by omega)]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega), show (2:Int)-1=1 by omega,
    show Trans.Recal.gp0 (B m) 1 = 1 from gp0_B m 1 (by omega),
    if_pos (by omega)]

theorem fpar0_B_one_lb (m : Nat) : Trans.Recal.fpar0 (B m) 1 1 = -1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_B]; omega), length_B]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_pos (by omega)]

theorem fpar1_B_one (m : Nat) : Trans.Recal.fpar (B m) 1 1 0 = 0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_B]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl, Bool.false_eq_true, if_false]
  rw [length_B]
  show (let j1 := Trans.Recal.fpar0 (B m) 1 0
    if j1 < 0 then -1 else if Trans.Recal.gp1 (B m) j1 < 1 then j1
    else Trans.Recal.fpar1Aux (m+1) (B m) 1 j1 0) = 0
  rw [fpar0_B_one]
  rfl

theorem fpar1_B_two (m : Nat) (hm : 1 ≤ m) :
    Trans.Recal.fpar (B m) 1 2 1 = -1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_B]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl, Bool.false_eq_true, if_false]
  rw [show Trans.Recal.gp1 (B m) 2 = 0 from by
        cases m with
        | zero => omega
        | succ p =>
          show (if (2:Int)<0 then 0 else ((B (p+1)).getD 2 (0,0)).2) = 0
          rw [if_neg (by omega)]
          show ((A 2 (p+1)).getD 0 (0,0)).2 = 0
          rw [getD_A 2 (p+1) 0 (by omega)],
      length_B]
  simp only [Trans.Recal.fpar1Aux]
  show (let j1 := Trans.Recal.fpar0 (B m) 2 1
    if j1 < 1 then -1 else if Trans.Recal.gp1 (B m) j1 < 0 then j1
    else Trans.Recal.fpar1Aux (m+2) (B m) 0 j1 1) = -1
  rw [fpar0_B_two m hm]
  simp only [show ¬((1:Int)<1) by omega, if_false]
  rw [show Trans.Recal.gp1 (B m) 1 = 1 from rfl, if_neg (by omega)]
  cases m with
  | zero => omega
  | succ p =>
    simp only [Trans.Recal.fpar1Aux]
    rw [fpar0_B_one_lb, if_pos (by omega)]

theorem isParentP_B_one (m : Nat) : Trans.Recal.isParentP (B m) 1 1 0 = true := by
  unfold Trans.Recal.isParentP
  rw [fpar1_B_one, lenI_B]
  rw [show decide ((0:Int)<(m:Int)+2)=true from decide_eq_true (by omega)]
  rfl

theorem isParentP_B_two (m : Nat) (hm : 1 ≤ m) :
    Trans.Recal.isParentP (B m) 1 2 1 = false := by
  unfold Trans.Recal.isParentP
  rw [fpar1_B_two m hm]
  simp

theorem trMax_B (m : Nat) : Trans.Recal.trMax (B m) = 1 := by
  -- This prefix has the same two row-one decisions as `G1.LG`; the tail is row zero.
  show Trans.Recal.trMaxAux ((B m).length+1) (B m) 0 = 1
  rw [length_B]
  simp only [Trans.Recal.trMaxAux]
  rw [if_neg (by rw [lenI_B]; omega)]
  rw [show Trans.Recal.isParentP (B m) 1 (0+1) 0 = true from by
        simpa using isParentP_B_one m]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  rw [if_neg (by rw [lenI_B]; omega)]
  cases m with
  | zero => rw [if_pos (by rfl)]; omega
  | succ p =>
    rw [show Trans.Recal.isParentP (B (p+1)) 1 (0+1+1) (0+1) = false from by
      simpa using isParentP_B_two (p+1) (by omega),
      if_pos (by rfl)]
    omega

theorem brF_B_succ (m : Nat) : Trans.Recal.brF (B (m+1)) = [A 2 (m+1)] := by
  unfold Trans.Recal.brF
  rw [trMax_B]
  show Trans.Recal.ppair (A 2 (m+1)) = [A 2 (m+1)]
  exact ppair_A 2 (m+1) (by omega)

theorem firstNodes_B_succ (m : Nat) :
    Trans.Recal.firstNodes (B (m+1)) = [2, ((m+3:Nat):Int)] := by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [brF_B_succ, trMax_B]
  simp [length_A]
  omega

theorem fpar_B (m k : Nat) (hk0 : 0 < k) (hk : k < m+2) :
    Trans.Recal.fpar (B m) 0 (k:Int) 0 = ((k-1:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_B]; omega), if_pos (by rfl), gp0_B m k hk, length_B]
  obtain ⟨q, rfl⟩ : ∃ q : Nat, k=q+1 := ⟨k-1, by omega⟩
  simp only [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega), show ((q+1:Nat):Int)-1 = (q:Int) by omega,
    gp0_B m q (by omega), if_pos (by omega)]
  omega

theorem joints_B_succ (m : Nat) : Trans.Recal.joints (B (m+1)) = [1] := by
  unfold Trans.Recal.joints
  rw [firstNodes_B_succ]
  change [Trans.Recal.fpar (B (m+1)) 0 2 0] = [1]
  rw [show Trans.Recal.fpar (B (m+1)) 0 2 0 = 1 from by
    have h := fpar_B (m+1) 2 (by omega) (by omega)
    simpa using h]

theorem isAncAux_B (m k : Nat) : ∀ f : Nat, k < m+2 → k < f →
    Trans.Recal.isAncAux f (B m) 0 (k:Int) 0 = true := by
  refine Nat.strongRecOn (motive := fun k => ∀ f : Nat, k < m+2 → k < f →
    Trans.Recal.isAncAux f (B m) 0 (k:Int) 0 = true) k ?_
  intro k ih f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0 : k=0
    · subst k; rw [if_pos (by rfl)]
    · rw [show ((0:Int)==(k:Int))=false from beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true, if_false]
      rw [fpar_B m k (by omega) hkm]
      rw [show (((k-1:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true, if_false]
      exact ih (k-1) (by omega) f (by omega) (by omega)

theorem isPrincipalP_B (m : Nat) : Trans.Recal.isPrincipalP (B m) = true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (B m) = false from by
        unfold Trans.Recal.isZeroP
        rw [length_B]
        simp,
      lenI_B]
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_B]; omega), length_B]
  simp only [Bool.not_false, Bool.true_and]
  rw [show (m:Int)+2-1=((m+1:Nat):Int) by omega]
  exact isAncAux_B m (m+1) (m+3) (by omega) (by omega)

theorem red_B_zero (f : Nat) : Trans.Recal.red f (B 0) = B 0 := by
  cases f with
  | zero => rfl
  | succ f =>
    rw [Trans.Recal.red]
    rfl

theorem red_B_step (f m : Nat) :
    Trans.Recal.red (f+2) (B (m+1)) =
      ((0:Int),(0:Int)) :: ((1:Int),(1:Int)) ::
        Trans.Recal.incrFirst (Trans.Recal.red f (C 1 m)) 2 := by
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (B (m+1)) = false from by
        unfold Trans.Recal.isZeroP
        rw [length_B]
        simp,
      isPrincipalP_B]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [show (Trans.Recal.gp0 (B (m+1)) 0 == 0
      && Trans.Recal.gp1 (B (m+1)) 0 == 0) = true from by rfl]
  simp only [if_true]
  rw [trMax_B, lenI_B]
  rw [show ((1:Int)==((m+1:Nat):Int)+2-1)=false from
    beq_eq_false_iff_ne.mpr (by omega)]
  simp only [Bool.false_eq_true, if_false]
  rw [brF_B_succ, firstNodes_B_succ, joints_B_succ]
  simp only [List.length_cons, List.length_nil]
  rw [show List.range 1 = [0] by rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [show ([A 2 (m+1)] : List Trans.Recal.PS).getD 0 [] = A 2 (m+1) from rfl,
      show ([2, ((m+3:Nat):Int)] : List Int).getD 0 0 = 2 from rfl,
      show ([1] : List Int).getD 0 0 = 1 from rfl]
  rw [show Trans.Recal.gp1 (A 2 (m+1)) 0 = 0 from
    gp1_A 2 (m+1) 0 (by omega) (by omega)]
  simp only [show ((0 : Int) == 0) = true from rfl, if_true]
  change Trans.Recal.jjSeq 0 1 ++ Trans.Recal.incrFirst
    (Trans.Recal.red (f+1) (((2:Int),(0:Int)) :: Trans.Recal.derp (A 2 (m+1)))) 2 = _
  rw [derp_A]
  rw [show (((2:Int),(0:Int)) :: A 3 m) =
      (((((2:Nat):Int),(0:Int))) :: A (1+2) m) from by simp,
    red_shift_C 1 2 m f (by omega) (by omega)]
  rfl

theorem red_B : ∀ (m f : Nat), Trans.Recal.red (2*m+f) (B m) = B m
  | 0, f => by simpa using red_B_zero f
  | m+1, f => by
    rw [show 2*(m+1)+f=(2*m+f)+2 by omega, red_B_step,
      red_C 1 (by omega) m f]
    rw [show Trans.Recal.incrFirst (A 0 (m+1)) (2:Int) = A 2 (m+1) from by
      simpa using incrFirst_A 0 2 (m+1)]
    rfl

theorem length_E (a m : Nat) : (E a m).length = m+1 := by
  simp [E, length_A]

theorem lenI_E (a m : Nat) : Trans.Recal.lenI (E a m) = (m:Int)+1 := by
  unfold Trans.Recal.lenI
  rw [length_E]
  omega

theorem gp0_E (a m k : Nat) (hk : k < m+1) :
    Trans.Recal.gp0 (E a m) (k:Int) = (a:Int)+(k:Int) := by
  cases k with
  | zero => simp [E, Trans.Recal.gp0]
  | succ q =>
    show (if ((q+1:Nat):Int)<0 then 0 else ((E a m).getD (q+1) (0,0)).1) = _
    rw [if_neg (by omega)]
    show ((A (a+1) m).getD q (0,0)).1 = _
    rw [getD_A (a+1) m q (by omega)]
    push_cast
    omega

theorem fpar_E (a m k : Nat) (hk0 : 0 < k) (hk : k < m+1) :
    Trans.Recal.fpar (E a m) 0 (k:Int) 0 = ((k-1:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_E]; omega), if_pos (by rfl), gp0_E a m k hk, length_E]
  obtain ⟨q,rfl⟩ : ∃ q : Nat, k=q+1 := ⟨k-1, by omega⟩
  simp only [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega), show ((q+1:Nat):Int)-1=(q:Int) by omega,
    gp0_E a m q (by omega), if_pos (by omega)]
  omega

theorem isAncAux_E (a m k : Nat) : ∀ f : Nat, k < m+1 → k < f →
    Trans.Recal.isAncAux f (E a m) 0 (k:Int) 0 = true := by
  refine Nat.strongRecOn (motive := fun k => ∀ f : Nat, k < m+1 → k < f →
    Trans.Recal.isAncAux f (E a m) 0 (k:Int) 0 = true) k ?_
  intro k ih f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0 : k=0
    · subst k; rw [if_pos (by rfl)]
    · rw [show ((0:Int)==(k:Int))=false from beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true, if_false]
      rw [fpar_E a m k (by omega) hkm]
      rw [show (((k-1:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true, if_false]
      exact ih (k-1) (by omega) f (by omega) (by omega)

theorem isPrincipalP_E (a m : Nat) : Trans.Recal.isPrincipalP (E a m) = true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (E a m) = false from by
        unfold Trans.Recal.isZeroP
        rw [length_E]
        cases m <;> rfl,
      lenI_E]
  simp only [Bool.not_false, Bool.true_and]
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_E]; omega), length_E,
      show (m:Int)+1-1=(m:Int) by omega]
  exact isAncAux_E a m m (m+2) (by omega) (by omega)

theorem fpar_E_zero (a m : Nat) : Trans.Recal.fpar (E a m) 0 0 0 = -1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_E]; omega), if_pos (by rfl), length_E]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_pos (by omega)]

theorem fAncAux_E_last (a m k : Nat) : ∀ (f : Nat) (acc : List Int),
    k < m+1 → k < f → acc.getLast?=some (k:Int) →
    (Trans.Recal.fAncAux f (E a m) 0 (k:Int) 0 acc).getLast?=some 0 := by
  refine Nat.strongRecOn (motive := fun k => ∀ (f:Nat) (acc:List Int),
    k<m+1 → k<f → acc.getLast?=some (k:Int) →
    (Trans.Recal.fAncAux f (E a m) 0 (k:Int) 0 acc).getLast?=some 0) k ?_
  intro k ih f acc hkm hkf hlast
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.fAncAux]
    by_cases hk0:k=0
    · subst k
      rw [show Trans.Recal.fpar (E a m) 0 ((0:Nat):Int) 0 = -1 from by
        simpa using fpar_E_zero a m, if_neg (by omega)]
      exact hlast
    · rw [fpar_E a m k (by omega) hkm, if_pos (by omega)]
      exact ih (k-1) (by omega) f (acc++[((k-1:Nat):Int)])
        (by omega) (by omega) (by simp)

theorem fAnc_E_last (a m : Nat) :
    (Trans.Recal.fAnc (E a m) 0 (m:Int) 0).getLast?=some 0 := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by rw [lenI_E]; omega), length_E]
  exact fAncAux_E_last a m m (m+2) [(m:Int)] (by omega) (by omega) (by simp)

theorem slice_E_full (a m : Nat) :
    Trans.Recal.slice (E a m) 0 ((m+1:Nat):Int)=E a m := by
  unfold Trans.Recal.slice
  simp only [Int.toNat_zero, List.drop_zero]
  rw [show (((m+1:Nat):Int)-0).toNat=m+1 by omega]
  simpa only [length_E] using (List.take_length : (E a m).take (E a m).length=E a m)

theorem ppair_E (a m : Nat) : Trans.Recal.ppair (E a m)=[E a m] := by
  unfold Trans.Recal.ppair
  rw [length_E, lenI_E]
  simp only [Trans.Recal.ppairAux]
  rw [if_neg (by omega), show (m:Int)+1-1=(m:Int) by omega, fAnc_E_last]
  simp only [Option.getD_some]
  rw [show (m:Int)+1=((m+1:Nat):Int) by omega, slice_E_full]
  rw [if_pos (by omega)]

theorem length_S (m : Nat) : (S m).length = m+2 := by
  simp [S, length_A]

theorem lenI_S (m : Nat) : Trans.Recal.lenI (S m) = (m:Int)+2 := by
  unfold Trans.Recal.lenI
  rw [length_S]
  omega

theorem gp0_S (m k : Nat) (hk : k < m+2) :
    Trans.Recal.gp0 (S m) (k:Int) = if k=0 then 0 else (k:Int)+2 := by
  unfold S
  cases k with
  | zero => rfl
  | succ q =>
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    show (if ((q+1:Nat):Int)<0 then 0 else ((S m).getD (q+1) (0,0)).1) = _
    rw [if_neg (by omega)]
    rw [show S m = (0,0)::(3,1)::A 4 m from rfl]
    cases q with
    | zero => rfl
    | succ p =>
      show ((A 4 m).getD p (0,0)).1 = _
      rw [getD_A 4 m p (by omega)]
      push_cast
      omega

theorem fpar_S (m k : Nat) (hk0 : 0 < k) (hk : k < m+2) :
    Trans.Recal.fpar (S m) 0 (k:Int) 0 = ((k-1:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_S]; omega), if_pos (by rfl), gp0_S m k hk, length_S]
  rw [if_neg (by omega)]
  obtain ⟨q,rfl⟩ : ∃ q : Nat, k=q+1 := ⟨k-1, by omega⟩
  simp only [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega), show ((q+1:Nat):Int)-1=(q:Int) by omega,
    gp0_S m q (by omega)]
  cases q with
  | zero => rw [if_pos (by omega)]
  | succ q =>
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    rw [if_pos (by push_cast; omega)]
    omega

theorem fpar0_S_one (m : Nat) : Trans.Recal.fpar0 (S m) 1 0 = 0 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_S]; omega), length_S]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega), show (1:Int)-1=0 by omega,
      show Trans.Recal.gp0 (S m) 1 = 3 from by simpa using gp0_S m 1 (by omega),
      show Trans.Recal.gp0 (S m) 0 = 0 from by simpa using gp0_S m 0 (by omega),
      if_pos (by omega)]

theorem fpar0_S_two (m : Nat) (hm : 1 ≤ m) : Trans.Recal.fpar0 (S m) 2 1 = 1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_S]; omega), length_S]
  rw [show Trans.Recal.gp0 (S m) 2 = 4 from by simpa using gp0_S m 2 (by omega)]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega), show (2:Int)-1=1 by omega,
      show Trans.Recal.gp0 (S m) 1 = 3 from by simpa using gp0_S m 1 (by omega),
      if_pos (by omega)]

theorem fpar0_S_one_lb (m : Nat) : Trans.Recal.fpar0 (S m) 1 1 = -1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_S]; omega), length_S]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_pos (by omega)]

theorem fpar1_S_one (m : Nat) : Trans.Recal.fpar (S m) 1 1 0 = 0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_S]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl, Bool.false_eq_true, if_false]
  rw [length_S]
  show (let j1 := Trans.Recal.fpar0 (S m) 1 0
    if j1 < 0 then -1 else if Trans.Recal.gp1 (S m) j1 < 1 then j1
    else Trans.Recal.fpar1Aux (m+1) (S m) 1 j1 0) = 0
  rw [fpar0_S_one]
  rfl

theorem fpar1_S_two (m : Nat) (hm : 1 ≤ m) :
    Trans.Recal.fpar (S m) 1 2 1 = -1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_S]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl, Bool.false_eq_true, if_false]
  rw [show Trans.Recal.gp1 (S m) 2 = 0 from by
        cases m with
        | zero => omega
        | succ p =>
          show (if (2:Int)<0 then 0 else ((S (p+1)).getD 2 (0,0)).2) = 0
          rw [if_neg (by omega)]
          show ((A 4 (p+1)).getD 0 (0,0)).2 = 0
          rw [getD_A 4 (p+1) 0 (by omega)],
      length_S]
  simp only [Trans.Recal.fpar1Aux]
  show (let j1 := Trans.Recal.fpar0 (S m) 2 1
    if j1 < 1 then -1 else if Trans.Recal.gp1 (S m) j1 < 0 then j1
    else Trans.Recal.fpar1Aux (m+2) (S m) 0 j1 1) = -1
  rw [fpar0_S_two m hm]
  simp only [show ¬((1:Int)<1) by omega, if_false]
  rw [show Trans.Recal.gp1 (S m) 1 = 1 from rfl, if_neg (by omega)]
  cases m with
  | zero => omega
  | succ p =>
    simp only [Trans.Recal.fpar1Aux]
    rw [fpar0_S_one_lb, if_pos (by omega)]

theorem trMax_S (m : Nat) : Trans.Recal.trMax (S m) = 1 := by
  show Trans.Recal.trMaxAux ((S m).length+1) (S m) 0 = 1
  rw [length_S]
  simp only [Trans.Recal.trMaxAux]
  rw [if_neg (by rw [lenI_S]; omega)]
  rw [show Trans.Recal.isParentP (S m) 1 (0+1) 0 = true from by
        unfold Trans.Recal.isParentP
        rw [show Trans.Recal.fpar (S m) 1 (0+1) 0 = 0 from by
              simpa using fpar1_S_one m,
            lenI_S]
        rw [show decide ((0:Int)<(m:Int)+2)=true from decide_eq_true (by omega)]
        rfl]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  rw [if_neg (by rw [lenI_S]; omega)]
  cases m with
  | zero => rw [if_pos (by rfl)]; omega
  | succ p =>
    rw [show Trans.Recal.isParentP (S (p+1)) 1 (0+1+1) (0+1) = false from by
      unfold Trans.Recal.isParentP
      rw [show Trans.Recal.fpar (S (p+1)) 1 (0+1+1) (0+1) = -1 from by
            simpa using fpar1_S_two (p+1) (by omega)]
      simp,
      if_pos (by rfl)]
    omega

theorem isAncAux_S (m k : Nat) : ∀ f : Nat, k < m+2 → k < f →
    Trans.Recal.isAncAux f (S m) 0 (k:Int) 0 = true := by
  refine Nat.strongRecOn (motive := fun k => ∀ f : Nat, k < m+2 → k < f →
    Trans.Recal.isAncAux f (S m) 0 (k:Int) 0 = true) k ?_
  intro k ih f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0 : k=0
    · subst k; rw [if_pos (by rfl)]
    · rw [show ((0:Int)==(k:Int))=false from beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true, if_false]
      rw [fpar_S m k (by omega) hkm]
      rw [show (((k-1:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true, if_false]
      exact ih (k-1) (by omega) f (by omega) (by omega)

theorem isPrincipalP_S (m : Nat) : Trans.Recal.isPrincipalP (S m) = true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (S m) = false from by
        unfold Trans.Recal.isZeroP
        rw [length_S]
        simp,
      lenI_S]
  simp only [Bool.not_false, Bool.true_and]
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_S]; omega), length_S,
      show (m:Int)+2-1=((m+1:Nat):Int) by omega]
  exact isAncAux_S m (m+1) (m+3) (by omega) (by omega)

theorem brF_S_succ (m : Nat) : Trans.Recal.brF (S (m+1)) = [A 4 (m+1)] := by
  unfold Trans.Recal.brF
  rw [trMax_S]
  show Trans.Recal.ppair (A 4 (m+1)) = [A 4 (m+1)]
  exact ppair_A 4 (m+1) (by omega)

theorem firstNodes_S_succ (m : Nat) :
    Trans.Recal.firstNodes (S (m+1)) = [2, ((m+3:Nat):Int)] := by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [brF_S_succ, trMax_S]
  simp [length_A]
  omega

theorem joints_S_succ (m : Nat) : Trans.Recal.joints (S (m+1)) = [1] := by
  unfold Trans.Recal.joints
  rw [firstNodes_S_succ]
  change [Trans.Recal.fpar (S (m+1)) 0 2 0] = [1]
  rw [show Trans.Recal.fpar (S (m+1)) 0 2 0 = 1 from by
    have h := fpar_S (m+1) 2 (by omega) (by omega)
    simpa using h]

theorem red_S_zero (f : Nat) : Trans.Recal.red (f+1) (S 0) = B 0 := by
  rw [Trans.Recal.red]
  rfl

theorem red_S_step (f m : Nat) : Trans.Recal.red (f+2) (S (m+1)) =
    ((0:Int),(0:Int)) :: ((1:Int),(1:Int)) ::
      Trans.Recal.incrFirst (Trans.Recal.red f (C 3 m)) 2 := by
  conv => lhs; rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (S (m+1)) = false from by
        unfold Trans.Recal.isZeroP
        rw [length_S]
        simp,
      isPrincipalP_S]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [show (Trans.Recal.gp0 (S (m+1)) 0 == 0
      && Trans.Recal.gp1 (S (m+1)) 0 == 0) = true from by rfl]
  simp only [if_true]
  rw [trMax_S, lenI_S]
  rw [show ((1:Int)==((m+1:Nat):Int)+2-1)=false from
    beq_eq_false_iff_ne.mpr (by omega)]
  simp only [Bool.false_eq_true, if_false]
  rw [brF_S_succ, firstNodes_S_succ, joints_S_succ]
  simp only [List.length_cons, List.length_nil]
  rw [show List.range 1=[0] by rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [show ([A 4 (m+1)] : List Trans.Recal.PS).getD 0 [] = A 4 (m+1) from rfl,
      show ([2, ((m+3:Nat):Int)] : List Int).getD 0 0 = 2 from rfl,
      show ([1] : List Int).getD 0 0 = 1 from rfl]
  rw [show Trans.Recal.gp1 (A 4 (m+1)) 0 = 0 from
    gp1_A 4 (m+1) 0 (by omega) (by omega)]
  simp only [show ((0 : Int) == 0) = true from rfl, if_true]
  change Trans.Recal.jjSeq 0 1 ++ Trans.Recal.incrFirst
    (Trans.Recal.red (f+1) (((2:Int),(0:Int)) :: Trans.Recal.derp (A 4 (m+1)))) 2 = _
  rw [derp_A]
  rw [show (((2:Int),(0:Int))::A 5 m) =
      (((((2:Nat):Int),(0:Int)))::A (3+2) m) from by simp,
    red_shift_C 3 2 m f (by omega) (by omega)]
  rfl

theorem red_S : ∀ (m f : Nat),
    Trans.Recal.red (2*m+f+1) (S m) = B m
  | 0, f => by simpa using red_S_zero f
  | m+1, f => by
    rw [show 2*(m+1)+f+1=(2*m+f+1)+2 by omega, red_S_step,
      show 2*m+f+1=2*m+(f+1) by omega, red_C 3 (by omega) m (f+1)]
    rw [show Trans.Recal.incrFirst (A 0 (m+1)) (2:Int)=A 2 (m+1) from by
      simpa using incrFirst_A 0 2 (m+1)]
    rfl

theorem red_R (m f : Nat) :
    Trans.Recal.red (2*m+f+2) (R m) = E 1 m := by
  rw [show 2*m+f+2=(2*m+f+1)+1 by omega, Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (R m) = false from by
        show Trans.Recal.isZeroP (E 2 m) = false
        unfold Trans.Recal.isZeroP
        rw [length_E]
        cases m <;> rfl,
      show Trans.Recal.isPrincipalP (R m) = true from by
        exact isPrincipalP_E 2 m]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [show (Trans.Recal.gp0 (R m) 0 == 0 && Trans.Recal.gp1 (R m) 0 == 0) = false from by rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [show (Trans.Recal.gp1 (R m) 0 == 0) = false from by rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [show Trans.Recal.jjSeq 0 (Trans.Recal.gp1 (R m) 0-1)
      ++ Trans.Recal.incrFirst (R m) (Trans.Recal.gp1 (R m) 0) = S m from by
        show [((0:Int),(0:Int))] ++ Trans.Recal.incrFirst (E 2 m) 1 = S m
        rw [show Trans.Recal.incrFirst (E 2 m) (1:Int) = E 3 m from by
          unfold E
          show ((2:Int)+1, (1:Int)) :: Trans.Recal.incrFirst (A 3 m) 1 = _
          rw [show Trans.Recal.incrFirst (A 3 m) (1:Int) = A 4 m from by
            simpa using incrFirst_A 3 1 m]
          simp]
        rfl,
      red_S m f]
  rw [show Trans.Recal.lenI (B m)-1=(m:Int)+1 from by rw [lenI_B]; omega]
  rw [show Trans.Recal.gp1 (R m) 0 = 1 from rfl]
  rw [show Int.toNat (1:Int)=1 by rfl]
  rw [show (B m).drop 1 = E 1 m from by rfl,
      isPrincipalP_E]
  rw [show decide ((1:Int) ≤ (m:Int)+1) = true from
    decide_eq_true (by omega)]
  simp only [Bool.true_and, if_true]
  rw [show Trans.Recal.gp0 (B m) 1 = 1 from gp0_B m 1 (by omega),
      show Trans.Recal.gp1 (B m) 1 = 1 from rfl]
  simp [Trans.Recal.incrFirst]

theorem gp0_L (m k : Nat) (hk : k < m+3) :
    Trans.Recal.gp0 (L m) (k:Int) = (k:Int) := by
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ k =>
      cases k with
      | zero => rfl
      | succ q =>
        show (if ((q+3:Nat):Int)<0 then 0 else ((L m).getD (q+3) (0,0)).1) = _
        rw [if_neg (by omega)]
        show ((A 3 m).getD q (0,0)).1 = _
        rw [getD_A 3 m q (by omega)]

theorem fpar_L (m k : Nat) (hk0 : 0<k) (hk : k<m+3) :
    Trans.Recal.fpar (L m) 0 (k:Int) 0 = ((k-1:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [show Trans.Recal.lenI (L m)=(m:Int)+3 from by
        unfold Trans.Recal.lenI; rw [length_L]; omega]; omega),
      if_pos (by rfl), gp0_L m k hk, length_L]
  obtain ⟨q,rfl⟩ : ∃ q:Nat,k=q+1 := ⟨k-1,by omega⟩
  simp only [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega), show ((q+1:Nat):Int)-1=(q:Int) by omega,
    gp0_L m q (by omega), if_pos (by omega)]
  omega

theorem fpar0_L_one (m:Nat) : Trans.Recal.fpar0 (L m) 1 0=0 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_L]; omega), length_L]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega), show (1:Int)-1=0 by omega,
    show Trans.Recal.gp0 (L m) 1=1 from gp0_L m 1 (by omega),
    show Trans.Recal.gp0 (L m) 0=0 from gp0_L m 0 (by omega), if_pos (by omega)]

theorem fpar0_L_two (m:Nat) : Trans.Recal.fpar0 (L m) 2 1=1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_L]; omega), length_L,
    show Trans.Recal.gp0 (L m) 2=2 from gp0_L m 2 (by omega)]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega), show (2:Int)-1=1 by omega,
    show Trans.Recal.gp0 (L m) 1=1 from gp0_L m 1 (by omega), if_pos (by omega)]

theorem fpar0_L_one_lb (m:Nat) : Trans.Recal.fpar0 (L m) 1 1=-1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_L]; omega), length_L]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_pos (by omega)]

theorem fpar1_L_one (m:Nat) : Trans.Recal.fpar (L m) 1 1 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl, Bool.false_eq_true, if_false]
  rw [length_L]
  show (let j1:=Trans.Recal.fpar0 (L m) 1 0
    if j1<0 then -1 else if Trans.Recal.gp1 (L m) j1<1 then j1
    else Trans.Recal.fpar1Aux (m+2) (L m) 1 j1 0)=0
  rw [fpar0_L_one]
  rfl

theorem fpar1_L_two_lb (m:Nat) : Trans.Recal.fpar (L m) 1 2 1=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl, Bool.false_eq_true, if_false]
  rw [length_L]
  simp only [Trans.Recal.fpar1Aux]
  show (let j1:=Trans.Recal.fpar0 (L m) 2 1
    if j1<1 then -1 else if Trans.Recal.gp1 (L m) j1<1 then j1
    else Trans.Recal.fpar1Aux (m+3) (L m) 1 j1 1)=-1
  rw [fpar0_L_two]
  simp only [show ¬((1:Int)<1) by omega, if_false]
  rw [show Trans.Recal.gp1 (L m) 1=1 from rfl, if_neg (by omega)]
  simp only [Trans.Recal.fpar1Aux]
  rw [fpar0_L_one_lb, if_pos (by omega)]

theorem fpar1_L_two (m:Nat) : Trans.Recal.fpar (L m) 1 2 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl, Bool.false_eq_true, if_false]
  rw [length_L]
  rw [show Trans.Recal.gp1 (L m) 2 = 1 from rfl]
  simp only [Trans.Recal.fpar1Aux]
  rw [show Trans.Recal.fpar0 (L m) 2 0=1 from by
        unfold Trans.Recal.fpar0
        rw [if_neg (by unfold Trans.Recal.lenI; rw [length_L]; omega), length_L,
          show Trans.Recal.gp0 (L m) 2=2 from gp0_L m 2 (by omega)]
        simp only [Trans.Recal.fpar0Aux]
        rw [if_neg (by omega), show (2:Int)-1=1 by omega,
          show Trans.Recal.gp0 (L m) 1=1 from gp0_L m 1 (by omega), if_pos (by omega)],
      if_neg (by omega), show Trans.Recal.gp1 (L m) 1=1 from rfl, if_neg (by omega)]
  rw [fpar0_L_one, if_neg (by omega), show Trans.Recal.gp1 (L m) 0=0 from rfl,
    if_pos (by omega)]

theorem trMax_L (m:Nat) : Trans.Recal.trMax (L m)=1 := by
  show Trans.Recal.trMaxAux ((L m).length+1) (L m) 0=1
  rw [length_L]
  simp only [Trans.Recal.trMaxAux]
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_L]; omega)]
  rw [show Trans.Recal.isParentP (L m) 1 (0+1) 0=true from by
    unfold Trans.Recal.isParentP
    rw [show Trans.Recal.fpar (L m) 1 (0+1) 0=0 from by simpa using fpar1_L_one m]
    unfold Trans.Recal.lenI
    rw [length_L]
    rw [show decide ((0:Int)<((m+3:Nat):Int))=true from decide_eq_true (by omega)]
    rfl]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  rw [if_neg (by unfold Trans.Recal.lenI; rw [length_L]; omega)]
  rw [show Trans.Recal.isParentP (L m) 1 (0+1+1) (0+1)=false from by
    unfold Trans.Recal.isParentP
    rw [show Trans.Recal.fpar (L m) 1 (0+1+1) (0+1)=-1 from by
      simpa using fpar1_L_two_lb m]
    simp,
    if_pos (by rfl)]
  omega

theorem isAncAux_L (m k:Nat) : ∀ f:Nat,k<m+3→k<f→
    Trans.Recal.isAncAux f (L m) 0 (k:Int) 0=true := by
  refine Nat.strongRecOn (motive:=fun k=>∀f:Nat,k<m+3→k<f→
    Trans.Recal.isAncAux f (L m) 0 (k:Int) 0=true) k ?_
  intro k ih f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0 : k=0
    · subst k
      rw [if_pos (by rfl)]
    · rw [show ((0:Int)==(k:Int))=false from beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true, if_false]
      rw [fpar_L m k (by omega) hkm]
      rw [show (((k-1:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true, if_false]
      exact ih (k-1) (by omega) f (by omega) (by omega)

theorem isPrincipalP_L (m:Nat):Trans.Recal.isPrincipalP (L m)=true:=by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (L m)=false from by
      unfold Trans.Recal.isZeroP
      rw [length_L]
      simp]
  simp only [Bool.not_false, Bool.true_and]
  unfold Trans.Recal.isAnc Trans.Recal.lenI
  rw [length_L, if_neg (by omega),
    show ((m+3:Nat):Int)-1=((m+2:Nat):Int) by omega]
  exact isAncAux_L m (m+2) (m+4) (by omega) (by omega)

theorem brF_L (m:Nat):Trans.Recal.brF (L m)=[R m]:=by
  unfold Trans.Recal.brF
  rw [trMax_L]
  show Trans.Recal.ppair (R m)=[R m]
  exact ppair_E 2 m

theorem firstNodes_L (m:Nat):Trans.Recal.firstNodes (L m)=[2,((m+3:Nat):Int)]:=by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [brF_L, trMax_L]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [show (R m).length=m+1 from by exact length_E 2 m]
  simp
  omega

theorem joints_L (m:Nat):Trans.Recal.joints (L m)=[1]:=by
  unfold Trans.Recal.joints
  rw [firstNodes_L]
  change [Trans.Recal.fpar (L m) 0 2 0]=[1]
  rw [show Trans.Recal.fpar (L m) 0 2 0=1 from by
    have h:=fpar_L m 2 (by omega) (by omega)
    simpa using h]

theorem red_L (m f:Nat):Trans.Recal.red (2*m+f+3) (L m)=L m:=by
  rw [show 2*m+f+3=(2*m+f+2)+1 by omega, Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (L m)=false from by
      unfold Trans.Recal.isZeroP
      rw [length_L]
      simp, isPrincipalP_L]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [show (Trans.Recal.gp0 (L m) 0==0 && Trans.Recal.gp1 (L m) 0==0)=true from by rfl]
  simp only [if_true]
  rw [trMax_L]
  unfold Trans.Recal.lenI
  rw [length_L]
  rw [show ((1:Int)==((m+3:Nat):Int)-1)=false from
    beq_eq_false_iff_ne.mpr (by omega)]
  simp only [Bool.false_eq_true, if_false]
  rw [brF_L, firstNodes_L, joints_L]
  simp only [List.length_cons, List.length_nil]
  rw [show List.range 1=[0] by rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [show ([R m]:List Trans.Recal.PS).getD 0 []=R m from rfl,
    show ([2,((m+3:Nat):Int)]:List Int).getD 0 0=2 from rfl,
    show ([1]:List Int).getD 0 0=1 from rfl]
  rw [show Trans.Recal.gp1 (R m) 0=1 from rfl]
  simp only [show ((1:Int)==0)=false from rfl, Bool.false_eq_true, if_false]
  rw [show Trans.Recal.fpar (L m) 1 2 0=0 from fpar1_L_two m]
  change Trans.Recal.jjSeq 0 1++Trans.Recal.incrFirst
    (Trans.Recal.red (2*m+f+2) (((2:Int),(1:Int))::Trans.Recal.derp (R m))) 1=L m
  rw [show (((2:Int),(1:Int))::Trans.Recal.derp (R m))=R m from by
      unfold R Trans.Recal.derp
      rfl,
    red_R]
  rw [show Trans.Recal.incrFirst (E 1 m) (1:Int)=R m from by
    unfold E R Trans.Recal.incrFirst
    rw [List.map_cons]
    show ((2:Int),(1:Int))::Trans.Recal.incrFirst (A 2 m) 1=((2:Int),(1:Int))::A 3 m
    rw [show Trans.Recal.incrFirst (A 2 m) (1:Int)=A 3 m from by
      simpa using incrFirst_A 2 1 m]]
  rfl

theorem redP_L (m:Nat):Trans.Recal.redP (L m)=L m:=by
  unfold Trans.Recal.redP
  have hlen:2*m+3≤Trans.Recal.redFuel (L m):=by
    unfold Trans.Recal.redFuel
    rw [length_L]
    omega
  let q:=Trans.Recal.redFuel (L m)-(2*m+3)
  rw [show Trans.Recal.redFuel (L m)=2*m+q+3 by unfold q; omega]
  exact red_L m q

/-! The reader only needs the row-one parent relation at the current top. -/

theorem gp1_L_tail (m k : Nat) (hk0 : 3 ≤ k) (hk : k < m+3) :
    Trans.Recal.gp1 (L m) (k:Int) = 0 := by
  obtain ⟨q, rfl⟩ : ∃ q, k = q+3 := ⟨k-3, by omega⟩
  show (if (((q+3:Nat):Int) < 0) then 0
    else ((L m).getD (q+3) (0,0)).2) = 0
  rw [if_neg (by omega)]
  change ((A 3 m).getD q (0,0)).2 = 0
  rw [getD_A 3 m q (by omega)]

theorem fpar0_L_adj (m k : Nat) (hk0 : 0 < k) (hk : k < m+3) :
    Trans.Recal.fpar0 (L m) (k:Int) ((k-1:Nat):Int) = ((k-1:Nat):Int) := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by
    unfold Trans.Recal.lenI
    rw [length_L]
    omega), length_L, gp0_L m k hk]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega),
    show ((k:Nat):Int)-1=((k-1:Nat):Int) by omega,
    gp0_L m (k-1) (by omega), if_pos (by omega)]

theorem fpar0_L_self (m k : Nat) (hk : k < m+3) :
    Trans.Recal.fpar0 (L m) (k:Int) (k:Int) = -1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by
    unfold Trans.Recal.lenI
    rw [length_L]
    omega), length_L, gp0_L m k hk]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_pos (by omega)]

theorem fpar1_L_adj (m k : Nat) (hk0 : 3 ≤ k) (hk : k < m+3) :
    Trans.Recal.fpar (L m) 1 (k:Int) ((k-1:Nat):Int) = -1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by
    unfold Trans.Recal.lenI
    rw [length_L]
    omega)]
  simp only [show ((1:Nat)==0)=false from rfl, Bool.false_eq_true, if_false]
  rw [length_L, gp1_L_tail m k hk0 hk]
  simp only [Trans.Recal.fpar1Aux]
  rw [fpar0_L_adj m k (by omega) hk, if_neg (by omega)]
  obtain ⟨q, rfl⟩ : ∃ q, k=q+3 := ⟨k-3, by omega⟩
  cases q with
  | zero =>
    rw [show 0+3-1=2 by omega,
      show Trans.Recal.gp1 (L m) ((2:Nat):Int) = 1 from rfl,
      if_neg (by omega)]
    rw [fpar0_L_self m 2 (by omega), if_pos (by omega)]
  | succ q =>
    rw [show q+1+3-1=q+3 by omega]
    rw [gp1_L_tail m (q+3) (by omega) (by omega), if_neg (by omega)]
    rw [fpar0_L_self m (q+3) (by omega), if_pos (by omega)]

theorem lenI_L (m : Nat) : Trans.Recal.lenI (L m) = (m:Int)+3 := by
  unfold Trans.Recal.lenI
  rw [length_L]
  omega

theorem notParent1_L_adj (m k : Nat) (hk0 : 3 ≤ k) (hk : k < m+3) :
    Trans.Recal.isParentP (L m) 1 (k:Int) ((k-1:Nat):Int) = false := by
  unfold Trans.Recal.isParentP
  rw [fpar1_L_adj m k hk0 hk,
    show decide (0 ≤ ((k-1:Nat):Int)) = true from decide_eq_true (by omega),
    show decide (((k-1:Nat):Int) < Trans.Recal.lenI (L m)) = true from
      decide_eq_true (by rw [lenI_L]; omega)]
  rfl

theorem isAdm_L_top (m : Nat) :
    Trans.Recal.isAdm (L m) ((m+1:Nat):Int) = true := by
  cases m with
  | zero => rfl
  | succ m =>
    cases m with
    | zero =>
      show (!(decide ((2:Int)>Trans.Recal.lenI (L 1)) ||
        (Trans.Recal.isParentP (L 1) 1 2 1 &&
          Trans.Recal.isParentP (L 1) 1 3 2))) = true
      rw [show decide ((2:Int)>Trans.Recal.lenI (L 1)) = false from
          decide_eq_false (by rw [lenI_L]; omega),
        show Trans.Recal.isParentP (L 1) 1 2 1 = false from by
        unfold Trans.Recal.isParentP
        rw [fpar1_L_two_lb 1,
          show decide ((0:Int) ≤ 1) = true from rfl,
          show decide ((1:Int) < Trans.Recal.lenI (L 1)) = true from
            decide_eq_true (by rw [lenI_L]; omega)]
        rfl]
      simp
    | succ q =>
      show (!(decide ((((q+2:Nat):Int)+1)>Trans.Recal.lenI (L (q+2))) ||
        (Trans.Recal.isParentP (L (q+2)) 1 (((q+2:Nat):Int)+1)
            ((((q+2:Nat):Int)+1)-1) &&
          Trans.Recal.isParentP (L (q+2)) 1 ((((q+2:Nat):Int)+1)+1)
            (((q+2:Nat):Int)+1)))) = true
      rw [show (((q+2:Nat):Int)+1)=((q+3:Nat):Int) by push_cast; omega,
        show (((q+3:Nat):Int)-1)=((q+2:Nat):Int) by push_cast; omega,
        show decide (((q+3:Nat):Int)>Trans.Recal.lenI (L (q+2))) = false from
          decide_eq_false (by rw [lenI_L]; push_cast; omega),
        show Trans.Recal.isParentP (L (q+2)) 1 ((q+3:Nat):Int)
            ((q+2:Nat):Int) = false from by
          simpa using notParent1_L_adj (q+2) (q+3) (by omega) (by omega)]
      simp

theorem adm_L_top (m : Nat) :
    Trans.Recal.adm (L m) ((m+1:Nat):Int) = ((m+1:Nat):Int) := by
  show Trans.Recal.admAux ((L m).length+2) (L m) ((m+1:Nat):Int) = _
  rw [length_L]
  simp only [Trans.Recal.admAux]
  rw [if_neg (by omega), isAdm_L_top m, if_pos rfl]

theorem transType_L_succ (k : Nat) :
    Trans.Recal.transTypeMain (L (k+1)) ((k+2:Nat):Int) ((k+3:Nat):Int) = 1 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L_tail (k+1) (k+3) (by omega) (by omega)]
  simp only [show ((0 : Int) == 0) = true from rfl, if_true]
  rw [show ((k+2:Nat):Int)=(((k+1)+1:Nat):Int) by omega,
    isAdm_L_top (k+1), if_pos rfl]

def High : Nat → Trans.Dict.BT
  | 0 => .D 1 .zero
  | _+1 => .D 0 .zero

def StepC2 : Nat → Trans.Dict.BT
  | 0 => .D 1 (.D 0 .zero)
  | _+1 => .D 0 (.D 0 .zero)

theorem mkC2_L_succ (k : Nat) :
    Trans.Recal.mkC2 (L (k+1)) ((k+2:Nat):Int) ((k+3:Nat):Int) 1 (High k) = StepC2 k := by
  cases k with
  | zero => rfl
  | succ k =>
    show Trans.Dict.BT.D 0
      (Trans.Recal.bplus Trans.Dict.BT.zero
        (Trans.Dict.BT.D (Trans.Recal.gp1 (L (k+2)) ((k+4:Nat):Int)).toNat Trans.Dict.BT.zero)) = _
    rw [gp1_L_tail (k+2) (k+4) (by omega) (by omega)]
    rfl

theorem size_rep0 : ∀ k : Nat, (rep0 k).size=k+1
  | 0 => rfl
  | k+1 => by
    simp only [rep0, Trans.Dict.BT.size, size_rep0 k]
    omega

theorem size_LBT (k : Nat) : (LBT k).size=k+4 := by
  simp only [LBT, Trans.Dict.BT.size, size_rep0]
  omega

theorem repl_rep0 : ∀ (f k : Nat), k+1 ≤ f →
    Trans.Recal.replMark f (rep0 (k+1)) (.D 0 .zero) (.D 0 (.D 0 .zero)) =
      some (rep0 (k+2))
  | 0, k, h => absurd h (by omega)
  | f+1, 0, _ => by
    exact G1.replMark_self (f+1) 0 Trans.Dict.BT.zero (.D 0 (.D 0 .zero)) (by omega)
  | f+1, k+1, h => by
    change Trans.Recal.replMark (f+1) (.D 0 (rep0 (k+1))) (.D 0 .zero)
      (.D 0 (.D 0 .zero)) = some (.D 0 (rep0 (k+2)))
    rw [Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 0 (rep0 (k+1))) == (.D 0 .zero)) = false from rfl]
    simp only [Bool.false_eq_true, if_false]
    rw [repl_rep0 f k (by omega)]
    rfl

theorem repl_LBT (f k : Nat) (hf : k+4 ≤ f) :
    Trans.Recal.replMark f (LBT k) (High k) (StepC2 k) = some (LBT (k+1)) := by
  obtain ⟨g, rfl⟩ : ∃ g, f=g+4 := ⟨f-4, by omega⟩
  cases k with
  | zero =>
    simp only [LBT, High, StepC2, rep0, Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 0 (.D 1 (.D 1 .zero))) == (.D 1 .zero)) = false from rfl,
      show ((Trans.Dict.BT.D 1 (.D 1 .zero)) == (.D 1 .zero)) = false from rfl,
      if_pos (G1.beq_BT_self (.D 1 .zero))]
    rfl
  | succ k =>
    change Trans.Recal.replMark (g+4) (.D 0 (.D 1 (.D 1 (rep0 (k+1)))))
      (.D 0 .zero) (.D 0 (.D 0 .zero)) = some (.D 0 (.D 1 (.D 1 (rep0 (k+2)))))
    rw [Trans.Recal.replMark,
      show ((Trans.Dict.BT.D 0 (.D 1 (.D 1 (rep0 (k+1))))) == (.D 0 .zero)) = false from rfl]
    simp only [Bool.false_eq_true, if_false]
    rw [Trans.Recal.replMark,
      show ((Trans.Dict.BT.D 1 (.D 1 (rep0 (k+1)))) == (.D 0 .zero)) = false from rfl]
    simp only [Bool.false_eq_true, if_false]
    rw [Trans.Recal.replMark,
      show ((Trans.Dict.BT.D 1 (rep0 (k+1))) == (.D 0 .zero)) = false from rfl]
    simp only [Bool.false_eq_true, if_false]
    rw [repl_rep0 (g+1) k (by omega)]
    rfl

/-! Memo-table invariant for the two requests made by the ladder reader. -/

abbrev Base : Trans.Recal.PS := [((0:Int),(0:Int))]
abbrev B0 : Trans.Recal.PS := B 0

def Val (k : Nat) : Option Int → Trans.Dict.BT
  | none => LBT k
  | _ => High k

def Good (p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT) : Prop :=
  (∀ k, p.1 = (L k, none) → p.2 = LBT k)
  ∧ (∀ k, p.1 = (L k, some ((k+2:Nat):Int)) → p.2 = High k)
  ∧ (p.1 = (B0, none) → p.2 = .D 0 (.D 1 .zero))
  ∧ (p.1 = (B0, some 1) → p.2 = .D 1 .zero)
  ∧ (p.1 = (Base, none) → p.2 = Trans.Dict.BT.zero)

def Sound (tbl : Trans.Recal.Memo) : Prop := ∀ p ∈ tbl, Good p

theorem Sound_nil : Sound [] := by intro p hp; simp at hp

theorem L_inj (a b : Nat) (h : L a = L b) : a=b := by
  have hl := congrArg List.length h
  rw [length_L, length_L] at hl
  omega

theorem L_ne_B0 (k : Nat) : L k ≠ B0 := by
  intro h
  have hl := congrArg List.length h
  rw [length_L, length_B] at hl
  omega

theorem L_ne_Base (k : Nat) : L k ≠ Base := by
  intro h
  have hl := congrArg List.length h
  rw [length_L] at hl
  simp at hl

theorem B0_ne_Base : B0 ≠ Base := by
  intro h
  have hl := congrArg List.length h
  rw [length_B] at hl
  simp at hl

theorem Sound_cons_L (tbl : Trans.Recal.Memo) (hs : Sound tbl) (k : Nat)
    (req : Option Int) (hr : req=none ∨ req=some ((k+2:Nat):Int)) :
    Sound (((L k,req),Val k req)::tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h | h
  · subst h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      have hL : L k=L j := congrArg Prod.fst hj
      have hreq : req=none := congrArg Prod.snd hj
      have hkj := L_inj k j hL
      subst hkj
      rw [hreq]
      rfl
    · intro j hj
      have hL : L k=L j := congrArg Prod.fst hj
      have hreq : req=some ((j+2:Nat):Int) := congrArg Prod.snd hj
      have hkj := L_inj k j hL
      subst hkj
      rw [hreq]
      rfl
    · intro hj
      exact absurd (congrArg Prod.fst hj) (L_ne_B0 k)
    · intro hj
      exact absurd (congrArg Prod.fst hj) (L_ne_B0 k)
    · intro hj
      exact absurd (congrArg Prod.fst hj) (L_ne_Base k)
  · exact hs p h

theorem Sound_cons_B (tbl : Trans.Recal.Memo) (hs : Sound tbl) (req : Option Int)
    (hr : req=none ∨ req=some 1) :
    Sound (((B0,req), if req=none then .D 0 (.D 1 .zero) else .D 1 .zero)::tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h | h
  · subst h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      exact absurd (congrArg Prod.fst hk).symm (L_ne_B0 k)
    · intro k hk
      exact absurd (congrArg Prod.fst hk).symm (L_ne_B0 k)
    · intro hk
      have hreq : req=none := congrArg Prod.snd hk
      rw [hreq]
      rfl
    · intro hk
      have hreq : req=some 1 := congrArg Prod.snd hk
      rw [hreq]
      rfl
    · intro hk
      exact absurd (congrArg Prod.fst hk) B0_ne_Base
  · exact hs p h

theorem Sound_cons_base (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    Sound (((Base,none),Trans.Dict.BT.zero)::tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h | h
  · subst h
    refine ⟨?_, ?_, ?_, ?_, fun _=>rfl⟩
    · intro k hk
      exact absurd (congrArg Prod.fst hk).symm (L_ne_Base k)
    · intro k hk
      exact absurd (congrArg Prod.fst hk).symm (L_ne_Base k)
    · intro hk
      exact absurd (congrArg Prod.fst hk).symm B0_ne_Base
    · intro hk
      exact absurd (congrArg Prod.fst hk).symm B0_ne_Base
  · exact hs p h

theorem good_of_find {tbl : Trans.Recal.Memo} (hs : Sound tbl)
    {key : Trans.Recal.PS × Option Int}
    {p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT}
    (h : tbl.find? (fun q=>q.1==key)=some p) : Good p ∧ p.1=key := by
  refine ⟨hs p (List.mem_of_find?_eq_some h), ?_⟩
  have hb : p.1 == key := List.find?_some (p:=fun q=>q.1==key) (a:=p) h
  exact eq_of_beq hb

theorem isReducedP_L (k : Nat) : Trans.Recal.isReducedP (L k)=true := by
  show (Trans.Recal.redP (L k)==L k)=true
  rw [redP_L]
  exact G1.beq_PS_self _

theorem run_base_ok (f : Nat) (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (f+1) Base none).run tbl).1=Trans.Dict.BT.zero ∧
      Sound ((Trans.Recal.runAux (f+1) Base none).run tbl).2 := by
  cases hf : tbl.find? (fun q=>q.1==(Base,(none:Option Int))) with
  | some p =>
    rw [G1.run_hit f Base none tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨hg.2.2.2.2 he,hs⟩
  | none =>
    rw [G1.run_base f tbl hf]
    exact ⟨rfl,Sound_cons_base tbl hs⟩

theorem runAux_B0 (g : Nat) (req : Option Int) (hr : req=none ∨ req=some 1)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+2) B0 req).run tbl).1 =
        (if req=none then .D 0 (.D 1 .zero) else .D 1 .zero) ∧
      Sound ((Trans.Recal.runAux (g+2) B0 req).run tbl).2 := by
  cases hf : tbl.find? (fun q=>q.1==(B0,req)) with
  | some p =>
    rw [G1.run_hit (g+1) B0 req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    refine ⟨?_,hs⟩
    rcases hr with h | h
    · subst h
      simpa using hg.2.2.1 he
    · subst h
      simpa using hg.2.2.2.1 he
  | none =>
    rw [Trans.Recal.runAux]
    simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
      MonadStateOf.get, Id.run, hf,
      show Trans.Recal.isReducedP B0=true from G1.isReducedP_LG 0,
      show Trans.Recal.isPrincipalP B0=true from G1.isPrincipalP_LG 0,
      Bool.not_true, Bool.false_eq_true, if_false,
      show Trans.Recal.lenI B0=2 from G1.lenI_LG 0,
      show (((2:Int)-1)==0)=false from rfl,
      show Trans.Recal.predP B0=Base from rfl]
    cases hrun : (Trans.Recal.runAux (g+1) Base none) tbl with
    | mk a s =>
      have ih:=run_base_ok g tbl hs
      rw [show (Trans.Recal.runAux (g+1) Base none).run tbl=(a,s) from hrun] at ih
      have ha:a=Trans.Dict.BT.zero:=ih.1
      have hsm:Sound s:=ih.2
      subst ha
      simp only [show ((Trans.Dict.BT.zero:Trans.Dict.BT)==.zero)=true from rfl,if_true]
      rcases hr with h | h
      · subst h
        exact ⟨rfl,Sound_cons_B s hsm none (Or.inl rfl)⟩
      · subst h
        exact ⟨rfl,Sound_cons_B s hsm (some 1) (Or.inr rfl)⟩

theorem runAux_L0 (g : Nat) (req : Option Int)
    (hr : req=none ∨ req=some 2) (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+3) (L 0) req).run tbl).1=Val 0 req ∧
      Sound ((Trans.Recal.runAux (g+3) (L 0) req).run tbl).2 := by
  cases hf : tbl.find? (fun q=>q.1==(L 0,req)) with
  | some p =>
    rw [G1.run_hit (g+2) (L 0) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    refine ⟨?_,hs⟩
    rcases hr with h | h
    · subst h; exact hg.1 0 he
    · subst h; exact hg.2.1 0 he
  | none =>
    rw [Trans.Recal.runAux]
    simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
      MonadStateOf.get, Id.run, hf, isReducedP_L 0, isPrincipalP_L 0,
      Bool.not_true, Bool.false_eq_true, if_false, lenI_L 0,
      show (((((0:Nat):Int)+3-1)==0))=false from rfl,
      show Trans.Recal.predP (L 0)=B0 from rfl]
    cases hrun : (Trans.Recal.runAux (g+2) B0 none) tbl with
    | mk a s =>
      have ih1:=runAux_B0 g none (Or.inl rfl) tbl hs
      rw [show (Trans.Recal.runAux (g+2) B0 none).run tbl=(a,s) from hrun] at ih1
      have ha:a=.D 0 (.D 1 .zero):=ih1.1
      have hsm:Sound s:=ih1.2
      subst ha
      simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
        modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
        MonadStateOf.get, Id.run,
        show ((Trans.Dict.BT.D 0 (.D 1 .zero))==.zero)=false from rfl,
        Bool.false_eq_true,if_false,
        show Trans.Recal.fpar (L 0) 0 (((0:Nat):Int)+3-1) 0=1 from by
          simpa using fpar_L 0 2 (by omega) (by omega),
        show Trans.Recal.adm (L 0) 1=1 from by simpa using adm_L_top 0]
      cases hrun2 : (Trans.Recal.runAux (g+2) B0 (some 1)) s with
      | mk c1 s2 =>
        have ih2:=runAux_B0 g (some 1) (Or.inr rfl) s hsm
        rw [show (Trans.Recal.runAux (g+2) B0 (some 1)).run s=(c1,s2) from hrun2] at ih2
        have hc1:c1=.D 1 .zero:=ih2.1
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
          modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
          MonadStateOf.get, Id.run,
          show Trans.Recal.transTypeMain (L 0) 1 (((0:Nat):Int)+3-1)=3 from rfl,
          show Trans.Recal.mkC2 (L 0) 1 (((0:Nat):Int)+3-1) 3
              (Trans.Dict.BT.D 1 .zero)=Trans.Dict.BT.D 1 (.D 1 .zero) from rfl]
        rcases hr with h | h
        · subst h
          rw [show Trans.Recal.replMark
              ((Trans.Dict.BT.D 0 (.D 1 .zero)).size+
                ((Trans.Dict.BT.D 1 .zero).size+
                  (Trans.Dict.BT.D 1 (.D 1 .zero)).size+4))
              (Trans.Dict.BT.D 0 (.D 1 .zero)) (Trans.Dict.BT.D 1 .zero)
                (Trans.Dict.BT.D 1 (.D 1 .zero)) = some (LBT 0) from rfl]
          exact ⟨rfl,Sound_cons_L s2 hsm2 0 none (Or.inl rfl)⟩
        · subst h
          simp only [show ¬((2:Int)<(((0:Nat):Int)+3-1)) by omega,if_false]
          exact ⟨rfl,Sound_cons_L s2 hsm2 0 (some 2) (Or.inr rfl)⟩

set_option maxHeartbeats 1000000 in
theorem runAux_step (k g : Nat) (req : Option Int)
    (hr : req=none ∨ req=some (((k+1)+2:Nat):Int))
    (tbl : Trans.Recal.Memo) (hs : Sound tbl)
    (ih : ∀ (r : Option Int), r=none ∨ r=some ((k+2:Nat):Int) →
      ∀ (s : Trans.Recal.Memo), Sound s →
        ((Trans.Recal.runAux (k+g+3) (L k) r).run s).1=Val k r ∧
          Sound ((Trans.Recal.runAux (k+g+3) (L k) r).run s).2) :
    ((Trans.Recal.runAux ((k+1)+g+3) (L (k+1)) req).run tbl).1=Val (k+1) req ∧
      Sound ((Trans.Recal.runAux ((k+1)+g+3) (L (k+1)) req).run tbl).2 := by
    cases hf : tbl.find? (fun q=>q.1==(L (k+1),req)) with
    | some p =>
      rw [show k+1+g+3=(k+g+3)+1 by omega,
        G1.run_hit (k+g+3) (L (k+1)) req tbl p hf]
      obtain ⟨hg,he⟩:=good_of_find hs hf
      refine ⟨?_,hs⟩
      rcases hr with h | h
      · subst h; exact hg.1 (k+1) he
      · subst h; exact hg.2.1 (k+1) he
    | none =>
      rw [show k+1+g+3=(k+g+3)+1 by omega,Trans.Recal.runAux]
      simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
        modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
        MonadStateOf.get, Id.run, hf, isReducedP_L (k+1), isPrincipalP_L (k+1),
        Bool.not_true, Bool.false_eq_true, if_false, lenI_L (k+1),
        show (((((k+1:Nat):Int)+3-1)==0))=false from by simp; omega,
        predP_L k]
      cases hrun : (Trans.Recal.runAux (k+g+3) (L k) none) tbl with
      | mk a s =>
        have ih1:=ih none (Or.inl rfl) tbl hs
        rw [show (Trans.Recal.runAux (k+g+3) (L k) none).run tbl=(a,s) from hrun] at ih1
        have ha:a=LBT k:=ih1.1
        have hsm:Sound s:=ih1.2
        subst ha
        simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
          modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
          MonadStateOf.get, Id.run,
          show ((LBT k)==Trans.Dict.BT.zero)=false from rfl,
          Bool.false_eq_true,if_false,
          show Trans.Recal.fpar (L (k+1)) 0 (((k+1:Nat):Int)+3-1) 0=
              ((k+2:Nat):Int) from by
            rw [show (((k+1:Nat):Int)+3-1)=((k+3:Nat):Int) by push_cast; omega]
            have h:=fpar_L (k+1) (k+3) (by omega) (by omega)
            simpa using h,
          show Trans.Recal.adm (L (k+1)) ((k+2:Nat):Int)=((k+2:Nat):Int) from by
            simpa using adm_L_top (k+1)]
        cases hrun2 : (Trans.Recal.runAux (k+g+3) (L k)
            (some ((k+2:Nat):Int))) s with
        | mk c1 s2 =>
          have ih2:=ih (some ((k+2:Nat):Int)) (Or.inr rfl) s hsm
          rw [show (Trans.Recal.runAux (k+g+3) (L k)
              (some ((k+2:Nat):Int))).run s=(c1,s2) from hrun2] at ih2
          have hc1:c1=High k:=ih2.1
          have hsm2:Sound s2:=ih2.2
          subst hc1
          simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
            modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
            MonadStateOf.get, Id.run,
            show Trans.Recal.transTypeMain (L (k+1)) ((k+2:Nat):Int)
                (((k+1:Nat):Int)+3-1)=1 from by
              rw [show (((k+1:Nat):Int)+3-1)=((k+3:Nat):Int) by push_cast; omega]
              exact transType_L_succ k,
            show Trans.Recal.mkC2 (L (k+1)) ((k+2:Nat):Int)
                (((k+1:Nat):Int)+3-1) 1 (High k)=StepC2 k from by
              rw [show (((k+1:Nat):Int)+3-1)=((k+3:Nat):Int) by push_cast; omega]
              exact mkC2_L_succ k]
          rcases hr with h | h
          · subst h
            rw [repl_LBT ((LBT k).size+((High k).size+(StepC2 k).size+4)) k (by
              show k+4≤(LBT k).size+((High k).size+(StepC2 k).size+4)
              rw [size_LBT]
              omega)]
            simp only [Option.getD_some]
            exact ⟨rfl,Sound_cons_L s2 hsm2 (k+1) none (Or.inl rfl)⟩
          · subst h
            simp only [show ¬((((k+1)+2:Nat):Int)<(((k+1:Nat):Int)+3-1)) by
                push_cast; omega,
              if_false,
              show Trans.Recal.gp1 (L (k+1)) (((k+1:Nat):Int)+3-1)=0 from by
                rw [show (((k+1:Nat):Int)+3-1)=((k+3:Nat):Int) by push_cast; omega]
                exact gp1_L_tail (k+1) (k+3) (by omega) (by omega)]
            exact ⟨rfl,Sound_cons_L s2 hsm2 (k+1)
              (some (((k+1)+2:Nat):Int)) (Or.inr rfl)⟩

set_option maxHeartbeats 2000000 in
theorem runAux_L (k g : Nat) (req : Option Int)
    (hr : req=none ∨ req=some ((k+2:Nat):Int))
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (k+g+3) (L k) req).run tbl).1=Val k req ∧
      Sound ((Trans.Recal.runAux (k+g+3) (L k) req).run tbl).2 := by
  induction k generalizing g req tbl with
  | zero => exact runAux_L0 g req (by simpa using hr) tbl hs
  | succ k ih =>
    apply runAux_step k g req hr tbl hs
    intro r h s ht
    exact ih g r h s ht

theorem transPort_L (m : Nat) : Trans.Recal.transPort (L m) = LBT m := by
  have hb : m + 3 ≤ Trans.Recal.transFuel (L m) := by
    show m + 3 ≤ 40 + 6 * ((L m).length + Trans.Recal.maxE (L m))
    rw [length_L]
    omega
  have h : Trans.Recal.transFuel (L m) =
      m + (Trans.Recal.transFuel (L m) - m - 3) + 3 := by
    omega
  show ((Trans.Recal.runAux (Trans.Recal.transFuel (L m)) (L m) none).run []).1 = _
  rw [h]
  exact (runAux_L m _ none (Or.inl rfl) [] Sound_nil).1

theorem expand_M (n : Nat) :
    BMS.expand M n = [[0,0],[1,1],[2,1]] ++
      (List.range (n+1)).map (fun a => [3+a,0]) := by
  show (BMS.expand? M n).getD [] = _
  have h : BMS.expand? M n = some (M.take 3 ++
      ((List.range (n+1)).map (fun a =>
        ([[3+a*1*1,0+a*0*1]] : BMS.Matrix))).flatten) := rfl
  have hf : (fun a : Nat => ([[3+a*1*1,0+a*0*1]] : BMS.Matrix)) =
      fun a => [[3+a,0]] := by
    funext a
    simp
  have hflat (l : List Nat) :
      ((l.map (fun a => ([[3+a,0]] : BMS.Matrix))).flatten) =
        l.map (fun a => ([3+a,0] : BMS.Col)) := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.map_cons, List.flatten_cons, ih]
      rfl
  rw [h, hf, hflat]
  rfl

theorem map_tail (m : Nat) :
    (((List.range m).map (fun a => ([3+a,0] : BMS.Col))) : BMS.Matrix).map
        (fun c => ((c.getD 0 0 : Int), (c.getD 1 0 : Int))) = A 3 m := by
  unfold A
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  apply Prod.ext <;> simp
  push_cast
  omega

theorem all_len_tail (m : Nat) :
    ((List.range m).map (fun a => ([3+a,0] : BMS.Col))).all
      (fun c => decide (c.length ≤ 2)) = true := by
  simp

theorem ofMatrix_M (n : Nat) :
    Trans.Recal.ofMatrix (BMS.expand M n) = some (L (n+1)) := by
  rw [expand_M]
  unfold Trans.Recal.ofMatrix
  rw [show (([[0,0],[1,1],[2,1]] : BMS.Matrix) ++
      (List.range (n+1)).map (fun a => ([3+a,0] : BMS.Col))).isEmpty = false from by
        cases n <;> rfl]
  rw [List.all_append, all_len_tail]
  simp only [List.all_cons, List.length_cons, List.length_nil, decide_true,
    Bool.and_true, Bool.not_false, Bool.true_and, if_true, List.map_append,
    List.map_cons, List.map_nil]
  rw [map_tail]
  rfl

/-- リンク 3。`wcnf` の指数は ω 塔の `n+1` 段目になる。 -/
theorem dict_LBT (n : Nat) :
    Trans.Dict.dict (LBT (n+1)) = fsN t (n+2) := by
  unfold LBT t
  rw [rep0_eq_G3Dict]
  exact G3Dict.dict_LBT_fsN n

theorem fsN_t (n : Nat) :
    fsN t (n+2) = phi (Evidence.WF.tower (n+1)) zero := by
  unfold t
  exact G3Dict.fsN_t n

theorem le_value_one (n : Nat) :
    le (phi (Evidence.WF.tower (n+1)) zero) TM.Term.one = false := by
  cases n <;> rfl

theorem one_plus_value (n : Nat) :
    plus TM.Term.one (phi (Evidence.WF.tower (n+1)) zero) =
      phi (Evidence.WF.tower (n+1)) zero := by
  show ofList ((toList TM.Term.one).filter
      (fun a => le (phi (Evidence.WF.tower (n+1)) zero) a) ++
      [phi (Evidence.WF.tower (n+1)) zero]) = _
  rw [show toList TM.Term.one = [TM.Term.one] from rfl]
  simp only [List.filter_cons, le_value_one, Bool.false_eq_true, if_false,
    List.filter_nil]
  rfl

/-- 行の主張。展開の値は `φ̄(ω↑↑(n+1),0)` で、`t[n+2]` と一致する。 -/
theorem oR_M (n : Nat) : Trans.oR (BMS.expand M n) = some (fsN t (n+2)) := by
  show (if (BMS.expand M n).isEmpty then some TM.Term.zero
        else ((Trans.Recal.ofMatrix (BMS.expand M n)).map Trans.Recal.transPort).map
          (fun u => plus TM.Term.one (Trans.Dict.dict u))) = _
  rw [show (BMS.expand M n).isEmpty = false from by
    rw [expand_M]
    cases n <;> rfl]
  simp only [Bool.false_eq_true, if_false, ofMatrix_M, Option.map_some]
  rw [transPort_L, dict_LBT]
  rw [fsN_t]
  exact congrArg some (one_plus_value n)

#guard (List.range 6).all fun n =>
  Trans.oR (BMS.expand M n) == some (fsN t (n+2))
#guard rest12.any fun r => r.m == M && r.t == t
#guard (rows.filter fun r => r.proof == "namespace G3").length == 1

#print axioms oR_M

end G3
end Rows.Selected
