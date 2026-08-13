import Rows.G4
import Rows.G5Dict

open TM Term BMS Trans Rows Rows.Selected

namespace Rows.Selected
namespace G5

def M : BMS.Matrix := [[0,0],[1,1],[2,2],[1,1],[2,2]]
def t : Term := psi (Z zero)
  (add (Z (phi zero zero)) (phi (phi zero zero) (Z zero)))

/-- The fixed height-two prefix followed by the ascending row-one tail. -/
def R (m : Nat) : Trans.Recal.PS :=
  (0,0) :: (1,1) :: (2,2) :: (1,1) :: G4.A 2 m

abbrev D1z : Trans.Dict.BT := .D 1 .zero
abbrev D2z : Trans.Dict.BT := .D 2 .zero
abbrev High : Trans.Dict.BT := .D 1 D1z

def RBT (m : Nat) : Trans.Dict.BT :=
  .D 0 (.sum D2z (G4.rep1 (m+1)))

theorem length_R (m : Nat) : (R m).length=m+4 := by
  simp [R, G4.length_A]

theorem lenI_R (m : Nat) : Trans.Recal.lenI (R m)=(m:Int)+4 := by
  unfold Trans.Recal.lenI
  rw [length_R]
  omega

theorem R_succ (m : Nat) :
    R (m+1)=R m ++ [((((2+m:Nat):Int),(1:Int)))] := by
  unfold R
  rw [G4.A_succ_last]
  rfl

theorem predP_R (m : Nat) : Trans.Recal.predP (R (m+1))=R m := by
  rw [R_succ]
  unfold Trans.Recal.predP
  rw [show ((R m ++ [((((2+m:Nat):Int),(1:Int)))]).length == 1)=false from by
    rw [List.length_append, length_R]
    simp]
  simp

/-! ### Link 1: expansion and parsing. -/

theorem expand_M (n : Nat) :
    BMS.expand M n = [[0,0],[1,1],[2,2],[1,1]] ++
      (List.range n).map (fun a => [2+a,1]) := by
  show (BMS.expand? M n).getD [] = _
  have h : BMS.expand? M n = some (M.take 3 ++
      ((List.range (n+1)).map (fun a =>
        ([[1+a*1*1,1+a*0*1]] : BMS.Matrix))).flatten) := rfl
  have hf : (fun a : Nat => ([[1+a*1*1,1+a*0*1]] : BMS.Matrix)) =
      fun a => [[1+a,1]] := by
    funext a
    simp
  have hflat (l : List Nat) :
      ((l.map (fun a => ([[1+a,1]] : BMS.Matrix))).flatten) =
        l.map (fun a => ([1+a,1] : BMS.Col)) := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.map_cons, List.flatten_cons, ih]
      rfl
  rw [h, hf, hflat]
  rw [List.range_succ_eq_map]
  simp only [Option.getD_some, M, List.take, List.map_cons, List.map_map]
  change [([0,0] : BMS.Col), [1,1], [2,2], [1,1]] ++
      (List.range n).map ((fun a => ([1+a,1] : BMS.Col)) ∘ Nat.succ) = _
  congr 2
  funext a
  simp
  omega

theorem map_tail (m : Nat) :
    (((List.range m).map (fun a => ([2+a,1] : BMS.Col))) : BMS.Matrix).map
        (fun c => ((c.getD 0 0 : Int), (c.getD 1 0 : Int))) = G4.A 2 m :=
  G4.map_tail m

theorem all_len_tail (m : Nat) :
    ((List.range m).map (fun a => ([2+a,1] : BMS.Col))).all
      (fun c => decide (c.length ≤ 2)) = true := by
  simp

/-- Link 1: the expanded row lands on the measured one-pair ladder. -/
theorem ofMatrix_M (n : Nat) :
    Trans.Recal.ofMatrix (BMS.expand M n)=some (R n) := by
  rw [expand_M]
  unfold Trans.Recal.ofMatrix
  rw [show (([[0,0],[1,1],[2,2],[1,1]] : BMS.Matrix) ++
      (List.range n).map (fun a => ([2+a,1] : BMS.Col))).isEmpty=false from by
        cases n <;> rfl]
  rw [List.all_append, all_len_tail]
  simp only [List.all_cons, List.length_cons, List.length_nil,
    Bool.and_true, Bool.not_false, Bool.true_and, List.map_append,
    List.map_cons, List.map_nil]
  rw [map_tail]
  rfl

#guard (List.range 8).all fun n =>
  Trans.Recal.ofMatrix (BMS.expand M n)==some (R n)
#guard (List.range 8).all fun m => Trans.Recal.predP (R (m+1))==R m
#guard rest12.any fun r => r.m==M && r.t==t

/-! ### Structural facts used by reduction. -/

theorem getD_R_tail (m k : Nat) (hk : k<m) :
    (R m).getD (k+4) (0,0)=((((k+2:Nat):Int),(1:Int))) := by
  show (G4.A 2 m).getD k (0,0)=_
  simpa [Nat.add_comm] using G4.getD_A 2 m k hk

theorem gp0_R_tail (m k : Nat) (hk : k<m) :
    Trans.Recal.gp0 (R m) ((k+4:Nat):Int)=((k+2:Nat):Int) := by
  show (if ((k+4:Nat):Int)<0 then 0 else
    ((R m).getD (k+4) (0,0)).1)=_
  rw [if_neg (by omega), getD_R_tail m k hk]

theorem gp1_R_tail (m k : Nat) (hk : k<m) :
    Trans.Recal.gp1 (R m) ((k+4:Nat):Int)=1 := by
  show (if ((k+4:Nat):Int)<0 then 0 else
    ((R m).getD (k+4) (0,0)).2)=1
  rw [if_neg (by omega), getD_R_tail m k hk]

theorem fpar_R_three (m : Nat) :
    Trans.Recal.fpar (R m) 0 3 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_R]; omega)]
  rfl

theorem fpar_R_tail (m k : Nat) (hk : k<m) :
    Trans.Recal.fpar (R m) 0 ((k+4:Nat):Int) 0=((k+3:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_R]; omega)]
  simp only [show ((0:Nat)==0)=true from rfl, if_true]
  rw [gp0_R_tail m k hk, length_R]
  rw [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega)]
  cases k with
  | zero =>
    change (if Trans.Recal.gp0 (R m) 3<2 then 3
      else Trans.Recal.fpar0Aux (m+4) (R m) 2 2 0)=3
    rw [show Trans.Recal.gp0 (R m) 3=1 from rfl, if_pos (by omega)]
  | succ k =>
    rw [show ((k+1+4:Nat):Int)-1=((k+4:Nat):Int) by omega,
      gp0_R_tail m k (by omega), if_pos (by push_cast; omega)]

theorem isAncAux_R_three (m f : Nat) (hf : 2≤f) :
    Trans.Recal.isAncAux f (R m) 0 3 0=true := by
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    rw [show ((0:Int)==3)=false from rfl]
    simp only [Bool.false_eq_true, if_false, fpar_R_three]
    rw [show ((0:Int)==(-1:Int))=false from rfl]
    simp only [Bool.false_eq_true, if_false]
    cases f with
    | zero => omega
    | succ f => rfl

theorem isAncAux_R_tail (m k : Nat) : ∀ f : Nat, k<m → k+3<f →
    Trans.Recal.isAncAux f (R m) 0 ((k+4:Nat):Int) 0=true := by
  refine Nat.strongRecOn (motive:=fun k => ∀ f:Nat, k<m → k+3<f →
    Trans.Recal.isAncAux f (R m) 0 ((k+4:Nat):Int) 0=true) k ?_
  intro k ih f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    rw [show ((0:Int)==((k+4:Nat):Int))=false from
      beq_eq_false_iff_ne.mpr (by omega)]
    simp only [Bool.false_eq_true, if_false]
    rw [fpar_R_tail m k hkm]
    rw [show (((k+3:Nat):Int)==(-1:Int))=false from
      beq_eq_false_iff_ne.mpr (by omega)]
    simp only [Bool.false_eq_true, if_false]
    cases k with
    | zero =>
      simpa using isAncAux_R_three m f (by omega)
    | succ k =>
      have h:=ih k (by omega) f (by omega) (by omega)
      simpa only [show (k+1+3:Nat)=k+4 by omega] using h

theorem isPrincipalP_R (m : Nat) : Trans.Recal.isPrincipalP (R m)=true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (R m)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_R]
    simp]
  simp only [Bool.not_false, Bool.true_and]
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_R]; omega), length_R, lenI_R]
  cases m with
  | zero =>
    simpa only [show ((0:Nat):Int)+4-1=3 by omega] using
      isAncAux_R_three 0 5 (by omega)
  | succ m =>
    simpa only [show (((m+1:Nat):Int)+4-1)=((m+4:Nat):Int) by omega] using
      isAncAux_R_tail (m+1) m (m+6) (by omega) (by omega)

theorem fAncAux_K_last (d a m k : Nat) (hda : d<a) : ∀ (f : Nat)
    (acc : List Int), k<m+1 → k<f → acc.getLast?=some (k:Int) →
    (Trans.Recal.fAncAux f (G4.K d a m) 0 (k:Int) 0 acc).getLast?=some 0 := by
  refine Nat.strongRecOn (motive:=fun k => ∀ (f:Nat) (acc:List Int),
    k<m+1 → k<f → acc.getLast?=some (k:Int) →
    (Trans.Recal.fAncAux f (G4.K d a m) 0 (k:Int) 0 acc).getLast?=some 0) k ?_
  intro k ih f acc hkm hkf hlast
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.fAncAux]
    by_cases hk0:k=0
    · subst k
      change (if Trans.Recal.fpar (G4.K d a m) 0 0 0≥0 then
        (Trans.Recal.fAncAux f (G4.K d a m) 0
          (Trans.Recal.fpar (G4.K d a m) 0 0 0) 0
          (acc++[Trans.Recal.fpar (G4.K d a m) 0 0 0])).getLast?
        else acc.getLast?)=some 0
      rw [show Trans.Recal.fpar (G4.K d a m) 0 0 0=-1 from by
        unfold Trans.Recal.fpar
        rw [if_neg (by rw [G4.lenI_K]; omega), if_pos (by rfl)]
        rw [G4.length_K, Trans.Recal.fpar0Aux, if_pos (by omega)],
        if_neg (by omega)]
      exact hlast
    · rw [G4.fpar_K d a m k hda (by omega) hkm, if_pos (by omega)]
      exact ih (k-1) (by omega) f (acc++[((k-1:Nat):Int)])
        (by omega) (by omega) (by simp)

theorem fAnc_K_last (d a m : Nat) (hda : d<a) :
    (Trans.Recal.fAnc (G4.K d a m) 0 (m:Int) 0).getLast?=some 0 := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by rw [G4.lenI_K]; omega), G4.length_K]
  exact fAncAux_K_last d a m m hda (m+2) [(m:Int)]
    (by omega) (by omega) (by simp)

theorem slice_K_full (d a m : Nat) :
    Trans.Recal.slice (G4.K d a m) 0 ((m:Int)+1)=G4.K d a m := by
  unfold Trans.Recal.slice
  simp only [Int.toNat_zero, List.drop_zero]
  rw [show (((m:Int)+1)-0).toNat=m+1 by omega]
  simpa only [G4.length_K] using
    (List.take_length : (G4.K d a m).take (G4.K d a m).length=G4.K d a m)

theorem ppair_K (d a m : Nat) (hda : d<a) :
    Trans.Recal.ppair (G4.K d a m)=[G4.K d a m] := by
  unfold Trans.Recal.ppair
  rw [G4.length_K, G4.lenI_K]
  rw [Trans.Recal.ppairAux]
  dsimp only
  rw [if_neg (by omega), show (m:Int)+1-1=(m:Int) by omega,
    fAnc_K_last d a m hda]
  simp only [Option.getD_some]
  rw [Trans.Recal.ppairAux, if_pos (by omega), slice_K_full]

theorem fpar0_R_one (m : Nat) : Trans.Recal.fpar0 (R m) 1 0=0 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_R]; omega), length_R]
  rw [Trans.Recal.fpar0Aux, if_neg (by omega)]
  change (if Trans.Recal.gp0 (R m) 0<1 then 0 else _)=0
  rw [show Trans.Recal.gp0 (R m) 0=0 from rfl, if_pos (by omega)]

theorem fpar0_R_two (m : Nat) : Trans.Recal.fpar0 (R m) 2 1=1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_R]; omega), length_R]
  rw [Trans.Recal.fpar0Aux, if_neg (by omega)]
  change (if Trans.Recal.gp0 (R m) 1<2 then 1 else _)=1
  rw [show Trans.Recal.gp0 (R m) 1=1 from rfl, if_pos (by omega)]

theorem fpar0_R_three_lb (m : Nat) : Trans.Recal.fpar0 (R m) 3 2=-1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_R]; omega), length_R]
  rw [Trans.Recal.fpar0Aux, if_neg (by omega)]
  change (if Trans.Recal.gp0 (R m) 2<1 then 2
    else Trans.Recal.fpar0Aux (m+3) (R m) 1 1 2)=-1
  rw [show Trans.Recal.gp0 (R m) 2=2 from rfl, if_neg (by omega)]
  rw [Trans.Recal.fpar0Aux, if_pos (by omega)]

theorem fpar1_R_one (m : Nat) : Trans.Recal.fpar (R m) 1 1 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_R]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl, Bool.false_eq_true, if_false]
  rw [show Trans.Recal.gp1 (R m) 1=1 from rfl, length_R]
  rw [Trans.Recal.fpar1Aux, fpar0_R_one, if_neg (by omega)]
  rw [show Trans.Recal.gp1 (R m) 0=0 from rfl, if_pos (by omega)]

theorem fpar1_R_two (m : Nat) : Trans.Recal.fpar (R m) 1 2 1=1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_R]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl, Bool.false_eq_true, if_false]
  rw [show Trans.Recal.gp1 (R m) 2=2 from rfl, length_R]
  rw [Trans.Recal.fpar1Aux, fpar0_R_two, if_neg (by omega)]
  rw [show Trans.Recal.gp1 (R m) 1=1 from rfl, if_pos (by omega)]

theorem fpar1_R_three_lb (m : Nat) :
    Trans.Recal.fpar (R m) 1 3 2=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_R]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl, Bool.false_eq_true, if_false]
  rw [show Trans.Recal.gp1 (R m) 3=1 from rfl, length_R]
  rw [Trans.Recal.fpar1Aux, fpar0_R_three_lb, if_pos (by omega)]

theorem isParentP_R_one (m : Nat) :
    Trans.Recal.isParentP (R m) 1 1 0=true := by
  unfold Trans.Recal.isParentP
  rw [fpar1_R_one, lenI_R]
  rw [show decide ((0:Int)<(m:Int)+4)=true from decide_eq_true (by omega)]
  rfl

theorem isParentP_R_two (m : Nat) :
    Trans.Recal.isParentP (R m) 1 2 1=true := by
  unfold Trans.Recal.isParentP
  rw [fpar1_R_two, lenI_R]
  rw [show decide ((1:Int)<(m:Int)+4)=true from decide_eq_true (by omega)]
  rfl

theorem isParentP_R_three (m : Nat) :
    Trans.Recal.isParentP (R m) 1 3 2=false := by
  unfold Trans.Recal.isParentP
  rw [fpar1_R_three_lb]
  simp

theorem trMax_R (m : Nat) : Trans.Recal.trMax (R m)=2 := by
  show Trans.Recal.trMaxAux ((R m).length+1) (R m) 0=2
  rw [length_R]
  rw [Trans.Recal.trMaxAux, if_neg (by rw [lenI_R]; omega)]
  change (if !Trans.Recal.isParentP (R m) 1 1 0 then 0
    else Trans.Recal.trMaxAux (m+4) (R m) 1)=2
  rw [isParentP_R_one]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  rw [Trans.Recal.trMaxAux, if_neg (by rw [lenI_R]; omega)]
  change (if !Trans.Recal.isParentP (R m) 1 2 1 then 1
    else Trans.Recal.trMaxAux (m+3) (R m) 2)=2
  rw [isParentP_R_two]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  rw [Trans.Recal.trMaxAux, if_neg (by rw [lenI_R]; omega)]
  change (if !Trans.Recal.isParentP (R m) 1 3 2 then 2
    else Trans.Recal.trMaxAux (m+2) (R m) 3)=2
  rw [isParentP_R_three]
  simp

theorem brF_R (m : Nat) : Trans.Recal.brF (R m)=[G4.K 1 2 m] := by
  unfold Trans.Recal.brF
  rw [trMax_R]
  change Trans.Recal.ppair (G4.K 1 2 m)=[G4.K 1 2 m]
  exact ppair_K 1 2 m (by omega)

theorem firstNodes_R (m : Nat) :
    Trans.Recal.firstNodes (R m)=[3,((m+4:Nat):Int)] := by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [brF_R, trMax_R]
  simp [G4.length_K]
  omega

theorem joints_R (m : Nat) : Trans.Recal.joints (R m)=[0] := by
  unfold Trans.Recal.joints
  rw [firstNodes_R]
  change [Trans.Recal.fpar (R m) 0 3 0]=[0]
  rw [fpar_R_three]

theorem fpar0_R_three_zero (m : Nat) :
    Trans.Recal.fpar0 (R m) 3 0=0 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_R]; omega), length_R]
  rw [Trans.Recal.fpar0Aux, if_neg (by omega)]
  change (if Trans.Recal.gp0 (R m) 2<1 then 2
    else Trans.Recal.fpar0Aux (m+3) (R m) 1 1 0)=0
  rw [show Trans.Recal.gp0 (R m) 2=2 from rfl, if_neg (by omega)]
  rw [Trans.Recal.fpar0Aux, if_neg (by omega)]
  change (if Trans.Recal.gp0 (R m) 1<1 then 1
    else Trans.Recal.fpar0Aux (m+2) (R m) 1 0 0)=0
  rw [show Trans.Recal.gp0 (R m) 1=1 from rfl, if_neg (by omega)]
  rw [Trans.Recal.fpar0Aux, if_neg (by omega)]
  rw [show Trans.Recal.gp0 (R m) 0=0 from rfl, if_pos (by omega)]

theorem fpar1_R_three_zero (m : Nat) :
    Trans.Recal.fpar (R m) 1 3 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_R]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl, Bool.false_eq_true, if_false]
  rw [show Trans.Recal.gp1 (R m) 3=1 from rfl, length_R]
  rw [Trans.Recal.fpar1Aux, fpar0_R_three_zero, if_neg (by omega)]
  rw [show Trans.Recal.gp1 (R m) 0=0 from rfl, if_pos (by omega)]

set_option maxHeartbeats 1000000 in
theorem red_R (m f : Nat) :
    Trans.Recal.red (2*m+f+3) (R m)=R m := by
  rw [show 2*m+f+3=(2*m+f+2)+1 by omega, Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (R m)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_R]
    simp,
    isPrincipalP_R]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [show (Trans.Recal.gp0 (R m) 0==0 &&
      Trans.Recal.gp1 (R m) 0==0)=true from rfl]
  simp only [if_true]
  rw [trMax_R, lenI_R]
  rw [show ((2:Int)==(m:Int)+4-1)=false from
    beq_eq_false_iff_ne.mpr (by omega)]
  simp only [Bool.false_eq_true, if_false]
  rw [brF_R, firstNodes_R, joints_R]
  simp only [List.length_cons, List.length_nil]
  rw [show List.range 1=[0] from rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [show ([G4.K 1 2 m] : List Trans.Recal.PS).getD 0 []=G4.K 1 2 m from rfl,
    show ([3,((m+4:Nat):Int)] : List Int).getD 0 0=3 from rfl,
    show ([0] : List Int).getD 0 0=0 from rfl]
  rw [show Trans.Recal.gp1 (G4.K 1 2 m) 0=1 from rfl]
  simp only [show ((1:Int)==0)=false from rfl, Bool.false_eq_true, if_false]
  rw [fpar1_R_three_zero]
  change Trans.Recal.jjSeq 0 2 ++ Trans.Recal.incrFirst
    (Trans.Recal.red (2*m+f+2) (((1:Int),(1:Int))::G4.A 2 m)) 0=R m
  change Trans.Recal.jjSeq 0 2 ++ Trans.Recal.incrFirst
    (Trans.Recal.red (2*m+f+2) (G4.K 1 2 m)) 0=R m
  rw [G4.red_K_all 1 2 m f (by omega) (by omega)]
  rw [show Trans.Recal.incrFirst (G4.A 1 (m+1)) 0=G4.A 1 (m+1) from by
    simpa using G4.incrFirst_A 1 0 (m+1)]
  rw [G4.A_succ]
  rfl

theorem redP_R (m : Nat) : Trans.Recal.redP (R m)=R m := by
  have hb : 2*m+3≤Trans.Recal.redFuel (R m) := by
    unfold Trans.Recal.redFuel
    rw [length_R]
    omega
  have he : Trans.Recal.redFuel (R m)=
      2*m+(Trans.Recal.redFuel (R m)-2*m-3)+3 := by omega
  unfold Trans.Recal.redP
  rw [he, red_R]

theorem isReducedP_R (m : Nat) : Trans.Recal.isReducedP (R m)=true := by
  unfold Trans.Recal.isReducedP
  rw [redP_R]
  exact G1.beq_PS_self _

/-! ### The type-three transition at the growing end. -/

theorem gp1_R_top (m : Nat) :
    Trans.Recal.gp1 (R (m+1)) ((m+4:Nat):Int)=1 :=
  gp1_R_tail (m+1) m (by omega)

theorem gp1_R_prev (m : Nat) :
    Trans.Recal.gp1 (R (m+1)) ((m+3:Nat):Int)=1 := by
  cases m with
  | zero => rfl
  | succ m =>
    simpa only [show (m+1+3:Nat)=m+4 by omega] using
      gp1_R_tail (m+2) m (by omega)

theorem fpar_R_top (m : Nat) :
    Trans.Recal.fpar (R (m+1)) 0 ((m+4:Nat):Int) 0=((m+3:Nat):Int) :=
  fpar_R_tail (m+1) m (by omega)

theorem fpar0_R_top_lb (m : Nat) :
    Trans.Recal.fpar0 (R (m+1)) ((m+4:Nat):Int) ((m+3:Nat):Int)=
      ((m+3:Nat):Int) := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_R]; omega), length_R, gp0_R_tail (m+1) m (by omega)]
  rw [Trans.Recal.fpar0Aux, if_neg (by omega)]
  rw [show ((m+4:Nat):Int)-1=((m+3:Nat):Int) by omega, gp0_R_prev]
  rw [if_pos (by
    push_cast
    omega)]
  where
    gp0_R_prev : Trans.Recal.gp0 (R (m+1)) ((m+3:Nat):Int)=((m+1:Nat):Int) := by
      cases m with
      | zero => rfl
      | succ m =>
        simpa only [show (m+1+3:Nat)=m+4 by omega,
          show (m+1+1:Nat)=m+2 by omega] using
          gp0_R_tail (m+2) m (by omega)

theorem fpar0_R_prev_lb (m : Nat) :
    Trans.Recal.fpar0 (R (m+1)) ((m+3:Nat):Int) ((m+3:Nat):Int)=-1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_R]; omega), length_R]
  rw [Trans.Recal.fpar0Aux, if_pos (by omega)]

theorem fpar1_R_top_lb (m : Nat) :
    Trans.Recal.fpar (R (m+1)) 1 ((m+4:Nat):Int) ((m+3:Nat):Int)=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_R]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl, Bool.false_eq_true, if_false]
  rw [gp1_R_top, length_R]
  rw [Trans.Recal.fpar1Aux, fpar0_R_top_lb, if_neg (by omega), gp1_R_prev,
    if_neg (by omega)]
  rw [Trans.Recal.fpar1Aux, fpar0_R_prev_lb, if_pos (by omega)]

theorem isAdm_R_parent (m : Nat) :
    Trans.Recal.isAdm (R (m+1)) ((m+3:Nat):Int)=true := by
  have hp : Trans.Recal.isParentP (R (m+1)) 1
      ((m+4:Nat):Int) ((m+3:Nat):Int)=false := by
    unfold Trans.Recal.isParentP
    rw [show decide (0≤((m+3:Nat):Int))=true from decide_eq_true (by omega),
      show decide (((m+3:Nat):Int)<Trans.Recal.lenI (R (m+1)))=true from
        decide_eq_true (by rw [lenI_R]; omega)]
    simp only [Bool.true_and]
    rw [fpar1_R_top_lb]
    exact decide_eq_false (by omega)
  unfold Trans.Recal.isAdm Trans.Recal.isUnadmitted
  rw [show decide (((m+3:Nat):Int)>Trans.Recal.lenI (R (m+1)))=false from by
    apply decide_eq_false
    rw [lenI_R]
    omega]
  simp only [Bool.false_or]
  rw [show ((m+3:Nat):Int)+1=((m+4:Nat):Int) by omega, hp, Bool.and_false]
  rfl

theorem adm_R_parent (m : Nat) :
    Trans.Recal.adm (R (m+1)) ((m+3:Nat):Int)=((m+3:Nat):Int) := by
  unfold Trans.Recal.adm
  rw [length_R]
  rw [Trans.Recal.admAux, if_neg (by omega), isAdm_R_parent, if_pos rfl]

theorem transType_R (m : Nat) :
    Trans.Recal.transTypeMain (R (m+1)) ((m+3:Nat):Int)
      ((m+4:Nat):Int)=3 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_R_top]
  simp only [show ((1:Int)==0)=false from rfl, Bool.false_eq_true, if_false]
  rw [gp1_R_prev, if_pos (by omega), isAdm_R_parent, if_pos rfl]

theorem mkC2_R (m : Nat) :
    Trans.Recal.mkC2 (R (m+1)) ((m+3:Nat):Int) ((m+4:Nat):Int)
      3 D1z=High := by
  show Trans.Dict.BT.D 1 (Trans.Recal.bplus .zero
    (.D (Trans.Recal.gp1 (R (m+1)) ((m+4:Nat):Int)).toNat .zero))=High
  rw [gp1_R_top]
  rfl

/-! ### Memo invariant.  The base is the first two rungs of `G2.L2`; the
growing family begins at `R 0`. -/

def Allowed : Nat → Option Int → Prop
  | 0, req => req=none ∨ req=some 3
  | k+1, req => req=none ∨ req=some ((k+3:Nat):Int) ∨
      req=some ((k+4:Nat):Int)

def Val : Nat → Option Int → Trans.Dict.BT
  | 0, req => if req=none then RBT 0 else D1z
  | k+1, req => if req=none then RBT (k+1)
      else if req=some ((k+3:Nat):Int) then High else D1z

theorem Allowed_none (k : Nat) : Allowed k none := by
  cases k <;> simp [Allowed]

theorem Val_none (k : Nat) : Val k none=RBT k := by
  cases k <;> simp [Val]

theorem Val_zero_top : Val 0 (some 3)=D1z := rfl

theorem Val_own (k : Nat) :
    Val (k+1) (some ((k+3:Nat):Int))=High := by
  simp [Val]

theorem Val_top (k : Nat) :
    Val (k+1) (some ((k+4:Nat):Int))=D1z := by
  change (if (some ((k+4:Nat):Int):Option Int)=none then RBT (k+1)
    else if some ((k+4:Nat):Int)=some ((k+3:Nat):Int) then High else D1z)=D1z
  rw [if_neg (by intro h; cases h), if_neg (by
    intro h
    injection h with h
    omega)]

def Good (p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT) : Prop :=
  G2.Good2 p ∧ ∀ k req, p.1=(R k,req) → Allowed k req → p.2=Val k req

def Sound (tbl : Trans.Recal.Memo) : Prop := ∀ p∈tbl, Good p

theorem Sound_nil : Sound [] := by intro p hp; simp at hp

theorem R_inj (a b : Nat) (h : R a=R b) : a=b := by
  have hl:=congrArg List.length h
  rw [length_R,length_R] at hl
  omega

theorem R_ne_base (k : Nat) : R k≠G1.Base := by
  intro h
  have hl:=congrArg List.length h
  rw [length_R] at hl
  simp [G1.Base] at hl

theorem R_ne_L2 (a b : Nat) : R a≠G2.L2 b := by
  intro h
  have hl:=congrArg List.length h
  rw [length_R,G2.len_L2] at hl
  have hb:b=a+2:=by omega
  subst b
  have hd:=congrArg (fun q => q.getD 3 ((0:Int),(0:Int))) h
  simp [R,G2.L2,List.replicate_succ] at hd

theorem good_R_entry (k : Nat) (req : Option Int) (hr : Allowed k req) :
    Good ((R k,req),Val k req) := by
  constructor
  · refine ⟨?_,?_,?_⟩
    · intro j h
      exact absurd (congrArg Prod.fst h) (R_ne_L2 k j)
    · intro j h
      exact absurd (congrArg Prod.fst h) (R_ne_L2 k j)
    · intro h
      exact absurd (congrArg Prod.fst h) (R_ne_base k)
  · intro j r h _
    have hR:R k=R j:=congrArg Prod.fst h
    have hkj:=R_inj k j hR
    subst hkj
    have hreq:req=r:=by simpa using congrArg Prod.snd h
    subst hreq
    rfl

theorem good_L2_entry (k : Nat) (req : Option Int) :
    Good ((G2.L2 k,req),G2.L2BT k) := by
  constructor
  · refine ⟨?_,?_,?_⟩
    · intro j h
      have hL:G2.L2 k=G2.L2 j:=congrArg Prod.fst h
      have hkj:=G2.L2_inj k j hL
      subst hkj
      rfl
    · intro j h
      have hL:G2.L2 k=G2.L2 j:=congrArg Prod.fst h
      have hkj:=G2.L2_inj k j hL
      subst hkj
      rfl
    · intro h
      exact absurd (congrArg Prod.fst h) (G2.L2_ne_base k)
  · intro j r h _
    exact absurd (congrArg Prod.fst h).symm (R_ne_L2 j k)

theorem good_base_entry :
    Good ((G1.Base,(none:Option Int)),Trans.Dict.BT.zero) := by
  constructor
  · exact (G2.Sound2_cons_base [] G2.Sound2_nil) _ (by simp)
  · intro j r h _
    exact absurd (congrArg Prod.fst h).symm (R_ne_base j)

theorem Sound_cons_R (tbl : Trans.Recal.Memo) (hs : Sound tbl) (k : Nat)
    (req : Option Int) (hr : Allowed k req) :
    Sound (((R k,req),Val k req)::tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h|h
  · subst h
    exact good_R_entry k req hr
  · exact hs p h

theorem Sound_cons_L2 (tbl : Trans.Recal.Memo) (hs : Sound tbl) (k : Nat)
    (req : Option Int) : Sound (((G2.L2 k,req),G2.L2BT k)::tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h|h
  · subst h
    exact good_L2_entry k req
  · exact hs p h

theorem Sound_cons_base (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    Sound (((G1.Base,(none:Option Int)),Trans.Dict.BT.zero)::tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h|h
  · subst h
    exact good_base_entry
  · exact hs p h

theorem good_of_find {tbl : Trans.Recal.Memo} (hs : Sound tbl)
    {key : Trans.Recal.PS × Option Int}
    {p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT}
    (h : tbl.find? (fun q=>q.1==key)=some p) : Good p ∧ p.1=key := by
  refine ⟨hs p (List.mem_of_find?_eq_some h),?_⟩
  have hb : p.1==key := List.find?_some (p:=fun q=>q.1==key) (a:=p) h
  exact eq_of_beq hb

theorem value_R_of_good {p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT}
    (hg : Good p) (k : Nat) (req : Option Int) (hr : Allowed k req)
    (he : p.1=(R k,req)) : p.2=Val k req :=
  hg.2 k req he hr

theorem run_base_ok (f : Nat) (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (f+1) G1.Base none).run tbl).1=Trans.Dict.BT.zero ∧
      Sound ((Trans.Recal.runAux (f+1) G1.Base none).run tbl).2 := by
  cases hf:tbl.find? (fun q=>q.1==(G1.Base,(none:Option Int))) with
  | some p =>
    rw [G1.run_hit f G1.Base none tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨hg.1.2.2 he,hs⟩
  | none =>
    rw [G1.run_base f tbl hf]
    exact ⟨rfl,Sound_cons_base tbl hs⟩

theorem runAux_L20 (g : Nat) (req : Option Int)
    (hr : req=none ∨ req=some 0) (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+2) (G2.L2 0) req).run tbl).1=G2.L2BT 0 ∧
      Sound ((Trans.Recal.runAux (g+2) (G2.L2 0) req).run tbl).2 := by
  cases hf:tbl.find? (fun q=>q.1==(G2.L2 0,req)) with
  | some p =>
    rw [show g+2=(g+1)+1 by omega,G1.run_hit (g+1) (G2.L2 0) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    refine ⟨?_,hs⟩
    rcases hr with h|h
    · subst h
      exact hg.1.1 0 he
    · subst h
      exact hg.1.2.1 0 he
  | none =>
    rw [show g+2=(g+1)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
      MonadStateOf.get, Id.run, hf, G2.isReducedP_L2 0, G2.isPrincipalP_L2 0,
      Bool.not_true, Bool.false_eq_true, if_false, G2.lenI_L2 0,
      show (((0:Nat):Int)+2-1==0)=false from by decide,
      show Trans.Recal.predP (G2.L2 0)=G1.Base from rfl]
    cases hrun:(Trans.Recal.runAux (g+1) G1.Base none) tbl with
    | mk a s =>
      have ih:=run_base_ok g tbl hs
      rw [show (Trans.Recal.runAux (g+1) G1.Base none).run tbl=(a,s) from hrun] at ih
      have ha:a=Trans.Dict.BT.zero:=ih.1
      have hsm:Sound s:=ih.2
      subst ha
      simp only [show ((Trans.Dict.BT.zero:Trans.Dict.BT)==.zero)=true from rfl,
        if_true]
      rcases hr with h|h
      · subst h
        exact ⟨rfl,Sound_cons_L2 s hsm 0 none⟩
      · subst h
        exact ⟨rfl,Sound_cons_L2 s hsm 0 (some 0)⟩

set_option maxHeartbeats 1000000 in
theorem runAux_L21 (g : Nat) (req : Option Int)
    (hr : req=none ∨ req=some 0) (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+3) (G2.L2 1) req).run tbl).1=G2.L2BT 1 ∧
      Sound ((Trans.Recal.runAux (g+3) (G2.L2 1) req).run tbl).2 := by
  cases hf:tbl.find? (fun q=>q.1==(G2.L2 1,req)) with
  | some p =>
    rw [show g+3=(g+2)+1 by omega,G1.run_hit (g+2) (G2.L2 1) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    refine ⟨?_,hs⟩
    rcases hr with h|h
    · subst h
      exact hg.1.1 1 he
    · subst h
      exact hg.1.2.1 1 he
  | none =>
    rw [show g+3=(g+2)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
      MonadStateOf.get, Id.run, hf, G2.isReducedP_L2 1, G2.isPrincipalP_L2 1,
      Bool.not_true, Bool.false_eq_true, if_false, G2.lenI_L2 1,
      show ((((1:Nat):Int)+2-1)==0)=false from by decide,
      show Trans.Recal.predP (G2.L2 1)=G2.L2 0 from G2.predP_L2 0]
    cases hrun:(Trans.Recal.runAux (g+2) (G2.L2 0) none) tbl with
    | mk a s =>
      have ih1:=runAux_L20 g none (Or.inl rfl) tbl hs
      rw [show (Trans.Recal.runAux (g+2) (G2.L2 0) none).run tbl=(a,s) from hrun]
        at ih1
      have ha:a=G2.L2BT 0:=ih1.1
      have hsm:Sound s:=ih1.2
      subst ha
      simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
        modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
        MonadStateOf.get, Id.run, hrun,
        show ((G2.L2BT 0)==Trans.Dict.BT.zero)=false from rfl,
        Bool.false_eq_true,if_false,
        show Trans.Recal.fpar (G2.L2 1) 0 (((1:Nat):Int)+2-1) 0=1 from by rfl,
        show Trans.Recal.adm (G2.L2 1) 1=0 from G2.adm_L2_1 1 (by omega)]
      cases hrun2:(Trans.Recal.runAux (g+2) (G2.L2 0) (some 0)) s with
      | mk c1 s2 =>
        have ih2:=runAux_L20 g (some 0) (Or.inr rfl) s hsm
        rw [show (Trans.Recal.runAux (g+2) (G2.L2 0) (some 0)).run s=(c1,s2)
          from hrun2] at ih2
        have hc1:c1=G2.L2BT 0:=ih2.1
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
          modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
          MonadStateOf.get, Id.run, hrun2,
          show Trans.Recal.mkC2 (G2.L2 1) 1 (((1:Nat):Int)+2-1)
            (Trans.Recal.transTypeMain (G2.L2 1) 1 (((1:Nat):Int)+2-1))
            (G2.L2BT 0)=G2.L2BT 1 from rfl]
        rcases hr with h|h
        · subst h
          rw [G2.replMark_L2BT
            ((G2.L2BT 0).size+((G2.L2BT 0).size+(G2.L2BT 1).size+4))
            0 (G2.L2BT 1) (by omega)]
          exact ⟨rfl,Sound_cons_L2 s2 hsm2 1 none⟩
        · subst h
          simp only [show ((0:Int)<((1:Nat):Int)+2-1) from by omega,if_true,
            StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
            modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
            MonadStateOf.get, Id.run]
          cases hrun3:(Trans.Recal.runAux (g+2) (G2.L2 0) (some 0)) s2 with
          | mk c0 s3 =>
            have ih3:=runAux_L20 g (some 0) (Or.inr rfl) s2 hsm2
            rw [show (Trans.Recal.runAux (g+2) (G2.L2 0) (some 0)).run s2=(c0,s3)
              from hrun3] at ih3
            have hc0:c0=G2.L2BT 0:=ih3.1
            have hsm3:Sound s3:=ih3.2
            subst hc0
            dsimp only
            rw [if_pos (G1.isMarkedB_self (G2.L2BT 0)),
              G2.replMark_L2BT
                ((G2.L2BT 0).size+((G2.L2BT 0).size+(G2.L2BT 1).size+4))
                0 (G2.L2BT 1) (by omega)]
            exact ⟨rfl,Sound_cons_L2 s3 hsm3 1 (some 0)⟩

theorem adm_R0_zero : Trans.Recal.adm (R 0) 0=0 := by rfl

theorem transType_R0 : Trans.Recal.transTypeMain (R 0) 0 3=5 := by rfl

theorem mkC2_R0 :
    Trans.Recal.mkC2 (R 0) 0 3 5 (G2.L2BT 1)=RBT 0 := by rfl

set_option maxHeartbeats 1000000 in
theorem runAux_R0 (g : Nat) (req : Option Int) (hr : Allowed 0 req)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+4) (R 0) req).run tbl).1=Val 0 req ∧
      Sound ((Trans.Recal.runAux (g+4) (R 0) req).run tbl).2 := by
  cases hf:tbl.find? (fun q=>q.1==(R 0,req)) with
  | some p =>
    rw [show g+4=(g+3)+1 by omega,G1.run_hit (g+3) (R 0) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_R_of_good hg 0 req hr he,hs⟩
  | none =>
    rw [show g+4=(g+3)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
      MonadStateOf.get, Id.run, hf, isReducedP_R 0, isPrincipalP_R 0,
      Bool.not_true, Bool.false_eq_true, if_false, lenI_R 0,
      show (((0:Nat):Int)+4-1)=3 from by omega,
      show ((3:Int)==0)=false from rfl,
      show Trans.Recal.predP (R 0)=G2.L2 1 from rfl]
    cases hrun:(Trans.Recal.runAux (g+3) (G2.L2 1) none) tbl with
    | mk a s =>
      have ih1:=runAux_L21 g none (Or.inl rfl) tbl hs
      rw [show (Trans.Recal.runAux (g+3) (G2.L2 1) none).run tbl=(a,s) from hrun]
        at ih1
      have ha:a=G2.L2BT 1:=ih1.1
      have hsm:Sound s:=ih1.2
      subst ha
      simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
        modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
        MonadStateOf.get, Id.run, hrun,
        show (((0:Nat):Int)+4-1)=3 from by omega,
        show ((G2.L2BT 1)==Trans.Dict.BT.zero)=false from rfl,
        Bool.false_eq_true,if_false,
        show Trans.Recal.fpar (R 0) 0 3 0=0 from fpar_R_three 0,
        adm_R0_zero]
      cases hrun2:(Trans.Recal.runAux (g+3) (G2.L2 1) (some 0)) s with
      | mk c1 s2 =>
        have ih2:=runAux_L21 g (some 0) (Or.inr rfl) s hsm
        rw [show (Trans.Recal.runAux (g+3) (G2.L2 1) (some 0)).run s=(c1,s2)
          from hrun2] at ih2
        have hc1:c1=G2.L2BT 1:=ih2.1
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
          modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
          MonadStateOf.get, Id.run, hrun2, transType_R0, mkC2_R0]
        rcases hr with h|h
        · subst h
          rw [G2.replMark_L2BT
            ((G2.L2BT 1).size+((G2.L2BT 1).size+(RBT 0).size+4))
            1 (RBT 0) (by omega)]
          refine ⟨Val_none 0,?_⟩
          have ht:=Sound_cons_R s2 hsm2 0 none (Or.inl rfl)
          rw [Val_none] at ht
          exact ht

        · subst h
          simp only [show ¬((3:Int)<3) by omega,if_false,
            show Trans.Recal.gp1 (R 0) 3=1 from rfl,
            StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
            modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
            MonadStateOf.get, Id.run]
          refine ⟨Val_zero_top.symm,?_⟩
          have ht:=Sound_cons_R s2 hsm2 0 (some 3) (Or.inr rfl)
          rw [Val_zero_top] at ht
          exact ht

theorem size_RBT (m : Nat) : (RBT m).size=m+6 := by
  rw [RBT,Trans.Dict.BT.size,Trans.Dict.BT.size,Trans.Dict.BT.size,
    Trans.Dict.BT.size,G4.size_rep1]
  omega

theorem repl_RBT (f m : Nat) (hf : m+3≤f) :
    Trans.Recal.replMark f (RBT m) D1z High=some (RBT (m+1)) := by
  cases f with
  | zero => omega
  | succ f =>
    rw [RBT]
    simp only [Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 0 (.sum D2z (G4.rep1 (m+1))))==D1z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    cases f with
    | zero => omega
    | succ f =>
      rw [Trans.Recal.replMark]
      have hrep : (G4.rep1 (m+1)).toL=[G4.rep1 (m+1)] := by
        rw [G4.rep1]
        rfl
      rw [show (Trans.Dict.BT.sum D2z (G4.rep1 (m+1))).toL=
        [D2z,G4.rep1 (m+1)] from by rw [Trans.Dict.BT.toL,hrep]; rfl]
      simp [Trans.Dict.BT.ofL,RBT]
      rw [G4.repl_rep1 f m (by omega)]

theorem Allowed_prev_top (k : Nat) :
    Allowed k (some ((k+3:Nat):Int)) := by
  cases k with
  | zero => exact Or.inr rfl
  | succ k =>
    exact Or.inr (Or.inr (by congr 2 <;> omega))

theorem Val_prev_top (k : Nat) :
    Val k (some ((k+3:Nat):Int))=D1z := by
  cases k with
  | zero => exact Val_zero_top
  | succ k =>
    simpa only [show (k+1+3:Nat)=k+4 by omega] using Val_top k

set_option maxHeartbeats 2000000 in
theorem runAux_step (k g : Nat) (req : Option Int) (hr : Allowed (k+1) req)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl)
    (ih : ∀ r : Option Int, Allowed k r → ∀ s : Trans.Recal.Memo, Sound s →
      ((Trans.Recal.runAux (k+g+4) (R k) r).run s).1=Val k r ∧
        Sound ((Trans.Recal.runAux (k+g+4) (R k) r).run s).2) :
    ((Trans.Recal.runAux ((k+1)+g+4) (R (k+1)) req).run tbl).1=
        Val (k+1) req ∧
      Sound ((Trans.Recal.runAux ((k+1)+g+4) (R (k+1)) req).run tbl).2 := by
  cases hf:tbl.find? (fun q=>q.1==(R (k+1),req)) with
  | some p =>
    rw [show (k+1)+g+4=(k+g+4)+1 by omega,
      G1.run_hit (k+g+4) (R (k+1)) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_R_of_good hg (k+1) req hr he,hs⟩
  | none =>
    rw [show (k+1)+g+4=(k+g+4)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
      MonadStateOf.get, Id.run, hf, isReducedP_R (k+1), isPrincipalP_R (k+1),
      Bool.not_true, Bool.false_eq_true, if_false, lenI_R (k+1),
      show ((((k+1:Nat):Int)+4-1)==0)=false from
        beq_eq_false_iff_ne.mpr (by omega),
      show Trans.Recal.predP (R (k+1))=R k from predP_R k]
    cases hrun:(Trans.Recal.runAux (k+g+4) (R k) none) tbl with
    | mk a s =>
      have ih1:=ih none (Allowed_none k) tbl hs
      rw [show (Trans.Recal.runAux (k+g+4) (R k) none).run tbl=(a,s) from hrun]
        at ih1
      have ha:a=RBT k:=by simpa only [Val_none] using ih1.1
      have hsm:Sound s:=ih1.2
      subst ha
      simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
        modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
        MonadStateOf.get, Id.run, hrun,
        show ((RBT k)==Trans.Dict.BT.zero)=false from rfl,
        Bool.false_eq_true,if_false,
        show Trans.Recal.fpar (R (k+1)) 0 (((k+1:Nat):Int)+4-1) 0=
            ((k+3:Nat):Int) from by
          simpa only [show (((k+1:Nat):Int)+4-1)=((k+4:Nat):Int) by omega]
            using fpar_R_top k,
        show Trans.Recal.adm (R (k+1)) ((k+3:Nat):Int)=((k+3:Nat):Int) from
          adm_R_parent k]
      cases hrun2:(Trans.Recal.runAux (k+g+4) (R k)
          (some ((k+3:Nat):Int))) s with
      | mk c1 s2 =>
        have ih2:=ih (some ((k+3:Nat):Int)) (Allowed_prev_top k) s hsm
        rw [show (Trans.Recal.runAux (k+g+4) (R k)
          (some ((k+3:Nat):Int))).run s=(c1,s2) from hrun2] at ih2
        have hc1:c1=D1z:=ih2.1.trans (Val_prev_top k)
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
          modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
          MonadStateOf.get, Id.run, hrun2,
          show Trans.Recal.transTypeMain (R (k+1)) ((k+3:Nat):Int)
              (((k+1:Nat):Int)+4-1)=3 from by
            simpa only [show (((k+1:Nat):Int)+4-1)=((k+4:Nat):Int) by omega]
              using transType_R k,
          show Trans.Recal.mkC2 (R (k+1)) ((k+3:Nat):Int)
              (((k+1:Nat):Int)+4-1) 3 D1z=High from by
            simpa only [show (((k+1:Nat):Int)+4-1)=((k+4:Nat):Int) by omega]
              using mkC2_R k]
        rcases hr with h|h|h
        · subst h
          rw [repl_RBT ((RBT k).size+(D1z.size+High.size+4)) k (by
            rw [size_RBT]
            omega)]
          simp only [Option.getD_some]
          refine ⟨Val_none (k+1),?_⟩
          have ht:=Sound_cons_R s2 hsm2 (k+1) none (Allowed_none (k+1))
          rw [Val_none] at ht
          exact ht
        · subst h
          simp only [show (((k+3:Nat):Int)<((k+1:Nat):Int)+4-1) from by omega,
            if_true, StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
            modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
            MonadStateOf.get, Id.run]
          cases hrun3:(Trans.Recal.runAux (k+g+4) (R k)
              (some ((k+3:Nat):Int))) s2 with
          | mk c0 s3 =>
            have ih3:=ih (some ((k+3:Nat):Int)) (Allowed_prev_top k) s2 hsm2
            rw [show (Trans.Recal.runAux (k+g+4) (R k)
              (some ((k+3:Nat):Int))).run s2=(c0,s3) from hrun3] at ih3
            have hc0:c0=D1z:=ih3.1.trans (Val_prev_top k)
            have hsm3:Sound s3:=ih3.2
            subst hc0
            dsimp only
            rw [if_pos (G1.isMarkedB_self D1z),
              G1.replMark_self (D1z.size+(D1z.size+High.size+4)) 1 .zero High
                (by omega)]
            simp only [Option.getD_some]
            refine ⟨(Val_own k).symm,?_⟩
            have ht:=Sound_cons_R s3 hsm3 (k+1)
              (some ((k+3:Nat):Int)) (by simp [Allowed])
            rw [Val_own k] at ht
            exact ht
        · subst h
          simp only [show ¬(((k+4:Nat):Int)<((k+1:Nat):Int)+4-1) by omega,
            if_false,
            show Trans.Recal.gp1 (R (k+1)) (((k+1:Nat):Int)+4-1)=1 from by
              simpa only [show (((k+1:Nat):Int)+4-1)=((k+4:Nat):Int) by omega]
                using gp1_R_top k,
            StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
            modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
            MonadStateOf.get, Id.run]
          refine ⟨(Val_top k).symm,?_⟩
          have ht:=Sound_cons_R s2 hsm2 (k+1)
            (some ((k+4:Nat):Int)) (by simp [Allowed])
          rw [Val_top k] at ht
          exact ht

set_option maxHeartbeats 3000000 in
theorem runAux_R (k g : Nat) (req : Option Int) (hr : Allowed k req)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (k+g+4) (R k) req).run tbl).1=Val k req ∧
      Sound ((Trans.Recal.runAux (k+g+4) (R k) req).run tbl).2 := by
  induction k generalizing g req tbl with
  | zero =>
    simpa only [Nat.zero_add] using runAux_R0 g req hr tbl hs
  | succ k ih =>
    apply runAux_step k g req hr tbl hs
    intro r hallowed s hsound
    exact ih g r hallowed s hsound

/-- Link 2: the recalibrated reader follows the ascending tail. -/
theorem transPort_R (m : Nat) : Trans.Recal.transPort (R m)=RBT m := by
  have hb:m+4≤Trans.Recal.transFuel (R m) := by
    show m+4≤40+6*((R m).length+Trans.Recal.maxE (R m))
    rw [length_R]
    omega
  have h:Trans.Recal.transFuel (R m)=
      m+(Trans.Recal.transFuel (R m)-m-4)+4 := by omega
  show ((Trans.Recal.runAux (Trans.Recal.transFuel (R m)) (R m) none).run []).1=_
  rw [h]
  simpa only [Val_none] using
    (runAux_R m _ none (Allowed_none m) [] Sound_nil).1

#guard (List.range 8).all fun m => Trans.Recal.transPort (R m)==RBT m

/-! ### Link 3 and composition. -/

theorem dict_RBT (n : Nat) : Trans.Dict.dict (RBT n)=fE n := by
  rw [RBT,G4.rep1_eq_G4Dict]
  exact G5Dict.dict_D0_sum_rep1_fE n

theorem one_plus_fE (n : Nat) : plus TM.Term.one (fE n)=fE n := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n => rfl

/-- The selected `ψ₀(Ω₂+ψ₁(Ω₂))` row has the measured expansion sequence for all `n`. -/
theorem oR_M (n : Nat) : Trans.oR (BMS.expand M n)=some (fE n) := by
  show (if (BMS.expand M n).isEmpty then some TM.Term.zero
        else ((Trans.Recal.ofMatrix (BMS.expand M n)).map Trans.Recal.transPort).map
          (fun u=>plus TM.Term.one (Trans.Dict.dict u)))=_
  rw [show (BMS.expand M n).isEmpty=false from by
    rw [expand_M]
    cases n <;> rfl]
  simp only [Bool.false_eq_true,if_false,ofMatrix_M,Option.map_some]
  rw [transPort_R,dict_RBT,one_plus_fE]

#guard (List.range 8).all fun n => Trans.oR (BMS.expand M n)==some (fE n)
#print axioms oR_M






end G5
end Rows.Selected
